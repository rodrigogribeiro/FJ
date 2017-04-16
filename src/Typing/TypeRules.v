Require Import
        List
        FJ.Base
        FJ.Semantics.AuxiliarDefinitions
        FJ.Syntax
        FJ.Typing.Subtyping.

(* type rules for expressions *)

Section TYPING.

  Variable CT : ClassTable.
  
  Reserved Notation "G '|--' e '::' C" (at level 58, e at next level).

  Inductive StupidWarning : Set := StupidCast : StupidWarning.

  Definition Gamma : Type := Map ClassName.

  Inductive ExpHasType (G : Gamma) : Exp -> ClassName -> Prop :=
  | T_Var : forall v C,
      M.find v G = Some C ->
      G |-- (EVar v) :: C
  | T_Field : forall e C fs i fd Ci fi,
      G |-- e :: C ->
      fields CT C fs  ->
      nth_error fs i = Some fd ->
      Ci = fdtype fd ->
      fi = get_name fd ->
      G |-- (EFieldAccess e fi) :: Ci
  | T_Invoc : forall e C Cs C0 Ds es m,
      G |-- e :: C0 ->
      m_type_lookup CT m C0 Ds C ->
      Forall2 (ExpHasType G) es Cs ->
      Forall2 (Subtype CT) Cs Ds ->
      G |-- EMethodInvoc e m es :: C
  | T_New : forall C Ds Cs fs es,
      fields CT C fs ->
      Ds = map fdtype fs ->
      Forall2 (ExpHasType G) es Cs ->
      Forall2 (Subtype CT) Cs Ds ->
      G |-- (ENew C es) :: C
  | T_UCast : forall e D C n,
      G |-- e :: D ->
      BoundedSubtype CT n D C ->          
      G |-- (ECast C e) :: C
  | T_DCast : forall e C D n,
      G |-- e :: D    ->
      BoundedSubtype CT n C D ->
      C <> D          ->     
      G |-- (ECast C e) :: C
  | T_SCast : forall e D C n m,      
      G |-- e :: D ->
      ~ (BoundedSubtype CT n D C)   ->
      ~ (BoundedSubtype CT m C D)   ->
      StupidWarning ->
      G |-- (ECast C e) :: C
  where "G '|--' e '::' C" := (ExpHasType G e C).

  Definition mkGamma (fargs : list FormalArg) : Gamma :=
    fold_left (fun ac f => M.add (get_name f) (ftype f) ac) fargs (M.empty _).

  (* method typing *)

  Inductive MethodOk : ClassName -> Method -> Prop :=
  | T_Method
    : forall CD C D C0 E0 e0 Fs Cs nodupfs K Ms nodupms fargs m nodupfargs,
      mkGamma ((mkFormalArg this C) :: fargs) |-- e0 :: E0 ->
      Subtype CT E0 C0 ->
      In CD CT ->
      CD = (mkClassDecl C D Fs nodupfs K Ms nodupms) ->
      map ftype fargs = Cs -> 
      override(CT, m , D, Cs, C0) ->      
      M.find m (to_map Ms) = Some (mkMethod C0 m fargs nodupfargs e0) ->
      MethodOk C (mkMethod C0 m fargs nodupfargs e0).

  (* class typing *)

  Inductive ClassOk : ClassDecl -> Prop :=
  | T_Class
    : forall C CD D fs K Ms nodupfs nodupms cfargs dfargs fdecl,
      K = mkConstructor C
                        (cfargs ++ dfargs)
                        (names cfargs)
                        (map (mkInitializer this) (names fs)) ->
      fields CT D fdecl ->
      NoDup (names (fdecl ++ fs)) ->
      Forall (MethodOk C) Ms ->
      In CD CT ->
      CD = (mkClassDecl C D fs nodupfs K Ms nodupms) ->
      ClassOk (mkClassDecl C D fs nodupfs K Ms nodupms).

End TYPING.

Notation "CT ';' G '|--' e '::' C" := (ExpHasType CT G e C)(at level 58, e at next level).

Hint Constructors StupidWarning.
Hint Constructors ExpHasType.


