Require Import
        List
        FJ.Base
        FJ.Semantics.AuxiliarDefinitions
        FJ.Syntax
        FJ.Typing.Subtyping
        FJ.Tactics.

(* type rules for expressions *)

Section TYPING.

  Variable CT : ClassTable.
  
  Reserved Notation "G '|--' e '::' C" (at level 58, e at next level).

  Inductive StupidWarning : Set := StupidCast : StupidWarning.

  Definition Gamma : Type := Map ClassName.

  Inductive ExpHasType (G : Gamma) : Exp -> ClassName -> Prop :=
  | T_Var : forall v C,
      M.MapsTo v C G ->
      G |-- (EVar v) :: C
  | T_Field : forall e C fs fd fi n,
      G |-- e :: C ->
      fields CT n C fs  ->
      M.MapsTo fi fd fs ->
      G |-- (EFieldAccess e fi) :: (fdtype fd)
  | T_Invoc : forall e C0 Ds es m n mt,
      G |-- e :: C0 ->
      m_type_lookup CT n m C0 mt ->
      Forall2 (ExpHasType G) es Ds ->
      Forall2 (Subtype CT) Ds (mtparams mt) ->
      G |-- EMethodInvoc e m es :: (mttype mt)
  | T_New : forall C Ds Cs fs es n,
      fields CT n C fs ->
      Ds = map fdtype (values fs) ->
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
    : forall CD C E0 MD n,
      M.MapsTo C CD CT ->
      mkGamma ((mkFormalArg this C) :: (margs MD)) |-- (mbody MD) :: E0 ->
      Subtype CT E0 (mtype MD) ->
      valid_override CT n (mname MD) (cextends CD)
                     (mkMethodType (map ftype (margs MD)) (mtype MD)) -> 
      MethodOk C MD.

  (* class typing *)

  Inductive ClassOk : ClassDecl -> Prop :=
  | T_Class
    : forall C CD D n dfds ms K fs,
      M.MapsTo C CD CT ->
      CD = mkClassDecl C D fs K ms ->
      fields CT n D dfds ->
      Forall (MethodOk C) (values ms) ->
      ClassOk CD.
      

End TYPING.

Notation "CT ';' G '|--' e '::' C" := (ExpHasType CT G e C)(at level 58, e at next level).

Hint Constructors StupidWarning.
Hint Constructors ExpHasType.
Hint Constructors MethodOk.
