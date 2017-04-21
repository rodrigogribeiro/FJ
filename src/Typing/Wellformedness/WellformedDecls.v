Require Import
        FJ.Base
        FJ.Syntax
        FJ.Typing.Wellformedness.WellformedExp
        FJ.Tactics.


(* well formed definitions for declarations *)

Section WF.

  Variable CT : ClassTable.

  Inductive WellFormedFormalArg : FormalArg -> Prop :=
    WFFormalArg
    : forall n C CD, M.MapsTo C CD CT ->
                     WellFormedFormalArg (mkFormalArg n C).
        
  Inductive WellFormedField : Field -> Prop :=
    WFField
    : forall n C CD, M.MapsTo C CD CT ->
                     WellFormedField (mkField n C).
  
  Inductive WellFormedConstructor : Constructor -> Prop :=
    WFConstructor
    : forall C args sups inis CD,
      M.MapsTo C CD CT ->
      Forall WellFormedFormalArg args ->
      WellFormedConstructor (mkConstructor C args sups inis).
  
  Inductive WellFormedMethod : Method -> Prop :=
    WFMethod
    : forall C m args nodup e CD,
      M.MapsTo C CD CT ->
      Forall WellFormedFormalArg args ->
      WellFormedExp CT e ->
      WellFormedMethod (mkMethod C m args nodup e).
  
  Inductive WellFormedClass : ClassDecl -> Prop :=
    WFClass : forall C D fs K ms CD DD,
      M.MapsTo C CD CT ->
      M.MapsTo D DD CT -> 
      Forall WellFormedField fs ->
      WellFormedConstructor K ->
      Forall WellFormedMethod ms ->
      WellFormedClass (mkClassDecl C D (to_map fs) K (to_map ms)).
End WF.

  Hint Constructors
       WellFormedFormalArg
       WellFormedField
       WellFormedConstructor
       WellFormedMethod
       WellFormedClass.

Section DEC.
  Variable CT : ClassTable.
    
  Definition WellFormedFormalArgDec
    : forall fa, {WellFormedFormalArg CT fa} + {~ WellFormedFormalArg CT fa}.
    refine (fun fa =>
               match fa return {WellFormedFormalArg CT fa} + {~ WellFormedFormalArg CT fa} with
               | mkFormalArg n C =>
                 match MapsToDec C CT with
                 | !! => No
                 | [|| CD ||] => Yes          
                 end  
               end).
    simpl in * ; eauto.
    intro H ; inverts H ; try map_solver.
  Defined.  

  Definition WellFormedFieldDec 
    : forall fd, {WellFormedField CT fd} + {~ WellFormedField CT fd}.
    refine (fun fa =>
               match fa return {WellFormedField CT fa} + {~ WellFormedField CT fa} with
               | mkField n C =>
                 match MapsToDec C CT with
                 | !! => No
                 | [|| CD ||] => Yes          
                 end  
               end) ; simpl in * ; eauto ; try (intro H ; inverts* H) ; try map_solver.
  Defined.  

  Definition WellFormedConstructorDec
    : forall K, {WellFormedConstructor CT K} + {~ WellFormedConstructor CT K}.
    refine (fun K =>
              match K return {WellFormedConstructor CT K} + {~ WellFormedConstructor CT K} with
              | mkConstructor C args sups inis =>
                match MapsToDec C CT with
                | [|| CD ||] =>
                  match Forall_dec WellFormedFormalArgDec args with
                  | Yes => Yes
                  | No  => No
                  end
                | !! => No    
                end
              end) ; simpl in * ; eauto ; try (intro H ; inverts* H) ; try map_solver.
  Defined.

  Definition WellFormedMethodDec
    : forall M, {WellFormedMethod CT M} + {~ WellFormedMethod CT M}.
    refine (fun M =>
              match M return {WellFormedMethod CT M} + {~ WellFormedMethod CT M} with
              | mkMethod C m args nodup e =>
                match MapsToDec C CT with
                | !! => No
                | [|| CD ||] =>
                  match Forall_dec WellFormedFormalArgDec args with
                  | No => No
                  | Yes =>
                    match WellFormedExpDec CT e with
                    | Yes => Yes
                    | No  => No           
                    end  
                  end
                end
              end) ; simpl in * ; try (intro H ; inverts H) ; try map_solver ; eauto.
  Defined.

  Definition WellFormedClassDec
    : forall CD, {WellFormedClass CT CD} + {~ WellFormedClass CT CD}.
    refine (fun CD =>
              match CD return {WellFormedClass CT CD} + {~ WellFormedClass CT CD} with
              | mkClassDecl C D fs K ms =>
                match MapsToDec C CT with
                | !! => No
                | [|| CD1 ||] =>
                  match MapsToDec D CT with
                  | !! => No
                  | [|| DD ||] =>
                    match Forall_dec WellFormedFieldDec (values fs) with
                    | No => No
                    | Yes =>
                      match WellFormedConstructorDec K with
                      | No => No
                      | Yes =>
                        match Forall_dec WellFormedMethodDec (values ms) with
                        | Yes => Yes
                        | No  => No           
                        end
                      end
                    end
                  end
                end
              end) ; simpl in * ; try (intro H ; inverts* H) ; eauto ; try map_solver.
  Defined.

End DEC.  