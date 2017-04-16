Require Import
        FJ.Base
        FJ.Syntax
        FJ.Typing.Wellformedness.WellformedExp.


(* well formed definitions for declarations *)

Section WF.

  Variable CT : ClassTable.

  Inductive WellFormedFormalArg : FormalArg -> Prop :=
    WFFormalArg
    : forall n C CD, C = get_name CD ->
                     In CD CT ->
                     WellFormedFormalArg (mkFormalArg n C).

  Inductive WellFormedField : Field -> Prop :=
    WFField
    : forall n C CD, C = get_name CD ->
                     In CD CT ->
                     WellFormedField (mkField n C).
  
  Inductive WellFormedConstructor : Constructor -> Prop :=
    WFConstructor
    : forall n args sups inis,
      Forall WellFormedFormalArg args
      -> WellFormedConstructor (mkConstructor n args sups inis).
  
  Inductive WellFormedMethod : Method -> Prop :=
    WFMethod
    : forall C m args nodup e CD,
      C = get_name CD ->
      In CD CT -> 
      Forall WellFormedFormalArg args ->
      WellFormedExp CT e ->
      WellFormedMethod (mkMethod C m args nodup e).
  
  Inductive WellFormedClass : ClassDecl -> Prop :=
    WFClass : forall C D fs nodupfs K ms nodupms CD DD,
      C = get_name CD ->
      D = get_name DD ->
      In CD CT ->
      In DD CT ->
      Forall WellFormedField fs ->
      WellFormedConstructor K ->
      Forall WellFormedMethod ms ->
      WellFormedClass (mkClassDecl C D fs nodupfs K ms nodupms).
End WF.

  Hint Constructors
       WellFormedFormalArg
       WellFormedField
       WellFormedConstructor
       WellFormedMethod
       WellFormedClass.