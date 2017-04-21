Require Import
        List
        Relations.Relations
        FJ.Tactics
	FJ.Syntax
        FJ.Semantics.AuxiliarDefinitions
        FJ.Typing.Subtyping.

(* definition of values *)

Section SEMANTICS.

  Variable CT : ClassTable.

  Inductive Value : Exp -> Prop :=
    v_new : forall C es, Forall Value es -> Value (ENew C es).

  Hint Constructors Value.

  Reserved Notation "e '~~>' e1" (at level 80).

  Inductive EStep : Exp -> Exp -> Prop :=
  | XField : forall C fs es fi ei i n,
      fields CT n C fs         ->
      Forall Value es          ->
      nth_error (values fs) i = Some fi ->
      nth_error es i = Some ei ->
      EFieldAccess (ENew C es) (get_name fi) ~~> ei
  | XInvoc : forall C m xs ds es e n,
      m_body_lookup CT n m C xs e   ->
      NoDup (this :: xs)          ->
      List.length ds = List.length xs ->
      EMethodInvoc (ENew C es) m ds ~~> [| ENew C es :: ds \ this :: xs |] e
  | XCast : forall C D es n,
      BoundedSubtype CT n C D ->
      Forall Value es ->      
      ECast D (ENew C es) ~~> ENew C es
  where "e '~~>' e1" := (EStep e e1).

  Hint Constructors EStep.

  Reserved Notation "e '~~>>' e1" (at level 60).

  Inductive ExpStep : Exp -> Exp -> Prop :=
  | EXStep : forall e e',
      e ~~> e' ->
      e ~~>> e'
  | EXField : forall e e' f,
      e ~~>> e' ->
      EFieldAccess e f ~~>> EFieldAccess e' f
  | EXMethodInvoc_step : forall e e' m es,
      e ~~>> e' ->
      EMethodInvoc e m es ~~>> EMethodInvoc e' m es
  | EXMethodInvoc_arg : forall e m ei ei' es es' i,
      ei ~~>> ei' ->
      nth_error es i = Some ei ->
      nth_error es' i = Some ei' ->
      (forall j, j <> i -> nth_error es j = nth_error es' j) ->
      EMethodInvoc e m es ~~>> EMethodInvoc e m es'
  | EXNewArg : forall C ei' es es' ei i,
      ei ~~>> ei' ->
      nth_error es i = Some ei ->
      nth_error es' i = Some ei' ->
      (forall j, j <> i -> nth_error es j = nth_error es' j) ->
      ENew C es ~~>> ENew C es'
  | EXCast : forall C e e',
      e ~~>> e' ->
      ECast C e ~~>> ECast C e'
  where "e '~~>>' e1" := (ExpStep e e1).

  Hint Constructors ExpStep.

  Notation "e '~~>>*' e'" := (clos_refl_trans_1n ExpStep e e')(at level 60).
End SEMANTICS.

Notation "CT '|=' e '~~>' e1" := (EStep CT e e1)(at level 80, e at next level).
Notation "CT '|=' e '~~>>' e1" := (ExpStep CT e e1)(at level 80, e at next level).
Notation "CT '|=' e '~~>>*' e'" := (clos_refl_trans_1n (ExpStep CT) e e')(at level 60).