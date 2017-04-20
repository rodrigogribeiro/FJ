Require Import
        FJ.Base
        FJ.Syntax.FJSyntax.

(* strong induction principle for expressions*)

Definition ExpInd :=
  fun (P : Exp -> Prop)
      (f : forall n, P (EVar n))
      (f1 : forall e n, P e -> P (EFieldAccess e n))
      (f2 : forall e n es,
          P e ->
          Forall P es ->
          P (EMethodInvoc e n es))
      (f3 : forall C e,
          P e -> P (ECast C e))
      (f4 : forall C es,
          Forall P es ->
          P (ENew C es)) =>
    fix F e {struct e} : P e :=
      match e as e' return e = e' -> P e' with
      | EVar n => fun _ => f n
      | EFieldAccess e n => fun _ => f1 e n (F e)
      | EMethodInvoc e n es => fun _ =>
        f2 e n es (F e) ((fix list_Forall_ind' (es' : list Exp) : Forall P es' :=
                            match es' with
                            | nil => Forall_nil P
                            | x :: xs => Forall_cons x (F x) (list_Forall_ind' xs)
                            end) es)
      | ECast C e => fun _ => f3 C e (F e)
      | ENew C es => fun _ =>
        f4 C es ((fix list_Forall_ind' (es' : list Exp) : Forall P es' :=
                            match es' with
                            | nil => Forall_nil P
                            | x :: xs => Forall_cons x (F x) (list_Forall_ind' xs)
                            end) es)
      end (eq_refl e).
