(* other tactics that I find useful *)

Require Import
        Arith_base
        FJ.Tactics.Crush
        FJ.Tactics.LibTactics.

(* general simplification tactic *)

Ltac s :=
  match goal with
  | [ |- context[eq_nat_dec ?a ?b] ] =>
    destruct (eq_nat_dec a b) ; subst ; try congruence
  | [H : context[eq_nat_dec ?a ?b] |- _] =>
    destruct (eq_nat_dec a b) ; subst ; try congruence
  end.

Ltac simp := repeat (simpl ; s) ; crush.