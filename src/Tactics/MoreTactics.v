(* other tactics that I find useful *)

Require Import
        Arith_base
        FJ.Base.Environment
        FJ.Tactics.Crush
        FJ.Tactics.LibTactics.

(* general simplification tactic *)

Ltac s :=
  match goal with
  | [ |- context[eq_nat_dec ?a ?b] ] =>
    destruct (eq_nat_dec a b) ; subst ; try congruence
  | [H : context[eq_nat_dec ?a ?b] |- _] =>
    destruct (eq_nat_dec a b) ; subst ; try congruence
  | [H : _ /\ _ |- _] => destruct* H                                          
  end.

Ltac simp := repeat (simpl ; s) ; crush.

Ltac map_solver :=
  repeat (match goal with
          | [H : M.MapsTo ?C ?CD ?CT, H2 : M.MapsTo ?C ?CD1 ?CT |- _] =>
            apply (F.MapsTo_fun H) in H2 ; substs
          | [H : ~ M.In ?C ?CS, H2 : M.MapsTo ?C ?D ?CS |- _] =>
            apply F.not_find_in_iff in H ; apply F.find_mapsto_iff in H2 ; crush
          | [H : M.MapsTo _ _ (M.empty _) |- _] =>
            apply F.empty_mapsto_iff in H ; crush
          end).
