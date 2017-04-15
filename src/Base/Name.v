Require Import
        Arith_base
        List
        FJ.Base.Notations
        FJ.Tactics.

(* definition of names *)

Definition Name := nat.

(* a type class for things that can have names *)

Class Nameable (A : Type) :={
  get_name : A -> Name ;
}.

Definition names {A : Type}{N : Nameable A}(ls : list A) := List.map get_name ls.

Definition find {A : Type}{N : Nameable A} : forall (n : Name)(ls : list A),
   { x : A | n = get_name x /\ In x ls} + {forall y : A, List.In y ls -> n <> get_name y}.
  refine (fix find n ls : { x : A | n = get_name x /\ In x ls} +
                          {forall y : A, List.In y ls -> n <> get_name y} :=
            match ls with
            | nil => !!
            | x :: xs =>
              match eq_nat_dec n (get_name x) with
              | left _ _ => [|| x ||]
              | right _ _ =>
                match find n xs with
                | [|| x ||] => [|| x ||]
                | !! => !!                 
                end
              end
            end).
  +
    intros y H ; simpl in * ; crush.
  +
    splits* ; simpl ; left*.
  +
    simpl in * ; crush.
  +
    intros y H ; crush.
    eapply n1 ; crush ; auto.
Defined.

(* Coq do not have a zipWith... *)

Fixpoint zipWith {A B C : Type}(f : A -> B -> C)(xs : list A)(ys : list B) : list C :=
  match xs , ys with
  | nil     , _       => nil
  | _       , nil     => nil
  | x :: xs , y :: ys => f x y :: zipWith f xs ys                
  end.  