Require Import
        Arith_base
        List
        FJ.Base.Environment
        FJ.Base.Notations
        FJ.Tactics.

(* definition of names *)

Definition Name := nat.

(* a type class for things that can have names *)

Class Nameable (A : Type) :={
  get_name : A -> Name ;
}.

Definition names {A : Type}{N : Nameable A}(m : list A) := List.map get_name m.

Definition to_map {A : Type}{N : Nameable A}(xs : list A) : Map A :=
  fold_right (fun v ac => M.add (get_name v) v ac) (M.empty _) xs.

(* Coq do not have a zipWith... *)

Fixpoint zipWith {A B C : Type}(f : A -> B -> C)(xs : list A)(ys : list B) : list C :=
  match xs , ys with
  | nil     , _       => nil
  | _       , nil     => nil
  | x :: xs , y :: ys => f x y :: zipWith f xs ys                
  end.  