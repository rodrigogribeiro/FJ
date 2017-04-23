Require Import
        List
        FJ.Base.Notations
        FJ.Tactics.

(* forall test *)

Definition Forall_dec {A : Type}{P : A -> Prop}(Pdec : forall x, {P x} + {~ P x}) :
  forall (xs : list A), {Forall P xs} + {~ Forall P xs}.
  induction xs.
  +
    left*.
  +  
    destruct IHxs.
    -
      destruct* (Pdec a) ; try (right ; intro H ; inverts* H).
    -
      right ; intro H ; inverts* H.
Defined.

(* Coq do not have a zipWith... *)

Fixpoint zipWith {A B C : Type}(f : A -> B -> C)(xs : list A)(ys : list B) : list C :=
  match xs , ys with
  | nil     , _       => nil
  | _       , nil     => nil
  | x :: xs , y :: ys => f x y :: zipWith f xs ys                
  end.  

Definition Forall2_partial
           {A B : Set}{P : A -> B -> Prop}
           (Pdec : forall (x : A), {{y | P x y}})
  : forall xs, {{ys | Forall2 P xs ys}}.
  induction xs ; simpl in * ; crush.
  +
    eapply Found ; eauto.
  +
    destruct (Pdec a).
    apply Unknown.
    destruct IHxs.
    apply Unknown.
    eapply Found ; eauto.
Defined.

Definition Forall2_dec {A B : Type}{P : A -> B -> Prop}(Pdec : forall x y, {P x y} + {~ P x y}) :
  forall (xs : list A)(ys : list B),
    length xs = length ys -> {Forall2 P xs ys} + {~ Forall2 P xs ys}.
  induction xs ; destruct ys ; simpl in * ; crush.
  apply IHxs in H.
  destruct (Pdec a b).
  destruct H.
  left*.
  right ; intro Hx ; inverts* Hx.
  right ; intro Hx ; inverts* Hx.
Defined.  

(* decidable equality test for lists *)

Definition list_eq_dec
           {A : Type}
           (Adec : forall (x y : A), {x = y} + {x <> y})
  : forall (l l' : list A), {l = l'} + {l <> l'}.
  induction l ; intros l' ; destruct* l' ;
    try solve [ right ; intro H ; congruence ].
  +
    destruct* (Adec a a0) ; substs.
    destruct* (IHl l').
    substs. left*.
    right ; intro H ; inverts* H.
    right ; intro H ; inverts* H.
Defined.