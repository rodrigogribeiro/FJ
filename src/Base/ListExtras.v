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


(* no dup decidable *)

Hint Constructors NoDup.

Definition NoDupDec
           {A : Type}
           (Adec : forall (x y : A), {x = y} + {x <> y}) :
  forall (xs : list A), {NoDup xs} + {~ NoDup xs}.
  refine (fix F xs :=
            match xs as xs' return xs = xs' -> {NoDup xs} + {~ NoDup xs} with
            | nil => fun _ => Yes
            | x :: xs =>
              match In_dec Adec x xs with
              | Yes => fun _ => No
              | No  => fun _ => 
                match F xs with
                | Yes => Yes
                | No  => No           
                end
              end
            end (eq_refl xs)) ; clear F ; substs* ;
    try solve [intro H ; inverts* H ] ; eauto.
Defined.  