Require Import
        List
        FJ.Base
        FJ.Syntax.FJSyntax
        FJ.Tactics
        FJ.Typing.Subtyping
        FJ.Typing.Wellformedness.

(* Class table *)


Definition ClassTableFiniteMap (CT : ClassTable)
  := forall CD CD1, In CD CT -> In CD1 CT -> get_name CD = get_name CD1 -> CD = CD1.
                
Definition ObjectNotInCT (CT : ClassTable)
  := forall CD, get_name CD = Object -> ~ In CD CT.

Definition SubtypeAntisymmetric (CT : ClassTable)
  := antisymmetric _ (Subtype CT).

(* Sanity definition *)

Record ClassTableSanity
  := mkClassTableSanity {
         CT : ClassTable ;
         object_not_in_CT : ObjectNotInCT CT ;
         subtype_is_antisymmetric : SubtypeAntisymmetric CT ;
         wellformed : Forall (WellFormedClass CT) CT
       }.

Axiom eq_class_dec : forall (C D : ClassDecl), {C = D} + {C <> D}.
  
Definition ClassTableFiniteMapDec
  : forall CT, {ClassTableFiniteMap CT} + {~ ClassTableFiniteMap CT}.
  refine (fix F CT : {ClassTableFiniteMap CT} + {~ ClassTableFiniteMap CT} :=
            match CT as CT1
                  return CT = CT1 -> {ClassTableFiniteMap CT1} + {~ ClassTableFiniteMap CT1} with
            | nil => fun _ => Yes
            | x :: xs => fun _ => 
              match find (get_name x) xs with
              | !! =>
                match F xs with
                | Yes => Yes
                | No  => No           
                end
              | [|| CD ||] =>
                match eq_class_dec x CD with
                | Yes =>
                  match F xs with
                  | Yes => Yes
                  | No  => No           
                  end
                | No  => No         
                end
              end  
            end (eq_refl CT)) ; clear F ; unfold ClassTableFiniteMap in * ; substs*.
  +
    intros ; simpl in * ; contradiction.
  +
    intros ; destruct* a.
    simpl in *.
    destruct* H. substs.
    destruct* H0. destruct* H0.
    substs.
    apply c ; eauto.
  +
    intro H. simpl in *.
    apply n. intros.
    apply H. right*. right*. auto.
  +
    destruct* a.
    intro.
    assert (In x (x :: xs)).
    simpl ; auto.
    assert (In CD (x :: xs)).
    simpl ; right*.
    apply (H1 _ _ H2 H3) in H.
    contradiction.
  +
    intros.
    destruct* H.
    substs.
    destruct* H0.
    apply n in H.
    contradiction.
    simpl in *.
    destruct* H0.
    substs.
    apply n in H.
    crush.
  +
    intro.
    apply n0 ; intros.
    apply H.
    simpl in *.
    right*.
    simpl in *.
    right*.
    auto.
Defined.    