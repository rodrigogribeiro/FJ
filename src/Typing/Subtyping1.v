Require Import
        FJ.Base
        FJ.Syntax
        FJ.Tactics.

(* Definitions of subtyping relation *)


Section SUBTYPING.

  Variable CT : ClassTable.

  Definition Object_not_in_CT : Prop :=
    lookup Object CT = None.

  Variable CT_Sanity : Object_not_in_CT.
  
  Hint Unfold Object_not_in_CT.

  Inductive DefinedClass : ClassTable -> ClassName -> Prop :=
  | ObjectDefined : forall CT, DefinedClass CT Object
  | ClassDefined  : forall CT C CD,
      lookup C CT = Some CD ->
      DefinedClass CT C.

  Hint Constructors DefinedClass.

  Lemma lookupDefined : forall C CD, lookup C CT = Some CD -> DefinedClass CT C.
  Proof.
    intros ; eauto.
  Qed.

  Hint Resolve lookupDefined.
       
  (* Predicate which holds if a class is defined *)
    
  Reserved Notation "C '<:' D " (at level 40).

  Inductive Subtype : ClassName -> ClassName -> Prop :=
  | S_Refl  : forall C,
      DefinedClass CT C ->
      C <: C
  | S_Trans : forall (C D E : ClassName) CD, 
      lookup C CT = Some CD  ->
      D = cextends CD   ->
      DefinedClass CT D ->
      DefinedClass CT E -> 
      C <: D -> 
      D <: E -> 
      C <: E
  where "C '<:' D" := (Subtype C D).

  Hint Constructors Subtype.

  (* Object is a super class of itself *)

  Lemma Object_is_superclass : 
    forall C, Subtype Object C -> C = Object.
  Proof.
    unfold Object_not_in_CT in * ;
      intros C H          ; 
      induction H         ;
      substs              ; 
      crush.
  Qed.

  (* No class has object as its subclass *)
  
  Lemma Object_not_subclass :
    forall C, C <> Object -> ~ (Subtype Object C).
  Proof.
    Hint Resolve Object_is_superclass.
    intros C H H1 ;
      apply Object_is_superclass in H1 ;
      crush.
  Qed.

  Hint Resolve Object_is_superclass Object_not_subclass.

  (* decidability of subtyping *)
  
  Fixpoint subtype_bound (CT : list ClassDecl)(n : nat)(C D : ClassName) : option bool :=
    match n with
    | O => None
    | S n' =>
      match eq_nat_dec C D with 
      | Yes =>
        match lookup C CT with
        | Some CD => Some true
        | None    => Some false                  
        end 
      | No  =>   
      end  
    end.

  Lemma subtype_bound_refl
    : forall C, DefinedClass CT C -> exists n, subtype_bound CT n C C = Some true.
  Proof.
    intros C HD ; induction CT ; inverts* HD ; simpl ; crush.
    +
      exists 1 ; simp. 
    +
      exists 1 ; simpl.
      destruct* (eq_nat_dec Object (cname a)) ; crush.
      destruct* (Nat.eq_dec (cname a) (cname a)) ; crush.
      destruct* (lookup Object c) ; crush.
      destruct* (Nat.eq_dec Object Object) ; crush.
      destruct* (Nat.eq_dec Object Object) ; crush.
    +
      destruct* (eq_nat_dec C (cname a)) ; crush.
      substs. exists 1. simpl.
      destruct* (eq_nat_dec (cname CD) (cname CD)) ; crush.
      destruct* (Nat.eq_dec (cname CD) (cname CD)) ; crush.
      assert (exists n, subtype_bound c n C C = Some true).
      -
        apply IHc ; eauto.
      -
        destruct H0 as [n1 Hn].
        exists (1 + n1). simpl.
        destruct* (eq_nat_dec C (cname a)) ; crush.
        destruct* (Nat.eq_dec C C) ; crush.
  Qed.

  Hint Resolve subtype_bound_refl.

  Lemma subtype_bound_step
    : forall C D CD,  lookup C CT = Some CD ->
                      DefinedClass CT D     ->
                      D = cextends CD       ->
                      exists n, subtype_bound CT n C D = Some true.
  Proof.
    intros C D CD HL HD HED ; exists 2 ; unfold Object_not_in_CT in * ;
    simpl in *. substs*. rewrite HL.
    destruct* (Nat.eq_dec C (cextends CD)).
    inverts* HD. rewrite CT_Sanity.
    destruct* (Nat.eq_dec Object Object) ; crush.
    rewrite H.
    destruct* (Nat.eq_dec (cextends CD) (cextends CD)) ; crush.
  Qed.

  Hint Resolve subtype_bound_step.

  Theorem subtype_bound_sound : forall n C D, subtype_bound CT n C D = Some true -> C <: D.
  Proof.
    induction n ; intros ; crush.
    remember (lookup C CT) ; destruct o ; try congruence.
    destruct (Nat.eq_dec C D) ; substs*.
    eapply IHn ; eauto.
    eapply S_Trans ; eauto.
    
    eapply lookupDefined.
    destruct (Nat.eq_dec C Object) ;
    destruct (Nat.eq_dec D Object) ; crush.
  Qed.
  
  Theorem subtype_bound_complete
    : forall C D, C <: D -> exists n, subtype_bound CT n C D = Some true.
  Proof.
    intros C D H ; induction H.
    apply subtype_bound_refl ; auto.
    eapply subtype_bound_trans ; eauto.
    eapply subtype_bound_step ; eauto.
  Qed.  
End SUBTYPING.

Notation "CT '|=' C '<:' D" := (Subtype CT C D)(at level 60, C at level 70).
