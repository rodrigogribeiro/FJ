Require Import
        List
        Relations
        FJ.Base
        FJ.Syntax
        FJ.Tactics.

(* Definitions of subtyping relation *)


Section SUBTYPING.
  Variable CT : ClassTable.

  Definition ClassTableFiniteMap (CT : ClassTable) :=
    forall CD CD1, In CD CT -> In CD1 CT -> get_name CD = get_name CD1 -> CD = CD1.
  
  Variable CTisFM : ClassTableFiniteMap CT.
  
  Inductive BoundedSubtype : nat -> ClassName -> ClassName -> Prop :=
  | BRefl  : forall C, BoundedSubtype 0 C C
  | BStep : forall C CD D E n,
      In CD CT        ->
      C = get_name CD ->
      D = cextends CD ->
      BoundedSubtype n D E   ->
      BoundedSubtype (1 + n) C E.

  Hint Constructors BoundedSubtype.

  Lemma BoundedSubtypeNoStep
    : forall C CD D E n,
      In CD CT ->
      C = get_name CD ->
      D = cextends CD ->
      ~ BoundedSubtype n D E ->
      ~ BoundedSubtype (1 + n) C E.
  Proof.
    intros ; intro.
    inverts* H3.
    unfold ClassTableFiniteMap in CTisFM.
    apply (CTisFM _ _ H H5) in H4.
    substs*.
  Qed.
  
  Hint Resolve BoundedSubtypeNoStep.

  Definition BoundedSubtypeDec : forall n C D, {BoundedSubtype n C D} + {~ BoundedSubtype n C D}.
    refine (fix subdec n C D : {BoundedSubtype n C D} + {~ BoundedSubtype n C D} :=
              match n as m return n = m -> {BoundedSubtype n C D} + {~ BoundedSubtype n C D} with
              | O => fun Heq =>
                  match eq_nat_dec C D with
                  | Yes => Yes
                  | No  => No           
                  end       
              | S n' => fun Heq =>
                  match find C CT with
                  | [|| CD ||]  =>
                    match subdec n' (cextends CD) D with
                    | Yes => Yes
                    | No  => No           
                    end  
                  | !!          => No                   
                  end          
              end (eq_refl n)
           ) ; clear subdec ;
               simpl in * ;
               substs ;
               eauto  ;
               try solve [ intro H ; inverts* H ].
    +
      destruct* a.
    +
      destruct* a ; eapply BoundedSubtypeNoStep ; eauto.
  Defined.

  (* subtyping relation *)

  Reserved Notation "C '<:' D" (at level 40).
  
  Inductive Subtype : ClassName -> ClassName -> Prop :=
  | SRefl : forall C, C <: C
  | SStep : forall C CD D E,                           
      In CD CT ->
      C = get_name CD ->
      D = cextends CD ->
      D <: E  ->
      C <: E
  where "C '<:' D" := (Subtype C D).

  Hint Constructors Subtype.
  
  Theorem BoundedSubtypeSound : forall n C D, BoundedSubtype n C D -> C <: D.
  Proof.
    intros n C D H ; induction H ; eauto.
  Qed.

  Theorem BoundedSubtypeComplete : forall C D, C <: D -> exists n, BoundedSubtype n C D.
  Proof.
    intros C D H ; induction H.
    +
      exists* 0.
    +
      destruct IHSubtype as [m Hm].
      exists* (1 + m).
  Qed.
End SUBTYPING.