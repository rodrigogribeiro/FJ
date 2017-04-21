Require Import
        List
        ListDec
        FJ.Base
        FJ.Syntax
        FJ.Tactics.

(* auxiliar definitions for FJ semantics *)

(* field lookup *)

Section Definitions.

  Variable CT : ClassTable.
  
  Inductive fields : nat -> ClassName -> Map Field -> Prop :=
  | F_Obj : fields 0 Object (M.empty _)
  | F_Cls : forall C CD D fs fs' n,
      fs = cfields CD                                ->
      M.MapsTo C CD CT                               ->
      D = cextends CD                                ->
      fields n D fs'                                 ->
      NoDup ((keys fs) ++ (keys fs'))                -> 
      fields (1 + n) C (P.update fs fs').
    
  (* method type lookup *)

  Inductive m_type_lookup : nat -> Name -> ClassName -> list ClassName -> ClassName -> Prop :=
  | mty_base : forall C C' CD ms M MD args Cs n,
      M.MapsTo C CD CT                               ->
      ms = cmethods CD                               ->
      M.MapsTo M MD ms                               ->
      args = margs MD                                ->
      Cs = map ftype args                            ->
      C' = mtype MD                                  ->
      m_type_lookup n M C Cs C'
  | mty_step : forall C C' CD D M Cs n,
      M.MapsTo C CD CT                             ->
      ~ M.In M (cmethods CD)                       ->
      D = cextends CD                              ->
      m_type_lookup n M D Cs C'                    ->
      m_type_lookup (1 + n) M C Cs C'.

  (* method body lookup *)

  Inductive m_body_lookup : nat -> Name -> ClassName -> list ClassName -> Exp -> Prop :=
  | mbody_base : forall C CD MD ms M args body ns n,
      M.MapsTo C CD CT                               ->
      ms = cmethods CD                               ->
      M.MapsTo M MD ms                               ->
      args = margs MD                                ->
      ns = map ftype args                            ->
      body = mbody MD                                ->
      m_body_lookup n M C ns body
  | mbody_step : forall C CD D ms M ns body n,
      M.MapsTo C CD CT                              ->
      ms = cmethods CD                              ->
      D = cextends CD                               ->
      ~ M.In M ms                                   ->
      m_body_lookup n M D ns body                   ->
      m_body_lookup (1 + n) M C ns body.                    

  Hint Constructors m_body_lookup.

  (* valid method overriding *)

  Inductive valid_override : Name -> ClassName -> list ClassName -> ClassName -> Prop :=
  | override_ok : forall  M C C0 Cs Ds D0 n,
      m_type_lookup n M C Ds D0 -> Cs = Ds -> C0 = D0 -> valid_override M C Cs C0.

  Hint Constructors valid_override.

  Record Entry := mkEntry {
     ename : Name ;
     eexp  : Exp ;
  }.   

  Instance NameEntry : Nameable Entry := {
     get_name := ename ;                                     
  }.

  (* substitution *)

  Fixpoint subst1 (e : Exp)(m : list Entry) : Exp :=
    match e with
    | EVar v => match find v m with
                | !! => e
                | [|| e' ||] => eexp e'
                end
    | EFieldAccess e f => EFieldAccess (subst1 e m) f
    | EMethodInvoc e n es =>
      EMethodInvoc (subst1 e m) n (map (fun e => subst1 e m) es)
    | ECast n e => ECast n (subst1 e m)
    | ENew n es => ENew n (map (fun e => subst1 e m) es)                     
    end.  

  Definition substitution (e : Exp)(es : list Exp)(vs : list Name) :=
    subst1 e (zipWith mkEntry vs es).
End Definitions.  

Hint Constructors fields m_type_lookup m_body_lookup.

Notation " '[|' ds '\' xs '|]' e " := (substitution e ds xs) (at level 30).

Section DEC.

  Lemma fieldsDeterministic
     : forall n CT C fs, fields CT n C fs -> forall fs', fields CT n C fs' -> fs = fs'.
  Proof.
    induction n ; intros CT C fs H fs' H' ;
      inverts H ; inverts* H' ; try map_solver ; fequals*.
  Qed.
  
  Definition fieldsDec : forall n CT C,
      {fs | fields CT n C fs} + {forall fs, ~ fields CT n C fs}.
    refine (fix F n CT C : {fs | fields CT n C fs} +
                           {forall fs, ~ fields CT n C fs} :=
            match n as n'
                  return n = n' -> {fs | fields CT n C fs} +
                                   {forall fs, ~ fields CT n C fs} with
            | 0    => fun _ =>
               match eq_nat_dec C Object with
               | Yes => [|| (@M.empty Field)  ||]
               | No  => !!           
               end           
            | S n1 => fun _ =>
               match MapsToDec C CT with
               | [|| CD ||] =>
                 match F n1 CT (cextends CD) with
                 | !! => !!
                 | [|| fs' ||] =>
                   match NoDup_dec eq_nat_dec ((keys (cfields CD)) ++ (keys fs')) with
                   | Yes => [|| P.update (cfields CD) fs' ||]
                   | No  => !!
                   end           
                 end  
               | !!  => !!
               end         
            end (eq_refl n)) ; clear F ; simpl in * ; substs ; eauto ;
             intros fs ; intro H ; inverts* H ; try map_solver.
    +
      apply (fieldsDeterministic _ _ _ _ f) in H4 ;  substs*.
    +
      apply n0 in H4 ; auto.
  Defined.

  Lemma m_type_lookupDeterministic :
    forall CT n M C Cs C', m_type_lookup CT n M C Cs C' ->
    forall Cs1 C1', m_type_lookup CT n M C Cs1 C1' -> Cs = Cs1 /\ C' = C1'.
  Proof.
    induction n ; intros M C Cs C' H Cs1 C1' H1 ;
      inverts* H ; inverts* H1 ; try map_solver ; jauto.
    eapply IHn ; eauto.
  Qed.

  Definition m_type_lookupDec
    : forall n CT C M, {p | exists Cs C', m_type_lookup CT n M C Cs C' /\ p = (Cs , C')} +
                       {forall Cs C', ~ m_type_lookup CT n M C Cs C'}.
    refine (fix F n CT C M : {p | exists Cs C', m_type_lookup CT n M C Cs C' /\ p = (Cs , C')} +
                             {forall Cs C', ~ m_type_lookup CT n M C Cs C'} :=
              match n as n' return  n = n' ->
                              {p | exists Cs C', m_type_lookup CT n M C Cs C' /\ p = (Cs , C')} +
                              {forall Cs C', ~ m_type_lookup CT n M C Cs C'} with
              | O => fun _ =>
                 match MapsToDec C CT with
                 | !! => !!
                 | [|| CD ||] =>
                   match MapsToDec M (cmethods CD) with
                   | !! => !!
                   | [|| MD ||] => [|| (map ftype (margs MD) , mtype MD) ||]
                   end
                 end        
              | S n1 => fun _ =>
                 match MapsToDec C CT with
                 | !! => !!
                 | [|| CD ||] =>
                   match MapsToDec M (cmethods CD) with
                   | !! =>
                     match F n1 CT (cextends CD) M with
                     | !! => !!
                     | [|| p ||] => [|| p ||]          
                     end
                   | [|| MD ||] => [|| (map ftype (margs MD) , mtype MD) ||]   
                   end
                 end          
              end (eq_refl n)) ; clear F ; simpl in * ; substs* ;
      try (intros ; intro H ; inverts* H) ; try map_solver.
      apply n2 in H4 ; auto.
  Defined.
  
  Lemma m_body_lookupDeterministic
    : forall n CT M C Cs e,
      m_body_lookup CT n M C Cs e ->
      forall Cs1 e1,
        m_body_lookup CT n M C Cs1 e1 ->
        Cs = Cs1 /\ e = e1.
  Proof.
    induction n ; intros CT M C Cs e H Cs1 e1 H1
    ; inverts* H ; inverts* H1 ; try map_solver ; jauto.
    eapply IHn ; eauto.
  Qed.

  Definition m_body_lookupDec
    : forall n CT M C, {p | exists Cs e, m_body_lookup CT n M C Cs e /\ p = (Cs , e)} +
                       {forall Cs e, ~ m_body_lookup CT n M C Cs e}.
    refine (fix F n CT M C : {p | exists Cs e, m_body_lookup CT n M C Cs e /\ p = (Cs , e)} +
                             {forall Cs e, ~ m_body_lookup CT n M C Cs e} :=
         match n as n'
              return n = n' -> {p | exists Cs e, m_body_lookup CT n M C Cs e /\ p = (Cs , e)} +
                               {forall Cs e, ~ m_body_lookup CT n M C Cs e} with
         | 0 => fun _ =>
             match MapsToDec C CT with
             | !! => !!
             | [|| CD ||] =>
               match MapsToDec M (cmethods CD) with
               | !! => !!
               | [|| MD ||] => [|| (map ftype (margs MD) , mbody MD) ||]
               end
             end    
         | S n1 => fun _ =>
             match MapsToDec C CT with
             | !! => !!
             | [|| CD ||] =>
               match MapsToDec M (cmethods CD) with
               | !! =>
                 match F n1 CT M (cextends CD) with
                 | !! => !!
                 | [|| p ||] => [|| p ||]          
                 end
               | [|| MD ||] => [|| (map ftype (margs MD) , mbody MD) ||]   
               end
             end                 
         end (eq_refl n)) ; clear F ; simpl in * ; substs* ;
      try (intros ; intro H ; inverts* H) ; try map_solver.
      apply n2 in H5 ; auto.
 Defined.   
End DEC.

