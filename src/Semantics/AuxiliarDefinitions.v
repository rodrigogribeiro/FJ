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

  Record MethodType
    := mkMethodType {
           mtparams : list ClassName ;
           mttype   : ClassName
         }.

  Definition eq_MethodType_dec : forall (mt mt' : MethodType), {mt = mt'} + {mt <> mt'}.
    repeat decide equality.
  Defined.
  
  Inductive m_type_lookup : nat -> Name -> ClassName -> MethodType -> Prop :=
  | mty_base : forall C C' CD ms M MD args Cs n mt,
      M.MapsTo C CD CT                               ->
      ms = cmethods CD                               ->
      M.MapsTo M MD ms                               ->
      args = margs MD                                ->
      Cs = map ftype args                            ->
      C' = mtype MD                                  ->
      mt = mkMethodType Cs C'                        ->
      m_type_lookup n M C mt
  | mty_step : forall C CD D M n mt,
      M.MapsTo C CD CT                             ->
      ~ M.In M (cmethods CD)                       ->
      D = cextends CD                              ->
      m_type_lookup n M D mt                    ->
      m_type_lookup (1 + n) M C mt.

  (* method body lookup *)

  Record MethodBody
    := mkMethodBody {
           mbnames : list Name ;
           mbexp   : Exp
       }.

  Inductive m_body_lookup : nat -> Name -> ClassName -> MethodBody -> Prop :=
  | mbody_base : forall C CD MD ms M args body ns n mb,
      M.MapsTo C CD CT                               ->
      ms = cmethods CD                               ->
      M.MapsTo M MD ms                               ->
      args = margs MD                                ->
      ns = map ftype args                            ->
      body = mbody MD                                ->
      mb = mkMethodBody ns body    ->
      m_body_lookup n M C mb
  | mbody_step : forall C CD D ms M n mb,
      M.MapsTo C CD CT                              ->
      ms = cmethods CD                              ->
      D = cextends CD                               ->
      ~ M.In M ms                                   ->
      m_body_lookup n M D mb                   ->
      m_body_lookup (1 + n) M C mb.                    

  Hint Constructors m_body_lookup.

  (* valid method overriding *)

  Inductive valid_override : nat -> Name -> ClassName -> MethodType -> Prop :=
  | override_ok : forall  M C mt mt1 n,
      m_type_lookup n M C mt ->
      mt = mt1 -> valid_override n M C mt1.

  Hint Constructors valid_override.

  (* substitution *)

  Fixpoint subst1 (e : Exp)(m : Map Exp) : Exp :=
    match e with
    | EVar v => match MapsToDec v m with
                | !! => e
                | [|| e' ||] => e'
                end
    | EFieldAccess e f => EFieldAccess (subst1 e m) f
    | EMethodInvoc e n es =>
      EMethodInvoc (subst1 e m) n (map (fun e => subst1 e m) es)
    | ECast n e => ECast n (subst1 e m)
    | ENew n es => ENew n (map (fun e => subst1 e m) es)                     
    end.  

  Definition substitution (e : Exp)(es : list Exp)(vs : list Name) :=
    subst1 e (P.of_list (combine vs es)).
End Definitions.  

Hint Constructors fields m_type_lookup m_body_lookup valid_override.

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
    forall CT n M C mt, m_type_lookup CT n M C mt ->
    forall mt1, m_type_lookup CT n M C mt1 -> mt = mt1.
  Proof.
    induction n ; intros M C mt H mt1 H1 ;
      inverts* H ; inverts* H1 ; try map_solver ; jauto.
  Qed.

  Definition m_type_lookupDec
    : forall n CT C M, {mt | m_type_lookup CT n M C mt} +
                       {forall mt, ~ m_type_lookup CT n M C mt}.
    refine (fix F n CT C M : {mt | m_type_lookup CT n M C mt} +
                             {forall mt, ~ m_type_lookup CT n M C mt} :=
              match n as n' return  n = n' ->
                              {mt | m_type_lookup CT n M C mt} +
                              {forall mt, ~ m_type_lookup CT n M C mt} with
              | O => fun _ =>
                 match MapsToDec C CT with
                 | !! => !!
                 | [|| CD ||] =>
                   match MapsToDec M (cmethods CD) with
                   | !! => !!
                   | [|| MD ||] => [|| mkMethodType (map ftype (margs MD)) (mtype MD) ||]
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
                   | [|| MD ||] => [|| mkMethodType (map ftype (margs MD)) (mtype MD) ||]   
                   end
                 end          
              end (eq_refl n)) ; clear F ; simpl in * ; substs* ;
      try (intros ; intro H ; inverts* H) ; try map_solver.
      apply n2 in H4 ; auto.
  Defined.
  
  Lemma m_body_lookupDeterministic
    : forall n CT M C mb,
      m_body_lookup CT n M C mb ->
      forall mb1,
        m_body_lookup CT n M C mb1 ->
        mb = mb1.
  Proof.
    induction n ; intros CT M C mb H mb1 H1
    ; inverts* H ; inverts* H1 ; try map_solver ; jauto.
  Qed.

  Definition m_body_lookupDec
    : forall n CT M C, {mb | m_body_lookup CT n M C mb} +
                       {forall mb, ~ m_body_lookup CT n M C mb}.
    refine (fix F n CT M C : {mb | m_body_lookup CT n M C mb} +
                             {forall mb, ~ m_body_lookup CT n M C mb} :=
         match n as n'
              return n = n' -> {mb | m_body_lookup CT n M C mb} +
                               {forall mb, ~ m_body_lookup CT n M C mb} with
         | 0 => fun _ =>
             match MapsToDec C CT with
             | !! => !!
             | [|| CD ||] =>
               match MapsToDec M (cmethods CD) with
               | !! => !!
               | [|| MD ||] => [|| mkMethodBody (map ftype (margs MD)) (mbody MD) ||]
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
               | [|| MD ||] => [|| mkMethodBody (map ftype (margs MD)) (mbody MD) ||]   
               end
             end                 
         end (eq_refl n)) ; clear F ; simpl in * ; substs* ;
      try (intros ; intro H ; inverts* H) ; try map_solver.
      apply n2 in H5 ; auto.
  Defined.
  
  Definition valid_overrideDec : forall CT n M C mt, {valid_override CT n M C mt} +
                                                     {~ valid_override CT n M C mt}.
    refine (fun CT n M C mt =>
              match m_type_lookupDec n CT C M with
              | !! => No
              | [|| mt1 ||] =>
                match eq_MethodType_dec mt mt1 with
                | Yes => Yes
                | No  => No           
                end
             end) ; simpl in * ; substs ; eauto ; try (intro H ; inverts H ; crush) ; eauto.
    apply (m_type_lookupDeterministic _ _ _ _ _ m _) in H0 ; crush.
 Defined.   
End DEC.

