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
  
  Inductive fields : nat -> ClassName -> list Field -> Prop :=
  | F_Obj : fields 0 Object nil
  | F_Cls : forall C D CD fs fs' n,
      fs = cfields CD                                ->
      In CD CT                                       ->
      C = get_name CD                                ->
      fields n D fs'                                 ->
      NoDup (names (fs ++ fs'))                      -> 
      fields (1 + n) C (fs ++ fs').
    
  (* method type lookup *)

  Reserved Notation "'mtype(' M ',' C ')' '=' Cs '~>' C1" (at level 40, Cs at next level).

  Inductive m_type_lookup : Name -> ClassName -> list ClassName -> ClassName -> Prop :=
  | mty_base : forall C C' D CD fs fsnodup K ms msnodup M MD args argsnodup body Cs,
      In CD CT                                       ->
      C = get_name CD                                ->
      CD = mkClassDecl C D fs fsnodup K ms msnodup   ->
      In MD ms                                       ->
      M = get_name MD                                ->
      MD = mkMethod C' M args argsnodup body         ->
      Cs = map ftype args                            ->
      mtype(M , C) = Cs ~> C'
  | mty_step : forall C C' CD MD D fs fsnodup K ms M msnodup Cs,
      In CD CT                                     ->
      C = get_name CD                              ->
      CD = mkClassDecl C D fs fsnodup K ms msnodup -> 
      ~ In MD ms                                   ->
      M = get_name MD                              ->
      mtype(M, D) = Cs ~> C'                       ->
      mtype(M, C) = Cs ~> C'
  where "'mtype(' M ',' C ')' '=' Cs '~>' C1"
          := (m_type_lookup M C Cs C1).

  (* method body lookup *)

  Reserved Notation "'mbody(' m ',' D ')' '='  xs ';' e " (at level 40).

  Inductive m_body_lookup : Name -> ClassName -> list ClassName -> Exp -> Prop :=
  | mbody_base : forall C C' CD MD D fs fsnodup K ms msnodup M args argsnodup body ns,
      CD = (mkClassDecl C D fs fsnodup K ms msnodup) ->
      C  = get_name CD                               -> 
      In CD CT                                       ->
      M = get_name MD                                ->
      MD = mkMethod C' M args argsnodup body         ->
      In MD ms                                       ->
      ns = map ftype args                            ->
      mbody(M, C) =  ns ; body
  | mbody_step : forall C CD MD D fs fsnodup K ms M msnodup ns body,
      In CD CT                                      ->
      CD = mkClassDecl C D fs fsnodup K ms msnodup  ->
      C = get_name CD                               ->
      ~ In MD ms                                    ->
      M = get_name MD                               ->
      mbody(M, D) =  ns ; body                      ->
      mbody(M, C) =  ns ; body                    
  where "'mbody(' M ',' D ')' '='  xs ';' e" := (m_body_lookup M D xs e).

  Hint Constructors m_body_lookup.

  (* valid method overriding *)

  Reserved Notation "'override(' M ',' C ',' Cs ',' D ')'" (at level 40).

  Inductive valid_override : Name -> ClassName -> list ClassName -> ClassName -> Prop :=
  | override_ok : forall  M C C0 Cs Ds D0,
      mtype(M,C) = Ds ~> D0 -> Cs = Ds -> C0 = D0 -> override( M , C , Cs , C0)
  where "'override(' M ',' C ',' Cs ',' D ')'" := (valid_override M C Cs D).

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

Notation "mtype(' CT ',' M ',' C ')' '=' Cs '~>' C1" := (m_type_lookup CT M C Cs C1)
                                                        (at level 40, Cs at level 60).

Notation "'mbody(' CT ',' m ',' D ')' '='  xs ';' e " := (m_body_lookup CT m D xs e)(at level 40).

Notation "'override(' CT ',' M ',' C ',' Cs ',' D ')'" := (valid_override CT M C Cs D)
                                                            (at level 40).

Notation " '[|' ds '\' xs '|]' e " := (substitution e ds xs) (at level 30).

Section DEC.

  Lemma fieldsDeterministic
     : forall n CT C fs, fields CT n C fs -> forall fs', fields CT n C fs' -> fs = fs'.
  Proof.
    induction n ; intros.
    +
      inverts H ; inverts* H0.
    +
      inverts* H ; inverts* H0.
      eapply IHn ; eauto.
      eapply F_Cls.
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
               | Yes => [|| nil ||]
               | No  => !!           
               end           
            | S n1 => fun _ =>
               match find C CT with
               | !! => !!
               | [|| CD ||] =>
                 match find (cextends CD) CT with
                 | !! => !!
                 | [|| DD ||] =>
                   match F n1 CT (cname DD) with
                   | !! => !!
                   | [|| fs' ||] =>
                     match NoDupDec eq_nat_dec (names (cfields CD ++ fs')) with
                     | Yes => [|| cfields CD ++ fs' ||]
                     | No  => !!           
                     end
                   end
                 end
               end           
            end (eq_refl n)) ; clear F ; simpl in * ; substs ;
            try solve [intros ; intro H ; inverts* H] ; eauto ; intros ; try intro.
    +
      destruct* a.
    +
      destruct* a.
      destruct* a0.
      inverts* H.
      
End DEC.