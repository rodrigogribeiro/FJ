Require Import
        FJ.Base
        FJ.Syntax
        FJ.Semantics.AuxiliarDefinitions
        FJ.Typing.Subtyping
        FJ.Typing.TypeRules.
        
(* custom induction principle for ExpHasType *)

Section INDUCTION.

  Definition TyExpInd :=
       fun (CT : ClassTable)   
           (G : Gamma)
           (P : Exp -> ClassName -> Prop)
       (f : forall v C, M.find v G = Some C -> P (EVar v) C) (* variable case *)
       (f0 : forall e C fs i fd Ci fi,                       (* field access case *)
           CT ; G |-- e :: C ->
           P e C ->      
           fields CT C fs ->
           nth_error fs i = Some fd ->
           Ci = fdtype fd ->
           fi = get_name fd ->
           P (EFieldAccess e fi) Ci)
       (f1 : forall e C Cs C0 Ds es m,                       (* method invocation case *)
           CT ; G |-- e :: C0 ->
           P e C0 ->      
           m_type_lookup CT m C0 Ds C ->
           Forall2 (ExpHasType CT G) es Cs ->
           Forall2 (Subtype CT) Cs Ds   ->
           Forall2 P es Cs ->
           P (EMethodInvoc e m es) C)
       (f2 : forall C Ds Cs fs es,                           (* object creation case *)
           fields CT C fs ->
           Ds = map fdtype fs ->
           Forall2 (ExpHasType CT G) es Cs ->
           Forall2 (Subtype CT) Cs Ds ->
           Forall2 P es Cs ->
           P (ENew C es) C)
       (f3 : forall e D C n,                                 (* upcast case *)
           CT ; G |-- e :: D ->
           P e D ->
           BoundedSubtype CT n D C ->
           P (ECast C e) C)
       (f4 : forall e C D n,                                 (* downcast case *)
           CT ; G |-- e :: D ->
           P e D ->
           BoundedSubtype CT n C D ->
           C <> D ->
           P (ECast C e) C)
       (f5 : forall e D C n m,                               (* stupid cast case *)
           CT ; G |-- e :: D ->
           P e D ->     
           ~ BoundedSubtype CT n D C ->
           ~ BoundedSubtype CT m C D ->
           StupidWarning ->
           P (ECast C e) C) =>
  fix F (e : Exp)(C : ClassName)(d : CT ; G |-- e :: C){struct d} : P e C :=
    match d in ( _ ; _ |-- e1 :: C1) return (P e1 C1) with
    | T_Var _ _ x C1 eq => f x C1 eq
    | T_Field _ _ e C fs i fd Ci fi He fds eq1 eq2 eq3 =>
      f0 e C fs i fd Ci fi He (F e C He) fds eq1 eq2 eq3
    | T_Invoc _ _ e C Cs C0 Ds es m He Hml Hfall1 Hfall2 =>
      f1 e C Cs C0 Ds es m He (F e C0 He) Hml Hfall1 Hfall2
         ((fix list_Forall_ind (es' : list Exp)(Cs' : list ClassName)
               (prf : Forall2 (ExpHasType CT G) es' Cs') : Forall2 P es' Cs' :=
             match prf with
             | Forall2_nil _ => Forall2_nil P
             | (@Forall2_cons  _ _ _ ex cx ees ccs H1 H2) =>
                  Forall2_cons ex cx (F ex cx H1) (list_Forall_ind ees ccs H2)
             end) es Cs Hfall1)
    | T_New _ _ C Ds Cs fs es Hfds Heq Hforall1 Hforall2 =>
      f2 C Ds Cs fs es Hfds Heq Hforall1 Hforall2
         ((fix list_Forall_ind (es' : list Exp)(Cs' : list ClassName)
               (prf : Forall2 (ExpHasType CT G) es' Cs') : Forall2 P es' Cs' :=
             match prf with
             | Forall2_nil _ => Forall2_nil P
             | (@Forall2_cons  _ _ _ ex cx ees ccs H1 H2) =>
                  Forall2_cons ex cx (F ex cx H1) (list_Forall_ind ees ccs H2)
             end) es Cs Hforall1)
    | T_UCast _ _ e D C n He Hsub => f3 e D C n He (F e D He) Hsub
    | T_DCast _ _ e C D n He Hsub Hneq => f4 e C D n He (F e D He) Hsub Hneq
    | T_SCast _ _ e D C n m He Hnsub Hmsub Hst => f5 e D C n m He (F e D He) Hnsub Hmsub Hst
    end.  
  
End INDUCTION.