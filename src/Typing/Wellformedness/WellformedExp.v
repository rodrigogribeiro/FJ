Require Import
        FJ.Base
	FJ.Syntax. 


Inductive WellFormedExp (CT : ClassTable) : Exp -> Prop :=
| WFVar
  : forall v, WellFormedExp CT (EVar v)
| WFFieldAccess
  : forall e n,
    WellFormedExp CT e ->
    WellFormedExp CT (EFieldAccess e n)
| WFMethodInvoc
  : forall e n es,
    WellFormedExp CT e ->
    Forall (WellFormedExp CT) es ->
    WellFormedExp CT (EMethodInvoc e n es)
| WFCast
  : forall e C CD,
    WellFormedExp CT e ->
    C = get_name CD ->
    In CD CT        ->
    WellFormedExp CT (ECast C e)
| WFNew
  : forall C es CD,
    C = get_name CD    ->
    In CD CT           ->
    Forall (WellFormedExp CT) es ->
    WellFormedExp CT (ENew C es).

Hint Constructors WellFormedExp.

(* custom induction principle for WellFormedExp *)

Definition WellFormedExpInd :=
  fun (CT : ClassTable)(P : Exp -> Prop)
      (f1 : forall v, P (EVar v))
      (f2 : forall e n,
          WellFormedExp CT e ->
          P e ->
          P (EFieldAccess e n))
      (f3 : forall e n es,
          WellFormedExp CT e ->
          P e ->
          Forall (WellFormedExp CT) es ->
          Forall P es ->
          P (EMethodInvoc e n es))
      (f4 : forall e C CD,
          WellFormedExp CT e ->
          P e ->
          C = get_name CD ->
          In CD CT ->
          P (ECast C e))
      (f5 : forall C es CD,
          C = get_name CD ->
          In CD CT ->
          Forall (WellFormedExp CT) es ->
          Forall P es ->
          P (ENew C es)) =>
    fix F (e : Exp)(d : WellFormedExp CT e){struct d} : P e :=
       match d in (WellFormedExp _ e1) return P e1 with
       | WFVar _ v => f1 v
       | WFFieldAccess _ e n He =>
         f2 e n He (F e He)
       | WFMethodInvoc _ e n es He Hes =>
         f3 e n es He (F e He) Hes
            ((fix list_Forall_ind {es' : list Exp}
                  (prf : Forall (WellFormedExp CT) es') : Forall P es' :=
                match prf with
                | Forall_nil _ => Forall_nil P
                | Forall_cons e He Hes => Forall_cons e (F e He)
                                                        (list_Forall_ind Hes)
                end) es Hes)
       | WFCast _ e C CD He Heq HIn =>
         f4 e C CD He (F e He) Heq HIn
       | WFNew _ C es CD Heq HIn Hes =>
         f5 C es CD Heq HIn Hes
            ((fix list_Forall_ind {es' : list Exp}
                  (prf : Forall (WellFormedExp CT) es') : Forall P es' :=
                match prf with
                | Forall_nil _ => Forall_nil P
                | Forall_cons e He Hes => Forall_cons e (F e He)
                                                        (list_Forall_ind Hes)
                end) es Hes)
       end.
