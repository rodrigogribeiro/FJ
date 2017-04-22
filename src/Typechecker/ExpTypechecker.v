Require Import
        FJ.Base
	FJ.Syntax
        FJ.Semantics.AuxiliarDefinitions
	FJ.Typing
        FJ.Tactics.

Set Implicit Arguments.

Definition ExpHasTypeDec
  : forall (n : nat) CT G e, {{ C | CT ; G |-- e :: C}}.
  refine (fix ExpHasTypeDec n CT G e : {{C | CT ; G |-- e :: C}} :=
            match e as e'
                  return e = e' -> {{C | CT ; G |-- e :: C}} with
            | EVar v => fun _ =>
               match MapsToDec v G with
               | !! => ??
               | [|| t ||] => Found _ t _
               end          
            | EFieldAccess e v => fun _ =>
               match ExpHasTypeDec n CT G e with
               | Found _ C _ =>
                 match fieldsDec n CT C with
                 | !! => ??
                 | [|| fds ||] =>
                   match MapsToDec v fds with
                   | !! => ??
                   | [|| ft ||] => Found _ (fdtype ft) _
                   end
                 end
               | ?? => ??
               end                      
            | EMethodInvoc e m es => fun _ =>
               match ExpHasTypeDec n CT G e with
               | ?? => ??
               | Found _ C _ =>
                 match m_type_lookupDec n CT C m with
                 | !! => ??
                 | [|| p ||] =>
                   match p with
                   | (Cs , t) =>
                     match eq_nat_dec (length es) (length Cs) with
                     | Yes =>
                       match Forall_partial (ExpHasTypeDec n CT G) es with
                       | ?? => ??
                       | Found _ Ds _ =>
                         match eq_nat_dec (length Ds) (length Cs) with
                         | Yes =>
                           match Forall2_dec (BoundedSubtypeDec CT n) Ds Cs _ with
                           | Yes => _
                           | No => ??           
                           end
                         | No  => ??  
                         end
                       end  
                     | No  => ??           
                     end  
                   end
                 end
               end                        
            | ECast C e => fun _ =>
               match ExpHasTypeDec n CT G e with
               | ?? => ??
               | Found _ D _ =>
                 match BoundedSubtypeDec CT n D C with
                 | Yes => Found _ C _
                 | No  =>
                   match BoundedSubtypeDec CT n C D with
                   | Yes =>
                     match eq_nat_dec C D with
                     | Yes => Found _ C _
                     | No  => Found _ C _               
                     end  
                   | No  => Found _ C _  
                   end
                 end  
               end                
            | ENew C es => fun _ => _
            end (eq_refl e)) ; clear ExpHasTypeDec ; simpl in * ; substs ; eauto ;
    try (intro C ; intro H ; inverts* H ; map_solver).
  eapply BoundedSubtypeForall2 in f0 ; eauto.
  destruct e3. destruct e0. destruct a.
  eauto.

  
(*
Definition ExpHasTypeDec
  : forall (n : nat) CT G e, {C | CT ; G |-- e :: C} + {forall C, ~ (CT ; G |-- e :: C)}.
  refine (fix ExpHasTypeDec n CT G e : {C | CT ; G |-- e :: C} +
                                       {forall C, ~ (CT ; G |-- e :: C)} :=
            match e as e'
                  return e = e' -> {C | CT ; G |-- e :: C} + {forall C, ~ (CT ; G |-- e :: C)} with
            | EVar v => fun _ =>
               match MapsToDec v G with
               | !! => !!
               | [|| t ||] => [|| t ||]          
               end          
            | EFieldAccess e v => fun _ =>
               match ExpHasTypeDec n CT G e with
               | [|| C ||] =>
                 match fieldsDec n CT C with
                 | !! => !!
                 | [|| fds ||] =>
                   match MapsToDec v fds with
                   | !! => !!
                   | [|| ft ||] => [|| fdtype ft ||]          
                   end
                 end
               | !! => !!  
               end                      
            | EMethodInvoc e m es => fun _ =>
               match ExpHasTypeDec n CT G e with
               | !! => !!
               | [|| C ||] =>
                 match m_type_lookupDec n CT C m with
                 | !! => !!
                 | [|| p ||] =>
                   match p with
                   | (Cs , t) => _
                   end
                 end
               end                        
            | ECast C e => fun _ => _
            | ENew C es => fun _ => _                          
            end (eq_refl e)) ; clear ExpHasTypeDec ; simpl in * ; substs ; eauto ;
    try (intro C ; intro H ; inverts* H ; map_solver).
    intro C1 ; intro H ; inverts H.
*)