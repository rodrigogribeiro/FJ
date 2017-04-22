Require Import
        FJ.Base
	FJ.Syntax
        FJ.Semantics.AuxiliarDefinitions
	FJ.Typing
        FJ.Tactics.


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
            | EMethodInvoc e m es => fun _ => _                                 
            | ECast C e => fun _ => _
            | ENew C es => fun _ => _                          
            end (eq_refl e)) ; clear ExpHasTypeDec ; simpl in * ; substs ; eauto ;
    try (intro C ; intro H ; inverts* H ; map_solver). 
  intro ; intro H.
  inverts H.