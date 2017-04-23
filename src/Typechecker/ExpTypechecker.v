Require Import
        FJ.Base
	FJ.Syntax
        FJ.Semantics.AuxiliarDefinitions
	FJ.Typing
        FJ.Tactics.

Set Implicit Arguments.

Definition ExpHasTypeDec
  : forall (n : nat) CT G e, {C | CT ; G |-- e :: C} + {True} .
  refine (fix ExpHasTypeDec n CT G e : {C | CT ; G |-- e :: C} + {True} :=
            match e as e'
                  return e = e' -> {C | CT ; G |-- e :: C} + {True} with
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
                   | [|| ft ||] => [|| (fdtype ft) ||]
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
                     match eq_nat_dec (length es) (length (mtparams p)) with
                     | Yes =>
                       match Forall2_partial (ExpHasTypeDec n CT G) es with
                       | !! => !!
                       | [|| Ds ||] =>
                         match eq_nat_dec (length Ds) (length (mtparams p)) with
                         | Yes =>
                           match Forall2_dec (BoundedSubtypeDec CT n) Ds (mtparams p) _ with
                           | Yes => [|| (mttype p) ||]
                           | No => !!           
                           end
                         | No  => !! 
                         end
                       end  
                     | No  => !!            
                   end
                 end
               end                        
            | ECast C e => fun _ =>
               match ExpHasTypeDec n CT G e with
               | !! => !!
               | [|| D ||] =>
                 match BoundedSubtypeDec CT n D C with
                 | Yes => [|| C ||]
                 | No  =>
                   match BoundedSubtypeDec CT n C D with
                   | Yes =>
                     match eq_nat_dec C D with
                     | Yes => [|| C ||]
                     | No  => [|| C ||]
                     end  
                   | No  => [|| C ||]  
                   end
                 end  
               end                
            | ENew C es => fun _ =>
               match fieldsDec n CT C with
               | !! => !!
               | [|| fs ||] =>
                 match eq_nat_dec (length es) (length (values fs)) with
                 | No => !!
                 | Yes =>
                   match Forall2_partial (ExpHasTypeDec n CT G) es with
                   | !! => !!
                   | [|| Ds ||] =>
                     match eq_nat_dec (length Ds) (length (map fdtype (values fs))) with
                     | No => !!
                     | Yes =>
                       match Forall2_dec (BoundedSubtypeDec CT n) Ds
                                         (map fdtype (values fs)) _ with
                       | Yes => [|| C ||]
                       | No  => !!           
                       end
                     end
                   end
                 end
               end
            end (eq_refl e)) ; clear ExpHasTypeDec ; simpl in * ; substs ; eauto ;
    try (intro C ; intro H ; inverts* H ; map_solver).
  Defined.
  
