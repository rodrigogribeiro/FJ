Require Import
        FJ.Base
	FJ.Syntax
	FJ.Typing.


Definition ExpHasTypeDec
  : forall CT G e, {C | CT ; G |-- e :: C} + {forall C, ~ (CT ; G |-- e :: C)}.
  refine (fix ExpHasTypeDec CT G e : {C | CT ; G |-- e :: C} + {forall C, ~ (CT ; G |-- e :: C)} :=
            match e as e'
                  return e = e' -> {C | CT ; G |-- e :: C} + {forall C, ~ (CT ; G |-- e :: C)} with
            | EVar v => fun _ =>
               match F.In_dec G v with
               | Yes => [|| _ ||]
               | No  => !!           
               end          
            | EFieldAccess e v => fun _ =>
               match ExpHasTypeDec CT G e with
               | [|| C ||] => _
               | !! => !!  
               end                      
            | EMethodInvoc e m es => fun _ => _                                 
            | ECast C e => fun _ => _
            | ENew C es => fun _ => _                          
            end (eq_refl e)).