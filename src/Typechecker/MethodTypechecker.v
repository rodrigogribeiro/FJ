Require Import
        FJ.Base
        FJ.Syntax
        FJ.Semantics.AuxiliarDefinitions
        FJ.Typing
        FJ.Tactics
        FJ.Typechecker.ExpTypechecker.


Definition MethodOkDec : forall (n : nat) CT C (M : Method), {{ M | MethodOk CT C M}}.
  refine (fun n CT C M =>
            match MapsToDec C CT with
            | !! => ??
            | [|| CD ||] =>
                match ExpHasTypeDec n CT (mkGamma ((mkFormalArg this C) :: (margs M)))
                                    (mbody M) with
                | ?? => ??
                | Found _ D _ =>
                  match valid_overrideDec CT n (mname M) (cextends CD)
                                          (mkMethodType (map ftype (margs M)) (mtype M)) with
                  | No => ??
                  | Yes =>
                    match BoundedSubtypeDec CT n D (mtype M) with
                    | Yes => Found _ M _
                    | No  => ??               
                    end
                  end   
              end
            end) ; simpl in * ; try map_solver ; eauto.
  eapply T_Method ;eauto.
  eapply BoundedSubtypeSound ; eauto.
Defined.