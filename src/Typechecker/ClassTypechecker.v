Require Import
        FJ.Base
        FJ.Syntax
        FJ.Semantics.AuxiliarDefinitions
        FJ.Typing
        FJ.Tactics
        FJ.Typechecker.MethodTypechecker.
(*
Definition ClassOkDec : forall (n : nat) CT (C : ClassName), {{CD | ClassOk CT CD}}.
  refine (fun n CT C =>
            match MapsToDec C CT with
            | !! => ??
            | [|| CD ||] =>          
              match fieldsDec n CT (cextends CD) with
              | !! => ??
              | [|| fs ||] =>
                match Forall2_partial (MethodOkDec n CT (cname CD)) (values (cmethods CD)) with
                | ?? => ??
                | Found _ mds _ => Found _ CD _   
                end
              end    
            end) ; simpl in *.
  eapply T_Class with (ms := cmethods CD) ; eauto.
*)