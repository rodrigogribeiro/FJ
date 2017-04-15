Require Import
        List
        FJ.Base
        FJ.Syntax.FJSyntax
        FJ.Tactics.

(* Class table *)

Definition ClassTable := list ClassDecl.

Definition ClassTableFiniteMap (CT : ClassTable) :=
  forall CD CD1, In CD CT -> In CD1 CT -> get_name CD = get_name CD1 -> CD = CD1.
              

