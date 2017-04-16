Require Import
        List
        Relations
        FJ.Base
        FJ.Syntax.FJSyntax
        FJ.Tactics
        FJ.Typing.Subtyping
        FJ.Typing.Wellformedness.

(* Class table *)


Definition ClassTableFiniteMap (CT : ClassTable)
  := forall CD CD1, In CD CT -> In CD1 CT -> get_name CD = get_name CD1 -> CD = CD1.
                
Definition ObjectNotInCT (CT : ClassTable)
  := forall CD, get_name CD = Object -> ~ In CD CT.

Definition SubtypeAntisymmetric (CT : ClassTable)
  := antisymmetric _ (Subtype CT).

(* Sanity definition *)

Record ClassTableSanity
  := mkClassTableSanity {
         CT : ClassTable ;
         object_not_in_CT : ObjectNotInCT CT ;
         subtype_is_antisymmetric : SubtypeAntisymmetric CT ;
         wellformed : Forall (WellFormedClass CT) CT
     }.