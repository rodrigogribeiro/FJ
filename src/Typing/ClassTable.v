Require Import
        List
        FJ.Base
        FJ.Syntax.FJSyntax
        FJ.Tactics
        FJ.Typing.Subtyping
        FJ.Typing.Wellformedness.

(* Class table *)

                
Definition ObjectNotInCT (CT : ClassTable)
  := ~ M.In Object CT.

Definition SubtypeAntisymmetric (CT : ClassTable)
  := forall C D, M.In C CT -> M.In D CT ->
                 CT |= C <: D -> CT |= D <: C -> C = D.

Axiom SubtypeAntisymmetricDec : forall CT, {SubtypeAntisymmetric CT} + {~ SubtypeAntisymmetric CT}.

(* Sanity definition *)

Definition ClassTableSanity (CT : ClassTable) :=
  ObjectNotInCT CT /\
  SubtypeAntisymmetric CT /\
  Forall (WellFormedClass CT) (values CT).

Hint Unfold ObjectNotInCT ClassTableSanity.

Definition ClassTableSanityDec
  : forall (CT : ClassTable), {ClassTableSanity CT} + {~ ClassTableSanity CT}.
  intro CT.
  destruct* (F.In_dec CT Object).
  +
    right ; unfold ClassTableSanity.
    intro H. destruct* H.
  +
    destruct (SubtypeAntisymmetricDec CT).
    *
      destruct (Forall_dec (WellFormedClassDec CT) (values CT)).
      -
        left ; unfold ClassTableSanity ; jauto.
      -
        right ; unfold ClassTableSanity.
        intro H. destruct* H as [H1 [H2 H3]].
    *
        right ; unfold ClassTableSanity.
        intro H. destruct* H as [H1 [H2 H3]].
Defined.          