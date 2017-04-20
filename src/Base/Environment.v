Require Export
	OrderedTypeEx
        FMapAVL
        FMapFacts.


(* Definition of finite maps for defining class tables and typing environments *)

Module M := FMapAVL.Make (Nat_as_OT).
Module P := WProperties_fun Nat_as_OT M.
Module F := P.F.

Definition Map := M.t.

