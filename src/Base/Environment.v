Require Export
        FJ.Base.Notations
	OrderedTypeEx
        FMapAVL
        FMapFacts.


(* Definition of finite maps for defining class tables and typing environments *)

Module M := FMapAVL.Make (Nat_as_OT).
Module P := WProperties_fun Nat_as_OT M.
Module F := P.F.

Definition Map := M.t.

Definition keys {A : Type}(m : Map A) := M.fold (fun k _ ac => k :: ac) m nil.

Definition values {A : Type}(m : Map A) := M.fold (fun _ v ac => v :: ac) m nil.

Definition MapsToDec {A : Type}
  : forall n (m : Map A), {C | M.MapsTo n C m} + {~ M.In n m}.
  refine (fun n m =>
            match M.find n m as r
                  return M.find n m = r -> {C | M.MapsTo n C m} + {~ M.In n m} with
            | None => fun _ => !!
            | Some x => fun _ => [|| x ||]           
            end (eq_refl (M.find n m))).
  apply F.find_mapsto_iff ; auto.
  intro H.
  apply F.in_find_iff in H ; try contradiction.
Defined.
