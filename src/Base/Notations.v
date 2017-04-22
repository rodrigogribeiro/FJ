(* Notations for easy dependently typed programming --- these are defined in CPDT book*)

Set Implicit Arguments.

(* notations for subset types -- sig types *)

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

(* notations for sumbool types *)

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
Notation "x || y" := (if x then Yes else Reduce y).

(* notations for sumor *)

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist _ x _) => e2
                             end)
                             (right associativity, at level 60).

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
                          (right associativity, at level 60).

(* partial subset types *)

Inductive Maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : Maybe P
| Found : forall x : A, P x -> Maybe P.

Notation "{{ x | P }}" := (Maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).