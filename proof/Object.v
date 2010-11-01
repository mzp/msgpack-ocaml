Require Import List Ascii.
Require Import Pow MultiByte.

Open Scope char_scope.

(* ** MsgPackで使うオブジェクトの定義 *)
Inductive object :=
| Bool (_ : bool)
| Array16  ( _ : list object).

(** * 妥当なオブジェクトの定義 *)
Inductive Valid : object -> Prop :=
| VArray16Nil  :
  Valid (Array16 nil)
| VArray16Cons : forall x xs,
  Valid x ->
  Valid (Array16 xs) ->
  List.length (x::xs) < pow 16 ->
  Valid (Array16 (x::xs)).


Lemma length_lt_O: forall A (x : A) xs,
  length (x::xs) > 0.
Proof.
intros.
simpl.
omega.
Qed.
Hint Resolve length_lt_O.

Lemma varray16_inv1: forall x xs,
  Valid (Array16 (x::xs)) ->
  ("000", "000") <> ascii16_of_nat (length (x :: xs)).
Proof.
intros.
apply ascii16_not_O.
split; [ apply length_lt_O | inversion H; auto ].
Qed.

Lemma length_inv: forall A (x y : A) xs ys,
  length (x :: xs) = length (y :: ys) ->
  length xs = length ys.
Proof.
intros.
inversion H.
auto.
Qed.

Lemma varray16_inv2 : forall A (x y : A) xs ys,
  pow 16 > length (x :: xs) ->
  pow 16 > length (y :: ys) ->
  ascii16_of_nat (length (x :: xs)) = ascii16_of_nat (length (y :: ys)) ->
  ascii16_of_nat (length xs) = ascii16_of_nat (length ys).
Proof.
intros.
apply ascii16_of_nat_eq in H1; auto.
Qed.

