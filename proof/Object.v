Require Import List.
Require Import Pow.

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

