Require Import List Ascii.
Require Import MultiByte Object ListUtil.

Open Scope list_scope.
Open Scope char_scope.

Inductive Serialized : object -> list ascii8 -> Prop :=
| STrue :
  Serialized (Bool true)  ["195"]
| SFalse :
  Serialized (Bool false) ["194"]
| SArray16Nil :
  Serialized (Array16 nil) ["221"; "000"; "000"]
| SArray16Cons : forall x xs y ys s1 s2 t1 t2,
  (t1,t2) = ascii16_of_nat (length xs) ->
  (s1,s2) = ascii16_of_nat (length (x::xs)) ->
  Serialized x y ->
  Serialized (Array16 xs) ("221"::t1::t2::ys) ->
  Serialized (Array16 (x::xs)) ("221"::s1::s2::y ++ ys).

Inductive SerializedList : list object -> list ascii8 -> Prop :=
| SSingle : forall x ys,
  Serialized x ys ->
  SerializedList [ x ] ys
| SCons : forall x xs ys zs,
  Serialized x ys ->
  SerializedList xs zs ->
  SerializedList (x::xs) (ys ++ zs).



