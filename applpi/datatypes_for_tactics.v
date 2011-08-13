Require Import List.
Require Import chan.

 (** the syntax of a process can be represented as a tree, we use lists of "relative positions" to identify each subtrees (eps for the root, one for the left subtree, two for the right subtree) *)

Inductive rel_pos : Set :=
  | one : rel_pos
  | two : rel_pos.

Definition pos := list rel_pos.
Definition eps := nil (A:=rel_pos).

(** an inout_pairs data structure represents a list of reacting in/out processes in the code of tactics *)

Set Implicit Arguments.

Inductive inout_pairs : Type :=
  | nilIO : inout_pairs
  | consIO : forall A b, chan A b -> pos -> pos -> inout_pairs -> inout_pairs.

Fixpoint appP (l m : inout_pairs) {struct l} : inout_pairs :=
  match l with
  | nilIO => m
  | consIO a0 a1 a2 a3 a4 l1 => consIO a2 a3 a4 (appP l1 m)
  end.

Unset Implicit Arguments.

