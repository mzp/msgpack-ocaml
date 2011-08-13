Require Import eqdep.

 (** true for linearized channels, false otherwise *)

Axiom chan : Set -> bool -> Set.

Notation "c &&& d" := (eqdep _ _ chan _ _ c _ _ d) (at level 70).

Axiom chan_dec :
  forall (A B : Set) (x' y' : bool) (x : chan A x') (y : chan B y'),
    {x &&& y} + {~ x &&& y}.
Implicit Arguments chan_dec [A B x' y'].