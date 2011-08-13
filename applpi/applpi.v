Require Import chan.
Require Import chanlist.

(** syntax *)

Set Implicit Arguments.
Unset Strict Implicit.

Inductive proc : Type :=
  | zeroP : proc
  | inP : forall A b, chan A b -> (A -> proc) -> proc
  | rinP : forall A b, chan A b -> (A -> proc) -> proc
  | outP : forall A b, chan A b -> A -> proc -> proc
  | parP : proc -> proc -> proc
  | nuP : forall A, (chan A false -> proc) -> proc
  | nuPl : forall A, (chan A true -> proc) -> proc.

(*Parameter c : (chan nat true).
Check (inP c (fun m => match m with O => zeroP | S _ => parP zeroP zeroP end)).*)

Notation "c << v >> P" := (outP c v P) (at level 40).
Notation "c ?? P" := (inP c P) (at level 40).
Notation "c ??* P" := (rinP c P) (at level 40).

Definition OutAtom (A : Set) (b : bool) (x : chan A b) (v : A) :=
  x << v >> zeroP.
Definition InAtom (A : Set) (b : bool) (x : chan A b) :=
  x ?? (fun y => zeroP).

Definition Cheq (A : Set) (a' : bool) (a : chan A a')
  (B : Set) (b' : bool) (b : chan B b') : bool :=
  match chan_dec a b with
  | left yes => true
  | right no => false
  end.

(** transition semantics *)

Inductive TrLabel : Type :=
  | OutL : forall (A : Set) (b : bool), chan A b -> A -> TrLabel
  | InL : forall (A : Set) (b : bool), chan A b -> A -> TrLabel
  | NewL : forall (A : Set) (b : bool), chan A b -> TrLabel
  | TauL : forall (A : Set) (b : bool), chan A b -> TrLabel.

Inductive Trans : proc -> TrLabel -> proc -> Prop :=
  | tr_out : forall A b (x : chan A b) v P,
      Trans (x << v >> P) (OutL x v) P
  | tr_in : forall A b (x : chan A b) v (C : A -> proc),
      Trans (x ?? C) (InL x v) (C v)
  | tr_rin : forall A b (x : chan A b) v (C : A -> proc),
      Trans (x ??* C) (InL x v) (parP (x ??* C) (C v))
  | tr_newl : forall A (C : chan A true -> proc) (x : chan A true),
      Trans (nuPl C) (NewL x) (C x)
  | tr_new : forall A (C : chan A false -> proc) (x : chan A false),
      Trans (nuP C) (NewL x) (C x)
  | tr_comOI : forall P P' Q Q' A b (x : chan A b) v,
      Trans P (OutL x v) P' ->
      Trans Q (InL x v) Q' -> Trans (parP P Q) (TauL x) (parP P' Q')
  | tr_comIO : forall P P' Q Q' A b (x : chan A b) v,
      Trans P (InL x v) P' ->
      Trans Q (OutL x v) Q' -> Trans (parP P Q) (TauL x) (parP P' Q')
  | tr_parL : forall P P' Q L,
      Trans P L P' -> Trans (parP P Q) L (parP P' Q)
  | tr_parR : forall P P' Q L,
      Trans P L P' -> Trans (parP Q P) L (parP Q P').

(** freshness *)

Definition fresh (A : Set) (b : bool) (c : chan A b) (L : ChanList) :=
  forall (B : Set) (b' : bool) (d : chan B b'),
    in_ChanList d L -> ~ c &&& d.

(** there are infinitely many non-linearized and linearized channels,
note that a process cannot use the axiom to create new channels because
Coq does not allow case analysis on type Prop:
fun x:proc => match (my_choose_fresh A x) with (exist y _) => y
 *)
Axiom choose_fresh : forall (A : Set) (L : ChanList),
  exists x : chan A false, fresh x L.
Axiom choose_freshl : forall (A : Set) (L : ChanList),
  exists x : chan A true, fresh x L.

(** reduction semantics *)

Inductive RedLabel : Type :=
  | New : forall A b, chan A b -> RedLabel
  | epsilon : forall A b, chan A b -> RedLabel.

Notation "l # P" := (pairT l P) (at level 70).

Definition state := prodT ChanList proc.

Inductive Redwith : state -> RedLabel -> state -> Prop :=
  | red_com : forall L P Q A b (x : chan A b),
      Trans P (TauL x) Q -> Redwith (L # P) (epsilon x) (L # Q)
  | red_new : forall L P Q A b (x : chan A b),
      Trans P (NewL x) Q -> fresh x L -> Redwith (L # P) (New x) (x & L # Q).

Notation "P -- L --> Q" := (Redwith P L Q) (at level 50).

Set Strict Implicit.
Unset Implicit Arguments.

Definition Red (P Q : state) : Prop := exists lbl : RedLabel, Redwith P lbl Q.

(** reflexive, transitive closure *)
Inductive Reds : state -> state -> Prop :=
  | reds_b : forall P : state, Reds P P
  | reds_i : forall P Q R : state, Red P Q -> Reds Q R -> Reds P R.

Lemma reds_trans : forall P Q R, Reds P Q -> Reds Q R -> Reds P R.
  induction 1; auto.
  intro.
  apply reds_i with Q; auto.
Qed.

Inductive Reds' : state -> state -> Prop :=
  | reds_b' : forall P, Reds' P P
  | reds_i' : forall P Q R, Reds' P Q -> Red Q R -> Reds' P R.

Lemma reds'_trans : forall P Q R : state, Reds' P Q -> Reds' Q R -> Reds' P R.
intros P Q R PQ.
intro PQ'.
generalize PQ; clear PQ.
elim PQ'.
auto.
intros.
apply (reds_i' _ _ _ (H0 PQ) H1).
Qed.

Lemma reds_reds' : forall P Q : state, Reds' P Q <-> Reds P Q.
intros.
split.
intros.
induction H.
apply reds_b.
apply reds_trans with Q.
auto.
apply reds_i with R.
auto.
apply reds_b.
intros.
induction H.
apply reds_b'.
apply reds'_trans with Q.
apply reds_i' with P.
apply reds_b'.
auto.
auto.
Qed.

Lemma reds_i2 : forall P Q R : state, Reds P Q -> Red Q R -> Reds P R.
intros.
generalize (reds_reds' P R); intro.
inversion_clear H1.
apply H2.
apply reds_i' with Q.
generalize (reds_reds' P Q); intro.
inversion_clear H1.
auto.
generalize (reds_reds' Q R); intro.
tauto.
Qed.

Lemma invariant_by_red :
 forall P : state -> Prop,
 (forall Q0 Q1 : state, Red Q0 Q1 -> P Q0 -> P Q1) ->
 forall p0 pn : state, P p0 -> Reds p0 pn -> P pn.
intros.
inversion H1.
rewrite <- H3; auto.
clear H4 P0 H5 R.
cut (P Q).
(* our goal can be expressed as a property of two universally
quantified processes, we can do elimination using the induction
principle generated by Coq *)
elim H3.
intros; auto.
intros.
apply H6.
apply H with (Q0 := P0).
auto.
auto.
apply H with (Q0 := p0).
auto.
auto.
Qed.



