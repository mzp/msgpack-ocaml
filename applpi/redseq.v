Require Import Omega.
Require Import ArithRing.
Require Import EqNat.
Require Import util.
Require Import chan.
Require Import chanlist.
Require Import applpi.

(** in this file, we define the notions of maximal and fair reduction sequences (or runs) *)

(** a stable process is a process that cannot evolve anymore *)

Definition Stable (LP : state) : Prop := ~ (exists KQ : state, Red LP KQ).

Definition UnStable (P : state) := exists P' : state, Red P P'.

(** a process sequence is a list of processes (rename to state sequence) *)

Definition stateSeq : Type := nat -> optionT state.

(** a reduction sequence is a process sequence such that each process has a predecessor by the reduction relation *)
Definition isRedSeq (PS : stateSeq) : Prop :=
  forall n : nat,
  (forall P : state,
   PS n = SomeT _ P ->
   (exists Q : state, PS (S n) = SomeT _ Q /\ Red P Q) \/ PS (S n) = NoneT _) /\
  (PS n = NoneT _ -> PS (S n) = NoneT _).

Fact empty_seq_isRedSeq : isRedSeq (fun x : nat => NoneT state).
red in |- *; intro.
split; intros.
discriminate H.
auto.
Qed.

Lemma isRedSeq_none :
 forall f : stateSeq,
 isRedSeq f ->
 forall n : nat, f n = NoneT _ -> forall m : nat, n <= m -> f m = NoneT _.
intros ps H n H0 m.
induction m.
intros.
inversion H1.
rewrite <- H2; auto.
intros.
inversion H1.
rewrite <- H2; auto.
red in H.
generalize (H m); intro.
inversion_clear H4.
generalize (IHm H3); intro.
auto.
Qed.

(** beyond a stable process, there are no more processes *)

Lemma isRedSeq_stable_none :
 forall f : stateSeq,
 isRedSeq f ->
 forall (n : nat) (P : state),
 f n = SomeT _ P /\ Stable P -> forall m : nat, n < m -> f m = NoneT _.
intros ps H n P H0 m.
induction m.
intros.
inversion H1.
intros.
red in H1.
inversion H1.
red in H.
generalize (H n); intro.
inversion_clear H2.
assert (ps n = SomeT state P).
intuition.
generalize (H4 _ H2); intros.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
red in H8.
inversion_clear H0.
red in H9.
assert (exists KQ : state, Red P KQ).
exists x.
inversion_clear H8.
exists x0.
auto.
generalize (H9 H0); contradiction.
rewrite <- H3; auto.
assert (n < m).
red in |- *.
auto.
generalize (IHm H4); intro.
red in H.
generalize (H m); intro Z; inversion_clear Z.
auto.
Qed.

Lemma RedSeq_is_postfix_closed :
 forall PS : stateSeq,
 isRedSeq PS -> forall x : nat, isRedSeq (fun n : nat => PS (x + n)).
intros.
red in H.
red in |- *.
split; intros.
generalize (H (x + n)); intro.
inversion_clear H1.
generalize (H2 _ H0); intro.
assert (S (x + n) = x + S n).
auto.
rewrite <- H4; auto.
generalize (H (x + n)); intro.
inversion_clear H1.
assert (S (x + n) = x + S n).
auto.
rewrite <- H1.
auto.
Qed.

(** extension of a redseq (to the left) *)
Lemma lem_RedSeq_is_prefix :
 forall f : stateSeq,
 isRedSeq f ->
 forall P : state,
 (exists f0 : state, f 0 = SomeT _ f0 /\ Red P f0) ->
 isRedSeq (fun j : nat => match j with
                          | O => SomeT _ P
                          | S k => f k
                          end).
intros.
inversion_clear H0.
rename x into f0.
inversion_clear H1.
red in |- *.
intro.
induction n.
split.
intros.
injection H1; intros.
left.
exists f0.
rewrite <- H3; auto.
intro X; discriminate X.
split.
intros.
assert ((exists fsn : _, f (S n) = SomeT _ fsn) \/ f (S n) = NoneT _).
case (f (S n)).
intro p; left; exists p; auto.
right; auto.
inversion_clear H3.
inversion_clear H4.
assert (Red P0 x).
red in H.
generalize (H n); intro.
inversion_clear H4.
generalize (H5 _ H1); intro.
inversion_clear H4.
inversion_clear H7.
inversion_clear H4.
rewrite H3 in H7; injection H7; intros.
rewrite H4.
auto.
rewrite H3 in H7; discriminate H7.
left.
exists x.
split.
auto.
auto.
auto.
intros.
red in H.
generalize (H n); intro.
inversion_clear H3.
auto.
Qed.

(** a maximal reduction sequence is a reduction sequence such the last process is stable (in a reduction sequence the last process may not be stable) *)

Definition isMaxRedSeq (PS : stateSeq) : Prop :=
  isRedSeq PS /\
  (forall (n : nat) (P : state),
   PS n = SomeT _ P -> PS (S n) = NoneT _ -> Stable P).

Fact empty_seq_isMaxRedSeq : isMaxRedSeq (fun x : nat => NoneT state).
red in |- *; split.
apply empty_seq_isRedSeq.
intros.
discriminate H.
Qed.

Lemma MaxRedSeq_is_postfix_closed :
 forall PS : stateSeq,
 isMaxRedSeq PS -> forall x : nat, isMaxRedSeq (fun n : nat => PS (x + n)).
intros.
red in H.
split; intros.
inversion_clear H.
apply RedSeq_is_postfix_closed.
auto.
inversion_clear H.
assert (x + S n = S (x + n)).
auto.
rewrite H in H1.
apply (H3 _ _ H0 H1).
Qed.

(** under which condition a redseq is a maxredseq *)
Lemma redseq_is_maxredseq :
  forall f,
    isRedSeq f ->
    (exists n, 
      (exists x,
	f n = SomeT _ x /\ Stable x /\ (forall m : nat, n < m -> f m = NoneT _))) ->
    isMaxRedSeq f.
intros.
red.
split; auto.
intros.
inversion_clear H0 as [m].
inversion_clear H3 as [Q].
decompose [and] H0; clear H0.
assert (n < m \/ m=n \/ m < n).
omega.
inversion_clear H0.
assert (m = (S n) \/ m > (S n)).
omega.
inversion_clear H0.
subst m.
rewrite H2 in H3; discriminate H3.
assert (S n <= m).
omega.
generalize (isRedSeq_none _ H _ H2 _ H0); intro X; rewrite X in H3; discriminate H3.
inversion_clear H4.
subst m.
rewrite H1 in H3; injection H3; intro; subst Q; auto.
generalize ((proj1 (H m)) _ H3); intro X.
inversion_clear X.
inversion_clear H4.
inversion_clear H7.
red in H5.
assert (exists x, (Red Q x)).
exists x; auto.
generalize (H5 H7); contradiction.
rewrite (H6 _ H0) in H1; discriminate H1.
Qed.

(** in order to define the fairness predicate, we define another transition relation *)

Inductive procs : Type :=
  | Single : proc -> procs
  | Pair : proc -> proc -> procs.

Inductive Trans2 : procs -> proc -> TrLabel -> proc -> Prop :=
  | tr2_out :
      forall (A : Set) (b : bool) (x : chan A b) (v : A) (P : proc),
      Trans2 (Single (x << v >> P)) (x << v >> P) (OutL x v) P
  | tr2_in :
      forall (A : Set) (b : bool) (x : chan A b) (v : A) (C : A -> proc),
      Trans2 (Single (x ?? C)) (x ?? C) (InL x v) (C v)
  | tr2_rin :
      forall (A : Set) (b : bool) (x : chan A b) (v : A) (C : A -> proc),
      Trans2 (Single (x ??* C)) (x ??* C) (InL x v) (parP (x ??* C) (C v))
  | tr2_new :
      forall (A : Set) (x : chan A false) (C : chan A false -> proc),
      Trans2 (Single (nuP C)) (nuP C) (NewL x) (C x)
  | tr2_newl :
      forall (A : Set) (x : chan A true) (C : chan A true -> proc),
      Trans2 (Single (nuPl C)) (nuPl C) (NewL x) (C x)
  | tr2_comOI :
      forall (R1 R2 P P' Q Q' : proc) (A : Set) (v : A) 
        (b : bool) (x : chan A b),
      Trans2 (Single R1) P (OutL x v) P' ->
      Trans2 (Single R2) Q (InL x v) Q' ->
      Trans2 (Pair R1 R2) (parP P Q) (TauL x) (parP P' Q')
  | tr2_comIO :
      forall (R1 R2 P P' Q Q' : proc) (A : Set) (v : A) 
        (b : bool) (x : chan A b),
      Trans2 (Single R1) P (InL x v) P' ->
      Trans2 (Single R2) Q (OutL x v) Q' ->
      Trans2 (Pair R1 R2) (parP P Q) (TauL x) (parP P' Q')
  | tr2_parL :
      forall (Ps : procs) (P P' Q : proc) (L : TrLabel),
      Trans2 Ps P L P' -> Trans2 Ps (parP P Q) L (parP P' Q)
  | tr2_parR :
      forall (Ps : procs) (P P' Q : proc) (L : TrLabel),
      Trans2 Ps P L P' -> Trans2 Ps (parP Q P) L (parP Q P').

Inductive reduced : proc -> state -> state -> Prop :=
  | red_single_in :
      forall (P Q R : proc) (K : ChanList) (A : Set) 
        (b : bool) (c : chan A b) (v : A),
      Trans2 (Single P) Q (InL c v) R -> reduced P (K # Q) (K # R)
  | red_single_out :
      forall (P Q R : proc) (K : ChanList) (A : Set) 
        (b : bool) (c : chan A b) (v : A),
      Trans2 (Single P) Q (OutL c v) R -> reduced P (K # Q) (K # R)
  | red_single_nu :
      forall (P Q R : proc) (K : ChanList) (A : Set) 
        (b : bool) (c : chan A b),
      Trans2 (Single P) Q (NewL c) R -> reduced P (K # Q) (c & K # R)
  | red_pairL :
      forall (P Q R S : proc) (K : ChanList) (A : Set) 
        (b : bool) (c : chan A b),
      Trans2 (Pair P S) Q (TauL c) R -> reduced P (K # Q) (K # R)
  | red_pairR :
      forall (P Q R S : proc) (K : ChanList) (A : Set) 
        (b : bool) (c : chan A b),
      Trans2 (Pair S P) Q (TauL c) R -> reduced P (K # Q) (K # R).

Definition enabled (P : proc) (Q : state) : Prop :=
  exists R : state, reduced P Q R.

Definition ev_reduced (P : proc) (PS : stateSeq) : Prop :=
  exists n : nat,
    (exists Q : state,
       (exists R : state,
          PS n = SomeT _ Q /\ PS (S n) = SomeT _ R /\ reduced P Q R)).

Definition infinitely_often (p : state -> Prop) (PS : stateSeq) : Prop :=
  forall m : nat,
  exists n : nat, (exists P : state, PS (m + n) = SomeT _ P /\ p P).

Lemma inf_often_is_postfix_closed :
 forall (ps : stateSeq) (P : proc),
 infinitely_often (fun Q : state => enabled P Q) ps ->
 forall x : nat,
 infinitely_often (fun Q : state => enabled P Q) (fun n : nat => ps (x + n)).
intros.
red in |- *.
intros.
red in H.
generalize (H (m + x)); intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
exists x0.
exists x1.
split; auto.
assert (m + x + x0 = x + (m + x0)).
ring.
rewrite <- H0.
auto.
Qed.

Lemma inf_often_is_prefix_closed :
 forall (ps : stateSeq) (P : proc) (x : nat),
 infinitely_often (fun Q : state => enabled P Q) (fun n : nat => ps (x + n)) ->
 infinitely_often (fun Q : state => enabled P Q) ps.
intros.
red in |- *; intros.
red in H.
generalize (H m); intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H1.
exists (x + x0).
exists x1.
split; auto.
assert (m + (x + x0) = x + (m + x0)).
ring.
rewrite H1.
auto.
Qed.

(** fairness predicate: a process sequence is fair if it does not contain any process that is infinitely often enabled *)

Definition is_postfix (PS' PS : stateSeq) : Prop :=
  exists n : nat, (forall m : nat, PS' m = PS (m + n)).

Lemma is_postfix_refl : forall ps : stateSeq, is_postfix ps ps.
intro.
red in |- *.
exists 0.
intro.
assert (m + 0 = m).
auto.
rewrite H; auto.
Qed.

Lemma is_postfix_trans :
 forall ps ps' ps'' : stateSeq,
 is_postfix ps ps'' -> is_postfix ps' ps -> is_postfix ps' ps''.
intros.
inversion_clear H.
inversion_clear H0.
red in |- *.
exists (x + x0).
intros.
rewrite (H m).
assert (ps (m + x0) = ps'' (m + x0 + x)).
rewrite <- (H1 (m + x0)).
auto.
rewrite H0.
assert (m + x0 + x = m + (x + x0)).
ring.
rewrite H2; auto.
Qed.

Definition isFairRedSeq (PS : stateSeq) : Prop :=
  forall PS' : stateSeq,
  is_postfix PS' PS ->
  forall P : proc,
  infinitely_often (fun Q : state => enabled P Q) PS' -> ev_reduced P PS'.

Fact empty_seq_isFairRedSeq : isFairRedSeq (fun x : nat => NoneT state).
red in |- *.
intros.
inversion_clear H.
red in H0.
generalize (H0 x); intro X; inversion_clear X.
inversion_clear H.
inversion_clear H2.
rewrite (H1 (x + x0)) in H; discriminate H.
Qed.

Lemma infinitely_often_postfix :
 forall (ps : stateSeq) (p : state -> Prop) (m : nat),
 infinitely_often p (fun x : nat => ps (m + x)) -> infinitely_often p ps.
intros.
red in H.
red in |- *; intro.
generalize (H m0); intros.
inversion_clear H0.
inversion_clear H1.
exists (m + x).
exists x0.
assert (m0 + (m + x) = m + (m0 + x)).
ring.
rewrite H1.
auto.
Qed.

Lemma FairRedSeq_is_postfix_closed :
 forall PS : stateSeq,
 isFairRedSeq PS -> forall x : nat, isFairRedSeq (fun n : nat => PS (x + n)).
intros.
red in |- *; intros.
red in H.
inversion_clear H0.
assert (is_postfix (fun m : nat => PS (x + (m + x0))) PS).
exists (x + x0).
intro.
assert (x + (m + x0) = m + (x + x0)).
ring.
rewrite H0; auto.
generalize (H _ H0); intro.
assert
 (infinitely_often (fun Q : state => enabled P Q)
    (fun m : nat => PS (x + (m + x0)))).
red in |- *.
intro.
generalize (H1 m); intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
exists x1.
exists x2.
split; auto.
rewrite <- H5.
rewrite (H2 (m + x1)).
auto.
generalize (H _ H0 _ H4); intro.
red in H5.
red in |- *.
inversion_clear H5.
exists x1.
inversion_clear H6.
inversion_clear H5.
decompose [and] H6; clear H6.
exists x2.
exists x3.
rewrite (H2 x1).
rewrite (H2 (S x1)).
auto.
Qed.

Lemma beq_nat_S : forall n, (beq_nat (S n) n) = false.
intro.
induction n; auto.
Qed.

Fixpoint le_bool (n:nat) (m:nat) {struct n} : bool :=
  match n, m with
    O, O => true
    | O, S _ => true
    | S _, O => false
    | (S nn), (S mm) => le_bool nn mm
  end.

Lemma le_bool_refl : forall n, (le_bool n n)=true.
intro.
induction n; auto.
Qed.

Lemma leq_le_bool : forall n m, n <= m -> (le_bool n m)=true.
double induction n m; auto.
intros.
inversion H0.
intros.
simpl; intuition.
Qed.

Lemma beq_nat_diff : forall n m, n<>m -> (beq_nat n m) = false.
double induction n m; intuition.
simpl.
auto.
Qed.

Lemma le_bool_S : forall n, (le_bool (S n) n)=false.
intro.
induction n; auto.
Qed.

Lemma leq_le_bool' : forall m n, n > m -> (le_bool n m)=false.
double induction n m; intuition.
inversion H.
inversion H0.
simpl.
intuition.
Qed.

Lemma ps_some_succ : forall ps, (isRedSeq ps) ->
    forall n (Sn:state), (ps n)=(SomeT _ Sn)  ->
	forall k, k <= n -> exists Sk, (ps k)=(SomeT _ Sk).
intros until k.
induction k.
(* base case *)
intro.
assert ((exists S0, ps 0 = SomeT state S0)\/(ps 0=(NoneT state))).
case (ps 0).
intro s; left; exists s; auto.
auto.
inversion_clear H2.
auto.
rewrite (isRedSeq_none _ H _ H3 n H1) in H0; discriminate H0.
(* inductive case *)
intro.
assert (exists Sk : state, ps k = SomeT state Sk).
intuition.
assert ((exists Sk0, ps (S k) = SomeT state Sk0)\/(ps (S k)=(NoneT state))).
case (ps (S k)).
intro s; left; exists s; auto.
auto.
inversion_clear H3.
auto.
rewrite (isRedSeq_none _ H _ H4 n H1) in H0; discriminate H0.
Qed.

Lemma ps_n_ps_Sn_red : forall ps, (isRedSeq ps) ->
  forall n Sn, ps n = SomeT _ Sn ->
    forall Sm, ps (S n) = SomeT _ Sm ->
      (Red Sn Sm).
intros.
generalize (H n); intro X; inversion_clear X.
generalize (H2 _ H0); clear H2; intro X; inversion_clear X.
inversion_clear H2 as [Sm'].
rewrite (proj1 H4) in H1; injection H1; intro; subst Sm'.
intuition.
rewrite H1 in H2; discriminate H2.
Qed.

Lemma reds_to_redseq'' : forall ps P, ps O = SomeT _ P ->
  (forall n, ps (S n) = NoneT _) -> 
    (isRedSeq ps).
intros.
red.
auto.
Qed.

Lemma reds_to_redseq' : forall S S', (Reds' S S') ->
  exists ps, exists n , (isRedSeq ps) /\
    ps O = SomeT _ S /\ ps n = SomeT _ S'.
intros.
induction H.
(* base case *)
exists (fun x => match x with O => SomeT _ P | _ => NoneT _ end).
exists 0.
split; auto.
apply reds_to_redseq'' with P; auto.
(* inductive case *)
inversion_clear IHReds' as [ps X]; inversion_clear X as [n Y]; decompose [and] Y; clear Y.
exists (fun x => if (le_bool x n) then
  (ps x)
  else if (beq_nat x (S n)) then
    (SomeT _ R)
    else
      (NoneT state)).
exists (S n).
split.
red.
intro.
assert (n0 <= n \/ n0=(S n) \/ n0 > (S n)).
omega.
decompose [or] H2; clear H2.
split.
left.
generalize (leq_le_bool _ _ H5); intro.
rewrite H6 in H2; clear H6.
assert ((S n0) <= n \/ (S n0)=(S n)).
omega.
inversion_clear H6.
generalize (leq_le_bool _ _ H7); intro.
rewrite H6; clear H6.
generalize (H1 n0); intro X; inversion_clear X.
generalize (H6 _ H2); intro X; inversion_clear X.
inversion_clear H9.
exists x; auto.
generalize (ps_some_succ _ H1 _ _ H4 _ H7); intro X; inversion_clear X.
rewrite H9 in H10; discriminate H10.
assert ((S n0) > n).
omega.
rewrite (leq_le_bool' _ _ H6).
rewrite H7.
rewrite <-(beq_nat_refl).
exists R.
injection H7; intro.
subst n0.
rewrite H4 in H2; injection H2; intros; subst P0; auto.
rewrite (leq_le_bool _ _ H5).
intros.
generalize (ps_some_succ _ H1 _ _ H4 _ H5); intro X; inversion_clear X.
rewrite H2 in H6; discriminate H6.
(*inversion_clear H5.*)
subst n0.
rewrite <-(beq_nat_refl).
rewrite (le_bool_S n).
split.
intros.
injection H2; clear H2; intro; subst P0.
right.
assert ((le_bool (S (S n)) n)=false).
apply leq_le_bool'.
omega.
rewrite H2.
assert ((beq_nat (S (S n)) (S n))=false).
apply beq_nat_S.
rewrite H5; clear H5.
auto.
intro X; discriminate X.
assert ((le_bool n0 n)=false).
apply leq_le_bool'.
omega.
assert ((beq_nat n0 (S n))=false).
apply beq_nat_diff.
omega.
rewrite H5; clear H5.
split.
left.
rewrite H2 in H5.
discriminate H5.
intros.
assert ((le_bool (S n0) n)=false).
apply leq_le_bool'.
omega.
rewrite H7; clear H7.
assert ((beq_nat (S n0) (S n))=false).
apply beq_nat_diff.
omega.
rewrite H7; clear H7.
auto.
split.
assert ((le_bool 0 n)=true).
apply leq_le_bool.
omega.
rewrite H2; clear H2.
auto.
assert ((le_bool (S n) n)=false).
apply le_bool_S.
rewrite H2; clear H2.
rewrite <-(beq_nat_refl).
auto.
Qed.

Lemma reds_to_redseq : forall S S', (Reds S S') ->
  exists ps, exists n , (isRedSeq ps) /\
    ps O = SomeT _ S /\ ps n = SomeT _ S'.
intros.
assert (Reds' S S').
generalize (reds_reds' S S'); tauto.
apply reds_to_redseq'; auto.
Qed.
