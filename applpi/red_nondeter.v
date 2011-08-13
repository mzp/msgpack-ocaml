Require Import chanlist.
Require Import applpi.
Require Import redseq.
Require Import logic.
Require Import stable.

 (** to verify a FMUSTEV property for a process, it is sufficient to show that it holds for all the derivatives *)

Lemma red_com_nondeter :
 forall P : proc,
 Guarded P ->
 forall L : ChanList,
 UnStable (L # P) ->
 forall f : tform,
 (forall P' : proc, Red (L # P) (L # P') -> tsat (FMUSTEV f) (L # P')) ->
 tsat (FMUSTEV f) (L # P).
intros P H L NOTSTABLE f H0.
apply FMUSTEV_sat.
intros.
generalize H2; intro MAXREDSEQ.
red in MAXREDSEQ.
inversion_clear MAXREDSEQ.
red in H4.
generalize (H4 0); clear H4; intro.
inversion_clear H4.
generalize (H6 _ H1); clear H6; intros.
inversion_clear H4.
inversion_clear H6.
inversion_clear H4.
inversion_clear H.
induction x.
generalize (guarded_no_New H4 H8); intro.
generalize H6 H8; clear H6 H8; rewrite <- H; clear H a; intros.
generalize (H0 _ H8); intros.
generalize (FMUSTEV_sat_inv H); intro.
generalize (H9 (fun x => PS (S x)) H6); intro.
assert (isMaxRedSeq (fun x : nat => PS (S x))).
assert (isMaxRedSeq PS).
red in |- *; auto.
apply (MaxRedSeq_is_postfix_closed _ H11 1).
assert (isFairRedSeq (fun x : nat => PS (S x))).
apply (FairRedSeq_is_postfix_closed _ H3 1).
generalize (H10 H11 H12); intros.
inversion_clear H13.
inversion_clear H14.
inversion_clear H13.
exists x; exists (S x1).
auto.
generalize (H5 _ _ H1 H6); clear H5; intros.
red in NOTSTABLE.
generalize (H4 NOTSTABLE); contradiction.
Qed.
