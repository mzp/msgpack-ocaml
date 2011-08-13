Require Import Classical.
Require Import chan.
Require Import chanlist.
Require Import set.
Require Import applpi.
Require Import inj.
Require Import inv.
Require Import cong.
Require Import cong_tactic.
Require Import cong_trans.
Require Import redseq.
Require Import logic.
Require Import util_for_tactics.

 (** when the goal has the shape (sat (FMUSTEV ...) P) and that P can only reduce by performing a nu action, it is possible to perform that reduction *)

Lemma red_new_deter :
    forall (f : tform) (L : ChanList) (obs : proc) 
      (A : Set) (C : chan A false -> proc),
    Stable (L # obs) ->
    (forall c : chan A false,
     fresh c L -> tsat (FMUSTEV f) (c & L # parP obs (C c))) ->
    tsat (FMUSTEV f) (L # parP obs (nuP C)).
intros.
apply FMUSTEV_sat.
intros.
generalize H2; intro.
red in H4.
inversion_clear H4.
red in H5.
generalize (H5 O); intro.
inversion_clear H4.
generalize (H7 _ H1); intro.
inversion_clear H4.
inversion_clear H9.
inversion_clear H4.
inversion_clear H10.
inversion H4.
generalize (inv_trans_tau H14); intro.
inversion_clear H15.
inversion_clear H16.
inversion_clear H15.
inversion_clear H17.
inversion_clear H15.
inversion_clear H17.
inversion_clear H15.
decompose [and] H17;clear H17.
injection H16; intros.
rewrite <-H17 in H19; inversion_clear H19.
inversion_clear H15.
inversion_clear H17.
decompose [and] H15;clear H15.
injection H16; intros.
rewrite <-H15 in H17; inversion_clear H17.
inversion_clear H17.
inversion_clear H15.
injection H16; intros.
rewrite <-H19 in H17.
apply NNPP.
intro.
red in H; apply H.
exists (L#x4); exists (epsilon x1); apply red_com; intuition.
inversion_clear H15.
injection H16; intros.
rewrite <-H15 in H17; inversion_clear H17.
inversion H12.
clear H16 H18 H17 P0 Q0 L1.
apply NNPP; intro; red in H; apply H.
exists ((x1&L)#P'); exists (New x1); apply red_new.
auto.
auto.
clear H16 H18 H17 Q0 P0 L1.
generalize (inv_trans_nuP1 H20); intros.
generalize x1 H12 H13 H14 H15 H20; clear x1 H12 H13 H14 H15 H20.
rewrite <-H16; clear H16 A0; intros.
generalize (inv_trans_nuP_lbl H20); intro.
inversion_clear H16.
inversion_clear H17.
generalize (NewL_inj1 H16); intro.
inversion_clear H17.
generalize x1 H12 H13 H14 H15 H16 H20; clear x1 H12 H13 H14 H15 H16 H20; rewrite H22; clear H21 b H22; intros.
clear H16.
generalize (inv_trans_nuP_cont H20); intro.
generalize (H0 _ H15); intro.
generalize (FMUSTEV_sat_inv H17); intros.
rewrite <-H14 in H9.
rewrite <-H19 in H9.
rewrite H16 in H9.
generalize (H21 (fun x => (PS (S x))) H9); intro.
generalize (MaxRedSeq_is_postfix_closed _ H2 (1)); intro.
simpl in H23.
generalize (H22 H23); intro.
generalize (FairRedSeq_is_postfix_closed _ H3 (1)); intro.
generalize (H24 H25); intro.
inversion_clear H26.
inversion_clear H27.
inversion_clear H26.
exists x3; exists (S x4).
auto.
generalize (H6 _ _ H1 H9); intro.
apply NNPP.
intro.
apply H4.
generalize (choose_fresh A L); intro.
inversion_clear H11.
exists ((x&L)#(parP obs (C x))).
exists (New x).
apply red_new.
tr_nu.
auto.
Qed.

Lemma red_new_deterl :
    forall (f : tform) (L : ChanList) (obs : proc) 
      (A : Set) (C : chan A true -> proc),
    Stable (L # obs) ->
    (forall c : chan A true,
     fresh c L -> tsat (FMUSTEV f) (c & L # parP obs (C c))) ->
    tsat (FMUSTEV f) (L # parP obs (nuPl C)).
intros.
apply FMUSTEV_sat.
intros.
generalize H2; intro.
red in H4.
inversion_clear H4.
red in H5.
generalize (H5 O); intro.
inversion_clear H4.
generalize (H7 _ H1); intro.
inversion_clear H4.
inversion_clear H9.
inversion_clear H4.
inversion_clear H10.
inversion H4.
generalize (inv_trans_tau H14); intro.
inversion_clear H15.
inversion_clear H16.
inversion_clear H15.
inversion_clear H17.
inversion_clear H15.
inversion_clear H17.
inversion_clear H15.
decompose [and] H17;clear H17.
injection H16; intros.
rewrite <-H17 in H19; inversion_clear H19.
inversion_clear H15.
inversion_clear H17.
decompose [and] H15;clear H15.
injection H16; intros.
rewrite <-H15 in H17; inversion_clear H17.
inversion_clear H17.
inversion_clear H15.
injection H16; intros.
rewrite <-H19 in H17.
apply NNPP.
intro.
red in H; apply H.
exists (L#x4); exists (epsilon x1); apply red_com; intuition.
inversion_clear H15.
injection H16; intros.
rewrite <-H15 in H17; inversion_clear H17.
inversion H12.
clear H16 H18 H17 P0 Q0 L1.
apply NNPP; intro; red in H; apply H.
exists ((x1&L)#P'); exists (New x1); apply red_new.
auto.
auto.
clear H16 H18 H17 Q0 P0 L1.
generalize (inv_trans_nuPl1 H20); intros.
generalize x1 H12 H13 H14 H15 H20; clear x1 H12 H13 H14 H15 H20.
rewrite <-H16; clear H16 A0; intros.
generalize (inv_trans_nuPl_lbl H20); intro.
inversion_clear H16.
inversion_clear H17.
generalize (NewL_inj1 H16); intro.
inversion_clear H17.
generalize x1 H12 H13 H14 H15 H16 H20; clear x1 H12 H13 H14 H15 H16 H20; rewrite H22; clear H21 b H22; intros.
clear H16.
generalize (inv_trans_nuPl_cont H20); intro.
generalize (H0 _ H15); intro.
generalize (FMUSTEV_sat_inv H17); intros.
rewrite <-H14 in H9.
rewrite <-H19 in H9.
rewrite H16 in H9.
generalize (H21 (fun x => (PS (S x))) H9); intro.
generalize (MaxRedSeq_is_postfix_closed _ H2 (1)); intro.
simpl in H23.
generalize (H22 H23); intro.
generalize (FairRedSeq_is_postfix_closed _ H3 (1)); intro.
generalize (H24 H25); intro.
inversion_clear H26.
inversion_clear H27.
inversion_clear H26.
exists x3; exists (S x4).
auto.
generalize (H6 _ _ H1 H9); intro.
apply NNPP.
intro.
apply H4.
generalize (choose_freshl A L); intro.
inversion_clear H11.
exists ((x&L)#(parP obs (C x))).
exists (New x).
apply red_new.
tr_nu.
auto.
Qed.

Lemma red_new_deter_set :
 forall (f : tform) (L : ChanList),
 ChanList_is_set L ->
 forall (obs : proc) (A : Set) (C : chan A false -> proc),
 Stable (L # obs) ->
 (forall c : chan A false,
  ChanList_is_set (c & L) -> tsat (FMUSTEV f) (c & L # parP obs (C c))) ->
 tsat (FMUSTEV f) (L # parP obs (nuP C)).
intros.
apply red_new_deter.
auto.
intros.
apply H1.
simpl in |- *.
split; auto.
apply fresh_pred2func.
auto.
Qed.

Ltac RedNewDeter_set :=
match goal with
  | |- (tsat (FMUSTEV ?A) ?B#(parP ?C (nuP ?D))) =>
apply red_new_deter_set
end.

(** when the goal has the shape (sat (FMUSTEV ...) P) and that P can only reduce by performing a communication, it is possible to perform that communication *)

Lemma red_com_deter_inout :
 forall (f : tform) (L : ChanList) (obs : proc) (A : Set) 
   (b : bool) (c : chan A b),
 ~ sat (INPUTS c ISANY) (L # obs) ->
 ~ (exists v : A, sat (OUTPUTS c v ISANY) (L # obs)) ->
 Stable (L # obs) ->
 forall (T : A -> proc) (U : proc) (v : A),
 tsat (FMUSTEV f) (L # parP obs (parP (T v) U)) ->
 tsat (FMUSTEV f) (L # parP obs (parP (c ?? T) (c << v >> U))).
intros.
apply FMUSTEV_sat.
intros.
red in H4.
inversion_clear H4.
red in H6.
generalize (H6 0); intro.
inversion_clear H4.
clear H9.
generalize (H8 _ H3); clear H8; intro.
inversion_clear H4.
inversion_clear H8.
inversion_clear H4.
inversion_clear H9.
inversion H4.
clear H9 L0 H11 P.
generalize (inv_trans_tau H13); intro.
inversion_clear H9.
inversion_clear H11.
inversion_clear H9.
inversion_clear H14.
inversion_clear H9.
inversion_clear H14.
inversion_clear H9.
decompose [and] H14; clear H14.
injection H11; intros.
rewrite <- H14 in H16.
inversion H16.
clear H18 H20 H19 P Q0 L0.
generalize (inv_trans_inP1 H22); intro.
generalize x1 x6 H10 H13 H9 H16 H22; clear x1 x6 H10 H13 H9 H16 H22.
rewrite <- H18; clear H18 A0; intros.
generalize (inv_trans_inP_bool H22); intro.
generalize x1 x6 H10 H13 H9 H16 H22; clear x1 x6 H10 H13 H9 H16 H22.
rewrite <- H18; clear H18 b0; intros.
generalize (inv_trans_inP_chan H22); intro.
generalize H10 H13 H9 H16 H22; clear H10 H13 H9 H16 H22.
rewrite <- H18; clear H18 x1; intros.
assert (exists v : A, sat (OUTPUTS c v ISANY) (L # obs)).
rewrite H15.
exists x6.
generalize (inv_trans_OutL H9); intros.
inversion_clear H18.
inversion_clear H19.
inversion_clear H18.
apply OUTPUTS_sat.
exists x7.
exists x1.
split.
apply cong_tr with (parP x7 (c << x6 >> x1)).
auto.
ProcCong.
auto.
absurd (exists v : A, sat (OUTPUTS c v ISANY) (L # obs)).
auto.
auto.
inversion H22.
inversion_clear H9.
inversion_clear H14.
decompose [and] H9; clear H9.
injection H11; intros.
rewrite <- H9 in H14.
inversion_clear H14.
inversion H18.
generalize (inv_trans_outP1 H18); intros.
generalize x1 H10 H13 x6 H16 H18; clear x1 H10 H13 x6 H16 H18.
rewrite <- H14; clear H14 A0; intros.
generalize (inv_trans_outP_bool H18); intros.
generalize x1 H10 H13 x6 H16 H18; clear x1 H10 H13 x6 H16 H18.
rewrite <- H14; clear H14 b0.
intros.
generalize (inv_trans_outP_chan_val H18); intros.
inversion_clear H14.
generalize H10 H13 H16 H18; clear H10 H13 H16 H18; rewrite <- H20;
 rewrite <- H19.
clear H20 H19 x1 x6; intros.
assert (sat (INPUTS c ISANY) (L # obs)).
apply INPUTS_sat.
generalize (inv_trans_InL H16); intros.
inversion_clear H14.
inversion_clear H19.
inversion_clear H14.
exists x6.
exists x1.
split.
apply cong_tr with (parP x6 (c ?? x1)).
rewrite H15; auto.
ProcCong.
auto.
absurd (sat (INPUTS c ISANY) (L # obs)).
auto.
auto.
inversion_clear H14.
inversion_clear H9.
red in H1.
assert (exists KQ : state, Red (L # obs) KQ).
exists (L # x4).
exists (epsilon x1).
apply red_com.
injection H11; intros.
rewrite H16.
auto.
absurd (exists KQ : state, Red (L # obs) KQ).
auto.
auto.
inversion_clear H9.
injection H11.
intros.
rewrite <- H9 in H14.
generalize (inv_trans_tau H14); intros.
inversion_clear H17.		 
inversion_clear H18.
inversion_clear H17.
inversion_clear H19.
inversion_clear H17.
inversion_clear H19.
inversion_clear H17.
decompose [and] H19; clear H19.
injection H18; intros.
rewrite <- H20 in H17.
inversion H17.
inversion_clear H17.
inversion_clear H19.
decompose [and] H17; clear H17.
injection H18; intros.
rewrite <- H17 in H19.
generalize (inv_trans_outP1 H19); intros.
generalize x1 x10 H14 H10 H13 H19 H21; clear x1 x10 H14 H10 H13 H19 H21.
rewrite <- H23.
clear H23 A0.
intros.
generalize (inv_trans_outP_bool H19); intros.
generalize x1 x10 H14 H10 H13 H19 H21; clear x1 x10 H14 H10 H13 H19 H21.
rewrite <- H23; clear H23 b0; intros.
generalize (inv_trans_outP_chan_val H19); intros.
inversion_clear H23.
generalize H14 H10 H13 H19 H21; clear H14 H10 H13 H19 H21.
rewrite <- H25; rewrite <- H24; clear H25 H24 x1 x10; intros.
rewrite <- H20 in H21.
generalize (inv_trans_inP_cont H21); intros.
generalize (inv_trans_outP_cont H19); intros.
rewrite H23 in H22; rewrite H24 in H22; rewrite H22 in H15.
rewrite <- H16 in H15.
generalize (FMUSTEV_sat_inv H2); intros.
rewrite H15 in H12.
rewrite <- H12 in H8.
generalize (H25 (fun n : nat => PS (S n)) H8).
intros.
assert (isMaxRedSeq (fun n : nat => PS (S n))).
assert (isMaxRedSeq PS).
red in |- *.
auto.
apply (MaxRedSeq_is_postfix_closed _ H27 1).
assert (isFairRedSeq (fun n : nat => PS (S n))).
apply (FairRedSeq_is_postfix_closed _ H5 1).
generalize (H26 H27 H28); intros.
inversion_clear H29.
inversion_clear H30.
inversion_clear H29.
exists x1.
exists (S x10).
auto.
inversion_clear H19.
inversion_clear H17.
injection H18; intros.
rewrite <- H21 in H19.
inversion H19.
inversion_clear H17.
injection H18; intros.
rewrite <- H17 in H19.
inversion H19.
inversion H11.
assert (exists KQ : state, Red (L # obs) KQ).
exists (x1 & L # P').
exists (New x1).
apply red_new.
auto.
auto.
absurd (exists KQ : state, Red (L # obs) KQ).
auto.
auto.
inversion H19.
inversion H24.
inversion H24.
generalize (H7 _ _ H3 H8).
intro.
assert
 (exists KQ : state, Red (L # parP obs (parP (c ?? T) (c << v >> U))) KQ).
exists (L # parP obs (parP (T v) U)).
exists (epsilon c).
apply red_com.
apply tr_parR.
apply tr_comIO with (x := c) (v := v).
apply tr_in.
apply tr_out.
absurd
 (exists KQ : state, Red (L # parP obs (parP (c ?? T) (c << v >> U))) KQ).
auto.
auto.
Qed.

Lemma red_com_deter_rinout :
 forall (f : tform) (L : ChanList) (obs : proc) (A : Set) 
   (b : bool) (c : chan A b),
 ~ sat (INPUTS c ISANY) (L # obs) ->
 ~ (exists v : A, sat (OUTPUTS c v ISANY) (L # obs)) ->
 Stable (L # obs) ->
 forall (T : A -> proc) (U : proc) (v : A),
 tsat (FMUSTEV f) (L # parP obs (parP (parP (c ??* T) (T v)) U)) ->
 tsat (FMUSTEV f) (L # parP obs (parP (c ??* T) (c << v >> U))).
intros.
apply FMUSTEV_sat.
intros.
red in H4.
inversion_clear H4.
red in H6.
generalize (H6 0); intro.
inversion_clear H4.
clear H9.
generalize (H8 _ H3); clear H8; intro.
inversion_clear H4.
inversion_clear H8.
inversion_clear H4.
inversion_clear H9.
inversion H4.
clear H11 P H9 L0.
generalize (inv_trans_tau H13); intro.
inversion_clear H9.
inversion_clear H11.
inversion_clear H9.
inversion_clear H14.
inversion_clear H9.
inversion_clear H14.
inversion_clear H9.
decompose [and] H14; clear H14.
injection H11; intros.
rewrite <- H14 in H16.
inversion H16.
clear H18 H20 H19 P Q0 L0.
generalize (inv_trans_rinP1 H22); intro.
generalize x1 x6 H10 H13 H9 H16 H22; clear x1 x6 H10 H13 H9 H16 H22.
rewrite <- H18; clear H18 A0; intros.
generalize (inv_trans_rinP_bool H22); intro.
generalize x1 x6 H10 H13 H9 H16 H22; clear x1 x6 H10 H13 H9 H16 H22.
rewrite <- H18; clear H18 b0; intros.
generalize (inv_trans_rinP_chan H22); intro.
generalize H10 H13 H9 H16 H22; clear H10 H13 H9 H16 H22; rewrite <- H18;
 clear H18 x1; intros.
assert (exists v : A, sat (OUTPUTS c v ISANY) (L # obs)).
rewrite H15.
exists x6.
generalize (inv_trans_OutL H9); intros.
inversion_clear H18.
inversion_clear H19.
inversion_clear H18.
apply OUTPUTS_sat.
exists x7.
exists x1.
split.
apply cong_tr with (parP x7 (c << x6 >> x1)).
auto.
ProcCong.
auto.
absurd (exists v : A, sat (OUTPUTS c v ISANY) (L # obs)).
auto.
auto.
inversion H22.
inversion_clear H9.
inversion_clear H14.
decompose [and] H9; clear H9.
injection H11; intros.
rewrite <- H9 in H14.
inversion_clear H14.
inversion H18.
generalize (inv_trans_outP1 H18); intros.
generalize x1 H10 H13 x6 H16 H18; clear x1 H10 H13 x6 H16 H18. 
rewrite <- H14; clear H14 A0; intros.
generalize (inv_trans_outP_bool H18); intros.
generalize x1 H10 H13 x6 H16 H18; clear x1 H10 H13 x6 H16 H18. 
rewrite <- H14; clear H14 b0.
intros.
generalize (inv_trans_outP_chan_val H18); intros.
inversion_clear H14.
generalize H10 H13 H16 H18; clear H10 H13 H16 H18; rewrite <- H20;
 rewrite <- H19.
clear H20 H19 x1 x6; intros.
assert (sat (INPUTS c ISANY) (L # obs)).
apply INPUTS_sat.
generalize (inv_trans_InL H16); intros.
inversion_clear H14.
inversion_clear H19.
inversion_clear H14.
exists x6.
exists x1.
split.
rewrite H15.
apply cong_tr with (parP x6 (c ?? x1)).
auto.
ProcCong.
auto.
absurd (sat (INPUTS c ISANY) (L # obs)).
auto.
auto.
inversion_clear H14.
inversion_clear H9.
red in H1.
assert (exists KQ : state, Red (L # obs) KQ).
exists (L # x4).
exists (epsilon x1).
apply red_com.
injection H11; intros.
rewrite H16.
auto.
absurd (exists KQ : state, Red (L # obs) KQ).
auto.
auto.
inversion_clear H9.
injection H11.
intros.
rewrite <- H9 in H14.
generalize (inv_trans_tau H14); intros.
inversion_clear H17.		 
inversion_clear H18.
inversion_clear H17.
inversion_clear H19.
inversion_clear H17.
inversion_clear H19.
inversion_clear H17.
decompose [and] H19; clear H19.
injection H18; intros.
rewrite <- H20 in H17.
inversion H17.
inversion_clear H17.
inversion_clear H19.
decompose [and] H17; clear H17.
injection H18; intros.
rewrite <- H17 in H19.
generalize (inv_trans_outP1 H19); intros.
generalize x1 H10 H13 H14 x10 H19 H21; clear x1 H10 H13 H14 x10 H19 H21.
rewrite <- H23.
clear H23 A0.
intros.
generalize (inv_trans_outP_bool H19); intros.
generalize x1 H10 H13 H14 x10 H19 H21; clear x1 H10 H13 H14 x10 H19 H21.
rewrite <- H23; clear H23 b0; intros.
generalize (inv_trans_outP_chan_val H19); intros.
inversion_clear H23.
generalize H10 H13 H14 H19 H21; clear H10 H13 H14 H19 H21.
rewrite <- H25; rewrite <- H24; clear H25 H24 x1 x10; intros.
rewrite <- H20 in H21.
generalize (inv_trans_rinP_cont H21); intros.
generalize (inv_trans_outP_cont H19); intros.
rewrite H24 in H22; rewrite H23 in H22; rewrite H22 in H15.
rewrite <- H16 in H15.
rewrite H15 in H12.
rewrite <- H12 in H8.
generalize (FMUSTEV_sat_inv H2); intros.
generalize (H25 (fun n : nat => PS (S n)) H8).
intros.
assert (isMaxRedSeq (fun n : nat => PS (S n))).
assert (isMaxRedSeq PS).
red in |- *; auto.
apply (MaxRedSeq_is_postfix_closed _ H27 1).
assert (isFairRedSeq (fun n : nat => PS (S n))).
apply (FairRedSeq_is_postfix_closed _ H5 1).
generalize (H26 H27 H28); intros.
inversion_clear H29.
inversion_clear H30.
inversion_clear H29.
exists x1.
exists (S x10).
auto.
inversion_clear H19.
inversion_clear H17.
injection H18; intros.
rewrite <- H21 in H19.
inversion H19.
inversion_clear H17.
injection H18; intros.
rewrite <- H17 in H19.
inversion H19.
inversion H11.
red in H1.
assert (exists KQ : state, Red (L # obs) KQ).
exists (x1 & L # P').
exists (New x1).
apply red_new.
auto.
auto.
absurd (exists KQ : state, Red (L # obs) KQ).
auto.
auto.
inversion H19.
inversion H24.
inversion H24.
generalize (H7 _ _ H3 H8); intro.
assert
 (exists KQ : state, Red (L # parP obs (parP (c ??* T) (c << v >> U))) KQ).
exists (L # parP obs (parP (parP (c ??* T) (T v)) U)).
exists (epsilon c).
apply red_com.
apply tr_parR.
apply tr_comIO with (x := c) (v := v).
apply tr_rin.
apply tr_out.
absurd
 (exists KQ : state, Red (L # parP obs (parP (c ??* T) (c << v >> U))) KQ).
auto.
auto.
Qed.