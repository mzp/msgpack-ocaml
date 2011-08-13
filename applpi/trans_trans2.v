Require Import chan.
Require Import applpi.
Require Import inj.
Require Import inv.
Require Import redseq.
Require Import inv2.

Set Implicit Arguments.

Lemma trans_trans2_lbl :
 forall P Q L,
 Trans P L Q ->
 forall R L', 
   Trans2 R P L' Q -> sim_lbl L L'.
do 4 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A C x|
   A C x|
   P P' Q Q' A b x v H IHTrans1 H1 IHTrans2|
   P P' Q Q' A b x v H IHTrans1 H1 IHTrans2|
   P P' Q L H IHTrans|
   P P' Q L H IHTrans].
intros.
generalize (inv_trans2_outP H); intro.
decompose [and] H0; clear H0.
rewrite H3.
apply sim_OutL.
intros.
generalize (inv_trans2_inP H); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
rewrite H2.
apply sim_InL.
intros.
generalize (inv_trans2_rinP H); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
rewrite H2.
apply sim_InL.
intros.
generalize (inv_trans2_nuPl H); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
rewrite H2.
apply sim_NewL.
intros.
generalize (inv_trans2_nuP H); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
rewrite H2.
apply sim_NewL.
intros.
inversion H0.
generalize (IHTrans1 _ _ H7); intros.
generalize (sim_lbl_OutL_inv1 H10); intros.
inversion_clear H11.
generalize x0 H6 v0 H7 H9 H10; clear x0 H6 v0 H7 H9 H10; rewrite <- H12;
 rewrite <- H13; clear H12 H13 A0 b0; intros.
generalize (sim_lbl_OutL_inv H10); intros.
inversion_clear H11.
rewrite <- H12.
apply sim_TauL.
generalize (IHTrans1 _ _ H7); intros.
generalize (sim_lbl_OutL_InL_dis H10); contradiction.
rewrite <- H8 in H1.
generalize (Trans_not_refl H1); contradiction.
rewrite <- H7 in H.
generalize (Trans_not_refl H); contradiction.
intros.
inversion H0.
generalize (IHTrans1 _ _ H7); intro.
assert (sim_lbl (OutL x0 v0) (InL x v)).
apply sim_lbl_sym.
auto.
generalize (sim_lbl_OutL_InL_dis H11); contradiction.
generalize (IHTrans2 _ _ H9); intro.
generalize (sim_lbl_OutL_inv1 H10); intros.
inversion_clear H11.
generalize x0 H6 v0 H7 H9 H10; clear x0 H6 v0 H7 H9 H10; rewrite <- H12;
 rewrite <- H13; clear H12 H13 A0 b0; intros.
generalize (sim_lbl_OutL_inv H10); intros.
inversion_clear H11.
rewrite <- H12.
apply sim_TauL.
rewrite <- H8 in H1.
generalize (Trans_not_refl H1); contradiction.
rewrite <- H7 in H.
generalize (Trans_not_refl H); contradiction.
intros.
inversion H0.
generalize (Trans2_not_refl H8); contradiction.
generalize (Trans2_not_refl H8); contradiction.
eapply IHTrans.
apply H5.
generalize (Trans2_not_refl H5); contradiction.
intros.
inversion H0.
generalize (Trans2_not_refl H6); contradiction.
generalize (Trans2_not_refl H6); contradiction.
generalize (Trans2_not_refl H5); contradiction.
eapply IHTrans.
apply H5.
Qed.

Lemma reduced_rin_red_tau' :
    forall R P Q L L',
    reduced R (L # P) (L' # Q) ->
    Red (L # P) (L' # Q) ->
    forall A b (c : chan A b) T,
    R = c ??* T ->
    L = L' /\
    (exists v,
       (exists U,
          Trans2 (Pair (c ??* T) (c << v >> U)) P (TauL c) Q \/
          Trans2 (Pair (c << v >> U) (c ??* T)) P (TauL c) Q)).
intros R P Q L L' H.
inversion H.
clear H1 H3 H5 P0 Q0 R0 H0 H4 K.
intro.
inversion H0.
inversion H1.
clear H3 L0 H7 Q0 H5 P0.
generalize (trans_trans2_lbl H6 H2).
intros.
generalize (sim_lbl_TauL_InL_dis H3); contradiction.
intros.
generalize (trans_trans2_lbl H7 H2).
intros.
generalize (sim_lbl_NewL_InL_dis H11); contradiction.
intros.
rewrite H7 in H2.
generalize (inv_trans2_OutL H2); intros.
inversion_clear H8.
discriminate H9.
intros.
rewrite H7 in H2.
generalize (inv_trans2_NewL H2); intros.
inversion_clear H8.
inversion_clear H9.
discriminate H8.
inversion_clear H9.
discriminate H8.
intros.
rewrite H7 in H2.
generalize (Trans2_Pair_rinP_Rcplmt H2); intro.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
split; auto.
generalize (TauL_inj1 H10); intro X; inversion_clear X.
generalize c0 T H7 H2 H10 x H9; clear c0 T H7 H2 H10 x H9; rewrite <-H8; rewrite <-H11; clear H8 H11 A0 b0; intros.
generalize (TauL_inj H10); intro.
generalize T H7 H2 H10 x H9; clear T H7 H2 H10 x H9.
rewrite <-H8; clear H8 c0; intros.
exists x.
exists x0.
rewrite <-H9; auto.
intros.
rewrite H7 in H2.
generalize (Trans2_Pair_rinP_Lcplmt H2); intro.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
split; auto.
generalize (TauL_inj1 H10); intro X; inversion_clear X.
generalize c0 T H7 H2 H10 x H9; clear c0 T H7 H2 H10 x H9; rewrite <-H8; rewrite <-H11; clear H8 H11 A0 b0; intros.
generalize (TauL_inj H10); intro.
generalize T H7 H2 H10 x H9; clear T H7 H2 H10 x H9.
rewrite <-H8; clear H8 c0; intros.
exists x.
exists x0.
rewrite <-H9; auto.
Qed.

Lemma reduced_rin_red_tau :
 forall P Q L L' A b (c : chan A b) T,
 reduced (c ??* T) (L # P) (L' # Q) ->
 Red (L # P) (L' # Q) ->
 L = L' /\
 (exists v,
    (exists U,
       Trans2 (Pair (c ??* T) (c << v >> U)) P (TauL c) Q \/
       Trans2 (Pair (c << v >> U) (c ??* T)) P (TauL c) Q)).
intros.
apply (reduced_rin_red_tau' H H0 (refl_equal (c ??* T))).
Qed.

Lemma trans2_in_trans_tau_false :
 forall P P' R A b (c : chan A b) v,
 Trans2 (Single R) P (InL c v) P' ->
 forall B b' (d : chan B b'), 
   Trans P (TauL d) P' -> False.
intros.
generalize (trans_trans2_lbl H0 H); intro.
generalize (sim_lbl_TauL_InL_dis H1); contradiction.
Qed.

Lemma trans2_in_trans_new_false :
 forall P P' R A b (c : chan A b) v,
 Trans2 (Single R) P (InL c v) P' ->
 forall B b' (d : chan B b'), 
   Trans P (NewL d) P' -> False.
intros.
generalize (trans_trans2_lbl H0 H); intro.
generalize (sim_lbl_NewL_InL_dis H1); contradiction.
Qed.

Unset Implicit Arguments.