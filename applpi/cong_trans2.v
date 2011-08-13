Require Import chan.
Require Import applpi.
Require Import redseq.
Require Import inj.
Require Import inv2.
Require Import cong.
Require Import cong_tactic.

Set Implicit Arguments.

Lemma inv_trans2_single_rinP_cong' :
  forall R P Q L,
    Trans2 (Single R) P L Q ->
    forall A b (c : chan A b) T,
      R = c ??* T ->
      exists R,
	Cong P (parP R (c ??* T)) /\
	(exists v, L = InL c v /\ Cong Q (parP R (parP (c ??* T) (T v)))).
intros R P; generalize R; clear R.
induction P.
intros.
inversion_clear H.
intros.
rewrite H1 in H0.
inversion H0.
intros.
rewrite H1 in H0.
generalize (inv_trans2_rinP_rinP1 H0); intro X; inversion_clear X.
generalize c0 T H1 H0; clear c0 T H1 H0; rewrite H2; rewrite H3; clear H2 H3 A0 b0; intros.
generalize (inv_trans2_rinP_rinP_chan H0); intro.
generalize H1 H0; clear H1 H0; rewrite H2; clear H2 c0; intros.
generalize (inv_trans2_rinP_rinP_cont H0); intro.
generalize H1 H0; clear H1 H0; rewrite H2; clear H2; intros.
exists zeroP.
split.
ProcCong.
generalize (inv_trans2_rinP H0); intro.
inversion_clear H2.
inversion_clear H4.
exists x.
split; intuition.
rewrite H5; ProcCong.
intros.
rewrite H0 in H.
inversion H.
intros.
rewrite H0 in H.
generalize (inv_trans2_rinP_parP H); intro X; inversion_clear X.
inversion_clear H1.
inversion_clear H2.
lapply (IHP1 _ _ _ H1 _ _ c T).
intro.
inversion_clear H2.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
exists (parP x0 P2).
split.
apply cong_tr with (parP (parP x0 (rinP c T)) P2).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
exists x1.
split; auto.
rewrite H3.
apply cong_tr with (parP (parP x0 (parP (rinP c T) (T x1))) P2).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
auto.
inversion_clear H1.
inversion_clear H2.
lapply (IHP2 _ _ _ H1 _ _ c T).
intro.
inversion_clear H2.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
exists (parP x0 P1).
split.
apply cong_tr with (parP P1 (parP x0 (rinP c T))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
exists x1.
split; auto.
rewrite H3.
apply cong_tr with (parP P1 (parP x0 (parP (rinP c T) (T x1)))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
auto.
intros.
rewrite H1 in H0.
inversion H0.
intros.
rewrite H1 in H0.
inversion H0.
Qed.

Lemma inv_trans2_single_rinP_cong :
  forall P Q L A b (c : chan A b) T,
    Trans2 (Single (c ??* T)) P L Q ->
    exists R,
      Cong P (parP R (c ??* T)) /\
      (exists v, L = InL c v /\ Cong Q (parP R (parP (c ??* T) (T v)))).
intros.
eapply inv_trans2_single_rinP_cong'.
apply H.
auto.
Qed.

Lemma inv_trans2_single_outP_cong' :
 forall P Q R L,
   Trans2 R P L Q ->
   forall A b (c : chan A b) v T,
     R = Single (c << v >> T) ->
     exists R,
       Cong P (parP R (c << v >> T)) /\ L = OutL c v /\ Cong Q (parP R T).
intros P Q R L H.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
generalize (Single_inj H); intro.
generalize (outP_inj1 H0); intro.
inversion_clear H1.
generalize c v0 H H0; clear c v0 H H0; rewrite <- H2; rewrite <- H3;
 clear H2 H3 A0 b0; intros.
generalize (outP_inj_chan_val H0); intro.
inversion_clear H1.
clear H; generalize H0; clear H0; rewrite <- H2; rewrite <- H3;
 clear H2 H3 v0 c; intros.
injection H0.
intro.
rewrite <- H.
exists zeroP.
split.
ProcCong.
split; auto.
ProcCong.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
generalize (IHTrans2 _ _ _ _ _ H0); intros.
inversion_clear H1.
decompose [and] H2; clear H2.
exists (parP x Q).
split.
apply cong_tr with (parP (parP x (c << v >> T)) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
split; auto.
apply cong_tr with (parP (parP x T) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
intros.
generalize (IHTrans2 _ _ _ _ _ H0); intros.
inversion_clear H1.
decompose [and] H2; clear H2.
exists (parP x Q).
split.
apply cong_tr with (parP Q (parP x (c << v >> T))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
split; auto.
apply cong_tr with (parP Q (parP x T)).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
Qed.

Lemma inv_trans2_single_outP_cong :
 forall P Q L A b (c : chan A b) v T,
   Trans2 (Single (c << v >> T)) P L Q ->
   exists R,
     Cong P (parP R (c << v >> T)) /\ L = OutL c v /\ Cong Q (parP R T).
intros.
eapply inv_trans2_single_outP_cong'.
apply H.
auto.
Qed.

Lemma inv_trans2_pair_outP_rinP_cong' :
 forall R P Q L,
   Trans2 R P L Q ->
   forall A b (c : chan A b) v U T,
     R = Pair (c << v >> U) (c ??* T) ->
     exists R,
       Cong P (parP R (parP (c << v >> U) (c ??* T))) /\
       L = TauL c /\ Cong Q (parP R (parP U (parP (c ??* T) (T v)))).
do 5 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
clear IHTrans0 IHTrans1.
injection H0; intros.
rewrite H2 in H1; rewrite H3 in H.
generalize (inv_trans2_single_outP_cong H); intros.
inversion_clear H4.
decompose [and] H5; clear H5.
generalize (OutL_inj1 H7); intros.
inversion_clear H5.
generalize c v0 T H0 H2 H3 H1 H H4 H7 H8; clear c v0 T H0 H2 H3 H1 H H4 H7 H8;
 rewrite <- H6; rewrite <- H9; clear H6 H9 A0 b0; intros.
generalize (OutL_inj H7); intros.
inversion_clear H5.
generalize T H0 H2 H3 H1 H H4 H7 H8; clear T H0 H2 H3 H1 H H4 H7 H8;
 rewrite <- H6; rewrite <- H9; clear H6 H9 c v0; intros.
clear H7.
generalize (inv_trans2_single_rinP_cong H1); intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
exists (parP x0 x1).
split; auto.
apply cong_tr with (parP (parP x0 (x << v >> U)) (parP x1 (x ??* T))).
apply cong_par.
auto.
auto.
ProcCong.
split; auto.
generalize (InL_inj H7); intros.
inversion_clear H6.
rewrite H11.
apply cong_tr with (parP (parP x0 U) (parP x1 (parP (x ??* T) (T x2)))).
apply cong_par; [ auto | auto ].
ProcCong.
intros.
clear IHTrans0 IHTrans1.
injection H0; intros.
rewrite H2 in H1; rewrite H3 in H.
generalize (inv_trans2_OutL H1); intro X; inversion_clear X.
discriminate H4.
intros.
generalize (IHTrans2 _ _ _ _ _ _ H0); intro X; inversion_clear X.
decompose [and] H1; clear H1.
exists (parP x Q).
split.
apply cong_tr with (parP (parP x (parP (c << v >> U) (c ??* T))) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
split; auto.
apply cong_tr with (parP (parP x (parP U (parP (c ??* T) (T v)))) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
intros.
generalize (IHTrans2 _ _ _ _ _ _ H0); intro X; inversion_clear X.
decompose [and] H1; clear H1.
exists (parP Q x).
split.
apply cong_tr with (parP Q (parP x (parP (c << v >> U) (c ??* T)))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
split; auto.
apply cong_tr with (parP Q (parP x (parP U (parP (c ??* T) (T v))))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
Qed.

Lemma inv_trans2_pair_outP_rinP_cong :
 forall P Q L A b (c : chan A b) v U T,
   Trans2 (Pair (c << v >> U) (c ??* T)) P L Q ->
   exists R,
     Cong P (parP R (parP (c << v >> U) (c ??* T))) /\
     L = TauL c /\ Cong Q (parP R (parP U (parP (c ??* T) (T v)))).
intros.
apply
 (inv_trans2_pair_outP_rinP_cong' H (refl_equal (Pair (c << v >> U) (c ??* T)))).
Qed.

Lemma inv_trans2_pair_rinP_outP_cong' :
 forall R P Q L,
   Trans2 R P L Q ->
   forall A b (c : chan A b) v U T,
     R = Pair (c ??* T) (c << v >> U) ->
     exists R,
       Cong P (parP R (parP (c ??* T) (c << v >> U))) /\
       L = TauL c /\ Cong Q (parP R (parP (parP (c ??* T) (T v)) U)).
do 5 intro.
induction H
 as
  [A b x v P|
   A b x v C|
   A b x v C|
   A x C|
   A x C|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   R1 R2 P P' Q Q' A v b x H IHTrans0 H1 IHTrans1|
   Ps P P' Q L H IHTrans2|
   Ps P P' Q L H IHTrans2].
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
clear IHTrans0 IHTrans1.
injection H0; intros.
rewrite H2 in H1; rewrite H3 in H.
generalize (inv_trans2_single_outP_cong H1); intros.
inversion_clear H4.
decompose [and] H5; clear H5.
discriminate H7.
intros.
clear IHTrans0 IHTrans1.
injection H0; intros.
rewrite H2 in H1; rewrite H3 in H.
generalize (inv_trans2_single_outP_cong H1); intros.
inversion_clear H4.
decompose [and] H5; clear H5.
generalize (OutL_inj1 H7); intros.
inversion_clear H5.
generalize c v0 T H0 H2 H3 H1 H H4 H7 H8; clear c v0 T H0 H2 H3 H1 H H4 H7 H8;
 rewrite <- H6; rewrite <- H9; clear H6 H9 A0 b0; intros.
generalize (OutL_inj H7); intros.
inversion_clear H5.
generalize T H0 H2 H3 H1 H H4 H7 H8; clear T H0 H2 H3 H1 H H4 H7 H8;
 rewrite <- H6; rewrite <- H9; clear H6 H9 c v0; intros.
clear H7.
generalize (inv_trans2_single_rinP_cong H); intros.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
exists (parP x0 x1).
split; auto.
apply cong_tr with (parP (parP x1 (x ??* T)) (parP x0 (x << v >> U))).
apply cong_par.
auto.
auto.
ProcCong.
split; auto.
generalize (InL_inj H7); intros.
inversion_clear H6.
rewrite H11.
apply cong_tr with (parP (parP x1 (parP (x ??* T) (T x2))) (parP x0 U)).
apply cong_par; [ auto | auto ].
ProcCong.
intros.
generalize (IHTrans2 _ _ _ _ _ _ H0); intro X; inversion_clear X.
decompose [and] H1; clear H1.
exists (parP x Q).
split.
apply cong_tr with (parP (parP x (parP (c ??* T) (c << v >> U))) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
split; auto.
apply cong_tr with (parP (parP x (parP (parP (c ??* T) (T v)) U)) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
intros.
generalize (IHTrans2 _ _ _ _ _ _ H0); intro X; inversion_clear X.
decompose [and] H1; clear H1.
exists (parP Q x).
split.
apply cong_tr with (parP Q (parP x (parP (c ??* T) (c << v >> U)))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
split; auto.
apply cong_tr with (parP Q (parP x (parP (parP (c ??* T) (T v)) U))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
Qed.

Lemma inv_trans2_pair_rinP_outP_cong :
 forall P Q L A b (c : chan A b) v U T,
   Trans2 (Pair (c ??* T) (c << v >> U)) P L Q ->
   exists R,
     Cong P (parP R (parP (c ??* T) (c << v >> U))) /\
     L = TauL c /\ Cong Q (parP R (parP (parP (c ??* T) (T v)) U)).
intros.
apply
 (inv_trans2_pair_rinP_outP_cong' H (refl_equal (Pair (c ??* T) (c << v >> U)))).
Qed.

Unset Implicit Arguments.
