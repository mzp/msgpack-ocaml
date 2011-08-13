Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import inv.
Require Import cong.
Require Import Classical.
Require Import Classical_Pred_Set.

 (** we show that transition/reduction properties (e.g., existence of a successor) are preserved modulo structural congruence *)

(** main lemma *)

Set Implicit Arguments.

Lemma cong_respects_trans_k :
 forall P P',
 Cong P P' ->
 (forall l Q,
  Trans P l Q -> exists Q', Trans P' l Q' /\ Cong Q Q') /\
 (forall l Q',
  Trans P' l Q' -> exists Q, Trans P l Q /\ Cong Q Q').
intros.
induction H
 as
  [P|
   P Q|
   P Q R|
   P Q P' Q' H IHCong1 H1 IHCong2|
   A b x C|
   P|
   P Q H IHCong|
   P Q R H IHCong1 H1 IHCong2].
(* case for the zero rule *)
split.
intros.
exists (parP Q zeroP).
split.
apply tr_parL.
auto.
apply cong_zero.
intros.
inversion H.
inversion H5.
inversion H5.
exists P'.
split; [ auto | apply cong_zero ].
inversion H4.
(* case for the comm rule *)
split.
intros.
inversion H.
clear H0 H1 P0 Q1.
exists (parP Q' P').
split.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_comm.
exists (parP Q' P').
split.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_comm.
exists (parP Q P').
split.
apply tr_parR.
auto.
apply cong_comm.
exists (parP P' P).
split.
apply tr_parL.
auto.
apply cong_comm.
intros.
inversion H.
exists (parP Q'0 P').
split.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_comm.
exists (parP Q'0 P').
split.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_comm.
exists (parP P P').
split.
apply tr_parR.
auto.
apply cong_comm.
exists (parP P' Q).
split.
apply tr_parL.
auto.
apply cong_comm.
(* cas de la regle assoc *)
split.
intros.
inversion H.
inversion H2.
exists (parP P'0 (parP Q Q')).
split.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
apply tr_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
apply tr_parR.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_assoc.
inversion H2.
exists (parP P'0 (parP Q Q')).
split.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
apply tr_parR.
auto.
apply cong_assoc.
exists (parP P (parP P'0 Q')).
split.
apply tr_parR.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_assoc.
inversion H4.
exists (parP P'0 (parP Q' R)).
split.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
apply tr_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q' R)).
split.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
apply tr_parL.
auto.
apply cong_assoc.
exists (parP P'0 (parP Q R)).
split.
apply tr_parL.
auto.
apply cong_assoc.
exists (parP P (parP P'0 R)).
split.
apply tr_parR.
apply tr_parL.
auto.
apply cong_assoc.
exists (parP P (parP Q P')).
split.
apply tr_parR.
apply tr_parR.
auto.
apply cong_assoc.
intros.
inversion H.
inversion H5.
exists (parP (parP P' P'0) R).
split.
apply tr_parL.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
apply tr_comOI with (A := A) (x := x) (v := v).
apply tr_parL.
auto.
auto.
apply cong_assoc.
inversion H5.
exists (parP (parP P' P'0) R).
split.
apply tr_parL.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_assoc.
exists (parP (parP P' Q) P'0).
split.
apply tr_comIO with (A := A) (x := x) (v := v).
apply tr_parL.
auto.
auto.
apply cong_assoc.
exists (parP (parP P' Q) R).
split.
apply tr_parL.
apply tr_parL.
auto.
apply cong_assoc.
inversion H4.
exists (parP (parP P P'0) Q'0).
split.
apply tr_comOI with (A := A) (x := x) (v := v).
apply tr_parR.
auto.
auto.
apply cong_assoc.
exists (parP (parP P P'0) Q'0).
split.
apply tr_comIO with (A := A) (x := x) (v := v).
apply tr_parR.
auto.
auto.
apply cong_assoc.
exists (parP (parP P P'0) R).
split.
apply tr_parL.
apply tr_parR.
auto.
apply cong_assoc.
exists (parP (parP P Q) P'0).
split.
apply tr_parR.
auto.
apply cong_assoc.
(* cas de la regle par *)
split.
intros.
inversion H0.
clear H3 H2 Q1 P0.
inversion_clear IHCong1.
generalize (H2 _ _ H4); intro X; inversion_clear X.
inversion_clear H8.
inversion_clear IHCong2.
generalize (H8 _ _ H7); intro X; inversion_clear X.
inversion_clear H12.
exists (parP x0 x1).
split.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong1.
inversion_clear IHCong2.
generalize (H8 _ _ H4); intro X; inversion_clear X.
generalize (H10 _ _ H7); intro X; inversion_clear X.
decompose [and] H12; decompose [and] H13; clear H12; clear H13.
exists (parP x0 x1).
split.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong1.
generalize (H7 _ _ H6); intro X; inversion_clear X.
decompose [and] H9; clear H9.
exists (parP x Q').
split.
apply tr_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong2.
generalize (H7 _ _ H6); intro X; inversion_clear X.
inversion_clear H9.
exists (parP P' x).
split.
apply tr_parR.
auto.
apply cong_par.
auto.
auto.
intros.
inversion H0.
inversion_clear IHCong1.
inversion_clear IHCong2.
generalize (H9 _ _ H4); intro X; inversion_clear X.
decompose [and] H12; clear H12.
generalize (H11 _ _ H7); intro X; inversion_clear X.
decompose [and] H12; clear H12.
exists (parP x0 x1).
split.
apply tr_comOI with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong1.
inversion_clear IHCong2.
generalize (H9 _ _ H4); intro X; inversion_clear X.
decompose [and] H12; clear H12.
generalize (H11 _ _ H7); intro X; inversion_clear X.
decompose [and] H12; clear H12.
exists (parP x0 x1).
split.
apply tr_comIO with (A := A) (x := x) (v := v).
auto.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong1.
generalize (H8 _ _ H6); intro X; inversion_clear X.
decompose [and] H9; clear H9.
exists (parP x Q).
split.
apply tr_parL.
auto.
apply cong_par.
auto.
auto.
inversion_clear IHCong2.
generalize (H8 _ _ H6); intro X; inversion_clear X.
decompose [and] H9; clear H9.
exists (parP P x).
split.
apply tr_parR.
auto.
apply cong_par.
auto.
auto.
(* cas de la replication *)
split.
intro l.
case l.
intros.
inversion H.
intros.
generalize (inv_trans_rinP1 H); intro.
generalize c a H.
clear c a H.
rewrite <- H0.
clear H0 A0.
intros.
generalize (inv_trans_rinP_bool H).
intro X.
generalize c H; clear c H; rewrite <- X; clear X b0; intros.
generalize (inv_trans_rinP_chan H).
intro X; rewrite X in H; rewrite X; clear X x.
generalize (inv_trans_rinP_cont H); intro.
rewrite H0 in H.
exists (parP (c ??* C) (C a)).
split.
apply tr_parR.
apply tr_in.
rewrite H0.
apply cong_refl.
intros.
inversion H.
intros.
inversion H.
intros.
inversion H.
inversion H2.
inversion H5.
clear H1 H2 H0 L Q P.
generalize H H4; clear H H4.
case l.
intros.
inversion H4.
intros.
generalize (inv_trans_rinP1 H4).
intro.
generalize c a H H4.
clear c a H H4.
rewrite <- H0.
clear H0 A0.
intros.
generalize (inv_trans_rinP_bool H4).
intro X; generalize c H H4; clear c H H4; rewrite <- X; clear X b0; intros.
generalize (inv_trans_rinP_chan H4).
intro X; rewrite X in H; rewrite X in H4; rewrite X in H3; rewrite X;
 clear X x.
generalize (inv_trans_rinP_cont H4); intro.
exists P'.
split.
rewrite H0.
apply tr_rin.
rewrite H0.
apply cong_tr with (Q := parP (parP (c ??* C) (c ?? C)) (C a)).
apply cong_par.
apply cong_rep.
apply cong_refl.
apply cong_tr with (Q := parP (c ??* C) (parP (c ?? C) (C a))).
apply cong_assoc.
apply cong_tr with (Q := parP (c ??* C) (parP (C a) (c ?? C))).
apply cong_par.
apply cong_refl.
apply cong_comm.
apply cong_sym.
apply cong_assoc.
intros.
inversion H4.
intros.
inversion H4.
clear H1 H2 H0 P Q L.
generalize H H4; clear H H4.
case l.
intros.
inversion H4.
intros.
generalize (inv_trans_inP1 H4); intro.
generalize c a H H4.
clear c a H H4.
rewrite <- H0; clear H0 A0.
intros.
generalize (inv_trans_inP_bool H4); intro.
generalize c H H4; clear c H H4; rewrite <- H0; clear H0 b0; intros.
generalize (inv_trans_inP_chan H4); intro.
rewrite <- H0 in H; rewrite <- H0 in H4; rewrite <- H0.
clear H0 c.
generalize (inv_trans_inP_cont H4); intro.
exists (parP (x ??* C) (C a)).
split.
apply tr_rin.
rewrite H0.
apply cong_refl.
intros.
inversion H4.
intros.
inversion H4.
(* case de la reflexion *)
split.
intros.
exists Q.
split.
auto.
apply cong_refl.
intros.
exists Q'.
split.
auto.
apply cong_refl.
(* case de la symetrie *)
split.
intros.
inversion_clear IHCong.
generalize (H2 _ _ H0); intro X; inversion_clear X.
decompose [and] H3; clear H3.
exists x.
split; [ auto | apply cong_sym; auto ].
intros.
inversion_clear IHCong.
generalize (H1 _ _ H0); intro X; inversion_clear X.
decompose [and] H3; clear H3.
exists x.
split; [ auto | apply cong_sym; auto ].
(* cas de la transitivity *)
split.
intros.
inversion_clear IHCong1.
generalize (H2 _ _ H0); intro X; inversion_clear X.
decompose [and] H4; clear H4.
inversion_clear IHCong2.
generalize (H4 _ _ H5); intro X; inversion_clear X.
decompose [and] H8; clear H8.
exists x0.
split.
auto.
apply cong_tr with (Q := x).
auto.
auto.
intros.
inversion_clear IHCong2.
generalize (H3 _ _ H0); intro X; inversion_clear X.
decompose [and] H4; clear H4.
inversion_clear IHCong1.
generalize (H7 _ _ H5); intro X; inversion_clear X.
decompose [and] H8; clear H8.
exists x0.
split.
auto.
apply cong_tr with (Q := x).
auto.
auto.
Qed.

Lemma cong_respects_trans :
 forall P Q l,
 Trans P l Q ->
 forall P', Cong P P' -> exists Q', Trans P' l Q' /\ Cong Q Q'.
intros.
generalize (cong_respects_trans_k H0); intro.
decompose [and] H1; clear H1.
apply H2.
auto.
Qed.

(** structural congruence of states (reminder: a state is a list of channels + a process), two states are structurally congruent when the lists are the same and the processes are structurally congruent *)

Definition Cong_st (P P' : state) :=
  fstT P = fstT P' /\ Cong (sndT P) (sndT P').

Lemma Cong_st_sym : forall p p', Cong_st p p' -> Cong_st p' p.
unfold Cong_st in |- *.
intros.
intuition.
apply cong_sym; auto.
Qed.

Lemma cong_respects_redwith :
 forall P Q l,
 Redwith P l Q ->
 forall P',
 Cong_st P P' -> 
 exists Q', Redwith P' l Q' /\ Cong_st Q Q'.
intros P Q l H.
inversion H.
intros.
red in H4.
inversion_clear H4.
generalize (cong_respects_trans H0 H6).
intro X; inversion_clear X.
inversion_clear H4.
exists (fstT P' # x0).
split.
induction P'.
simpl in |- *.
apply red_com.
simpl in H6.
auto.
split.
simpl in |- *.
auto.
simpl in |- *.
auto.
intros.
red in H5.
inversion_clear H5.
generalize (cong_respects_trans H0 H7).
intro X; inversion_clear X.
inversion_clear H5.
exists (x & fstT P' # x0).
split.
induction P'.
simpl in |- *.
apply red_new.
simpl in H8.
auto.
simpl in H6.
rewrite <- H6.
auto.
split.
simpl in |- *.
rewrite <- H6.
simpl in |- *.
auto.
simpl in |- *.
auto.
Qed.

Lemma cong_respects_red :
 forall P Q,
 Red P Q ->
 forall P',
 Cong_st P P' -> 
 exists Q', Red P' Q' /\ Cong_st Q Q'.
intros P Q H.
unfold Red in H.
inversion_clear H.
intros.
generalize (cong_respects_redwith H0 H); intro X; inversion_clear X.
inversion_clear H1.
exists x0.
split.
exists x.
auto.
auto.
Qed.

Lemma cong_respects_reds' :
 forall P Q,
 Reds' P Q ->
 forall P',
 Cong_st P P' -> exists Q', Reds' P' Q' /\ Cong_st Q Q'.
intros P Q H.
induction H.
intros.
exists P'.
split.
apply reds_b'.
auto.
intros.
generalize (IHReds' _ H1); intro.
inversion_clear H2.
inversion_clear H3.
generalize (cong_respects_red H0 H4).
intros.
inversion_clear H3.
inversion_clear H5.
exists x0.
split.
apply reds_i' with x.
auto.
auto.
auto.
Qed.

Lemma cong_respects_reds :
 forall P Q,
 Reds P Q ->
 forall P',
 Cong_st P P' -> 
 exists Q', Reds P' Q' /\ Cong_st Q Q'.
intros.
assert (Reds' P Q).
generalize (reds_reds' P Q); intro X; inversion_clear X.
auto.
generalize (cong_respects_reds' H1 H0); intros.
inversion_clear H2.
inversion_clear H3.
exists x.
split.
generalize (reds_reds' P' x); intro X; inversion_clear X.
auto.
auto.
Qed.

(** application: any process structurally congruent to a process able to perform a Out action is also able to perform a Out action*)

Lemma all_trans_out_cong :
 forall P Q,
 Cong P Q ->
 forall A b (c : chan A b),
 (forall l P',
  Trans P l P' -> exists v, l = OutL c v) ->
 forall l Q', Trans Q l Q' -> 
   exists v, l = OutL c v.
intros.
apply NNPP.
intro.
generalize
 (not_ex_all_not _ (fun v : A => l = OutL c v) H2); 
 intro.
generalize (cong_respects_trans H1 (cong_sym H)); intro.
inversion_clear H4.
inversion_clear H5.
generalize (H0 _ _ H4); intro.
inversion_clear H5.
generalize (H3 x0); intro.
apply H5; auto.
Qed.

Unset Implicit Arguments.

