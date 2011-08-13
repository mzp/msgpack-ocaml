Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import inv.
Require Import cong.
Require Import cong_resp.

Set Implicit Arguments.

Lemma Cong_outP_parP_inP :
 forall A b (c : chan A b) v P B b' (d : chan B b') (w:B) (*B is not tempty*) Q R,
 Cong (c << v >> P) (parP (d ?? Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_fresh B nilC); intros.
inversion_clear H0.
lapply (H2 (InL d w) (parP (Q w) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion_clear H0.
apply tr_parL.
apply tr_in.
Qed.

Lemma Cong_outP_parP_rinP :
 forall A b (c : chan A b) v P B b' (d : chan B b') (w : B) (*B is not tempty*) Q R,
 Cong (c << v >> P) (parP (d ??* Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_fresh B nilC); intros.
inversion_clear H0.
lapply (H2 (InL d w) (parP (parP (d ??* Q) (Q w)) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion_clear H0.
apply tr_parL.
apply tr_rin.
Qed.

Lemma Cong_outP_parP_nuP :
 forall A b (c : chan A b) v P B (Q : chan B false -> proc) R, 
   Cong (c << v >> P) (parP (nuP Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_fresh B nilC); intros.
inversion_clear H0.
lapply (H2 (NewL x) (parP (Q x) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion H0.
apply tr_parL.
apply tr_new.
Qed.

Lemma Cong_outP_parP_nuPl :
 forall A b (c : chan A b) v P B (Q : chan B true -> proc) R,
   Cong (c << v >> P) (parP (nuPl Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_freshl B nilC); intros.
inversion_clear H0.
lapply (H2 (NewL x) (parP (Q x) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion H0.
apply tr_parL.
apply tr_newl.
Qed.

Lemma Cong_inP_parP_nuPl :
  forall A b (c : chan A b) P B (Q : chan B true -> proc) R,
    Cong (c ?? P) (parP (nuPl Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_freshl B nilC); intros.
inversion_clear H0.
lapply (H2 (NewL x) (parP (Q x) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion H0.
apply tr_parL.
apply tr_newl.
Qed.

Lemma Cong_inP_parP_nuP :
  forall A b (c : chan A b) P B (Q : chan B false -> proc) R,
    Cong (c ?? P) (parP (nuP Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_fresh B nilC); intros.
inversion_clear H0.
lapply (H2 (NewL x) (parP (Q x) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion H0.
apply tr_parL.
apply tr_new.
Qed.

Lemma Cong_inP_parP_outP :
 forall A b (c : chan A b) P B b' (d : chan B b') w Q R,
 Cong (c ?? P) (parP (d << w >> Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
elim H0; intros.
lapply (H2 (OutL d w) (parP Q R)).
intro.
inversion_clear H3.
inversion_clear H4.
inversion H3.
apply tr_parL.
apply tr_out.
Qed.

Lemma Cong_rinP_parP_outP :
  forall A b (c : chan A b) P B b' (d : chan B b') w Q R,
    Cong (c ??* P) (parP (d << w >> Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
elim H0; intros.
lapply (H2 (OutL d w) (parP Q R)).
intro.
inversion_clear H3.
inversion_clear H4.
inversion H3.
auto.
apply tr_parL.
apply tr_out.
Qed.

Lemma Cong_rinP_parP_nuP :
  forall A b (c : chan A b) P B (Q : chan B false -> proc) R,
    Cong (c ??* P) (parP (nuP Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_fresh B nilC); intros.
inversion_clear H0.
lapply (H2 (NewL x) (parP (Q x) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion H0.
apply tr_parL.
apply tr_new.
Qed.

Lemma Cong_rinP_parP_nuPl :
  forall A b (c : chan A b) P B (Q : chan B true -> proc) R,
    Cong (c ??* P) (parP (nuPl Q) R) -> False.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
generalize (choose_freshl B nilC); intros.
inversion_clear H0.
lapply (H2 (NewL x) (parP (Q x) R)).
intros.
inversion_clear H0.
inversion_clear H4.
inversion H0.
apply tr_parL.
apply tr_newl.
Qed.

Lemma Cong_outP_parP_outP0 :
  forall A b (c : chan A b) v P B b' (d : chan B b') w P' Q, 
    Cong (c << v >> P) (parP (d << w >> P') Q) -> A = B.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
lapply (H1 (OutL c v) P).
intro.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
generalize (inv_trans_outP1 H3); intro.
auto.
lapply (H2 (OutL d w) (parP P' Q)).
intro X; inversion_clear X.
inversion_clear H0.
generalize (inv_trans_outP1 H5); intro.
auto.
apply tr_parL.
apply tr_out.
apply tr_out.
Qed.

Lemma Cong_outP_parP_outP_bool :
  forall A b (c : chan A b) v P b' (d : chan A b') w P' Q,
    Cong (c << v >> P) (parP (d << w >> P') Q) -> b = b'.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
lapply (H1 (OutL c v) P).
intro.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
generalize (inv_trans_outP_bool H3); intro.
auto.
lapply (H2 (OutL d w) (parP P' Q)).
intro X; inversion_clear X.
inversion_clear H0.
generalize (inv_trans_outP_bool H5); intro.
auto.
apply tr_parL.
apply tr_out.
apply tr_out.
Qed.

Lemma Cong_outP_parP_outP_chan_val :
  forall A b (c d : chan A b) v w P P' Q,
    Cong (c << v >> P) (parP (d << w >> P') Q) -> c = d /\ v = w.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
lapply (H1 (OutL c v) P).
intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H3.
generalize (inv_trans_outP_chan_val H0); intro.
inversion_clear H3.
auto.
lapply (H2 (OutL d w) (parP P' Q)).
intro.
inversion_clear H3.
inversion_clear H5.
generalize (inv_trans_outP_chan_val H3); intro.
auto.
apply tr_parL.
apply tr_out.
apply tr_out.
Qed.

Lemma Cong_inP_parP_inP0 :
  forall A b (c : chan A b) P B b' (d : chan B b') P' Q,
    Cong (c ?? P) (parP (d ?? P') Q) -> 
    forall w : B,(*B is not empty*) A = B.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (P' w) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_inP1 H3).
apply tr_parL.
apply tr_in.
Qed.

Lemma Cong_inP_parP_inP_bool :
 forall A b (c : chan A b) P b' (d : chan A b') P' Q,
   Cong (c ?? P) (parP (d ?? P') Q) -> 
   forall w : A,(*A is not empty*) b = b'.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (P' w) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_inP_bool H3).
apply tr_parL.
apply tr_in.
Qed.

Lemma Cong_inP_parP_inP_chan :
  forall A b (c d : chan A b) P P' Q,
    Cong (c ?? P) (parP (d ?? P') Q) -> 
    forall v : A,(*A not empty*) c = d.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
lapply (H1 (InL c v) (P v)).
intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H3.
generalize (inv_trans_inP_chan H0); intro.
inversion_clear H3.
auto.
lapply (H2 (InL d v) (parP (P' v) Q)).
intro.
inversion_clear H3.
inversion_clear H5.
generalize (inv_trans_inP_chan H3); intro.
auto.
apply tr_parL.
apply tr_in.
apply tr_in.
Qed.

Lemma Cong_inP_parP_rinP0 :
 forall A b (c : chan A b) P B b' (d : chan B b') P' Q, 
   Cong (c ?? P) (parP (d ??* P') Q) -> 
   forall w : B, A = B.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (parP (d ??* P') (P' w)) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_inP1 H3).
apply tr_parL.
apply tr_rin.
Qed.

Lemma Cong_inP_parP_rinP_bool :
  forall A b (c : chan A b) P b' (d : chan A b') P' Q,
    Cong (c ?? P) (parP (d ??* P') Q) -> 
    forall w : A,(*A is not empty*) b = b'.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (parP (d ??* P') (P' w)) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_inP_bool H3).
apply tr_parL.
apply tr_rin.
Qed.

Lemma Cong_inP_parP_rinP_chan :
  forall A b (c d : chan A b) P P' Q,
    Cong (c ?? P) (parP (d ??* P') Q) -> 
    forall v : A,(*A not empty*) c = d.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
lapply (H1 (InL c v) (P v)).
intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H3.
generalize (inv_trans_rinP_chan H0); intro.
inversion_clear H3.
auto.
lapply (H2 (InL d v) (parP (parP (d ??* P') (P' v)) Q)).
intro.
inversion_clear H3.
inversion_clear H5.
generalize (inv_trans_inP_chan H3); intro.
auto.
apply tr_parL.
apply tr_rin.
apply tr_in.
Qed.

Lemma Cong_rinP_parP_inP0 :
 forall A b (c : chan A b) P B b' (d : chan B b') P' Q, 
   Cong (c ??* P) (parP (d ?? P') Q) -> 
   forall w : B, A = B.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (P' w) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_rinP1 H3).
apply tr_parL.
apply tr_in.
Qed.

Lemma Cong_rinP_parP_inP_bool :
  forall A b (c : chan A b) P b' (d : chan A b') P' Q,
    Cong (c ??* P) (parP (d ?? P') Q) -> 
    forall w : A,(*A is not empty*) b = b'.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (P' w) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_rinP_bool H3).
apply tr_parL.
apply tr_in.
Qed.

Lemma Cong_rinP_parP_inP_chan :
  forall A b (c d : chan A b) P P' Q,
    Cong (c ??* P) (parP (d ?? P') Q) -> 
    forall v : A,(*A not empty*) c = d.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
lapply (H1 (InL c v) (parP (c ??* P) (P v))).
intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H3.
generalize (inv_trans_inP_chan H0); intro.
inversion_clear H3.
auto.
lapply (H2 (InL d v) (parP (P' v) Q)).
intro.
inversion_clear H3.
inversion_clear H5.
generalize (inv_trans_rinP_chan H3); intro.
auto.
apply tr_parL.
apply tr_in.
apply tr_rin.
Qed.

Lemma Cong_rinP_parP_rinP0 :
  forall A b (c : chan A b) P B b' (d : chan B b') P' Q, 
    Cong (c ??* P) (parP (d ??* P') Q) -> 
    forall w : B, A = B.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (parP (d ??* P') (P' w)) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_rinP1 H3).
apply tr_parL.
apply tr_rin.
Qed.

Lemma Cong_rinP_parP_rinP_bool :
 forall A b (c : chan A b) P b' (d : chan A b') P' Q,
   Cong (c ??* P) (parP (d ??* P') Q) -> 
   forall w : A,(*A is not empty*) b = b'.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL d w) (parP (parP (d ??* P') (P' w)) Q)).
intro X; inversion_clear X.
inversion_clear H2.
apply (inv_trans_rinP_bool H3).
apply tr_parL.
apply tr_rin.
Qed.

Lemma Cong_rinP_parP_rinP_chan :
  forall A b (c d : chan A b) P P' Q,
    Cong (c ??* P) (parP (d ??* P') Q) -> 
    forall v : A,(*A not empty*) c = d.
intros.
generalize (cong_respects_trans_k H); intro.
inversion_clear H0.
lapply (H1 (InL c v) (parP (c ??* P) (P v))).
intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H3.
generalize (inv_trans_rinP_chan H0); intro.
inversion_clear H3.
auto.
lapply (H2 (InL d v) (parP (parP (d ??* P') (P' v)) Q)).
intro.
inversion_clear H3.
inversion_clear H5.
generalize (inv_trans_rinP_chan H3); intro.
auto.
apply tr_parL.
apply tr_rin.
apply tr_rin.
Qed.

Unset Implicit Arguments.

