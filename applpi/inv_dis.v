Require Import chan.
Require Import applpi.
Require Import inv.

 (** discrimination lemmas, not provided automatically by Coq because of dependent types
(they cause an assertion failure) *)

Set Implicit Arguments.

Lemma inv_trans_parP_obs_rinP_outP_TauL :
 forall (obs : proc) (A : Set) (b : bool) (c : chan A b) 
   (v : A) (T : A -> proc) (U : proc) (B : Set) (b' : bool) 
   (d : chan B b') (P : proc),
 Trans (parP obs (parP (c ??* T) (c << v >> U))) (TauL d) P ->
 (* observer fait out *)
 (exists obs' : proc,
    (exists P' : proc,
       (exists v' : A,
          Trans obs (OutL c v') obs' /\
          Trans (parP (c ??* T) (c << v >> U)) (InL c v') P' /\
          P = parP obs' P'))) \/
 
 (* observer fait in*)
 (exists obs' : proc,
    (exists P' : proc,
       Trans obs (InL c v) obs' /\
       Trans (parP (c ??* T) (c << v >> U)) (OutL c v) P' /\ P = parP obs' P')) \/
 
 (* observer fait tau*)
 (exists obs' : proc,
    Trans obs (TauL d) obs' /\ P = parP obs' (parP (c ??* T) (c << v >> U)))
 (* comm on the ready to communicate couple *)
  \/ P = parP obs (parP (parP (c ??* T) (T v)) U).
intros.
generalize (inv_trans_tau H); intro X; inversion_clear X.
inversion_clear H0.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
decompose [and] H2; clear H2.
left.
exists x1.
injection H0; intros.
rewrite <- H2 in H4.
inversion H4.
generalize (inv_trans_rinP1 H10); intros.
subst A x2 L Q P0.
generalize (inv_trans_rinP_bool H10); intros.
subst b'.
generalize (inv_trans_rinP_chan H10); intros.
subst d.
exists (parP (parP (c ??* T) (T x3)) (c << v >> U)).
exists x3.
injection H0; clear H0; intros; subst x x0.
split; auto.
split.
apply tr_parL.
apply tr_rin.
rewrite H5.
generalize (inv_trans_rinP_cont H10); intros.
subst P'.
auto.
inversion_clear H10.
inversion_clear H1.
inversion_clear H2.
decompose [and] H1; clear H1.
right; left.
injection H0; clear H0; intros; subst x x0.
inversion H2.
inversion_clear H7.
subst x2 L P0 Q.
generalize (inv_trans_outP1 H7); intros.
subst B.
generalize (inv_trans_outP_bool H7); intros.
subst b'.
generalize (inv_trans_outP_chan_val H7); intro X; inversion_clear X.
subst d x3.
exists x1.
exists (parP (c ??* T) U).
split; auto.
split.
apply tr_parR.
apply tr_out.
rewrite H5.
generalize (inv_trans_outP_cont H7); intro.
subst U.
auto.
inversion_clear H2.
inversion_clear H1.
right; right; left.
exists x1.
split.
injection H0; intros.
rewrite H4; auto.
injection H0; intros.
rewrite H1; auto.
inversion_clear H1.
right; right; right.
injection H0; intros.
rewrite <- H1 in H2.
generalize (inv_trans_tau H2); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
decompose [and] H7; clear H7.
injection H5; intros.
rewrite <- H8 in H6.
inversion_clear H6.
inversion_clear H6.
inversion_clear H7.
decompose [and] H6; clear H6.
injection H5; clear H5; intros; subst x3 x4.
generalize (inv_trans_outP1 H7); intro.
subst B.
generalize (inv_trans_outP_bool H7); intro.
subst b'.
generalize (inv_trans_outP_chan_val H7); intro X; inversion_clear X.
subst d x7.
generalize (inv_trans_outP_cont H7); intro.
generalize (inv_trans_rinP_cont H9); intro.
subst x6 x5 x2 x x0 P.
auto.
inversion_clear H7.
inversion_clear H6.
injection H5; clear H5; intros; subst x3 x4.
inversion_clear H7.
inversion_clear H6.
injection H5; clear H5; intros; subst x3 x4.
inversion_clear H7.
Qed.


