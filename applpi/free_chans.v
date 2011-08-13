Require Import Classical.
Require Import JMeq.
Require Import util.
Require Import chan.
Require Import chanlist.
Require Import fresh.
Require Import applpi.
Require Import inj.
Require Import inv.
Require Import cong.
Require Import cong_trans.

Set Implicit Arguments.

(** non occurrence of a channel in a process *)

Inductive notinp (A:Set) (b:bool) (c : chan A b) : proc -> Prop :=
  | zero_notin : notinp c zeroP
  | in_notin : forall B b' (d : chan B b') C,
      ~ c &&& d ->
      (forall x, ~ (x %% c) -> notinp c (C x)) -> notinp c (d ?? C)
  | rin_notin : forall B b' (d : chan B b') C,
      ~ c &&& d ->
      (forall x, ~ (x %% c) -> notinp c (C x)) -> notinp c (d ??* C)
  | out_notin : forall B b' (d : chan B b') v C,
      ~ c &&& d -> ~ (c %% v) -> notinp c C -> notinp c (d << v >> C)
  | par_notin : forall P Q,
    notinp c P -> notinp c Q -> notinp c (parP P Q)
  | nu_notin : forall B (C : chan B false -> proc),
      (forall d, ~ c &&& d -> notinp c (C d)) ->
      notinp c (nuP C)
  | nul_notin : forall B (C : chan B true -> proc),
      (forall d, ~ c &&& d -> notinp c (C d)) ->
      notinp c (nuPl C).

(** inversion lemmas for the notinp predicate *)

Lemma inv_out_notinp' :
 forall A b (c : chan A b) P,
 notinp c P ->
 forall B b' (d : chan B b') v C,
 P = d << v >> C -> ~ c &&& d /\ ~ (c %% v) /\ notinp c C.
intros A b c P H.
induction H
 as
  [|
   B b' d C H H0 H1|
   B b' d C H H0 H1|
   B b' d v C H H0 H1 IHnotinp|
   P Q H IHnotinp1 H1 IHnotinp2|
   B C H H0|
   B C H H0].
intros.
discriminate H.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
generalize (outP_inj1 H2); intros.
inversion_clear H3.
generalize d0 v0 H2; clear d0 v0 H2; rewrite <- H4; rewrite <- H5;
 clear H4 H5 B0 b'0; intros.
generalize (outP_inj_chan_val H2); intros.
inversion_clear H3.
generalize H2; clear H2; rewrite <- H4; rewrite <- H5; clear H4 H5 d0 v0;
 intros.
generalize (outP_inj_cont H2); intros.
rewrite <- H3; auto.
intros.
discriminate H0.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma inv_out_notinp :
 forall A b (c : chan A b) B b' (d : chan B b') v C,
   notinp c (d << v >> C) -> ~ c &&& d /\ ~ (c %% v) /\ notinp c C.
intros.
eapply inv_out_notinp'.
apply H.
auto.
Qed.

Lemma inv_in_notinp' :
    forall A b (c : chan A b) P,
    notinp c P ->
    forall B b' (d : chan B b') C,
    P = d ?? C -> ~ c &&& d /\ (forall x, ~ (x %% c) -> notinp c (C x)).
induction 1; intros.
discriminate H.
generalize (inP_inj1 H2); intros.
inversion_clear H3.
subst B0 b'0.
generalize (inP_inj_chan H2); intros.
subst d0.
generalize (inP_inj_cont H2); intros.
subst C0.
split; auto.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
Qed.

Lemma inv_in_notinp :
 forall A b (c : chan A b) B b' (d : chan B b') C,
 notinp c (d ?? C) ->
 ~ c &&& d /\ (forall x, ~ (x %% c) -> notinp c (C x)).
intros.
eapply inv_in_notinp'.
apply H.
auto.
Qed.

Lemma inv_rin_notinp' :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall B b' (d : chan B b') C,
      P = d ??* C -> ~ c &&& d /\ (forall x, ~ (x %% c) -> notinp c (C x)).
induction 1; intros; try discriminate.
generalize (rinP_inj1 H2); intros.
inversion_clear H3.
subst B0 b'0.
generalize (rinP_inj_chan H2); intros.
subst d0.
generalize (rinP_inj_cont H2); intros.
subst C0.
split; auto.
Qed.

Lemma inv_rin_notinp :
  forall A b (c : chan A b) B b' (d : chan B b') C,
    notinp c (d ??* C) ->
    ~ c &&& d /\ (forall x, ~ (x %% c) -> notinp c (C x)).
intros.
eapply inv_rin_notinp'.
apply H.
auto.
Qed.

Lemma inv_nul_notin' :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall B (C : chan B true -> proc),
      P = nuPl C -> forall d, ~ c &&& d -> notinp c (C d).
induction 1; intros; try discriminate.
generalize (nuPl_inj1 H1); intro.
subst B0.
generalize (nuPl_inj_cont H1); intro.
subst C0.
apply H.
auto.
Qed.

Lemma inv_nul_notin :
  forall A b (c : chan A b) B (C : chan B true -> proc),
    notinp c (nuPl C) ->
    forall d, ~ c &&& d -> notinp c (C d).
intros.
apply inv_nul_notin' with (d := d) (P := nuPl C).
auto.
auto.
auto.
Qed.

Lemma inv_nu_notin' :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall B (C : chan B false -> proc),
      P = nuP C ->
      forall d, ~ c &&& d -> notinp c (C d).
induction 1; intros; try discriminate.
generalize (nuP_inj1 H1); intro.
subst B0.
generalize (nuP_inj_cont H1); intro.
subst C0.
apply H.
auto.
Qed.

Lemma inv_nu_notin :
  forall A b (c : chan A b) B (C : chan B false -> proc),
    notinp c (nuP C) ->
    forall d, ~ c &&& d -> notinp c (C d).
intros.
apply inv_nu_notin' with (d := d) (P := nuP C).
auto.
auto.
auto.
Qed.

(** occurrence of a channel in a process *)

Definition isinp A b (c : chan A b) p : Prop := ~ notinp c p.

Lemma in_isinp :
 forall A b (c : chan A b) P A' b' (d : chan A' b'),
   (exists z, ~ (z %% d) /\ isinp d (P z)) -> isinp d (c ?? P).
intros.
inversion_clear H.
inversion_clear H0.
intro X; generalize (inv_in_notinp X); clear X; intro X;
 inversion_clear X.
generalize (H2 _ H); intro.
apply H1; auto.
Qed.

Lemma rin_isinp :
  forall A b (c : chan A b) P A' b' (d : chan A' b'),
    (exists z, ~ (z %% d) /\ isinp d (P z)) -> isinp d (c ??* P).
intros.
inversion_clear H.
inversion_clear H0.
intro X; generalize (inv_rin_notinp X); clear X; intro X;
 inversion_clear X.
generalize (H2 _ H); intro.
apply H1; auto.
Qed.

(** inversion lemmas *)

Lemma inv_out_isinp :
 forall A b (c : chan A b) v P A' b' (d : chan A' b'),
   isinp d (c << v >> P) -> d &&& c \/ (d %% v) \/ isinp d P.
intros.
apply NNPP; intro.
apply H.
generalize (not_or_and _ _ H0); intro.
inversion_clear H1.
generalize (not_or_and _ _ H3); intro.
inversion_clear H1.
apply out_notin.
auto.
auto.
unfold isinp in H5.
apply (NNPP _ H5).
Qed.

Lemma inv_in_isinp :
 forall A b (c : chan A b) P A' b' (d : chan A' b'),
 isinp d (c ?? P) -> d &&& c \/ (exists z, ~ (z %% d) /\ isinp d (P z)).
intros.
apply NNPP; intro.
apply H.
generalize (not_or_and _ _ H0); intro.
inversion_clear H1.
apply in_notin.
auto.
intros.
apply NNPP; intro.
apply H3; exists x.
split; auto.
Qed.

Lemma inv_rin_isinp :
 forall A b (c : chan A b) P A' b' (d : chan A' b'),
 isinp d (c ??* P) -> d &&& c \/ (exists z, ~ (z %% d) /\ isinp d (P z)).
intros.
apply NNPP; intro.
apply H.
generalize (not_or_and _ _ H0); intro.
inversion_clear H1.
apply rin_notin.
auto.
intros.
apply NNPP; intro.
apply H3; exists x.
split; auto.
Qed.

Lemma inv_par_isinp :
  forall A b (c : chan A b) P Q,
    isinp c (parP P Q) -> isinp c P \/ isinp c Q.
intros.
apply NNPP; intro.
apply H.
apply par_notin.
generalize (not_or_and _ _ H0); intro.
inversion_clear H1.
unfold isinp in H2; apply NNPP; auto.
generalize (not_or_and _ _ H0); intro.
inversion_clear H1.
unfold isinp in H3; apply NNPP; auto.
Qed.

Lemma inv_nu_isinp :
 forall A (P : chan A false -> proc) A' b' (d : chan A' b'),
   isinp d (nuP P) -> exists z, ~ z &&& d /\ isinp d (P z).
intros.
apply NNPP; intro.
apply H.
apply nu_notin.
intros.
apply NNPP; intro.
apply H0.
exists d0.
auto.
Qed.

(** occurrence checks / cong *)

Lemma cong_respects_notinp' :
  forall P Q,
    Cong P Q ->
    forall A b (c : chan A b), notinp c P <-> notinp c Q.
do 3 intro.
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
split; intros.
apply par_notin.
auto.
apply zero_notin.
inversion_clear H.
auto.
split; intros.
inversion_clear H.
apply par_notin.
auto.
auto.
inversion_clear H.
apply par_notin.
auto.
auto.
split; intros.
inversion_clear H.
inversion_clear H0.
apply par_notin.
auto.
apply par_notin.
auto.
auto.
inversion_clear H.
inversion_clear H1.
apply par_notin.
apply par_notin.
auto.
auto.
auto.
intros.
split; intros.
inversion_clear H0.
apply par_notin.
generalize (IHCong1 _ _ c); tauto.
generalize (IHCong2 _ _ c); tauto.
inversion_clear H0.
apply par_notin.
generalize (IHCong1 _ _ c); tauto.
generalize (IHCong2 _ _ c); tauto.
intros.
split; intros.
apply par_notin.
auto.
generalize (inv_rin_notinp H); intro.
apply in_notin.
intuition.
intuition.
inversion_clear H.
auto.
tauto.
split; intros.
generalize (IHCong _ _ c); tauto.
generalize (IHCong _ _ c); tauto.
split; intros.
generalize (IHCong1 _ _ c); generalize (IHCong2 _ _ c); tauto.
generalize (IHCong1 _ _ c); generalize (IHCong2 _ _ c); tauto.
Qed.

Lemma cong_respects_notinp :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall Q,
      Cong P Q -> notinp c Q.
intros.
generalize (cong_respects_notinp' H0); intros.
generalize (H1 _ _ c); tauto.
Qed.

Lemma cong_respects_isinp :
  forall A b (c : chan A b) P,
    isinp c P ->
    forall Q,
      Cong P Q -> isinp c Q.
intros.
intro; apply H; eapply cong_respects_notinp.
apply H1.
apply cong_sym; auto.
Qed.

(** notinp / trans *)

Lemma notinp_trans_OutL' :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' L,
      Trans P L P' ->
      forall B b' (d : chan B b') v,
	L = OutL d v -> notinp c P' /\ ~ c &&& d /\ ~ (c %% v).
intros A b c P H P' L H0.
induction H0
 as
  [A0 b0 x v P|
   A0 b0 x v C|
   A0 b0 x v C|
   A0 C x|
   A0 C x|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q L H0 IHTrans|
   P P' Q L H0 IHTrans].
intros.
generalize (inv_out_notinp H); intro X; decompose [and] X;
 clear X.
split; auto.
generalize (OutL_inj1 H0); intro X; inversion_clear X.
generalize d v0 H0 H1 H3; clear d v0 H0 H1 H3; rewrite <- H2; rewrite <- H5;
 clear H2 H5 B b'; intros.
generalize (OutL_inj H0); intro X; inversion_clear X.
rewrite <- H2; rewrite <- H5; auto.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
inversion_clear H.
generalize (IHTrans H2 _ _ _ _ H1); intros.
split.
apply par_notin.
intuition.
auto.
intuition.
intros.
inversion_clear H.
generalize (IHTrans H3 _ _ _ _ H1); intros.
split.
apply par_notin.
intuition.
intuition.
intuition.
Qed.

Lemma notinp_trans_OutL :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' B b' (d : chan B b') v,
      Trans P (OutL d v) P' -> notinp c P' /\ ~ c &&& d /\ ~ (c %% v).
intros.
apply notinp_trans_OutL' with (d := d) (v := v) (L := OutL d v) (P := P).
auto.
auto.
auto.
Qed.

Lemma notinp_trans_InL' :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' L,
      Trans P L P' ->
      forall B b' (d : chan B b') v,
	~ (v %% c) -> L = InL d v -> notinp c P' /\ ~ c &&& d.
intros A b c P H P' L H0.
induction H0
 as
  [A0 b0 x v P|
   A0 b0 x v C|
   A0 b0 x v C|
   A0 C x|
   A0 C x|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q L H0 IHTrans|
   P P' Q L H0 IHTrans].
intros.
discriminate H1.
intros.
generalize (inv_in_notinp H); intro X; inversion_clear X.
split.
apply H3.
generalize (InL_inj1 H1); intro X; inversion_clear X.
generalize x C H v H0 H1 H2 H3; clear x C H v H0 H1 H2 H3; rewrite H4;
 rewrite H5; clear H4 H5 A0 b0; intros.
generalize (InL_inj H1); intros.
inversion_clear H4.
rewrite H6.
auto.
generalize (InL_inj1 H1); intro X; inversion_clear X.
generalize x C H v H0 H1 H2 H3; clear x C H v H0 H1 H2 H3; rewrite H4;
 rewrite H5; clear H4 H5 A0 b0; intros.
generalize (InL_inj H1); intros.
inversion_clear H4.
rewrite <- H5.
auto.
intros.
generalize (inv_rin_notinp H); intro X; inversion_clear X.
split.
apply par_notin.
auto.
apply H3.
generalize (InL_inj1 H1); intro X; inversion_clear X.
generalize x C H v H0 H1 H2 H3; clear x C H v H0 H1 H2 H3; rewrite H4;
 rewrite H5; clear H4 H5 A0 b0; intros.
generalize (InL_inj H1); intros.
inversion_clear H4.
rewrite H6.
auto.
generalize (InL_inj1 H1); intro X; inversion_clear X.
generalize x C H v H0 H1 H2 H3; clear x C H v H0 H1 H2 H3; rewrite H4;
 rewrite H5; clear H4 H5 A0 b0; intros.
generalize (InL_inj H1); intros.
inversion_clear H4.
rewrite <- H5; auto.
intros.
discriminate H1.
intros.
discriminate H1.
intros.
discriminate H3.
intros.
discriminate H3.
intros.
inversion_clear H.
generalize (IHTrans H3 _ _ _ _ H1 H2); intros.
inversion_clear H.
split; auto.
apply par_notin.
auto.
auto.
intros.
inversion_clear H.
generalize (IHTrans H4 _ _ _ _ H1 H2); intros.
inversion_clear H.
split; auto.
apply par_notin.
auto.
auto.
Qed.

Lemma notinp_trans_InL :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' B b' (d : chan B b') v,
      ~ (v %% c) -> Trans P (InL d v) P' -> notinp c P' /\ ~ c &&& d.
intros.
eapply notinp_trans_InL' with (d := d) (v := v) (P := P) (L := InL d v).
auto.
auto.
auto.
auto.
Qed.

Lemma notinp_trans_TauL' :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' L,
      Trans P L P' ->
      forall B b' (d : chan B b'),
	L = TauL d -> notinp c P'.
intros A b c P H P' L H0.
induction H0
 as
  [A0 b0 x v P|
   A0 b0 x v C|
   A0 b0 x v C|
   A0 C x|
   A0 C x|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q L H0 IHTrans|
   P P' Q L H0 IHTrans].
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
generalize (TauL_inj1 H2); intros.
inversion_clear H3.
clear IHTrans1 IHTrans2.
clear B b' d H2 H4 H5.
apply par_notin.
inversion_clear H.
generalize (notinp_trans_OutL H2 H0); intro.
intuition.
inversion_clear H.
generalize (notinp_trans_InL H3); intro.
generalize (inv_trans_OutL H0); intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
assert (notinp c (parP x1 (x << v >> x0))).
apply cong_respects_notinp with P.
auto.
auto.
inversion_clear H4.
generalize (inv_out_notinp H8); intros.
decompose [and] H4; clear H4.
assert (~ (v %% c)).
intro.
apply H11.
apply sym_JMeq.
auto.
generalize (H _ _ _ _ _ H4 H1); intro.
intuition.
intros.
clear B b' d H2 IHTrans2 IHTrans1.
inversion_clear H.
apply par_notin.
generalize (notinp_trans_InL H2); intro.
generalize (inv_trans_OutL H1); intro.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
assert (notinp c (parP x1 (x << v >> x0))).
apply cong_respects_notinp with Q.
auto.
auto.
inversion_clear H4.
generalize (inv_out_notinp H8); intros.
decompose [and] H4; clear H4.
assert (~ (v %% c)).
intro; apply H11.
apply sym_JMeq.
auto.
generalize (H _ _ _ _ _ H4 H0); intro.
intuition.
generalize (notinp_trans_OutL H3 H1); intro.
intuition.
intros.
inversion_clear H.
apply par_notin.
apply IHTrans with (d := d).
auto.
auto.
auto.
intros.
inversion_clear H.
apply par_notin.
auto.
apply IHTrans with (d := d).
auto.
auto.
Qed.

Lemma notinp_trans_TauL :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' B b' (d : chan B b'),
      Trans P (TauL d) P' -> notinp c P'.
intros.
apply notinp_trans_TauL' with (P := P) (d := d) (L := TauL d).
auto.
auto.
auto.
Qed.

Lemma notinp_trans_NewL' :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' L,
      Trans P L P' ->
      forall B b' (d : chan B b'),
	L = NewL d -> ~ d &&& c -> notinp c P'.
intros.
induction H0.
discriminate H1.
discriminate H1.
discriminate H1.
generalize (NewL_inj1 H1); intro X; inversion_clear X.
subst B b'.
generalize (NewL_inj H1); intro.
subst d.
generalize (inv_nul_notin H); intro.
apply H0.
auto.
generalize (NewL_inj1 H1); intro X; inversion_clear X.
subst B b'.
generalize (NewL_inj H1); intro.
subst d.
generalize (inv_nu_notin H); intro.
apply H0.
auto.
discriminate H1.
discriminate H1.
inversion_clear H.
apply par_notin; auto.
inversion_clear H.
apply par_notin; auto.
Qed.

Lemma notinp_trans_NewL :
  forall A b (c : chan A b) P,
    notinp c P ->
    forall P' B b' (d : chan B b'),
      Trans P (NewL d) P' -> ~ d &&& c -> notinp c P'.
intros.
apply notinp_trans_NewL' with (P := P) (d := d) (L := NewL d); auto.
Qed.

(** isinp / trans *)

Lemma isinp_trans_OutL' :
  forall A b (c : chan A b) P,
    isinp c P ->
    forall P' L,
      Trans P L P' ->
      forall B b' (d : chan B b') v,
	L = OutL d v -> ~ d &&& c -> ~ (v %% c) -> isinp c P'.
intros A b c P H P' L H0.
induction H0
 as
  [A0 b0 x v P|
   A0 b0 x v C|
   A0 b0 x v C|
   A0 C x|
   A0 C x|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q L H0 IHTrans|
   P P' Q L H0 IHTrans].
intros.
generalize (OutL_inj1 H0); intro X; inversion_clear X.
generalize d v0 H0 H1 H2; clear d v0 H0 H1 H2; rewrite <- H3; rewrite <- H4;
 clear H3 H4 B b'; intros.
generalize (OutL_inj H0); intro X; inversion_clear X.
clear H0; rewrite <- H4 in H2; clear H4; rewrite <- H3 in H1; clear H3 d v0.
red in |- *; intro; red in H; apply H.
apply out_notin.
auto.
intro.
apply H2.
apply sym_JMeq.
auto.
auto.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
red in |- *; intro; red in H; apply H.
apply par_notin.
apply NNPP; intro.
generalize (IHTrans H5 _ _ _ _ H1 H2 H3); intro.
red in H6.
apply H6.
inversion_clear H4.
auto.
inversion_clear H4.
auto.
intros.
red in |- *; intro.
red in H; apply H.
inversion_clear H4.
apply par_notin.
auto.
apply NNPP; intro.
generalize (IHTrans H4 _ _ _ _ H1 H2 H3); intro.
red in H7.
auto.
Qed.

Lemma isinp_trans_OutL :
  forall A b (c : chan A b) P,
    isinp c P ->
    forall P' B b' (d : chan B b') v,
      Trans P (OutL d v) P' -> ~ d &&& c -> ~ (v %% c) -> isinp c P'.
intros.
apply isinp_trans_OutL' with (P := P) (d := d) (v := v) (L := OutL d v).
auto.
auto.
auto.
auto.
auto.
Qed.

Lemma isinp_trans_OutL2' :
  forall A b (c : chan A b) P',
    isinp c P' ->
    forall P L,
      Trans P L P' ->
      forall B b' (d : chan B b') v,
	L = OutL d v -> isinp c P.
intros A b c P' H P L H0.
induction H0
 as
  [A0 b0 x v P|
   A0 b0 x v C|
   A0 b0 x v C|
   A0 C x|
   A0 C x|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q L H0 IHTrans|
   P P' Q L H0 IHTrans].
intros.
intro X; apply H.
generalize (inv_out_notinp X); intro.
intuition.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
red in |- *; intro; red in H; apply H.
apply par_notin.
apply NNPP; intro.
generalize (IHTrans H3 _ _ _ _ H1); intro.
inversion_clear H2.
auto.
inversion_clear H2.
auto.
intros.
red in |- *; intro.
red in H; apply H.
inversion_clear H2.
apply par_notin.
auto.
apply NNPP; intro.
generalize (IHTrans H2 _ _ _ _ H1); intro.
auto.
Qed.

Lemma isinp_trans_OutL2 :
  forall A b (c : chan A b) P',
    isinp c P' ->
    forall P B b' (d : chan B b') v,
      Trans P (OutL d v) P' -> isinp c P.
intros.
apply isinp_trans_OutL2' with (P' := P') (d := d) (v := v) (L := OutL d v).
auto.
auto.
auto.
Qed.

Lemma isinp_trans_InL' :
  forall A b (c : chan A b) P',
    isinp c P' ->
    forall P L,
      Trans P L P' ->
      forall B b' (d : chan B b') v,
	L = InL d v -> isinp c P \/ v %% c.
intros A b c P' H P L H0.
induction H0
 as
  [A0 b0 x v P|
   A0 b0 x v C|
   A0 b0 x v C|
   A0 C x|
   A0 C x|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q Q' A0 b0 x v H0 IHTrans1 H1 IHTrans2|
   P P' Q L H0 IHTrans|
   P P' Q L H0 IHTrans].
intros.
discriminate H0.
intros.
generalize (InL_inj1 H0); intro X; inversion_clear X.
generalize d v0 H0; clear d v0 H0; rewrite <- H1; rewrite <- H2;
 clear H1 H2 B b'.
intros.
generalize (InL_inj H0); intro X; inversion_clear X.
clear H0.
rewrite H1; rewrite <- H2; clear H1 H2 v0 x.
elim (classic (v %% c)); intro.
auto.
left.
intro; apply H.
generalize (inv_in_notinp H1); intro.
inversion_clear H2.
apply H4.
auto.
intros.
generalize (InL_inj1 H0); intro X; inversion_clear X.
generalize d v0 H0; clear d v0 H0; rewrite <- H1; rewrite <- H2;
 clear H1 H2 B b'.
intros.
generalize (InL_inj H0); intro X; inversion_clear X.
clear H0.
rewrite <- H2; clear H2 v0 H1 d.
elim (classic (v %% c)); intro.
auto.
left.
intro; apply H.
generalize (inv_rin_notinp H1); intro.
inversion_clear H2.
apply par_notin.
apply rin_notin.
auto.
auto.
apply H4.
auto.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
generalize (inv_par_isinp H); intro.
inversion_clear H2.
generalize (IHTrans H3 _ _ _ _ H1); intros.
inversion_clear H2.
left.
intro X; inversion_clear X; auto.
auto.
left.
intro X; inversion_clear X; auto.
intros.
generalize (inv_par_isinp H); intro.
inversion_clear H2.
left.
intro X; inversion_clear X; auto.
generalize (IHTrans H3 _ _ _ _ H1); intros.
inversion_clear H2.
left.
intro X; inversion_clear X; auto.
auto.
Qed.

Lemma isinp_trans_InL :
  forall A b (c : chan A b) P',
    isinp c P' ->
    forall P B b' (d : chan B b') v,
      Trans P (InL d v) P' -> isinp c P \/ v %% c.
intros.
apply isinp_trans_InL' with (d := d) (v := v) (P' := P') (L := InL d v).
auto.
auto.
auto.
Qed.

Lemma isinp_trans_tau' :
  forall P P' K,
    Trans P K P' ->
    forall A b (c : chan A b),
      K = TauL c ->
      forall B b' (d : chan B b'),
	isinp d P' -> isinp d P.
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
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
clear IHTrans1 IHTrans2; intros.
clear H0 c.
generalize (inv_par_isinp H2); intro X; inversion_clear X.
generalize (isinp_trans_OutL2 H0 H); intro.
intro X; inversion_clear X; apply H3; auto.
generalize (isinp_trans_InL H0 H1); intros.
inversion_clear H3.
intro X; inversion_clear X; auto.
generalize (jmeq_types H4); intros.
generalize x v H H1 H4; clear x v H H1 H4; rewrite H3.
clear H3 A; intros.
cut (isinp d P).
intros.
intro X; inversion_clear X; auto.
rewrite <- (JMeq_eq H4).
generalize (inv_trans_OutL H); intros.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
apply cong_respects_isinp with (parP x1 (x << v >> x0)).
intro X; inversion_clear X.
generalize (inv_out_notinp H7); intro.
inversion_clear H8.
inversion_clear H10.
auto.
apply cong_sym; auto.
intros.
clear H0 c IHTrans1 IHTrans2.
generalize (inv_par_isinp H2); intro X; inversion_clear X.
generalize (isinp_trans_InL H0 H); intro.
inversion_clear H3.
intro X; inversion_clear X; auto.
cut (isinp d Q).
intro.
intro X; inversion_clear X; auto.
generalize (jmeq_types H4); intro.
generalize x v H H1 H4; clear x v H H1 H4; rewrite H3; clear H3 A; intros.
rewrite <- (JMeq_eq H4).
generalize (inv_trans_OutL H1); intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
apply cong_respects_isinp with (parP x1 (x << v >> x0)).
intro.
inversion_clear H3.
generalize (inv_out_notinp H8); intro.
intuition.
apply cong_sym; auto.
generalize (isinp_trans_OutL2 H0 H1); intro.
intro X; inversion_clear X; auto.
intros.
generalize (inv_par_isinp H1); intro X; inversion_clear X.
generalize (IHTrans _ _ _ H0 _ _ _ H2).
intro.
intro X; inversion_clear X; auto.
intro X; inversion_clear X; auto.
intros.
generalize (inv_par_isinp H1); intro X; inversion_clear X.
intro X; inversion_clear X; auto.
generalize (IHTrans _ _ _ H0 _ _ _ H2).
intro.
intro X; inversion_clear X; auto.
Qed.

Lemma isinp_trans_tau :
  forall P P' A b (c : chan A b),
    Trans P (TauL c) P' ->
    forall B b' (d : chan B b'),
      isinp d P' -> isinp d P.
intros.
eapply isinp_trans_tau' with (K := TauL c) (P' := P') (c := c).
auto.
auto.
auto.
Qed.

(** free channels *)

Definition free_chans L p : Prop :=
  forall B b' (d : chan B b'), isinp d p <-> in_ChanList d L.

Lemma free_chans_perm :
  forall P L L',
    free_chans L P -> free_chans L' P -> incC L L' /\ incC L' L.
intros.
red in H.
red in H0.
split.
red in |- *; intros.
generalize (H0 _ _ c); intro.
generalize (H _ _ c); intro.
tauto.
red in |- *; intros.
generalize (H0 _ _ c); intro.
generalize (H _ _ c); intro.
tauto.
Qed.

(** free_chans / trans *)

Lemma free_chans_trans_tau :
  forall P P' A b (c : chan A b),
    Trans P (TauL c) P' ->
    forall L,
      free_chans L P -> forall L', free_chans L' P' -> incC L' L.
intros.
red in H0.
red in H1.
red in |- *; intros.
generalize (H1 _ _ c0); intro X; inversion_clear X.
generalize (H4 H2); intros.
generalize (isinp_trans_tau H H5); intro.
generalize (H0 _ _ c0); intro X; inversion_clear X.
auto.
Qed.

Lemma isin_proc_mono_nu :
  forall A (C : chan A false -> proc) B b (c : chan B b) x,
    isinp c (C x) -> ~ x &&& c -> isinp c (nuP C).
intros.
intro.
apply H.
apply notinp_trans_NewL with (d := x) (P := nuP C); auto.
apply tr_new.
Qed.

Lemma isin_proc_mono_nul :
  forall A (C : chan A true -> proc) B b (c : chan B b) x,
    isinp c (C x) -> ~ x &&& c -> isinp c (nuPl C).
intros.
intro.
apply H.
apply notinp_trans_NewL with (d := x) (P := nuPl C); auto.
apply tr_newl.
Qed.

Lemma free_chans_trans_new' :
  forall P P' K,
    Trans P K P' ->
    forall A b (c : chan A b),
      K = NewL c ->
      forall L,
	free_chans L P ->
	fresh c L ->
	forall L', free_chans L' P' -> incC L' (c & L).
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
discriminate H.
intros.
discriminate H.
intros.
discriminate H.
intros.
generalize (NewL_inj1 H); intro X; inversion_clear X.
generalize c H H1; clear c H H1; rewrite <- H3; rewrite <- H4;
 clear H3 H4 A0 b; intros.
generalize (NewL_inj H); intro.
rewrite <- H3; rewrite <- H3 in H1; clear H3 H c.
red in |- *; intros.
generalize (H2 _ _ c); intro X; inversion_clear X.
generalize (H4 H); clear H3 H4; intro.
elim (classic (x &&& c)); intro.
simpl in |- *; auto.
simpl in |- *; right.
generalize (isin_proc_mono_nul H3 H4); intro.
generalize (H0 _ _ c); intro.
tauto.
intros.
generalize (NewL_inj1 H); intro X; inversion_clear X.
generalize c H H1; clear c H H1; rewrite <- H3; rewrite <- H4;
 clear H3 H4 A0 b; intros.
generalize (NewL_inj H); intro.
rewrite <- H3; rewrite <- H3 in H1; clear H3 H c.
red in |- *; intros.
generalize (H2 _ _ c); intro X; inversion_clear X.
generalize (H4 H); clear H3 H4; intro.
elim (classic (x &&& c)); intro.
simpl in |- *; auto.
simpl in |- *; right.
generalize (isin_proc_mono_nu H3 H4); intro.
generalize (H0 _ _ c); intro.
tauto.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
red in |- *; intros.
elim (classic (c &&& c0)); intro.
simpl in |- *; auto.
generalize (H3 _ _ c0); intro X; inversion_clear X.
generalize (H7 H4); clear H7 H6; intros.
generalize (inv_par_isinp H6); intro X; inversion_clear X.
assert (isinp c0 P).
intro.
apply H7.
apply notinp_trans_NewL with (d := c) (P := P).
auto.
rewrite <- H0; auto.
auto.
auto.
assert (isinp c0 (parP P Q)).
intro X; inversion_clear X.
auto.
generalize (H1 _ _ c0); intro X; inversion_clear X.
generalize (H10 H9); intro; clear H10 H11.
simpl in |- *; auto.
assert (isinp c0 (parP P Q)).
intro X; inversion_clear X.
auto.
generalize (H1 _ _ c0); intro X; inversion_clear X.
generalize (H9 H8); intro; clear H10 H9.
simpl in |- *; auto.
intros.
red in |- *; intros.
elim (classic (c &&& c0)); intro.
simpl in |- *; auto.
generalize (H3 _ _ c0); intro X; inversion_clear X.
generalize (H7 H4); clear H7 H6; intros.
generalize (inv_par_isinp H6); intro X; inversion_clear X.
assert (isinp c0 (parP Q P)).
intro X; inversion_clear X.
auto.
generalize (H1 _ _ c0); intro X; inversion_clear X.
generalize (H9 H8); clear H10 H9; intro.
simpl in |- *; auto.
assert (isinp c0 P).
intro.
apply H7.
apply notinp_trans_NewL with (d := c) (P := P).
auto.
rewrite <- H0; auto.
auto.
auto.
assert (isinp c0 (parP Q P)).
intro X; inversion_clear X.
auto.
generalize (H1 _ _ c0); intro X; inversion_clear X.
generalize (H10 H9); intro; clear H10 H11.
simpl in |- *; auto.
Qed.

Lemma free_chans_trans_new :
  forall P P' A b (c : chan A b),
    Trans P (NewL c) P' ->
    forall L,
      free_chans L P ->
      fresh c L -> forall L', free_chans L' P' -> incC L' (c & L).
intros.
apply
 (free_chans_trans_new' H (refl_equal (NewL c)) H0 H1 H2).
Qed.

Lemma free_chans_red :
 forall P0 P',
 Red P0 P' ->
 forall L,
 free_chans L (sndT P0) /\ incC L (fstT P0) ->
 forall L', free_chans L' (sndT P') -> incC L' (fstT P').
intros.
inversion_clear H.
inversion H2.
simpl in |- *.
inversion_clear H0.
rewrite <- H3 in H6; simpl in H6.
rewrite <- H5 in H1; simpl in H.
generalize (free_chans_trans_tau H H6 H1); intro.
rewrite <- H3 in H7; simpl in H7.
apply incC_trans with L.
auto.
auto.
simpl in |- *.
rewrite <- H4 in H0; simpl in H0; inversion_clear H0.
assert (fresh x0 L).
apply incC_fresh with L0.
auto.
auto.
rewrite <- H6 in H1; simpl in H1.
generalize (free_chans_trans_new H H7 H0 H1); intro.
apply incC_trans with (x0 & L).
auto.
apply incC_weak.
auto.
Qed.

(** a channel that does not occur in the process but that occurs
in the environment never appears during reductions *)

Lemma notinp_reds' :
  forall P0 P',
    Reds P0 P' ->
    forall A b (c : chan A b),
      notinp c (sndT P0) /\ in_ChanList c (fstT P0) ->
      notinp c (sndT P') /\ in_ChanList c (fstT P').
intros.
apply
 invariant_by_red
  with
    (P := fun P' : state => notinp c (sndT P') /\ in_ChanList c (fstT P'))
    (p0 := P0).
intros.
inversion_clear H1.
inversion H3.
rewrite <- H4 in H2; simpl in H2; simpl in |- *.
split; intuition.
apply notinp_trans_TauL with (P := P) (d := x0).
auto.
auto.
simpl in |- *.
split.
assert (~ x0 &&& c).
rewrite <- H5 in H2; inversion_clear H2.
simpl in H9.
red in H4.
apply H4.
auto.
apply notinp_trans_NewL with (P := P) (d := x0).
rewrite <- H5 in H2; inversion_clear H2.
auto.
auto.
rewrite <- H5 in H2; inversion_clear H2.
auto.
auto.
rewrite <- H5 in H2; inversion_clear H2.
auto.
auto.
auto.
Qed.

Lemma notinp_reds :
 forall P0 P',
 Reds P0 P' ->
 forall A b (c : chan A b),
 notinp c (sndT P0) /\ in_ChanList c (fstT P0) -> notinp c (sndT P').
intros.
apply (proj1 (notinp_reds' H H0)).
Qed.

Unset Implicit Arguments.