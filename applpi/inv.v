Require Import chan.
Require Import applpi.
Require Import inj.

 (** inversion lemmas, not provided automatically by Coq because of dependent types
(they cause an assertion failure) *)

Set Implicit Arguments.

Lemma inv_trans_rinP1 :
  forall A b (c : chan A b) P B b' (d : chan B b') v Q,
    Trans (c ??* P) (InL d v) Q -> A = B.
intros.
inversion H.
auto.
Qed.

Lemma inv_trans_rinP_bool :
  forall A b (c : chan A b) C b' (c' : chan A b') v P,
    Trans (c ??* C) (InL c' v) P -> b = b'.
intros.
inversion H.
rewrite <-H2; auto.
Qed.

Lemma inv_trans_rinP_chan_cont' :
 forall Q P L,
 Trans Q L P ->
 forall A b (c : chan A b) C,
 Q = c ??* C ->
 forall c' v,
 L = InL c' v -> c = c' /\ P = parP (c ??* C) (C v).
do 4 intro.
induction H.
intros.
discriminate H0.
intros.
discriminate H.
intros.
generalize (InL_inj1 H0); intro.
inversion_clear H1.
generalize c C0 H c' v0 H0; clear c C0 H c' v0 H0; rewrite <- H2;
 rewrite <- H3; clear H2 H3 A0 b0; intros.
generalize (InL_inj H0); intro.
inversion_clear H1.
clear H0; rewrite <- H2; rewrite <- H3; clear H2 H3 v0 c'.
generalize (rinP_inj_chan H); intro.
generalize H; clear H; rewrite H0; clear H0 x; intro.
split; auto.
generalize (rinP_inj_cont H); intro.
rewrite <- H0; auto.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_rinP_chan :
 forall A b (c : chan A b) C (c' : chan A b) v P, 
   Trans (c ??* C) (InL c' v) P -> c = c'.
intros.
apply
 (proj1
    (inv_trans_rinP_chan_cont' H (refl_equal (c ??* C)) 
       (refl_equal (InL c' v)))).
Qed.

Lemma inv_trans_rinP_cont :
  forall A b (c : chan A b) v C P,
    Trans (c ??* C) (InL c v) P -> P = parP (c ??* C) (C v).
intros.
apply
 (proj2
    (inv_trans_rinP_chan_cont' H (refl_equal (c ??* C)) 
       (refl_equal (InL c v)))).
Qed.

Lemma inv_trans_inP1 :
 forall A b (c : chan A b) P B b' (d : chan B b') v Q,
   Trans (c ?? P) (InL d v) Q -> A = B.
intros.
inversion H.
auto.
Qed.

Lemma inv_trans_inP_bool :
 forall A b (c : chan A b) C b' (c' : chan A b') v P,
   Trans (c ?? C) (InL c' v) P -> b = b'.
intros.
inversion H.
rewrite <-H2; auto.
Qed.

Lemma inv_trans_inP_chan_cont' :
 forall Q P L,
 Trans Q L P ->
 forall A b (c : chan A b) C,
 Q = c ?? C ->
 forall (c' : chan A b) v, 
   L = InL c' v -> c = c' /\ P = C v.
do 4 intro.
induction H.
intros.
discriminate H0.
intros.
generalize (InL_inj1 H0); intro.
inversion_clear H1.
generalize c C0 H c' v0 H0; clear c C0 H c' v0 H0; rewrite <- H2;
 rewrite <- H3; clear H2 H3 A0 b0; intros.
generalize (InL_inj H0); intro.
inversion_clear H1.
clear H0; rewrite <- H2; rewrite <- H3; clear H2 H3 v0 c'.
generalize (inP_inj_chan H); intro.
generalize H; clear H; rewrite H0; clear H0 x; intro.
split; auto.
generalize (inP_inj_cont H); intro.
rewrite <- H0; auto.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_inP_chan :
 forall A b (c : chan A b) C (c' : chan A b) v P, 
   Trans (c ?? C) (InL c' v) P -> c = c'.
intros.
apply
 (proj1
    (inv_trans_inP_chan_cont' H (refl_equal (c ?? C)) (refl_equal (InL c' v)))).
Qed.

Lemma inv_trans_inP_cont :
 forall A b (c : chan A b) v C P, 
   Trans (c ?? C) (InL c v) P -> P = C v.
intros.
apply
 (proj2
    (inv_trans_inP_chan_cont' H (refl_equal (c ?? C)) (refl_equal (InL c v)))).
Qed.

Lemma inv_trans_outP1 :
 forall A b (c : chan A b) v P B b' (d : chan B b') w Q, 
   Trans (c << v >> P) (OutL d w) Q -> A = B.
intros.
inversion H.
auto.
Qed.

Lemma inv_trans_outP_bool :
 forall A b (c : chan A b) v P b' (d : chan A b') w Q,
   Trans (c << v >> P) (OutL d w) Q -> b = b'.
intros.
inversion H.
rewrite <-H2; auto.
Qed.

Lemma inv_trans_outP_chan_val_cont' :
 forall P Q L,
 Trans P L Q ->
 forall A b (c : chan A b) v T,
 P = c << v >> T ->
 forall (d : chan A b) w, 
   L = OutL d w -> c = d /\ v = w /\ Q = T.
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
generalize (outP_inj1 H); intro.
inversion_clear H1.
generalize c v0 H d w H0; clear c v0 H d w H0; rewrite <- H2; rewrite <- H3;
 clear H2 H3 A0 b0; intros.
generalize (outP_inj_chan_val H); intro.
inversion_clear H1.
generalize H H0; clear H H0; rewrite <- H2; rewrite <- H3; clear H2 H3 c v0;
 intros.
injection H.
intro.
generalize (OutL_inj H0); intro.
inversion_clear H2.
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
intros.
discriminate H2.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_outP_chan_val :
 forall A b (c : chan A b) v C (c' : chan A b) v' P,
   Trans (c << v >> C) (OutL c' v') P -> c = c' /\ v = v'.
intros.
generalize
 (inv_trans_outP_chan_val_cont' H (refl_equal (c << v >> C)) (refl_equal (OutL c' v'))); intro.
intuition.
Qed.

Lemma inv_trans_outP_cont :
  forall A b (c : chan A b) v C P,
    Trans (c << v >> C) (OutL c v) P -> P = C.
intros.
generalize
 (inv_trans_outP_chan_val_cont' H (refl_equal (c << v >> C)) (refl_equal (OutL c v))); intro.
intuition.
Qed.

Lemma inv_trans_nuP1 :
 forall A (P : chan A false -> proc) B b' (d : chan B b') Q, 
   Trans (nuP P) (NewL d) Q -> A = B.
intros.
inversion H.
auto.
Qed.

Lemma inv_trans_nuP_cont' :
 forall Q P L,
 Trans Q L P ->
 forall A (C : chan A false -> proc),
 Q = nuP C -> 
 forall c, 
   L = NewL c -> P = C c.
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
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
generalize (nuP_inj1 H); intro.
generalize C0 H c H0; clear C0 H c H0; rewrite <- H1; clear H1 A0; intros.
generalize (nuP_inj_cont H); intro.
rewrite <- H1.
generalize (NewL_inj H0); intro.
rewrite <- H2.
auto.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_nuP_cont :
 forall A (C : chan A false -> proc) c P,
   Trans (nuP C) (NewL c) P -> P = C c.
intros.
apply
 (inv_trans_nuP_cont' H (refl_equal (nuP C)) (refl_equal (NewL c))).
Qed.

Lemma inv_trans_nuPl1 :
 forall A (P : chan A true -> proc) B b' (d : chan B b') Q, 
   Trans (nuPl P) (NewL d) Q -> A = B.
intros.
inversion H.
auto.
Qed.

Lemma inv_trans_nuPl_cont' :
 forall Q P L,
 Trans Q L P ->
 forall A (C : chan A true -> proc),
 Q = nuPl C -> 
 forall c, 
   L = NewL c -> P = C c.
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
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
generalize (nuPl_inj1 H); intro.
generalize C0 H c H0; clear C0 H c H0; rewrite <- H1; clear H1 A0; intros.
generalize (nuPl_inj_cont H); intro.
rewrite <- H1.
generalize (NewL_inj H0); intro.
rewrite <- H2.
auto.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_nuPl_cont :
 forall A (C : chan A true -> proc) c (P : proc),
 Trans (nuPl C) (NewL c) P -> P = C c.
intros.
apply
 (inv_trans_nuPl_cont' H (refl_equal (nuPl C)) (refl_equal (NewL c))).
Qed.

Lemma inv_trans_tau' :
 forall P P' L,
 Trans P L P' ->
 forall A b (c : chan A b),
 L = TauL c ->
 exists P1,
   (exists P2,
      P = parP P1 P2 /\
      (exists P1',
         (exists P2',
            (exists v,
               Trans P1 (OutL c v) P1' /\
               Trans P2 (InL c v) P2' /\ P' = parP P1' P2') \/
            (exists v,
               Trans P2 (OutL c v) P2' /\
               Trans P1 (InL c v) P1' /\ P' = parP P1' P2') \/
            Trans P1 (TauL c) P1' /\ P' = parP P1' P2 \/
            Trans P2 (TauL c) P2' /\ P' = parP P1 P2'))).
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
intros.
exists P; exists Q; split; auto.
exists P'; exists Q'.
left.
generalize (TauL_inj1 H0); intros.
inversion_clear H2.
generalize c H0; clear c H0; rewrite <- H3; rewrite <- H4; clear H3 H4 A0 b0;
 intros.
generalize (TauL_inj H0); intros.
rewrite <- H2.
exists v.
auto.
intros.
exists P; exists Q; split; auto.
exists P'; exists Q'.
right; left.
generalize (TauL_inj1 H0); intros.
inversion_clear H2.
generalize c H0; clear c H0; rewrite <- H3; rewrite <- H4; clear H3 H4 A0 b0;
 intros.
generalize (TauL_inj H0); intros.
rewrite <- H2.
exists v.
auto.
intros.
exists P; exists Q; split; auto.
generalize (IHTrans _ _ _ H0); intro X; inversion_clear X.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H2.
inversion_clear H3.
inversion_clear H2.
decompose [and] H3; clear H3.
exists P'; exists P'.
right; right; left.
rewrite <- H0; auto.
inversion_clear H2.
inversion_clear H3.
decompose [and] H2; clear H2.
exists P'; exists P'.
right; right; left.
rewrite <- H0; auto.
inversion_clear H3.
inversion_clear H2.
exists P'; exists P'.
right; right; left.
split; auto.
rewrite <- H0.
auto.
inversion_clear H2.
exists P'; exists P'.
right; right; left.
split; auto.
rewrite <- H0.
auto.
intros.
exists Q; exists P; split; auto.
generalize (IHTrans _ _ _ H0); intro X; inversion_clear X.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion_clear H2.
inversion_clear H3.
inversion_clear H2.
decompose [and] H3; clear H3.
exists P'; exists P'.
right; right; right.
rewrite <- H0; auto.
inversion_clear H2.
inversion_clear H3.
decompose [and] H2; clear H2.
exists P'; exists P'.
right; right; right.
rewrite <- H0; auto.
inversion_clear H3.
inversion_clear H2.
exists P'; exists P'.
right; right; right.
rewrite <- H0; auto.
inversion_clear H2.
exists P'; exists P'.
right; right; right.
rewrite <- H0; auto.
Qed.

Lemma inv_trans_tau :
 forall P P' A b (c : chan A b),
 Trans P (TauL c) P' ->
 exists P1,
   (exists P2,
      P = parP P1 P2 /\
      (exists P1',
         (exists P2',
            (exists v,
               Trans P1 (OutL c v) P1' /\
               Trans P2 (InL c v) P2' /\ P' = parP P1' P2') \/
            (exists v,
               Trans P2 (OutL c v) P2' /\
               Trans P1 (InL c v) P1' /\ P' = parP P1' P2') \/
            Trans P1 (TauL c) P1' /\ P' = parP P1' P2 \/
            Trans P2 (TauL c) P2' /\ P' = parP P1 P2'))).
intros.
apply (inv_trans_tau' H (refl_equal (TauL c))).
Qed.

Lemma inv_trans_inP_lbl' :
 forall L Q P,
 Trans Q L P ->
 forall A b (c : chan A b) C,
 Q = c ?? C -> 
 exists v, L = InL c v /\ P = C v.
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
generalize (inP_inj1 H); intro.
inversion_clear H0.
generalize c C0 H; clear c C0 H; rewrite <- H1; rewrite <- H2; clear H1 H2;
 intros.
generalize (inP_inj_chan H); intro.
generalize H; clear H; rewrite <- H0; clear H0 c; intros.
generalize (inP_inj_cont H); intro.
rewrite <- H0; exists v; auto.
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
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_inP_lbl :
 forall A b (c : chan A b) C L P,
 Trans (c ?? C) L P -> 
 exists v, L = InL c v /\ P = C v.
intros.
apply (inv_trans_inP_lbl' H (refl_equal (c ?? C))).
Qed.

Lemma inv_trans_rinP_lbl' :
 forall L Q P,
 Trans Q L P ->
 forall A b (c : chan A b) C,
 Q = c ??* C -> 
 exists v, L = InL c v /\ P = parP (c ??* C) (C v).
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
generalize (rinP_inj1 H); intro.
inversion_clear H0.
generalize c C0 H; clear c C0 H; rewrite <- H1; rewrite <- H2; clear H1 H2;
 intros.
generalize (rinP_inj_chan H); intro.
generalize H; clear H; rewrite <- H0; clear H0 c; intros.
generalize (rinP_inj_cont H); intro.
rewrite <- H0; exists v; auto.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_rinP_lbl :
 forall A b (c : chan A b) C L P,
 Trans (c ??* C) L P -> 
 exists v, L = InL c v /\ P = parP (c ??* C) (C v).
intros.
apply (inv_trans_rinP_lbl' H (refl_equal (c ??* C))).
Qed.

Lemma inv_trans_outP_lbl' :
 forall L Q P,
 Trans Q L P ->
 forall A b (c : chan A b) v C,
 Q = c << v >> C -> 
 L = OutL c v /\ P = C.
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
generalize (outP_inj1 H); intro.
inversion_clear H0.
generalize c v0 H; clear c v0 H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 A0 b0; intros.
generalize (outP_inj_chan_val H); intro.
inversion_clear H0.
rewrite <- H1; rewrite <- H2.
rewrite <- H1 in H; rewrite <- H2 in H.
injection H.
auto.
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
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_outP_lbl :
 forall A b (c : chan A b) v C L P,
 Trans (c << v >> C) L P -> 
 L = OutL c v /\ P = C.
intros.
apply (inv_trans_outP_lbl' H (refl_equal (c << v >> C))).
Qed.

Lemma inv_trans_nuP_lbl' :
 forall L Q P,
 Trans Q L P ->
 forall A (C : chan A false -> proc),
 Q = nuP C -> 
 exists c, L = NewL c /\ P = C c.
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
generalize (nuP_inj1 H); intro.
generalize C0 H; clear C0 H; rewrite <- H0; clear H0 A0; intros.
generalize (nuP_inj_cont H); intro.
rewrite <- H0.
exists x; auto.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_nuP_lbl :
 forall A (C : chan A false -> proc) L P,
 Trans (nuP C) L P -> 
 exists c, L = NewL c /\ P = C c.
intros.
apply (inv_trans_nuP_lbl' H (refl_equal (nuP C))).
Qed.

Lemma inv_trans_nuPl_lbl' :
 forall L Q P,
 Trans Q L P ->
 forall A (C : chan A true -> proc),
 Q = nuPl C -> 
 exists c, L = NewL c /\ P = C c.
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
generalize (nuPl_inj1 H); intro.
generalize C0 H; clear C0 H; rewrite <- H0; clear H0 A0; intros.
generalize (nuPl_inj_cont H); intro.
rewrite <- H0.
exists x; auto.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans_nuPl_lbl :
 forall A (C : chan A true -> proc) L P,
 Trans (nuPl C) L P -> 
 exists c, L = NewL c /\ P = C c.
intros.
apply (inv_trans_nuPl_lbl' H (refl_equal (nuPl C))).
Qed.

(** application: the transition relation is not reflexive *)

Lemma Trans_not_refl : 
  forall P L, 
    Trans P L P -> False.
intro.
induction P.
intros.
inversion_clear H.
intros.
generalize (inv_trans_inP_lbl H0); intros.
inversion_clear H1.
inversion_clear H2.
rewrite H3 in H0.
eapply H.
apply H0.
intros.
generalize (inv_trans_rinP_lbl H0); intros.
inversion_clear H1.
inversion_clear H2.
discriminate H3.
intros.
generalize (inv_trans_outP_lbl H); intros.
inversion_clear H0.
rewrite H2 in H.
eapply IHP.
apply H.
intros.
inversion H.
eapply IHP1.
apply H4.
eapply IHP1.
apply H4.
eapply IHP1.
apply H3.
eapply IHP2.
apply H3.
intros.
generalize (inv_trans_nuP_lbl H0); intros.
inversion_clear H1.
inversion_clear H2.
rewrite H3 in H0.
eapply H.
apply H0.
intros.
generalize (inv_trans_nuPl_lbl H0); intros.
inversion_clear H1.
inversion_clear H2.
rewrite H3 in H0.
eapply H.
apply H0.
Qed.

Inductive sim_lbl : TrLabel -> TrLabel -> Prop :=
  | sim_InL :
      forall A b (c : chan A b) v w,
      sim_lbl (InL c v) (InL c w)
  | sim_OutL :
      forall A b (c : chan A b) v,
      sim_lbl (OutL c v) (OutL c v)
  | sim_TauL :
      forall A b (c : chan A b), sim_lbl (TauL c) (TauL c)
  | sim_NewL :
      forall A b (c d : chan A b), sim_lbl (NewL c) (NewL d).

Lemma sim_lbl_sym : 
  forall L L', sim_lbl L L' -> sim_lbl L' L.
intros.
induction H.
apply sim_InL.
apply sim_OutL.
apply sim_TauL.
apply sim_NewL.
Qed.

Lemma sim_lbl_OutL_inv1' :
 forall L L',
 sim_lbl L L' ->
 forall A B b b' (x : chan A b) (y : chan B b') v w, 
   L = OutL x v -> L' = OutL y w -> A = B /\ b = b'.
intros L L' H.
induction H.
intros.
discriminate H.
intros.
rewrite H in H0.
apply (OutL_inj1 H0); intros.
intros.
discriminate H.
intros.
discriminate H.
Qed.

Lemma sim_lbl_OutL_inv' :
 forall L L',
 sim_lbl L L' ->
 forall A b (x y : chan A b) v w,
 L = OutL x v -> L' = OutL y w -> x = y /\ v = w.
intros L L' H.
induction H.
intros.
discriminate H.
intros.
rewrite H in H0.
apply (OutL_inj H0); intros.
intros.
discriminate H.
intros.
discriminate H.
Qed.

Lemma sim_lbl_OutL_inv1 :
 forall A B b b' (x : chan A b) (y : chan B b') v w, 
   sim_lbl (OutL x v) (OutL y w) -> A = B /\ b = b'.
intros.
eapply sim_lbl_OutL_inv1'.
apply H.
reflexivity.
reflexivity.
Qed.

Lemma sim_lbl_OutL_inv :
 forall A b (x y : chan A b) v w,
 sim_lbl (OutL x v) (OutL y w) -> x = y /\ v = w.
intros.
eapply sim_lbl_OutL_inv'.
apply H.
reflexivity.
reflexivity.
Qed.

Lemma sim_lbl_OutL_InL_dis' :
 forall L L',
 sim_lbl L L' ->
 forall A B b b' (x : chan A b) (y : chan B b') v w, 
   L = OutL x v -> L' = InL y w -> False.
intros L L' H.
induction H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H.
intros.
discriminate H.
Qed.

Lemma sim_lbl_OutL_InL_dis :
 forall A B b b' (x : chan A b) (y : chan B b') v w, 
   sim_lbl (OutL x v) (InL y w) -> False.
intros.
generalize (sim_lbl_OutL_InL_dis' H); intros.
apply H0 with (x0 := x) (y0 := y) (v0 := v) (w0 := w).
auto.
auto.
Qed.

Lemma sim_lbl_TauL_InL_dis' :
 forall L L',
 sim_lbl L L' ->
 forall A B b b' (x : chan A b) (y : chan B b') w,
 L = TauL x -> L' = InL y w -> False.
intros L L' H.
induction H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H.
Qed.

Lemma sim_lbl_TauL_InL_dis :
 forall A B b b' (x : chan A b) (y : chan B b') w,
 sim_lbl (TauL x) (InL y w) -> False.
intros.
generalize (sim_lbl_TauL_InL_dis' H); intros.
apply H0 with (x0 := x) (y0 := y) (w0 := w).
auto.
auto.
Qed.

Lemma sim_lbl_TauL_OutL_dis' :
 forall L L',
 sim_lbl L L' ->
 forall A B b b' (x : chan A b) (y : chan B b') w,
 L = TauL x -> L' = OutL y w -> False.
intros L L' H.
induction H.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H.
Qed.

Lemma sim_lbl_TauL_OuL_dis :
 forall A B b b' (x : chan A b) (y : chan B b') w,
 sim_lbl (TauL x) (OutL y w) -> False.
intros.
generalize (sim_lbl_TauL_OutL_dis' H); intros.
apply H0 with (x0 := x) (y0 := y) (w0 := w).
auto.
auto.
Qed.

Lemma sim_lbl_NewL_InL_dis' :
 forall L L',
 sim_lbl L L' ->
 forall A B b b' (x : chan A b) (y : chan B b') w,
 L = NewL x -> L' = InL y w -> False.
intros L L' H.
induction H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma sim_lbl_NewL_InL_dis :
 forall A B b b' (x : chan A b) (y : chan B b') w,
 sim_lbl (NewL x) (InL y w) -> False.
intros.
generalize (sim_lbl_NewL_InL_dis' H); intros.
apply H0 with (x0 := x) (y0 := y) (w0 := w).
auto.
auto.
Qed.

Lemma trans_trans_lbl :
 forall P Q L,
 Trans P L Q -> 
 forall L', 
   Trans P L' Q -> sim_lbl L L'.
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
generalize (inv_trans_outP_lbl H); intro.
inversion_clear H0.
rewrite H1.
apply sim_OutL.
intros.
generalize (inv_trans_inP_lbl H); intro.
inversion_clear H0.
inversion_clear H1.
rewrite H0.
apply sim_InL.
intros.
generalize (inv_trans_rinP_lbl H); intro.
inversion_clear H0.
inversion_clear H1.
rewrite H0.
apply sim_InL.
intros.
generalize (inv_trans_nuPl_lbl H); intro.
inversion_clear H0.
inversion_clear H1.
rewrite H0.
apply sim_NewL.
intros.
generalize (inv_trans_nuP_lbl H); intro.
inversion_clear H0.
inversion_clear H1.
rewrite H0.
apply sim_NewL.
intros.
inversion H0.
generalize (IHTrans1 _ H6); intros.
generalize (sim_lbl_OutL_inv1 H9); intros.
inversion_clear H10.
generalize x0 v0 H5 H6 H8 H9; clear x0 v0 H5 H6 H8 H9; rewrite <- H11;
 rewrite <- H12; clear H11 H12 A0 b0; intros.
generalize (sim_lbl_OutL_inv H9); intros.
inversion_clear H10.
rewrite <- H11.
apply sim_TauL.
generalize (IHTrans1 _ H6); intros.
generalize (sim_lbl_OutL_InL_dis H9); contradiction.
rewrite <- H7 in H1.
generalize (Trans_not_refl H1); contradiction.
rewrite <- H6 in H.
generalize (Trans_not_refl H); contradiction.
intros.
inversion H0.
generalize (IHTrans1 _ H6); intros.
generalize (sim_lbl_OutL_InL_dis (sim_lbl_sym H9));
 contradiction.
generalize (IHTrans2 _ H8); intros.
generalize (sim_lbl_OutL_inv1 H9); intros.
inversion_clear H10.
generalize x0 v0 H5 H6 H8 H9; clear x0 v0 H5 H6 H8 H9; rewrite <- H11;
 rewrite <- H12; clear H11 H12 A0 b0; intros.
generalize (sim_lbl_OutL_inv H9); intros.
inversion_clear H10.
rewrite <- H11.
apply sim_TauL.
rewrite <- H7 in H1.
generalize (Trans_not_refl H1); contradiction.
rewrite <- H6 in H.
generalize (Trans_not_refl H); contradiction.
intros.
inversion H0.
generalize (Trans_not_refl H7); contradiction.
generalize (Trans_not_refl H7); contradiction.
apply (IHTrans _ H4).
generalize (Trans_not_refl H4); contradiction.
intros.
inversion H0.
generalize (Trans_not_refl H5); contradiction.
generalize (Trans_not_refl H5); contradiction.
generalize (Trans_not_refl H4); contradiction.
apply (IHTrans _ H4).
Qed.

Unset Implicit Arguments.