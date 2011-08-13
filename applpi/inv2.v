Require Import chan.
Require Import applpi.
Require Import inj.
Require Import redseq.

Set Implicit Arguments.

Lemma Single_inj : 
  forall R R', 
    Single R = Single R' -> R = R'.
intros.
injection H.
auto.
Qed.

Lemma inv_trans2_inP_inP1' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 R = Single (x ?? C) ->
 forall B b' (y : chan B b') D,
 P = y ?? D -> A = B /\ b = b'.
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
discriminate H0.
intros.
generalize (Single_inj H); intros.
rewrite H1 in H0.
apply (inP_inj1 H0).
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
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma inv_trans2_inP_inP1 :
  forall A b (x : chan A b) C B b' (y : chan B b') D L Q,
    Trans2 (Single (x ?? C)) (y ?? D) L Q -> A = B /\ b = b'.
intros.
apply
 (inv_trans2_inP_inP1' H (refl_equal (Single (x ?? C))) (refl_equal (y ?? D))).
Qed.

Lemma inv_trans2_inP_inP_cont' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 R = Single (x ?? C) -> 
 forall D, P = x ?? D -> C = D.
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
discriminate H0.
intros.
generalize (Single_inj H); intros.
rewrite H1 in H0.
apply (inP_inj_cont H0).
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
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma inv_trans2_inP_inP_cont :
 forall A b (x : chan A b) C D L Q, 
   Trans2 (Single (x ?? C)) (x ?? D) L Q -> C = D.
intros.
apply
 (inv_trans2_inP_inP_cont' H (refl_equal (Single (x ?? C))) (refl_equal (x ?? D))).
Qed.

Lemma inv_trans2_rinP_rinP1' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 R = Single (x ??* C) ->
 forall B b' (y : chan B b') D,
   P = y ??* D -> A = B /\ b = b'.
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
discriminate H0.
intros.
discriminate H0.
intros.
generalize (Single_inj H); intros.
rewrite H1 in H0.
apply (rinP_inj1 H0).
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma inv_trans2_rinP_rinP1 :
 forall A b (x : chan A b) C B b' (y : chan B b') D L Q,
   Trans2 (Single (x ??* C)) (y ??* D) L Q -> A = B /\ b = b'.
intros.
apply
 (inv_trans2_rinP_rinP1' H (refl_equal (Single (x ??* C))) (refl_equal (y ??* D))).
Qed.

Lemma inv_trans2_rinP_rinP_chan' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 R = Single (x ??* C) ->
 forall (y : chan A b) D, 
   P = y ??* D -> x = y.
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
generalize (Single_inj H); intros.
rewrite H0 in H1.
generalize (rinP_inj_chan H1); auto.
intros.
discriminate H0.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma inv_trans2_rinP_rinP_chan :
 forall A b (x : chan A b) C (y : chan A b) D L Q,
   Trans2 (Single (x ??* C)) (y ??* D) L Q -> x = y.
intros.
apply
 (inv_trans2_rinP_rinP_chan' H (refl_equal (Single (x ??* C))) (refl_equal (y ??* D))).
Qed.

Lemma inv_trans2_rinP_rinP_cont' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 R = Single (x ??* C) -> 
 forall D, P = x ??* D -> C = D.
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
discriminate H0.
intros.
discriminate H0.
intros.
generalize (Single_inj H); intros.
rewrite H1 in H0.
apply (rinP_inj_cont H0).
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H2.
intros.
discriminate H2.
intros.
discriminate H1.
intros.
discriminate H1.
Qed.

Lemma inv_trans2_rinP_rinP_cont :
 forall A b (x : chan A b) C D L Q, 
   Trans2 (Single (x ??* C)) (x ??* D) L Q -> C = D.
intros.
apply
 (inv_trans2_rinP_rinP_cont' H (refl_equal (Single (x ??* C))) (refl_equal (x ??* D))).
Qed.

Lemma inv_trans2_inP' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 P = x ?? C -> 
 R = Single (x ?? C) /\ (exists v, L = InL x v /\ Q = C v).
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
generalize (inP_inj1 H); intro.
inversion_clear H0.
generalize x0 C0 H; clear x0 C0 H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 A0 b0; intros.
generalize (inP_inj_chan H); intro.
generalize H; clear H; rewrite <- H0; clear H0 x0; intros.
generalize (inP_inj_cont H); intro.
rewrite <- H0.
split; auto.
exists v; auto.
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

Lemma inv_trans2_inP :
 forall R A b (x : chan A b) C L Q,
 Trans2 R (x ?? C) L Q ->
 R = Single (x ?? C) /\ (exists v, L = InL x v /\ Q = C v).
intros.
apply (inv_trans2_inP' H (refl_equal (x ?? C))); intro.
Qed.

Lemma inv_trans2_rinP' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 P = x ??* C ->
 R = Single (x ??* C) /\ (exists v, L = InL x v /\ Q = parP (x ??* C) (C v)).
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
generalize (rinP_inj1 H); intro.
inversion_clear H0.
generalize x0 C0 H; clear x0 C0 H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 A0 b0; intros.
generalize (rinP_inj_chan H); intro.
generalize H; clear H; rewrite <- H0; clear H0 x0; intros.
generalize (rinP_inj_cont H); intro.
rewrite <- H0.
split; auto.
exists v; auto.
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

Lemma inv_trans2_rinP :
 forall R A b (x : chan A b) C L Q,
 Trans2 R (x ??* C) L Q ->
 R = Single (x ??* C) /\ (exists v, L = InL x v /\ Q = parP (x ??* C) (C v)).
intros.
apply (inv_trans2_rinP' H (refl_equal (x ??* C))); intro.
Qed.

Lemma inv_trans2_rinP_parP' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 R = Single (x ??* C) ->
 forall P1 P2,
 P = parP P1 P2 ->
 (exists P1', Trans2 (Single (x ??* C)) P1 L P1' /\ Q = parP P1' P2) \/
 (exists P2', Trans2 (Single (x ??* C)) P2 L P2' /\ Q = parP P1 P2').
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
left.
exists P'.
injection H1; intros.
rewrite <- H3.
rewrite <- H2.
rewrite <- H0.
auto.
right.
exists P'.
injection H1; intros.
rewrite <- H3.
rewrite <- H2.
rewrite <- H0.
auto.
Qed.

Lemma inv_trans2_rinP_parP :
 forall A b (x : chan A b) C P1 P2 L Q,
 Trans2 (Single (x ??* C)) (parP P1 P2) L Q ->
 (exists P1', Trans2 (Single (x ??* C)) P1 L P1' /\ Q = parP P1' P2) \/
 (exists P2', Trans2 (Single (x ??* C)) P2 L P2' /\ Q = parP P1 P2').
intros.
apply
 (inv_trans2_rinP_parP' H (refl_equal (Single (x ??* C))) (refl_equal (parP P1 P2))).
Qed.

Lemma inv_trans2_OutL' :
 forall P Q R L,
 Trans2 R P L Q ->
 forall A b (c : chan A b) v,
 L = OutL c v -> 
 exists C, R = Single (c << v >> C).
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
generalize (OutL_inj1 H); intro.
inversion_clear H0.
generalize c v0 H; clear c v0 H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 A0 b0; intros.
generalize (OutL_inj H); intro.
inversion_clear H0.
rewrite H1; rewrite H2; exists P; auto.
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
auto.
auto.
Qed.

Lemma inv_trans2_OutL :
 forall P Q R A b (c : chan A b) v,
 Trans2 R P (OutL c v) Q -> 
 exists C, R = Single (c << v >> C).
intros.
generalize (inv_trans2_OutL' H (refl_equal (OutL c v)));
 intros.
inversion_clear H0.
injection H1.
intro; exists x; auto.
Qed.

Lemma inv_trans2_InL' :
 forall P Q R L,
 Trans2 R P L Q ->
 forall A b (c : chan A b) v,
 L = InL c v ->
 exists C, R = Single (c ?? C) \/ R = Single (c ??* C).
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
generalize (InL_inj1 H); intro.
inversion_clear H0.
generalize c v0 H; clear c v0 H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 A0 b0; intros.
generalize (InL_inj H); intro.
inversion_clear H0.
rewrite <- H1.
exists C.
auto.
intros.
generalize (InL_inj1 H); intro.
inversion_clear H0.
generalize c v0 H; clear c v0 H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 A0 b0; intros.
generalize (InL_inj H); intro.
inversion_clear H0.
rewrite <- H1.
exists C.
auto.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
auto.
auto.
Qed.

Lemma inv_trans2_InL :
 forall P Q R A b (c : chan A b) v,
 Trans2 R P (InL c v) Q ->
 exists C, 
   R = Single (c ?? C) \/ R = Single (c ??* C).
intros.
apply (inv_trans2_InL' H (refl_equal (InL c v))).
Qed.

Lemma inv_trans2_TauL' :
 forall RS P Q L,
 Trans2 RS P L Q ->
 forall R S : proc,
 RS = Pair R S ->
 forall A b (c : chan A b),
 L = TauL c ->
 exists v,
   (exists T,
      (exists U,
         R = c ??* T /\ S = c << v >> U \/
         R = c ?? T /\ S = c << v >> U \/
         R = c << v >> U /\ S = c ??* T \/ R = c << v >> U /\ S = c ?? T)).
intros RS P Q L H.
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
clear IHTrans0 IHTrans1.
generalize (TauL_inj1 H2); intro X; inversion_clear X.
generalize c H2; clear c H2; rewrite <- H3; rewrite <- H4; clear H3 H4 A0 b0;
 intros.
generalize (TauL_inj H2); intro.
rewrite <- H3; clear H3 c H2.
generalize (inv_trans2_OutL H); intro X; inversion_clear X.
generalize (inv_trans2_InL H1); intro X; inversion_clear X.
injection H0; intros.
rewrite <- H4; rewrite <- H5.
exists v; exists x1; exists x0; inversion_clear H3.
injection H2; injection H6; auto.
injection H2; injection H6; auto.
intros.
clear IHTrans0 IHTrans1.
generalize (TauL_inj1 H2); intro X; inversion_clear X.
generalize c H2; clear c H2; rewrite <- H3; rewrite <- H4; clear H3 H4 A0 b0;
 intros.
generalize (TauL_inj H2); intro.
rewrite <- H3; clear H3 c H2.
generalize (inv_trans2_OutL H1); intro X; inversion_clear X.
generalize (inv_trans2_InL H); intro X; inversion_clear X.
injection H0; intros.
rewrite <- H4; rewrite <- H5.
exists v; exists x1; exists x0; inversion_clear H3.
injection H2; injection H6; auto.
injection H2; injection H6; auto.
auto.
auto.
Qed.

Lemma inv_trans2_TauL :
 forall R S P Q A b (c : chan A b),
 Trans2 (Pair R S) P (TauL c) Q ->
 exists v,
   (exists T,
      (exists U,
         R = c ??* T /\ S = c << v >> U \/
         R = c ?? T /\ S = c << v >> U \/
         R = c << v >> U /\ S = c ??* T \/ R = c << v >> U /\ S = c ?? T)).
intros.
eapply inv_trans2_TauL'.
apply H.
auto.
auto.
Qed.

Lemma inv_trans2_NewL' :
 forall P Q R L,
 Trans2 R P L Q ->
 forall A b (c : chan A b),
 L = NewL c ->
 (exists C : chan A false -> proc, R = Single (nuP C)) \/
 (exists C : chan A true -> proc, R = Single (nuPl C)).
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
generalize (NewL_inj1 H); intro.
intros.
left.
inversion_clear H0.
generalize c H; clear c H; rewrite <- H1; rewrite <- H2; clear H1 H2; intros.
exists C.
auto.
intros.
generalize (NewL_inj1 H); intro.
intros.
right.
inversion_clear H0.
generalize c H; clear c H; rewrite <- H1; rewrite <- H2; clear H1 H2; intros.
exists C.
auto.
intros.
discriminate H0.
intros.
discriminate H0.
auto.
auto.
Qed.

Lemma inv_trans2_NewL :
 forall P Q R A b (c : chan A b),
 Trans2 R P (NewL c) Q ->
 (exists C : chan A false -> proc, R = Single (nuP C)) \/
 (exists C : chan A true -> proc, R = Single (nuPl C)).
intros.
eapply inv_trans2_NewL' with (c := c).
apply H.
auto.
Qed.

Lemma inv_trans2_single_rinP' :
 forall L P Q R,
 Trans2 R P L Q ->
 forall A b (x : chan A b) C,
 R = Single (x ??* C) -> 
 exists v, L = InL x v.
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
generalize (Single_inj H); intro.
generalize (rinP_inj1 H0); intro.
inversion_clear H1.
generalize x0 C0 H H0; clear x0 C0 H H0; rewrite <- H2; rewrite <- H3;
 clear H2 H3 A0 b0; intros.
generalize (rinP_inj_chan H0); intro.
rewrite <- H1.
exists v; auto.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
auto.
auto.
Qed.

Lemma inv_trans2_single_rinP :
 forall A b (x : chan A b) C L P Q,
   Trans2 (Single (x ??* C)) P L Q -> 
   exists v, L = InL x v.
intros.
apply
 (inv_trans2_single_rinP' H (refl_equal (Single (x ??* C)))).
Qed.

Lemma inv_trans2_outP' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A b (x : chan A b) v C,
 P = x << v >> C -> 
 R = Single (x << v >> C) /\ L = OutL x v /\ Q = C.
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
generalize (outP_inj1 H); intro.
inversion_clear H0.
generalize x0 v0 H; clear x0 v0 H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 A0 b0; intros.
generalize (outP_inj_chan_val H); intro.
inversion_clear H0.
generalize H; clear H.
rewrite <- H1; rewrite <- H2; clear H1 H2 x0 v0.
intro.
generalize (outP_inj_cont H); intro.
rewrite H0.
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

Lemma inv_trans2_outP :
 forall R A b (x : chan A b) v C L Q,
 Trans2 R (x << v >> C) L Q ->
 R = Single (x << v >> C) /\ L = OutL x v /\ Q = C.
intros.
apply (inv_trans2_outP' H (refl_equal (x << v >> C))).
Qed.

Lemma inv_trans2_nuP' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A (C : chan A false -> proc),
 P = nuP C ->
 R = Single (nuP C) /\ (exists c, L = NewL c /\ Q = C c).
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
generalize (nuP_inj1 H); intro.
generalize C0 H; clear C0 H; rewrite <- H0; clear H0 A0; intros.
generalize (nuP_inj_cont H); intro.
rewrite <- H0.
split; auto.
exists x.
auto.
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

Lemma inv_trans2_nuP :
 forall R A (C : chan A false -> proc) L Q,
 Trans2 R (nuP C) L Q ->
 R = Single (nuP C) /\ (exists c, L = NewL c /\ Q = C c).
intros.
apply (inv_trans2_nuP' H (refl_equal (nuP C))).
Qed.

Lemma inv_trans2_nuPl' :
 forall R L P Q,
 Trans2 R P L Q ->
 forall A (C : chan A true -> proc),
 P = nuPl C ->
 R = Single (nuPl C) /\ (exists c, L = NewL c /\ Q = C c).
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
generalize (nuPl_inj1 H); intro.
generalize C0 H; clear C0 H; rewrite <- H0; clear H0 A0; intros.
generalize (nuPl_inj_cont H); intro.
rewrite <- H0.
split; auto.
exists x.
auto.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H0.
Qed.

Lemma inv_trans2_nuPl :
 forall R A (C : chan A true -> proc) L Q,
 Trans2 R (nuPl C) L Q ->
 R = Single (nuPl C) /\ (exists c, L = NewL c /\ Q = C c).
intros.
apply (inv_trans2_nuPl' H (refl_equal (nuPl C))).
Qed.

Lemma inv_trans2_rinP_outP_tau' :
 forall R P P' L,
 Trans2 R P L P' ->
 forall A b (c : chan A b),
 L = TauL c ->
 forall T v U,
   R = Pair (c ??* T) (c << v >> U) ->
 exists P1,
   (exists P2,
      P = parP P1 P2 /\
      (exists P1',
         (exists P2',
            Trans2 (Single (c ??* T)) P1 (InL c v) P1' /\
            Trans2 (Single (c << v >> U)) P2 (OutL c v) P2' /\
            P' = parP P1' P2' \/
            Trans2 (Pair (c ??* T) (c << v >> U)) P1 (TauL c) P1' /\
            P' = parP P1' P2 \/
            Trans2 (Pair (c ??* T) (c << v >> U)) P2 (TauL c) P2' /\
            P' = parP P1 P2'))).
intros R P P' L H.
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
clear IHTrans0 IHTrans1.
intros.
injection H2; intros.
rewrite H4 in H.
generalize (inv_trans2_OutL H); intro.
inversion_clear H5.
discriminate H6.
clear IHTrans0 IHTrans1.
intros.
generalize (TauL_inj1 H0); intro.
inversion_clear H3.
generalize c H0 T v0 H2; clear c H0 T v0 H2; rewrite <- H4; rewrite <- H5;
 clear H4 H5 A0 b0; intros.
generalize (TauL_inj H0); clear H0; intro X; rewrite <- X;
 rewrite <- X in H2; clear X c.
exists P; exists Q; split; auto.
exists P'; exists Q'.
left.
injection H2; intros.
rewrite <- H0.
rewrite <- H3.
rewrite H0 in H1.
generalize (inv_trans2_OutL H1); intro.
inversion_clear H4.
generalize (Single_inj H5); intro.
generalize (outP_inj_chan_val H4); intro.
inversion_clear H6.
rewrite H8.
rewrite <- H0 in H1.
auto.
intros.
generalize (IHTrans2 _ _ _ H0 _ _ _ H1); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
decompose [and] H3; clear H3.
exists P; exists Q; split; auto.
exists (parP x1 x2).
exists Q.
right; left.
rewrite H7; split; auto.
rewrite H2.
eapply tr2_comIO.
apply H4.
auto.
inversion_clear H3.
inversion_clear H4.
exists P; exists Q; split; auto.
exists (parP x1 x0).
exists Q.
right; left.
rewrite H5; split; auto.
rewrite H2.
apply tr2_parL.
auto.
inversion_clear H4.
exists P; exists Q; split; auto.
exists (parP x x2).
exists Q.
right; left.
rewrite H5; split; auto.
rewrite H2.
apply tr2_parR.
auto.
intros.
generalize (IHTrans2 _ _ _ H0 _ _ _ H1); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
decompose [and] H3; clear H3.
exists Q; exists P; split; auto.
exists zeroP; exists P'.
right; right.
split; auto.
rewrite H2; rewrite H7.
eapply tr2_comIO.
apply H4.
auto.
inversion_clear H3.
inversion_clear H4.
exists Q; exists P.
split; auto.
exists zeroP; exists P'.
right; right.
split; auto.
rewrite H2; rewrite H5; eapply tr2_parL.
auto.
inversion_clear H4.
exists Q; exists P.
split; auto.
exists zeroP; exists P'.
right; right.
split; auto.
rewrite H2; rewrite H5; eapply tr2_parR.
auto.
Qed.

Lemma inv_trans2_rinP_outP_tau :
 forall P P' A b (c : chan A b) T v U,
 Trans2 (Pair (c ??* T) (c << v >> U)) P (TauL c) P' ->
 exists P1,
   (exists P2,
      P = parP P1 P2 /\
      (exists P1',
         (exists P2',
            Trans2 (Single (c ??* T)) P1 (InL c v) P1' /\
            Trans2 (Single (c << v >> U)) P2 (OutL c v) P2' /\
            P' = parP P1' P2' \/
            Trans2 (Pair (c ??* T) (c << v >> U)) P1 (TauL c) P1' /\
            P' = parP P1' P2 \/
            Trans2 (Pair (c ??* T) (c << v >> U)) P2 (TauL c) P2' /\
            P' = parP P1 P2'))).
intros.
eapply inv_trans2_rinP_outP_tau'.
apply H.
auto.
auto.
Qed.

Lemma inv_trans2_outP_rinP_tau' :
 forall R P P' L,
 Trans2 R P L P' ->
 forall A b (c : chan A b),
 L = TauL c ->
 forall T v U,
 R = Pair (c << v >> U) (c ??* T) ->
 exists P1,
   (exists P2,
      P = parP P1 P2 /\
      (exists P1',
         (exists P2',
            Trans2 (Single (c << v >> U)) P1 (OutL c v) P1' /\
            Trans2 (Single (c ??* T)) P2 (InL c v) P2' /\ P' = parP P1' P2' \/
            Trans2 (Pair (c << v >> U) (c ??* T)) P1 (TauL c) P1' /\
            P' = parP P1' P2 \/
            Trans2 (Pair (c << v >> U) (c ??* T)) P2 (TauL c) P2' /\
            P' = parP P1 P2'))).
intros R P P' L H.
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
generalize (TauL_inj1 H0); intro.
inversion_clear H3.
generalize c H0 T v0 H2; clear c H0 T v0 H2; rewrite <- H4; rewrite <- H5;
 clear H4 H5 A0 b0; intros.
generalize (TauL_inj H0); clear H0; intro X; rewrite <- X;
 rewrite <- X in H2; clear X c.
exists P; exists Q; split; auto.
exists P'; exists Q'.
left.
injection H2; intros.
rewrite <- H0.
rewrite <- H3.
rewrite H3 in H.
generalize (inv_trans2_OutL H); intro.
inversion_clear H4.
generalize (Single_inj H5); intro.
generalize (outP_inj_chan_val H4); intro.
inversion_clear H6.
rewrite H8.
rewrite <- H3 in H.
auto.
intros.
clear IHTrans0 IHTrans1.
intros.
injection H2; intros.
rewrite H4 in H.
generalize (inv_trans2_InL H); intro.
inversion_clear H5.
inversion_clear H6.
discriminate H5.
discriminate H5.
intros.
generalize (IHTrans2 _ _ _ H0 _ _ _ H1); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
decompose [and] H3; clear H3.
exists P; exists Q; split; auto.
exists (parP x1 x2).
exists Q.
right; left.
rewrite H7; split; auto.
rewrite H2.
eapply tr2_comOI.
apply H4.
auto.
inversion_clear H3.
inversion_clear H4.
exists P; exists Q; split; auto.
exists (parP x1 x0).
exists Q.
right; left.
rewrite H5; split; auto.
rewrite H2.
apply tr2_parL.
auto.
inversion_clear H4.
exists P; exists Q; split; auto.
exists (parP x x2).
exists Q.
right; left.
rewrite H5; split; auto.
rewrite H2.
apply tr2_parR.
auto.
intros.
generalize (IHTrans2 _ _ _ H0 _ _ _ H1); intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H3.
inversion_clear H4.
decompose [and] H3; clear H3.
exists Q; exists P; split; auto.
exists zeroP; exists P'.
right; right.
split; auto.
rewrite H2; rewrite H7.
eapply tr2_comOI.
apply H4.
auto.
inversion_clear H3.
inversion_clear H4.
exists Q; exists P.
split; auto.
exists zeroP; exists P'.
right; right.
split; auto.
rewrite H2; rewrite H5; eapply tr2_parL.
auto.
inversion_clear H4.
exists Q; exists P.
split; auto.
exists zeroP; exists P'.
right; right.
split; auto.
rewrite H2; rewrite H5; eapply tr2_parR.
auto.
Qed.

Lemma inv_trans2_outP_rinP_tau :
 forall P P' A b (c : chan A b) T v U,
 Trans2 (Pair (c << v >> U) (c ??* T)) P (TauL c) P' ->
 exists P1,
   (exists P2,
      P = parP P1 P2 /\
      (exists P1',
         (exists P2',
            Trans2 (Single (c << v >> U)) P1 (OutL c v) P1' /\
            Trans2 (Single (c ??* T)) P2 (InL c v) P2' /\ P' = parP P1' P2' \/
            Trans2 (Pair (c << v >> U) (c ??* T)) P1 (TauL c) P1' /\
            P' = parP P1' P2 \/
            Trans2 (Pair (c << v >> U) (c ??* T)) P2 (TauL c) P2' /\
            P' = parP P1 P2'))).
intros.
eapply inv_trans2_outP_rinP_tau'.
apply H.
auto.
auto.
Qed.

Lemma Trans2_Pair_rinP_Rcplmt' :
 forall Ps P Q L,
 Trans2 Ps P L Q ->
 forall A b (c : chan A b) T R,
 Ps = Pair (c ??* T) R ->
 (exists v, 
   (exists U, R = c << v >> U)) /\ L = TauL c.
intros Ps P Q L H.
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
injection H0; intros.
rewrite H3 in H; intros.
generalize (inv_trans2_single_rinP H); intros.
inversion_clear H4.
discriminate H5.
intros.
injection H0; intros.
rewrite H3 in H.
generalize (inv_trans2_InL H); intro.
inversion_clear H4.
inversion_clear H5.
discriminate H4.
generalize (Single_inj H4); intros.
generalize (rinP_inj1 H5); intros.
inversion_clear H6.
generalize c T H0 H3 H H4 H5; clear c T H0 H3 H H4 H5; rewrite H7; rewrite H8;
 clear H7 H8 A0 b0; intros.
generalize (rinP_inj_chan H5); intros.
generalize H0 H3 H H4 H5; clear H0 H3 H H4 H5; rewrite H6; clear H6 c; intros.
generalize (inv_trans2_OutL H1); intro.
inversion_clear H6.
generalize (Single_inj H7); intros.
split; auto.
exists v; exists x1; auto.
rewrite <- H2; auto.
auto.
auto.
Qed.

Lemma Trans2_Pair_rinP_Rcplmt :
 forall P Q L A b (c : chan A b) T R,
 Trans2 (Pair (c ??* T) R) P L Q ->
 (exists v, 
   (exists U, R = c << v >> U)) /\ L = TauL c.
intros.
apply
 (Trans2_Pair_rinP_Rcplmt' H (refl_equal (Pair (c ??* T) R))).
Qed.

Lemma Trans2_Pair_rinP_Lcplmt' :
 forall Ps P Q L,
 Trans2 Ps P L Q ->
 forall A b (c : chan A b) T R,
 Ps = Pair R (c ??* T) ->
 (exists v, 
   (exists U, R = c << v >> U)) /\ L = TauL c.
intros Ps P Q L H.
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
injection H0; intros.
rewrite H2 in H1; intros.
generalize (inv_trans2_single_rinP H1); intros.
inversion_clear H4.
generalize (inv_trans2_OutL H); intro.
inversion_clear H4.
generalize (Single_inj H6); intros.
generalize (inv_trans2_InL H1); intro.
inversion_clear H7.
inversion_clear H8.
generalize (Single_inj H7); intros.
discriminate H8.
generalize (Single_inj H7); intros.
generalize (rinP_inj1 H8); intros.
inversion_clear H9.
generalize c T H0 H1 x0 H2 H5 H7 H8; clear c T H0 x0 H1 H2 H5 H7 H8;
 rewrite H10; rewrite H11; clear H10 H11 A0 b0; intros.
generalize (rinP_inj_chan H8); intros.
rewrite H9.
split; auto.
exists v.
exists x1; rewrite <- H3; auto.
intros.
injection H0; intros.
rewrite H2 in H1.
generalize (inv_trans2_OutL H1); intro.
inversion_clear H4.
discriminate H5.
auto.
auto.
Qed.

Lemma Trans2_Pair_rinP_Lcplmt :
 forall P Q L A b (c : chan A b) T R,
 Trans2 (Pair R (c ??* T)) P L Q ->
 (exists v, 
   (exists U, R = c << v >> U)) /\ L = TauL c.
intros.
apply
 (Trans2_Pair_rinP_Lcplmt' H (refl_equal (Pair R (c ??* T)))).
Qed.

(** application: trans2 is not reflexive *)

Lemma Trans2_not_refl :
 forall P R L, 
   Trans2 R P L P -> False.
intro.
induction P.
intros.
inversion_clear H.
intros.
generalize (inv_trans2_inP H0); intros.
inversion_clear H1.
inversion_clear H3.
inversion_clear H1.
rewrite H4 in H0.
eapply H.
apply H0.
intros.
generalize (inv_trans2_rinP H0); intros.
inversion_clear H1.
inversion_clear H3.
inversion_clear H1.
discriminate H4.
intros.
generalize (inv_trans2_outP H); intros.
decompose [and] H0; clear H0.
rewrite H4 in H.
eapply IHP.
apply H.
intros.
inversion H.
eapply IHP1.
apply H5.
eapply IHP1.
apply H5.
eapply IHP1.
apply H4.
eapply IHP2.
apply H4.
intros.
generalize (inv_trans2_nuP H0); intros.
inversion_clear H1.
inversion_clear H3.
inversion_clear H1.
rewrite H4 in H0.
eapply H.
apply H0.
intros.
generalize (inv_trans2_nuPl H0); intros.
inversion_clear H1.
inversion_clear H3.
inversion_clear H1.
rewrite H4 in H0.
eapply H.
apply H0.
Qed.

Unset Implicit Arguments.