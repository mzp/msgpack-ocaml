Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import inj.
Require Import cong.
Require Import cong_tactic.
Require Import cong_resp.

(** infer the shape of the process given some action *)

Set Implicit Arguments.

Lemma inv_trans_OutL' :
 forall P Q l,
 Trans P l Q ->
 forall A b (c : chan A b) v,
 l = OutL c v ->
 exists C,
   (exists obs, Cong P (parP obs (c << v >> C)) /\ Cong Q (parP obs C)).
intros P l Q H.
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
generalize (OutL_inj1 H); intros.
inversion_clear H0.
generalize c v0 H; clear c v0 H.
rewrite <- H1.
rewrite <- H2.
clear H1 H2.
intros.
generalize (OutL_inj H); intro.
inversion_clear H0.
rewrite H1; rewrite H2.
exists P.
exists zeroP.
split; [ ProcCong | ProcCong ].
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
generalize (IHTrans _ _ _ _ H0); intro X; inversion_clear X.
inversion_clear H1.
exists x.
exists (parP x0 Q).
split.
apply cong_tr with (parP (parP x0 (c << v >> x)) Q).
apply cong_par.
intuition.
apply cong_refl.
ProcCong.
apply cong_tr with (parP (parP x0 x) Q).
apply cong_par.
intuition.
apply cong_refl.
ProcCong.
intros.
generalize (IHTrans _ _ _ _ H0); intro X; inversion_clear X.
inversion_clear H1.
exists x.
exists (parP Q x0).
split.
apply cong_tr with (parP Q (parP x0 (c << v >> x))).
apply cong_par.
apply cong_refl.
intuition.
ProcCong.
apply cong_tr with (parP Q (parP x0 x)).
apply cong_par.
apply cong_refl.
intuition.
ProcCong.
Qed.

Lemma inv_trans_OutL :
 forall P Q A b (c : chan A b) v,
 Trans P (OutL c v) Q ->
 exists C,
   (exists obs, Cong P (parP obs (c << v >> C)) /\ Cong Q (parP obs C)).
intros.
apply inv_trans_OutL' with (l := OutL c v).
auto.
auto.
Qed.

Lemma inv_trans_InL' :
 forall P Q l,
 Trans P l Q ->
 forall A b (c : chan A b) v,
 l = InL c v ->
 exists C,
   (exists obs, Cong P (parP obs (c ?? C)) /\ Cong Q (parP obs (C v))).
intros P Q l H.
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
generalize (InL_inj1 H); intros.
inversion_clear H0.
generalize c v0 H; clear c v0 H.
rewrite <- H1.
rewrite <- H2.
clear H1 H2; intros.
generalize (InL_inj H); intros.
inversion_clear H0.
rewrite <- H1.
rewrite <- H2.
exists C.
exists zeroP.
split; [ ProcCong | ProcCong ].
intros.
generalize (InL_inj1 H); intros.
inversion_clear H0.
generalize c v0 H; clear c v0 H.
rewrite <- H1.
rewrite <- H2.
clear H1 H2; intros.
generalize (InL_inj H); intros.
inversion_clear H0.
rewrite <- H1.
rewrite <- H2.
exists C.
exists (x ??* C).
split.
apply cong_rep.
apply cong_refl.
intros.
discriminate H.
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
generalize (IHTrans _ _ _ _ H0); intro X; inversion_clear X.
exists x.
inversion_clear H1.
exists (parP x0 Q).
split.
inversion_clear H2.
apply cong_tr with (parP (parP x0 (c ?? x)) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
inversion_clear H2.
apply cong_tr with (parP (parP x0 (x v)) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
intros.
generalize (IHTrans _ _ _ _ H0); intro X; inversion_clear X.
exists x.
inversion_clear H1.
exists (parP Q x0).
split.
inversion_clear H2.
apply cong_tr with (parP Q (parP x0 (c ?? x))).
apply cong_par.
auto.
apply cong_refl.
auto.
ProcCong.
inversion_clear H2.
apply cong_tr with (parP Q (parP x0 (x v))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
Qed.

Lemma inv_trans_InL :
 forall P Q A b (c : chan A b) v,
 Trans P (InL c v) Q ->
 exists C,
   (exists obs, Cong P (parP obs (c ?? C)) /\ Cong Q (parP obs (C v))).
intros.
apply inv_trans_InL' with (l := InL c v).
auto.
auto.
Qed.

Lemma trans_InL_some_any :
 forall P Q A b (c : chan A b) v,
 Trans P (InL c v) Q -> 
 forall w, 
   exists Q', Trans P (InL c w) Q'.
intros.
generalize (inv_trans_InL H); intros.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
assert (exists Q' : proc, Trans (parP x0 (c ?? x)) (InL c w) Q').
exists (parP x0 (x w)).
apply tr_parR.
apply tr_in.
inversion_clear H0.
generalize (cong_respects_trans H3 (cong_sym H1)); intro.
inversion_clear H0.
inversion_clear H4.
exists x2.
auto.
Qed.

Lemma inv_trans_NewL_nuP' :
 forall P Q l,
 Trans P l Q ->
 forall A (c : chan A false),
 l = NewL c ->
 exists obs,
   (exists C,
      Cong P (parP obs (nuP C)) /\ Cong Q (parP obs (C c))).
intros P Q l H;
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
generalize (NewL_inj1 H); intro.
inversion_clear H0.
discriminate H2.
intros.
generalize (NewL_inj1 H); intro.
inversion_clear H0.
clear H2; generalize c H; clear c H; rewrite <- H1; clear H1 A0; intros.
generalize (NewL_inj H); intro.
clear H.
rewrite <- H0; clear H0 c.
exists zeroP.
exists C.
split.
ProcCong.
ProcCong.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
generalize (IHTrans _ _ H0); intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists (parP x Q).
exists x0.
split.
apply cong_tr with (parP (parP x (nuP x0)) Q).
apply cong_par.
auto.
ProcCong.
ProcCong.
apply cong_tr with (parP (parP x (x0 c)) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
intros.
generalize (IHTrans _ _ H0); intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists (parP Q x).
exists x0.
split.
apply cong_tr with (parP Q (parP x (nuP x0))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
apply cong_tr with (parP Q (parP x (x0 c))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
Qed.

Lemma inv_trans_NewL_nuP :
 forall P Q A (c : chan A false),
 Trans P (NewL c) Q ->
 exists obs,
   (exists C,
      Cong P (parP obs (nuP C)) /\ Cong Q (parP obs (C c))).
intros.
apply inv_trans_NewL_nuP' with (NewL c).
auto.
auto.
Qed.


Lemma inv_trans_NewL_nuPl' :
 forall P Q l,
 Trans P l Q ->
 forall A (c : chan A true),
 l = NewL c ->
 exists obs,
   (exists C,
      Cong P (parP obs (nuPl C)) /\ Cong Q (parP obs (C c))).
intros P Q l H;
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
generalize (NewL_inj1 H); intro.
inversion_clear H0.
clear H2; generalize c H; clear c H; rewrite <- H1; clear H1 A0; intros.
generalize (NewL_inj H); intro.
clear H.
rewrite <- H0; clear H0 c.
exists zeroP.
exists C.
split.
ProcCong.
ProcCong.
intros.
generalize (NewL_inj1 H); intro.
inversion_clear H0.
discriminate H2.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
generalize (IHTrans _ _ H0); intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists (parP x Q).
exists x0.
split.
apply cong_tr with (parP (parP x (nuPl x0)) Q).
apply cong_par.
auto.
ProcCong.
ProcCong.
apply cong_tr with (parP (parP x (x0 c)) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
intros.
generalize (IHTrans _ _ H0); intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists (parP Q x).
exists x0.
split.
apply cong_tr with (parP Q (parP x (nuPl x0))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
apply cong_tr with (parP Q (parP x (x0 c))).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
Qed.

Lemma inv_trans_NewL_nuPl :
 forall P Q A (c : chan A true),
 Trans P (NewL c) Q ->
 exists obs,
   (exists C,
      Cong P (parP obs (nuPl C)) /\ Cong Q (parP obs (C c))).
intros.
apply inv_trans_NewL_nuPl' with (NewL c).
auto.
auto.
Qed.

Unset Implicit Arguments.
