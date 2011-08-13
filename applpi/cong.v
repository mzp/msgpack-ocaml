Require Import chan.
Require Import applpi.

(** structural congruence, standard definition (except that it does not define scope extrusion) *)

Set Implicit Arguments.

Inductive Cong : proc -> proc -> Prop :=
  | cong_zero : forall P, Cong P (parP P zeroP)
  | cong_comm : forall P Q, Cong (parP P Q) (parP Q P)
  | cong_assoc : forall P Q R, 
    Cong (parP (parP P Q) R) (parP P (parP Q R))
  | cong_par : forall P Q P' Q',
      Cong P P' -> Cong Q Q' -> Cong (parP P Q) (parP P' Q')
  | cong_rep : forall A b (x : chan A b) C,
      Cong (x ??* C) (parP (x ??* C) (x ?? C))
      (* TODO:
       | cong_rep2: (A:Set)(b:bool)(x:(chan A b))(C:A->proc)
      	(Cong (rinP x C) (parP (rinP x C) (rinP x C)))
        useless? *)
  | cong_refl : forall P, Cong P P
  | cong_sym : forall P Q, Cong P Q -> Cong Q P
  | cong_tr : forall P Q R, Cong P Q -> Cong Q R -> Cong P R.

(** structural congruence properties of the inert process *)

Inductive zeros_only : proc -> Prop :=
  | one_zero : zeros_only zeroP
  | par_zero : forall P,
      zeros_only P -> forall Q, zeros_only Q -> zeros_only (parP P Q).

Lemma cong_zero_zeros_only :
  forall P Q, Cong Q P -> (zeros_only Q <-> zeros_only P).
intros P Q H.
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
apply par_zero.
auto.
apply one_zero.
inversion_clear H.
auto.
split.
intros.
inversion_clear H.
apply par_zero.
auto.
auto.
intros.
inversion_clear H.
apply par_zero.
auto.
auto.
split; intros.
inversion_clear H.
inversion_clear H0.
apply par_zero.
auto.
apply par_zero.
auto.
auto.
inversion_clear H.
inversion_clear H1.
apply par_zero.
apply par_zero.
auto.
auto.
auto.
split; intros.
inversion_clear H0.
apply par_zero.
inversion_clear IHCong1.
apply H0.
auto.
inversion_clear IHCong2.
apply H0.
auto.
inversion_clear H0.
apply par_zero.
inversion_clear IHCong1.
apply H4.
auto.
inversion_clear IHCong2.
apply H4.
auto.
split.
intros.
inversion_clear H.
intros.
inversion_clear H.
inversion_clear H0.
tauto.
tauto.
tauto.
Qed.

Lemma zeros_only_cong_zeroP : forall P, zeros_only P -> Cong P zeroP.
intros.
induction H as [| P H IHzeros_only1 Q H1 IHzeros_only2].
apply cong_refl.
apply cong_tr with (parP zeroP zeroP).
apply cong_par.
auto.
auto.
apply cong_sym.
apply cong_zero.
Qed.

Lemma cong_parP_zeroP :
  forall P Q, Cong (parP P Q) zeroP -> Cong P zeroP /\ Cong Q zeroP.
intros.
generalize (cong_zero_zeros_only H); intro.
inversion_clear H0.
assert (zeros_only zeroP).
apply one_zero.
generalize (H2 H0); intro.
inversion_clear H3.
generalize (zeros_only_cong_zeroP H4).
generalize (zeros_only_cong_zeroP H5).
intuition.
Qed.

Unset Implicit Arguments.