Require Import Classical.
Require Import applpi.
Require Import cong.
Require Import logic.

 (** extensions to original logic, include a fixpoint operator *)

Set Implicit Arguments.

Axiom NEXT : tform -> tform.

Axiom NEXT_satisfaction : forall P G,
    tsat (NEXT G) P <-> (exists Q, Red P Q /\ tsat G Q).

Lemma NEXT_sat : forall P G,
 (exists Q, Red P Q /\ tsat G Q) -> tsat (NEXT G) P.
intros.
generalize (NEXT_satisfaction P G); intro X; inversion_clear X.
apply H1.
auto.
Qed.

Lemma NEXT_sat_inv : forall P G,
 P |=t (NEXT G) -> exists Q, Red P Q /\ tsat G Q.
intros.
generalize (NEXT_satisfaction P G); intro X; inversion_clear X.
apply H0.
auto.
Qed.

Definition MUST_NEXT f := NEGT (NEXT (NEGT f)).

Lemma MUST_NEXT_sat_inv : forall f P,
 tsat (MUST_NEXT f) P -> forall Q, Red P Q -> tsat f Q.
intros.
unfold MUST_NEXT in H.
generalize (NEGT_sat_inv H); clear H; intro.
apply NNPP.
intro.
apply H.
apply NEXT_sat.
exists Q.
split.
auto.
apply NEGT_sat.
auto.
Qed.

Lemma MUST_NEXT_sat : forall P G,
 (forall Q, Red P Q -> tsat G Q) -> tsat (MUST_NEXT G) P.
intros.
unfold MUST_NEXT in |- *.
apply NEGT_sat.
intro.
generalize (NEXT_sat_inv H0); clear H0; intro.
inversion_clear H0.
inversion_clear H1.
generalize (NEGT_sat_inv H2); clear H2; intro.
apply H1.
apply H.
auto.
Qed.

Axiom GUA : form -> form -> form.

Axiom GUA_satisfaction : forall L P F G,
  (L # P) |= (GUA F G) <->
  (forall P', (L # P') |= F -> (L # parP P P') |= G).

Lemma GUA_sat : forall L P F G,
  (forall P', sat F (L # P') -> sat G (L # parP P P')) ->
  sat (GUA F G) (L # P).
intros.
generalize (GUA_satisfaction L P F G); intro X; inversion_clear X.
auto.
Qed.

Lemma CONSISTS_GUA_ADJ : forall F G H,
  (forall P, sat (CONSISTS F G) P -> sat H P) ->
  forall P, sat F P -> sat (GUA G H) P.
intros.
induction P.
apply GUA_sat.
intros.
apply H0.
apply CONSISTS_sat.
exists b.
exists P'.
split; auto.
apply cong_refl.
Qed.

Axiom STABLE : tform.

Axiom STABLE_satisfaction :
    forall P, P |=t STABLE <-> ~ (exists Q, Red P Q).

Lemma STABLE_sat : forall P, 
  ~ (exists Q, Red P Q) -> P |=t STABLE.
intro.
generalize (STABLE_satisfaction P); intro X; inversion_clear X; auto.
Qed.

Lemma STABLE_sat_inv : forall P, 
  P |=t STABLE -> ~ (exists Q, Red P Q).
intro.
generalize (STABLE_satisfaction P); intro X; inversion_clear X; auto.
Qed.

Require Import chan.
Require Import chanlist.
Require Import logic.

Axiom MU : (tform -> tform) -> tform.

Axiom MU_satisfaction : forall F P,
  tsat (MU F) P <->
  (forall p,
    (forall Q, tsat (F p) Q -> (Q |=t p)) -> tsat p P).

Lemma MU_sat : forall F P,
  (forall p, 
    (forall Q, tsat (F p) Q -> tsat p Q) -> tsat p P) -> tsat (MU F) P.
intros.
generalize (MU_satisfaction F P); intros.
inversion_clear H0.
auto.
Qed.

Lemma MU_sat_inv : forall F P,
  tsat (MU F) P ->
  forall p, 
    (forall Q, tsat (F p) Q -> tsat p Q) -> tsat p P.
intros.
generalize (MU_satisfaction F P); intros.
inversion_clear H1.
auto.
Qed.

Definition MUSTEV_ALT F :=
  MU (fun p => ORT F (ANDT (NEGT STABLE) (MUST_NEXT p))).

Unset Implicit Arguments.





