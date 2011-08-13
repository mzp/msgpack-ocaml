Require Import Classical.
Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import inv.
Require Import redseq.
Require Import cong.
Require Import cong_tactic.
Require Import cong_resp.
Require Import cong_trans.
Require Import logic.
Require Import free_chans.

Set Implicit Arguments.

 (** properties of logic operators *)

(** involution of negation *)
Lemma NEG_NEG : forall F P, sat (NEG (NEG F)) P -> sat F P.
intros.
generalize (NEG_sat_inv H); intro.
apply NNPP.
intro.
apply H0.
apply NEG_sat.
auto.
Qed.

Lemma not_OR_AND : forall F G P,
 ~ sat (OR F G) P -> sat (AND (NEG F) (NEG G)) P.
intros.
unfold AND in |- *.
apply NEG_sat.
intro.
apply H.
apply OR_sat.
generalize (OR_sat_inv H0); intro.
inversion_clear H1.
left.
apply (NEG_NEG H2).
right.
apply (NEG_NEG H2).
Qed.

Lemma not_AND_OR : forall F G P,
 ~ sat (AND F G) P -> sat (OR (NEG F) (NEG G)) P.
intros.
apply NNPP.
intro.
apply H.
apply AND_sat.
generalize (not_OR_AND H0); intro.
generalize (AND_sat_inv H1); intro.
inversion_clear H2.
generalize (NEG_NEG H4); intro.
generalize (NEG_NEG H3); intro.
auto.
Qed.

(** De Morgan law *)
Lemma NEG_AND_OR : forall F G P,
 sat (NEG (AND F G)) P -> sat (OR (NEG F) (NEG G)) P.
intros.
apply OR_sat.
generalize (NEG_sat_inv H); intro.
generalize (not_AND_OR H0); intro.
generalize (OR_sat_inv H1); intro.
auto.
Qed.

Lemma intro_left_OR : forall f P, sat f P -> forall g, sat (OR f g) P.
intros.
apply OR_sat.
left.
auto.
Qed.

Lemma intro_right_OR : forall f P, sat f P -> forall g, sat (OR g f) P.
intros.
apply OR_sat.
right.
auto.
Qed.

Lemma DISTR_CONSISTS_AND : forall F G H P,
 sat (CONSISTS (AND F G) H) P -> sat (AND (CONSISTS F H) (CONSISTS G H)) P.
intros.
induction P.
generalize (CONSISTS_sat_inv H0); clear H0; intros.
inversion_clear H0.
inversion_clear H1.
decompose [and] H0; clear H0.
generalize (AND_sat_inv H3); clear H3; intro.
inversion_clear H0.
apply AND_sat.
split.
apply CONSISTS_sat.
exists x; exists x0.
split.
auto.
split; auto.
apply CONSISTS_sat.
exists x.
exists x0.
split; auto.
Qed.

(*Lemma FACTO_CONSISTS_AND : ((F,G,H:form)(P:state)(sat (AND (CONSISTS F H) (CONSISTS G H)) P) -> 
 (sat (CONSISTS (AND F G) H) P)).
Intros.
Generalize (AND_sat_inv H0); Clear H0; Intro.
Inversion_clear H0.
NewInduction P.
Generalize (CONSISTS_sat_inv H1); Clear H1; Intros.
Inversion_clear H0.
Inversion_clear H1.
Decompose [and] H0;Clear H0.
Generalize (CONSISTS_sat_inv H2); Clear H2; Intros.
Inversion_clear H0.
Inversion_clear H2.
Decompose [and] H0;Clear H0.*)

(*Fact NO_DISTR_CONSISTS_AND : ((F,G,H:form)(P:state)(sat (AND (CONSISTS F H) (CONSISTS G H)) P) -> 
 (sat (CONSISTS (AND F G) H) P)) -> False.
Intros.
Generalize (choose_fresh nat nilC); Intros.
Inversion_clear H0.
Generalize (choose_fresh nat (x&nilC)); Intros.
Inversion_clear H0.
Generalize (choose_fresh nat (x0&(x&nilC))); Intros.
Inversion_clear H0.
Assert (sat 
 (AND 
   (CONSISTS (ISOUTPUT x O (ISOUTPUT x0 O ISANY)) (ISOUTPUT x O ISANY)) 
   (CONSISTS (ISOUTPUT x O (ISOUTPUT x1 O ISANY)) (ISOUTPUT x O ISANY))) 
 (x0&(x&nilC))#(parP (outP x O (OutAtom x0 O)) (outP x O (OutAtom x1 O)))).
Apply AND_sat.
Split.
Apply CONSISTS_sat.
Exists (outP x O (OutAtom x0 O)).
Exists (outP x O (OutAtom x1 O)).
Split.
Apply cong_refl.
Split.
Apply ISOUTPUT_sat.
Exists zeroP.
Exists (OutAtom x0 O).
Split.
ProcCong.
Apply ISOUTPUT_sat.
Exists zeroP.
Exists zeroP.
Split.
Unfold OutAtom.
ProcCong.
Auto.
Apply ISOUTPUT_sat.
Exists zeroP.
Exists (OutAtom x1 O).
Split.
ProcCong.
Auto.
Apply CONSISTS_sat.
Exists (outP x O (OutAtom x1 O)).
Exists (outP x O (OutAtom x0 O)).
Split.
Apply cong_comm.
Split.
Apply ISOUTPUT_sat.
Exists zeroP.
Exists (OutAtom x1 O).
Split.
ProcCong.
Apply ISOUTPUT_sat.
Exists zeroP.
Exists zeroP.
Split.
Unfold OutAtom.
ProcCong.
Auto.
Apply ISOUTPUT_sat.
Exists zeroP.
Exists (OutAtom x0 O).
Split.
ProcCong.
Apply ISANY_sat.
Generalize (H ? ? ? ? H0); Intro.
Generalize (CONSISTS_sat_inv H4); Clear H4; Intro X; Inversion_clear X.
Inversion_clear H4.
Decompose [and] H5;Clear H5.
Generalize (AND_sat_inv H7); Clear H7; Intro.
Inversion_clear H5.

Lemma cong_par_inv : 
(R,T:proc)
(Cong R T) ->
(P,Q,U,V:proc)(A,B:Set)(b,b':bool)
(c:(chan A b);d:(chan B b'))(u:A;v:B)
R==(parP (outP c u U) (outP d v V)) ->
T==(parP P Q) -> 
((Cong P (parP (outP c u U) (outP d v V)))/\(Cong Q zeroP))\/
((Cong Q (parP (outP c u U) (outP d v V)))/\(Cong P zeroP))\/
((Cong P (outP c u U))/\(Cong Q (outP d v V)))\/
((Cong Q (outP c u U))/\(Cong P (outP d v V))).
Do 3 Intro.
NewInduction H.
Intros.
Left.
Injection H0; Intros.
Rewrite <-H1.
Rewrite <-H2; Rewrite H.
Split; ProcCong.
Intros.
Injection H; Injection H0; Intros.
Right; Right; Right.
Rewrite <-H1; Rewrite <-H2.
Rewrite H4; Rewrite H3.
Split; ProcCong.
Intros.
Discriminate H.
Intros.
Injection H0; Injection H2; Intros.
Right; Right; Left.
Rewrite <-H4; Rewrite <-H3.
Split; [Apply cong_tr with P | Apply cong_tr with Q].
Apply cong_sym; Auto.
Rewrite H6; ProcCong.
Apply cong_sym; Auto.
Rewrite H5; ProcCong.
Intros.
Discriminate H.
Intros.
Right; Right; Left.
Rewrite H0 in H; Injection H; Intros.
Rewrite H2; Rewrite H1; Split; ProcCong.
Intros.
Abort.

*)

Lemma DISTR_CONSISTS_OR : forall F G H P,
 sat (OR (CONSISTS F H) (CONSISTS G H)) P <-> sat (CONSISTS (OR F G) H) P.
split.
intros.
generalize (OR_sat_inv H0); intro.
inversion_clear H1.
induction P.
generalize (CONSISTS_sat_inv H2).
intro X; inversion_clear X.
inversion_clear H1.
decompose [and] H3; clear H3.
apply CONSISTS_sat.
exists x.
exists x0.
split.
auto.
split; auto.
apply OR_sat.
auto.
induction P.
generalize (CONSISTS_sat_inv H2).
intro X; inversion_clear X.
inversion_clear H1.
decompose [and] H3; clear H3.
apply CONSISTS_sat.
exists x.
exists x0.
split.
auto.
split; auto.
apply OR_sat.
auto.
intros.
induction P.
generalize (CONSISTS_sat_inv H0).
intro X; inversion_clear X.
inversion_clear H1.
decompose [and] H2; clear H2.
generalize (OR_sat_inv H4); intro.
inversion_clear H2.
apply OR_sat.
left.
apply CONSISTS_sat.
exists x.
exists x0.
split.
auto.
auto.
apply OR_sat.
right.
apply CONSISTS_sat.
exists x.
exists x0.
auto.
Qed.

(** properties of temporal predicates *)

Lemma NEGT_NEGT : forall F P, tsat (NEGT (NEGT F)) P -> tsat F P.
intros.
generalize (NEGT_sat_inv H); intro.
apply NNPP.
intro.
apply H0.
apply NEGT_sat.
auto.
Qed.

Lemma not_ORT_ANDT : forall F G P,
 ~ tsat (ORT F G) P -> tsat (ANDT (NEGT F) (NEGT G)) P.
intros.
unfold ANDT in |- *.
apply NEGT_sat.
intro.
apply H.
apply ORT_sat.
generalize (ORT_sat_inv H0); intro.
inversion_clear H1.
left.
apply (NEGT_NEGT H2).
right.
apply (NEGT_NEGT H2).
Qed.

Lemma not_ANDT_ORT : forall F G P,
 ~ tsat (ANDT F G) P -> tsat (ORT (NEGT F) (NEGT G)) P.
intros.
apply NNPP.
intro.
apply H.
apply ANDT_sat.
generalize (not_ORT_ANDT H0); intro.
generalize (ANDT_sat_inv H1); intro.
inversion_clear H2.
generalize (NEGT_NEGT H4); intro.
generalize (NEGT_NEGT H3); intro.
auto.
Qed.

Lemma NEGT_ANDT_ORT : forall F G P,
 tsat (NEGT (ANDT F G)) P -> tsat (ORT (NEGT F) (NEGT G)) P.
intros.
apply ORT_sat.
generalize (NEGT_sat_inv H); intro.
generalize (not_ANDT_ORT H0); intro.
generalize (ORT_sat_inv H1); intro.
auto.
Qed.

Lemma MAYEV_prefix : forall P Q p,
 Red P Q -> tsat (MAYEV p) Q -> tsat (MAYEV p) P.
intros.
apply MAYEV_sat.
generalize (MAYEV_sat_inv H0); intro.
inversion_clear H1.
exists x.
split.
apply reds_trans with Q.
auto.
apply reds_i with Q.
auto.
apply reds_b.
intuition.
intuition.
Qed.

Lemma idempotence_ALWAYS : forall f P,
 tsat (ALWAYS f) P -> tsat (ALWAYS (ALWAYS f)) P.
intros.
unfold ALWAYS in |- *.
apply NEGT_sat.
intro.
generalize (MAYEV_sat_inv H0); intro.
inversion_clear H1.
inversion_clear H2.
assert (tsat (MAYEV (NEGT f)) x).
apply NEGT_NEGT.
auto.
generalize (MAYEV_sat_inv H2); intro.
inversion_clear H4.
inversion_clear H5.
unfold ALWAYS in H.
generalize (NEGT_sat_inv H); intros.
apply H5.
apply MAYEV_sat.
exists x0.
split.
apply reds_trans with x.
auto.
auto.
auto.
Qed.

Lemma now_is_FMUSTEV : forall f P, tsat f P -> tsat (FMUSTEV f) P.
intros.
apply FMUSTEV_sat.
intros.
exists P.
exists 0.
split.
auto.
auto.
Qed.

Lemma idempotence_FMUSTEV :
 forall f P,
 tsat (FMUSTEV (FMUSTEV f)) P -> tsat (FMUSTEV f) P.
intros.
generalize (FMUSTEV_sat_inv H); intro.
apply FMUSTEV_sat; intros.
generalize (H0 _ H1 H2 H3); intros.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
generalize (FMUSTEV_sat_inv H6); intro.
generalize (H4 (fun x : nat => PS (x0 + x))); intros.
assert (x0 + 0 = x0).
auto.
rewrite H8 in H7; clear H8.
generalize (H7 H5); clear H5; intros.
assert (isMaxRedSeq (fun x : nat => PS (x0 + x))).
apply MaxRedSeq_is_postfix_closed.
auto.
assert (isFairRedSeq (fun x : nat => PS (x0 + x))).
apply FairRedSeq_is_postfix_closed.
auto.
generalize (H5 H8 H9); intro.
inversion_clear H10.
inversion_clear H11.
exists x1.
exists (x0 + x2).
auto.
Qed.

Lemma FMUSTEV_ALWAYS_FMUSTEV : forall f P,
 tsat (FMUSTEV (ALWAYS f)) P -> tsat (FMUSTEV f) P.
intros.
generalize (FMUSTEV_sat_inv H); intros.
apply FMUSTEV_sat.
intros.
generalize (H0 PS H1 H2 H3); intros.
inversion_clear H4.
inversion_clear H5.
inversion_clear H4.
exists x.
exists x0.
split; auto.
unfold ALWAYS in H6.
generalize (NEGT_sat_inv H6); intro.
apply NNPP.
intro.
apply H4.
apply MAYEV_sat.
exists x.
split.
apply reds_b.
apply NEGT_sat.
auto.
Qed.

(** properties of spatial predicates *)

(*Lemma sat_ZEROS_cong_zeroP : (P:proc)(L:ChanList)
 (sat ZEROS L#P) -> (Cong zeroP P).
Intros.
Unfold ZEROS in H.
Generalize (CONSISTS_sat_inv H); Intro.
Inversion_clear H0.
Inversion_clear H1.
Decompose [and] H0;Clear H0.
Generalize (ISZERO_sat_inv H3); Intro.
Simpl in H0.
Generalize (ISZERO_sat_inv H4); Intro.
Simpl in H2.
Apply cong_tr with (parP x x0).
Rewrite H0; Rewrite H2; ProcCong.
Apply cong_sym; Auto.
Qed.

Lemma sat_ZEROS_parP : (P,Q:proc)(L:ChanList)
 (sat ZEROS L#P)/\(sat ZEROS L#Q) -> (sat ZEROS L#(parP P Q)).
Intros.
Inversion_clear H.
Unfold ZEROS.
Apply CONSISTS_sat.
Exists zeroP.
Exists zeroP.
Split.
Generalize (sat_ZEROS_cong_zeroP ? ? H0); Intro.
Generalize (sat_ZEROS_cong_zeroP ? ? H1); Intro.
Apply cong_par.
Apply cong_sym; Auto.
Apply cong_sym; Auto.
Split.
Apply ISZERO_sat.
Auto.
Apply ISZERO_sat.
Auto.
Qed.*)

Lemma outputs_parP_R :
 forall A b (a : chan A b) v P L,
 sat (OUTPUTS a v ISANY) (L # P) ->
 forall Q, sat (OUTPUTS a v ISANY) (L # parP P Q).
intros.
apply OUTPUTS_sat.
generalize (OUTPUTS_sat_inv H); intros.
inversion_clear H0.
inversion_clear H1.
decompose [and] H0; clear H0.
exists (parP x Q).
exists x0.
split; auto.
apply cong_tr with (parP (parP (a << v >> x0) x) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
Qed.

Lemma outputs_parP_L : forall A b (a : chan A b) v P L,
 sat (OUTPUTS a v ISANY) (L # P) ->
 forall Q, sat (OUTPUTS a v ISANY) (L # parP Q P).
intros.
apply OUTPUTS_sat.
generalize (OUTPUTS_sat_inv H); intros.
inversion_clear H0.
inversion_clear H1.
decompose [and] H0; clear H0.
exists (parP Q x).
exists x0.
split; auto.
apply cong_tr with (parP Q (parP (a << v >> x0) x)).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
Qed.

(** spatial predicates / structural congruence *)

Lemma Cong_parP_parP_outP : forall (P Q R : state) A b (c : chan A b) v C,
 Cong (parP (sndT P) (sndT Q)) (parP (c << v >> C) (sndT R)) ->
 sat (OUTPUTS c v ISANY) P \/ sat (OUTPUTS c v ISANY) Q.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (OutL c v) (parP C (sndT R))).
intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
left.
generalize (inv_trans_OutL H2); intros.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
induction P.
apply OUTPUTS_sat.
exists x1.
exists x0.
split; auto.
simpl in H5.
apply cong_tr with (parP x1 (c << v >> x0)).
auto.
ProcCong.
generalize (inv_trans_OutL H2); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H5.
right.
induction Q.
apply OUTPUTS_sat.
exists x1.
exists x0.
split; auto.
apply cong_tr with (parP x1 (c << v >> x0)).
auto.
ProcCong.
apply tr_parL.
apply tr_out.
Qed.

Lemma Cong_parP_parP_inP : forall (P Q R : state) A b (c : chan A b) (v:A) (*A is not empty*) C,
 Cong (parP (sndT P) (sndT Q)) (parP (c ?? C) (sndT R)) ->
 sat (INPUTS c ISANY) P \/ sat (INPUTS c ISANY) Q.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL c v) (parP (C v) (sndT R))).
intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
left.
generalize (inv_trans_InL H2); intros.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
induction P.
apply INPUTS_sat.
exists x1.
exists x0.
split.
apply cong_tr with (parP x1 (c ?? x0)).
auto.
ProcCong.
intro; auto.
right.
induction Q.
apply INPUTS_sat.
generalize (inv_trans_InL H2); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H5.
exists x1.
exists x0.
split.
apply cong_tr with (parP x1 (c ?? x0)).
auto.
ProcCong.
intro; auto.
apply tr_parL.
apply tr_in.
Qed.

Lemma Cong_parP_parP_rinP : forall (P Q R : state) A b (c : chan A b) (v : A) (*A is not empty*) C,
  Cong (parP (sndT P) (sndT Q)) (parP (c ??* C) (sndT R)) ->
  sat (INPUTS c ISANY) P \/ sat (INPUTS c ISANY) Q.
intros.
generalize (cong_respects_trans_k H); intro X; inversion_clear X.
lapply (H1 (InL c v) (parP (parP (c ??* C) (C v)) (sndT R))).
intro X; inversion_clear X.
inversion_clear H2.
inversion_clear H3.
left.
generalize (inv_trans_InL H2); intros.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
induction P.
apply INPUTS_sat.
exists x1.
exists x0.
split; auto.
apply cong_tr with (parP x1 (c ?? x0)).
auto.
ProcCong.
right.
induction Q.
apply INPUTS_sat.
generalize (inv_trans_InL H2); intro X; inversion_clear X.
inversion_clear H3.
inversion_clear H5.
exists x1.
exists x0.
split.
apply cong_tr with (parP x1 (c ?? x0)).
auto.
ProcCong.
intro; auto.
apply tr_parL.
apply tr_rin.
Qed.

Lemma sat_OUTPUTS_parP_OR : forall A b (c : chan A b) v L P Q,
 sat (OUTPUTS c v ISANY) (L # parP P Q) ->
 sat (OUTPUTS c v ISANY) (L # P) \/ sat (OUTPUTS c v ISANY) (L # Q).
intros.
generalize (OUTPUTS_sat_inv H); clear H; intro.
inversion_clear H.
inversion_clear H0.
decompose [and] H; clear H.
clear H1.
assert (Trans (parP (c << v >> x0) x) (OutL c v) (parP x0 x)).
apply tr_parL.
apply tr_out.
generalize (cong_respects_trans H (cong_sym H0)); intro.
inversion_clear H1.
inversion_clear H2.
inversion H1.
clear H2 P0 H5 Q0 H4 L0.
generalize (inv_trans_OutL H7); intro.
inversion_clear H2.
inversion_clear H4.
inversion_clear H2.
left.
apply OUTPUTS_sat.
exists x3.
exists x2.
split; auto.
apply cong_tr with (parP x3 (c << v >> x2)).
auto.
ProcCong.
clear H2 Q0 H5 P0 H4 L0.
generalize (inv_trans_OutL H7); intro.
inversion_clear H2.
inversion_clear H4.
inversion_clear H2.
right.
apply OUTPUTS_sat.
exists x3.
exists x2.
split; auto.
apply cong_tr with (parP x3 (c << v >> x2)).
auto.
ProcCong.
Qed.

Lemma not_outputs_parP : forall A b (a : chan A b) P Q L,
 ~ (exists v, sat (OUTPUTS a v ISANY) (L # P)) /\
 ~ (exists v, sat (OUTPUTS a v ISANY) (L # Q)) ->
 ~ (exists v, sat (OUTPUTS a v ISANY) (L # parP P Q)).
intros.
inversion_clear H.
intro.
inversion_clear H.
generalize (OUTPUTS_sat_inv H2); intro.
inversion_clear H.
inversion_clear H3.
decompose [and] H; clear H.
clear H4.
generalize (Cong_parP_parP_outP (L # P) (L # Q) (L # x0) H3); intro.
elim H.
intro.
assert (exists v, sat (OUTPUTS a v ISANY) (L # P)).
exists x; auto.
auto.
intro.
assert (exists v, sat (OUTPUTS a v ISANY) (L # Q)).
exists x; auto.
auto.
Qed.

Lemma not_inputs_parP :
 forall A b (a : chan A b) (v : A) (*A not empty*) P Q L,
 ~ sat (INPUTS a ISANY) (L # P) /\ ~ sat (INPUTS a ISANY) (L # Q) ->
 ~ sat (INPUTS a ISANY) (L # parP P Q).
intros.
inversion_clear H.
intro.
generalize (INPUTS_sat_inv H); intro.
inversion_clear H2.
inversion_clear H3.
decompose [and] H2; clear H2.
generalize (Cong_parP_parP_inP (L # P) (L # Q) (L # x) v H3); intro.
elim H2.
intro.
auto.
intro.
auto.
Qed.

(** unsatisfaction of some spatial predicates can be reduced to occurence checks *)

Lemma dont_belong_not_cong : forall A b (c : chan A b) P,
 notinp c (sndT P) ->
 ~ (exists v, sat (OUTPUTS c v ISANY) P) /\ ~ sat (INPUTS c ISANY) P.
intros.
split.
intro.
inversion_clear H0.
induction P.
generalize (OUTPUTS_sat_inv H1); intros.
inversion_clear H0.
inversion_clear H2.
decompose [and] H0; clear H0.
clear H3.
assert (notinp c (parP (c << x >> x1) x0)).
apply cong_respects_notinp with b0.
auto.
auto.
inversion_clear H0.
generalize (inv_out_notinp H3); intro.
decompose [and] H0; clear H0.
auto.
intro.
induction P.
generalize (INPUTS_sat_inv H0); intro.
inversion_clear H1.
inversion_clear H2.
decompose [and] H1; clear H1.
assert (notinp c (parP (c ?? x0) x)).
apply cong_respects_notinp with b0.
auto.
auto.
inversion_clear H1.
generalize (inv_in_notinp H4); intro.
decompose [and] H1; clear H1.
auto.
Qed.

Lemma dont_belong_never_cong : forall R A b (c : chan A b),
 notinp c (sndT R) /\ in_ChanList c (fstT R) ->
 forall R',
 Reds R R' ->
 ~ (exists v, sat (OUTPUTS c v ISANY) R') /\ ~ sat (INPUTS c ISANY) R'.
intros.
generalize (notinp_reds H0 H); intro.
generalize (dont_belong_not_cong R' H1); intros.
auto.
Qed.

Unset Implicit Arguments.
