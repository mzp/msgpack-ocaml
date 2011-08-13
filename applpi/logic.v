Require Import JMeq.
Require Import Classical.
Require Import util.
Require Import chan.
Require Import chanlist.
Require Import set.
Require Import applpi.
Require Import redseq.
Require Import cong.

 (* What we need is a function to check whether or not a channel appears in a formula, we therefore need a type to isolate formulas from other predicates, this implies to write the satisfiability relation explicitly.*)

(** basic formulas *)

Set Implicit Arguments.

Inductive form : Type :=
  | ISANY : form
  | NEG : form -> form
  | OR : form -> form -> form
(*| ISZERO : form*)
  | INPUTS : forall A b, chan A b -> form -> form
(*| ISRINPUT : (A:Set)(b:bool)(chan A b) -> form -> form*)
  | OUTPUTS : forall A b, chan A b -> A -> form -> form
  | CONSISTS : form -> form -> form
(*| FORALL : (A:Set)(b:bool)((chan A b) -> form) -> form*)
.

(*Goal (f:form)(P,P':state)(A:Set;b:bool)(c:(chan A b))
	(Redwith P (epsilon c) P') -> ((sat f P)<->(sat f P')).
Intro.
NewInduction f.*)


(* We cannot write the satisfiablity function if form lies in Prop, if form lies in Set this is not possible either (impredicative type), if form lies in Type we have problems of well-formedness.

If form lies in Prop, we can write in an indirect way the satisfiability predicate,
however since we do not need induction on formulas, we axiomatize the satisfiability
relation.*)

(** satisfaction relation *)

Axiom sat : form -> state -> Prop.

Notation "P |= f" := (sat f P) (at level 50).

Axiom ISANY_satisfaction : forall P, sat ISANY P.

Axiom NEG_satisfaction :
    forall G P, ~ sat G P <-> sat (NEG G) P.

Axiom OR_satisfaction :
    forall F G P, sat F P \/ sat G P <-> sat (OR F G) P.

Axiom INPUTS_satisfaction :
    forall L P F A b (c : chan A b),
    (exists R,
       (exists Q,
          Cong P (parP (c ?? Q) R) /\ (forall v, sat F (L # Q v)))) <->
    sat (INPUTS c F) (L # P).

Axiom OUTPUTS_satisfaction :
  forall L P F A b (c : chan A b) v,
    (exists R,
      (exists Q, Cong P (parP (c << v >> Q) R) /\ sat F (L # Q))) <->
    sat (OUTPUTS c v F) (L # P).

Axiom CONSISTS_satisfaction :
  forall L R F G,
    (exists P,
      (exists Q, Cong R (parP P Q) /\ sat F (L # P) /\ sat G (L # Q))) <->
    sat (CONSISTS F G) (L # R).

(*Inductive sat : form -> state -> Prop :=
  ISANY_sat : (P:state)(sat ISANY P)
| NEG_sat : (G:form)(P:state)(unsat G P) -> (sat (NEG G) P)
| OR_sat : (F,G:form)(P:state)(sat F P)/\(sat G P) -> (sat (OR F G) P)
| ISINPUT_sat : (L:ChanList)(P:proc)(F:form)(A:Set)(b:bool)(c:(chan A b))
 (EXT R:proc | (EXT Q:A->proc |
  (Cong P (parP (inP c Q) R))/\((v:A)(sat F L#(Q v))))) -> (sat (ISINPUT c F) L#P)
| ISOUTPUT_sat : (L:ChanList)(P:proc)(F:form)(A:Set)(b:bool)(c:(chan A b))(v:A)
 (EXT R:proc | (EXT Q:proc |
  (Cong P (parP (outP c v Q) R))/\(sat F L#Q))) -> (sat (ISOUTPUT c v F) L#P)
| CONSISTS_sat : (L:ChanList)(R:proc)(F,G:form)
 (EXT P:proc | (EXT Q:proc | (Cong R (parP P Q))/\(sat F L#P)/\(sat G L#Q))) ->
	(sat (CONSISTS F G) L#R)
with unsat : form -> state -> Prop :=
  NEG_unsat : (G:form)(P:state)(sat G P) -> (unsat (NEG G) P)
| OR_unsat : (F,G:form)(P:state)(unsat F P)/\(unsat G P) -> (unsat (OR F G) P)
| ISINPUT_unsat : (L:ChanList)(P:proc)(F:form)(A:Set)(b:bool)(c:(chan A b))
 (R:proc)(Q:A->proc)~(Cong P (parP (inP c Q) R))\/
 (EXT R:proc | (EXT Q:A->proc |
  (Cong P (parP (inP c Q) R))/\(EX v:A | (unsat F L#(Q v))))) -> (unsat (ISINPUT c F) L#P)
| ISOUTPUT_unsat : (L:ChanList)(P:proc)(F:form)(A:Set)(b:bool)(c:(chan A b))(v:A)
 (R,Q:proc)~(Cong P (outP c v Q))\/
 (EXT R:proc | (EXT Q:proc |
  (Cong P (parP (outP c v Q) R))/\(unsat F L#Q))) -> (unsat (ISOUTPUT c v F) L#P)
| CONSISTS_unsat : (L:ChanList)(R:proc)(F,G:form)
 (((P:proc)(Q:proc)(Cong R (parP P Q)) -> (unsat F L#P)\/(unsat G L#Q))) ->
	(unsat (CONSISTS F G) L#R).*)

(*Axiom FORALL_satisfaction : (A:Set)(b:bool)(F:(chan A b) -> form)(P:state)
 ((c:(chan A b))(sat (F c) P)) <-> (sat (FORALL F) P).*)

Inductive tform : Type :=
  | STAT : form -> tform
  | NEGT : tform -> tform
  | ORT : tform -> tform -> tform
  | MAYEV : tform -> tform
  | MUSTEV : tform -> tform
  | FMUSTEV : tform -> tform.

Axiom tsat : tform -> state -> Prop.

Notation "P |=t f" := (tsat f P) (at level 50).

Axiom STAT_satisfaction :
  forall P F, sat F P <-> tsat (STAT F) P.

Axiom NEGT_satisfaction :
  forall P F, ~ tsat F P <-> tsat (NEGT F) P.

Axiom ORT_satisfaction :
  forall P F G,
    tsat F P \/ tsat G P <-> tsat (ORT F G) P.

Axiom MAYEV_satisfaction :
  forall P F,
    (exists Q, Reds P Q /\ tsat F Q) <-> tsat (MAYEV F) P.

Axiom MUSTEV_satisfaction :
  forall P F,
    (forall PS,
      PS 0 = SomeT _ P ->
      isMaxRedSeq PS ->
      exists Q,
	(exists n, PS n = SomeT _ Q /\ tsat F Q)) <-> tsat (MUSTEV F) P.

Axiom FMUSTEV_satisfaction :
  forall P F,
    (forall PS,
      PS 0 = SomeT _ P ->
      isMaxRedSeq PS ->
      isFairRedSeq PS ->
      exists Q,
	(exists n, PS n = SomeT _ Q /\ tsat F Q)) <-> tsat (FMUSTEV F) P.

Lemma ISANY_sat : forall P, sat ISANY P.
intro.
apply (ISANY_satisfaction P).
Qed.

Hint Immediate ISANY_sat: core.

Lemma NEG_sat : forall G P, ~ sat G P -> sat (NEG G) P.
generalize NEG_satisfaction; intros.
generalize (H G P); tauto.
Qed.

Lemma NEG_sat_inv : forall G P, sat (NEG G) P -> ~ sat G P.
intros G P H.
generalize NEG_satisfaction; intros.
generalize (H0 G P); tauto.
Qed.

Lemma OR_sat :
  forall F G P, sat F P \/ sat G P -> sat (OR F G) P.
intros.
generalize (OR_satisfaction F G P); tauto.
Qed.

Lemma OR_sat_inv :
  forall F G P, sat (OR F G) P -> sat F P \/ sat G P.
intros.
generalize (OR_satisfaction F G P); tauto.
Qed.

(*Lemma ISZERO_sat : (P:state)
 (sndT P)==zeroP -> (sat ISZERO P).
Intros.
Generalize (ISZERO_satisfaction P); Tauto.
Qed.

Lemma ISZERO_sat_inv : (P:state)
 (sat ISZERO P) -> (sndT P)==zeroP.
Intros.
Generalize (ISZERO_satisfaction P); Tauto.
Qed.*)

Lemma INPUTS_sat :
  forall L P F A b (c : chan A b),
    (exists R,
      (exists Q,
	Cong P (parP (c ?? Q) R) /\ (forall v, sat F (L # Q v)))) ->
    sat (INPUTS c F) (L # P).
intros.
generalize (INPUTS_satisfaction L P F c); intro.
inversion_clear H0.
auto.
Qed.

Lemma INPUTS_sat_inv :
  forall L P F A b (c : chan A b),
    sat (INPUTS c F) (L # P) ->
    exists R,
      (exists Q,
	Cong P (parP (c ?? Q) R) /\ (forall v, sat F (L # Q v))).
intros.
generalize (INPUTS_satisfaction L P F c); intro.
inversion_clear H0.
auto.
Qed.

(*Lemma ISRINPUT_sat : (L:ChanList)(P:proc)(F:form)(A:Set)(b:bool)(c:(chan A b))
 (EXT Q:A->proc | P==(rinP c Q)/\((v:A)(sat F L#(Q v)))) -> (sat (ISRINPUT c F) L#P).
Intros.
Generalize (ISRINPUT_satisfaction L P F c); Intro.
Inversion_clear H0.
Auto.
Qed.

Lemma ISRINPUT_sat_inv : (L:ChanList)(P:proc)(F:form)(A:Set)(b:bool)(c:(chan A b))
 (sat (ISRINPUT c F) L#P) -> (EXT Q:A->proc | P==(rinP c Q)/\((v:A)(sat F L#(Q v)))).
Intros.
Generalize (ISRINPUT_satisfaction L P F c); Intro.
Inversion_clear H0.
Auto.
Qed.*)

Lemma OUTPUTS_sat :
  forall L P F A b (c : chan A b) v,
    (exists R,
      (exists Q, Cong P (parP (c << v >> Q) R) /\ sat F (L # Q))) ->
    sat (OUTPUTS c v F) (L # P).
intros.
generalize (OUTPUTS_satisfaction L P F c v); intro.
inversion_clear H0.
auto.
Qed.

Lemma OUTPUTS_sat_inv :
 forall L P F A b (c : chan A b) v,
 sat (OUTPUTS c v F) (L # P) ->
 exists R,
   (exists Q, Cong P (parP (c << v >> Q) R) /\ sat F (L # Q)).
intros.
generalize (OUTPUTS_satisfaction L P F c v); intro.
inversion_clear H0.
auto.
Qed.

Lemma CONSISTS_sat :
  forall L R F G,
    (exists P,
      (exists Q, Cong R (parP P Q) /\ sat F (L # P) /\ sat G (L # Q))) ->
 sat (CONSISTS F G) (L # R).
intros.
generalize (CONSISTS_satisfaction L R F G); intro.
inversion_clear H0; auto.
Qed.

Lemma CONSISTS_sat_inv :
  forall L R F G,
    sat (CONSISTS F G) (L # R) ->
    exists P,
      (exists Q, Cong R (parP P Q) /\ sat F (L # P) /\ sat G (L # Q)).
intros.
generalize (CONSISTS_satisfaction L R F G); intro.
inversion_clear H0; auto.
Qed.

(*Lemma FORALL_sat : (A:Set)(b:bool)(F:(chan A b) -> form)(P:state)
 ((c:(chan A b))(sat (F c) P)) -> (sat (FORALL F) P).
Intros.
Generalize (FORALL_satisfaction F P); Intro.
Inversion_clear H0.
Tauto.
Qed.

Lemma FORALL_sat_inv :  (A:Set)(b:bool)(F:(chan A b) -> form)(P:state)
 (sat (FORALL F) P) -> ((c:(chan A b))(sat (F c) P)).
Intros.
Generalize (FORALL_satisfaction F P); Intro.
Inversion_clear H0.
Apply H2; Auto.
Qed.*)

(*Lemma UNTIL_sat : (f,g:form)(P:state)
 ((PS:procSeq)(PS O)==(SomeT ? P) ->
   (isMaxRedSeq PS) ->
   (EXT Q:state | (EX n:nat | (PS n)==(SomeT ? Q) /\ (sat g Q) /\
       ((i:nat)(lt i n) -> (Pi:state)(PS i)==(SomeT ? Pi) -> (sat f Pi))))) ->
 (sat (UNTIL f g) P).
Intros.
Generalize (UNTIL_satisfaction f g P); Intro.
Tauto.
Qed.

Lemma UNTIL_sat_inv : (f,g:form)(P:state)
 (sat (UNTIL f g) P) ->
 ((PS:procSeq)(PS O)==(SomeT ? P) ->
   (isMaxRedSeq PS) ->
   (EXT Q:state | (EX n:nat | (PS n)==(SomeT ? Q) /\ (sat g Q) /\
       ((i:nat)(lt i n) -> (Pi:state)(PS i)==(SomeT ? Pi) -> (sat f Pi))))).
Intros.
Generalize (UNTIL_satisfaction f g P); Intro.
Inversion_clear H2; Auto.
Qed.*)

Lemma STAT_sat : forall P F, sat F P -> tsat (STAT F) P.
intros.
generalize (STAT_satisfaction P F).
tauto.
Qed.

Lemma STAT_sat_inv : forall P F, tsat (STAT F) P -> sat F P.
intros.
generalize (STAT_satisfaction P F).
tauto.
Qed.

Lemma NEGT_sat : forall P G, ~ tsat G P -> tsat (NEGT G) P.
intros.
generalize (NEGT_satisfaction P G).
tauto.
Qed.

Lemma NEGT_sat_inv : forall P G, tsat (NEGT G) P -> ~ tsat G P.
intros P G H.
generalize (NEGT_satisfaction P G); intros.
tauto.
Qed.

Lemma ORT_sat : forall P F G, tsat F P \/ tsat G P -> tsat (ORT F G) P.
intros.
generalize (ORT_satisfaction P F G); tauto.
Qed.

Lemma ORT_sat_inv : forall P F G, tsat (ORT F G) P -> tsat F P \/ tsat G P.
intros.
generalize (ORT_satisfaction P F G); tauto.
Qed.

Lemma MAYEV_sat : forall P F,
  (exists Q, Reds P Q /\ tsat F Q) -> tsat (MAYEV F) P.
intros.
generalize (MAYEV_satisfaction P F); intro.
inversion_clear H0.
auto.
Qed.

Lemma MAYEV_sat_inv :
 forall P F,
 tsat (MAYEV F) P -> exists Q, Reds P Q /\ tsat F Q.
intros.
generalize (MAYEV_satisfaction P F); intro.
inversion_clear H0.
auto.
Qed.

Lemma MUSTEV_sat :
 forall P F,
   (forall PS,
     PS 0 = SomeT _ P ->
     isMaxRedSeq PS ->
     exists Q,
       (exists n, PS n = SomeT _ Q /\ tsat F Q)) -> tsat (MUSTEV F) P.
intros.
generalize (MUSTEV_satisfaction P F).
intro X; inversion_clear X.
tauto.
Qed.

Lemma MUSTEV_sat_inv :
  forall P F,
    tsat (MUSTEV F) P ->
    forall PS,
      PS 0 = SomeT _ P ->
      isMaxRedSeq PS ->
      exists Q,
	(exists n, PS n = SomeT _ Q /\ tsat F Q).
intros.
generalize (MUSTEV_satisfaction P F).
intro X; inversion_clear X.
apply H3.
auto.
auto.
auto.
Qed.

Lemma FMUSTEV_sat :
  forall P F,
    (forall PS,
      PS 0 = SomeT _ P ->
      isMaxRedSeq PS ->
      isFairRedSeq PS ->
      exists Q,
	(exists n, PS n = SomeT _ Q /\ tsat F Q)) -> tsat (FMUSTEV F) P.
intros.
generalize (FMUSTEV_satisfaction P F).
intro X; inversion_clear X.
apply H0.
auto.
Qed.

Lemma FMUSTEV_sat_inv :
  forall P F,
    tsat (FMUSTEV F) P ->
    forall PS,
      PS 0 = SomeT _ P ->
      isMaxRedSeq PS ->
      isFairRedSeq PS ->
      exists Q,
	(exists n, PS n = SomeT _ Q /\ tsat F Q).
intros.
generalize (FMUSTEV_satisfaction P F).
intro X; inversion_clear X.
auto.
Qed.

(** occurrence of variables in formulas *)

Inductive notin (A : Set) (b : bool) (c : chan A b) : form -> Prop :=
  | ISANY_notin : notin c ISANY
  | NEG_notin : forall G, notin c G -> notin c (NEG G)
  | OR_notin : forall F G, notin c F -> notin c G -> notin c (OR F G)
      (* | ISZERO_notin : (notin c ISZERO)*)
  | INPUTS_notin : forall B b' (d : chan B b') G,
      ~ d &&& c -> notin c G -> notin c (INPUTS d G)
  | OUTPUTS_notin : forall B b' (d : chan B b') v G,
      ~ d &&& c -> ~ (v %% c) -> notin c G -> notin c (OUTPUTS d v G)
  | CONSISTS_notin : forall G H, notin c G -> notin c H -> notin c (CONSISTS G H).
(* | FORALL_notin : (B:Set)(b':bool)(F:(chan B b')->form)
 ((d:(chan B b')) ~(c &&& d) -> (notin c (F d))) -> (notin c (FORALL F))*)
(* | UNTIL_notin : (G,H:form)(notin c G) -> (notin c H) -> (notin c (UNTIL G H))
 | MAYEV_notin : (G:form)(notin c G) -> (notin c (MAYEV G))*)

Inductive tnotin (A : Set) (b : bool) (c : chan A b) : tform -> Prop :=
  | STAT_notin : forall f, notin c f -> tnotin c (STAT f)
  | NEGT_notin : forall G, tnotin c G -> tnotin c (NEGT G)
  | ORT_notin : forall F G, tnotin c G -> tnotin c F -> tnotin c (ORT F G)
  | MAYEV_notin : forall G, tnotin c G -> tnotin c (MAYEV G)
  | MUSTEV_notin : forall G, tnotin c G -> tnotin c (MUSTEV G)
  | FMUSTEV_notin : forall G, tnotin c G -> tnotin c (FMUSTEV G).

Definition isin A b (c : chan A b) f := ~ notin c f.

Definition tisin A b (c : chan A b) f := ~ tnotin c f.

Lemma OUTPUTS_inj1 : forall A B b b' (c : chan A b) (d : chan B b') v w F G,
    OUTPUTS c v F = OUTPUTS d w G -> A = B /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma OUTPUTS_inj0 : forall A B b b' (c : chan A b) (d : chan B b') v w F G,
 OUTPUTS c v F = OUTPUTS d w G -> (c %% d) /\ (v %% w) /\ F = G.
intros.
split.
change
  match OUTPUTS d w G with
  | OUTPUTS AA bb cc vv FF => c %% cc
  | _ => c %% d
  end in |- *.
rewrite <- H.
auto.
split.
change
  match OUTPUTS d w G with
  | OUTPUTS AA bb cc vv FF => v %% vv
  | _ => v %% w
  end in |- *.
rewrite <- H.
auto.
change
  match OUTPUTS d w G with
  | OUTPUTS AA bb cc vv FF => F = FF
  | _ => F = G
  end in |- *.
rewrite <- H.
auto.
Qed.

Lemma OUTPUTS_inj : forall A b (c d : chan A b) v w F G,
 OUTPUTS c v F = OUTPUTS d w G -> c = d /\ v = w /\ F = G.
intros.
generalize (OUTPUTS_inj0 H); intro.
decompose [and] H0; clear H0.
split.
apply JMeq_eq.
auto.
split.
apply JMeq_eq.
auto.
auto.
Qed.

Lemma inv_OUTPUTS_notin' : forall A b (c : chan A b) F,
  notin c F ->
  forall B b' (d : chan B b') v G,
    F = OUTPUTS d v G -> ~ d &&& c /\ ~ (v %% c) /\ notin c G.
do 5 intro.
induction H
 as
  [|
   G H IHnotin|
   F G H IHnotin1 H1 IHnotin2|
   B b' d G H H0 IHnotin|
   B b' d v G H H0 H1 IHnotin|
   G H H1 IHnotin1 H2 IHnotin2].
intros.
discriminate H.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
discriminate H1.
intros.
generalize (OUTPUTS_inj1 H2); intro.
inversion_clear H3.
generalize d0 v0 H2; clear d0 v0 H2; rewrite <- H4; rewrite <- H5; auto.
clear H4 H5 B0 b'0.
intros.
generalize (OUTPUTS_inj H2); intro.
decompose [and] H3; clear H3.
rewrite <- H4.
rewrite <- H6.
rewrite <- H7.
auto.
intros.
discriminate H0.
Qed.

Lemma inv_OUTPUTS_notin : forall A b (c : chan A b) B b' (d : chan B b') v G,
 notin c (OUTPUTS d v G) -> ~ d &&& c /\ ~ (v %% c) /\ notin c G.
intros.
eapply inv_OUTPUTS_notin'.
apply H.
auto.
Qed.

Definition free_vars L f := forall B b' (d : chan B b'), isin d f <-> in_ChanList d L.

Definition tfree_vars L f := forall B b' (d : chan B b'), tisin d f <-> in_ChanList d L.

Lemma tisin_isin : forall A b (d : chan A b) f,
 tisin d (STAT f) <-> isin d f.
intros.
split.
intro.
red in H.
red in |- *.
intro.
apply H.
apply STAT_notin.
auto.
intro.
red in H.
red in |- *.
intro.
apply H.
inversion_clear H0.
auto.
Qed.

Lemma free_vars_tfree_vars : forall L f,
  free_vars L f -> tfree_vars L (STAT f).
intros.
red in |- *.
intros.
red in H.
generalize (H B b' d); intro.
inversion_clear H0.
split.
intro.
apply H1.
generalize (tisin_isin d f); tauto.
intro.
generalize (tisin_isin d f); intro X; inversion_clear X.
auto.
Qed.

Lemma free_vars_incC_notin :
  forall L f,
    free_vars L f ->
    forall K A b (c : chan A b),
      ChanList_is_set (c & K) -> incC L K -> notin c f.
intros.
apply NNPP.
intro.
fold (isin c f) in H1.
red in H.
red in H1.
assert
 (forall B b' (d : chan B b'), isin d f -> in_ChanList d K).
intros.
generalize (H _ _ d); intro.
inversion_clear H4.
auto.
generalize (H3 _ _ _ H2); intros.
simpl in H0.
inversion_clear H0.
generalize (fresh_func2pred _ _ _ _ H5); intro.
red in H0.
generalize (H0 _ _ _ H4); intros.
auto.
Qed.

Lemma free_vars_incC_tnotin :
  forall L f,
    tfree_vars L f ->
    forall K A b (c : chan A b),
      ChanList_is_set (c & K) -> incC L K -> tnotin c f.
intros.
apply NNPP.
intro.
red in H.
red in H1.
assert
 (forall B b' (d : chan B b'), tisin d f -> in_ChanList d K).
intros.
generalize (H _ _ d); intro.
inversion_clear H4.
auto.
generalize (H3 _ _ _ H2); intros.
simpl in H0.
inversion_clear H0.
generalize (fresh_func2pred _ _ _ _ H5); intro.
red in H0.
generalize (H0 _ _ _ H4); intros.
auto.
Qed.

(** derived formulas *)

Definition FALSE := NEG ISANY.

Definition AND F G := NEG (OR (NEG F) (NEG G)).

Definition IMP f g := OR (NEG f) g.

(*Definition OUTPUTS [A:Set;b:bool;c:(chan A b);v:A;F:form] :=
  (CONSISTS (ISOUTPUT c v F) ISANY).

Definition INPUTS [A:Set;b:bool;c:(chan A b);F:form] :=
  (CONSISTS (OR (ISINPUT c F) (ISRINPUT c F)) ISANY).*)

Definition ANDT F G := NEGT (ORT (NEGT F) (NEGT G)).

Definition ALWAYS F := NEGT (MAYEV (NEGT F)).

(*Definition EXISTS [A:Set;b:bool] := [F:(chan A b)->form]
	(NEG (FORALL [c:(chan A b)](NEG (F c)))).*)

(*Definition ZEROS := (CONSISTS ISZERO ISZERO).

Definition MUSTEV [f:form] : form := (UNTIL ISANY f).*)

Lemma AND_sat : forall F G P,
  sat F P /\ sat G P -> sat (AND F G) P.
intros.
unfold AND in |- *.
apply NEG_sat.
intro.
generalize (OR_sat_inv H0); intro.
inversion_clear H1.
generalize (NEG_sat_inv H2); intro.
apply H1.
intuition.
generalize (NEG_sat_inv H2); intro.
apply H1.
intuition.
Qed.

Lemma AND_sat_inv : forall F G P,
  sat (AND F G) P -> sat F P /\ sat G P.
intros.
unfold AND in H.
generalize (NEG_sat_inv H); intro.
apply NNPP.
intro.
apply H0.
generalize (not_and_or _ _ H1); intro.
apply OR_sat.
inversion_clear H2.
left.
apply NEG_sat.
auto.
right.
apply NEG_sat.
auto.
Qed.

Lemma ANDT_sat : forall F G P,
  tsat F P /\ tsat G P -> tsat (ANDT F G) P.
intros.
unfold ANDT in |- *.
apply NEGT_sat.
intro.
generalize (ORT_sat_inv H0); intro.
inversion_clear H1.
generalize (NEGT_sat_inv H2); intro.
apply H1.
intuition.
generalize (NEGT_sat_inv H2); intro.
apply H1.
intuition.
Qed.

Lemma ANDT_sat_inv : forall F G P,
  tsat (ANDT F G) P -> tsat F P /\ tsat G P.
intros.
unfold ANDT in H.
generalize (NEGT_sat_inv H); intro.
apply NNPP.
intro.
apply H0.
generalize (not_and_or _ _ H1); intro.
apply ORT_sat.
inversion_clear H2.
left.
apply NEGT_sat.
auto.
right.
apply NEGT_sat.
auto.
Qed.

(*Lemma ISINPUT_sat_inv : (A:Set;b:bool;c:(chan A b))(L:ChanList)(P:proc)(f:form)
 (sat (ISINPUT c f) L#P) ->
 (EXT C:A->proc | (EXT Q:proc |
     (Cong P (parP (inP c C) Q)) \/ (Cong P (parP (rinP c C) Q)))).
Intros.
Unfold INPUTS in H.
Generalize (CONSISTS_sat_inv H); Intro.
Inversion_clear H0.
Inversion_clear H1.
Decompose [and] H0;Clear H0.
Generalize (OR_sat_inv H3); Intro.
Inversion_clear H0.
Generalize (ISINPUT_sat_inv H2); Intro.
Inversion_clear H0.
Inversion_clear H5.
Exists x1.
Exists x0.
Left.
Apply cong_tr with (parP x x0).
Auto.
Apply cong_par.
Rewrite H0; Apply cong_refl.
Apply cong_refl.
Generalize (ISRINPUT_sat_inv H2); Intro.
Inversion_clear H0.
Inversion_clear H5.
Exists x1.
Exists x0.
Right.
Apply cong_tr with (parP x x0).
Auto.
Rewrite H0; Apply cong_refl.
Qed.

Lemma OUTPUTS_sat_inv : (A:Set;b:bool;c:(chan A b);v:A)(L:ChanList)(P:proc)(f:form)
 (sat (OUTPUTS c v f) L#P) ->
 (EXT C:proc | (EXT Q:proc |
     (Cong P (parP (outP c v C) Q)))).
Intros.
Unfold OUTPUTS in H.
Generalize (CONSISTS_sat_inv H); Intros.
Inversion_clear H0.
Inversion_clear H1.
Decompose [and] H0;Clear H0.
Generalize (ISOUTPUT_sat_inv H3); Intros.
Inversion_clear H0.
Inversion_clear H2.
Exists x1.
Exists x0.
Apply cong_tr with (parP x x0).
Auto.
Rewrite H0; Apply cong_refl.
Qed.

Lemma MUSTEV_sat : (P:state)(F:form)((PS:stateSeq)(PS O)==(SomeT ? P) ->
 (isMaxRedSeq PS) ->
 (EXT M:ChanList | (EXT Q:proc | (EX n:nat |
       (PS n)==(SomeT ? M#Q) /\ (sat F M#Q))))) -> (sat (MUSTEV F) P).
Intros.
Unfold MUSTEV.
Apply UNTIL_sat.
Intros.
Generalize (H ? H0 H1); Intros.
Inversion_clear H2.
Inversion_clear H3.
Inversion_clear H2.
Inversion_clear H3.
Exists x#x0.
Exists x1.
Split; Auto.
Qed.

Lemma MUSTEV_sat_inv : (P:(state); F:form)
 (sat (MUSTEV F) P) -> ((PS:stateSeq)
   (PS O)==(SomeT state P)
   ->(isMaxRedSeq PS)
   ->(EXT M:ChanList |
          (EXT Q:proc |
               (EX n:nat | (PS n)==(SomeT state M#Q)/\(sat F M#Q))))).
Intros.
Unfold MUSTEV in H.
Generalize (UNTIL_sat_inv H); Intros.
Generalize (H2 ? H0 H1); Intro X; Inversion_clear X.
Inversion_clear H3.
Decompose [and] H4;Clear H4.
Exists (fstT x).
Exists (sndT x).
Exists x0.
NewInduction x.
Auto.
Qed.*)

(*Lemma test_sat : (A:Set)(b:bool)(c:(chan A b))(v:A)
	(sat (OUTPUTS A b c v ISZERO) nilC#(outP c v zeroP)).
Intros.
Unfold OUTPUTS.
Apply CONSISTS_sat.
Exists (parP (outP c v zeroP) zeroP).
Split.
Apply cong_sym; Apply cong_zero.
Apply ISPAR_sat.
Exists (outP c v zeroP).
Exists zeroP.
Split.
Auto.
Split.
Apply ISOUTPUT_sat.
Exists zeroP.
Split; Auto.
Apply ISZERO_sat.
Simpl; Auto.
Apply ISANY_sat.
Qed.*)

(*Lemma test_sat : (A:Set)(b:bool)(e,d:(chan A b))(v,v',w,w':A)~e=d ->
 (sat
   (NEG (EXISTS [c:(chan A b)](CONSISTS (ISOUTPUT c v ISANY) (ISOUTPUT c w ISANY))))
   (e&(d&nilC))#(parP (OutAtom e v') (OutAtom d w'))).
Intros A b e d v v' w w' diff.
Apply NEG_sat.
Unfold EXISTS.
Intro.
Generalize (NEG_sat_inv H); Clear H; Intro.
Apply H.
Apply FORALL_sat.
Intro.
Apply NEG_sat.
Intro.
Generalize (CONSISTS_sat_inv H0); Clear H0; Intro.
Inversion_clear H0.
Decompose [and] H1;Clear H1.
Generalize (ISPAR_sat_inv H2); Clear H2; Intro.
Inversion_clear H1.
Inversion_clear H2.
Decompose [and] H1;Clear H1.
Generalize (ISOUTPUT_sat_inv H4); Intro.
Inversion_clear H1.
Inversion_clear H3.
Generalize (ISOUTPUT_sat_inv H5); Intro.
Inversion_clear H3.
Inversion_clear H7.
Rewrite H1 in H2; Rewrite H3 in H2; Rewrite H2 in H0.
Unfold OutAtom in H0.
Assert ((l:TrLabel;P':proc)(Trans (parP (outP c v x2) (outP c w x3)) l P') -> (EX v:A | l==(OutL c v))).
Intros.
Inversion H7.
Generalize (dis_trans_outP_InL ? ? ? ? ? ? ? ? ? ? H14); Contradiction.
Generalize (dis_trans_outP_InL ? ? ? ? ? ? ? ? ? ? H11); Contradiction.
Clear H10 L H11 Q H9 P.
Generalize (inv_trans_outP_lbl ? ? ? ? ? ? ? H13); Intro. the lemma used here has slightly changed
Exists v.
Auto.
Generalize (inv_trans_outP_lbl ? ? ? ? ? ? ? H13); Intro.
Exists w.
Auto.
Generalize (all_trans_out_cong ? ? H0 ? ? ? H7); Intro.
Assert (Trans (parP (outP e v' zeroP) (outP d w' zeroP)) (OutL e v') (parP zeroP (outP d w' zeroP))).
Apply tr_parL.
Apply tr_out.
Generalize (H9 ? ? H10); Intro.
Inversion_clear H11.
Assert (Trans (parP (outP e v' zeroP) (outP d w' zeroP)) (OutL d w') (parP  (outP e v' zeroP) zeroP)).
Apply tr_parR.
Apply tr_out.
Generalize (H9 ? ? H11); Intro.
Inversion_clear H13.
Generalize (OutL_inj ? ? ? ? ? ? H14); Intro.
Generalize (OutL_inj ? ? ? ? ? ? H12); Intro.
Inversion_clear H13.
Inversion_clear H15.
Apply diff.
Rewrite H16; Rewrite H13; Auto.
Qed.*)

Lemma free_vars_neg : forall L f,
  free_vars L (NEG f) <-> free_vars L f.
intros.
split.
intros.
red in |- *.
split; intros.
red in H.
generalize (H _ _ d); intro X; inversion_clear X.
apply H1.
red in |- *.
intro.
apply H0.
inversion_clear H3.
auto.
red in H.
generalize (H _ _ d); intro X; inversion_clear X.
intro.
generalize (H2 H0); intro.
apply H4.
apply NEG_notin.
auto.
intros.
red in |- *.
intros.
split; intros.
red in H.
generalize (H _ _ d); intros.
inversion_clear H1.
apply H2.
intro; apply H0.
apply NEG_notin.
auto.
generalize (H _ _ d); intros.
inversion_clear H1.
intro.
cut (notin d f).
intro.
apply H3.
auto.
auto.
inversion_clear H1.
auto.
Qed.

Lemma free_vars_always :
 forall (L : ChanList) (f : tform),
 tfree_vars L f <-> tfree_vars L (ALWAYS f).
split.
intros.
red in |- *.
intros.
red in H.
split.
intro.
generalize (H _ _ d); intro.
inversion_clear H1.
apply H2.
red in |- *.
red in H0.
intro; apply H0.
unfold ALWAYS in |- *.
apply NEGT_notin.
apply MAYEV_notin.
apply NEGT_notin.
auto.
intros.
generalize (H _ _ d); intro X; inversion_clear X.
unfold ALWAYS in |- *.
red in |- *; intro.
generalize (H2 H0); intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
auto.
intros.
red in |- *.
red in H.
split.
intros.
cut (tisin d (ALWAYS f)).
intros.
generalize (H _ _ d); tauto.
red in |- *.
intro.
apply H0.
unfold ALWAYS in H1.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
auto.
intros.
intro.
generalize (H _ _ d); intro.
inversion_clear H2.
generalize (H4 H0); intro.
apply H2.
unfold ALWAYS in |- *.
apply NEGT_notin.
apply MAYEV_notin.
apply NEGT_notin.
auto.
Qed.

Inductive ins_c_only (A : Set) (b : bool) (c : chan A b) : proc -> Prop :=
  | ins_c_only_zeroP : forall P, ins_c_only c P -> ins_c_only c (parP P zeroP)
  | ins_c_only_inP : forall C, ins_c_only c (c ?? C)
  | ins_c_only_rinP : forall C, ins_c_only c (c ??* C)
  | ins_c_only_parP : forall P Q,
      ins_c_only c P -> ins_c_only c Q -> ins_c_only c (parP P Q).

Unset Implicit Arguments.




