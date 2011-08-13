Require Import util.
Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import redseq.
Require Import cong.
Require Import cong_tactic.
Require Import cong_resp.
Require Import logic.
Require Import stable.

 (** what it means for a property to be independent of structual congruent rearrangement *)

Set Implicit Arguments.

Lemma cong_resp_satisfaction :
 forall L P Q,
 Cong Q P -> forall f, sat f (L # P) <-> sat f (L # Q).
intros.
induction f.
split; [ auto | auto ].
split; intros.
apply NEG_sat; intro.
generalize (NEG_sat_inv H0); intro.
tauto.
apply NEG_sat; intro.
generalize (NEG_sat_inv H0); intro.
tauto.
split; intros.
apply OR_sat; generalize (OR_sat_inv H0); intro.
tauto.
apply OR_sat; generalize (OR_sat_inv H0); intro.
tauto.
split; intros.
apply INPUTS_sat.
generalize (INPUTS_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists x.
exists x0.
split; auto.
apply cong_tr with P; auto.
apply INPUTS_sat.
generalize (INPUTS_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists x.
exists x0.
split; auto.
apply cong_tr with Q; apply cong_sym; auto.
apply cong_sym; auto.
split; intros.
apply OUTPUTS_sat.
generalize (OUTPUTS_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists x; exists x0; split; auto.
apply cong_tr with P.
auto.
auto.
apply OUTPUTS_sat.
generalize (OUTPUTS_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
exists x; exists x0; split; auto.
apply cong_tr with Q.
apply cong_sym; auto.
auto.
split; intros.
apply CONSISTS_sat.
generalize (CONSISTS_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
exists x; exists x0; split; auto.
apply cong_tr with P; intuition.
intuition.
apply CONSISTS_sat.
generalize (CONSISTS_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
exists x; exists x0; split; auto.
apply cong_tr with Q; apply cong_sym.
auto.
apply cong_sym; intuition.
intuition.
Qed.

Lemma cong_resp_sat :
 forall L P f,
 sat f (L # P) -> forall Q, Cong Q P -> sat f (L # Q).
intros.
generalize (cong_resp_satisfaction L H0 f).
tauto.
Qed.

(*Lemma cong_resp_sat : (p:form)
 (cong_independent p) ->
 (L:ChanList;P,P':proc)
 (Cong P P')->
 (sat p L#P) -> (sat p L#P').
Intros.
Red in H.
Apply H with P.
Auto.
Auto.
Qed.*)

(** tactic to prove that some property is independent of structural congruent rearrangement *)

(*Definition cong_independent [p:form] :=
 (P,Q:proc)(Cong P Q) -> (L:ChanList)(sat p L#P) -> (sat p L#Q).

Lemma cong_ind_OR: (f,g:form)(cong_independent f) -> (cong_independent g) -> 
(cong_independent (OR f g)).
Intros.
Red.
Intros.
Generalize (OR_sat_inv H2); Intros.
Inversion_clear H3.
Apply OR_sat.
Left.
Red in H.
Apply H with P.
Auto.
Auto.
Apply OR_sat.
Right.
Red in H0.
Apply H0 with P.
Auto.
Auto.
Qed.

Lemma cong_ind_OUTPUTS : (f:form)(A:Set)(b:bool)(c:(chan A b))(v:A)
(cong_independent (OUTPUTS c v f)).
Intros.
Red.
Intros.
Apply OUTPUTS_sat.
Generalize (OUTPUTS_sat_inv H0); Intros.
Inversion_clear H1.
Inversion_clear H2.
Decompose [and] H1;Clear H1.
Exists x.
Exists x0.
Split; Auto.
Apply cong_tr with P.
Apply cong_sym; Auto.
Auto.
Qed.

Lemma cong_ind_INPUTS : (f:form)(A:Set)(b:bool)(c:(chan A b))
(cong_independent (INPUTS c f)).
Intros.
Red.
Intros.
Generalize (INPUTS_sat_inv H0); Intros.
Inversion_clear H1.
Inversion_clear H2.
Decompose [and] H1;Clear H1.
Apply INPUTS_sat.
Exists x.
Exists x0.
Split; Auto.
Apply cong_tr with P.
Apply cong_sym; Auto.
Auto.
Qed.*)

(*Lemma cong_ind_ZEROS : (cong_independent ZEROS).
Red.
Intros.
Unfold ZEROS.
Unfold ZEROS in H0.
Generalize (CONSISTS_sat_inv H0); Intros.
Inversion_clear H1.
Inversion_clear H2.
Apply CONSISTS_sat.
Exists x.
Exists x0.
Split; Auto.
Apply cong_tr with P.
Apply cong_sym; Auto.
Inversion_clear H1.
Apply cong_tr with (parP x x0).
Auto.
ProcCong.
Decompose [and] H1;Clear H1.
Generalize (ISZERO_sat_inv H4); Intro.
Generalize (ISZERO_sat_inv H5); Intro.
Split; [Apply ISZERO_sat; Auto | Apply ISZERO_sat; Auto].
Qed.*)

(*Lemma cong_ind_CONSISTS: (f,g:form)(cong_independent f) -> (cong_independent g) -> 
(cong_independent (CONSISTS f g)).
Intros.
Red.
Intros.
Generalize (CONSISTS_sat_inv H2); Intros.
Inversion_clear H3.
Inversion_clear H4.
Decompose [and] H3;Clear H3.
Apply CONSISTS_sat.
Exists x; Exists x0.
Split; Auto.
Apply cong_tr with P.
Apply cong_sym; Auto.
Auto.
Qed.

Definition cong_tindependent [p:tform] :=
 (P,Q:proc)(Cong P Q) -> (L:ChanList)(tsat p L#P) -> (tsat p L#Q).*)

(*Lemma cong_resp_tsat : (p:tform)
 (cong_tindependent p) ->
 (L:ChanList;P,P':proc)
 (Cong P P')->
 (tsat p L#P) -> (tsat p L#P').
Intros.
Red in H.
Apply H with P.
Auto.
Auto.
Qed.*)

(*Lemma cong_ind_ALWAYS: (f:tform)(cong_tindependent f) -> 
(cong_tindependent (ALWAYS f)).
Intros.
Unfold ALWAYS.
Red; Intros.
Generalize (NEGT_sat_inv H1); Intros.
Apply NEGT_sat.
Intro.
Apply H2.
Generalize (MAYEV_sat_inv H3); Intros.
Inversion_clear H4.
Inversion_clear H5.
Apply MAYEV_sat.
Assert (Cong_st L#Q L#P).
Red.
Simpl; Auto.
Split; [Auto | Apply cong_sym; Auto ].
Generalize (cong_respects_reds ? ? H4 ? H5); Intro.
Inversion_clear H7.
Inversion_clear H8.
Exists x0.
Split; Auto.
Apply NEGT_sat.
Generalize (NEGT_sat_inv H6); Intros.
Intro.
Apply H8.
Red in H.
NewInduction x.
Apply H with (sndT x0).
Red in H9.
Simpl in H9.
Apply cong_sym; Intuition.
NewInduction x0.
Simpl.
Red in H9.
Simpl in H9; Inversion_clear H9.
Rewrite H11; Auto.
Qed.*)

Definition Cong_ps (PS PS' : stateSeq) :=
  forall n,
    (forall Q,
      PS n = SomeT _ Q -> exists Q', Cong_st Q Q' /\ PS' n = SomeT _ Q') /\
    (PS n = NoneT _ -> PS' n = NoneT _).

Lemma Cong_ps_refl : forall PS, Cong_ps PS PS.
intros.
red in |- *.
intro.
split.
intros.
exists Q.
split; auto.
red in |- *.
split; auto.
apply cong_refl.
auto.
Qed.

Lemma Cong_ps_sym : forall p p', Cong_ps p p' -> Cong_ps p' p.
intros.
red in |- *.
intros.
split.
intros.
red in H.
generalize (H n); intros.
inversion_clear H1.
cut (exists Q, p n = SomeT _ Q).
intros.
inversion_clear H1.
generalize (H2 _ H4); clear H2; intros.
inversion_clear H1.
decompose [and] H2; clear H2.
exists x.
split; auto.
rewrite H0 in H5; injection H5; intros.
rewrite H2; apply Cong_st_sym; auto.
assert ((exists Q0, p n = SomeT _ Q0) \/ p n = NoneT _).
case (p n).
intro X; left; exists X; auto.
auto.
inversion_clear H1.
auto.
generalize (H3 H4); intros.
rewrite H0 in H1.
discriminate H1.
intros.
red in H.
generalize (H n); intros.
inversion_clear H1.
assert ((exists Q0, p n = SomeT _ Q0) \/ p n = NoneT _).
case (p n).
intro X; left; exists X; auto.
auto.
inversion_clear H1.
inversion_clear H4.
generalize (H2 _ H1); intros.
inversion_clear H4.
inversion_clear H5.
rewrite H0 in H6; discriminate H6.
auto.
Qed.

Lemma Cong_ps_trans :
 forall ps ps',
 Cong_ps ps ps' ->
 forall ps'', Cong_ps ps' ps'' -> Cong_ps ps ps''.
intros ps ps' H.
red in H.
intros.
red in |- *.
intro.
generalize (H n); intro X; inversion_clear X.
split.
intros.
generalize (H1 _ H3); intro X; inversion_clear X.
decompose [and] H4; clear H4.
red in H0.
generalize (H0 n); intro X; inversion_clear X.
clear H7.
generalize (H4 _ H6); intro X; inversion_clear X.
inversion_clear H7.
exists x0.
split.
red in |- *.
inversion_clear H8.
inversion_clear H5.
split.
rewrite H8; rewrite H7; auto.
apply cong_tr with (sndT x).
auto.
auto.
auto.
intros.
generalize (H0 n); intro X; inversion_clear X.
auto.
Qed.

Lemma cong_redseq :
 forall PS,
 isRedSeq PS ->
 forall P,
 PS 0 = SomeT state P ->
 forall P',
 Cong_st P P' ->
 exists PS', PS' 0 = SomeT _ P' /\ Cong_ps PS PS' /\ isRedSeq PS'.
intros.
unfold Cong_ps in |- *.
unfold isRedSeq in |- *.

let R :=
 constr:(fun (n : nat) (PS'n PS'Sn : optionT state) =>
         (n = 0 -> PS'n = SomeT state P') /\
         (forall Q : state,
          PS n = SomeT state Q ->
          exists Q' : state,
            Cong_st Q Q' /\
            PS'n = SomeT state Q' /\
            (forall R : state,
             PS (S n) = SomeT state R ->
             exists R' : state,
               Cong_st R R' /\ PS'Sn = SomeT state R' /\ Red Q' R') /\
            (PS (S n) = NoneT state -> PS'Sn = NoneT state)) /\
         (PS n = NoneT state -> PS'n = NoneT state) /\
         (PS'n = NoneT state -> PS'Sn = NoneT state)) in
cut (sigT (fun PS' : stateSeq => forall n : nat, R n (PS' n) (PS' (S n)))).
intro X; inversion_clear X.
exists x.
split.
exact (proj1 (H2 0) (refl_equal 0)).
split.
intro.
split.
intros.
generalize (proj1 (proj2 (H2 n)) _ H3); intro X; inversion_clear X.
decompose [and] H4; clear H4.
exists x0.
auto.
exact (proj1 (proj2 (proj2 (H2 n)))).
intro.
split.
intros.
cut ((exists Z : state, PS n = SomeT _ Z) \/ PS n = NoneT _).
intros.
inversion_clear H4.
inversion_clear H5.
red in H.
generalize (proj1 (H n) _ H4); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H6.
generalize (proj1 (proj2 (H2 n)) _ H4); intros.
inversion_clear H6.
decompose [and] H8; clear H8.
generalize (H9 _ H5); intro X; inversion_clear X.
decompose [and] H8; clear H8.
left; exists x3.
rewrite H10 in H3; injection H3; intro X; rewrite <- X; auto.
right.
apply (proj1 (proj2 (proj2 (H2 (S n))))).
auto.
generalize (proj1 (proj2 (proj2 (H2 n)))); intro.
rewrite (H4 H5) in H3; discriminate H3.
case (PS n).
intro p; left; exists p; auto.
auto.
exact (proj2 (proj2 (proj2 (H2 n)))).

apply
 EXT_sigT
  with
    (P := fun PS' : stateSeq =>
          forall n : nat,
          (n = 0 -> PS' n = SomeT state P') /\
          (forall Q : state,
           PS n = SomeT state Q ->
           exists Q' : state,
             Cong_st Q Q' /\
             PS' n = SomeT state Q' /\
             (forall R : state,
              PS (S n) = SomeT state R ->
              exists R' : state,
                Cong_st R R' /\ PS' (S n) = SomeT state R' /\ Red Q' R') /\
             (PS (S n) = NoneT state -> PS' (S n) = NoneT state)) /\
          (PS n = NoneT state -> PS' n = NoneT state) /\
          (PS' n = NoneT state -> PS' (S n) = NoneT state)).

red in H.
generalize (proj1 (H 0) _ H0); fold (isRedSeq PS) in H; intro.
inversion_clear H2.
inversion_clear H3.
inversion_clear H2.
generalize (cong_respects_red H4 H1); intro.
inversion_clear H2.
inversion_clear H5.

cut
 (sigT
    (fun u : stateSeq =>
     forall n : nat,
     (n = 0 -> u n = SomeT state P') /\
     (forall Q : state,
      PS n = SomeT state Q ->
      exists Q' : state,
        Cong_st Q Q' /\
        u n = SomeT state Q' /\
        (forall R : state,
         PS (S n) = SomeT state R ->
         exists R' : state,
           Cong_st R R' /\ u (S n) = SomeT state R' /\ Red Q' R') /\
        (PS (S n) = NoneT state -> u (S n) = NoneT state)) /\
     (PS n = NoneT state -> u n = NoneT state) /\
     (u n = NoneT state -> u (S n) = NoneT state))).
intro.
inversion_clear X.
exists x1.
auto.
apply
 Choice_Prop2
  with
    (R := fun (n : nat) (PS'n PS'Sn : optionT state) =>
          (n = 0 -> PS'n = SomeT state P') /\
          (forall Q : state,
           PS n = SomeT state Q ->
           exists Q' : state,
             Cong_st Q Q' /\
             PS'n = SomeT state Q' /\
             (forall R : state,
              PS (S n) = SomeT state R ->
              exists R' : state,
                Cong_st R R' /\ PS'Sn = SomeT state R' /\ Red Q' R') /\
             (PS (S n) = NoneT state -> PS'Sn = NoneT state)) /\
          (PS n = NoneT state -> PS'n = NoneT state) /\
          (PS'n = NoneT state -> PS'Sn = NoneT state))
    (P := SomeT _ P')
    (Q := SomeT _ x0).
split.
auto.
split.
intros.
rewrite H0 in H5; injection H5; intro X; rewrite <- X; clear X H5 Q.
exists P'.
split; auto.
split; auto.
split.
intros.
rewrite H3 in H5; injection H5; intro X; rewrite <- X; clear X H5 R.
exists x0.
split; auto.
intro X; rewrite H3 in X; discriminate X.
split.
intro X; rewrite H0 in X; discriminate X.
intro X; discriminate X.
intros.
apply
 EXT_sigT
  with
    (P := fun y : optionT state =>
          (S x1 = 0 -> Q' = SomeT state P') /\
          (forall Q : state,
           PS (S x1) = SomeT state Q ->
           exists Q'0 : state,
             Cong_st Q Q'0 /\
             Q' = SomeT state Q'0 /\
             (forall R : state,
              PS (S (S x1)) = SomeT state R ->
              exists R' : state,
                Cong_st R R' /\ y = SomeT state R' /\ Red Q'0 R') /\
             (PS (S (S x1)) = NoneT state -> y = NoneT state)) /\
          (PS (S x1) = NoneT state -> Q' = NoneT state) /\
          (Q' = NoneT state -> y = NoneT state)).
inversion_clear X.
inversion_clear H5.
inversion_clear H8.
inversion_clear H9.

cut ((exists Z : state, PS x1 = SomeT _ Z) \/ PS x1 = NoneT _).
intro X; inversion_clear X.
inversion_clear H9.

generalize (H5 _ H11); intro X; inversion_clear X.
decompose [and] H9; clear H9.

red in H.
generalize (proj1 (H x1) _ H11); intro X; inversion_clear X.
inversion_clear H9.
inversion_clear H15.
generalize (H13 _ H9); intro X; inversion_clear X.
decompose [and] H15; clear H15.

generalize (proj1 (H (S x1)) _ H9); intro X; inversion_clear X.
inversion_clear H15.
inversion_clear H19.
generalize (cong_respects_red H22 H18); intros.
inversion_clear H19.
inversion_clear H23.
exists (SomeT state x8).
split.
intro X; discriminate X.
split.
intros.
exists x6.
rewrite H9 in H23; injection H23; intro.
rewrite <- H25.
split; auto.
split; auto.
split.
intros.
exists x8.
split.
rewrite H15 in H26; injection H26; intro X; rewrite <- X; auto.
split; auto.
intros.
rewrite H15 in H26; discriminate H26.
split.
intros.
rewrite H9 in H23; discriminate H23.
intros.
rewrite H20 in H23; discriminate H23.
exists (NoneT state).
split.
intro X; discriminate X.
split.
intros.
rewrite H9 in H19; injection H19; intro.
rewrite <- H22.
exists x6.
split; auto.
split; auto.
split.
intros.
rewrite H15 in H23; discriminate H23.
auto.
split.
intro X; rewrite H9 in X; discriminate X.
auto.
exists (NoneT state).
split.
intro X; discriminate X.
split.
intros.
rewrite H9 in H15; discriminate H15.
split.
intros.
auto.
auto.
exists (NoneT state).
split.
intro X; discriminate X.
split.
intros.
red in H.
generalize (proj2 (H x1) H9); intro.
rewrite H11 in H12; discriminate H12.
split.
auto.
auto.
case (PS x1).
intro p; left; exists p; auto.
auto.

(* case of the process 0 is stable *)

exists
 (fun n : nat => match n with
                 | O => SomeT state P'
                 | _ => NoneT state
                 end).
intro.
split.
intros.
rewrite H2.
auto.
split.
intros.
cut (n = 0 \/ (exists m : nat, n = S m)).
intro.
inversion_clear H4.
rewrite H5 in H2; rewrite H0 in H2; injection H2; intros.
rewrite <- H4.
exists P'.
split; auto.
rewrite H5.
split; auto.
split.
intros.
rewrite H3 in H6; discriminate H6.
auto.
inversion_clear H5.
rewrite H4 in H2.
generalize (isRedSeq_none _ H _ H3); intros.
assert (1 <= S x).
omega.
generalize (H5 _ H6); intros.
rewrite H2 in H7; discriminate H7.
case n.
auto.
intros.
right; exists n0; auto.
case n.
split.
intros.
rewrite H0 in H2; discriminate H2.
auto.
intros.
split; [ auto | auto ].
Qed.

Lemma cong_maxredseq_inter :
 forall PS : stateSeq,
 isMaxRedSeq PS ->
 forall P : state,
 PS 0 = SomeT state P ->
 forall P' : state,
 Cong_st P P' ->
 forall PS' : stateSeq,
 isRedSeq PS' /\ PS' 0 = SomeT _ P' /\ Cong_ps PS PS' -> isMaxRedSeq PS'.
intros.
red in |- *.
split.
intuition.
intros.
cut (PS n = NoneT state \/ (exists Q : state, PS n = SomeT state Q)).
(* case (PS n)==(NoneT state) *)
intro X; inversion_clear X.
decompose [and] H2; clear H2.
red in H9.
generalize (proj2 (H9 n) H5); intro.
rewrite H3 in H2; discriminate H2.
(* case (EXT Q:state | (PS n)==(SomeT state Q)) 
idea: we show that PS n must be stable (since PS n+1 is NoneT and PS is a MaxRedSeq)
and since ps's are Cong_ps, then PS' n is also stable
*)
inversion_clear H5.
cut (Stable x).
intros.
decompose [and] H2; clear H2.
red in H10.
generalize (H10 n); intro.
inversion_clear H2.
clear H11.
generalize (H8 _ H6); intros.
inversion_clear H2.
inversion_clear H11.
apply cong_respects_stable with x.
auto.
rewrite H3 in H12; injection H12; intros.
rewrite H11; auto.
(* show the cut Stable x *)
red in |- *; intro.
inversion_clear H5.
red in H.
inversion_clear H.
cut (PS (S n) = NoneT state).
intro.
generalize (H8 _ _ H6 H); intro.
apply H9.
exists x0; auto.
(* show the cut (PS (S n))==(NoneT state) *)
decompose [and] H2; clear H2.
generalize (Cong_ps_sym H11); intros.
red in H2.
generalize (H2 (S n)); intros.
inversion_clear H9.
tauto.
(* show the cut (PS n)==(NoneT state)\/(EXT Q:state | (PS n)==(SomeT state Q)) *)
case (PS n).
intro p; right; exists p; auto.
auto.
Qed.

Lemma cong_maxredseq :
 forall PS : stateSeq,
 isMaxRedSeq PS ->
 forall P : state,
 PS 0 = SomeT state P ->
 forall P' : state,
 Cong_st P P' ->
 exists PS' : stateSeq,
   isMaxRedSeq PS' /\ PS' 0 = SomeT _ P' /\ Cong_ps PS PS'.
intros.
red in H.
inversion_clear H.
generalize (cong_redseq H2 H0 H1); intros.
inversion_clear H.
decompose [and] H4; clear H4.
generalize
 (cong_maxredseq_inter (conj H2 H3) H0 H1 (conj H7 (conj H H6)));
 intro.
exists x.
split; auto.
Qed.

(* I couldn't prove this one *)
Axiom cong_maxfairredseq_inter :
    forall PS : stateSeq,
    isMaxRedSeq PS ->
    isFairRedSeq PS ->
    forall P : state,
    PS 0 = SomeT state P ->
    forall P' : state,
    Cong_st P P' ->
    forall PS' : stateSeq,
    isMaxRedSeq PS' /\ PS' 0 = SomeT _ P' /\ Cong_ps PS PS' ->
    isFairRedSeq PS'.

Lemma cong_maxfairredseq :
 forall PS : stateSeq,
 isMaxRedSeq PS ->
 isFairRedSeq PS ->
 forall P : state,
 PS 0 = SomeT state P ->
 forall P' : state,
 Cong_st P P' ->
 exists PS' : stateSeq,
   isMaxRedSeq PS' /\
   isFairRedSeq PS' /\ PS' 0 = SomeT _ P' /\ Cong_ps PS PS'.
intros.
red in H.
inversion_clear H.
generalize (cong_redseq H3 H1 H2); intros.
inversion_clear H.
decompose [and] H5; clear H5.
generalize (conj H3 H4); intro X; fold (isMaxRedSeq PS) in X.
generalize (cong_maxredseq_inter X H1 H2 (conj H8 (conj H H7)));
 intro.
generalize
 (cong_maxfairredseq_inter X H0 H1 H2 (conj H5 (conj H H7))); 
 intro.
exists x.
auto.
Qed.

Lemma cong_resp_tsatisfaction :
 forall (f : tform) (L : ChanList) (P Q : proc),
 Cong Q P -> (tsat f (L # P) <-> tsat f (L # Q)).
intro.
induction f.
split; intros.
apply STAT_sat.
apply cong_resp_sat with P.
apply (STAT_sat_inv H0).
auto.
apply STAT_sat.
apply cong_resp_sat with Q.
apply (STAT_sat_inv H0).
apply cong_sym; auto.
split; intros.
apply NEGT_sat; intro; generalize (NEGT_sat_inv H0); intro.
apply H2.
generalize (IHf L _ _ H); intros.
tauto.
apply NEGT_sat; intro; generalize (NEGT_sat_inv H0); intro.
apply H2.
generalize (IHf L _ _ H); intros.
tauto.
split; intros.
apply ORT_sat; generalize (ORT_sat_inv H0); intros.
generalize (IHf1 L _ _ H); intro.
generalize (IHf2 L _ _ H); intro.
tauto.
apply ORT_sat; generalize (ORT_sat_inv H0); intros.
generalize (IHf1 L _ _ H); intro.
generalize (IHf2 L _ _ H); intro.
tauto.
split; intros.
apply MAYEV_sat.
generalize (MAYEV_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
assert (Cong_st (L # Q) (L # P)).
red in |- *.
simpl in |- *; auto.
generalize (cong_respects_reds H1 (Cong_st_sym H2)); intro.
inversion_clear H4.
inversion_clear H5.
exists x0.
split; auto.
induction x; induction x0.
inversion_clear H6.
generalize (IHf a _ _ H7); intros.
simpl in H5; rewrite <- H5.
tauto.
apply MAYEV_sat.
generalize (MAYEV_sat_inv H0); intros.
inversion_clear H1.
inversion_clear H2.
assert (Cong_st (L # Q) (L # P)).
red in |- *.
simpl in |- *; auto.
generalize (cong_respects_reds H1 H2); intro.
inversion_clear H4.
inversion_clear H5.
exists x0.
split; auto.
induction x; induction x0.
inversion_clear H6.
generalize (IHf a _ _ H7); intros.
simpl in H5; rewrite <- H5.
tauto.
split; intros.
apply MUSTEV_sat.
generalize (MUSTEV_sat_inv H0); intros.
assert (Cong_st (L # Q) (L # P)).
split; auto.
generalize (cong_maxredseq H3 H2 H4); intro.
inversion_clear H5.
decompose [and] H6; clear H6.
generalize (H1 _ H8 H5); intro X; inversion_clear X.
inversion_clear H6.
inversion_clear H7.
generalize (Cong_ps_sym H9); intro.
red in H7.
generalize (H7 x1); intro.
inversion_clear H11.
generalize (H12 _ H6); intro. 
inversion_clear H11.
inversion_clear H14.
exists x2; exists x1.
split; auto.
induction x2.
induction x0.
red in H11.
inversion_clear H11.
generalize (IHf a _ _ H16); intros.
simpl in H14; rewrite H14 in H11.
simpl in H11.
rewrite H14 in H10; tauto.
apply MUSTEV_sat.
generalize (MUSTEV_sat_inv H0); intros.
assert (Cong_st (L # Q) (L # P)).
split; auto.
generalize (cong_maxredseq H3 H2 (Cong_st_sym H4)); intro.
inversion_clear H5.
decompose [and] H6; clear H6.
generalize (H1 _ H8 H5); intro X; inversion_clear X.
inversion_clear H6.
inversion_clear H7.
generalize (Cong_ps_sym H9); intro.
red in H7.
generalize (H7 x1); intro.
inversion_clear H11.
generalize (H12 _ H6); intro. 
inversion_clear H11.
inversion_clear H14.
exists x2; exists x1.
split; auto.
induction x2.
induction x0.
red in H11.
inversion_clear H11.
generalize (IHf a _ _ H16); intros.
simpl in H14; rewrite H14 in H11.
simpl in H11.
rewrite H14 in H10; tauto.
split; intros.
apply FMUSTEV_sat.
generalize (FMUSTEV_sat_inv H0); intros.
assert (Cong_st (L # Q) (L # P)).
split; auto.
generalize (cong_maxfairredseq H3 H4 H2 H5); intro.
inversion_clear H6.
decompose [and] H7; clear H7.
generalize (H1 _ H8 H6 H9); intro X; inversion_clear X.
inversion_clear H7.
inversion_clear H10.
generalize (Cong_ps_sym H11); intro.
red in H10.
generalize (H10 x1); intro.
inversion_clear H13.
generalize (H14 _ H7); intro. 
inversion_clear H13.
inversion_clear H16.
exists x2; exists x1.
split; auto.
induction x2.
induction x0.
red in H13.
inversion_clear H13.
generalize (IHf a _ _ H18); intros.
simpl in H16; rewrite H16 in H13; simpl in H13; rewrite H16 in H12; tauto.
apply FMUSTEV_sat.
generalize (FMUSTEV_sat_inv H0); intros.
assert (Cong_st (L # Q) (L # P)).
split; auto.
generalize (cong_maxfairredseq H3 H4 H2 (Cong_st_sym H5)); intro.
inversion_clear H6.
decompose [and] H7; clear H7.
generalize (H1 _ H8 H6 H9); intro X; inversion_clear X.
inversion_clear H7.
inversion_clear H10.
generalize (Cong_ps_sym H11); intro.
red in H10.
generalize (H10 x1); intro.
inversion_clear H13.
generalize (H14 _ H7); intro. 
inversion_clear H13.
inversion_clear H16.
exists x2; exists x1.
split; auto.
induction x2.
induction x0.
red in H13.
inversion_clear H13.
generalize (IHf a _ _ H18); intros.
simpl in H16; rewrite H16 in H13; simpl in H13; rewrite H16 in H12; tauto.
Qed.

Lemma cong_resp_tsat :
 forall (L : ChanList) (P : proc) (f : tform),
 tsat f (L # P) -> forall Q : proc, Cong Q P -> tsat f (L # Q).
intros.
generalize (cong_resp_tsatisfaction f L H0).
tauto.
Qed.

(*Recursive Tactic Definition cong_ind :=
Match Context With
  [ |- (cong_independent (FMUSTEV ?1))] ->
Apply cong_ind_FMUSTEV;
cong_ind
| [ |- (cong_independent (OR ?1 ?2))] ->
Apply cong_ind_OR;
[cong_ind | cong_ind]
| [ |- (cong_independent (CONSISTS ?1 ?2))] ->
Apply cong_ind_CONSISTS;
[cong_ind | cong_ind]
| [ |- (cong_independent (OUTPUTS ?3 ?4 ?5)) ] ->
Apply cong_ind_OUTPUTS
| [ |- (cong_independent (INPUTS ?3 ?4)) ] ->
Apply cong_ind_INPUTS
(*| [ |- (cong_independent ZEROS) ] ->
Apply cong_ind_ZEROS*)
| [ |- (cong_independent (ALWAYS ?1)) ] ->
Apply cong_ind_ALWAYS;
cong_ind
| _ -> Fail.*)

Ltac clean_zero :=
  match goal with
  |  |- (tsat ?X1 (?X2 # ?X3)) =>
      let tmp := elim_zero X3 in
      (apply cong_resp_tsat with tmp; [ idtac | ProcCong ])
  end.

Unset Implicit Arguments. 