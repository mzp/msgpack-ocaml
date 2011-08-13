Require Import Classical.
Require Import ArithRing.
Require Import util.
Require Import chan.
Require Import chanlist.
Require Import set.
Require Import applpi.
Require Import inj.
Require Import inv.
Require Import inv2.
Require Import inv_dis.
Require Import cong_trans.
Require Import cong_trans2.
Require Import redseq.
Require Import trans_trans2.
Require Import logic.
Require Import logic_prop.
Require Import logic_tactic.
Require Import logic_tactic2.

Lemma conf_red_obs_rin_out' : forall A b (c : chan A b) v ps L0 R T U,
  isMaxRedSeq ps -> isFairRedSeq ps ->
  ps 0 = SomeT _ (L0 # parP R (parP (c ??* T) (c << v >> U))) ->
  (forall R', Reds (L0 # R) R' ->
    ~ (exists v, R' |= OUTPUTS c v ISANY) /\ ~ R' |= INPUTS c ISANY ) ->
  exists n, (exists R',
    Reds (L0 # R) R' /\
    ps n = SomeT _ (fstT R' # parP (sndT R') (parP (parP (c ??* T) (T v)) U))).
intros A b c v ps L0 R T U maxredseq fairredseq ps0 interfere.
apply NNPP.
intro.
(* we'll prove later that rinP is infinitely enabled (under the ab absurdo hypothesis); using that cut, the fairness assumption we'll let us find a process in which rinP is reduced *)
cut (forall ps', (is_postfix ps' ps)->(infinitely_often (fun Q => (enabled (c ??* T) Q)) ps')).
intro.
red in fairredseq.
generalize (fairredseq _ (is_postfix_refl ps) _ (H0 ps (is_postfix_refl ps))); intro.
red in H1.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
decompose [and] H2; clear H2.
rename x into m.
rename x0 into P.
rename x1 into P'.
rename H1 into ps_m.
rename H4 into ps_Sm.
rename H5 into reduced_rinP.

(* ASSERTION BEGIN *)

(* we prove that the process only changes by reducing the observer (since we know ab absurdo that rinP is never reduced and that the observer is not interfering *)
assert (forall n,
  (exists R', (Reds (L0#R) R') /\ (ps n)=(SomeT _ ((fstT R')#(parP (sndT R') (parP (c ??* T) (c <<v>> U))))))).
intro n.
induction n.
(* base case *)
exists (L0#R).
split; auto.
apply reds_b.
(* inductive case *)
inversion_clear IHn.
inversion_clear H1.
inversion maxredseq.
clear H4.
red in H1.
generalize (H1 n); clear H1; intro.
inversion_clear H1.
clear H5.
generalize (H4 _ H3); clear H4; intro X; inversion_clear X.
inversion_clear H1.
inversion_clear H4.
inversion_clear H5.
(* we explore all the possible reductions between the processes at rank n and at rank n+1, the only cases that are ok are when the observer process does a tau or a new *)
inversion H4.
subst x0 x1 P0 L.
generalize (inv_trans_parP_obs_rinP_outP_TauL H9); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
decompose [and] H6; clear H6.
(* the observer does the out part of a tau, which is impossible because of the non-interference hypothesis *)
assert (exists v, x |= (OUTPUTS c v ISANY)).
exists x3.
generalize (inv_trans_OutL H5); intros.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
induction x.
apply cong_resp_sat with (parP x5 (c <<x3>> x4)).
SolveOUTPUTS.
auto.
auto.
generalize (interfere _ H2); intro X; inversion_clear X.
absurd (exists v, x |= (OUTPUTS c v ISANY)).
auto.
auto.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
decompose [and] H6; clear H6.
(* the observer does the in part of a tau, which is impossible because of the non-interference hypothesis *)
assert (x |= (INPUTS c ISANY)).
generalize (inv_trans_InL H5); intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
induction x.
apply cong_resp_sat with (parP x4 (c ?? x3)).
SolveINPUTS.
auto.
auto.
generalize (interfere _ H2); intro X; inversion_clear X.
absurd (x |= (INPUTS c ISANY)).
auto.
auto.
inversion_clear H6.
inversion_clear H5.
inversion_clear H6.
(* the observer does a tau, which let us prove the goal *)
induction x.
exists (a#x0).
split.
apply reds_i2 with (a#b1).
auto.
exists (epsilon x2).
apply red_com.
auto.
simpl.
subst Q.
auto.
(* the communicating pair does a tau, which is contradictory with the hypothesis ab absurdo that says that rinP is never reduced *)
assert (exists n,
          (exists R',
               (Reds (L0#R) R') /\ 
	       (ps n)=(SomeT _ ((fstT R')#(parP (sndT R') (parP (parP (c ??* T) (T v)) U)))))).
exists (S n).
exists x.
split; auto.
subst Q; auto.
generalize (H H6); contradiction.
(* the process does a new, this can only happen in the case of the observer *)
inversion H7.
subst Q L1 Q0 P1.
induction x.
exists ((x2&a)#P'0).
split.
apply reds_i2 with (a#b1).
auto.
exists (New x2).
apply red_new; auto.
subst x0.
auto.
subst Q L1 P1 Q0.
inversion H15.
inversion H16.
inversion H16.
(* case where there is no process at rank n+1: impossible by definition of the reduction sequence *)
inversion maxredseq.
generalize (H5 _ _ H3 H1); clear H3 H1; intro.
red in H1.
assert (exists KQ, (Red ((fstT x)#(parP (sndT x) (parP (c ??* T) (c <<v>> U)))) KQ)).
exists ((fstT x)#(parP (sndT x) (parP (parP (c ??* T) (T v)) U))).
exists (epsilon c).
apply red_com.
apply tr_parR.
apply tr_comIO with (A:=A) (x:=c) (v:=v).
apply tr_rin.
apply tr_out.
generalize (H1 H3); contradiction.

(* ASSERTION END *)

(* at this point, we know that the process has always the same form, that is that the communicating pair is never reduced (and this thanks to the ab absurdo hypothesis)

we now have this assertion + the knowledge of some P/P' pair of processes such that P -> P' with rinP reduced in between (this comes from the fairness hypothesis)
*)

assert (Red P P').
inversion maxredseq.
clear H3; red in H2.
generalize (H2 m); clear H2; intro.
inversion_clear H2.
clear H4; generalize (H3 _ ps_m); intro.
inversion_clear H2.
inversion_clear H4.
inversion_clear H2.
inversion_clear H5.
rewrite ps_Sm in H4.
injection H4; clear H4; intro; subst x.
exists x0.
auto.
rewrite ps_Sm in H4; discriminate H4.
induction P.
induction P'.
generalize (reduced_rin_red_tau reduced_rinP H2); intro.
inversion_clear H3.
inversion_clear H5.
inversion_clear H3.
generalize (H1 m); intro.
inversion_clear H3.
inversion_clear H6.

rewrite H7 in ps_m.
injection ps_m; intros.
subst a b0 a0.
clear ps_m.

(* we just have to infer the from of P' to find a contradiction, deux cas similaires *)

inversion_clear H5.

(* premier cas *)

generalize (inv_trans2_rinP_outP_tau H4); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
inversion_clear H8.
decompose [and] H6;clear H6.
injection H5; clear H5; intros.
rewrite <-H6 in H8.
assert (x1 |= (INPUTS c ISANY)).
induction x1.
generalize (inv_trans2_single_rinP_cong H8); intros.
inversion_clear H9.
inversion_clear H12.
apply cong_resp_sat with (parP x1 (rinP c T)).
SolveINPUTS.
auto.
auto.
generalize (interfere _ H3); intro X; inversion_clear X.
generalize (H13 H9); contradiction.
inversion_clear H6.
inversion_clear H8.
assert (x1 |= (INPUTS c ISANY)).
induction x1.
injection H5; intros.
rewrite H10.
generalize (inv_trans2_pair_rinP_outP_cong H6); intro X; inversion_clear X.
decompose [and] H11;clear H11.
apply cong_resp_sat with (parP x1 (parP (rinP c T) (outP c x x0))).
SolveINPUTS.
auto.
auto.
generalize (interfere _ H3); intro X; inversion_clear X.
auto.
inversion_clear H8.
injection H5; intros.
rewrite <-H8 in H6.
generalize (inv_trans2_rinP_outP_tau H6); intro X; inversion_clear X.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
inversion_clear H12.
inversion_clear H13.
decompose [and] H12;clear H12.
assert (exists n:nat,
          (exists R':state, 
               (Reds (L0#R) R')
               /\(ps n)=(SomeT state
                      ((fstT R')#(parP (sndT R'))
                                  (parP (parP (rinP c T) (T v)) U))))).
injection H11; intros.
rewrite <-H12 in H15.
rewrite <-H14 in H13.
generalize (inv_trans2_outP H15); intro X; inversion_clear X.
inversion_clear H18.
generalize (OutL_inj H19); intro X; inversion_clear X.
rewrite H21 in H13.
rewrite H21 in H15.
generalize (inv_trans2_rinP H13); intro X; inversion_clear X.
inversion_clear H23.
inversion_clear H24.
generalize (InL_inj H23); intro.
inversion_clear H24.
rewrite <-H27 in H25.
exists (S m).
exists x1.
split; auto.
rewrite ps_Sm.
rewrite H9.
rewrite <-H10.
rewrite H16.
rewrite H25.
rewrite H20.
auto.
auto.
inversion_clear H12.
inversion_clear H13.
injection H11; intros.
rewrite <-H15 in H12.
inversion H12.
inversion_clear H13.
injection H11; intros.
rewrite <-H13 in H12.
inversion H12.

(* second cas *)

generalize (inv_trans2_outP_rinP_tau H4); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
inversion_clear H8.
decompose [and] H6;clear H6.
injection H5; clear H5; intros.
rewrite <-H6 in H8.
assert (exists v, (x1 |= (OUTPUTS c v ISANY))).
exists x.
induction x1.
generalize (inv_trans2_single_outP_cong H8); intros.
inversion_clear H9.
inversion_clear H12.
apply cong_resp_sat with (parP x1 (outP c x x0)).
SolveOUTPUTS.
auto.
auto.
generalize (interfere _ H3); intro X; inversion_clear X.
generalize (H12 H9); contradiction.
inversion_clear H6.
inversion_clear H8.
assert (exists v, x1 |= (OUTPUTS c v ISANY)).
exists x.
induction x1.
injection H5; intros.
rewrite H10.
generalize (inv_trans2_pair_outP_rinP_cong H6); intro X; inversion_clear X.
decompose [and] H11;clear H11.
apply cong_resp_sat with (parP x1 (parP (outP c x x0) (rinP c T))).
SolveOUTPUTS.
auto.
auto.
generalize (interfere _ H3); intro X; inversion_clear X.
auto.
inversion_clear H8.
injection H5; intros.
rewrite <-H8 in H6.
generalize (inv_trans2_outP_rinP_tau H6); intro X; inversion_clear X.
inversion_clear H11.
inversion_clear H12.
inversion_clear H13.
inversion_clear H12.
inversion_clear H13.
decompose [and] H12;clear H12.
injection H11; intros.
rewrite <-H14 in H13.
generalize (inv_trans2_rinP H13); intro X; inversion_clear X.
discriminate H17.
inversion_clear H12.
inversion_clear H13.
injection H11; intros.
rewrite <-H15 in H12; inversion H12.
inversion_clear H13.
injection H11; intros.
rewrite <-H13 in H12; inversion H12.

(* the new goal is:
(ps':stateSeq)
    (is_postfix ps' ps)
    ->(infinitely_often [Q:proc](enabled (rinP A c T) Q) ps') *)
unfold infinitely_often.
(* the idea is to make an induction on the rank of the process,
we generalize the current goal to be able to do so *)
cut (forall (PS':stateSeq), (is_postfix PS' ps) ->
  (exists n0:nat,
    (exists R0:state,
      (Reds (L0#R) R0) /\
      (PS' n0) = (SomeT _ ((fstT R0)#(parP (sndT R0) (parP (rinP c T) (outP c v U))))) /\
      (enabled (rinP c T) ((fstT R0)#(parP (sndT R0) (parP (rinP c T) (outP c v U)))))))).
intros.
inversion_clear H1.
generalize (H0 (fun n:nat => (ps (plus (plus m x) n)))); intro.
assert (is_postfix (fun n:nat => (ps (plus (plus m x) n))) ps).
exists (plus m x); intro.
assert ((plus (plus m x) m0)=(plus m0 (plus m x))).
ring.
rewrite H3; auto.
generalize (H1 H3); clear H1; intro.
inversion_clear H1.
exists x0.
inversion_clear H4.
decompose [and] H1;clear H1.
exists ((fstT x1)#(parP (sndT x1) (parP (rinP c T) (outP c v U)))).
split.
rewrite (H2 (plus m x0)).
assert ((plus (plus m x0) x)=(plus (plus m x) x0)).
ring.
rewrite H1; auto.
red.
exists ((fstT x1)#(parP (sndT x1) (parP (parP (rinP c T) (T v)) U))).
apply red_pairL with (c:=c) (S:=(outP c v U)).
apply tr2_parR.
apply tr2_comIO with (x:=c) (v:=v).
apply tr2_rin.
apply tr2_out.
(* the new goal is:
   (ps':stateSeq)
    (is_postfix ps' ps)
    ->(PS':stateSeq)
       (is_postfix PS' ps')
       ->(EX n0:nat |
            (EXT R0:state |
                 (Reds L0#R R0)
                 /\(PS' n0)
                    ==(SomeT state
                        (fstT R0)#(parP (sndT R0)
                                    (parP (rinP c T) (outP c v U))))
                   /\(enabled (rinP c T)
                       (fstT R0)#(parP (sndT R0)
                                   (parP (rinP c T) (outP c v U)))))) *)
(* we generalize the goal to showing that it holds for any rank *)
cut (forall (n0:nat), 
  (exists R0:state,
    (Reds (L0#R) R0)
    /\(ps n0) =(SomeT state ((fstT R0)#(parP (sndT R0) (parP (rinP c T) (outP c v U)))))
    /\(enabled (rinP c T) ((fstT R0)#(parP (sndT R0) (parP (rinP c T) (outP c v U))))))).
intros.
exists O.
inversion_clear H1.
rewrite (H2 O).
generalize (H0 (plus (0) x)); intro X; inversion_clear X.
decompose [and] H1;clear H1.
exists x0.
auto.
(* new goal:
   (n0:nat)
    (EXT R0:state |
         (Reds L0#R R0)
         /\(ps n0)
            ==(SomeT state
                (fstT R0)#(parP (sndT R0)
                            (parP (rinP c T) (outP c v U))))
           /\(enabled (rinP c T)
               (fstT R0)#(parP (sndT R0) (parP (rinP c T) (outP c v U)))))
*)
intro.
induction n0.
(* base case *)
exists (L0#R).
split.
apply reds_b.
split; auto.
unfold enabled.
assert ((reduced (rinP c T) (L0#(parP R (parP (rinP c T) (outP c v U))))
(L0#(parP R (parP (parP (rinP c T) (T v)) U))))).
apply red_pairL with (S:=(outP c v U)) (c:=c).
apply tr2_parR.
apply tr2_comIO with (A:=A) (x:=c) (v:=v).
apply tr2_rin.
apply tr2_out.
exists (L0#(parP R (parP (parP (rinP c T) (T v)) U))).
auto.

(* inductive case *)

inversion_clear IHn0.
inversion_clear H0.
inversion_clear H2.
generalize maxredseq; intro X; unfold isMaxRedSeq in X; inversion_clear X.
clear H4; unfold isRedSeq in H2.
generalize (H2 n0); clear H2; intro.
inversion_clear H2.
clear H5.
generalize (H4 _ H0); clear H4; intro.
inversion_clear H2.
inversion_clear H4.
inversion_clear H2.
inversion_clear H5.
inversion H2.
clear H5 L H7 P.
generalize (inv_trans_parP_obs_rinP_outP_TauL H9); intro X; inversion_clear X.
inversion_clear H5.
inversion_clear H7.
inversion_clear H5.
decompose [and] H7; clear H7.
generalize (interfere _ H1); intro X; elim X; clear X; intros.
assert (exists v, (x |= (OUTPUTS c v ISANY))).
exists x5.
induction x.
generalize (inv_trans_OutL H5); intro X; inversion_clear X.
inversion_clear H13.
inversion_clear H14.
apply cong_resp_sat with (parP x6 (outP c x5 x)).
SolveOUTPUTS.
auto.
auto.
generalize (H7 H13); contradiction.
inversion_clear H5.
inversion_clear H7.
inversion_clear H5.
decompose [and] H7;clear H7.
generalize (interfere _ H1); intro X; elim X; clear X; intros.
assert (x |= (INPUTS c ISANY)).
induction x.
generalize (inv_trans_InL H5); intro X; inversion_clear X.
inversion_clear H13.
inversion_clear H14.
apply cong_resp_sat with (parP x5 (inP c x)).
SolveINPUTS.
auto.
auto.
generalize (H10 H13); contradiction.
inversion_clear H7.
inversion_clear H5.
inversion_clear H7.
exists ((fstT x)#x3).
split.
apply reds_i2 with x.
auto.
exists (epsilon x2).
induction x.
apply red_com.
auto.
split.
simpl; rewrite <-H10.
rewrite H4; rewrite <-H8; auto.
unfold enabled.
exists ((fstT x)#(parP (sndT ((fstT x)#x3)) (parP (parP (rinP c T) (T v)) U))).
apply red_pairL with (S:=(outP c v U)) (c:=c).
apply tr2_parR.
apply tr2_comIO with (A:=A) (x:=c) (v:=v).
apply tr2_rin.
apply tr2_out.
assert (exists n:nat,
          (exists R':state,
               (Reds (L0#R) R')
               /\(ps n) = (SomeT state
                      ((fstT R')#(parP (sndT R')
                                  (parP (parP (rinP c T) (T v)) U)))))).
exists (S n0).
exists x.
split; auto.
rewrite <-H5.
rewrite H4; rewrite <-H8; auto.
generalize (H H7); contradiction.
clear H5 L H6 P.
inversion H7.
clear H5 P H6 L.
exists ((x2&(fstT x))#P').
split.
apply reds_i2 with x.
auto.
exists (New x2).
induction x.
apply red_new.
auto.
auto.
split.
simpl.
rewrite H12.
rewrite H4; rewrite <-H9; auto.
assert (reduced (rinP c T) ((x2&(fstT x))#(parP P' (parP (rinP c T) (outP c v U))) )
((x2&(fstT x))#(parP P' (parP (parP (rinP c T) (T v)) U)))).
apply red_pairL with (S:=(outP c v U)) (c:=c).
apply tr2_parR.
apply tr2_comIO with (A:=A) (x:=c) (v:=v).
apply tr2_rin.
apply tr2_out.
unfold enabled; exists ((x2&(fstT x))#(parP P' (parP (parP (rinP c T) (T v)) U))).
auto.
inversion H13.
inversion H18.
inversion H18.
inversion_clear maxredseq.
generalize (H5 _ _ H0 H4); intro X.
assert (exists KQ:state,
             (Red
               ((fstT x)#(parP (sndT x) (parP (rinP c T) (outP c v U))))
               KQ)).
exists ((fstT x)#(parP (sndT x) (parP (parP (rinP c T) (T v)) U))).
exists (epsilon c).
apply red_com.
apply tr_parR.
apply tr_comIO with (x:=c) (v:=v).
apply tr_rin.
apply tr_out.
generalize (X H6); contradiction.
Qed.

(** confluence between a communicating pair and a non-interfering process *)
Lemma conf_red_obs_rin_out : forall A b (c : chan A b) v T U R L,
 ChanList_is_set L ->
 (forall R', Reds (L # R) R' ->
   ~ (exists v, R' |= (OUTPUTS c v ISANY)) /\ ~ R' |= (INPUTS c ISANY)) ->
 forall B b' (d : chan B b') w,
   (forall L', ChanList_is_set L' /\ incC L L' ->
     (L' # parP (parP (c ??* T) (T v)) U) |= OUTPUTS d w ISANY) ->
 (L # parP R (parP (c ??* T) (c << v >> U))) |=t FMUSTEV (STAT (OUTPUTS d w ISANY)) .
intros.
apply FMUSTEV_sat.
intros.
generalize (conf_red_obs_rin_out' _ _ _ _ _ _ _ _ _ H3 H4 H2 H0); intro X;
 inversion_clear X.
inversion_clear H5.
inversion_clear H6.
exists (fstT x0 # parP (sndT x0) (parP (parP (c ??* T) (T v)) U)).
exists x.
split; auto.
apply STAT_sat.
apply outputs_parP_L.
apply H1.
eapply channels_created_so_far_is_growing_set.
auto.
apply H5.
Qed.

Inductive guard : ChanList -> proc -> Prop :=
  | guard_zeroP : guard nilC zeroP
  | guard_outP : forall A b (c : chan A b) v P,
      guard (c & nilC) (c << v >> P)
  | guard_inP : forall A b (c : chan A b) P,
      guard (c & nilC) (c ?? P)
  | guard_rinP : forall A b (c : chan A b) P,
      guard (c & nilC) (c ??* P)
  | guard_parP : forall P Q lp lq,
      guard lp P -> guard lq Q -> guard (lq ^^ lp) (parP P Q)
  | guard_nuP : forall A (C : chan A false -> proc), 
    guard nilC (nuP C)
  | guard_nuPl : forall A (C : chan A true -> proc), 
    guard nilC (nuPl C).

(** confluence of nu actions: 
   the order in which nu actions are performed does not matter 
   for a goal of the shape P |=t FMUSTEV ... *)
Axiom conf_red_new : forall L P P' A b (c : chan A b),
  (L # P) -- New c --> (c & L # P') ->
  forall p Lp, tfree_vars Lp p -> ~ in_ChanList c Lp ->
    forall K, guard K P' -> inter Lp K nilC ->
      (c & L # P') |=t FMUSTEV p  -> 
        (L # P) |=t FMUSTEV p.

Axiom conf_red_new_always : forall L P P' A b (c : chan A b),
  (L # P) -- New c --> (c & L # P') ->
    forall p, tnotin c p ->
      (c & L # P') |=t FMUSTEV (ALWAYS p) ->
        (L # P) |=t FMUSTEV (ALWAYS p) .

(** confluence of linearized communications: 
   when the goal is of the form P |=t FMUSTEV ALWAYS ..., 
   linearized communications can be performed in priority *)
Axiom conf_red_com_always : forall L P P' A (c : chan A true),
    (L # P) -- epsilon c --> (L # P') ->
    forall p,
       (L # P') |=t FMUSTEV (ALWAYS p) -> 
        (L # P) |=t  FMUSTEV (ALWAYS p).

(** confluence of linearized communications: 
   when the goal is of the form P |=t FMUSTEV ..., 
   linearized communications can be performed in priority under some conditions *)
Axiom conf_red_com : forall L P P' A (c : chan A true),
    (L # P) -- epsilon c --> (L # P') ->
    forall p Lp, tfree_vars Lp p -> ~ in_ChanList c Lp ->
      forall K, guard K P' -> inter Lp K nilC -> 
        (L # P') |=t FMUSTEV p  -> 
          (L # P) |=t FMUSTEV p .


