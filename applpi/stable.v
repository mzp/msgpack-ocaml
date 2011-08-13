Require Import eqdep.
Require Import util.
Require Import util_for_tactics.
Require Import chan.
Require Import chanlist.
Require Import set.
Require Import applpi.
Require Import inv.
Require Import fresh.
Require Import redseq.
Require Import cong.
Require Import cong_tactic.
Require Import cong_trans.
Require Import cong_resp.
Require Import cong_inj_dis.
Require Import logic.
Require Import logic_prop.

Set Implicit Arguments.

 (** a process is guarded by some channel list when it is solely composed of input/output subprocesses *)

Inductive guarded : ChanList -> proc -> Prop :=
  | guarded_zeroP : guarded nilC zeroP
  | guarded_outP : forall A b (c : chan A b) v P,
      guarded (c & nilC) (c << v >> P)
  | guarded_inP : forall A b (c : chan A b) P,
      guarded (c & nilC) (c ?? P)
  | guarded_rinP : forall A b (c : chan A b) P,
      guarded (c & nilC) (c ??* P)
  | guarded_parP : forall P Q lp lq,
      guarded lp P -> guarded lq Q -> guarded (lq ^^ lp) (parP P Q).

Definition Guarded P := exists l, guarded l P.

Fixpoint is_guarded (P : proc) (l : ChanList) {struct P} :
 optionT ChanList :=
  match P with
  | zeroP => SomeT _ l
  | inP _ _ c C => SomeT _ (c & l)
  | rinP _ _ c C => SomeT _ (c & l)
  | outP _ _ c v C => SomeT _ (c & l)
  | parP P Q =>
      let l2 := is_guarded P l in
      match l2 with
      | NoneT => NoneT _
      | SomeT l1 => is_guarded Q l1
      end
  | nuP _ C => NoneT _
  | nuPl _ C => NoneT _
  end.

Lemma is_guarded_deter_some :
 forall P L L',
 is_guarded P L = SomeT _ L' ->
 forall K, is_guarded P K <> NoneT _.
intro.
induction P.
intros.
intro.
simpl in H0.
discriminate H0.
intros.
intro.
simpl in H1.
discriminate H1.
intros.
intro.
simpl in H1.
discriminate H1.
intros.
intro.
simpl in H0.
discriminate H0.
intros.
intro.
simpl in H.
cut
 ((exists K : ChanList, is_guarded P1 L = SomeT _ K) \/
  is_guarded P1 L = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H1.
rewrite H2 in H.
simpl in H0.
cut
 ((exists M : ChanList, is_guarded P1 K = SomeT _ M) \/
  is_guarded P1 K = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H1.
rewrite H3 in H0.
generalize (IHP2 _ _ H x0); intro.
apply H1.
auto.
generalize (IHP1 _ _ H2 K); intro.
apply H3.
auto.
case (is_guarded P1 K).
intro; left; exists c; auto.
right; auto.
rewrite H1 in H.
discriminate H.
case (is_guarded P1 L).
intro; left; exists c; auto.
right; auto.
intros.
simpl in H0.
discriminate H0.
intros.
simpl in H0.
discriminate H0.
Qed.

Lemma is_guarded_deter_none :
 forall P L,
 is_guarded P L = NoneT _ -> forall K : ChanList, is_guarded P K = NoneT _.
intro.
induction P.
intros.
simpl in H.
discriminate H.
intros.
simpl in H0.
discriminate H0.
intros.
simpl in H0.
discriminate H0.
intros.
simpl in H.
discriminate H.
intros.
simpl in |- *.
cut
 ((exists M : ChanList, is_guarded P1 K = SomeT _ M) \/
  is_guarded P1 K = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H0.
rewrite H1.
simpl in H.
cut
 ((exists M : ChanList, is_guarded P1 L = SomeT _ M) \/
  is_guarded P1 L = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H0.
rewrite H2 in H.
apply IHP2 with (L := x0).
auto.
generalize (IHP1 _ H0 K); intro.
rewrite H1 in H2.
discriminate H2.
case (is_guarded P1 L).
intro; left; exists c.
auto.
right; auto.
rewrite H0.
auto.
case (is_guarded P1 K).
intro; left; exists c.
auto.
right; auto.
intros.
simpl in |- *.
auto.
intros.
simpl in |- *.
auto.
Qed.

Lemma guarded_shift :
 forall P L M,
 is_guarded P M = SomeT _ L ->
 forall K, is_guarded P nilC = SomeT _ K -> L = K ^^ M.
intro.
induction P.
intros.
simpl in H.
injection H; intro.
simpl in H0.
injection H0; intro.
rewrite <- H1; rewrite <- H2.
simpl in |- *; auto.
intros.
simpl in H0.
simpl in H1.
injection H0; intro.
injection H1; intro.
rewrite <- H2; rewrite <- H3.
simpl in |- *.
auto.
intros.
simpl in H0.
simpl in H1.
injection H0; intro.
injection H1; intro.
rewrite <- H2; rewrite <- H3.
simpl in |- *.
auto.
intros.
simpl in H0.
simpl in H.
injection H0; intro.
injection H; intro.
rewrite <- H2; rewrite <- H1.
simpl in |- *.
auto.
intros.
simpl in H.
simpl in H0.
cut
 ((exists K : ChanList, is_guarded P1 nilC = SomeT _ K) \/
  is_guarded P1 nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H1.
cut
 ((exists K : ChanList, is_guarded P1 M = SomeT _ K) \/
  is_guarded P1 M = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H1.
generalize (IHP1 _ _ H3 x H2); intro.
rewrite H2 in H0.
rewrite H3 in H.
cut
 ((exists K : ChanList, is_guarded P2 nilC = SomeT _ K) \/
  is_guarded P2 nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H4.
generalize (IHP2 _ _ H x1 H5); intro.
generalize (IHP2 _ _ H0 x1 H5); intro.
rewrite H4.
rewrite H6.
generalize (appC_assoc x1 x M); intro.
rewrite H7.
rewrite <- H1.
auto.
generalize (is_guarded_deter_none _ _ H4 x0); intro.
rewrite H in H5; discriminate H5.
case (is_guarded P2 nilC).
intro; left; exists c.
auto.
right; auto.
generalize (is_guarded_deter_none _ _ H1 nilC); intro.
rewrite H2 in H3; discriminate H3.
case (is_guarded P1 M).
intro; left; exists c.
auto.
right; auto.
rewrite H1 in H0.
discriminate H0.
case (is_guarded P1 nilC).
intro; left; exists c.
auto.
right; auto.
intros.
simpl in H1.
discriminate H1.
intros.
simpl in H0.
discriminate H0.
Qed.

Lemma is_guarded_decompose :
 forall P1 P2 L,
 is_guarded (parP P1 P2) nilC = SomeT ChanList L ->
 exists L1,
   (exists L2,
      L = L2 ^^ L1 /\
      is_guarded P1 nilC = SomeT _ L1 /\ is_guarded P2 nilC = SomeT _ L2).
intro.
induction P1
 as [| A b c p H| A b c p H| A b c a P1 IHP1| P0 IHP0 P2 IHP2| A p H| A p H].
intros.
simpl in H.
exists nilC; exists L.
rewrite <- (app_k_nil L).
simpl in |- *.
intuition.
intros.
simpl in H0.
cut
 ((exists L' : ChanList, is_guarded P2 nilC = SomeT _ L') \/
  is_guarded P2 nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H1.
generalize (guarded_shift _ _ H0 H2); intro.
exists (c & nilC).
exists x.
simpl.
auto.
generalize (is_guarded_deter_some _ _ H0 nilC); intro.
absurd (is_guarded P2 nilC = NoneT ChanList).
auto.
auto.
case (is_guarded P2 nilC).
intro; left; exists c0.
auto.
right; auto.
intros.
simpl in H0.
cut
 ((exists L' : ChanList, is_guarded P2 nilC = SomeT _ L') \/
  is_guarded P2 nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H1.
generalize (guarded_shift _ _ H0 H2); intro.
exists (c & nilC).
exists x.
simpl.
auto.
generalize (is_guarded_deter_some _ _ H0 nilC); intro.
absurd (is_guarded P2 nilC = NoneT ChanList).
auto.
auto.
case (is_guarded P2 nilC).
intro; left; exists c0.
auto.
right; auto.
intros.
simpl in H.
cut
 ((exists L' : ChanList, is_guarded P2 nilC = SomeT _ L') \/
  is_guarded P2 nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H0.
generalize (guarded_shift _ _ H H1); intro.
exists (c & nilC).
exists x.
simpl.
intuition.
generalize (is_guarded_deter_some _ _ H nilC); intro.
absurd (is_guarded P2 nilC = NoneT ChanList).
auto.
auto.
case (is_guarded P2 nilC).
intro; left; exists c0.
auto.
right; auto.
intros.
simpl in H.
cut
 ((exists L' : ChanList, is_guarded P0 nilC = SomeT _ L') \/
  is_guarded P0 nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H0.
rewrite H1 in H.
cut
 ((exists L' : ChanList, is_guarded P2 x = SomeT _ L') \/
  is_guarded P2 x = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H0.
rewrite H2 in H.
cut
 ((exists L' : ChanList, is_guarded (parP P0 P2) nilC = SomeT _ L') \/
  is_guarded (parP P0 P2) nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H0.
cut
 ((exists L' : ChanList, is_guarded P1 nilC = SomeT _ L') \/
  is_guarded P1 nilC = NoneT _).
intro X; elim X; [ clear X; intro | clear X; intro ].
inversion_clear H0.
generalize (guarded_shift _ _ H H4); intro.
exists x0.
exists x2.
simpl in |- *.
rewrite H1.
intuition.
generalize (is_guarded_deter_some _ _ H nilC H0); intro.
contradiction.
case (is_guarded P1 nilC).
intro; left; exists c.
auto.
right; auto.
simpl in H0.
rewrite H1 in H0.
rewrite H2 in H0; discriminate H0.
case (is_guarded (parP P0 P2) nilC).
intro; left; exists c.
auto.
right; auto.
rewrite H0 in H.
discriminate H.
case (is_guarded P2 x).
intro; left; exists c.
auto.
right; auto.
rewrite H0 in H.
discriminate H.
case (is_guarded P0 nilC).
intro; left; exists c.
auto.
right; auto.
intros.
simpl in H0.
discriminate H0.
intros.
simpl in H0.
discriminate H0.
Qed.

Lemma is_guarded_is_guarded :
 forall (P : proc) (l : ChanList),
 is_guarded P nilC = SomeT _ l -> guarded l P.
intros P.
induction P.
simpl.
intros.
injection H.
intro.
rewrite <- H0.
apply guarded_zeroP.
intros.
simpl in H0.
injection H0.
intros.
rewrite <- H1.
apply guarded_inP.
intros.
simpl in H0; injection H0; intros.
rewrite <- H1.
apply guarded_rinP.
intros.
simpl in H.
injection H.
intro X; rewrite <- X.
apply guarded_outP.
intros.
generalize (is_guarded_decompose _ _ H); intro X; inversion_clear X.
inversion_clear H0.
decompose [and] H1; clear H1.
rewrite H0.
apply guarded_parP.
apply IHP1.
auto.
apply IHP2.
auto.
intros.
simpl in H0.
discriminate H0.
intros.
simpl in H0.
discriminate H0.
Qed.

Lemma guarded_no_nuP :
 forall (P : proc) (l : ChanList),
 guarded l P ->
 ~
 (exists obs : proc,
    (exists A : Set,
       (exists C : chan A false -> proc, Cong P (parP obs (nuP C))))) /\
 ~
 (exists obs : proc,
    (exists A : Set,
       (exists C : chan A true -> proc, Cong P (parP obs (nuPl C))))).
intros.
induction H
 as [| A b c v P| A b c P| A b c P| P Q lp lq H IHguarded1 H1 IHguarded2].
split.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
generalize (cong_zero_zeros_only H0); intros.
inversion_clear H.
lapply H1.
intro.
inversion_clear H.
inversion_clear H4.
apply one_zero.

intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
generalize (cong_zero_zeros_only H0); intros.
inversion_clear H.
lapply H1.
intro.
inversion_clear H.
inversion_clear H4.
apply one_zero.

split.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
assert (Cong (c << v >> P) (parP (nuP x1) x)).
apply cong_tr with (parP x (nuP x1)).
auto.
ProcCong.
apply (Cong_outP_parP_nuP H).

intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
assert (Cong (c << v >> P) (parP (nuPl x1) x)).
apply cong_tr with (parP x (nuPl x1)).
auto.
ProcCong.
apply (Cong_outP_parP_nuPl H).

split.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
assert (Cong (c ?? P) (parP (nuP x1) x)).
apply cong_tr with (parP x (nuP x1)).
auto.
ProcCong.
apply (Cong_inP_parP_nuP H).

intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
assert (Cong (c ?? P) (parP (nuPl x1) x)).
apply cong_tr with (parP x (nuPl x1)).
auto.
ProcCong.
apply (Cong_inP_parP_nuPl H).

split.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
assert (Cong (c ??* P) (parP (nuP x1) x)).
apply cong_tr with (parP x (nuP x1)).
auto.
ProcCong.
apply (Cong_rinP_parP_nuP H).

intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
assert (Cong (c ??* P) (parP (nuPl x1) x)).
apply cong_tr with (parP x (nuPl x1)).
auto.
ProcCong.
apply (Cong_rinP_parP_nuPl H).

split.
intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
generalize (cong_respects_trans_k H2); intro.
inversion_clear H0.
generalize (choose_fresh x0 nilC); intro.
inversion_clear H0.
lapply (H4 (NewL x2) (parP x (x1 x2))).
intro.
inversion_clear H0.
inversion_clear H6.
inversion_clear H0.
generalize (inv_trans_NewL_nuP H6); intros.
inversion_clear IHguarded1.
apply H8.
inversion_clear H0.
exists x4.
inversion_clear H10.
exists x0.
exists x5.
intuition.
generalize (inv_trans_NewL_nuP H6); intros.
inversion_clear IHguarded2.
apply H8.
inversion_clear H0.
exists x4.
inversion_clear H10.
exists x0.
exists x5.
intuition.
apply tr_parR.
apply tr_new.

intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
generalize (cong_respects_trans_k H2); intro.
inversion_clear H0.
generalize (choose_freshl x0 nilC); intro.
inversion_clear H0.
lapply (H4 (NewL x2) (parP x (x1 x2))).
intro.
inversion_clear H0.
inversion_clear H6.
inversion_clear H0.
generalize (inv_trans_NewL_nuPl H6); intros.
inversion_clear IHguarded1.
apply H9.
inversion_clear H0.
exists x4.
inversion_clear H10.
exists x0.
exists x5.
intuition.
generalize (inv_trans_NewL_nuPl H6); intros.
inversion_clear IHguarded2.
apply H9.
inversion_clear H0.
exists x4.
inversion_clear H10.
exists x0.
exists x5.
intuition.
apply tr_parR.
apply tr_newl.
Qed.

Lemma guarded_no_New :
 forall (P : proc) (l : ChanList),
 guarded l P ->
 forall (L K : ChanList) (P' : proc), Red (L # P) (K # P') -> L = K.
intros P l H.
induction H
 as [| A b c v P| A b c P| A b c P| P Q lp lq H IHguarded1 H1 IHguarded2].
intros.
inversion H.
inversion H0.
auto.
inversion H5.
intros.
inversion H.
inversion H0.
auto.
inversion H5.
intros.
inversion H.
inversion H0.
auto.
inversion H5.
intros.
inversion H.
inversion H0.
auto.
inversion H5.
intros.
inversion H0.
inversion H2.
auto.
inversion H7.
generalize (guarded_no_nuP H); intros.
inversion_clear H15.
induction b.
generalize (inv_trans_NewL_nuPl H14); intro.
assert
 (exists obs : proc,
    (exists A : Set,
       (exists C : chan A true -> proc, Cong P (parP obs (nuPl C))))).
inversion_clear H15.
inversion_clear H18.
exists x1; exists A; exists x2.
intuition.
generalize (H17 H18); contradiction.
generalize (inv_trans_NewL_nuP H14); intro.
assert
 (exists obs : proc,
    (exists A : Set,
       (exists C : chan A false -> proc, Cong P (parP obs (nuP C))))).
inversion_clear H15.
inversion_clear H18.
exists x1; exists A; exists x2.
intuition.
generalize (H16 H18); contradiction.
generalize (guarded_no_nuP H1); intros.
inversion_clear H15.
induction b.
generalize (inv_trans_NewL_nuPl H14); intro.
assert
 (exists obs : proc,
    (exists A : Set,
       (exists C : chan A true -> proc, Cong Q (parP obs (nuPl C))))).
inversion_clear H15.
inversion_clear H18.
exists x1; exists A; exists x2.
intuition.
generalize (H17 H18); contradiction.
generalize (inv_trans_NewL_nuP H14); intro.
assert
 (exists obs : proc,
    (exists A : Set,
       (exists C : chan A false -> proc, Cong Q (parP obs (nuP C))))).
inversion_clear H15.
inversion_clear H18.
exists x1; exists A; exists x2.
intuition.
generalize (H16 H18); contradiction.
Qed.

Lemma
  guarded_in :
    forall (P : proc) (l : ChanList),
    guarded l P ->
    forall (A : Set) (b : bool) (c : chan A b) (v : A) (Q : proc),
    Trans P (InL c v) Q -> in_ChanList c l.
intros P l gua.
induction gua.
intros.
inversion H.
intros.
inversion_clear H.
intros.
generalize (inv_trans_inP1 H); intro.
subst A0.
generalize (inv_trans_inP_bool H); intros.
subst b0.
generalize (inv_trans_inP_chan H); intros.
subst c0.
simpl.
auto.
intros.
generalize (inv_trans_rinP1 H); intro.
subst A0.
generalize (inv_trans_rinP_bool H); intros.
subst b0.
generalize (inv_trans_rinP_chan H); intros.
subst c0.
simpl.
auto.
intros.
inversion H.
clear H1 H2 H0 L P0 Q1.
generalize (IHgua1 _ _ _ _ _ H4); intro.
apply in_chanlist_weakeningL.
auto.
clear H1 H2 H0 L P0 Q1.
generalize (IHgua2 _ _ _ _ _ H4); intro.
apply in_chanlist_weakeningR.
auto.
Qed.

Lemma guarded_out :
 forall (P : proc) (l : ChanList),
 guarded l P ->
 forall (A : Set) (b : bool) (c : chan A b) (v : A) (Q : proc),
 Trans P (OutL c v) Q -> in_ChanList c l.
intros P l gua.
induction gua.
intros.
inversion H.
intros.
generalize (inv_trans_outP1 H); intros.
generalize c0 v0 H; clear c0 v0 H.
rewrite <- H0.
clear H0 A0; intros.
generalize (inv_trans_outP_bool H); intros.
generalize c0 H; clear c0 H; rewrite <- H0; clear H0 b0; intros.
generalize (inv_trans_outP_chan_val H); intros.
inversion_clear H0.
rewrite <- H1.
simpl in |- *.
auto.
intros.
inversion H.
intros.
inversion H.
intros.
inversion H.
clear H1 H2 H0 L P0 Q1.
generalize (IHgua1 _ _ _ _ _ H4); intro.
apply in_chanlist_weakeningL.
auto.
clear H1 H2 H0 L P0 Q1.
generalize (IHgua2 _ _ _ _ _ H4); intro.
apply in_chanlist_weakeningR.
auto.
Qed.

Lemma stable_weak :
 forall (P : proc) (L : ChanList),
 Stable (L # P) ->
 forall (A : Set) (b : bool) (c : chan A b), Stable (c & L # P).
intro.
induction P.
intros.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
inversion_clear H1.
inversion_clear H1.
intros.
unfold Stable in |- *.
intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
inversion H2.
inversion H2.

intros.
unfold Stable.
intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
inversion H2.
inversion H2.
intros.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
inversion H1.
inversion H1.
intros.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
generalize (inv_trans_tau H1); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
unfold Stable in H.
assert (exists Q : state, Red (L # parP P1 P2) Q).
exists (L # parP x4 x5).
unfold Red in |- *.
exists (epsilon x1).
apply red_com.
apply tr_comOI with (x := x1) (v := x6).
injection H2; intros.
rewrite H4; intuition.
injection H2; intros.
rewrite H0; intuition.
apply H; auto.
inversion_clear H0.
unfold Stable in H.
assert (exists Q : state, Red (L # parP P1 P2) Q).
exists (L # parP x4 x5).
unfold Red in |- *.
exists (epsilon x1).
apply red_com.
inversion_clear H3.
apply tr_comIO with (x := x1) (v := x6).
injection H2; intros.
rewrite H4; intuition.
injection H2; intros.
rewrite H3; intuition.
apply H; auto.
inversion_clear H3.
apply H.
exists (L # parP x4 P2).
red in |- *.
exists (epsilon x1).
apply red_com.
apply tr_parL.
injection H2; intros.
rewrite H4; intuition.
injection H2; intros.
apply H.
exists (L # parP P1 x5).
red in |- *.
exists (epsilon x1).
apply red_com.
apply tr_parR.
rewrite H3; intuition.
inversion H1.
apply H.
exists (x1 & L # parP P' P2).
exists (New x1).
apply red_new.
apply tr_parL.
auto.
red in H2.
red in |- *.
intros.
apply H2.
simpl in |- *.
auto.
apply H.
exists (x1 & L # parP P1 P').
exists (New x1).
apply red_new.
apply tr_parR.
auto.
red in |- *.
intros.
red in H2.
apply H2.
simpl in |- *; auto.
intros.
generalize (choose_fresh A L).
intros.
inversion_clear H1.
red in |- *.
intro.
apply H0.
exists (x & L # p x).
exists (New x).
apply red_new.
tr_nu.
auto.
intros.
generalize (choose_freshl A L).
intros.
inversion_clear H1.
red in |- *.
intro.
apply H0.
exists (x & L # p x).
exists (New x).
apply red_new.
tr_nu.
auto.
Qed.

Lemma stable_weak_lst :
 forall (P : proc) (L : ChanList),
 Stable (L # P) -> forall K : ChanList, Stable (K ^^ L # P).
intros.
induction K.
simpl in |- *.
auto.
simpl in |- *.
apply stable_weak.
auto.
Qed.

(** a process that is guarded by a list of channels in which there is no pair of identical channels is stable *)

Lemma guarded_set_stable :
 forall (l : ChanList) (P : proc),
 guarded l P -> ChanList_is_set l -> Stable (l # P).
intros l P gua.
induction gua.
intro.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
inversion_clear H1.
inversion_clear H1.
intro.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
inversion H1.
inversion H1.
intro.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
inversion H1.
inversion H1.
intro.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
inversion H1.
inversion H1.
intro.
unfold Stable in |- *.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
generalize (inv_trans_tau H1); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
inversion_clear H3.
injection H2; intros.
rewrite <- H5 in H0.
rewrite <- H3 in H4.
elim H4; clear H4; intros H4 HH4.
generalize (guarded_in  gua2  H4); intro.
generalize (guarded_out gua1  H0); intro.
generalize (same_element_twice _ _ _ _ _ (conj H6 H7)); intro.
apply H8; auto.
inversion_clear H0.
inversion_clear H3.
injection H2; intros.
rewrite <- H3 in H0.
rewrite <- H4 in H0.
decompose [and] H0; clear H0.
generalize (guarded_out gua2 H5); intro.
generalize (guarded_in gua1 H7); intro.
generalize (same_element_twice _ _ _ _ _ (conj H0 H6)); intro.
auto.
inversion_clear H3.
inversion_clear H0.
generalize (chanlist_is_set_projR _ _ H); intro.
generalize (IHgua1 H0); intros.
unfold Stable in H5.
apply H5.
exists (lp # x4).
exists (epsilon x1).
apply red_com.
injection H2; intros.
rewrite H7; intuition.
generalize (chanlist_is_set_projL _ _ H); intro.
inversion_clear H0.
generalize (IHgua2 H3); intro.
unfold Stable in H0.
apply H0.
exists (lq # x5).
exists (epsilon x1).
apply red_com.
injection H2; intros.
rewrite H6; auto.
inversion H1.
clear H0 H4 P0 Q1 H3 L.
generalize (chanlist_is_set_projR _ _ H); intro.
generalize (IHgua1 H0); intro.
apply H3.
exists (x1 & lp # P').
exists (New x1).
apply red_new.
auto.
apply (fresh_projR _ _ _ _ _ H2).
clear H0 H4 Q1 P0 H3 L.
generalize (chanlist_is_set_projL _ _ H); intro.
generalize (IHgua2 H0); intro.
apply H3.
exists (x1 & lq # P').
exists (New x1).
apply red_new.
auto.
apply (fresh_projL _ _ _ _ _ H2).
Qed.

Lemma permutC_stable :
 forall (P : proc) (L : ChanList),
 Stable (L # P) -> forall K : ChanList, permutC L K -> Stable (K # P).
intros P L H.
intros.
induction H0
 as
  [l|
   A a' a l0 l1 H0 IHpermutC|
   A a' a l|
   l0 l1 l2 H0 IHpermutC1 H1 IHpermutC2].
auto.
red in |- *.
intro.
inversion_clear H1.
inversion_clear H2.
inversion_clear H1.
red in H.
apply H.
exists (a & l0 # Q).
exists (epsilon x1).
apply red_com.
auto.
red in H.
apply H.
exists (x1 & a & l0 # Q).
exists (New x1).
apply red_new.
auto.
red in H3.
red in |- *.
intros.
apply H3.
apply in_chanlist_permutC with (a & l0).
apply permutC_cons.
auto.
auto.
red in |- *.
intro.
inversion_clear H0.
red in H.
apply H.
inversion_clear H1.
inversion_clear H0.
exists (a & l # Q).
exists (epsilon x1).
apply red_com.
auto.
exists (x1 & a & l # Q).
exists (New x1).
apply red_new.
auto.
red in |- *.
intros.
red in H2.
apply H2.
simpl in H0.
inversion_clear H0.
generalize (in_chanlist_app_com l (a & nilC) _ _ d); intro.
inversion_clear H0.
apply H5.
simpl in |- *.
left.
apply eqdep_trans with (y := a).
auto.
auto.
generalize (in_chanlist_app_com l (a & nilC) _ _ d); intro.
inversion_clear H0.
apply H5.
simpl in |- *.
auto.
apply IHpermutC2.
apply IHpermutC1.
auto.
Qed.

Lemma guarded_set_stable_weak :
 forall (l : ChanList) (P : proc),
 guarded l P ->
 ChanList_is_set l ->
 forall l' : ChanList, ChanList_is_set l' -> incC l l' -> Stable (l' # P).
intros.
generalize (set_inclusion _ _ H0 H1 H2); intro.
inversion_clear H3.
generalize (guarded_set_stable H H0); intro.
assert (Stable (x ^^ l # P)).
apply stable_weak_lst.
auto.
apply permutC_stable with (x ^^ l).
auto.
apply permutC_sym.
apply permutC_trans with (l ^^ x).
auto.
apply permutC_app_com.
Qed.

Lemma stable_outP_dup :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b) 
   (v w : A) (P Q R : proc),
 Stable (L # parP (c << v >> P) R) ->
 Stable (L # parP (parP (c << v >> P) (c << w >> Q)) R).
intros.
red in |- *.
intro.
red in H.
apply H.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
generalize (inv_trans_tau H1); intro.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
inversion_clear H3.
inversion_clear H0.
decompose [and] H3; clear H3.
injection H2.
intros.
rewrite <- H4 in H0.
inversion H0.
exists (L # parP P x5).
exists (epsilon x1).
apply red_com.
generalize (inv_trans_outP1 H11); intros.
generalize x1 x6 H1 H0 H5 H8 H11; clear x1 x6 H1 H0 H5 H8 H11.
rewrite <- H12; clear H12 A0.
intros.
generalize (inv_trans_outP_bool H11); intros.
generalize x1 x6 H1 H0 H5 H8 H11; clear x1 x6 H1 H0 H5 H8 H11.
rewrite <- H12; clear H12 b0.
intros.
generalize (inv_trans_outP_chan_val H11); intros.
inversion_clear H12.
generalize H1 H0 H5 H8 H11; clear H1 H0 H5 H8 H11.
rewrite <- H13.
rewrite <- H14.
clear H13 H14.
intros.
generalize (inv_trans_outP_cont H11); intros.
eapply tr_comOI.
rewrite H12 in H11.
apply H11.
rewrite H3; auto.
generalize (inv_trans_outP1 H11); intros.
generalize x1 x6 H1 H0 H5 H8 H11; clear x1 x6 H1 H0 H5 H8 H11.
rewrite <- H12; clear H12 A0.
intros.
generalize (inv_trans_outP_bool H11); intros.
generalize x1 x6 H1 H0 H5 H8 H11; clear x1 x6 H1 H0 H5 H8 H11.
rewrite <- H12; clear H12 b0.
intros.
generalize (inv_trans_outP_chan_val H11); intros.
inversion_clear H12.
generalize H1 H0 H5 H8 H11; clear H1 H0 H5 H8 H11.
rewrite <- H13.
rewrite <- H14.
clear H13 H14.
intros.
generalize (inv_trans_outP_cont H11); intros.
assert (exists KQ : state, Red (L # parP (c << v >> P) R) KQ).
generalize (trans_InL_some_any H5 v); intros.
inversion_clear H13.
exists (L # parP P x7).
exists (epsilon c).
apply red_com.
eapply tr_comOI.
apply tr_out.
rewrite H3.
apply H14.
absurd (exists KQ : state, Red (L # parP (c << v >> P) R) KQ).
auto.
auto.
inversion_clear H0.
inversion_clear H3.
decompose [and] H0; clear H0.
injection H2; intros.
rewrite <- H4 in H5.
inversion_clear H5.
inversion H7.
inversion H7.
inversion_clear H3.
inversion_clear H0.
injection H2; intros.
rewrite <- H5 in H3.
generalize (inv_trans_tau H3); intro.
inversion_clear H6.
inversion_clear H7.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
inversion_clear H8.
inversion_clear H6.
decompose [and] H8.
injection H7; intros.
rewrite <- H9 in H10.
inversion H10.
inversion_clear H6.
inversion_clear H8.
decompose [and] H6; clear H6.
injection H7; intros.
rewrite <- H9 in H10.
inversion H10.
inversion_clear H8.
inversion_clear H6.
injection H7; intros.
rewrite <- H10 in H8.
inversion H8.
inversion_clear H6.
injection H7; intros.
rewrite <- H6 in H8.
inversion H8.
inversion_clear H0.
injection H2; intros.
exists (L # parP (c << v >> P) x5).
exists (epsilon x1).
apply red_com.
apply tr_parR.
rewrite H0.
auto.
inversion H1.
inversion H6.
inversion H11.
inversion H11.
exists (x1 & L # parP (c << v >> P) P').
exists (New x1).
apply red_new.
apply tr_parR.
auto.
auto.
Qed.

Axiom no_action_not_congruent_in :
    forall (P : state) (A : Set) (b : bool) (a : chan A b) 
      (w : A) (l : (*A is not tempty*)ChanList),
    guarded l (sndT P) ->
    ~ in_ChanList a l -> incC l (fstT P) -> ~ sat (INPUTS a ISANY) P.
(*Intros P A b a w l H.
NewInduction P.
Simpl in H.
NewInduction H.
Intros.
Intro.
Generalize (INPUTS_sat_inv H1); Intros.
Inversion_clear H2.
Inversion_clear H3.
Decompose [and] H2;Clear H2.
Generalize (cong_parP_zeroP ? ? (cong_sym ? ? H3)); Intros.
Inversion_clear H2.
Generalize (cong_zero_zeros_only ? ? H5); Intros.
Inversion_clear H2.
Cut (zeros_only (inP a x0)).
Intro.
Inversion_clear H2.
Apply H8.
Apply one_zero.
Intros.
Intro.
Generalize (INPUTS_sat_inv H1); Intros.
Inversion_clear H2.
Inversion_clear H3.
Decompose [and] H2;Clear H2.
Apply (Cong_outP_parP_inP ? ? ? ? ? ? ? ? w ? ? H3).
Intros.
Intro.
Generalize (INPUTS_sat_inv H1); Intros.
Inversion_clear H2.
Inversion_clear H3.
Decompose [and] H2;Clear H2.
Generalize (Cong_inP_parP_inP0 ? ? ? ? ? ? ? ? ? H3 w); Intro.
Generalize c P H H0 H1 H3; Clear c P H H0 H1 H3; Rewrite H2; Clear H2 A0; Intros.
Generalize (Cong_inP_parP_inP_bool ? ? ? ? ? ? ? ? H3 w); Intro.
Generalize c P H H0 H1 H3; Clear c P H H0 H1 H3; Rewrite H2; Clear H2 A0; Intros.
Generalize (Cong_inP_parP_inP_chan ? ? ? ? ? ? ? H3 w); Intro.
Generalize P H H0 H1 H3; Clear P H H0 H1 H3; Rewrite H2; Clear H2 c; Intros.
Apply H.
Simpl.
Auto.
Intros.
Intro.
Generalize (INPUTS_sat_inv H1); Intros.
Inversion_clear H2.
Inversion_clear H3.
Decompose [and] H2;Clear H2.
Generalize (Cong_rinP_parP_inP0 ? ? ? ? ? ? ? ? ? H3 w); Intro.
Generalize c P H H0 H1 H3; Clear c P H H0 H1 H3; Rewrite H2; Clear H2 A0; Intros.
Generalize (Cong_rinP_parP_inP_bool ? ? ? ? ? ? ? ? H3 w); Intro.
Generalize c P H H0 H1 H3; Clear c P H H0 H1 H3; Rewrite H2; Clear H2 A0; Intros.
Generalize (Cong_rinP_parP_inP_chan ? ? ? ? ? ? ? H3 w); Intro.
Generalize P H H0 H1 H3; Clear P H H0 H1 H3; Rewrite H2; Clear H2 c; Intros.
Apply H.
Simpl.
Auto.
Intros.
Simpl in H2.
Generalize (not_in_chanlist_appC lq lp ? ? a H0); Intro X; Inversion_clear X.
Generalize (incC_appC ? ? ? H2); Intro X; Inversion_clear X.
Generalize (IHguarded1 H4 H6); Intro.
Generalize (IHguarded2 H3 H5); Intro.
Apply (not_inputs_parP ? ? ? w ? ? ? (conj ? ? H7 H8)); Intro.
Qed.*)

Lemma no_action_not_congruent_out :
 forall (P : state) (A : Set) (b : bool) (a : chan A b) (l : ChanList),
 guarded l (sndT P) ->
 ~ in_ChanList a l ->
 incC l (fstT P) -> ~ (exists v : A, sat (OUTPUTS a v ISANY) P).
intros P A b a l H.
induction P.
simpl in H.
induction H
 as
  [| A0 b0 c v P| A0 b0 c P| A0 b0 c P| P Q lp lq H IHguarded1 H1 IHguarded2].
intros.
intro.
inversion_clear H1.
generalize (OUTPUTS_sat_inv H2); intros.
inversion_clear H1.
inversion_clear H3.
decompose [and] H1; clear H1.
generalize (cong_parP_zeroP (cong_sym H3)); intros.
inversion_clear H1.
generalize (cong_zero_zeros_only H5); intros.
inversion_clear H1.
cut (zeros_only (a << x >> x1)).
intro.
inversion_clear H1.
apply H8.
apply one_zero.
intros.
intro.
inversion_clear H1.
generalize (OUTPUTS_sat_inv H2); intros.
inversion_clear H1.
inversion_clear H3.
decompose [and] H1; clear H1.
generalize (Cong_outP_parP_outP0 H3); intro.
generalize c v H H0 H2 H3; clear c v H H0 H2 H3; rewrite H1; clear H1 A0;
 intros.
generalize (Cong_outP_parP_outP_bool H3); intro.
generalize c v H H0 H2 H3; clear c v H H0 H2 H3; rewrite H1; clear H1 b0;
 intros.
generalize (Cong_outP_parP_outP_chan_val H3); intro.
inversion_clear H1.
generalize H H0 H3 H2; clear H H0 H3 H2; rewrite H5; rewrite H6;
 clear H5 H6 c v; intros.
apply H.
simpl in |- *.
auto.
intros.
intro.
inversion_clear H1.
generalize (OUTPUTS_sat_inv H2); intros.
inversion_clear H1.
inversion_clear H3.
decompose [and] H1; clear H1.
apply (Cong_inP_parP_outP H3).
intros.
intro.
inversion_clear H1.
generalize (OUTPUTS_sat_inv H2); intros.
inversion_clear H1.
inversion_clear H3.
decompose [and] H1; clear H1.
apply (Cong_rinP_parP_outP H3).
intros.
simpl in H2.
generalize (not_in_chanlist_appC lq lp _ _ a H0); intro X; inversion_clear X.
generalize (incC_appC _ _ _ H2); intro X; inversion_clear X.
generalize (IHguarded1 H4 H6); intro.
generalize (IHguarded2 H3 H5); intro.
apply (not_outputs_parP (conj H7 H8)); intro.
Qed.

Lemma cong_respects_stable :
 forall P, 
   Stable P -> forall Q, Cong_st P Q -> Stable Q.
intros.
red in |- *.
intro.
inversion_clear H1.
generalize (cong_respects_red H2 (Cong_st_sym H0)).
intro X; inversion_clear X.
decompose [and] H1; clear H1.
red in H.
apply H.
exists x0; auto.
Qed.

Lemma now_is_ALWAYS : forall f P, tsat f P -> Stable P -> tsat (ALWAYS f) P.
intros.
unfold ALWAYS in |- *.
apply NEGT_sat.
intro.
generalize (MAYEV_sat_inv H1); intro.
inversion_clear H2.
inversion_clear H3.
generalize (NEGT_sat_inv H4); intro.
inversion H2.
rewrite H6 in H.
apply H3; auto.
clear H7 H8 R P0.
red in H0.
apply H0.
exists Q; auto.
Qed.

Unset Implicit Arguments.