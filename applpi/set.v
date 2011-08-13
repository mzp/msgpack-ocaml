Require Import eqdep.
Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import fresh.

 (***
   * sets
   ***)

Fixpoint fresh_func (A : Set) (aa : bool) (c : chan A aa)
 (L : ChanList) {struct L} : Prop :=
  match L with
  | nilC => True
  | consC B bb d tl => ~ c &&& d /\ fresh_func A aa c tl
  end.


Lemma fresh_pred2func :
 forall (A : Set) (aa : bool) (c : chan A aa) (L : ChanList),
 fresh c L -> fresh_func _ _ c L.
intros.
generalize A aa c H; clear A aa c H.
induction L.
intros.
simpl in |- *.
auto.
intros.
simpl in |- *.
split.
red in H.
apply H.
simpl in |- *; auto.
apply IHL.
red in H.
red in |- *; intros.
apply H.
simpl in |- *; auto.
Qed.

Lemma fresh_func2pred :
 forall (A : Set) (aa : bool) (c : chan A aa) (L : ChanList),
 fresh_func _ _ c L -> fresh c L.
intros.
generalize A aa c H; clear A aa c H.
induction L.
intros.
red in |- *; intros.
simpl in H0; contradiction.
intros.
red in |- *; intros.
simpl in H.
inversion_clear H.
simpl in H0.
inversion_clear H0.
intro.
apply H1.
apply eqdep_trans with (y := d).
auto.
auto.
generalize (IHL _ _ _ H2); intros.
red in H0.
apply H0.
auto.
Qed.

Lemma fresh_is_fresh :
 forall (A : Set) (b : bool) (c : chan A b) (l : ChanList),
 fresh_func A b c l -> ~ in_ChanList c l.
intros.
induction l.
intro.
simpl in H0.
auto.
simpl in H.
inversion_clear H.
generalize (IHl H1); intro.
intro.
simpl in H2.
inversion_clear H2.
apply H0; auto.
apply H; auto.
Qed.

Fixpoint ChanList_is_set (l : ChanList) : Prop :=
  match l with
  | nilC => True
  | consC B bb b tl => fresh_func B bb b tl /\ ChanList_is_set tl
  end.

Lemma chanlist_fresh :
 forall (lst : ChanList) (A : Set) (b : bool) (c : chan A b),
 ChanList_is_set (c & lst) -> fresh c lst.
intros.
simpl in H.
inversion_clear H.
apply fresh_func2pred.
auto.
Qed.

Lemma set_incC_isnot_in_chanlist :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 ChanList_is_set (c & L) ->
 forall K : ChanList, incC K L -> ~ in_ChanList c K.
intros.
intro.
red in H0.
generalize (H0 _ _ _ H1); intro.
simpl in H.
inversion_clear H.
generalize (fresh_func2pred _ _ _ _ H3); intro.
red in H.
generalize (H _ _ _ H2); intros.
auto.
Qed.

Lemma chanlist_is_set_extend :
 forall L : ChanList,
 ChanList_is_set L ->
 forall (A : Set) (b : bool) (c : chan A b),
 fresh c L -> ChanList_is_set (c & L).
intros.
simpl in |- *.
split.
apply fresh_pred2func.
auto.
auto.
Qed.

Lemma chanlist_is_set_incC_extend :
 forall L K : ChanList,
 ChanList_is_set L ->
 incC L K ->
 forall (A : Set) (b : bool) (c : chan A b),
 ChanList_is_set (c & K) -> ChanList_is_set (c & L).
intros.
simpl in |- *.
split; auto.
apply fresh_pred2func.
red in |- *; intros.
simpl in H1.
inversion_clear H1.
generalize (fresh_func2pred _ _ _ _ H3); intros.
red in H1; intro.
assert (in_ChanList d K).
red in H0.
apply H0.
auto.
generalize (H1 _ _ _ H6); auto.
Qed.

Lemma chanlist_is_app_com :
 forall L K : ChanList, ChanList_is_set (L ^^ K) <-> ChanList_is_set (K ^^ L).
intro.
induction L.
simpl in |- *; intro; rewrite <- (app_k_nil K); tauto.
intro.
generalize A b c; clear A b c.
induction K.
simpl in |- *.
rewrite <- (app_k_nil L).
tauto.
intros.
split; intro.
(* first split *)
simpl in |- *.
split.
simpl in H.
inversion_clear H.
generalize (fresh_func2pred _ _ _ _ H0); intro.
red in H.
apply fresh_pred2func.
red in |- *.
intros.
generalize (in_chanlist_app_com K (c0 & L) _ _ d); intro.
inversion_clear H3.
generalize (H4 H2); clear H4 H5; intros.
simpl in H3.
inversion_clear H3.
intro.
assert (in_ChanList c (L ^^ c & K)).
generalize (in_chanlist_app_com L (c & K) _ _ c); intro.
inversion_clear H5.
apply H7; clear H7 H6.
simpl in |- *.
auto.
generalize (H _ _ _ H5); intro.
apply H6.
apply eqdep_trans with (y := d).
auto.
auto.
generalize (IHL (c & K)); intro.
inversion_clear H3.
generalize (H5 H1); clear H5 H6; intro.
simpl in H3.
inversion_clear H3.
generalize (fresh_func2pred _ _ _ _ H5); intro.
red in H3.
apply H3.
generalize (in_chanlist_app_com K L _ _ d); intro.
inversion_clear H7.
apply H9.
auto.
generalize (IHK _ _ c0); intro.
inversion_clear H0.
apply H1.
simpl in |- *.
split.
clear H1 H2.
simpl in H.
inversion_clear H.
generalize (IHL (c & K)); intro.
inversion_clear H.
generalize (H2 H1); intro.
clear H2 H3.
simpl in H.
inversion_clear H.
generalize (fresh_func2pred _ _ _ _ H2); intro.
red in H.
apply fresh_pred2func.
red in |- *.
intros.
generalize (fresh_func2pred _ _ _ _ H0); intro.
red in H5.
apply H5.
generalize (in_chanlist_app_com L (c & K) _ _ d); intros.
inversion_clear H6.
apply H8; clear H8 H7.
simpl in |- *.
generalize (in_chanlist_app_com L K _ _ d); intro.
inversion_clear H6.
right.
apply H7.
auto.
simpl in H.
inversion_clear H.
generalize (IHL (c & K)); intro.
inversion_clear H.
generalize (H4 H3); intro.
simpl in H.
inversion_clear H.
generalize (IHL K); intro.
inversion_clear H.
apply H9.
auto.
(* second split *)
simpl in |- *.
split.
simpl in H.
inversion_clear H.
generalize (IHK _ _ c0); intro.
inversion_clear H.
generalize (H3 H1); clear H2 H3; intro.
simpl in H.
inversion_clear H.
generalize (fresh_func2pred _ _ _ _ H0); intro.
generalize (fresh_func2pred _ _ _ _ H2); intro.
red in H.
red in H4.
apply fresh_pred2func.
red in |- *.
intros.
generalize (in_chanlist_app_com L (c & K) _ _ d); intro.
inversion_clear H6.
generalize (H7 H5); intro.
clear H7 H8.
simpl in H6.
inversion_clear H6.
intro.
assert (in_ChanList c0 (K ^^ c0 & L)).
generalize (in_chanlist_app_com K (c0 & L) _ _ c0); intro.
inversion_clear H8.
apply H10.
simpl in |- *.
auto.
generalize (H _ _ _ H8); intro.
apply H9.
apply eqdep_trans with (y := d).
auto.
auto.
apply H4.
generalize (in_chanlist_app_com L K _ _ d); intro.
inversion_clear H6.
apply H9.
auto.
simpl in H.
inversion_clear H.
generalize (IHL (c & K)); intro.
inversion_clear H.
apply H3.
clear H2 H3.
simpl in |- *.
generalize (IHK _ _ c0); intro.
inversion_clear H.
generalize (H3 H1); clear H2 H3; intro.
simpl in H.
inversion_clear H.
generalize (IHL K); intro.
inversion_clear H.
generalize (H4 H3); clear H4 H5; intro.
split; auto.
apply fresh_pred2func.
red in |- *.
generalize (fresh_func2pred _ _ _ _ H0); intro.
generalize (fresh_func2pred _ _ _ _ H2); intro.
red in H5.
red in H4.
intros.
apply H4.
generalize (in_chanlist_app_com K (c0 & L) _ _ d); intro.
inversion_clear H7.
apply H9; clear H8 H9.
simpl in |- *.
right.
generalize (in_chanlist_app_com L K _ _ d); intro.
inversion_clear H7.
apply H9.
auto.
Qed.

Lemma chanlist_is_set_projL :
 forall L K : ChanList, ChanList_is_set (K ^^ L) -> ChanList_is_set K.
intro.
induction L.
intro; rewrite <- (app_k_nil K).
auto.
intros.
generalize (chanlist_is_app_com K (c & L)); intro X; elim X; clear X; intros.
generalize (H0 H); clear H0 H1; intro.
simpl in H0.
inversion_clear H0.
generalize (chanlist_is_app_com K L); intro X; elim X; clear X; intros.
generalize (H3 H2); intro.
apply IHL.
auto.
Qed.

Lemma chanlist_is_set_projR :
 forall L K : ChanList, ChanList_is_set (K ^^ L) -> ChanList_is_set L.
intros.
generalize (chanlist_is_app_com K L); intro X; elim X; clear X; intros.
generalize (H0 H); intro.
apply chanlist_is_set_projL with K.
auto.
Qed.

Lemma same_element_twice :
 forall (A : Set) (b : bool) (a : chan A b) (L K : ChanList),
 in_ChanList a L /\ in_ChanList a K -> ~ ChanList_is_set (L ^^ K).
intros A v a L.
induction L.
intro.
induction K.
intro.
inversion_clear H.
simpl in H0; contradiction.
intro.
inversion_clear H.
simpl in H0; contradiction.
(* inductive case *)
intros.
inversion_clear H.
simpl in H0.
inversion_clear H0.
intro.
simpl in H0.
inversion_clear H0.
generalize (fresh_func2pred _ _ _ _ H2); intro.
red in H0.
assert (in_ChanList a (L ^^ K)).
apply in_chanlist_weakeningL.
auto.
generalize (H0 _ _ _ H4); intro.
apply H5; auto.
intro.
simpl in H0.
inversion_clear H0.
generalize (IHL _ (conj H H1)).
tauto.
Qed.

Lemma set_inclusion2 :
 forall (l l' : ChanList) (A : Set) (b : bool) (c : chan A b),
 ChanList_is_set (c & l) ->
 ChanList_is_set (c & l') -> incC (c & l) (c & l') -> incC l l'.
intros.
red in |- *.
intros.
red in H1.
generalize (H1 _ _ c0); intros.
assert (in_ChanList c0 (c & l)).
simpl in |- *; auto.
generalize (H3 H4); intro.
simpl in H5.
inversion_clear H5.
simpl in H.
inversion_clear H.
generalize (fresh_is_fresh _ _ _ _ H5); intros.
generalize (in_ChanList_eqdep _ _ c0 _ _ c H6 _ H2); intro.
generalize (H H8); intro.
contradiction.
auto.
Qed.

Lemma permutC_set :
 forall L K : ChanList, permutC L K -> ChanList_is_set L -> ChanList_is_set K.
intros L K H.
induction H
 as
  [l| A a' a l0 l1 H IHpermutC| A a' a l| l0 l1 l2 H IHpermutC1 H1 IHpermutC2].
auto.
intro.
simpl in |- *.
simpl in H0.
inversion_clear H0.
split.
apply fresh_pred2func.
red in |- *; intros.
generalize (fresh_func2pred _ _ _ _ H1); intro.
red in H3.
apply H3.
apply (in_chanlist_permutC _ _ (permutC_sym _ _ H) _ _ _ H0).
apply IHpermutC.
auto.
intros.
simpl in H.
inversion_clear H.
generalize (chanlist_is_app_com l (a & nilC)); intro.
inversion_clear H.
apply H3.
simpl in |- *.
auto.
tauto.
Qed.

Lemma set_inclusion :
 forall l l' : ChanList,
 ChanList_is_set l ->
 ChanList_is_set l' ->
 incC l l' -> exists l'' : ChanList, permutC l' (l ^^ l'').
intro.
induction l.
intro.
induction l'.
intros.
exists nilC.
simpl in |- *.
apply permutC_refl.
intros.
assert (ChanList_is_set l' /\ incC nilC l').
split.
simpl in H0; intuition.
red in |- *; intros.
simpl in H2; contradiction.
inversion_clear H2.
generalize (IHl' H H3 H4); intros.
inversion_clear H2.
exists (c & l').
simpl in |- *.
apply permutC_refl.
intros.
assert (in_ChanList c l').
red in H1.
apply H1.
simpl in |- *.
auto.
generalize (decompose_list _ _ _ _ H2); intro.
inversion_clear H3.
inversion_clear H4.
assert (exists l''' : ChanList, permutC l' (c & l''')).
exists (x ^^ x0).
apply permutC_trans with (x ^^ c & x0).
rewrite <- H3; apply permutC_refl.
generalize (permutC_app_com (c & x0) x); intro.
apply permutC_trans with ((c & x0) ^^ x).
apply permutC_sym.
auto.
simpl in |- *.
apply permutC_cons.
apply permutC_app_com.
auto.
inversion_clear H4.
cut (incC (c & l) (c & x1)).
intro.
generalize (permutC_set _ _ H5 H0); intro.
generalize (set_inclusion2 _ _ _ _ _ H H6 H4); intro.
simpl in H6.
inversion_clear H6.
simpl in H.
inversion_clear H.
generalize (IHl _ H10 H9 H7); intro.
inversion_clear H.
exists x2.
apply permutC_trans with (c & x1).
auto.
simpl in |- *.
apply permutC_cons.
auto.
auto.
apply (incC_permutC _ _ H1 _ H5).
Qed.

Lemma chanlist_is_set_contract :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 ChanList_is_set (c & L) -> ChanList_is_set L.
intros.
simpl in H.
intuition.
Qed.

Lemma chanlist_is_set_rotate :
 forall L : ChanList, ChanList_is_set L -> ChanList_is_set (rotate L).
intros.
induction L.
simpl in |- *.
auto.
simpl in |- *.
simpl in H.
inversion_clear H.
generalize (chanlist_is_app_com L (c & nilC)); intro.
inversion_clear H.
apply H3.
simpl in |- *.
auto.
Qed.

Lemma chanlist_is_set_rotate' :
 forall L : ChanList, ChanList_is_set (rotate L) -> ChanList_is_set L.
intros.
induction L.
simpl in |- *.
auto.
simpl in |- *.
simpl in H.
generalize (chanlist_is_app_com L (c & nilC)); intro.
inversion_clear H0.
generalize (H1 H); intro.
simpl in H0.
auto.
Qed.

Lemma chanlist_is_set_rotate'' :
 forall L K : ChanList,
 (ChanList_is_set (rotate L) -> ChanList_is_set (rotate K)) ->
 ChanList_is_set L -> ChanList_is_set K.
intros.
apply chanlist_is_set_rotate'.
apply H.
apply chanlist_is_set_rotate.
auto.
Qed.

Lemma chanlist_is_set_rotate''' :
 forall L K : ChanList,
 (ChanList_is_set (rotate L) -> ChanList_is_set K) ->
 ChanList_is_set L -> ChanList_is_set K.
intros.
apply H.
apply chanlist_is_set_rotate.
auto.
Qed.

Lemma chanlist_is_set_contract' :
 forall (L K : ChanList) (A : Set) (b : bool) (c : chan A b),
 (ChanList_is_set L -> ChanList_is_set K) ->
 ChanList_is_set (c & L) -> ChanList_is_set K.
intros.
apply H.
simpl in H0.
intuition.
Qed.

Ltac CheckListSetDelRot' val :=
  match constr:val with
  | 0 =>  (* nuke the head *)
  apply chanlist_is_set_contract'
  | (S _) =>
       (* rotate the head *)
       apply chanlist_is_set_rotate''';
       cbv beta iota zeta delta [rotate appC] in |- *
  end.

Ltac CheckListSetDelRot :=
  match goal with
  |  |- (ChanList_is_set (?X1 & ?X2) -> ChanList_is_set (?X1 & ?X3)) =>
      apply chanlist_is_set_rotate'';
       cbv beta iota zeta delta [rotate appC] in |- *
  |  |- (ChanList_is_set (?X1 & ?X2) -> ChanList_is_set (?X3 & ?X4)) =>
      let bel := belongs_to X1 X4 in
      CheckListSetDelRot' bel
  end.

Ltac CheckListSetPermutC :=
  match goal with
  |  |- (ChanList_is_set ?X1 -> ChanList_is_set ?X2) =>
      apply permutC_set with (L := X1); PermutProve
  end.

Ltac CheckListSet :=
  match goal with
  |  |- (ChanList_is_set ?X1 -> ChanList_is_set ?X2) =>
      let l1 := eval compute in (lengthC X1) in
      let l2 := eval compute in (lengthC X2) in
      match eval compute in (l1 = l2) with
      | (?X3 = ?X3) => CheckListSetPermutC
      | _ => CheckListSetDelRot; CheckListSet
      end
  end.

(** tactics to check that a channel is not in a list given information about some set *)

Ltac CheckNotInChanList :=
  match goal with
  | id0:(ChanList_is_set (?X1 & ?X3)) |- (~ in_ChanList ?X1 ?X2) =>
      apply set_incC_isnot_in_chanlist with (L := X3); [ exact id0 | idtac ]
  end.

Ltac CheckNotInChanList2 id :=
  match goal with
  | id:(ChanList_is_set ?X3) |- (~ in_ChanList ?X1 ?X2) =>
      let k := belongs_to X1 X3 in
      match constr:k with
      | 0 => fail
      | (S _) =>
          let subset := del_one_elt X3 X1 nilC in
          (cut (ChanList_is_set (X1 & subset));
            [ intro _X; CheckNotInChanList; simpl in |- *; CheckInc
            | apply permutC_set with X3; [ PermutProve | exact id ] ])
      end
  end.

(** the list of channels created so far is a growing set *)

Lemma channels_created_so_far_is_growing_set :
 forall L : ChanList,
 ChanList_is_set L ->
 forall (P : proc) (P' : state),
 Reds (L # P) P' -> ChanList_is_set (fstT P') /\ incC L (fstT P').
intros.
apply
 invariant_by_red
  with
    (P := fun K : state => ChanList_is_set (fstT K) /\ incC L (fstT K))
    (p0 := L # P).
intros.
inversion_clear H1.
inversion H3.
rewrite <- H4 in H2.
simpl in |- *; simpl in H2; auto.
rewrite <- H5 in H2.
simpl in |- *; simpl in H2.
split; auto.
split; auto.
apply fresh_pred2func.
auto.
intuition.
apply incC_weak_not_in_ChanList.
intuition.
apply fresh_isnot_in_ChanList.
eapply incC_fresh.
apply H4.
intuition.
simpl in |- *.
split; auto.
apply incC_sym.
auto.
Qed.