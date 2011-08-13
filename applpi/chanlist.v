Require Import eqdep.
Require Import chan.
Require Import Classical.

 Set Implicit Arguments.
Unset Strict Implicit.

Inductive ChanList : Type :=
  | nilC : ChanList
  | consC : forall (A : Set) (b : bool), chan A b -> ChanList -> ChanList.

Fixpoint in_ChanList (A : Set) (b : bool) (c : chan A b)
 (l : ChanList) {struct l} : Prop :=
  match l with
  | nilC => False
  | consC B b' d tl => c &&& d \/ in_ChanList c tl
  end.

Fixpoint appC (l m : ChanList) {struct l} : ChanList :=
  match l with
  | nilC => m
  | consC _ _ a l1 => consC a (appC l1 m)
  end.

Lemma appC_assoc :
 forall L K M : ChanList, appC (appC L K) M = appC L (appC K M).
intros.
elim L.
simpl in |- *.
auto.
intros.
simpl in |- *.
rewrite H.
auto.
Qed.

Set Strict Implicit.
Unset Implicit Arguments.

Notation "l ^^ m" := (appC l m) (at level 35, right associativity).

Notation "c & l" := (consC c l) (at level 35, right associativity).

Lemma consC_sm_fp :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 L = c & L -> False.
intro.
induction L.
intros.
discriminate H.
intros.
apply (IHL A b c).
change
  match c0 & c & L with
  | consC AA bb cc LL => L = LL
  | _ => L = c & L
  end in |- *.
rewrite <- H.
auto.
Qed.

Lemma eqdep_consC :
 forall (A B : Set) (a' b' : bool) (a : chan A a') (b : chan B b'),
 a &&& b -> forall L : ChanList, a & L = b & L.
intros.
elim H.
auto.
Qed.

Fixpoint lengthC (l : ChanList) : nat :=
  match l with
  | nilC => 0
  | (consC _ _ _ m) => S (lengthC m)
  end.

Lemma app_k_nil : forall K : ChanList, K = K ^^ nilC.
intro K.
induction K.
simpl in |- *; auto.
simpl in |- *.
rewrite <- IHK.
auto.
Qed.

Lemma in_chanlist_app_com :
 forall (L K : ChanList) (A : Set) (b : bool) (a : chan A b),
 in_ChanList a (L ^^ K) <-> in_ChanList a (K ^^ L).
intro.
induction L.
(* base case *)
simpl in |- *.
intro K; rewrite <- (app_k_nil K).
tauto.
intro.
induction K.
simpl in |- *.
rewrite <- (app_k_nil L).
tauto.
(* inductive case *)
intros.
split.
(* first part of the split *)
intro.
simpl in H.
elim H; [ clear H; intro | clear H; intro ].
simpl in |- *.
right.
generalize (IHK A1 b1 a); intro X; elim X; clear X; intros.
clear H1.
apply H0.
simpl in |- *.
auto.
generalize (IHL (c0 & K) A1 b1 a); intro.
elim H0; clear H0; intros.
clear H1; generalize (H0 H); clear H0; intro.
simpl in H0.
elim H0; [ clear H0; intro | clear H0; intro ].
simpl in |- *.
auto.
simpl in |- *.
right.
generalize (IHK A1 b1 a); intro X; elim X; clear X; intros.
clear H2.
apply H1.
simpl in |- *.
right.
generalize (IHL K A1 b1 a); intro X; elim X; clear X; intros.
apply H3.
auto.
(* second part of the split *)
intro.
simpl in H.
elim H; [ clear H; intro | clear H; intro ].
simpl in |- *.
right.
generalize (IHL (c0 & K) A1 b1 a); intro X; elim X; clear X; intros.
clear H0.
apply H1.
simpl in |- *.
auto.
generalize (IHK A1 b1 a); intro X; elim X; clear X; intros.
clear H0.
generalize (H1 H).
intro.
simpl in H0.
elim H0; [ clear H0; intro | clear H0; intro ].
simpl in |- *.
auto.
simpl in |- *.
right.
generalize (IHL (c0 & K) A1 b1 a); intro X; elim X; clear X; intros.
clear H2; apply H3.
simpl in |- *.
right.
generalize (IHL K A1 b1 a); intro.
elim H2; intros.
apply H4.
auto.
Qed.

Lemma in_chanlist_weakeningL :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 in_ChanList c L -> forall K : ChanList, in_ChanList c (K ^^ L).
intro.
induction L.
intros.
simpl in H.
contradiction.
intros.
simpl in H.
inversion_clear H.
generalize (in_chanlist_app_com K (c & L) _ _ c0); intro X; elim X; clear X;
 intros.
apply H1.
simpl in |- *.
auto.
generalize (in_chanlist_app_com K (c & L) _ _ c0); intro X; elim X; clear X;
 intros.
apply H1.
simpl in |- *.
right.
generalize (IHL _ _ c0 H0 K); intro.
generalize (in_chanlist_app_com K L _ _ c0); intro X; elim X; clear X; intros.
apply H3.
auto.
Qed.

Lemma in_chanlist_weakeningR :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 in_ChanList c L -> forall K : ChanList, in_ChanList c (L ^^ K).
intro.
induction L.
intros.
simpl in H.
contradiction.
intros.
simpl in |- *.
simpl in H.
inversion_clear H.
auto.
right.
apply IHL.
auto.
Qed.

Lemma in_chanlist_app_or :
 forall (A : Set) (b : bool) (c : chan A b) (K L : ChanList),
 in_ChanList c (K ^^ L) -> in_ChanList c K \/ in_ChanList c L.
intros.
induction K; induction L.
simpl in H; contradiction.
right.
simpl in H; auto.
left.
rewrite <- (app_k_nil (c0 & K)) in H.
auto.
simpl in H.
inversion_clear H.
left; simpl in |- *; auto.
generalize (IHK H0); intro.
inversion_clear H.
left; simpl in |- *; auto.
auto.
Qed.

Lemma in_ChanList_eqdep :
 forall (A : Set) (b : bool) (c : chan A b) (A' : Set)
   (b' : bool) (c' : chan A' b'),
 c &&& c' -> forall l : ChanList, in_ChanList c l -> in_ChanList c' l.
intros.
induction l.
simpl in H0.
contradiction.
simpl in H0.
inversion_clear H0.
simpl in |- *.
left.
apply eqdep_trans with (y := c).
auto.
auto.
generalize (IHl H1); intros.
simpl in |- *.
auto.
Qed.

Lemma decompose_list :
 forall (K : ChanList) (A : Set) (b : bool) (c : chan A b),
 in_ChanList c K ->
 exists K0 : ChanList, (exists K1 : ChanList, K = K0 ^^ c & K1).
intro.
induction K.
intros.
simpl in H; contradiction.
intros.
simpl in H.
inversion_clear H.
exists nilC.
simpl in |- *.
exists K.
elim H0.
auto.
generalize (IHK A0 b0 c0 H0); intro.
inversion_clear H.
inversion_clear H1.
exists (c & x).
simpl in |- *.
exists x0.
elim H.
auto.
Qed.

(***
   * inclusion
   ***)

Definition incC (L' L : ChanList) : Prop :=
  forall (A : Set) (b : bool) (c : chan A b),
  in_ChanList c L' -> in_ChanList c L.

Lemma incC_sym : forall L : ChanList, incC L L.
intros.
red in |- *.
auto.
Qed.

Lemma incC_trans : forall L K M : ChanList, incC L K -> incC K M -> incC L M.
intros.
unfold incC in H.
unfold incC in H0.
unfold incC in |- *.
intros.
apply H0.
apply H.
auto.
Qed.

Lemma incC_appC :
 forall L K M : ChanList, incC (L ^^ K) M -> incC L M /\ incC K M.
intros.
split.
red in |- *.
intros.
red in H.
apply H.
apply in_chanlist_weakeningR; auto.
red in |- *.
intros.
red in H.
apply H.
apply in_chanlist_weakeningL; auto.
Qed.

Lemma incC_weak :
 forall L K : ChanList,
 incC L K -> forall (A : Set) (b : bool) (c : chan A b), incC (c & L) (c & K).
intros.
red in |- *.
intros.
simpl in |- *.
simpl in H0.
inversion_clear H0.
auto.
red in H.
right.
apply H.
auto.
Qed.

Lemma incC_weak_not_in_ChanList :
 forall L K : ChanList,
 incC L K ->
 forall (A : Set) (b : bool) (c : chan A b),
 ~ in_ChanList c L -> incC L (c & K).
intros.
red in |- *.
intros.
simpl in |- *.
right.
red in H.
apply H.
auto.
Qed.

Lemma incC_sublist :
 forall L L' : ChanList,
 incC L' L ->
 forall (A : Set) (b : bool) (c : chan A b),
 in_ChanList c L -> incC (c & L') L.
intros.
red in |- *.
intros.
simpl in H1.
inversion_clear H1.
generalize L' H A b c H0 A0 b0 c0 H2; clear L' H A b c H0 A0 b0 c0 H2.
induction L.
intros.
simpl in H0; contradiction.
intros.
simpl in H0.
inversion_clear H0.
simpl in |- *.
left.
apply eqdep_trans with (y := c0).
auto.
auto.
simpl in |- *.
right.
apply IHL with (L' := L) (c := c0).
apply incC_sym.
auto.
auto.
generalize L' H A b c H0 A0 b0 c0 H2; clear L' H A b c H0 A0 b0 c0 H2.
induction L.
intros.
simpl in H0; contradiction.
intros.
simpl in H0.
inversion_clear H0.
red in H.
apply H.
auto.
red in H.
apply H.
auto.
Qed.

Lemma in_ChanList_incC :
 forall (A : Set) (b : bool) (c : chan A b) (K : ChanList),
 ~ in_ChanList c K ->
 forall L : ChanList, incC L K /\ incC K L -> ~ in_ChanList c L.
intros.
intro.
apply H.
inversion_clear H0.
red in H2.
apply H2.
auto.
Qed.

Lemma not_in_chanlist_appC :
 forall (L K : ChanList) (A : Set) (b : bool) (a : chan A b),
 ~ in_ChanList a (L ^^ K) -> ~ in_ChanList a L /\ ~ in_ChanList a K.
intro.
induction L.
simpl in |- *.
intros.
split.
intro.
contradiction.
auto.
intros.
split.
intro.
simpl in H0.
elim H0.
intro.
assert (in_ChanList a ((c & L) ^^ K)).
simpl in |- *.
auto.
absurd (in_ChanList a ((c & L) ^^ K)).
auto.
auto.
intro.
assert (in_ChanList a ((c & L) ^^ K)).
simpl in |- *.
right.
apply in_chanlist_weakeningR.
auto.
apply H.
auto.
intro.
apply H.
apply in_chanlist_weakeningL.
auto.
Qed.


Ltac CheckInChanList :=
  match goal with
  |  |- (in_ChanList ?X1 ?X2) => simpl in |- *; CheckInChanList
  |  |- (?X1 \/ ?X2) => first
  [ left; CheckInChanList | right; CheckInChanList ]
  |  |- (?X1 &&& ?X1) => apply eqdep_intro
  |  |- (?X1 &&& ?X2) => fail
  | _ => fail
  end.

Ltac CheckInc :=
  match goal with
  |  |- (incC ?X1 ?X1) => apply incC_sym
  |  |- (incC nilC ?X1) => red in |- *; simpl in |- *; contradiction
  |  |- (incC (?X1 & ?X2) (?X3 & ?X4)) =>
      apply incC_sublist; [ CheckInc | CheckInChanList ]
  |  |- (incC (?X1 & ?X2) ?X3) => fail
  end. (* case where the rhs is a variable *)

(***
   * permutations
   ***)

Inductive permutC : ChanList -> ChanList -> Prop :=
  | permutC_refl : forall l : ChanList, permutC l l
  | permutC_cons :
      forall (A : Set) (a' : bool) (a : chan A a') (l0 l1 : ChanList),
      permutC l0 l1 -> permutC (a & l0) (a & l1)
  | permutC_append :
      forall (A : Set) (a' : bool) (a : chan A a') (l : ChanList),
      permutC (a & l) (l ^^ a & nilC)
  | permutC_trans :
      forall l0 l1 l2 : ChanList,
      permutC l0 l1 -> permutC l1 l2 -> permutC l0 l2.

Lemma permutC_sym : forall L K : ChanList, permutC L K -> permutC K L.
intros.
induction H
 as
  [l| A a' a l0 l1 H IHpermutC| A a' a l| l0 l1 l2 H IHpermutC1 H1 IHpermutC2].
apply permutC_refl.
apply permutC_cons.
auto.
generalize A a' a; clear A a' a.
induction l.
intros.
simpl in |- *.
apply permutC_cons.
apply permutC_refl.
intros.
simpl in |- *.
assert (permutC (c & l ^^ a & nilC) (c & a & l)).
apply permutC_cons.
auto.
apply permutC_trans with (l1 := c & a & l).
auto.
apply permutC_trans with (l1 := a & l ^^ c & nilC).
apply permutC_append with (l := a & l) (a := c).
apply permutC_cons.
apply IHl.
apply permutC_trans with (l1 := l1).
auto.
auto.
Qed.

Lemma permutC_inv_head :
 forall (L : ChanList) (A B : Set) (a' b' : bool) (c : chan A a')
   (d : chan B b'), permutC (c & d & L) (d & c & L).
intros.
apply permutC_trans with (l1 := (c & L) ^^ d & nilC).
simpl in |- *.
apply permutC_cons.
apply permutC_append.
apply permutC_sym.
apply permutC_append with (l := c & L) (a := d).
Qed.

Lemma permutC_app_com : forall L K : ChanList, permutC (L ^^ K) (K ^^ L).
intro.
induction L.
intro.
simpl in |- *.
rewrite <- (app_k_nil K).
apply permutC_refl.
intro.
generalize (IHL (c & K)); intro.
simpl in |- *.
simpl in H.
apply permutC_trans with (l1 := c & K ^^ L).
apply permutC_cons.
apply IHL.
induction K.
simpl in |- *.
apply permutC_refl.
simpl in |- *.
apply permutC_trans with (l1 := c0 & c & K ^^ L).
apply permutC_inv_head.
apply permutC_cons.
apply IHK.
generalize (IHL (c & K)); intro.
simpl in H0.
auto.
Qed.

Lemma in_chanlist_permutC :
 forall L K : ChanList,
 permutC L K ->
 forall (A : Set) (b : bool) (c : chan A b),
 in_ChanList c L -> in_ChanList c K.
intros L K H.
induction H
 as
  [l| A a' a l0 l1 H IHpermutC| A a' a l| l0 l1 l2 H IHpermutC1 H1 IHpermutC2].
auto.
intros.
simpl in H0.
simpl in |- *.
inversion_clear H0.
auto.
right.
apply IHpermutC.
auto.
intros.
simpl in H.
inversion_clear H.
generalize (in_chanlist_app_com l (a & nilC) _ _ c); intro.
inversion_clear H.
apply H2.
simpl in |- *.
auto.
generalize (in_chanlist_app_com l (a & nilC) _ _ c); intro.
inversion_clear H.
apply H2.
simpl in |- *.
auto.
intros.
apply IHpermutC2.
apply IHpermutC1.
auto.
Qed.

Lemma incC_permutC :
 forall L L' : ChanList,
 incC L L' -> forall L'' : ChanList, permutC L' L'' -> incC L L''.
intro.
induction L.
intro.
induction L'.
intros.
red in |- *; intros.
simpl in H1; contradiction.
intros.
red in |- *; intros.
simpl in H1; contradiction.
intros.
assert (in_ChanList c L').
red in H.
apply H.
simpl in |- *; auto.
generalize (decompose_list _ _ _ _ H1); intro.
inversion_clear H2.
inversion_clear H3.
red in |- *.
intros.
simpl in H3.
inversion_clear H3.
generalize
 (in_ChanList_eqdep _ _ _ _ _ _ (eqdep_sym _ _ _ _ _ _ _ _ _ H4) _ H1);
 intro.
apply (in_chanlist_permutC _ _ H0 _ _ _ H3).
red in H.
simpl in H.
assert (c0 &&& c \/ in_ChanList c0 L).
auto.
generalize (H _ _ _ H3); intro.
generalize (in_chanlist_permutC _ _ H0 _ _ _ H5); intro.
auto.
Qed.

Lemma incC_permutC2 :
 forall (A : Set) (b : bool) (c : chan A b) (L' K : ChanList),
 incC (c & L') (c & K) ->
 forall L : ChanList, permutC L (c & L') -> incC L (c & K).
intros.
red in |- *.
intros.
red in H.
apply H.
apply in_chanlist_permutC with L.
auto.
auto.
Qed.

Lemma incC_weak_permutC :
 forall (A : Set) (b : bool) (c : chan A b) (L' K : ChanList),
 incC L' K -> forall L : ChanList, permutC L (c & L') -> incC L (c & K).
intros.
red in |- *.
intros.
simpl in |- *.
assert (in_ChanList c0 (c & L')).
apply in_chanlist_permutC with L.
auto.
auto.
simpl in H2.
inversion_clear H2.
auto.
right.
red in H.
apply H.
auto.
Qed.

Definition rotate (l : ChanList) : ChanList :=
  match l with
  | nilC => nilC
  | (consC _ _ a tl) => tl ^^ a & nilC
  end.

Lemma rotate_permutC : forall L : ChanList, permutC L (rotate L).
intros.
induction L.
simpl in |- *.
apply permutC_refl.
simpl in |- *.
apply permutC_append.
Qed.

Ltac Permut n :=
  match goal with
  |  |- (permutC ?X1 ?X1) => apply permutC_refl
  |  |- (permutC (?X1 & ?X2) (?X1 & ?X3)) =>
      let newn := eval compute in (lengthC X2) in
      (apply permutC_cons; Permut newn)
  |  |- (permutC (?X1 & ?X2) ?X3) =>
      match eval compute in n with
      | 1 => fail
      | _ =>
          let
          (*  | _ -> Let l0'='(?2^^(?1&nilC)) In*)
          l0' := constr:(X2 ^^ X1 & nilC) in
          (apply (permutC_trans (X1 & X2) l0' X3);
            [ apply permutC_append | compute in |- *; Permut (pred n) ])
      end
  end.

Ltac PermutProve :=
  match goal with
  |  |- (permutC ?X1 ?X2) =>
      match eval compute in (lengthC X1 = lengthC X2) with
      | (?X1 = ?X1) => Permut X1
      end
  end.


Ltac test_chan2 c d yes_cont no_cont :=
  match constr:(c &&& d) with
  | (?X1 &&& ?X1) => yes_cont
  | (?X1 &&& ?X2) => no_cont
  end.

Ltac del_one_elt lst elt germ :=
  match constr:lst with
  | nilC => germ
  | (?X1 & ?X2) =>
    let tmp := eval compute in (germ ^^ X2) in
      test_chan2 X1 elt tmp
       ltac:(del_one_elt X2 elt (germ ^^ X1 & nilC))
  end.

Ltac CheckIncWeak' v lhs elt :=
  match constr:v with
  | 0 => apply incC_weak_not_in_ChanList
  | _ =>
      let tmp := del_one_elt lhs elt nilC in
      let tmp' := eval compute in tmp in
      (apply incC_permutC2 with tmp'; [ apply incC_weak | PermutProve ])
  end.

Ltac belongs_to elt lst :=
  match constr:lst with
  | nilC => constr:0
  | (?X1 & ?X2) => test_chan2 X1 elt 1 ltac:(belongs_to elt X2)
  end.

Ltac CheckIncWeak :=
  match goal with
  |  |- (incC (?X1 & ?X2) (?X1 & ?X3)) => apply incC_weak
  |  |- (incC ?X1 (?X2 & ?X3)) =>
      let bel := belongs_to X2 X1 in
      CheckIncWeak' bel X1 X2
  end.

(** intersection *)

Definition inter (P P' M : ChanList) : Prop :=
  forall (A : Set) (b : bool) (c : chan A b),
  in_ChanList c P /\ in_ChanList c P' <-> in_ChanList c M.

Lemma inter_weak :
 forall (A : Set) (b : bool) (c : chan A b) (L K M : ChanList),
 inter L K M -> ~ in_ChanList c K -> inter (c & L) K M.
intros.
red in |- *.
intros.
split.
intros.
red in H.
simpl in H1.
inversion_clear H1.
inversion_clear H2.
assert (in_ChanList c K).
elim H1.
auto.
absurd (in_ChanList c K).
auto.
auto.
generalize (H _ _ c0); intro.
inversion_clear H2.
apply H4.
auto.
intros.
red in H.
generalize (H _ _ c0); intro.
inversion_clear H2.
generalize (H4 H1); intros.
inversion_clear H2.
split; auto.
simpl in |- *.
auto.
Qed.

Lemma inter_nilC' :
 forall (A : Set) (b : bool) (c : chan A b) (K M : ChanList),
 inter nilC K M -> M = nilC.
intros.
assert
 ((exists A : Set,
     (exists b : bool,
        (exists c : chan A b, (exists tl : ChanList, M = c & tl)))) \/
  M = nilC).
case M.
auto.
intros.
left.
exists A0; exists b0; exists c0; exists c1.
auto.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
inversion_clear H1.
inversion_clear H0.
assert (in_ChanList x1 M).
rewrite H1; simpl in |- *; auto.
generalize (H _ _ x1); intros.
inversion_clear H2.
generalize (H4 H0); intros.
inversion_clear H2.
simpl in H5.
contradiction.
auto.
Qed.

Lemma inter_nilC : forall K : ChanList, inter nilC K nilC.
intros.
induction K.
red in |- *.
intros.
split.
intros.
inversion_clear H.
simpl in H0; contradiction.
intro X; simpl in X; contradiction.
red in |- *.
intros.
split.
intros.
inversion_clear H.
auto.
intros.
simpl in H; contradiction.
Qed.

Lemma inter_nilC2 : forall K : ChanList, inter K nilC nilC.
intros.
induction K.
red in |- *.
intros.
split.
intros.
inversion_clear H.
simpl in H0; contradiction.
intro X; simpl in X; contradiction.
red in |- *.
intros.
split.
intros.
inversion_clear H.
auto.
intros.
simpl in H; contradiction.
Qed.

(** element deletion *)

Set Implicit Arguments.
Unset Strict Implicit.

Definition del (P : ChanList) (A' : Set) (b' : bool)
  (c' : chan A' b') (M : ChanList) : Prop :=
  forall (A : Set) (b : bool) (c : chan A b),
  in_ChanList c P /\ ~ c &&& c' <-> in_ChanList c M.

Set Strict Implicit.
Unset Implicit Arguments.

Lemma chanlist_del :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 exists K : ChanList, del L c K.
intro L; induction L.
intros.
exists nilC.
split; intro.
intuition.
intuition.
intros.
generalize (IHL _ _ c0); intro X; inversion_clear X.
red in H.
elim (classic (c &&& c0)); intro.
exists x.
split; intros.
generalize (H _ _ c1); intro X; inversion_clear X.
apply H2.
split; auto.
inversion_clear H1.
simpl in H4.
inversion_clear H4.
assert (c1 &&& c0).
apply eqdep_trans with (y := c).
auto.
auto.
generalize (H5 H4); intro X; inversion_clear X.
auto.
intuition.
generalize (H _ _ c1); intro X; inversion_clear X.
generalize (H3 H1); intro.
split.
simpl in |- *.
right; intuition.
intuition.
exists (c & x).
split; intros.
inversion_clear H1.
simpl in H2.
inversion_clear H2.
simpl in |- *; auto.
generalize (H _ _ c1); intro X; inversion_clear X.
simpl in |- *; right; apply H2.
auto.
simpl in H1.
inversion_clear H1.
split.
simpl in |- *; auto.
intro.
assert (c &&& c0).
apply eqdep_trans with (y := c1).
auto.
auto.
auto.
generalize (H _ _ c1); intro X; inversion_clear X.
generalize (H3 H2); intro.
split.
simpl in |- *; intuition.
intuition.
Qed.

Lemma del_weak :
 forall (P : ChanList) (A : Set) (b : bool) (c : chan A b),
 ~ in_ChanList c P -> del (c & P) c P.
intros.
red in |- *.
intros.
split.
intros.
inversion_clear H0.
simpl in H1.
inversion_clear H1.
absurd (c0 &&& c).
auto.
auto.
auto.
intros.
split.
simpl in |- *; auto.
intro.
apply H.
elim H1.
auto.
Qed.

Lemma permutC_del' :
 forall P Q : ChanList,
 permutC P Q ->
 forall (R : ChanList) (A : Set) (b : bool) (c : chan A b),
 del P c R <-> del Q c R.
intros.
induction H
 as
  [l|
   A0 a' a l0 l1 H IHpermutC|
   A0 a' a l|
   l0 l1 l2 H IHpermutC1 H1 IHpermutC2].
tauto.
split.
intros.
red in |- *.
intros.
split.
intros.
inversion_clear H1.
red in H0.
assert (in_ChanList c0 (a & l0)).
apply in_chanlist_permutC with (L := a & l1).
apply permutC_cons.
apply permutC_sym.
auto.
auto.
generalize (H0 _ _ c0); intros.
inversion_clear H4.
generalize (H5 (conj H1 H3)); intro.
auto.
intros.
red in H0.
generalize (H0 _ _ c0); intro.
inversion_clear H2.
generalize (H4 H1); intros.
inversion_clear H2.
simpl in H5.
inversion_clear H5.
simpl in |- *.
split; auto.
generalize (in_chanlist_permutC _ _ H _ _ _ H2); intro.
simpl in |- *.
auto.
intro.
red in H0.
red in |- *.
intros.
split.
intros.
inversion_clear H1.
simpl in H2.
inversion_clear H2.
assert (in_ChanList c0 (a & l1)).
simpl in |- *.
auto.
elim (H0 _ _ c0).
intros.
generalize (H4 (conj H2 H3)); intro.
auto.
generalize (in_chanlist_permutC _ _ H _ _ _ H1); intro.
elim (H0 _ _ c0); intros.
apply H4.
simpl in |- *.
auto.
intros.
elim (H0 _ _ c0); intros.
generalize (H3 H1); intro.
split.
inversion_clear H4.
simpl in H5; inversion_clear H5.
simpl in |- *; auto.
assert (in_ChanList c0 (a & l1)).
simpl in |- *.
auto.
generalize (H2 (conj H5 H6)); intro.
apply in_chanlist_permutC with (L := a & l1).
apply permutC_cons.
apply permutC_sym.
auto.
auto.
intuition.
split; intros.
red in H.
red in |- *; intro.
split; intros.
inversion_clear H0.
elim (H _ _ c0); intros.
apply H0.
split; auto.
elim (in_chanlist_app_com (a & nilC) l _ _ c0); auto.
elim (H _ _ c0); intros.
assert (in_ChanList c0 (a & l) /\ ~ c0 &&& c).
auto.
inversion_clear H3; split; auto.
elim (in_chanlist_app_com (a & nilC) l _ _ c0); intros.
auto.
red in |- *.
intros.
red in H.
split; intros.
inversion_clear H0.
elim (H _ _ c0); intros.
apply H0.
split; auto.
elim (in_chanlist_app_com (a & nilC) l _ _ c0); intros.
auto.
elim (H _ _ c0); intros.
assert (in_ChanList c0 (l ^^ a & nilC) /\ ~ c0 &&& c).
auto.
inversion_clear H3; split; auto.
elim (in_chanlist_app_com (a & nilC) l _ _ c0); auto.
split; intros.
tauto.
tauto.
Qed.

Lemma permutC_del :
 forall P Q : ChanList,
 permutC P Q ->
 forall (R : ChanList) (A : Set) (b : bool) (c : chan A b),
 del P c R -> del Q c R.
intros.
generalize (permutC_del' _ _ H R _ _ c); intros.
tauto.
Qed.

Ltac Del :=
  match goal with
  |  |- (del ?X1 ?X2 ?X3) =>
      let k := belongs_to X2 X1 in
      match constr:k with
      | 0 => fail
      | (S _) =>
          let subset := del_one_elt X1 X2 nilC in
          (apply permutC_del with (P := X2 & subset);
            [ simpl in |- *; PermutProve | simpl in |- *; apply del_weak ])
      end
  end.