Require Import chan.
Require Import chanlist.
Require Import applpi.

 Lemma fresh_projR :
 forall (A : Set) (b : bool) (a : chan A b) (L K : ChanList),
 fresh a (L ^^ K) -> fresh a K.
intros.
red in |- *.
intros.
red in H.
apply H.
apply in_chanlist_weakeningL.
auto.
Qed.

Lemma fresh_projL :
 forall (A : Set) (b : bool) (a : chan A b) (L K : ChanList),
 fresh a (L ^^ K) -> fresh a L.
intros.
red in |- *; intros.
red in H; apply H.
apply in_chanlist_weakeningR.
auto.
Qed.

Lemma fresh_isnot_in_ChanList :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 fresh c L -> ~ in_ChanList c L.
intros.
intro.
red in H.
generalize (H _ _ _ H0); intros.
apply H1; auto.
Qed.

Lemma isnot_in_ChanList_fresh :
 forall (L : ChanList) (A : Set) (b : bool) (c : chan A b),
 ~ in_ChanList c L -> fresh c L.
intros.
red in |- *.
intros.
intro.
apply H.
assert (d &&& c).
auto.
elim H2.
auto.
Qed.

Lemma incC_fresh :
 forall (A : Set) (b : bool) (c : chan A b) (L : ChanList),
 fresh c L -> forall L' : ChanList, incC L' L -> fresh c L'.
intros.
red in H.
red in |- *.
intros.
apply H.
apply H0.
auto.
Qed.
