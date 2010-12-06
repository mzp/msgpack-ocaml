Require Import Ascii.
Require Import ListUtil Object MultiByte SerializeSpec Prefix ProofUtil Pow.

Definition Soundness obj1 x : Prop := forall obj2,
  Serialized obj1 x ->
  Serialized obj2 x ->
  Valid obj1 ->
  Valid obj2 ->
  obj1 = obj2.

Ltac straightfoward :=
  intros;
  unfold Soundness;
  intros obj2 Hs1 Hs2 V1 V2;
  inversion Hs2;
  reflexivity.

Lemma  soundness_nil:
  Soundness Nil ["192"].
Proof.
straightfoward.
Qed.

Lemma soundness_true :
  Soundness (Bool true) ["195"].
Proof.
straightfoward.
Qed.

Lemma soundness_false :
  Soundness (Bool false) ["194"].
Proof.
straightfoward.
Qed.

Lemma soundness_pfixnum: forall x1 x2 x3 x4 x5 x6 x7,
  Soundness (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
            [Ascii x1 x2 x3 x4 x5 x6 x7 false].
Proof.
straightfoward.
Qed.

Lemma soundness_nfixnum: forall x1 x2 x3 x4 x5,
  Soundness (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
            [Ascii x1 x2 x3 x4 x5 true true true].
Proof.
straightfoward.
Qed.

Lemma soundness_uint8 : forall c,
  Soundness (Uint8 c) ("204"::list_of_ascii8 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
rewrite_for obj2.
auto.
Qed.

Lemma soundness_uint16 : forall c,
  Soundness (Uint16 c) ("205"::list_of_ascii16 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_uint32 : forall c,
  Soundness (Uint32 c) ("206"::list_of_ascii32 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_uint64 : forall c,
  Soundness (Uint64 c) ("207"::list_of_ascii64 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_int8 : forall c,
  Soundness (Int8 c) ("208"::list_of_ascii8 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_int16 : forall c,
  Soundness (Int16 c) ("209"::list_of_ascii16 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_int32 : forall c,
  Soundness (Int32 c) ("210"::list_of_ascii32 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_int64 : forall c,
  Soundness (Int64 c) ("211"::list_of_ascii64 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_float : forall c,
  Soundness (Float c) ("202"::list_of_ascii32 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_double : forall c,
  Soundness (Double c) ("203"::list_of_ascii64 c).
Proof.
intros.
unfold Soundness.
intros obj2 Hs1 Hs2 V1 V2.
inversion Hs2.
assert (c = c0); [| rewrite_for c ]; auto with ascii.
Qed.

Lemma soundness_fixraw : forall cs b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 b5 b6 b7 b8 = ascii8_of_nat (length cs) ->
  Soundness (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true)::cs).
Proof.
straightfoward.
Qed.

Lemma soundness_raw16: forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  Soundness (Raw16 cs) ("218"::s1::s2::cs).
Proof.
straightfoward.
Qed.

Lemma soundness_raw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
  Soundness (Raw32 cs) ("219"::s1::s2::s3::s4::cs).
Proof.
straightfoward.
Qed.

Lemma soundness_fixarray_nil :
  Soundness (FixArray []) ["144"].
Proof.
unfold Soundness.
intros.
inversion H0; auto.
apply ascii8_not_O in H10; [ contradiction |].
split; [ simpl; omega |].
rewrite_for obj2.
inversion H2.
transitivity (pow 4); [ assumption |].
apply pow_lt.
auto.
Qed.

Lemma soundness_array16_nil :
  Soundness (Array16 []) ["220"; "000"; "000"].
Proof.
unfold Soundness.
intros.
inversion H0; auto.
apply ascii16_not_O in H8; [ contradiction |].
split; [ simpl; omega |].
rewrite_for obj2.
inversion H2.
assumption.
Qed.

Lemma soundness_array32_nil:
  Soundness (Array32 []) ["221"; "000"; "000";"000"; "000"].
Proof.
unfold Soundness.
intros.
inversion H0; auto.
apply ascii32_not_O in H10; [ contradiction |].
split; [ simpl; omega |].
rewrite_for obj2.
inversion H2.
assumption.
Qed.

Lemma soundness_fixmap_nil:
  Soundness (FixMap []) ["128"].
Proof.
unfold Soundness.
intros.
inversion H0; auto.
apply ascii8_not_O in H10; [ contradiction |].
split; [ simpl; omega |].
rewrite_for obj2.
inversion H2.
transitivity (pow 4); [ assumption |].
apply pow_lt.
auto.
Qed.

Lemma soundness_map16_nil:
  Soundness (Map16 []) ["222"; "000"; "000"].
Proof.
unfold Soundness.
intros.
inversion H0; auto.
apply ascii16_not_O in H7; [ contradiction |].
split; [ simpl; omega |].
rewrite_for obj2.
inversion H2.
assumption.
Qed.

Lemma soundness_map32_nil:
  Soundness (Map32 []) ["223"; "000"; "000";"000"; "000"].
Proof.
unfold Soundness.
intros.
inversion H0; auto.
apply ascii32_not_O in H10; [ contradiction |].
split; [ simpl; omega |].
rewrite_for obj2.
inversion H2.
assumption.
Qed.

Lemma soundness_array16_cons: forall x xs t1 t2 s1 s2 y ys,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length (x :: xs)) ->
  Serialized x y ->
  (Serialized x y -> Soundness x y) ->
  Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  (Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
    Soundness (Array16 xs) ("220" :: t1 :: t2 :: ys)) ->
  Serialized (Array16 (x :: xs)) ("220" :: s1 :: s2 :: y ++ ys) ->
  Soundness (Array16 (x :: xs)) ("220" :: s1 :: s2 :: y ++ ys).
Proof.
Admitted.
(*intros.
generalize H1 H3; intros Hs1 Hs'1.
apply H2 in H1.
apply H4 in H3.
unfold Soundness in *.
intros.
inversion H6.
 rewrite <- H11, <- H12 in *.
 apply ascii16_not_O in H0.
  contradiction.

  split.
   apply length_lt_O.

   inversion H7.
   auto.

 rewrite <- H13 in *; clear H13.
 inversion H7.
 inversion H8.
 apply prefix in Hs1.
 apply prefix in Hs'1.
 unfold Prefix in *.

 generalize H15 H16; intros Hs2 Hs'2.
 apply (Hs1 _ _ ys ys0) in H15; auto.
 rewrite H15 in *; clear H15.
 apply H1 in Hs2; auto.
 rewrite Hs2.
 apply app_same in H11.
 rewrite H11 in *; clear H11.

 assert ((t0,t3) = (t1,t2)).
  rewrite H, H12.
  apply (varray16_inv2  _ x0 x); auto.
  rewrite <- H0, <- H14.
  reflexivity.

  inversion H11.
  rewrite H26, H27 in *.
  apply H3 in Hs'2; auto.
  inversion Hs'2.
  reflexivity.
Qed.*)
*)

Hint Resolve
  soundness_nil soundness_true soundness_false
  : soundness.

Lemma soundness_intro: forall obj x,
  (Serialized obj x -> Soundness obj x)->
  Soundness obj x.
Proof.
unfold Soundness.
intros.
apply H in H1; auto.
Qed.

Lemma soundness : forall obj1 x,
  Soundness obj1 x.
Proof.
intros.
apply soundness_intro.
intro.
pattern obj1,x.
apply Serialized_ind; intros; auto with soundness.
Admitted.
