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
unfold Soundness.
intros.
inversion H7.
 rewrite_for s1.
 rewrite_for s2.
 apply ascii16_not_O in H0; [ contradiction |].
 split; [ simpl; omega |].
 inversion H8.
 assumption.

 rewrite_for obj2.
 inversion H8.
 inversion H9.
 assert (y = y0).
  generalize prefix.
  unfold Prefix.
  intro Hprefix.
  apply (Hprefix x _ x0 _ ys ys0); auto.

  rewrite_for y0.
  apply H2 with (obj2:=x0) in H1; auto.
  apply app_same in H12.
  apply H4 with (obj2:=(Array16 xs0)) in H3; auto.
   inversion H3.
   rewrite H1.
   reflexivity.

   rewrite H15 in H0.
   simpl in H0.
   apply ascii16_of_nat_eq in H0; auto.
   inversion H0.
   rewrite <- H28 in H.
   rewrite <- H13 in H.
   inversion H.
   rewrite_for t0.
   rewrite_for t3.
   rewrite_for ys.
   assumption.
Qed.

Lemma soundness_array32_cons: forall x xs y ys s1 s2 s3 s4 t1 t2 t3 t4,
  ((t1,t2),(t3,t4)) = ascii32_of_nat (length xs) ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat (length (x::xs)) ->
  Serialized x y ->
  (Serialized x y -> Soundness x y) ->
  Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) ->
  (Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) -> Soundness (Array32 xs) ("221"::t1::t2::t3::t4::ys)) ->
  Serialized (Array32 (x::xs)) ("221"::s1::s2::s3::s4::y ++ ys) ->
  Soundness (Array32 (x::xs)) ("221"::s1::s2::s3::s4::y ++ ys).
Proof.
unfold Soundness.
intros.
inversion H7.
 rewrite_for s1.
 rewrite_for s2.
 rewrite_for s3.
 rewrite_for s4.
 apply ascii32_not_O in H0; [ contradiction |].
 split; [ simpl; omega |].
 inversion H8.
 assumption.

 rewrite_for obj2.
 inversion H8.
 inversion H9.
 assert (y = y0).
  generalize prefix.
  unfold Prefix.
  intro Hprefix.
  apply (Hprefix x _ x0 _ ys ys0); auto.

  rewrite_for y0.
  apply H2 with (obj2:=x0) in H1; auto.
  apply app_same in H16.
  apply H4 with (obj2:=(Array32 xs0)) in H3; auto.
   inversion H3.
   rewrite H1.
   reflexivity.

   rewrite H17 in H0.
   simpl in H0.
   apply ascii32_of_nat_eq in H0; auto.
   inversion H0.
   rewrite <- H30 in H.
   rewrite <- H15 in H.
   inversion H.
   rewrite_for t0.
   rewrite_for t5.
   rewrite_for t6.
   rewrite_for t7.
   rewrite_for ys.
   assumption.
Qed.

Hint Resolve
  soundness_true soundness_false
  soundness_nil soundness_pfixnum soundness_nfixnum
  soundness_uint8 soundness_uint16 soundness_uint32 soundness_uint64
  soundness_int8  soundness_int16  soundness_int32  soundness_int64
  soundness_float soundness_double
  soundness_raw16 soundness_raw32
  soundness_fixarray_nil soundness_array16_nil soundness_array32_nil
  soundness_fixmap_nil soundness_map16_nil soundness_map32_nil
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
 apply soundness_fixraw with (b6:=b6) (b7:=b7) (b8:=b8); auto.
Admitted.
