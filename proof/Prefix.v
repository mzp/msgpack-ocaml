Require Import List Ascii.
Require Import ListUtil Object SerializeSpec MultiByte ProofUtil Pow.

Definition Prefix obj1 x : Prop := forall obj2 y xs ys,
  Serialized obj1 x ->
  Serialized obj2 y ->
  Valid obj1 ->
  Valid obj2 ->
  x ++ xs = y ++ ys ->
  x = y.

Ltac destruct_serialize obj y :=
  match goal with
    | [ H1 : _ ++ _ = y ++ _,
        H2 : Serialized obj y |- _ ] =>
    destruct y as [ | a ] ;
      [ inversion H2 | inversion H1 ; rewrite_for a; inversion H2 ];
      auto
  end.

(* 結果が1バイトになる変換 *)
Ltac straight_forward :=
  intros;
  unfold Prefix;
  intros obj2 y xs ys S1 S2 V1 V2 Happ;
  destruct_serialize obj2 y.

Lemma prefix_true :
  Prefix (Bool true) ["195"].
Proof.
straight_forward.
Qed.

Lemma prefix_false :
  Prefix (Bool false) ["194"].
Proof.
straight_forward.
Qed.

Lemma prefix_nil :
  Prefix Nil ["192"].
Proof.
straight_forward.
Qed.

Lemma prefix_pfixnum: forall x1 x2 x3 x4 x5 x6 x7,
  Prefix (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
         [Ascii x1 x2 x3 x4 x5 x6 x7 false].
Proof.
straight_forward.
Qed.

Lemma prefix_nfixnum : forall  x1 x2 x3 x4 x5,
  Prefix (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
         [Ascii x1 x2 x3 x4 x5 true true true].
Proof.
straight_forward.
Qed.

(* 結果が固定長多バイトになる変換 *)
Lemma prefix_same : forall A (x y xs ys : list A),
  x ++ xs = y ++ ys ->
  length x = length y ->
  x = y.
Proof.
induction x; induction y; intros; auto.
 simpl in H0.
 discriminate.

 simpl in H0.
 discriminate.

 inversion H.
 inversion H0.
 apply IHx in H3; auto.
 rewrite_for y.
 reflexivity.
Qed.

Ltac same_as_uint8 :=
  unfold Prefix;
  intros c obj2 y xs ys S1 S2 V1 V2 Happ;
  destruct_serialize obj2 y;
  rewrite_for y;
  apply prefix_same in Happ; simpl;  auto with ascii.

Lemma prefix_uint8 : forall c,
  Prefix (Uint8 c) ("204"::list_of_ascii8 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_uint16: forall c,
  Prefix (Uint16 c) ("205"::list_of_ascii16 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_uint32: forall c,
  Prefix (Uint32 c) ("206"::list_of_ascii32 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_uint64 : forall c,
  Prefix (Uint64 c) ("207"::list_of_ascii64 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int8 : forall c,
  Prefix (Int8 c) ("208"::list_of_ascii8 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int16 : forall c,
  Prefix (Int16 c) ("209"::list_of_ascii16 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int32 : forall c,
  Prefix (Int32 c) ("210"::list_of_ascii32 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_int64 : forall c,
  Prefix (Int64 c) ("211"::list_of_ascii64 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_float : forall c,
  Prefix (Float c) ("202"::list_of_ascii32 c).
Proof.
same_as_uint8.
Qed.

Lemma prefix_double : forall c,
  Prefix (Double c) ("203"::list_of_ascii64 c).
Proof.
same_as_uint8.
Qed.

Lemma app_length_eq : forall A (xs ys zs ws : list A),
  xs ++zs = ys ++ ws ->
  length xs = length ys ->
  xs = ys.
Proof.
induction xs; induction ys; simpl; intros; auto.
 inversion H0.

 inversion H0.

 inversion H.
 inversion H0.
 assert (xs = ys); [| rewrite_for xs; auto].
 apply (IHxs _ zs ws); auto.
Qed.

Lemma prefix_fixraw : forall cs b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 b5 b6 b7 b8 = ascii8_of_nat (length cs) ->
  Prefix (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true)::cs).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H2.
inversion H3.
assert (cs = cs0); [| rewrite_for cs; auto ].
apply (app_length_eq _ _ _ xs ys); auto.
rewrite <- (nat_ascii8_embedding (length cs)),
        <- (nat_ascii8_embedding (length cs0)).
 rewrite <- H, <- H8.
 apply ascii5 in H; auto.
 decompose [and] H.
 apply ascii5 in H8; auto.
 decompose [and] H8.
 rewrite H16,H17,H18,H19,H21,H22.
 reflexivity.

 transitivity (pow 5); auto with pow.

 transitivity (pow 5); auto with pow.
Qed.

Lemma prefix_raw16 : forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  Prefix (Raw16 cs) ("218"::s1::s2::cs).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H2.
inversion H3.
inversion H7.
assert (cs = cs0); [| rewrite_for cs; auto ].
apply (app_length_eq _ _ _ xs ys); auto.
rewrite <- (nat_ascii16_embedding (length cs)),
        <- (nat_ascii16_embedding (length cs0)); auto.
rewrite <- H, <- H8, H12, H13.
reflexivity.
Qed.

Lemma prefix_raw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
  Prefix (Raw32 cs) ("219"::s1::s2::s3::s4::cs).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H2.
inversion H3.
inversion H7.
assert (cs = cs0); [| rewrite_for cs; auto ].
apply (app_length_eq _ _ _ xs ys); auto.
rewrite <- (nat_ascii32_embedding (length cs)),
        <- (nat_ascii32_embedding (length cs0)); auto.
rewrite <- H, <- H8, H12, H13, H14, H15.
reflexivity.
Qed.

Lemma prefix_fixarray_nil:
  Prefix (FixArray []) ["072"].
Proof.
straight_forward.
Qed.

Lemma  prefix_array16_nil:
  Prefix (Array16 []) ["220"; "000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H9, <- H11 in *.
assert (("000", "000") <> ascii16_of_nat ((length (x::xs0)))); try contradiction.
inversion H2.
apply ascii16_not_O.
split; auto.
simpl.
omega.
Qed.

Lemma  prefix_array32_nil:
  Prefix (Array32 []) ["221"; "000"; "000";"000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H9, <- H11, <- H12, <- H13 in *.
assert (("000", "000",("000","000")) <> ascii32_of_nat ((length (x::xs0)))); try contradiction.
inversion H2.
apply ascii32_not_O.
split; auto.
simpl.
omega.
Qed.

Lemma prefix_fixmap_nil:
  Prefix (FixMap []) ["128"].
Proof.
straight_forward.
Qed.

Lemma prefix_map16_nil:
  Prefix (Map16 []) ["222"; "000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H10, <- H12 in *.
assert (("000", "000") <> ascii16_of_nat ((length ((x1, x2)::xs0)))); try contradiction.
inversion H2.
apply ascii16_not_O.
split.
 simpl.
 omega.

 exact H19.
Qed.

Lemma prefix_map32_nil:
  Prefix (Map32 []) ["223"; "000"; "000";"000"; "000"].
Proof.
unfold Prefix; intros.
destruct_serialize obj2 y.
rewrite_for obj2.
rewrite_for y.
inversion H3.
rewrite <- H10, <- H12, <- H13, <- H14 in *.
assert (("000", "000",("000","000")) <> ascii32_of_nat ((length ((x1, x2)::xs0)))); try contradiction.
inversion H2.
apply ascii32_not_O.
split.
 simpl.
 omega.

 exact H21.
Qed.

Lemma prefix_array16_cons: forall x xs y ys s1 s2 t1 t2,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length (x :: xs)) ->
  Serialized x y ->
  Prefix x y ->
  Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  Prefix (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  Prefix (Array16 (x::xs)) ("220"::s1::s2::y ++ ys).
Proof.
unfold Prefix.
intros.
destruct_serialize obj2 y0.
 rewrite_for y0.
 inversion H9.
 rewrite_for s1.
 rewrite_for s2.
 apply ascii16_not_O in H0; [ contradiction |].
 inversion H7.
 split; [ simpl; omega | exact H17 ].

 rewrite_for y0.
 rewrite_for obj2.
 inversion H9.
 rewrite_for s0.
 rewrite_for s3.
 assert( y++ ys = y1 ++ ys1); [| rewrite_for (y++ys); reflexivity ].
 rewrite <- (app_assoc y ys xs0), <- (app_assoc y1 ys1 ys0) in H18.
 inversion H7.
 inversion H8.
 apply (H2 x0 y1 (ys++xs0) (ys1++ys0))in H1; auto.
 rewrite_for y1.
 apply app_same in H18.
 apply (H4 (Array16 xs1)  ("220" :: t0 :: t3 :: ys1) xs0 ys0) in H3; auto.
 inversion H3.
 reflexivity.
 change (("220" :: t1 :: t2 :: ys) ++ xs0) with ("220" :: t1 :: t2 :: (ys ++ xs0)).
 change (("220" :: t0 :: t3 :: ys1) ++ ys0) with ("220" :: t0 :: t3 :: (ys1 ++ ys0)).
 unfold ascii8 in *.
 rewrite <- H18.
 rewrite H0 in H13.
 apply ascii16_of_nat_eq in H13; auto.
 simpl in H13.
 inversion H13.
 rewrite <- H26 in H11.
 rewrite <- H11 in H.
 inversion H.
 reflexivity.
Qed.

Hint Resolve
  prefix_true prefix_false
  prefix_nil prefix_pfixnum prefix_nfixnum
  prefix_uint8 prefix_uint16 prefix_uint32 prefix_uint64
  prefix_int8  prefix_int16  prefix_int32  prefix_int64
  prefix_float prefix_double
  prefix_raw16 prefix_raw32
  prefix_fixarray_nil prefix_array16_nil prefix_array32_nil
  prefix_fixmap_nil prefix_map16_nil prefix_map32_nil
  : prefix.

Lemma prefix_intro: forall obj x,
  (Serialized obj x -> Prefix obj x)->
  Prefix obj x.
Proof.
unfold Prefix.
intros.
apply H with (xs:=xs) (ys:=ys) in H1; auto.
Qed.

Lemma prefix : forall obj1 x,
  Prefix obj1 x.
Proof.
intros.
apply prefix_intro.
intro.
pattern obj1,x.
apply Serialized_ind; intros; auto with prefix.
 apply (prefix_fixraw _ b1 b2 b3 b4 b5 b6 b7 b8); auto.
Focus 2.
 apply prefix_array16_cons with (t1:=t1) (t2:=t2); auto.
Admitted.
