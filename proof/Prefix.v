Require Import List Ascii.
Require Import ListUtil Object SerializeSpec MultiByte ProofUtil.

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

(*Lemma prefix_array16_nil:
  Serialized (Array16 []) ["220"; "000"; "000"] ->
  Prefix (Array16 []) ["220"; "000"; "000"].
Proof.
unfold Prefix; intros.
destruct y; [ inversion H0 | idtac].

inversion H3.
rewrite <- H5 in *; clear H5.
destruct y; [ inversion H0 | idtac].

inversion H3.
rewrite <- H5 in *; clear H5.
destruct y; [ inversion H0 | idtac].

inversion H3.
rewrite <- H5 in *; clear H5.
inversion H0; auto.
apply ascii16_not_O in H12.
 contradiction.

 rewrite <- H11 in *; clear H11.
 split.
  apply length_lt_O.

  inversion H2.
  auto.
Qed.

Lemma prefix_array16_cons: forall x xs t1 t2 s1 s2 y ys,
  Serialized x y ->
  (Serialized x y -> Prefix x y) ->
  (Serialized (Array16 xs) ("221" :: t1 :: t2 :: ys) ->
    Prefix (Array16 xs) ("221" :: t1 :: t2 :: ys)) ->
  Serialized (Array16 (x :: xs)) ("221" :: s1 :: s2 :: y ++ ys) ->
  Serialized (Array16 xs) ("221" :: t1 :: t2 :: ys) ->
  (t1, t2) = ascii16_of_nat (length xs) ->
  Prefix (Array16 (x :: xs)) ("221" :: s1 :: s2 :: y ++ ys).
Proof.
Admitted.
intros.
apply H0 in H.
apply H1 in H3.
unfold Prefix in *.
intros.
inversion H2.

destruct y0; [ inversion H5 | inversion H8 ].
rewrite <- H19 in *; clear H19.

destruct y0; [ inversion H5 | inversion H8 ].
rewrite <- H19 in *; clear H19.

destruct y0; [ inversion H5 | inversion H8 ].
rewrite <- H19 in *; clear H19.

inversion H5.
 rewrite <- H23, <- H24 in *.
 apply ascii16_not_O in H15.
  contradiction.

  split.
   apply length_lt_O.

   inversion H6.
   auto.

 rewrite H13, <- H23, <- H25 in *; clear H13 H23 H25.
 rewrite <- (app_assoc y ys xs0), <- (app_assoc y2 ys2 ys0) in H22.
 inversion H6; inversion H7.
 apply (H _ _ (ys ++ xs0) (ys2 ++ ys0)) in H27; auto.
 apply (H3 _ _ xs0 ys0) in H28; auto.
  inversion H28.
  rewrite H27.
  reflexivity.

  assert ((t1,t2)=(t4,t5)).
   rewrite H4, H24.
   apply (varray16_inv2 _ x x1); auto.
   rewrite <- H15, <- H26.
   reflexivity.

   inversion H36.
   simpl.
   rewrite H27 in *.

   apply app_same in H22.
   rewrite H22.
   reflexivity.
Qed.
*)

Lemma prefix : forall obj1 x,
  Serialized obj1 x ->
  Prefix obj1 x.
Proof.
Admitted.
(*intros.
generalize H.
pattern obj1, x.
apply Serialized_ind; auto; intros.
 (* true *)
 apply prefix_true in H0.
 assumption.

 (* false *)
 apply prefix_false in H0.
 assumption.

 (* nil *)
 apply prefix_array16_nil in H0.
 assumption.

 (* cons *)
 eapply prefix_array16_cons; auto.
Qed.
*)