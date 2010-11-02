Require Import List.
Require Import ListUtil Object SerializeSpec MultiByte.

Definition Prefix obj1 x : Prop := forall obj2 y xs ys,
  Serialized obj2 y ->
  Valid obj1 ->
  Valid obj2 ->
  x ++ xs = y ++ ys ->
  x = y.

Lemma prefix_true :
  Serialized (Bool true) ["195"] ->
  Prefix (Bool true) ["195"].
Proof.
unfold Prefix; intros.
destruct y; [ inversion H0 | idtac].
inversion H3.
rewrite <- H5 in H0.
inversion H0.
reflexivity.
Qed.

Lemma prefix_false :
  Serialized (Bool false) ["194"] ->
  Prefix (Bool false) ["194"].
Proof.
unfold Prefix; intros.
destruct y; [ inversion H0 | idtac].
inversion H3.
rewrite <- H5 in H0.
inversion H0.
reflexivity.
Qed.

Lemma prefix_array16_nil:
  Serialized (Array16 []) ["221"; "000"; "000"] ->
  Prefix (Array16 []) ["221"; "000"; "000"].
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

Lemma prefix : forall obj1 x,
  Serialized obj1 x ->
  Prefix obj1 x.
Proof.
intros.
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
