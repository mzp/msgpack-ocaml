Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec.

Open Scope char_scope.

Fixpoint serialize (obj : object) : list ascii8 :=
  match obj with
    | Bool true  => [ "195" ]
    | Bool false => [ "194" ]
    | Array16 xs =>
      let ys :=
        flat_map serialize xs
      in
      let (s1, s2) :=
        ascii16_of_nat (length  xs)
      in
        "221"::s1::s2::ys
  end.

Fixpoint take {A} n (xs : list A) :=
  match n, xs with
    | O , _ => []
    | _ , [] => []
    | S m, x::xs =>
      x::take m xs
  end.

Fixpoint drop {A} n (xs : list A) :=
  match n, xs with
    | O , _ => xs
    | _ , [] => []
    | S m, x::xs =>
      drop m xs
  end.

Definition split_at {A} (n : nat) (xs : list A) : list A * list A :=
  (take n xs, drop n xs).

Fixpoint deserialize (xs : list ascii8) :=
  match xs with
    | "195"::ys =>
      (Bool true)::deserialize ys
    | "194"::ys =>
      (Bool false)::deserialize ys
    | "221"::s1::s2::ys =>
      let n :=
        nat_of_ascii16 (s1,s2) in
      let (zs, ws) :=
        split_at n @@ deserialize ys
      in
        (Array16 zs)::ws
    | _ =>
      []
  end.

Theorem serialize_correct : forall obj xs,
  Serialized obj xs ->
  serialize obj = xs.
Proof.
intros.
generalize H.
pattern obj,xs.
apply Serialized_ind; auto; intros; simpl.
 rewrite <- ascii16_of_nat_O.
 reflexivity.

 simpl in H1.
 rewrite <- H1.
 apply H3 in H2.
 rewrite H2.
 apply H5 in H4.
 simpl in H4.
 rewrite <- H0 in *.
 inversion H4.
 reflexivity.
Qed.

Lemma take_length : forall A ( xs : list A) n,
  n = List.length xs ->
  take n xs = xs.
Proof.
induction xs; intros; simpl in *.
 rewrite H.
 reflexivity.

 rewrite H.
 simpl.
 rewrite IHxs; auto.
Qed.

Lemma drop_length : forall A ( xs : list A) n,
  n = List.length xs ->
  drop n xs = [].
Proof.
induction xs; intros; simpl in *.
 rewrite H.
 reflexivity.

 rewrite H.
 simpl.
 rewrite IHxs; auto.
Qed.

Lemma take_nil : forall A n,
  take n ([] : list A) = [].
Proof.
induction n; auto.
Qed.

Lemma take_drop_length : forall A ( xs ys : list A) n,
  take n xs = ys ->
  drop n xs = [ ] ->
  xs  = ys.
Proof.
induction xs; intros; simpl in *.
 rewrite take_nil in H.
 assumption.

 destruct n.
  simpl in H0.
  discriminate.

  simpl in *.
  destruct ys.
   discriminate.

   inversion H.
   rewrite H3.
   apply IHxs in H3; auto.
   rewrite H3.
   reflexivity.
Qed.

Lemma prefix_deserialize : forall x xs y ys,
  Serialized x y ->
  Valid x ->
  [ x ] = deserialize y ->
  xs = deserialize ys ->
  x :: xs = deserialize (y ++ ys).
Proof.
intros x xs y ys H.
generalize xs ys H.
pattern x, y.
apply Serialized_ind; auto; intros; simpl in *.
 match goal with [ H : xs0 = _ |- _ ] => rewrite H end.
 reflexivity.

 match goal with [ H : xs0 = _ |- _ ] => rewrite H end.
 reflexivity.

 match goal with [ H : xs0 = _ |- _ ] => rewrite H end.
 reflexivity.

 match goal with [ H : xs1 = _ |- _ ] => rewrite H end.
 match goal with [ H : [ Array16 _ ] = _ |- _ ] => inversion H end.
 match goal with [ H : Valid (Array16 (_::_)) |- _ ] => inversion H end.
 apply (H3 (deserialize (ys0 ++ ys1)) (ys0 ++ ys1)) in H2; auto.
 rewrite <- app_assoc.
 assert(  Array16 (x0 :: xs0) :: deserialize ys1 =
   Array16
     (take (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2)
        (deserialize (y0 ++ ys0 ++ ys1)))
   :: drop (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2)
        (deserialize (y0 ++ ys0 ++ ys1))); auto.
 rewrite <- H2.
 apply (H5 (deserialize ys1) ys1) in H4; auto.
 inversion H4.
 change (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2) with (nat_of_ascii16 (s1,s2)) in *.
 change (nat_of_ascii8 t1 * 256 + nat_of_ascii8 t2) with (nat_of_ascii16 (t1,t2)) in *.
 match goal with [ H : deserialize ys1 = _ |- _ ] => rewrite H end.
 rewrite H0,H1.
 rewrite nat_ascii16_embedding; auto.
 rewrite nat_ascii16_embedding; auto.

 change (length (x0 :: xs0)) with (S (length xs0)) in *.
 omega.
Admitted.

Lemma deserialize_correct : forall x ys,
  Serialized x ys ->
  Valid x ->
  deserialize ys = [ x ].
Proof.
intros x ys H.
generalize H.
pattern x, ys.
apply Serialized_ind; auto; intros.
simpl.
change (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2) with (nat_of_ascii16 (s1,s2)).
inversion H7.
assert (nat_of_ascii16 (s1, s2) = length (x0 :: xs)).
 rewrite H1.
 apply nat_ascii16_embedding; auto.

 rewrite <- (prefix_deserialize x0 xs y ys0), take_length, drop_length; auto.
  rewrite H3; auto.

  apply H5 in H4; auto.
  simpl in H4.
  inversion H4.
  rewrite H15.
  apply take_drop_length in H15; auto.
Qed.


