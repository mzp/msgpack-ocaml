Require Import List Omega.

Notation "[ ]" := nil : list_scope.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Lemma app_same : forall A (xs ys zs : list A),
  xs ++  ys = xs ++ zs -> ys = zs.
Proof.
induction xs; intros; simpl in H.
 auto.

 inversion H.
 apply IHxs in H1.
 auto.
Qed.
Lemma length_lt_O: forall A (x : A) xs,
  length (x::xs) > 0.
Proof.
intros.
simpl.
omega.
Qed.

Lemma length_inv: forall A (x y : A) xs ys,
  length (x :: xs) = length (y :: ys) ->
  length xs = length ys.
Proof.
intros.
inversion H.
auto.
Qed.

Hint Resolve length_lt_O.


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

Lemma take_length : forall A ( xs ys : list A) n,
  n = List.length xs ->
  take n (xs ++ ys) = xs.
Proof.
induction xs; intros; simpl in *.
 rewrite H.
 reflexivity.

 rewrite H.
 simpl.
 rewrite IHxs; auto.
Qed.

Lemma drop_length : forall A ( xs ys : list A) n,
  n = List.length xs ->
  drop n (xs ++ ys) = ys.
Proof.
induction xs; intros; simpl in *.
 rewrite H.
 reflexivity.

 rewrite H.
 simpl.
 rewrite IHxs; auto.
Qed.

Lemma split_at_length : forall A (xs ys : list A),
  (xs, ys) = split_at (length xs) (xs ++ ys).
Proof.
intros.
unfold split_at.
rewrite take_length, drop_length; auto.
Qed.

Lemma split_at_soundness : forall A (xs ys zs : list A) n,
  (ys,zs) = split_at n xs ->
  xs = ys ++ zs.
Proof.
induction xs; induction n; intros; simpl;
  try (inversion H; reflexivity).

  unfold split_at in *.
  simpl in H.
  destruct ys.
   inversion H.

   rewrite (IHxs ys zs n); auto.
    inversion H.
    reflexivity.

    inversion H.
    reflexivity.
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

Fixpoint pairwise { A } ( xs : list A ) :=
  match xs with
    | [] => []
    | [x] => []
    | k :: v :: ys =>
      (k, v) :: pairwise ys
  end.
