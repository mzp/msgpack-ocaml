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