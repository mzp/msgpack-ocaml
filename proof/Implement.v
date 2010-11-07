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
    | "194"::ys =>
      (Bool false)::deserialize ys
    | "195"::ys =>
      (Bool true)::deserialize ys
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

Lemma deserialize_prefix : forall x y xs,
  Serialized y  x ->
  deserialize x = [ y ] ->
  deserialize (x ++ xs) = y :: deserialize xs.
Proof.
intros until y.
pattern y, x.
apply Serialized_ind; auto; intros.
 simpl.

