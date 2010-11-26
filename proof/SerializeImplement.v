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

