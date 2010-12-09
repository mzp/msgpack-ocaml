Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec Pow.

Open Scope char_scope.

Fixpoint pairwise { A } ( xs : list A ) :=
  match xs with
    | [] => []
    | [x] => []
    | k :: v :: ys =>
      (k, v) :: pairwise ys
  end.

Fixpoint deserialize (xs : list ascii8) :=
  match xs with
    | "192" :: ys =>
      Nil::deserialize ys
    | "194" :: ys =>
      Bool false :: deserialize ys
    | "195" :: ys =>
      Bool true :: deserialize ys
    | Ascii b1 b2 b3 b4 b5 b6 b7 false :: ys =>
      PFixnum (Ascii b1 b2 b3 b4 b5 b6 b7 false) :: deserialize ys
    | (Ascii b1 b2 b3 b4 b5 true true true) :: ys =>
      NFixnum (Ascii b1 b2 b3 b4 b5 true true true) :: deserialize ys
    | "204" :: c1 :: ys =>
      Uint8 c1 :: deserialize ys
    | "205" :: c1 :: c2 :: ys =>
      Uint16 (c1, c2) :: deserialize ys
    | "206" :: c1 :: c2 :: c3 :: c4 :: ys =>
      Uint32 ((c1, c2), (c3, c4)) :: deserialize ys
    | "207" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
      Uint64 (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize ys
    | "208" :: c1 :: ys =>
      Int8 c1 :: deserialize ys
    | "209" :: c1 :: c2 :: ys =>
      Int16 (c1, c2) :: deserialize ys
    | "210" :: c1 :: c2 :: c3 :: c4 :: ys =>
      Int32 ((c1, c2), (c3, c4)) :: deserialize ys
    | "211" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
      Int64 (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize ys
    | "202" :: c1 :: c2 :: c3 :: c4 :: ys =>
      Float ((c1,c2), (c3, c4)) :: deserialize ys
    | "203" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
      Double (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize ys
    | Ascii b1 b2 b3 b4 b5 true false true :: ys =>
      let n :=
        nat_of_ascii8 (Ascii b1 b2 b3 b4 b5 false false false) in
      let (zs, ws) :=
        split_at n @@ deserialize ys in
        FixArray zs :: ws
    | "220" :: s1 :: s2 :: ys =>
      let n :=
        nat_of_ascii16 (s1,s2) in
      let (zs, ws) :=
        split_at n @@ deserialize ys in
        Array16 zs :: ws
    | "221" :: s1 :: s2 :: s3 :: s4 :: ys =>
      let n :=
        nat_of_ascii32 ((s1, s2), (s3, s4)) in
      let (zs, ws) :=
        split_at n @@ deserialize ys in
        Array32 zs :: ws
    | Ascii b1 b2 b3 b4 false false false true :: ys =>
      let n :=
        nat_of_ascii8 (Ascii b1 b2 b3 b4 false false false false) in
      let (zs, ws) :=
        split_at (2 * n) @@ deserialize ys in
        FixMap (pairwise zs) :: ws
    | "222" :: s1 :: s2 :: ys =>
      let n :=
        nat_of_ascii16 (s1,s2) in
      let (zs, ws) :=
        split_at (2 * n) @@ deserialize ys in
        Map16 (pairwise zs) :: ws
    | "223" :: s1 :: s2 :: s3 :: s4 :: ys =>
      let n :=
        nat_of_ascii32 ((s1, s2), (s3, s4)) in
      let (zs, ws) :=
        split_at (2 * n) @@ deserialize ys in
        Map32 (pairwise zs) :: ws
    | _ =>
      []
  end.

Inductive SerializedList : list object -> list ascii8 -> Prop :=
| SLNil  :
  SerializedList [] []
| SLTrue : forall os bs,
  SerializedList os bs ->
  SerializedList ((Bool true)::os) ("195"::bs)
| SLFalse : forall os bs,
  SerializedList os bs ->
  SerializedList ((Bool false)::os) ("194"::bs)
| SLArray16 : forall os n xs ys bs s1 s2,
  SerializedList os bs ->
  (xs,ys) = split_at n os ->
  n < pow 16 ->
  (s1,s2) = ascii16_of_nat n ->
  SerializedList ((Array16 xs)::ys) ("221"::s1::s2::bs).

Lemma app_cons: forall A (xs ys zs : list A) x,
  x :: (xs ++ ys) ++ zs = x :: (xs ++ ys ++ zs).
Proof.
induction xs; intros; simpl; auto.
rewrite (IHxs ys zs a).
reflexivity.
Qed.

Lemma sl_soundness: forall x xs y ys,
  Serialized x y ->
  Valid x ->
  SerializedList xs ys ->
  SerializedList (x :: xs) (y ++ ys).
Admitted.
(*Proof.
intros x xs y ys H.
generalize xs ys H.
pattern x,y.
apply Serialized_ind; intros; simpl; auto.
 apply SLTrue; auto.

 apply SLFalse; auto.

 change (["221"; "000"; "000"] ++ ys0) with ("221"::"000"::"000"::ys0).
 apply (SLArray16 xs0 0); auto.
  rewrite ascii16_of_nat_O.
  reflexivity.

 rewrite app_cons.
 inversion H7.
  apply (SLArray16 (x0 :: xs0 ++ xs1) (length (x0::xs0))); auto.
  apply (H3 (xs0 ++ xs1) (ys0 ++ ys1)) in H2; auto.
  apply (H5 xs1 ys1) in H4; auto.
  inversion H4.
  apply split_at_soundness in H20.
  rewrite H20 in H19.
  auto.

  apply split_at_length.
Qed.*)

Lemma deserialize_soundness : forall os bs,
  SerializedList os bs ->
  deserialize bs = os.
Proof.
apply SerializedList_ind; intros.
 reflexivity.

 simpl; rewrite H0; auto.

 simpl; rewrite H0; auto.

 simpl.
 rewrite H0.
 change (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2) with (nat_of_ascii16 (s1,s2)).
 rewrite H3.
 rewrite nat_ascii16_embedding; auto.
 unfold split_at in H1.
 inversion H1.
 reflexivity.
Qed.