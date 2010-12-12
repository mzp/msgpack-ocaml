Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec Pow SerializedList.

Open Scope char_scope.

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


Lemma deserialize_correct : forall os bs,
  SerializedList os bs ->
  deserialize bs = os.
Admitted.
(*Proof.
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
Qed.*)