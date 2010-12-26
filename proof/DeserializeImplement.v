Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec Pow SerializedList.

Open Scope char_scope.

Definition compact (xs : list object) : list ascii8 :=
  List.flat_map (fun x => match x with
                            FixRaw xs =>  xs
                            | _ => []
                          end)
  xs.

Fixpoint deserialize (n : nat) (xs : list ascii8) {struct xs} :=
  match n with
    | 0 =>
      match xs with
        | "192" :: ys =>
          Nil::deserialize 0 ys
        | "194" :: ys =>
          Bool false :: deserialize 0 ys
        | "195" :: ys =>
          Bool true :: deserialize 0 ys
        | Ascii b1 b2 b3 b4 b5 b6 b7 false :: ys =>
          PFixnum (Ascii b1 b2 b3 b4 b5 b6 b7 false) :: deserialize 0 ys
        | (Ascii b1 b2 b3 b4 b5 true true true) :: ys =>
          NFixnum (Ascii b1 b2 b3 b4 b5 true true true) :: deserialize 0 ys
        | "204" :: c1 :: ys =>
          Uint8 c1 :: deserialize 0 ys
        | "205" :: c1 :: c2 :: ys =>
          Uint16 (c1, c2) :: deserialize 0 ys
        | "206" :: c1 :: c2 :: c3 :: c4 :: ys =>
          Uint32 ((c1, c2), (c3, c4)) :: deserialize 0 ys
        | "207" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
          Uint64 (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize 0 ys
        | "208" :: c1 :: ys =>
          Int8 c1 :: deserialize 0 ys
        | "209" :: c1 :: c2 :: ys =>
          Int16 (c1, c2) :: deserialize 0 ys
        | "210" :: c1 :: c2 :: c3 :: c4 :: ys =>
          Int32 ((c1, c2), (c3, c4)) :: deserialize 0 ys
        | "211" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
          Int64 (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize 0 ys
        | "202" :: c1 :: c2 :: c3 :: c4 :: ys =>
          Float ((c1,c2), (c3, c4)) :: deserialize 0 ys
        | "203" :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: ys =>
          Double (((c1, c2), (c3, c4)), ((c5, c6), (c7, c8))) :: deserialize 0 ys
        | Ascii b1 b2 b3 b4 b5 true false true :: ys =>
          let n :=
            nat_of_ascii8 (Ascii b1 b2 b3 b4 b5 false false false) in
          let (zs, ws) :=
            split_at n @@ deserialize n ys in
            FixRaw (compact zs) :: ws
        | "218" :: s1 :: s2 :: ys =>
          let n :=
            nat_of_ascii16 (s1,s2) in
          let (zs, ws) :=
            split_at n @@ deserialize n ys in
            Raw16 (compact zs) :: ws
        | "219" :: s1 :: s2 :: s3 :: s4 :: ys =>
          let n :=
            nat_of_ascii32 ((s1,s2),(s3,s4)) in
          let (zs, ws) :=
            split_at n @@ deserialize n ys in
            Raw32 (compact zs) :: ws
        | Ascii b1 b2 b3 b4 true false false true :: ys =>
          let n :=
            nat_of_ascii8 (Ascii b1 b2 b3 b4 false false false false) in
            let (zs, ws) :=
              split_at n @@ deserialize n ys in
              FixArray zs :: ws
        | "220" :: s1 :: s2 :: ys =>
          let n :=
            nat_of_ascii16 (s1,s2) in
            let (zs, ws) :=
              split_at n @@ deserialize 0 ys in
              Array16 zs :: ws
        | "221" :: s1 :: s2 :: s3 :: s4 :: ys =>
          let n :=
            nat_of_ascii32 ((s1, s2), (s3, s4)) in
            let (zs, ws) :=
              split_at n @@ deserialize 0 ys in
              Array32 zs :: ws
        | Ascii b1 b2 b3 b4 false false false true :: ys =>
          let n :=
            nat_of_ascii8 (Ascii b1 b2 b3 b4 false false false false) in
            let (zs, ws) :=
              split_at (2 * n) @@ deserialize 0 ys in
              FixMap (pair zs) :: ws
        | "222" :: s1 :: s2 :: ys =>
          let n :=
            nat_of_ascii16 (s1,s2) in
            let (zs, ws) :=
              split_at (2 * n) @@ deserialize 0 ys in
              Map16 (pair zs) :: ws
        | "223" :: s1 :: s2 :: s3 :: s4 :: ys =>
          let n :=
            nat_of_ascii32 ((s1, s2), (s3, s4)) in
            let (zs, ws) :=
              split_at (2 * n) @@ deserialize 0 ys in
              Map32 (pair zs) :: ws
        | _ =>
          []
      end
    | S m =>
      match xs with
        | y::ys => FixRaw [ y ]::deserialize m ys
        | _ => []
      end
  end.

Lemma deserialize_correct : forall os bs,
  SerializedList os bs ->
  deserialize 0 bs = os.
Proof.
  apply SerializedList_ind; intros.
  Focus 18.
  simpl.
  change (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2) with (nat_of_ascii16 (s1,s2)).



  simpl.
  rewrite H0.
  change (nat_of_ascii8 s1 * 256 + nat_of_ascii8 s2) with (nat_of_ascii16 (s1,s2)).
  rewrite H3.
  rewrite nat_ascii16_embedding; auto.
  unfold split_at in H1.
  inversion H1.
  reflexivity.
Qed.*)