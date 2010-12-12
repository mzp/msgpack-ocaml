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

Definition lift P (o : object) (b : list ascii) := forall os bs,
  P os bs -> P (o::os) (b ++ bs).

Inductive SerializedList : list object -> list ascii8 -> Prop :=
| SLbot :
  SerializedList [] []
| SLNil:
  lift SerializedList Nil ["192"]
| SLTrue :
  lift SerializedList (Bool true)  ["195"]
| SLFalse :
  lift SerializedList (Bool false) ["194"]
| SLPFixnum : forall x1 x2 x3 x4 x5 x6 x7,
  lift SerializedList (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
                      [Ascii x1 x2 x3 x4 x5 x6 x7 false]
| SLNFixnum : forall  x1 x2 x3 x4 x5,
  lift SerializedList (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
                      [Ascii x1 x2 x3 x4 x5 true true true]
| SLUint8 : forall c,
  lift SerializedList (Uint8 c) ("204" :: list_of_ascii8 c)
| SLUint16 : forall c,
  lift SerializedList (Uint16 c) ("205" :: list_of_ascii16 c)
| SLUint32 : forall c,
  lift SerializedList (Uint32 c) ("206" :: list_of_ascii32 c)
| SLUint64 : forall c,
  lift SerializedList (Uint64 c) ("207" :: list_of_ascii64 c)
| SLInt8 : forall c,
  lift SerializedList (Int8 c) ("208" :: list_of_ascii8 c)
| SLInt16 : forall c,
  lift SerializedList (Int16 c) ("209" :: list_of_ascii16 c)
| SLInt32 : forall c,
  lift SerializedList (Int32 c) ("210" :: list_of_ascii32 c)
| SLInt64 : forall c,
  lift SerializedList (Int64 c) ("211" :: list_of_ascii64 c)
| SLFloat : forall c,
  lift SerializedList (Float c) ("202" :: list_of_ascii32 c)
| SLDouble : forall c,
  lift SerializedList (Double c) ("203" :: list_of_ascii64 c)
| SLFixRaw : forall cs b1 b2 b3 b4 b5,
  Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (length cs) ->
  lift SerializedList (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true) :: cs)
| SLRaw16 : forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  lift SerializedList (Raw16 cs) ("218" :: s1 :: s2 :: cs)
| SLRaw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
   lift SerializedList (Raw32 cs) ("219" :: s1 :: s2 :: s3 :: s4 :: cs)
| SLFixArray : forall os n b1 b2 b3 b4 xs ys bs,
  SerializedList os bs ->
  (xs,ys) = split_at n os ->
  n < pow 4 ->
  (Ascii b1 b2 b3 b4 false false false false) = ascii8_of_nat n ->
  SerializedList ((FixArray xs) :: ys) ((Ascii b1 b2 b3 b4 true false false true) :: bs)
| SLArray16 : forall os n xs ys bs s1 s2,
  SerializedList os bs ->
  (xs,ys) = split_at n os ->
  n < pow 16 ->
  (s1,s2) = ascii16_of_nat n ->
  SerializedList ((Array16 xs)::ys) ("220" :: s1 :: s2 :: bs)
| SLArray32 : forall os n xs ys bs s1 s2 s3 s4,
  SerializedList os bs ->
  (xs,ys) = split_at n os ->
  n < pow 32 ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat n ->
  SerializedList ((Array32 xs)::ys) ("221" :: s1 :: s2 :: s3 :: s4 :: bs)
| SLFixMap : forall os n b1 b2 b3 b4 xs ys bs,
  SerializedList os bs ->
  (xs,ys) = split_at (2 * n) os ->
  n < pow 4 ->
  (Ascii b1 b2 b3 b4 false false false false) = ascii8_of_nat n ->
  SerializedList ((FixMap (pairwise xs)) :: ys) ((Ascii b1 b2 b3 b4 false false false true) :: bs)
| SLMap16 : forall os n xs ys bs s1 s2,
  SerializedList os bs ->
  (xs,ys) = split_at (2 * n) os ->
  n < pow 16 ->
  (s1,s2) = ascii16_of_nat n ->
  SerializedList ((Map16 (pairwise xs))::ys) ("222" :: s1 :: s2 :: bs)
| SLMap32 : forall os n xs ys bs s1 s2 s3 s4,
  SerializedList os bs ->
  (xs,ys) = split_at (2 * n) os ->
  n < pow 32 ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat n ->
  SerializedList ((Map32 (pairwise xs))::ys) ("223" :: s1 :: s2 :: s3 :: s4 :: bs).

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