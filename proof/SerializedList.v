Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec Pow.

Open Scope char_scope.

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