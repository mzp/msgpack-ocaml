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
          Nil::deserialize n ys
        |  "218" :: s1 :: s2 :: ys =>
          let n := nat_of_ascii16 (s1,s2) in
            let (zs, ws) :=
              split_at n @@ deserialize n ys in
              Raw16 (compact zs) :: ws
        | "220" :: s1 :: s2 :: ys =>
          let n :=
            nat_of_ascii16 (s1,s2) in
            let (zs, ws) :=
              split_at n @@ deserialize 0 ys in
              Array16 zs :: ws
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