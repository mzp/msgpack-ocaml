Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec.

Open Scope char_scope.

Fixpoint serialize (obj : object) : list ascii8 :=
  match obj with
    | Nil        => [ "192" ]
    | Bool false => [ "194" ]
    | Bool true  => [ "195" ]
    | PFixnum (Ascii b1 b2 b3 b4 b5 b6 b7 _) =>
      [ Ascii b1 b2 b3 b4 b5 b6 b7 false ]
    | NFixnum (Ascii b1 b2 b3 b4 b5 _ _ _) =>
      [ Ascii b1 b2 b3 b4 b5 true true true ]
    | Uint8  c => "204"::list_of_ascii8 c
    | Uint16 c => "205"::list_of_ascii16 c
    | Uint32 c => "206"::list_of_ascii32 c
    | Uint64 c => "207"::list_of_ascii64 c
    | Int8   c => "208"::list_of_ascii8 c
    | Int16  c => "209"::list_of_ascii16 c
    | Int32  c => "210"::list_of_ascii32 c
    | Int64  c => "211"::list_of_ascii64 c
    | Float  c => "202"::list_of_ascii32 c
    | Double c => "203"::list_of_ascii64 c
    | FixRaw xs =>
      match ascii8_of_nat @@ length xs with
        | Ascii b1 b2 b3 b4 b5 _ _ _ =>
          (Ascii b1 b2 b3 b4 b5 true false true)::xs
      end
    | Raw16 xs =>
      let (s1,s2) :=
        ascii16_of_nat @@ length xs
      in
        "218"::s1::s2::xs
    | Raw32 xs =>
      match ascii32_of_nat @@ length xs with
        | ((s1,s2),(s3,s4)) =>
          "219"::s1::s2::s3::s4::xs
      end
    | FixArray xs =>
      let ys :=
        flat_map serialize xs
      in
      match ascii8_of_nat @@ length xs with
        | Ascii b1 b2 b3 b4 _ _ _ _ =>
          (Ascii b1 b2 b3 b4 true false false true)::ys
      end
    | Array16 xs =>
      let ys :=
        flat_map serialize xs
      in
      let (s1, s2) :=
        ascii16_of_nat (length  xs)
      in
        "220"::s1::s2::ys
    | Array32 xs =>
      let ys :=
        flat_map serialize xs
      in
      match ascii32_of_nat @@ length xs with
        | ((s1,s2),(s3,s4)) =>
         "221"::s1::s2::s3::s4::ys
      end
    | FixMap xs =>
      let ys :=
        flat_map (fun p => serialize (fst p) ++ serialize (snd p)) xs
      in
      match ascii8_of_nat @@ length xs with
        | Ascii b1 b2 b3 b4 _ _ _ _ =>
          (Ascii b1 b2 b3 b4 false false false false)::ys
      end
    | Map16 xs =>
      let ys :=
        flat_map (fun p => serialize (fst p) ++ serialize (snd p)) xs
      in
      let (s1, s2) :=
        ascii16_of_nat (length  xs)
      in
        "222"::ys
    | Map32 xs =>
      let ys :=
        flat_map (fun p => serialize (fst p) ++ serialize (snd p)) xs
      in
      match ascii32_of_nat @@ length xs with
        | ((s1,s2),(s3,s4)) =>
         "223"::s1::s2::s3::s4::ys
      end
  end.

Theorem serialize_correct : forall obj xs,
  Serialized obj xs ->
  serialize obj = xs.
Admitted.
(*Proof.
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

*)