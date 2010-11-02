Require Import Ascii List.
Require Import ListUtil Object MultiByte.

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
