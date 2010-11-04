Require Import Ascii List.
Require Import ListUtil Object MultiByte Util.

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

Definition split_at {A} n (xs : list A) :=
  (take n xs, drop n xs).

Fixpoint deserialize (xs : list ascii8) :=
  match xs with
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
