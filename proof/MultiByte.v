(*
   16bits,32bits,64bitsの定義。BigEndian。
*)
Require Import List Ascii NArith Omega Euclid.
Require Import Pow.

Open Scope char_scope.

(* * 型の定義 *)
Definition ascii8  : Set := ascii.
Definition ascii16 : Set := (ascii8  * ascii8)%type.
Definition ascii32 : Set := (ascii16 * ascii16)%type.
Definition ascii64 : Set := (ascii32 * ascii32)%type.

(** ** natとの相互変換 *)
Definition nat_of_ascii8 :=
  nat_of_ascii.

Definition ascii8_of_nat :=
  ascii_of_nat.

Definition ascii16_of_nat (a : nat)  :=
  let (q,r,_,_) := divmod a (pow 8) (pow_lt_O 8) in
    (ascii8_of_nat q, ascii8_of_nat r).

Definition nat_of_ascii16 (a : ascii16) :=
  let (a1, a2) := a in
    (nat_of_ascii8 a1) * (pow 8) + (nat_of_ascii8 a2).

Definition ascii32_of_nat (a : nat)  :=
  let (q,r,_,_) := divmod a (pow 16) (pow_lt_O 16) in
    (ascii16_of_nat q, ascii16_of_nat r).

Definition nat_of_ascii32 (a : ascii32) :=
  let (a1, a2) := a in
    (nat_of_ascii16 a1) * (pow 16) + (nat_of_ascii16 a2).

Definition ascii64_of_nat (a : nat)  :=
  let (q,r,_,_) := divmod a (pow 32) (pow_lt_O 32) in
    (ascii32_of_nat q, ascii32_of_nat r).

Definition nat_of_ascii64 (a : ascii64) :=
  let (a1, a2) := a in
    (nat_of_ascii32 a1) * (pow 32) + (nat_of_ascii32 a2).

(** ** natに戻せることの証明 *)
Lemma nat_ascii8_embedding : forall n,
  n < pow 8 ->
  nat_of_ascii8 (ascii8_of_nat n) = n.
Proof.
intros.
unfold nat_of_ascii8,ascii8_of_nat.
rewrite nat_ascii_embedding.
 reflexivity.

 simpl in H.
 assumption.
Qed.

Lemma nat_ascii16_embedding : forall n,
  n < pow 16 ->
  nat_of_ascii16 (ascii16_of_nat n) = n.
Proof.
intros.
unfold ascii16_of_nat, nat_of_ascii16.
destruct divmod.
rewrite (nat_ascii8_embedding q), (nat_ascii8_embedding r); try omega.
apply divmod_lt_q with (t := 8) in e;
  change (8+8) with 16; assumption.
Qed.

Lemma nat_ascii32_embedding : forall n,
  n < pow 32 ->
  nat_of_ascii32 (ascii32_of_nat n) = n.
Proof.
intros.
unfold ascii32_of_nat, nat_of_ascii32.
destruct divmod.
rewrite (nat_ascii16_embedding q), (nat_ascii16_embedding r); try omega.
apply divmod_lt_q with (t := 16) in e;
  change (16+16) with 32; assumption.
Qed.

Lemma nat_ascii64_embedding : forall n,
  n < pow 64 ->
  nat_of_ascii64 (ascii64_of_nat n) = n.
Proof.
intros.
unfold ascii64_of_nat, nat_of_ascii64.
destruct divmod.
rewrite (nat_ascii32_embedding q), (nat_ascii32_embedding r); try omega.
apply divmod_lt_q with (t := 32) in e;
  change (32+32) with 64; assumption.
Qed.

(** ** ascii8への変換 *)
Definition list_of_ascii8  (x : ascii8) :=
  x :: nil.

Definition list_of_ascii16 (p : ascii16) :=
  match p with
    (x1,x2) => (list_of_ascii8 x1) ++ (list_of_ascii8 x2)
  end.

Definition list_of_ascii32 (p : ascii32) :=
  match p with
    (x1,x2) => (list_of_ascii16 x1) ++ (list_of_ascii16 x2)
  end.

Definition list_of_ascii64 (p : ascii64) :=
  match p with
    (x1,x2) => (list_of_ascii32 x1) ++ (list_of_ascii32 x2)
  end.

Lemma list_of_ascii8_eq : forall c1 c2,
  list_of_ascii8 c1 = list_of_ascii8 c2 ->
  c1 = c2.
Proof.
intros.
unfold list_of_ascii8 in H.
inversion H.
reflexivity.
Qed.

Lemma list_of_ascii16_eq : forall c1 c2,
  list_of_ascii16 c1 = list_of_ascii16 c2 ->
  c1 = c2.
Proof.
intros.
destruct c1; destruct c2.
inversion H.
reflexivity.
Qed.

Lemma list_of_ascii32_eq : forall c1 c2,
  list_of_ascii32 c1 = list_of_ascii32 c2 ->
  c1 = c2.
Proof.
intros.
destruct c1; destruct c2.
destruct a; destruct a0; destruct a1; destruct a2.
inversion H.
reflexivity.
Qed.

Lemma list_of_ascii64_eq : forall c1 c2,
  list_of_ascii64 c1 = list_of_ascii64 c2 ->
  c1 = c2.
Proof.
intros.
destruct c1; destruct c2.
destruct a; destruct a0; destruct a1; destruct a2.
destruct a; destruct a3; destruct a0; destruct a4;
destruct a1; destruct a5; destruct a2; destruct a6.
inversion H.
reflexivity.
Qed.

(** 0でないことの証明 *)
Lemma ascii8_not_O: forall n,
  0 < n < pow 8 ->
  "000" <> ascii8_of_nat n.
Proof.
intros.
destruct H.
apply nat_ascii8_embedding in H0.
destruct (ascii8_of_nat n).
intro.
destruct b; destruct b0; destruct b1; destruct b2; destruct b3; destruct b4; destruct b5; destruct b6; inversion H1.
compute in H0.
rewrite <- H0 in H.
inversion H.
Qed.

Lemma ascii16_not_O: forall n,
  0 < n < pow 16 ->
  ("000","000") <> ascii16_of_nat n.
Proof.
intros.
unfold ascii16_of_nat.
destruct divmod.
destruct H.
intro.
inversion H1.
generalize e; intro.
apply divmod_not_O in e; auto.
decompose [or] e.
 apply ascii8_not_O in H3; auto.
 apply divmod_lt_q with (t:=8) in e0; auto.

 apply ascii8_not_O in H4; auto.
Qed.

(* ** 2^n未満なら等価性が変らないことの証明 *)
Lemma ascii8_of_nat_eq : forall n m,
  n < pow 8 ->
  m < pow 8 ->
  ascii8_of_nat n = ascii8_of_nat m ->
  n = m.
Proof.
intros.
rewrite <- (nat_ascii8_embedding n), <- (nat_ascii8_embedding m), <- H1; auto.
Qed.

Lemma ascii16_of_nat_eq : forall n m,
  n < pow 16 ->
  m < pow 16 ->
  ascii16_of_nat n = ascii16_of_nat m ->
  n = m.
Proof.
intros.
rewrite <- (nat_ascii16_embedding n), <- (nat_ascii16_embedding m), <- H1; auto.
Qed.
