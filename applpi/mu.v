Require Import Classical.
Require Import util.
Require Import applpi.
Require Import redseq.
Require Import logic.
Require Import logic_prop.
Require Import logic_tactic2.
Require Import logic_extensions.

Set Implicit Arguments.

 (** fixpoint theory *)

Definition imply_pred p q : Prop :=
  forall P, P |=t p -> P |=t q.

Definition is_monotonic F : Prop :=
  forall p q, imply_pred p q -> imply_pred (F p) (F q).

Lemma MU_is_least :
 forall F,
 is_monotonic F ->
 forall X,
 (forall P, tsat (F X) P -> tsat X P) ->
 forall Q, Q |=t (MU F) -> Q |=t X.
intros.
generalize (MU_sat_inv H1); intro.
apply H2.
intros.
apply H0.
auto.
Qed.

Lemma MU_is_prefixedpoint :
 forall F, is_monotonic F -> imply_pred (F (MU F)) (MU F).
intros.
red in H.
red in |- *.
intros.
apply MU_sat.
intros.
apply H1.
cut (imply_pred (F (MU F)) (F p)).
intro.
unfold imply_pred in H2.
apply H2.
auto.
(* prove cut *)
apply H.
red.
apply MU_is_least.
unfold is_monotonic in |- *; auto.
auto.
Qed.

Definition eq_pred p q :=
  forall P, (tsat p P -> tsat q P) /\ (tsat q P -> tsat p P).

Lemma MU_is_fix :
 forall F, is_monotonic F -> eq_pred (MU F) (F (MU F)).
intros.
unfold eq_pred in |- *.
intro.
split.
(* (MU F) <= (F (MU F)) *)
intro.
(* we have (Mu F), we want to prove (F (Mu F)) *)
generalize (MU_sat_inv H0); intro.
(* by definition of (Mu F), it is enough to prove that (F (Mu F)) contains its image by F *)
apply (H1 (F (MU F))).
(* we have to prove (F (F (Mu F)))->(F (Mu F)), i.e. (F (Mu F))->(Mu F) by monotonicity, true since (Mu F)
is a pre-fixed point *)
intro.
apply H.
apply MU_is_prefixedpoint.
auto.
(* (F (MU F)) <= (MU F)*)
apply MU_is_prefixedpoint.
auto.
Qed.

Unset Implicit Arguments.

Lemma contra :
 forall (T : Type) (p q : T -> Prop),
 (forall Q : T, p Q -> q Q) -> forall Q : T, ~ q Q -> ~ p Q.
intros.
intro.
apply H0.
apply H.
auto.
Qed.

Inductive Redsp (phi : state -> Prop) : state -> state -> Type :=
  | redsp_b : forall P Q : state, Red P Q /\ phi P /\ phi Q -> Redsp phi P Q
  | redsp_i :
      forall P Q R : state,
      Redsp phi P Q -> Red Q R /\ phi R -> Redsp phi P R.

Inductive Redsp' (phi : state -> Prop) : state -> state -> Type :=
  | redsp_b' :
      forall P Q : state, Red P Q /\ phi P /\ phi Q -> Redsp' phi P Q
  | redsp_i' :
      forall P Q R : state,
      Red P Q /\ phi P -> Redsp' phi Q R -> Redsp' phi P R.

Lemma redsp'_trans :
 forall (phi : state -> Prop) (P Q R : state),
 Redsp' phi P Q -> Redsp' phi Q R -> Redsp' phi P R.
intros.
induction X.
apply redsp_i' with (Q := Q).
decompose [and] a; clear a.
auto.
auto.
apply redsp_i' with (Q := Q).
auto.
apply IHX.
auto.
Qed.

Lemma redsp_redsp' :
    forall (phi : state -> Prop) (P Q : state),
    Redsp phi P Q -> Redsp' phi P Q.
intros.
elim X.
intros.
decompose [and] a;clear a.
apply redsp_b'.
auto.
intros.
inversion r.
clear H0 H1 P1 Q1.
decompose [and] H;clear H.
apply redsp_i' with (Q:=Q0).
auto.
apply redsp_b'.
inversion_clear a.
auto.
clear H0 H1 P1 R0.
assert (Redsp' phi Q0 R).
apply redsp_b'.
inversion_clear a.
inversion_clear H. 
auto.
apply redsp'_trans with (Q:=Q0).
auto.
auto.
Qed.

(** equivalence between the native mustev predicate and the fixpoint version *)

Lemma mustev_mu :
 forall (p : tform) (P : state), tsat (MUSTEV p) P -> tsat (MUSTEV_ALT p) P.
intros.
unfold MUSTEV_ALT in |- *.
apply MU_sat.
intros.
apply NNPP.
intro.

(* given the hypothesis ~(sat p0 P) and the hypothesis H0, we show 
~(sat p P) and (NEXT (NEG p0) P) *)

generalize
 (contra state
    (fun Q : state => tsat (ORT p (ANDT (NEGT STABLE) (MUST_NEXT p0))) Q)
    (fun Q : state => tsat p0 Q) H0); intro.
generalize (H2 _ H1); clear H2; intro.
generalize (not_ORT_ANDT H2); clear H2; intro.
generalize (ANDT_sat_inv H2); clear H2; intro.
inversion_clear H2.
generalize (NEGT_ANDT_ORT H4); clear H4; intro.
generalize (ORT_sat_inv H2); clear H2; intro.
inversion_clear H2.
generalize (NEGT_NEGT H4); clear H4; intro.
generalize (MUSTEV_sat_inv H); intro.

generalize
 (H4 (fun x : nat => match x with
                     | O => SomeT _ P
                     | _ => NoneT state
                     end) (refl_equal (SomeT _ P))); 
 intro.
cut
 (isMaxRedSeq
    (fun x : nat =>
     match x with
     | O => SomeT state P
     | S _ => NoneT state
     end)).
intro.
generalize (H5 H6); clear H5 H6; intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H5.
induction x0.
injection H6; intro.
rewrite <- H5 in H7.
generalize (NEGT_sat_inv H3); intro.
apply H8; auto.
discriminate H6.
red in |- *.
split.
red in |- *.
split.
case n.
intros.
auto.
intros.
discriminate H6.
auto.
intros.
induction n.
injection H6; intro.
rewrite <- H8.
generalize (STABLE_sat_inv H2); intro.
auto.
discriminate H6.
generalize (NEGT_sat_inv H4); clear H4; intro.
apply H2; clear H2.
apply MUST_NEXT_sat.
intros.
apply NNPP; intro.
generalize (conj H2 H4); clear H2 H4; intro.
rename Q into P'.

(* to solve the probleme it is enough to find an infinite
sequence of processes such that p0 nevers holds *)

cut
 (exists PS : stateSeq,
    PS 0 = SomeT _ P /\
    (forall n : nat,
     exists Q0 : state,
       (exists Q : state,
          PS n = SomeT _ Q0 /\
          PS (S n) = SomeT _ Q /\ Red Q0 Q /\ ~ tsat p0 Q0))).
intro.
inversion_clear H4.
inversion_clear H5.
generalize (MUSTEV_sat_inv H); clear H; intro.
generalize (H x); intro.
assert (isMaxRedSeq x).
red in |- *.
split.
red in |- *.
split.
intros.
generalize (H6 n); intro.
inversion_clear H8.
inversion_clear H9.
decompose [and] H8; clear H8.
left.
exists x1.
rewrite H7 in H9; injection H9; intro.
rewrite H8; auto.
intro.
generalize (H6 n).
intro X; inversion_clear X.
inversion_clear H8.
decompose [and] H9; clear H9.
rewrite H8 in H7; discriminate H7.
intros.
generalize (H6 n).
intro X; inversion_clear X.
inversion_clear H9.
decompose [and] H10; clear H10.
rewrite H8 in H12; discriminate H12.
generalize (H5 H4 H7); intro.
inversion_clear H8.
inversion_clear H9.
inversion_clear H8.
generalize (H6 x1); intro.
inversion_clear H8.
inversion_clear H11.
decompose [and] H8; clear H8.

(* comme dans le preambule, on derive ~(p x3) de ~(p0 x3) *)

generalize
 (contra state
    (fun Q : state => tsat (ORT p (ANDT (NEGT STABLE) (MUST_NEXT p0))) Q)
    (fun Q : state => tsat p0 Q) H0); intro.
generalize (H8 x2 H15); clear H8; intro.
generalize (not_ORT_ANDT H8); clear H8; intro.
generalize (ANDT_sat_inv H8); clear H8; intro.
inversion_clear H8.
rewrite H9 in H11; injection H11; intros.
rewrite H8 in H10.
generalize (NEGT_sat_inv H14); clear H14; intro.
apply H14; auto.

cut
 (ex
    (fun PS : nat -> state =>
     PS 0 = P /\
     (forall n : nat, Red (PS n) (PS (S n)) /\ ~ tsat p0 (PS (S n))))).
intros X.
elim X.
intros x p1.
exists (fun k : nat => SomeT _ (x k)).
split.
inversion_clear p1.
rewrite H4; auto.
intro.
exists (x n).
exists (x (S n)).
split; auto.
split; auto.
induction n.
inversion_clear p1.
generalize (H5 0); intro.
inversion_clear H6.
split; auto.
rewrite H4; auto.
inversion_clear p1.
generalize (H5 (S n)); intro.
split.
inversion_clear H6.
auto.
generalize (H5 n); intro.
inversion_clear H7.
auto.

(* on peut ecrire une fonction correspondant a la reduction sequence desiree
a partir d'une preuve de l'existence d'un successeur adequat pour tout etat
x atteint vie une reduction sequence adequate *)

Fixpoint mustev_mu_g (phi : state -> Prop) (seed0 seed1 : state)
 (H : Redsp phi seed0 seed1)
 (X0 : forall (x : state) (Px : Redsp phi seed0 x),
       sigT (fun y : state => Red x y /\ phi y)) (k : nat) {struct k} :
 sigT (fun y : state => Redsp phi seed0 y) :=
  match k with
  | O => existT (fun x => Redsp phi seed0 x) seed1 H
  | S n =>
      match mustev_mu_g phi seed0 seed1 H X0 n with
      | existT m M =>
          match X0 m M with
          | existT l L =>
              existT (fun x => Redsp phi seed0 x) l (redsp_i _ _ _ _ M L)
          end
      end
  end.

Definition mustev_mu_h (phi : state -> Prop) (seed0 seed1 : state)
  (H : Redsp phi seed0 seed1)
  (X0 : forall (x : state) (Px : Redsp phi seed0 x),
        sigT (fun y : state => Red x y /\ phi y)) (n : nat) : state :=
  match mustev_mu_g _ _ _ H X0 n with
  | existT m _ => m
  end.

cut
 (forall (x : state) (H : Redsp (fun x : state => ~ tsat p0 x) P x),
  sigT (fun y : state => Red x y /\ ~ tsat p0 y)).
intro.
assert (Redsp (fun x : state => ~ tsat p0 x) P P').
apply redsp_b.
inversion_clear H2.
auto.
exists
 (fun j : nat =>
  match j with
  | O => P
  | S t => mustev_mu_h (fun x : state => ~ tsat p0 x) P P' X0 X t
  end).
split.
auto.
intro.
induction n.
unfold mustev_mu_h in |- *; simpl in |- *.
auto.
unfold mustev_mu_h in |- *; simpl in |- *.
elim (mustev_mu_g (fun x : state => ~ tsat p0 x) P P' X0 X n); intro.
intro.
elim (X x p1); intro.
tauto.

(* maintenant on doit prouver que tout etat atteint par une sequence d'etat
ne verifiant pas p0 peut encore se prolonger *)

intros.
assert (Redsp (fun x : state => ~ tsat p x) P x).
induction H4.
apply redsp_b.
split.
decompose [and] a; clear a.
auto.
split.
apply (NEGT_sat_inv H3).
decompose [and] a; clear a.
generalize
 (contra state
    (fun Q : state => tsat (ORT p (ANDT (NEGT STABLE) (MUST_NEXT p0))) Q)
    (fun Q : state => tsat p0 Q) H0); intro.
generalize (H5 Q H7); clear H5; intro.
generalize (not_ORT_ANDT H5); clear H5; intro.
generalize (ANDT_sat_inv H5); clear H5; intro.
inversion_clear H5.
apply (NEGT_sat_inv H8).
generalize (IHRedsp H H1 H3 H2); intro.
apply redsp_i with (Q := Q).
auto.
assert (tsat p R \/ ~ tsat p R).
apply classic.
inversion_clear H5.
generalize (H0 R); intro.
assert (tsat (ORT p (ANDT (NEGT STABLE) (MUST_NEXT p0))) R).
apply ORT_sat.
left; auto.
generalize (H5 H7); intro.
inversion_clear a.
generalize (H10 H8); contradiction.
inversion_clear a.
auto.

assert (exists y : state, Red x y /\ ~ tsat p0 y).
apply NNPP.
intro.
generalize (not_ex_all_not _ (fun y => Red x y /\ ~ tsat p0 y) H5); clear H5;
 intro.
assert (forall n : state, Red x n -> tsat p0 n).
intro.
generalize (H5 n); intro.
generalize (not_and_or _ _ H6); intro.
generalize (or_to_imply _ _ H7); intro.
intros.
apply NNPP.
tauto.
cut (~ tsat STABLE x).
intro.
assert (~ tsat STABLE x /\ tsat (MUST_NEXT p0) x).
split.
auto.
apply MUST_NEXT_sat.
auto.
assert (tsat (ORT p (ANDT (NEGT STABLE) (MUST_NEXT p0))) x).
apply ORT_sat.
right.
apply ANDT_sat.
split.
apply NEGT_sat.
intuition.
intuition.
generalize (H0 _ H9); intro.
inversion H4.
decompose [and] H11; clear H11.
apply H17.
auto.
inversion_clear H11.
apply H15.
auto.
intro.

(* on montre par contradiction que x ne peut etre stable parce sinon
on peut construire une sequence le long de laquelle p n'est jamais verifie *)

Fixpoint mustev_mu_f (phi : state -> Prop) (P R : state)
 (H : Redsp' (fun x : state => ~ phi x) P R) (n : nat) {struct H} :
 optionT state :=
  match H with
  | redsp_b' p q redpq =>
      match n with
      | O => SomeT _ p
      | S O => SomeT _ q
      | S (S _) => NoneT state
      end
  | redsp_i' p q r redpq redqr =>
      match n with
      | O => SomeT _ p
      | S O => SomeT _ q
      | S (S n) => mustev_mu_f phi _ _ redqr (S n)
      end
  end.

generalize (MUSTEV_sat_inv H); clear H; intro.
assert (Redsp' (fun x : state => ~ tsat p x) P x).
apply redsp_redsp'.
auto.
generalize (H (mustev_mu_f (fun w : state => tsat p w) _ _ X0)); intro.
assert (mustev_mu_f (fun w : state => tsat p w) _ _ X0 0 = SomeT state P).
elim X0.
simpl in |- *.
auto.
simpl in |- *.
auto.
assert (isRedSeq (mustev_mu_f (fun w : state => tsat p w) _ _ X0)).
elim X0.
simpl in |- *.
intros.
red in |- *.
intro.
case n.
split.
intros.
left; exists Q.
split; auto.
injection H10; intros.
rewrite <- H11.
decompose [and] a; clear a.
induction Q.
auto.
intro Z; discriminate Z.
intros.
split.
intros.
auto.
auto.
intros.
assert
 (exists f0 : state,
    mustev_mu_f (fun w : state => tsat p w) _ _ r 0 = SomeT _ f0 /\ Red P0 f0).
exists Q.
split.
elim r.
simpl in |- *.
auto.
simpl in |- *.
auto.
inversion_clear a.
auto.
generalize (lem_RedSeq_is_prefix _ H10 _ H11); intros.

assert
 (forall n : nat,
  mustev_mu_f (fun w : state => tsat p w) _ _
    (redsp_i' (fun x0 : state => ~ tsat p x0) P0 Q R a r) n =
  (fun j : nat =>
   match j with
   | O => SomeT state P0
   | S k => mustev_mu_f (fun w : state => tsat p w) Q R r k
   end) n).

intro.
induction n.
simpl in |- *.
auto.
induction n.
simpl in |- *.
elim r.
simpl in |- *.
auto.
simpl in |- *.
auto.
simpl in |- *.
auto.

generalize
 (extension _ _ _
    (fun j : nat =>
     match j with
     | O => SomeT state P0
     | S k => mustev_mu_f (fun w : state => tsat p w) Q R r k
     end) H13); intro.
rewrite H14.
auto.
assert
 (exists n : nat,
    (exists x' : state,
       mustev_mu_f (fun w : state => tsat p w) P x X0 n = SomeT _ x' /\
       Stable x' /\
       (forall m : nat,
        n < m -> mustev_mu_f (fun w : state => tsat p w) P x X0 m = NoneT _))).
assert
 (exists n : nat,
    mustev_mu_f (fun w : state => tsat p w) P x X0 n = SomeT state x).
elim X0.
simpl in |- *.
intros.
exists 1.
auto.
simpl in |- *.
intros.
inversion_clear H11.
exists (S x0).
induction x0.
generalize H12; clear H12.
elim r.
simpl in |- *.
auto.
simpl in |- *.
auto.
auto.
inversion_clear H11.
exists x0.
exists x.
split; auto.
split.
apply (STABLE_sat_inv H7).
intros.
red in H11.
generalize (STABLE_sat_inv H7); clear H7; intro.
generalize (isRedSeq_stable_none _ H10 _ _ (conj H12 H7)); intro.
assert (x0 < m).
red in |- *.
auto.
apply H13.
auto.
generalize (redseq_is_maxredseq _ H10 H11); intro.
generalize (H _ H9 H12); intro.
inversion_clear H13.
inversion_clear H14.
inversion_clear H13.
assert
 (forall (w : nat) (W : state),
  mustev_mu_f (fun w : state => tsat p w) P x X0 w = SomeT state W ->
  ~ tsat p W).
elim X0.
simpl in |- *.
intros.
induction w.
injection H13; intro.
rewrite <- H16.
decompose [and] a; clear a.
auto.
induction w.
injection H13; intros.
rewrite <- H16; decompose [and] a; clear a.
auto.
discriminate H13.
simpl in |- *.
intros.
induction w.
injection H16; intros.
rewrite <- H17.
inversion_clear a.
auto.
induction w.
assert (mustev_mu_f (fun w : state => tsat p w) Q R r 0 = SomeT state Q).
elim r.
simpl in |- *.
auto.
simpl in |- *.
auto.
generalize (H13 _ _ H17); intro.
injection H16; intros.
rewrite <- H19; auto.
apply (H13 _ _ H16).
generalize (H13 _ _ H14); intro.
apply H16.
auto.

(* il existe forcement un y qui suit x et qui ne verifie pas p0 *)

apply EXT_sigT with (P := fun y : state => Red x y /\ ~ tsat p0 y).
auto.
Qed.

