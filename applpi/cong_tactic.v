(*Load "libapplpi.v".*)

(** A tactic to prove that two processes that only differ by simple abelian monoidal rules are structurally equivalent *)

(*Goal (P,Q,R,T:proc)(Cong (parP (parP P (parP Q R)) T) (parP P (parP Q (parP R T)))).
Intros.
Apply cong_tr with (parP P (parP (parP Q R) T)).
Apply cong_assoc.
Apply cong_tr with (parP P (parP Q (parP R T))).
Apply cong_par.
Apply cong_refl.
Apply cong_assoc.
Apply cong_refl.
Abort.*)

(*Goal (P,Q,R,T:proc)(Cong (parP P (parP (parP Q R) T)) (parP P (parP Q (parP R T)))).
Intros.
Apply cong_tr with (parP P (parP Q (parP R T))).
Apply cong_par.
Apply cong_refl.
Apply cong_assoc.
Apply cong_refl.
Abort.*)

(*Goal (P,Q,R:proc)(Cong (parP P (parP Q R)) (parP R (parP P Q))).
Intros.
Abort.

Goal (P,Q,R:proc)(Cong (parP R (parP P Q)) (parP P (parP R Q))).
Intros.
Apply cong_tr with (parP (parP R P) Q).
Apply cong_sym; Apply cong_assoc.
Apply cong_tr with (parP (parP P R) Q).
Apply cong_par.
Apply cong_comm.
Apply cong_refl.
Apply cong_assoc.
Abort.*)

Require Import applpi.
Require Import cong.

Ltac flatten_aux P sub :=
  match constr:P with
  | (parP ?X1 ?X2) =>
      let sub' := flatten_aux X2 sub in
      flatten_aux X1 sub'
  | ?X1 => constr:(parP X1 sub)
  end.

Ltac flatten P :=
  match constr:P with
  | (parP ?X1 ?X2) => let sub' := flatten X2 in
                      flatten_aux X1 sub'
  | ?X1 => constr:X1
  end.

Ltac flatten_left' :=
  match goal with
  |  |- (Cong (parP (parP ?X1 ?X2) ?X3) _) =>
      apply cong_tr with (parP X1 (parP X2 X3));
       [ apply cong_assoc | flatten_left' ]
  |  |- (Cong (parP ?X1 ?X2) (parP ?X1 ?X3)) =>
      apply cong_par; [ apply cong_refl | flatten_left' ]
  |  |- (Cong ?X1 ?X1) => apply cong_refl
  end.

Ltac flatten_left :=
  match goal with
  |  |- (Cong ?X1 ?X2) =>
      let tmp := flatten X1 in
      (apply cong_tr with tmp; [ flatten_left' | idtac ])
  end.

Lemma cong_assoc_r :
 forall P Q R, Cong (parP P (parP Q R)) (parP (parP P Q) R).
intros.
apply cong_sym.
apply cong_assoc.
Qed.

Ltac flatten_right' :=
  match goal with
  |  |- (Cong _ (parP (parP ?X1 ?X2) ?X3)) =>
      apply cong_tr with (parP X1 (parP X2 X3));
       [ flatten_right' | apply cong_assoc_r ]
  |  |- (Cong (parP ?X1 ?X2) (parP ?X1 ?X3)) =>
      apply cong_par; [ apply cong_refl | flatten_right' ]
  |  |- (Cong ?X1 ?X1) => apply cong_refl
  end.

Ltac flatten_right :=
  match goal with
  |  |- (Cong ?X1 ?X2) =>
      let tmp := flatten X2 in
      (apply cong_tr with tmp; [ idtac | flatten_right' ])
  end.

Ltac rotate_left :=
  match goal with
  |  |- (Cong (parP ?X1 ?X2) _) =>
      apply cong_tr with (parP X2 X1); [ apply cong_comm | idtac ];
       flatten_left
  end.

Ltac ProcCong2 :=
  match goal with
  |  |- (Cong (parP ?X1 ?X2) (parP ?X1 ?X3)) =>
      apply cong_par; [ apply cong_refl | ProcCong2 ]
  |  |- (Cong (parP ?X1 ?X2) (parP ?X3 ?X4)) => rotate_left; ProcCong2
  |  |- (Cong ?X1 ?X1) => apply cong_refl
  end.

(*Goal (P,Q,R,T:proc)(Cong (parP (parP P (parP Q R)) T) 
(parP (parP R T) (parP P Q))).
Intros.
flatten_left.
flatten_right.
ProcCong2.
Abort.*)

Ltac elim_zero P :=
  match constr:P with
  | (parP zeroP ?X1) => elim_zero X1
  | (parP ?X1 zeroP) => elim_zero X1
  | (parP ?X1 ?X2) => elim_zero' X1 X2
  | ?X1 => constr:X1
  end
 with elim_zero' pl pr :=
  let pl' := elim_zero pl in
  match constr:pl' with
  | zeroP => elim_zero_pl_zeroP pr
  | ?X1 => elim_zero_pl_not_zeroP X1 pr
  end
 with elim_zero_pl_zeroP pr :=
  let pr' := elim_zero pr in
  match constr:pr' with
  | zeroP => constr:zeroP
  | ?X1 => constr:X1
  end
 with elim_zero_pl_not_zeroP pl pr :=
  let pr' := elim_zero pr in
  match constr:pr' with
  | zeroP => pl
  | ?X1 => constr:(parP pl X1)
  end.

Lemma elim_zero_l : forall P Q, Cong P Q -> Cong (parP zeroP P) Q.
intros.
apply cong_tr with P.
apply cong_sym.
apply cong_tr with (parP P zeroP).
apply cong_zero.
apply cong_comm.
auto.
Qed.

Lemma elim_zero_l2 : forall P Q, Cong P Q -> Cong (parP P zeroP) Q.
intros.
apply cong_sym.
apply cong_tr with P.
apply cong_sym; auto.
apply cong_zero.
Qed.

Lemma elim_zero_r : forall P Q, Cong P Q -> Cong P (parP zeroP Q).
intros.
apply cong_tr with Q.
auto.
apply cong_tr with (parP Q zeroP).
apply cong_zero.
apply cong_comm.
Qed.

Lemma elim_zero_r2 : forall P Q, Cong P Q -> Cong P (parP Q zeroP).
intros.
apply cong_tr with Q.
auto.
apply cong_zero.
Qed.

Ltac elim_zero_tactic :=
  match goal with
  |  |- (Cong ?X1 ?X1) => apply cong_refl
  |  |- (Cong (parP zeroP ?X1) ?X2) => apply elim_zero_l; elim_zero_tactic
  |  |- (Cong (parP ?X1 zeroP) ?X2) => apply elim_zero_l2; elim_zero_tactic
  |  |- (Cong ?X1 (parP zeroP ?X2)) => apply elim_zero_r; elim_zero_tactic
  |  |- (Cong ?X1 (parP ?X2 zeroP)) => apply elim_zero_r2; elim_zero_tactic
  |  |- (Cong (parP ?X1 ?X2) (parP ?X3 ?X4)) =>
      apply cong_par; [ elim_zero_tactic | elim_zero_tactic ]
  end.

Ltac elim_zero_t :=
  match goal with
  |  |- (Cong ?X1 ?X2) =>
      let tmp := elim_zero X1 in
      let tmp2 := elim_zero X2 in
      (apply cong_tr with tmp;
        [ elim_zero_tactic
        | apply cong_tr with tmp2; [ idtac | elim_zero_tactic ] ])
  end.

(*Goal (P,Q,R,T:proc)(Cong (parP (parP R T) (parP P Q))
(parP (parP zeroP (parP R T)) (parP P Q))).
Intros.
elim_zero_t.
Abort.

Goal (P,Q,R,T:proc)(Cong (parP (parP P (parP Q R)) T) 
(parP (parP (parP zeroP R) T) (parP P Q))).
Intros.
elim_zero_t.
flatten_left.
flatten_right.
ProcCong2.
Abort.

Goal (P:proc)(Cong P (parP P zeroP)).
Intros.
elim_zero_t.
ProcCong2.
Abort.

Goal (Cong zeroP (parP (parP zeroP zeroP) zeroP)).
elim_zero_t.
ProcCong2.
Abort.*)

Ltac ProcCong :=
  match goal with
  |  |- (Cong ?X1 ?X2) =>
      elim_zero_t; flatten_left; flatten_right; ProcCong2
  end.








