Require Import util.
Require Import chan.
Require Import set.
Require Import applpi.
Require Import logic.

 (** miscellaneous meta-level functions used in tactics *)

Ltac test_chan c d :=
  match constr:(c &&& d) with
  | (?X1 &&& ?X1) => idtac
  | (?X1 &&& ?X2) => fail
  end.


Ltac test_option2 v no_cont :=
  match constr:v with
  | (Some ?X2) => v
  | None => no_cont
  end.

Ltac extract_option v :=
  match constr:v with
  | (Some ?X2) => constr:X2
  | _ => fail
  end.

Ltac extract_optionT v :=
  match constr:v with
  | (SomeT ?X1 ?X2) => constr:X2
  | _ => fail
  end.


(** automatic inference of a nu transition *)

Ltac tr_new2 :=
  match goal with
  |  |- (Trans (nuP ?X1) (NewL ?X2) ?X3) => apply (tr_new X1)
  end.

Ltac tr_newl2 :=
  match goal with
  |  |- (Trans (nuPl ?X1) (NewL ?X2) ?X3) => apply (tr_newl X1)
  end.

Ltac tr_nu :=
  match goal with
  |  |- (Trans (nuP ?X1) (NewL ?X2) ?X3) => tr_new2
  |  |- (Trans (nuPl ?X1) (NewL ?X2) ?X3) => tr_newl2
  |  |- (Trans ?X1 (NewL ?X2) ?X3) => first
  [ apply tr_parR; tr_nu | apply tr_parL; tr_nu | fail ]
  end.

(** macros to generate fresh channels *)

Ltac ChooseFreshL typ :=
  match goal with
  |  |- (tsat ?X1 (?X2 # ?X3)) =>
      generalize (choose_freshl typ X2); intro _X; elim _X; clear _X
  end.

Ltac ChooseFresh typ :=
  match goal with
  |  |- (tsat ?X1 (?X2 # ?X3)) =>
      generalize (choose_fresh typ X2); intro _X; elim _X; clear _X
  end.

Ltac ChooseFreshL_set typ name :=
  match goal with
  | id0:(ChanList_is_set ?X2) |- (tsat ?X1 (?X2 # ?X3)) =>
      elim (choose_freshl typ X2); intro name; intro _X;
       generalize (chanlist_is_set_extend X2 id0 _ _ _ _X);
       clear _X id0; intro id0
  end.

Ltac ChooseFresh_set typ name :=
  match goal with
  | id0:(ChanList_is_set ?X2) |- (tsat ?X1 (?X2 # ?X3)) =>
      elim (choose_fresh typ X2); intro name; intro _X;
       generalize (chanlist_is_set_extend X2 id0 _ _ _ _X);
       clear _X id0; intro id0
  end.

(** clean_zero simply erases the inert subprocesses of the goal under the assumption that the formula to be proved does not discriminate structurally congruent processes *)

(*Fixpoint elim_zero_proc [P:proc] : proc :=
Cases P of
  (parP zeroP Q) => (elim_zero_proc Q)
| (parP Q zeroP) => (elim_zero_proc Q)
| (parP Q R) => (parP (elim_zero_proc Q) (elim_zero_proc R))
| _ => P
end.*)

(*Tactic Definition clean_zero :=
Match Context With
[ |- (tsat ?1 ?2#?3) ] ->
Let tmp=(Eval Cbv Beta Delta [elim_zero_proc] Iota Zeta in (elim_zero_proc ?3)) In*)
(* we need to unfold the function but not other functions inside the term! *)
(*Apply cong_resp_sat with tmp;
[cong_ind | ProcCong | Idtac].*)








