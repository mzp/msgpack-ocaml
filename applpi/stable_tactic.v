Require Import List.
Require Import util_for_tactics.
Require Import chanlist.
Require Import applpi.
Require Import redseq.
Require Import stable.
Require Import datatypes_for_tactics.
Require Import conf_red_com_always_tactic.

 (** CheckUnstable *)

Ltac rep_cont_hd_in_pos lst :=
  match constr:lst with
  | nilIO => fail
  | (consIO ?X1 ?X2 ?X3 _) => constr:X2
  end.

Ltac rep_cont_hd_out_pos lst :=
  match constr:lst with
  | nilIO => fail
  | (consIO ?X1 ?X2 ?X3 _) => constr:X3
  end.

Ltac rep_cont_hd_chan lst :=
  match constr:lst with
  | nilIO => fail
  | (consIO ?X1 ?X2 ?X3 _) => constr:X1
  end.

Ltac head_cons lst :=
  match constr:lst with
  | (?X1 :: ?X2) => constr:X1
  | _ => idtac
  end.

Ltac tail_cons lst :=
  match constr:lst with
  | (?X1 :: ?X2) => constr:X2
  | nil => lst
  end.

Ltac comIO_or_comOI p w :=
  match constr:p with
  | one => apply tr_comIO with (v := w); tr_par_inout; tr_par_inout
  | _ => apply tr_comOI with (v := w); tr_par_inout; tr_par_inout
  end.

Ltac CheckTransTauL' in_p out_p v :=
  let hd_in_p := head_cons in_p in
  let hd_out_p := head_cons out_p in
  let tl_in_p := tail_cons in_p in
  let tl_out_p := tail_cons out_p in
  match constr:(hd_in_p = hd_out_p) with
  | (?X1 = ?X1) => par_left_or_right X1 tl_in_p tl_out_p v
  | (?X1 = ?X2) => comIO_or_comOI X1 v
  end
 with par_left_or_right p tl_in_p tl_out_p v :=
  match constr:p with
  | one => apply tr_parL; CheckTransTauL' tl_in_p tl_out_p v
  | _ => apply tr_parR; CheckTransTauL' tl_in_p tl_out_p v
  end.

Ltac CheckTransTauL in_pos out_pos val :=
  let in_p := eval compute in (rev in_pos) in
  let out_p := eval compute in (rev out_pos) in
  CheckTransTauL' in_p out_p val.

Ltac CheckUnstable :=
  match goal with
  |  |- (UnStable (?X1 # ?X2)) =>
      let lst := search_inout X2 in
      let hd_in_pos := rep_cont_hd_in_pos lst in
      let hd_out_pos := rep_cont_hd_out_pos lst in
      let hd_chan := rep_cont_hd_chan lst in
      let hd_val := pickup_val X2 hd_out_pos in
      let new_P := rep_cont_simp X2 hd_in_pos hd_out_pos in
      (exists (X1 # new_P); exists (epsilon hd_chan); apply red_com;
        CheckTransTauL hd_in_pos hd_out_pos hd_val)
  end.

(** CheckExistsGuard *)

Ltac CheckExistsGuard :=
  match goal with
  |  |- (Guarded ?X1) =>
      let v_opt := eval compute in (is_guarded X1 nilC) in
      let v := extract_optionT v_opt in
      (exists v; apply is_guarded_is_guarded; simpl in |- *; trivial)
  end.

(** CheckStable *)

Ltac CheckStable :=
  match goal with
  |  |- (Stable (?X1 # ?X2)) =>
      let v_opt := eval compute in (is_guarded X2 nilC) in
      let v := extract_optionT v_opt in
      (apply guarded_set_stable_weak with (l := v);
        [ apply is_guarded_is_guarded; simpl in |- *; auto
        | idtac
        | idtac
        | idtac ])
  end.