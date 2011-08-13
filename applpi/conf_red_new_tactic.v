Require Import List.
Require Import util_for_tactics.
Require Import applpi.
Require Import set.
Require Import logic.
Require Import conf_red.
Require Import datatypes_for_tactics.
Require Import conf_red_com_always_tactic.

 (*** 
   * (search_nul 'eps P) optionally returns one nul subprocess of P
   * (pickup_nul_cont P p) returns the continuation of the nul subprocess
   *  at position p
   * (rep_nul_cont_simp P new_c nul_pos) returns the process obtained
   *  from P by reducing the nul subprocess at position nul_pos using
   *  new_c channel
   ***)

Ltac search_nul cur P :=
  match constr:P with
  | (nuPl ?X1) => constr:(Some cur)
  | (parP ?X1 ?X2) =>
      let tmp := search_nul (one :: cur) X1 in
      test_option2 tmp ltac:(search_nul (two :: cur) X2)
  | zeroP => constr:(None (A:=cur))
  | (?X1 ?? ?X2) => constr:(None (A:=pos))
  | (?X1 ??* ?X2) => constr:(None (A:=pos))
  | (?X1 << ?X2 >> ?X3) => constr:(None (A:=pos))
  | (nuP ?X1) => constr:(None (A:=pos))
  | _ => constr:(None (A:=pos))
  end. (* Instead of Fail, so that we can process processes with variable in lieu of subprocesses *)

Ltac pickup_nul_cont' P pos :=
  match constr:pos with
  | nil => pickup_nul_cont_atom P
  | (?X1 :: ?X2) => pickup_nul_cont'' X1 X2 P
  end
 with pickup_nul_cont'' hd tl P :=
  match constr:hd with
  | one => pickup_nul_cont_one P tl
  | two => pickup_nul_cont_two P tl
  end
 with pickup_nul_cont_one P tl :=
  match constr:P with
  | (parP ?X1 ?X2) => pickup_nul_cont' X1 tl
  | _ => fail
  end
 with pickup_nul_cont_two P tl :=
  match constr:P with
  | (parP ?X1 ?X2) => pickup_nul_cont' X2 tl
  | _ => fail
  end
 with pickup_nul_cont_atom P :=
  match constr:P with
  | (nuPl ?X1) => constr:X1
  | _ => fail
  end.

Ltac pickup_nul_cont P p :=
  let rev_p := eval compute in (rev p) in
  pickup_nul_cont' P rev_p.

Ltac rep_nul_cont_simp P new_c nul_pos :=
  let nul_cont := pickup_nul_cont P nul_pos in
  let new_nul := eval cbv beta iota zeta in (nul_cont new_c) in
  subst_cont P new_nul nul_pos.

(***
   * (ConfRedNewL c) where c is supposed to be a fresh linearized
   *  channel applies to (sat (FMUSTEV ?1) ?2#?3) goals, it picks up
   *  one nul subprocess, performs the reduction and proves it correct
   *
   * This tactic performs ok even if the interface of the process is
   * not completely visible (there may be variables in lieu of processes)
   ***)

Ltac ConfRedNewL new_c :=
match goal with
  | |- (tsat (FMUSTEV ?A) (?B#?C))  =>
let some_pos := (search_nul eps C) in
let nul_pos := (extract_option some_pos) in
let new_P := (rep_nul_cont_simp C new_c nul_pos) in
eapply conf_red_new with (P':=new_P) (c:=new_c);
[(apply red_new; [tr_nu | auto]) | auto | idtac | idtac | idtac | idtac]
end.

Ltac ConfRedNewL_set c :=
ConfRedNewL c;
[apply chanlist_fresh; auto | idtac | idtac].

Ltac search_nu cur P :=
  match constr:P with
  | (nuP ?X1) => constr:(Some cur)
  | (parP ?X1 ?X2) =>
      let tmp := search_nu (one :: cur) X1 in
      test_option2 tmp ltac:(search_nu (two :: cur) X2)
  | zeroP => constr:(None (A:=cur))
  | (?X1 ?? ?X2) => constr:(None (A:=pos))
  | (?X1 ??* ?X2) => constr:(None (A:=pos))
  | (?X1 << ?X2 >> ?X3) => constr:(None (A:=pos))
  | (nuPl ?X1) => constr:(None (A:=pos))
  | _ => constr:(None (A:=pos))
  end.

Ltac pickup_nu_cont' P p :=
  match constr:p with
  | nil => pickup_nu_cont_atom P
  | (?X1 :: ?X2) => pickup_nu_cont'' X1 X2 P
  end
 with pickup_nu_cont'' hd tl P :=
  match constr:hd with
  | one => pickup_nu_cont_one P tl
  | two => pickup_nu_cont_two P tl
  end
 with pickup_nu_cont_one P tl :=
  match constr:P with
  | (parP ?X1 ?X2) => pickup_nu_cont' X1 tl
  | _ => fail
  end
 with pickup_nu_cont_two P tl :=
  match constr:P with
  | (parP ?X1 ?X2) => pickup_nu_cont' X2 tl
  | _ => fail
  end
 with pickup_nu_cont_atom P :=
  match constr:P with
  | (nuP ?X1) => constr:X1
  | _ => fail
  end.

Ltac pickup_nu_cont P p :=
  let rev_p := eval compute in (rev p) in
  pickup_nu_cont' P rev_p.

Ltac rep_nu_cont_simp P new_c nu_pos :=
  let nu_cont := pickup_nu_cont P nu_pos in
  let new_nu := eval cbv beta iota zeta in (nu_cont new_c) in
  subst_cont P new_nu nu_pos.

Ltac ConfRedNew new_c :=
match goal with
  | |- (tsat (FMUSTEV ?A) (?B#?C)) =>
let some_pos := (search_nu eps C) in
let nu_pos := (extract_option some_pos) in
let new_P := (rep_nu_cont_simp C new_c nu_pos) in
eapply conf_red_new with (P':=new_P) (c:=new_c);
[apply red_new; [tr_nu | auto] | auto | idtac | idtac | idtac | idtac ]
end.

Ltac ConfRedNew_set c :=
ConfRedNew c;
[apply chanlist_fresh; auto | idtac | idtac].

