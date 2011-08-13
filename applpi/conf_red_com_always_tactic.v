Require Import List.
Require Import listT.
Require Import chan.
Require Import chanlist.
Require Import applpi.
Require Import util_for_tactics.
Require Import datatypes_for_tactics.

 (***
   * (search_inout P) returns the list of reacting in/out processes in P,
   *  search_inout' looks for in processes and search_out looks for corresponding
   *  out processes
   * (subst_cont P Q p) replaces the subprocess at position p in P with
   *  the process Q
   * (pickup_val P p) picks up the value of the output process at position p
   *  in P
   * (pickup_out_cont P p) and (pickup_in_cont P p) pick up the continuations
   * (rep_cont_simp P in_pos out_pos) returns the process resulting from
   *  the communication between subprocesses at positions in_pos and out_pos
   * (rep_cont P lst) returns the list of processes that may result from
   *  an intra-communication in P
   ***)

Ltac search_out c p lst cur P :=
  match constr:P with
  | (?X1 << ?X2 >> ?X3) =>
      test_chan2 X1 c (consIO c p cur lst) lst
  | (OutAtom ?X1 ?X2) =>
      test_chan2 X1 c (consIO c p cur lst) lst
  | (parP ?X1 ?X2) =>
      let l1 := search_out c p lst (one :: cur) X1 in
      search_out c p l1 (two :: cur) X2
  | zeroP => lst
  | (?X1 ?? ?X2) => lst
  | (InAtom ?X1) => lst
  | (?X1 ??* ?X2) => lst
  | (nuP ?X1) => fail
  | (nuPl ?X1) => fail
  | _ =>
       (* we Fail if the process contains some nu, there is no strong reason for 
  enforcing that behavior *)
  lst
  end. (* instead of Fail so that we can process processes 
represented by a variable *)

Ltac search_inout' lst cur whole P :=
  match constr:P with
  | (?X1 ?? ?X2) =>
      let tmp := search_out X1 cur nilIO eps whole in
      eval compute in (appP tmp lst)
  | (InAtom ?X1) =>
      let tmp := search_out X1 cur nilIO eps whole in
      eval compute in (appP tmp lst)
  | (?X1 ??* ?X2) =>
      let tmp := search_out X1 cur nilIO eps whole in
      eval compute in (appP tmp lst)
  | (parP ?X1 ?X2) =>
      let l1 := search_inout' lst (one :: cur) whole X1 in
      search_inout' l1 (two :: cur) whole X2
  | zeroP => lst
  | (?X1 << ?X2 >> ?X3) => lst
  | (OutAtom ?X1 ?X2) => lst
  | (nuP ?X1) => fail
  | (nuPl ?X1) => fail
  | _ => lst
  end.

Ltac search_inout P := search_inout' nilIO eps P P.

Ltac subst_cont' P Q p :=
  match constr:p with
  | nil => Q
  | (?X1 :: ?X2) => subst_cont'' X1 X2 P Q
  end
 with subst_cont'' hd tl P Q :=
  match constr:hd with
  | one => subst_cont_one P Q tl
  | two => subst_cont_two P Q tl
  end
 with subst_cont_one P Q tl :=
  match constr:P with
  | (parP ?X3 ?X4) =>
      let tmp := subst_cont' X3 Q tl in
      constr:(parP tmp X4)
  | _ => fail
  end
 with subst_cont_two P Q tl :=
  match constr:P with
  | (parP ?X3 ?X4) =>
      let tmp := subst_cont' X4 Q tl in
      constr:(parP X3 tmp)
  | _ => fail
  end.

Ltac subst_cont P Q p :=
  let rev_p := eval compute in (rev p) in
  subst_cont' P Q rev_p.

Ltac pickup_val' P pos :=
  match constr:pos with
  | nil => pickup_val_atom P
  | (?X1 :: ?X2) => pickup_vall X1 X2 P
  end
 with pickup_vall hd tl P :=
  match constr:hd with
  | one => pickup_val_one P tl
  | two => pickup_val_two P tl
  end
 with pickup_val_one P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_val' X3 tl
  | _ => fail
  end
 with pickup_val_two P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_val' X4 tl
  | _ => fail
  end
 with pickup_val_atom P :=
  match constr:P with
  | (?X1 << ?X2 >> ?X3) => constr:X2
  | (OutAtom ?X1 ?X2) => constr:X2
  | _ => fail
  end.

Ltac pickup_val P p :=
  let rev_p := eval compute in (rev p) in
  pickup_val' P rev_p.

Ltac pickup_out_cont' P pos :=
  match constr:pos with
  | nil => pickup_out_cont_atom P
  | (?X1 :: ?X2) => pickup_out_cont'' X1 X2 P
  end
 with pickup_out_cont'' hd tl P :=
  match constr:hd with
  | one => pickup_out_cont_one P tl
  | two => pickup_out_cont_two P tl
  end
 with pickup_out_cont_one P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_out_cont' X3 tl
  | _ => fail
  end
 with pickup_out_cont_two P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_out_cont' X4 tl
  | _ => fail
  end
 with pickup_out_cont_atom P :=
  match constr:P with
  | (?X1 << ?X2 >> ?X3) => constr:X3
  | (OutAtom ?X1 ?X2) => constr:zeroP
  | _ => fail
  end.

Ltac pickup_out_cont P p :=
  let rev_p := eval compute in (rev p) in
  pickup_out_cont' P rev_p.

Ltac pickup_in_cont' P pos v :=
  match constr:pos with
  | nil => pickup_in_cont_atom P v
  | (?X1 :: ?X2) => pickup_in_cont'' X1 X2 P v
  end
 with pickup_in_cont'' hd tl P v :=
  match constr:hd with
  | one => pickup_in_cont_one P tl v
  | two => pickup_in_cont_two P tl v
  end
 with pickup_in_cont_one P tl v :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_in_cont' X3 tl v
  | _ => fail
  end
 with pickup_in_cont_two P tl v :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_in_cont' X4 tl v
  | _ => fail
  end
 with pickup_in_cont_atom P v :=
  match constr:P with
  | (?X1 ?? ?X2) => constr:(X2 v)
  | (?X1 ??* ?X2) => constr:(parP (X1 ??* X2) (X2 v))
  | (InAtom ?X1) => constr:zeroP
  | _ => fail
  end.

Ltac pickup_in_cont P p v :=
  let rev_p := eval compute in (rev p) in
  pickup_in_cont' P rev_p v.

Ltac rep_cont_simp P in_pos out_pos :=
  let v := pickup_val P out_pos in
  let out_cont := pickup_out_cont P out_pos in
  let in_cont := pickup_in_cont P in_pos v in
  let new_in := eval cbv beta iota zeta in in_cont in
  let  (* instead of solely Compute *)
  new_p0 := subst_cont P out_cont out_pos in
  subst_cont new_p0 new_in in_pos.

Ltac rep_cont P lst :=
  match constr:lst with
  | nilIO => constr:(nilT proc)
  | (consIO ?X1 ?X2 ?X3 ?X4) => rep_cont' P X2 X3 X4
  end
 with rep_cont' P in_pos out_pos tl :=
  let tmp := rep_cont_simp P in_pos out_pos in
  let newtl := rep_cont P tl in
  constr:(consT proc tmp newtl).

(***
   *
   ***)

Ltac tr_comIO2 val :=
  match goal with
  |  |- (Trans ?X1 (TauL ?X2) ?X3) =>
      apply tr_comIO with (x := X2) (v := val)
  end.

Ltac tr_comOI2 val :=
  match goal with
  |  |- (Trans ?X1 (TauL ?X2) ?X3) =>
      apply tr_comOI with (x := X2) (v := val)
  end.

Ltac tr_in2 :=
  match goal with
  |  |- (Trans (?X1 ?? ?X2) (InL ?X3 ?X4) ?X5) =>
      apply tr_in with (C := X2) (x := X3) (v := X4)
  end.

Ltac tr_rin2 :=
  match goal with
  |  |- (Trans (?X1 ??* ?X2) (InL ?X3 ?X4) ?X5) =>
      apply tr_rin with (C := X2) (x := X3) (v := X4)
  end.

Ltac tr_out2 :=
  match goal with
  |  |- (Trans (?X1 << ?X2 >> ?X3) (OutL ?X4 ?X5) ?X6) => 
  apply tr_out
  end.

Ltac tr_par_inout :=
  match goal with
  |  |- (Trans (?X1 ?? ?X2) (InL ?X3 ?X4) ?X5) => tr_in2
  |  |- (Trans (InAtom ?X1) (InL ?X2 ?X3) ?X4) =>
      unfold InAtom in |- *; tr_in2
  |  |- (Trans (?X1 ??* ?X2) (InL ?X3 ?X4) ?X5) => tr_rin2
  |  |- (Trans (?X1 << ?X2 >> ?X3) (OutL ?X4 ?X5) ?X6) => tr_out2
  |  |- (Trans (OutAtom ?X1 ?X2) (OutL ?X3 ?X4) ?X5) =>
      unfold OutAtom in |- *; tr_out2
  |  |- (Trans ?X1 (InL ?X2 ?X3) ?X4) =>
      (apply tr_parR; tr_par_inout) || (apply tr_parL; tr_par_inout)
  |  |- (Trans ?X1 (OutL ?X2 ?X3) ?X4) =>
      (apply tr_parR; tr_par_inout) || (apply tr_parL; tr_par_inout)
  end.

Ltac tr_comio val := tr_comIO2 val; tr_par_inout; tr_par_inout.

Ltac tr_comoi val := tr_comOI2 val; tr_par_inout; tr_par_inout.

Ltac tr_com val := first [ tr_comio val | tr_comoi val ].

Ltac decomp val :=
  match goal with
  |  |- (Trans ?X1 ?X2 ?X3) =>
      tr_com val ||
        (apply tr_parL; decomp val) || (apply tr_parR; decomp val)
  end.

Ltac unary_IOlist_to_atom lst :=
  match constr:lst with
  | nilIO => fail
  | (consIO ?X1 ?X2 ?X3 nilIO) => constr:X1
  | _ => fail
  end.

Ltac unary_IOlist_to_atom_out lst :=
  match constr:lst with
  | nilIO => fail
  | (consIO ?X1 ?X2 ?X3 nilIO) => constr:X3
  | _ => fail
  end.

Ltac unary_listT_to_atom lst :=
  match constr:lst with
  | (nilT _) => fail
  | (consT _ ?X1 (nilT _)) => constr:X1
  | _ => fail
  end.

(* wrapper for the lemma conf_red_com that applies to the
only syntactically visible enabled communication *)

(*

TODO: update to 8.1

Tactic Definition ConfRedComAlways :=
Match Context With
  [ |- (sat (FMUSTEV (ALWAYS ?1)) ?2#?3) ] ->
Let lst = (search_inout ?3) In
Let c' = (unary_IOlist_to_atom lst) In
Let out_pos = (unary_IOlist_to_atom_out lst) In
Let val = (pickup_val ?3 out_pos) In
Let ns = (rep_cont ?3 lst) In
Let new_P = (unary_listT_to_atom ns) In
Apply conf_red_com_always with c:=c' P':=new_P;
[Apply red_com; decomp val | Idtac].

*)