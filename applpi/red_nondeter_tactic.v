Require Import List.
Require Import listT.
Require Import chanlist.
Require Import applpi.
Require Import util_for_tactics.
Require Import datatypes_for_tactics.
Require Import logic.

 Ltac search_out2 c p lst cur P :=
  match constr:P with
  | (?X1 << ?X2 >> ?X3) =>
      test_chan2 X1 c (consIO c p cur lst) lst
  | (parP ?X1 ?X2) =>
      let l1 := search_out2 c p lst (one :: cur) X1 in
      search_out2 c p l1 (two :: cur) X2
  | zeroP => lst
  | (?X1 ?? ?X2) => lst
  | (?X1 ??* ?X2) => lst
  | (nuP ?X1) => fail
  | (nuPl ?X1) => fail
  | _ => fail
  end.

Ltac search_inout2' lst cur whole P :=
  match constr:P with
  | (?X1 ?? ?X2) =>
      let tmp := search_out2 X1 cur nilIO eps whole in
      eval compute in (appP tmp lst)
  | (?X1 ??* ?X2) =>
      let tmp := search_out2 X1 cur nilIO eps whole in
      eval compute in (appP tmp lst)
  | (parP ?X1 ?X2) =>
      let l1 := search_inout2' lst (one :: cur) whole X1 in
      search_inout2' l1 (two :: cur) whole X2
  | zeroP => lst
  | (?X1 << ?X2 >> ?X3) => lst
  | (nuP ?X1) => fail
  | (nuPl ?X1) => fail
  | _ => fail
  end.

Ltac search_inout2 P := search_inout2' nilIO eps P P.

Ltac subst_cont2' P Q p :=
  match constr:p with
  | nil => Q
  | (?X1 :: ?X2) => subst_cont2'' X1 X2 P Q
  end
 with subst_cont2'' hd tl P Q :=
  match constr:hd with
  | one => subst_cont2_one P Q tl
  | two => subst_cont2_two P Q tl
  end
 with subst_cont2_one P Q tl :=
  match constr:P with
  | (parP ?X3 ?X4) =>
      let tmp := subst_cont2' X3 Q tl in
      constr:(parP tmp X4)
  | _ => fail
  end
 with subst_cont2_two P Q tl :=
  match constr:P with
  | (parP ?X3 ?X4) =>
      let tmp := subst_cont2' X4 Q tl in
      constr:(parP X3 tmp)
  | _ => fail
  end.

Ltac subst_cont2 P Q p :=
  let rev_p := eval compute in (rev p) in
  subst_cont2' P Q rev_p.

Ltac pickup_val2' P pos :=
  match constr:pos with
  | nil => pickup_val2_atom P
  | (?X1 :: ?X2) => pickup_val2l X1 X2 P
  end
 with pickup_val2l hd tl P :=
  match constr:hd with
  | one => pickup_val2_one P tl
  | two => pickup_val2_two P tl
  end
 with pickup_val2_one P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_val2' X3 tl
  | _ => fail
  end
 with pickup_val2_two P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_val2' X4 tl
  | _ => fail
  end
 with pickup_val2_atom P :=
  match constr:P with
  | (?X1 << ?X2 >> ?X3) => constr:X2
  | _ => fail
  end.

Ltac pickup_val2 P p :=
  let rev_p := eval compute in (rev p) in
  pickup_val2' P rev_p.

Ltac pickup_out2_cont' P pos :=
  match constr:pos with
  | nil => pickup_out2_cont_atom P
  | (?X1 :: ?X2) => pickup_out2_cont'' X1 X2 P
  end
 with pickup_out2_cont'' hd tl P :=
  match constr:hd with
  | one => pickup_out2_cont_one P tl
  | two => pickup_out2_cont_two P tl
  end
 with pickup_out2_cont_one P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_out2_cont' X3 tl
  | _ => fail
  end
 with pickup_out2_cont_two P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_out2_cont' X4 tl
  | _ => fail
  end
 with pickup_out2_cont_atom P :=
  match constr:P with
  | (?X1 << ?X2 >> ?X3) => constr:X3
  | _ => fail
  end.

Ltac pickup_out2_cont P p :=
  let rev_p := eval compute in (rev p) in
  pickup_out2_cont' P rev_p.

Ltac pickup_in2_cont' P pos :=
  match constr:pos with
  | nil => pickup_in2_cont_atom P
  | (?X1 :: ?X2) => pickup_in2_cont'' X1 X2 P
  end
 with pickup_in2_cont'' hd tl P :=
  match constr:hd with
  | one => pickup_in2_cont_one P tl
  | two => pickup_in2_cont_two P tl
  end
 with pickup_in2_cont_one P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_in2_cont' X3 tl
  | _ => fail
  end
 with pickup_in2_cont_two P tl :=
  match constr:P with
  | (parP ?X3 ?X4) => pickup_in2_cont' X4 tl
  | _ => fail
  end
 with pickup_in2_cont_atom P :=
  match constr:P with
  | (?X1 ?? ?X2) => constr:X2
  | (?X1 ??* ?X2) => constr:(fun x => parP (X1 ??* X2) (X2 x))
  | _ => fail
  end.

Ltac pickup_in2_cont P p :=
  let rev_p := eval compute in (rev p) in
  pickup_in2_cont' P rev_p.

Ltac rep_cont2_simp P in_pos out_pos :=
  let v := pickup_val2 P out_pos in
  let out_cont := pickup_out2_cont P out_pos in
  let in_cont := pickup_in2_cont P in_pos in
  let new_in := eval cbv beta iota zeta in (in_cont v) in
  let  (* instead of solely Compute *)
  new_p0 := subst_cont2 P out_cont out_pos in
  subst_cont2 new_p0 new_in in_pos.

Ltac rep_cont2 P lst :=
  match constr:lst with
  | nilIO => constr:(nilT proc)
  | (consIO ?X1 ?X2 ?X3 ?X4) => rep_cont2' P X2 X3 X4
  end
 with rep_cont2' P in_pos out_pos tl :=
  let tmp := rep_cont2_simp P in_pos out_pos in
  let newtl := rep_cont2 P tl in
  constr:(consT proc tmp newtl).

(** We conjecture that our tactic NextComms is complete. *) 
Axiom NextComms_conjecture : False.

Ltac NextComms :=
  match goal with
  | id0:(Red (?X1 # ?X2) (?X1 # ?X3)) |- (tsat (FMUSTEV ?X4) (?X1 # ?X3)) =>
      let lst := search_inout2 X2 in
      let ns := rep_cont2 X2 lst in
      (cut (in_listT proc X3 ns);
        [ clear id0 | generalize NextComms_conjecture; contradiction ])
  end.

