Require Import chan.
Require Import chanlist.
Require Import util_for_tactics.
Require Import applpi.
Require Import cong.
Require Import cong_tactic.
Require Import logic.
Require Import logic_prop.

 (* tactic to prove that ZEROS holds of some state *)

(*Tactic Definition SolveZEROS_direct :=
Match Context With
[ |- (sat ZEROS ?1#zeroP) ] ->
Unfold ZEROS;
Apply CONSISTS_sat;
Exists zeroP;
Exists zeroP;
Split; [ProcCong | Split; [Apply ISZERO_sat; Simpl; Auto | Apply ISZERO_sat; Simpl; Auto]].

Tactic Definition SolveZEROS :=
Match Context With
  [ |- (sat ZEROS ?1#(parP ?2 ?3)) ] ->
Apply sat_ZEROS_parP;
Split; [SolveZEROS | SolveZEROS]
| [ |- (sat ZEROS ?1#zeroP)] ->
SolveZEROS_direct
| _ -> Fail.*)

(** tactic to prove that OUTPUTS holds of some state *)

Lemma sat_OUTPUTS_OUTPUTS_parP :
 forall (A : Set) (b : bool) (c : chan A b) (v : A) 
   (f : form) (L : ChanList) (P Q : proc),
 sat (OUTPUTS c v f) (L # P) \/ sat (OUTPUTS c v f) (L # Q) ->
 sat (OUTPUTS c v f) (L # parP P Q).
intros.
inversion_clear H.
generalize (OUTPUTS_sat_inv H0); intro.
inversion_clear H.
inversion_clear H1.
inversion_clear H.
apply OUTPUTS_sat.
exists (parP x Q).
exists x0.
split; auto.
apply cong_tr with (parP (parP (c << v >> x0) x) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
generalize (OUTPUTS_sat_inv H0); intro.
inversion_clear H.
inversion_clear H1.
apply OUTPUTS_sat.
exists (parP x P).
exists x0.
split; auto.
apply cong_tr with (parP P (parP (c << v >> x0) x)).
apply cong_par.
apply cong_refl.
intuition.
ProcCong.
intuition.
Qed.

(*Tactic Definition SolveISOUTPUT :=
Match Context With
[ |- (sat (ISOUTPUT ?3 ?4 ?5) ?6#(outP ?7 ?8 ?9)) ] ->
Apply ISOUTPUT_sat;
Exists ?9;
Split; [Auto | Idtac].*)

(*Lemma SolveISOUTPUT_test : (A:Set)(b:bool)(c:(chan A b))(v:A)(P:proc)(f:form)
(sat (ISOUTPUT A b c v f) nilC#(outP c v P)).
Intros.
SolveISOUTPUT.
Abort.*)

Ltac test_val v w :=
  let v' := eval compute in v with w' := eval compute in w in
  match constr:(v' = w') with
  | (?X1 = ?X1) => idtac
  | (?X1 = ?X2) => fail
  end.

Ltac SolveOUTPUTS_direct :=
  match goal with
  |  |- (sat (OUTPUTS ?X3 ?X4 ?X5) (?X6 # ?X7 << ?X8 >> ?X9)) =>
      test_chan X3 X7; test_val X4 X8; apply OUTPUTS_sat; exists zeroP;
       exists X9; split; [ ProcCong | idtac ]
  end.

(*Lemma SolveOUTPUTS_direct_test : (A:Set)(b:bool)(c:(chan A b))(v:A)(P:proc)(f:form)
(sat (OUTPUTS c v f) nilC#(outP c v P)).
Intros.
SolveOUTPUTS_direct.
Abort.*)

Ltac SolveOUTPUTS :=
  match goal with
  |  |- (sat (OUTPUTS ?X3 ?X4 ?X5) (?X6 # parP ?X7 ?X8)) =>
      apply sat_OUTPUTS_OUTPUTS_parP; first
       [ right; SolveOUTPUTS | left; SolveOUTPUTS ]
  |  |- (sat (OUTPUTS ?X3 ?X4 ?X5) (?X6 # OutAtom ?X7 ?X8)) =>
      unfold OutAtom in |- *; SolveOUTPUTS_direct
  |  |- (sat (OUTPUTS ?X3 ?X4 ?X5) (?X6 # ?X7 << ?X8 >> ?X9)) =>
      SolveOUTPUTS_direct
  end.

(*Lemma SolveOUTPUTS_test : (A:Set)(b:bool)(c:(chan A b))(v:A)(P:proc)(f:form)
(sat (OUTPUTS c v f) nilC#(parP zeroP (parP (outP c v P) zeroP))).
Intros.
SolveOUTPUTS.
Abort.*)

(** tactic to prove that INPUTS holds of some state *)

Lemma sat_INPUTS_INPUTS_parP :
 forall (A : Set) (b : bool) (c : chan A b) (f : form) 
   (L : ChanList) (P Q : proc),
 sat (INPUTS c f) (L # P) \/ sat (INPUTS c f) (L # Q) ->
 sat (INPUTS c f) (L # parP P Q).
intros.
inversion_clear H.
generalize (INPUTS_sat_inv H0); intro.
inversion_clear H.
inversion_clear H1.
decompose [and] H; clear H.
apply INPUTS_sat.
exists (parP Q x).
exists x0.
split.
apply cong_tr with (parP (parP (c ?? x0) x) Q).
apply cong_par.
auto.
apply cong_refl.
ProcCong.
auto.
generalize (INPUTS_sat_inv H0); intro.
inversion_clear H.
inversion_clear H1.
decompose [and] H; clear H.
apply INPUTS_sat.
exists (parP P x).
exists x0.
split.
apply cong_tr with (parP P (parP (c ?? x0) x)).
apply cong_par.
apply cong_refl.
auto.
ProcCong.
auto.
Qed.

(*Tactic Definition SolveISINPUT :=
Match Context With
[ |- (sat (ISINPUT ?3 ?4) ?6#(inP ?7 ?8)) ] ->
Apply ISINPUT_sat;
Exists ?8;
Split; [Auto | Intro; Idtac].

Tactic Definition SolveISRINPUT :=
Match Context With
[ |- (sat (ISRINPUT ?3 ?4) ?6#(rinP ?7 ?8)) ] ->
Apply ISRINPUT_sat;
Exists ?8;
Split; [Auto | Intro; Idtac].*)

(*Lemma SolveINPUTS_test : (A:Set)(b:bool)(c:(chan A b))(v:A)(P:A->proc)(f:form)
(sat (INPUTS c f) nilC#(inP c P)).
Intros.
Apply INPUTS_sat.
Exists zeroP.
Exists P.
Split; [ProcCong | Idtac].
Abort.*)

Ltac SolveINPUTS_direct :=
  match goal with
  |  |- (sat (INPUTS ?X3 ?X4) (?X6 # ?X7 ?? ?X8)) =>
      test_chan X3 X7; apply INPUTS_sat; exists zeroP; exists X8; split;
       [ ProcCong | idtac ]
  end.

Ltac SolveINPUTS_direct_rinP :=
  match goal with
  |  |- (sat (INPUTS ?X3 ?X4) (?X6 # ?X7 ??* ?X8)) =>
      test_chan X3 X7; apply INPUTS_sat; exists (X7 ??* X8); exists X8; split;
       [ apply cong_tr with (parP (X7 ??* X8) (X7 ?? X8));
          [ apply cong_rep | apply cong_comm ]
       | idtac ]
  end.

(*Lemma SolveINPUTS_test2 : (A:Set)(b:bool)(c:(chan A b))(v:A)(P:A->proc)(f:form)
(sat (INPUTS c f) nilC#(rinP c P)).
Intros.
SolveINPUTS_direct_rinP.*)

Ltac SolveINPUTS :=
  match goal with
  |  |- (sat (INPUTS ?X3 ?X4) (?X6 # parP ?X7 ?X8)) =>
      apply sat_INPUTS_INPUTS_parP; first
       [ right; SolveINPUTS | left; SolveINPUTS ]
  |  |- (sat (INPUTS ?X3 ?X4) (?X6 # InAtom ?X7)) =>
      unfold OutAtom in |- *; SolveINPUTS_direct
  |  |- (sat (INPUTS ?X3 ?X4) (?X6 # ?X7 ?? ?X8)) => SolveINPUTS_direct
  |  |- (sat (INPUTS ?X3 ?X4) (?X6 # ?X7 ??* ?X8)) =>
      SolveINPUTS_direct_rinP
  end.

Ltac SolveOROUTPUTS :=
  match goal with
  |  |- (sat (OR ?X1 ?X2) (?X3 # ?X4)) => first
  [ apply intro_left_OR; SolveOROUTPUTS
  | apply intro_right_OR; SolveOROUTPUTS ]
  |  |- (sat (OUTPUTS ?X3 ?X4 ?X5) (?X6 # ?X7)) => SolveOUTPUTS
  | _ => fail
  end.
