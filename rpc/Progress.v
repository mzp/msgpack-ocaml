Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import Session.
Require Import ServerSpec ClientSpec.

Inductive Progress : chan response true -> form -> Prop :=
| progress : forall res x,
  Progress res (OUTPUTS res x ISANY).

Theorem rpc_progress : forall res S C f,
  (forall ch, ServerSpec ch (S ch)) ->
  (forall ch, ClientSpec ch res (C ch)) ->
  Progress res f ->
  (nilC # nuPl (fun c => parP (S c) (C c))) |=t (FMUSTEV (ALWAYS (STAT f))).
Proof with auto.
intros res S C f SS CS FS.
apply cong_resp_tsat with (parP zeroP
  (nuPl (fun c : chan session true => parP (S c) (C c)))).
 (* subgoal 1*)
 apply red_new_deterl.
 CheckStable; [ simpl | simpl | CheckInc]...
 intros.
 specialize (SS c).
 specialize (CS c).
 destruct SS; destruct CS.
  (* call case *)
  destruct H1.
  apply red_com_deter_rinout.
   intro.
   apply INPUTS_sat_inv  in H2.
   decompose [ex and] H2.
   apply cong_zero_zeros_only in H3.
   assert (zeros_only zeroP); [apply one_zero|].
   apply H3 in H4.
   inversion H4.
   inversion H8.

   intro.
   decompose[ex] H2.
   apply OUTPUTS_sat_inv in H3.
   decompose [ex and] H3.
   apply cong_zero_zeros_only in H4.
   assert (zeros_only zeroP); [apply one_zero|].
   apply H4 in H5.
   inversion H5.
   inversion H9.

   CheckStable; [ simpl | simpl | CheckInc]...


   CheckStable.

  CheckExistsGuard.
CheckUnstable.
intros.
NextComms.
simpl in |- *.
intros.
or_false.
SolveINPUTS.

  (* notify case *)

 case H.

 (* subgoal 2: Cong ... *)
