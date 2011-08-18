Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import Session.
Require Import ServerSpec ClientSpec.

Theorem rpc_progress : forall res S C,
  (forall ch, ServerSpec ch (S ch)) ->
  (forall ch, ClientSpec ch res (C ch)) ->
  exists x : response,
  (nilC # nuPl (fun c => parP (S c) (C c))) |=t (FMUSTEV (ALWAYS (STAT (OUTPUTS res x ISANY)))).
Proof with auto.
intros res S C SS CS.
eapply ex_intro.
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

   (* callback *)
   specialize (H0 (Call req res)).
   inversion H0.
   apply cong_resp_tsat with (parP (ch ??* P) (parP (res ?? P0) (OutAtom res x))).

    apply red_com_deter_inout.
     intro.
     apply INPUTS_sat_inv  in H2.
     decompose [ex and] H2.
     apply cong_zero_zeros_only in H3.
   assert (zeros_only zeroP); [apply one_zero|].
   apply H3 in H4.
   inversion H4.
   inversion H8.



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
