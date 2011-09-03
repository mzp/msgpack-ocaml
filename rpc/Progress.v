Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import Session.
Require Import ServerSpec ClientSpec.

Axiom session_neq_response : session <> response.

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
    apply red_com_deter_inout; try intro.
     apply INPUTS_sat_inv  in H2.
     decompose [ex and] H2.
     apply Cong_rinP_parP_inP0 with (c:=ch) (d:=res) in H6; auto.
     generalize session_neq_response; intro...

     decompose [ex] H2.
     apply OUTPUTS_sat_inv in H6.
     decompose [ex and] H6.
     apply Cong_rinP_parP_outP in H7...
     decompose [ex] H2.
     unfold Red in *.
     decompose [ex] H6.
     inversion H7.
      inversion H12.

      inversion H10.


Check cong_assoc.
     apply Cong_outP_parP_rinP with (c:=ch) (d:=res) in H7.

 with (parP zeroP
  (nuPl (fun c : chan session true => parP (S c) (C c)))).
Check cong_comm.


     apply cong_comm in H7.


Check ( session = response).
SearchPattern(_ <> _).
assert (nat <> bool).
intro.
auto.


     apply (Cong_inP_parP_rinP0 _ _ ch _ _ _ res _ _) in H6.
     apply Cong_inP_parP_rinP_chan in H6.
     specialize (H8 x).
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
