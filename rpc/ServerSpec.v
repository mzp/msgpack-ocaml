Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import Session.

Inductive ServerSpec' : session -> proc -> Prop :=
| SCall   : forall req res val,
  ServerSpec' (Call req res) (OutAtom res val)
| SNotify : forall n,
  ServerSpec' (Notify n) zeroP.

Inductive ServerSpec : proc -> Prop :=
| SServer : forall b (ch : chan session b) P,
  (forall msg, ServerSpec' msg (P msg)) ->
  ServerSpec (ch ??* (fun msg => P msg)).

