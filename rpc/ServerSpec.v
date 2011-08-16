Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import Session.

Inductive ServerSpec' : session -> proc -> Prop :=
| SCall   : forall req res x,
  ServerSpec' (Call req res) (OutAtom res x)
| SNotify : forall n,
  ServerSpec' (Notify n) zeroP.

Inductive ServerSpec : chan session true -> proc -> Prop :=
| SServer : forall ch P,
  (forall x, ServerSpec' x (P x)) ->
  ServerSpec ch (ch ??* P).

