Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import Session.

Inductive ClientSpec : chan session true -> chan response true -> proc -> Prop :=
| CCall   : forall P ch req res,
  ClientSpecAfterCall ch res P -> ClientSpec ch res ( ch << (Call req res) >> P)
| CNotify : forall P ch res n,
  ClientSpec ch res P -> ClientSpec ch res ( ch << (Notify n) >> P)
with ClientSpecAfterCall : chan session true -> chan response true -> proc -> Prop :=
| CRet   : forall ch res P,
  (forall x, ClientSpec ch res (P x)) -> ClientSpecAfterCall ch res (res ?? P).
