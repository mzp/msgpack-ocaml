Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import List String.
Require Import libapplpi.
Require Import Object Session.

Inductive ServerSpec : proc -> Prop :=
| SCall   : forall f b (ch : chan session b),
  (forall req res, ServerSpecAfterCall res (f (Call req res))) ->
  ServerSpec (ch ?? f)
| SNotify : forall f b (ch : chan session b),
  (forall n, ServerSpec (f (Notify n))) -> ServerSpec (ch ?? f)
with ServerSpecAfterCall : chan response true -> proc -> Prop :=
  ServerSPecAfterCall : forall P (ch : chan response true) rval,
    ServerSpec P -> ServerSpecAfterCall ch (ch << rval >> P).
