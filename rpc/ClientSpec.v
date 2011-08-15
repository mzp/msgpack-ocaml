Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import Session.

Inductive ClientSpec : proc -> Prop :=
| CCall   : forall Q b (ch : chan session b) c ret,
  ClientSpecAfterCall Q -> ClientSpec ( ch << (Call c ret) >> Q)
| CNotify : forall Q b (ch : chan session b) n,
  ClientSpec Q -> ClientSpec ( ch << (Notify n) >> Q)
with ClientSpecAfterCall : proc -> Prop :=
| CRet   : forall b (ch : chan session b) f,
  (forall ret, ClientSpec (f ret)) -> ClientSpecAfterCall (ch ?? f).