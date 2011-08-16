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
