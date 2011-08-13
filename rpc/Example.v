Add LoadPath "../applpi".
Add LoadPath "../proof".

Require Import libapplpi.
Require Import MultiByte.

Record request := makeRequest {

}.

Locate "??*".

Definition server (i : chan (nat * (chan nat true)) true) :=
 i ??* (fun ar =>
 let a := fst ar in
 let r := snd ar in
  (OutAtom r (plus a (1)))).
