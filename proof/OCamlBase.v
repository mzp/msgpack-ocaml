Require Export String.
Require Export List.
Require Export ExtractUtil.
Require Export OCamlUtil.

Open Scope string_scope.

Notation "op ; x" := (semicolon_flipped x op) (at level 50).
