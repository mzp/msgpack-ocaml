MsgPack for OCaml
==============================

Building
--------

    $ make
    $ sudo make install

Usage
-----

### Serialize and deserialize Msgpack objects

``` ocaml
(* serialize *)
let bytes = 
  Msgpack.Serialize.serialize_string (`FixArray [`PFixnum 1; `PFixnum 2; `PFixnum 3])
    
(* deserialize *)
let obj =
  Msgpack.Serialize.deserialize_string bytes
```

### Serialize and deserialize OCaml types (using meta_conv)

``` ocaml
open Msgpack_conv

type t = {
  int : int;
  str : string;
} with conv(msgpack)

(* serialize *)
let bytes = 
  Msgpack.Serialize.serialize_string (msgpack_of_t { int = 42; str = "ans" })

(* deserialize *)
let obj =
  t_of_msgpack (Msgpack.Serialize.deserialize_string bytes)
```

See also the `example/` directory.

Testing
-------

    $ ocaml setup.ml -configure --enable-tests
    $ make test

Using with Coq
--------------

If you want to use msgpack at OCaml, you need not do this section.
This section for user intrested in formal verification.

You need Coq 8.4 and omake.

    $ cd proof
    $ make
    $ cp *.ml ../lib

