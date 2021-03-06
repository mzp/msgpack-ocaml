open Msgpack
open Msgpack_conv
open OUnit

type t1 = {
  int : int;
  str : string;
  b   : bool;
  f   : float;
  u   : unit;
  c   : char;
} with conv(msgpack)

type t2 =
  int list with conv(msgpack)

type t3 =
  int array with conv(msgpack)

type t4 =
  string option with conv(msgpack)

type t5 =
  int * string with conv(msgpack)

type t6 =
  Foo of int | Bar with conv(msgpack)

let check pack unpack x y =
  assert_equal x (pack y);
  assert_equal y (unpack x)

let tests = [
  "record" >:: begin fun () ->
    check
      msgpack_of_t1 t1_of_msgpack_exn
        (`FixMap [`FixRaw ['i'; 'n'; 't'], `PFixnum 42;
                  `FixRaw ['s'; 't'; 'r'], `FixRaw ['b'; 'a'; 'z'];
                  `FixRaw ['b'],           `Bool true;
                  `FixRaw ['f'],           `Float 42.;
                  `FixRaw ['u'],           `Nil;
                  `FixRaw ['c'],           `FixRaw ['_'];
                  ])
        { int = 42; str = "baz"; b = true; f = 42.; u = (); c = '_' }
  end;
  "list" >:: begin fun () ->
    check
      msgpack_of_t2 t2_of_msgpack_exn
        (`FixArray [`PFixnum 1; `PFixnum 2; `PFixnum 3])
        [ 1; 2; 3 ]
  end;
  "array" >:: begin fun () ->
    check
      msgpack_of_t3 t3_of_msgpack_exn
        (`FixArray [`PFixnum 1; `PFixnum 2; `PFixnum 3])
        [| 1; 2; 3 |]
  end;
  "option" >:: begin fun () ->
    check
      msgpack_of_t4 t4_of_msgpack_exn
        `Nil None;
    check
      msgpack_of_t4 t4_of_msgpack_exn
        (`FixRaw ['f'; 'o'; 'o']) (Some "foo")
  end;
  "tuple" >:: begin fun () ->
    check
      msgpack_of_t5 t5_of_msgpack_exn
        (`FixArray [`PFixnum 0; `FixRaw ['x']]) (0, "x")
  end;
  "varint" >:: begin fun () ->
    check
      msgpack_of_t6 t6_of_msgpack_exn
        (`FixMap [`FixRaw ['F'; 'o'; 'o' ], `FixArray [`PFixnum 42]]) (Foo 42)
  end
]
