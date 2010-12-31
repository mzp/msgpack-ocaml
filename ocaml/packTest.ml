open Base
open OUnit
open MsgpackCore
open Pack

let _ = begin "pack.ml" >::: [
  "nil/boolはフォルスルーする" >:: begin fun () ->
    assert_equal Nil @@ pack `Nil;
    assert_equal (Bool true) @@ pack (`Bool true);
    assert_equal (Bool false) @@ pack (`Bool false)
  end
] end +> run_test_tt_main

