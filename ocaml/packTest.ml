open Base
open OUnit
open MsgpackCore
open Pack

let _ = begin "pack.ml" >::: [
  "nil/boolはフォルスルーする" >:: begin fun () ->
    assert_equal Nil @@ pack `Nil;
    assert_equal (Bool true) @@ pack (`Bool true);
    assert_equal (Bool false) @@ pack (`Bool false)
  end;
  "pfixnumはnatからasciiになる" >:: begin fun () ->
    assert_equal (PFixnum (Ascii (false,false,false,false,false,false,false,false))) @@
      pack (`PFixnum 0);
    assert_equal (PFixnum (Ascii (true,false,false,false,false,false,false,false))) @@
      pack (`PFixnum 1);
    assert_equal (PFixnum (Ascii (false,false,true,false,false,false,false,false))) @@
      pack (`PFixnum 4)
  end;
  "pfixnumに規定外の数を入れるとエラーになる" >:: begin fun () ->
    assert_raises (Not_conversion "pfixnum") (fun () -> pack (`PFixnum 128))
  end
] end +> run_test_tt_main

