open Sll
open Interpret

let rec make_nat = function
  | 0 -> Ctr ("Z", [])
  | n -> Ctr ("S", [make_nat (n - 1)])

let rec from_nat = function
  | Ctr ("Z", [])  -> 0
  | Ctr ("S", [x]) -> 1 + from_nat x
  | x -> raise (Interpret_error ("(from_nat) bad nat: " ^ string_of_expr x))

let make_int z =
  if z < 0
  then Ctr ("N", [make_nat (-z)])
  else (make_nat z)

let from_int = function
  | Ctr ("N", [x]) -> -(from_nat x)
  | x -> from_nat x

let () =
  let gdefs = [
    (* Subtraction for Non-Negative integers *)
    "snn"  $ ("Z" +> [],    ["y"]) => GCall ("neg", Var "y", []);
    "snn"  $ ("S" +> ["x"], ["y"]) => GCall ("sud", Var "y", [Var "x"]);

    (* Subtract from already Decremented second argument Unexplored first one *)
    "sud"  $ ("Z" +> [],    ["x"]) => Ctr ("S", [Var "x"]);
    "sud"  $ ("S" +> ["y"], ["x"]) => GCall ("snn", Var "x", [Var "y"]);

    (* Negate integer *)
    "neg"  $ ("Z" +> [],    []) => Ctr ("Z", []);
    "neg"  $ ("S" +> ["x"], []) => Ctr ("N", [Ctr ("S", [Var "x"])]);
    "neg"  $ ("N" +> ["x"], []) => Var "x";

    (* Addition *)
    "add"  $ ("Z" +> [],    ["y"]) => Var "y";
    "add"  $ ("S" +> ["x"], ["y"]) =>
      GCall ("aup", Var "y", [Ctr ("S", [Var "x"])]);
    "add"  $ ("N" +> ["x"], ["y"]) => GCall ("sup", Var "y", [Var "x"]);

    (* Add Unexplored integer and Positive one *)
    "aup"  $ ("Z" +> [],    ["y"]) => Var "y";
    "aup"  $ ("S" +> ["x"], ["y"]) =>
      Ctr ("S", [GCall ("aup", Var "x", [Var "y"])]);
    "aup"  $ ("N" +> ["x"], ["y"]) => GCall ("snn", Var "y", [Var "x"]);

    (* Subtract from Unexplored integer Positive one *)
    "sup"  $ ("Z" +> [],    ["y"]) => Ctr ("N", [Var "y"]);
    "sup"  $ ("S" +> ["x"], ["y"]) => GCall ("sud", Var "y", [Var "x"]);
    "sup"  $ ("N" +> ["x"], ["y"]) =>
      Ctr ("N", [GCall ("aup", Var "y", [Var "x"])]);

    (* Multiplication *)
    "mul"  $ ("Z" +> [],    ["y"]) => Ctr ("Z", []);
    "mul"  $ ("S" +> ["x"], ["y"]) =>
      GCall ("add", Var "y", [GCall ("mul", Var "x", [Var "y"])]);
    "mul"  $ ("N" +> ["x"], ["y"]) =>
      GCall ("neg", GCall ("mul", Var "x", [Var "y"]), []);

    (* Is Negative predicate *)
    "isn"  $ ("Z" +> [],    []) => Ctr ("F", []);
    "isn"  $ ("S" +> ["x"], []) => Ctr ("F", []);
    "isn"  $ ("N" +> ["x"], []) => Ctr ("T", []);

    (* Absolute value *)
    "abs"  $ ("Z" +> [],    []) => Ctr ("Z", []);
    "abs"  $ ("S" +> ["x"], []) => Ctr ("S", [Var "x"]);
    "abs"  $ ("N" +> ["x"], []) => Var "x";

    (* Signum function *)
    "sgn"  $ ("Z" +> [],    []) => Ctr ("Z", []);
    "sgn"  $ ("S" +> ["x"], []) => Ctr ("S", [Ctr ("Z", [])]);
    "sgn"  $ ("N" +> ["x"], []) => Ctr ("N", [Ctr ("S", [Ctr ("Z", [])])]);

    (* Condition / if-then-else *)
    "cnd"  $ ("T" +> [], ["t"; "f"]) => Var "t";
    "cnd"  $ ("F" +> [], ["t"; "f"]) => Var "f";
  ] in
  let fdefs = [
    (* Subtraction *)
    "sub" >$ ["x"; "y"] >= GCall ("add", Var "x", [GCall ("neg", Var "y", [])]);

    (* Less then predicate *)
    "lss" >$ ["x"; "y"] >= GCall ("isn", FCall ("sub", [Var "x"; Var "y"]), []);

    (* Division for Non-Negative integers *)
    "dnn" >$ ["x"; "y"] >= GCall ("cnd",
      FCall ("lss", [Var "x"; Var "y"]), [
      Ctr ("Z", []);
      Ctr ("S", [FCall ("dnn", [
        FCall ("sub", [Var "x"; Var "y"]);
        Var "y"])])]);

    (* Division *)
    "div" >$ ["x"; "y"] >= GCall ("mul",
      GCall ("mul", GCall ("sgn", Var "x", []), [GCall ("sgn", Var "y", [])]), [
      FCall ("dnn", [
        GCall ("abs", Var "x", []); GCall ("abs", Var "y", [])])]);

    (* signed Modulo *)
    "mod" >$ ["x"; "y"] >= FCall ("sub", [ Var "x";
      GCall ("mul", FCall ("div", [Var "x"; Var "y"]), [Var "y"])]);
  ] in
  let program = make_program fdefs gdefs (Ctr ("Z", [])) in
  print_endline (string_of_program program);
  let tester make_call func control x y =
    let term = make_call func x y in
    let program = { program with term } in
    if run program = make_int (control x y)
    then print_string      " ok"
    else print_endline "\n [FAIL]"
  in
  let test = tester (fun func x y -> GCall (func, make_int x, [make_int y])) in
  test  "snn" ( - )   8    5 ;
  test  "snn" ( - )   5    8 ;
  test  "snn" ( - )   8    0 ;
  test  "snn" ( - )   0    8 ;
  test  "snn" ( - )   0    0 ;
  test  "add" ( + )   0    0 ;
  test  "add" ( + )   0    8 ;
  test  "add" ( + )   0  (-8);
  test  "add" ( + )   5    0 ;
  test  "add" ( + )   5    8 ;
  test  "add" ( + )   5  (-8);
  test  "add" ( + )   8  (-5);
  test  "add" ( + ) (-7)   0 ;
  test  "add" ( + ) (-7)   5 ;
  test  "add" ( + ) (-7)   7 ;
  test  "add" ( + ) (-7)   9 ;
  test  "add" ( + ) (-7) (-5);
  test  "mul" ( * )   0    0 ;
  test  "mul" ( * )   5    0 ;
  test  "mul" ( * )   0    5 ;
  test  "mul" ( * )   5    8 ;
  test  "mul" ( * )   5  (-8);
  test  "mul" ( * ) (-8)   5 ;
  test  "mul" ( * ) (-8) (-5);
  let testf = tester (fun func x y -> FCall (func, [make_int x; make_int y])) in
  testf "sub" ( - )   5  (-8);
  testf "sub" ( - ) (-8)   5 ;
  testf "sub" ( - ) (-8) (-5);
  testf "dnn" ( / )   0    5 ;
  testf "dnn" ( / )   3    5 ;
  testf "dnn" ( / )  40    8 ;
  testf "dnn" ( / )  41    8 ;
  testf "dnn" ( / )  39    8 ;
  testf "div" ( / )   0    5 ;
  testf "div" ( / )   3    5 ;
  testf "div" ( / )  40    8 ;
  testf "div" ( / )  41    8 ;
  testf "div" ( / )  39    8 ;
  testf "div" ( / )   3  (-8);
  testf "div" ( / ) (-8)   3 ;
  testf "div" ( / ) (-8) (-3);
  testf "mod" (mod)   0    5 ;
  testf "mod" (mod)   3    5 ;
  testf "mod" (mod)  40    8 ;
  testf "mod" (mod)  41    8 ;
  testf "mod" (mod)  39    8 ;
  testf "mod" (mod)   3  (-8);
  testf "mod" (mod) (-8)   3 ;
  testf "mod" (mod) (-8) (-3);
  print_endline "";

  print_string "x (some integer value) = ";
  let x = make_int (read_int ()) in
  print_string "y (some integer again) = ";
  let y = make_int (read_int ()) in
  let ratio  = run { program with term = FCall ("div", [x; y]) } in
  let modulo = run { program with term = FCall ("mod", [x; y]) } in
  print_endline ("x / y = " ^ string_of_int (from_int ratio));
  print_endline ("x % y = " ^ string_of_int (from_int modulo));
