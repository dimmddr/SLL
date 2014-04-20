open Printf
open Ostap
open Util
open Matcher
open Sll

let ident = ostap (n:IDENT {Token.repr n})
let cnt = ostap (c:CNT {Token.repr c})

let list_of_opt = function
  | Some xs -> xs
  | None    -> []

let resolveRule name pat args body =
  match pat with
  | (`PArg pname)          -> `FRule (name >$ (pname::args) >= body)
  | (`PCtr (pname, pargs)) -> `DPGRule (name, pat, args, body)

let rec toSLL acc gn p a b =
  let toId x = 
    match x with
    | `PArg n -> n
    | `PCtr (n, a) -> (String.lowercase n) ^ "_arg" in
  let rec idlist x = List.map toId x in
  let rec varlist x = List.map (fun n -> `Var (toId n)) x in
    match p with
     | `PCtr (n, ((`PArg n1 :: xs) as pargs))      -> `GRule (gn $ (n +> (idlist pargs), a) => b) :: acc
     | `PCtr (n, [])                               -> `GRule (gn $ (n +> [], a) => b) :: acc
     | `PCtr (n, ((`PCtr (n1, l) :: xs) as pargs)) -> 
       let body_args = (varlist pargs) @ (List.map (fun n -> `Var n) a) in 
       let new_gname = (gn ^ "_" ^ n) in
       let new_def = `GRule (gn $ (n +> (idlist pargs), a) => (`FCall (new_gname, body_args))) in
         toSLL (new_def :: acc) new_gname (`PCtr (n1,l)) ((idlist xs) @ a) b
     | (`PArg name)                   -> [] (*exception*)

let rec elim_deep_pat x = 
  match x with
  | `FRule (fn, b) :: smth -> (`FRule (fn, b) :: (elim_deep_pat smth))
  | `DPGRule (gn, p, a, b) :: smth -> (toSLL [] gn p a b) @ (elim_deep_pat smth)
  | [] -> []

let defs_splitter xs =
  let rec helper defs fdefs gdefs =
    match defs with
    | (`FRule (fn, b) :: smth)     -> helper smth ((fn, b) :: fdefs) gdefs
    | (`GRule (gn, pn, b) :: smth) -> helper smth fdefs ((gn, pn, b) :: gdefs)
    | []                           -> (fdefs, gdefs)
  in helper xs [] []

ostap (
  program_parser[e_parser][dp_parser]:
    defs:(funDef[e_parser][dp_parser])* -"." term:expression[e_parser] {
      let (fdefs, gdefs) = defs_splitter (elim_deep_pat defs) in
      make_program fdefs gdefs term
    }
  ;
  funDef[e_parser][dp_parser]:
    rule[e_parser][dp_parser]
  ;
  rule[e_parser][dp_parser]:
    name:ident -"(" pat:deep_pat[dp_parser] gargs:(-"," ident)* -")"
        -"=" gbody:e_parser
    { resolveRule name pat gargs gbody }
  ;
  args_list[e_parser]: -"(" list0[e_parser] -")"
  ;
  deep_pat[dp_parser]: 
      name:ident {`PArg name}
    | pname:cnt pargs:dp_args[dp_parser]  {`PCtr (pname, pargs)}
  ;
  dp_args[dp_parser]: 
    pargs:(-"(" list0[dp_parser] -")")? { list_of_opt pargs }
  ;
  expression[e_parser]:
      constructor[e_parser]
    | funCall[e_parser]
    | v:ident  { `Var v }
  ;
  ident_ctr_args:
    pargs:(-"(" list0[ident] -")")? { list_of_opt pargs }
  ;
  constructor[e_parser]:
    cname:cnt  args:args_list[e_parser]?
    { `Ctr cname (list_of_opt args) }
  ;
  funCall[e_parser]:
    name:ident args:args_list[e_parser]
    { `FCall (name, args) }
)

class lexer s =
  let skip  = Skip.create [Skip.whitespaces " \n\t\r"] in
  let ident = Str.regexp "[a-z][a-zA-Z0-9]*" in
  let cnt = Str.regexp "[A-Z][a-zA-Z0-9]*" in
  object (self)

    inherit t s

    method skip p c = skip s p c
    method getIDENT = self#get "identifier" ident
    method getCNT   = self#get "constructor" cnt

  end

let rec pure_parser xs = expression pure_parser xs
let rec dp_parser xs = deep_pat dp_parser xs
let program_parser = program_parser pure_parser dp_parser

let resolve_gcalls { fdefs = fdefs; gdefs = gdefs; term = term; } =
  let rec resolve_expr = function
    | `FCall (name, parg :: args) when not (Ident_map.mem name fdefs) ->
        `GCall (name, resolve_expr parg, List.map resolve_expr args)
    | `FCall (fname, fargs) -> `FCall (fname, List.map resolve_expr fargs)
    | `GCall (gname, pname, gargs) -> `GCall (gname, pname, gargs)
    | `Ctr (cname, cargs) -> `Ctr (cname, List.map resolve_expr cargs)
    | `Var name -> `Var name
  in
  let resolved_fdefs = Ident_map.map (fun { fargs = fargs; fbody = fbody; } ->
    { fargs = fargs; fbody = resolve_expr fbody } ) fdefs
  in
  let resolved_gdefs = Ident_map.map (fun gpdefs ->
    Ident_map.map (fun { pargs = pargs; gargs = gargs; gbody = gbody; } ->
      { pargs = pargs; gargs = gargs; gbody = resolve_expr gbody; })
      gpdefs) gdefs
  in
  { fdefs = resolved_fdefs; gdefs = resolved_gdefs; term = resolve_expr term; }

let parse source_text cont =
  Combinators.unwrap (program_parser (new lexer source_text))
    (fun program -> cont (resolve_gcalls program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 5) `Acc reason))

let example =
    "isOne(S(S(x, y),a))=F(x,y,a)\n"
  ^ "isOne(S(Z, b))=T\n"
  ^ "isOne(Z)=T\n"
  ^ ".\n"
  ^ "isOne(S(S(X, Y), A)))"

let big_example = string_of_program string_of_pure Arithm.program

let verbose_test () =
  Combinators.unwrap (program_parser (new lexer example))
    (fun program ->
      printf "Parsed program:\n%s\n" (string_of_program string_of_pure program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 3) `Acc reason))

let big_test () =
  Combinators.unwrap (program_parser (new lexer example))
    (fun program ->
       let result = Interpret.run (resolve_gcalls program) in
       printf "%s\n" (string_of_pure result))
    (fun _ -> ())
