open Printf
open Ostap
open Util
open Matcher
open Sll
open Parser

let rec toSLL acc gn p a b =
  let toId x = 
    match x with
    | `PArg n -> n
    | `PCtr (n, a) -> (String.lowercase n) ^ "_arg" in
  let rec idlist x = List.map toId x in
  let rec varlist x = List.map (fun n -> `Var (toId n)) x in
    match p with
     | `PCtr (n, ((`PCtr (n1, l) :: xs) as pargs)) -> 
       let body_args = (varlist pargs) @ (List.map (fun n -> `Var n) a) in 
       let new_gname = (gn ^ "_" ^ n) in
       let new_def = `GRule (gn $ (n +> (idlist pargs), a) => (`FCall (new_gname, body_args))) in
         toSLL (new_def :: acc) new_gname (`PCtr (n1,l)) ((idlist xs) @ a) b
     | `PCtr (n, pargs) -> `GRule (gn $ (n +> (idlist pargs), a) => b) :: acc
     | `PArg name       -> failwith "`PAgrs has inappropiate argument list"


ostap (
  dp_g_rule[expr_parser][dp_parser]:
    name:ident -"(" pat:deep_pat[dp_parser] gargs:(-"," ident)* -")"
        -"=" gbody:expr_parser
    { toSLL [] name pat gargs gbody }
  ;
  deep_pat[dp_parser]: 
      name:ident { `PArg name }
    | pname:cnt pargs:dp_args[dp_parser]  { `PCtr (pname, pargs) }
  ;
  dp_args[dp_parser]: 
    pargs:(-"(" list0[dp_parser] -")")? { list_of_opt pargs }
  )

ostap (
  dp_decl[expr_parser][dp_parser]:
    pure_decl[expr_parser] 
    | dp_g_rule[expr_parser][dp_parser]
)

let rec dp_parser xs = deep_pat dp_parser xs
let rec dp_decl_parser = dp_decl pure_expr_parser dp_parser
let dp_program_parser = program_parser dp_decl_parser pure_term_pure_expr_parser

let parse source_text cont =
  Combinators.unwrap (dp_program_parser (new lexer source_text))
    (fun program -> cont (resolve_gcalls program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 5) `Acc reason))

let example =
    "isOne(S(S(x)))=F\n"
  ^ "isOne(S(Z))=T\n"
  ^ ".\n"
  ^ "isOne(S(S(Z)))"

let verbose_test () =
  Combinators.unwrap (dp_program_parser (new lexer example))
    (fun program ->
      printf "Parsed program:\n%s\n" (string_of_program string_of_pure program))
    (fun reason ->
      printf "Parser error:\n%s\n" (Reason.toString (`First 3) `Acc reason))

let big_test () =
  Combinators.unwrap (dp_program_parser (new lexer example))
    (fun program ->
       let result = Interpret.run (resolve_gcalls program) in
       printf "%s\n" (string_of_pure result))
    (fun _ -> ())
