(* AST *)
type variable = { name : string; id : int }
[@@deriving show { with_path = false }]

type expression =
  | Var of variable
  | Abs of variable * expression
  | App of expression * expression
  | Redex of expression * expression
[@@deriving show { with_path = false }]

(* PRINT *)

let show_var_id = ref false

let redex_to_string (Redex (Abs (red_v, red_e), e2)) expr_to_str =
  let rec helper_abs expr_to_str = function
    | Abs (u, (Abs _ as a)) ->
        Format.asprintf "%s%s" u.name (helper_abs expr_to_str a)
    | Abs (u, e) -> Format.asprintf "%s.%s" u.name (expr_to_str e)
    | a -> Format.asprintf ".%s" (expr_to_str a)
  in

  let wrap_to_color str color =
    "<span style=\"color:" ^ color ^ "\">" ^ str ^ "</span>"
  in
  let wrap_variable v = Format.asprintf "%s" (wrap_to_color v.name "#00f") in
  let first =
    let rec helper = function
      | Var v -> if red_v.id = v.id then wrap_variable v else v.name
      | Abs (v, e) ->
          Format.asprintf "λ%s%s" (helper (Var v)) (helper_abs helper e)
      | App (e1, e2) ->
          let first =
            Format.asprintf
              (match e1 with
              | Var _ | App _ | Redex _ -> "%s"
              | Abs _ -> "(%s)")
              (helper e1)
          in
          let second =
            Format.asprintf
              (match e2 with Var _ -> "%s" | _ -> "(%s)")
              (helper e2)
          in
          first ^ second
      | Redex _ -> failwith "Redex in redex"
    in
    helper (Abs (red_v, red_e))
  in
  let second =
    wrap_to_color
      (match e2 with
      | Var v -> v.name
      | _ -> Format.asprintf "(%s)" (expr_to_str e2))
      "#f00"
  in
  Format.asprintf "(%s)%s" first second

let expression_to_string e =
  (* print_string (show_expression e); *)
  let rec helper_abs expr_to_str = function
    | Abs (u, (Abs _ as a)) ->
        Format.asprintf "%s%s" u.name (helper_abs expr_to_str a)
    | Abs (u, e) -> Format.asprintf "%s.%s" u.name (expr_to_str e)
    | a -> Format.asprintf ".%s" (expr_to_str a)
  in
  let rec helper = function
    | Var v -> v.name ^ if !show_var_id then Int.to_string v.id else ""
    | Abs (v, e) -> Format.asprintf "λ%s%s" v.name (helper_abs helper e)
    | App (e1, e2) ->
        let first =
          Format.asprintf
            (match e1 with Var _ | App _ | Redex _ -> "%s" | Abs _ -> "(%s)")
            (helper e1)
        in
        let second =
          Format.asprintf
            (match e2 with Var _ -> "%s" | _ -> "(%s)")
            (helper e2)
        in
        first ^ second
    | Redex (Abs (v, e), e2) as r -> redex_to_string r helper
    | _ -> failwith "Wrong implementation"
  in
  helper e

let print_expression e = expression_to_string e |> print_string

let print_html_expression e =
  print_expression e;
  print_string " --> ";
  print_string "<br/>\n"

(* PARSE *)
open Angstrom

let ws_newline =
  let is_ws = function
    | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
    | _ -> false
  in
  take_while is_ws

let ws =
  let is_ws = function '\x20' | '\x0d' | '\x09' -> true | _ -> false in
  take_while is_ws

let token s = ws *> string s
let parens s = token "(" *> s <* token ")"

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init

let p_var =
  ws *> peek_char_fail >>= function
  | 'a' .. 'z' ->
      take_while1 (function 'a' .. 'z' | '0' .. '9' -> true | _ -> false)
  | _ -> fail "not a variable"

let p_abs p_e =
  token "\\" *> p_var >>= fun v ->
  token "." *> p_e >>= fun e -> return (Abs ({ name = v; id = 0 }, e))

let p_app p_e = chainl1 p_e (return (fun e1 e2 -> App (e1, e2)))

let p_macro_def p_e =
  lift2
    (fun name e -> (name, e))
    (ws
    *> take_while1 (function
         | 'A' .. 'Z' | '0' .. '9' | '_' -> true
         | _ -> false))
    (token "=" *> p_e <* ws <* token "\n" <* ws_newline)

let p_macro =
  ws *> peek_char_fail >>= function
  | 'A' .. 'Z' | '0' .. '9' | '_' ->
      take_while1 (function
        | 'A' .. 'Z' | '0' .. '9' | '_' -> true
        | _ -> false)
  | _ -> fail "not a macro"

module StringMap = Map.Make (String)

let p_expression macros =
  fix @@ fun p_expression ->
  let term =
    p_abs p_expression <|> parens p_expression
    <|> (p_var >>| fun v -> Var { name = v; id = 0 })
    <|> ( p_macro >>= fun m ->
          match StringMap.find_opt m macros with
          | Some e -> return e
          | None -> fail ("unknown macros, or in its definition: " ^ m) )
  in
  let term = p_app term <|> term in
  term

let p_program =
  let rec collect_macros macros =
    p_macro_def (p_expression macros)
    >>= (fun (name, expr) ->
          let macros = StringMap.add name expr macros in
          collect_macros macros)
    <|> return macros
  in
  ws_newline *> collect_macros StringMap.empty
  >>= (fun macros -> ws_newline *> p_expression macros)
  <* ws_newline

(* makes all variable unique by adding to each corresponding id. one way of implementing capture-avoiding substitution *)
let parse_lambda s =
  let annotate e =
    let fresh_id =
      let counter = ref 0 in
      fun () ->
        let id = !counter in
        counter := id + 1;
        id
    in
    let rec helper env = function
      | Var v -> (
          try
            let id = List.assoc v.name env in
            Var { name = v.name; id }
          with Not_found ->
            let id = fresh_id () in
            Var { name = v.name; id })
      | Abs (v, body) ->
          let new_id = fresh_id () in
          let v' = { name = v.name; id = new_id } in
          let env' = (v.name, new_id) :: env in
          Abs (v', helper env' body)
      | App (e1, e2) -> App (helper env e1, helper env e2)
    in
    helper [] e
  in
  match parse_string ~consume:All p_program s with
  | Ok e -> annotate e
  | Error msg -> failwith ("Error: Parser. Check your lambda: " ^ msg)

(* REDUCE *)

type strategy = CBN | NO | CBV | AO

let rec subst_local e (x : variable) v =
  match e with
  | Var y -> if y.id = x.id then v else e
  | Abs (y, e1) ->
      if y.id = x.id then Abs (y, e1) else Abs (y, subst_local e1 x v)
  | App (e1, e2) -> App (subst_local e1 x v, subst_local e2 x v)
  | Redex _ -> failwith "redex in subst"

let subst e =
  let rec helper = function
    | Var v -> Var v
    | Abs (y, e1) -> Abs (y, helper e1)
    | App (e1, e2) -> App (helper e1, helper e2)
    | Redex (Abs (x, e1), e2) -> subst_local e1 x e2
    | _ -> failwith "Wrong redex"
  in
  helper e

exception OneReduction of expression

(* rules: https://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf *)

let find_redex_cbn e =
  let is_found = ref false in
  let rec helper e =
    if !is_found then e
    else
      match e with
      | Var x -> Var x
      | Abs (x, e) -> Abs (x, e)
      | App (e1, e2) -> (
          match helper e1 with
          | Abs _ as a ->
              is_found := true;
              Redex (a, e2)
          | a -> App (a, e2))
      | a -> a
  in
  let res = helper e in
  if !is_found then Some res else None

let reduce_cbn original_e =
  match find_redex_cbn original_e with
  | Some e ->
      print_html_expression e;
      Some (subst e)
  | None -> None

let find_redex_cbv e =
  let is_found = ref false in
  let rec helper e =
    if !is_found then e
    else
      match e with
      | Var x -> Var x
      | Abs (x, e) -> Abs (x, e)
      | App (e1, e2) -> (
          match helper e1 with
          | Abs _ as a ->
              is_found := true;
              let e2' = helper e2 in
              Redex (a, e2')
          | e1' ->
              let e2' = helper e2 in
              App (e1', e2'))
      | Redex _ as r -> r
  in
  let res = helper e in
  if !is_found then Some res else None

let reduce_cbv original_e =
  match find_redex_cbv original_e with
  | Some e ->
      print_html_expression e;
      Some (subst e)
  | None -> None

let find_redex_ao e =
  let is_found = ref false in
  let rec helper e =
    if !is_found then e
    else
      match e with
      | Var x -> Var x
      | Abs (x, e) -> Abs (x, helper e)
      | App (e1, e2) -> (
          match helper e1 with
          | Abs _ as a ->
              is_found := true;
              let e2' = helper e2 in
              Redex (a, e2')
          | e1' ->
              let e2' = helper e2 in
              App (e1', e2'))
      | Redex _ as r -> r
  in
  let res = helper e in
  if !is_found then Some res else None

let reduce_ao original_e =
  match find_redex_ao original_e with
  | Some e ->
      print_html_expression e;
      Some (subst e)
  | None -> None

(* let rec reduce_nok current_e k =
   match current_e with
   | Var x -> Var x
   | Abs (x, e) -> (
       match reduce_nok e (fun reduced_e -> k (Abs (x, reduced_e))) with
       | e' -> Abs (x, e'))
   | App (e1, e2) -> (
       match reduce_cbnk e1 (fun reduced_e1 -> k (App (reduced_e1, e2))) with
       | Abs (x, e) ->
           let s = subst e x e2 in
           on_reduction k (e, x, e2);
           raise (OneReduction (k s))
       (* reduce_nok s *)
       (* dont continue, stop after one redution *)
       | e1' ->
           let e1'' =
             reduce_nok e1' (fun reduced_e1' -> k (App (reduced_e1', e2)))
           in
           let e2' =
             reduce_nok e2 (fun reduced_e2 -> k (App (e1'', reduced_e2)))
           in
           App (e1'', e2')) *)

(* let reduce_no original_e =
   try
     let _ = reduce_nok original_e Fun.id in
     None
   with OneReduction next_e -> Some next_e *)

let rec loop_reduce reduction_function e n =
  if n <= 0 then e
  else
    match reduction_function e with
    | Some next_e -> loop_reduce reduction_function next_e (n - 1)
    | None -> e

let reduce (s : strategy) (n : int) (e : expression) =
  match s with
  | CBV -> loop_reduce reduce_cbv e n
  | CBN -> loop_reduce reduce_cbn e n
  | AO -> loop_reduce reduce_ao e n
(* | NO -> loop_reduce reduce_no e n *)

(* RUNNING *)

let _ = show_var_id := false
let run_lambda s = print_expression (parse_lambda s)

let run_lambda__small_step ss s =
  print_expression (reduce ss 200 (parse_lambda s))
