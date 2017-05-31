type expr =
    Identifier  of string
  | Abstraction of string * expr
  | Application of expr * expr;;

let rec string_of_expr = function
    Identifier(s) -> s
  | Abstraction(s, t) -> Printf.sprintf "(\\%s. %s)" s (string_of_expr t)
  | Application(t, u) ->
    Printf.sprintf "(%s) (%s)" (string_of_expr t) (string_of_expr u);;

let ident s   = Identifier(s);;
let abst  s t = Abstraction(s, t);;
let app   t u = Application(t, u);;

let rec free_vars = function
    Identifier(s) -> [s]
  | Abstraction(s, t) -> List.filter (fun x -> x <> s) (free_vars t)
  | Application(t, u) ->
    let t_vars = free_vars t in
    let u_vars = free_vars u in
    List.append t_vars (List.filter (fun x -> not (List.mem x t_vars)) u_vars);;

let rec fresh_vars var lst =
  if List.mem var lst then
    fresh_vars (var ^ "'") lst
  else
    var;;

let rec substitute var term = function
    Identifier(s)     -> if s = var then term else ident s
  | Abstraction(s, t) ->
    let t_vars = free_vars t in
    let term_vars = free_vars term in
    if s = var then
      abst s t
    else if (not (List.mem var (t_vars))) then
      abst s t
    else if (List.mem s term_vars) then
      let f = fresh_vars s (List.append t_vars term_vars) in
      abst f (substitute var term t)
    else
      abst s (substitute var term t)
  | Application(t, u) ->
    app (substitute var term t) (substitute var term u);;

let is_redex = function
    Application(Abstraction(s, t), u) -> true
  | _ -> false;;

let beta_reduce = function
    Application(Abstraction(s, t), u) -> substitute s u t
  | t -> t;;

let rec normalize_single t =
  if is_redex t then
    beta_reduce t 
  else
    match t with
      Identifier(s) -> ident s
    | Abstraction(s, t) -> abst s (normalize_single t)
    | Application(t, u) -> 
      let normalized_t = normalize_single t in
      if t = normalized_t then
        app t (normalize_single u)
      else
        app normalized_t u
and
  normalize t =
  begin
    let normalized_t = normalize_single t
    in
    if normalized_t = t then
      t
    else
      normalized_t |> normalize
  end;;

(* todo: ノーマルフォームかどうか調べる関数を作る *)

let rec alpha_convertible t = function
    Identifier(s2) -> 
    begin
      match t with
        Identifier(s1) -> s1 = s2
      | _ -> false
    end
  | Abstraction(s2, t2) ->
    begin
      match t with
        Abstraction(s1, t1) ->
        if s1 = s2 then
          alpha_convertible t1 t2
        else
          alpha_convertible t1 (substitute s2 (ident s1) t2)
      | _ -> false
    end
  | Application(t2, u2) ->
    begin
      match t with
      | Application(t1, u1) -> 
        (alpha_convertible t1 t2) && (alpha_convertible u1 u2)
      | _ -> false
    end;;

let isEqualExpr expr1 expr2 =
  match (expr1, expr2) with
  | (Identifier(id1), Identifier(id2)) -> id1 = id2
  | (Abstraction(s, t), _) -> alpha_convertible expr1 expr2
  | (Application(t, u), _) -> alpha_convertible expr1 expr2
  | _ -> false;;

let a = ident "a" and
  b = ident "b" and
  f = ident "f" and
  n = ident "n" and
  p = ident "p" and
  q = ident "q" and
  x = ident "x" and
  y = ident "y" and
  z = ident "z";;
let zero = abst "f" (abst "x" x) and
  one  = abst "f" (abst "x" (app f x)) and
  two  = abst "f" (abst "x" (app f (app f x))) and
  three = abst "f" (abst "x" (app f (app f (app f x))));;
let _true  = abst "a" (abst "b" a) and
  _false = abst "a" (abst "b" b) and
  _if    = abst "f" (abst "x" (abst "y" (app (app f x) y)));;
let isZero = abst "n" (app (app n (abst "y" _false)) _true);;
let cons = abst "x" (abst "y" (abst "z" (app (app z x) y))) and
  car  = abst "x" (app x _true) and
  cdr  = abst "x" (app x  _false);;
let succ = abst "n" (abst "f" (abst "x" (app f (app (app n f) x))));;
let add = abst "a" (abst "b" (abst "f" (abst "x" (app (app b f) (app (app a f) x)))));;
let power = abst "a" (abst "b" (app b a));;
let yc = abst "f" (app (abst "x" (app f (app x x))) (abst "x" (app f (app x x))));;
let zc = abst "f" (app (abst "x" (app f (abst "y" (app (app x x) y)))) (abst "x" (app f (abst "y" (app (app x x) y)))));;
let mul = abst "a" (abst "b" (abst "f" (abst "x" (app (app b (app a f)) x))));;
let pred = abst "n" (abst "f" (abst "x" (app cdr (app (app n (abst "p" (app (app cons (app f (app car p))) (app car p)))) (app (app cons x) x)))));;
let fact_impl = abst "f" (abst "n" (app (app (app _if (app isZero n)) one) (app (app mul n) (app f (app pred n)))));;
let fact = app yc fact_impl;;

let rec genN n =
  let rec _genN n k ret =
    if n = k then ret else _genN n (k + 1) ((app succ ret) |> normalize)
  in
  let x = ident "x" in
  _genN n 0 (abst "f" (abst "x" x));;


let () = begin
  Printf.printf "zero  := %s\n" (zero |> string_of_expr);
  Printf.printf "one   := %s\n" (one |> string_of_expr);
  Printf.printf "two   := %s\n" (two |> string_of_expr);
  Printf.printf "three := %s\n" (three |> string_of_expr);

  Printf.printf "_true  := %s\n" (_true |> string_of_expr);
  Printf.printf "_false := %s\n" (_false |> string_of_expr);
  Printf.printf "_if    := %s\n" (_if |> string_of_expr);

  Printf.printf "(app (app (app _if _true) p) q) |> string_of_expr -> %s\n" ((app (app (app _if _true) p) q) |> string_of_expr);
  Printf.printf "(app (app (app _if _true) p) q) |> normalize |> isEqualExpr p -> %s\n" ((app (app (app _if _true)  p) q) |> normalize |> isEqualExpr p |> string_of_bool);
  Printf.printf "(app (app (app _if _false) p) q) |> normalize |> isEqualExpr q -> %s\n" ((app (app (app _if _false) p) q) |> normalize |> isEqualExpr q |> string_of_bool);
  Printf.printf "isZero := %s\n" (isZero |> string_of_expr);
  Printf.printf "(app isZero zero) |> isEqualExpr _true -> %s\n" ((app isZero zero) |> normalize |> isEqualExpr _true |> string_of_bool);
  Printf.printf "(app isZero one) |> isEqualExpr _false -> %s\n" ((app isZero  one) |> normalize |> isEqualExpr _false |> string_of_bool);
  Printf.printf "cons := %s\n" (cons |> string_of_expr);
  Printf.printf "car  := %s\n" (car |> string_of_expr);
  Printf.printf "cdr  := %s\n" (cdr |> string_of_expr);
  Printf.printf "(app (app cons one) two) |> normalize |> string_of_expr -> %s\n" ((app (app cons one) two) |> normalize |> string_of_expr);
  Printf.printf "(app (app cons (app (app cons one) two)) (app (app cons one) two)) |> normalize |> string_of_expr -> %s\n" ((app (app cons (app (app cons one) two)) (app (app cons one) two)) |> normalize |> string_of_expr);
  Printf.printf "succ := %s\n" (succ |> string_of_expr);
  Printf.printf "(app succ zero) |> normalize |> isEqualExpr one -> %s\n" ((app succ zero) |> normalize |> isEqualExpr one |> string_of_bool);

  Printf.printf "add := %s\n" (add |> string_of_expr);
  Printf.printf "(app (app add one) two) |> normalize |> isEqualExpr three -> %s\n" ((app (app add one) two) |> normalize |> isEqualExpr three |> string_of_bool);
  Printf.printf "mul := %s\n" (mul |> string_of_expr);

  Printf.printf "(app(app mul two) three) |> normalize |> isEqualExpr (genN 6) -> %s\n" ((app (app mul two) three) |> normalize |> isEqualExpr (genN 6) |> string_of_bool);

  Printf.printf "power := %s\n" (power |> string_of_expr);
  Printf.printf "(app(app power three) two) |> normalize |> isEqualExpr (genN 9) -> %s\n" ((app (app power three) two) |> normalize |> isEqualExpr (genN 9) |> string_of_bool);

  Printf.printf "pred := %s\n" (pred |> string_of_expr);
  Printf.printf "(app pred three) |> normalize |> isEqualExpr two -> %s\n" ((app pred three) |> normalize |> isEqualExpr two |> string_of_bool);
  Printf.printf "(app pred zero) |> normalize |> isEqualExpr zero -> %s\n" ((app pred zero) |> normalize |> isEqualExpr zero |> string_of_bool);

  Printf.printf "yc := %s\n" (yc |> string_of_expr);
  Printf.printf "zc := %s\n" (zc |> string_of_expr);
  Printf.printf "fact_impl := %s\n" (fact_impl |> string_of_expr);
  Printf.printf "fact := %s\n" (fact |> string_of_expr);
  Printf.printf "(app fact three) |> normalize |> string_of_expr -> %s\n" ((app fact three) |> normalize |> string_of_expr);
end;;
