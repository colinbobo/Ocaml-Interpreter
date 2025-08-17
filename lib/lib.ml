open Utils
include My_parser

(* open Interp03__Lib open Utils;; *)

(*
let rec string_of_ty (ty : ty) : string =
  match ty with
  | TUnit -> "TUnit"
  | TFloat -> "TFloat"
  | TInt -> "TInt"
  | TBool -> "TBool"
  | TVar x -> "TVar \"" ^ x ^"\""
  | TFun (t1, t2) -> "TFun (" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"
  | TList t -> "TList (" ^ string_of_ty t ^ ")"
  | TOption t -> "TOption (" ^ string_of_ty t ^ ")"
  | TPair (t1, t2) -> "TPair (" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"


let string_of_constr (t1, t2) =
  "(" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"
  
let string_of_constr_list l =
  "[" ^ String.concat "; " (List.map string_of_constr l) ^ "]"
  *)
let parse = My_parser.parse 

let ty_subst t x =
  let rec go = function
    | TUnit -> TUnit
    | TFloat -> TFloat
    | TInt -> TInt
    | TBool -> TBool
    | TVar y -> if x = y then t else TVar y
    | TFun (t1, t2) -> TFun (go t1, go t2)
    | TList t -> go t
    | TOption t -> go t
    | TPair (t1, t2) -> TPair (go t1, go t2)
  in go

let rec fvs = function
  | TUnit | TFloat | TInt| TBool -> VarSet.empty
  | TVar x -> VarSet.of_list [x]
  | TFun (t1, t2) -> VarSet.union (fvs t1) (fvs t2) 
  | TList t -> fvs t
  | TOption t -> fvs t 
  | TPair (t1, t2) -> VarSet.union (fvs t1) (fvs t2)

let ty_subst_c t x (t1, t2) = (ty_subst t x t1, ty_subst t x t2)
let ty_subst_cs t x = List.map (ty_subst_c t x)

let unify (ty: ty) (lst : constr list) = let a = TVar (gensym()) in let lst = lst @ [(a, ty)] in
(*  print_endline ("Unify called with:");
  print_endline ("ty = " ^ string_of_ty t);
  print_endline ("constraints = " ^ string_of_constr_list lst);*)
  let rec go l = 
    match l with
    | [] -> None 
    | [var, t] when var = a -> Some (Forall (VarSet.to_list (fvs t), t))
    | (t1, t2) :: cs when t1 = t2 -> go cs
    | (TFun (t1, t2), TFun (t1', t2')) :: cs ->
      go ((t1, t1') :: (t2, t2') :: cs)
    | (TVar x, t) :: cs ->
      if VarSet.mem x (fvs t)
      then None 
      else go (ty_subst_cs t x cs)
    | (t, TVar x) :: cs -> go ((TVar x, t) :: cs)
    | (TOption t1, TOption t2) :: cs | (TList t1, TList t2) :: cs  -> go ((t1, t2) :: cs)
    | (TPair (t1, t2), TPair (t3, t4)) :: cs -> go ((t1, t3) :: (t2, t4) :: cs)
    | _ -> None
    in go lst
  

let rec type_of' (ctxt : stc_env) (e : expr) : (ty * constr list) = 
  let rec go e =
    match e with 
    | Unit -> (TUnit, [])
    | True -> (TBool, [])
    | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | ENone -> let a = TVar (gensym()) in (TOption a, [])
    | ESome e -> let t, c = go e in (TOption t, c)
    | OptMatch {matched = e; some_name = x; some_case = e1; none_case = e2} -> let t, c = go e in 
      let a = TVar (gensym()) in let t1, c1 = type_of' (Env.add x (Forall ([], a)) ctxt) e1 (* might be wrong shouold make sure this is the right way to add to context*)
      in let t2, c2 = go e2 in (
        t2, (t, TOption a) :: (t1, t2) :: c @ c1 @ c2 
        )
    | Nil -> let a = TVar (gensym()) in (TList a, [])
    | Annot (e, t) -> let t', c = go e in (
      t, (t, t') :: c
      )
    | Bop (op, e1, e2) -> (
      match op with 
      | Comma -> let t1, c1 = go e1 in let t2, c2 = go e2 in (
        TPair (t1, t2), c1 @ c2
      )
      | Cons -> let t1, c1 = go e1 in let t2, c2 = go e2 in (
        TList t1, (t2, TList t1) :: c1 @ c2
      )
      | Add | Sub | Mul | Div | Mod -> let t1, c1 = go e1 in let t2, c2 = go e2 in (
        TInt, (t1, TInt) :: (t2, TInt) :: c1 @ c2
      )
      | AddF | SubF | MulF | DivF | PowF -> let t1, c1 = go e1 in let t2, c2 = go e2 in (
        TFloat, (t1, TFloat) :: (t2, TFloat) :: c1 @ c2
      )
      | Lt | Lte | Gt | Gte | Eq | Neq -> let t1, c1 = go e1 in let t2, c2 = go e2 in (
        TBool, (t1, t2) :: c1 @ c2
      )
      | And | Or -> let t1, c1 = go e1 in let t2, c2 = go e2 in (
        TBool, (TBool, t1) :: (TBool, t2) :: c1 @ c2
      )
      | Concat -> let t1, c1 = go e1 in let t2, c2 = go e2 in let a = TVar (gensym()) in (
        TList a, (t1, TList a) :: (t2, TList a) :: c1 @ c2
      )
      )
    | Assert False -> let a = TVar (gensym()) in (a, [])
    | Assert e -> let t, c = go e in (
      TUnit, (t, TBool) :: c
      )
    | If (e1, e2, e3) -> let t1, c1 = go e1 in let t2, c2 = go e2 in let t3, c3 = go e3 in (
      t3, (t1, TBool) :: (t2, t3) :: c1 @ c2 @ c3 
    )
    | App (e1, e2) ->  let t1, c1 = go e1 in let t2, c2 = go e2 in let a = TVar (gensym()) in (
      a, (t1, TFun (t2, a)) :: c1 @ c2 
    )
    | Let {is_rec = false; name = x; value = e1; body = e2} -> let t1, c1 = go e1 in let t2, c2 = type_of' (Env.add x (Forall ([], t1)) ctxt) e2 in (
      t2, c1 @ c2 
    )
    | Let {is_rec = true; name = x; value = e1; body = e2} -> let a = TVar (gensym()) in let b = TVar (gensym()) in 
      let t1, c1 = type_of' (Env.add x (Forall ([], TFun (a, b))) ctxt) e1 in let t2, c2 = type_of' (Env.add x (Forall ([], t1)) ctxt) e2 in (
        t2, (t1, TFun (a, b)) :: c1 @ c2
      )
    | ListMatch {matched = e; hd_name = h; tl_name = tl; cons_case = e1; nil_case = e2} -> let t, c = go e in let a = TVar (gensym()) in 
      let t1, c1 = let ctxt = Env.add h (Forall ([], a)) ctxt in let ctxt = Env.add tl (Forall ([], TList a)) ctxt in type_of' ctxt e1 in 
      let t2, c2 = go e2 in (
        t2, (t, TList a) :: (t1, t2) :: c @ c1 @ c2
      )
    | PairMatch {matched = e; fst_name = x; snd_name = y; case = e'} -> let t, c = go e in let a = TVar (gensym()) in let b = TVar (gensym()) in
      let t', c' = let ctxt = Env.add x (Forall ([], a)) ctxt in let ctxt = Env.add y (Forall ([], b)) ctxt in type_of' ctxt e' in (
        t', (t, TPair(a, b)) :: c @ c'
      )
    | Fun (x, Some t, e) -> let t', c = type_of' (Env.add x (Forall ([], t)) ctxt) e in (
      TFun (t, t'), c 
    ) 
    | Fun (x, None, e) -> let a = TVar (gensym()) in let t, c = type_of' (Env.add x (Forall ([], a)) ctxt) e in (
      TFun (a, t), c
    )
    | Var x -> let Forall(bnd_vars, t) = Env.find x ctxt in
      let substitute = List.map (fun x -> (x, TVar (gensym()))) bnd_vars in 
      let t_inst = List.fold_left (fun acc (x, t') -> ty_subst t' x acc) t substitute in 
      (
        t_inst, []
      )
  in go e 

let type_of ctxt e = 
  let t, c = type_of' ctxt e in 
  unify t c 


exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals


let rec eval_expr env e = 
  let rec helper = function 
  | Unit -> VUnit
  | True -> VBool (true)
  | False -> VBool (false)
  | Nil -> VList []
  | ENone -> VNone
  | Int (n) -> VInt (n)
  | Float (n) -> VFloat (n)
  | Var (x) -> (
    match Env.find_opt x env with
    | Some v -> v
    | _ -> failwith "2" (* Check this again (case should never happen) *) 
    )
  | Bop (op, e1, e2) -> (
    match op with 
    | Add | Sub | Mul | Div | Mod | AddF | SubF | MulF | DivF | PowF -> num_operate (op) e1 e2
    | Lt | Lte | Gt | Gte | Eq | Neq -> bool_operate (op) e1 e2
    | And | Or -> logic_operate (op) e1 e2
    | Cons -> (
      match helper e1 with
      | v1 -> (
        match helper e2 with 
        | VList v2 -> VList (v1 :: v2)
        | _ -> failwith "19"
      )
    )
    | Concat -> (
      match helper e1 with
      | VList v1 -> (
        match helper e2 with 
        | VList v2 -> VList (v1 @ v2)
        | _ -> failwith "19"
      )
      | _ -> failwith "20"
    )
    | Comma -> let v1 = helper e1 in let v2 = helper e2 in VPair (v1, v2)
  )
  | ESome e -> let v = helper e in VSome v
  | OptMatch {matched = e; some_name = x; some_case = e1; none_case = e2} -> (
    match helper e with
    | VSome v -> let v1 = eval_expr (Env.add x v env) e1 in v1
    | VNone -> helper e2 
    | _ -> failwith "eval match opt"
  )
  | ListMatch {matched = e; hd_name = h; tl_name = t; cons_case = e1; nil_case = e2} -> (
    match helper e with 
    | VList (vh :: vt) -> let env = Env.add h vh env in let env = Env.add t (VList vt) env in eval_expr env e1 
    | VList [] -> helper e2
    | _ -> failwith "list match eval"
  )
  | PairMatch {matched = e; fst_name = x; snd_name = y; case = e'} -> (
    match helper e with 
    | VPair (v1, v2) -> let env = Env.add x v1 env in let env = Env.add y v2 env in eval_expr env e'
    | _ -> failwith "pair match eval"
  )
  | Annot (e, _) -> helper e
  | Fun (x, _, e) -> VClos {name = None; arg = x; body = e; env = env} 
  | If (e1, e2, e3) -> (
    match helper e1 with 
    | VBool true -> helper e2
    | VBool false -> helper e3
    | _ -> failwith "3"
  )
  | App (e1, e2) -> ( 
    match helper e1 with
    | VClos {name = None; arg = x; body = e; env = fun_env} -> (
        match helper e2 with
        | v -> eval_expr (Env.add x v fun_env) e
        )
    | VClos {name = Some f; arg = x; body = body; env = fun_env} ->(
        match helper e2 with
        | v -> let fun_env = Env.add f (VClos {name = Some f; arg = x; body; env = fun_env}) fun_env in
        eval_expr (Env.add x v fun_env) body
        )
    | _ -> failwith "5"
  )
  | Let {is_rec = false; name = x; value = e; body = b} -> let env = Env.add x (helper e) env in eval_expr env b
  | Let {is_rec = true; name = f; value = e; body = b} ->
    let closure = 
      match eval_expr env e with
      | VClos {name = None; arg; body; env = clos_env} ->
          VClos {name = Some f; arg; body; env = Env.add f (VClos {name = Some f; arg; body; env = clos_env}) clos_env}
      | _ -> failwith "6"
    in
    let env' = Env.add f closure env in eval_expr env' b
  | Assert e -> (
    match helper e with 
    | VBool true -> VUnit
    | _ -> raise AssertFail
  )
  and num_operate op e1 e2 =
    match helper e1 with 
    | VInt n1 -> (
      match helper e2, op with 
      | VInt 0, Div -> raise DivByZero 
      | VInt 0, Mod -> raise DivByZero
      | VInt n2, Add -> VInt (n1 + n2)
      | VInt n2, Sub -> VInt (n1 - n2)
      | VInt n2, Mul -> VInt (n1 * n2)
      | VInt n2, Div -> VInt (n1 / n2)
      | VInt n2, Mod -> VInt (n1 mod n2)
      | _ -> failwith "8"
      (* maybe need catch all cases *)
    )
    | VFloat n1 -> (
      match helper e2, op with 
      | VFloat 0., DivF -> raise DivByZero 
      | VFloat n2, AddF -> VFloat (n1 +. n2)
      | VFloat n2, SubF -> VFloat (n1 -. n2)
      | VFloat n2, MulF -> VFloat (n1 *. n2)
      | VFloat n2, DivF -> VFloat (n1 /. n2)
      | VFloat n2, PowF -> VFloat (n1 ** n2)
      | _ -> failwith "80"
    )
    | _ -> failwith "9" 
  and bool_operate op e1 e2 =
    match helper e1 with 
    | n1 -> (
      match helper e2, op with 
      | n2, Eq -> VBool (n1 = n2)
      | n2, Neq -> VBool (n1 <> n2)
      | n2, Lt -> VBool (n1 < n2)
      | n2, Lte -> VBool (n1 <= n2)
      | n2, Gt -> VBool (n1 > n2)
      | n2, Gte -> VBool (n1 >= n2)
      | _ -> failwith "10" 
    )
  and logic_operate op e1 e2 = 
    match op with
    | And -> (
      match helper e1 with 
      | VBool false -> VBool false
      | VBool true -> (
        match helper e2 with 
        | VBool b -> VBool (true && b)
        | _ -> failwith "12"
      )
      | _ -> failwith "16"
      )
    | Or -> (
      match helper e1 with 
      | VBool true -> VBool true
      | VBool false -> helper e2
      | _ -> failwith "17"
      )
    | _ -> failwith "14"
  in helper e


let type_check =
  let rec go ctxt = function
  | [] -> Some (Forall ([], TUnit))
  | {is_rec;name;value} :: ls ->
    match type_of ctxt (Let {is_rec;name;value; body = Var name}) with
    | Some ty -> (
      match ls with
      | [] -> Some ty
      | _ ->
        let ctxt = Env.add name ty ctxt in
        go ctxt ls
    )
    | None -> None
  in go Env.empty

let eval p =
  let rec nest = function
    | [] -> Unit
    | [{is_rec;name;value}] -> Let {is_rec;name;value;body = Var name}
    | {is_rec;name;value} :: ls -> Let {is_rec;name;value;body = nest ls}
  in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog -> (
    match type_check prog with
    | Some ty -> Ok (eval prog, ty)
    | None -> Error TypeError
  )
  | None -> Error ParseError
