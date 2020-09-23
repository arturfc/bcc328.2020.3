(* semantic.ml *)

module A = Absyn
module S = Symbol
module T = Type

type entry = [%import: Env.entry]
type env = [%import: Env.env]

(* Obtain the location of an ast *)

let loc = Location.loc

(* Reporting errors *)

let undefined loc category id =
  Error.error loc "undefined %s %s" category (S.name id)

let misdefined loc category id =
  Error.error loc "%s is not a %s" (S.name id) category

let type_mismatch loc expected found =
  Error.error loc "type mismatch: expected %s, found %s" (T.show_ty expected) (T.show_ty found)

(* Searhing in symbol tables *)

let look env category id pos =
  match S.look id env with
  | Some x -> x
  | None -> undefined pos category id

let tylook tenv id pos =
  look tenv "type" id pos

let varlook venv id pos =
  match look venv "variable" id pos with
  | VarEntry t -> t
  | FunEntry _ -> misdefined pos "variable" id

let funlook venv id pos =
  match look venv "function" id pos with
  | VarEntry _ -> misdefined pos "function" id
  | FunEntry (params, result) -> (params, result)

(* Type compatibility *)

let compatible ty1 ty2 pos =
  if not (T.coerceable ty1 ty2) then
    type_mismatch pos ty2 ty1

(* Set the value in a reference of optional *)

let set reference value =
  reference := Some value;
  value

(* Checking expressions *)

let rec check_exp env (pos, (exp, tref)) =
  match exp with
  | A.BoolExp _ -> set tref T.BOOL
  | A.IntExp  _ -> set tref T.INT
  | A.RealExp _ -> set tref T.REAL
  | A.StringExp _ -> set tref T.STRING
  | A.LetExp (decs, body) ->  check_exp_let env pos tref decs body
  | A.BreakExp -> (if (env.inloop) then
                    T.VOID
                  else
                    Error.error pos "break outside of the loop")
  | A.NegativeExp (expression) -> (let value = check_exp env expression in
                                  begin match value with
                                    | T.INT  -> set tref value
                                    | T.REAL -> set tref value
                                    | _ -> type_mismatch pos T.REAL value
                                  end)                             
  | A.BinaryExp (left, operation, right) -> (let left_type = check_exp env left in
                                            let right_type = check_exp env right in
                                            begin match operation with
                                              | A.Plus | A.Minus | A.Div | A.Times | A.Mod | A.Power -> check_var_type pos left_type right_type tref
                                              | A.And | A.Or -> check_logic_type pos left_type right_type tref
                                              | A.Equal | A.NotEqual | A.LowerThan | A.GreaterThan | A.GreaterEqual | A.LowerEqual -> check_type_comparison pos left_type right_type tref
                                              | _ -> Error.fatal "not implemented"
                                            end)
  | A.ExpSeq (list_expression) -> (let rec check_seq = function
                                  | []         -> T.VOID
                                  | [head]     -> check_exp env head
                                  | head::tail -> ignore (check_exp env head); 
                                  check_seq tail
                                  in
                                    check_seq list_expression)
  | A.WhileExp (comparison, exp) -> let e_loop = {env with inloop = true} in
                                    ignore(check_exp e_loop comparison);
                                    ignore(check_exp e_loop exp);
                                    set tref T.VOID
                                    | _ -> Error.fatal "not implemented"

and check_var_type pos left_var_type right_var_type tref =
  match left_var_type, right_var_type with
  | T.INT,  T.INT  -> set tref T.INT
  | T.INT,  T.REAL
  | T.REAL, T.INT
  | T.REAL, T.REAL -> set tref T.REAL
  | _              -> type_mismatch pos right_var_type right_var_type

and check_logic_type pos left_expression right_expression tref =
  match left_expression, right_expression with
  | T.BOOL, T.BOOL -> set tref T.BOOL
  | _ -> (match left_expression with | T.BOOL -> type_mismatch pos T.BOOL right_expression | _ -> type_mismatch pos T.BOOL left_expression)

and check_type_comparison pos left_var_type right_var_type tref =
  match left_var_type with
  | T.STRING -> (match right_var_type with T.STRING -> set tref T.BOOL |_-> type_mismatch pos T.STRING right_var_type)
  | T.INT    -> (match right_var_type with T.INT    -> set tref T.BOOL |_-> type_mismatch pos T.INT right_var_type)
  | T.REAL   -> (match right_var_type with T.REAL   -> set tref T.BOOL |_-> type_mismatch pos T.REAL right_var_type)

and check_exp_let env pos tref decs body =
  let env' = List.fold_left check_dec env decs in
  let tbody = check_exp env' body in
  set tref tbody

(* Checking declarations *)

and check_dec_var env pos ((name, type_opt, init), tref) =
  let tinit = check_exp env init in
  let tvar =
    match type_opt with
    | Some tname ->
       let t = tylook env.tenv tname pos in
       compatible tinit t (loc init);
       t
    | None -> tinit
  in
  ignore (set tref tvar);
  let venv' = S.enter name (VarEntry tvar) env.venv in
  {env with venv = venv'}

and check_dec env (pos, dec) =
  match dec with
  | A.VarDec x -> check_dec_var env pos x
  | _ -> Error.fatal "unimplemented"

let semantic program =
  check_exp Env.initial program
