(* ML code for processing Z machine semantics *)

structure Z_Machine = struct

type param = string * string
datatype operation = Operation of {name: string, state: string, params: param list, pre: string list, update: string, guard: string list}
datatype zmachine = ZMachine of {name: string, state: string, inv: string, init: string, operations: string list}

val SEXP = Const (@{const_name SEXP}, dummyT --> dummyT)

(* Calculate the types (i.e. maximal sets) of each parameter from the given sets *)

fun params_set pss =
  let 
    open Syntax; open Library               
  in lambda (Syntax.free Lift_Expr.state_id) 
      (if pss = [] 
       then @{term "UNIV :: unit set"} 
       else foldr1 (fn (x, y) => const @{const_abbrev "Product_Type.Times"} $ x $ y) pss)
  end                                                                                     

fun firstLower s =
  case String.explode s of [] => "" | c :: cs => String.implode (Char.toLower c :: cs);

fun get_op_chan ctx n = 
  Proof_Context.read_const 
    {proper = true, strict = false} 
    ctx 
    (firstLower n ^ Channel_Type.ctor_suffix);

fun mk_chan_show_eq n ctx = 
  let open Syntax; open HOLogic; val show = const @{const_name show} in
    Syntax.check_term ctx (
      mk_Trueprop (eq_const dummyT $ (show $ (get_op_chan ctx n $ free "x"))
                                   $ (const @{const_name show_op_channel} $ mk_literal (Long_Name.base_name n) $ (free "x")))
    )
  end; 

fun mk_chan_show_fun tname ops ctx =
  let val typ = Syntax.read_typ ctx tname in
  Function_Fun.add_fun 
    [(Binding.name ("show_" ^ tname), SOME (typ --> @{typ "String.literal"}), NoSyn)]
    (map (fn n => ((Binding.empty_atts, mk_chan_show_eq n ctx), [], [])) ops)
    (Function_Fun.fun_config) ctx
  end

fun mk_chan_show_inst tname ops thy =
  let val ctx0 = Class.instantiation_cmd ([tname], [], "show") thy;
      val ctx1 = mk_chan_show_fun tname ops ctx0;
  in Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac ctx1 []) ctx1
  end

fun zop_type n = n ^ "_type"

fun zop_pre n = n ^ "_pre"

fun zop_guard n = n ^ "_guard"

fun zop_update n = n ^ "_update"

(* FIXME: Guard ~> Precondition, Postcondition ~> Guard *)

fun mk_zop (Operation {name = n, state = s, params = ps, pre = pre, update = upd, guard = g}) ctx =
  let open Syntax; open Library; open Logic; open HOLogic; open Lift_Expr
      val pss = (map (fn (p, t) => (p, lift_expr ctx ((parse_term ctx t)))) ps)
      val pset = params_set (map snd pss)
      val set = SEXP $ pset
      val parm = dest_setT (range_type (Term.type_of (check_term ctx set)))
      val st = read_typ ctx s
      val ppat = mk_tuple (map (free o fst) pss)
      val ppre = 
         lambda (free state_id) 
                (mk_lift_expr ctx (foldr1 mk_conj ((map (parse_term ctx) pre))) $ Bound 0) 
      val pguard = 
         lambda (free state_id) 
                (mk_conj (const @{const_name Set.member} $ ppat $ (pset $ Bound 0)
                         , mk_lift_expr ctx (foldr1 mk_conj ((map (parse_term ctx) g))) $ Bound 0)) 

      (* val pupd = Type.constraint (st --> st) (parse_term ctx upd)

      val code_unfold = Attrib.check_src @{context} (Token.make_src ("code_unfold", Position.none) [])
      val z_defs = Attrib.check_src @{context} (Token.make_src ("z_defs", Position.none) [])
      fun gen n ty term = snd o Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , [code_unfold, z_defs])
           , check_term ctx term))
*)
  in (* Generate the type of the operation (i.e. the set of possible parameter values *)
     snd (Local_Theory.define 
           ((Binding.name (zop_type n), NoSyn)
         , ((Binding.name (zop_type n ^ "_def")
           , @{attributes [code_unfold, z_defs]})
           , check_term ctx set)) ctx) |>
     (
     (*
     (* Generate the precondition *)
     gen (zop_pre n) (parm --> st --> dummyT) (tupled_lambda ppat (SEXP $ ppre))
     #>
     (* Generate the guard *)
     gen (zop_guard n) (parm --> st --> dummyT) (tupled_lambda ppat (SEXP $ pguard))
     #>
     (* Generate the update *)
     gen (zop_update n) (parm --> st --> st) (tupled_lambda ppat pupd)
     #>
     *)     
     snd o Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           (* It would be better if we could mark these as "code" rather than "code_unfold" to retain
              the structure in the language target. For now, code_unfold is required to ensure that
              the semantics of enumerated inputs is correctly calculated *)
           , @{attributes [code_unfold, z_defs]})
           , check_term ctx ( 
              (Const (@{const_name "mk_zop"}, (parm --> st --> dummyT) --> dummyT)
                $ tupled_lambda ppat (SEXP $ ppre))
                $ tupled_lambda ppat (Type.constraint (st --> st) (parse_term ctx upd))
                $ tupled_lambda ppat (SEXP $ pguard)
(*                $ free (zop_pre n)
                $ free (zop_update n)
                $ free (zop_guard n) *)
                ))))
  end;

fun get_zop_ptype n ctx =
  case Proof_Context.read_const {proper = false, strict = false} ctx n of
    Const (_, Type (@{type_name fun}, [a, _])) => a |
    _ => raise Match;
      
fun read_const_name ctx n =
  case Proof_Context.read_const {proper = false, strict = false} ctx n of
    Const (n', _) => n' |
    Free (n', _) => n' |
    _ => raise Match;

fun zmachine_body_sem n st init inve ops ctx =
  let open Syntax; open HOLogic; open Proof_Context
      val oplist = 
            mk_list dummyT 
              (map (fn n => const @{const_name zop_event} $ read_const {proper = false, strict = false} ctx (firstLower n) $ const (read_const_name ctx (zop_type n)) $ const (read_const_name ctx n)) ops)
  in snd (Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , @{attributes [code, z_machine_defs]})
           , check_term ctx 
              (const @{const_name "z_machine"} $ Type.constraint (st --> st) init $ inve $ oplist))) ctx) end

fun chantype_name n = n ^ "_chan"

fun zmachine_sem (ZMachine {name = n, state = s, init = i, inv = inv, operations = ops}) ctx =
  let open Syntax; open HOLogic; open Lift_Expr
    val cs = map (fn n => (firstLower n, YXML.content_of (string_of_typ ctx (get_zop_ptype n ctx)))) ops
    val st = read_typ ctx s
    val inve = mk_lift_expr ctx (parse_term ctx inv)
    val init = parse_term ctx i
  in Channel_Type.compile_chantype (chantype_name n, cs) ctx |>
     Named_Target.theory_init o mk_chan_show_inst (chantype_name n) ops o Local_Theory.exit_global |>
     zmachine_body_sem n st init inve ops
  end

val parse_param = 
  let open Parse in
    name -- (@{keyword "\<in>"} |-- term)
  end;

val parse_operation =
  let open Scan; open Parse in
  ((name --| @{keyword "="}) --
  (Scan.optional (@{keyword "over"} |-- typ) "_") --
  (Scan.optional (@{keyword "params"} |-- repeat1 parse_param) []) --
  (Scan.optional (@{keyword "pre"} |-- repeat1 term) ["True"]) --
  (Scan.optional (@{keyword "update"} |-- term) "[\<leadsto>]") --
  (Scan.optional (@{keyword "where"} |-- repeat1 term) ["True"]))
  >> (fn (((((n, st), ps), g), upd), post) => Operation {name = n, state = st, params = ps, pre = g, update = upd, guard = post})
   end;

val parse_zmachine = 
  let open Scan; open Parse in
  (name --| @{keyword "="}) --
  (Scan.optional (@{keyword "over"} |-- typ) "_") --
  (@{keyword "init"} |-- term) --
  (Scan.optional (@{keyword "invariant"} |-- term) "True") --
  (@{keyword "operations"} |-- repeat1 name)
  >> (fn ((((n, st), init), inv), ops) => ZMachine {name = n, state = st, init = init, inv = inv, operations = ops})
  end;
 

end  