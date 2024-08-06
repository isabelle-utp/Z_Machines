(* ML code for processing Z machine semantics *)

structure Z_Machine = struct

type param = string * string

datatype operation_body =
  (* Operations build by definition from scratch *)
  OperDefn of {params: param list, pre: string list, update: string, output: string} |
  (* Operations built by composing other operations, or using imperative program notation *)
  OperComp of {params: param list, pre: string list, body: string} |
  (* Operations built by promotion *)
  OperProm of {promop: string, plens: string} |
  (* Operations that emit information on the state *)
  OperEmit of {emit: string} |
  (* Operations that extend an existing operation *)
  OperExt of {params: param list, pre: string list, extends: string, update: string, output: string}

datatype operation = 
  Operation of {name: string, state: string, body: operation_body}

datatype initialisation = 
  Init of {name: string, state: string, update: string}

datatype zmachine = ZMachine of {name: string, state: string, inv: string, init: string, operations: string list, ends: string}

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
    (map (fn n => ((Binding.empty_atts, mk_chan_show_eq n ctx), [], [])) (ops @ map (fn n => n ^ "_Out") ops))
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

fun gen n ty term ctx = snd (Local_Theory.define 
  ((Binding.name n, NoSyn)
  , ((Binding.name (n ^ "_def")
  , @{attributes [code_unfold, z_defs]})
  , Syntax.check_term ctx (Type.constraint ty term))) ctx);

fun def_zop n set st body ctx = 
  let open Syntax; open HOLogic; open Local_Theory
      val parm = dest_setT (range_type (Term.type_of (check_term ctx set)))
  in
     (* Generate the type of the operation (i.e. the set of possible parameter values *)
     gen (zop_type n) dummyT (check_term ctx set) ctx |>
     (* Generate the operation body *)
     (* It would be better if we could mark these as "code" rather than "code_unfold" to retain
        the structure in the language target. For now, code_unfold is required to ensure that
        the semantics of enumerated inputs is correctly calculated *)
     gen n (parm --> st --> dummyT) body
  end

fun mk_zinit (Init {name = n, state = s, update = upd}) ctx =
  let open Syntax; open Library; open Logic; open HOLogic; open Local_Theory
      val st = read_typ ctx s 
  in snd (define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , @{attributes [code_unfold, z_defs]})
           , check_term ctx (Type.constraint (st --> st) (parse_term ctx upd)))) ctx)
  end;

fun mk_zop (Operation {name = n, state = s, body = OperDefn {params = ps, pre = pre, update = upd, output = ot}}) ctx =
  let open Syntax; open Library; open Logic; open HOLogic; open Lift_Expr
      val pss = (map (fn (p, t) => (p, lift_expr ctx ((parse_term ctx t)))) ps)
      val pset = params_set (map snd pss)
      val set = SEXP $ pset
      val parm = dest_setT (range_type (Term.type_of (check_term ctx set)))
      val st = read_typ ctx s
      val ppat = mk_tuple (map (free o fst) pss)

      val ppre = 
         lambda (free state_id) 
                (mk_conj (const @{const_name Set.member} $ ppat $ (pset $ Bound 0)
                         , mk_lift_expr ctx (foldr1 mk_conj ((map (parse_term ctx) pre))) $ Bound 0)) 
      val poutput = 
         lambda (free state_id) 
                ((mk_lift_expr ctx (parse_term ctx ot)) $ Bound 0) 
      val body = ( 
              (Const (@{const_name "mk_zop"}, (parm --> st --> dummyT) --> dummyT)
                $ tupled_lambda ppat (SEXP $ ppre))
                $ tupled_lambda ppat (Type.constraint (st --> st) (parse_term ctx upd))
                $ tupled_lambda ppat (SEXP $ poutput)
                )
  in def_zop n set st body ctx 
     |> gen (zop_pre n) (parm --> st --> dummyT) (tupled_lambda ppat (SEXP $ ppre))
  end |
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

mk_zop (Operation {name = n, state = s, body = OperProm {promop = opr, plens = lens}}) ctx =
  let open Syntax; open Lift_Expr
      val opr' = read_term ctx opr; 
      val pn = fst (dest_Const opr');
      val opr_type = const (zop_type pn);
      val opr_pre = const (zop_pre pn);
      val lens' = parse_term ctx lens 
      val st = read_typ ctx s
      val set = check_term ctx (const @{const_name "promoted_type"} $ lens' $ const @{const_name collection_lens} $ opr_type)
      val ppre = check_term ctx (const @{const_name "promote_pre"} $ lens' $ const @{const_name collection_lens} $ opr_pre)
      val body = const @{const_name "promote_operation"} $ lens' $ const @{const_name collection_lens} $ const pn
  in def_zop n set st body ctx
     |> gen (zop_pre n) (dummyT --> st --> dummyT) ppre
  end |
mk_zop (Operation {name = n, state = s, body = OperComp {params = ps, pre = pre, body = bdy}}) ctx =
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
      val body = tupled_lambda ppat (Type.constraint (st --> dummyT) (parse_term ctx bdy))
  in def_zop n set st body ctx
     |> gen (zop_pre n) (parm --> st --> dummyT) (tupled_lambda ppat (SEXP $ ppre))
 end |
mk_zop (Operation {name = n, state = s, body = OperEmit {emit = e}}) ctx =
  let open Syntax; open HOLogic; open Lift_Expr
  val set = mk_lift_expr ctx (mk_set dummyT [parse_term ctx e])
  val st = read_typ ctx s
  val parm = dest_setT (range_type (Term.type_of (check_term ctx set)))
  val body = const @{const_abbrev emit_op}
  in def_zop n set st body ctx 
     (* Generate precondition *)
     |> gen (zop_pre n) (parm --> st --> dummyT) (Abs ("p", parm, SEXP $ lambda (free state_id) @{term True}))
  end |
mk_zop (Operation {name = n, state = s, body = OperExt {params = ps, pre = pre, extends = extends, update = upd, output = ot}}) ctx =
  let open Syntax; open Library; open Logic; open HOLogic; open Lift_Expr
      val pss = (map (fn (p, t) => (p, lift_expr ctx ((parse_term ctx t)))) ps)
      val pset = params_set (map snd pss)
      val set = SEXP $ pset
      val parm = dest_setT (range_type (Term.type_of (check_term ctx set)))
      val st = read_typ ctx s
      val ppat = mk_tuple (map (free o fst) pss)

      val ppre = 
         lambda (free state_id) 
                (mk_conj (const @{const_name Set.member} $ ppat $ (pset $ Bound 0)
                         , mk_lift_expr ctx (foldr1 mk_conj ((map (parse_term ctx) pre))) $ Bound 0)) 
      val poutput = 
         lambda (free state_id) 
                ((mk_lift_expr ctx (parse_term ctx ot)) $ Bound 0) 
      val body = ( 
              (Const (@{const_name "extend_operation"}, (parm --> st --> dummyT) --> dummyT)
                $ tupled_lambda ppat (SEXP $ ppre))
                $ tupled_lambda ppat (parse_term ctx extends)
                $ tupled_lambda ppat (Type.constraint (st --> st) (parse_term ctx upd))
                $ tupled_lambda ppat (SEXP $ poutput)
                )
  in def_zop n set st body ctx 
     |> gen (zop_pre n) (parm --> st --> dummyT) (tupled_lambda ppat (SEXP $ ppre))
  end;


fun get_zop_ptype n ctx =
  case Proof_Context.read_const {proper = false, strict = false} ctx n of
    Const (_, Type (@{type_name fun}, [a, _])) => a |
    _ => raise Match;
    
fun get_zop_outtype n ctx = 
  case Proof_Context.read_const {proper = false, strict = false} ctx n of
    Const (_, Type (@{type_name fun}, 
              [_, Type (@{type_name fun}, 
                  [_, Type (@{type_name itree}, 
                      [_, Type (@{type_name prod}, [a, _])])])])) => a |
    _ => raise Match;

  
fun read_const_name ctx n =
  case Proof_Context.read_const {proper = false, strict = false} ctx n of
    Const (n', _) => n' |
    Free (n', _) => n' |
    _ => raise Match;

fun zmachine_body_sem n st init inve ops ends ctx =
  let open Syntax; open HOLogic; open Proof_Context
      val oplist = 
            mk_list dummyT 
              (map (fn n => const @{const_name zop_event} 
                            $ read_const {proper = false, strict = false} ctx (firstLower n) 
                            $ const (read_const_name ctx (zop_type n))
                            $ const (read_const_name ctx (zop_pre n)) 
                            $ read_const {proper = false, strict = false} ctx (firstLower n ^ "_Out") 
                            $ const (read_const_name ctx n)) ops)
  in snd (Local_Theory.define 
           ((Binding.name n, NoSyn)
         , ((Binding.name (n ^ "_def")
           , @{attributes [code, z_machine_defs]})
           , check_term ctx 
              (const @{const_name "z_machine"} $ Type.constraint (st --> st) init $ inve $ oplist $ ends))) ctx) end

fun chantype_name n = n ^ "_chan"

fun zmachine_sem (ZMachine {name = n, state = s, init = i, inv = inv, operations = ops, ends = e}) thy =
  let open Syntax; open HOLogic; open Lift_Expr
    val ctx = Named_Target.theory_init thy
    val cs = map (fn n => (firstLower n, YXML.content_of (string_of_typ ctx (get_zop_ptype n ctx)))) ops @
             map (fn n => (firstLower n ^ "_Out", YXML.content_of (string_of_typ ctx (get_zop_outtype n ctx)))) ops
    val st = read_typ ctx s
    val inve = mk_lift_expr ctx (parse_term ctx inv)
    val init = parse_term ctx i
    val ends = mk_lift_expr ctx (parse_term ctx e)
  in Channel_Type.compile_chantype (chantype_name n, cs) thy |>
     Named_Target.theory_init o mk_chan_show_inst (chantype_name n) ops |>
     Local_Theory.exit_global o zmachine_body_sem n st init inve ops ends
  end

val parse_param = 
  let open Parse in
    name -- (@{keyword "\<in>"} |-- term)
  end;

val parse_operdefn =
  let open Scan; open Parse in
  ((Scan.optional (@{keyword "params"} |-- repeat1 parse_param) []) --
  (Scan.optional (@{keyword "pre"} |-- repeat1 term) ["True"]) --
  (Scan.optional (@{keyword "update"} |-- term) "[\<leadsto>]") --
  (Scan.optional (@{keyword "output"} |-- term) "()")
  >> (fn (((ps, g), upd), ot) => OperDefn {params = ps, pre = g, update = upd, output = ot}))
  end

val parse_opercomp = 
  let open Scan; open Parse in
  ((Scan.optional (@{keyword "params"} |-- repeat1 parse_param) []) --
  (Scan.optional (@{keyword "pre"} |-- repeat1 term) ["True"]) --
  (@{keyword "is"} |-- term)) >> (fn ((ps, pre), bdy) => OperComp {params = ps, pre = pre, body = bdy})
  end

val parse_operprom =
  let open Scan; open Parse in
  ((@{keyword "promote"} |-- term) -- (@{keyword "in"} |-- term) 
  >> (fn (oper, lens) => OperProm {promop = oper, plens = lens}))
  end

val parse_operemit =
  let open Scan; open Parse in
  (@{keyword "emit"} |-- term)
  >> (fn e => OperEmit {emit = e})
  end

val parse_operext =
  let open Scan; open Parse in
  ((Scan.optional (@{keyword "params"} |-- repeat1 parse_param) []) --
  (Scan.optional (@{keyword "pre"} |-- repeat1 term) ["True"]) --
  (@{keyword "extends"} |-- term) --
  (Scan.optional (@{keyword "update"} |-- term) "[\<leadsto>]") --
  (Scan.optional (@{keyword "output"} |-- term) "()")
  >> (fn ((((ps, g), ext), upd), ot) => OperExt {params = ps, pre = g, extends = ext, update = upd, output = ot}))
  end


val parse_operbody = parse_operprom || parse_opercomp || parse_operemit || parse_operext || parse_operdefn;

val parse_operation =
  let open Scan; open Parse in
  ((name --| @{keyword "="}) --
  (Scan.optional (@{keyword "over"} |-- typ) "_") --
  parse_operbody)
  >> (fn ((n, st), body) => Operation {name = n, state = st, body = body})
   end;

val parse_zinit =
  let open Scan; open Parse in
  ((name --| @{keyword "="}) --
  (@{keyword "over"} |-- typ) --
  (@{keyword "update"} |-- term))
  >> (fn ((n, st), upd) => Init {name = n, state = st, update = upd})
  end;

val parse_zmachine = 
  let open Scan; open Parse in
  (name --| @{keyword "="}) --
  (Scan.optional (@{keyword "over"} |-- typ) "_") --
  (@{keyword "init"} |-- term) --
  (Scan.optional (@{keyword "invariant"} |-- term) "True") --
  (@{keyword "operations"} |-- repeat1 name) --
  (Scan.optional (@{keyword "until"} |-- term) "False")
  >> (fn (((((n, st), init), inv), ops), ends) => ZMachine {name = n, state = st, init = init, inv = inv, operations = ops, ends = ends})
  end;
 

end  