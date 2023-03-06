structure Show_Record = struct

fun mk_field_pair n =
  let open HOLogic; open Syntax
  in mk_prod (mk_literal (Long_Name.base_name n), Const (@{const_name show}, dummyT --> literalT) $ (const n $ free "x"))
  end;

fun mk_field_assocs ns =
  let open HOLogic
  in mk_list (mk_prodT (literalT, literalT)) (map (fn n => mk_field_pair n) ns)
  end;

fun mk_record_show_eq info ctx = 
  let open Syntax; open HOLogic; 
      val show = const @{const_name show}; 
      val ns = map fst (#fields info) in
    Syntax.check_term ctx (
      mk_Trueprop (eq_const literalT $ (show $ free "x")
                                     $ (@{const show_fields} $ mk_field_assocs ns $ (mk_literal "()")
    )))
  end; 

fun mk_record_show_inst tname thy =
  let 
  open Syntax
  open Term
  open Proof_Context
  val (Type (qname, _)) = read_type_name {proper = false, strict = false} (init_global thy) tname
  val info = Record.the_info thy qname
  val r_ext = fst (#extension info)
  val ctx0 = Class.instantiation_cmd ([r_ext], ["show"], "show") thy;
  val (_, ctx1) = Local_Theory.begin_nested ctx0
  val ctx2 = Specification.definition 
                   (SOME (Binding.name ("show_" ^ Long_Name.base_name r_ext), NONE, NoSyn)) 
                   [] [] ((Binding.empty, []), (mk_record_show_eq info ctx0)) ctx1 |> snd
  val ctx3 = Local_Theory.end_nested ctx2
  in Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac ctx3 []) ctx3
  end

end