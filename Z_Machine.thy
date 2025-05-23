theory Z_Machine
  imports Z_Operations Z_Animator Z_Testing "Z_Toolkit.Z_Toolkit" 
    "HOL-Library.Code_Target_Numeral" "ITree_Simulation.Code_Rational" "ITree_UTP.ITree_Random" "ITree_VCG.ITree_VCG"
    "Explorer.Explorer" Show_Record
  keywords "zmachine" "zoperation" "zinit" :: "thy_decl_block"
    and "over" "init" "invariant" "operations" "until" "params" "output" "pre" "update" "\<in>" "promote" "emit" "extends"
begin

declare [[literal_variables=false]]

named_theorems z_machine_defs

hide_const Map.dom
hide_const Map.ran

text \<open> An operation can have its parameters supplied by an event, using the construct below. \<close>

abbreviation input_in_where_choice 
  :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> ('s \<Rightarrow> bool) \<times> ('e, 's) htree) \<Rightarrow> 's \<Rightarrow> 'e \<Zpfun> ('e, 's) itree" where
  "input_in_where_choice c A P \<equiv> (\<lambda> s. (\<lambda> e \<in> build\<^bsub>c\<^esub> ` A s | fst (P (the (match\<^bsub>c\<^esub> e))) s \<bullet> snd (P (the (match\<^bsub>c\<^esub> e))) s))"

(*
definition zop_event :: 
  "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 
   ('a \<Rightarrow> 's \<Rightarrow> ('e, 'b \<times> 's) itree) \<Rightarrow> 
   ('e, 's) htree" where
[code_unfold]: 
  "zop_event c A d zop = 
    (\<lambda> s. Vis (prism_fun c (A s) 
               (\<lambda> v. (pre (zop v) s, zop v s \<bind> (\<lambda> (b, s'). Vis {build\<^bsub>d\<^esub> b \<mapsto> Ret s'})))))"
*)

definition zop_event :: 
  "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 
   ('a \<Rightarrow> 's \<Rightarrow> ('e, 'b \<times> 's) itree) \<Rightarrow> 
   ('e, 's) htree" where
[code_unfold]: 
  "zop_event c A P d zop = (c?(x):A | @(P x) \<rightarrow> output_return (zop x) d)"

lemma hl_zop_event_full: 
  "\<lbrakk> wb_prism c; \<And> p. H{P \<and> \<guillemotleft>p\<guillemotright> \<in> A \<and> @(Pre p)} zop p {ret. Q} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} zop_event c A Pre d zop \<^bold>{Q\<^bold>}"
  apply (simp add: zop_event_def)
  apply (rule hoare_safe)
   apply (simp)
  apply (rule hoare_safe)
  apply simp
  done

lemma hl_zop_event: 
  "\<lbrakk> wb_prism c; \<And> p. H{P} zop p {ret. Q} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} zop_event c A Pre d zop \<^bold>{Q\<^bold>}"
  by (simp add: hl_proc_conj_pre hl_zop_event_full)
  
(*
lemma pdom_zop_event: "wb_prism c \<Longrightarrow> pdom (zop_event c A zop s) = {e. e \<in> build\<^bsub>c\<^esub> ` A s \<and> pre (zop (the (match\<^bsub>c\<^esub> e))) s}"
  by (simp add: zop_event_def dom_prism_fun, auto)
*)

text \<open> A machine has an initialisation and a list of operations. \<close>

lemma wp_Vis: "wp (\<lambda> s. Vis (F s)) P = (\<exists> e\<in>dom F. wp (\<lambda> s. F s e) P)\<^sub>e"
  apply (auto simp add: wp_itree_def itree_rel_defs fun_eq_iff)
  apply (metis imageE pran_pdom)
  apply (meson pfun_app_in_ran)
  done

lemma wlp_Vis: "wlp (\<lambda> s. Vis (F s)) P = (\<forall> e\<in>dom F. wlp (\<lambda> s. F s e) P)\<^sub>e"
  apply (auto simp add: wlp_itree_def itree_rel_defs fun_eq_iff)
  apply (meson pfun_app_in_ran)
  apply (metis imageE pran_pdom)
  done

definition z_machine_main :: "(('e::show, 's) htree) list \<Rightarrow> ('e, 's) htree" where
"z_machine_main Ops = (foldr (\<box>) Ops Stop)"

definition z_machine :: "('s::default) subst \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> (('e::show, 's) htree) list \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 'e process" where
[code_unfold]: "z_machine Init Inv Ops End = process Init (iterate (Not \<circ> End) (z_machine_main Ops))"

(*
definition z_machine :: "('s::default) subst \<Rightarrow> ('e, 's) htree list \<Rightarrow> 'e process" where
[code_unfold]: "z_machine Init Ops = process Init (loop (foldr (\<box>) Ops Stop))"
*)

lemma deadlock_free_z_machine:
  fixes Inv :: "'s::default \<Rightarrow> bool"
  assumes 
    "Init establishes Inv"
    "\<And> E. E\<in>set Events \<Longrightarrow> H{Inv} E {Inv}"
    "`\<not> End \<and> Inv \<longrightarrow> dfp (foldr (\<box>) Events Stop)`"
  shows "deadlock_free (z_machine Init Inv Events End)"
proof (simp add: z_machine_def z_machine_main_def, rule deadlock_free_processI, rule deadlock_free_init_iterate[where P="Inv"], rule assms(1), simp_all)
  from assms(2) show "\<^bold>{Inv\<^bold>} foldr (\<box>) Events Stop \<^bold>{Inv\<^bold>}"
  proof (induct Events)
    case Nil
    then show ?case by (simp, metis SEXP_def hl_Stop)
  next
    case (Cons Ev Events)
    then show ?case
      by (metis foldr.simps(2) hl_choice list.set_intros(1) list.set_intros(2) o_apply)
  qed
  show "`\<not> End \<and> Inv \<longrightarrow> dfp (foldr (\<box>) Events Stop)`"
    using assms(3) by auto
qed

lemma preserves_trivial: "H{True} P {True}"
  by (simp add: hoare_alt_def)

method deadlock_free_invs uses invs =
  (((simp add: z_machine_defs)?
   ,rule deadlock_free_z_machine
   ,(zpog_full; auto)[1]
   ,((auto intro!: hl_zop_event preserves_trivial hoare_lemmas invs)[1] ; fail)))

method deadlock_free uses invs =
  ((deadlock_free_invs invs: invs),
   (simp add: zop_event_def extchoice_inp_where_combine extchoice_event_block z_defs z_locale_defs wp Ball_Sum_iff Bex_Sum_iff split_sum_all split_sum_ex;
    expr_simp add: split_sum_all split_sum_ex;
    ((rule conjI allI impI | erule conjE disjE exE)+; rename_alpha_vars?)?))

text \<open> Function to show the channel of an operation \<close>

definition show_op_channel :: "String.literal \<Rightarrow> 'a::show \<Rightarrow> String.literal" where
"show_op_channel c p = c + STR '' '' + show p"

ML \<open>open YXML\<close>

ML_file \<open>Z_Machine.ML\<close>

ML \<open>
Outer_Syntax.command @{command_keyword zmachine} "define a Z machine"
    (Z_Machine.parse_zmachine >> (Toplevel.theory o Z_Machine.zmachine_sem));

Outer_Syntax.command @{command_keyword zoperation} "define a Z operation"
    (Z_Machine.parse_operation >> (Toplevel.local_theory NONE NONE o Z_Machine.mk_zop));

Outer_Syntax.command @{command_keyword zinit} "define a Z initialisation"
    (Z_Machine.parse_zinit >> (Toplevel.local_theory NONE NONE o Z_Machine.mk_zinit));

\<close>

code_datatype pfun_of_alist pfun_of_map pfun_entries

setup \<open> Explorer_Lib.switch_to_quotes \<close>

declare [[literal_variables]]

text \<open> Change the default target of string syntax to be literals. Literals are much better for
  code generation, and also provide more control since they are a distinct type to lists.
  We also replace the @{typ string} type name with @{typ "String.literal"}.
 \<close>

bundle literal_syntax
begin

no_syntax
  "_String" :: "str_position \<Rightarrow> string" (\<open>(\<open>open_block notation=\<open>literal string\<close>\<close>_)\<close>)

syntax
  "_Literal" :: "str_position \<Rightarrow> String.literal"  (\<open>(\<open>open_block notation=\<open>literal string\<close>\<close>_)\<close>)

end

hide_type (open) string

type_synonym string = "String.literal"

unbundle literal_syntax

text \<open> The next line allows us to create lists of characters from literals by coercion. \<close>

declare [[coercion String.explode]]

unbundle Expression_Syntax

instantiation rational :: default
begin
definition "default_rational = (0::rational)"
instance ..
end

instantiation rational :: "show"
begin
instance ..
end

code_printing
  constant "show_rational_inst.show_rational" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "rational" :: "show" \<rightharpoonup> (Haskell) -

instantiation rat :: default
begin
definition "default_rat = (0::rat)"
instance ..
end

text \<open> We need an instance of the "Show" class for sets. Due to the way the code generator works,
  we need to replace the standard generated code datatype "Set" without our own, and derive
  a custom instance of show. The code below achieve this. \<close>

instantiation set :: ("show") "show"
begin

text \<open> The following strange definition of show for sets simply ensures that the code generator
  make a show instance for the element type. Without this definition, no code for this is 
  generated. The definition of show on the Haskell side is then replaced by the following
  code printing commands, so this code does not actually make it to Haskell. \<close>

definition show_set :: "'a set \<Rightarrow> String.literal" where
"show_set A = (let B = show ` A in '''')"

instance ..

end

code_printing
  code_module ListSet \<rightharpoonup> (Haskell)
\<open>module ListSet(Set(..)) where {
 import Prelude;
 import Data.List;
 data Set a = Set [a] | Coset [a];
 instance Show a => Show (Set a) where
 show (Set xs) = "{" ++ concat (intersperse "," (map show xs)) ++ "}"
 show (Coset xs) = "-" ++ show (Set xs);
 }
\<close> for type_constructor set
| type_constructor "set" \<rightharpoonup> (Haskell) "(ListSet.Set '(_'))"
| constant "List.set" \<rightharpoonup> (Haskell) "ListSet.Set"
| constant "List.coset" \<rightharpoonup> (Haskell) "ListSet.Coset"
| constant "show_set_inst.show_set" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "set" :: "show" \<rightharpoonup> (Haskell) -

code_reserved (Haskell) List_Set

end