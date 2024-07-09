section \<open> Z-style Operations \<close>

theory Z_Operations
  imports "ITree_UTP.ITree_UTP"
begin

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50) and
  Set.not_member  ("'(~:')") and
  Set.not_member  ("(_/ ~: _)" [51, 51] 50)

subsection \<open> Operations \<close>

text \<open> In the most basic form, and operation is simply an indexed Kleisli tree. The index type
  @{typ 'a} represents the inputs and outputs of the operation. \<close>

type_synonym ('e, 'a, 'b, 's) operation = "'a \<Rightarrow> 's \<Rightarrow> ('e, 'b \<times> 's) itree"

text \<open> An operation is constructed from a precondition, update, and postcondition, all of which
  are parameterised. \<close>

definition mk_zop :: 
  "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's subst) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'b) \<Rightarrow> ('e, 'a, 'b, 's) operation" where
"mk_zop P \<sigma> Q R = (\<lambda> v. assume (P v) ;; assert (Q v) ;; \<langle>\<sigma> v\<rangle>\<^sub>a ;; proc_ret (R v))"

lemma dlf_mk_zop [wp]: "dfp (mk_zop P \<sigma> Q R v) = (@(P v) \<longrightarrow> @(Q v))\<^sub>e"
  by (simp add: mk_zop_def wp)

abbreviation (input) "emit_op \<equiv> mk_zop (\<lambda> p. (True)\<^sub>e) (\<lambda> p. [\<leadsto>]) (\<lambda> p. (True)\<^sub>e) (\<lambda> p. (())\<^sub>e)"

text \<open> An operation requires that precondition holds, and that following the update the postcondition(s)
  also hold. \<close>

lemma wlp_proc_ret [wp]: "wlp (proc_ret e) retp[r. @(P r)] = (\<forall> r. \<guillemotleft>r\<guillemotright> = e \<longrightarrow> @(P r))\<^sub>e"
  by (auto simp add: wlp_alt_def proc_ret_def ret_pred_def)

lemma pre_proc_ret: "pre (proc_ret e) = (\<lambda> s. True)"
  by (simp add: wp_alt_def proc_ret_def)

lemma pre_zop [wp, code_unfold]: "pre (mk_zop P \<sigma> Q R v) = [\<lambda> \<s>. P v \<s> \<and> Q v \<s>]\<^sub>e"
  by (simp add: mk_zop_def pre_proc_ret wp, subst_eval)

lemma wlp_zop [wp]: 
  "wlp (mk_zop P \<sigma> Q R v) retp[r. b] = [\<lambda> \<s>. P v \<s> \<longrightarrow> Q v \<s> \<longrightarrow> (\<sigma> v \<dagger> [\<lambda> \<s>. b \<s>]\<^sub>e) \<s>]\<^sub>e"
  by (simp add: mk_zop_def pre_proc_ret wp)

(*
lemma wp_zop [wp, code_unfold]: "wp (mk_zop P \<sigma> Q R v) b = [\<lambda> \<s>. P v \<s> \<and> Q v \<s> \<and> (\<sigma> v \<dagger> [\<lambda> \<s>. b \<s>]\<^sub>e) \<s>]\<^sub>e"
  by (simp add: mk_zop_def wp)

lemma wlp_zop [wp, code_unfold]: "wlp (mk_zop P \<sigma> Q v) b = [\<lambda> \<s>. P v \<s> \<longrightarrow> Q v \<s> \<longrightarrow> (\<sigma> v \<dagger> [\<lambda> \<s>. b \<s>]\<^sub>e) \<s>]\<^sub>e"
  by (simp add: mk_zop_def wp)

lemma itree_pre_zop [dpre]: "itree_pre (mk_zop P \<sigma> Q v) = [\<lambda> \<s>. P v \<s>]\<^sub>e"
  by (simp add: mk_zop_def dpre wp)

lemma itree_rel_zop [itree_rel]: "itree_rel (mk_zop P \<sigma> Q v) = {(x, z). P v x \<and> Q v x \<and> z = \<sigma> v x}"
  by (simp add: mk_zop_def itree_rel relcomp_unfold)

lemma mk_zop_state_sat: "\<lbrakk> P v s; Q v s \<rbrakk> \<Longrightarrow> mk_zop P \<sigma> Q v s = Ret (\<sigma> v s)"
  by (simp add: mk_zop_def seq_itree_def kleisli_comp_def assume_def test_def assigns_def)
*)

subsection \<open> Promotion \<close>

text \<open> We implement a promotion scheme where we can extract the local state from a larger
  global state in order to execute an operation on the former. This requires that we 
  define a promotion lens. \<close>

definition promotion_lens ::
  "('ls \<Longrightarrow> 'g) \<comment> \<open> The collection of local states in the global state \<close>
    \<Rightarrow> ('i \<Rightarrow> 'l \<Longrightarrow> 'ls) \<comment> \<open> An indexed lens for individuals from the collection, (see @{const collection_lens})\<close>
    \<Rightarrow> 'i \<Rightarrow> 'l \<Longrightarrow> 'g" \<comment> \<open> An indexed lens giving a local state at each index \<close>
  where
"promotion_lens x pl = (\<lambda> v. dyn_lens_poly pl x (\<lambda> s. v))"

text \<open> The next gets the set of indices for which a promotion is defined \<close>

definition promotion_type :: "('ls \<Longrightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'l \<Longrightarrow> 'ls) \<Rightarrow> 'g \<Rightarrow> \<bbbP> 'i" where
[expr_defs]: "promotion_type a cl = (\<lambda> s. {i. s \<in> \<S>\<^bsub>cl i ;\<^sub>L a\<^esub>})"

expr_constructor promotion_type

lemma promotion_type_list [simp, code_unfold]: 
  "vwb_lens a \<Longrightarrow> promotion_type a list_collection_lens = ({0..<length($a)})\<^sub>e"
  by (simp add: promotion_type_def source_lens_comp source_list_collection_lens wb_lens.source_UNIV, expr_auto)

lemma promotion_type_pfun [simp, code_unfold]:
  "vwb_lens a \<Longrightarrow> promotion_type a pfun_collection_lens = (dom($a))\<^sub>e"
  by (simp add: promotion_type_def source_lens_comp source_pfun_collection_lens wb_lens.source_UNIV, expr_simp)

text \<open> Since the set of acceptable parameters of an operation can depend on the state, we need to 
  lift the type expression as part of the type promotion. \<close>

definition promoted_type :: "('ls \<Longrightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'l \<Longrightarrow> 'ls) \<Rightarrow> ('l \<Rightarrow> 'a set) \<Rightarrow> 'g \<Rightarrow> ('i \<times> 'a) set" where
"promoted_type a cl A = (\<lambda> s. Sigma (promotion_type a cl s) (\<lambda> i. (A \<up> a:cl(i)) s))"

text \<open> The simple case for type promotion is when there is no dependency on the state, as shown
  below. \<close>

lemma promoted_type_nodep [simp, code_unfold]: 
  "promoted_type a cl (\<guillemotleft>A\<guillemotright>)\<^sub>e = (promotion_type a cl \<times> \<guillemotleft>A\<guillemotright>)\<^sub>e"
  by (simp add: promoted_type_def usubst, simp add: SEXP_def)

text \<open> Promoting an operation first checks whether the promotion lens is defined for the given
  index. If not, it deadlocks. Otherwise, the operation is run on the local state, which is
  then injected back into the global state. \<close>

definition promote_operation :: "('ls \<Longrightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'l \<Longrightarrow> 'ls) \<Rightarrow> ('e, 'a, 'b, 'l) operation \<Rightarrow> ('e, 'i \<times> 'a, 'b, 'g) operation" where
"promote_operation x pl P = 
  (let a = promotion_lens x pl in (\<lambda> (i, v). promote_iproc (a i) (P v)))"

text \<open> The following notation allows us to promote an operation using the inferred collection lens. \<close>

syntax "_promote_op" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("promote-op")
translations "_promote_op a P" == "CONST promote_operation a (CONST collection_lens) P"

text \<open> Promotion of an operation constructed from a precondition and update requires that we lift
       the underlying expressions and update. \<close>

definition promote_pre :: 
  "('ls \<Longrightarrow> 'g) 
    \<Rightarrow> ('i \<Rightarrow> 'l \<Longrightarrow> 'ls) 
    \<Rightarrow> ('a \<Rightarrow> 'l \<Rightarrow> bool) 
    \<Rightarrow> 'i \<times> 'a \<Rightarrow> 'g \<Rightarrow> bool" where 
  "promote_pre x cl P = (\<lambda> (a, p). ((P p) \<up> x:cl(a) \<and> \<^bold>D(x:cl(a)))\<^sub>e)"

lemma promote_mk_zop [wp, code_unfold]:
  "\<lbrakk> vwb_lens x; \<And> i. mwb_lens (cl i) \<rbrakk> \<Longrightarrow>
   promote_operation x cl (mk_zop P \<sigma> Q R) 
    = mk_zop 
        (\<lambda> (a, p). ((P p) \<up> x:cl(a) \<and> \<^bold>D(x:cl(a)))\<^sub>e) 
        (\<lambda> (a, p). (\<sigma> p) \<up>\<^sub>s x:cl(a))
        (\<lambda> (a, p). (Q p) \<up> x:cl(a))
        (\<lambda> (a, p). (R p) \<up> x:cl(a))"
  by (auto simp add: promote_operation_def mk_zop_def Let_unfold promotion_lens_def fun_eq_iff promote_iproc_def proc_ret_def
      assume_def seq_itree_def kleisli_comp_def test_def expr_defs assigns_def lens_defs lens_source_def)

text \<open> These are needed so that the code generator can apply promotion \<close>

declare mwb_list_collection_lens [code_unfold]
declare pfun_collection_lens_mwb [code_unfold]


syntax
  "_preserves"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "preserves" 40)
  "_preserves_under" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ preserves _ under _" [40, 0, 40] 40)
  "_establishes"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "establishes" 40)

translations
  "_preserves S P" => "H{P} S {_. P}"
  "_preserves_under S P Q" => "H{P \<and> Q} S {_. P}"
  "_establishes \<sigma> P" => "H{CONST True} \<langle>\<sigma>\<rangle>\<^sub>a {P}"

subsection \<open> Proof Automation \<close>

method z_wlp uses add = (hoare_wlp_auto add: z_defs add)
method z_wlp_auto uses add = (hoare_wlp_auto add: z_defs z_locale_defs add)

method zpog uses add =
  (hoare_wlp add: z_defs add; (clarify)?; 
   expr_taut; 
   ((clarsimp del: notI)?; 
    (((erule conjE | rule conjI | erule disjE | rule impI); (clarsimp del: notI)?)+)?))
method zpog_full uses add = (zpog add: z_locale_defs add)

end