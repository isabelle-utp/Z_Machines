section \<open> Z-style Operations \<close>

theory Z_Operations
  imports "ITree_UTP.ITree_UTP"
begin

text \<open> In the most basic form, and operation is simply an indexed Kleisli tree. The index type
  @{typ 'a} represents the inputs and outputs of the operation. \<close>

type_synonym ('e, 'a, 's) operation = "'a \<Rightarrow> ('e, 's) htree"

text \<open> Promoting an operation first checks whether the promotion lens is defined for the given
  index. If not, it deadlocks. Otherwise, the operation is run on the local state, which is
  then injected back into the global state. \<close>

definition promote_op :: "('i \<Rightarrow> ('ls \<Longrightarrow> 's)) \<Rightarrow> ('e, 'a, 'ls) operation \<Rightarrow> ('e, 'i \<times> 'a, 's) operation" where
"promote_op a P = (\<lambda> (i, v) s. if s \<in> \<S>\<^bsub>a i\<^esub> 
                               then P v (get\<^bsub>a i\<^esub> s) \<bind> (\<lambda> ls'. Ret (put\<^bsub>a i\<^esub> s ls'))
                               else deadlock)"

definition operation :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('e, 'a, 's) operation \<Rightarrow> ('e, 's) htree" where
"operation c P = c?(v) | pre (P v) \<rightarrow> P v"

definition io_operation :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('b \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b \<times> 's) htree) \<Rightarrow> ('e, 's) htree" where
"io_operation c d P = undefined"

method z_wlp uses add = (hoare_wlp_auto add: z_defs add)
method z_wlp_auto uses add = (hoare_wlp_auto add: z_defs z_locale_defs add)

method zpog uses add = 
  (hoare_wlp add: z_defs add; 
   expr_taut; 
   clarsimp del: notI;
   (((rule conjI | erule disjE); (clarsimp)?)+)?)
method zpog_full uses add = (zpog add: z_locale_defs add)

end