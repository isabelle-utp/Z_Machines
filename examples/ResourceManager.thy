section \<open> Resource Manager \<close>

theory ResourceManager
  imports "Z_Machines.Z_Machine"
begin 

consts RES :: "integer set"

schema ResourceManager =
  res  :: "integer set"
  free :: "integer set"
  where "free \<subseteq> res" "res \<subseteq> RES"

record_default ResourceManager
 
zoperation Allocate =
  over ResourceManager
  params r \<in> RES
  update "[free \<leadsto> free - {r}]"
  where "r \<in> free"

zoperation Allocate\<^sub>1 =
  over ResourceManager
  params r \<in> RES
  update "[free \<leadsto> free - {r}]"
  where "r \<in> free \<and> r = Min free"

zoperation Deallocate =
  over ResourceManager
  params r \<in> RES
  pre "r \<notin> free"
  update "[free \<leadsto> free \<union> {r}]"

lemma Allocate\<^sub>1_refines_Allocate: "Allocate r \<sqsubseteq> Allocate\<^sub>1 r"
  by (auto simp add: Allocate_def Allocate\<^sub>1_def input_in_rel dpre assigns_rel refined_by_def wp mk_zop_def
      seq_rel assume_rel test_rel relcomp_unfold)

zmachine ResourceManagerProc =
  init "[res \<leadsto> RES, free \<leadsto> RES]"
  operations "Allocate\<^sub>1" "Deallocate"

def_consts RES = "set (map integer_of_int [0..5])"

simulate ResourceManagerProc

end