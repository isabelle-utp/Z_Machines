section \<open> Building Entry System \<close>

theory BuildingEntry
  imports "Z_Machines.Z_Machine"
begin

term subst_upd

type_synonym staff = \<nat>

consts 
  Staff :: "staff set"
  maxentry :: "\<nat>"

schema ASystem = 
  s :: "\<bbbP> staff"
  where "s \<in> \<bbbF> Staff" "#s < maxentry"

record_default ASystem

zoperation AEnterBuilding =
  over ASystem
  params p\<in>Staff
  pre "#s < maxentry \<and> p \<notin> s"
  update "[s \<leadsto> s \<union> {p}]"

zoperation ALeaveBuilding =
  over ASystem
  params p\<in>Staff
  pre "p \<in> s"
  update "[s \<leadsto> s - {p}]"

zmachine ABuildingEntry =
  over ASystem
  init "[s \<leadsto> {}]"
  operations AEnterBuilding ALeaveBuilding

def_consts 
  Staff = "{0..10}"
  maxentry = "5"

animate ABuildingEntry

schema CSystem =
  l :: "staff list"
  where 
    "l \<in> iseq Staff" "#l \<le> maxentry"

record_default CSystem

zoperation CEnterBuilding =
  params p \<in> Staff
  pre "#l < maxentry \<and> p \<notin> ran l"
  update "[l \<leadsto> l @ [p]]"

definition ListRetrieveSet :: "CSystem \<Rightarrow> (_, ASystem) itree" where
"ListRetrieveSet = \<questiondown>CSystem? ;; \<langle>\<lblot>s \<leadsto> set l\<rblot>\<rangle>\<^sub>a"

definition SetRetrieveList :: "ASystem \<Rightarrow> (_, CSystem) itree" where
"SetRetrieveList = \<questiondown>ASystem? ;; \<langle>\<lblot>l \<leadsto> sorted_list_of_set s\<rblot>\<rangle>\<^sub>a"

find_theorems "(\<circ>\<^sub>s)"

lemma "ListRetrieveSet ;; SetRetrieveList = \<questiondown>CSystem?"
  apply (simp add: ListRetrieveSet_def SetRetrieveList_def ASystem_inv_def assigns_seq kcomp_assoc assigns_assume assigns_seq_comp usubst usubst_eval)

lemma "p \<in> Staff \<Longrightarrow> (ListRetrieveSet ;; AEnterBuilding p) \<sqsubseteq> (CEnterBuilding p ;; ListRetrieveSet)"
  unfolding ListRetrieveSet_def AEnterBuilding_def CEnterBuilding_def
  apply refine_auto
   apply (simp add: distinct_card)
  done
  
end

