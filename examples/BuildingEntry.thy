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
  where "#s < maxentry"

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

simulate ABuildingEntry

schema CSystem =
  l :: "staff list"
  where "distinct l \<and> #l \<le> maxentry"

zoperation CEnterBuilding =
  params p \<in> Staff
  pre "#l < maxentry \<and> p \<notin> set l"
  update "[l \<leadsto> l @ [p]]"

definition ListRetrieveSet :: "CSystem \<Rightarrow> ASystem" where
"ListRetrieveSet = \<lblot>s \<leadsto> set l\<rblot>"

lemma "\<langle>ListRetrieveSet\<rangle>\<^sub>a \<Zcomp> AEnterBuilding p = CEnterBuilding p \<Zcomp> \<langle>ListRetrieveSet\<rangle>\<^sub>a"
  oops

end

