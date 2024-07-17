section \<open> Buffer Z Machine \<close>

theory Buffer_Z
  imports "Z_Machines.Z_Machine"
begin lit_vars

consts VAL :: "int set"

zstore Buffer_state =
  buf :: "int list"
  v :: "int"
  where "set buf \<subseteq> VAL"

zoperation Input =
  over Buffer_state
  params x \<in> VAL
  update "[buf \<leadsto> buf @ [x]]"

lemma Input_inv [hoare_lemmas]: "Input x preserves Buffer_state_inv"
  by zpog_full

zoperation Output =
  over Buffer_state
  pre "length buf > 0"
  update "[buf \<leadsto> tl buf, v \<leadsto> hd buf]"
  output v

lemma Output_inv [hoare_lemmas]: "Output() preserves Buffer_state_inv"
  by zpog_full (meson in_mono list.set_sel(2))

zoperation State =
  over Buffer_state
  params st \<in> "{buf}"

lemma State_inv [hoare_lemmas]: "State st preserves Buffer_state_inv"
  by zpog_full

zmachine Buffer =
  init "[buf \<leadsto> []]"
  invariant "Buffer_state_inv"
  operations Input Output State

thm Buffer_def

lemma Buffer_deadlock_free: "VAL \<noteq> {} \<Longrightarrow> deadlock_free Buffer"
  by deadlock_free

def_consts VAL = "{0,1,2,3}"

animate Buffer

end