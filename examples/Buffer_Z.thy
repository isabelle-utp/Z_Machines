section \<open> Buffer Z Machine \<close>

theory Buffer_Z
  imports "Z_Machines.Z_Machine"
begin lit_vars

consts VAL :: "integer set"

schema Buffer_state =
  buf :: "integer list"

record_default Buffer_state

zoperation Input =
  over Buffer_state
  params v \<in> VAL
  update "[buf \<leadsto> buf @ [v]]"

zoperation Output =
  over Buffer_state
  params v \<in> VAL
  pre "length buf > 0"
  update "[buf \<leadsto> tl buf]"
  where "v = hd buf"

zoperation State =
  over Buffer_state
  params st \<in> "{buf}"

zmachine Buffer =
  init "[buf \<leadsto> []]"
  operations Input Output State

def_consts VAL = "{0,1,2,3}"

animate Buffer

end