section \<open> Incubator \<close>

theory Incubator
  imports "Z_Machines.Z_Machine"
begin

consts MAX_TEMP :: \<int>
consts MIN_TEMP :: \<int>

definition "TEMP = {MIN_TEMP..MAX_TEMP}"

def_consts 
  MAX_TEMP = 30
  MIN_TEMP = 15

zstore IncubatorMonitor = 
  temp :: \<int>
  where "MIN_TEMP \<le> temp" "temp \<le> MAX_TEMP"

zoperation Increment =
  over IncubatorMonitor
  pre "temp < MAX_TEMP"
  update "[temp\<Zprime> = temp + 1]"

lemma Increment_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} Increment() \<^bold>{IncubatorMonitor_inv\<^bold>}"
  by zpog_full

zoperation Decrement =
  over IncubatorMonitor
  pre "temp > MIN_TEMP" \<comment> \<open> Change to @{term "(temp \<ge> MIN_TEMP)\<^sub>e"} to break the invariant \<close>
  update "[temp\<Zprime> = temp - 1]"

lemma Decrement_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} Decrement() \<^bold>{IncubatorMonitor_inv\<^bold>}"
  by zpog_full

zoperation GetTemp =
  over IncubatorMonitor
  params currentTemp \<in> "{temp}"

lemma GetTemp_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} GetTemp v \<^bold>{IncubatorMonitor_inv\<^bold>}"
  by zpog_full

zmachine Incubator =
  init "[temp \<leadsto> 20]"
  operations Increment Decrement GetTemp

animate Incubator

end
  