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

schema IncubatorMonitor = 
  temp :: \<int>
  where "MIN_TEMP \<le> temp" "temp \<le> MAX_TEMP"

record_default IncubatorMonitor

zoperation Increment =
  over IncubatorMonitor
  pre "temp < MAX_TEMP"
  update "[temp\<Zprime> = temp + 1]"

lemma Increment_correct: "\<^bold>{IncubatorMonitor\<^bold>} Increment() \<^bold>{IncubatorMonitor\<^bold>}"
  unfolding Increment_def IncubatorMonitor_inv_def by hoare_wlp

zoperation Decrement =
  over IncubatorMonitor
  pre "temp > MIN_TEMP" \<comment> \<open> Change to @{term "(temp \<ge> MIN_TEMP)\<^sub>e"} to break the invariant \<close>
  update "[temp\<Zprime> = temp - 1]"

lemma Decrement_correct: "\<^bold>{IncubatorMonitor\<^bold>} Decrement() \<^bold>{IncubatorMonitor\<^bold>}"
  unfolding Decrement_def IncubatorMonitor_inv_def by hoare_wlp

zoperation GetTemp =
  over IncubatorMonitor
  params currentTemp \<in> TEMP
  where "temp = currentTemp"

lemma GetTemp_correct: "\<^bold>{IncubatorMonitor\<^bold>} GetTemp v \<^bold>{IncubatorMonitor\<^bold>}"
  unfolding GetTemp_def IncubatorMonitor_inv_def by hoare_wlp

zmachine Incubator =
  init "[temp \<leadsto> 20]"
  operations Increment Decrement GetTemp

animate Incubator

end
  