section \<open> Incubator \<close>

theory Incubator_locales
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
  where mintemp: "MIN_TEMP \<le> temp" maxtemp: "temp \<le> MAX_TEMP"

zoperation Increment =
  over IncubatorMonitor
  pre "temp < MAX_TEMP"
  update "[temp\<Zprime> = temp + 1]"

lemma Increment_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} Increment() \<^bold>{IncubatorMonitor_inv\<^bold>}"
  unfolding Increment_def IncubatorMonitor_inv_def  
proof (hoare_wlp_auto)
  fix temp
  assume pres: "temp < MAX_TEMP" and inv: "IncubatorMonitor temp" 
  then interpret IncubatorMonitor temp
    by simp
  show "IncubatorMonitor (temp + 1)"
  proof
    show "MIN_TEMP \<le> temp + 1"
      using mintemp by auto
    show "temp + 1 \<le> MAX_TEMP"
      by (simp add: add1_zle_eq pres)
  qed
qed

zoperation Decrement =
  over IncubatorMonitor
  pre "temp > MIN_TEMP" \<comment> \<open> Change to @{term "(temp \<ge> MIN_TEMP)\<^sub>e"} to break the invariant \<close>
  update "[temp\<Zprime> = temp - 1]"

lemma Decrement_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} Decrement() \<^bold>{IncubatorMonitor_inv\<^bold>}"
  unfolding Decrement_def IncubatorMonitor_inv_def IncubatorMonitor_def by hoare_wlp

zoperation GetTemp =
  over IncubatorMonitor
  params currentTemp \<in> TEMP
  where "temp = currentTemp"

lemma GetTemp_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} GetTemp v \<^bold>{IncubatorMonitor_inv\<^bold>}"
  unfolding GetTemp_def IncubatorMonitor_inv_def IncubatorMonitor_def by hoare_wlp

zmachine Incubator =
  init "[temp \<leadsto> 20]"
  operations Increment Decrement GetTemp

animate Incubator

end
  