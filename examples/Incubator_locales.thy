section \<open> Incubator \<close>

theory Incubator_locales
  imports "Z_Machines.Z_Machine" "HOL-Library.Code_Target_Int"
begin

consts MAX_TEMP :: \<nat>
consts MIN_TEMP :: \<nat>

definition "TEMP = {MIN_TEMP..MAX_TEMP}"

def_consts 
  MAX_TEMP = 30
  MIN_TEMP = 15

zstore IncubatorMonitor = 
  temp :: \<nat>
  where mintemp: "MIN_TEMP \<le> temp" maxtemp: "temp \<le> MAX_TEMP"

zoperation Increment =
  over IncubatorMonitor
  pre "temp < MAX_TEMP"
  update "[temp\<Zprime> = temp + 1]"

lemma Increment_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} Increment() \<^bold>{IncubatorMonitor_inv\<^bold>}"
proof zpog
  fix temp
  assume pres: "temp < MAX_TEMP" and inv: "IncubatorMonitor temp" 
  then interpret IncubatorMonitor temp
    by simp
  show "IncubatorMonitor (Suc temp )"
  proof
    show "MIN_TEMP \<le> Suc temp"
      using mintemp by auto
    show "Suc temp \<le> MAX_TEMP"
      using pres by auto
  qed
qed

zoperation Decrement =
  over IncubatorMonitor
  pre "temp > MIN_TEMP" \<comment> \<open> Change to @{term "(temp \<ge> MIN_TEMP)\<^sub>e"} to break the invariant \<close>
  update "[temp\<Zprime> = temp - 1]"

lemma Decrement_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} Decrement() \<^bold>{IncubatorMonitor_inv\<^bold>}"
  by (zpog_full; simp)

zoperation GetTemp =
  over IncubatorMonitor
  params currentTemp \<in> TEMP
  where "temp = currentTemp"

lemma GetTemp_correct: "\<^bold>{IncubatorMonitor_inv\<^bold>} GetTemp v \<^bold>{IncubatorMonitor_inv\<^bold>}"
  by zpog_full

zmachine Incubator =
  init "[temp \<leadsto> 20]"
  operations Increment Decrement GetTemp

animate Incubator

end
  