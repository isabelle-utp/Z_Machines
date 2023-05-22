section \<open> Incubator \<close>

theory Incubator
  imports "Z_Machines.Z_Machine"
begin

subsection \<open> Constants and Store \<close>

definition MIN_TEMP :: \<int> where
[z_defs]: "MIN_TEMP = 15"

definition MAX_TEMP :: \<int> where
[z_defs]: "MAX_TEMP = 30"

definition TEMP :: "\<bbbP> \<int>" where
"TEMP = {MIN_TEMP..MAX_TEMP}"

zstore IncubatorMonitor = 
  temp :: \<int>
  where "MIN_TEMP \<le> temp" "temp \<le> MAX_TEMP"

subsection \<open> Operations \<close>

zoperation Increment =
  over IncubatorMonitor
  pre "temp < MAX_TEMP"
  update "[temp\<Zprime> = temp + 1]"

zoperation Decrement =
  over IncubatorMonitor
  pre "temp > MIN_TEMP" \<comment> \<open> Change to @{term "(temp \<ge> MIN_TEMP)\<^sub>e"} to break the invariant \<close>
  update "[temp\<Zprime> = temp - 1]"

zoperation GetTemp =
  over IncubatorMonitor
  emit temp

zinit IncubatorInit =
  over IncubatorMonitor
  update "[temp \<leadsto> 20]"

subsection \<open> Animation \<close>

zmachine Incubator_Anim =
  init IncubatorInit
  invariant IncubatorMonitor_inv
  operations GetTemp Increment Decrement

animate Incubator_Anim

subsection \<open> Verification \<close>

lemma Increment_correct [hoare_lemmas]: 
  "Increment() preserves IncubatorMonitor_inv"
  by zpog_full

lemma Decrement_correct [hoare_lemmas]: 
  "Decrement() preserves IncubatorMonitor_inv"
  by zpog_full

lemma GetTemp_correct [hoare_lemmas]: 
  "GetTemp v preserves IncubatorMonitor_inv"
  by zpog_full

lemma IncubatorInit_correct [hoare_lemmas]: 
  "IncubatorInit establishes IncubatorMonitor_inv"
  by zpog_full

zmachine Incubator =
  init IncubatorInit
  operations Increment Decrement

lemma dlockf_Incubator: "deadlock_free Incubator"
  by (deadlock_free, linarith)

text \<open> Deadlock freedom requires that one operation is enable at any time. We exclude 
  @{const GetTemp}, because it exists to show the current temperature and so is trivally always
  enables. The machine consisting only of @{const Increment} and @{const Decrement} is deadlock-free
  because the system must always be in a state where the current temperature is less than the maximum
  or greater than the minimum. \<close>

end
  