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

instantiation Incubator_chan :: "show"
begin

fun show_Incubator_chan :: "Incubator_chan \<Rightarrow> String.literal" where
"show_Incubator_chan (increment_C x) = STR ''Increment '' + show x" |
"show_Incubator_chan (decrement_C x) = STR ''Decrement '' + show x" |
"show_Incubator_chan (getTemp_C x) = STR ''GetTemp '' + show x"

instance ..

end

definition z_machine_main2 :: "(('e, 's) htree) list \<Rightarrow> ('e::show, 's) htree" where
"z_machine_main2 Ops = foldr (\<box>) Ops Stop"

definition z_machine2 :: "('s::default) subst \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> (('e::show, 's) htree) list \<Rightarrow> 'e process" where
[code_unfold]: "z_machine2 Init Inv Ops = process Init (loop (z_machine_main2 Ops))"

definition "Incubator2 =
z_machine2 [temp \<leadsto> 20] (\<lambda>\<s>. True)
 [zop_event increment Increment_type Increment, zop_event decrement Decrement_type Decrement,
  zop_event getTemp GetTemp_type GetTemp]"

animate Incubator2

end
  