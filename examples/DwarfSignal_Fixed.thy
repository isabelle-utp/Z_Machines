section \<open> Dwarf Signal \<close>

theory DwarfSignal_Fixed
  imports "Z_Machines.Z_Machine"
begin                

subsection \<open> State Space \<close>

enumtype LampId = L1 | L2 | L3

type_synonym Signal = "LampId set"

enumtype ProperState = dark | stop | warning | drive

definition "ProperState = {dark, stop, warning, drive}"

fun signalLamps :: "ProperState \<Rightarrow> LampId set" where
"signalLamps dark = {}" |
"signalLamps stop = {L1, L2}" |
"signalLamps warning = {L1, L3}" |
"signalLamps drive = {L2, L3}"

lemma signalLamps: "signalLamps x \<in> {{}, {L1, L2}, {L1, L3}, {L2, L3}}"
  by (cases x; simp)

zstore Dwarf = 
  last_proper_state :: "ProperState"
  turn_off :: "LampId set"
  turn_on  :: "LampId set"
  last_state :: "Signal"
  current_state :: "Signal"
  desired_proper_state :: "ProperState"
  where 
    "signalLamps desired_proper_state = (current_state - turn_off) \<union> turn_on"
    "turn_on \<inter> turn_off = {}"

subsection \<open> Operations \<close>

zoperation SetNewProperState =
  over Dwarf
  params st\<in>"ProperState - {last_proper_state}"
  pre "current_state = signalLamps desired_proper_state \<and> (desired_proper_state = stop \<longrightarrow> st \<noteq> drive)"
  update "[last_proper_state\<Zprime> = desired_proper_state
          ,turn_off\<Zprime> = current_state - signalLamps st
          ,turn_on\<Zprime> = signalLamps st - current_state
          ,last_state\<Zprime> = current_state
          ,desired_proper_state\<Zprime> = st]"

zoperation TurnOff =
  over Dwarf
  params l\<in>turn_off 
  update "[turn_off\<Zprime> = turn_off - {l}
          ,turn_on\<Zprime> = turn_on - {l}
          ,last_state\<Zprime> = current_state
          ,current_state\<Zprime> = current_state - {l}]"

zoperation TurnOn =
  over Dwarf
  params l\<in>turn_on
  pre "turn_off = {}"
  update "[turn_off\<Zprime> = turn_off - {l}
          ,turn_on\<Zprime> = turn_on - {l}
          ,last_state\<Zprime> = current_state
          ,current_state\<Zprime> = current_state \<union> {l}]"

zoperation Shine =
  over Dwarf
  params l\<in>"{current_state}"

definition Init :: "Dwarf subst" where
  [z_defs]:
  "Init = 
  [ last_proper_state \<leadsto> stop
  , turn_off \<leadsto> {}
  , turn_on \<leadsto> {}
  , last_state \<leadsto> signalLamps stop
  , current_state \<leadsto> signalLamps stop
  , desired_proper_state \<leadsto> stop ]"

zmachine DwarfSignal = 
  init Init
  operations SetNewProperState TurnOn TurnOff Shine
animate DwarfSignal

subsection \<open> Structural Invariants \<close>

lemma "Init establishes Dwarf_inv"
  by z_wlp_auto

lemma "(SetNewProperState p) preserves Dwarf_inv"
  by z_wlp_auto

lemma TurnOn_correct: "(TurnOn l) preserves Dwarf_inv"
  by z_wlp_auto

lemma TurnOff_correct: "(TurnOff l) preserves Dwarf_inv"
  by z_wlp_auto  

lemma Shine_correct: "(Shine l) preserves Dwarf_inv"
  by z_wlp_auto


lemma 
  shows "deadlock_free (z_machine \<sigma> Ops)"
  oops

lemma "`Dwarf_inv \<longrightarrow> (\<exists> l. wp (zop_event shine Shine_type Shine) Dwarf_inv)`"
  apply (simp add: wp Dwarf_inv_def zop_event_def Dwarf_def Shine_def Shine_type_def TurnOn_def usubst_eval)
  done

subsection \<open> Requirements \<close>

subsubsection \<open> NeverShowAll \<close>

zexpr NeverShowAll 
  is "current_state \<noteq> {L1, L2, L3}"

lemma "(SetNewProperState p) preserves NeverShowAll"
  by z_wlp_auto

lemma TurnOn_NeverShowAll: "TurnOn l preserves NeverShowAll under Dwarf_inv"
proof zpog_full
  fix turn_on :: "\<bbbP> LampId" and current_state :: "\<bbbP> LampId" and desired_proper_state :: ProperState
  assume 
    1: "signalLamps desired_proper_state = current_state \<union> turn_on" and
    2: "current_state \<noteq> {L1, L2, L3}" and
    3: "l \<in> turn_on"
  have "current_state \<union> turn_on \<in> {{}, {L1, L2}, {L1, L3}, {L2, L3}}"
    by (metis "1" signalLamps)

  with 2 3 show "insert l current_state \<noteq> {L1, L2, L3}"
    by (smt (verit, best) LampId.distinct(2) LampId.distinct(4) LampId.distinct(6) UnI2 Un_insert_left insertE insert_absorb insert_absorb2 insert_commute insert_ident singleton_insert_inj_eq)
qed

lemma TurnOff_NeverShowAll: "TurnOff l preserves NeverShowAll"
  by zpog_full
     (metis (full_types) Diff_empty Diff_insert0 LampId.exhaust insertCI insert_Diff insert_absorb)

subsubsection \<open> MaxOneLampChange \<close>

zexpr MaxOneLampChange
  is "\<exists> l. current_state - last_state = {l} \<or> last_state - current_state = {l} \<or> last_state = current_state"

lemma "(SetNewProperState p) preserves MaxOneLampChange"
  by z_wlp_auto

subsubsection \<open> ForbidStopToDrive \<close>

zexpr ForbidStopToDrive
  is "last_proper_state = stop \<longrightarrow> desired_proper_state \<noteq> drive"

lemma "(SetNewProperState p) preserves ForbidStopToDrive"
  by z_wlp_auto  

subsubsection \<open> DarkOnlyToStop \<close>

zexpr DarkOnlyToStop
  is "last_proper_state = dark \<longrightarrow> desired_proper_state = stop"

subsubsection \<open> DarkOnlyFromStop \<close>

zexpr DarkOnlyFromStop
  is "desired_proper_state = dark \<longrightarrow> last_proper_state = stop"

subsection \<open> All Requirements \<close>

zexpr DwarfReq
  is "NeverShowAll \<and> MaxOneLampChange \<and> ForbidStopToDrive \<and> DarkOnlyToStop \<and> DarkOnlyFromStop"


(*
definition "CheckReq = 
  (\<questiondown>\<not> @NeverShowAll? \<Zcomp> violation!(STR ''NeverShowAll'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @MaxOneLampChange? \<Zcomp> violation!(STR ''MaxOneLampChange'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @ForbidStopToDrive? \<Zcomp> violation!(STR ''ForbidStopToDrive'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @DarkOnlyToStop? \<Zcomp> violation!(STR ''DarkOnlyToStop'') \<rightarrow> Skip) \<box>
  (\<questiondown>\<not> @DarkOnlyFromStop? \<Zcomp> violation!(STR ''DarkOnlyFromStop'') \<rightarrow> Skip)"
*)

end