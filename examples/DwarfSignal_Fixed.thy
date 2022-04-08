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
  params st\<in>"ProperState - {desired_proper_state}"
  pre "current_state = signalLamps desired_proper_state 
       \<and> (desired_proper_state = stop \<longrightarrow> st \<noteq> drive)
       \<and> (desired_proper_state = dark \<longrightarrow> st = stop)
       \<and> (st = dark \<longrightarrow> desired_proper_state = stop)"
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
  by zpog_full

lemma "(SetNewProperState p) preserves Dwarf_inv"
  by (zpog_full, auto)

lemma TurnOn_correct: "(TurnOn l) preserves Dwarf_inv"
  by (zpog_full, auto)

lemma TurnOff_correct: "(TurnOff l) preserves Dwarf_inv"
  by (zpog_full, auto)

lemma Shine_correct: "(Shine l) preserves Dwarf_inv"
  by (zpog_full)

subsection \<open> Requirements \<close>

subsubsection \<open> NeverShowAll \<close>

zexpr NeverShowAll 
  is "current_state \<noteq> {L1, L2, L3}"

lemma SetNewProperState_NeverShowAll: "(SetNewProperState p) preserves NeverShowAll"
  by zpog_full

lemma TurnOn_NeverShowAll: "TurnOn l preserves NeverShowAll under Dwarf_inv"
proof (zpog_full)
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

lemma SetNewProperState_MaxOneLampChange: "(SetNewProperState p) preserves MaxOneLampChange"
  by zpog

lemma TurnOn_MaxOneLampChange: "(TurnOn l) preserves MaxOneLampChange"
  by (zpog_full; auto)

lemma TurnOff_MaxOneLampChange: "(TurnOff l) preserves MaxOneLampChange"
  by (zpog_full; auto)

subsubsection \<open> ForbidStopToDrive \<close>

zexpr ForbidStopToDrive
  is "last_proper_state = stop \<longrightarrow> desired_proper_state \<noteq> drive"

lemma SetNewProperState_ForbidStopToDrive: "(SetNewProperState p) preserves ForbidStopToDrive"
  by zpog  

lemma "(TurnOn l) preserves ForbidStopToDrive"
  by zpog

lemma "(TurnOff l) preserves ForbidStopToDrive"
  by zpog

subsubsection \<open> DarkOnlyToStop \<close>

zexpr DarkOnlyToStop
  is "last_proper_state = dark \<longrightarrow> desired_proper_state = stop"

lemma SetNewProperState_DarkOnlyToStop: "(SetNewProperState p) preserves DarkOnlyToStop"
  by zpog

subsubsection \<open> DarkOnlyFromStop \<close>

zexpr DarkOnlyFromStop
  is "desired_proper_state = dark \<longrightarrow> last_proper_state = stop"

lemma SetNewProperState_DarkOnlyFromStop: "(SetNewProperState p) preserves DarkOnlyFromStop"
  by zpog

subsection \<open> All Requirements \<close>

zexpr DwarfReq
  is "NeverShowAll \<and> MaxOneLampChange \<and> ForbidStopToDrive \<and> DarkOnlyToStop \<and> DarkOnlyFromStop"

lemma SetNewProperState_DwarfReq: "(SetNewProperState p) preserves DwarfReq"
  by (auto intro!: hl_conj simp add: DwarfReq_def SetNewProperState_NeverShowAll 
      SetNewProperState_MaxOneLampChange SetNewProperState_ForbidStopToDrive 
      SetNewProperState_DarkOnlyToStop SetNewProperState_DarkOnlyFromStop)

end