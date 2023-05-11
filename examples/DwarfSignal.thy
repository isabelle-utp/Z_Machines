section \<open> Dwarf Signal \<close>

theory DwarfSignal
  imports "Z_Machines.Z_Machine"
begin                

notation undefined ("???")

subsection \<open> State Space \<close>

enumtype LampId = L1 | L2 | L3

type_synonym Signal = "LampId set"

enumtype ProperState = dark | stop | warning | drive

fun signalLamps :: "ProperState \<Rightarrow> LampId set" where
"signalLamps dark = {}" |
"signalLamps stop = {L1, L2}" |
"signalLamps warning = {L1, L3}" |
"signalLamps drive = {L2, L3}"

text \<open> Could we have separate processes for the actual lamp and its controller? We would then
  try to verify that the controller preserves the lamp-based safety properties. The current
  set up doesn't preserve them. \<close>

zstore Dwarf = 
  last_proper_state :: "ProperState"
  turn_off :: "LampId set"
  turn_on  :: "LampId set"
  last_state :: "Signal"
  current_state :: "Signal"
  desired_proper_state :: "ProperState"
  where 
    "(current_state - turn_off) \<union> turn_on = signalLamps desired_proper_state"
    "turn_on \<inter> turn_off = {}"

subsection \<open> Operations and Machine \<close>

zoperation SetNewProperState =
  over Dwarf
  params st\<in>"ProperState - {desired_proper_state}"
  pre "current_state = signalLamps desired_proper_state"
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
  update "[turn_off\<Zprime> = turn_off - {l}
          ,turn_on\<Zprime> = turn_on - {l}
          ,last_state\<Zprime> = current_state
          ,current_state\<Zprime> = current_state \<union> {l}]"

zoperation Shine =
  over Dwarf
  emit current_state

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
  invariant Dwarf_inv
  operations SetNewProperState TurnOn TurnOff Shine

animate DwarfSignal

subsection \<open> Structural Invariants and Deadlock Freedom \<close>

lemma "Init establishes Dwarf_inv"
  by zpog_full

lemma [hoare_lemmas]: 
  "(SetNewProperState p) preserves Dwarf_inv"
  by (zpog_full; auto)

lemma [hoare_lemmas]: "TurnOn l preserves Dwarf_inv"
  by (zpog_full, auto)

lemma [hoare_lemmas]: "TurnOff l preserves Dwarf_inv"
  by (zpog_full, auto)  

lemma [hoare_lemmas]: "Shine l preserves Dwarf_inv"
  by (zpog_full; auto)

lemma deadlock_free_DwarfSignal: "deadlock_free DwarfSignal"
  by deadlock_free

subsection \<open> Requirements \<close>

zexpr NeverShowAll
  is "current_state \<noteq> {L1, L2, L3}"

zexpr MaxOneLampChange
  is "(\<exists> l. current_state - last_state = {l} \<or> last_state - current_state = {l} \<or> last_state = current_state)"

zexpr ForbidStopToDrive
  is "(last_proper_state = stop \<longrightarrow> desired_proper_state \<noteq> drive)"

zexpr DarkOnlyToStop
  is "(last_proper_state = dark \<longrightarrow> desired_proper_state = stop)"

zexpr DarkOnlyFromStop
  is "(desired_proper_state = dark \<longrightarrow> last_proper_state = stop)"

zexpr DwarfReq
  is "NeverShowAll \<and> MaxOneLampChange \<and> ForbidStopToDrive \<and> DarkOnlyToStop \<and> DarkOnlyFromStop"

zoperation ViolNeverShowAll =
  pre "\<not> NeverShowAll"

zmachine DwarfSignalTest = 
  init Init
  operations SetNewProperState TurnOn TurnOff Shine ViolNeverShowAll

animate DwarfSignalTest

lemma "(SetNewProperState p) preserves NeverShowAll"
  by zpog_full

lemma "(SetNewProperState p) preserves MaxOneLampChange"
  by zpog_full

lemma "(SetNewProperState p) preserves ForbidStopToDrive"
  apply zpog_full
  quickcheck
  oops

lemma "TurnOn l preserves NeverShowAll"
  apply zpog_full
  quickcheck
  oops

end