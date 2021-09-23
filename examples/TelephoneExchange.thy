theory TelephoneExchange
  imports "Z_Machines.Z_Machine"
begin unbundle Z_Syntax

type_synonym digit = integer
type_synonym subs = "digit list"

definition Digit :: "\<bbbP> digit" where "Digit = integer_of_int ` {0..9}"

term integer_of_int

consts 
  Subs :: "\<bbbP> (digit list)" 

definition "Valid = {n \<in> blists 6 Digit. \<exists> s \<in> Subs. n \<le> s}"

definition 
  "TelephoneExchange_axioms = (Subs \<in> \<bbbP> (seq Digit))"

enumtype Status = seize | dialling | unobtainable | connecting | ringing | speech | engaged | suspended

definition "Connected = {ringing , speech, suspended}"

definition "Established = Connected \<union> {connecting , engaged}"

type_synonym subrec = "Status \<times> digit list"

definition SubRec :: "Status \<leftrightarrow> digit list" where
"SubRec = {(s, n). (s = seize \<longleftrightarrow> n = []) 
                 \<and> (s = dialling \<longleftrightarrow> n \<in> Valid - Subs - {[]})
                 \<and> (s = unobtainable \<longleftrightarrow> n \<notin> Valid)
                 \<and> (s \<in> Established \<longleftrightarrow> n \<in> Subs)}"

definition st :: "subrec \<Zpfun> Status" where [simp]: "st = (\<lambda> x \<bullet> first x)"
definition num :: "subrec \<Zpfun> subs" where [simp]: "num = (\<lambda> x \<bullet> second x)"

no_syntax
  "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<Zcomp>" 54)
          
schema Exchange =
  Free :: "\<bbbP> subs"
  Unavailable :: "\<bbbP> subs"
  Callers :: "\<bbbP> subs"
  cal :: "subs \<leftrightarrow> subrec"
  connected :: "subs \<leftrightarrow> subs"
where
  "[Free, Unavailable, dom cal \<union> dom connected] partitions Subs"
  "Callers = dom ((cal \<Zcomp> st) \<Zrres> Connected)"
  "connected = Callers \<Zdres> (cal \<Zcomp> num)"

record_default Exchange

definition "InitExchange = [Free\<Zprime> = Subs, Unavailable\<Zprime> = {}, Callers\<Zprime> = {}, cal\<Zprime> = {}, connected\<Zprime> = {}]"

zoperation LiftFree =
  params s \<in> Subs
  pre "s \<in> Free"
  update "[Free\<Zprime> = Free - {s}
          ,cal\<Zprime> = cal \<union> {s \<mapsto> (seize, [])}]"

declare list_partitions_def [simp]

lemma "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange\<^bold>}LiftFree s\<^bold>{Exchange\<^bold>}"
  unfolding LiftFree_def Exchange_inv_def
  apply (hoare_wlp_auto)
   apply (auto simp add: Connected_def comp_pfun_graph pfun_graph_domres[THEN sym])
  apply (simp add: Domain_iff disjoint_iff rel_ranres_def)
  done

zoperation LiftSuspended =
  params s \<in> Subs
  pre "(s, suspended) \<in> connected\<^sup>\<sim> \<Zcomp> cal \<Zcomp> st" 
  update "[cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (speech, s)}]"

zoperation Answer =
  params s \<in> Subs
  pre "(s, ringing) \<in> connected\<^sup>\<sim> \<Zcomp> cal \<Zcomp> st"
  update "[Free\<Zprime> = Free - {s}, cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (speech, s)}]"

definition "nextstate n = 
  (if n \<in> Subs then connecting
   else if n \<in> Valid - Subs then dialling
   else unobtainable)"

zoperation Dial =
  params s \<in> Subs d \<in> Digit
  pre "(s, seize) \<in> cal \<Zcomp> st \<or> (s, dialling) \<in> cal \<Zcomp> st"
  update "[cal\<Zprime> = (let newnum = (cal \<Zcomp> num) s @ [d] in cal \<oplus> {s \<mapsto> (nextstate newnum, newnum)})]"

zoperation ClearAttempt =
  params s \<in> Subs
  pre "s \<in> dom cal \<and> (cal \<Zcomp> st) s \<in> {seize, dialling , connecting , engaged, unobtainable}"
  update "[Free\<Zprime> = Free \<union> {s}, cal\<Zprime> = {s} \<Zndres> cal]"

zoperation ClearLine =
  params s \<in> Subs
  pre "s \<in> dom cal \<and> (cal \<Zcomp> st) s \<in> {ringing , suspended}"
  update "[ Free\<Zprime> = Free \<union> {s, connected s}, cal\<Zprime> = {s} \<Zndres> cal
          , Callers\<Zprime> = Callers - {s, connected s}, connected\<Zprime> = {s} \<Zndres> connected]"

zoperation ClearConnect =
  params s \<in> Subs
  pre "s \<in> dom cal \<and> (cal \<Zcomp> st) s = speech"
  update "[ Free\<Zprime> = Free \<union> {s}
          , cal\<Zprime> = ({s} \<Zndres> cal) \<oplus> {connected s \<mapsto> (seize, [])}
          , Callers\<Zprime> = Callers - {s}
          , connected\<Zprime> = {s} \<Zndres> connected]"

zoperation ClearSuspend =
  params s \<in> Subs
  pre "s \<in> ran connected"
  update "[cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (suspended, s)}]"

zoperation ClearUnavail =
  params s \<in> Subs
  pre "s \<in> Unavailable"
  update "[Free\<Zprime> = Free \<union> {s}, Unavailable\<Zprime> = Unavailable - {s}]"

zoperation MakeUnavail =
  params s \<in> Subs
  pre "s \<in> dom cal \<and> (cal \<Zcomp> st) s \<in> {seize, dialling}"
  update "[Unavailable\<Zprime> = Unavailable \<union> {s}, cal\<Zprime> = {s} \<Zndres> cal]"

zoperation Connect2Ringing =
  params s \<in> Subs
  pre "s \<in> dom cal \<and> (cal \<Zcomp> st) s = connecting \<and> s \<notin> dom connected \<and> (cal \<Zcomp> num) s \<in> Free"
  update "[ Free\<Zprime> = Free - {s}
          , cal\<Zprime> = cal \<oplus> {s \<mapsto> (ringing, (cal \<Zcomp> num) s)}
          , Callers\<Zprime> = Callers \<union> {s}
          , connected\<Zprime> = connected \<oplus> {s \<mapsto> (cal \<Zcomp> num) s}]"

zoperation Connect2Engaged =
  params s \<in> Subs
  pre "s \<in> dom cal \<and> (cal \<Zcomp> st) s = connecting \<and> s \<notin> dom connected \<and> (cal \<Zcomp> num) s \<notin> Free"
  update "[ cal\<Zprime> = cal \<oplus> {s \<mapsto> (engaged, (cal \<Zcomp> num) s)} ]"
  

zmachine TelephoneExchange =
  over Exchange
  init "InitExchange"
  operations 
    LiftFree LiftSuspended Answer Dial 
    ClearAttempt ClearLine ClearConnect ClearSuspend ClearUnavail
    MakeUnavail
    Connect2Ringing Connect2Engaged
    
def_consts Subs = "{[1,2,3], [3,4,5], [6,7,8]}"

animate TelephoneExchange



end