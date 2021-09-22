theory TelephoneExchange
  imports "Z_Machines.Z_Machine"
begin unbundle Z_Syntax

type_synonym digit = nat
type_synonym subs = "digit list"

definition Digit :: "\<bbbP> digit" where "Digit = {0..9}"

consts 
  Subs :: "\<bbbP> (digit list)" 

definition "Valid = {n \<in> seq Digit. \<exists> s \<in> Subs. n \<subseteq> s}"

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

definition st :: "subrec \<leftrightarrow> Status" where "st = {(x, y). y = fst x}"
definition num :: "subrec \<leftrightarrow> subs" where "num = {(x, y). y = snd x}"


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

zoperation LiftFree =
  params s \<in> Subs
  pre "s \<in> Free"
  update "[Free\<Zprime> = Free - {s}
          ,Unavailable\<Zprime> = Unavailable
          ,cal\<Zprime> = cal \<union> {s \<mapsto> (seize, [])}]"

zoperation LiftSuspended =
  params s \<in> Subs
  pre "(s, suspended) \<in> connected\<^sup>\<sim> \<Zcomp> cal \<Zcomp> st"
  update "[cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (speech, s)}]"

end