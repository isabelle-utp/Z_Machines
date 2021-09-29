theory TelephoneExchange_locales
  imports Explorer "Z_Machines.Z_Machine"
begin unbundle Z_Syntax

term pdom

type_synonym digit = integer
type_synonym subs = "digit list"

definition Digit :: "\<bbbP> digit" where "Digit = integer_of_int ` {0..9}"

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

definition st :: "subrec \<Zpfun> Status" where [expr_defs]: "st = (\<lambda> x \<bullet> first x)"
definition num :: "subrec \<Zpfun> subs" where [expr_defs]: "num = (\<lambda> x \<bullet> second x)"

no_syntax
  "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<Zcomp>" 54)

zstore Exchange =
  Free :: "\<bbbP> subs"
  Unavailable :: "\<bbbP> subs"
  Callers :: "\<bbbP> subs"
  cal :: "subs \<Zpfun> subrec"
  connected :: "subs \<Zpfun> subs"
where
  parts: "[Free, Unavailable, dom cal \<union> ran connected] partitions Subs"
  Callers: "dom ((cal \<Zcomp> st) \<Zrres> Connected) = Callers"
  connected: "Callers \<Zdres> (cal \<Zcomp> num) = connected"
  nself: "dom connected \<inter> ran connected = {}" \<comment> \<open> Added by SF: no self connections \<close>
  connected_inj: "pfun_inj connected"

declare list_partitions_def [simp]

context Exchange
begin

lemma dom_connected_Callers: "dom connected = Callers"
  using invariants by (auto simp add: num_def st_def)

lemma dom_connected_subset_cal: "dom connected \<subseteq> dom cal"
  by (metis Domain_rel_domres Int_absorb Int_lower2 UNIV_def connected num_def pdom_UNIV_comp pdom_pabs rel_of_pfun_comp rel_of_pfun_dom)

lemma dom_suspended_connected: "dom ((cal \<Zcomp> st) \<Zrres> {suspended}) \<subseteq> dom connected"
  by (metis Connected_def Domain_mono dom_connected_Callers insert_subset invariants(2) rel_ranres_le subset_insertI)

end

definition "InitExchange = [Free\<Zprime> = Subs, Unavailable\<Zprime> = {}, Callers\<Zprime> = {}, cal\<Zprime> = {\<mapsto>}, connected\<Zprime> = 0]"

zoperation LiftFree =
  params s \<in> Subs
  pre "s \<in> Free"
  update "[Free\<Zprime> = Free - {s}
          ,cal\<Zprime> = cal \<oplus> {s \<mapsto> (seize, [])}]"



lemma LiftFree_correct: "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange_inv\<^bold>}LiftFree s\<^bold>{Exchange_inv\<^bold>}"
unfolding Exchange_inv_def LiftFree_def
proof (hoare_wlp_auto)
  fix Free :: \<open>\<bbbP> integer list\<close> and Unavailable :: \<open>\<bbbP> integer list\<close>
    and Callers :: \<open>\<bbbP> integer list\<close> and cal :: \<open>integer list \<Zpfun> Status \<times> integer list\<close> 
    and connected :: \<open>integer list \<Zpfun> integer list\<close>
  assume 
    pres: \<open>s \<in> Subs\<close> \<open>s \<in> Free\<close> and
    inv: \<open>Exchange Free Unavailable Callers cal connected\<close>
  then interpret P: Exchange Free Unavailable Callers cal connected
    by simp
    
  show \<open>Exchange (Free - {s}) Unavailable Callers (cal(s \<mapsto> (seize, []))\<^sub>p) connected\<close>
  proof
    from pres P.invariants show \<open>[Free - {s}, Unavailable, dom (cal(s \<mapsto> (seize, []))\<^sub>p) \<union> ran connected] partitions Subs\<close>
      by auto
  next    
    from pres P.invariants show \<open>dom (([cal(s \<mapsto> (seize, []))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [st]\<^sub>\<Zpfun>) \<Zrres> Connected) = Callers\<close>
      by (auto simp add: st_def Connected_def simp add: disjoint_iff)
  next
    from pres P.invariants show \<open>Callers \<Zdres> ([cal(s \<mapsto> (seize, []))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [num]\<^sub>\<Zpfun>) = [connected]\<^sub>\<Zpfun>\<close> 
      by (auto)
         (metis Un_iff disjoint_iff pdom_pranres pdom_res_upd_out pranres_pdom subsetD)
  next
    show \<open>dom connected \<inter> ran connected = {}\<close>
      by (simp add: P.nself)
  next
    show "pfun_inj connected"
      by (simp add: P.connected_inj)
  qed
qed

zoperation LiftSuspended =
  params s \<in> Subs
  pre "(s, suspended) \<in> connected\<^sup>\<sim> \<Zcomp> cal \<Zcomp> st" 
  update "[cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (speech, s)}]"

lemma [simp]: "speech \<in> Connected"
  by (simp add: Connected_def)

text \<open> I think we need an invariant that those who have suspended a call did not initiate that call. \<close>

lemma "st \<Zrres> {suspended} \<le> st \<Zrres> Connected"
  
  oops

lemma dom_num [simp]: "dom num = UNIV"
  by (metis Int_absorb UNIV_def num_def pdom_pabs)

lemma dom_st [simp]: "dom st = UNIV"
  by (simp add: st_def)

lemma suspended_Connected [simp]: "suspended \<in> Connected"
  by (simp add: Connected_def)

lemma suspended_le_Connected [simp]: "{suspended} \<subseteq> Connected"
  by (simp add: Connected_def)


syntax
  "_image_syn" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("(_\<^sup>\<rightarrow> _)" 999)
  "_preimage_syn" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("(_\<^sup>\<leftarrow> _)" 999)

translations
  "_image_syn f A" == "CONST ran (CONST dom_res A f)"
  "_preimage_syn f A" == "CONST dom (CONST ran_res f A)"

setup Explorer_Lib.switch_to_quotes

lemma [simp]: "pfun_inj f \<Longrightarrow> [f]\<^sub>\<Zpfun>\<^sup>\<sim> = [pfun_inv f]\<^sub>\<Zpfun>"
  by (simp add: pfun_graph_pfun_inv rel_of_pfun_def)

lemma f_pfun_inv_f_apply: "\<lbrakk> pfun_inj f; x \<in> pdom f \<rbrakk> \<Longrightarrow> pfun_inv f(f(x)\<^sub>p)\<^sub>p = x"
  by (metis pdom_pfun_inv pfun_inj_inv pfun_inj_inv_inv pfun_inv_f_f_apply)

lemma "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange_inv\<^bold>}LiftSuspended s\<^bold>{Exchange_inv\<^bold>}"
  unfolding LiftSuspended_def proof (hoare_wlp_auto)
  fix Free :: "\<bbbP> integer list" and Unavailable :: "\<bbbP> integer list" and Callers :: "\<bbbP> integer list" and cal :: "integer list \<Zpfun>
                        Status \<times> integer list" and connected :: "integer list \<Zpfun> integer list" and y :: "integer list"
  assume 
    pres: "connected(y)\<^sub>p \<in> Subs" "y \<in> dom cal" "fst (cal(y)\<^sub>p) = suspended" "y \<in> dom connected" "s = connected(y)\<^sub>p" and
    inv:  "Exchange Free Unavailable Callers cal connected"
  then interpret P: Exchange Free Unavailable Callers cal connected
    by simp
  show "Exchange Free Unavailable Callers (cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p) connected"
  proof
    show "[Free, Unavailable, dom (cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p) \<union> ran connected] partitions Subs" 
      using pres P.parts P.connected_inj by (auto simp add: num_def st_def f_pfun_inv_f_apply)
  next
    show "[cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [st]\<^sub>\<Zpfun>\<^sup>\<leftarrow> Connected = Callers" 
      using pres P.parts P.connected_inj P.Callers by (auto simp add: num_def st_def f_pfun_inv_f_apply Connected_def)
  next
    show "Callers \<Zdres> ([cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [num]\<^sub>\<Zpfun>) = [connected]\<^sub>\<Zpfun>"
      using pres P.connected P.connected_inj by (auto simp add: f_pfun_inv_f_apply pfun_eq_iff num_def)
  next
    show "dom connected \<inter> ran connected = {}"
      by (simp add: P.nself)
  next
    show "pfun_inj connected"
      by (simp add: P.connected_inj)
  qed
qed

zoperation Answer =
  params s \<in> Subs
  pre "(s, ringing) \<in> connected\<^sup>\<sim> \<Zcomp> cal \<Zcomp> st"
  update "[ Free\<Zprime> = Free - {s}
          , cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (speech, s)}]"

hide_const Map.dom Map.ran

lemma Answer_correct: "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange_inv\<^bold>}Answer s\<^bold>{Exchange_inv\<^bold>}"
  unfolding Answer_def Exchange_inv_def 
proof (hoare_wlp_auto)
  fix Free :: "\<bbbP> integer list" and Unavailable :: "\<bbbP> integer list" and Callers :: "\<bbbP> integer list" and cal :: "integer list \<Zpfun>
                        Status \<times> integer list" and connected :: "integer list \<Zpfun> integer list" and y :: "integer list"
  assume 
    invs: "Exchange Free Unavailable Callers cal connected" and
    pres: "connected(y)\<^sub>p \<in> Subs" "y \<in> dom cal" "fst (cal(y)\<^sub>p) = ringing" "y \<in> dom connected" "s = connected(y)\<^sub>p"
  then interpret P: Exchange Free Unavailable Callers cal connected
    by simp
  show "Exchange (Free - {connected(y)\<^sub>p}) Unavailable Callers (cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p) connected"
  proof
    from pres P.parts P.connected_inj show "[Free - {connected(y)\<^sub>p}, Unavailable, dom (cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p) \<union> ran connected] partitions Subs"
      by (auto simp add: f_pfun_inv_f_apply, metis imageI pran_pdom)
  next
    from pres P.connected_inj P.dom_connected_subset_cal P.dom_connected_Callers P.Callers show "[cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [st]\<^sub>\<Zpfun>\<^sup>\<leftarrow> Connected = Callers"
      by (simp add: f_pfun_inv_f_apply P.connected_inj st_def insert_absorb)
  next
    from pres P.connected_inj P.dom_connected_subset_cal P.dom_connected_Callers P.connected show "Callers \<Zdres> ([cal([connected]\<^sub>\<Zpfun>\<^sup>\<sim>(connected(y)\<^sub>p)\<^sub>r \<mapsto> (speech, connected(y)\<^sub>p))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [num]\<^sub>\<Zpfun>) = [connected]\<^sub>\<Zpfun>"
      by (auto simp add: f_pfun_inv_f_apply num_def pfun_eq_iff)
  next
    show "dom connected \<inter> ran connected = {}"
      by (simp add: P.nself)
  next
    show "pfun_inj connected"
      by (simp add: P.connected_inj)
  qed
qed

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
          , Callers\<Zprime> = Callers - {s, connected s}
          , connected\<Zprime> = {s} \<Zndres> connected]"

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
  pre "s \<in> dom cal \<and> (cal \<Zcomp> st) s = connecting \<and> s \<notin> dom connected \<and> (cal \<Zcomp> num) s \<in> Free \<and> (cal \<Zcomp> num) s \<notin> ran connected"
  update "[ Free\<Zprime> = Free - {s}
          , cal\<Zprime> = cal \<oplus> {s \<mapsto> (ringing, (cal \<Zcomp> num) s)}
          , Callers\<Zprime> = Callers \<union> {s}
          , connected\<Zprime> = connected \<oplus> {s \<mapsto> (cal \<Zcomp> num) s}]"

lemma Connect2Ringing_correct: "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange_inv\<^bold>}Connect2Ringing s\<^bold>{Exchange_inv\<^bold>}"
  unfolding Connect2Ringing_def
proof (hoare_wlp_auto)
  fix Free :: "\<bbbP> integer list" and Unavailable :: "\<bbbP> integer list" and Callers :: "\<bbbP> integer list" and cal :: "integer list \<Zpfun>
                        Status \<times> integer list" and connected :: "integer list \<Zpfun> integer list"
  assume 
    pres: "s \<in> Subs" "s \<in> dom cal" "fst (cal(s)\<^sub>p) = connecting" "s \<notin> dom connected" "snd (cal(s)\<^sub>p) \<in> Free" "snd (cal(s)\<^sub>p) \<notin> ran connected" and
    invs: "Exchange Free Unavailable Callers cal connected"

  then interpret P: Exchange Free Unavailable Callers cal connected
    by simp

  show "Exchange (Free - {s}) Unavailable (insert s Callers) (cal(s \<mapsto> (ringing, snd (cal(s)\<^sub>p)))\<^sub>p) (connected(s \<mapsto> snd (cal(s)\<^sub>p))\<^sub>p)"
  proof
    from pres P.parts show "[Free - {s}, Unavailable, dom (cal(s \<mapsto> (ringing, snd (cal(s)\<^sub>p)))\<^sub>p) \<union> ran (connected(s \<mapsto> snd (cal(s)\<^sub>p))\<^sub>p)] partitions Subs" 
      apply (auto simp add: Connected_def st_def num_def)
      nitpick
  next
    show "[cal(s \<mapsto> (ringing, snd (cal(s)\<^sub>p)))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [st]\<^sub>\<Zpfun>\<^sup>\<leftarrow> Connected = insert s Callers" sorry
  next
    show "insert s Callers \<Zdres> ([cal(s \<mapsto> (ringing, snd (cal(s)\<^sub>p)))\<^sub>p]\<^sub>\<Zpfun> \<Zcomp> [num]\<^sub>\<Zpfun>) = [connected(s \<mapsto> snd (cal(s)\<^sub>p))\<^sub>p]\<^sub>\<Zpfun>" sorry
  next
    show "dom (connected(s \<mapsto> snd (cal(s)\<^sub>p))\<^sub>p) \<inter> ran (connected(s \<mapsto> snd (cal(s)\<^sub>p))\<^sub>p) = {}" sorry
  next
    show "pfun_inj (connected(s \<mapsto> snd (cal(s)\<^sub>p))\<^sub>p)" sorry
  qed
qed


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