theory TelephoneExchange_locales
  imports "Z_Machines.Z_Machine"
begin unbundle Z_Syntax

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

definition st :: "subrec \<Zpfun> Status" where "st = (\<lambda> x \<bullet> first x)"
definition num :: "subrec \<Zpfun> subs" where "num = (\<lambda> x \<bullet> second x)"

no_syntax
  "_kleisli_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<Zcomp>" 54)

locale Exchange_locale =
  fixes
  Free :: "\<bbbP> subs" and
  Unavailable :: "\<bbbP> subs" and
  Callers :: "\<bbbP> subs" and
  cal :: "subs \<Zpfun> subrec" and
  connected :: "subs \<Zpinj> subs"
assumes   
  inv1: "[Free, Unavailable, dom cal \<union> dom [connected]\<^sub>\<Zpinj>] partitions Subs" and
  inv2: "dom ((cal \<Zcomp> st) \<Zrres> Connected) = Callers" and
  inv3: "Callers \<Zdres> (cal \<Zcomp> num) = connected" and
  inv4: "dom [connected]\<^sub>\<Zpinj> \<inter> ran [connected]\<^sub>\<Zpinj> = {}"
begin

lemmas invs = inv1 inv2 inv3 inv4

lemma "dom [connected]\<^sub>\<Zpinj> \<subseteq> dom cal"
  oops
end

print_theorems


term Exchange_locale


schema Exchange =
  Free :: "\<bbbP> subs"
  Unavailable :: "\<bbbP> subs"
  Callers :: "\<bbbP> subs"
  cal :: "subs \<Zpfun> subrec"
  connected :: "subs \<Zpinj> subs"
where
(*  "[Free, Unavailable, dom cal \<union> dom [connected]\<^sub>\<Zpinj>] partitions Subs"
  "dom ((cal \<Zcomp> st) \<Zrres> Connected) = Callers"
  "Callers \<Zdres> (cal \<Zcomp> num) = connected"
  "dom [connected]\<^sub>\<Zpinj> \<inter> ran [connected]\<^sub>\<Zpinj> = {}" \<comment> \<open> Added by SF: no self connections \<close> *)
  "Exchange_locale Free Unavailable Callers cal connected"

record_default Exchange

definition "InitExchange = [Free\<Zprime> = Subs, Unavailable\<Zprime> = {}, Callers\<Zprime> = {}, cal\<Zprime> = {\<mapsto>}, connected\<Zprime> = 0]"

zoperation LiftFree =
  params s \<in> Subs
  pre "s \<in> Free"
  update "[Free\<Zprime> = Free - {s}
          ,cal\<Zprime> = cal \<oplus> {s \<mapsto> (seize, [])}]"

declare list_partitions_def [simp]

find_theorems Exchange_locale

lemma "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange_inv\<^bold>}LiftFree s\<^bold>{Exchange_inv\<^bold>}"
unfolding LiftFree_def proof (hoare_wlp_auto)
  fix Free Unavailable Callers cal connected
  assume pres: "s \<in> Subs" "s \<in> Free" and inv: "Exchange_locale Free Unavailable Callers cal connected" 
  then interpret P: Exchange_locale Free Unavailable Callers cal connected
    by simp
  from pres P.invs show "Exchange_locale (Free - {s}) Unavailable Callers (cal(s \<mapsto> (seize, []))\<^sub>p) connected"
    apply (unfold_locales)
    apply (auto simp add: st_def num_def Un_absorb2 disjoint_iff Connected_def)
    apply (metis (no_types, lifting) pdom_pranres pdom_res_comp pdom_res_upd_out pranres_pdom subsetD)
    done
qed

zoperation LiftSuspended =
  params s \<in> Subs
  pre "(s, suspended) \<in> connected\<^sup>\<sim> \<Zcomp> cal \<Zcomp> st" 
  update "[cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (speech, s)}]"

context Exchange_locale
begin

lemma dom_connected_subset_cal: "dom [connected]\<^sub>\<Zpinj> \<subseteq> dom cal"
  using invs by (auto, metis pdom_comp pdom_pranres subsetD)

lemma dom_connected_Callers: "dom [connected]\<^sub>\<Zpinj> = Callers"
  using invs
  apply (auto simp add: num_def st_def)
  apply (metis (no_types, lifting) insert_subset pdom_comp pdom_pranres pdom_upd pfun_upd_ext)
  apply (metis mem_Collect_eq pdom_comp ppreimageE)
  apply (metis fst_conv mem_Collect_eq pabs_comp pabs_eta pdom_pabs ppreimageI pran_res_UNIV)
  done

lemma dom_suspended_connected: "dom ((cal \<Zcomp> st) \<Zrres> {suspended}) \<subseteq> dom [connected]\<^sub>\<Zpinj>"
  by (metis Connected_def Domain_mono dom_connected_Callers insert_subset inv2 rel_ranres_le subset_insertI)

end

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


lemma "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange\<^bold>}LiftSuspended s\<^bold>{Exchange\<^bold>}"
unfolding LiftSuspended_def proof (hoare_wlp_auto)
  fix Free Unavailable Callers cal connected
  assume pres: "s \<in> Subs" "st(cal([pinv connected]\<^sub>\<Zpinj>(s)\<^sub>p)\<^sub>p)\<^sub>p = suspended" "s \<in> ran [connected]\<^sub>\<Zpinj>" "[pinv connected]\<^sub>\<Zpinj>(s)\<^sub>p \<in> dom cal"
    and inv: "Exchange_locale Free Unavailable Callers cal connected"

  then interpret P: Exchange_locale Free Unavailable Callers cal connected
    by simp

  show "Exchange_locale Free Unavailable Callers (cal([pinv connected]\<^sub>\<Zpinj>(s)\<^sub>p \<mapsto> (speech, s))\<^sub>p) connected"
    using pres P.invs apply (unfold_locales)
       apply (auto simp add: st_def num_def pfun_eq_iff pinv_f_f_apply)
      apply (metis P.dom_connected_Callers fst_conv mem_Collect_eq ppreimageI snd_conv)
    done
qed

zoperation Answer =
  params s \<in> Subs
  pre "(s, ringing) \<in> connected\<^sup>\<sim> \<Zcomp> cal \<Zcomp> st"
  update "[ Free\<Zprime> = Free - {s}
          , cal\<Zprime> = cal \<oplus> {(connected\<^sup>\<sim>) s \<mapsto> (speech, s)}]"

lemma "s \<in> Subs \<Longrightarrow> \<^bold>{Exchange\<^bold>}Answer s\<^bold>{Exchange\<^bold>}"
  unfolding Answer_def Exchange_inv_def
  apply (hoare_wlp_auto)
  oops

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