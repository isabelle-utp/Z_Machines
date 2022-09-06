theory BirthdayBook
  imports "Z_Machines.Z_Machine"
begin

type_synonym name = "String.literal"
type_synonym date = "String.literal"

consts
  NAME :: "name set"
  DATE :: "date set"

zstore BirthdayBook = 
  known :: "\<bbbP> name"
  birthday :: "name \<Zpfun> date"
  where "known = dom birthday" "known \<subseteq> NAME" "ran(birthday) \<subseteq> DATE"

zoperation AddBirthday = 
  over BirthdayBook
  params name\<in>NAME date\<in>DATE
  pre "name \<notin> known"
  update "[known \<leadsto> known \<union> {name}, birthday \<leadsto> birthday \<oplus> {name \<mapsto> date}]"

lemma AddBirthday_inv: "AddBirthday (n, d) preserves BirthdayBook_inv"
  by zpog_full

zoperation FindBirthday =
  over BirthdayBook
  params name\<in>NAME date\<in>DATE
  pre "name \<in> dom birthday"
  where "date = birthday(name)"

lemma FindBirthday_inv: "FindBirthday (n, d) preserves BirthdayBook_inv"
  by zpog_full

zoperation Remind =
  over BirthdayBook
  params today\<in>DATE cards\<in>"\<bbbP> NAME"
  where "cards = {n \<in> known. birthday(n) = today}"

lemma Remind_inv: "Remind (n, d) preserves BirthdayBook_inv"
  by zpog_full

zmachine BirthdayBookSys = 
  init "[known \<leadsto> {}, birthday \<leadsto> {\<mapsto>}]"
  operations AddBirthday FindBirthday Remind

definition [z_defs]: "BirthdayBook_axioms = (NAME \<noteq> {} \<and> DATE \<noteq> {})"

lemma BirthdayBook_deadlock_free: "BirthdayBook_axioms \<Longrightarrow> deadlock_free BirthdayBookSys"
  unfolding BirthdayBookSys_def
  by (deadlock_free "BirthdayBook_inv :: BirthdayBook \<Rightarrow> bool" invs: AddBirthday_inv FindBirthday_inv Remind_inv) 

def_consts NAME = "{STR ''Simon''}" 
def_consts DATE = "{STR ''25/08/1983''}"

animate BirthdayBookSys

end