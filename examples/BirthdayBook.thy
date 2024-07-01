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
  where "dom(birthday) = known" "known \<subseteq> NAME" "ran(birthday) \<subseteq> DATE"

zoperation AddBirthday = 
  over BirthdayBook
  params name\<in>NAME date\<in>DATE
  pre "name \<notin> known"
  update "[known \<leadsto> known \<union> {name}, birthday \<leadsto> birthday \<oplus> {name \<mapsto> date}]"
  
lemma AddBirthday_inv: "AddBirthday (n, d) preserves BirthdayBook_inv"
  by zpog_full

zoperation FindBirthday =
  over BirthdayBook
  params name\<in>NAME
  pre "name \<in> dom birthday"
  output "birthday(name)"

lemma FindBirthday_inv: "FindBirthday n preserves BirthdayBook_inv"
  by zpog_full

zoperation Remind =
  over BirthdayBook
  params today\<in>DATE cards\<in>"\<bbbP> NAME"
  where "cards = {n \<in> known. birthday(n) = today}"

lemma Remind_inv: "Remind (n, d) preserves BirthdayBook_inv"
  by zpog_full

zmachine BirthdayBookSys =
  over BirthdayBook
  init "[known \<leadsto> {}, birthday \<leadsto> {\<mapsto>}]"
  invariant BirthdayBook_inv
  operations AddBirthday FindBirthday Remind

definition [z_defs]: "BirthdayBook_axioms = (NAME \<noteq> {} \<and> DATE \<noteq> {})"

lemma BirthdayBook_deadlock_free: "BirthdayBook_axioms \<Longrightarrow> deadlock_free BirthdayBookSys"
  apply (deadlock_free invs: AddBirthday_inv FindBirthday_inv Remind_inv)
  apply blast
  done

animate BirthdayBookSys
  defines NAME = "{''Simon'', ''Jim''}" DATE = "{''25/08/1983''}"

end