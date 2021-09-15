theory BirthdayBook
  imports "Z_Machines.Z_Machine"
begin

type_synonym name = "String.literal"
type_synonym date = "String.literal"

consts
  NAME :: "name set"
  DATE :: "date set"

schema BirthdayBook = 
  known :: "\<bbbP> name"
  birthday :: "name \<Zpfun> date"
  where "known = dom birthday"

record_default BirthdayBook

zoperation AddBirthday = 
  over BirthdayBook
  params name\<in>NAME date\<in>DATE
  pre "name \<notin> known"
  update "[known \<leadsto> known \<union> {name}, birthday \<leadsto> birthday \<oplus> {name \<mapsto> date}]"

zoperation FindBirthday =
  over BirthdayBook
  params name\<in>NAME date\<in>DATE
  pre "name \<in> known"
  where "date = birthday(name)"

zoperation Remind =
  over BirthdayBook
  params today\<in>DATE cards\<in>"\<bbbP> DATE"
  where "cards = {n \<in> known. birthday(n) = today}"

zmachine BirthdayBookSys = 
  init "[known \<leadsto> {}, birthday \<leadsto> {\<mapsto>}]"
  operations AddBirthday FindBirthday Remind

def_consts NAME = "{STR ''Simon''}" 
def_consts DATE = "{STR ''25/08/1983''}"

animate BirthdayBookSys

end