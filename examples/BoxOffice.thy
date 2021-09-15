subsection \<open> Theatre Box Office \<close>

theory BoxOffice
  imports "Z_Machines.Z_Machine"
begin

type_synonym SEAT = integer
type_synonym CUSTOMER = String.literal

consts 
  initalloc :: "SEAT set"
  SEAT      :: "SEAT set"
  CUSTOMER  :: "CUSTOMER set"

schema BoxOffice = 
  seating :: "SEAT set"
  sold :: "SEAT \<Zpfun> CUSTOMER"
  where "pdom(sold) \<subseteq> seating"

record_default BoxOffice

zoperation Purchase0 =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER
  pre "s \<notin> pdom(sold)"
  update "[sold \<leadsto> sold \<oplus> {s \<mapsto> c}]"

zoperation Return0 =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER
  pre "s \<in> pdom(sold) \<and> c = sold s"
  update "[sold \<leadsto> {s} \<Zndres> sold]" 

zmachine BoxOfficeProc =
  init "[seating \<leadsto> initalloc, sold \<leadsto> {\<mapsto>}]"
  operations Purchase0 Return0

def_consts 
  initalloc = "SEAT"
  SEAT = "set [0,1,2,3]"
  CUSTOMER = "set [STR ''Simon'', STR ''Jim'', STR ''Christian'']"

animate BoxOfficeProc

end