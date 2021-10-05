subsection \<open> Theatre Box Office \<close>

theory BoxOffice
  imports "Z_Machines.Z_Machine"
begin

subsection \<open> Types \<close>

type_synonym seat = integer
type_synonym customer = String.literal

consts 
  initalloc :: "seat set"
  SEAT      :: "seat set"
  CUSTOMER  :: "customer set"

subsection \<open> State Space \<close>

zstore BoxOffice = 
  \<comment> \<open> The seats available for purchase \<close>
  seating :: "seat set"
  \<comment> \<open> Record of seat sales \<close>
  sold :: "seat \<Zpfun> customer"
  where dom_sold: "dom(sold) \<subseteq> seating"

subsection \<open> Operations \<close>

text \<open> Purchase of a seat by a customer \<close>

zoperation Purchase0 =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER
  pre "s \<notin> dom(sold)"
  update "[sold \<leadsto> sold \<oplus> {s \<mapsto> c}]"

text \<open> Return of a seat by a customer \<close>

zoperation Return0 =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER
  pre "s \<in> dom(sold) \<and> c = sold s"
  update "[sold \<leadsto> {s} \<Zndres> sold]" 

subsection \<open> Machine and Animation \<close>

zmachine BoxOfficeProc =
  init "[seating \<leadsto> initalloc, sold \<leadsto> {\<mapsto>}]"
  operations Purchase0 Return0

text \<open> We define finite sets for each of the given sets to allow animation. \<close>

def_consts 
  initalloc = "SEAT"
  SEAT = "{0,1,2,3}"
  CUSTOMER = "{STR ''Simon'', STR ''Jim'', STR ''Christian''}"

animate BoxOfficeProc

end