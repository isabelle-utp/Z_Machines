theory HotelKeyCard
  imports "Z_Machines.Z_Machine"
begin

type_synonym guest = integer
type_synonym key = integer
type_synonym room = integer
type_synonym card = "key \<times> key"

consts
  GUEST :: "\<bbbP> guest"
  KEY :: "\<bbbP> key"
  ROOM :: "\<bbbP> room"

schema State = 
  owns :: "room \<Zpfun> guest"
  currk :: "room \<Zpfun> key"
  issued :: "\<bbbP> key"
  cards :: "guest \<Zpfun> \<bbbP> card"
  roomk :: "room \<Zpfun> key"
  isin :: "room \<Zpfun> \<bbbP> guest"
  safe :: "room \<Zpfun> \<bool>"
  where "dom(owns) \<subseteq> GUEST"

zoperation CheckIn =
  params r\<in>ROOM g\<in>GUEST k\<in>KEY
  update "[currk\<Zprime> = currk \<oplus> {r \<mapsto> k}
          ,issued\<Zprime> = issued \<union> {k}
          ,cards\<Zprime> = cards \<oplus> {g \<mapsto> cards g \<union> {(currk r, k)}}
          ,owns\<Zprime> = owns \<oplus> {r \<mapsto> g}
          ,safe\<Zprime> = safe \<oplus> {r \<mapsto> False}]"
  where "k \<notin> issued"

zoperation EnterRoom =
  params r\<in>ROOM g\<in>GUEST k\<in>KEY k'\<in>KEY
  

end