theory TrivialPursuit
  imports "Z_Machines.Z_Machine"
begin

enumtype Player = one | two | three | four | five | six

enumtype Colour = blue | pink | yellow | brown | green | orange

zstore LocalScore =
  s :: "Colour set"

zstore GlobalScore =
  score :: "Player \<Zpfun> LocalScore"

zoperation AnswerLocal =
  params c \<in> Colour
  pre "c \<notin> s"
  update "[s \<leadsto> s \<union> {c}]"

zoperation AnswerGlobal =
  promote AnswerLocal in score

zmachine TrivialPursuit =
  over GlobalScore
  init "[score \<leadsto> (\<lambda> p\<in>Player \<bullet> \<lblot> s \<leadsto> {} \<rblot>)]"
  operations AnswerGlobal
 
animate TrivialPursuit

end