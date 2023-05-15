theory TrivialPursuit
  imports "Z_Machines.Z_Machine"
begin

enumtype Player = one | two | three | four | five | six
enumtype Colour = blue | pink | yellow | brown | green | orange

zstore LocalScore =
  s :: "Colour set"

zstore GlobalScore =
  score :: "Player \<Zpfun> LocalScore"
  winner :: "Player option"

zoperation AnswerLocal =
  params c \<in> Colour 
  pre "c \<notin> s"
  update "[s \<leadsto> s \<union> {c}]"

zoperation AnswerGlobal' =
  params p\<in>Player c\<in>Colour
  is "AnswerLocal(c) \<Up>\<Up> score[p]"

zoperation AnswerGlobal =
  promote AnswerLocal in score

zoperation WinGame =
  params p \<in> Player
  pre "(score p):s = Colour"
  update "[winner\<Zprime> = Some p]"

zmachine TrivialPursuit =
  over GlobalScore
  init "[score \<leadsto> (\<lambda> p\<in>Player \<bullet> \<lblot> s \<leadsto> {} \<rblot>), winner \<leadsto> None]"
  operations AnswerGlobal WinGame
  until "winner \<noteq> None"
   
animate TrivialPursuit

end