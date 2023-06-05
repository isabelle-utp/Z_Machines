section \<open> Dining Philosophers in Z-Machines \<close>

theory Dining_Philosophers
  imports "Z_Machines.Z_Machine"
begin

subsection \<open> Constants and State \<close>

consts phil_num :: int

text \<open> We represent philsophers by the constant @{const phil_num} of type @{typ int}, which should 
  be greater than 1. \<close>

abbreviation "Phils \<equiv> {0..<phil_num}"

text \<open> @{term Phils} is the set of all philosopher identifiers, numbering from 0 to 
  @{term "phil_num - 1"}. The identifiers for each chopstick is equivalent to this set as well. \<close>

enumtype phil_state = thinking | eating

text \<open> @{typ phil_state} is the state of a philosopher: they can either by @{const thinking} or
  @{const eating}. \<close>

zstore Phil_Table =
  chopsticks :: "int \<Zpfun> bool"
  has_left   :: "int \<Zpfun> bool"
  has_right  :: "int \<Zpfun> bool"
  phil_st    :: "int \<Zpfun> phil_state"
  where
  "dom chopsticks = Phils"

text \<open> The state of the table is given through the type @{typ Phil_Table}. Variable 
  @{const chopsticks} gives the availability of every chopstick. Variables @{const has_left} and
  @{const has_right} determines whether a philosopher has the left or right chopstick, respectively.
  Finally, @{const phil_st} gives the state for each philosopher. \<close>

subsection \<open> Operations \<close>

zoperation TakeLeft =
  params p\<in>Phils
  pre "phil_st(p) = thinking" "chopsticks ((p - 1) mod phil_num)"
  update "[chopsticks[((p - 1) mod phil_num)] \<leadsto> False
          ,has_left[p] \<leadsto> True]"

text \<open> @{const TakeLeft} allows philosopher @{term p} to pick-up the fork to their left. They must
  be in the thinking state, and the chopstick to the left must be available. The latter is determined
  using modulus, so that the left chopstick for philosopher 0 is @{term "phil_num - 1"}, and so on. 
  If the precondition is satisfied, the chopstick become unavailable, and the philosopher gains it. \<close>

zoperation TakeRight =
  params p\<in>Phils
  pre "phil_st(p) = thinking" "chopsticks p"
  update "[chopsticks[p] \<leadsto> False
          ,has_right[p] \<leadsto> True]"

text \<open> @{const TakeRight} is similar to @{const TakeLeft}, except that we take the chopstick with
  the same identifier as the philosopher. \<close>

zoperation Eat =
  params p\<in>Phils
  pre "has_left p" "has_right p" "phil_st p = thinking"
  update "[phil_st[p] \<leadsto> eating]"

text \<open> @{const Eat} is the operation that allows the philosopher to move to the eating state. They
  must have both the left and right chopstick, and still be in the @{const thinking} state. This
  being the case, they transition to @{const eating}. \<close>

zoperation Release =
  params p\<in>Phils
  pre "phil_st(p) = eating"
  update "[chopsticks[((p - 1) mod phil_num)] \<leadsto> True
          ,chopsticks[p] \<leadsto> True
          ,has_left[p] \<leadsto> False
          ,has_right[p] \<leadsto> False
          ,phil_st[p] \<leadsto> thinking]"

text \<open> @{const Release} allows the philsopher to release both chopsticks once they've reached 
  the @{const eating} state. That being the case, both chopsticks are released and the philosopher
  moves back to the @{const thinking} state. \<close>

zoperation Think =
  params p\<in>Phils
  pre "phil_st(p) = thinking"

text \<open> @{const Think} allows us to see whether a given philosopher is thinking. It is useful for
  observation, but not verification. \<close>

subsection \<open> Z-Machine and Animation \<close>

zmachine Dining_Philosophers =
  over Phil_Table
  init "[chopsticks \<leadsto> (\<lambda> i\<in>Phils \<bullet> True)
        ,has_left \<leadsto> (\<lambda> i\<in>Phils \<bullet> False)
        ,has_right \<leadsto> (\<lambda> i\<in>Phils \<bullet> False)
        ,phil_st \<leadsto> (\<lambda> i\<in>Phils \<bullet> thinking)]"
  operations TakeLeft TakeRight Eat Release

text \<open> We set the initial state for all chopsticks to be available, all philosophers to not be 
  holding any chopstick, and all philosophers to be @{const thinking}. \<close>

animate Dining_Philosophers
  defines phil_num = 4

check_deadlock Dining_Philosophers
  defines phil_num = 5
  depth 10

check_reachable Dining_Philosophers Eat
  defines phil_num = 4

text \<open> At the point of animation we can vary the number of philosophers to observe possible scenarios. \<close>

end