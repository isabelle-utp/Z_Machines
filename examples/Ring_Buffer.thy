theory Ring_Buffer
  imports "Z_Machines.Z_Machine"
begin

consts 
  MAX_SIZE :: "nat" 
  VAL :: "int set"

zstore Buffer = 
  sz :: "nat"
  arr :: "nat \<Zpfun> int"
  rtop :: "nat"
  rbot :: "nat"
  where 
    "dom(arr) = {0..MAX_SIZE-1}"
    "sz \<le> MAX_SIZE"
    "rtop < MAX_SIZE"
    "rbot < MAX_SIZE"

zoperation Input =
  params v\<in>VAL
  pre "sz < MAX_SIZE"
  update "[ sz\<Zprime> = sz + 1
          , rbot\<Zprime> = (rbot + 1) mod MAX_SIZE
          , arr\<Zprime> = arr \<oplus> {rbot \<mapsto> v} ]"

zoperation Output =
  params v\<in>VAL
  pre "sz > 0" "v = $arr[rtop]"
  update "[ sz\<Zprime> = sz - 1
          , rtop\<Zprime> = (rtop + 1) mod MAX_SIZE ]"

zoperation Array =
  emit "map arr [0..<MAX_SIZE]"

zinit Init_Buffer =
  over Buffer
  update "[ sz\<Zprime> = 0, rtop\<Zprime> = 0, rbot\<Zprime> = 0
          , arr\<Zprime> = (\<lambda> i\<in>{0..MAX_SIZE - 1} \<bullet> 0) ]" 

zmachine Ring_Buffer =
  init Init_Buffer
  operations Input Output Array

animate Ring_Buffer
  defines VAL = "{0..3}" MAX_SIZE = "3"

lemma "Input(v) preserves Buffer_inv"
  apply zpog_full
  apply (metis One_nat_def Suc_leI insert_absorb less_imp_Suc_add mem_Collect_eq sl1 zero_less_Suc)
  done

lemma "Output(v) preserves Buffer_inv"
  apply zpog_full
   apply (meson diff_le_self dual_order.trans)
  done

end