theory Bounded_Buffer
  imports "Z_Machines.Z_Machine"
begin

consts MAX_SIZE :: "nat"

consts VAL :: "int set"

zstore Buffer = 
  sz :: "nat"
  buf :: "int list"
  where 
  "sz = length buf"
  "sz \<le> MAX_SIZE"

zoperation Input =
  over Buffer
  params v\<in>VAL
  pre "sz < MAX_SIZE"
  update "[ sz\<Zprime> = sz + 1
          , buf\<Zprime> = buf @ [v] ]"

zoperation Output =
  over Buffer
  params v\<in>VAL
  pre "sz > 0" "v = hd buf"
  update "[ sz\<Zprime> = sz - 1
          , buf\<Zprime> = tl buf ]"

zoperation Size =
  emit sz

zinit Init =
  over Buffer
  update "[sz\<Zprime> = 0, buf\<Zprime> = []]"

zmachine Bounded_Buffer =
  init Init
  operations Size Output Input

animate Bounded_Buffer
  defines MAX_SIZE = 3 VAL = "{0..5}"

lemma "Init establishes Buffer_inv"
  by zpog_full

lemma "Size(n) preserves Buffer_inv"
  by zpog_full

lemma "Input(v) preserves Buffer_inv"
  by zpog_full

lemma "Output(v) preserves Buffer_inv"
  apply zpog_full
  apply (metis diff_le_self dual_order.trans)
  done

end