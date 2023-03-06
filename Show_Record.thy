section \<open> Show instances for records \<close>

theory Show_Record
  imports "Z_Toolkit.Haskell_Show"
  keywords "show_record" :: "thy_decl_block"
begin

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse x [] = []" | 
"intersperse x [y] = [y]" |
"intersperse x (y # ys) = y # x # intersperse x ys"

definition show_fields :: "(String.literal \<times> String.literal) list \<Rightarrow> String.literal \<Rightarrow> String.literal"
  where "show_fields flds moref = 
           (let field_asgns = map (\<lambda> (fn, fv). fn + STR '' = '' + fv) flds
            in STR ''{'' 
               + fold (+) (intersperse STR '', '' field_asgns) STR '''' 
               + (if moref = STR ''()'' then STR '''' else STR '', '' + moref)
               + STR ''}'')" 

ML_file \<open>Show_Record.ML\<close>

ML \<open>
Outer_Syntax.command @{command_keyword show_record} "create a show class instance for a record"
    (Parse.name >> (Toplevel.theory o Show_Record.mk_record_show_inst)); \<close>

end