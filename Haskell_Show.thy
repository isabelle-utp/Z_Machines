section \<open> Show class for code generation \<close>

theory Haskell_Show
  imports "HOL-Library.Code_Target_Int"
begin

text \<open> The following class should correspond to the Haskell type class Show, but currently it
       has only part of the signature. \<close>

class "show" =
  fixes "show" :: "'a \<Rightarrow> String.literal"

text \<open> We set up code printing so that this class, and the constants therein, are mapped to the
  Haskell Show class. \<close>

code_printing
  type_class "show" \<rightharpoonup> (Haskell) "Prelude.Show"
| constant "show" \<rightharpoonup> (Haskell) "Prelude.show"


instantiation unit :: "show"
begin

fun show_unit :: "unit \<Rightarrow> String.literal" where
"show_unit () = STR ''()''"

instance ..

end

text \<open> We create an instance for bool, that generates an Isabelle function \<close>

instantiation bool :: "show"
begin

fun show_bool :: "bool \<Rightarrow> String.literal" where
"show_bool True = STR ''True''" |
"show_bool False = STR ''False''"

instance ..

end

text \<open> We map the instance for bool to the built-in Haskell show, and have the code generator
  use the built-in class instance. \<close>

code_printing
  constant "show_bool_inst.show_bool" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "bool" :: "show" \<rightharpoonup> (Haskell) -

text \<open> Actually, we don't really need to create the show function if all we're interested in is
  code generation. Here, for the @{typ integer} instance, we omit the definition. This is
  because @{typ integer} is set up to correspond to the built-in Haskell type Integer, which
  already has a Show instance. \<close>

instantiation integer :: "show"
begin

instance ..

end

text \<open> For the code generator, the crucial line follows. This maps the (unspecified) Isabelle show
  function to the Haskell show function, which is built-in. We also specify that no instance of
  Show should be generated for integer, as it exists already. \<close>

code_printing
  constant "show_integer_inst.show_integer" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "integer" :: "show" \<rightharpoonup> (Haskell) -



text \<open> For @{typ int}, we are effectively dealing with a packaged version of @{typ integer} in
  the code generation set up. So, we simply define show in terms of the "underlying" integer
  using @{const integer_of_int}. \<close>

instantiation int :: "show"
begin

definition show_int :: "int \<Rightarrow> String.literal" where
"show_int x = show (integer_of_int x)"

instance ..

end

text \<open> As a result, we can prove a code equation that will mean that our show instance for @{typ int}
  simply calls the built-in show function for @{typ integer}. \<close>

lemma show_int_of_integer [code]: "show (int_of_integer x) = show x" 
  by (simp add: show_int_def)

text \<open> Now we have a small example data type, and a show instance, which we will generate. \<close>

datatype D = MyData bool | MyData2 int

instantiation D :: "show"
begin

fun show_D :: "D \<Rightarrow> String.literal" where
"show_D (MyData x) = STR ''MyData '' + show x" |
"show_D (MyData2 x) = STR ''MyData2 '' + show x"

instance ..

end

definition "hello x = show x"

definition "hello2 = hello (MyData True)"

definition "hello3 = hello (1 :: integer)"

export_code "hello" "hello2" hello3 in Haskell 

end