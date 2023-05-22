section \<open> Testing Z-Machines \<close>

theory Z_Testing
  imports Z_Animator
  keywords "check_deadlock" :: "thy_defn"
begin

code_identifier
  code_module Z_Testing \<rightharpoonup> (Haskell) Interaction_Trees

generate_file \<open>code/animate/ZTesting.hs\<close> = \<open>
module ZTesting (itree_rev_traces, dlock_traces, test_dlock, test_event) where
import Interaction_Trees;
import Prelude;
import System.IO;
import Data.Ratio;
import Data.List;

data IEvt e = Evt { getEvt :: e } | Dlock | Term deriving (Eq, Show)

isEvt :: IEvt e -> Bool
isEvt (Evt e) = True
isEvt _ = False

isDlock :: IEvt e -> Bool
isDlock Dlock = True
isDlock _ = False

expand_itree :: ([IEvt e], Itree e s) -> [([IEvt e], Itree e s)]
expand_itree (Dlock : tr, p) = [(Dlock : tr, p)]
expand_itree (Term : tr, p) = [(Term : tr, p)]
expand_itree (tr, Vis (Pfun_of_alist [])) = [(Dlock : tr, Vis (Pfun_of_alist []))]
expand_itree (tr, Vis (Pfun_of_alist m)) = map (\(e, p) -> (Evt e : tr, p)) m
expand_itree (tr, Sil p) = expand_itree (tr, p)
exoand_itree (tr, Ret v) = [(Term : tr, Ret v)]

expand_itrees :: [([IEvt e], Itree e s)] -> [([IEvt e], Itree e s)]
expand_itrees ts = concat (map expand_itree ts)

itree_rev_traces :: Int -> Itree e s -> [[IEvt e]]
itree_rev_traces n p = map fst ((iterate expand_itrees [([], p)]) !! (n+1))

dlock_traces :: Int -> Itree e s -> [[e]]
dlock_traces n p = map (reverse . map getEvt . filter isEvt) (filter (isDlock . head) trs)
  where trs = itree_rev_traces n p

event_traces :: Int -> (e -> Bool) -> Itree e s -> [[e]]
event_traces n t p = map (reverse . map getEvt . filter isEvt) (filter ((\e -> isEvt e && t (getEvt e)) . head) trs)
  where trs = itree_rev_traces n p

test_event :: Show e => Int -> (e -> Bool) -> Itree e s -> IO ()
test_event n t p = do { case trs of
                        [] -> putStrLn ("No matching traces found of length <= " ++ show n ++ ".")
                        (tr : _) -> putStrLn ("Trace found: " ++ show tr ++ ".")
                    }
  where trs = event_traces n t p

test_dlock :: Show e => Int -> Itree e s -> IO ()
test_dlock n p = do { case trs of
                        [] -> putStrLn ("No deadlocking traces found of length <= " ++ show n ++ ".")
                        (tr : _) -> putStrLn ("Deadlocks after: " ++ show tr ++ ".")
                    }
  where trs = dlock_traces n p
\<close>

ML \<open>

structure Z_Machine_Testing =
struct

fun test_files_cp ghc tmp = 
  "(fn path => let open Isabelle_System; val path' = Path.append path (Path.make [\"code\", \"animate\"])" ^
  " in writeln \"Compiling test...\"; bash (\"cd \" ^ Path.implode path' ^ \"; " ^ ghc ^ " ZTest.hs >> /dev/null; ./ZTest\") ; copy_dir path' (Path.explode \"" ^ tmp ^ "\") end)";


fun dlock_test_file model thy =
  "module Main where \n" ^
  "import ZTesting; \n" ^
  "import " ^ thy ^ "; \n" ^
  "main = test_dlock 10 " ^ Z_Machine_Animator.firstLower model

fun event_test_file model chan thy =
  "module Main where \n" ^
  "import ZTesting; \n" ^
  "import " ^ thy ^ "; \n" ^
  "main = test_event 10 is_" ^ chan ^ " " ^ Z_Machine_Animator.firstLower model

fun prep_testing test_file ctx =
  let open Generated_Files; 
      val (tmp, thy') = Z_Machine_Animator.simulator_setup (Local_Theory.exit_global ctx);
      val ctx' = Named_Target.theory_init thy'
      val ghc = getenv "ISABELLE_GHC"
      val _ = if (ghc = "") then error "GHC is not set up. Please set the environment variable ISABELLE_GHC." else ()
  in
  generate_file (Path.binding0 (Path.make ["code", "animate", "ZTest.hs"]), (Input.string test_file)) ctx' |>
  (fn ctx' => 
    let val _ = compile_generated_files 
                 ctx'
                 [([], (Local_Theory.exit_global ctx')), ([Path.binding0 (Path.make ["code", "animate", "ZTesting.hs"])], @{theory})] 
                 [] [([Path.binding0 (Path.make ["code", "animate", "ZTest"])], SOME true)]
                 (Path.binding0 (Path.make []))
                 (Input.string (test_files_cp ghc (Path.implode tmp)))
    in ctx' end)
  end

fun dlock_test model thy =
  let val ctx = Named_Target.theory_init thy
      val ctx' =
        (Code_Target.export_code true [Code.read_const (Local_Theory.exit_global ctx) model] [((("Haskell", ""), SOME ({physical = false}, (Path.explode "animate", Position.none))), [])] ctx)
        |> prep_testing (dlock_test_file model (Context.theory_name thy))
  in thy
  end 

fun event_test model chan thy =
  let val ctx = Named_Target.theory_init thy
      val ctx' =
        (Code_Target.export_code true [Code.read_const (Local_Theory.exit_global ctx) model] [((("Haskell", ""), SOME ({physical = false}, (Path.explode "animate", Position.none))), [])] ctx)
        |> prep_testing (event_test_file model chan (Context.theory_name thy))
  in thy
  end 


end

\<close>


ML \<open>
  Outer_Syntax.command @{command_keyword check_deadlock} "check deadlock in a Z Machine"
  (Parse.name 
   >> (fn model => 
        Toplevel.theory 
        (fn thy => let val anim = Z_Machine_Testing.dlock_test model thy in thy end)));
\<close>


end
