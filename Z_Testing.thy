section \<open> Testing Z-Machines \<close>

theory Z_Testing
  imports Z_Animator
begin

code_identifier
  code_module Z_Testing \<rightharpoonup> (Haskell) Interaction_Trees

generate_file \<open>code/animate/ZTesting.hs\<close> = \<open>
module ZTesting (itree_rev_traces, dlock_traces, test_dlock) where
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
dlock_traces n p = map (reverse . map getEvt . filter isEvt) (filter (isDlock . head) (itree_rev_traces n p))

test_dlock :: Show e => Int -> Itree e s -> IO ()
test_dlock n p = case dlock_traces n p of
                   [] -> putStrLn ("No deadlocking traces found of length <= " ++ show n ++ ".")
                   (tr : _) -> putStrLn ("Deadlocks after: " ++ show tr ++ ".")
\<close>

ML \<open>

structure Z_Machine_Testing =
struct

fun dlock_test_file model thy =
  "module Main where \n" ^
  "import ZTesting; \n" ^
  "import " ^ thy ^ "; \n" ^
  "main = test_dlock 10 " ^ Z_Machine_Animator.firstLower model

fun dlock_test_files_cp ghc tmp = 
  "(fn path => let open Isabelle_System; val path' = Path.append path (Path.make [\"code\", \"animate\"])" ^
  " in writeln \"Compiling deadlock test...\"; bash (\"cd \" ^ Path.implode path' ^ \"; " ^ ghc ^ " DlockTest.hs >> /dev/null; ./DlockTest\") ; copy_dir path' (Path.explode \"" ^ tmp ^ "\") end)";


fun prep_testing model thy ctx =
  let open Generated_Files; 
      val (tmp, thy') = Z_Machine_Animator.simulator_setup (Local_Theory.exit_global ctx);
      val ctx' = Named_Target.theory_init thy'
      val ghc = getenv "ISABELLE_GHC"
      val _ = if (ghc = "") then error "GHC is not set up. Please set the environment variable ISABELLE_GHC." else ()
  in
  generate_file (Path.binding0 (Path.make ["code", "animate", "DlockTest.hs"]), (Input.string (dlock_test_file model thy))) ctx' |>
  (fn ctx' => 
    let val _ = compile_generated_files 
                 ctx'
                 [([], (Local_Theory.exit_global ctx')), ([Path.binding0 (Path.make ["code", "animate", "ZTesting.hs"])], @{theory})] 
                 [] [([Path.binding0 (Path.make ["code", "animate", "DlockTest"])], SOME true)]
                 (Path.binding0 (Path.make []))
                 (Input.string (dlock_test_files_cp ghc (Path.implode tmp)))
    in ctx' end)
  end

fun dlock_test model thy =
  let val ctx = Named_Target.theory_init thy
      val ctx' =
        (Code_Target.export_code true [Code.read_const (Local_Theory.exit_global ctx) model] [((("Haskell", ""), SOME ({physical = false}, (Path.explode "animate", Position.none))), [])] ctx)
        |> prep_testing model (Context.theory_name thy)
  in thy
  end 

end

\<close>


end
