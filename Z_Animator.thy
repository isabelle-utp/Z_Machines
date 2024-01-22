theory Z_Animator                 
  imports "Interaction_Trees.ITrees" "ITree_Simulation.Show_Channel"
  keywords "animate" :: "thy_defn"
begin

code_datatype pfun_of_alist pfun_of_map pfun_entries

code_identifier
  code_module Z_Animator \<rightharpoonup> (Haskell) Interaction_Trees
| code_module Partial_Fun \<rightharpoonup> (Haskell) Interaction_Trees
| code_module Interaction_Trees \<rightharpoonup> (Haskell) Interaction_Trees

generate_file \<open>code/animate/Animate.hs\<close> = \<open>
module Animate (animate) where
import Interaction_Trees;
import Prelude;
import System.IO;
import Data.Ratio;
import Data.List;

removeSubstr :: String -> String -> String;
removeSubstr w "" = "";
removeSubstr w s@(c:cs) = (if w `isPrefixOf` s then Prelude.drop (Prelude.length w) s else c : removeSubstr w cs);

data EventCont p = InputEvtCont [(String, p)] | OutEvtCont (String, p)

showEventCont :: (String, EventCont p) -> String
showEventCont (n, InputEvtCont _) = n
showEventCont (n, OutEvtCont (v, _)) = n ++ " " ++ v

eventHierarchy :: [(String, p)] -> [(String, EventCont p)]
eventHierarchy m = map (\c -> (c,
                              (\es -> if length es == 1 then OutEvtCont (head es) else InputEvtCont es)
                              $ map (\(e, p) -> (tail (dropWhile (\x -> x /= ' ') e), p)) 
                              $ filter (isPrefixOf (c ++ " ") . fst) m)) chans
  where
--  m = map (\(e, p) -> (Prelude.show e, p)) m
  chans = nub $ map (takeWhile (\x -> x /= ' ') . fst) m

animate_cnt :: (Eq e, Prelude.Show e, Prelude.Show s) => Prelude.Int -> Itree e s -> Prelude.IO ();
animate_cnt n (Ret x) = Prelude.putStrLn ("Terminated: " ++ Prelude.show x);
animate_cnt n (Sil p) = 
  do { if (n >= 20) then do { Prelude.putStr "Many steps (> 20); Continue? [Y/N]"; q <- Prelude.getLine; 
                              if (q == "Y") then animate_cnt 0 p else Prelude.putStrLn "Ended early.";
                            }
                    else animate_cnt (n + 1) p
     };
animate_cnt n (Vis (Pfun_of_alist [])) = putStrLn "Deadlocked.";
animate_cnt n t@(Vis (Pfun_of_alist m)) = 
  do { putStrLn ("Operations:" ++ concat (map (\(n, e) -> " (" ++ show n ++ ") " ++ e ++ ";") (zip [1..] (map showEventCont eh))));
       e <- getLine;
       if (e == "q" || e == "Q") then
         putStrLn "Animation terminated"
       else
       case (reads e) of
         []       -> do { putStrLn "No parse"; animate_cnt n t }
         [(v, _)] -> if (v > length eh)
                       then do { putStrLn "Rejected"; animate_cnt n t }
                       else case (snd (eh !! (v - 1))) of
                              InputEvtCont opts -> 
                                do { putStrLn ("Parameters:" ++ concat (map (\(n, e) -> " (" ++ show n ++ ") " ++ e ++ ";") (zip [1..] (map fst opts))))
                                   ; e <- getLine
                                   ; case (reads e) of
                                       []       -> do { putStrLn "No parse"; animate_cnt n t }
                                       [(v, _)] -> if (v > length opts)
                                                   then do { putStrLn "Rejected"; animate_cnt n t }
                                                   else animate_cnt 0 (snd (opts !! (v - 1)))

                                   }
                              OutEvtCont (_, p) -> animate_cnt 0 p
     }                                                            
  where eh = eventHierarchy (map (\(e, p) -> (Prelude.show e, p)) m);
animate :: (Eq e, Prelude.Show e, Prelude.Show s) => Itree e s -> Prelude.IO ();
animate p = do { hSetBuffering stdout NoBuffering; putStrLn ""; putStrLn "Starting Animation..."; animate_cnt 0 p }
\<close>

ML \<open> 

structure Z_Machine_Animator =
struct

structure ISim_Path = Theory_Data
  (type T = Path.T option
   val empty = NONE
   val extend = I
   val merge = fn (_, y) => y);

fun simulator_setup thy = 
  let open Isabelle_System; val tmp = Path.expand (create_tmp_path "itree-animate" "")
  in case (ISim_Path.get thy) of NONE => () | SOME oldtmp => rm_tree oldtmp;
    make_directory tmp; (tmp, ISim_Path.put (SOME tmp) thy)
  end

fun sim_files_cp ghc tmp = 
  "(fn path => let open Isabelle_System; val path' = Path.append path (Path.make [\"code\", \"animate\"])" ^
  " in writeln \"Compiling animation...\"; bash (\"cd \" ^ Path.implode path' ^ \"; " ^ ghc ^ " Animation &> /dev/null\") ; copy_dir path' (Path.explode \"" ^ tmp ^ "\") end)";

open Named_Target

fun firstLower s =
  case String.explode s of [] => "" | c :: cs => String.implode (Char.toLower c :: cs);

fun simulation_file model thy =
  "module Main where \n" ^
  "import Animate; \n" ^
  "import " ^ thy ^ "; \n" ^
  "main = animate " ^ firstLower model

fun prep_animation model thy ctx =
  let open Generated_Files; 
      val (tmp, thy') = simulator_setup (Local_Theory.exit_global ctx);
      val ctx' = Named_Target.theory_init thy'
      val ghc = getenv "ISABELLE_GHC"
      val _ = if (ghc = "") then error "GHC is not set up. Please set the environment variable ISABELLE_GHC." else ()
  in
  generate_file (Path.binding0 (Path.make ["code", "animate", "Animation.hs"]), (Input.string (simulation_file model thy))) ctx' |>
  (fn ctx' => 
    let val _ = compile_generated_files 
                 ctx'
                 [([], (Local_Theory.exit_global ctx')), ([Path.binding0 (Path.make ["code", "animate", "Animate.hs"])], @{theory})] 
                 [] [([Path.binding0 (Path.make ["code", "animate", "Animation"])], SOME true)]
                 (Path.binding0 (Path.make []))
                 (Input.string (sim_files_cp ghc (Path.implode tmp)))
    in ctx' end)
  end

fun run_animation thy =
  
  case ISim_Path.get thy of
    NONE => error "No animation" |
    SOME f => 
      let val p = Path.append f (Path.make ["animate"])
      in writeln (Active.run_system_shell_command (SOME (Path.implode p)) ("./Animation") "Start animation") end

fun animate model thy =
  let val ctx = Named_Target.theory_init thy
      val ctx' =
        (Code_Target.export_code true [Code.read_const (Local_Theory.exit_global ctx) model] [((("Haskell", ""), SOME ({physical = false}, (Path.explode "animate", Position.none))), [])] ctx)
        |> prep_animation model (Context.theory_name {long = false} thy)
  in run_animation (Local_Theory.exit_global ctx')
  end 

end;
\<close>


ML \<open>
  Outer_Syntax.command @{command_keyword animate} "animate a Z Machine"
  ((Parse.name -- Scan.optional (@{keyword "defines"} |-- Scan.repeat1 ((Parse.name --| @{keyword "="}) -- Parse.term)) []) 
   >> (fn (model, defs) => 
        Toplevel.theory 
        (fn thy => let val anim = Z_Machine_Animator.animate model (Def_Const.def_consts defs thy) in thy end)));

\<close>

end