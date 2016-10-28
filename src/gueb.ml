open Absenvgenerique
open Stubfunc
open Ir
open Uafgenerique
open Graph
open Program_piqi
open Program
open Heap_functions

(* global vars *)
let verbose = ref false
let show_call = ref false
let show_free = ref false
let show_values = ref false
(*/let details_values = ref false*)
let program = ref "reil"
let func = ref "main"
let funcs_file = ref ""
let stub_name = ref ""
let type_analysis = ref 0
let dir_output = ref "results"
let print_graph = ref false
(*let merge_output = ref false*)
let flow_graph_dot = ref false
let flow_graph_gml = ref false
let flow_graph_disjoint = ref false
let max_func = ref 400
let max_ins = ref None
let total_max_ins = ref None
let group_by = ref "alloc"
let no_clean_stack = ref false
let analyze_irreducible_loop = ref false
let depth = ref None 
let absenv = ref ""

(* Signature *)
module type TAnalysis = functor (Absenv_v : AbsEnvGenerique)-> functor (Ir_v : IR) -> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique) ->
sig
      val init : string -> unit
      val launch_analysis : string  ->  unit
      val launch_analysis_list : string list ->  unit
      val end_analysis : unit -> unit
end ;;

(* Main analysis *)
module GuebAnalysis: TAnalysis = functor (Absenv_v : AbsEnvGenerique) -> functor (Ir_v : IR) -> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique)->
struct
    module GraphIR = My_Graph (Absenv_v) (Ir_v) (Stubfunc_v) (Uaf_v)
 
    let list_funcs = ref []
    let malloc = ref []
    let free = ref []

    let parsed_func = Hashtbl.create 100

    let counter = 
        let ctr = ref (-1) in
        fun () -> 
            incr ctr; 
            !ctr;;

    let init program_file =
        let () = Printf.printf "Lauch VSA on %s\n" program_file in
        let () = GraphIR.set_size (!max_func) in
        let () = match !max_ins with
                  | Some d -> GraphIR.set_max_ins d 
                  | None -> () 
        in
        let () = match !total_max_ins with
                  | Some d -> GraphIR.set_total_max_ins d 
                  | None -> () 
        in
        let () = if (!analyze_irreducible_loop) then GraphIR.set_irreducible_loop () in
        let () = 
                match (!depth) with
                | None -> ()
                | Some d -> GraphIR.set_depth d 
        in
        let channel =
            try open_in_bin program_file 
            with _ -> let () = Printf.printf "Reil.REIL file not found (have you used -reil ? )\n" in exit 0
        in
        let buf = Piqirun.init_from_channel channel in
        let raw_program = parse_program buf in
        let () = close_in channel in 
        let raw_heap_func = raw_program.heap_func in
        let () = list_funcs := raw_program.functions in
        let () = malloc := List.map (fun x -> Int64.to_int x) raw_heap_func.call_to_malloc in
        free := List.map (fun x -> Int64.to_int x) raw_heap_func.call_to_free
        

    let launch_analysis func_name  = 
        let () = Printf.printf "Launch the analysis on %s (%d)\n" func_name (counter ())in
        let dir = Printf.sprintf "%s/%s" (!dir_output) (func_name) in
        let _ = GraphIR.launch_value_analysis func_name (!list_funcs) (!malloc) (!free) (not (!no_clean_stack)) dir (!verbose) (!show_values) (!show_call) (!show_free)  ((!flow_graph_gml) || (!flow_graph_dot) ) (!flow_graph_gml) (!flow_graph_dot) (!flow_graph_disjoint) parsed_func in
        let () = Printf.printf "--------------------------------\n" in
        flush Pervasives.stdout

    let launch_analysis_list funcs_name = List.iter (fun x -> launch_analysis x) funcs_name 
        
    let end_analysis () = GraphIR.end_analysis ()
    end ;;


module AllFuncs: TAnalysis = functor (Absenv_v : AbsEnvGenerique) -> functor (Ir_v : IR) -> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique)->
struct
    module GraphIR = My_Graph (Absenv_v) (Ir_v) (Stubfunc_v) (Uaf_v)
 
    let list_funcs = ref []
    let malloc = ref []
    let free = ref []

    let parsed_func = Hashtbl.create 100

    let counter = 
        let ctr = ref (-1) in
        fun () -> 
            incr ctr; 
            !ctr;;

    let init program_file =
        let () = Printf.printf "Lauch VSA on %s\n" program_file in
        let () = GraphIR.set_size (!max_func) in
        let () = match !max_ins with
                  | Some d -> GraphIR.set_max_ins d 
                  | None -> () 
        in
        let () = match !total_max_ins with
                  | Some d -> GraphIR.set_total_max_ins d 
                  | None -> () 
        in
        let () = if (!analyze_irreducible_loop) then GraphIR.set_irreducible_loop () in
        let () = 
                match (!depth) with
                | None -> GraphIR.set_depth 4 (* default depth *)
                | Some d -> GraphIR.set_depth d 
        in
        let channel =
            try open_in_bin program_file 
            with _ -> let () = Printf.printf "Reil.REIL file not found (have you used -reil ? )\n" in exit 0
        in
        let buf = Piqirun.init_from_channel channel in
        let raw_program = parse_program buf in
        let () = close_in channel in 
        let raw_heap_func = raw_program.heap_func in
        let () = list_funcs := raw_program.functions in
        let () = malloc := List.map (fun x -> Int64.to_int x) raw_heap_func.call_to_malloc in
        free := List.map (fun x -> Int64.to_int x) raw_heap_func.call_to_free
        

    let launch_analysis func_name  = 
        let () = Printf.printf "Launch the analysis on %s (%d)\n" func_name (counter ())in
        let dir = Printf.sprintf "%s/%s" (!dir_output) (func_name) in
        let _ = GraphIR.launch_value_analysis func_name (!list_funcs) (!malloc) (!free) (not (!no_clean_stack)) dir (!verbose) (!show_values) (!show_call) (!show_free)  ((!flow_graph_gml) || (!flow_graph_dot) ) (!flow_graph_gml) (!flow_graph_dot) (!flow_graph_disjoint) parsed_func in
        let () = Printf.printf "--------------------------------\n" in
        flush Pervasives.stdout

    let launch_analysis_list _funcs_name = let open Function_ in List.iter (fun x -> launch_analysis x.name) (!list_funcs)
        
    let end_analysis () = GraphIR.end_analysis ()
    end ;;

(* Callgraph analysis *)
module SuperGraphAnalysis : TAnalysis = functor (Absenv_v : AbsEnvGenerique) -> functor (Ir_v : IR)-> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique)->
struct
    module GraphIR = My_Graph (Absenv_v) (Ir_v) (Stubfunc_v) (Uaf_v)
 
    let list_funcs = ref []
    let parsed_func = Hashtbl.create 100

    let init program_file =
        let () =  GraphIR.set_size (!max_func) in        
        let () =  match !max_ins with
                  | Some d -> GraphIR.set_max_ins d 
                  | None -> () 
        in
        let () = match !total_max_ins with
                  | Some d -> GraphIR.set_total_max_ins d 
                  | None -> () 
        in
        let channel = open_in_bin program_file in
        let buf = Piqirun.init_from_channel channel in
        let raw_program = parse_program buf in
        let () = close_in channel in 
        list_funcs := raw_program.functions


    let launch_analysis func_name  = 
        let dir = Printf.sprintf "%s/%s" (!dir_output) (func_name) in
        let _ = GraphIR.launch_supercallgraph_analysis func_name (!list_funcs)  dir (!verbose) (!show_call) ((!flow_graph_gml) || (!flow_graph_dot) ) (!flow_graph_gml) (!flow_graph_dot) (!flow_graph_disjoint) parsed_func in
        flush Pervasives.stdout

    let launch_analysis_list funcs_name = List.iter (fun x -> launch_analysis  x) funcs_name 
    
    let end_analysis () = ()
end ;;

(* Callgraph analysis *)
module ExportFuncs : TAnalysis = functor (Absenv_v : AbsEnvGenerique) -> functor (Ir_v : IR)-> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique)->
struct
    module GraphIR = My_Graph (Absenv_v) (Ir_v) (Stubfunc_v) (Uaf_v)
 
    let list_funcs = ref []

    let init program_file =
        let channel = open_in_bin program_file in
        let buf = Piqirun.init_from_channel channel in
        let raw_program = parse_program buf in
        let () = close_in channel in 
        list_funcs := raw_program.functions

    let launch_analysis func_name  = 
        let _ = GraphIR.export_func_unloop (!list_funcs) func_name in
        ()

    let launch_analysis_list funcs_name = List.iter (fun x -> launch_analysis x) funcs_name 
    
    let end_analysis () = ()
end ;;

let launch_stub stub p f uaf to_list =
    let m_absenv = match (!absenv) with
        | "2" -> (module Absenv2.AbsEnv :Absenvgenerique.AbsEnvGenerique)
        | "3" -> (module Absenv3.AbsEnv :Absenvgenerique.AbsEnvGenerique)
        | "1-no-top" -> (module Absenvnotop.AbsEnv :Absenvgenerique.AbsEnvGenerique)
        | "2-no-top" -> (module Absenv2notop.AbsEnv :Absenvgenerique.AbsEnvGenerique)
        | "3-no-top" -> (module Absenv3notop.AbsEnv :Absenvgenerique.AbsEnvGenerique)
        | _ -> (module Absenv.AbsEnv :Absenvgenerique.AbsEnvGenerique)
    in let module Absenv = (val m_absenv : Absenvgenerique.AbsEnvGenerique) in
    let m_uaf = match uaf with
        | "alloc" -> (module Uafgroupbyalloc.UafGroupByAlloc : Uafgenerique.UafGenerique)
        | "free" -> (module Uafgroupbyfree.UafGroupByFree : Uafgenerique.UafGenerique)
        | _ -> failwith "Unknow groupby model ? "
    in let module Uaf = (val m_uaf : Uafgenerique.UafGenerique) in
    let m_stub = match stub with
        | "optipng" -> (module Stubfunc.StubOptiPNG : Stubfunc.Stubfunc)  
        | "jasper" -> (module Stubfunc.StubJasper : Stubfunc.Stubfunc)
        | "gnome-nettool" -> (module Stubfunc.StubGnomeNettool : Stubfunc.Stubfunc)  
        | "tiff2pdf" -> (module Stubfunc.StubTiff2pdfLibtiff : Stubfunc.Stubfunc)  
        | _ -> (module Stubfunc.StubNoFunc : Stubfunc.Stubfunc) 
    in let module Stub = (val m_stub : Stubfunc.Stubfunc) in
    let module Analysis = GuebAnalysis(Absenv)(Reil.REIL)(Stub)(Uaf) in
    let () = Analysis.init p in
    let () = match to_list with
    | false -> Analysis.launch_analysis (List.hd f)
    | true ->  Analysis.launch_analysis_list f in
    Analysis.end_analysis ();;

let read_lines_file filename = 
    let lines = ref [] in
    let ()  = Printf.printf "begin\n" in
    let chan = open_in filename in
    let () =
    try while true; do
        let new_line = input_line chan in
        lines := new_line :: !lines 
        done;  
    with End_of_file -> close_in chan in
    List.rev !lines ;;


let () =
    let speclist = [("-v", Arg.Set verbose, "Enable verbose mode");
        ("-show-call", Arg.Set show_call, "Show calls");
        ("-show-free", Arg.Set show_free, "Show freed variables");
        ("-show-values", Arg.Set show_values, "Show values computed (hugeee print)");
      (*  ("-print-graph", Arg.Set print_graph, "Print the graph (for type 2, experimental)");
        ("-merge-output", Arg.Set print_graph, "Merge output values (experimental)");*)
        ("-flow-graph-dot", Arg.Set flow_graph_dot, "Export flow graph (Dot)");
        ("-flow-graph-gml", Arg.Set flow_graph_gml, "Export flow graph (Gml)"); 
        ("-flow-graph-call-disjoint", Arg.Set flow_graph_disjoint, "Export as separate functions");
        ("-reil", Arg.String (fun x -> program:=x), "Name of the Reil.REIL file (protobuf), default : reil");
        ("-func", Arg.String (fun x ->  func:=x), "Name of the entry point function, default : main");
        ("-funcs-file", Arg.String (fun x ->  funcs_file:=x), "Name of the files containing all the functions name");
        ("-stub", Arg.String (fun x -> stub_name:=x), "Name of the stub module");
        ("-type", Arg.Int (fun x -> type_analysis:=x), "\n\t0 : uaf detection (default)\n\t1 : compute callgraph size \n\t2 : uaf detection on a set of functions\n\t3 : compute callgraph size on a set of functions");
        ("-output-dir", Arg.String (fun x -> dir_output:=x), "Output directory. Default results");
        ("-groupby", Arg.String (fun x -> group_by:=x), "Group UaF by (experimental):\n\talloc (default)\n\tfree");
        ("-no-clean-stack", Arg.Set no_clean_stack, "Do not clean stack values after return");
(*        ("-unroll-irreducible", Arg.Set analyze_irreducible_loop, "Unroll irreducible loops");*)
        ("-depth", Arg.Int (fun x -> depth:=Some x), "Max depth of functions analyzed. Default unlimited");
        ("-size", Arg.Int (fun x -> max_func:=x), "Max number of funcs to analyze. Default 400");
        ("-size-ins", Arg.Int (fun x -> max_ins:=Some x), "Max number of ins to analyze. Default unlimited");
        ("-total-ins", Arg.Int (fun x -> total_max_ins:=Some x), "Max number of ins to analyze in total (all entry points). Default unlimited");
        ("-absenv", Arg.String (fun x -> absenv:= x), "Memory model selection: (experimental)\n\t 1 -> default (HA/HF)\n\t 2 -> Pointer based (more precise)\n\t 3 -> Pointer based + use-after-return detection");
    ] in
    let _ =  Arg.parse speclist print_endline "GUEB: Experimental static analyzer detecting heap and stack use-after-free on binary code.\nGUEB is still under intensive development, for any questions, please contact josselin.feist[@]imag.fr\n"  in
    let module Uaf = Uafgroupbyalloc.UafGroupByAlloc in (* not used in SGanalysis *)
    match(!type_analysis) with
        | 0 ->
            launch_stub (!stub_name) (!program) [(!func)] (!group_by) false
        | 1 -> 
            let module SGanalysis = SuperGraphAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
            SGanalysis.init (!program) ;
            SGanalysis.launch_analysis (!func) ;
            SGanalysis.end_analysis () ;
        | 2 ->
            let funcs=read_lines_file (!funcs_file) in
            launch_stub (!stub_name) (!program) funcs (!group_by) true
        | 3 ->
            let funcs=read_lines_file (!funcs_file) in
            let module SGanalysis = SuperGraphAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
            SGanalysis.init (!program) ;
            SGanalysis.launch_analysis_list funcs ;
            SGanalysis.end_analysis () ;
        | 4 -> 
            let module SGanalysis = ExportFuncs(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
            SGanalysis.init (!program) ;
            SGanalysis.launch_analysis (!func) ;
            SGanalysis.end_analysis () ;
        | 5 -> 
            let funcs=read_lines_file (!funcs_file) in
            let module SGanalysis = ExportFuncs(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
            SGanalysis.init (!program) ;
            SGanalysis.launch_analysis_list funcs ;
            SGanalysis.end_analysis () ;
        | 6 ->
            let module SGanalysis = AllFuncs(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
            SGanalysis.init (!program) ;
            SGanalysis.launch_analysis_list [] ;
            SGanalysis.end_analysis () ;
        | _ -> 
            Printf.printf "Bad analysis type\n"
