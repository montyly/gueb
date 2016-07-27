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
let max_depth = ref 400



(* Signature *)
module type TAnalysis = functor (Absenv_v : AbsEnvGenerique)-> functor (Ir_v : IR) -> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique) ->
sig
      val launch_analysis : string ->  string ->  unit
      val launch_analysis_list : string ->  string list ->  unit
end ;;

(* Main analysis *)
module GuebAnalysis: TAnalysis = functor (Absenv_v : AbsEnvGenerique) -> functor (Ir_v : IR) -> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique)->
struct
    module GraphIR = My_Graph (Absenv_v) (Ir_v) (Stubfunc_v) (Uaf_v)
 
    let parsed_func = Hashtbl.create 100

    let launch_analysis program_file func_name  = 
        let () = Printf.printf "Launch the analysis on %s\n" func_name in
        let channel =
            try open_in_bin program_file 
            with _ -> let () = Printf.printf "Reil.REIL file not found (have you used -reil ? )\n" in exit 0
        in
        let buf = Piqirun.init_from_channel channel in
        let raw_program = parse_program buf in
        let () = close_in channel in 
        let raw_heap_func = raw_program.heap_func in
        let list_funcs = raw_program.functions in
        let malloc = List.map (fun x -> Int64.to_int x) raw_heap_func.call_to_malloc in
        let free = List.map (fun x -> Int64.to_int x) raw_heap_func.call_to_free in
        let dir = Printf.sprintf "%s/%s" (!dir_output) (func_name) in
        let _ = GraphIR.launch_value_analysis func_name list_funcs malloc free dir (!verbose) (!show_values) (!show_call) (!show_free)  ((!flow_graph_gml) || (!flow_graph_dot) ) (!flow_graph_gml) (!flow_graph_dot) (!flow_graph_disjoint) parsed_func in
        Printf.printf "--------------------------------\n";
        GraphIR.end_analysis ()

    let launch_analysis_list program_file funcs_name = 
        List.iter (fun x -> launch_analysis program_file x) funcs_name 
    end ;;

(* Callgraph analysis *)
module SuperGraphAnalysis : TAnalysis = functor (Absenv_v : AbsEnvGenerique) -> functor (Ir_v : IR)-> functor (Stubfunc_v : Stubfunc) -> functor (Uaf_v : UafGenerique)->
struct
    module GraphIR = My_Graph (Absenv_v) (Ir_v) (Stubfunc_v) (Uaf_v)
 
    let parsed_func = Hashtbl.create 100

    let launch_analysis program_file func_name  = 
        let channel = open_in_bin program_file in
        let buf = Piqirun.init_from_channel channel in
        let raw_program = parse_program buf in
        let () = close_in channel in 
        let list_funcs = raw_program.functions in
        let dir = Printf.sprintf "%s/%s" (!dir_output) (func_name) in
        let _ = GraphIR.launch_supercallgraph_analysis func_name list_funcs  dir (!max_depth) (!verbose) (!show_call) ((!flow_graph_gml) || (!flow_graph_dot) ) (!flow_graph_gml) (!flow_graph_dot) (!flow_graph_disjoint) parsed_func in
        flush Pervasives.stdout

    let launch_analysis_list program_file funcs_name = 
        List.iter (fun x -> launch_analysis program_file x) funcs_name 
end ;;

let launch_stub stub p f _uaf =
    let module Uaf = Uafgroupbyfree.UafGroupByFree in
    let module M0 = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
    let module M_Optipng = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubOptiPNG)(Uaf) in
    let module M_Jasper = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubJasper)(Uaf) in 
    let module M_Gnome_nettool = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubGnomeNettool)(Uaf) in
    let module M_Tiff2pfd = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubTiff2pdfLibtiff)(Uaf) in
    match (stub) with
        | "optipng" -> M_Optipng.launch_analysis p f  
        | "jasper" -> M_Jasper.launch_analysis p f  
        | "gnome-nettool" -> M_Gnome_nettool.launch_analysis p f  
        | "tiff2pdf" -> M_Tiff2pfd.launch_analysis p f  
        | _ -> M0.launch_analysis p f 

let launch_stub_list stub p f _uaf =
    let module Uaf = Uafgroupbyfree.UafGroupByFree in
    let module M0 = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
    let module M_Optipng = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubOptiPNG)(Uaf) in
    let module M_Jasper = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubJasper)(Uaf) in 
    let module M_Gnome_nettool = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubGnomeNettool)(Uaf) in
    let module M_Tiff2pfd = GuebAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubTiff2pdfLibtiff)(Uaf) in
    match (stub) with
        | "optipng" -> M_Optipng.launch_analysis_list p f  
        | "jasper" -> M_Jasper.launch_analysis_list p f  
        | "gnome-nettool" -> M_Gnome_nettool.launch_analysis_list p f  
        | "tiff2pdf" -> M_Tiff2pfd.launch_analysis_list p f  
        | _ -> M0.launch_analysis_list p f 

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
        ("-type", Arg.Int (fun x -> type_analysis:=x), "\n\t0 : uaf detection (default)\n\t1 : compute callgraph size (NOT WORKING on BinNavi 6)\n\t2 : uaf detection on a set of functions\n\t3 : compute callgraph size on a set of functions");
        ("-depth", Arg.Int (fun x -> max_depth:=x), "Max number of funcs to analyze (type 1 and 3). Default 400");
        ("-output_dir", Arg.String (fun x -> dir_output:=x), "Output directory, default /tmp");
    ] in
    let _ =  Arg.parse speclist print_endline "GUEB : Static analyzer\n"  in
    let module Uaf = Uafgroupbyfree.UafGroupByFree in
    match(!type_analysis) with
        | 0 ->
            launch_stub (!stub_name) (!program) (!func) "uaffree" 
        | 1 -> 
            let module SGanalysis = SuperGraphAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
            SGanalysis.launch_analysis (!program) (!func) ;
        | 2 ->
            let funcs=read_lines_file (!funcs_file) in
            launch_stub_list (!stub_name) (!program) funcs "uaffree" 
        | 3 ->
            let funcs=read_lines_file (!funcs_file) in
            let module SGanalysis = SuperGraphAnalysis(Absenv.AbsEnv)(Reil.REIL)(StubNoFunc)(Uaf) in
            SGanalysis.launch_analysis_list (!program) funcs ;
        | _ -> 
            Printf.printf "Bad analysis type\n"
