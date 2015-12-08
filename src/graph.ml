open Absenv;;
open Ir ;;
open Unix;;
open Stubfunc;;

(*
 * Debug fonction
 * *)
let print s=Printf.printf "%s %s\n" s (Printf.sprintf "%d:%d" ((int_of_float (Sys.time()*.100.))/60) ((mod) (int_of_float (Sys.time()*.100.)) 60)  );
            Pervasives.flush Pervasives.stdout;;

let print_ram () = 
    let gc=Gc.quick_stat() in Printf.sprintf "%f mo used"(((gc.Gc.minor_words+.gc.Gc.major_words-.gc.Gc.promoted_words)*.8.)/.(1024.*.1024.*.1024.)) ;;

let type_NODE_NORMAL   =       0b0;;
let type_NODE_MALLOC   =       0b1;;
let type_NODE_FREE     =      0b10;;
let type_NODE_CALL     =     0b100;;
let type_NODE_RETN     =    0b1000;;
let type_NODE_ENTRY    =  0b100000;;
let type_NODE_NOT_LOAD = 0b1000000;;


module My_Graph (Absenv_v : AbsEnvGenerique) (Ir_a : IR) (Stubfunc_a : Stubfunc) =
struct

    exception ERROR;;
    exception NOT_RET of (Absenv_v.absenv list)*(Absenv_v.he list)*(Absenv_v.he list)*bool;;
    exception NOT_RET_NOT_LEAF;;
    exception Timeout_unloop;;

    module Ir_v = Ir_a (Absenv_v)
    module Stubfunc_v = Stubfunc_a (Absenv_v)
    type node =
    {
        addr : int ;
        stmt : Ir_v.ir_stmt;
        unloop : int ;
        mutable type_node : int;
        mutable init : Absenv_v.absenv list;
        mutable vsa : Absenv_v.absenv list;
        mutable ha : Absenv_v.he list;
        mutable hf : Absenv_v.he list;
    };;
    type bb = {
        uniq_id : int ;
        addr_bb : int;
        mutable sons : bb list;
        mutable sons_kosaraju : bb list; (* Dirty hack -> sons are erase during kosaraju*)
        mutable fathers : bb list;
        mutable nodes : node list;
        mutable fathers_kosaraju : bb list; (* Dirty hack -> sons are erase during kosaraju*)
        mutable unloop : int; (* use when copy during unrooling node*)
        mutable is_done : bool; (*value analysis done *)
    };;

    type site = ((int*int)*string*int)

    let number_bbs=ref 0

    let number_call = ref 0

    let current_call = ref 0
    
    let saved_values = ref [] 
   
    let saved_call = ref [] 
    
    (* Hashtbl that contains result 
     * form :
     *  (id,size)  *   free sites  * malloc site * use sites 
     * *)
    let sg_uaf = ((Hashtbl.create 100) : (( (int*int) * ((site list) list)   , (site list) *   ((site list) list) ) Hashtbl.t )) ;;

    (* 
     * pretty print for sg_uaf
     *)
    let pp_uaf_label l  = String.concat "\n" (List.map (fun (p,(addr,it),f,n) -> (Printf.sprintf "%s%d%d[label=\"0x%x:%d call %s\"]" p (addr/0x100) it (addr/0x100) it f) ) l)
  
    let add_p l =
        let l = List.rev l in 
        let p = ref "" in
        let l =List.map 
            (fun ((addr,it),f,n) ->
                let ret = ((!p),(addr,it),f,n) in
                let _ = p:=(!p)^(Printf.sprintf "%d%d" (addr/0x100) it) in
                ret 
            ) l
        in
        List.rev l

   let pp_uaf st=
        let st = List.rev st in
        let pp (p,(addr,it),f,n) = (Printf.sprintf "%s%d%d" p (addr/0x100) it ) in
        Printf.sprintf "%s" (List.fold_left (fun x y -> x^"->"^(pp y)) (pp (List.hd st)) (List.tl st));;

    let pp_uafs st =
        List.fold_left (fun x y -> (pp_uaf y) ^ " \n " ^ x ) (pp_uaf (List.hd st)) (List.tl st);;

    let pp_alloc (p,(addr,it),f,n) = Printf.sprintf "%s%d%d[label=\"%s -> 0x%x:%d alloc\", style=filled,shape=\"box\", fillcolor=\"turquoise\"]" p (addr/0x100) it f (addr/0x100) it
    
    let pp_free free = String.concat "\n" (List.map (fun (p,(addr,it),f,n) ->  Printf.sprintf "%s%d%d[label=\"%s -> 0x%x:%d free\", style=filled,shape=\"box\", fillcolor=\"green\"]" p (addr/0x100) it f (addr/0x100) it) free)
    
    let pp_use use = String.concat "\n" (List.map (fun (p,(addr,it),f,n) ->  Printf.sprintf "%s%d%d[label=\"%s -> 0x%x:%d use\", style=filled,shape=\"box\", fillcolor=\"red\"]" p  (addr/0x100) it f  (addr/0x100) it) use)

    (*
     * print to dot format
     *)
    let print_uaf_dot filename alloc free use = 
        let oc = open_out filename in
        let alloc = add_p ( alloc) in
        let free = List.map (fun x -> add_p ( x)) free in
        let use = List.map (fun x -> add_p ( x)) use in
        let _ = Printf.fprintf oc "strict digraph g {\n" in
        let _ = Printf.fprintf oc "%s\n" (pp_uaf alloc) in
        let _ = Printf.fprintf oc "%s\n" (pp_uafs free) in
        let _ = Printf.fprintf oc "%s\n" (pp_uafs use) in
        let _ = Printf.fprintf oc "%s\n" (pp_uaf_label (List.tl alloc)) in
        let _ = Printf.fprintf oc "%s\n" (pp_uaf_label (List.concat (List.map (fun x -> List.tl x )free))) in
        let _ = Printf.fprintf oc "%s\n" (pp_uaf_label (List.concat (List.map (fun x -> List.tl x ) use))) in
        let _ = Printf.fprintf oc "%s\n" (pp_alloc (List.hd alloc (*(List.length alloc)-1*))) in
        let _ = Printf.fprintf oc "%s\n" (pp_free (List.map ( fun x ->(List.hd x (*(List.length x)-1*)) ) free)) in
        let _ = Printf.fprintf oc "%s\n" (pp_use (List.map ( fun x ->(List.hd x (*(List.length x)-1*)) ) use)) in
        let _ = Printf.fprintf oc "}\n" in
        close_out oc

    let print_uaf_values oc values calls chunk_id chunk_type alloc free use =
        let check bb addr it =
            List.exists (fun x ->
                 x.addr = addr
            ) bb.nodes
        in
        let ((alloc_addr,alloc_it),alloc_func_name,alloc_call_n) = List.hd alloc in
        let frees = List.map (fun x -> List.hd x) free in
        let uses = List.map (fun x -> List.hd x) use in
        let rec walk values bb_alloc bb_free bb_use = 
            match values with
            | (y,key)::tl ->
(*                let () = 
                    begin
                        let () = Printf.printf "-------\n" in let _ = check y alloc_addr alloc_it in Printf.printf "#######\n"
                    end
                in*)
(*                let () = Printf.printf "Key %d call_n %d\n" key alloc_call_n in*)
                let () = if (key = alloc_call_n && check y alloc_addr alloc_it) then
                    Printf.fprintf oc "%03d%d[style=filled,fillcolor=\"mediumspringgreen\",hack=2]\n" alloc_call_n  y.addr_bb
                in
                let () = List.iter 
                    (fun ((free_addr,free_it),free_func_name,free_call_n) ->
                        if (key = free_call_n && (check y free_addr free_it)) then
                            Printf.fprintf oc "%03d%d[style=filled,fillcolor=\"green\",hack=4]\n" free_call_n y.addr_bb
                    ) frees
                in
                let () = List.iter 
                    (fun ((use_addr,use_it),use_func_name,use_call_n) ->
                        if (key = use_call_n && check y use_addr use_it) then
                            Printf.fprintf oc "%03d%d[style=filled,fillcolor=\"red\",hack=6]\n" use_call_n y.addr_bb
                    ) uses
                in
                walk tl bb_alloc bb_free bb_use     
            | _ -> ()
        in walk values [] [] []

    let subgraph_extraction oc values calls chunk_id chunk_type alloc free use =    
        let check bb addr it =
            it = bb.unloop &&
            List.exists (fun x ->
                 x.addr = addr
            ) bb.nodes
        in
        let find_node ((n_addr,n_it),n_func_name,n_call) =
            let rec walk vals = 
                match vals with
                | [] -> raise Not_found
                | (y,key)::tl ->
                    if(key = n_call && check y n_addr n_it ) then (y,key)
                    else walk tl
            in
            walk values
        in 
        let l = ref [] in
        let rec walk_desc n ori_to_dst =
            match n with
            | [] -> (!l)
            | (bb,key)::hd ->
                        if ( List.exists( fun (x,n) -> x.addr_bb = bb.addr_bb && n = key && x.unloop = bb.unloop ) (!l))  then (walk_desc hd ori_to_dst)
                        else   
                            let () = List.iter 
                                (fun (ori,dst,ori_n,dst_n) -> 
                                    if (ori.addr_bb = bb.addr_bb && ori_n = key && ori.unloop = bb.unloop ) then
                                        let _ = walk_desc [(dst,dst_n)] ori_to_dst
                                        in ()
                                ) calls
                            in
                            let () =  if(ori_to_dst) then 
                                List.iter 
                                (fun (ori,dst,ori_n,dst_n) -> 
                                    if (dst.addr_bb = bb.addr_bb && dst_n = key && dst.unloop = bb.unloop ) then
                                        let _ = walk_desc (List.map (fun x -> x,ori_n) ori.sons) ori_to_dst
                                        in ()
                                ) calls
                            in
                            let () = Printf.printf "number son %d %x %d\n"  key bb.addr_bb (List.length bb.sons) in
                            let walk_sons = walk_desc (List.map (fun x -> x,key ) bb.sons) ori_to_dst in
                            if ( List.exists( fun (x,n) -> x.addr_bb = bb.addr_bb  && n = key && x.unloop = bb.unloop ) (!l)) then walk_sons @ (walk_desc hd ori_to_dst)
                            else
                                let () = Printf.printf "ici\n" in
                                let () = l := ((bb,key)::(!l)) in
                                walk_sons @ (walk_desc hd ori_to_dst)
        in 
        let rec walk_asc n = 
            match n with
            | [] -> (!l)
            | (bb,key)::hd ->
                        if ( List.exists( fun (x,n) -> x.addr_bb = bb.addr_bb  && n = key && x.unloop = bb.unloop ) (!l)) then (walk_asc hd)
                        else    
                           let () = List.iter 
                                (fun (ori,dst,ori_n,dst_n) -> 
                                    if (ori.addr_bb = bb.addr_bb && ori_n = key && ori.unloop = bb.unloop ) then
                                        let () = l := ((bb,key)::(!l)) in (* should do better here *)
                                        let _ = walk_desc [(dst,dst_n)] false
                                        in ()
                                ) calls
                           in
                           let () = List.iter 
                                (fun (ori,dst,ori_n,dst_n) -> 
                                    if (dst.addr_bb = bb.addr_bb && dst_n = key && dst.unloop = bb.unloop ) then
                                        let _ = walk_asc [(ori,ori_n)]
                                        in ()
                                ) calls
                            in
                            let walk_fathers = walk_asc (List.map (fun x -> x,key) bb.fathers) in
                            if ( List.exists( fun (x,n) -> x.addr_bb = bb.addr_bb  && n = key && x.unloop = bb.unloop ) (!l)) then walk_fathers @ (walk_asc hd)
                            else
                                let () = l := ((bb,key)::(!l)) in
                                walk_fathers @ (walk_asc hd)
        in
        try
            let node_alloc = find_node (List.hd alloc) in
            let nodes_free = List.map (fun x -> find_node (List.hd x) ) free in
            let () = List.iter (fun (x,k) -> Printf.printf "Node free %x\n" x.addr_bb) nodes_free in
            let nodes_use = List.map (fun x -> find_node (List.hd x) ) use in
            let () = l:=[] in
            let _ = walk_asc [node_alloc]  in
            let nodes_entry_alloc = (!l) in
            let () = l:=[] in
            let _ = walk_desc [node_alloc] true in
            let nodes_from_alloc_to_free = (!l) in
            let () = l:=[] in
            let nodes_from_free_to_alloc = walk_asc nodes_free  in
            let () = l:=[] in
            let nodes_alloc_free = List.filter (fun (x,key_x) -> List.exists (fun (y,key_y) -> y.addr_bb=x.addr_bb && key_y = key_x) nodes_from_alloc_to_free ) (List.rev nodes_from_free_to_alloc) in (* list.rev as optim *)
            let () = Printf.printf "Nodes free to use %d \n" (List.length (!l)) in
            let _ = walk_desc nodes_free true in
            let () = Printf.printf "Nodes free to use stop\n" in
            let nodes_from_free_to_use = (!l) in
            let () = l:=[] in
            let nodes_from_use_to_free = walk_asc nodes_use  in
            let nodes_free_use = List.filter (fun (x,key_x) -> List.exists (fun (y,key_y) -> y.addr_bb=x.addr_bb && key_y = key_x) nodes_from_free_to_use ) (List.rev nodes_from_use_to_free) in (* list.rev as optim *)
            let () = List.iter
                (fun (x,key) -> 
                    Printf.fprintf oc "%03d%d[style=filled,fillcolor=\"cadetblue1\",hack=1]\n" key  x.addr_bb ) nodes_entry_alloc  in
            let () = List.iter
                (fun (x,key) -> 
                    Printf.fprintf oc "%03d%d[style=filled,fillcolor=\"darkorchid1\",hack=3]\n" key  x.addr_bb ) nodes_alloc_free  in
            List.iter
                (fun (x,key) -> 
                    Printf.fprintf oc "%03d%d[style=filled,fillcolor=\"yellow\",hack=5]\n" key  x.addr_bb ) nodes_free_use
        with Not_found -> Printf.printf "Error, node not found during subgraph extraction\n"

    let print_values dir values calls =
        let txt = Printf.sprintf "strict digraph g {\n" in
        let pp_val_bb bb = Printf.sprintf "0x%x" bb.addr_bb in
        let pp_val_node n = Printf.sprintf "0x%x" n.addr in
        let sg_uaf_by_alloc = ((Hashtbl.create 100) : ((int*int  ,  ( (site list *  ((site list) list) * ((site list) list)) ) list ) Hashtbl.t ))  in
        (* first ordone result by alloc, not by free *)
        let _ =
            Hashtbl.iter 
                (fun ((chunk_id,chunk_type),free) (alloc,use) ->
                    let key = chunk_id,chunk_type in
                    try
                        let elems=Hashtbl.find sg_uaf_by_alloc key in
                        Hashtbl.replace sg_uaf_by_alloc key ((alloc,free,use)::elems)
                    with
                    Not_found -> Hashtbl.add sg_uaf_by_alloc key [alloc,free,use]
                ) sg_uaf in
      (*  let print_values_dot_stream_node oc n =
            let prev_addr = ref 0 in
            let access_heap= List.fold_left (fun x y -> Printf.sprintf "%s %s" x (Absenv_v.pp_chunk y)) ""  (Ir_v.access_heap n.stmt n.vsa) in
            let () = if(!prev_addr>0)
                then
                Printf.fprintf oc "%d -> %d\n%d[label=\"%s AccessHeap %s HF %s\"]\n" (!prev_addr) n.addr n.addr (pp_val_node n) access_heap "empty"
            else
                Printf.fprintf oc "%d[label=\"%s AccessHeap %s HF %s\"]\n" n.addr (pp_val_node n)  access_heap "empty"
            in prev_addr := n.addr 
        in *)
        let print_values_dot_stream_bb bb counter =
            let access_heap = List.map (fun x -> Ir_v.access_heap x.stmt x.vsa) bb.nodes in
            let access_heap = List.concat access_heap in
            let access_heap = List.map (fun x -> Absenv_v.pp_chunk x) access_heap in
            let access_heap = List.sort_uniq String.compare access_heap in
            let access_heap = 
                if(List.length access_heap > 0)
                then
                     Printf.sprintf "\\nAccessHeap %s" (List.fold_left (fun x y -> Printf.sprintf "%s %s" x y) "" access_heap) 
                else Printf.sprintf "" 
            in
            let txt = Printf.sprintf "%03d%d[label=\"%d : %x%s\"]\n" (counter) bb.addr_bb counter bb.addr_bb access_heap in
            List.fold_left (fun x y -> Printf.sprintf "%s%03d%d -> %03d%d\n" x (counter) bb.addr_bb (counter)  y.addr_bb) txt bb.sons
        in
        (* order bb by functions *)
        let tbl = Hashtbl.create 200 in
        let () = List.iter 
            (fun (y,key) -> (* key is the number of the function *) 
                    try
                        let elems=Hashtbl.find tbl key in
                        Hashtbl.replace tbl key (y::elems)
                    with
                    Not_found -> Hashtbl.add tbl key [y]
            ) values in
        let txt = Hashtbl.fold
            (fun key l prev ->
                let txt = Printf.sprintf "%ssubgraph cluster_%d { \n" prev (key)  in
                let txt = List.fold_left (fun x y -> Printf.sprintf "%s%s" x (print_values_dot_stream_bb y key)) txt l in
                Printf.sprintf "%s}\n" txt
            ) tbl txt in
        let txt = List.fold_left (
            fun x (ori,dst,ori_n,dst_n) -> 
                Printf.sprintf "%s%03d%d -> %03d%d\n" x ori_n ori.addr_bb dst_n dst.addr_bb
                ) txt calls in
(*        Hashtbl.iter
            (fun ((chunk_id,chunk_type),free) (alloc,use) ->
                let str =       
                    match chunk_type with
                    | 0 -> "chunk"
                    | 1 -> "init_val"
                    | _ -> "unknow"
                in
                let oc = open_out (Printf.sprintf "%s/uaf-%s%d-details.dot" dir str  chunk_id) in
                let () = Printf.fprintf oc "%s" txt in
                let () = subgraph_extraction oc values calls chunk_id chunk_type alloc free use in
                let () = print_uaf_values oc values calls chunk_id chunk_type alloc free use in
                let _ = Printf.fprintf oc "}\n" in
                close_out oc
        ) sg_uaf*)
        Hashtbl.iter 
            (fun (chunk_id,chunk_type) elems -> 
                let str =       
                    match chunk_type with
                    | 0 -> "chunk"
                    | 1 -> "init_val"
                    | _ -> "unknow"
                in 
                let n = ref 0 in
                List.iter 
                    (fun (alloc,free,use) ->
                        let () = n := (!n)+1 in
                        let oc = open_out (Printf.sprintf "%s/uaf-%s%d-%ddetails.dot" dir str  chunk_id (!n)) in
                        let () = Printf.fprintf oc "%s" txt in
                        let () = subgraph_extraction oc values calls chunk_id chunk_type alloc free use in
                        let () = print_uaf_values oc values calls chunk_id chunk_type alloc free use in
                        let _ = Printf.fprintf oc "}\n" in
                        close_out oc
                ) elems
        ) sg_uaf_by_alloc 
        
    let print_graph_dot dir values calls =
        let txt = Printf.sprintf "strict digraph g {\n" in
        let pp_val_bb bb = Printf.sprintf "0x%x" bb.addr_bb in
        let pp_val_node n = Printf.sprintf "0x%x" n.addr in
        let print_values_dot_stream_bb bb counter =
            let access_heap = List.map (fun x -> Ir_v.access_heap x.stmt x.vsa) bb.nodes in
            let access_heap = List.concat access_heap in
            let access_heap = List.map (fun x -> Absenv_v.pp_chunk x) access_heap in
            let access_heap = List.sort_uniq String.compare access_heap in
            let access_heap = 
                if(List.length access_heap > 0)
                then
                     Printf.sprintf "\\nAccessHeap %s" (List.fold_left (fun x y -> Printf.sprintf "%s %s" x y) "" access_heap) 
                else Printf.sprintf "" 
            in
            let txt = Printf.sprintf "%03d%d[label=\"%d : %x%s\"]\n" (counter) bb.addr_bb counter bb.addr_bb access_heap in
            List.fold_left (fun x y -> Printf.sprintf "%s%03d%d -> %03d%d\n" x (counter) bb.addr_bb (counter)  y.addr_bb) txt bb.sons
        in
        (* order bb by functions *)
        let tbl = Hashtbl.create 200 in
        let () = List.iter 
            (fun (y,key) -> (* key is the number of the function *) 
                    try
                        let elems=Hashtbl.find tbl key in
                        Hashtbl.replace tbl key (y::elems)
                    with
                    Not_found -> Hashtbl.add tbl key [y]
            ) values in
        let find_leafs n = 
            let nodes = Hashtbl.find tbl n in
            let leafs = List.find_all (fun x -> List.length x.sons == 0) nodes in
            let is_loop n = List.exists (fun x -> (x.addr_bb = n.addr_bb) && (x.unloop != n.unloop)) nodes in
            List.filter (fun x -> not (is_loop x)) leafs 
        in
        let txt = List.fold_left (
            fun x (ori,dst,ori_n,dst_n) ->
                if (ori.unloop ==0) then
                  let leafs =  find_leafs dst_n in
                  let ori_son = List.hd ori.sons in (* todo : call with many sons ? *)
                  let txt = List.fold_left (fun y x -> Printf.sprintf "%s%03d%d -> %03d%d\n" y dst_n x.addr_bb ori_n ori_son.addr_bb ) "" leafs in 
(*                  let txt = Printf.sprintf "%s%03d%0d -> %03d%d[style=dashed]\n" txt ori_n ori.addr_bb ori_n ori_son.addr_bb in*)
                  let () = ori.sons <- [] in
                  Printf.sprintf "%s%s%03d%d -> %03d%d\n" x txt ori_n ori.addr_bb dst_n dst.addr_bb
                else  
                    begin
                    let () = Hashtbl.remove tbl dst_n in
                    let () = ori.sons <- [] in
                    x
                    end
                ) txt calls in
        let txt = Hashtbl.fold
            (fun key l prev ->
               (* let txt = Printf.sprintf "%ssubgraph cluster_%d { \n" prev (key)  in
                let txt = List.fold_left (fun x y -> Printf.sprintf "%s%s" x (print_values_dot_stream_bb y key)) txt l in *)
                let txt = List.fold_left (fun x y -> Printf.sprintf "%s%s" x (print_values_dot_stream_bb y key)) prev l in
                txt
              (*  Printf.sprintf "%s}\n" txt*)
            ) tbl txt in
        let oc = open_out (Printf.sprintf "%s/graph.dot" dir) in
        let () = Printf.fprintf oc "%s" txt in
        let () = Printf.fprintf oc "}\n" in
        close_out oc



(*
    let print_sg_values dir_output =
        Hashtbl.iter
            (fun ((chunk_id,chunk_type),free) (alloc,use) ->
                print_uaf_values "/tmp/test" (!saved_values) (!saved_call) chunk_id chunk_type alloc free use
        ) sg_uaf
*)

    let print_sg dir_output =
        if (Hashtbl.length sg_uaf) == 0 then ()
        else
        let () =
        try 
            Unix.mkdir dir_output 0o777 
        with
            _ -> ()
        in
        let sg_uaf_by_alloc = ((Hashtbl.create 100) : ((int*int  ,  ( (site list *  ((site list) list) * ((site list) list)) ) list ) Hashtbl.t ))  in
        (* first ordone result by alloc, not by free *)
        let _ =
            Hashtbl.iter 
                (fun ((chunk_id,chunk_type),free) (alloc,use) ->
                    let key = chunk_id,chunk_type in
                    try
                        let elems=Hashtbl.find sg_uaf_by_alloc key in
                        Hashtbl.replace sg_uaf_by_alloc key ((alloc,free,use)::elems)
                    with
                    Not_found -> Hashtbl.add sg_uaf_by_alloc key [alloc,free,use]
                ) sg_uaf in
        let _ = Printf.printf "Results, uaf found : \n\n" in
        Hashtbl.iter 
            (fun (chunk_id,chunk_type) elems -> 
                let str =       
                begin 
                    match chunk_type with
                    | 0 -> "chunk"
                    | 1 -> "init_val"
                    | _ -> "unknow"
                end
                in
                let n = ref 0 in
                let _ = List.iter (fun (alloc,free,use) -> print_uaf_dot (let _ = n:=!n+1 in Printf.sprintf "%s/uaf-%s%d-%d.dot" dir_output str chunk_id !n)  alloc free use ) elems in
                let _ = Printf.printf "%s%d is an uaf :\n" str chunk_id in
                let _ = List.iter (fun (alloc,free,use) ->
                    let alloc_str=Absenv_v.pp_state alloc in
                    let free_str=List.fold_left (fun x y -> (Absenv_v.pp_state y)^"\n\t"^x) "" free in  
                    let use_str= List.fold_left (fun x y -> (Absenv_v.pp_state y)^"\n\t"^x) "" use in    
                    Printf.printf "Allocated in \n\t%s\nfreed in \n\t%s\nused in \n\t%s\n--------------------------------------\n"        
                    alloc_str free_str use_str ) elems in
                Printf.printf "#################################\n" 
            ) sg_uaf_by_alloc ;;

    let print_sg_details sg values dir_output = 
        if (Hashtbl.length sg) == 0 then ()
        else
        let () =
        try 
            Unix.mkdir dir_output 0o777 
        with
            _ -> ()
        in
        let sg_uaf_by_alloc = ((Hashtbl.create 100) : ((int*int  ,  ( (site list *  ((site list) list) * ((site list) list)) ) list ) Hashtbl.t ))  in
        (* first ordone result by alloc, not by free *)
        let _ =
            Hashtbl.iter 
                (fun ((chunk_id,chunk_type),free) (alloc,use) ->
                    let key = chunk_id,chunk_type in
                    try
                        let elems=Hashtbl.find sg_uaf_by_alloc key in
                        Hashtbl.replace sg_uaf_by_alloc key ((alloc,free,use)::elems)
                    with
                    Not_found -> Hashtbl.add sg_uaf_by_alloc key [alloc,free,use]
                ) sg in
        Hashtbl.iter 
            (fun (chunk_id,chunk_type) elems -> () 

        ) sg_uaf_by_alloc ;;



    let get_nodes l = List.map (fun y ->y.nodes) l;;
    
    let get_nodes_from_bbs b = List.concat (get_nodes b);;

    let rec find_bb bbs addr =
        match bbs with
        | [] -> None
        | hd :: tl -> if hd.addr_bb == addr then Some hd
                      else find_bb tl addr;;


    let connect_bb bbs connexion = 
        let (f,s)=connexion in
        match (find_bb bbs f),(find_bb bbs s) with
        | None,_ | _,None -> ()
        | Some father,Some son -> let _= father.sons <- son::father.sons in let _= son.fathers <- father::son.fathers in ()  ;;  

    let rec connect_bbs bbs connexions =
        match connexions with
        | [] -> List.rev bbs
        | hd :: tl ->  let _ =connect_bb bbs hd  in connect_bbs bbs tl ;;

    let rec update_type nodes addrs type_node=
        match addrs with
        | [] -> ()
        | tl::hd ->
                List.iter (fun x -> 
                        match x.addr with
                        | _ when x.addr=tl -> let _ = x.type_node<-(lor) x.type_node type_node in  ()
                        | _ -> ()
                        ) nodes;
                update_type nodes hd type_node;;

    let update_call_retn nodes call_retn =
        let (call,retn)=call_retn in
        let _ =update_type nodes call type_NODE_CALL in
        update_type nodes retn type_NODE_RETN;;

    let update_malloc_free_protobuf list_nodes malloc_addr free_addr =
        List.iter 
            (fun y -> 
                match Ir_v.get_value_jump y.stmt with
                | None -> ()
                | Some a ->
                    if (List.exists (fun x-> x=a) malloc_addr) then (y.type_node <- (lor) y.type_node type_NODE_MALLOC);
                    if (List.exists (fun x-> x=a) free_addr) then (y.type_node <- (lor) y.type_node type_NODE_FREE);
            ) list_nodes;;           

    let find_eip nodes eip = 
        try
            List.find (fun x -> x.addr_bb=eip) nodes 
        with
            Not_found -> let () = Printf.printf "Error, EIP not found\n" in exit 0;;

    let create_nodes arg =
        let (stmt,addr,unloop)=arg in
        {addr=addr;stmt=stmt;unloop=42;type_node=type_NODE_NORMAL;init = [] ; vsa=[];ha=[];hf=[]};;
   
    let create_bbs_nodes list_nodes list_bb =
        let find list_addr list_nodes=List.find_all (fun n -> List.exists (fun x -> x=n.addr) list_addr) list_nodes in
        let rec create_bbs_rec list_bb list_nodes l =
            match list_bb with
            | [] -> l
            | hd::tl -> 
                let (addr,list_addr_node)=hd in
                 create_bbs_rec tl list_nodes ({uniq_id=0;addr_bb=addr;sons=[];sons_kosaraju=[];fathers=[];fathers_kosaraju=[];unloop=0;is_done=false;nodes=(find list_addr_node list_nodes)}::l)
        in create_bbs_rec list_bb list_nodes [];;
                       
    let create_bb addr =  
            let _ = number_bbs:= (!number_bbs)+1 in
            {uniq_id= !number_bbs;addr_bb=addr;sons=[];sons_kosaraju=[];fathers=[];fathers_kosaraju=[];unloop=0;is_done=false;nodes=[]}
 
    (** Export **)
    
    
    let print_bb_dot stream bb =
        let print_link n0 n1  = Printf.fprintf stream "%d -> %d;\n" n0.uniq_id n1.uniq_id in
        let print_bb n = Printf.fprintf stream "%d[label=\"0x%x:%d (%d)\"];\n" n.uniq_id (n.addr_bb/0x100) n.unloop n.uniq_id in
        let _ = print_bb bb in
        let _ = List.iter (fun x -> print_link bb x) bb.sons in 
        ()
    
    let print_bbs_dots_stream stream bbs=
        let _ = Printf.fprintf stream "digraph g {\n" in
        let rec rec_print_bb_dots bbs =
            match bbs with
            | [] -> ()
            | hd::tl -> let _ = print_bb_dot stream hd in
                        rec_print_bb_dots tl
        in 
        let _ = rec_print_bb_dots bbs in
        Printf.fprintf stream "}\n"
    
    let print_bbs_dots filename bbs = 
        let oc = open_out filename in
        let _ = print_bbs_dots_stream oc bbs in
        close_out oc
    
    (** Manipulate **)
    
    
    (* first : addr low, and unloop low *)
    
    let func_compare x y = 
        if(x.addr_bb<y.addr_bb) then 1
        else if (x.addr_bb==y.addr_bb) then
            if(x.unloop==y.unloop) then 0
            else if(x.unloop<y.unloop) then 1
            else -1
       else -1
    
    let list_sort_uniq x = List.sort_uniq func_compare x
    
    (* TODO if version ocaml too low (sort_uniq is a recent func), should to something cleaner to check this *)
(*    let list_remove x = 
        let rec l_r_rec l st = 
        match l with    
        | [] -> st
        | tl::hd -> if (List.exists (fun x -> x.addr_bb==tl.addr_bb && x.unloop == tl.unloop)  st) then l_r_rec hd st     
                    else l_r_rec hd (tl::st)
        in
        l_r_rec x []
    
    let list_sort_uniq x = list_remove (List.sort func_compare x)*)
    
    let remove_dupplicate elems = list_sort_uniq elems
    
    (* hack number use to differenciate new node when you create it with kosaraju *)
    let hack_number=ref 0;;
    
    let new_node node val_unloop = {addr=node.addr;stmt=node.stmt;unloop=val_unloop; type_node=node.type_node;init=node.init;vsa=node.vsa;ha=node.ha;hf=node.hf};;
   
    let new_bb bb unloop= 
        let _ = number_bbs:=(!number_bbs)+1 in
        {uniq_id= !number_bbs;addr_bb=bb.addr_bb;sons=bb.sons;sons_kosaraju=bb.sons_kosaraju;fathers=bb.fathers;fathers_kosaraju=bb.fathers_kosaraju;unloop=unloop;is_done=false;nodes= []};;
    
    
    (** Function for loop manipulation **)
    
    let find_entry_father nodes=
        let fathers=(List.concat (List.map (fun x -> x.fathers) nodes)) 
           in List.filter (fun x -> List.for_all (fun y -> y.addr_bb!=x.addr_bb || x.unloop!=y.unloop) nodes) fathers ;;
    
    let find_entry nodes head=
        let father_entry=find_entry_father nodes in
        let rec take_son fathers nodes stack = 
        match fathers with 
        | [] -> stack
        | tl::hd -> 
            if (List.exists (fun x -> x.addr_bb==tl.addr_bb && x.unloop == tl.unloop) nodes) 
                then take_son hd nodes (tl::stack)
            else take_son hd nodes stack
        in
        match (take_son (List.concat (List.map (fun x -> x.sons)  father_entry)) nodes []) with
        | [] -> [head]
        | l -> l;;
    
    let find_non_entry fathers stack =
        List.filter (fun x -> List.exists (fun y -> y.addr_bb==x.addr_bb && x.unloop==y.unloop) stack) fathers;;

    let find_arc node stack = 
            let arc_end=find_non_entry node.fathers stack in
                List.map (fun x -> (node,x) ) arc_end;;
    
    let nodes_not_in ori new_nodes= List.filter (fun x -> List.for_all (fun y -> y.addr_bb!=x.addr_bb) new_nodes) (ori);;

    let nodes_in ori new_nodes= List.filter (fun x -> List.exists (fun y -> y.addr_bb==x.addr_bb) ori) new_nodes;; 
    
    let replace_ori ori new_nodes=(nodes_not_in ori new_nodes)@(nodes_in ori new_nodes);;
    
    let add_ori ori new_nodes=
        let rec add_ori_rec ori new_nodes stack =
            match ori with
            | [] -> remove_dupplicate stack
            | tl::hd -> let new_stack = (nodes_not_in [tl] new_nodes) in
                        add_ori_rec hd new_nodes new_stack@stack
        in
        add_ori_rec ori new_nodes ((nodes_in ori new_nodes)@(nodes_not_in new_nodes ori));;
        
    let remove_ori_no_check ori stop=List.filter (fun x -> x.addr_bb!=stop.addr_bb && x.unloop!=stop.unloop) ori;;
        
    let rec find_node_in_nodes node nodes =
         match nodes with
         | [] -> None
         | tl::hd -> if (tl.addr_bb==node.addr_bb) then Some tl
                    else find_node_in_nodes node hd;;
    
    let fix_son_node node nodes new_nodes entry stop=
        let ori_node=(find_node_in_nodes node nodes) in
            match ori_node with
            | None -> ()
            | Some a -> 
                let ori=a.sons in
                let ori_with_new_nodes=replace_ori ori new_nodes in
                if (node.addr_bb==stop.addr_bb)
                    then node.sons<-remove_ori_no_check ori_with_new_nodes entry
                else node.sons<-ori_with_new_nodes;;
    
    let remove_all_fathers nodes=
        List.iter (fun x -> x.fathers<-[]) nodes;;
    
    let add_fathers_from_son nodes=
        List.iter (fun x -> List.iter (fun y -> y.fathers<-(x::y.fathers)) x.sons) nodes;;
    
    let reset_fathers nodes=
        let _ = remove_all_fathers nodes in
        let _ = add_fathers_from_son nodes in
        List.iter (fun x -> x.fathers<-remove_dupplicate x.fathers) nodes ;; 
    
    let rec fix_link_nodes new_nodes nodes nodes2 entry stop=
        match new_nodes with 
        | [] -> ()
        | tl::hd ->
            let _ = fix_son_node tl nodes nodes2 entry stop in
            fix_link_nodes hd nodes nodes2 entry stop ;;
    
    let copy_remove_arc entry stop nodes number_unloop= 
        let rec copy_remove_arc_rec entry stop nodes stack n=
            if n==0 then 
                let _ = fix_link_nodes nodes nodes nodes entry stop in
                stack
            else
                let _ = hack_number:=!hack_number+1 in
                let new_nodes=List.map (fun x -> new_bb x number_unloop ) nodes in
                let _ = fix_link_nodes new_nodes nodes new_nodes entry stop in
                let new_entry=(find_node_in_nodes entry new_nodes) in
                let new_stop=(find_node_in_nodes stop new_nodes) in
                match new_entry,new_stop with
                | None,_ | _,None ->stack
                | Some a, Some b-> 
                    let _ = stop.sons<-add_ori stop.sons [a] in
                    let _ = a.fathers<-add_ori a.fathers [stop] in
                    copy_remove_arc_rec a b new_nodes (new_nodes::stack) (n-1)
        in copy_remove_arc_rec entry stop nodes [nodes] number_unloop;;
    
    let copy_remove_arcs list_arc nodes number_unloop=
        let rec copy_remove_arcs_rec list_arc nodes stack=
            match list_arc with 
            | [] -> stack
            | (a,b)::tl -> copy_remove_arcs_rec tl nodes ((copy_remove_arc a b nodes number_unloop)@stack)
        in
        copy_remove_arcs_rec list_arc nodes [];;
    
    
    let copy_loop nodes entry_points number_unloop=
        let rec copy_loop_rec nodes entry_points stack =
            match entry_points with
            | [] -> stack
            | tl::hd -> 
                let list_arc=find_arc tl nodes in
                let new_stack=copy_remove_arcs list_arc nodes number_unloop in
                copy_loop_rec nodes hd (new_stack@stack)
        in copy_loop_rec nodes entry_points [];;
    
    let unloop nodes number_unloop head=
            let entry_points = remove_dupplicate (find_entry nodes head) in
            let list_list_nodes=copy_loop nodes entry_points number_unloop in
            let concat_list=remove_dupplicate (List.concat list_list_nodes) in
            concat_list;;
    
    
    let unloop_sc sc  number_unloop head =
        let rec unloop_sc_rec sc sc_stack=
            match sc with
            | [] ->  sc_stack
            | hd::tl ->
                if( (List.length hd)> 1)
                    then
                    let new_unloop= (unloop (hd) number_unloop  head) in
                        if(List.length new_unloop<1) 
                            then unloop_sc_rec tl sc_stack
                        else
                            let new_stack =  (new_unloop::sc_stack) in
                            unloop_sc_rec tl new_stack
                else unloop_sc_rec tl (hd::sc_stack)
        in
        let retour=unloop_sc_rec sc [] in 
        let concat_list=List.concat retour in
        let _ =  reset_fathers concat_list in
        retour;;
    
    
    
    (** Kosaraju **)
    (* Filter son/father kosaraju *)
    let remove_on_one_node_son node addr unloop_number=
        node.sons_kosaraju<-List.filter (fun x -> x.addr_bb!=addr || (x.addr_bb==addr && x.unloop != unloop_number) ) node.sons_kosaraju;;
    
    let remove_on_one_node_father node addr unloop_number=
        node.fathers_kosaraju<-List.filter (fun x -> x.addr_bb!=addr || (x.addr_bb==addr && x.unloop != unloop_number) ) node.fathers_kosaraju;;
    
    (* Remove path kosaraju *)
    let remove_path stack node=
        let _  = List.iter (fun x -> remove_on_one_node_father x node.addr_bb node.unloop) stack in
        List.filter (fun x -> x.addr_bb!=node.addr_bb || x.unloop!=node.unloop) stack;;
    
    (* Remove path from stack *)
    let rec remove_path_stack stack path =
        match stack,path with
        | [],_ | _,[] -> stack
        | n,tl::hd  -> remove_path_stack (remove_path n tl) hd;;
    
    
    (* Dfs *)
    (* see https://stackoverflow.com/questions/4653914/topological-sort-in-ocaml *)
    
    let dfs start_node = 
      let rec explore path visited node = 
        if List.exists (fun x -> x.addr_bb==node.addr_bb && x.unloop=node.unloop) path    then visited  
        else if List.exists (fun x -> x.addr_bb==node.addr_bb && x.unloop=node.unloop) visited then visited 
        else     
          let new_path = node :: path in 
          let edges = node.sons_kosaraju in 
          let visited  = List.fold_left (explore new_path) visited edges in
          node :: visited
      in explore [] [] start_node ;; (* TODO : boom if lenght=-1!! *)
    
    
    let dfs_path start_node =
      let rec explore path visited node = 
        if List.exists (fun x -> x.addr_bb==node.addr_bb && x.unloop=node.unloop) path    then visited  
        else if List.exists (fun x -> x.addr_bb==node.addr_bb && x.unloop=node.unloop) visited then visited     
        else     
          let new_path = node :: path in 
          let edges = node.fathers_kosaraju in 
          let visited  = List.fold_left (explore new_path) visited edges in
          node :: visited
      in explore [] [] start_node;;
    
    let exists_son_out n list_nodes=
         not (List.for_all (fun x -> (List.exists (fun y -> y.addr_bb=x.addr_bb && y.unloop=x.unloop) list_nodes) ) n.sons_kosaraju);;   
    
    (* create stack dfs *)
    let create_stack_dfs start_node list_nodes=
        let rec clean_leafs l stack leafs=
            match l with
            | [] -> List.rev stack
            | hd::tl ->  if( exists_son_out hd leafs) then List.rev stack
                         else clean_leafs tl (hd::stack) leafs
        in 
        let rec create start_node stack =
            if ((List.length start_node.sons_kosaraju)==0) then (start_node::stack)
            else let leafs=dfs start_node in
                 let leafs_clean=clean_leafs (List.rev leafs) [] leafs in
                 let _ = List.iter (fun x -> List.iter (fun y -> remove_on_one_node_son y x.addr_bb x.unloop )  list_nodes ) leafs_clean in
                 create start_node ((leafs_clean)@stack)
          in create start_node [];;
    
    let create_strongly_connected stack=
        let rec create stack sc =
            match stack with 
            | [] -> sc
            | tl::hd ->
                let path=dfs_path tl in
                let new_stack = remove_path_stack stack path in
                create new_stack (path::sc)
        in create (List.rev stack) [];;
            
    
    (* Kosaraju algo (no kidding?)  *)
    let kosaraju start_node list_nodes=
        let stack = create_stack_dfs start_node list_nodes in
        create_strongly_connected stack;;
    
    (* Remove loop *)
    let create_leafs sc head =
        List.find_all (
            fun x -> 
                    if (List.exists (fun x -> x.addr_bb = head.addr_bb) x.sons)  
                        then 
                        let () = x.sons <- (List.find_all (fun x -> x.addr_bb != head.addr_bb) x.sons) in
                        let () = head.fathers<-(List.find_all (fun y -> y.addr_bb != x.addr_bb) head.fathers) in
                        true
                   else false
            ) sc ;;
    

    (* debug fonction *)    
    let print_addr l = (String.concat " " (List.map (fun x -> Printf.sprintf "0x%x:%d (%d)" x.addr_bb x.unloop x.uniq_id) l))  
    
    let find_node n nodes n_diff = 
            try List.find (fun x -> (x.addr_bb = n.addr_bb) && (x.unloop=n.unloop+n_diff)) nodes
            with Not_found -> n 
    
    let find_node_no_unloop n nodes  = 
            try List.find (fun x -> (x.addr_bb = n.addr_bb) ) nodes
            with Not_found -> n 
    
    let fix_sons_fathers list_nodes =
        let fix nodes nodes_prev n_diff =
            List.iter (fun x ->
                        let node_prev = find_node x nodes_prev (-n_diff) in
                        let new_fathers = List.map (fun y -> find_node y nodes n_diff) node_prev.fathers in
                        let new_sons = List.map (fun y -> find_node y nodes n_diff) node_prev.sons in
                        let () = x.fathers <- new_fathers in
                        x.sons <- new_sons
                      ) nodes in
        let (n_first,nodes_first) = List.fold_left (fun (n_x,x) (n_y,y) -> if n_x<n_y then (n_x,x) else (n_y,y)) (List.hd list_nodes) (List.tl list_nodes) in
        List.iter (fun (n_x,n) ->   
                        if(n_x!=n_first) then fix n nodes_first (n_x-n_first)
                        else ()
                 ) list_nodes
    
    let copy_nodes list_nodes number_unloop_init =
        let rec copy_nodes_rec list_nodes number_unloop stack =
(*            let () = Printf.printf "Number unloop left %d \n" number_unloop in*)
            let n_unloop=(number_unloop) in
            if number_unloop<=0 then
                let _ = List.iter (fun x -> x.unloop <- x.unloop+n_unloop) list_nodes in
                let new_nodes = list_nodes in
                ((n_unloop,new_nodes)::stack)
            else
                let new_nodes = List.map (fun x -> new_bb x (x.unloop+n_unloop)) list_nodes in
                copy_nodes_rec list_nodes (number_unloop-1) ((n_unloop,new_nodes)::stack)
        in copy_nodes_rec list_nodes number_unloop_init []
       
    let fix_entry_leaf new_nodes list_news_nodes entry leafs = 
        let n,nodes = new_nodes in
        let leafs_n = List.map (fun x -> find_node_no_unloop x nodes) leafs in
        try
            let (_,nodes_n1) = List.find (fun (n1,nodes) -> n1=(n+1)) list_news_nodes in
            let entry_n1 = List.map (fun x -> find_node_no_unloop x nodes_n1) entry in
            let _ = List.iter (fun x -> x.sons <- entry_n1@x.sons) leafs_n in
            let _ = List.iter (fun x -> x.fathers <- leafs_n) entry_n1 in
            nodes
        with
            Not_found -> nodes
    
    let expanse_loop list_nodes entry_point leafs number_unloop = 
        let new_list_nodes = copy_nodes list_nodes number_unloop in
        let new_list_nodes = List.rev (new_list_nodes) in
        let () = fix_sons_fathers new_list_nodes in
        let sc = List.concat (List.map (fun (_,n) -> n) new_list_nodes) in
        let list_nodes = List.map (fun  x ->  fix_entry_leaf x new_list_nodes entry_point leafs) new_list_nodes in
        List.concat list_nodes
    
    let rec unrool head list_nodes number_unloop =
        let select_best_entry l = List.fold_left (fun x y -> if ( List.length x.fathers > List.length y.fathers) then x else y ) (List.hd l) (List.tl l) in
        let exist l = List.find_all (fun x -> List.exists (fun y -> y.addr_bb=x.addr_bb) list_nodes) l in
        let () = List.iter (fun x -> let _ = x.sons_kosaraju<-(exist x.sons) in x.fathers_kosaraju<-(exist x.fathers)) list_nodes in
        let scs = kosaraju head list_nodes in
        let unrool_sc sc head = 
        begin
            if (List.length sc==1) then sc 
            else
            let all_entry_point = find_entry sc head in
            let entry_point = [select_best_entry all_entry_point] in (* quand on a plusieurs entry_point, on en selectionne qu'un pour le reste ? code a changer, vu que par la suite on pouvait en avoir plusieurs ;) TODO *)
            let leafs = List.map (fun x -> (x,create_leafs sc x)) entry_point in (* leafs is list of : entry_point -> leaf*) 
            let sc = unrool (List.hd entry_point) sc number_unloop in
            let _ = List.iter (fun x -> let _ = x.sons_kosaraju<-x.sons in x.fathers_kosaraju<-x.fathers) list_nodes in
            let ret = expanse_loop sc entry_point (List.concat (List.map (fun (x,y) -> y) leafs)) number_unloop  in
            ret
        end
        in List.concat (List.map (fun x -> unrool_sc x head) scs) ;;
    
    let begin_eip b=
    try 
        let n=List.find (fun x -> x.addr==b.addr_bb) b.nodes (* TODO need beeter stuff for EIP... *)
        in n.type_node<-((lor) n.type_node type_NODE_ENTRY)
    with 
      Not_found -> Printf.printf "Eip not found ! \n"
    
    let find_nodes_from_addr list_addr list_nodes val_unloop=List.map (fun x -> new_node x val_unloop ) (List.find_all (fun n -> List.exists (fun x -> x=n.addr) list_addr) list_nodes );;
    
    let parse_protobuf_number func call_to_malloc call_to_free number_unloop  =
        let (bbs,connexion_unfiltre,eip_addr,_,nodes,call_retn)=Ir_v.parse_func_protobuf func in
        let connexion=List.filter (fun (x,y) -> x!=y) connexion_unfiltre in (* TODO need to handle loop on himself ! *)
        let bb_nodes = List.map (fun x -> let (addr,list_nodes)=x in (create_bb addr,list_nodes)) bbs in
        let bbs_only=List.map (fun x-> let (a,b)=x in a)  bb_nodes in
        let bbs_connect= connect_bbs bbs_only connexion in
        let eip=find_eip bbs_connect eip_addr in
        let bb_unloop= unrool eip bbs_connect number_unloop  in
        let f addr l = 
            let (bb_ret,list_ret) = List.find (fun x -> let (a,b)=x in a.addr_bb==addr) l 
            in list_ret
        in
        let bbs_with_nodes_list=List.map (fun x -> (x,f x.addr_bb bb_nodes)) bb_unloop in
        let nodes_begin=(List.map create_nodes nodes) in
        let bbs=List.map (
            fun x-> 
                let (bb,list_nodes)=x in
                let () = bb.nodes<- (find_nodes_from_addr list_nodes nodes_begin bb.unloop) in bb
            ) bbs_with_nodes_list in
        let nodes=List.concat (List.map (fun x -> x.nodes) bbs) in
        let () = begin_eip eip in
        let () = update_call_retn nodes call_retn in
        let () = update_malloc_free_protobuf nodes call_to_malloc call_to_free in
        (eip,bbs,func.name);;
    
    let rec remove_loop_time timeout func call_to_malloc call_to_free number_unloop (*old_h*) =
        if (number_unloop==0) then parse_protobuf_number func call_to_malloc call_to_free 0
        else
          try
            let _ = Unix.alarm timeout in
            parse_protobuf_number func call_to_malloc call_to_free number_unloop;
          with Timeout_unloop -> 
            let () = func.number_unlooping <- Int64.of_int (number_unloop-1) in 
            let () = Printf.printf "Timeout ! %s \n" func.name in 
            let () = flush Pervasives.stdout in 
            remove_loop_time timeout func call_to_malloc call_to_free (max 0 (number_unloop-1)) 
    
    let parse_protobuf func call_to_malloc call_to_free = 
            let number_unloop=Ir_v.parse_func_protobuf_number_unloop func in
            if (number_unloop==0) then  parse_protobuf_number func call_to_malloc call_to_free 0
            else
                let old_handler = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout_unloop)) in
                let ret = remove_loop_time 10 func call_to_malloc call_to_free number_unloop (*old_handler*) in
                let _ = Unix.alarm 0 in
                let _ = Sys.signal Sys.sigalrm old_handler in
                ret
   
    (*
     * Pretty print function
     *
     * *) 
    let pp_type_node t=
        (if ((land) t type_NODE_NORMAL>0) then "Normal " else "")^
        (if ((land) t type_NODE_MALLOC>0) then "Malloc " else "")^
        (if ((land) t type_NODE_FREE>0) then "Free " else "")^
        (if ((land) t type_NODE_CALL>0) then "Call " else "")^
        (if ((land) t type_NODE_RETN>0) then "Retn " else "")^
        (if ((land) t type_NODE_ENTRY>0) then "Entry " else "")^
        (if ((land) t type_NODE_NOT_LOAD>0) then "Not load " else "");;
    
    let pp_nodes_value n =
        let rec pp_nodes_values_rec n l =
            match n with 
            | [] -> l
            | hd::tl -> pp_nodes_values_rec tl ((Printf.sprintf "%x:%d " hd.addr hd.unloop )^(Ir_v.print_stmt hd.stmt)^(Printf.sprintf " type %s" (pp_type_node hd.type_node))^" : \n"^(Absenv_v.pp_absenvs hd.vsa)^(Printf.sprintf "Ha : %s \nHf : %s\n\n" (Absenv_v.pp_he hd.ha) (Absenv_v.pp_he hd.hf) )^l) 
        in pp_nodes_values_rec n "";;
    
    let pp_nodes_value_unloop n =
        let rec pp_nodes_values_rec n l =
            match n with 
            | [] -> l
            | (hd,unloop)::tl -> pp_nodes_values_rec tl ((Printf.sprintf "%x:%d " hd.addr unloop )^(Ir_v.print_stmt hd.stmt)^(Printf.sprintf " type %s" (pp_type_node hd.type_node))^" : \n"^(Absenv_v.pp_absenvs hd.vsa)^(Printf.sprintf "Ha : %s Hf : %s\n\n" (Absenv_v.pp_he hd.ha) (Absenv_v.pp_he hd.hf) )^l) 
        in pp_nodes_values_rec n "";;

    (* counter of chunk variable *)    
    let number_chunk=ref 0;;
    
    let init_value b state func_name=
        let _ = b.is_done<-false in
        let rec init_value_rec nodes =
        match nodes with
        | [] -> ()
        | hd::tl -> 
            let () = Absenv_v.clean_vsa hd.vsa in
            let () = hd.vsa<-[] in
            let () = hd.ha<-[] in 
            let () = hd.hf<-[] in
            (
                match hd.type_node with
                | _ when ((land) hd.type_node type_NODE_ENTRY)>0 
                    -> hd.init<-Absenv_v.init_first 
                | _ when ((land) hd.type_node type_NODE_MALLOC)>0 
                    -> 
                    let new_state = ((hd.addr,hd.unloop),func_name,(!current_call))::state in
                    let () = hd.init<-(Absenv_v.init_malloc ( !number_chunk) new_state ) in
                    let () = hd.ha<-[Absenv_v.init_chunk !number_chunk 0 new_state]  in
                    number_chunk:=!number_chunk+1;
                | _ -> ()
            );
            init_value_rec tl 
        in init_value_rec b.nodes;;
    
    (** Value analysis **)
    
    (* DO NOT USE THIS FUNCTION IF YOU HAVE LOOP, or be ready to take a looong coffee :) *)
    
   
    (* Functions useless for now *) 
(*    let (bb_to_save:(string * bb list) list ref) = ref [];;
    
    let max_number_bb = 500;;
    
    let save_log file log =
         let channel = open_out file in
         let () = output_string channel log in
         close_out channel;;
    
    let save_values file func_bbs =
        let channel = open_out file in
        let () = Marshal.to_channel channel func_bbs [Marshal.Closures] in
        close_out channel ;;
    
    let save_values_block file  bb = (*save_values   ;;*)
        let _ = bb_to_save:=(file,bb)::!bb_to_save in
        if(List.length(!bb_to_save)>max_number_bb) 
            then
            let () = List.iter (fun x -> let (f,b)=x in save_values f b) !bb_to_save in
            bb_to_save:=[] ;;
    
    let save_values_end file bb = (*save_values ;;*)
        let () = bb_to_save:=(file,bb)::!bb_to_save in
        let () = Printf.printf "Test\n" in
        List.iter (fun x -> let (f,b)=x in let _ = Printf.printf "%s" f in save_values f b) !bb_to_save;;
    
    let read_values file =
        let channel = open_in file in
        let func_bbs_poly = Marshal.from_channel channel in
        let func_bbs = (func_bbs_poly: bb list ) in
        let _ = close_in channel in
        Printf.sprintf "%s\n" (pp_nodes_value_unloop (List.concat (List.map (fun x -> List.map (fun y -> (y,x.unloop)) x.nodes ) func_bbs)));;
  *)
 
    (* 
     * Scoring function, useless for now 
     * 
     * *) 

(*    let ht_score= Hashtbl.create 2000;; (* If value = true, the func used the heap *)
    
    let number_score_true ()= Hashtbl.fold (fun x y z -> match y with 
                                                       | true -> z+1
                                                       | false -> z) ht_score 0;;
    
    let is_calling_heap n = 
        match n.type_node with
        | _ when ((land) n.type_node type_NODE_MALLOC)>0 -> true
        | _ when ((land) n.type_node type_NODE_FREE)>0 -> true
        | _ -> false;;
    
    let score_heap_use bbs func_name score_child=
        let nodes=List.concat (List.map (fun x -> x.nodes) bbs) in
            let score_call_heap = (List.fold_left (fun x y -> (||) x (is_calling_heap y)) false (List.concat (List.map (fun x -> x.nodes) bbs))) in
            let score_func = (List.fold_left (fun x y -> (||) x  (Ir_v.score_heap_use (y.stmt,y.vsa))) false nodes) in  
            let score=(||) score_func ((||) score_child score_call_heap ) in
            try
               let _ =  Hashtbl.replace ht_score func_name ((||) (Hashtbl.find ht_score func_name) score) in
               let _ = Printf.printf "Score of %s %B child %B all %B \n" func_name score_func score_child score in
               Hashtbl.find ht_score func_name
            with
                Not_found -> 
                    let _ = Hashtbl.add ht_score func_name score in
                    let _ = Printf.printf "Score of %s %B child %B all %B \n" func_name score_func score_child score in
                    let _ = Printf.printf "Number of score %d Number of true %d\n" (Hashtbl.length ht_score) (number_score_true()) in
                    Hashtbl.find ht_score func_name;;
    
    (* If score= false, not re-analyse*)
    let test_score indice= 
        try  
        (
            if((Hashtbl.find ht_score indice))  then
            (
                let _ = Printf.printf "test score %s -> false \n" indice in
                false;
            )
            else
            (
                let _ = Printf.printf "test score %s -> true \n" indice in
                true;
            )
        )
        with
            Not_found -> 
            (
                let _ = Printf.printf "test score %s -> false not found \n" indice in
                false
            );;

    *)
   
    let score_heap_use bbs func_name score_child = false ;; (* Useless for now *)
 
    (* Debug function *)
    let print_backtrack ((addr,it),name,n) = Printf.sprintf "0x%x:%d:%s" addr it name;;
    let print_time()= Printf.sprintf "%d:%d:%d:%d" ((int_of_float (Sys.time()*.100.))/(60*60*60))  ((mod) ((int_of_float (Sys.time()*.100.))/(60*60)) 60)  ((mod) ((int_of_float (Sys.time()*.100.))/60) 60 ) ((mod) (int_of_float (Sys.time()*.100.)) 60);;
   
    (** Uaf structure manipulation **)
 
    let add_uaf c state =
        let filter_list l1 l2 =
            let l1_minus_l2 =
            List.fold_left (
                fun x y -> 
                 if (List.mem y l2 ) then x
                 else y::x
                ) [] l1
            in
            l1_minus_l2@l2
        in
        let c_alloc,c_free = Absenv_v.get_chunk_states c in
        let key = Absenv_v.get_chunk_key c,c_free in
        let a,b = key in
        try
            let alloc,use=Hashtbl.find sg_uaf key in
            let use = filter_list use state in
            Hashtbl.replace sg_uaf key (alloc,use)
        with
            Not_found -> Hashtbl.add sg_uaf key (c_alloc,state)
     
    let check_uaf bbs backtrack addr=
        let nodes=List.concat (List.map (fun x -> x.nodes) bbs) in
        let uaf_result=List.map Ir_v.check_uaf (List.map (fun x -> (x.stmt,x.vsa,x.hf,(x.addr,x.unloop))) nodes) in
        if (List.length uaf_result)>0 
        then
            List.iter (
                fun x-> match x with
                    | None -> ()
                    | Some (stmt,chunks,addr) ->
                        let _,b,_ = (List.hd backtrack) in
                        let state = (addr,b,!current_call)::backtrack in
                        let _ = List.iter (fun c -> add_uaf c [state]) chunks in
                        Printf.printf "Uaf find :%s\n" ((let a,it = addr in Printf.sprintf "%x:%d " a it )^(Ir_v.print_stmt stmt)^(Absenv_v.pp_he chunks) )
            ) uaf_result;
       if (List.exists (
            fun x -> match x with
            | None -> false
            | Some x -> true
          ) uaf_result) 
        then Printf.printf "Uaf find in %x Backtrack %s \n ###################################################################\n" addr (String.concat " " (List.map print_backtrack backtrack )) ;;
    
    let find_func_name func_name list_func list_malloc list_free =
        let func =(List.find (fun (x:Program_piqi.function_) -> x.name = func_name) list_func) in 
        parse_protobuf func list_malloc list_free
    
    let find_func_eip func_eip list_func list_malloc list_free=
        let func = List.find (fun (x:Program_piqi.function_) -> ( ((Int64.to_int x.eip)/0x100) = func_eip)) list_func in
        parse_protobuf func list_malloc list_free
    
    (* If you ignore a call, put TOP in eax *) 
    let ignore_call vsa n state = Absenv_v.set_value_string vsa "eax" (Absenv_v.top_value()) 
   
    (* Restore the previous stack frame when something is wrong *) 
    let restore_stack_frame prev_vsa vsa = 
                let prev_esp = Absenv_v.get_value_string prev_vsa "esp" in
                let prev_ebp = Absenv_v.get_value_string prev_vsa "ebp" in
                let vsa = Absenv_v.set_value_string vsa "esp" prev_esp in
                Absenv_v.set_value_string vsa "ebp" prev_ebp

    let visit_before bb = ()
    
    let visit_after bb = ()
    
    let rec value_analysis func list_funcs list_malloc list_free backtrack dir_output verbose show_values show_call show_free details_values  =
        let score_childs=ref false in
        let rec merge_father fathers m=
            match fathers with
                | [] -> m
                | hd::tl -> merge_father tl (Absenv_v.merge hd.vsa m)
        in
        let rec merge_fathers_heap fathers ha hf=
            match fathers with
                | [] -> (ha,hf)
                | hd::tl -> merge_fathers_heap tl (Absenv_v.merge_he hd.ha ha) (Absenv_v.merge_he hd.hf hf)
        in
        let (func_eip,func_bbs,func_name)=func in
        let rec value_analysis_nodes_rec n fathers bb_ori=
           
             (* Put init values *)
            let _ = n.vsa<-Absenv_v.update n.init (merge_father fathers []) in
            (* Merge values from fathers *)
            let (ha,hf) = merge_fathers_heap fathers n.ha n.hf in
            (* Merge chunk values *)
            let _ = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
            let () = n.hf<-hf in
            let _ =
                if(show_values) 
                    then
                    let _ = Printf.printf "Func transfer node %s\n %s" func_name (pp_nodes_value [n]) in
                    flush Pervasives.stdout 
            in
            if ((land) n.type_node type_NODE_FREE)>0 then
                let () = if(verbose) then Printf.printf "Call Free %x %s | %s \n" n.addr func_name (String.concat " " (List.map print_backtrack backtrack )) in
                try 
                    let _ =  n.vsa <- Absenv_v.restore_esp n.vsa in
                    let val_esp=Absenv_v.get_value_string n.vsa "esp" in
                    let names=Absenv_v.values_to_names val_esp in
                    let vals=List.map (fun x -> Absenv_v.get_value n.vsa x) names in
                    let vals_filter=Absenv_v.filter_values  vals in
                    try 
                        let df = Absenv_v.check_df n.hf vals_filter in
                        match df with
                        | [] ->     
                            let (ha,hf)=Absenv_v.free n.ha n.hf vals_filter (((n.addr,n.unloop),func_name,!current_call)::backtrack) show_free  in
                            let _ = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                            n.hf<-hf
                        | _ -> 
                            List.iter (
                                fun c -> 
                                  add_uaf c [(((n.addr,n.unloop),"DF "^func_name,(!current_call))::backtrack)]
                            ) df                 
                    with
                        Not_found -> 
                            let (ha,hf)=Absenv_v.free n.ha n.hf vals_filter (((n.addr,n.unloop),func_name,!current_call)::backtrack) show_free in
                            let _ = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                            n.hf<-hf
                with 
                    AbsEnv.ERROR ->
                        begin   
                             if (verbose) then Printf.printf "Error on free? \n" 
                        end
            else if (((land) n.type_node type_NODE_CALL)>0 && ((land) n.type_node type_NODE_MALLOC)>0)  
                then
                n.vsa <- Absenv_v.restore_esp n.vsa 
            else if ((land) n.type_node type_NODE_CALL)>0 then
                let addr_call=Ir_v.get_value_jump n.stmt in
                match addr_call with
                | None -> (* if unknow jump *) 
                    let vsa = Absenv_v.restore_esp n.vsa in
                    n.vsa <- ignore_call vsa number_chunk (((n.addr,n.unloop),func_name,!current_call)::backtrack)
                | Some a -> 
                    let is_stub, vsa,ha,hf=Stubfunc_v.stub a n.vsa n.ha n.hf number_chunk (n.addr,n.unloop) func_name (!current_call) backtrack  in
                    if is_stub 
                        then 
                            let _ = n.vsa<-vsa in
                            let _ = n.ha<-ha in
                            n.hf<-hf
                    else
                        try
                            let (func_eip_ori,func_bbs_ori,func_name)= find_func_eip a list_funcs list_malloc list_free in
                            if (List.exists (fun (addr,x,n) -> x=func_name) backtrack) 
                                then
                                let () = if (verbose) then Printf.printf "Rec %x %s | %s \n" n.addr func_name (String.concat " " (List.map print_backtrack backtrack ))  in
                                let _ =flush Pervasives.stdout in
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa number_chunk (((n.addr,n.unloop),func_name,!current_call)::backtrack)
                            else
                                let (func_eip,func_bbs)=(func_eip_ori,func_bbs_ori) in
                                let number_call_prev = (!current_call) in
                                let () = 
                                    if(details_values) 
                                    then 
                                        let () = number_call:=(!number_call+1) in
                                        let () = saved_call := (bb_ori,func_eip,(!current_call),(!number_call))::(!saved_call) in 
                                        current_call := (!number_call)
                                in
                                let _ = List.iter (fun x -> init_value x (((n.addr,n.unloop),func_name,!current_call)::backtrack) func_name) func_bbs in
                                let _ = (List.find (fun x -> x.addr==func_eip.addr_bb) func_eip.nodes).init<-n.vsa in
                                let _ = (List.find (fun x -> x.addr==func_eip.addr_bb) func_eip.nodes).ha<-n.ha in
                                let _ = (List.find (fun x -> x.addr==func_eip.addr_bb) func_eip.nodes).hf<-n.hf in
                                try
                                    let () = if(show_call) then Printf.printf "Call %d %d (bb %x) 0x%x:%d %s | %s\n" (!current_call) (!number_call) (bb_ori.addr_bb) n.addr bb_ori.unloop func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                    let _ = flush Pervasives.stdout in
                                    let (vsa,ha,hf,score)=value_analysis (func_eip,func_bbs,func_name)(*next_func*) list_funcs list_malloc list_free (((n.addr,n.unloop),func_name,!current_call)::backtrack) dir_output verbose show_values show_call show_free details_values in
                                    let () = if(verbose) then Printf.printf "End call %d %x:%d %s | %s\n"  (!current_call) n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                    let _ = check_uaf func_bbs (((n.addr,n.unloop),func_name,!current_call)::backtrack) n.addr in 
                                    let () = if(details_values) then current_call:=number_call_prev in
                                    let _ = score_childs:=(||) (!score_childs) score in
                                    try
                                        let _ = n.vsa<-Absenv_v.filter_esp_ebp vsa verbose in
                                        let _ = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                        n.hf<-hf
                                    with
                                        | AbsEnv.ERROR -> 
                                            let _ = if (verbose) then 
                                                let _ = Printf.printf "Func transfer node Error Filter esp / ebp \n %s" (pp_nodes_value [n]) in
                                                let _ = Printf.printf "\n---\n" in
                                                let _ = Printf.printf "%s\n" (Absenv_v.pp_absenvs vsa) in 
                                                flush Pervasives.stdout 
                                            in
                                            let _ = n.vsa <- restore_stack_frame n.vsa vsa in
                                            let _ = n.vsa <- Absenv_v.restore_esp n.vsa in
                                            let _ = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                            n.hf<-hf
                                        |_ -> Printf.printf "WTF \n";
                                with
                                    | NOT_RET (vsa,ha,hf,score)  ->
                                        let _ = Printf.printf "End call (NOT RET) %x:%d %s | %s\n" n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                        let _ = check_uaf func_bbs (((n.addr,n.unloop),func_name,!current_call)::backtrack) n.addr in
                                        let () = if(details_values) then current_call:=number_call_prev in
                                        let _ = score_childs:=(||) (!score_childs) score in
                                        let _ = if (verbose) then 
                                            let _ = Printf.printf  "Func transfer node Not ret \n %s" (pp_nodes_value [n]) in
                                            let _ = Printf.printf "\n---\n" in
                                            Printf.printf "%s\n" (Absenv_v.pp_absenvs vsa) 
                                        in
                                        let _ = flush Pervasives.stdout  in
                                        let _ = n.vsa <- restore_stack_frame n.vsa vsa in
                                        let _ = n.vsa <- Absenv_v.restore_esp n.vsa in
                                        let _ = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                        n.hf<-hf;                                               
                                   | NOT_RET_NOT_LEAF ->
                                        let () = if (verbose) then Printf.printf "End call (NOT RET NOT LEAF) %x:%d %s | %s\n" n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                        let _ = check_uaf func_bbs (((n.addr,n.unloop),func_name,!current_call)::backtrack) n.addr in
                                        let () = if(details_values) then current_call:=number_call_prev in
                                        let _ = n.vsa <- restore_stack_frame n.vsa vsa in
                                        let _ = n.vsa <- Absenv_v.restore_esp n.vsa in
                                        let _ = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                        n.hf<-hf;  
                        with
                            Not_found ->
                                let () = if(verbose) then Printf.printf "Not found 0x%x\n" a in
(*                                let vsa = restore_stack_frame n.vsa vsa in*)
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa number_chunk (((n.addr,n.unloop),func_name,!current_call)::backtrack)
                else
                    n.vsa<-Ir_v.function_transfer n.stmt n.vsa n.hf number_chunk (n.addr,n.unloop) func_name (!current_call) backtrack; (* TODO should be number_init *)
        in
            let rec value_analysis_rec bb=
                if( (not bb.is_done) && (List.for_all (fun x -> x.is_done) bb.fathers)) 
                    then
                    let () = visit_before bb in
                    let fathers_filter = List.filter (fun x -> (List.length x.nodes)>0) bb.fathers in
                    let fathers=ref ((List.map (fun x -> List.nth x.nodes ((List.length x.nodes)-1)) fathers_filter )) in
                    let () = List.iter (
                        fun x -> 
                            let _ =  value_analysis_nodes_rec x (!fathers) bb  in
                            fathers:=[x];
                        ) bb.nodes in
                    let _ = bb.is_done<-true in
                    let () = 
                        if(details_values)
                            then
                            saved_values:=(bb,(!current_call))::(!saved_values)
                    in
                    let () = visit_after bb in
                    List.iter value_analysis_rec bb.sons
        in
        let _ = value_analysis_rec func_eip in
        let retn_node=List.filter (fun x -> ((land) x.type_node type_NODE_RETN)>0) (List.concat (List.map (fun x -> x.nodes) func_bbs)) in
        match retn_node with
            | [] ->     
                let leaf_bbs=List.filter (fun x -> (List.length x.sons)==0) func_bbs in
                let leaf_bbs_filter=List.filter (fun x -> (List.length x.nodes)>0) leaf_bbs in
                let leaf_node=List.map (fun x -> (List.nth x.nodes ((List.length x.nodes)-1))) leaf_bbs_filter in
                begin
                    match leaf_node with
                        | [] -> raise NOT_RET_NOT_LEAF
                        | [hd] -> (hd.vsa,hd.ha,hd.hf,score_heap_use func_bbs func_name (!score_childs))
                        | hd::tl -> raise (NOT_RET ((List.fold_left (fun x y-> Absenv_v.merge x y.vsa) hd.vsa tl),(List.fold_left (fun x y ->Absenv_v.merge_he x y.ha) hd.ha tl),( List.fold_left (fun x y ->Absenv_v.merge_he x y.hf) hd.hf tl ),score_heap_use func_bbs func_name (!score_childs)))
               end
            | [hd] ->
                (hd.vsa,hd.ha,hd.hf,score_heap_use func_bbs func_name (!score_childs))
            | hd::tl ->
                ((List.fold_left (fun x y-> Absenv_v.merge x y.vsa) hd.vsa tl),(List.fold_left (fun x y ->Absenv_v.merge_he x y.ha) hd.ha tl),( List.fold_left (fun x y ->Absenv_v.merge_he x y.hf) hd.hf tl ),score_heap_use func_bbs func_name (!score_childs))
    
    let rec explore_graph func list_funcs backtrack ref_count verbose show_call print_graph =
        let (func_eip,func_bbs,func_name)=func in
        let rec explore_nodes_rec n fathers bb_ori=
            if ((land) n.type_node type_NODE_FREE)>0 then ()
            else if ((land) n.type_node type_NODE_CALL)>0 
                then
                let addr_call=Ir_v.get_value_jump n.stmt in
                match addr_call with
                    | None -> ()
                    | Some a -> 
                        try
                            let (func_eip_ori,func_bbs_ori,func_name)= find_func_eip a list_funcs [] [] in
                                if (List.exists (fun x -> x=func_name) backtrack) then ()
                                else
                                   let (func_eip,func_bbs)=(func_eip_ori,func_bbs_ori) in
                                   let () = ref_count := (!ref_count)+1 in
                                   let  () = if (show_call) 
                                        then
                                        Printf.printf "call %x:%d %s | %s\n" n.addr bb_ori.unloop  func_name (List.fold_left (fun x y -> x^" "^y) "" backtrack) 
                                    in
                                let number_call_prev = (!current_call) in
                                let () = 
                                    if(print_graph) 
                                    then 
                                        let () = number_call:=(!number_call+1) in
                                        let () = saved_call := (bb_ori,func_eip,(!current_call),(!number_call))::(!saved_call) in 
                                        current_call := (!number_call)
                                in
                                let () = explore_graph (func_eip,func_bbs,func_name) list_funcs (func_name::backtrack) ref_count verbose show_call print_graph in
                                if(print_graph) then current_call:=number_call_prev
                        with
                            Not_found -> ()
        in
        let rec explore_rec bb=
            if( (not bb.is_done) && (List.for_all (fun x -> x.is_done) bb.fathers)) then
            let fathers_filter = List.filter (fun x -> (List.length x.nodes)>0) bb.fathers in
            let fathers=ref ((List.map (fun x -> List.nth x.nodes ((List.length x.nodes)-1)) fathers_filter )) in
            let () = List.iter (
                fun x ->
                    let _ =  explore_nodes_rec x (!fathers) bb  in
                    fathers:=[x]
                ) bb.nodes in
            let _ = bb.is_done<-true in
            let () = if(print_graph) then saved_values:=(bb,(!current_call))::(!saved_values) in
            List.iter explore_rec bb.sons 
        in
        explore_rec func_eip    
    
    let launch_supercallgraph_analysis func_name list_funcs list_malloc list_free dir_output verbose show_call print_graph =
        let count = ref 10 in
        try 
            let (eip,bbs,name) = find_func_name func_name list_funcs list_malloc list_free in
            let _ = List.iter (fun x -> init_value x [((eip.addr_bb,eip.unloop),func_name,!current_call)] func_name) bbs in
            let () = explore_graph (eip,bbs,name)  list_funcs ([""]) count verbose show_call print_graph in
            let () = Printf.printf "Number of func from %s : %d\n" func_name (!count) in
            let _ = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in
            (!count)
        with
            | Not_found -> 
                let () = Printf.printf "Func %s : error (func not found)\n" func_name in
                let () = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in
                (!count)
            | NOT_RET (vsa,ha,hf,score) -> 
                let () = if(verbose) then Printf.printf "Not ret\n" in
                let () = Printf.printf "Number of func from %s %d\n" func_name (!count) in
                let () = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in
                (!count) 
            | NOT_RET_NOT_LEAF -> 
                let () = if(verbose) then Printf.printf "Not ret\n" in
                let () = Printf.printf "Number of func %s %d\n" func_name (!count) in
                let () = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in
                (!count) 

    let launch_value_analysis func_name list_funcs list_malloc list_free dir_output verbose show_values show_call show_free details_values =
        try 
            let (eip,bbs,name) = find_func_name func_name list_funcs list_malloc list_free in
            let _ = List.iter (fun x -> init_value x [((eip.addr_bb,eip.unloop),func_name,!current_call)] func_name) bbs  in
            let _ = value_analysis (eip,bbs,name)  list_funcs list_malloc list_free ([(eip.addr_bb,0),name,0]) dir_output verbose show_values show_call show_free details_values in
            let _ = check_uaf bbs [(eip.addr_bb,0),name,!current_call] (0) in
            let () = print_sg dir_output in
            if(details_values)
                then print_values dir_output (!saved_values) (!saved_call) 
        with
            | Not_found -> Printf.printf "Func %s : error (not found)\n" func_name
            | NOT_RET (vsa,ha,hf,score) -> ()
            | NOT_RET_NOT_LEAF -> ()

end;;

