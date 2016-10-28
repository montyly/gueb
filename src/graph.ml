open Absenvgenerique
open Ir 
open Stubfunc
open Program_piqi
open Uafgenerique

module My_Graph (Absenv_v : AbsEnvGenerique) (Ir_a : IR) (Stubfunc_a : Stubfunc) (Uaf_a : UafGenerique ) =
struct

    exception NOT_RET of (Absenv_v.absenv)*bool;;
    exception NOT_RET_NOT_LEAF;;
    exception Timeout_unloop;;
    exception MAX_EXPLORE;;
    exception MAX_INS;;

    module Ir_v = Ir_a (Absenv_v)
    module Stubfunc_v = Stubfunc_a (Absenv_v)
    module Uaf_v = Uaf_a (Absenv_v)
    type node =
    {
        addr : int ;
        stmt : Ir_v.ir_stmt;
        mutable type_node : int;
        mutable init : Absenv_v.absenv;
        mutable vsa : Absenv_v.absenv;
    };;
    type bb = {
        uniq_id : int ;
        addr_bb : int;
        mutable sons : bb list;
        mutable sons_kosaraju : bb list; (* Dirty hack -> sons are erase during kosaraju*)
        mutable fathers : bb list;
        mutable nodes : node list;
        mutable fathers_kosaraju : bb list; (* Dirty hack -> sons are erase during kosaraju*)
        mutable unloop : int; (* use when copy during unrolling node*)
        mutable is_done : bool; (*value analysis done *)
        mutable number_sons : int; (*used to know if is leaf *)
    };;

    let type_NODE_NORMAL   =       0b0;;
    let type_NODE_MALLOC   =       0b1;;
    let type_NODE_FREE     =      0b10;;
    let type_NODE_CALL     =     0b100;;
    let type_NODE_RETN     =    0b1000;;
    let type_NODE_ENTRY    =  0b100000;;
    let type_NODE_NOT_LOAD = 0b1000000;;

    type subgraph_node_type =
        | NODE_OUT
        | NODE_ALLOC
        | NODE_FREE
        | NODE_USE
        | NODE_DF
        | NODE_EIP
        | NODE_EIP_ALLOC
        | NODE_ALLOC_FREE
        | NODE_FREE_USE

    let _pp_site_type s = match s with
        | Uafgenerique.SITE_NORMAL -> "normal"
        | Uafgenerique.SITE_ALLOC -> "alloc"
        | Uafgenerique.SITE_FREE -> "free"
        | Uafgenerique.SITE_USE -> "use"
        | Uafgenerique.SITE_DF -> "df"      

    let _pp_subgraph_type s = match s with
        | NODE_OUT -> "out"
        | NODE_ALLOC -> "alloc"
        | NODE_FREE -> "free"
        | NODE_USE -> "use"
        | NODE_DF -> "df" 
        | NODE_EIP -> "eip" 
        | NODE_EIP_ALLOC -> "eip_alloc"
        | NODE_ALLOC_FREE -> "alloc_free"
        | NODE_FREE_USE -> "free_use"

 (*   let _pp_event s = Printf.sprintf "%x" s (*(cs,_t) = String.concat " " (List.map (fun x -> Gueb_type.pp_call_string x) cs)*)*)

    let _pp_event l = String.concat " " (List.map (fun (s,t) -> Printf.sprintf "%s:%s" (_pp_site_type t) (Uafgenerique.pp_site s)) l)
(* Printf.sprintf "%x" s (*(cs,_t) = String.concat " " (List.map (fun x -> Gueb_type.pp_call_string x) cs)*)*)
        

    let site_to_subgraph_type t =
        match t with
        | Uafgenerique.SITE_NORMAL -> NODE_OUT
        | Uafgenerique.SITE_ALLOC -> NODE_ALLOC
        | Uafgenerique.SITE_FREE -> NODE_FREE
        | Uafgenerique.SITE_USE -> NODE_USE
        | Uafgenerique.SITE_DF -> NODE_DF
        
    let decrease_subgraph_type t = match t with
        | NODE_OUT -> NODE_OUT
        | NODE_ALLOC -> NODE_EIP_ALLOC
        | NODE_FREE -> NODE_ALLOC_FREE
        | NODE_USE | NODE_DF -> NODE_FREE_USE
        | NODE_EIP -> NODE_EIP
        (* do not decrease inside states *)
        | NODE_EIP_ALLOC -> NODE_EIP_ALLOC 
        | NODE_ALLOC_FREE -> NODE_ALLOC_FREE 
        | NODE_FREE_USE -> NODE_FREE_USE

    let increase_subgraph_type t = match t with
        | NODE_ALLOC -> NODE_ALLOC_FREE
        | NODE_FREE -> NODE_FREE_USE
        | NODE_EIP -> NODE_EIP_ALLOC
        | NODE_USE -> NODE_FREE_USE
        | NODE_DF -> NODE_FREE_USE
        (* do not increase other states *)
        | NODE_OUT -> NODE_OUT
        | NODE_EIP_ALLOC -> NODE_EIP_ALLOC 
        | NODE_ALLOC_FREE -> NODE_ALLOC_FREE 
        | NODE_FREE_USE -> NODE_FREE_USE

    let number_bbs=ref 0

    let number_call = ref 0

    let current_call = ref 0
    
    (* (bb_ori,bb_it), bb_dst, ori_n, dst_n *) 
    let saved_call = ref [] 
    
    let call_stack = Stack.create () 
    let call_stack_tbl = Hashtbl.create 200
    
    (* bb_ori, bb_dst, ori_n, dst_n,name_ret_func *)     
    let saved_ret_call = ref [] 

    let irreducible = ref false    
    
    let depth_max = ref None
    
    let number_analyzed_func = ref 0

    let max_func = ref 400
    
    let max_ins = ref None

    let total_max_ins = ref None

    let number_analyzed_ins = ref 0

    let total_number_analyzed_ins = ref 0

    let set_irreducible_loop () = irreducible := true
    
    let set_depth d = depth_max := Some d

    let set_size d = max_func := d
    
    let set_max_ins d = max_ins := Some d

    let set_total_max_ins d = total_max_ins := Some d

    let is_sup_depth l = match (!depth_max) with        
                        | None -> false
                        | Some d -> (List.length l) > d


    let reach_number_ins () =
        match (!total_max_ins) with
        | None -> false
        | Some x -> (x < ((!total_number_analyzed_ins) + (!number_analyzed_ins)))

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
        | hd :: tl ->  let () =connect_bb bbs hd  in connect_bbs bbs tl ;;

    let rec update_type nodes addrs type_node=
        match addrs with
        | [] -> ()
        | tl::hd ->
                List.iter (fun x -> 
                        match x.addr with
                        | _ when x.addr=tl -> let () = x.type_node<-(lor) x.type_node type_node in  ()
                        | _ -> ()
                        ) nodes;
                update_type nodes hd type_node;;

    let update_call_retn nodes call_retn =
        let (call,retn)=call_retn in
        let () =update_type nodes call type_NODE_CALL in
        update_type nodes retn type_NODE_RETN;;


    let find_eip nodes eip = 
        try
            List.find (fun x -> x.addr_bb=eip) nodes 
        with
            Not_found -> let () = Printf.printf "Error, EIP not found\n" in exit 0;;

    let create_nodes arg =
        let (stmt,addr,_unloop)=arg in
        {addr=addr;stmt=stmt;type_node=type_NODE_NORMAL;init = Absenv_v.initAbsenEnv () ; vsa=Absenv_v.initAbsenEnv ()};;
   
    let create_bb addr =  
            let () = number_bbs:= (!number_bbs)+1 in
            {uniq_id= !number_bbs;addr_bb=addr;sons=[];sons_kosaraju=[];fathers=[];fathers_kosaraju=[];unloop=0;is_done=false;nodes=[];number_sons=0}
 
    let new_node node = {addr=node.addr;stmt=node.stmt; type_node=node.type_node;init=node.init;vsa=node.vsa;};;
   
    let new_bb bb unloop= 
        let () = number_bbs:=(!number_bbs)+1 in
        {uniq_id= !number_bbs;addr_bb=bb.addr_bb;sons=bb.sons;sons_kosaraju=bb.sons_kosaraju;fathers=bb.fathers;fathers_kosaraju=bb.fathers_kosaraju;unloop=unloop;is_done=false;nodes= [];number_sons=List.length (bb.sons)};;
    
    (** Function for loop manipulation **)
    
    let find_entry_father nodes=
        let fathers=(List.concat (List.map (fun x -> x.fathers) nodes)) 
           in List.filter (fun x -> List.for_all (fun y -> y.addr_bb<>x.addr_bb || x.unloop<>y.unloop) nodes) fathers ;;
    
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
        | [] -> (*Printf.printf "No entry\n" ;*) [head]
        | l ->  (*Printf.printf "Entry %d %d\n" (List.length l) (List.length nodes); List.iter (fun x -> Printf.printf "%x\n" x.addr_bb) nodes;*) l;;
    
    (** Kosaraju **)
    (* Filter son/father kosaraju *)
    let remove_on_one_node_son node addr unloop_number=
        node.sons_kosaraju<-List.filter (fun x -> x.addr_bb<>addr || (x.addr_bb==addr && x.unloop <> unloop_number) ) node.sons_kosaraju;;
    
    let remove_on_one_node_father node addr unloop_number=
        node.fathers_kosaraju<-List.filter (fun x -> x.addr_bb<>addr || (x.addr_bb==addr && x.unloop <> unloop_number) ) node.fathers_kosaraju;;
    
    (* Remove path kosaraju *)
    let remove_path stack node=
        let ()  = List.iter (fun x -> remove_on_one_node_father x node.addr_bb node.unloop) stack in
        List.filter (fun x -> x.addr_bb<>node.addr_bb || x.unloop<>node.unloop) stack;;
    
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
                 let () = List.iter (fun x -> List.iter (fun y -> remove_on_one_node_son y x.addr_bb x.unloop )  list_nodes ) leafs_clean in
                 create start_node ((leafs_clean)@stack)
          in create start_node [];;
    
    let create_strongly_connected stack=
        let rec create stack sc =
            match stack with 
            | [] -> sc
            | tl::_ ->
                let path=dfs_path tl in
                let new_stack = remove_path_stack stack path in
                create new_stack (path::sc)
        in create (List.rev stack) [];;
            
    
    (* Kosaraju algo *)
    let kosaraju start_node list_nodes=
        let stack = create_stack_dfs start_node list_nodes in
        create_strongly_connected stack;;
    
    (* Remove loop *)
    let remove_arc sc head =
        List.find_all (
            fun x -> 
                    if (List.exists (fun x -> x.addr_bb = head.addr_bb) x.sons)  
                        then 
                        let () = x.sons <- (List.find_all (fun x -> x.addr_bb <> head.addr_bb) x.sons) in
                        let () = head.fathers<-(List.find_all (fun y -> y.addr_bb <> x.addr_bb) head.fathers) in
                        true
                   else false
            ) sc ;;
    

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
                        if(n_x<>n_first) then fix n nodes_first (n_x-n_first)
                        else ()
                 ) list_nodes
    
    let copy_nodes list_nodes number_unloop_init =
        let rec copy_nodes_rec list_nodes number_unloop stack =
            let n_unloop=(number_unloop) in
            if number_unloop<=0 then
                let () = List.iter (fun x -> x.unloop <- x.unloop+n_unloop) list_nodes in
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
            let (_,nodes_n1) = List.find (fun (n1,_) -> n1=(n+1)) list_news_nodes in
            let entry_n1 = find_node_no_unloop entry nodes_n1 in
            let () = List.iter (fun x -> x.sons <- entry_n1::x.sons) leafs_n in
            let () = entry_n1.fathers <- leafs_n in
            nodes
        with
            Not_found -> nodes
    
    let expanse_loop list_nodes leafs number_unloop = 
        let new_list_nodes = copy_nodes list_nodes number_unloop in
        let new_list_nodes = List.rev (new_list_nodes) in
        let () = fix_sons_fathers new_list_nodes in
        let list_nodes = List.map (fun  x -> List.concat (List.map (fun (e,l) -> fix_entry_leaf x new_list_nodes e l ) leafs)) new_list_nodes in
        List.concat list_nodes
    
    let rec unroll head list_nodes number_unloop irreducible =
        let select_best_entry l = List.fold_left (fun x y -> if ( List.length x.fathers > List.length y.fathers) then x else y ) (List.hd l) (List.tl l) in
        let exist l = List.find_all (fun x -> List.exists (fun y -> y.addr_bb=x.addr_bb) list_nodes) l in
        let () = List.iter (fun x -> let () = x.sons_kosaraju<-(exist x.sons) in x.fathers_kosaraju<-(exist x.fathers)) list_nodes in
        let scs = kosaraju head list_nodes in
        let unroll_sc sc head = 
        begin
            if (List.length sc==1) then sc 
            else
            let all_entry_point = find_entry sc head in
            let entry_point = if(irreducible) then all_entry_point else [select_best_entry all_entry_point] in 
            let entry_arcs = List.map (fun x -> (x,remove_arc sc x)) entry_point in (* leafs is list of : entry_point -> nodes fathers*) 
            let sc = unroll (List.hd entry_point) sc number_unloop irreducible in
            let ret = expanse_loop sc entry_arcs number_unloop  in
            ret
        end
        in List.concat (List.map (fun x -> unroll_sc x head) scs) ;;
    
    let begin_eip b=
    try 
        let n=List.find (fun x -> x.addr==b.addr_bb) b.nodes (* TODO need beeter stuff for EIP... *)
        in n.type_node<-((lor) n.type_node type_NODE_ENTRY)
    with 
      Not_found -> Printf.printf "Eip not found ! \n"
    
    let find_nodes_from_addr list_addr list_nodes =List.map (fun x -> new_node x  ) (List.find_all (fun n -> List.exists (fun x -> x=n.addr) list_addr) list_nodes );;
   
    let parse_protobuf_no_unloop func =
        let (bbs,connexion_unfiltre,eip_addr,_,nodes,call_retn)=Ir_v.parse_func_protobuf func in
        let connexion=List.filter (fun (x,y) -> x<>y) connexion_unfiltre in (* TODO need to handle loop on himself ! *)
        let bb_nodes = List.map (fun x -> let (addr,list_nodes)=x in (create_bb addr,list_nodes)) bbs in
        let bbs_only=List.map (fun x-> let (a,_)=x in a)  bb_nodes in
        let bbs_connect= connect_bbs bbs_only connexion in
        let () = List.iter (fun x -> x.number_sons <- List.length (x.sons)) bbs_connect in
        let eip=find_eip bbs_connect eip_addr in
        let f addr l = 
            let (_,list_ret) = List.find (fun x -> let (a,_)=x in a.addr_bb==addr) l 
            in list_ret
        in
        let bbs_with_nodes_list=List.map (fun x -> (x,f x.addr_bb bb_nodes)) bbs_connect in
        let nodes_begin=(List.map create_nodes nodes) in
        let bbs=List.map (
            fun x-> 
                let (bb,list_nodes)=x in
                let () = bb.nodes<- (find_nodes_from_addr list_nodes nodes_begin) in bb
            ) bbs_with_nodes_list in
        let nodes=List.concat (List.map (fun x -> x.nodes) bbs) in
        let () = begin_eip eip in
        let () = update_call_retn nodes call_retn in
        let open Function_ in
        (eip,bbs,func.name);;
 

    let parse_protobuf_number func number_unloop  =
            let (bbs,connexion_unfiltre,eip_addr,_,nodes,call_retn)=Ir_v.parse_func_protobuf func in
            let connexion=List.filter (fun (x,y) -> x<>y) connexion_unfiltre in (* TODO need to handle loop on himself ! *)
            let bb_nodes = List.map (fun x -> let (addr,list_nodes)=x in (create_bb addr,list_nodes)) bbs in
            let bbs_only=List.map (fun x-> let (a,_)=x in a)  bb_nodes in
            let bbs_connect= connect_bbs bbs_only connexion in
            let () = List.iter (fun x -> x.number_sons <- List.length (x.sons)) bbs_connect in
            let eip=find_eip bbs_connect eip_addr in
            let bb_unloop= unroll eip bbs_connect number_unloop (!irreducible) in
            let f addr l = 
                let (_,list_ret) = List.find (fun x -> let (a,_)=x in a.addr_bb==addr) l 
                in list_ret
            in
            let bbs_with_nodes_list=List.map (fun x -> (x,f x.addr_bb bb_nodes)) bb_unloop in
            let nodes_begin=(List.map create_nodes nodes) in
            let bbs=List.map (
                fun x-> 
                    let (bb,list_nodes)=x in
                    let () = bb.nodes<- (find_nodes_from_addr list_nodes nodes_begin) in bb
                ) bbs_with_nodes_list in
            let nodes=List.concat (List.map (fun x -> x.nodes) bbs) in
            let () = begin_eip eip in
            let () = update_call_retn nodes call_retn in
            let open Function_ in
            (eip,bbs,func.name);;
    
    let rec remove_loop_time timeout func  number_unloop  =
        if (number_unloop==0) then parse_protobuf_number func  0
        else
          try
            let _ = Unix.alarm timeout in
            parse_protobuf_number func  number_unloop;
          with Timeout_unloop -> 
            let open Function_ in
            let () = func.number_unlooping <- Int64.of_int (number_unloop-1) in 
            let () = Printf.printf "Timeout ! %s \n" func.name in 
            let () = flush Pervasives.stdout in 
            remove_loop_time timeout func  (max 0 (number_unloop-1)) 
    
    let parse_protobuf func = 
            let number_unloop=Ir_v.parse_func_protobuf_number_unloop func in
            let ret = 
                if (number_unloop==0) then  parse_protobuf_number func  0
            else
                let old_handler = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout_unloop)) in
                let ret = remove_loop_time 10 func  number_unloop (*old_handler*) in
                let _ = Unix.alarm 0 in
                let _ = Sys.signal Sys.sigalrm old_handler in
                ret
            in
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
    
    let pp_nodes_value n val_unloop  =
        let rec pp_nodes_values_rec n l =
            match n with 
            | [] -> l
            | hd::tl -> pp_nodes_values_rec tl ((Printf.sprintf "%x:%d " hd.addr val_unloop )^(Ir_v.print_stmt hd.stmt)^(Printf.sprintf " type %s" (pp_type_node hd.type_node))^" : \n"^(Absenv_v.pp_absenvs hd.vsa)(*^(Printf.sprintf "Ha : %s \nHf : %s\n\n" (Absenv_v.pp_ha vsa) (Absenv_v.pp_hf vsa)*) ^l) 
        in pp_nodes_values_rec n "";;
    
    let init_value b =
        let () = b.is_done<-false in
        let rec init_value_rec nodes =
        match nodes with
        | [] -> ()
        | hd::tl -> 
            let () = Absenv_v.clean_vsa hd.vsa in
            let () = hd.vsa<- Absenv_v.initAbsenEnv ()in
            (
                match hd.type_node with
                | _ when ((land) hd.type_node type_NODE_ENTRY)>0 
                    -> hd.init<-Absenv_v.init_first 
                | _ -> ()
            );
            init_value_rec tl 
        in init_value_rec b.nodes;;
    
    let score_heap_use _bbs _func_name _score_child = false ;; (* Useless for now *)
 
    let print_backtrack ((addr,it),name,_n) = Printf.sprintf "0x%x:%d:%s" addr it name;;
   
    (** Uaf structure manipulation **)

    let add_uaf ?(t=Uafgenerique.SITE_USE) c state =
        Uaf_v.add_uaf ~t:t c state
     
    let check_uaf bbs backtrack verbose =
        List.iter (fun (nodes,unloop) ->
         let uaf_result=List.map Ir_v.check_uaf (List.map (fun x -> (x.stmt,x.vsa,(x.addr,unloop))) nodes) in
         if (List.length uaf_result)>0 
         then
             List.iter (
                 fun x-> match x with
                     | None -> ()
                     | Some (stmt,chunks,addr) ->
                         let _,b,_ = (List.hd backtrack) in
                         let state = (addr,b,!current_call)::backtrack in
                         List.iter (fun c -> add_uaf c [state]) chunks ;
                         if(verbose) then Printf.printf "Uaf find :%s\n" ((let a,it = addr in Printf.sprintf "%x:%d " a it )^(Ir_v.print_stmt stmt)^(Absenv_v.pp_he chunks) );
             ) uaf_result
        ) (List.map (fun x -> (x.nodes,x.unloop) ) bbs )
    
    let find_func_name func_name list_func  =
        (* Dirty hack, we kept DF in name for pretty print, so we need to remove it *)
        let func_name = try
                if (String.sub func_name 0 3 = "DF ") then String.sub func_name 3 ((String.length func_name)-3)
                    else func_name
                with _ -> func_name
        in
        let open Function_ in
        let func =(List.find (fun (x:Program_piqi.function_) -> x.name = func_name) list_func) in 
        parse_protobuf func 
    
    let find_func_name_no_unloop func_name list_func  =
        (* Dirty hack, we kept DF in name for pretty print, so we need to remove it *)
        let func_name = try
                if ((String.sub func_name 0 3) = "DF ") then String.sub func_name 3 ((String.length func_name)-3)
                    else func_name
                with _ -> func_name
        in
        let open Function_ in
        let func =(List.find (fun (x:Program_piqi.function_) -> x.name = func_name) list_func) in 
        parse_protobuf_no_unloop func 

    let find_func_eip func_eip list_func =
        let open Function_ in
        let func = List.find (fun (x:Program_piqi.function_) -> ( ((Int64.to_int x.addr_to_call)/0x100) = func_eip)) list_func in   
        parse_protobuf func
    
    let find_func_eip_no_unloop func_eip list_func =
        let open Function_ in
        let func = List.find (fun (x:Program_piqi.function_) -> ( ((Int64.to_int x.addr_to_call)/0x100)  = func_eip)) list_func in   
        parse_protobuf_no_unloop func 

    (* If you ignore a call, put TOP in eax *) 
    let ignore_call vsa = Absenv_v.set_value_string vsa "eax" (Absenv_v.top_value()) 
   
    (* Restore the previous stack frame when something is wrong *) 
    let restore_stack_frame prev_vsa vsa = 
                let prev_esp = Absenv_v.get_value_string prev_vsa "esp" in
                let prev_ebp = Absenv_v.get_value_string prev_vsa "ebp" in
                let vsa = Absenv_v.set_value_string vsa "esp" prev_esp in
                let vsa = Absenv_v.set_value_string vsa "ebp" prev_ebp in
                Absenv_v.filter_he vsa

    let stack_to_list s =
    if (Stack.is_empty s) then []
    else 
        let l = ref [] in
        let () = Stack.iter (fun x -> l := x::!l) s in
        !l

    let incr_number_ins () = number_analyzed_ins := (!number_analyzed_ins) + 1

    let is_max_ins () = match !max_ins with
        | None -> false
        | Some d -> d < (!number_analyzed_ins)

    (** Value analysis **)
    (* DO NOT USE THIS FUNCTION IF YOU HAVE LOOP, or be ready to take a looong coffee :) *)
    let rec value_analysis func list_funcs malloc_addr free_addr backtrack clean_stack dir_output verbose show_values show_call show_free addr_caller  addr_caller_unloop n_caller flow_graph parsed_func =
        let score_childs=ref false in
        let rec merge_father fathers m=
            match fathers with
                | [] -> m
                | hd::tl -> merge_father tl (Absenv_v.merge hd.vsa m)
        in
        let (func_eip,func_bbs,func_name)=func in
        let value_analysis_nodes_rec n fathers bb_ori=
            let () = incr_number_ins () in
             (* Put init values *)
            let () = n.vsa<-Absenv_v.update n.init (merge_father fathers (Absenv_v.initAbsenEnv ())) in
            let () =
                if(show_values) 
                    then
                    let () = Printf.printf "Func transfer node %s\n %s" func_name (pp_nodes_value [n] bb_ori.unloop) in
                    flush Pervasives.stdout 
            in
            if ((land) n.type_node type_NODE_CALL)>0 then
                let addr_call=Ir_v.get_value_jump n.stmt n.vsa in
                match addr_call with
                | None -> (* if unknow jump *) 
                    let vsa = Absenv_v.restore_esp n.vsa in
                    n.vsa <- ignore_call vsa 
                | Some a ->
                    (* If call to free , should may be merge this into the stub module *)
                    if (List.exists (fun x-> x=a) free_addr) then
                    begin
                        let () =
                        let () = if(verbose) then Printf.printf "Call Free %x %s | %s \n" n.addr func_name (String.concat " " (List.map print_backtrack backtrack )) in
                        try 
                            let () = n.vsa <- Absenv_v.restore_esp n.vsa in
                            let val_esp=Absenv_v.get_value_string n.vsa "esp" in
                            let names=Absenv_v.values_to_names val_esp in
                            let vals=List.map (fun x -> Absenv_v.get_value n.vsa x) names in
                            let vals_filter=Absenv_v.filter_values  vals in
                            try 
                                let df = Absenv_v.check_df n.vsa vals_filter in
                                let () = Absenv_v.free n.vsa vals_filter (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) show_free  in
                                match df with
                                | [] -> ()
                                | _ ->
                                    if(verbose) then Printf.printf "DF found :%s\n" (Absenv_v.pp_he df);
                                    List.iter (
                                        fun c -> 
                                          add_uaf c ~t:Uafgenerique.SITE_DF [(((n.addr,bb_ori.unloop),"DF "^func_name,(!current_call))::backtrack)]
                                    ) df                 
                            with
                                Not_found -> () 
                        with 
                            Absenvgenerique.ERROR -> if (verbose) then Printf.printf "Error on free? \n" 
                in
                        (* Case of realloc *)
                        if (List.exists (fun x-> x=a) malloc_addr) then
                            let new_state = ((n.addr,bb_ori.unloop),func_name,(!current_call))::backtrack in
                            n.vsa <-  Absenv_v.malloc_ret n.vsa new_state

                    end
                    (* If call to malloc *) 
                    else if (List.exists (fun x-> x=a) malloc_addr) then
                        let new_state = ((n.addr,bb_ori.unloop),func_name,(!current_call))::backtrack in
                        let () = n.vsa <-  Absenv_v.malloc_ret n.vsa new_state in
                        n.vsa <- Absenv_v.restore_esp n.vsa 
                    else
                    (* check if stub *)
                    let is_stub, vsa=Stubfunc_v.stub a n.vsa (n.addr,bb_ori.unloop) func_name (!current_call) backtrack  in
                    if is_stub then n.vsa<-vsa 
                    else if (is_sup_depth backtrack) then
                                let () = if (verbose) then Printf.printf "Max depth reached\n" in
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa 
                    else if (!number_analyzed_func > !max_func) then 
                                let () = if (verbose) then Printf.printf "Number of func max reached\n" in
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa 
                    else if(is_max_ins ()) then
                                let () = if (verbose) then Printf.printf "Number of ins max reached\n" in
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa 
                    else
                        (* Call function *)
                        let () = number_analyzed_func := (!number_analyzed_func) +1 in
                        try
                            let func_name_ori=func_name in
                            let (func_eip_ori,func_bbs_ori,func_name)= find_func_eip a list_funcs in
                            if (List.exists (fun (_,x,_) -> x=func_name) backtrack) 
                                then
                                let () = if (verbose) then Printf.printf "Rec %x %s | %s \n" n.addr func_name (String.concat " " (List.map print_backtrack backtrack ))  in
                                let () = flush Pervasives.stdout in
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa 
                            else
                                let (func_eip,func_bbs)=(func_eip_ori,func_bbs_ori) in
                                let number_call_prev = (!current_call) in
                                let () = number_call:=(!number_call+1) in
                                let () = 
                                    if(flow_graph) 
                                    then 
                                        let () = saved_call := ((bb_ori.addr_bb,bb_ori.unloop),func_eip.addr_bb,(!current_call),(!number_call),func_name_ori)::(!saved_call) in 
                                        let () = Stack.push (n.addr,bb_ori.unloop) call_stack in
                                        Hashtbl.add call_stack_tbl (!number_call) (stack_to_list call_stack) 
                                in
                                let () = current_call := (!number_call) in
                                let () = List.iter (fun x -> init_value x ) func_bbs in
                                let () = (List.find (fun x -> x.addr==func_eip.addr_bb) func_eip.nodes).init<-n.vsa in
                                let called_func_n = !current_call in
                                try
                                    let () = if(show_call) then Printf.printf "Call %d %d (bb %x) 0x%x:%d %s | %s\n" (!current_call) (!number_call) (bb_ori.addr_bb) n.addr bb_ori.unloop func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                    let () = flush Pervasives.stdout in
                                    let (vsa,score)=value_analysis (func_eip,func_bbs,func_name) list_funcs malloc_addr free_addr (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) clean_stack dir_output verbose show_values show_call show_free bb_ori.addr_bb bb_ori.unloop number_call_prev flow_graph parsed_func in
                                    let () = if(verbose) then Printf.printf "End call %d %x:%d %s | %s\n"  (!current_call) n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                    let () = check_uaf func_bbs (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) verbose in 
                                    let () = if(flow_graph) then let _ = Stack.pop call_stack in () 
                                    in
                                    let () = current_call:=number_call_prev in
                                    let () = score_childs:=(||) (!score_childs) score in
                                    try
                                        let vsa = Absenv_v.filter_esp_ebp vsa clean_stack verbose in
                                        n.vsa <- Absenv_v.free_stack vsa (((func_eip.addr_bb,0),func_name,called_func_n)::((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) 
                                     with
                                        | Absenvgenerique.ERROR -> 
                                            let () = if (verbose) then 
                                                let () = Printf.printf "Func transfer node Error Filter esp / ebp \n %s" (pp_nodes_value [n] bb_ori.unloop) in
                                                let () = Printf.printf "\n---\n" in
                                                let () = Printf.printf "%s\n" (Absenv_v.pp_absenvs vsa) in 
                                                flush Pervasives.stdout 
                                            in
                                            let vsa = restore_stack_frame n.vsa vsa in
                                            let vsa = Absenv_v.restore_esp vsa in
                                            n.vsa <- Absenv_v.free_stack vsa (((func_eip.addr_bb,0),func_name,called_func_n)::((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) 
 
                                with
                                    | NOT_RET (vsa,score)  ->
                                        let () = Printf.printf "End call (NOT RET) %x:%d %s | %s\n" n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                        let () = check_uaf func_bbs (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) verbose in
                                        let () = if(flow_graph) then let _ = Stack.pop call_stack in ()
                                        in
                                        let () = current_call:=number_call_prev in
                                        let () = score_childs:=(||) (!score_childs) score in
                                        let () = if (verbose) then 
                                            let () = Printf.printf  "Func transfer node Not ret \n %s" (pp_nodes_value [n] bb_ori.unloop) in
                                            let () = Printf.printf "\n---\n" in
                                            Printf.printf "%s\n" (Absenv_v.pp_absenvs vsa) 
                                        in
                                        let () = flush Pervasives.stdout  in
                                        let () = n.vsa <- restore_stack_frame n.vsa vsa in
                                        let vsa = Absenv_v.restore_esp n.vsa in
                                        n.vsa <- Absenv_v.free_stack vsa (((func_eip.addr_bb,0),func_name,called_func_n)::((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) 
                                   | NOT_RET_NOT_LEAF ->
                                        let () = if (verbose) then Printf.printf "End call (NOT RET NOT LEAF) %x:%d %s | %s\n" n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                        let () = check_uaf func_bbs (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) verbose in
                                        let () = if(flow_graph) then let _ = Stack.pop call_stack in ()
                                        in
                                        let () = current_call:=number_call_prev in
                                        let () = n.vsa <- restore_stack_frame n.vsa vsa in
                                        let vsa = Absenv_v.restore_esp n.vsa in
                                        n.vsa <- Absenv_v.free_stack vsa (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) 
                        with
                            Not_found ->
                                let () = if(verbose) then Printf.printf "Not found 0x%x\n" a in
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa 
                else n.vsa<-Ir_v.function_transfer n.stmt n.vsa (n.addr,bb_ori.unloop) func_name (!current_call) backtrack; (* TODO should be number_init *)
        in
            let rec value_analysis_rec bb=
                if(reach_number_ins () || is_max_ins ()) then raise MAX_INS
                else
                if( (not bb.is_done) && (List.for_all (fun x -> x.is_done) bb.fathers)) then
                    let fathers_filter = List.filter (fun x -> (List.length x.nodes)>0) bb.fathers in
                    let fathers=((List.map (fun x -> List.nth x.nodes ((List.length x.nodes)-1)) fathers_filter )) in
                    let _ = List.fold_left (fun fathers x -> value_analysis_nodes_rec x fathers bb; [x]) fathers bb.nodes in
                    let () = bb.is_done<-true in
                    List.iter value_analysis_rec bb.sons
        in
        let () = value_analysis_rec func_eip in
        let retn_node=List.filter (fun x -> ((land) x.type_node type_NODE_RETN)>0) (List.concat (List.map (fun x -> x.nodes) func_bbs)) in
        let retn_bb=List.filter (fun bb -> List.exists (fun x-> ((land) x.type_node type_NODE_RETN)>0 ) bb.nodes) func_bbs in
        let () = 
            if((flow_graph) && addr_caller <> 0) then 
                List.iter (fun x -> saved_ret_call := ((addr_caller,addr_caller_unloop), n_caller, (x.addr_bb,x.unloop), !current_call,func_name)::(!saved_ret_call)) retn_bb
        in
        match retn_node with
            | [] ->     
                let leaf_bbs=List.filter (fun x -> x.number_sons==0) func_bbs in
                let leaf_node=List.map (fun x -> (List.nth x.nodes ((List.length x.nodes)-1))) leaf_bbs in
                begin
                    match leaf_node with
                        | [] -> raise NOT_RET_NOT_LEAF
                        | [hd] -> (hd.vsa,score_heap_use func_bbs func_name (!score_childs))
                        | hd::tl -> raise (NOT_RET ((List.fold_left (fun x y-> Absenv_v.merge x y.vsa) hd.vsa tl),score_heap_use func_bbs func_name (!score_childs)))
               end
            | [hd] ->
                (hd.vsa,score_heap_use func_bbs func_name (!score_childs))
            | hd::tl ->
                ((List.fold_left (fun x y-> Absenv_v.merge x y.vsa) hd.vsa tl),score_heap_use func_bbs func_name (!score_childs))

    
    let rec explore_graph func list_funcs backtrack number_analyzed_func_reil_inst verbose show_call addr_caller addr_caller_unloop  n_caller flow_graph parsed_func =
        if (!number_analyzed_func > !max_func) then raise MAX_EXPLORE
        else
        let (func_eip,func_bbs,func_name)=func in
        let explore_nodes_rec n n_pred bb_ori=
            if ((land) n.type_node type_NODE_FREE)>0 then ()
            else if ((land) n.type_node type_NODE_CALL)>0 
                then
                
                let addr_call=Ir_v.get_first_arg n_pred.stmt in
                match addr_call with
                    | None -> ()
                    | Some a -> 
                        try
                            let func_name_ori=func_name in
                            let (func_eip_ori,func_bbs_ori,func_name)= find_func_eip a list_funcs in
                                if (List.exists (fun x -> x=func_name) backtrack) then ()
                                else
                                   let (func_eip,func_bbs)=(func_eip_ori,func_bbs_ori) in
                                   let () = number_analyzed_func := (!number_analyzed_func)+1 in
                                   let  () = if (show_call) 
                                        then
                                        Printf.printf "call %x:%d %s | %s\n" n.addr bb_ori.unloop  func_name (String.concat " " backtrack) 
                                    in
                                let number_call_prev = (!current_call) in
                                let () = number_call:=(!number_call+1) in
                                let () = saved_call := ((bb_ori.addr_bb,bb_ori.unloop),func_eip.addr_bb,(!current_call),(!number_call),func_name_ori)::(!saved_call) in 
                                let () = 
                                    if(flow_graph) 
                                    then 
                                        let () = Stack.push (n.addr,bb_ori.unloop) call_stack in
                                        Hashtbl.add call_stack_tbl (!number_call) (stack_to_list call_stack)
                                in
                                let () = current_call := (!number_call) in
                                let () = explore_graph (func_eip,func_bbs,func_name) list_funcs (func_name::backtrack)  number_analyzed_func_reil_inst verbose show_call bb_ori.addr_bb bb_ori.unloop number_call_prev flow_graph parsed_func in
                                let () =current_call:=number_call_prev in
                                if(flow_graph) then 
                                        let _ = Stack.pop call_stack in ()
                        with
                            Not_found -> ()
        in
        let rec explore_rec bb=
            if( (not bb.is_done) && (List.for_all (fun x -> x.is_done) bb.fathers)) then
            let _ = List.fold_left (
                fun pred x ->
                    let () = number_analyzed_func_reil_inst := (!number_analyzed_func_reil_inst) + 1 in
                    let () = explore_nodes_rec x pred  bb in
                    x 
                ) (List.hd bb.nodes) (List.tl bb.nodes) in
            let () = bb.is_done<-true in
            let retn_bb=List.filter (fun bb -> List.exists (fun x-> ((land) x.type_node type_NODE_RETN)>0 ) bb.nodes) func_bbs in
            let () = 
                if((flow_graph) && addr_caller <> 0) then 
                List.iter (fun x -> saved_ret_call := ((addr_caller,addr_caller_unloop), n_caller, (x.addr_bb,x.unloop), !current_call,func_name)::(!saved_ret_call)) retn_bb
            in
            List.iter explore_rec bb.sons 
        in
        explore_rec func_eip    

    let print_site_dot oc (((addr,it),f,n),t) =
        match t with
        | Uafgenerique.SITE_NORMAL -> Printf.fprintf oc "%d%d%d[label=\"0x%x:%d call %s\", type=\"normal\"]\n"  n (Ir_v.get_real_addr addr) it (Ir_v.get_real_addr addr) it f
        | Uafgenerique.SITE_ALLOC -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d alloc\", type=\"alloc\" , style=filled,shape=\"box\", fillcolor=\"turquoise\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it
        | Uafgenerique.SITE_FREE -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d free\", type=\"free\", style=filled,shape=\"box\", fillcolor=\"green\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it
        | Uafgenerique.SITE_USE -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d use\", type=\"use\", style=filled,shape=\"box\", fillcolor=\"red\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it
        | Uafgenerique.SITE_DF -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d DF\", type=\"use\", style=filled,shape=\"box\", fillcolor=\"purple3\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it

    let already_seen_bb_dot = Hashtbl.create 4000

    let print_bbt_dot oc (bb,t) func_name n id_node=
        let addr = (Ir_v.get_real_addr bb.addr_bb) in
        let id_node_txt =
            try Hashtbl.find id_node (n,(addr)) 
            with Not_found ->        
                let id_node_txt = Printf.sprintf "%d%d" n (addr) in
                let () = Hashtbl.add id_node (n,addr/0x100) id_node_txt in
                id_node_txt
        in
        let print_event oc id_node_txt f addr t color = Printf.fprintf oc "%s[label=\"%s -> 0x%x %s\", type=\"%s\", style=filled,shape=\"box\", fillcolor=\"%s\"]\n" id_node_txt f addr f t color in
        let print oc id_node_txt addr t color = Printf.fprintf oc "%s[label=\"0x%x\", type=\"%s\", style=filled, fillcolor=\"%s\"]\n" id_node_txt addr t color in
        if (Hashtbl.mem already_seen_bb_dot (id_node_txt)) then () 
        else
            let () = Hashtbl.add already_seen_bb_dot (id_node_txt) 0 in
            match t with
            | NODE_OUT -> Printf.fprintf oc "%s[label=\"0x%x \", type=\"normal\"]\n"  id_node_txt (addr)
            | NODE_ALLOC -> print_event oc id_node_txt func_name addr "alloc" "blue" 
            | NODE_FREE -> print_event oc id_node_txt func_name addr "free" "green" 
            | NODE_USE -> print_event oc id_node_txt func_name addr "use" "red" 
            | NODE_DF -> print_event oc id_node_txt func_name addr "df" "purple3" 
            | NODE_EIP -> print oc id_node_txt addr "eip" "orange" 
            | NODE_EIP_ALLOC -> print oc id_node_txt addr "eipalloc" "pink" 
            | NODE_ALLOC_FREE -> print oc id_node_txt addr "allocfree" "aquamarine"
            | NODE_FREE_USE -> print oc id_node_txt addr "freeuse" "darkolivegreen2"  

    let print_bbt_ir_dot oc (bb,t) func_name n id_node=
        let addr_id = bb.addr_bb in
        let addr = Ir_v.get_real_addr bb.addr_bb in
        let it = bb.unloop in
        let id_node_txt =
            try Hashtbl.find id_node (n,(addr_id),it) 
            with Not_found ->        
                let id_node_txt = Printf.sprintf "%3d%d%d" n (addr_id) it in
                let () = Hashtbl.add id_node (n,addr_id,it) id_node_txt in
                id_node_txt
        in
        let print_event oc id_node_txt f addr t color = Printf.fprintf oc "%s[label=\"%s -> 0x%x %s\", type=\"%s\", style=filled,shape=\"box\", fillcolor=\"%s\"]\n" id_node_txt f addr f t color in
        let print oc id_node_txt addr it t color = Printf.fprintf oc "%s[label=\"0x%x:%d\", type=\"%s\", style=filled, fillcolor=\"%s\"]\n" id_node_txt addr it t color in
        if (Hashtbl.mem already_seen_bb_dot (id_node_txt)) then () 
        else
            let () = Hashtbl.add already_seen_bb_dot (id_node_txt) 0 in
            match t with
            | NODE_OUT -> Printf.fprintf oc "%s[label=\"0x%x:%d \", type=\"normal\"]\n"  id_node_txt (addr) it
            | NODE_ALLOC -> print_event oc id_node_txt func_name addr "alloc" "blue" 
            | NODE_FREE -> print_event oc id_node_txt func_name addr "free" "green" 
            | NODE_USE -> print_event oc id_node_txt func_name addr "use" "red" 
            | NODE_DF -> print_event oc id_node_txt func_name addr "df" "purple3" 
            | NODE_EIP -> print oc id_node_txt addr it "eip" "orange" 
            | NODE_EIP_ALLOC -> print oc id_node_txt addr it "eipalloc" "pink" 
            | NODE_ALLOC_FREE -> print oc id_node_txt addr it "allocfree" "aquamarine"
            | NODE_FREE_USE -> print oc id_node_txt addr it "freeuse" "darkolivegreen2"  


    let export_callsite n =
      try
        let l = Hashtbl.find call_stack_tbl n in
        let h_addr,h_it = List.hd l in
        List.fold_left (fun txt x -> let addr,it= x in Printf.sprintf "%x:%d-%s" (Ir_v.get_real_addr addr) it txt) (Printf.sprintf "%x:%d" (h_addr/0x100) h_it) (List.tl l) 
      with 
        | Not_found -> let () = Printf.printf "Callsite number unknow %d\n" n in "??" 
        | _ -> let () = Printf.printf "Callsite unknow \n" in "??" 

    let already_seen_bb_gml = Hashtbl.create 4000

    let print_bbt_gml oc (bb,t) _f n id_node=
        let addr = (Ir_v.get_real_addr bb.addr_bb) in
        let last_addr = (List.nth bb.nodes ((List.length bb.nodes)-1)).addr/0x100 in
        let print_nodes n = String.concat "," (List.map (fun x -> Printf.sprintf "%x" (x.addr/0x100))n) in
        let id_node_val = 
            try Hashtbl.find id_node (n,addr) 
            with Not_found ->
                let id_node_val = (Hashtbl.length id_node)  in
                let () = Hashtbl.add id_node (n,addr) id_node_val in
                id_node_val 
        in
        if (Hashtbl.mem already_seen_bb_gml (id_node_val)) then () 
        else
            let () = Hashtbl.add already_seen_bb_gml (id_node_val) 0 in
            let print oc n id_node_val nodes addr t = Printf.fprintf oc "node [ \n id %d \n addr %d \n call %d \n addrlast %d \n nodes \"%s\" \n label \"0x%x:%d\" \n type \"%s\" \n callsite \"%s\"\n]\n" id_node_val addr n last_addr nodes addr n t (export_callsite n) in
            match t with
            | NODE_OUT -> print oc n id_node_val "" addr "normal"
            | NODE_ALLOC -> print oc n id_node_val "" addr "alloc"
            | NODE_FREE ->  print oc n id_node_val "" addr "free"
            | NODE_USE -> print oc n id_node_val (print_nodes bb.nodes) addr "use"
            | NODE_DF -> print oc n id_node_val (print_nodes bb.nodes) addr "df" 
            | NODE_EIP -> print oc n id_node_val "" addr "eip" 
            | NODE_EIP_ALLOC ->  print oc n id_node_val "" addr "eipalloc" 
            | NODE_ALLOC_FREE -> print oc n id_node_val "" addr "allocfree" 
            | NODE_FREE_USE -> print oc n id_node_val "" addr "freeuse" 

    let print_site_arc_dot oc (((addr,it),_f,n),_t) leafs =
        List.iter (fun (((addr_,it_),_f_,n_),_t_) -> 
            Printf.fprintf oc "%d%d%d -> %d%d%d\n" n (Ir_v.get_real_addr addr) it n_ (addr_/0x100) it_ 
        ) leafs  

    let already_seen_arc_dot = Hashtbl.create 4000

    let print_bbt_arc_dot oc (ori_addr,ori_n,_,dst_addr,dst_n,_) id_node =
        if( ((Ir_v.get_real_addr ori_addr)=Ir_v.get_real_addr dst_addr) && (ori_n = dst_n)) then ()
        else
        let id_src = 
            try Hashtbl.find id_node (ori_n,(Ir_v.get_real_addr ori_addr)) 
            with Not_found ->        
                let id_node_txt = Printf.sprintf "%d%d" ori_n (Ir_v.get_real_addr ori_addr) in
                let () = Hashtbl.add id_node (ori_n,Ir_v.get_real_addr ori_addr) id_node_txt in
                id_node_txt
        in
        let id_dst = 
            try Hashtbl.find id_node (dst_n,(Ir_v.get_real_addr dst_addr)) 
            with Not_found ->        
                let id_node_txt = Printf.sprintf "%d%d" dst_n (Ir_v.get_real_addr dst_addr) in
                let () = Hashtbl.add id_node (dst_n,Ir_v.get_real_addr dst_addr) id_node_txt in
                id_node_txt
        in
        if (Hashtbl.mem already_seen_arc_dot (id_src,id_dst)) then () 
        else
            let () = Hashtbl.add already_seen_arc_dot (id_src,id_dst) 0 in
             Printf.fprintf oc "%s -> %s\n" id_src id_dst

    let print_bbt_ir_arc_dot oc (ori_addr,ori_n,ori_it,dst_addr,dst_n,dst_it) id_node =
        if( ((ori_addr)=dst_addr) && (ori_n = dst_n)) then ()
        else
        let id_src = 
            try Hashtbl.find id_node (ori_n,(ori_addr),ori_it) 
            with Not_found ->        
                let id_node_txt = Printf.sprintf "%3d%d%d" ori_n ( ori_addr) ori_it in
                let () = Hashtbl.add id_node (ori_n, ori_addr,ori_it) id_node_txt in
                id_node_txt
        in
        let id_dst = 
            try Hashtbl.find id_node (dst_n,(dst_addr),dst_it) 
            with Not_found ->        
                let id_node_txt = Printf.sprintf "%3d%d%d" dst_n ( dst_addr) dst_it in
                let () = Hashtbl.add id_node (dst_n,dst_addr,dst_it) id_node_txt in
                id_node_txt
        in
        if (Hashtbl.mem already_seen_arc_dot (id_src,id_dst)) then () 
        else
            let () = Hashtbl.add already_seen_arc_dot (id_src,id_dst) 0 in
             Printf.fprintf oc "%s -> %s\n" id_src id_dst



    let already_seen_arc_gml = Hashtbl.create 4000

    let print_bbt_arc_gml oc (ori_addr,ori_n,_,dst_addr,dst_n,_) id_node =
        if( ((Ir_v.get_real_addr ori_addr)=Ir_v.get_real_addr dst_addr) && (ori_n = dst_n)) then ()
        else
        let id_src = 
            try Hashtbl.find id_node (ori_n,(Ir_v.get_real_addr ori_addr)) 
            with Not_found ->
                let id_node_val = (Hashtbl.length id_node)  in
                let () = Hashtbl.add id_node (ori_n,Ir_v.get_real_addr ori_addr) id_node_val in
                id_node_val 
        in        
        let id_dst =
            try Hashtbl.find id_node (dst_n,(Ir_v.get_real_addr dst_addr)) 
            with Not_found ->
                let id_node_val = (Hashtbl.length id_node)  in
                let () = Hashtbl.add id_node (dst_n,Ir_v.get_real_addr dst_addr) id_node_val in
                id_node_val 
        in
        if (Hashtbl.mem already_seen_arc_gml (id_src,id_dst)) then () 
        else
            let () = Hashtbl.add already_seen_arc_gml (id_src,id_dst) 0 in
            Printf.fprintf oc "edge [ \n source %d \n target %d\n]\n" id_src id_dst



    let clean_already_seen () = 
        Hashtbl.clear already_seen_bb_gml ;
        Hashtbl.clear already_seen_arc_gml ;
        Hashtbl.clear already_seen_bb_dot ;
        Hashtbl.clear already_seen_arc_dot ;;

    let print_begin_dot oc =
        Printf.fprintf oc "strict digraph g {\n"

    let print_end_dot oc =
         Printf.fprintf oc "}\n"
 
    let print_begin_gml oc =
        Printf.fprintf oc "graph [ \nversion 2\ndirected 1\n"

    let print_end_gml oc =
         Printf.fprintf oc "]\n"
 
    let print_group_dot oc bbst n =
        let () = Printf.fprintf oc "Subgraph cluster_%d\n {" n in
        let () = List.iter (fun (bb) -> Printf.fprintf oc "%d%d\n" n ((Ir_v.get_real_addr bb.addr_bb))) bbst in
        Printf.fprintf oc "}\n"

    let print_group_ir_dot oc bbst n =
        let () = Printf.fprintf oc "Subgraph cluster_%d\n {" n in
        let () = List.iter (fun (bb) -> Printf.fprintf oc "%3d%d%d\n" n ( bb.addr_bb) bb.unloop) bbst in
        Printf.fprintf oc "}\n"

    let print_group_gml _oc _bbst _n = ()
   
    (* calls : (bb_ori,bb_it) , bb_dst , ori_n, dst_n *)
    let get_call bb call_id calls =
        List.find_all (fun ((bb_ori,_),_,ori_n,_,_) -> ori_n = call_id && bb_ori = bb.addr_bb) calls

    let get_call_invert bb call_id calls =
        List.find_all (fun (_,bb_dst,_,dst_n,_) -> dst_n = call_id && bb_dst = bb.addr_bb) calls 

    (* ret : (bb_ori,bb_it) ,ori_n , (bb_dst,bb_it) , dst_n ,func_name*)
    let get_ret bb call_id rets =
        List.find_all (fun ((bb_ori,_),ori_n,_,_,_) -> ori_n = call_id && bb_ori = bb.addr_bb) rets

    let get_func eip funcs =
        try 
            find_func_eip_no_unloop eip funcs
        with
            Not_found -> failwith (Printf.sprintf "Get func not found %x\n" eip)
   
    let export_ret_joint bb call_id id_node rets oc print_arc = 
        let ret = get_ret bb call_id rets in
        List.iter (fun (_,_,(ret_addr,_),ret_id,_) -> List.iter (fun x -> print_arc oc (ret_addr, ret_id ,0,x.addr_bb, call_id,x.unloop) id_node) bb.sons) ret

    let export_call bb call_id id_node calls oc print_arc print_group call_stack funcs explore_bb disjoint =
        let call = get_call bb call_id calls in
        match call with         
        | [] ->
            begin 
            try List.iter (fun x -> print_arc oc (bb.addr_bb,call_id,bb.unloop,x.addr_bb,call_id,x.unloop) id_node) bb.sons
            with Not_found -> failwith "Error "
            end
        | l -> List.iter ( fun (_,dst_eip,_,func_called_id,_) -> 
                                               let () = print_arc oc (bb.addr_bb, call_id,bb.unloop, dst_eip,func_called_id,0) id_node in
                                               let (func_called_eip,bbs,func_called_name) = get_func (dst_eip/0x100) funcs in
                                               let () = print_group oc bbs func_called_id in
                                               let () = if(disjoint) then List.iter (fun x -> print_arc oc (bb.addr_bb,call_id,bb.unloop,x.addr_bb,call_id,0) id_node) bb.sons in
                                               let last_node_addr = (List.hd (List.rev bb.nodes)).addr in
                                               explore_bb func_called_eip func_called_id func_called_name (last_node_addr::call_stack) 
                ) l

     let merge_types_backward t1 t2 = match t1,t2 with
        | a,b when a=b -> None
        | NODE_ALLOC,_ | _, NODE_ALLOC -> Some NODE_ALLOC
        | NODE_FREE,_ | _,NODE_FREE -> Some NODE_FREE
        | NODE_DF,_ -> Some NODE_DF
        | NODE_USE,_ | _ , NODE_USE -> Some NODE_USE
        | NODE_EIP,_| _, NODE_EIP -> Some NODE_EIP
        | _, NODE_EIP_ALLOC -> Some NODE_EIP_ALLOC
        | NODE_EIP_ALLOC, _ -> Some NODE_EIP_ALLOC
        | _, NODE_ALLOC_FREE  -> Some NODE_ALLOC_FREE
        | NODE_ALLOC_FREE,_  -> Some NODE_ALLOC_FREE
        | _, NODE_FREE_USE -> Some NODE_FREE_USE
        | NODE_FREE_USE,_ -> Some NODE_FREE_USE
        | NODE_OUT,_  -> Some NODE_OUT

     let merge_types_forward t1 t2 = match t1,t2 with
        | a,b when a=b -> None
        | NODE_DF,_ | _,NODE_DF -> Some NODE_DF
        | NODE_USE,_ | _ , NODE_USE -> Some NODE_USE
        | NODE_FREE,_ | _,NODE_FREE -> Some NODE_FREE
        | NODE_FREE_USE,_ | _,NODE_FREE_USE -> Some NODE_FREE_USE
        | NODE_ALLOC_FREE,_ | _, NODE_ALLOC_FREE -> Some NODE_ALLOC_FREE
        | NODE_ALLOC,_ | _, NODE_ALLOC -> Some NODE_ALLOC
        | NODE_EIP_ALLOC, _ | _,  NODE_EIP_ALLOC-> Some NODE_EIP_ALLOC
        | NODE_EIP,_ -> Some NODE_EIP
        | NODE_OUT,_ -> Some NODE_OUT


     let merge_types_forward_equal t1 t2 = match t1,t2 with
        | a,b when a=b -> a
        | NODE_DF,_ | _,NODE_DF -> NODE_DF
        | NODE_USE,_ | _ , NODE_USE -> NODE_USE
        | NODE_FREE,_ | _,NODE_FREE -> NODE_FREE
        | NODE_FREE_USE,_ | _,NODE_FREE_USE -> NODE_FREE_USE
        | NODE_ALLOC_FREE,_ | _, NODE_ALLOC_FREE -> NODE_ALLOC_FREE
        | NODE_ALLOC,_ | _, NODE_ALLOC -> NODE_ALLOC
        | NODE_EIP_ALLOC, _ | _,  NODE_EIP_ALLOC-> NODE_EIP_ALLOC
        | NODE_EIP,_ -> NODE_EIP
        | NODE_OUT,_  -> NODE_OUT

     let rec find_node_in_bbs addr nodes =
                match nodes with
                | [] -> None
                | tl::hd -> if (List.exists (fun x -> x.addr==addr) tl.nodes) then Some tl
                        else find_node_in_bbs addr hd

     let find_node_from_name addr name funcs = 
                let _eip,bbs,_ = find_func_name_no_unloop name funcs in
                match find_node_in_bbs addr bbs with
                | Some n -> n
                | None -> failwith (Printf.sprintf "Error during backward exploration %x %s\n" addr name)

    let explore_backward l_event funcs calls rets =
        let l_event = List.rev l_event in
        let type_tbl = Hashtbl.create 200 in
        let explore_call bb call_n calls f t = 
                let call = get_call_invert bb call_n calls in
                List.iter (fun ((ori,_),_,ori_id,_,name) -> f (find_node_from_name ori  name funcs) t ori_id true) call
        in
        let explore_ret bb call_n rets f t = 
                let ret = get_ret bb call_n rets in
                List.iter (fun (_,_,(ret_addr,_),ret_id,func_ret_name) ->  f (find_node_from_name ret_addr func_ret_name funcs) t ret_id false) ret
        in
        let rec explore n t call_n was_call =
                let addr = n.addr_bb in
                let t =
                        try
                                let prev_t = Hashtbl.find type_tbl (addr,call_n) in
                                let t_new = merge_types_backward t prev_t  in
                                begin
                                        match t_new with
                                        | None -> None
                                        | Some t_new -> if t_new = prev_t then None else Some t_new
                                end
                        with Not_found -> Some t
                in
                match t with
                | Some t -> 
                        let () = Hashtbl.replace type_tbl (addr,call_n) t in
                        let t = decrease_subgraph_type t in 
                        let () = explore_call n call_n calls explore t in
                        let () = if(not was_call) then explore_ret n call_n rets explore t in
                        List.iter (fun x -> explore x t call_n false) n.fathers 
                | None -> () (* do not explore if t not changing *)
        in     
        let extract event f =
                let node = List.hd event in
                let (((addr,_),func_name,call_n),t) = node in
                let node_found = find_node_from_name addr func_name funcs in
                f node_found ((site_to_subgraph_type t)) call_n false
        in
        let () = List.iter (fun  x -> extract x explore ) l_event in
        type_tbl


    let explore_forward eip l_event funcs calls rets =
        let type_tbl = Hashtbl.create 2000 in
        let find_node addr funcs = 
                try
                        let eip,_,_ = find_func_eip_no_unloop addr funcs in eip
                with Not_found -> failwith (Printf.sprintf "Func not found %x \n" addr)
        in
        let explore_call bb call_n calls f t = 
                let call = get_call bb call_n calls in
                match call with
                | [] -> false
                | l -> List.iter (fun (_,dst,_,dst_id,_) -> f (find_node (Ir_v.get_real_addr dst) funcs) t dst_id) l ; true
        in
        let explore_after_ret bb call_n rets f = 
                let ret = get_ret bb call_n rets in
                let t = List.fold_left (fun acc (_,_,(ret_addr,_),ret_id,_) -> 
                                        try
                                                merge_types_forward_equal acc (Hashtbl.find type_tbl (ret_addr,ret_id))
                                        with
                                                Not_found -> acc
                        ) (NODE_EIP) ret 
                in List.iter (fun x -> f x t call_n) bb.sons
        in
        let handle_event event =
                (*  from a event, we took the node addr, then we retrive the value of the bb.addr_bb*) 
                let (((addr,_),func_name,call_n),t) = List.hd event in 
                let n = find_node_from_name addr func_name funcs in 
                Hashtbl.add type_tbl (n.addr_bb,call_n) (site_to_subgraph_type t)
        in
        let () = List.iter (fun x -> handle_event x)  l_event in 
        let rec explore n t call_n =
                let addr = n.addr_bb in
                let t = 
                        try
                                let prev_t = Hashtbl.find type_tbl (addr,call_n) in
                                merge_types_forward t prev_t 
                        with Not_found -> Some t
                in
                match t with
                | Some t -> 
                        let () = Hashtbl.replace type_tbl (addr,call_n) t in
                        let t = increase_subgraph_type t in
                        if (not (explore_call n call_n calls explore t)) then                         
                                List.iter (fun x -> explore x t call_n) n.sons
                        else explore_after_ret n call_n rets explore

                | None -> () (* do not explore if t not changing *)
        in     
        let eip = find_node eip funcs in
        let () = explore eip NODE_EIP 0 in
        type_tbl

    let export_flow_graph_uaf filename print_begin print_end print_node print_arc print_group type_tbl_backward type_tbl_forward eip calls funcs rets flow_graph_disjoint =
        let merge_type f b = match f,b with
                | a,b when a=b -> a
                | NODE_OUT,_ | _,NODE_OUT -> NODE_OUT
                | NODE_EIP,_ | _,NODE_EIP-> NODE_EIP
                | NODE_FREE,_ | _,NODE_FREE -> NODE_FREE
                | NODE_ALLOC,_ | _,NODE_ALLOC -> NODE_ALLOC
                | NODE_DF,_ | _ , NODE_DF -> NODE_DF
                | NODE_USE,_ | _,NODE_USE -> NODE_USE
                | NODE_EIP_ALLOC, NODE_ALLOC_FREE -> NODE_EIP_ALLOC
                | NODE_ALLOC_FREE, NODE_FREE_USE -> NODE_ALLOC_FREE
                | NODE_FREE_USE,NODE_ALLOC_FREE -> NODE_FREE_USE
                | NODE_FREE_USE,_  -> NODE_FREE_USE
                | NODE_ALLOC_FREE,_  -> NODE_ALLOC_FREE
                | NODE_EIP_ALLOC,_ -> NODE_EIP_ALLOC
        in
        let oc = open_out filename in 
        let () = Printf.printf "Export %s\n" filename in
        let bb_saw = Hashtbl.create 40000 in (* not taking /0x100, because some bb REIL share the same /0x100 *)
        let id_node = Hashtbl.create 40000 in
        let () = print_begin oc in
        let rec explore_bb bb call_id func_name call_stack =
            if (Hashtbl.mem bb_saw (bb.addr_bb,call_id)) then ()
            else
                let () = Hashtbl.add bb_saw (bb.addr_bb,call_id) true in
                let t = 
                        try
                                let t_forward = Hashtbl.find type_tbl_forward (bb.addr_bb,call_id) in
                                let t_backward = Hashtbl.find type_tbl_backward (bb.addr_bb,call_id) in
                                merge_type t_forward t_backward
                         with
                                Not_found -> NODE_OUT
                in               
                let () = print_node oc (bb,t) func_name call_id id_node in
                let () = if(not flow_graph_disjoint) then export_ret_joint bb call_id id_node rets oc print_arc in
                let () = export_call bb call_id id_node calls oc print_arc print_group call_stack funcs explore_bb flow_graph_disjoint in
                List.iter (fun x -> explore_bb x call_id func_name call_stack) bb.sons
        in
        let eip,bbs,name = get_func eip funcs in
        let () = print_group oc bbs 0 in
        let () = explore_bb eip 0 name [eip.addr_bb] in
        let () = print_end oc  in
        let () = clean_already_seen () in
        close_out oc 

    let export_flow_graph filename print_begin print_end print_node print_arc print_group  eip calls funcs rets flow_graph_disjoint =
        let oc = open_out filename in 
        let () = Printf.printf "Export %s\n" filename in
        let bb_saw = Hashtbl.create 40000 in (* not taking /0x100, because some bb REIL share the same /0x100 *)
        let id_node = Hashtbl.create 40000 in
        let () = print_begin oc in
        let rec explore_bb bb call_id func_name call_stack =
            if (Hashtbl.mem bb_saw (bb.addr_bb,call_id)) then ()
            else
                let () = Hashtbl.add bb_saw (bb.addr_bb,call_id) true in
                let t = if((Ir_v.get_real_addr bb.addr_bb) <> eip) then NODE_OUT else NODE_EIP in
                let () = print_node oc (bb,t) func_name call_id id_node in
                let () = if(not flow_graph_disjoint) then export_ret_joint bb call_id id_node rets oc print_arc in
                let () = export_call bb call_id id_node calls oc print_arc print_group call_stack funcs explore_bb flow_graph_disjoint in
                List.iter (fun x -> explore_bb x call_id func_name call_stack) bb.sons
        in
        let eip,bbs,name = get_func eip funcs in
        let () = print_group oc bbs 0 in
        let () = explore_bb eip 0 name [eip.addr_bb] in
        let () = print_end oc  in
        let () = clean_already_seen () in
        close_out oc 

    let export_flow_graph_unloop filename print_begin print_end print_node print_arc print_group name funcs =
        let oc = open_out filename in 
        let () = Printf.printf "Export %s\n" filename in
        let id_node = Hashtbl.create 40000 in
        let () = print_begin oc in
        let eip,bbs,name = find_func_name name funcs in
        let rec explore_bb bb func_name =
            let t = if(bb.addr_bb <> eip.addr_bb) then NODE_OUT else NODE_EIP in
            let () = print_node oc (bb,t) func_name 0 id_node in
            let () = List.iter (fun x -> print_arc oc (bb.addr_bb,0,bb.unloop,x.addr_bb,0,x.unloop) id_node) bb.sons in
            List.iter (fun x -> explore_bb x func_name ) bb.sons
        in
        let () = print_group oc bbs 0 in
        let () = explore_bb eip name in
        let () = print_end oc  in
        let () = clean_already_seen () in
        close_out oc 

    let export_func_unloop funcs name =
        let filename = Printf.sprintf "%s.dot" name in
        let filename_unloop = Printf.sprintf "%s-unloop.dot" name in
        let filename_unloop_ir = Printf.sprintf "%s-unloop-irreducible.dot" name in
        let () = export_flow_graph_unloop filename print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot name funcs in
        let () = export_flow_graph_unloop filename_unloop print_begin_dot print_end_dot print_bbt_ir_dot print_bbt_ir_arc_dot print_group_ir_dot name funcs in
        let () = irreducible := true in
        export_flow_graph_unloop filename_unloop_ir print_begin_dot print_end_dot print_bbt_ir_dot print_bbt_ir_arc_dot print_group_ir_dot name funcs 


    let print_sg dir_output eip calls list_funcs ret flow_graph_gml flow_graph_dot flow_graph_disjoint =
        if(not (Uaf_v.is_uaf () )) then ()
        else
        let () =
        try 
            Unix.mkdir dir_output 0o777 
        with
            _ -> ()
        in
        let sg_uaf_by_alloc = Uaf_v.get_sg_uaf_by_alloc () in
        let () = Printf.printf "Results, uaf found : \n\n" in
        Hashtbl.iter 
            (fun (chunk_id,chunk_type) elems -> 
                let str = Absenv_v.pp_chunk_t chunk_type in
                let n = ref 0 in
                List.iter (fun (alloc,free,use) ->
                        let l_event =(alloc::free@use) in
                        let () = Uaf_v.export_tree_uaf (Printf.sprintf "%s/uaf-%s%d-%d.dot" dir_output str chunk_id !n)  print_begin_dot print_end_dot print_site_dot print_site_arc_dot alloc free use in
                        let () = if(flow_graph_dot || flow_graph_gml) then
                                let type_tbl_backward = explore_backward l_event list_funcs calls ret in
                                let type_tbl_forward = explore_forward eip l_event list_funcs calls ret in
                                let () = if (flow_graph_dot) then   
                                    let () = export_flow_graph_uaf (Printf.sprintf "%s/uaf-%s%d-%d-details.dot" dir_output str chunk_id !n) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot type_tbl_backward type_tbl_forward eip calls list_funcs ret false  
                                    in if(flow_graph_disjoint) then
                                            export_flow_graph_uaf (Printf.sprintf "%s/uaf-%s%d-%d-details-disjoint.dot" dir_output str chunk_id !n) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot type_tbl_backward type_tbl_forward eip calls list_funcs ret true 
                                in
                                if (flow_graph_gml) then
                                     export_flow_graph_uaf (Printf.sprintf "%s/uaf-%s%d-%d-details.gml" dir_output str chunk_id !n) print_begin_gml print_end_gml print_bbt_gml print_bbt_arc_gml print_group_gml type_tbl_backward type_tbl_forward eip calls list_funcs ret false
                        in n:=!n+1 
                ) elems
            ) sg_uaf_by_alloc ;;


    let print_g dir_output eip calls list_funcs ret flow_graph_gml flow_graph_dot flow_graph_disjoint =
        let () = Hashtbl.clear already_seen_bb_gml in
        let () = Hashtbl.clear already_seen_arc_gml in
        let () = Hashtbl.clear already_seen_bb_dot in
        let () = Hashtbl.clear already_seen_arc_dot in
        let () = try 
            Unix.mkdir dir_output 0o777 
        with
            _ -> ()
        in
        let () = if (flow_graph_dot) then   
            let () = export_flow_graph (Printf.sprintf "%s/graph-details.dot" dir_output ) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot eip calls list_funcs ret false  
            in if(flow_graph_disjoint) then
             export_flow_graph (Printf.sprintf "%s/graph-details-disjoint.dot" dir_output ) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot eip calls list_funcs ret true 
        in
        let () = if (flow_graph_gml) then
            export_flow_graph (Printf.sprintf "%s/graph-details.gml" dir_output ) print_begin_gml print_end_gml print_bbt_gml print_bbt_arc_gml print_group_gml  eip calls list_funcs ret false in
        ()
 
    let launch_supercallgraph_analysis func_name list_funcs dir_output verbose show_call flow_graph flow_graph_dot flow_graph_gml flow_graph_disjoint parsed_func =
        let () = Hashtbl.clear call_stack_tbl in
        let () = Stack.clear call_stack in
        let () = Hashtbl.add call_stack_tbl (0) ([(0,0)]) in
        let () = Stack.push (0,0) call_stack in
        let () = number_analyzed_func := 0 in
        let count_reil_inst = ref 0 in
        try 
            let (eip,bbs,name) = find_func_name func_name list_funcs in
            let () = List.iter (fun x -> init_value x ) bbs in
            let () = try
                let () = explore_graph (eip,bbs,name)  list_funcs ([""])  count_reil_inst verbose show_call 0 0 0 flow_graph parsed_func in
                let () = print_g dir_output (eip.addr_bb/0x100) (!saved_call) list_funcs (!saved_ret_call) flow_graph_dot flow_graph_gml flow_graph_disjoint in
                Printf.printf "Number of func from %s : %d and %d REIL inst\n" func_name (!number_analyzed_func) (!count_reil_inst)
            with
                MAX_EXPLORE -> 
                let () = print_g dir_output (eip.addr_bb/0x100) (!saved_call) list_funcs (!saved_ret_call) flow_graph_dot flow_graph_gml flow_graph_disjoint in
                Printf.printf "Number of func from %s : MAX\n" func_name
            in
            (!number_analyzed_func)
        with
            | Not_found -> 
                let () = Printf.printf "Func %s : error (func not found)\n" func_name in
                (!number_analyzed_func)
            | NOT_RET (_vsa,_score) -> 
                let () = if(verbose) then Printf.printf "Not ret\n" in
                let () = Printf.printf "Number of func from %s %d\n" func_name (!number_analyzed_func) in
                (!number_analyzed_func) 
            | NOT_RET_NOT_LEAF -> 
                (!number_analyzed_func) 

    let launch_value_analysis func_name list_funcs list_malloc list_free clean_stack dir_output verbose show_values show_call show_free flow_graph flow_graph_dot flow_graph_gml flow_graph_disjoint parsed_func =
        if(not (reach_number_ins())) then
        try
            let () = number_analyzed_ins := 0 in
            let () = number_analyzed_func := 0 in
            let () = Hashtbl.clear call_stack_tbl in
            let () = Stack.clear call_stack in
            let () = Hashtbl.add call_stack_tbl (0) ([(0,0)]) in
            let () = Stack.push (0,0) call_stack in
            let () = Uaf_v.clear () in
            let (eip,bbs,name) = find_func_name func_name list_funcs in
            let () = List.iter (fun x -> init_value x ) bbs  in
            let _ = value_analysis (eip,bbs,name)  list_funcs list_malloc list_free ([(eip.addr_bb,0),name,0]) clean_stack dir_output verbose show_values show_call show_free  0 0 0 flow_graph parsed_func in
            let () = check_uaf bbs [(eip.addr_bb,0),name,!current_call] verbose in
            let () = total_number_analyzed_ins := (!total_number_analyzed_ins) + (!number_analyzed_ins) in
            let () = Printf.printf "End of analysis (number of ins analyzed %d)\n" (!number_analyzed_ins) in
            print_sg dir_output (eip.addr_bb/0x100) (!saved_call) list_funcs (!saved_ret_call) flow_graph_dot flow_graph_gml flow_graph_disjoint
        with
            | Not_found -> Printf.printf "Func %s : error (not found)\n" func_name
            | NOT_RET (_vsa,_score) -> ()
            | NOT_RET_NOT_LEAF -> ()
            | MAX_INS -> Printf.printf "Total number ins max reached %d %d \n" (!total_number_analyzed_ins) (!number_analyzed_ins)


        let end_analysis () =
                let () = Printf.printf "End analysis, total analyzed ins %d\n " (!total_number_analyzed_ins) in
                Uaf_v.end_analysis ()
end;;

