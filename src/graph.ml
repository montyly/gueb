open Absenv
open Ir 
open Stubfunc
open Program_piqi


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
    exception NOT_RET of (Absenv_v.absenv)*(Absenv_v.he list)*(Absenv_v.he list)*bool;;
    exception NOT_RET_NOT_LEAF;;
    exception Timeout_unloop;;
    exception MAX_EXPLORE;;

    module Ir_v = Ir_a (Absenv_v)
    module Stubfunc_v = Stubfunc_a (Absenv_v)
    type node =
    {
        addr : int ;
        stmt : Ir_v.ir_stmt;
        mutable type_node : int;
        mutable init : Absenv_v.absenv;
        mutable vsa : Absenv_v.absenv;
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

    type site_type = 
        | SITE_NORMAL
        | SITE_ALLOC
        | SITE_FREE
        | SITE_USE
        | SITE_DF

    let pp_site_type s = match s with
        | SITE_NORMAL -> "normal"
        | SITE_ALLOC -> "alloc"
        | SITE_FREE -> "free"
        | SITE_USE -> "use"
        | SITE_DF -> "df"      

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

    let pp_subgraph_type s = match s with
        | NODE_OUT -> "out"
        | NODE_ALLOC -> "alloc"
        | NODE_FREE -> "free"
        | NODE_USE -> "use"
        | NODE_DF -> "df" 
        | NODE_EIP -> "eip" 
        | NODE_EIP_ALLOC -> "eip_alloc"
        | NODE_ALLOC_FREE -> "alloc_free"
        | NODE_FREE_USE -> "free_use"

    let site_to_subgraph_type t =
        match t with
        | SITE_NORMAL -> NODE_OUT
        | SITE_ALLOC -> NODE_ALLOC
        | SITE_FREE -> NODE_FREE
        | SITE_USE -> NODE_USE
        | SITE_DF -> NODE_DF
        

    (* site : (addr,it) * func_name * call_n *)
    type site = (int*int)*string*int

    (* On a list of site, add type, t for the last, SITE_NORMAL for others *)
    let add_type sites t = 
        let add_type_ ((addr,it),s,n) t = (((addr,it),s,n),t) in
        let head = List.hd sites in
        let head = add_type_ head t in
        let tl = List.tl sites in
        let tl = List.map (fun x -> add_type_ x SITE_NORMAL) tl in
        head::tl
       (* let sites_rev = List.rev sites in
        let head = List.hd sites_rev in     
        let head = add_type head t in
        let tl = List.tl sites_rev in
        let tl = List.map (fun x -> add_type x SITE_NORMAL) tl in
        List.rev (head::tl)*)

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


    type tree_node = {
        site : site*site_type;
        mutable leafs : tree_node list;
    }

    let number_bbs=ref 0

    let number_call = ref 0

    let current_call = ref 0
    
(*    let saved_values = ref [] *)
  
    (* (bb_ori,bb_it), bb_dst, ori_n, dst_n *) 
    let saved_call = ref [] 
    
    let call_stack = Stack.create () 
    let call_stack_tbl = Hashtbl.create 200
    
    (* bb_ori, bb_dst, ori_n, dst_n,name_ret_func *)     
    let saved_ret_call = ref [] 

    (* Hashtbl that contains result 
     * form :
     *  (id,size)  *   free sites  * malloc site * use sites
     * key is chunk * free site, because from a same malloc, different free that lead to different uaf 
     * *)
    let sg_uaf = ((Hashtbl.create 100) : (( (int*Absenv_v.chunk_t) * (((site*site_type) list) list)   , ((site*site_type) list) *   (((site*site_type) list) list) ) Hashtbl.t )) ;;



    (* 
     * pretty print for sg_uaf
     *)
    let pp_uaf_label l  = String.concat "\n" (List.map (fun (p,(addr,it),f,_n) -> (Printf.sprintf "%s%d%d[label=\"0x%x:%d call %s\"]" p (Ir_v.get_real_addr addr) it (Ir_v.get_real_addr addr) it f) ) l)
  
    let add_p l =
        let l = List.rev l in 
        let p = ref "" in
        let l =List.map 
            (fun ((addr,it),f,n) ->
                let ret = ((!p),(addr,it),f,n) in
                let () = p:=(!p)^(Printf.sprintf "%d%d" (Ir_v.get_real_addr addr) it) in
                ret 
            ) l
        in
        List.rev l

   let pp_uaf st=
        let st = List.rev st in
        let pp (p,(addr,it),_f,_n) = (Printf.sprintf "%s%d%d" p (Ir_v.get_real_addr addr) it ) in
        String.concat "->" (List.map (fun x -> pp x) st)

    let pp_uafs st =
        String.concat "\n" (List.map (fun x -> pp_uaf x) st)

    let pp_alloc (p,(addr,it),f,_n) = Printf.sprintf "%s%d%d[label=\"%s -> 0x%x:%d alloc\", style=filled,shape=\"box\", fillcolor=\"turquoise\"]" p (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it
    
    let pp_free free = String.concat "\n" (List.map (fun (p,(addr,it),f,_n) ->  Printf.sprintf "%s%d%d[label=\"%s -> 0x%x:%d free\", style=filled,shape=\"box\", fillcolor=\"green\"]" p (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it) free)
    
    let pp_use use = String.concat "\n" (List.map (fun (p,(addr,it),f,_n) ->  Printf.sprintf "%s%d%d[label=\"%s -> 0x%x:%d use\", style=filled,shape=\"box\", fillcolor=\"red\"]" p  (Ir_v.get_real_addr addr) it f  (Ir_v.get_real_addr addr) it) use)

    (*
     * print to dot format
     *)
    let print_uaf_dot filename alloc free use =
        let oc = open_out filename in
        let remove_type t = fst t in
        let alloc = List.map remove_type alloc in
        let free = List.map (fun x -> List.map remove_type x) free in
        let use = List.map (fun x -> List.map remove_type x) use in
        let alloc = add_p ( alloc) in
        let free = List.map (fun x -> add_p ( x)) free in
        let use = List.map (fun x -> add_p ( x)) use in
        let () = Printf.fprintf oc "strict digraph g {\n" in
        let () = Printf.fprintf oc "%s\n" (pp_uaf alloc) in
        let () = Printf.fprintf oc "%s\n" (pp_uafs free) in
        let () = Printf.fprintf oc "%s\n" (pp_uafs use) in
        let () = Printf.fprintf oc "%s\n" (pp_uaf_label (List.tl alloc)) in
        let () = Printf.fprintf oc "%s\n" (pp_uaf_label (List.concat (List.map (fun x -> List.tl x )free))) in
        let () = Printf.fprintf oc "%s\n" (pp_uaf_label (List.concat (List.map (fun x -> List.tl x ) use))) in
        let () = Printf.fprintf oc "%s\n" (pp_alloc (List.hd alloc (*(List.length alloc)-1*))) in
        let () = Printf.fprintf oc "%s\n" (pp_free (List.map ( fun x ->(List.hd x (*(List.length x)-1*)) ) free)) in
        let () = Printf.fprintf oc "%s\n" (pp_use (List.map ( fun x ->(List.hd x (*(List.length x)-1*)) ) use)) in
        let () = Printf.fprintf oc "}\n" in
        close_out oc

    let print_graph_dot dir values calls =
        let txt = Printf.sprintf "strict digraph g {\n" in
        let print_values_dot_stream_bb bb counter =
            let access_heap = List.map (fun x -> Ir_v.access_heap x.stmt x.vsa) bb.nodes in
            let access_heap = List.concat access_heap in
            let access_heap = List.map (fun x -> Absenv_v.pp_chunk x) access_heap in
            let access_heap = List.sort_uniq String.compare access_heap in
            let access_heap = 
                if(List.length access_heap > 0)
                then
                     Printf.sprintf "\\nAccessHeap %s" (String.concat " " access_heap) 
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
            let is_loop n = List.exists (fun x -> (x.addr_bb = n.addr_bb) && (x.unloop <> n.unloop)) nodes in
            List.filter (fun x -> not (is_loop x)) leafs 
        in
        let txt = List.fold_left (
            fun x (ori,dst,ori_n,dst_n) ->
                if (ori.unloop ==0) then
                  let leafs =  find_leafs dst_n in
                  let ori_son = List.hd ori.sons in (* todo : call with many sons ? *)
                  let txt = List.fold_left (fun y x -> Printf.sprintf "%s%03d%d -> %03d%d\n" y dst_n x.addr_bb ori_n ori_son.addr_bb ) "" leafs in 
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
                let txt = List.fold_left (fun x y -> Printf.sprintf "%s%s" x (print_values_dot_stream_bb y key)) prev l in
                txt
            ) tbl txt in
        let oc = open_out (Printf.sprintf "%s/graph.dot" dir) in
        let () = Printf.fprintf oc "%s" txt in
        let () = Printf.fprintf oc "}\n" in
        close_out oc


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
        {addr=addr;stmt=stmt;type_node=type_NODE_NORMAL;init = Absenv_v.initAbsenEnv () ; vsa=Absenv_v.initAbsenEnv ();ha=[];hf=[]};;
   
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
            let () = number_bbs:= (!number_bbs)+1 in
            {uniq_id= !number_bbs;addr_bb=addr;sons=[];sons_kosaraju=[];fathers=[];fathers_kosaraju=[];unloop=0;is_done=false;nodes=[]}
 
    (** Export **)
    
    
    let print_bb_dot stream bb =
        let print_link n0 n1  = Printf.fprintf stream "%d -> %d;\n" n0.uniq_id n1.uniq_id in
        let print_bb n = Printf.fprintf stream "%d[label=\"0x%x:%d (%d)\"];\n" n.uniq_id (n.addr_bb/0x100) n.unloop n.uniq_id in
        let () = print_bb bb in
        List.iter (fun x -> print_link bb x) bb.sons 
    
    let print_bbs_dots_stream stream bbs=
        let () = Printf.fprintf stream "digraph g {\n" in
        let rec rec_print_bb_dots bbs =
            match bbs with
            | [] -> ()
            | hd::tl -> let () = print_bb_dot stream hd in
                        rec_print_bb_dots tl
        in 
        let () = rec_print_bb_dots bbs in
        Printf.fprintf stream "}\n"
    
    let print_bbs_dots filename bbs = 
        let oc = open_out filename in
        let () = print_bbs_dots_stream oc bbs in
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
    
    let new_node node = {addr=node.addr;stmt=node.stmt; type_node=node.type_node;init=node.init;vsa=node.vsa;ha=node.ha;hf=node.hf};;
   
    let new_bb bb unloop= 
        let () = number_bbs:=(!number_bbs)+1 in
        {uniq_id= !number_bbs;addr_bb=bb.addr_bb;sons=bb.sons;sons_kosaraju=bb.sons_kosaraju;fathers=bb.fathers;fathers_kosaraju=bb.fathers_kosaraju;unloop=unloop;is_done=false;nodes= []};;
    
    
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
        | [] -> [head]
        | l -> l;;
    
    let find_non_entry fathers stack =
        List.filter (fun x -> List.exists (fun y -> y.addr_bb==x.addr_bb && x.unloop==y.unloop) stack) fathers;;

    let find_arc node stack = 
            let arc_end=find_non_entry node.fathers stack in
                List.map (fun x -> (node,x) ) arc_end;;
    
    let nodes_not_in ori new_nodes= List.filter (fun x -> List.for_all (fun y -> y.addr_bb<>x.addr_bb) new_nodes) (ori);;

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
        
    let remove_ori_no_check ori stop=List.filter (fun x -> x.addr_bb<>stop.addr_bb && x.unloop<>stop.unloop) ori;;
        
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
        let () = remove_all_fathers nodes in
        let () = add_fathers_from_son nodes in
        List.iter (fun x -> x.fathers<-remove_dupplicate x.fathers) nodes ;; 
    
    let rec fix_link_nodes new_nodes nodes nodes2 entry stop=
        match new_nodes with 
        | [] -> ()
        | tl::hd ->
            let () = fix_son_node tl nodes nodes2 entry stop in
            fix_link_nodes hd nodes nodes2 entry stop ;;
    
    let copy_remove_arc entry stop nodes number_unloop= 
        let rec copy_remove_arc_rec entry stop nodes stack n=
            if n==0 then 
                let () = fix_link_nodes nodes nodes nodes entry stop in
                stack
            else
                let () = hack_number:=!hack_number+1 in
                let new_nodes=List.map (fun x -> new_bb x number_unloop ) nodes in
                let () = fix_link_nodes new_nodes nodes new_nodes entry stop in
                let new_entry=(find_node_in_nodes entry new_nodes) in
                let new_stop=(find_node_in_nodes stop new_nodes) in
                match new_entry,new_stop with
                | None,_ | _,None ->stack
                | Some a, Some b-> 
                    let () = stop.sons<-add_ori stop.sons [a] in
                    let () = a.fathers<-add_ori a.fathers [stop] in
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
        let () =  reset_fathers concat_list in
        retour;;
    
    
    
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
                        let () = x.sons <- (List.find_all (fun x -> x.addr_bb <> head.addr_bb) x.sons) in
                        let () = head.fathers<-(List.find_all (fun y -> y.addr_bb <> x.addr_bb) head.fathers) in
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
                        if(n_x<>n_first) then fix n nodes_first (n_x-n_first)
                        else ()
                 ) list_nodes
    
    let copy_nodes list_nodes number_unloop_init =
        let rec copy_nodes_rec list_nodes number_unloop stack =
(*            let () = Printf.printf "Number unloop left %d \n" number_unloop in*)
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
            let entry_n1 = List.map (fun x -> find_node_no_unloop x nodes_n1) entry in
            let () = List.iter (fun x -> x.sons <- entry_n1@x.sons) leafs_n in
            let () = List.iter (fun x -> x.fathers <- leafs_n) entry_n1 in
            nodes
        with
            Not_found -> nodes
    
    let expanse_loop list_nodes entry_point leafs number_unloop = 
        let new_list_nodes = copy_nodes list_nodes number_unloop in
        let new_list_nodes = List.rev (new_list_nodes) in
        let () = fix_sons_fathers new_list_nodes in
       (* let sc = List.concat (List.map (fun (_,n) -> n) new_list_nodes) in*)
        let list_nodes = List.map (fun  x ->  fix_entry_leaf x new_list_nodes entry_point leafs) new_list_nodes in
        List.concat list_nodes
    
    let rec unrool head list_nodes number_unloop =
        let select_best_entry l = List.fold_left (fun x y -> if ( List.length x.fathers > List.length y.fathers) then x else y ) (List.hd l) (List.tl l) in
        let exist l = List.find_all (fun x -> List.exists (fun y -> y.addr_bb=x.addr_bb) list_nodes) l in
        let () = List.iter (fun x -> let () = x.sons_kosaraju<-(exist x.sons) in x.fathers_kosaraju<-(exist x.fathers)) list_nodes in
        let scs = kosaraju head list_nodes in
        let unrool_sc sc head = 
        begin
            if (List.length sc==1) then sc 
            else
            let all_entry_point = find_entry sc head in
            let entry_point = [select_best_entry all_entry_point] in (* quand on a plusieurs entry_point, on en selectionne qu'un pour le reste ? code a changer, vu que par la suite on pouvait en avoir plusieurs ;) TODO *)
            let leafs = List.map (fun x -> (x,create_leafs sc x)) entry_point in (* leafs is list of : entry_point -> leaf*) 
            let sc = unrool (List.hd entry_point) sc number_unloop in
            let () = List.iter (fun x -> let () = x.sons_kosaraju<-x.sons in x.fathers_kosaraju<-x.fathers) list_nodes in
            let ret = expanse_loop sc entry_point (List.concat (List.map (fun (_,y) -> y) leafs)) number_unloop  in
            ret
        end
        in List.concat (List.map (fun x -> unrool_sc x head) scs) ;;
    
    let begin_eip b=
    try 
        let n=List.find (fun x -> x.addr==b.addr_bb) b.nodes (* TODO need beeter stuff for EIP... *)
        in n.type_node<-((lor) n.type_node type_NODE_ENTRY)
    with 
      Not_found -> Printf.printf "Eip not found ! \n"
    
    let find_nodes_from_addr list_addr list_nodes =List.map (fun x -> new_node x  ) (List.find_all (fun n -> List.exists (fun x -> x=n.addr) list_addr) list_nodes );;
   

    let rec clean_vsa_nodes nodes = 
        match nodes with
        | [] -> ()
        | hd::tl -> let () = hd.vsa <- Absenv_v.initAbsenEnv () in
                    let () = hd.ha <- [] in
                    let () = hd.hf <- [] in
                    clean_vsa_nodes tl 
 
    let rec clean_vsa_bbs bbs = 
        match bbs with
        | [] -> ()
        | hd::tl -> let () = clean_vsa_nodes hd.nodes in clean_vsa_bbs tl    
    
    let parse_protobuf_no_unloop func =
        let (bbs,connexion_unfiltre,eip_addr,_,nodes,call_retn)=Ir_v.parse_func_protobuf func in
        let connexion=List.filter (fun (x,y) -> x<>y) connexion_unfiltre in (* TODO need to handle loop on himself ! *)
        let bb_nodes = List.map (fun x -> let (addr,list_nodes)=x in (create_bb addr,list_nodes)) bbs in
        let bbs_only=List.map (fun x-> let (a,_)=x in a)  bb_nodes in
        let bbs_connect= connect_bbs bbs_only connexion in
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
(*        let () = update_malloc_free_protobuf nodes  in*)
        (eip,bbs,func.name);;
 

    let parse_protobuf_number func number_unloop  =
            let (bbs,connexion_unfiltre,eip_addr,_,nodes,call_retn)=Ir_v.parse_func_protobuf func in
            let connexion=List.filter (fun (x,y) -> x<>y) connexion_unfiltre in (* TODO need to handle loop on himself ! *)
            let bb_nodes = List.map (fun x -> let (addr,list_nodes)=x in (create_bb addr,list_nodes)) bbs in
            let bbs_only=List.map (fun x-> let (a,_)=x in a)  bb_nodes in
            let bbs_connect= connect_bbs bbs_only connexion in
            let eip=find_eip bbs_connect eip_addr in
            let bb_unloop= unrool eip bbs_connect number_unloop  in
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
    (*        let () = update_malloc_free_protobuf nodes  in*)
            (eip,bbs,func.name);;
    
    let rec remove_loop_time timeout func  number_unloop (*old_h*) =
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
(*        try
            let (eip,bbs,n) = Hashtbl.find parsed_func func in
            let () = clean_vsa_bbs bbs in
(*            let () = Printf.printf "Func %s already seen !\n" n in*)
            (eip,bbs,n)
        with Not_found ->*)
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
(*            let () = Hashtbl.add parsed_func func ret in*)
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
            | hd::tl -> pp_nodes_values_rec tl ((Printf.sprintf "%x:%d " hd.addr val_unloop )^(Ir_v.print_stmt hd.stmt)^(Printf.sprintf " type %s" (pp_type_node hd.type_node))^" : \n"^(Absenv_v.pp_absenvs hd.vsa)^(Printf.sprintf "Ha : %s \nHf : %s\n\n" (Absenv_v.pp_he hd.ha) (Absenv_v.pp_he hd.hf) )^l) 
        in pp_nodes_values_rec n "";;
    
    let pp_nodes_value_unloop n =
        let rec pp_nodes_values_rec n l =
            match n with 
            | [] -> l
            | (hd,unloop)::tl -> pp_nodes_values_rec tl ((Printf.sprintf "%x:%d " hd.addr unloop )^(Ir_v.print_stmt hd.stmt)^(Printf.sprintf " type %s" (pp_type_node hd.type_node))^" : \n"^(Absenv_v.pp_absenvs hd.vsa)^(Printf.sprintf "Ha : %s Hf : %s\n\n" (Absenv_v.pp_he hd.ha) (Absenv_v.pp_he hd.hf) )^l) 
        in pp_nodes_values_rec n "";;

    (* counter of chunk variable *)    
    let number_chunk=ref 0;;
    
    let init_value b =
        let () = b.is_done<-false in
        let rec init_value_rec nodes =
        match nodes with
        | [] -> ()
        | hd::tl -> 
            let () = Absenv_v.clean_vsa hd.vsa in
            let () = hd.vsa<- Absenv_v.initAbsenEnv ()in
            let () = hd.ha<-[] in 
            let () = hd.hf<-[] in
            (
                match hd.type_node with
                | _ when ((land) hd.type_node type_NODE_ENTRY)>0 
                    -> hd.init<-Absenv_v.init_first 
             (*   | _ when ((land) hd.type_node type_NODE_MALLOC)>0 
                    -> 
                    let new_state = ((hd.addr,hd.unloop),func_name,(!current_call))::state in
                    let () = hd.init<-(Absenv_v.init_malloc ( !number_chunk) new_state ) in
                    let () = hd.ha<-[Absenv_v.init_chunk !number_chunk 0 new_state]  in
                    number_chunk:=!number_chunk+1;
                *)
                | _ -> ()
            );
            init_value_rec tl 
        in init_value_rec b.nodes;;
    
    
   
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
   
    let score_heap_use _bbs _func_name _score_child = false ;; (* Useless for now *)
 
    (* Debug function *)
    let print_backtrack ((addr,it),name,_n) = Printf.sprintf "0x%x:%d:%s" addr it name;;
    let print_time()= Printf.sprintf "%d:%d:%d:%d" ((int_of_float (Sys.time()*.100.))/(60*60*60))  ((mod) ((int_of_float (Sys.time()*.100.))/(60*60)) 60)  ((mod) ((int_of_float (Sys.time()*.100.))/60) 60 ) ((mod) (int_of_float (Sys.time()*.100.)) 60);;
   
    (** Uaf structure manipulation **)

    let add_uaf ?(t=SITE_USE) c state =
        let state = List.map (fun x -> add_type x t) state in
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
        let c_alloc = add_type c_alloc SITE_ALLOC in
        let c_free = List.map (fun x -> add_type x SITE_FREE) c_free in
        let key = Absenv_v.get_chunk_key c,c_free in
        try
            let alloc,use=Hashtbl.find sg_uaf key in
            let use = filter_list use state in
            Hashtbl.replace sg_uaf key (alloc,use)
        with
            Not_found -> Hashtbl.add sg_uaf key (c_alloc,state)
     
    let check_uaf bbs backtrack addr=
(*        let nodes=List.concat (List.map (fun x -> x.nodes) bbs) in/*)
        List.iter (fun (nodes,unloop) ->
         let uaf_result=List.map Ir_v.check_uaf (List.map (fun x -> (x.stmt,x.vsa,x.hf,(x.addr,unloop))) nodes) in
         if (List.length uaf_result)>0 
         then
             List.iter (
                 fun x-> match x with
                     | None -> ()
                     | Some (stmt,chunks,addr) ->
                         let _,b,_ = (List.hd backtrack) in
                         let state = (addr,b,!current_call)::backtrack in
                         let () = List.iter (fun c -> add_uaf c [state]) chunks in
                         Printf.printf "Uaf find :%s\n" ((let a,it = addr in Printf.sprintf "%x:%d " a it )^(Ir_v.print_stmt stmt)^(Absenv_v.pp_he chunks) )
             ) uaf_result;
        if (List.exists (
             fun x -> match x with
             | None -> false
             | Some _ -> true
           ) uaf_result) 
         then Printf.printf "Uaf find in %x Backtrack %s \n ###################################################################\n" addr (String.concat " " (List.map print_backtrack backtrack ))
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
                Absenv_v.set_value_string vsa "ebp" prev_ebp

    let visit_before _bb = ()
    
    let visit_after _bb = ()
      
    let stack_to_list s =
    if (Stack.is_empty s) then []
    else 
        let l = ref [] in
        let () = Stack.iter (fun x -> l := x::!l) s in
        !l

    (** Value analysis **)
    (* DO NOT USE THIS FUNCTION IF YOU HAVE LOOP, or be ready to take a looong coffee :) *)
    let rec value_analysis func list_funcs malloc_addr free_addr backtrack dir_output verbose show_values show_call show_free addr_caller  addr_caller_unloop n_caller flow_graph parsed_func =
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
        let value_analysis_nodes_rec n fathers bb_ori=
           
             (* Put init values *)
            let () = n.vsa<-Absenv_v.update n.init (merge_father fathers (Absenv_v.initAbsenEnv ())) in
            (* Merge values from fathers *)
            let (ha,hf) = merge_fathers_heap fathers n.ha n.hf in
            (* Merge chunk values *)
            let () = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
            let () = n.hf<-hf in
            let () =
                if(show_values) 
                    then
                    let () = Printf.printf "Func transfer node %s\n %s" func_name (pp_nodes_value [n] bb_ori.unloop) in
                    flush Pervasives.stdout 
            in
(*            if ((land) n.type_node type_NODE_FREE)>0 the)
            else if (((land) n.type_node type_NODE_CALL)>0 && ((land) n.type_node type_NODE_MALLOC)>0)  
                then
                n.vsa <- Absenv_v.restore_esp n.vsa 
            else*) 
            if ((land) n.type_node type_NODE_CALL)>0 then
            begin
                let addr_call=Ir_v.get_value_jump n.stmt n.vsa in
                match addr_call with
                | None -> (* if unknow jump *) 
                    let vsa = Absenv_v.restore_esp n.vsa in
                    n.vsa <- ignore_call vsa 
                | Some a ->
                    (* If call to free , should may be merge this into the stub module *)
                    if (List.exists (fun x-> x=a) free_addr) then
                    begin
                        (* Case of realloc *)
                        let () = if (List.exists (fun x-> x=a) malloc_addr) then
                            let new_state = ((n.addr,bb_ori.unloop),func_name,(!current_call))::backtrack in
                            let () = n.vsa <-Absenv_v.update  (Absenv_v.init_malloc ( !number_chunk) new_state )  n.vsa in
                            let () = n.ha <- (Absenv_v.init_chunk !number_chunk (Absenv_v.classical_chunk()) new_state) :: n.ha in
                            number_chunk:=!number_chunk+1 in
                        let () = if(verbose) then Printf.printf "Call Free %x %s | %s \n" n.addr func_name (String.concat " " (List.map print_backtrack backtrack )) in
                        try 
                            let () =  n.vsa <- Absenv_v.restore_esp n.vsa in
                            let val_esp=Absenv_v.get_value_string n.vsa "esp" in
                            let names=Absenv_v.values_to_names val_esp in
                            let vals=List.map (fun x -> Absenv_v.get_value n.vsa x) names in
                            let vals_filter=Absenv_v.filter_values  vals in
                            try 
                                let df = Absenv_v.check_df n.hf vals_filter in
                                    let (ha,hf)=Absenv_v.free n.ha n.hf vals_filter (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) show_free  in
                                    let () = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                    let () = n.hf<-hf in
                                match df with
                                | [] ->    ()
                                | _ -> 
                                    List.iter (
                                        fun c -> 
                                          add_uaf c ~t:SITE_DF [(((n.addr,bb_ori.unloop),"DF "^func_name,(!current_call))::backtrack)]
                                    ) df                 
                            with
                                Not_found -> () 
(*                                    let (ha,hf)=Absenv_v.free n.ha n.hf vals_filter (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) show_free in
                                    let () = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                    n.hf<-hf*)
                        with 
                            AbsEnv.ERROR ->
                                begin   
                                     if (verbose) then Printf.printf "Error on free? \n" 
                                end
                    end
                    (* If call to malloc *) 
                    else if (List.exists (fun x-> x=a) malloc_addr) then
                        let new_state = ((n.addr,bb_ori.unloop),func_name,(!current_call))::backtrack in
                        let () = n.vsa <-Absenv_v.update  (Absenv_v.init_malloc ( !number_chunk) new_state )  n.vsa in
                        let () = n.ha <- (Absenv_v.init_chunk !number_chunk (Absenv_v.classical_chunk()) new_state) :: n.ha in
                        let () = number_chunk:=!number_chunk+1 in
                        n.vsa <- Absenv_v.restore_esp n.vsa 
                    else
                    (* check if stub *)
                    let is_stub, vsa,ha,hf=Stubfunc_v.stub a n.vsa n.ha n.hf number_chunk (n.addr,bb_ori.unloop) func_name (!current_call) backtrack  in
                    if is_stub 
                        then 
                            let () = n.vsa<-vsa in
                            let () = n.ha<-ha in
                            n.hf<-hf
                    else
                        try
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
                                let () = 
                                    if(flow_graph) 
                                    then 
                                        let () = number_call:=(!number_call+1) in
                                        let () = saved_call := ((bb_ori.addr_bb,bb_ori.unloop),func_eip.addr_bb,(!current_call),(!number_call))::(!saved_call) in 
                                        let () = Stack.push (n.addr,bb_ori.unloop) call_stack in
                                        let () = Hashtbl.add call_stack_tbl (!number_call) (stack_to_list call_stack) in
                                        current_call := (!number_call)
                                in
                                let () = List.iter (fun x -> init_value x ) func_bbs in
                                let () = (List.find (fun x -> x.addr==func_eip.addr_bb) func_eip.nodes).init<-n.vsa in
                                let () = (List.find (fun x -> x.addr==func_eip.addr_bb) func_eip.nodes).ha<-n.ha in
                                let () = (List.find (fun x -> x.addr==func_eip.addr_bb) func_eip.nodes).hf<-n.hf in
                                try
                                    let () = if(show_call) then Printf.printf "Call %d %d (bb %x) 0x%x:%d %s | %s\n" (!current_call) (!number_call) (bb_ori.addr_bb) n.addr bb_ori.unloop func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                    let () = flush Pervasives.stdout in
                                    let (vsa,ha,hf,score)=value_analysis (func_eip,func_bbs,func_name)(*next_func*) list_funcs malloc_addr free_addr (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) dir_output verbose show_values show_call show_free bb_ori.addr_bb bb_ori.unloop number_call_prev flow_graph parsed_func in
                                    let () = if(verbose) then Printf.printf "End call %d %x:%d %s | %s\n"  (!current_call) n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                    let () = check_uaf func_bbs (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) n.addr in 
                                    let () = if(flow_graph) then 
                                        let _ = Stack.pop call_stack in
                                        current_call:=number_call_prev 
                                    in
                                    let () = score_childs:=(||) (!score_childs) score in
                                    try
                                        let () = n.vsa<-Absenv_v.filter_esp_ebp vsa verbose in
                                        let () = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                        n.hf<-hf
                                    with
                                        | AbsEnv.ERROR -> 
                                            let () = if (verbose) then 
                                                let () = Printf.printf "Func transfer node Error Filter esp / ebp \n %s" (pp_nodes_value [n] bb_ori.unloop) in
                                                let () = Printf.printf "\n---\n" in
                                                let () = Printf.printf "%s\n" (Absenv_v.pp_absenvs vsa) in 
                                                flush Pervasives.stdout 
                                            in
                                            let () = n.vsa <- restore_stack_frame n.vsa vsa in
                                            let () = n.vsa <- Absenv_v.restore_esp n.vsa in
                                            let () = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                            n.hf<-hf
                                        |_ -> Printf.printf "WTF \n";
                                with
                                    | NOT_RET (vsa,ha,hf,score)  ->
                                        let () = Printf.printf "End call (NOT RET) %x:%d %s | %s\n" n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                        let () = check_uaf func_bbs (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) n.addr in
                                        let () = if(flow_graph) then 
                                                                let _ = Stack.pop call_stack in
                                                                current_call:=number_call_prev 
                                        in
                                        let () = score_childs:=(||) (!score_childs) score in
                                        let () = if (verbose) then 
                                            let () = Printf.printf  "Func transfer node Not ret \n %s" (pp_nodes_value [n] bb_ori.unloop) in
                                            let () = Printf.printf "\n---\n" in
                                            Printf.printf "%s\n" (Absenv_v.pp_absenvs vsa) 
                                        in
                                        let () = flush Pervasives.stdout  in
                                        let () = n.vsa <- restore_stack_frame n.vsa vsa in
                                        let () = n.vsa <- Absenv_v.restore_esp n.vsa in
                                        let () = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                        n.hf<-hf;                                               
                                   | NOT_RET_NOT_LEAF ->
                                        let () = if (verbose) then Printf.printf "End call (NOT RET NOT LEAF) %x:%d %s | %s\n" n.addr bb_ori.unloop   func_name (String.concat " " (List.map print_backtrack backtrack )) in
                                        let () = check_uaf func_bbs (((n.addr,bb_ori.unloop),func_name,!current_call)::backtrack) n.addr in
                                        let () = if(flow_graph) then 
                                                                let _ = Stack.pop call_stack in
                                                                current_call:=number_call_prev 
                                        in
                                        let () = n.vsa <- restore_stack_frame n.vsa vsa in
                                        let () = n.vsa <- Absenv_v.restore_esp n.vsa in
                                        let () = n.ha<-Absenv_v.merge_alloc_free_conservatif ha hf in
                                        n.hf<-hf;  
                        with
                            Not_found ->
                                let () = if(verbose) then Printf.printf "Not found 0x%x\n" a in
(*                                let vsa = restore_stack_frame n.vsa vsa in*)
                                let vsa = Absenv_v.restore_esp n.vsa in
                                n.vsa <- ignore_call vsa 
                end
                else
                    n.vsa<-Ir_v.function_transfer n.stmt n.vsa n.hf number_chunk (n.addr,bb_ori.unloop) func_name (!current_call) backtrack; (* TODO should be number_init *)
        in
            let rec value_analysis_rec bb=
                if( (not bb.is_done) && (List.for_all (fun x -> x.is_done) bb.fathers)) 
                    then
                    let () = visit_before bb in
                    let fathers_filter = List.filter (fun x -> (List.length x.nodes)>0) bb.fathers in
                    let fathers=ref ((List.map (fun x -> List.nth x.nodes ((List.length x.nodes)-1)) fathers_filter )) in
                    let () = List.iter (
                        fun x -> 
                            let () =  value_analysis_nodes_rec x (!fathers) bb  in
                            fathers:=[x];
                        ) bb.nodes in
                    let () = bb.is_done<-true in
                   (* let () =  
                        Remove this for now
                        if(details_values)
                            then (* for now, only keeping the last vsa of a bb or not*)
                         (*   let () = bb.nodes <- [List.hd (List.rev bb.nodes)] in*)
                            saved_values:=(bb,(!current_call))::(!saved_values)
                    in*)
                    let () = visit_after bb in
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
    
    let rec explore_graph func list_funcs backtrack ref_count max_count ref_count_reil_inst verbose show_call addr_caller addr_caller_unloop  n_caller flow_graph parsed_func =
        if (!ref_count > max_count) then raise MAX_EXPLORE
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
                            let (func_eip_ori,func_bbs_ori,func_name)= find_func_eip a list_funcs in
                                if (List.exists (fun x -> x=func_name) backtrack) then ()
                                else
                                   let (func_eip,func_bbs)=(func_eip_ori,func_bbs_ori) in
                                   let () = ref_count := (!ref_count)+1 in
                                   let  () = if (show_call) 
                                        then
                                        Printf.printf "call %x:%d %s | %s\n" n.addr bb_ori.unloop  func_name (String.concat " " backtrack) 
                                    in
                                let number_call_prev = (!current_call) in
                                let () = 
                                    if(flow_graph) 
                                    then 
                                        let () = number_call:=(!number_call+1) in
                                        let () = saved_call := ((bb_ori.addr_bb,bb_ori.unloop),func_eip.addr_bb,(!current_call),(!number_call))::(!saved_call) in 
                                        let () = Stack.push (n.addr,bb_ori.unloop) call_stack in
                                        let () = Hashtbl.add call_stack_tbl (!number_call) (stack_to_list call_stack) in
                                        current_call := (!number_call)
                                in
                                let () = explore_graph (func_eip,func_bbs,func_name) list_funcs (func_name::backtrack) ref_count max_count ref_count_reil_inst verbose show_call bb_ori.addr_bb bb_ori.unloop number_call_prev flow_graph parsed_func in
                                if(flow_graph) then 
                                        let _ = Stack.pop call_stack in
                                        current_call:=number_call_prev
                        with
                            Not_found -> ()
        in
        let rec explore_rec bb=
            if( (not bb.is_done) && (List.for_all (fun x -> x.is_done) bb.fathers)) then
          (*  let fathers_filter = List.filter (fun x -> (List.length x.nodes)>0) bb.fathers in
            let fathers=ref ((List.map (fun x -> List.nth x.nodes ((List.length x.nodes)-1)) fathers_filter )) in*)
            let _ = List.fold_left (
                fun pred x ->
                    let () = ref_count_reil_inst := (!ref_count_reil_inst) + 1 in
                    let () = explore_nodes_rec x pred  bb in
                  (*  let () = fathers:=[x] in*)
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


    let print_site(((addr,it),f,n),_t) = Printf.sprintf "%x,%d %s %d" (Ir_v.get_real_addr addr) it f n

    let uaf_to_tree (alloc:(site*site_type) list) (free:((site*site_type) list) list) (use:((site*site_type) list) list)  =
        (* convert a list of site to a tree (linear) *) 
        let site_to_tree sites = 
            let leaf = { site = List.hd sites ; leafs = [] } in
            let _ = List.fold_left (fun res x ->
                let new_leaf = {site = x; leafs = [] } in
                let () = res.leafs <- [new_leaf] in
                new_leaf
            ) leaf (List.tl sites) in
            leaf 
        in
        (* Add a sites in tree *)
        let rec add_sites_to_tree leaf s sites = 
            try
                let next_leaf = 
                    if (s=leaf.site) then leaf
                    else
                        List.find (fun x -> x.site = s  ) leaf.leafs 
                  in
                    add_sites_to_tree next_leaf (List.hd sites) (List.tl sites)
            with
                Not_found -> 
                    leaf.leafs <- leaf.leafs@[(site_to_tree(s::sites))] (* add in the end -> alloc first in dot files *)
        in    
        let first_tree = site_to_tree alloc in
        let () = List.iter (fun x -> add_sites_to_tree first_tree (List.hd x) (List.tl x)) free in
        let () = List.iter (fun x -> add_sites_to_tree first_tree (List.hd x) (List.tl x)) use in
        first_tree

    let print_site_dot oc (((addr,it),f,n),t) =
        match t with
        | SITE_NORMAL -> Printf.fprintf oc "%d%d%d[label=\"0x%x:%d call %s\", type=\"normal\"]\n"  n (Ir_v.get_real_addr addr) it (Ir_v.get_real_addr addr) it f
        | SITE_ALLOC -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d alloc\", type=\"alloc\" , style=filled,shape=\"box\", fillcolor=\"turquoise\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it
        | SITE_FREE -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d free\", type=\"free\", style=filled,shape=\"box\", fillcolor=\"green\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it
        | SITE_USE -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d use\", type=\"use\", style=filled,shape=\"box\", fillcolor=\"red\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it
        | SITE_DF -> Printf.fprintf oc "%d%d%d[label=\"%s -> 0x%x:%d DF\", type=\"use\", style=filled,shape=\"box\", fillcolor=\"red\"]\n" n (Ir_v.get_real_addr addr) it f (Ir_v.get_real_addr addr) it

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
            | NODE_DF -> print_event oc id_node_txt func_name addr "df" "red" 
            | NODE_EIP -> print oc id_node_txt addr "eip" "orange" 
            | NODE_EIP_ALLOC -> print oc id_node_txt addr "eipalloc" "pink" 
            | NODE_ALLOC_FREE -> print oc id_node_txt addr "allocfree" "aquamarine"
            | NODE_FREE_USE -> print oc id_node_txt addr "freeuse" "darkolivegreen2"  

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

    let print_bbt_arc_dot oc (ori_addr,ori_n,dst_addr,dst_n) id_node =
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

    let already_seen_arc_gml = Hashtbl.create 4000

    let print_bbt_arc_gml oc (ori_addr,ori_n,dst_addr,dst_n) id_node =
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

    let print_group_gml _oc _bbst _n = ()
   
    let export_call_graph_uaf filename print_begin print_end print_node print_arc (alloc:(site*site_type) list) (free:((site*site_type) list) list) (use:((site*site_type) list) list)  =
        let oc = open_out filename in 
        let () = print_begin oc in
        let () = Printf.printf "Export %s\n" filename in
        let alloc = List.rev alloc in
        let free = List.map (fun x -> List.rev x) free in 
        let use = List.map (fun x -> List.rev x) use in 
        let tree = uaf_to_tree alloc free use in
        let rec explore leaf =
            let () = print_node oc leaf.site in
            let () = print_arc oc leaf.site (List.map (fun x -> x.site ) leaf.leafs) in
            List.iter (fun x -> explore x) leaf.leafs 
        in
        let () = explore tree  in
        let () = print_end oc  in
        close_out oc

    (* tree uaf, funcs (eip,bbs,name) -> funcs as (eip,(bb, typebbs) list,name,n) *)
    let tree_to_list_func tree funcs =
        let add_type addr t x = 
            if (List.exists (fun y -> y.addr = addr ) x.nodes) then (x,t) 
            else (x,SITE_NORMAL) in
        let ret = ref [] in
        let rec explore l =
            let (((addr,_),f,n),t) = l.site in
            match t with
            | SITE_NORMAL -> List.iter explore l.leafs
            | SITE_USE | SITE_DF ->
                let func = find_func_name_no_unloop f funcs in
                let func_convert (eip,bbs,name) = (eip,List.map (fun x -> add_type addr t x) bbs, name,n)  in
                let func =  (func_convert func) in
                ret := (func)::(!ret)
            | SITE_ALLOC|SITE_FREE -> ()
                
        in
        let () = explore tree in
        !ret

    let callgraph_to_list eip calls funcs =
       (* let compare bb1 bb2 = 
            let () = Printf.printf "Compare %x %x : %d \n" bb1.addr_bb bb2.addr_bb ( compare (bb1.addr_bb/0x100) (bb2.addr_bb/0x100))
            in compare (bb1.addr_bb) (bb2.addr_bb) 
        in*)
        let funcs_called = List.map (fun (_,eip,_,n) -> (eip/0x100,n) ) calls in
        let func_convert (eip,bbs,name) n = (eip,List.map (fun x ->x, SITE_NORMAL ) ((*List.sort_uniq compare*) bbs), name,n)  in
        List.map (fun (eip,n) -> func_convert (find_func_eip_no_unloop eip funcs) n) ((eip,0)::funcs_called)
        
        

    let create_arc_bbs bbst n = 
        let bbs = List.map (fun (bb,_t) -> bb) bbst in
        (*let first_bb = List.hd bbs in*)
        let bbs = List.tl bbs in
        let ret = ref [] in
        let () = List.iter (fun x ->
                    List.iter (fun y ->
                        ret := (x.addr_bb,n,y.addr_bb,n)::(!ret)
                    ) x.sons
        ) bbs in
        !ret
            
    let update_type_func list_func sites =
        let update (eip,bbst,name,n) =
            let bbst = List.map (fun (bb,t) ->
                try
                    let (*(_,_,_),t_*)m = List.find_all ( fun (((y,_),_,n_),_t_) ->
                        List.exists (fun x -> x.addr = y && n = n_) bb.nodes
                    ) sites
                    in
                    (* Order of priority when node is multiple types *) 
                    let t_ = if (List.exists (fun (_,t) -> t = SITE_DF) m) then SITE_DF 
                             else if (List.exists (fun (_,t) -> t = SITE_USE) m) then SITE_USE
                             else if (List.exists (fun (_,t) -> t = SITE_FREE) m) then SITE_FREE
                             else if (List.exists (fun (_,t) -> t = SITE_ALLOC) m) then SITE_ALLOC
                             else SITE_NORMAL
                    in
                    (bb,site_to_subgraph_type t_)
                with
                    _ -> (bb,site_to_subgraph_type t)
            ) bbst in
            (eip,bbst,name,n)
        in 
        List.map update list_func

    let update_type_subgraph list_funcs eip eip_alloc alloc_free free_use =
        let update (_eip_,bbst,name,n) =
            let bbst = List.map (fun (bb,t) ->
                let t_ =
                    if (t = NODE_ALLOC || t = NODE_FREE || t = NODE_USE || t = NODE_DF) then t
                    else if ((Ir_v.get_real_addr bb.addr_bb) = fst eip && n = snd eip) then NODE_EIP 
                    else if (List.exists (fun a -> (Ir_v.get_real_addr bb.addr_bb) = fst a && n = snd a) eip_alloc) then NODE_EIP_ALLOC
                    else if (List.exists (fun a -> (Ir_v.get_real_addr bb.addr_bb) = fst a && n = snd a) (List.concat alloc_free)) then NODE_ALLOC_FREE
                    else if (List.exists (fun a -> (Ir_v.get_real_addr bb.addr_bb) = fst a && n = snd a) (List.concat (List.concat( free_use)))) then NODE_FREE_USE
                    else t
               in (bb,t_)
             ) bbst in
             (eip,bbst,name,n)
        in
        List.map update list_funcs
            
    let update_arcs list_arcs calls ret flow_graph_disjoint =
        let udpate_call_ori_sons_to_ret l r = 
            List.map (fun (ori_addr, ori_n, dst_addr, dst_n) -> 
                        try 
                            let (_,_,(ret_addr,_),ret_n) = List.find (fun ((ori_ret,_ori_ret_unloop), ori_ret_n, (_ret_addr,_ret_addr_unloop),_ret_n) -> ori_addr/0x100 = ori_ret/0x100 && ori_n = ori_ret_n) r in
                            (ret_addr,ret_n,dst_addr,dst_n)
                        with Not_found -> (ori_addr, ori_n, dst_addr, dst_n)
            ) l
        in
        let add_call_ori_dst l c = 
            l@(List.map (fun ((bb_ori,_bb_ori_unloop),bb_dst,n_ori,n_dst) -> (bb_ori,n_ori,bb_dst,n_dst) ) c)
        in
        let list_arcs = if( not flow_graph_disjoint) then udpate_call_ori_sons_to_ret list_arcs ret else list_arcs in
        let list_arc = add_call_ori_dst list_arcs calls in
        list_arc

    let rec explore_desc addr n arcs ret = 
        try
            let new_sons = Hashtbl.find arcs (addr,n) in
            let new_sons = List.filter ( fun (a,b)  -> not (List.exists (fun (c,d) -> a=c && b=d) (!ret))) new_sons in
            let () = ret := (!ret)@(new_sons) in
            List.iter (fun (a,b) -> explore_desc a b arcs ret) new_sons
        with
            Not_found -> () 

    let list_to_hash l h =
        List.iter (fun (addr_ori,n_ori,addr_dst,n_dst)  ->
            let addr_ori,addr_dst = addr_ori/0x100,addr_dst/0x100 in
            let prev = try Hashtbl.find h (addr_ori,n_ori) with Not_found -> [] in
            Hashtbl.replace h (addr_ori,n_ori) ((addr_dst,n_dst)::prev)
        ) l

    let list_to_hash_invert l h =
        List.iter (fun (addr_ori,n_ori,addr_dst,n_dst)  ->
            let addr_ori,addr_dst = addr_ori/0x100,addr_dst/0x100 in
            let prev = try Hashtbl.find h (addr_dst,n_dst) with Not_found -> [] in
            Hashtbl.replace h (addr_dst,n_dst) ((addr_ori,n_ori)::prev)
        ) l

    let find_nodes_between addr n addr_site n_site arcs arcs_invert =
        let ori_dst = ref [] in
        let dst_ori = ref [] in
        let () = explore_desc addr n arcs ori_dst in
        let () = explore_desc (addr_site) n_site arcs_invert dst_ori in
        List.filter (fun (a,b) -> (List.exists (fun (c,d) -> a=c && b=d ) (!dst_ori) )) (!ori_dst)
        
    let find_bb_addr (((addr,_it),f,n),_t) funcs =
        try
            let (_,bbs,_) = find_func_name_no_unloop f funcs in
            let bb = List.find (fun bb -> List.exists (fun x -> x.addr=addr) bb.nodes) bbs in
            ((Ir_v.get_real_addr bb.addr_bb),n)
        with
            Not_found -> let () = Printf.printf "Not found ori bb %x %s\n" addr f in (0,0)

(*
    let get_type_node bb l_event eip call_stack =
        let same_event (((n,_),_,_),_) bb = List.exists (fun x -> x.addr/0x100 = n/0x100) bb.nodes in
        let rec same_call_stack events call_stack = 
            match events,call_stack with
            | [],[] -> true
            | (((n,_),_,_),_)::events,addr::call_stack -> if(addr = n) then same_call_stack events call_stack
                                                          else false
            | [],_ | _,[] -> false
        in
        if ((Ir_v.get_real_addr bb.addr_bb) = eip && ((List.length call_stack)=1)) then NODE_EIP 
        else
        let t =
            try
                let events = List.find_all (fun l -> same_event (List.hd l) bb && same_call_stack (List.tl l) call_stack) l_event in
                let m = List.map (fun x -> List.hd x) events in
                (* in case of multipe types *)
                if (List.exists (fun (_,t) -> t = SITE_DF) m) then SITE_DF 
                else if (List.exists (fun (_,t) -> t = SITE_USE) m) then SITE_USE
                else if (List.exists (fun (_,t) -> t = SITE_FREE) m) then SITE_FREE
                else if (List.exists (fun (_,t) -> t = SITE_ALLOC) m) then SITE_ALLOC
                else SITE_NORMAL 
            with Not_found -> SITE_NORMAL
        in site_to_subgraph_type t
 *)

    (* calls : (bb_ori,bb_it) , bb_dst , ori_n, dst_n *)
    let get_call bb call_id calls =
        try
            Some (List.find (fun ((bb_ori,_),_,ori_n,_) -> ori_n = call_id && bb_ori = bb.addr_bb) calls)
        with
            Not_found -> None
 
    (* ret : (bb_ori,bb_it) ,ori_n , (bb_dst,bb_it) , dst_n *)
    let get_ret bb call_id rets =
        try
            Some (List.find_all (fun ((bb_ori,_),ori_n,_,_,_) -> ori_n = call_id && bb_ori = bb.addr_bb) rets)
        with
            Not_found -> None      
 
    let get_func eip funcs =
        try 
            find_func_eip_no_unloop eip funcs
        with
            Not_found -> failwith (Printf.sprintf "Get func not found %x\n" eip)
   
    let export_ret_joint bb call_id id_node rets oc print_arc = 
        let ret = get_ret bb call_id rets in
        match ret with
        | Some l -> List.iter (fun (_,_,(ret_addr,_),ret_id,_) -> List.iter (fun x -> print_arc oc (ret_addr, ret_id ,x.addr_bb, call_id) id_node) bb.sons) l
        | None -> ()

    let export_call bb call_id id_node calls oc print_arc print_group call_stack funcs explore_bb disjoint =
        let call = get_call bb call_id calls in
        match call with         
        | None ->
            begin 
            try List.iter (fun x -> print_arc oc (bb.addr_bb,call_id,x.addr_bb,call_id) id_node) bb.sons
            with Not_found -> failwith "Error "
            end
        | Some (_,dst_eip,_,func_called_id) -> let () = print_arc oc (bb.addr_bb, call_id, dst_eip,func_called_id) id_node in
                                               let (func_called_eip,bbs,func_called_name) = get_func (dst_eip/0x100) funcs in
                                               let () = print_group oc bbs func_called_id in
                                               let () = if(disjoint) then List.iter (fun x -> print_arc oc (bb.addr_bb,call_id,x.addr_bb,call_id) id_node) bb.sons in
                                               let last_node_addr = (List.hd (List.rev bb.nodes)).addr in
                                               explore_bb func_called_eip func_called_id func_called_name (last_node_addr::call_stack) 

     let merge_types_backward t1 t2 = match t1,t2 with
        | a,b when a=b -> None
        | NODE_OUT,_ | _, NODE_OUT -> Some NODE_OUT
        | NODE_EIP,_| _, NODE_EIP -> Some NODE_EIP
        | NODE_EIP_ALLOC, NODE_EIP_ALLOC-> Some NODE_EIP_ALLOC
        | NODE_ALLOC,_ | _, NODE_ALLOC -> Some NODE_ALLOC
        | NODE_ALLOC_FREE,_ | _, NODE_ALLOC_FREE -> Some NODE_ALLOC_FREE
        | NODE_FREE,_ | _,NODE_FREE -> Some NODE_FREE
        | NODE_FREE_USE,_ | _,NODE_FREE_USE -> Some NODE_FREE_USE
        | NODE_USE,_ | _ , NODE_USE -> Some NODE_USE
        | NODE_DF,_ | _,NODE_DF -> Some NODE_DF

     let merge_types_forward t1 t2 = match t1,t2 with
        | a,b when a=b -> None
        | NODE_DF,_ | _,NODE_DF -> Some NODE_DF
        | NODE_USE,_ | _ , NODE_USE -> Some NODE_USE
        | NODE_FREE,_ | _,NODE_FREE -> Some NODE_FREE
        | NODE_FREE_USE,_ | _,NODE_FREE_USE -> Some NODE_FREE_USE
        | NODE_ALLOC_FREE,_ | _, NODE_ALLOC_FREE -> Some NODE_ALLOC_FREE
        | NODE_ALLOC,_ | _, NODE_ALLOC -> Some NODE_ALLOC
        | NODE_EIP_ALLOC, NODE_EIP_ALLOC-> Some NODE_EIP_ALLOC
        | NODE_EIP,_| _, NODE_EIP -> Some NODE_EIP
        | NODE_OUT,_ | _, NODE_OUT -> Some NODE_OUT

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

    let explore_backward l_event funcs rets =
        let type_tbl = Hashtbl.create 2000 in
        let explore_ret bb call_n rets f t = 
                let ret = get_ret bb call_n rets in
                match ret with
                | Some l -> List.iter (fun (_,_,(ret_addr,_),ret_id,func_ret_name) -> f (find_node_from_name ret_addr func_ret_name funcs) t ret_id) l
                | None -> ()
        in
        let rec explore n t call_n =
                let addr = n.addr_bb in
                let t = 
                        try
                                let prev_t = Hashtbl.find type_tbl (addr,call_n) in
                                merge_types_backward t prev_t 
                        with Not_found -> Some t
                in
                match t with
                | Some t -> 
                        let () = Hashtbl.replace type_tbl (addr,call_n) t in
                        let t = decrease_subgraph_type t in 
                        let () = explore_ret n call_n rets explore t in
                        List.iter (fun x -> explore x t call_n) n.fathers
                | None -> () (* do not explore if t not changing *)
        in     
        let extract event f =
                let node = List.hd event in
                let (((addr,_),func_name,call_n),t) = node in
                f (find_node_from_name addr func_name funcs) ((site_to_subgraph_type t)) call_n
        in
        let () = List.iter (fun  x -> extract x explore ) l_event in
        type_tbl


    let explore_forward eip l_event funcs calls =
        let type_tbl = Hashtbl.create 2000 in
        let find_node addr funcs = 
                try
                        let eip,_,_ = find_func_eip_no_unloop addr funcs in eip
                with Not_found -> failwith (Printf.sprintf "Func not found %x \n" addr)
(*                match fiind addr bbs with
                | Some n -> n
                | None -> failwith (Printf.sprintf "Error during backward exploration %x %s\n" addr name)*)
        in
        let explore_call bb call_n calls f t = 
                let call = get_call bb call_n calls in
                match call with
                | Some (_,dst,_,dst_id) -> f (find_node (Ir_v.get_real_addr dst) funcs) t dst_id
                | None -> ()
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
                        let () = explore_call n call_n calls explore t in
                        List.iter (fun x -> explore x t call_n) n.sons
                | None -> () (* do not explore if t not changing *)
        in     
        let eip = find_node eip funcs in
        let () = explore eip NODE_EIP 0 in
        let () = Printf.printf "Size %d\n" (Hashtbl.length type_tbl) in
        type_tbl

    let export_flow_graph_uaf filename print_begin print_end print_node print_arc print_group type_tbl_backward type_tbl_forward eip calls funcs rets flow_graph_disjoint =
        let merge_type f b = match f,b with
                | a,b when a=b -> a
                | NODE_OUT,_ | _,NODE_OUT -> NODE_OUT
                | NODE_EIP,_ | _,NODE_EIP-> NODE_EIP
                | NODE_FREE,_ | _,NODE_FREE -> NODE_FREE
                | NODE_ALLOC,_ | _,NODE_ALLOC -> NODE_ALLOC
                | NODE_USE,_ -> NODE_USE
                | NODE_DF,_ -> NODE_DF
                | NODE_FREE_USE,NODE_ALLOC_FREE -> NODE_FREE_USE
                | _,NODE_USE | _ ,NODE_DF | NODE_EIP_ALLOC,_ | NODE_ALLOC_FREE,_ | _ , NODE_EIP_ALLOC | NODE_FREE_USE,_  -> NODE_OUT
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
                (*let t_forward = get_type_node bb l_event eip call_stack in*)
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
(*        let max_call_id = ref 0 in*)
        let rec explore_bb bb call_id func_name call_stack =
            if (Hashtbl.mem bb_saw (bb.addr_bb,call_id)) then ()
            else
                let () = Hashtbl.add bb_saw (bb.addr_bb,call_id) true in
                let t = NODE_OUT in
                let () = print_node oc (bb,t) func_name call_id id_node in
                let () = if(not flow_graph_disjoint) then export_ret_joint bb call_id id_node rets oc print_arc in
                let () = export_call bb call_id id_node calls oc print_arc print_group call_stack funcs explore_bb flow_graph_disjoint in
                List.iter (fun x -> explore_bb x call_id func_name call_stack) bb.sons
        in
        let eip,bbs,name = get_func eip funcs in
        let () = print_group oc bbs 0 in
        let () = explore_bb eip 0 name [eip.addr_bb] in
        let () = print_end oc  in
        close_out oc 


    let print_sg dir_output eip calls list_funcs ret flow_graph_gml flow_graph_dot flow_graph_disjoint =
        if (Hashtbl.length sg_uaf) == 0 then ()
        else
        let () =
        try 
            Unix.mkdir dir_output 0o777 
        with
            _ -> ()
        in
        let sg_uaf_by_alloc = ((Hashtbl.create 100) : ((int*Absenv_v.chunk_t  ,  ( ((site*site_type) list *  (((site*site_type) list) list) * (((site*site_type) list) list)) ) list ) Hashtbl.t ))  in
        (* first ordone result by alloc, not by free *)
        let () =
            Hashtbl.iter 
                (fun ((chunk_id,chunk_type),free) (alloc,use) ->
                    let key = chunk_id,chunk_type in
                    try
                        let elems=Hashtbl.find sg_uaf_by_alloc key in
                        Hashtbl.replace sg_uaf_by_alloc key ((alloc,free,use)::elems)
                    with
                    Not_found -> Hashtbl.add sg_uaf_by_alloc key [alloc,free,use]
                ) sg_uaf in
        let () = Printf.printf "Results, uaf found : \n\n" in
        Hashtbl.iter 
            (fun (chunk_id,chunk_type) elems -> 
                let str = Absenv_v.pp_chunk_t chunk_type in
                let n = ref 0 in
                List.iter (fun (alloc,free,use) ->
                        let l_event =(alloc::free@use) in
                        let type_tbl_backward = explore_backward l_event list_funcs ret in
                        let type_tbl_forward = explore_forward eip l_event list_funcs calls in
                        let () = export_call_graph_uaf (Printf.sprintf "%s/uaf-%s%d-%d.dot" dir_output str chunk_id !n)  print_begin_dot print_end_dot print_site_dot print_site_arc_dot alloc free use in
                        let () = if (flow_graph_dot) then   
                            let () = export_flow_graph_uaf (Printf.sprintf "%s/uaf-%s%d-%d-details.dot" dir_output str chunk_id !n) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot type_tbl_backward type_tbl_forward eip calls list_funcs ret false  
                            in if(flow_graph_disjoint) then
                                    export_flow_graph_uaf (Printf.sprintf "%s/uaf-%s%d-%d-details-disjoint.dot" dir_output str chunk_id !n) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot type_tbl_backward type_tbl_forward eip calls list_funcs ret true 
                        in
                        let () = if (flow_graph_gml) then
                             export_flow_graph_uaf (Printf.sprintf "%s/uaf-%s%d-%d-details.gml" dir_output str chunk_id !n) print_begin_gml print_end_gml print_bbt_gml print_bbt_arc_gml print_group_gml type_tbl_backward type_tbl_forward eip calls list_funcs ret false
                        in n:=!n+1 
                ) elems
            ) sg_uaf_by_alloc ;;


    let print_g dir_output eip calls list_funcs ret flow_graph_gml flow_graph_dot flow_graph_disjoint =
        let () = Hashtbl.clear already_seen_bb_gml in
        let () = Hashtbl.clear already_seen_arc_gml in
        let () = Hashtbl.clear already_seen_bb_dot in
        let () = Hashtbl.clear already_seen_arc_dot in
        let () = if (flow_graph_dot) then   
            let () = export_flow_graph (Printf.sprintf "%s/graph-details.dot" dir_output ) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot eip calls list_funcs ret false  
            in if(flow_graph_disjoint) then
             export_flow_graph (Printf.sprintf "%s/graph-details-disjoint.dot" dir_output ) print_begin_dot print_end_dot print_bbt_dot print_bbt_arc_dot print_group_dot eip calls list_funcs ret true 
        in
        let () = if (flow_graph_gml) then
            export_flow_graph (Printf.sprintf "%s/graph-details.gml" dir_output ) print_begin_gml print_end_gml print_bbt_gml print_bbt_arc_gml print_group_gml  eip calls list_funcs ret false in
        ()
 
    let launch_supercallgraph_analysis func_name list_funcs dir_output max_depth verbose show_call flow_graph flow_graph_dot flow_graph_gml flow_graph_disjoint parsed_func =
        let () = Hashtbl.clear call_stack_tbl in
        let () = Stack.clear call_stack in
        let () = Hashtbl.add call_stack_tbl (0) ([(0,0)]) in
        let () = Stack.push (0,0) call_stack in
        let count = ref 1 in
        let count_reil_inst = ref 0 in
        try 
            let (eip,bbs,name) = find_func_name func_name list_funcs in
            let () = List.iter (fun x -> init_value x ) bbs in
            let () = try
                let () = explore_graph (eip,bbs,name)  list_funcs ([""]) count max_depth count_reil_inst verbose show_call 0 0 0 flow_graph parsed_func in
                let () = print_g dir_output (eip.addr_bb/0x100) (!saved_call) list_funcs (!saved_ret_call) flow_graph_dot flow_graph_gml flow_graph_disjoint in
                Printf.printf "Number of func from %s : %d and %d REIL inst\n" func_name (!count) (!count_reil_inst)
            with
                MAX_EXPLORE -> Printf.printf "Number of func from %s : MAX\n" func_name
            in
          (*  let _ = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in*)
            (!count)
        with
            | Not_found -> 
                let () = Printf.printf "Func %s : error (func not found)\n" func_name in
                (*ilet () = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in*)
                (!count)
            | NOT_RET (_vsa,_ha,_hf,_score) -> 
                let () = if(verbose) then Printf.printf "Not ret\n" in
                let () = Printf.printf "Number of func from %s %d\n" func_name (!count) in
            (*    let () = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in*)
                (!count) 
            | NOT_RET_NOT_LEAF -> 
           (*     let () = if(print_graph) then print_graph_dot dir_output (!saved_values) (!saved_call) in*)
                (!count) 

    let launch_value_analysis func_name list_funcs list_malloc list_free dir_output verbose show_values show_call show_free flow_graph flow_graph_dot flow_graph_gml flow_graph_disjoint parsed_func =
        try
            let () = Hashtbl.clear call_stack_tbl in
            let () = Stack.clear call_stack in
            let () = Hashtbl.add call_stack_tbl (0) ([(0,0)]) in
            let () = Stack.push (0,0) call_stack in
            let (eip,bbs,name) = find_func_name func_name list_funcs in
            let () = List.iter (fun x -> init_value x ) bbs  in
            let _ = value_analysis (eip,bbs,name)  list_funcs list_malloc list_free ([(eip.addr_bb,0),name,0]) dir_output verbose show_values show_call show_free  0 0 0 flow_graph parsed_func in
            let () = check_uaf bbs [(eip.addr_bb,0),name,!current_call] (0) in
            print_sg dir_output (eip.addr_bb/0x100) (!saved_call) list_funcs (!saved_ret_call) flow_graph_dot flow_graph_gml flow_graph_disjoint
        with
            | Not_found -> Printf.printf "Func %s : error (not found)\n" func_name
            | NOT_RET (_vsa,_ha,_hf,_score) -> ()
            | NOT_RET_NOT_LEAF -> ()

end;;

