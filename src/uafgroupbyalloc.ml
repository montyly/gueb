open Absenvgenerique
open Uafgenerique
open Uafastree

module UafGroupByAlloc (Absenv_v : AbsEnvGenerique) =
struct

        type site_type = Uafgenerique.site_type

    	(* site : (addr,it) * func_name * call_n *)
	type site = Uafgenerique.site

        (* Hashtbl that contains result 
        * form :
        *  (id,size)  *   free sites  * malloc site * use sites
        * key is chunk * free site, because from a same malloc, different free that lead to different uaf 
        * *)
        let sg_uaf = ((Hashtbl.create 100) : (( (int*Absenv_v.chunk_t)  , ((site*site_type) list) * (((site*site_type) list) list) *  (((site*site_type) list) list) ) Hashtbl.t )) 

        let merge_tree = HashTree.create 100

        let is_uaf () = (Hashtbl.length sg_uaf) > 0

        let clear () = Hashtbl.clear sg_uaf

        let end_analysis () = 
                let count = ref 0 in
                HashTree.iter (fun _k v ->
                        Printf.printf "\n####################\nSame : \n";
                        List.iter (fun x -> count:=(!count) +1 ; Printf.printf "%s\n" x)  v ;
                ) merge_tree;
                Printf.printf "\n%d different root causes (on %d detected)\n" (HashTree.length merge_tree) (!count)

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
            let key = Absenv_v.get_chunk_key c in
            try
                let alloc,free,use=Hashtbl.find sg_uaf key in
                let free = filter_list free c_free in
                let use = filter_list use state in
                Hashtbl.replace sg_uaf key (alloc,free,use)
            with
                Not_found -> Hashtbl.add sg_uaf key (c_alloc,c_free,state)

        let get_sg_uaf_by_alloc () =
                let sg_uaf_by_alloc = ((Hashtbl.create 100) : ((int*Absenv_v.chunk_t  ,  ( ((site*site_type) list *  (((site*site_type) list) list) * (((site*site_type) list) list)) ) list ) Hashtbl.t ))  in
                (* first ordone result by alloc, not by free *)
                let () =
                    Hashtbl.iter 
                        (fun ((chunk_id,chunk_type)) (alloc,free,use) ->
                            let key = chunk_id,chunk_type in
                            try
                                let elems=Hashtbl.find sg_uaf_by_alloc key in
                                Hashtbl.replace sg_uaf_by_alloc key ((alloc,free,use)::elems)
                            with
                            Not_found -> Hashtbl.add sg_uaf_by_alloc key [alloc,free,use]
                        ) sg_uaf 
                in sg_uaf_by_alloc

        let export_tree_uaf filename print_begin print_end print_node print_arc (alloc:(site*site_type) list) (free:((site*site_type) list) list) (use:((site*site_type) list) list)  =
            let oc = open_out filename in 
            let () = print_begin oc in
            let () = Printf.printf "Export %s\n" filename in
            let free = remove_df free use in
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
            let () = close_out oc in
            let tree = alloc_free_to_tree alloc free in
            try
                let prev = HashTree.find merge_tree tree in
                HashTree.replace merge_tree tree (filename::prev)
            with
                Not_found ->  HashTree.add merge_tree tree [filename];
            
end

