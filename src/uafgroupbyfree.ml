open Absenvgenerique
open Uafgenerique

module UafGroupByFree (Absenv_v : AbsEnvGenerique) =
struct

        type site_type = Uafgenerique.site_type

    	(* site : (addr,it) * func_name * call_n *)
	type site = Uafgenerique.site

        type tree_node = {
            site : site*site_type;
            mutable leafs : tree_node list;
        }

        (* On a list of site, add type, t for the last, SITE_NORMAL for others *)
        let add_type sites t = 
            let add_type_ ((addr,it),s,n) t = (((addr,it),s,n),t) in
            let head = List.hd sites in
            let head = add_type_ head t in
            let tl = List.tl sites in
            let tl = List.map (fun x -> add_type_ x SITE_NORMAL) tl in
            head::tl

        (* Hashtbl that contains result 
        * form :
        *  (id,size)  *   free sites  * malloc site * use sites
        * key is chunk * free site, because from a same malloc, different free that lead to different uaf 
        * *)
        let sg_uaf = ((Hashtbl.create 100) : (( (int*Absenv_v.chunk_t) * (((site*site_type) list) list)   , ((site*site_type) list) *   (((site*site_type) list) list) ) Hashtbl.t )) 

        let is_uaf () = (Hashtbl.length sg_uaf) > 0

        let clear () = Hashtbl.clear sg_uaf

        let end_analysis () = ()

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

        let get_sg_uaf_by_alloc () =
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
                        ) sg_uaf 
                in sg_uaf_by_alloc

        let export_tree_uaf filename print_begin print_end print_node print_arc (alloc:(site*site_type) list) (free:((site*site_type) list) list) (use:((site*site_type) list) list)  =
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
end

