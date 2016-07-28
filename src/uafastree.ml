open Uafgenerique

exception NOT_EQUAL

type tree_node = {
    site : site*site_type;
    mutable leafs : tree_node list;
}

let rec equal_tree t1 t2 =
        if(not ( equal_site t1.site t2.site)) then false
        else if( (List.length t1.leafs) <> (List.length t2.leafs)) then false
        else if (List.length t1.leafs) = 0 then true
        else
        try
               List.iter (fun v1 ->
                        if( not( List.fold_left (fun acc2 v2 -> (||) (equal_tree v1 v2) acc2) false t2.leafs )) then raise NOT_EQUAL
               ) t1.leafs;
               true
        with
                NOT_EQUAL -> false
        
module HashTree = Hashtbl.Make (struct
        type t = tree_node
        let equal t1 t2 = equal_tree t1 t2
        let hash t =  
                let (_,func_name,_),_ = t.site in 
                Hashtbl.hash func_name
end)

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

let alloc_free_to_tree (alloc:(site*site_type) list) (free:((site*site_type) list) list)  =
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
    let rec remove_heads l =
        if(List.length(l.leafs) = 1) then remove_heads (List.hd l.leafs)
        else 
                let (_addr,func_name,_n),t = l.site in
                {l with site = (((0,0),func_name,0),t)}
    in
    let first_tree = site_to_tree alloc in
    let () = List.iter (fun x -> add_sites_to_tree first_tree (List.hd x) (List.tl x)) free in
    remove_heads first_tree


