type site_type =
        | SITE_NORMAL
        | SITE_ALLOC
        | SITE_FREE
        | SITE_USE
        | SITE_DF

type site = (int * int) * string * int

(* do not compare call_n *)
let equal_site s1 s2 =
        let (((addr1,it1),_,_),t1) = s1 in
        let (((addr2,it2),_,_),t2) = s2 in
        (&&) ( (&&) (addr1 = addr2) (it1 = it2)) (t1 = t2)
   


(* On a list of site, add type, t for the last, SITE_NORMAL for others *)
let add_type sites t = 
    let add_type_ ((addr,it),s,n) t = (((addr,it),s,n),t) in
    let head = List.hd sites in
    let head = add_type_ head t in
    let tl = List.tl sites in
    let tl = List.map (fun x -> add_type_ x SITE_NORMAL) tl in
    head::tl

let remove_df (free:((site*site_type) list) list) (use:((site*site_type) list) list) =
    let use = List.map (fun x -> List.hd x) use in
    let df = List.find_all (fun (_,t) -> t = SITE_DF) use in
    let new_free  = List.filter (fun x -> 
                let s1 = List.hd x in
                let is_inside = List.fold_left (fun acc s2 ->
                        let (((addr1,it1),_,n1),_) = s1 in
                        let (((addr2,it2),_,n2),_) = s2 in
                        let is_eq =(&&)  ( (&&) (addr1 = addr2) (it1 = it2) ) (n1 = n2) in
                        (||) is_eq acc
                ) false df
                in
                not is_inside) free
    in 
    new_free


module type UafGenerique =  functor (Absenv_v : Absenvgenerique.AbsEnvGenerique) ->
sig

      val is_uaf : unit -> bool
      val clear : unit -> unit
      val end_analysis : unit -> unit
      val add_uaf :
        ?t:site_type ->
        Absenv_v.he -> ((int * int) * string * int) list list -> unit
      val get_sg_uaf_by_alloc :
        unit ->
        (int * Absenv_v.chunk_t,
         ((site * site_type) list * (site * site_type) list list *
          (site * site_type) list list)
         list)
        Hashtbl.t
      val export_tree_uaf :
        string ->
        (out_channel -> unit) ->
        (out_channel -> unit) ->
        (out_channel -> site * site_type -> unit) ->
        (out_channel -> site * site_type -> (site * site_type) list -> unit) ->
        (site * site_type) list ->
        (site * site_type) list list -> (site * site_type) list list -> unit
end

