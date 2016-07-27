type site_type = SITE_NORMAL | SITE_ALLOC | SITE_FREE | SITE_USE | SITE_DF
type site = (int * int) * string * int
module type UafGenerique =
  functor (Absenv_v : Absenvgenerique.AbsEnvGenerique) ->
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
