module My_Graph :
  functor
    (Absenv_v : Absenvgenerique.AbsEnvGenerique) (Ir_a : Ir.IR) (Stubfunc_a : Stubfunc.Stubfunc) (Uaf_a : Uafgenerique.UafGenerique) ->
    sig
      val export_func_unloop :
        Program_piqi.Program_piqi.function_ list -> string -> unit
      val set_irreducible_loop : unit -> unit
      val set_depth : int -> unit
      val set_size  : int -> unit
      val set_max_ins  : int -> unit
      val launch_supercallgraph_analysis :
        string ->
        Program_piqi.Program_piqi.function_ list ->
        string ->
        bool -> bool -> bool -> bool -> bool -> bool -> 'a -> int
      val launch_value_analysis :
        string ->
        Program_piqi.Program_piqi.function_ list ->
        int list ->
        int list ->
        bool ->
        string ->
        bool ->
        bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a -> unit
      val end_analysis : unit -> unit
    end
