module My_Graph :
  functor
    (Absenv_v : Absenvgenerique.AbsEnvGenerique) (Ir_a : Ir.IR) (Stubfunc_a : Stubfunc.Stubfunc) (Uaf_a : Uafgenerique.UafGenerique) ->
    sig
      val launch_supercallgraph_analysis :
        string ->
        Program_piqi.Program_piqi.function_ list ->
        string ->
        int -> bool -> bool -> bool -> bool -> bool -> bool -> 'a -> int
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
