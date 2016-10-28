exception TOP_VAL
exception TOP_OFFSETS
exception ERROR
module type AbsEnvGenerique =
  sig
    type he
    type absenv
    type valuesSet
    type nameVal
    type chunk_t
    val initAbsenEnv : unit -> absenv
    val init_first : absenv
    val init_vs_chunk :
      int -> chunk_t -> Gueb_type.call_stack -> valuesSet
    val init_chunk :
      int -> chunk_t -> Gueb_type.call_stack -> he
    val new_init_memory :
      int ref -> Gueb_type.call_stack -> valuesSet
    val classical_chunk : unit -> chunk_t
    val create_cst : int -> valuesSet
(*    val merge_he : he list -> he list -> he list*)
(*    val merge_alloc_free_conservatif : he list -> he list -> he list*)
    val merge_values_two : valuesSet -> valuesSet -> valuesSet
    val merge : absenv -> absenv -> absenv
    val update : absenv -> absenv -> absenv
    val get_integer_values : valuesSet -> int option list
    val get_value : absenv -> nameVal -> valuesSet
    val get_value_create :
      absenv ->
      nameVal ->
      Gueb_type.call_stack -> absenv * valuesSet
    val set_value : absenv -> nameVal -> valuesSet -> absenv
    val get_chunk_key : he -> int * chunk_t
    val get_chunk_states :
      he ->
      Gueb_type.call_stack *
      Gueb_type.call_stack list
    val get_value_string : absenv -> string -> valuesSet
    val get_value_string_create :
      absenv ->
      string ->
      Gueb_type.call_stack -> absenv * valuesSet
    val set_value_string : absenv -> string -> valuesSet -> absenv
    val string_to_name : string -> nameVal
    val values_to_names : valuesSet -> nameVal list
    val add : valuesSet -> valuesSet -> valuesSet
    val sub : valuesSet -> valuesSet -> valuesSet
    val mul : valuesSet -> valuesSet -> valuesSet
    val div : valuesSet -> valuesSet -> valuesSet
    val and_op : valuesSet -> valuesSet -> valuesSet
    val or_op : valuesSet -> valuesSet -> valuesSet
    val xor_op : valuesSet -> valuesSet -> valuesSet
    val modulo : valuesSet -> valuesSet -> valuesSet
    val bsh : valuesSet -> valuesSet -> valuesSet
    val is_zero : valuesSet -> valuesSet
    val pp_name : nameVal -> string
    val pp_valuesset : valuesSet -> string
    val pp_absenvs : absenv -> string
    val pp_he : he list -> string
    val pp_chunk : he -> string
    val pp_chunk_t : chunk_t -> string
    val pp_state : Gueb_type.call_stack -> string
    val check_uaf : absenv -> valuesSet -> he list
    val check_df : absenv -> valuesSet -> he list
    val free :
      absenv ->
      valuesSet ->
      Gueb_type.call_stack -> bool -> unit 
    val filter_values : valuesSet list -> valuesSet
    val filter_esp_ebp : absenv -> bool -> bool -> absenv
    val filter_he : absenv-> absenv
    val restore_stack_frame : absenv -> absenv -> absenv
    val names_to_he : nameVal list -> he list
    val check_use_heap : nameVal list -> bool
    val retn_not_analyse : unit -> valuesSet
    val top_value : unit -> valuesSet
    val free_stack : absenv -> Gueb_type.call_stack -> absenv
    val clean_vsa : absenv -> unit
    val restore_esp : absenv -> absenv
    val malloc_ret : absenv -> Gueb_type.call_stack -> absenv
    val malloc_arg : absenv -> Gueb_type.call_stack -> int -> absenv
  end
