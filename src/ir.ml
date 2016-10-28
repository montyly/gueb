open Absenvgenerique
open Program_piqi

module type IR = functor (Absenv_v : AbsEnvGenerique) ->
sig 
    type ir_stmt
    val print_stmt : ir_stmt -> string
    val print_type : ir_stmt -> string
    val parse_func_protobuf :  Program_piqi.function_-> Gueb_type.basic_block list * Gueb_type.edge list * int * int  * (ir_stmt*int*int) list * (int list * int list)
    (*val parse_func_protobuf :  Program_piqi.function_-> Gueb_type.basic_block list * Gueb_type.edge list * Gueb_type.addr * int  * (ir_stmt*int*int) list * (int list * int list)*)
    val parse_func_protobuf_number_unloop :  Program_piqi.function_-> int                    (* bbs,connection_unfilter,eip, number_unloop,nodes,call_retn)  *)
    val get_real_addr : int -> int

    val get_value_jump : ir_stmt -> Absenv_v.absenv -> int option
    val get_first_arg: ir_stmt -> int option
    val function_transfer : ir_stmt -> Absenv_v.absenv -> Gueb_type.addr -> string -> int -> Gueb_type.call_stack -> Absenv_v.absenv
    val access_heap : ir_stmt -> Absenv_v.absenv -> Absenv_v.he list
    val check_uaf : (ir_stmt*Absenv_v.absenv*Gueb_type.addr) -> (ir_stmt*Absenv_v.he list *Gueb_type.addr) option 
    val score_heap_use : (ir_stmt*Absenv_v.absenv) -> bool  (*TODO use with hashmap *)
    
end ;;



