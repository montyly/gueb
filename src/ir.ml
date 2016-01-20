open Absenv;;
open Program_piqi;;
open Program_piqi;;

module type IR = functor (Absenv_v : AbsEnvGenerique) ->
sig 
    type ir_stmt
    val print_stmt : ir_stmt -> string
    val print_type : ir_stmt -> string
    val parse_nodes_file : string -> (ir_stmt*int*int) list
    val parse_bbs_file : string -> (int*(int list)) list
    val parse_connexions_file : string -> (int*int) list
    val parse_call_retn : string -> string -> (int list*int list)
    val parse_malloc_free : string -> string -> (int list*int list)
    val parse_not_load : string -> int list
    val parse_eip : string -> int
    val parse_number_unloop : string -> int
    val parse_func_protobuf :  Program_piqi.function_-> (int*(int list)) list * (int * int) list * int * int  * (ir_stmt*int*int) list * (int list * int list)
    val parse_func_protobuf_number_unloop :  Program_piqi.function_-> int                    (* bbs,connection_unfilter,eip, number_unloop,nodes,call_retn)  *)

    val get_value_jump : ir_stmt -> Absenv_v.absenv list -> int option
    val function_transfer : ir_stmt -> Absenv_v.absenv list -> Absenv_v.he list -> int ref -> (int*int) -> string -> int -> ((int*int)*string*int) list -> Absenv_v.absenv list
    val access_heap : ir_stmt -> Absenv_v.absenv list -> Absenv_v.he list
    val check_uaf : (ir_stmt*Absenv_v.absenv list*Absenv_v.he list*(int*int)) -> (ir_stmt*Absenv_v.he list *(int*int)) option 
    val score_heap_use : (ir_stmt*Absenv_v.absenv list) -> bool  (*TODO use with hashmap *)
    
end ;;


(*
 * Set of functions to read files
 *
 * *)
let read_lines_file filename = 
    let lines = ref [] in
    let chan = open_in filename in
    let () =
    try while true; do
        let new_line = input_line chan in
        lines := new_line :: !lines 
        done;  
    with End_of_file -> close_in chan in
    List.rev !lines ;;

let rec filter_none l r =
    match l with
    | [] -> r
    | hd::tl -> match hd with
                | Some a -> filter_none tl (a::r)
                | _ -> filter_none tl r;;

let read_file file_name pattern func =
    let lines=read_lines_file file_name in
    let lines_no_filter= List.map 
        (fun x -> 
            try
                Some (Scanf.sscanf x pattern func)
            with    
            End_of_file -> None    
       ) lines in
    filter_none lines_no_filter [] ;;

module REIL = functor (Absenv_v : AbsEnvGenerique ) ->
struct
 
(*
 * REIL 
 **)
type type_of_node_reil=
    | Sub
    | And
    | Xor
    | Str
    | Bsh
    | Jcc
    | Stm
    | Ldm   
    | Add
    | Nop
    | Mul
    | Mod
    | Div
    | Or
    | Bisz
    | Undef 
    | Unknow;;

type size_arg_reil=
 |OPERAND_SIZE_ADDRESS
 |OPERAND_SIZE_BYTE
 |OPERAND_SIZE_WORD
 |OPERAND_SIZE_DWORD
 |OPERAND_SIZE_EMPTY
 |OPERAND_SIZE_QWORD
 |OPERAND_SIZE_OWORD;;

type register_reil=
 |ESP
 |EBP
 |ECX
 |EDX
 |EBX
 |EDI
 |ESI
 |EIP
 |EAX
 |T0
 |T1
 |T2
 |T3
 |T4
 |T5
 |T6
 |T7
 |T8
 |T9
 |T10
 |T11
 |T12
 |T13
 |T14
 |T15
 |T16
 |T17
 |T18
 |T19
 |T20
 |T21
 |T22
 |T23
 |T24
 |T25
 |T26
 |T27
 |T28
 |T29
 |T30
 |T31
 |T32
 |T33
 |T34
 |T35
 |T36
 |T37
 |T38
 |T39
 |CF
 |OF
 |SF
 |DF
 |ZF
 |DSBASE
 |SSBASE;;

type arg_reil=
    | Empty 
    | Integer of  int
    | Register of register_reil
    | Sub_address  ;; (** jmp create by reil **)

type stmt_reil = 
{
    type_node : type_of_node_reil;
    arg0 : arg_reil;
    arg1 : arg_reil;
    arg2 : arg_reil;
}

let create_arg size_arg type_arg value_reil=
    match size_arg,type_arg,value_reil with
    | "OPERAND_SIZE_QWORD","INTEGER_LITERAL",_ -> Integer (int_of_float (float_of_string value_reil))
    | _,"INTEGER_LITERAL",_ ->  Integer (int_of_float (float_of_string value_reil)) 
    | _,_,"esp"->Register (ESP)
    | _,_,"ebp"->Register (EBP)
    | _,_,"ecx"->Register (ECX)
    | _,_,"edx"->Register (EDX)
    | _,_,"ebx"->Register (EBX)
    | _,_,"edi"->Register (EDI)
    | _,_,"esi"->Register (ESI)
    | _,_,"eip"->Register (EIP)
    | _,_,"eax"->Register (EAX)
    | _,_,"t0"->Register (T0)
    | _,_,"t1"->Register (T1)
    | _,_,"t2"->Register (T2)
    | _,_,"t3"->Register (T3)
    | _,_,"t4"->Register (T4)
    | _,_,"t5"->Register (T5)
    | _,_,"t6"->Register (T6)
    | _,_,"t7"->Register (T7)
    | _,_,"t8"->Register (T8)
    | _,_,"t9"->Register (T9)
    | _,_,"t10"->Register (T10)
    | _,_,"t11"->Register (T11)
    | _,_,"t12"->Register (T12)
    | _,_,"t13"->Register (T12)
    | _,_,"t14"->Register (T14)
    | _,_,"t15"->Register (T15)
    | _,_,"t16"->Register (T16)
    | _,_,"t17"->Register (T17)
    | _,_,"t18"->Register (T18)
    | _,_,"t19"->Register (T19)
    | _,_,"t20"->Register (T20)
    | _,_,"t21"->Register (T21)
    | _,_,"t22"->Register (T22)
    | _,_,"t23"->Register (T22)
    | _,_,"t24"->Register (T24)
    | _,_,"t25"->Register (T25)
    | _,_,"t26"->Register (T26)
    | _,_,"t27"->Register (T27)
    | _,_,"t28"->Register (T28)
    | _,_,"t29"->Register (T29)
    | _,_,"t30"->Register (T30)
    | _,_,"t31"->Register (T31)
    | _,_,"t32"->Register (T32)
    | _,_,"t33"->Register (T33)
    | _,_,"t34"->Register (T34)
    | _,_,"t35"->Register (T35)
    | _,_,"t36"->Register (T36)
    | _,_,"t37"->Register (T37)
    | _,_,"t38"->Register (T38)
    | _,_,"t39"->Register (T39)
    | _,_,"CF"->Register (CF)
    | _,_,"OF"->Register (OF)
    | _,_,"SF"->Register (SF)
    | _,_,"DF"->Register (DF)
    | _,_,"ZF"->Register (ZF)
    | _,_,"dsbase"-> Register (DSBASE)
    | _,_,"ssbase"-> Register (SSBASE)
    | _,_,"" -> Empty
    | _,_,_ -> Sub_address;;

(* 
 * REIL parsing
 * *)

let create_stmt_reil type_node s0 t0 v0 s1 t1 v1 s2 t2 v2={type_node=type_node;arg0=create_arg s0 t0 v0 ;arg1=create_arg s1 t1 v1;arg2=create_arg s2 t2 v2}

let create_connexion a b = (a,b);;

let create_bb a list_n=(a,list_n);;
    
let parse_reil addr type_node s0 t0 v0 s1 t1 v1 s2 t2 v2 = 
    match type_node with
    | "add" -> (create_stmt_reil Add s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0)
    | "and" -> (create_stmt_reil And s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "bisz" -> (create_stmt_reil Bisz s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "bsh" -> (create_stmt_reil Bsh s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "div" -> (create_stmt_reil Div s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "jcc" -> (create_stmt_reil Jcc s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "ldm" -> (create_stmt_reil Ldm s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "mod" -> (create_stmt_reil Mod s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "mul" -> (create_stmt_reil Mul s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "nop" -> (create_stmt_reil Nop s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "or" -> (create_stmt_reil Or s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "stm" -> (create_stmt_reil Stm s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "str" -> (create_stmt_reil Str s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "sub" -> (create_stmt_reil Sub s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "undef" -> (create_stmt_reil Undef s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "unkn" -> (create_stmt_reil Unknow s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | "xor" -> (create_stmt_reil Xor s0 t0 v0 s1 t1 v1 s2 t2 v2,addr,0) 
    | _ -> (create_stmt_reil Unknow s0 t0 v0 s1 t1 v1 s2 t2 v2 ,addr,0);;

   type ir_stmt=stmt_reil;;
   
(*
 * REIL pretty printing functions
 *
 * *) 
    let print_type s =
         match s.type_node with
        | Sub -> "sub"
        | And  -> "and"
        | Xor -> "xor"
        | Str -> "str"
        | Bsh -> "bsh"
        | Jcc -> "jcc"
        | Stm -> "stm"
        | Ldm -> "ldm"
        | Add -> "add"
        | Div -> "div"
        | Mul -> "mul"
        | Or -> "or"
        | Undef -> "undef"
        | Mod -> "mod"
        | Bisz -> "bisz"
        | _ -> "Unknow";;

    let print_reg reg=
        match reg with 
            | ESP -> "esp"
            | EBP -> "ebp"
            | ECX -> "ecx"
            | EDX -> "edx"
            | EBX -> "ebx"
            | EDI -> "edi"
            | ESI -> "esi"
            | EIP -> "eip"
            | EAX -> "eax"
            | T0 -> "t0"
            | T1 -> "t1"
            | T2 -> "t2"
            | T3 -> "t3"
            | T4 -> "t4"
            | T5 -> "t5"
            | T6 -> "t6"
            | T7 -> "t7"
            | T8 -> "t8"
            | T9 -> "t9"
            | T10 -> "t10"
            | T11 -> "t11"
            | T12 -> "t12"
            | T13 -> "t13"
            | T14 -> "t14"
            | T15 -> "t15"
            | T16 -> "t16"
            | T17 -> "t17"
            | T18 -> "t18"
            | T19 -> "t19"
            | T20 -> "t20"
            | T21 -> "t21"
            | T22 -> "t22"
            | T23 -> "t23"
            | T24 -> "t24"
            | T25 -> "t22"
            | T26 -> "t22"
            | T27 -> "t27"
            | T28 -> "t28"
            | T29 -> "t29"
            | T30 -> "t30"
            | T31 -> "t31"
            | T32 -> "t32"
            | T33 -> "t33"
            | T34 -> "t34"
            | T35 -> "t35"
            | T36 -> "t36"
            | T37 -> "t37"
            | T38 -> "t38"
            | T39 -> "t39"
            | CF -> "CF"
            | OF -> "OF"
            | SF -> "SF"
            | DF -> "DF"
            | ZF -> "ZF"
            | DSBASE -> "dsbase"
            | SSBASE -> "ssbase";;


    let print_args s =
        let print_size_arg si=
            ",-" 
        in
        let print_arg arg = 
            match arg with
                | Empty -> ",EMPTY, "
                | Integer a -> ",INTEGER_LITERAL,"^(string_of_int a)
                | Register reg -> ",REGISTER,"^(print_reg reg)
                | Sub_address ->  ",SUB_ADDRESS, "(** jmp create by reil **)
        in
        (print_size_arg s)^(print_arg s.arg0)^(print_size_arg s)^(print_arg s.arg1)^(print_size_arg s)^(print_arg s.arg2);;
            

    let print_stmt s = (print_type s)^(print_args s);;
        
    let parse_nodes_file file_name = read_file file_name "%d,%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^\n]" parse_reil;;
   
    let parse_bb addr s=
        let p s=Scanf.sscanf s "%d,%s" (fun x y -> (x,y))  in
        let rec f chaine = 
            try
                let (n,s)=p chaine in (n::(f s)) 
            with
                End_of_file -> []
        in (addr,(f s));;
 
    let parse_bbs_file bb_name = read_file  bb_name "%d:%s" parse_bb ;;
    
    let parse_connexions_file file_name = read_file file_name "%d,%d" create_connexion;;
    
    let parse_call_retn call retn =  (read_file call "%d" (fun x -> x) ,read_file retn "%d" (fun x -> x));;

    let parse_malloc_free malloc free =
        let m=read_file malloc "%d" (fun x -> x) in
        let f=read_file  free "%d" (fun x -> x)  in
        (m,f);;

    let parse_not_load not_load = read_file not_load "%x" (fun x->x);;
    
    (* TODO mieux faire *)
    let parse_eip eip = List.hd (read_file eip "%d" (fun x->x) );;

    let parse_number_unloop eip = List.hd (read_file  eip "%d" (fun x->x) );;

    let get_value_jump ir vsa =
        match ir.type_node with
        | Jcc -> (
            match ir.arg2 with
                | Integer a -> 
                    Some a
                | Register T1 -> 
                    let v = Absenv_v.get_value_string vsa "t1" in
                    let is = Absenv_v.get_integer_values v  in
                    if (List.length is) == 0 then None
                    else
                        List.hd is 
                | _ -> None                 
            )
        | _ -> None;;


    let arg_to_string a=
        match a with 
        | Register r -> print_reg r
        | Integer a -> string_of_int a
        | _ -> "uknw";;

    (*
     * transfer function
     * *)
    let function_transfer ir abs hf number_init addr func_name call_number backtrack = 
        let state = (addr,func_name,call_number)::backtrack in
        match ir.type_node with 
            (*
             * add a1,a2,a3
             * for each value a1/n
             *  for each value a2
             *      a3=a1+a2
             * *)            
            | Add -> 
                let arg0=arg_to_string (ir.arg0) in
                let arg1=arg_to_string (ir.arg1) in
                let arg2=arg_to_string (ir.arg2) in
                Absenv_v.set_value_string abs arg2 (Absenv_v.add (Absenv_v.get_value_string abs arg0) (Absenv_v.get_value_string abs arg1));
            (*
             * sub a1,a2,a3
             * for each value a1
             *  for each value a2
             *      a3=a1-a2
             * *)             
             | Sub -> 
                let arg0=arg_to_string (ir.arg0) in
                let arg1=arg_to_string (ir.arg1) in
                let arg2=arg_to_string (ir.arg2) in
                let val1 = Absenv_v.get_value_string abs arg0 in 
                let val2 =Absenv_v.get_value_string abs arg1 in 
                let val_sub = Absenv_v.sub val1 val2 in 
                Absenv_v.set_value_string abs arg2 val_sub
            (*
             * and a1,a2,a3
             * for each value a1
             *  for each value a2
             *      a3=a1 and -a2
             * *)            
            | And -> 
                let arg0=arg_to_string (ir.arg0) in
                let arg1=arg_to_string (ir.arg1) in
                let arg2=arg_to_string (ir.arg2) in
                if(arg0=arg1) then Absenv_v.set_value_string abs arg2 (Absenv_v.get_value_string abs arg0) (* and with himself*)
                else Absenv_v.set_value_string abs arg2 (Absenv_v.and_op (Absenv_v.get_value_string abs arg0) (Absenv_v.get_value_string abs arg1))
            (*
             * or a1,a2,a3
             * for each value a1
             *  for each value a2
             *      a3=a1 or a2
             * *)            
            | And -> 
                let arg0=arg_to_string (ir.arg0) in
                let arg1=arg_to_string (ir.arg1) in
                let arg2=arg_to_string (ir.arg2) in
                if(arg0=arg1) then Absenv_v.set_value_string abs arg2 (Absenv_v.get_value_string abs arg0) (* or with himself*)
                else Absenv_v.set_value_string abs arg2 (Absenv_v.and_op (Absenv_v.get_value_string abs arg0) (Absenv_v.get_value_string abs arg1))
            (*
             * str a1,,a3
             *      a3=a1
             * *)            
            | Str ->
                let arg0=arg_to_string (ir.arg0) in
                let arg2=arg_to_string (ir.arg2) in
                Absenv_v.set_value_string abs arg2 (Absenv_v.get_value_string abs arg0)
            (*
             * stm a1,,a3
             * for each value3 a3
             *  [value3]=a1
             * *)
            | Stm ->
                let arg0=arg_to_string (ir.arg0) in
                let arg2=arg_to_string (ir.arg2) in
                let vals=Absenv_v.get_value_string abs arg2 in
                let names=Absenv_v.values_to_names vals in
                if (List.length names)==1 
                then (*Strong update*)
                    let new_abs,val_arg0=Absenv_v.get_value_string_create abs arg0 number_init state in 
                    Absenv_v.set_value new_abs (List.hd names) val_arg0
                else (* Weak update *)
                    let val_arg0=Absenv_v.get_value_string abs arg0 in
                    let new_vals x abs =  Absenv_v.get_value_create abs x number_init state in
                    let merge_vals x abs = 
                        let new_abs,new_values = new_vals x abs in
                        new_abs, Absenv_v.merge_values_two val_arg0 new_values 
                    in
                    let rec iter_rec abs names = 
                        match names with
                        | [] -> abs
                        | hd::tl -> 
                            let new_abs,vals = merge_vals hd abs in
                            iter_rec (Absenv_v.set_value new_abs hd vals) tl
                    in
                    iter_rec abs names
            (*
             * ldm a1,,a3
             * for each value1 a1
             *  a3=[value1]
             * *)
            | Ldm ->
                let arg0=arg_to_string (ir.arg0) in
                let arg2=arg_to_string (ir.arg2) in
                let new_abs,vals=Absenv_v.get_value_string_create abs arg0 number_init state in
                let abs=new_abs in
                let names=Absenv_v.values_to_names vals in
                let abs_ref = ref abs in
                let vals_arg0 =
                    let f x =
                        let new_abs,vals = Absenv_v.get_value_create (!abs_ref) x number_init state in
                        let _ = abs_ref := new_abs in
                        vals
                    in  List.map f names 
                in
                let abs=(!abs_ref) in
                if (List.length vals_arg0>15) then (* too many values, better to put TOP *)
                        let _ = Printf.printf "Number ldm max reach\n" in
                         Absenv_v.set_value_string abs arg2 (Absenv_v.top_value ())
                else if (List.length vals_arg0>0) then
                    let rec merge_vals_rec vals l =
                        match vals with
                        | [] -> l
                        | hd::tl -> merge_vals_rec tl (Absenv_v.merge_values_two hd l)
                    in
                    Absenv_v.set_value_string abs arg2 (merge_vals_rec vals_arg0 (List.hd vals_arg0))
                else abs
            (*
             * xor a1 b1,
             * for each value a1
             *  for each value a2
             *      a3=a1 xor a2
             * *)
            | Xor ->                 
                let arg0=arg_to_string (ir.arg0) in
                let arg1=arg_to_string (ir.arg1) in
                let arg2=arg_to_string (ir.arg2) in
                if (arg0 = arg1) then  Absenv_v.set_value_string abs arg2 (Absenv_v.create_cst 0)
                 else
                    let val0 = Absenv_v.get_value_string abs arg0 in 
                    let val1 =Absenv_v.get_value_string abs arg1 in 
                    let val_xor = Absenv_v.xor_op val0 val1 in 
                    Absenv_v.set_value_string abs arg2 val_xor
            (*
             * bisz a1 , , b1
             * if a1==0 then b1 = 1
             *
             * *)
            | Bisz  ->
                let arg0=arg_to_string (ir.arg0) in
                let arg2=arg_to_string (ir.arg2) in
                let val0 = Absenv_v.get_value_string abs arg0 in 
                let is_zero = Absenv_v.is_zero val0 in 
                Absenv_v.set_value_string abs arg2 is_zero
            (*
             * mod a1,a2,a3
             * for each value a1
             *  for each value a2
             *      a3=a1%a2
             * *)             
             | Mod -> 
                let arg0=arg_to_string (ir.arg0) in
                let arg1=arg_to_string (ir.arg1) in
                let arg2=arg_to_string (ir.arg2) in
                let val1 = Absenv_v.get_value_string abs arg0 in 
                let val2 =Absenv_v.get_value_string abs arg1 in 
                let val_mod = Absenv_v.modulo val1 val2 in 
                Absenv_v.set_value_string abs arg2 val_mod
            (*
             * bsh a1,a2,a3
             * for each value a1
             *  for each value a2
             *      a3=a1 << a2 (if a2 <0, a1 >> a2)
             * *)             
             | Bsh -> 
                let arg0=arg_to_string (ir.arg0) in
                let arg1=arg_to_string (ir.arg1) in
                let arg2=arg_to_string (ir.arg2) in
                let val1 = Absenv_v.get_value_string abs arg0 in 
                let val2 =Absenv_v.get_value_string abs arg1 in 
                let val_bsh = Absenv_v.bsh val1 val2 in 
                Absenv_v.set_value_string abs arg2 val_bsh
            | _ -> abs;;

    (* 
     * Check for uaf on stm or ldm
     * *)
    let check_uaf (stmt,abs,hf,addr) =
        match stmt.type_node with
        (*
         * stm a1,,a3
         * for each value3 a3
         *  [value3]=a1
         * so check if value3 is a freed block
         * *)
        | Stm ->
                (
                let arg2=arg_to_string (stmt.arg2) in
                let vals=Absenv_v.get_value_string abs arg2 in
                let names=Absenv_v.values_to_names vals in
                let chunks=Absenv_v.check_uaf names hf in
                match chunks with
                | [] -> None
                | c -> Some (stmt,chunks,addr)
                )
        (*
         * ldm a1,,a3
         * for each value1 a1
         *  a3=[value1]
         * so check if value1 is a freed block
         * *)
        | Ldm ->
                (
                let arg0=arg_to_string (stmt.arg0) in
                let vals=Absenv_v.get_value_string abs arg0 in
                let names=Absenv_v.values_to_names vals in
                let chunks=Absenv_v.check_uaf names hf in
                match chunks with
                | [] -> None
                | c -> Some (stmt,chunks,addr)
                )

        | _ -> None;;


    (*
     * Return heaps elements accessed
     *) 
    let access_heap  stmt abs =
        match stmt.type_node with
        (*
         * stm a1,,a3
         * for each value3 a3
         *  [value3]=a1
         * return  value3 inter HE
         * *)
        | Stm ->
                let arg2=arg_to_string (stmt.arg2) in
                let vals=Absenv_v.get_value_string abs arg2 in
                let names=Absenv_v.values_to_names vals in
                Absenv_v.names_to_he names   
        (*
         * ldm a1,,a3
         * for each value1 a1
         *  a3=[value1]
         *  return value1 inter HE
         * *)
        | Ldm ->
                let arg0=arg_to_string (stmt.arg0) in
                let vals=Absenv_v.get_value_string abs arg0 in
                let names=Absenv_v.values_to_names vals in
                Absenv_v.names_to_he names 
        | _ -> [] ;;

    (* 
     * Protobuf parsing
     *)    
    let parse_blocks_protobuf (blocks : Program_piqi.block list ) =
        List.map (fun (x : Program_piqi.block) -> (Int64.to_int x.addr,List.map (fun y -> Int64.to_int y)  x.nodes_addr) ) blocks;;

    let parse_relations_protobuf  (relations : Program_piqi.block_relation list) = 
        List.map (fun  (x : Program_piqi.block_relation) -> (Int64.to_int x.father,Int64.to_int x.son) ) relations ;;

    let parse_node_protobuf (node: Program_piqi.node) =
        let parse_reil_addr  type_node s0 t0 v0 s1 t1 v1 s2 t2 v2  = parse_reil (Int64.to_int node.addr) type_node s0 t0 v0 s1 t1 v1 s2 t2 v2  in
        Scanf.sscanf node.node_desc "%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^,],%[^\n]" parse_reil_addr;;
        
    let parse_nodes_protobuf (nodes: Program_piqi.node list) =
        List.map (fun x -> parse_node_protobuf x) nodes;;
 
   let parse_func_protobuf  (func : Program_piqi.function_ ) = 
        let bbs = parse_blocks_protobuf func.blocks in
        let connec = parse_relations_protobuf func.block_relations in
        let eip = Int64.to_int func.eip in
        let number_unloop = Int64.to_int func.number_unlooping in
        let nodes = parse_nodes_protobuf func.nodes in
        let call_retn = (List.map (fun x -> Int64.to_int x ) func.calls,List.map (fun x -> Int64.to_int x ) func.retns) in
        (bbs,connec,eip,number_unloop,nodes,call_retn) ;;

   let parse_func_protobuf_number_unloop  (func : Program_piqi.function_ ) =
     max (Int64.to_int func.number_unlooping) 1

    (* Scoring function, this is not yet used *)   
    let score_heap_use (stmt,abs) =
        match stmt.type_node with
        | Stm ->
                (
                    let arg2=arg_to_string (stmt.arg2) in
                        let vals=Absenv_v.get_value_string abs arg2 in
                            let names=Absenv_v.values_to_names vals in
                                Absenv_v.check_use_heap names
                )
        | _ -> false;;
    


         

end

