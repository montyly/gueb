
(* 
 *  Default abstract environment 
 *
 *)
module AbsEnv =
struct

    (* 
     * Absenv definition 
     **)    
    type offset = int;;

    type register = string;;

    type chunk_t = NORMAL | INIT;;

    type chunk = {
            base_chunk : int;
            size : int;
            type_chunk : chunk_t ; (* 0 : heap, 1 : init mem, hack when no init memory, we class it as chunk *)
            mutable state_alloc : ((int*int)*string*int) list; (* addr it func_name number_func *)
            mutable state_free : (((int*int)*string*int) list) list; (* in case of chunk as valueSet, this never use, until uaf found, then takes value from hf *)
        };;

    type he = chunk;;

    type init = chunk;;

    type kset = 
        | Offsets of offset list
        | TOP_Offsets;;

    type base = 
        | Constant 
        | HE of he
        | Init of register ;;

    type valueSet = {
            base_vs :base;
            mutable offsets : kset; (* TODO remove mutable, one day may be  *) 
        };;

    type valuesSet = 
        | Values of valueSet list
        | TOP;;

    type baseoffset = {
            base : base;
            offset : offset;
        }

    type nameVal = 
        | Reg of register
        | BaseOffset of baseoffset;;

(*    type absenv = {
            name : nameVal;
            mutable values : valuesSet;
        };;*)

    let equal_off (o1:offset) (o2:offset) = o1 = o2
    let equal_chunk_t (c1:chunk_t) (c2:chunk_t) = c1 = c2
    let equal_register (r1:register) (r2:register) = r1 = r2

    module HashHeap = Hashtbl.Make (struct 
        type t = (int*offset*chunk_t) 
        let equal (id1,of1,t1) (id2,of2,t2) = (equal_chunk_t t1 t2 ) && (id1 = id2) && (equal_off of1 of2)
        let hash = Hashtbl.hash
    end)

    module HashStack = Hashtbl.Make (struct 
        type t = register * offset
        let equal (r1,of1) (r2,of2) = (equal_register r1 r2) && (equal_off of1 of2)
        let hash = Hashtbl.hash
    end)

    module HashConstant = Hashtbl.Make (struct 
        type t = offset 
        let equal o1 o2 = equal_off o1 o2
        let hash n = n
    end)

    module HashRegister = Hashtbl.Make (struct 
        type t = register 
        let equal r1 r2 = equal_register r1 r2 
        let hash r = 
            match r with
            |"esp"-> 0
            |"ebp"-> 1
            |"ecx"-> 2
            |"edx"-> 3
            |"ebx"-> 4
            |"edi"-> 5
            |"esi"-> 6
            |"eip"-> 7
            |"eax"-> 8
            |"t0"-> 9
            |"t1"-> 10
            |"t2"-> 11
            |"t3"-> 12
            |"t4"-> 13
            |"t5"-> 14
            |"t6"-> 15
            |"t7"-> 16
            |"t8"-> 17
            |"t9"-> 18
            |"t10"-> 19
            |"t11"-> 20
            |"t12"-> 21
            |"t13"-> 22
            |"t14"-> 23
            |"t15"-> 24
            |"t16"-> 25
            |"t17"-> 26
            |"t18"-> 27
            |"t19"-> 28
            |"t20"-> 29
            |"t21"-> 30
            |"t22"-> 31
            |"t23"-> 32
            |"t24"-> 33
            |"t25"-> 34
            |"t26"-> 35
            |"t27"-> 36
            |"t28"-> 37
            |"t29"-> 38
            |"t30"-> 39
            |"t31"-> 40
            |"t32"-> 41
            |"t33"-> 42
            |"t34"-> 43
            |"t35"-> 44
            |"t36"-> 45
            |"t37"-> 46
            |"t38"-> 47
            |"t39"-> 48
            |"CF"-> 49
            |"OF"-> 50
            |"SF"-> 51
            |"DF"-> 52
            |"ZF"-> 53
            |"dsbase"-> 54
            |"ssbase"-> 55
            | v -> Hashtbl.hash v
    end)

    type absenv = {
            heap : (chunk * valuesSet) HashHeap.t; (* chunk_id * offset * type -> chunk * valuesset *)
            stack : (valuesSet) HashStack.t ; (* register_init_name * offset -> valuesset *)
            constant : (valuesSet) HashConstant.t; (* offset -> valuesset *)
            register : (valuesSet) HashRegister.t; (* register_name -> valuesSet*)
            mutable ha : he list;
            mutable hf : he list;
        };;

    let classical_chunk () = NORMAL

    let number_chunk = ref 0

    (* number max of value *)
    let max_KSET=10;;

    let top_value() = TOP;;

    let create_cst a = Values ([{base_vs=Constant;offsets=Offsets [a]}]);;

    let string_to_name s =
        try BaseOffset {base=Constant;offset=int_of_string s}
        with    
            _ -> Reg s;;

    let value_to_names v =
        let rec value_to_names_rec b o l =
            match o with
            | [] -> l
            | hd::tl -> value_to_names_rec b tl ((BaseOffset ({base=b;offset=hd}))::l)
        in match v.offsets with
        | Offsets offsets ->  value_to_names_rec v.base_vs offsets []
        | TOP_Offsets -> [];;
           
    let values_to_names v=
        let rec values_to_names_rec v l=
            match v with
            | [] -> l
            | hd::tl -> values_to_names_rec tl (value_to_names hd)@l
        in 
        match v with
        | TOP -> []
        | Values v -> values_to_names_rec v [];;
             
    let get_hf abs = abs.hf

    (* 
     * Comparaison functions
     * *)
    let same_chunk h1 h2 =
        h1.base_chunk=h2.base_chunk (*&& h1.size=h2.size*) && h1.type_chunk=h2.type_chunk ;;


    let same_base b1 b2 =
        match b1,b2 with
        | Constant,Constant -> true
        | Init r1, Init r2 -> r1=r2
        | HE h1, HE h2 -> same_chunk h1 h2
        | Constant , Init _ | Constant , HE _ | Init _ , Constant | Init _ , HE _ | HE _ , Constant | HE _ , Init _  -> false;;
        
    let same_base_offset b1 b2 =
        match (b1.base,b2.base) with
        | Constant ,Constant -> b1.offset==b2.offset
        | Init r1, Init r2 ->r1=r2 &&  b1.offset==b2.offset
        | HE h1 , HE h2 -> (same_chunk  h1 h2) && b1.offset==b2.offset
        | Constant , Init _ | Constant , HE _ | Init _ , Constant | Init _ , HE _ | HE _ , Constant | HE _ , Init _  -> false;;

    let same_name n1 n2 =  
        match (n1,n2) with
        | Reg r1,Reg r2 -> r1=r2
        | BaseOffset b1, BaseOffset b2 -> same_base_offset b1 b2
        | Reg _ , BaseOffset _ | BaseOffset _ , Reg _ -> false;;

    (* 
     * Printy print functions
     * *)
    let pp_register r= r;; 

    let pp_cst =
        "Cst" ;;

    let pp_state st=
        String.concat " " (List.map (fun ((addr,it),f,_n) -> (Printf.sprintf "0x%x:%d:%s" addr it f) ) st)
   
    let pp_states st =
        String.concat " | " (List.map (fun x -> pp_state x ) st )
 
    let pp_chunk_full he =
        let str= 
        begin
            match he.type_chunk with
            | NORMAL -> "chunk"
            | INIT -> "val_init"
        end
        in 
        str^(string_of_int he.base_chunk) ^"("^(string_of_int he.size)^") alloc : ["^(pp_state he.state_alloc)^"] free : ["^(pp_states he.state_free)^"]";;
   
    let pp_chunk_t t =
        match t with
        | INIT -> "init_val"
        | NORMAL -> "chunk"
 
    let pp_chunk he = pp_chunk_full he
(*        let str= 
        begin
            match he.type_chunk with
            | NORMAL -> "chunk"
            | INIT -> "val_init"
        end
        in 
        str^(string_of_int he.base_chunk);;*)
    
    let pp_he h =
        "\t"^(String.concat " \n\t" (List.map (fun x -> pp_chunk_full x) h))

    let pp_base b=
        match b with    
        | Constant -> pp_cst 
        | Init r-> pp_register r
        | HE h-> pp_chunk h;;

    (* Small trick, if big number print as "-value" *)
    let pp_offset o= 
       (* if o > 0xff000000 then  (string_of_int (((mod) o 0x100000000)-0x100000000))
        else*) Printf.sprintf "0x%x" o;;

    let pp_baseoffset bo =
        pp_base bo.base ^" "^
        pp_offset bo.offset;;

    let pp_name name= 
        match name with
        | Reg r -> pp_register r
        | BaseOffset bo -> pp_baseoffset bo;;

    let pp_valueset vs=
        match vs.offsets with
        | Offsets offsets -> pp_base vs.base_vs ^" + ["^(String.concat " " (List.map (fun x -> pp_offset x) offsets))^" ]"
        | TOP_Offsets -> pp_base vs.base_vs ^ " TOP";;

    let pp_valuesset vs =
        match vs with
        | TOP -> "TOP"
        | Values v -> " | " ^(String.concat " | " (List.map (fun x -> pp_valueset x) v))

    let pp_absenv name values =
        pp_name name ^" : "^(pp_valuesset values) 

    let pp_absenvs abs =
        let heap = abs.heap in
        let stack = abs.stack in
        let constant = abs.constant in
        let register = abs.register in
        let txt = HashRegister.fold (fun reg values txt -> txt ^"\t"^(pp_register reg )^" : "^(pp_valuesset values)^"\n" ) register "Register\n" in
        let txt = HashStack.fold (fun (reg,off) values txt -> txt ^"\t"^(pp_register reg) ^" "^(pp_offset off)^" : "^(pp_valuesset values)^"\n" ) stack (Printf.sprintf "%sStack\n" txt) in
        let txt = HashHeap.fold (fun (_,off,_) (chunk,values) txt -> txt ^"\t"^(pp_chunk chunk)^" "^(pp_offset off)^" : "^(pp_valuesset values)^"\n" ) heap (Printf.sprintf "%sHeap\n" txt) in
        let txt = HashConstant.fold (fun off values txt -> txt ^"\t"^(pp_cst)^" "^( pp_offset off )^" : "^(pp_valuesset values)^"\n" ) constant (Printf.sprintf "%sConstant\n" txt) in
        txt ^ (Printf.sprintf "Ha : %s \nHf : %s\n\n" (pp_he abs.ha) (pp_he abs.hf)        )

    let copy_vals v=
        let rec copy_vals_rec v l= 
            match v with
            | [] -> l
            | hd::tl -> copy_vals_rec tl (({base_vs=hd.base_vs;offsets=hd.offsets})::l)
        in copy_vals_rec v [];;

    let copy_valsset v=
        match v with
        | TOP -> TOP
        | Values v -> Values (copy_vals v);;

    (* other if you want to have one ESP per function*)
    let initAbsenEnv () = {stack = HashStack.create 50; heap = HashHeap.create 50; register = HashRegister.create 50; constant = HashConstant.create 50; ha = []; hf = []};;

    let get_he abs id offset t =
        let tbl = abs.heap in
        let _,res = HashHeap.find tbl (id,offset,t) in
        res
 
    let get_he_chunk abs id offset t =
        let tbl = abs.heap in
        let res,_ = HashHeap.find tbl (id,offset,t) in
        res

    let get_stack abs reg offset  =
        let tbl = abs.stack in
        HashStack.find tbl (reg,offset) 
    
    let get_constant abs offset =
        let tbl = abs.constant in
        HashConstant.find tbl (offset) 

    let get_register abs reg  =
        let tbl = abs.register in
        HashRegister.find tbl (reg) 

    let set_he abs id offset t chunk vs =
        let tbl = abs.heap in
        HashHeap.replace tbl (id,offset,t) (chunk,vs)
    
    let set_stack abs reg offset vs =
        let tbl = abs.stack in
        HashStack.replace tbl (reg,offset) (vs)
    
    let set_constant abs offset vs =
        let tbl = abs.constant in
        HashConstant.replace tbl (offset) (vs)

    let set_register abs reg vs =
        let tbl = abs.register in
        HashRegister.replace tbl (reg) (vs)
 
    let init_reg abs r =
        set_register abs r (Values ([{base_vs=Init (r);offsets=Offsets [0]}]))

    let init_reg_base abs r =
        set_register abs r (Values ([{base_vs=Constant ;offsets=Offsets [0]}]));;

    let init_reg_val abs r v =
        set_register abs r v

    let init_first =
        let abs = initAbsenEnv() in
        let () = init_reg abs "esp" in
        let () = init_reg abs "ebp" in
        let () = init_reg abs "eax" in
        let () = init_reg_base abs "dsbase" in
        let () = init_reg_base abs "ssbase" in
        abs

    let init_chunk n  type_chunk state=
        {base_chunk=n;size=0;type_chunk=type_chunk;state_alloc=state;state_free=[]};;
 
    let new_init_memory n state =
        let () = n := (!n)+1 in 
        Values ([{base_vs= HE(init_chunk (!n) INIT state); offsets=Offsets([0])}]) ;;

    let init_vs_chunk n  type_chunk state=
        Values ([{base_vs=HE ({base_chunk=n;size=0;type_chunk=type_chunk;state_alloc=state;state_free=[]}) ; offsets=Offsets [0] }]);;
 
    let init_malloc n state =
        let abs = initAbsenEnv() in
        (*let name = BaseOffset ({base=HE ({base_chunk=n;size=0;type_chunk=0;state_alloc=state;state_free=[]});offset=0}) in*)
        let chunk = ({base_chunk=n;size=0;type_chunk=NORMAL;state_alloc=state;state_free=[]}) in
        let vals = Values ([{base_vs=Constant;offsets=Offsets [0]}]) in
        let () = set_he abs n 0 NORMAL chunk vals in
        let () = init_reg_val abs "eax" (Values ([{base_vs=HE ({base_chunk=n;size=0;type_chunk=NORMAL;state_alloc=state;state_free=[]}) ; offsets=Offsets [0] }])) in
        abs


    let append_offsets o1 o2 =
        match (o1,o2) with
        | TOP_Offsets,_ | _,TOP_Offsets -> raise Absenvgenerique.TOP_OFFSETS
        | Offsets o1,Offsets o2 -> Offsets (List.sort_uniq (fun a b -> compare a b)  (o1@o2))

    let merge_offsets o =
        let rec merge_offsets_rec o l =
           match o with
            | [] -> l
            | tl::hd -> merge_offsets_rec hd (append_offsets tl l)
        in
        try   merge_offsets_rec o (Offsets [])
        with
            Absenvgenerique.TOP_OFFSETS->TOP_Offsets;;

   
    let merge_he h1 h2 =
        let rec merge_he_rec h l =
            match h with
            | [] -> l
            | hd::tl -> merge_he_rec (List.filter (fun x ->  hd.type_chunk <> x.type_chunk ||  x.base_chunk<>hd.base_chunk ) tl)  (hd::l)
        in merge_he_rec (h1@h2) [];;
            
    let merge_alloc_free_conservatif ha hf =
        let is_in b hf=List.exists (fun x -> x.base_chunk=b.base_chunk && x.type_chunk = b.type_chunk) hf in
        (List.filter (fun x-> not( is_in x hf)) ha);;

 
    let merge_values values =
        let val_same_base value values = List.filter (fun x -> same_base value.base_vs x.base_vs) values in
        let val_diff_base value values = List.filter (fun x -> not (same_base value.base_vs x.base_vs)) values  in
        let rec merge_values_rec values l =
            match values with
            | [] -> 
            (
                match l with
                | None -> raise Absenvgenerique.TOP_VAL
                | Some v -> Values v                   
            )
            | hd::tl ->
            (
                let same_val=val_same_base hd tl in
                let diff_val=val_diff_base hd tl in
                match l with
                | None -> merge_values_rec diff_val (Some [{base_vs=hd.base_vs;offsets=merge_offsets (List.map (fun x -> x.offsets) (hd::same_val))}])
                | Some v-> merge_values_rec diff_val (Some (([({base_vs=hd.base_vs;offsets=merge_offsets (List.map (fun x -> x.offsets) (hd::same_val))})]@v)))
            )
            in
            match values with
            | TOP -> TOP
            | Values v ->
            (
                try  merge_values_rec v None
                with 
                Absenvgenerique.TOP_VAL -> TOP
            )

(*    let merge_values_two v1 v2=
        match (v1,v2) with
        | TOP,_ | _,TOP -> TOP
        | Values v1, Values v2 -> merge_values (Values (v1@v2));;*)
    
    (* If TOP, keep no TOP *) 
    let merge_values_two v1 v2=
        match (v1,v2) with
        | TOP,v | v,TOP -> v
        | Values v1, Values v2 -> merge_values (Values (v1@v2));;   

    (* should may be use first class module here ? *)
    let merge a b =  
        let stack_a = a.stack in
        let heap_a = a.heap in
        let constant_a = a.constant in
        let register_a = a.register in
        let stack_b = b.stack in
        let heap_b = b.heap in
        let constant_b = b.constant in
        let register_b = b.register in
        let nor_union a b hash_fold hash_fold2 hash_find hash_mem = 
            let only_a = hash_fold (fun k v l -> if ( hash_mem b k) then l else (k,v)::l) a [] in        
            let only_b, both = hash_fold2 (fun k v1 (l1,l2) -> try let v2 =  hash_find a k in (l1,(k,v1,v2)::l2) with Not_found -> ((k,v1)::l1,l2)) b ([],[]) in
            only_a,only_b,both
        in
        let only_stack_a,only_stack_b,both_stack = nor_union stack_a stack_b (HashStack.fold) (HashStack.fold) (HashStack.find) (HashStack.mem)in
        let only_heap_a,only_heap_b,both_heap = nor_union heap_a heap_b (HashHeap.fold) (HashHeap.fold) (HashHeap.find) (HashHeap.mem) in
        let only_register_a,only_register_b,both_register = nor_union register_a register_b (HashRegister.fold) (HashRegister.fold) (HashRegister.find) (HashRegister.mem) in
        let only_constant_a,only_constant_b,both_constant = nor_union constant_a constant_b (HashConstant.fold) (HashConstant.fold) (HashConstant.find) (HashConstant.mem) in
        let stack = HashStack.create 50 in
        let heap = HashHeap.create 50 in
        let register = HashRegister.create 50 in
        let constant = HashConstant.create 50 in
        let add tbl l add_func = List.iter (fun (k,v) -> add_func tbl k v ) l in
        let add_merge tbl l add_func = List.iter (fun (k,v1,v2) -> add_func tbl k (merge_values_two v1 v2) ) l in
        let add_merge_he tbl l add_func = List.iter (fun (k,(c1,v1),(_c2,v2)) -> add_func tbl k (c1,(merge_values_two v1 v2)) ) l in (* TODO should check that c1 = c2 ? *)
        let add_all tbl l1 l2 b add_func = 
            let () = add tbl l1 add_func in
            let () = add tbl l2 add_func in
            add_merge tbl b add_func in
        let add_he tbl l1 l2 b add_func = 
            let () = add tbl l1 add_func in
            let () = add tbl l2 add_func in
            add_merge_he tbl b add_func in
        let () = add_all stack only_stack_a only_stack_b both_stack (HashStack.add) in
        let () = add_all register only_register_a only_register_b both_register (HashRegister.add) in
        let () = add_all constant only_constant_a only_constant_b both_constant (HashConstant.add) in
        let () = add_he heap only_heap_a only_heap_b both_heap (HashHeap.add) in
        let ha = merge_he a.ha b.ha in
        let hf = merge_he a.hf b.hf in
        {stack = stack; heap = heap ; constant = constant; register = register; ha = ha ; hf = hf}
       
    (* merge a and b, if intersection, keeps a *) 
    (* should may be use first class module here ? *)
    let update a b = 
        let stack_a = a.stack in
        let heap_a = a.heap in
        let constant_a = a.constant in
        let register_a = a.register in
        let stack_b = b.stack in
        let heap_b = b.heap in
        let constant_b = b.constant in
        let register_b = b.register in
        let nor_union a b fold mem = (* in intersection, keeps a *)
            let vals = fold (fun k v l -> (k,v)::l) a [] in
            let vals_b =  fold (fun k v l -> if( mem a k) then l else (k,v)::l) b [] in
            vals,vals_b 
        in
        let vals_stack_a,only_stack_b = nor_union stack_a stack_b (HashStack.fold) (HashStack.mem) in
        let vals_heap_a,only_heap_b = nor_union heap_a heap_b (HashHeap.fold) (HashHeap.mem) in
        let vals_register_a,only_register_b = nor_union register_a register_b (HashRegister.fold) (HashRegister.mem) in
        let vals_constant_a,only_constant_b = nor_union constant_a constant_b (HashConstant.fold) (HashConstant.mem) in
        let stack = HashStack.create 50 in
        let heap = HashHeap.create 50 in
        let register = HashRegister.create 50 in
        let constant = HashConstant.create 50 in
        let add tbl l add_func = List.iter (fun (k,v) -> add_func tbl k v ) l in
        let add_all tbl l1 l2 add_func = 
            let () = add tbl l1 add_func in
            add tbl l2 add_func 
        in
        let () = add_all stack vals_stack_a only_stack_b (HashStack.add) in
        let () = add_all heap vals_heap_a only_heap_b (HashHeap.add) in
        let () = add_all register vals_register_a only_register_b (HashRegister.add) in
        let () = add_all constant vals_constant_a only_constant_b (HashConstant.add)  in
        let ha = merge_he a.ha b.ha in
        let hf = merge_he a.hf b.hf in
        {stack = stack; heap = heap ; constant = constant; register = register; ha = ha ; hf = hf}

 (*   let get_tbl abs name = 
        match name with
        | Reg _ -> abs.register
        | BaseOffset b ->
            match b.base with
            | Constant -> abs.constant
            | HE _ -> abs.heap 
            | Init _ -> abs.stack*)

    let set_value abs name values =
        let () =
            match name with
            | Reg r -> set_register abs r values
            | BaseOffset b ->
                match b.base with
                | Constant -> set_constant abs b.offset values
                | HE c -> set_he abs c.base_chunk b.offset c.type_chunk c values 
                | Init r -> set_stack abs r b.offset values
        in abs
(*        try
            let elem=List.find (fun x -> same_name x.name name) absenvs in
            elem.values <- values;
            absenvs
        with
        Not_found -> {name=name;values=values}::absenvs*)
        
    let get_integer_values vs =
        match vs with 
        | Values v ->
            let v = List.filter ( fun x -> match x.base_vs with | Constant -> true | HE _ | Init _ -> false ) v in
            let offsets = List.map (fun x -> x.offsets) v in
            if (List.exists (fun x -> match x with | TOP_Offsets -> true | Offsets _ -> false ) offsets) then [None]
            else
                let offsets = List.map (fun x -> match x with | Offsets o -> (List.map (fun y -> Some y) o) | TOP_Offsets -> [Some 0] ) offsets in
                List.concat offsets
        | TOP -> [None]

    let get_value_unsafe abs name =
        let vals = 
            match name with
            | Reg r -> get_register abs r 
            | BaseOffset b ->
                match b.base with
                | Constant -> get_constant abs b.offset
                | HE c -> get_he abs c.base_chunk b.offset c.type_chunk 
                | Init r -> get_stack abs r b.offset
        in match vals with
        | Values vals -> Values (copy_vals vals)
        | TOP -> TOP
 
    let get_value abs name =
        try
           get_value_unsafe abs name 
        with
             Not_found ->  Values ([]);;

    (* same as get_value, but create values if not found *)
    let get_value_create abs name state=
        try
            let vals = get_value_unsafe abs name in 
            match vals with
            | Values v -> (abs, Values (copy_vals v))
            | TOP -> abs,TOP (* TODO should be change, and TOP check in values_to_names *)
            with
                Not_found -> 
                    let new_val = Values ([{base_vs= HE(init_chunk (!number_chunk) INIT state); offsets=Offsets([0])}  ])  in
                    let () = number_chunk := (!number_chunk)+1 in
                    let abs = set_value abs name new_val in
                    (abs,new_val);;


    let get_value_string absenvs name=
        try Values ([{base_vs=Constant;offsets=Offsets [int_of_string name]}])
        with    
            Failure "int_of_string" -> 
                let name_convert = string_to_name name in
                get_value absenvs name_convert;;

    (* same as get_value_string, but create values if not found *)
    let get_value_string_create absenvs name state=
        try (absenvs, Values ([{base_vs=Constant;offsets=Offsets [int_of_string name]}]))
        with    
            Failure "int_of_string" -> 
                let name_convert = string_to_name name in
                get_value_create absenvs name_convert state;;

    let set_value_string absenvs name values =
        let name_convert = string_to_name name in
        set_value absenvs name_convert values;;
      
    let get_chunk_key c = c.base_chunk,c.type_chunk;;

    let get_chunk_states c= c.state_alloc,c.state_free ;;

    let remove_dupplicate o =
        let rec remove_dupplicate_rec o l =
            match o with
            | [] -> 
                if(List.length(l) >  max_KSET) then TOP_Offsets
                else Offsets l
            | hd::tl -> 
                if (List.exists (fun x -> x==hd) tl) then remove_dupplicate_rec tl l
                else remove_dupplicate_rec tl (hd::l)
        in 
        match o with 
        | TOP_Offsets -> TOP_Offsets
        | Offsets o -> remove_dupplicate_rec o [];;

    (*
     * 
     * Offset manipulation 
     * *)
    let add_offsets o1 o2 =
        let rec add_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> 
                add_offsets_rec o1 tl 
                (
                    (List.map 
                        (fun x -> 
                            if ( x+hd  > 0xffffffff) then
                                (((mod) (x+hd) 0x100000000))
                            else  (x+hd) 
                        ) 
                    o1) 
                @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 ->remove_dupplicate (add_offsets_rec o1 o2 []);;

    let sub_offsets o1 o2 =
        let rec sub_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> sub_offsets_rec o1 tl 
              (
                (List.map 
                    (fun x ->
                            if (x-hd) >=0 then (x-hd) 
                            else ((mod) (((mod) (x-hd) 0x100000000)+0x100000000) 0x100000000) 
(*                        if (hd-x)>=0 then (hd-x)   
                        else ((mod) (((mod) (hd-x) 0x100000000)+0x100000000) 0x100000000) (* Ocaml return a negative number with mod, so need this conversion *)*)
                    ) 
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (sub_offsets_rec o1 o2 []);;

    let mul_offsets o1 o2 =
        let rec mul_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> mul_offsets_rec o1 tl 
              (
                   (List.map 
                        (fun x -> ( x * hd  )) 
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (mul_offsets_rec o1 o2 []);;

    let div_offsets o1 o2 =
        let rec div_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> div_offsets_rec o1 tl 
              (
                   (List.map 
                        (fun x -> if(hd<>0) then x / hd  else x ) 
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (div_offsets_rec o1 o2 []);;

    let and_offsets o1 o2 =
        let rec and_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> and_offsets_rec o1 tl 
              (
                   (List.map 
                        (fun x -> (land) x hd  ) 
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (and_offsets_rec o1 o2 []);;

    let mod_offsets o1 o2 =
        let rec mod_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> mod_offsets_rec o1 tl 
              (
                   (List.map 
                        (fun x -> (if (hd <>0) then (mod) x hd else x ) )
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (mod_offsets_rec o1 o2 []);;

    let xor_offsets o1 o2 =
        let rec xor_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> xor_offsets_rec o1 tl 
              (
                   (List.map 
                        (fun x -> (lxor) x hd  ) 
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (xor_offsets_rec o1 o2 []);;
 
   let or_offsets o1 o2 =
        let rec or_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> or_offsets_rec o1 tl 
              (
                   (List.map 
                        (fun x -> (lor) x hd  ) 
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (or_offsets_rec o1 o2 []);;



    let bsh_offsets o1 o2 =
        let rec bsh_offsets_rec o1 o2 l =
            match o2 with
            | [] -> Offsets l
            | hd::tl -> bsh_offsets_rec o1 tl 
              (
                   (List.map 
                        (fun x -> if(hd>0) then (lsl) x hd
                                  else (lsr) x hd

                   )
                o1)
             @l)
        in 
        match (o1,o2) with
        | TOP_Offsets,_| _,TOP_Offsets -> TOP_Offsets
        | Offsets o1, Offsets o2 -> remove_dupplicate (bsh_offsets_rec o1 o2 []);;

    (* 
     * arthmetique operation
     * *)
    let add a b = 
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant)) 
                then  Values (List.map (fun x -> let ()  = x.offsets<-add_offsets ((List.hd a).offsets) x.offsets in x ) b)
            else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then Values (List.map (fun x -> let () = x.offsets<-add_offsets ((List.hd b).offsets) x.offsets in x) a)
           else TOP;;

    let sub a b = 
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-sub_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-sub_offsets x.offsets  offset_b ) ; x) a)
           else
                TOP;;
      
 (*   let and_op a b = (*TODO should rewrite this *)
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if ((List.length a)==1 && (List.hd a).base_vs == Constant ) then
                match (List.hd a).offsets with
                | TOP_Offsets -> TOP
                | Offsets o -> 
                    if((List.length o)==1 && (List.hd o)>=4294967280) then Values b
                    else if ((List.length b)==1 && (List.hd b).base_vs == Constant ) then
                        match (List.hd b).offsets with
                        | TOP_Offsets -> TOP
                        | Offsets o -> 
                            if((List.length o)==1 && (List.hd o)>=4294967280) then Values a
                            else TOP
                    else TOP
            else if ((List.length b)==1 && (List.hd b).base_vs == Constant ) then
                match (List.hd b).offsets with
                | TOP_Offsets -> TOP
                | Offsets o -> 
                    if((List.length o)==1 && (List.hd o)>=4294967280) then Values a
                    else TOP
            else
                TOP;;
*)
    let mul a b = 
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-mul_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-mul_offsets offset_b x.offsets) ; x) a)
           else
                TOP;;

    let div a b = 
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-div_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-div_offsets x.offsets  offset_b ) ; x) a)
           else
                TOP;;

    let and_op a b = 
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-and_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-and_offsets offset_b x.offsets) ; x) a)
           else
                TOP;;
     

    let or_op a b = 
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-or_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-or_offsets offset_b x.offsets) ; x) a)
           else
                TOP;;


    let xor_op a b = 
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-xor_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-xor_offsets offset_b x.offsets) ; x) a)
           else
                TOP;;
 
    let modulo a b =
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-mod_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-mod_offsets x.offsets offset_b ) ; x) a)
           else
                TOP;;

    let bsh a b =
        match (a,b) with
        | (TOP,_) | (_,TOP) -> TOP
        | (Values a,Values b) ->
            if (((List.length a)==1) && ((List.hd a).base_vs == Constant))
                then
                let head=List.hd a in
                let offset_a=head.offsets in
                Values (List.map (fun x -> ignore(x.offsets<-bsh_offsets offset_a x.offsets) ; x ) b)
           else if (((List.length b)==1) && ((List.hd b).base_vs == Constant))
                then
                let head=List.hd b in
                let offset_b=head.offsets in
                Values (List.map (fun x -> ignore( x.offsets<-bsh_offsets x.offsets offset_b ) ; x) a)
           else
                TOP;;



    let is_zero v =
        match v with
        | Values a ->
               if((List.length a) == 1 && (List.hd a).base_vs == Constant) then
               (
                   match (List.hd (a)).offsets with
                   | Offsets o ->
                        if((List.length o)==1 && (List.hd o) == 0) then Values ([{base_vs= Constant; offsets=Offsets([1])}])
                        else Values ([{base_vs= Constant; offsets=Offsets([0])}])

                   | TOP_Offsets -> Values ([{base_vs= Constant; offsets=Offsets([0])}])
               )
               else Values ([{base_vs= Constant; offsets=Offsets([0])}])
        | TOP -> Values ([{base_vs= Constant; offsets=Offsets([0])}]) 


    let free_stack a _ = a

    (*
     * Remove elem in list that are not coming from the heap
     * *)
    let clean_he_for_free v =
        List.fold_left (fun acc x ->
                match x.base_vs with
                | HE e -> e::acc
                | Init _ | Constant -> acc
            ) [] v
    
    (*
     * Checking for double-free
     *)
    let check_df abs vals =
        let hf = abs.hf in
        match vals with
        | TOP -> raise Absenvgenerique.ERROR
        | Values v ->
        begin
        let chunk_in chunk chunks=
            List.exists 
                (fun x  -> (same_base (HE chunk) (HE x))
                ) chunks 
        in
        let free_elems_cleans = clean_he_for_free v in
        List.filter (fun x -> chunk_in x free_elems_cleans ) hf
        end

    (*
     * free elem
     * *)
    let free abs vals state show_free =
        let (ha,hf) = abs.ha,abs.hf in
        match vals with
        | TOP -> raise Absenvgenerique.ERROR
        | Values v -> 
            let () = if(show_free) then Printf.printf "Free on %s \n" (pp_valuesset (Values v)) in
            let chunk_not_in chunk chunks = List.exists (fun x -> not (same_base (HE chunk) (HE x)) ) chunks in
            let free_elems_cleans = clean_he_for_free v in
            let new_ha=List.filter (fun x->chunk_not_in x free_elems_cleans) ha in
            let new_hf=(List.map (fun a -> {a with state_free=state::a.state_free})  free_elems_cleans)@hf in
            let () = abs.ha <- merge_alloc_free_conservatif new_ha new_hf in (* may be useless*)
            abs.hf <- new_hf

    (* 
     * Filter values
     * *)
    let filter_values v=
        let rec filter_values_rec v l=
            match v with
            | [] -> merge_values (Values l)
            | [TOP] -> merge_values (Values l)
            | [Values v]-> merge_values (Values (v@l))
            | TOP::tl -> filter_values_rec tl l
            | (Values v)::tl -> filter_values_rec tl (v@l)
        in filter_values_rec v [];;

    (*
     * Check is esp or ebp took stranges values
     * *)
    let filter_esp_ebp abs free_stack verbose =
        let val_ebp=get_value_string abs "ebp" in
        let ()  = 
            match val_ebp with
            | TOP -> let () = if (verbose) then Printf.printf "Error Ebp = TOP\n" in
                     raise Absenvgenerique.ERROR
            | Values _ -> ()
        in
        let val_esp=get_value_string abs "esp" in
        match val_esp with
            | TOP -> let () = if (verbose) then Printf.printf("Error ! \n") in raise Absenvgenerique.ERROR
            | Values v -> 
                if (List.length v) <>1 then let () = if (verbose) then Printf.printf("Error 2! \n") in raise Absenvgenerique.ERROR
                else 
                    match ((List.hd v).offsets) with
                    | TOP_Offsets-> let () = if (verbose) then Printf.printf("Error3 ! \n") in  raise Absenvgenerique.ERROR
                    | Offsets o -> 
                        if ((List.length o) <> 1) then let () = if (verbose) then Printf.printf("Error4 ! \n") in raise Absenvgenerique.ERROR
                        else
                            if(free_stack) then
                                    let offset=List.hd (o) in
(*                                    List.filter *)
                                    let stack = abs.stack in
                                    let out_of_scope = HashStack.fold
                                        (fun (name,b_offset) _ l ->
                                            match name with
                                            | "esp" ->
                                                    if(b_offset <0xf0000000) then l (* case when for example esp + 0x4, because esp init =0 *)
                                                    else if (b_offset<offset) then ((name,b_offset)::l)
                                                    else l
                                            | _  -> l
                                        ) stack [] 
                                    in 
                                    let () = List.iter (fun x -> HashStack.remove stack x ) out_of_scope in
                                    let ha = merge_alloc_free_conservatif abs.ha abs.hf in
                                    {stack = stack; register = abs.register ; constant = abs.constant ; heap = abs.heap; ha = ha ; hf = abs.hf}
                             else
                                    {stack = abs.stack; register = abs.register ; constant = abs.constant ; heap = abs.heap; ha = abs.ha ; hf = abs.hf}

    (* 
     * Restore in v1 stack frame values from v2
     *) 
    let restore_stack_frame v1 v2 =
        let v1_esp = set_value_string v1 "esp" (get_value_string v2 "esp") in
        let v1_ebp = set_value_string v1_esp "ebp" (get_value_string v2 "ebp") in
        v1_ebp;;


    let filter_he abs =
            let ha = merge_alloc_free_conservatif abs.ha abs.hf in
            {abs with ha = ha}

    let names_to_he names =
        let rec filter n l = 
            match n with
            | [] -> l
            | BaseOffset b::tl ->
                begin
                    match b.base with
                    | HE h -> filter tl (h::l)
                    | Init _ | Constant -> filter tl l
                end
            | Reg _ :: tl -> filter tl l
        in
        filter names []
        
    let check_uaf names hf =
        List.fold_left (fun acc x ->
                match x with
                | Reg _ -> acc 
                | BaseOffset b -> 
                        match b.base with
                        | HE h->
                            begin 
                            try
                                let f = List.find (fun x -> same_chunk x h) hf in
                                ({h with state_free=f.state_free})::acc
                            with 
                                Not_found -> acc
                            end
                        | Init _ | Constant -> acc
        ) [] names
        
    let check_use_heap names =
        let ret = List.map 
            (fun x -> 
                match x with
                | Reg _ -> false
                | BaseOffset b ->
                    match b.base with
                    | HE _-> true
                    | Init _ | Constant -> false
            ) names
        in
        List.fold_left (fun x y ->(||)  x y) false ret;;

    let retn_not_analyse () = TOP;;

  (*  let clean_vs _list_vs= () ;;

    let clean_vss list_vs =
         match list_vs with 
         | TOP -> ()
         | Values vs -> List.iter clean_vs vs ;;*)

    let clean_vsa abs = 
        let () = abs.ha <- [] in
        let () = abs.hf <- [] in
        let heap = abs.heap in
        let stack = abs.stack in
        let constant = abs.constant in
        let register = abs.register in
        let () = HashHeap.reset heap in
        let () = HashStack.reset stack in
        let () = HashConstant.reset constant in
        HashRegister.reset register
   
    let restore_esp vsa =
        let val_esp=get_value_string vsa "esp" in
        let val_esp_4 = add val_esp (create_cst 4) in
        set_value_string vsa "esp" val_esp_4

    let malloc_ret abs state =
        let chunk = ({base_chunk=(!number_chunk);size=0;type_chunk=NORMAL;state_alloc=state;state_free=[]}) in
        let vals = Values ([{base_vs=Constant;offsets=Offsets [0]}]) in
        let () = set_he abs (!number_chunk) 0 NORMAL chunk vals in
        let () = init_reg_val abs "eax" (Values ([{base_vs=HE ({base_chunk=(!number_chunk);size=0;type_chunk=NORMAL;state_alloc=state;state_free=[]}) ; offsets=Offsets [0] }])) in
        let () = number_chunk := !number_chunk +1 in
        let () = abs.ha <- chunk::abs.ha in
        abs    

    let malloc_arg abs state off =
        let chunk = ({base_chunk=(!number_chunk);size=0;type_chunk=NORMAL;state_alloc=state;state_free=[]}) in
        let vals = Values ([{base_vs=Constant;offsets=Offsets [0]}]) in
        let () = set_he abs (!number_chunk) 0 NORMAL chunk vals in
        let val_esp= get_value_string abs "esp" in  
        let val_esp_add = add val_esp (create_cst off) in
        let arg = List.hd (values_to_names val_esp_add) in
        let abs = set_value abs arg (Values ([{base_vs=HE ({base_chunk=(!number_chunk);size=0;type_chunk=NORMAL;state_alloc=state;state_free=[]}) ; offsets=Offsets [0] }])) in
        let () = number_chunk := !number_chunk +1 in
        let () = abs.ha <- chunk::abs.ha in
        abs    
end;;
