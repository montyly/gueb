open Absenv;;

module type Stubfunc = functor (Absenv_v : AbsEnvGenerique) ->
sig
   val stub : int -> Absenv_v.absenv -> Absenv_v.he list -> Absenv_v.he list -> int ref -> (int*int) -> string -> int -> ((int*int)*string*int) list ->  bool * Absenv_v.absenv * Absenv_v.he list * Absenv_v.he list

end ;;


module StubNoFunc = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let stub _addr vsa ha hf _number_init _addr _func_name _call_number _backtrack  = false,vsa,ha,hf
end;;
 
module StubOptiPNG = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let png_free    = 0x08055F00 ;;
    let png_destroy = 0x08055E30 ;;
    let skip = [0x8055220(*png_set_error_fn*)];;

    let restore_esp vsa = Absenv_v.restore_esp vsa;;    

    let call_png_free vsa ha hf addr func_name call_number backtrack =
        try
            let val_esp=Absenv_v.get_value_string vsa "esp" in
            let val_esp_8= Absenv_v.add val_esp (Absenv_v.create_cst 8) in
            let names=Absenv_v.values_to_names val_esp_8 in
            let vals=List.map (fun x -> Absenv_v.get_value vsa x) names in
            let vals_filter=Absenv_v.filter_values  vals in
            let (ha,hf)=Absenv_v.free ha hf vals_filter ((addr,func_name,call_number)::backtrack) false in
            let ha=Absenv_v.merge_alloc_free_conservatif ha hf in
            true,(restore_esp vsa),ha,hf
        with                        
            AbsEnv.ERROR -> 
                let () = Printf.printf "Error on png_free? \n" in 
                true,(restore_esp vsa),ha,hf

    let call_png_destroy vsa ha hf addr func_name call_number backtrack  =
        try
            let val_esp=Absenv_v.get_value_string vsa "esp" in
            let val_esp_4= Absenv_v.add val_esp (Absenv_v.create_cst 4) in
            let names=Absenv_v.values_to_names val_esp_4 in
            let vals=List.map (fun x -> Absenv_v.get_value vsa x) names in
            let vals_filter=Absenv_v.filter_values  vals in
            let (ha,hf)=Absenv_v.free ha hf vals_filter ((addr,func_name,call_number)::backtrack) false in
            let ha=Absenv_v.merge_alloc_free_conservatif ha hf in
            true,(restore_esp vsa),ha,hf
        with                        
            AbsEnv.ERROR -> 
                let () = Printf.printf "Error on png_destroy? \n" in 
                true,(restore_esp vsa),ha,hf

    let stub addr_call vsa ha hf _number_init addr func_name call_number backtrack  =
        if (addr_call = png_free) then call_png_free vsa ha hf addr func_name call_number backtrack 
        else if (addr_call = png_destroy) then  call_png_destroy vsa ha hf addr func_name call_number backtrack
        else if (List.exists (fun x -> x=addr_call) skip) then true,(restore_esp vsa),ha,hf
        else false,vsa,ha,hf
        
end;;

module StubJasper = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let jas_matrix_create    = 0x08052C40 ;;
    let jas_iccattrtab_create    = 0x08054D32 ;;
    let skip = [];;


    let restore_esp vsa = Absenv_v.restore_esp vsa;;    


    let call_jas_matrix vsa ha hf number_chunk _addr _func_name _call_number backtrack =
        try
            let new_chunk = (Absenv_v.init_vs_chunk ( !number_chunk) (Absenv_v.classical_chunk()) backtrack) in
            let vsa = Absenv_v.set_value_string vsa "eax" new_chunk in
            let ha=(Absenv_v.init_chunk !number_chunk (Absenv_v.classical_chunk()) backtrack)::ha  in
            let () = number_chunk:=!number_chunk+1 in
            true,(restore_esp vsa),ha,hf
        with                        
            _ -> 
                true,(restore_esp vsa),ha,hf

    let stub addr_call vsa ha hf number_init addr func_name call_number backtrack  =
        if (addr_call = jas_matrix_create) then call_jas_matrix vsa ha hf number_init addr func_name call_number backtrack 
        else if (addr_call = jas_iccattrtab_create) then call_jas_matrix vsa ha hf number_init addr func_name call_number backtrack 
        else if (List.exists (fun x -> x=addr_call) skip) then true,(restore_esp vsa),ha,hf
        else false,vsa,ha,hf
        
end;;

module StubGnomeNettool = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let gtk_tree_model_get  = 0x0804DBD0 ;; (* The address of the function *)

    (* This function will restore esp *) 

    let restore_esp vsa = Absenv_v.restore_esp vsa;;    




    let call_gtk_tree_model_get vsa ha hf number_chunk _addr _func_name _call_number backtrack =
        try
            let vsa = restore_esp vsa in
            (* We create a new chunk*)
            let new_chunk = (Absenv_v.init_vs_chunk ( !number_chunk) (Absenv_v.classical_chunk()) backtrack) in
            (* We look for the value stored in the third argument *)
            (* First we get the value of esp *)
            let val_esp=Absenv_v.get_value_string vsa "esp" in  
            (* We add 36 to get the right argument *)
            let val_esp_36 = Absenv_v.add val_esp (Absenv_v.create_cst 36) in
            (* we transform the values to names, see the abs env model. 
                In ordre to simplify this example, we do strong update on the first possibility.
                A version with strong and weak update should be made*)
            let third_arg = List.hd (Absenv_v.values_to_names val_esp_36) in
            (* We put the new chunk in the third arg *)
            let vsa = Absenv_v.set_value vsa third_arg new_chunk in
            (* We add a the new chunk in ha *)
            let ha=(Absenv_v.init_chunk !number_chunk (Absenv_v.classical_chunk()) backtrack)::ha  in
            let () = number_chunk:=!number_chunk+1 in
            (* the first boolean means to the caller that the function was stubbed *)
            true,vsa,ha,hf
        with                        
            _ -> 
                true,restore_esp vsa ,ha,hf

    let stub addr_call vsa ha hf number_init addr func_name call_number backtrack  =
        if (addr_call = gtk_tree_model_get) then call_gtk_tree_model_get vsa  ha hf number_init addr func_name call_number backtrack 
        else false,vsa,ha,hf
        
end;;


