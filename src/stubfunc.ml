open Absenvgenerique;;

module type Stubfunc = functor (Absenv_v : AbsEnvGenerique) ->
sig
   val stub : int -> Absenv_v.absenv -> (int*int) -> string -> int -> ((int*int)*string*int) list ->  bool * Absenv_v.absenv 

end ;;


module StubNoFunc = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let stub _addr_call vsa  _addr _func_name _call_number _backtrack  = false,vsa
end;;
 
module StubOptiPNG = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let png_free    = 0x08055F00 ;;
    let png_destroy = 0x08055E30 ;;
    let skip = [0x8055220(*png_set_error_fn*)];;

    let restore_esp vsa = Absenv_v.restore_esp vsa;;    

    let call_png_free vsa addr func_name call_number backtrack =
        try
            let val_esp=Absenv_v.get_value_string vsa "esp" in
            let val_esp_8= Absenv_v.add val_esp (Absenv_v.create_cst 8) in
            let names=Absenv_v.values_to_names val_esp_8 in
            let vals=List.map (fun x -> Absenv_v.get_value vsa x) names in
            let vals_filter=Absenv_v.filter_values  vals in
            (* does not check for df *)
            let () = Absenv_v.free vsa vals_filter ((addr,func_name,call_number)::backtrack) false in
            true,(restore_esp vsa)
        with                        
            Absenvgenerique.ERROR -> 
                let () = Printf.printf "Error on png_free? \n" in 
                true,(restore_esp vsa)

    let call_png_destroy vsa addr func_name call_number backtrack =
        try
            let val_esp=Absenv_v.get_value_string vsa "esp" in
            let val_esp_4= Absenv_v.add val_esp (Absenv_v.create_cst 4) in
            let names=Absenv_v.values_to_names val_esp_4 in
            let vals=List.map (fun x -> Absenv_v.get_value vsa x) names in
            let vals_filter=Absenv_v.filter_values  vals in
            (* does not check for df *)
            let () = Absenv_v.free vsa vals_filter ((addr,func_name,call_number)::backtrack) false in
            true,(restore_esp vsa)
        with                        
            Absenvgenerique.ERROR -> 
                let () = Printf.printf "Error on png_destroy? \n" in 
                true,(restore_esp vsa)

    let stub addr_call vsa addr func_name call_number _backtrack  =
        if (addr_call = png_free) then call_png_free vsa addr func_name call_number _backtrack 
        else if (addr_call = png_destroy) then  call_png_destroy vsa addr func_name call_number _backtrack
        else if (List.exists (fun x -> x=addr_call) skip) then true,(restore_esp vsa)
        else false,vsa
        
end;;

module StubJasper = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let jas_matrix_create    = 0x08052C40 ;;
    let jas_iccattrtab_create    = 0x08054D32 ;;
    let skip = [];;


    let restore_esp vsa = Absenv_v.restore_esp vsa;;    


    let call_jas_matrix vsa addr func_name call_number backtrack =
        try
            let new_state = ((addr,func_name,call_number)::backtrack) in
            let vsa = Absenv_v.malloc_ret vsa new_state in
            true,(restore_esp vsa)
        with                        
            _ -> 
                true,(restore_esp vsa)

    let stub addr_call vsa addr func_name call_number _backtrack  =
        if (addr_call = jas_matrix_create) then call_jas_matrix vsa addr func_name call_number _backtrack 
        else if (addr_call = jas_iccattrtab_create) then call_jas_matrix vsa addr func_name call_number _backtrack 
        else if (List.exists (fun x -> x=addr_call) skip) then true,(restore_esp vsa)
        else false,vsa
        
end;;

module StubGnomeNettool = functor (Absenv_v : AbsEnvGenerique) ->
struct
    let gtk_tree_model_get  = 0x0804DBD0 ;; (* The address of the function *)

    (* This function will restore esp *) 

    let restore_esp vsa = Absenv_v.restore_esp vsa;;    

    let call_gtk_tree_model_get vsa addr func_name call_number backtrack =
        try
            let vsa = restore_esp vsa in
            let new_state = ((addr,func_name,call_number)::backtrack) in
            (* add malloc in the third argument *)
            let vsa = Absenv_v.malloc_arg vsa new_state 36 in
            true,vsa
        with                        
            _ -> 
                true,restore_esp vsa

    let stub addr_call vsa addr func_name call_number _backtrack  =
        if (addr_call = gtk_tree_model_get) then call_gtk_tree_model_get vsa  addr func_name call_number _backtrack 
        else false,vsa
        
end;;

module StubTiff2pdfLibtiff = functor (Absenv_v : AbsEnvGenerique) ->
struct

    let addr_skip = [0x08057cbc;0x08057d15;0x08057dd3;0x08057e5d;0x08057e8d;0x080580ae;0x080581c4;0x08058804;0x08058831;0x08058892;0x080588f4;0x08058b2b;0x08058c4a;0x08058ca0;0x08058d38;0x08058d5a;0x08058d7c;0x08058d9e;0x08058e36;0x08058e40;0x08058e62;0x08058e84;0x08058ea6;0x08058ed5;0x08058ee9;0x08058ef3;0x08058ef8;0x08059008;0x0805904e;0x080590ba;0x08059179;0x080591e5;0x08059415;0x0805943e;0x08059472;0x0805949b;0x080594c4;0x080594ed;0x08059516;0x0805953f;0x08059788;0x0805aeac;0x0805aed9;0x0805b065;0x0805b0a9;0x0805bd63;0x0805bd90;0x0805be23;0x0805c128;0x0805c143;0x0805c1ae;0x0805c22b;0x0805c24d;0x0805c39d;0x0805cb41;0x0805cbbe;0x0805cc8c;0x0805ccc3;0x0805ccd1;0x0805cce9;0x0805d0e5;0x0805d0ef;0x0805d0f9;0x0805d2cd;0x0805d483;0x0805d58f;0x0805d5ca;0x0805d605;0x0805d6e8;0x0805d7da;0x0805d830;0x0805d886;0x0805d8f4;0x0805db1d;0x0805dde1;0x0805e1d8;0x0805e257;0x0805e4f6;0x0805e77f;0x0805e9e7;0x0805ec49;0x0805ef4b;0x0805f1fe;0x0805f2a0;0x0805f50f;0x0805f953;0x0805fd8d;0x080601ba;0x080605c9;0x080609d8;0x08060da9;0x080611be;0x08061580;0x08061c62;0x08062332;0x080624c7;0x08062590;0x080625a3;0x080625b6;0x080625e5;0x08062616;0x08062645;0x08062674;0x08062716;0x080627ba;0x080628c9;0x080629d0;0x08062a05;0x08062adb;0x08062afb;0x08062b1e;0x08062b48;0x08062b62;0x08062b82;0x08062bb7;0x08062bf2;0x08062c14;0x08062c36;0x08062c5f;0x08062c76;0x08062c93;0x08062cc5;0x08062d09;0x08062d29;0x08062d4b;0x08062d65;0x08062d85;0x08062dba;0x08062df5;0x08062e19;0x08062e33;0x08062e56;0x08062e8b;0x08062ed5;0x08062ef5;0x08062f17;0x08062f2e;0x08062f54;0x08062f80;0x08062f98;0x08062fcd;0x08063017;0x08063037;0x08063059;0x08063070;0x08063096;0x080630c0;0x080631fd;0x080634ea;0x08064ab8;0x08064b2a;0x08064b77;0x08064c49;0x08065045;0x080654ef;0x08065765;0x08066155;0x080682cd;0x0806847c;0x08068945;0x08068950;0x0806897b;0x08068a06;0x08068a30;0x08069147;0x0806b343;0x0806b7e5;0x0806b83d;0x0806b895;0x0806b8ed;0x0806b945;0x0806b99e;0x0806b9f6;0x0806bae3;0x0806bb3b;0x0806bb8c;0x0806bbe4;0x0806bc3c;0x0806bc94;0x0806bcec;0x0806bd49;0x0806bda1;0x0806bdf9;0x0806be51;0x0806bea9;0x0806bf01;0x0806bf88;0x0806c0f1;0x0806c25a;0x0806c3a8;0x0806c5ab;0x0806c802;0x0806c84f;0x0806c89c;0x0806c8e9;0x0806c936;0x0806c9ae;0x0806ca4a;0x0806cae6;0x0806cb55;0x0806cbf7;0x0806cc99;0x0806cd6e;0x0806ce43;0x0806cfc9;0x0806d1c0;0x0806d45e;0x0806d500;0x0806d5a2;0x0806d644;0x0806d719;0x0806db8f;0x0806e4d1;0x0806f335;0x0806f3a8;0x0806f3c3;0x0806f3de;0x0806f43c;0x0807180c;0x08073f3b;0x08075098;0x08075938;0x08075998;0x080759f8;0x08075c62;0x08075cc8;0x080760f4;0x08076296;0x08076b86;0x08076c2b;0x08076d88;0x0807f8b7;0x0807faf3;0x0807ff0c;0x0807ffb2;0x08080036;0x080800a8;0x0808011a;0x0808014d;0x08080187;0x080801c8;0x08080202;0x0808023c;0x08080278;0x080802b4;0x080802e7;0x0808031a;0x0808034f;0x08080382;0x080803be;0x080803fa;0x08080428;0x0808045b;0x0808048e;0x080805c2;0x0808070a;0x080808cf;0x08080970;0x080839c0;0x08087654;0x0808829b;0x0808a255;0x0808a6af;0x0808a6e0;0x080904d2;0x0809055d;0x08090ff5;0x08090fff;0x0809101a;0x08091025;0x08091042;0x08091050;0x08091073;0x0809107e;0x0809109b;0x080910b3;0x080910c1;0x080910d0;0x080910de;0x080910ec;0x08091104;0x0809111c;0x08091132;0x0809114b;0x08091159;0x08091167;0x08091175;0x08091183;0x08091191;0x0809119f;0x08091880;0x0809601c;0x080982f7;0x0809842d;0x080984bc;0x080989a1;0x08098c78;0x08098d47;0x08098ee7;0x080991b2;0x08099353;0x0809978e;0x0809982d;0x08099956;0x08099c54;0x08099dc0;0x0809a195;0x0809a31a;0x0809a45f;0x0809a648;0x0809a6d8;0x0809a6dd;0x0809a72e;0x0809a7a1;0x0809a7f4;0x0809a848;0x0809a8e2;0x0809a980;0x0809accf;0x0809ad36;0x0809adb9;0x0809ae3d;0x0809ae7d;0x0809aedd;0x0809aefd;0x0809af9c;0x0809b2bb;0x0809b31b;0x0809b480;0x0809b4e0;0x0809b505;0x0809b543;0x0809b5b3;0x0809b5e5;0x0809b628;0x0809b66e;0x0809b6dc;0x0809b71a;0x0809b760;0x0809b7d0;0x0809b83d;0x0809b854;0x0809be53;0x0809be84;0x0809c047;0x0809c1a5;0x0809c324;0x0809c43d;0x0809c49d;0x0809c7de;0x0809c845;0x0809c862;0x0809c8c2;0x0809c8e9;0x0809c974;0x0809c980;0x0809c99b;0x0809c9b6;0x0809ca14;0x0809ca74;0x0809ce8d;0x0809d20a;0x0809d36b;0x0809d3f3;0x0809d7cb;0x0809d87e;0x0809da2a;0x0809dc4c;0x0809dd97;0x0809df3b;0x0809e317;0x0809e401;0x0809ede0;0x0809f1e4;0x0809f252;0x0809f357;0x0809f36a;0x0809f37d;0x0809f397;0x0809f3b8;0x0809f3d9;0x0809f4f4;0x0809f645;0x0809f990;0x0809fb9e;0x0809fce8;0x080a5b60;0x080a5e00;0x080a6a80;0x080a6e80;0x080aee80;0x080c36e0;0x080c37e0;0x080c3be0;0x080ce1a0;0x080d0358;0x080d035c;0x080d0398;0x080d039c;0x080d055c];;

    let restore_esp vsa = Absenv_v.restore_esp vsa;;    


    let stub addr_call vsa _addr  _func_name _call_number _backtrack  =
        if (List.exists (fun x -> x = addr_call) addr_skip) then true, restore_esp vsa
        else false,vsa
        
end;;



