type addr = (int*int)
type call_id = int
type call_name = string
type call_string = ((addr) * call_name * call_id)
type call_stack = call_string list

type basic_block = (int * (int list)) 
type edge = (int * int)

let compare_call_string ((addr,it),name,id) ((addr2,it2),name2,id2) =
        match Pervasives.compare addr addr2 with
        | 0 -> begin match Pervasives.compare it it2 with
               | 0 -> 
                        begin
                        match Pervasives.compare name name2 
                        with 0 -> Pervasives.compare id id2
                        | l -> l
                        end
                | l -> l
                end
        | l -> l
                
let rec compare_call_stack s1 s2 =
        match s1,s2 with
        | [] , [] -> 0
        | [] , _ ->  1
        | _ , [] -> (-1)
        | hd::tl, hd2::tl2 ->
                match compare_call_string hd hd2 with
                | 0 -> compare_call_stack tl tl2
                | l -> l

let pp_call_string ((addr,it),f,_) = Printf.sprintf "0x%x:%d:%s" addr it f

let pp_call_stack cs = 
        String.concat " " (List.map (fun x -> pp_call_string x) cs)
