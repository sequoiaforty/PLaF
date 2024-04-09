open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  (*TREE CODE HERE WORKS*)
  | IsEmpty ( e ) -> eval_expr e >>= tree_of_treeVal >>= fun x1 -> return (BoolVal (x1 = Empty))
  | EmptyTree ( _t ) ->
    return (TreeVal Empty)
  | Node ( e1 , e2 , e3 ) ->
    eval_expr e1 >>= fun n1 ->
    eval_expr e2 >>= tree_of_treeVal >>= fun n2 ->
    eval_expr e3 >>= tree_of_treeVal >>= fun n3 ->
    return (TreeVal (Node (n1, n2, n3)))
  | CaseT ( e1 , e2 , id1 , id2 , id3 , e3 ) ->
    eval_expr e1 >>= tree_of_treeVal >>= fun f1 ->
    (match f1 with
      | Empty -> eval_expr e2
      | Node(a, l, r) ->
    extend_env id1 a >>+
    extend_env id2 (TreeVal l) >>+
    extend_env id3 (TreeVal r) >>+
    eval_expr e3)
    (*RECORD CODE HERE*)
  | Record( fs ) -> return (RecordVal (List.map
  (fun x ->
    match x with
    | (stringx, (booly, (exprz)) -> (stringx, eval_expr exprz)
    ))
  fs))
  (*| Record ( fs ) -> List.fold_left (fun acc (stringx, (booly, (eval_expr exprz))) -> ExtendEnv(stringx,exprz,acc)) EmptyEnv fs >>=
  eval_exprs fs >>= fun x ->
    (match (convert_record_to_list x) with
    | (fname::fname_tl, fvalue::fvalue_tl) -> eval_expr (RecordVal (convert_list_to_record (fname_tl, fvalue_tl)))
    | _ -> [])    *)
  (*| Proj (e , id ) -> eval_expr e >>= convert_record_to_list >>= fun frames ->
    (match frames with
    | (fname, fvalue)::tl -> if ((eval_expr fname) = (eval_expr id))
                              then (eval_expr fvalue)
                              else (eval_expr (Proj (Record (convert_list_to_record tl), id)))
    | [] -> "Proj : field does not exist")   *)
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | _ -> failwith "Not implemented yet!"
and
  eval_exprs : expr list -> ( exp_val list ) ea_result =
  fun es ->
  match es with
  | [] -> return []
  | h :: t -> eval_expr h >>= fun i ->
  eval_exprs t >>= fun l ->
  return ( i :: l )

let rec eval_exprs : expr list -> ( exp_val list ) ea_result =
  fun es ->
  match es with
  | [] -> return []
  | h :: t -> eval_expr h >>= fun i -> eval_exprs t >>= fun l -> return ( i :: l )

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e


(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


