let sum = List.fold_left (+) 0;;


let size = 25 

let columns = 
  [| [7;2;1;1;7];
     [1;1;2;2;1;1];
     [1;3;1;3;1;3;1;3;1];
     [1;3;1;1;5;1;3;1];
     [1;3;1;1;4;1;3;1];
     [1;1;1;2;1;1];
     [7;1;1;1;1;1;7];
     [1;1;3];
     [2;1;2;1;8;2;1];
     [2;2;1;2;1;1;1;2];
     [1;7;3;2;1];
     [1;2;3;1;1;1;1;1];
     [4;1;1;2;6];
     [3;3;1;1;1;3;1];
     [1;2;5;2;2];
     [2;2;1;1;1;1;1;2;1];
     [1;3;3;2;1;8;1];
     [6;2;1];
     [7;1;4;1;1;3];
     [1;1;1;1;4];
     [1;3;1;3;7;1];
     [1;3;1;1;1;2;1;1;4];
     [1;3;1;4;3;3];
     [1;1;2;2;2;6;1];
     [7;1;3;2;1;1] |];;

let lines =
  [| [7;3;1;1;7];
     [1;1;2;2;1;1];
     [1;3;1;3;1;1;3;1];
     [1;3;1;1;6;1;3;1];
     [1;3;1;5;2;1;3;1];
     [1;1;2;1;1];
     [7;1;1;1;1;1;7];
     [3;3];
     [1;2;3;1;1;3;1;1;2];
     [1;1;3;2;1;1];
     [4;1;4;2;1;2];
     [1;1;1;1;1;4;1;3];
     [2;1;1;1;2;5];
     [3;2;2;6;3;1];
     [1;9;1;1;2;1];
     [2;1;2;2;3;1];
     [3;1;1;1;1;5;1];
     [1;2;2;5];
     [7;1;2;1;1;1;3];
     [1;1;2;1;2;2;1];
     [1;3;1;4;5;1];
     [1;3;1;3;10;2];
     [1;3;1;1;6;6];
     [1;1;2;1;1;2];
     [7;2;1;2;5] |];;

let know_black = 
  [[3;4;12;13;21], 3;
   [6;7;10;14;15;18], 8;
   [6;11;16;20], 16;
   [3;4;9;10;15;20;21],21]



(* B B B B 
   B W W B
   B W W B
   B B B B *)
(*
let size = 4

let columns = 
  [| [4];
     [1;1];
     [1;1];
     [4] |]

let lines =
  [| [4];
     [1;1];
     [1;1];
     [4] |] 

let know_black = []
*)
  
type cel = 
| W 
| B 

let int_of_ij i j = i*size + j
let var_of_ij i j = int_of_ij i j + 1

let n_cnf = ref (size * size + 1) 

let disj_extra = ref [] 

let new_var () = 
  let v = !n_cnf in
  disj_extra := v :: !disj_extra;
  incr n_cnf;
  v

let pp_line l =
  List.iter (Format.printf "%i ") l;
  Format.printf "0\n"

let partial = Array.make (size * size) None 

let sign_color c = if c = W then -1 else 1 

exception IncompatibleColor

let check_ij i j c = 
  match partial.(int_of_ij i j) with
  | None -> ()
  | Some c' -> if c <> c' then raise IncompatibleColor

let cel_to_pos get_ij l =
  let k = ref 0 in
  let res = ref [] in
  let rec aux l = 
    match l with
    | [] -> ()
    | (c,n) :: l ->
      for x = 1 to n do
        let i,j = get_ij !k in
        check_ij i j c;
        res := (sign_color c) * (var_of_ij i j) :: !res;
        incr k
      done;
      aux l in
  aux l;
  assert (!k = size);
  !res

let cnf l = 
  (* v <=> /\ l *)
  let v = new_var () in
  pp_line (v::List.map (fun x -> -x) l); (* ( /\ l => v ) = 
                                            -(/\ l) \/ v  =
                                            \/ -l \/ v *)
  List.iter (fun a -> pp_line [-v;a]) l  (* v => /\ l  = 
                                            /\ v => l   = 
                                            /\ -v \/ l *) 



let setit to_ij l = 
  let n_b = sum l in
  let min_w = List.length l - 1 in
  assert (0 <= n_b && n_b <= size);
  let extra_w = size - n_b - min_w in
  if extra_w = 0 then
    let rec set k l = 
      match l with
      | [] -> assert false
      | [0] -> assert (k = size)
      | n::l ->
        let l, c = 
          if n = 0 then l, W else (n-1::l, B) in
        partial.(to_ij k) <- Some c;
        set (k+1) l in
    set 0 l

let print_partial () =
  for i=0 to size - 1 do
    for j=0 to size - 1 do
      match partial.(int_of_ij i j) with
      | None   -> Format.printf "_ "
      | Some B -> Format.printf "B "
      | Some W -> Format.printf "W "
    done;
    Format.printf "@."
  done

let doit get_ij l = 
  let n_b = sum l in
  let min_w = List.length l - 1 in
  assert (0 <= n_b && n_b <= size);
  let extra_w = size - n_b - min_w in
  disj_extra := [];
  let rec aux accu l min extra_w =
    match l with 
    | [] -> 
      begin 
        try
          cnf (cel_to_pos get_ij ((W,extra_w) :: accu))
        with IncompatibleColor -> ()
      end
    | b::l -> 
      for i = 0 to extra_w do
        aux ((B, b) :: (W,min + i) :: accu) l 1 (extra_w - i)
      done in
  aux [] (List.rev l) 0 extra_w;
  Format.eprintf "%i@." (List.length !disj_extra);
  pp_line !disj_extra

let countit s k l = 
  let n_b = sum l in
  let min_w = List.length l - 1 in
  assert (0 <= n_b && n_b <= size);
  let extra_w = size - n_b - min_w in
  Format.printf "%s %i extra = %i@." s k extra_w 

let doline j = doit (fun i -> (i, j)) 
let docol i  = doit (fun j -> (i, j))

let countline j = countit "line" j
let countcol i  = countit "col " i

let setline j = setit (fun i -> int_of_ij i j) 
let setcol i  = setit (fun j -> int_of_ij i j)

let init_partial () = 
  List.iter (fun (is,j) ->
    List.iter (fun i -> partial.(int_of_ij i j) <- Some B) is) know_black;
  for i = 0 to size-1 do (setline i) lines.(i) done;
  for i = 0 to size-1 do (setcol i) columns.(i) done 
 




(* Avec simplication *)

let _ = 
  init_partial ();
  for i = 0 to Array.length partial - 1 do
    match partial.(i) with
    | None -> ()
    | Some c -> 
      Format.printf "%i 0\n" ((sign_color c) * (i+1))
  done;
  for i = 0 to size-1 do (doline i) lines.(i) done;
  for i = 0 to size-1 do (docol i) columns.(i) done
  
(* Sans simplification *)
(*
let _ = 
  let pp_known_black i j = Format.printf "%i 0\n" (sign_color B * var_of_ij i j) in
  let pp_l_black (is,j) = List.iter (fun i -> pp_known_black i j) is in
  List.iter pp_l_black know_black;
  for i = 0 to size-1 do (doline i) lines.(i) done;
  for i = 0 to size-1 do (docol i) columns.(i) done 
*)
(*
Avec simplification 
generation : 0.717s
nb var     : 28424
wc -l      : 722955 
glucose    : 0.631563 s

Sans simplification
generation : 4.126s
nb var     : 167815
wc - l     : 4347012
glucose    : 7.92508 s

*)
  
