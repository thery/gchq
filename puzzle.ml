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

let sign_color c = if c = W then -1 else 1 

let cel_to_pos get_ij l =
  let k = ref 0 in
  let res = ref [] in
  let rec aux l = 
    match l with
    | [] -> ()
    | (c,n) :: l ->
      for i = 1 to n do
        res := (sign_color c) * (get_ij !k) :: !res;
        incr k
      done;
      aux l in
  aux l;
  assert (!k = size);
  !res

let of_ij (i,j) = (i*size + j + 1) 

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

let cnf l = 
  (* v <=> /\ l *)
  let v = new_var () in
  pp_line (v::List.map (fun x -> -x) l); (* ( /\ l => v ) = 
                                            -(/\ l) \/ v  =
                                            \/ -l \/ v *)
  List.iter (fun a -> pp_line [-v;a]) l   (* v => /\ l  = 
                                            /\ v => l   = 
                                            /\ -v \/ l *) 
    
let doit get_ij l = 
  let n_b = sum l in
  let min_w = List.length l - 1 in
  assert (0 <= n_b && n_b <= size);
  let extra_w = size - n_b - min_w in
  disj_extra := [];
  let rec aux accu l min extra_w =
    match l with 
    | [] -> 
      cnf (cel_to_pos get_ij ((W,extra_w) :: accu))
    | b::l -> 
      for i = 0 to extra_w do
        aux ((B, b) :: (W,min + i) :: accu) l 1 (extra_w - i)
      done in
  aux [] (List.rev l) 0 extra_w;
  pp_line !disj_extra


let doline j = doit (fun i -> of_ij (i,j)) 
let docol i  = doit (fun j -> of_ij (i,j))

let _ = 
  let pp_known_black ij = Format.printf "%i 0\n" (sign_color B * of_ij ij) in
  let pp_l_black (is,j) = List.iter (fun i -> pp_known_black (i,j)) is in
  List.iter pp_l_black know_black;
  for i = 0 to size-1 do (doline i) lines.(i) done;
  for i = 0 to size-1 do (docol i) columns.(i) done



   


  
