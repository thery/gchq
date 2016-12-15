
(* invariant known land color = color *) 

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

(*
let size = 4 
let columns = [| []; [2]; [2]; [] |]
let lines   = [| []; [2]; [2]; [] |]
let know_black = []
*)

(*
let size = 2 
let columns = [| [1]; [1] |]
let lines   = [| [1]; [1] |]
let know_black = []
*)

(*
let size = 4 
let columns = [| [1;1]; [2];   [1;1]; [1;1] |]
let lines   = [| [1;1]; [1;1]; [1;1]; [1;1] |]
let know_black = [[1],0]
*)


type row = 
  { known : int;
    color : int }

let mk_row k c = {
  known = k;
  color = k land c
}
  
let initial_row = {
  known = (-1) lsl size;
  color = 0;
}

type puzzle = row array 

type constraint_row = int
type disj_row = constraint_row list 

let bit v i = (v lsr i) land 1 

let print_row row = 
  for i = 0 to size - 1 do
    let k = bit row.known i in
    let c = bit row.color i in
    Format.printf "%s "
      (if k = 1 then
         if c = 1 then "B" else "W"
       else "_")
  done;
  Format.printf "\n"

let print puzzle = 
  Array.iter print_row puzzle

let check_valid row cr =
  row.color = (cr land row.known)

let filter row (disj_row:disj_row) = 
  let rec aux accu disj_row = 
    match disj_row with 
    | [] -> accu
    | cr :: disj_row1 ->
      if check_valid row cr then aux (cr::accu) disj_row1
      else aux accu disj_row1 in
  aux [] disj_row

exception UnSat

let print_disj disj = 
  List.iter (fun c -> print_row {known = (-1); color = c }) disj
        
let update_row row disj_row1 = 
  let disj_row = filter row disj_row1 in
  match disj_row with
  | [] -> raise UnSat
  | c :: disj_row ->
    let rec aux k disj_row = 
      match disj_row with
      | [] -> mk_row k c
      | c' :: disj_row ->
        let k' = k land (lnot (c lxor c')) in
        if k' = row.known then row
        else aux k' disj_row
    in
    let row1 = aux (-1) disj_row in
    row1, c::disj_row

let update_lines puzzle constraints =
  let progress = ref false in
  for i = 0 to size - 1 do
    let row = puzzle.(i) in
    let row', disj = update_row puzzle.(i) constraints.(i) in
    constraints.(i) <- disj;
    if  row.known <> row'.known then begin
      puzzle.(i) <- row'; 
      progress := true
    end
  done;
  !progress

let get_col puzzle i = 
  let k = ref initial_row.known  in
  let c = ref initial_row.color  in
  for j = 0 to size - 1 do
    let row = puzzle.(j) in
    k := !k lor ((bit row.known i) lsl j);
    c := !c lor ((bit row.color i) lsl j)
  done; 
  mk_row !k !c

let set_col puzzle i row = 
  for j = 0 to size - 1 do
    let k = bit row.known j in
    if k = 1 then
      let line = puzzle.(j) in
      let i1 = 1 lsl i in
      let nk = line.known lor i1 in
      let nc = 
        (line.color land (lnot i1)) lor 
          ((bit row.color j) lsl i) in
      let nline = mk_row nk nc in
      puzzle.(j) <- nline
  done
   
let update_cols puzzle constraints =
  let progress = ref false in
  for i = 0 to size - 1 do
    let row = get_col puzzle i in
    let row', disj = update_row row constraints.(i) in
    constraints.(i) <- disj;
    if row.known <> row'.known then begin
      set_col puzzle i row'; 
      progress := true
    end
  done;
  !progress


let check_full puzzle = 
  let forall = ref true in
  Array.iter (fun row -> forall := !forall && row.known = (-1)) puzzle;
  !forall

let solve puzzle lconstr cconstr =
  let rec aux i = 
    Format.printf "i = %i@." i;
    let p1 = update_lines puzzle lconstr in
    let p2 = update_cols  puzzle cconstr in
    if p1 || p2 then aux (i+1) in
  aux 0;
  if check_full puzzle then Format.printf "OK@."
  else  Format.printf "ERROR@.";
  print puzzle

(* ------------------------------------------------------- *)

let sum = List.fold_left (+) 0

type cel = 
| W 
| B 

let get_color puzzle i j = 
  let row = puzzle.(j) in
  let k = bit row.known i in
  if k = 1 then
    let c = bit row.color i in
    if c = 1 then Some B else Some W
  else None

let set_color puzzle i j c = 
  let row = puzzle.(j) in
  let k = row.known lor (1 lsl i) in
  let c = 
    if c = B then row.color lor (1 lsl i)
    else row.color land (lnot (1 lsl i)) in
  let row = { known = k; color = c } in
  puzzle.(j) <- row

let add_color puzzle get_ij c (k,colors) =
  let i,j = get_ij k in
  match get_color puzzle i j with
  | Some c' when c <> c' -> None
  | _ ->
    let colors = 
      if c = B then colors lor (1 lsl k)
      else colors in
    Some (k-1, colors)

let rec add_colors puzzle get_ij c n kcolors = 
  if n = 0 then Some kcolors 
  else
    match add_color puzzle get_ij c kcolors with
    | None -> None
    | Some kcolors -> add_colors puzzle get_ij c (n-1) kcolors
  
let doit puzzle get_ij l = 
  let n_b = sum l in
  let min_w = List.length l - 1 in
  let extra_w = size - n_b - min_w in
  let disj_extra = ref [] in

  let rec aux kcolors l min extra_w =
    match l with 
    | [] -> disj_extra := snd kcolors :: !disj_extra
    | b::l -> 
      for i = 0 to extra_w do
        match add_colors puzzle get_ij W (min+i) kcolors with
        | None -> ()
        | Some kcolors ->
          match add_colors puzzle get_ij B b kcolors with
          | None -> ()
          | Some kcolors -> aux kcolors l 1 (extra_w - i)
      done in
  aux (size-1, 0) (List.rev l) 0 extra_w;
  !disj_extra

let doline puzzle j = doit puzzle (fun i -> (i, j)) 
let docol puzzle i  = doit puzzle (fun j -> (i, j))

let setit puzzle to_ij l = 
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
        let i,j = to_ij k in
        set_color puzzle i j c;
        set (k+1) l in
    set 0 l

let setline puzzle j = setit puzzle (fun i -> i, j) 
let setcol puzzle i  = setit puzzle (fun j -> i, j)

let init_partial puzzle = 
  List.iter (fun (is,j) ->
    List.iter (fun i -> set_color puzzle i j B) is) know_black;
  print puzzle;
  Format.printf "@.";
  for i = 0 to size-1 do (setline puzzle i) lines.(i) done;
  for i = 0 to size-1 do (setcol puzzle i) columns.(i) done 
 

let _ = 
  let puzzle = Array.make size initial_row in
  init_partial puzzle;
  print puzzle;
  Format.printf "@.";
  let lconstr = Array.init size (fun i -> doline puzzle i lines.(i)) in
  let cconstr = Array.init size (fun i -> docol puzzle i columns.(i))  in
  try 
    solve puzzle lconstr cconstr 
  with UnSat ->
    Format.printf "UnSat@.";
    print puzzle


          




  
    
  
  
