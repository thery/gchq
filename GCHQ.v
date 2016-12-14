From SMTCoq Require Import SMTCoq.
From SMTCoq Require Import PArray Int63.
Require Import Int31 ZArith.

From mathcomp Require Import ssreflect ssrnat seq ssrbool.

(* We encode the colour as booleans *)
Definition white := true.
Definition black := false.

Open Scope nat_scope.

Definition count d (f : nat -> bool) :=
  let fix c m i n :=
    if m is m1.+1 then 
    if ~~ f i then c m1 i.+1 n.+1 else 
    if n is _.+1 then n :: c m1 i.+1 0 else c m1 i.+1 0
    else if n is _.+1 then [::n] else [::] in c d  0 0.

Compute count 6 (nth black  [:: white; white; black; black; black; white]).

Definition count_row (f : nat -> nat -> bool) d i := count d (f i).
Definition count_col (f : nat -> nat -> bool) d i := count d (fun j => f j i).

Definition test_m := 
   [:: [:: white; black; white; black; white; white]; 
       [:: white; white; white; white; white; white];
       [:: white; white; black; black; white; white];
       [:: white; white; black; black; white; white];
       [:: white; white; white; white; white; white];
       [:: white; white; white; white; white; white]
    ].

Definition l2f l i j := nth black (nth [::] l i) j.

Compute count_row (l2f test_m) 6 0.
Compute count_col (l2f test_m) 6 5.

Check ncons.

Compute ncons 3 false [::true].
Print form.
Inductive boolb := 
|  trueb 
| falseb 
| eqb (_ _ : boolb)
| andb (_ : seq boolb) 
| implb (_ : seq boolb) 
| orb (_ : seq boolb) 
| negb (_ : boolb) 
| varb (_ : int).


Definition gen_constr l d :=
 let fix aux res accu l extra m :=
  if l is n :: l1 then
    let fix f i r :=
        let r1 := aux r (ncons n black (ncons (i + m) white accu)) l1 (extra - i) 1 in 
        if i is i1.+1 then f i1 r1
        else r1  
     in f extra res
  else  (ncons extra white accu) :: res
  in
   aux [::] [::] (rev l) (d - (size l).-1 -  foldl addn 0 l) 0.

Compute (gen_constr) [::2] 4.

Definition nat2int n := 
  of_Z (Z_of_nat n).

Definition int_iota n k := 
  map nat2int (iota n k).

Definition of_ij d i j := varb (i * d + j).

Definition gen_form f l d :=
  let ll := gen_constr l d in
  orb (map (fun l =>
             andb (map
              (fun p =>
                let: (i,b) := p in
                  (if b then (f i) else negb (f i)))
              (zip (int_iota 0 d) l)))  ll).

Compute gen_form (fun i => varb (0 + i)%int) [::2] 4.

(*

Definition size := 25. 

Definition columns := 
  [::[::7;2;1;1;7];
     [::1;1;2;2;1;1];
     [::1;3;1;3;1;3;1;3;1];
     [::1;3;1;1;5;1;3;1];
     [::1;3;1;1;4;1;3;1];
     [::1;1;1;2;1;1];
     [::7;1;1;1;1;1;7];
     [::1;1;3];
     [::2;1;2;1;8;2;1];
     [::2;2;1;2;1;1;1;2];
     [::1;7;3;2;1];
     [::1;2;3;1;1;1;1;1];
     [::4;1;1;2;6];
     [::3;3;1;1;1;3;1];
     [::1;2;5;2;2];
     [::2;2;1;1;1;1;1;2;1];
     [::1;3;3;2;1;8;1];
     [::6;2;1];
     [::7;1;4;1;1;3];
     [::1;1;1;1;4];
     [::1;3;1;3;7;1];
     [::1;3;1;1;1;2;1;1;4];
     [::1;3;1;4;3;3];
     [::1;1;2;2;2;6;1];
     [::7;1;3;2;1;1]].

Definition lines :=
  [:: [::7;3;1;1;7];
     [::1;1;2;2;1;1];
     [::1;3;1;3;1;1;3;1];
     [::1;3;1;1;6;1;3;1];
     [::1;3;1;5;2;1;3;1];
     [::1;1;2;1;1];
     [::7;1;1;1;1;1;7];
     [::3;3];
     [::1;2;3;1;1;3;1;1;2];
     [::1;1;3;2;1;1];
     [::4;1;4;2;1;2];
     [::1;1;1;1;1;4;1;3];
     [::2;1;1;1;2;5];
     [::3;2;2;6;3;1];
     [::1;9;1;1;2;1];
     [::2;1;2;2;3;1];
     [::3;1;1;1;1;5;1];
     [::1;2;2;5];
     [::7;1;2;1;1;1;3];
     [::1;1;2;1;2;2;1];
     [::1;3;1;4;5;1];
     [::1;3;1;3;10;2];
     [::1;3;1;1;6;6];
     [::1;1;2;1;1;2];
     [::7;2;1;2;5]].

Definition known_black := 
  [::([::3;4;12;13;21], 3);
   ([::6;7;10;14;15;18], 8);
   ([::6;11;16;20], 16);
   ([::3;4;9;10;15;20;21],21)].
*)

Definition size := 4.
Definition isize := nat2int size. 

Definition columns := 
  [::[::];
     [::2];
     [::2];
     [::]
  ]. 

Definition lines := 
  [::[::];
     [::2];
     [::2];
     [::]
  ]. 

Definition known_black : seq (seq nat * nat) := 
  [::].

Definition gen_columns f :=
  andb (map 
    (fun p => let: (i, l) := p in  (gen_form (f i) l size))
   (zip (int_iota 0 size) columns)).


Definition gen_lines f :=
  andb (map 
    (fun p => let: (j, l) := p in (gen_form (fun i => f i j) l size))
   (zip (int_iota 0 size) lines)).


Definition gen_black f :=
   andb (map
    (fun p => let: (l, j) := p in 
     (andb (map (fun i => (f (nat2int i) (nat2int j))) l)))
    known_black).

Definition gen_all f := andb [::gen_black f; gen_lines f; gen_columns f].

Compute gen_all (of_ij isize).

Definition gen_sol f (sol : seq (seq bool)) :=
 andb (map
  (fun p => 
     let: (j, l) := p in
      andb (map
         (fun p1 => 
               let: (i, b) := p1 in
               (if b then (f i j) else negb (f i j)))
       (zip (int_iota 0 size) l)))
   (zip (int_iota 0 size) sol)).


(*
Fixpoint bsize r f := match f with
 trueb => r | 
 falseb => r | 
 orb f1 f2 =>  (bsize (bsize (r + 1) f1) f2)%Z |
 andb f1 f2 => (bsize (bsize (r) f1) f2)%Z |
 negb f1 => (bsize (r) f1)%Z |
 _ => (r)%Z
 end.
*)

(*

Eval vm_compute in 
  map
  (fun i => 
    (i, bsize 0%Z (gen_form _ trueb falseb negb andb orb (varb 7) (nth [::] columns i) size)))
  (iota 0 size).
*)

(*
Time Definition foo := 
 Eval vm_compute in gen_form _ trueb falseb negb andb orb (varb 7) (nth [::] columns 1) size.
 

Eval vm_compute in 
  map
  (fun i => 
    (i, bsize 0%Z (gen_form _ trueb falseb negb andb orb (varb 7) (nth [::] lines i) size)))
  (iota 0 size).


Eval vm_compute in bsize 0 (gen_all boolb trueb falseb negb andb orb varb).
*)

Definition sol := [:: [:: true; true; true; true];
                     [:: true; false; false; true];
                     [:: true; false; false; true];
                     [:: true; true; true; true]].

Definition formula :=
Eval compute in 
  eqb
    (gen_all (of_ij isize))
    (gen_sol (of_ij isize) sol).

Print form.
Print array.

Print Map.bst.

Definition idt := 0%int.
Definition idf := 1%int.

Print form.


Definition aMap t := (seq (int * t) * int)%type.
Definition aset {t} (m : aMap t) f := 
  let: (l, n) := m in (((n + 1)%int, f) :: l, (n + 1)%int).
Definition maset {t}  (m : aMap t) f  :=
  let m1 := aset m f in (m1, (2 * snd m1)%int).

Inductive sform : Type :=
    sFatom : int -> sform
  | sFtrue : sform
  | sFfalse : sform
  | sFand : seq int -> sform
  | sFor : seq int -> sform
  | sFimp : seq int -> sform
  | sFxor : int -> int -> sform
  | sFiff : int -> int -> sform
  | sFite : int -> int -> int -> sform.


Definition map_fold {T1 T2 T3 : Type} (f : T1 -> T2 -> T1 * T3) 
                    (v : T1) (l : seq T2) : T1 * seq T3 :=
  foldl (fun p v2 => 
           let: (v1, v3)  := f (fst p) v2 in
           (v1, v3 :: snd p)) (v, [::]) l.

Print form.
     

Fixpoint hash_boolb (m : aMap sform) (f : boolb) : aMap sform * int  :=
  match f with 
|  trueb => (m, idt)
| falseb => (m, idf) 
| eqb f1 f2  =>
    let: (m1, n1) := hash_boolb m f1 in
    let: (m2, n2) := hash_boolb m1 f2 in
    maset m2 (sFiff n1 n2)
| andb fs => let: (m1, l) := map_fold hash_boolb m fs in
    maset m1 (sFand l)
| orb fs => let: (m1, l) := map_fold hash_boolb m fs in
    maset m1 (sFor l)
| implb fs => let: (m1, l) := map_fold hash_boolb m fs in
    maset m1 (sFimp l) 
| negb (negb f1) =>  hash_boolb m f1
| negb f1 =>
   let: (m1, n1) := hash_boolb m f1 in
   (m1, n1 + 1)%int
| varb i =>
   (m, 2 * (i + 2))%int31
end.

Print size.
Locate size.

Definition all_hash_boolp (f : boolb) :=
  let s2 := size * size in
  let l := 
   (idf, sFfalse) :: (idt, sFtrue) ::
   (map (fun i => ((i + 2)%int, sFatom i)) (int_iota 0 s2)) in
  hash_boolb (l, nat2int s2.+1) f.


Compute all_hash_boolp formula.

