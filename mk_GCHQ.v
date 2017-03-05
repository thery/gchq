From SMTCoq Require Import SMTCoq.
From SMTCoq Require Import PArray Int63.
Require Import GCHQ.

Definition finterp h1 h9 h2 h3 h4 h5 h6 h7 h8 :=
  hinterp h2 h3 h4 h5 h6 h7 h8 h9 h1.

Definition tr (z : Z) : bool.
exact true.
Qed.

Definition tt (i : int) := tr (to_Z i).

Definition pb := pb1.

Time Definition tt1 :=
   Eval vm_compute in  finterp (gen_all pb) tt.

Time Definition tt2 :=
  Eval lazy delta[tt1 mk_andb mk_orb 
     seq.head seq.foldl seq.behead] iota beta in 
  tt1 true false 
  Bool.eqb mk_andb mk_implb mk_orb Datatypes.negb.

Ltac end_tac v :=
  let w := eval compute in v in
idtac w;
(timeout 30 (
    try (
     assert (Datatypes.implb tt2 ((tr w))); [
                          unfold tt2; verit | idtac]; 
                                  idtac "ho"; fail 1);
      idtac "false"; exact false)) ||
idtac "true"; exact true.

Ltac col i j n :=
  let u := constr:(Zeq_bool j n) in 
  let v := eval compute in u in
     match v with true => exact nil
                 |false => apply cons; 
                           [end_tac (i * n + j)%Z|
                            col i (j + 1)%Z n]
     end.

Ltac row i n :=
  let u := constr:(Zeq_bool i n) in 
  let v := eval compute in u in
     match v with true => exact nil
                 |false => apply cons; 
                           [col i 0%Z n|
                            row (i + 1)%Z n]
     end.

Definition s0 : list bool.
col 0 0 (Z.of_nat (p_size pb)).
Defined.
