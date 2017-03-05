From SMTCoq Require Import SMTCoq.
From SMTCoq Require Import PArray Int63.
Require Import GCHQ.
Import Datatypes.

Notation "'X'"  := (id true).

Notation "'O'"  := (id false).

Definition sol_pb1 := 
(
 (O :: O :: O :: O :: O :: O :: O :: X :: O :: O :: O :: X :: X :: X :: O :: X :: O :: X :: O :: O :: O :: O :: O :: O :: O :: nil) ::
 (O :: X :: X :: X :: X :: X :: O :: X :: O :: O :: X :: O :: O :: X :: X :: X :: X :: X :: O :: X :: X :: X :: X :: X :: O :: nil) ::
 (O :: X :: O :: O :: O :: X :: O :: X :: X :: X :: X :: X :: O :: O :: O :: X :: O :: X :: O :: X :: O :: O :: O :: X :: O :: nil) ::
 (O :: X :: O :: O :: O :: X :: O :: X :: O :: X :: X :: O :: O :: O :: O :: O :: O :: X :: O :: X :: O :: O :: O :: X :: O :: nil) ::
 (O :: X :: O :: O :: O :: X :: O :: X :: X :: O :: O :: O :: O :: O :: X :: O :: O :: X :: O :: X :: O :: O :: O :: X :: O :: nil) ::
 (O :: X :: X :: X :: X :: X :: O :: X :: X :: O :: O :: X :: X :: X :: X :: X :: X :: X :: O :: X :: X :: X :: X :: X :: O :: nil) ::
 (O :: O :: O :: O :: O :: O :: O :: X :: O :: X :: O :: X :: O :: X :: O :: X :: O :: X :: O :: O :: O :: O :: O :: O :: O :: nil) ::
 (X :: X :: X :: X :: X :: X :: X :: X :: O :: O :: O :: X :: X :: X :: O :: O :: O :: X :: X :: X :: X :: X :: X :: X :: X :: nil) ::
 (O :: X :: O :: O :: X :: O :: O :: O :: X :: X :: O :: X :: O :: X :: O :: O :: O :: X :: O :: X :: X :: O :: X :: O :: O :: nil) ::
 (O :: X :: O :: X :: X :: X :: X :: X :: X :: O :: O :: O :: X :: O :: O :: X :: X :: X :: X :: O :: X :: X :: X :: O :: X :: nil) ::
 (X :: O :: O :: O :: O :: X :: O :: X :: O :: O :: O :: O :: X :: O :: O :: X :: O :: X :: X :: X :: X :: O :: O :: X :: X :: nil) ::
 (X :: O :: X :: O :: X :: X :: X :: O :: X :: X :: X :: O :: X :: O :: X :: O :: O :: O :: O :: X :: O :: X :: O :: O :: O :: nil) ::
 (X :: X :: O :: O :: X :: X :: O :: X :: O :: X :: O :: X :: X :: X :: X :: X :: X :: O :: O :: X :: O :: O :: O :: O :: O :: nil) ::
 (X :: X :: X :: O :: O :: O :: X :: O :: O :: X :: O :: O :: X :: O :: O :: O :: O :: O :: O :: X :: O :: O :: O :: X :: O :: nil) ::
 (O :: X :: O :: O :: O :: O :: O :: O :: O :: O :: O :: X :: O :: X :: O :: X :: X :: O :: O :: X :: X :: X :: X :: O :: X :: nil) ::
 (X :: O :: O :: X :: O :: X :: X :: O :: O :: X :: X :: X :: O :: O :: X :: O :: O :: O :: X :: X :: X :: X :: X :: O :: X :: nil) ::
 (O :: O :: O :: X :: O :: X :: O :: X :: O :: X :: X :: O :: X :: X :: X :: X :: O :: O :: O :: O :: O :: X :: O :: X :: X :: nil) ::
 (X :: X :: X :: X :: X :: X :: X :: X :: O :: X :: X :: X :: O :: O :: X :: O :: O :: X :: X :: X :: O :: O :: O :: O :: O :: nil) ::
 (O :: O :: O :: O :: O :: O :: O :: X :: O :: X :: X :: O :: O :: X :: X :: X :: O :: X :: O :: X :: O :: X :: O :: O :: O :: nil) ::
 (O :: X :: X :: X :: X :: X :: O :: X :: O :: O :: X :: X :: O :: X :: X :: O :: O :: X :: X :: X :: O :: O :: X :: O :: X :: nil) ::
 (O :: X :: O :: O :: O :: X :: O :: X :: X :: X :: O :: O :: O :: O :: X :: X :: O :: O :: O :: O :: O :: X :: X :: O :: X :: nil) ::
 (O :: X :: O :: O :: O :: X :: O :: X :: O :: O :: O :: X :: O :: O :: O :: O :: O :: O :: O :: O :: O :: O :: X :: O :: O :: nil) ::
 (O :: X :: O :: O :: O :: X :: O :: X :: O :: X :: X :: O :: O :: O :: O :: O :: O :: X :: O :: O :: O :: O :: O :: O :: X :: nil) ::
 (O :: X :: X :: X :: X :: X :: O :: X :: X :: O :: O :: X :: X :: X :: X :: X :: X :: O :: X :: O :: X :: O :: O :: X :: X :: nil) ::
 (O :: O :: O :: O :: O :: O :: O :: X :: O :: O :: X :: X :: X :: O :: X :: O :: O :: X :: X :: X :: O :: O :: O :: O :: O :: nil) :: nil
).

Lemma verify_sol_pb1 : verify_sol pb1 sol_pb1.
Proof. by compute. Qed.

Lemma interp_free f u : 
  interp f u =
   let ff f := finterp u (fun x => f (to_Z x))
   in ff (fun x => f (Int63Op.of_Z x))
   true false 
  Bool.eqb mk_andb mk_implb mk_orb Datatypes.negb.
Proof.
simpl.
apply interp_ext; intro x.
by rewrite Int63Axioms.of_to_Z.
Qed.


Lemma sol_pb1_ok s : verify_sol pb1 s -> sol_pb1 = s.
Proof.
intro H.
apply (test_eq_correct pb1).
- by compute.
- by compute.
- by compute.
- by apply verify_sol_pb1.
- by exact H.
rewrite interp_free.
set (u := fun _ =>  _).
vm_compute in u.
set (ff := (fun _ => _)).
unfold u.
   lazy delta[is_true mk_andb mk_orb mk_implb 
     seq.head seq.foldl seq.foldr seq.behead] iota beta.
unfold is_true.
verit.
Qed.


(*
Definition pb := pb2.
Definition es : sol := nil.
Definition tr (z : Z) := true.


Time Definition tt1 f :=
   Eval vm_compute in  finterp (gen_all pb) (fun x => f (to_Z x)).


Time Definition tt2 :=
  Eval lazy delta[tt1 mk_andb mk_orb 
     seq.head seq.foldl seq.behead] iota beta in 
  tt1 tr true false 
  Bool.eqb mk_andb mk_implb mk_orb Datatypes.negb.

Ltac end_tac v :=
  let w := eval compute in v in
idtac w;
(timeout 40 (
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

Definition s : sol.
row 0 (Z.of_nat (p_size pb)).
Defined.

Lemma verify_sol_s : verify_sol pb s.
Proof. by compute. Qed.

Lemma interp_free f u : 
  interp f u =
   let ff f := finterp u (fun x => f (to_Z x))
   in ff (fun x => f (Int63Op.of_Z x))
   true false 
  Bool.eqb mk_andb mk_implb mk_orb Datatypes.negb.
Proof.
simpl.
apply interp_ext; intro x.
by rewrite Int63Axioms.of_to_Z.
Qed.


Lemma s_ok s1 : verify_sol pb s1 -> s = s1.

Proof.
intro H.
apply (test_eq_correct pb).
- by compute.
- by compute.
- by compute.
- by apply verify_sol_s.
- by exact H.
rewrite interp_free.
set (u := fun _ =>  _).
compute in u.
set (ff := (fun _ => _)).
unfold u.
   lazy delta[is_true mk_andb mk_orb mk_implb 
     seq.head seq.foldl seq.foldr seq.behead] iota beta.
verit.
Qed.

*)