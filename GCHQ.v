(*
From SMTCoq Require Import SMTCoq.
From SMTCoq Require Import PArray Int63.
*)

From SMTCoq Require  Int63.
Require Import Int31 ZArith.
From mathcomp Require Import all_ssreflect.

Local Notation int := Int63Native.int.

(*****************************************************************************)
(*                                                                           *)
(*                         Misc THMs                                         *)
(*                                                                           *)
(*****************************************************************************)


Lemma big_rcons (R : Type) (idx : R) (op :  Monoid.com_law idx)
     (I : Type) (i : I) (r : seq I) 
     (P : pred I) (F : I -> R)  (x := \big[op/idx]_(j <- r | P j) F j) :
   \big[op/idx]_(j <- (rcons r i) | P j) F j =
   (if P i then op (F i) x else x).
Proof.
rewrite {}/x; elim: r => /= [|a r IH]; first by rewrite big_cons.
rewrite !big_cons IH.
do 2 case : (P _) => //.
by rewrite !Monoid.mulmA [op (F a) _]Monoid.mulmC.
Qed.

Lemma big_rev (R : Type) (idx : R) (op :  Monoid.com_law idx)
     (I : Type) (r : seq I) (P : pred I) (F : I -> R) : 
   \big[op/idx]_(j <- rev r | P j) F j =
   \big[op/idx]_(j <- r | P j) F j.
Proof.
elim: r => //= u r IH.
by rewrite rev_cons big_rcons big_cons IH.
Qed.

Lemma foldl_addnA a b l :
  foldl addn (a + b) l = a + foldl addn b l.
Proof.
by elim: l a b => //= c l IH a b; rewrite -addnA IH.
Qed.

Lemma foldl_addn l : foldl addn 0 l = \sum_(i <- l) i.
Proof.
elim: l => /= [|a l IH] ; first by rewrite big_nil.
by rewrite big_cons -IH addnC foldl_addnA.
Qed.

Lemma rev_nseq (T : Type) (t : T) n : rev (nseq n t) = nseq n t.
Proof.
apply: (@eq_from_nth _ t) => [|i].
  by rewrite size_rev.
rewrite size_rev => Hi.
by rewrite nth_rev // !nth_nseq !if_same.
Qed.

Lemma iota_rcons a b :
  iota a b.+1 = rcons (iota a b) (a + b).
Proof.
rewrite /=; elim: b a => /= [a|b IH a].
  by rewrite addn0.
by rewrite IH addnS.
Qed.

Definition nat2int n := 
  Int63Op.of_Z (Z_of_nat n).

Definition int_iota n k := 
  map nat2int (iota n k).

Lemma int_iota_rcons a b :
  int_iota a b.+1 = rcons (int_iota a b) (nat2int (a + b)).
Proof.
by rewrite /int_iota iota_rcons map_rcons.
Qed.

Lemma List_in_rcons (A : Type) (a b : A) l :
  List.In a (rcons l b) -> a = b \/ List.In a l.
Proof.
elim: l => [[] //-> //|c l IH /= [->|/IH [H|H]]//]; first by left.
- by right; left.
- by left.
by right; right.
Qed.

(* Décomposition of a list of boolean from the head *)
Inductive lboolD b : seq bool -> Type :=
  lboolB : forall n, lboolD b (nseq n b)
| lboolW : forall n l, lboolD b (ncons n b (~~b :: l)).

Lemma lbool_spec b l : lboolD b l.
Proof.
pose a := (fun x => x == ~~b).
pose m := find (fun x => x == ~~b) l.
case: (leqP (size l) m) => H.
  suff->: l = (nseq (size l) b) by apply: lboolB.
    apply: (@eq_from_nth _ false) => [|i Hi].
      by rewrite size_nseq.
    rewrite nth_nseq Hi.
   have /(@before_find _ false) : i < m by apply: leq_trans Hi _.
   by case: nth; case: (b).
suff->: l = ncons m b (~~b :: drop m.+1 l) by apply: lboolW.
apply: (@eq_from_nth _ false) => [|i Hi].
  by rewrite size_ncons /= size_drop -addSnnS addnC subnK.
rewrite nth_ncons /=.
case: leqP=> [H1|/(@before_find _ false)]; last by case: nth; case: (b).
rewrite -{1}(subnK H1).
case: (_ - _) => [/=|n].
  by apply/eqP/(@nth_find _ _ a); rewrite has_find.
by rewrite [RHS]/= nth_drop addnC addSnnS.
Qed.

(* Décomposition of a list of boolean from the tail *)
Inductive rboolD b : seq bool -> Type :=
  rboolB : forall n, rboolD b (nseq n b)
| rboolW : forall n l, rboolD b (l ++ (~~b ::nseq n b)).

Lemma rbool_spec b l : rboolD b l.
Proof.
rewrite -[l]revK.
case: (lbool_spec b (rev l)) => [n|n l1].
  by rewrite rev_nseq; apply: rboolB.
rewrite - cat_nseq rev_cat rev_nseq rev_cons cat_rcons.
by apply: rboolW.
Qed.

(* fold on natural numbers *)
Fixpoint foldi {T1 : Type} (f : nat -> T1 -> T1) i r :=
   let r1 := f i r in
   if i is i1.+1 then foldi f i1 r1
   else r1.

(*****************************************************************************)
(*                                                                           *)
(*                         Reification for boolean formulae                  *)
(*                                                                           *)
(*****************************************************************************)

Inductive boolb := 
| trueb 
| falseb 
| eqb (_ _ : boolb)
| andb (_ : seq boolb) 
| implb (_ : seq boolb) 
| orb (_ : seq boolb) 
| negb (_ : boolb) 
| varb (_ : int).


Definition mk_andb l := 
 foldl Datatypes.andb (head true l) (behead l).

Lemma mk_andb_nil : mk_andb [::] = true.
Proof. by []. Qed.

Lemma mk_andb_cons a l : mk_andb (a :: l) = a && mk_andb l.
Proof.
rewrite /mk_andb /=; case: l => //= [|a1 l1].
  by rewrite andbT.
elim : l1 a a1 => //= b l1 IH a a1.
by rewrite !IH andbA andbC.
Qed.

Lemma mk_andb_map (A : Type) (f : A -> bool) (l : seq A) :
  (forall i, List.In i l -> f i) ->
  mk_andb [seq f i | i <- l] = true.
Proof.
elim: l => //= a l IH H.
rewrite mk_andb_cons H; last by left.
rewrite IH // => i Hi.
by rewrite H //; right.
Qed.

Definition mk_orb l := 
 foldl Datatypes.orb (head false l) (behead l).

Lemma mk_orb_nil : mk_orb [::] = false.
Proof. by []. Qed.

Lemma mk_orb_cons a l : mk_orb (a :: l) = a || mk_orb l.
Proof.
rewrite /mk_orb /=; case: l => //= [|a1 l1].
  by rewrite orbF.
elim : l1 a a1 => //= b l1 IH a a1.
by rewrite !IH orbA orbC.
Qed.

Lemma mk_orb_map (A : Type) (f : A -> bool) (l : seq A) :
  (exists i, List.In i l /\ f i) -> mk_orb [seq f i | i <- l] = true.
Proof.
elim: l => [[i []//]|a l IH [j]] /= [[H1 | H1] H2].
  by rewrite mk_orb_cons H1 H2.
rewrite mk_orb_cons orbC IH //.
by exists j.
Qed.

Definition mk_implb l := 
 foldr Datatypes.implb (head true l) (behead l).

Lemma mk_implb_nil : mk_implb nil = true.
Proof. by []. Qed.

Lemma mk_implb_one a :  mk_implb [::a] = a.
Proof. by []. Qed.

Lemma mk_implb_two a b :  mk_implb [::b; a] = (Datatypes.implb a b).
Proof. by []. Qed.

Section hinterp.

Variable a_t : bool.
Variable a_f : bool.
Variable a_eq : bool -> bool -> bool.
Variable a_and : list bool -> bool.
Variable a_impl : list bool -> bool.
Variable a_or : list bool -> bool.
Variable a_neg : bool -> bool.

Fixpoint hinterp f exp {struct exp} := 
match exp with
|  trueb => a_t
| falseb => a_f
| eqb e1 e2 => a_eq (hinterp f e1) (hinterp f e2)
| andb es =>
    let es1 := map (hinterp f) es in a_and es1
| implb es =>
    let es1 := map (hinterp f) es in a_impl es1
| orb es =>
    let es1 := map (hinterp f) es in
    a_or es1
| negb e1 => a_neg (hinterp f e1) 
| varb i => f i
end.

Lemma hinterp_ext f1 f2 : 
  f1 =1 f2 -> forall exp, hinterp f1 exp = hinterp f2 exp.
Proof.
move=> H.
fix 1; case; try (by apply: erefl);
  try ((move=> l; (congr a_and || congr a_impl || congr a_or);
       move: l; fix 1; case); [apply: erefl | (move=> a l; congr (_ :: _));
     [apply: hinterp_ext|apply: hinterp_ext0]]).
- by move=> b1 b2 /=; congr (a_eq _ _); apply: hinterp_ext.
- by move=> b; congr a_neg; apply: hinterp_ext.
by move=> i; apply: H.
Qed.

End hinterp.

Definition interp (f : int -> bool) exp  := 
  hinterp Datatypes.true Datatypes.false
     Bool.eqb mk_andb mk_implb mk_orb Datatypes.negb f exp.


Definition zinterp (f : Z -> bool) exp  := 
  hinterp Datatypes.true Datatypes.false
     Bool.eqb mk_andb mk_implb mk_orb Datatypes.negb (f \o Int63Op.to_Z)  exp.

Lemma interp_ext f1 f2 exp :
  f1 =1 f2 -> interp f1 exp = interp f2 exp.
Proof.  by move=> Hi; apply: hinterp_ext. Qed.

Lemma interp_zinterp f exp :
  interp f exp =
  let zf := zinterp^~ exp in
  let zf1 := f \o Int63Op.of_Z in zf zf1.
Proof.
apply: hinterp_ext => i /=.
by rewrite Int63Axioms.of_to_Z.
Qed.


(*****************************************************************************)
(*                                                                           *)
(*                         Colours as boolean values                         *)
(*                                                                           *)
(*****************************************************************************)

Definition colour := bool.
Definition white : colour := true.
Definition black : colour := false.


(*****************************************************************************)
(*                                                                           *)
(*                  Counting sequences of black squares                      *)
(*                                                                           *)
(*****************************************************************************)


Fixpoint count_aux (l : seq colour) n :=
    if l is a :: l1 then 
    if ~~ a then count_aux l1 n.+1 else 
    if n is _.+1 then n :: count_aux l1 0 else count_aux l1 0
    else if n is _.+1 then [::n] else [::].

Definition count l := count_aux l 0.

Compute count  [:: black; white; white; black; black; black; white].

Lemma count_neq0 l : 0 \notin count l.
Proof.
rewrite /count.
elim: l {2}0 => //= [[|n] //| [] l //= IH [] // n].
by rewrite in_cons /=.
Qed.

Lemma count_nseq_black n : count (nseq n.+1 black) = [::n.+1].
Proof.
rewrite /count -{2}[n]addn0.
by elim: n 0 => //= n IH m; rewrite IH /= addnS.
Qed.

Lemma count_nseq_white n : count (nseq n white) = [::].
Proof.
rewrite /count -[[::]]/(if 0 is _.+1 then [:: 0] else [::]).
by elim: n 0 => //= n -> [|m] /=.
Qed.

Lemma count_cat l1 l2 :
  count (l1 ++ white :: l2) = count l1 ++ count l2.
Proof.
rewrite {1 2}/count.
elim: l1 0 => /= [[|n]//|[] /= l1 IH [|n]] //.
by rewrite IH.
Qed. 

Lemma count_black_white l n : 
  count (ncons n.+1 black (white :: l)) = n.+1 :: count l.
Proof. by rewrite - cat_nseq count_cat count_nseq_black. Qed.

Lemma count_white l : count (white :: l) = count l.
Proof. by []. Qed.

Lemma count_whites l n : count (ncons n white  l) = count l.
Proof. by elim: n. Qed.

Lemma count_rcons_white l : count (rcons l white) = count l.
Proof.
rewrite /count.
elim: l 0  => // [[]]//= l IH [|n] //.
by rewrite IH.
Qed.

Lemma count_rcons_whites l n : count (l ++ nseq n white) = count l.
Proof.
elim: n l => [l|n IH /= l]; first by rewrite cats0.
by rewrite - cat_rcons IH count_rcons_white.
Qed.

Lemma count_rcons_black_white l n : 
  count (l ++ (white :: (nseq n.+1 black))) = rcons (count l) n.+1.
Proof. by rewrite count_cat count_nseq_black cats1. Qed.

Lemma count_rev : {morph count : l / rev l}.
Proof.
move=> l.
elim: {l}_.+1 {-2}l (ltnSn (size l)) => // n IH l H.
case: (lbool_spec black l) H => [[/=|m]|[/=|m] l1] H //.
- by rewrite rev_nseq count_nseq_black.
- by rewrite !rev_cons count_white count_rcons_white IH.
rewrite count_black_white - cat_nseq rev_cat rev_cons rev_nseq.
rewrite rev_cons cat_rcons count_rcons_black_white IH //.
by rewrite -ltnS (leq_trans _ H) // ltnS size_ncons /= addnS ltnS leq_addl.
Qed.

Lemma count_gt0 i l : i \in count l -> i > 0.
Proof. 
rewrite /count.
elim: l i {1}0 => /= /= [i [|m] |a l1 IH i [|m]] //=.
- by rewrite inE => /eqP->.
- by case: a => /IH.
by (case: a; rewrite /= ?inE)=> [/orP[/eqP->//|]|] /IH.
Qed.

Lemma count_sum l :
   \sum_(i <- count l) i.+1 <= (size l).+1.
Proof.
elim: {l}_.+1 {-2}l (ltnSn (size l)) => // n IH l H.
case: (lbool_spec black l) H => [[/=|m]|[/=|m] l1] H.
- by rewrite big_nil.
- by rewrite count_nseq_black big_cons big_nil size_nseq addn0.
- by rewrite count_white (leq_trans (IH _ H)).
rewrite count_black_white big_cons size_ncons -addSn leq_add2l /=.
apply: IH.
rewrite ltnS in H.
apply: leq_trans H.
by rewrite size_ncons /= leq_addl.
Qed.

Lemma count_nilE l : count l = [::] -> l = nseq (size l) white.
Proof.
elim: l => //= [[]] /= l IH H; first by rewrite {1}IH.
move: H; case: (lbool_spec black l) => [n1|n1 l1].
  by rewrite (count_nseq_black n1).
by rewrite count_black_white.
Qed.


(*****************************************************************************)
(*                                                                           *)
(*           A solution as a sequence of sequence of colours                 *)
(*                                                                           *)
(*****************************************************************************)

Definition sol := seq (seq colour).

Definition get_row (s : sol) i := nth [::] s i.
Definition get_col (s : sol) j := map (fun l => nth false l j) s.

Lemma get_row_col s i j :
 nth false (get_row s i) j =  nth false (get_col s j) i.
Proof.
case: (leqP (size s) i) => H; last first.
  by rewrite (nth_map [::]).
rewrite [get_row _ _]nth_default ?nth_nil //=.
by rewrite nth_default // size_map.
Qed.

Definition get_xy (s : sol) i j :=
  nth false (get_row s i) j.

Definition is_square {A: Type} (n : nat) (p : seq (seq A)) :=
  (size p == n) && [forall i : 'I_n, size (nth [::] p i) == n].

Lemma get_row_size n s i :
   is_square n s ->
   i < n -> size (get_row s i) = n.
Proof.
move=> Hwf Li.
by have /andP[_ /forallP/(_ (Ordinal Li))/eqP] := Hwf.
Qed.

Lemma get_col_size n s i :
   is_square n s ->
   i < n -> size (get_col s i) = n.
Proof.
move=> Hwf Li.
rewrite size_map.
by have /andP[/eqP->] := Hwf.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*        A partial solution as a sequence of sequence of optional colours   *)
(*                                                                           *)
(*****************************************************************************)


Definition psol := seq (seq (option colour)).

(* Getting a row *)
Definition pget_row (s : psol) i := nth [::] s i.

Lemma pget_row_size n s i :
  is_square n s -> i < n -> size (pget_row s i) = n.
Proof.
move=> Hwf Li.
by have /andP[_ /forallP/(_ (Ordinal Li))/eqP] := Hwf.
Qed.

(* Setting a row *)
Definition pset_row (s : psol) i v := 
  [seq (if j == i then v else pget_row s j) | j <- iota 0 (size s)].

Lemma pset_row_square n s i v :
 is_square n s -> 
 (i < n -> size v = n) -> is_square n (pset_row s i v).
Proof.
move=> H Hs; have /andP[/eqP H1 /forallP H2] := H.
apply/andP; split.
  by rewrite size_map size_iota H1.
apply/forallP=> j; apply/eqP.
rewrite (nth_map 0); last by rewrite size_iota H1.
rewrite nth_iota ?add0n; last by rewrite H1.
case: eqP => // xDi.
  by apply: Hs; rewrite -xDi.
by apply: pget_row_size.
Qed.
 
Lemma pset_row_correct s i j v :
 i < size s -> pget_row (pset_row s i v) j = 
              if i == j then v else pget_row s j.
Proof.
move=> Ls.
have [Ls1|Ls1] := leqP (size s) j.
  rewrite [LHS]nth_default ?size_map ?size_iota //.
  case: eqP=> H; rewrite ?[RHS]nth_default //.
  by have := Ls1; rewrite -H leqNgt Ls.
have /(nth_iota 0) := Ls1.
rewrite add0n => {1}<-.
rewrite [LHS](nth_map 0) // !(nth_iota 0) ?size_iota //.
by rewrite !add0n eq_sym.
Qed.

(* Getting a columm *)
Definition pget_col (s : psol) j := [seq nth None l j | l <- s].

(* Setting a column *)
Definition pset_col (s : psol) j v :=
  [seq (let l := pget_row s i in
      [seq (if j1 == j then nth None v i else nth None l j1) | 
          j1 <- iota 0 (size l)])
       | i <- iota 0 (size s)].

Lemma pset_col_square n s j v :
 is_square n s -> size v = n -> is_square n (pset_col s j v).
Proof.
move=> H Hs; have /andP[/eqP H1 /forallP H2] := H.
apply/andP; split.
  by rewrite size_map size_iota H1.
apply/forallP=> i; apply/eqP.
rewrite (nth_map 0); last by rewrite size_iota H1.
rewrite nth_iota ?H1 ?add0n //=.
rewrite size_map size_iota.
by apply: pget_row_size.
Qed.

Lemma pset_col_correct n s i j v :
 size v = n -> is_square n s -> j < n -> 
 pget_col (pset_col s j v) i = 
              if i == j then v else pget_col s i.
Proof.
move=> Hs Hwf Ls; have /andP[/eqP H1wf /forallP H2wf] := Hwf.
apply: (@eq_from_nth _ None) => [|i1 Hi1].
  by case: eqP => _; rewrite !size_map size_iota // Hs.
have /(nth_iota 0) := Hi1.
rewrite add0n => {1}<-.
rewrite [LHS](nth_map [::]) // !(nth_iota 0) ?size_iota //; last first.
  by move: Hi1; rewrite !size_map size_iota.
have F : 0 + i1 < size (iota 0 (size s)).
  by move: Hi1; rewrite !size_map size_iota.
rewrite (nth_map 0 [::] _ F) /=.
rewrite nth_iota !add0n; last first.
  by move: Hi1; rewrite !size_map size_iota.
have Oi1 : i1 < n.
  by move: Hi1; rewrite !size_map size_iota H1wf.
have [Ls1|Ls1] := leqP (size s) i.
  rewrite [LHS]nth_default ?size_map ?size_iota //; last first.
    by rewrite (pget_row_size n) // -H1wf.
  case: eqP=> H.
    by move: Ls1; rewrite H1wf H leqNgt Ls.
  rewrite (nth_map [::]) ?H1wf // nth_default //.
  have /eqP-> := H2wf (Ordinal Oi1).
  by rewrite -H1wf.
have iLn : i < n by rewrite -H1wf.
rewrite (nth_map 0); last first.
   by rewrite size_iota (pget_row_size n).
rewrite nth_iota ?(pget_row_size n) // add0n.
case: eqP => // /eqP iDj.
by rewrite (nth_map [::]) // H1wf.
Qed.

(* Getting  a cell *)
Definition pget_xy (s : psol) i j := nth None (pget_row s i) j.

Definition pset_xy (s : psol) i j v := 
  pset_row s i 
   (let l := pget_row s i in 
         [seq (if j1 == j then v else nth None l j1) | j1 <- iota 0 (size l)]).

Lemma pset_xy_square n s i j v :
  is_square n s -> is_square n (pset_xy s i j v).
Proof.
move=> H.
apply: pset_row_square => // Hi.
by rewrite size_map size_iota (pget_row_size n).
Qed.

Lemma pset_xy_correct n s i j i1 j1 v :
  is_square n s -> i < n -> j < n ->
  pget_xy (pset_xy s i j v) i1 j1 = 
    if (i == i1) && (j == j1) then v else pget_xy s i1 j1.
Proof.
move=> Hwf Li Lj; have /andP[/eqP H1wf /forallP H2wf] := Hwf.
rewrite /pget_xy /pset_xy.
rewrite pset_row_correct //; last by rewrite H1wf.
case: eqP => // <-.
case: (leqP n j1) => H; last first.
  rewrite (nth_map 0); last first.
    by rewrite size_iota (pget_row_size n).
  rewrite nth_iota ?(pget_row_size n) // add0n eq_sym.
  by case: eqP.
rewrite nth_default; last first.
  by rewrite size_map size_iota (pget_row_size n).
case: eqP => /= H1.
  by move: H; rewrite -H1 leqNgt Lj.
by rewrite nth_default ?(pget_row_size n).
Qed.

Lemma pget_row_col s i j :
 nth None (pget_row s i) j =  nth None (pget_col s j) i.
Proof.
case: (leqP (size s) i) => H; last first.
  by rewrite (nth_map [::]).
rewrite [pget_row _ _]nth_default ?nth_nil //=.
by rewrite nth_default // size_map.
Qed.

(* a partial solution implies a solution *)
Definition entail n (ps : psol) (s : sol) :=
  [&& is_square n ps, is_square n s &
    [forall i : 'I_n,
     forall j : 'I_n,
     forall b : bool,
      (pget_xy ps i j == Some b) ==> (get_xy s i j == b)]].

Lemma entailP n ps s :
  reflect 
   [/\ is_square n ps, is_square n s &
    forall i j b, i < n -> j < n -> 
       pget_xy ps i j = Some b -> get_xy s i j = b]
   (entail n ps s).
Proof.
apply: (iffP and3P) => [[H1 H2 /forallP H3]|[H1 H2 H3]]; split=> //.
  move=> i j b Hi Hj H4.
  have /forallP/(_ (Ordinal Hj))/forallP/(_ b) := H3 (Ordinal Hi).
  move/implyP=> H5.
  by apply/eqP/H5/eqP.
apply/forallP=> i; apply/forallP=> j; apply/forallP=> b; apply/implyP=> /eqP.
by move=> /(H3 i j b (ltn_ord i) (ltn_ord j))->.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*  Given a count, return the list of possible solutions                     *)
(*                                                                           *)
(*****************************************************************************)


Fixpoint gen_constr_aux res accu l extra m :=
  if l is n :: l1 then
    foldi (fun i r =>
               gen_constr_aux r 
                      (ncons n black (ncons (i + m) white accu)) l1 (extra - i) 1)
          extra res
  else  (ncons extra white accu) :: res.

(* Build all the lists that are of length d with a count l *)
Definition gen_constr l d :=
 gen_constr_aux [::] [::] (rev l) (d - (size l).-1 -  foldl addn 0 l) 0.

Compute gen_constr [::1; 3] 6.

Lemma gen_constr_aux_incl res accu l extra m :
  {subset res <= (gen_constr_aux res accu l extra m)}.
Proof.
elim: l res accu extra m =>
          /= [res accu extra m i H|n l IH res accu extra m i H].
   by rewrite in_cons H orbC.
elim: extra res {1}extra H => /= [res extra H|extra IH1 res e H].
  by apply: IH.
by apply/IH1/IH.
Qed.

Lemma gen_constr_aux_count res accu l extra m :
  (m = (accu != [::])) -> (forall i, i \in l -> 0 < i) ->
  (forall i, i \in res -> count i = rev l ++ count accu) ->
  (forall i, i \in gen_constr_aux res accu l extra m ->
       count i = rev l ++ count accu).
Proof.
elim: l res accu extra m => /= 
    [res accu extra m Hm Hl H i|b l IH res accu extra m Hm Hl H i].
  rewrite in_cons => /orP[/eqP->|/H//].
  by rewrite count_whites.
have bP : 0 < b by apply: Hl; rewrite in_cons eqxx.
elim: {1 4}extra (leqnn extra) res H => //= [_ res H | e IH1 eL res H].
  rewrite subn0 add0n.
  rewrite -[1]/(true: nat) => /IH-> //; last 2 first.
  - by move=> i1 Hi1; apply: Hl; rewrite in_cons Hi1 orbC.
  - move=> i1 /H->.
    case: (b) bP => // b1 _.
    rewrite rev_cons  cat_rcons.
    case: (accu) Hm => [->/=|u a -> /=].
      by rewrite count_nseq_black.
    by rewrite - cat_nseq (count_cat (nseq b1.+1 black)) count_nseq_black.
  - case: (b) bP => // b1 _.
    case: (accu) Hm => [->/=|u a -> /=].
      by rewrite rev_cons cat_rcons count_nseq_black.
    have /=<- := (@cat_nseq _ b1.+1 black).
    rewrite rev_cons cat_rcons.
    by rewrite (count_cat (nseq b1.+1 black)) count_nseq_black.
  by case: (b) bP.
apply: IH1 => [|i1 Hi1]; first by apply: ltnW.
rewrite (IH res (ncons b black (white :: ncons (e + m)%Nrec white accu))
                (extra - e.+1) true) //.
- rewrite rev_cons cat_rcons.
  case: (b) bP => // b1 _.
  rewrite - cat_nseq (count_cat (nseq b1.+1 black)) count_nseq_black.
  by rewrite count_whites.
- by case: (b) bP.
- by move=> i2 Hi2; apply: Hl; rewrite inE Hi2 orbC.
move=> i2 Hi2.
rewrite H //.
rewrite rev_cons cat_rcons.
case: (b) bP => // b1 _.
rewrite - cat_nseq (count_cat (nseq b1.+1 black)) count_nseq_black.
by rewrite count_whites.
Qed.

(* It has the right count *)
Lemma gen_constr_count l d i :
  (forall i1, i1 \in l -> 0 < i1) -> i \in gen_constr l d -> count i = l.
Proof.
move=> Hl.
rewrite /gen_constr -{2}[0]/(false : nat) => /gen_constr_aux_count /=.
rewrite revK cats0; apply=> //.
by move=> i1 Hi1; apply: Hl; rewrite -mem_rev.
Qed.

Lemma gen_constr_aux_size res accu l extra m :
  (m = (accu != [::])) -> (forall i, i \in l -> 0 < i) ->
  (forall i, i \in res -> 
       size i = extra + m + \sum_(i <- l) i + (size accu + size l).-1) ->
  (forall i, i \in gen_constr_aux res accu l extra m ->
       size i = extra + m + \sum_(i <- l) i + (size accu + size l).-1).

Proof.
elim: l res accu extra m => /= 
    [res accu extra m Hm Hl H i|b l IH res accu extra m Hm Hl H i].
  rewrite in_cons => /orP[/eqP->|/H//].
  rewrite size_ncons big_nil !addn0 Hm.
  by case: (accu) => //= _ a; rewrite !addnS addn0.
have bP : 0 < b by apply: Hl; rewrite in_cons eqxx.
elim: {1 5}extra (leqnn extra) res H => //= [_ res H | e IH1 eL res H].
  rewrite subn0 !add0n.
  rewrite -[1]/(true: nat) => /IH-> //; last 2 first.
  - by move=> i1 Hi1; apply: Hl; rewrite in_cons Hi1 orbC.
  - move=> i1 /H->.
    rewrite big_cons !size_ncons /=.
    case: (b) bP => // b1 _.
    rewrite !(addSn, addnS) /= !addn0 !addnA.
    congr ((_ + _ + _).+1).
    rewrite -!addnA; congr (_ + _ ).
    by rewrite addnC [b1 + _]addnC !addnA.
  - rewrite big_cons !size_ncons /=.
    case: (b) bP => // b1 _.
    rewrite !(addSn, addnS) /= addn0 !addnA.
    congr ((_ + _ + _).+1).
    rewrite -!addnA; congr (_ + _).
    by rewrite addnC [b1 + _]addnC !addnA.
  by case: (b) bP.
apply: IH1 => [|i1 Hi1]; first by apply: ltnW.
rewrite (IH res (ncons b black (white :: ncons (e + m)%N white accu))
                (extra - e.+1) true) //.
- rewrite size_ncons /= size_ncons /=.
  case: (b) bP => // b1 _.
  rewrite -{2}(subnK eL)  big_cons !(addSn, addnS) /= addn0 !addnA.
  congr ((_ + _).+2).
  rewrite -!addnA; congr (_ + _).
  rewrite !addnA; congr (_ + _).
  rewrite [RHS]addnC -!addnA; congr (_ + _).
  by rewrite addnC !addnA.
- by case: (b) bP.
- by move=> i2 Hi2; apply: Hl; rewrite inE Hi2 orbC.
move=> i2 Hi2.
rewrite H //.
rewrite  -{1}(subnK eL) !size_ncons /= !(addnS, addSn).
rewrite big_cons /= size_ncons !addnA addn0.
congr (_ + _ + _).+1.
rewrite -!addnA; congr (_ + _).
rewrite [RHS]addnC !addnA; congr (_ + _).
by rewrite addnC !addnA.
Qed.

(* It has the right size *)
Lemma gen_constr_size l d i :
  (forall i1, i1 \in l -> 0 < i1) -> 
   i \in gen_constr l d ->  (size l).-1 + \sum_(i <- l) i <= d ->
   size i = d.
Proof.
move=> Hi Hf Hu.
move: Hf.
rewrite /gen_constr -[0]/(false: nat) => Hf.
rewrite (gen_constr_aux_size _ _ _ _ _ _ _ _ _ Hf) //; last first.
- by move=> i1 Hil; apply: Hi; rewrite -mem_rev.
rewrite foldl_addn big_rev /=.
rewrite addn0 -subnDA /= add0n size_rev -addnA [_.-1 + _]addnC.
by rewrite subnK // addnC.
Qed.

Lemma gen_constr_aux_mem res accu l extra m l1 :
   (m = (accu != [::])) -> 
   (accu != [::] -> last white l1 = white) ->
   size l1 = 
      \sum_(i <- l) i + extra + (size l - (accu == [::])) ->
    count l1 = rev l ->
    l1 ++ accu \in gen_constr_aux res accu l extra m.
Proof.
elim: l res accu extra m l1 =>
     [res accu extra m l1|
      n k IH res accu extra m l1].
  rewrite big_nil add0n => _ _ H /count_nilE ->.
  by rewrite H /= sub0n addn0 in_cons cat_nseq eqxx.
rewrite big_cons rev_cons [size (_ :: _)]/=.
case: (rbool_spec white l1) => [n1 |n1 l2 Hm1 Hm2].
  by rewrite count_nseq_white; case: rev.
rewrite size_cat [size (_ :: _)]/= size_nseq.
rewrite -{1}cat_rcons count_rcons_whites.
have F1 m1 : rcons (nseq m1 black) black = nseq m1.+1 black.
  by elim: m1 => //= m1 ->.
move=> H1 H2.
have Hn1 : m <= n1.
  have := Hm2; rewrite Hm1; case: eqP => //=.
  by rewrite last_cat /=; case: (n1) => //= _ /(_ is_true_true).
have Hn2 : n1 -  m <= extra.
  rewrite leq_subLR; have := count_sum (rcons l2 (~~ white)).
  rewrite H2 size_rcons big_rcons /= big_rev /=.
  rewrite (eq_bigr (addn 1)) // big_split /= sum1_size ltnS.
  rewrite -(leq_add2r n1) addSnnS H1 /=.
  rewrite -!addnA leq_add2l addnC -!addnA leq_add2l.
  rewrite Hm1; case: eqP => /=; first by rewrite subn1 leq_add2r.
  by rewrite subn0 add1n -addSnnS leq_add2r.
rewrite /= -{2}(subnK Hn2).
set f := (fun _ _ => _).
have FF res1 : (l2 ++ false :: nseq n1 white) ++ accu \in f (n1 - m) res1.
  rewrite /f /= subnK //.
  case: (rbool_spec black l2) Hm2 H1 H2 => [n2 Hm2|n2 l3 Hm2].
    rewrite !F1 count_nseq_black => H1 H2.
    have kZ : k = [::].
      by rewrite -[k]revK; case: rev H2 => //= u [].
    rewrite  -{1}cat_rcons F1.
    move: H2 H1; rewrite size_nseq -[n2 + n1.+1]addSnnS kZ => [[->]] /=.
    rewrite big_nil addn0 /= => /eqP.
    rewrite -addnA eqn_add2l => /eqP {2}->.
    rewrite (_ : 1 - _ = m); last by rewrite Hm1; case: eqP.
    by rewrite addnK subnn in_cons /= -{1}catA !cat_nseq eqxx.
  rewrite size_cat /= size_nseq rcons_cat /= count_cat F1 count_nseq_black.
  rewrite -{1}cat_rcons cats0 => H1 /eqP.
  rewrite eqseq_rcons => /andP[/eqP U1 /eqP U2].
  rewrite -{1}cat_rcons rcons_cat /= F1 U2 -{1}cat_rcons -!catA !cat_nseq.
apply: (IH _ _ _ true) => //.
- by case: (n) U2 => //=.
- by rewrite last_rcons.
- apply/eqP; rewrite -(eqn_add2r n1).
  rewrite size_rcons addSnnS.
  move/eqP: H1.
  rewrite U2 [_ + n]addnC -!addnA eqn_add2l => /eqP->.
  rewrite eqn_add2l.
  case: (n) U2 => //= n3 Hn3; rewrite subn0.
  rewrite -{1}(subnK Hn2) -addnA eqn_add2l.
  rewrite -{2}(subnK Hn1) [size k + _]addnC -addnA eqn_add2l.
  rewrite Hm1; case: (accu == [::]) => //.
  by rewrite subnS subn0.
- by rewrite count_rcons_white.
elim: (extra - _) res => [res |e IH1 res //]; last by apply: IH1.
rewrite add0n.
case E : (_ - _) => [|n2]; rewrite /= -{}E //.
elim: n2 (f _ _) (FF res) => /= [v |n3 IH1 v Hv].
  by apply: gen_constr_aux_incl.
apply: IH1.
by apply: gen_constr_aux_incl.
Qed.

(* It contains all *)
Lemma gen_constr_mem l l1 d :
   count l1 = l -> size l1 = d -> l1 \in gen_constr l d.
Proof.
move=> H1 H2.
rewrite /gen_constr -[l1]cats0.
apply: (gen_constr_aux_mem _ _ _ _ false) => //; last by rewrite revK.
rewrite big_rev /= size_rev subn1 H2 foldl_addn.
have F1 : (size l).-1 <= d.
  have := count_sum l1.
  rewrite H1 H2.
  rewrite (eq_bigr (addn 1)) // big_split /= sum1_size.
  case: (size l) => //= n.
  rewrite ltnS => /(leq_trans _)-> //.
  by apply: leq_addr.
rewrite [_ + (_ - _)]addnC !subnK //.
rewrite -(leq_add2r (size l).-1) subnK //.
have := count_sum l1.
rewrite H1 H2.
rewrite (eq_bigr (addn 1)) // big_split /= sum1_size.
case: (l) => //= [|u l2]; first by rewrite big_nil.
by rewrite addSn ltnS addnC.
Qed.

Compute size (gen_constr [::7;2;1;1;7] 25).
Compute (gen_constr [::1;3;1;3;1;3;1;3;1] 25).

(*****************************************************************************)
(*                                                                           *)
(*        Checking if a partial solution fits a solution                     *)
(*                                                                           *)
(*****************************************************************************)


Fixpoint pcheck {A : eqType} f (l : seq A) := 
  if f is a :: f1 then 
    if l is b :: l1 then
      if a is Some a1 then
        if a1 == b then pcheck f1 l1 else false
      else pcheck f1 l1
    else false
  else if l is _ :: _ then false else true.

Lemma pcheck_correct (A : eqType) f (l : seq A) a :
  size f = size l ->
  (forall i b, i < size f -> nth None f i = Some b -> 
               nth a l i = b) ->
  pcheck f l.
Proof.
elim: f l => /= [[]//|b f IH [|c l] //= [] Hf].
case: b => // [b1 Ha|Ha]; last first.
  apply: IH => // i b Hi Hn.
  by apply: (Ha i.+1).
have /=->: nth a (c :: l) 0 = b1 by apply: Ha.
rewrite eqxx IH => // i b Hi Hn.
by apply: (Ha i.+1).
Qed.
 
Lemma entail_pcheck_col n ps p (l : seq (seq bool)) j :
  entail n ps p -> j < n -> get_col p j \in l ->
  get_col p j \in [seq i <- l | pcheck (pget_col ps j) i].
Proof.
move=> He Hs Hg.
have /entailP[Sps Sp H1e] := He.
have /andP[/eqP S1ps /forallP S2ps] := Sps.
have /andP[/eqP S1p /forallP S2p] := Sp.
rewrite mem_filter Hg andbT.
apply: (pcheck_correct _ _ _ false) => [|i1 b Hi1 Li1].
  by apply: etrans (_ : n = _); rewrite size_map.
rewrite -get_row_col.
apply: H1e => //.
  by move: Hi1; rewrite size_map S1ps.
by rewrite [LHS]pget_row_col.
Qed.

Lemma entail_pcheck_row n ps p (l : seq (seq bool)) i :
  entail n ps p -> i < n ->
  get_row p i \in l ->
  get_row p i \in [seq j <- l | pcheck (pget_row ps i) j].
Proof.
move=> He Hs Hg.
have /entailP[Sps Sp H1e] := He.
have /andP[/eqP S1ps /forallP S2ps] := Sps.
have /andP[/eqP S1p /forallP S2p] := Sp.
rewrite mem_filter Hg andbT.
apply: (pcheck_correct _ _ _ false) => [|i1 b Hi1 Li1].
  apply: etrans (_ : n = _); first by apply: pget_row_size.
  by apply/esym/get_row_size.
apply: H1e => //.
by move: Hi1; rewrite (pget_row_size n). 
Qed.

(*****************************************************************************)
(*                                                                           *)
(*        Generate the formula that represents a count                       *)
(*                                                                           *)
(*****************************************************************************)

Definition of_ij d i j := varb (i * d + j).

Definition gen_form f l d :=
  let ll := gen_constr l d in
  orb (map (fun l =>
             andb (map
              (fun p =>
                let: (i,b) := p in
                  (if b then (f i) else negb (f i)))
              (zip (int_iota 0 d) l)))  ll).

Compute gen_form (fun i => varb (0 + i)) [::2] 4.


Definition to_ij d u := 
  let i := Z.to_nat (Int63Op.to_Z (Int63Native.div u d)) in
  let j := Z.to_nat (Int63Op.to_Z (Int63Native.modulo u d)) in (i, j).


Definition f_interp n s x :=
  let: (i, j) := to_ij (nat2int n) x in
                   get_xy s i j.

Lemma f_interpE n s i j :
  (Z.of_nat n * Z.of_nat n < Int63Axioms.wB)%Z ->
  i < n -> j < n ->
  f_interp n s (nat2int i * nat2int n + nat2int j) =
  get_xy s i j.
Proof.
move=> Hm Li Lj.
have F1 : (0 <= Z.of_nat n < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  by apply: BigNumPrelude.Zsquare_le.
have F2 : (0 <= Z.of_nat j < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : Z.of_nat n <= _)%Z.
    by apply/inj_le/leP/ltnW.
  by apply: BigNumPrelude.Zsquare_le.
have F3 : (0 <= Z.of_nat i < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : Z.of_nat n <= _)%Z.
    by apply/inj_le/leP/ltnW.
  by apply: BigNumPrelude.Zsquare_le.
have F4 : (0 <= Z.of_nat i * Z.of_nat n < Int63Axioms.wB)%Z.
  split; first by rewrite -Nat2Z.inj_mul; apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Zmult_le_compat_r.
    by apply/inj_le/leP/ltnW.
  by apply: Zle_0_nat.
have F5 : (0 <= Z.of_nat i * Z.of_nat n + Z.of_nat j <
 Int63Axioms.wB)%Z.
  split.
    rewrite -Nat2Z.inj_mul.
    by apply: Z.add_nonneg_nonneg; apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : ((Z.of_nat i + 1) * Z.of_nat n  <= _)%Z).
    rewrite Z.mul_add_distr_r Z.mul_1_l.
    apply: Zplus_le_compat_l.
    by apply/inj_le/leP/ltnW.
  apply: Zmult_le_compat_r; last by apply: Zle_0_nat.
  have-> : (Z.of_nat i + 1 = Z.of_nat i.+1)%Z.
    by rewrite Nat2Z.inj_succ Z.add_1_r.
  by apply/inj_le/leP.
rewrite /f_interp /= Int63Axioms.div_spec /nat2int.
rewrite !(Int63Axioms.add_spec, Int63Axioms.mul_spec).
rewrite !Int63Properties.of_Z_spec.
rewrite !Zmod_small //.
rewrite Int63Axioms.mod_spec.
set u1 := Z.modulo; rewrite -{1}/u1.
rewrite !(Int63Axioms.add_spec, Int63Axioms.mul_spec).
rewrite !Int63Properties.of_Z_spec.
rewrite !Zmod_small // {}/u1.
rewrite Z.div_add_l; last first.
  by case: (n) Li.
rewrite Z.div_small; last first.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Z.add_0_r Nat2Z.id.
rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
  by rewrite Nat2Z.id.
split; first by apply: Zle_0_nat.
by apply/inj_lt/ltP.
Qed.

Definition lf_interp :=
  locked (fun n s u =>
  (f_interp n s  (Int63Op.of_Z u))).

Lemma lf_interpEn n s f :
   interp (f_interp n s) f = interp (lf_interp n s \o Int63Op.to_Z) f.
Proof.
apply: interp_ext => i.
rewrite /= /lf_interp; unlock.
by rewrite Int63Axioms.of_to_Z.
Qed.

Definition finterp h1 h9 h2 h3 h4 h5 h6 h7 h8 :=
  hinterp h2 h3 h4 h5 h6 h7 h8 h9 h1.

Lemma finterpE h1 h2 h3 h4 h5 h6 h7 h8 h9 : 
  finterp h1 h9 h2 h3 h4 h5 h6 h7 h8 =
  hinterp h2 h3 h4 h5 h6 h7 h8 h9 h1.
Proof. by []. Qed.

Lemma interp_gen_form_row (s : sol) x l :
  size (get_row s x) = size s ->
  (Z.of_nat (size s) * Z.of_nat (size s) < Int63Axioms.wB)%Z ->
  x < size s ->
  count (get_row s x) = l ->
  interp (f_interp (size s) s)
         (gen_form (fun i => varb (nat2int x * nat2int (size s) + i))
               l (size s)).
Proof.
move=> Hus Hm Hs H.
have : get_row s x \in gen_constr l (size s).
  by apply: gen_constr_mem.
rewrite /gen_form.
elim: gen_constr => [//|a l1 IH].
rewrite inE => /orP[/eqP Ha | Hu]; last first.
  by rewrite /= mk_orb_cons [mk_orb _]IH ?orbT.
rewrite /= mk_orb_cons /=.
rewrite mk_andb_map // => {IH}i.
have {3}-> : size s = size a by rewrite -Ha.
have: (forall y, y < size a ->  nth false a y = get_xy s x y).
  by move=> y Hy; rewrite -Ha.
have: size a <= size s by rewrite -Ha Hus.
move: {Ha}a.
apply: last_ind => //= u a IH1 Hl Ha.
rewrite size_rcons.
rewrite int_iota_rcons zip_rcons ?map_rcons ?size_map ?size_iota //= => Hv.
case: (List_in_rcons _ _ _ _ Hv) => [->/=|/IH1 -> //]; last 2 first.
- by rewrite (leq_trans _ Hl) // size_rcons.
- move=> y Ly.
  by rewrite -Ha ?nth_rcons ?Ly // size_rcons (leq_trans Ly).
have : get_xy s x (size u) = a.
  rewrite -Ha  ?size_rcons //.
  by rewrite nth_rcons ltnn eqxx.
have Hl1 : size u < size s.
  by apply: leq_trans Hl; rewrite size_rcons.
case: {Ha Hv Hl}a.
  by rewrite /= add0n f_interpE.
by rewrite /= add0n f_interpE // => ->.
Qed.

Lemma interp_gen_form_col (s : sol) y l :
  (Z.of_nat (size s) * Z.of_nat (size s) < Int63Axioms.wB)%Z ->
  y < size s ->
  count (get_col s y) = l ->
  interp (f_interp (size s) s)
         (gen_form (fun i => varb (i * nat2int (size s) + nat2int y))
               l (size s)).
Proof.
move=> Hm Hs H.
have Hus : size (get_col s y) = size s.
  by rewrite size_map.
have : get_col s y \in gen_constr l (size s).
  by apply: gen_constr_mem.
rewrite /gen_form.
elim: gen_constr => [//|a l1 IH].
rewrite inE => /orP[/eqP Ha | Hu]; last first.
  by rewrite /= mk_orb_cons [mk_orb _]IH ?orbT.
rewrite /= mk_orb_cons /=.
rewrite mk_andb_map // => i.
have {3}-> : size s = size a by rewrite -Ha.
have: (forall x, x < size a ->  nth false a x = get_xy s x y).
  by move=> x Hx; rewrite -Ha -get_row_col.
have: size a <= size s by rewrite -Ha Hus.
move: {Ha}a.
apply: last_ind => //= u a IH1 Hl Ha.
rewrite size_rcons.
rewrite int_iota_rcons zip_rcons ?map_rcons ?size_map ?size_iota //= => Hv.
case: (List_in_rcons _ _ _ _ Hv) => [->/=|/IH1 -> //]; last 2 first.
- by rewrite (leq_trans _ Hl) // size_rcons.
- move=> x Lx.
  by rewrite -Ha ?nth_rcons ?Lx // size_rcons (leq_trans Lx).
have : get_xy s (size u) y = a.
  rewrite -Ha  ?size_rcons //.
  by rewrite nth_rcons ltnn eqxx.
have Hl1 : size u < size s.
  by apply: leq_trans Hl; rewrite size_rcons.
case: {Ha Hv Hl}a.
  by rewrite /= add0n f_interpE.
by rewrite /= add0n f_interpE // => ->.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*        Generate the formula that represents a count                       *)
(*        taking a partial solution into account                             *)
(*                                                                           *)
(*****************************************************************************)

Definition pgen_form (pp : seq (option colour)) f l d :=
  let ll := [seq i <- gen_constr l d | pcheck pp i] in
  orb (map (fun l =>
             andb (map
              (fun p =>
                let: (i,b) := p in
                  (if b then (f i) else negb (f i)))
              (zip (int_iota 0 d) l)))  ll).


Lemma interp_pgen_form_row n (s : sol) pp x l :
  (Z.of_nat n * Z.of_nat n < Int63Axioms.wB)%Z ->
  x < n ->
  entail n pp s ->
  count (get_row s x) = l ->
  interp (f_interp n s)
         (pgen_form (pget_row pp x) 
                (fun i => varb (nat2int x * nat2int n + i))
               l n).
Proof.
move=> Hm Hs He H.
have /entailP[Spp Sp H1e] := He.
have /andP[/eqP S1pp /forallP S2pp] := Spp.
have /andP[/eqP S1p /forallP S2p] := Sp.
have Hus : size (get_row s x) = n.
  by apply: get_row_size.
have : get_row s x \in gen_constr l n.
  by apply: gen_constr_mem.
rewrite /pgen_form.
elim: gen_constr => [//|a l1 IH].
rewrite inE => /orP[/eqP Ha | Hu]; last first.
  rewrite /=.
  case E : (pcheck (pget_row pp x) a) => /=.
    by rewrite mk_orb_cons [mk_orb _]IH ?orbT.
  by apply: IH.
rewrite /=.
have -> : pcheck (pget_row pp x) a.
  rewrite -Ha.
  apply: (pcheck_correct _ _ _ false).
    by rewrite (pget_row_size n).
  move=> y b Hy Hn.
  apply: H1e => //.
  by move: Hy; rewrite (pget_row_size n).
rewrite /= mk_orb_cons /=.
rewrite mk_andb_map // => i.
have {3}-> : n = size a by rewrite -Ha.
have: (forall y, y < size a ->  nth false a y = get_xy s x y).
  by move=> y Hy; rewrite -Ha.
have: size a <= n by rewrite -Ha Hus.
move: {Ha}a.
apply: last_ind => //= u a IH1 Hl Ha.
rewrite size_rcons.
rewrite int_iota_rcons zip_rcons ?map_rcons ?size_map ?size_iota //= => Hv.
case: (List_in_rcons _ _ _ _ Hv) => [->/=|/IH1 -> //]; last 2 first.
- by rewrite (leq_trans _ Hl) // size_rcons.
- move=> y Ly.
  by rewrite -Ha ?nth_rcons ?Ly // size_rcons (leq_trans Ly).
have : get_xy s x (size u) = a.
  rewrite -Ha  ?size_rcons //.
  by rewrite nth_rcons ltnn eqxx.
have Hl1 : size u < n.
  by apply: leq_trans Hl; rewrite size_rcons.
case: {Ha Hv Hl}a.
  by rewrite /= add0n f_interpE.
by rewrite /= add0n f_interpE // => ->.
Qed.

Lemma interp_pgen_form_col n (s : sol) pp y l :
  (Z.of_nat n * Z.of_nat n < Int63Axioms.wB)%Z ->
  y < n ->
  entail n pp s ->
  count (get_col s y) = l ->
  interp (f_interp n s)
         (pgen_form (pget_col pp y) 
                (fun i => varb (i * nat2int n + nat2int y))
               l n).
Proof.
move=> Hm Hs He H.
have /entailP[Spp Sp H1e] := He.
have /andP[/eqP S1pp /forallP S2pp] := Spp.
have /andP[/eqP S1p /forallP S2p] := Sp.
have Hus : size (get_col s y) = n.
  by rewrite size_map.
have : get_col s y \in gen_constr l n.
  by apply: gen_constr_mem.
rewrite /pgen_form.
elim: gen_constr => [//|a l1 IH].
rewrite inE => /orP[/eqP Ha | Hu]; last first.
  rewrite /=.
  case E : (pcheck (pget_col pp y) a) => /=.
    by rewrite mk_orb_cons [mk_orb _]IH ?orbT.
  by apply: IH.
rewrite /=.
have -> : pcheck (pget_col pp y) a.
  rewrite -Ha.
  apply: (pcheck_correct _ _ _ false).
    by rewrite size_map S1pp (get_col_size n).
  move=> x b Hx Hn.
  rewrite -get_row_col.
  apply: H1e => //.
    by move: Hx; rewrite size_map S1pp.
  by move: Hn; rewrite -pget_row_col.
rewrite /= mk_orb_cons /=.
rewrite mk_andb_map // => i.
have {3}-> : n = size a by rewrite -Ha.
have: (forall x, x < size a ->  nth false a x = get_xy s x y).
  by move=> x Hx; rewrite -Ha -get_row_col.
have: size a <= n by rewrite -Ha Hus.
move: {Ha}a.
apply: last_ind => //= u a IH1 Hl Ha.
rewrite size_rcons.
rewrite int_iota_rcons zip_rcons ?map_rcons ?size_map ?size_iota //= => Hv.
case: (List_in_rcons _ _ _ _ Hv) => [->/=|/IH1 -> //]; last 2 first.
- by rewrite (leq_trans _ Hl) // size_rcons.
- move=> x Lx.
  by rewrite -Ha ?nth_rcons ?Lx // size_rcons (leq_trans Lx).
have : get_xy s (size u) y = a.
  rewrite -Ha  ?size_rcons //.
  by rewrite nth_rcons ltnn eqxx.
have Hl1 : size u < n.
  by apply: leq_trans Hl; rewrite size_rcons.
case: {Ha Hv Hl}a.
  by rewrite /= add0n f_interpE.
by rewrite /= add0n f_interpE // => ->.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*                                 The problem                               *)
(*                                                                           *)
(*****************************************************************************)


Section Problem.

Record problem := Problem 
  {p_size : nat; p_cols : seq (seq nat);
   p_rows : seq (seq nat); p_known_black : seq (nat * seq nat)}.

Variable pb : problem.

Let psize := p_size pb.
Let cols := p_cols pb.
Let rows := p_rows pb. 
Let known_black := p_known_black pb.

Definition pb1 : problem := {|
p_size := 25;
p_rows := [:: [:: 7; 3; 1; 1; 7];
              [:: 1; 1; 2; 2; 1; 1];
              [:: 1; 3; 1; 3; 1; 1; 3;
                  1];
              [:: 1; 3; 1; 1; 6; 1; 3;
                  1];
              [:: 1; 3; 1; 5; 2; 1; 3;
                  1];
              [:: 1; 1; 2; 1; 1];
              [:: 7; 1; 1; 1; 1; 1; 7];
              [:: 3; 3];
              [:: 1; 2; 3; 1; 1; 3; 1;
                  1; 2];
              [:: 1; 1; 3; 2; 1; 1];
              [:: 4; 1; 4; 2; 1; 2];
              [:: 1; 1; 1; 1; 1; 4; 1;
                  3];
              [:: 2; 1; 1; 1; 2; 5];
              [:: 3; 2; 2; 6; 3; 1];
              [:: 1; 9; 1; 1; 2; 1];
              [:: 2; 1; 2; 2; 3; 1];
              [:: 3; 1; 1; 1; 1; 5; 1];
              [:: 1; 2; 2; 5];
              [:: 7; 1; 2; 1; 1; 1; 3];
              [:: 1; 1; 2; 1; 2; 2; 1];
              [:: 1; 3; 1; 4; 5; 1];
              [:: 1; 3; 1; 3; 10; 2];
              [:: 1; 3; 1; 1; 6; 6];
              [:: 1; 1; 2; 1; 1; 2];
              [:: 7; 2; 1; 2; 5]];
p_cols := [:: [:: 7; 2; 1; 1; 7];
              [:: 1; 1; 2; 2; 1; 1];
              [:: 1; 3; 1; 3; 1; 3; 1;
                  3; 1];
              [:: 1; 3; 1; 1; 5; 1; 3;
                  1];
              [:: 1; 3; 1; 1; 4; 1; 3;
                  1];
              [:: 1; 1; 1; 2; 1; 1];
              [:: 7; 1; 1; 1; 1; 1; 7];
              [:: 1; 1; 3];
              [:: 2; 1; 2; 1; 8; 2; 1];
              [:: 2; 2; 1; 2; 1; 1; 1;
                  2];
              [:: 1; 7; 3; 2; 1];
              [:: 1; 2; 3; 1; 1; 1; 1;
                  1];
              [:: 4; 1; 1; 2; 6];
              [:: 3; 3; 1; 1; 1; 3; 1];
              [:: 1; 2; 5; 2; 2];
              [:: 2; 2; 1; 1; 1; 1; 1;
                  2; 1];
              [:: 1; 3; 3; 2; 1; 8; 1];
              [:: 6; 2; 1];
              [:: 7; 1; 4; 1; 1; 3];
              [:: 1; 1; 1; 1; 4];
              [:: 1; 3; 1; 3; 7; 1];
              [:: 1; 3; 1; 1; 1; 2; 1;
                  1; 4];
              [:: 1; 3; 1; 4; 3; 3];
              [:: 1; 1; 2; 2; 2; 6; 1];
              [:: 7; 1; 3; 2; 1; 1]];
p_known_black := [:: (3,[:: 3; 4; 12; 13;
                          21]);
                     (8, [:: 6; 7; 10; 14;
                          15; 18]);
                     (16, [:: 6; 11; 16; 20]);
                     (21, [:: 3; 4; 9; 10;
                          15; 20; 21])
                     ] |}.


Definition pb2 : problem := {|
p_size := 4;
p_cols := [:: [::]; [:: 2]; [:: 2];
              [::]];
p_rows := [:: [::]; [:: 2]; [:: 2];
              [::]];
p_known_black := [::] 
|}.


Definition verify_col s :=
  all (fun i => count (get_col s i) == nth [::] cols i) (iota 0 psize).

Lemma verify_colP s : 
  reflect (forall i : 'I_psize, count (get_col s i) = nth [::] cols i)
          (verify_col s).
Proof.
apply: (iffP allP) => [H i| H x].
  suff /(H _)/eqP : (i : nat) \in iota 0 psize by [].
  by rewrite -val_enum_ord map_f // mem_enum.
rewrite -val_enum_ord => /mapP /= [y Hy ->].
by rewrite H.
Qed.

Hypothesis valid_rows_size : size rows = psize. 
(*
Lemma valid_rows_size : size rows = psize.
Proof. by []. Qed.
*)

Hypothesis valid_cols_size : size cols = psize. 
(*
Lemma valid_cols_size : size cols = psize.
Proof. by []. Qed.
*)

(*
Compute [seq (length (gen_constr i psize)) | i <- rows].
*)

Definition verify_row s :=
  all (fun i => count (get_row s i) == nth [::] rows i) (iota 0 psize).

Lemma verify_rowP s : 
  reflect (forall i : 'I_psize, count (get_row s i) = nth [::] rows i)
          (verify_row s).
Proof.
apply: (iffP allP) => [H i| H x].
  suff /(H _)/eqP : (i : nat) \in iota 0 psize by [].
  by rewrite -val_enum_ord map_f // mem_enum.
rewrite -val_enum_ord => /mapP /= [y Hy ->].
by rewrite H.
Qed.

Definition valid_count d l :=
  (all (leq 1) l) && 
  ((size l).-1 + foldl addn 0 l  <= d).

Lemma valid_count_gt_0 l d i :
  valid_count d l -> i \in l -> 0 < i.
Proof. by move=> /andP[/allP/(_ i)]. Qed.

Lemma valid_count_suml d l :
  valid_count d l -> (size l).-1 + \sum_(i <- l) i  <= d.
Proof. by move=> /andP[_]; rewrite foldl_addn. Qed.

Hypothesis valid_count_rows : all (valid_count psize) rows.

(*
Lemma valid_count_rows : all (valid_count psize) rows.
Proof. by compute. Qed.
*)

Hypothesis valid_count_cols : all (valid_count psize) cols.

(*
Lemma valid_count_cols : all (valid_count psize) cols.
Proof. by compute. Qed.
*)

Hypothesis psize_fits_int : 
  (Z.of_nat psize * Z.of_nat psize < Int63Axioms.wB)%Z.

(*
Lemma psize_fits_int : 
  (Z.of_nat psize * Z.of_nat psize < Int63Axioms.wB)%Z.
Proof. by []. Qed.
*)

Definition verify_known_black s :=
  all (fun x => 
          all (fun y => ~~ get_xy s x.1 y) x.2) known_black.


Lemma verify_known_blackP s : 
  reflect (forall (x y : nat) (l : seq nat), 
            y \in l -> (x, l) \in known_black ->
            get_xy s x y = black)
          (verify_known_black s).
Proof.
apply: (iffP allP) => [H x y l xIl lyIb| H [l y] lyIb].
  by have /allP/(_ _ xIl) := H _ lyIb; case: get_xy.
apply/allP=> x /= xIl.
by rewrite (H _ _ _ xIl lyIb).
Qed.

Definition valid_known_black :=
  all (fun x => 
          (x.1 < psize) && all (fun y => y < psize) x.2) known_black.

Hypothesis valid_known_black_true : valid_known_black.

Lemma valid_known_blackP : 
  forall x y l, y \in l -> (x, l) \in known_black -> x < psize /\ y < psize.
Proof.
move=> x y l yIl xlIk.
have /allP/(_ _ xlIk)/andP[H1] := valid_known_black_true.
by move=> /allP/(_ y yIl).
Qed.

Definition verify_square n (s : sol) :=
  (size s == n) && (all (fun i => size i == n) s).

Lemma verify_square_is_square n s :
   verify_square n s = is_square n s.
Proof.
apply/andP/andP=> [[H1 /allP H2]|[H1 H2]]; split=> //.
  apply/forallP => x.
  by apply/H2/mem_nth; rewrite (eqP H1).
apply/allP=> i Hi.
have F : index i s < n.
  by rewrite -(eqP H1) index_mem.
have /forallP/(_ (Ordinal F)) := H2.
by rewrite nth_index.
Qed.

Definition verify_sol s :=
 [&& verify_square psize s, verify_col s,  verify_row s & verify_known_black s]. 

Lemma verify_solP s : 
  reflect
    [/\  
        is_square psize s, 
        forall i : 'I_psize, count (get_row s i) = nth [::] rows i,
        forall j : 'I_psize, count (get_col s j) = nth [::] cols j &
        forall (x y : nat) (l : seq nat), 
            y \in l -> (x, l) \in known_black -> get_xy s x y = black]
    (verify_sol s).
Proof.
apply: (iffP and4P)=> [[H1 H2 H3 H4]|[H1 H2 H3 H4]]; split => //.
- by rewrite -verify_square_is_square.
- by apply: verify_rowP.
- by apply: verify_colP.
- by apply: verify_known_blackP.
- by rewrite verify_square_is_square.
- by have /verify_colP := H3.
- by have /verify_rowP := H2.
by have /verify_known_blackP := H4.
Qed.

Definition init_pp : psol := nseq psize (nseq psize None).

Lemma init_pp_size : size init_pp = psize.
Proof. by rewrite size_nseq. Qed.

Lemma init_pp_square : is_square psize init_pp.
Proof.
rewrite /is_square init_pp_size eqxx /=.
apply/forallP=> [[x]] /=.
rewrite !nth_nseq => ->.
by rewrite size_nseq.
Qed.

Lemma init_pp_correct i j : 
  pget_xy init_pp i j = None.
Proof.
rewrite /pget_xy /pget_row.
rewrite nth_nseq; case: leqP; rewrite ?nth_nil //.
by rewrite nth_nseq if_same.
Qed.

Lemma init_pp_entail s : is_square psize s -> entail psize init_pp s.
Proof.
rewrite /entail init_pp_square => -> /=.
apply/forallP=> i; apply/forallP=> j; apply/forallP=> c.
by rewrite init_pp_correct.
Qed.

Fixpoint vupdate s (l : seq nat) i  :=
  if l is j :: l then
  vupdate (pset_xy s i j (Some black)) l i else
  s.

Lemma vupdate_square n s l i : 
  is_square n s -> is_square n (vupdate s l i).
Proof.
elim: l s => //= a l IH s Hs.
apply: IH.
by apply: pset_xy_square.
Qed.

Fixpoint hupdate s (l : seq (nat * seq nat)) :=
  if l is (i, vl) :: l then
    hupdate (vupdate s vl i) l
  else s.

Lemma hupdate_square n s l : 
  is_square n s -> is_square n (hupdate s l).
Proof.
elim: l s => //= [] [vl a] l IH s Hs.
by apply/IH/vupdate_square.
Qed.

Definition pp := hupdate init_pp known_black.

Lemma pp_square : is_square psize pp.
Proof. by apply/hupdate_square/init_pp_square. Qed.

Lemma pp_correct s : verify_sol s -> entail psize pp s.
Proof.
move=> /and4P[Hs _ _ /verify_known_blackP].
rewrite /pp.
rewrite verify_square_is_square in Hs.
have := init_pp_entail s Hs.
have := init_pp_square.
move: valid_known_blackP.
elim: known_black init_pp => //= [] [x vl] l IH s1 H1s1 H2s1 H3s1 H.
apply: IH => 
    [x1 y1 l1 y1Il1 x1l1Il|||x1 y1 l1 x1Il1 V1].
- by apply: H1s1 y1Il1 _; rewrite inE x1l1Il orbC.
- by apply: vupdate_square.
- have: forall y, y \in vl -> get_xy s x y = black.
    by move=> y Hy; apply: H Hy _; rewrite inE eqxx.
  have: forall y, y \in vl -> y < psize.
    move=> y yIvl.
    have [] // := H1s1 x y _ yIvl.
    by rewrite inE eqxx.
  elim: (vl) s1 H1s1 H2s1 H3s1 => //= a l1 IH1 s1 H1s1 H2s1 H3s1 H1 H2.
  have [F1 F2] : x < psize /\ a < psize.
    have F1 : a \in a :: l1 by rewrite inE eqxx.
    by apply: H1s1 F1 _; rewrite inE eqxx.
  apply: IH1 => // [x1 y1 l2 y1Il2|||y1 h1Il1|y yIl1].
  - rewrite !inE=> /orP[/andP[/=  /eqP -> /eqP V1]|V1].
      split=> //.
      by apply: H1; rewrite -V1 inE orbC y1Il2.
    by apply: H1s1 y1Il2 _; rewrite inE orbC V1.
  - by apply: pset_xy_square.
  - apply/entailP; split => // [|i j b Li Lj].
      by apply: pset_xy_square.
    rewrite (pset_xy_correct psize) //.
    case: eqP=> [<-|/= _]; last first.
      by have /entailP[_ _] := H3s1; apply.
    case: eqP=> [<-/= [<-]|/= _]; last first.
      by have /entailP[_ _] := H3s1; apply.
    by apply: H2; rewrite inE eqxx.
  - by apply: H1; rewrite inE orbC h1Il1.
  by apply: H2; rewrite inE orbC yIl1.
by apply: H x1Il1 _; rewrite inE orbC V1.
Qed.

Definition cl i pp :=
let l := nth [::] rows i in
let pl := pget_row pp i in
let v := gen_constr l psize in
[seq i <- v | pcheck pl i].

Lemma cl_correct pp p i :  
  entail psize pp p -> 
  count (get_row p i) = nth [::] rows i->
  i < psize ->
  get_row p i \in cl i pp.
Proof.
move=> Epp Hc Li.
have /entailP[Spp Sp E1pp] := Epp.
apply: entail_pcheck_row Epp _ _ => //.
apply: gen_constr_mem => //.
by apply: get_row_size.
Qed.

Lemma cl_size pp i l :  
  i < psize -> l \in cl i pp -> size l = psize.
Proof.
move=> Li; rewrite /cl mem_filter => /andP[_ H].
have Vp : valid_count psize (nth [::] rows i).
  have F1 : i < size rows by rewrite valid_rows_size.
  by have /allP/(_  _ (mem_nth [::] F1)) := 
            valid_count_rows.
apply: gen_constr_size H _ => [i1|].
  by apply: valid_count_gt_0 Vp.
by apply: valid_count_suml Vp.
Qed.
 
Definition lpp pp := foldi (fun n psol => 
   let v := cl n psol in
   if v is [::l] then
    (pset_row psol n [seq Some i | i <- l]) else psol) psize.-1 pp.

Hypothesis psize_gt_0 : 0 < psize.

Lemma lpp_correct p pp : 
  entail psize pp p -> 
  (forall i, i < psize -> count (get_row p i) = nth [::] rows i)->
  entail psize (lpp pp) p.
Proof.
move=> Ep Cp.
rewrite /lpp.
elim: {-2}(_.-1) (leqnn (psize.-1)) pp Ep Cp => /=;
  last first.
  set f := fun _ _ => _.
  move=> n IH Ln pp Ep Cp.
  apply: IH => //.
  - by apply: ltnW.
  have Ln1 : n.+1 < psize by rewrite -(prednK psize_gt_0).
  have := cl_correct pp p n.+1 Ep (Cp n.+1 Ln1) Ln1.
  case: cl => // a [|l] //.
  rewrite inE => /eqP<-.
  have /entailP[H1 H2 H3] := Ep.
  have Hpp : size pp = psize by case/andP: H1 => /eqP.
  (apply/entailP; split) => // [|i j b Hi Hj].
    apply: pset_row_square => // Hn.
    by rewrite size_map (get_row_size psize).
  rewrite /pget_xy.
  rewrite pset_row_correct //; last by rewrite Hpp.
  case: eqP => [<-|_ U]; last by apply: H3.
  rewrite (nth_map false) // => [[<-//]|].
  by rewrite (get_row_size psize).
move=> L pp Ep Cp.
have /entailP[H1 H2 H3] := Ep.
have Hpp : size pp = psize by case/andP: H1 => /eqP.
have F1 : 0 < psize by [].
have := cl_correct pp p 0 Ep (Cp _ F1) F1.
case: cl => // a [|l] //.
rewrite inE => /eqP<-.
(apply/entailP; split) => // [|i j b Hi Hj].
  apply: pset_row_square => // Hn.
  by rewrite size_map (get_row_size psize).
rewrite /pget_xy.
rewrite pset_row_correct //; last by rewrite Hpp.
case: eqP => [<-|_ U]; last by apply: H3.
rewrite (nth_map false) // => [[<-//]|].
by rewrite (get_row_size psize).
Qed.
  
Definition cp i pp :=
let l := nth [::] cols i in
let pl := pget_col pp i in
let v := gen_constr l psize in
[seq i <- v | pcheck pl i].

Lemma cp_correct pp p j :  
  entail psize pp p -> 
  count (get_col p j) = nth [::] cols j ->
  j < psize ->
  get_col p j \in cp j pp.
Proof.
move=> Epp Hc Lj.
apply: entail_pcheck_col (Epp) _ _ => //.
apply: gen_constr_mem => //.
apply: get_col_size => //.
by case/entailP : Epp.
Qed.

Lemma cp_size pp j l :  
  j < psize -> l \in cp j pp -> size l = psize.
Proof.
move=> Lj; rewrite /cp mem_filter => /andP[_ H].
have Vp : valid_count psize (nth [::] cols j).
  have F1 : j < size cols by rewrite valid_cols_size.
  by have /allP/(_  _ (mem_nth [::] F1)) := 
            valid_count_cols.
apply: gen_constr_size H _ => [i1|].
  by apply: valid_count_gt_0 Vp.
apply: valid_count_suml Vp.
Qed.

Definition cpp pp := foldi (fun n psol => 
   let v := cp n psol in
   if v is [::l] then
    (pset_col psol n [seq Some i | i <- l]) else psol) psize.-1 pp.

Lemma cpp_correct p pp : 
  entail psize pp p -> 
  (forall j, j < psize -> count (get_col p j) = nth [::] cols j)->
  entail psize (cpp pp) p.
Proof.
move=> Ep Cp.
rewrite /cpp.
elim: {-2}(_.-1) (leqnn (psize.-1)) pp Ep Cp => /=;
  last first.
  set f := fun _ _ => _.
  move=> n IH Ln pp Ep Cp.
  apply: IH => //.
    by apply: ltnW.
  have Ln1 : n.+1 < psize by rewrite -(prednK psize_gt_0).
  have := cp_correct pp p n.+1 Ep (Cp n.+1 Ln1) Ln1.
  case: cp => // a [|l] //.
    rewrite inE => /eqP<-.
  have /entailP[H1 H2 H3] := Ep.
  have Hpp : size pp = psize by case/andP: H1 => /eqP.
  have Hp : size p = psize by case/andP: H2 => /eqP.
  (apply/entailP; split) => // [|i j b Hi Hj].
    apply: pset_col_square => //.
    by rewrite size_map (get_col_size psize).
  rewrite /pget_xy pget_row_col.
  rewrite (pset_col_correct psize) //; last first.
    by rewrite !size_map.
  case: eqP => [<-|_ U]; last first.
    apply: H3 => //.
    by rewrite [LHS]pget_row_col.
  rewrite (nth_map false) // => [[<-//]|].
    by rewrite [LHS]get_row_col.
  rewrite size_map.
  by move: Hi; rewrite Hp.
move=> L pp Ep Cp.
have /entailP[H1 H2 H3] := Ep.
have Hpp : size pp = psize by case/andP: H1 => /eqP.
have Hp : size p = psize by case/andP: H2 => /eqP.
have F1 : 0 < psize by [].
have := cp_correct pp p 0 Ep (Cp _ F1) F1.
case: cp => // a [|l] //.
rewrite inE => /eqP<-.
(apply/entailP; split) => // [|i j b Hi Hj].
  apply: pset_col_square => //.
  by rewrite size_map (get_col_size psize).
rewrite /pget_xy pget_row_col.
rewrite (pset_col_correct psize) //; last first.
  by rewrite !size_map.
case: eqP => [<-|_ U]; last first.
  apply: H3 => //.
  by rewrite [LHS]pget_row_col.
rewrite (nth_map false) // => [[<-//]|].
  by rewrite [LHS]get_row_col.
rewrite size_map.
by move: Hi; rewrite Hp.
Qed.

Fixpoint iter_pp n pp := 
  let pp1 := cpp (lpp pp) in
  if pp1 == pp then pp else
  if n is n1.+1 then iter_pp n1 pp1 else pp1.

Lemma iter_pp_correct n p pp : 
  entail psize pp p -> 
  verify_sol p ->
  entail psize (iter_pp n pp) p.
Proof.
move=> He Hv.
have /verify_solP[H1 H2 H3 H4] := Hv.
elim: n pp He => /= [pp1 He|n IH pp1 He1].
  case: eqP => // _.
  apply: cpp_correct=> [|j Hj]; last first.
    by apply: (H3 (Ordinal Hj)).
  apply: lpp_correct => // i Hi.
  by apply: (H2 (Ordinal Hi)).
case: eqP => // _.
apply: IH.
apply: cpp_correct=> [|j Hj]; last first.
  by apply: (H3 (Ordinal Hj)).
apply: lpp_correct => // i Hi.
by apply: (H2 (Ordinal Hi)).
Qed.

Definition final_pp := iter_pp psize pp.

Lemma final_pp_entail p : verify_sol p -> entail psize final_pp p.
Proof.
by move=> Hv; apply: iter_pp_correct => //; apply: pp_correct.
Qed.

Definition gen_cols pp :=
  andb 
    [seq  (pgen_form
             (pget_col pp j)
             (fun i => varb (i * nat2int psize + nat2int j))
             (nth [::] cols j)) psize | j <- iota 0 psize].

Lemma gen_cols_correct s :
  verify_sol s -> interp (f_interp psize s) (gen_cols final_pp).
Proof.
move=> Hv.
rewrite /gen_cols.
have : forall i, i \in iota 0 psize -> i < psize.
  by move=> i; rewrite mem_iota.
elim: iota => // b l IH Hu.
rewrite map_cons [interp _ _]mk_andb_cons.
apply/andP; split; last first.
  by apply: IH => i Hi; apply: Hu; rewrite inE Hi orbC.
have Lb : b < psize by apply: Hu; rewrite inE eqxx.
apply: interp_pgen_form_col.
- by exact: psize_fits_int.
- by exact: Lb.
- by apply: final_pp_entail.
have /verify_solP[_ _ H _] := Hv.
by apply: H (Ordinal Lb).
Qed.

Definition gen_rows pp :=
  andb 
    [seq  (pgen_form
             (pget_row pp i)
             (fun j =>  varb (nat2int i * nat2int psize + j))
             (nth [::] rows i)) psize | i <- iota 0 psize].

Lemma gen_rows_correct s :
  verify_sol s -> interp (f_interp psize s) (gen_rows final_pp).
Proof.
move=> Hv.
rewrite /gen_rows.
have : forall i, i \in iota 0 psize -> i < psize.
  by move=> i; rewrite mem_iota.
elim: iota => // b l IH Hu.
rewrite map_cons [interp _ _]mk_andb_cons.
apply/andP; split; last first.
  by apply: IH => i Hi; apply: Hu; rewrite inE Hi orbC.
have Lb : b < psize by apply: Hu; rewrite inE eqxx.
apply: interp_pgen_form_row.
- by exact: psize_fits_int.
- by exact: Lb.
- by apply: final_pp_entail.
have /verify_solP[_ H _ _] := Hv.
by apply: H (Ordinal Lb).
Qed.

Definition gen_all :=
  andb [:: gen_rows final_pp; gen_cols final_pp].

Lemma gen_all_correct s :
  verify_sol s -> interp (f_interp psize s) gen_all.
Proof.
move=> Hv; rewrite [interp _ _]mk_andb_cons.
rewrite [X in X && _]gen_rows_correct; last by exact: Hv.
by rewrite mk_andb_cons /= [X in X && _]gen_cols_correct.
Qed.   

Definition test_eq n (s1 s2 : sol) :=
  andb 
   [seq 
      (andb 
        [seq (if get_xy s1 i j then
                 (varb (nat2int i * nat2int n + nat2int j)) else
                 (negb (varb (nat2int i * nat2int n + nat2int j))))
      | j <- iota 0 n]) | i <- iota 0 n].

Lemma test_is_square_eq_correct n s1 s2 :
  (Z.of_nat n * Z.of_nat n < Int63Axioms.wB)%Z ->
  is_square n s1 -> is_square n s2 ->
  interp (f_interp n s2) (test_eq n s1 s2) -> s1 = s2.
Proof.
move=> Hn Hs1 Hs2 Hi.
have S1 : size s1 = n by have /andP[/eqP] := Hs1.
have S2 : size s2 = n by have /andP[/eqP] := Hs2.
apply: (@eq_from_nth _ ([::] : seq bool))=> [|i H1i]; first by rewrite S2.
have Hin : i < n by rewrite -S1.
have : size (nth [::] s1 i) = n.
  by case/andP : Hs1 => _ /forallP/(_ (Ordinal Hin))/eqP.
have : size (nth [::] s2 i) = n.
  by case/andP : Hs2 => _ /forallP/(_ (Ordinal Hin))/eqP.
move: Hi.
have: i \in iota 0 n by rewrite mem_iota -S1.
rewrite /test_eq.
elim: {-2}iota => //= a l IH.
rewrite mk_andb_cons !inE /= => /orP[/eqP Ha|H] /andP[H1 H2] H3 H4; last first.
  by apply: IH.
apply: (@eq_from_nth _ false); first by rewrite H4.
move=> j Hj.
move: H1.
have: j \in iota 0 n by rewrite mem_iota -H4.
elim: iota => //= b l1 IH1.
rewrite mk_andb_cons !inE => /orP[/eqP Hb|H1] /andP[V1 V2]; last first.
  by apply: IH1.
suff EE : 
    get_xy s2 i j = interp (f_interp n s2) 
                     (varb (nat2int i * nat2int n + nat2int j)).
  move: {V2}V1 EE.
  rewrite -Ha -Hb.
  case E : get_xy; rewrite /f_interp /= => V1 V2.
    by rewrite [LHS]E [RHS]V2 V1.
  by rewrite [LHS]E [RHS]V2 (negPf V1).
rewrite /= f_interpE //.
by rewrite -H4.
Qed.

Lemma test_eq_correct s1 s2 :
  verify_sol s1 -> verify_sol s2 ->
  interp (f_interp psize s2)
           (implb [:: test_eq psize s1 s2; gen_all]) -> s1 = s2.
Proof.
move=> Hs1 Hs2 Hi.
apply: test_is_square_eq_correct psize_fits_int _ _ _.
- by case/verify_solP : Hs1.
- by case/verify_solP : Hs2.
move: (gen_all_correct _ Hs2) Hi.
rewrite /= mk_implb_two /= !mk_andb_cons !mk_andb_nil !andbT /=.
by case: (_ && _).
Qed.

End Problem.



