(*
From SMTCoq Require Import SMTCoq.
From SMTCoq Require Import PArray Int63.
*)

From SMTCoq Require  Int63.
Require Import Int31 ZArith.
From mathcomp Require Import all_ssreflect.

Locate int.
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
|  trueb 
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
 foldl Datatypes.implb (head true l) (behead l).

Fixpoint interp (f : int -> bool) exp {struct exp} := 
match exp with
|  trueb => Datatypes.true
| falseb => Datatypes.false
| eqb e1 e2 => Bool.eqb (interp f e1) (interp f e2)
| andb es =>
    let es1 := map (interp f) es in mk_andb es1
| implb es =>
    let es1 := map (interp f) es in mk_implb es1
| orb es =>
    let es1 := map (interp f) es in
    mk_orb es1
| negb e1 => Datatypes.negb (interp f e1) 
| varb i => f i
end.

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

Definition is_square {A: Type} (p : seq (seq A)) :=
  [forall i : 'I_(size p), size (nth [::] p i) == size p].

Lemma get_row_size s i :
   is_square s ->
   i < size s -> size (get_row s i) = size s.
Proof.
move=> Hwf Li.
by have /forallP/(_ (Ordinal Li))/eqP := Hwf.
Qed.

(*****************************************************************************)
(*                                                                           *)
(*        A partial solution as a sequence of sequence of optional colours   *)
(*                                                                           *)
(*****************************************************************************)


Definition psol := seq (seq (option colour)).

(* Getting a row *)
Definition pget_row (s : psol) i := nth [::] s i.

Lemma pget_row_size s i :
  is_square s -> i < size s -> size (pget_row s i) = size s.
Proof.
move=> Hwf Li.
by have /forallP/(_ (Ordinal Li))/eqP := Hwf.
Qed.

(* Setting a row *)
Definition pset_row (s : psol) i v := 
  [seq (if j == i then v else pget_row s j) | j <- iota 0 (size s)].

Lemma pset_row_square s i v :
 is_square s -> 
 (i < size s -> size v = size s) -> is_square (pset_row s i v).
Proof.
move=> H Hs; apply/forallP=> x; apply/eqP.
rewrite [RHS]size_map size_iota.
have Lx : x < size s.
  by case: x => /= x1; rewrite size_map size_iota.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota // add0n.
case: eqP => // xDi.
  by apply: Hs; rewrite -xDi.
by rewrite pget_row_size.
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

(* Getting a colum *)
Definition pget_col (s : psol) j := [seq nth None l j | l <- s].

(* Setting a column *)
Definition pset_col (s : psol) j v :=
  [seq (let l := pget_row s i in
      [seq (if j1 == j then nth None v i else nth None l j1) | 
          j1 <- iota 0 (size l)])
       | i <- iota 0 (size s)].

Lemma pset_col_square s j v :
 is_square s -> size v = size s -> is_square (pset_col s j v).
Proof.
move=> H Hs; apply/forallP=> x; apply/eqP.
rewrite [RHS]size_map size_iota.
have Lx : x < size s.
  by case: x => /= x1; rewrite size_map size_iota.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota // add0n.
by rewrite size_map size_iota pget_row_size.
Qed.

Lemma pset_col_correct s i j v :
 size v = size s -> is_square s -> j < size s -> 
 pget_col (pset_col s j v) i = 
              if i == j then v else pget_col s i.
Proof.
move=> Hs Hwf Ls.
apply: (@eq_from_nth _ None) => [|i1 Hi1].
  by case: eqP => _; rewrite !size_map size_iota ?Hs.
have /(nth_iota 0) := Hi1.
rewrite add0n => {1}<-.
rewrite [LHS](nth_map [::]) // !(nth_iota 0) ?size_iota //; last first.
  by move: Hi1; rewrite !size_map size_iota.
have F : 0 + i1 < size (iota 0 (size s)).
  by move: Hi1; rewrite !size_map size_iota.
rewrite (nth_map 0 [::] _ F) /=.
rewrite nth_iota !add0n; last first.
  by move: Hi1; rewrite !size_map size_iota.
have Oi1 : i1 < size s.
  by move: Hi1; rewrite !size_map size_iota.
have [Ls1|Ls1] := leqP (size s) i.
  rewrite [LHS]nth_default ?size_map ?size_iota //; last first.
    by have /forallP/(_ (Ordinal Oi1))/eqP-> := Hwf.
  case: eqP=> H.
    by move: Ls1; rewrite H leqNgt Ls.
  rewrite (nth_map [::]) // nth_default //.
  by have /forallP/(_ (Ordinal Oi1))/eqP-> := Hwf.
rewrite (nth_map 0); last first.
  by rewrite size_iota pget_row_size.
rewrite nth_iota ?pget_row_size // add0n.
case: eqP => // /eqP iDj.
by rewrite (nth_map [::]).
Qed.

(* Getting  a cell *)
Definition pget_xy (s : psol) i j := nth None (pget_row s i) j.

Definition pset_xy (s : psol) i j v := 
  pset_row s i 
   (let l := pget_row s i in 
         [seq (if j1 == j then v else nth None l j1) | j1 <- iota 0 (size l)]).

Lemma pset_xy_square s i j v :
  is_square s -> is_square (pset_xy s i j v).
Proof.
move=> H.
apply: pset_row_square => // Hi.
by rewrite size_map size_iota pget_row_size.
Qed.

Lemma pset_xy_correct s i j i1 j1 v :
  is_square s -> i < size s -> j < size s ->
  pget_xy (pset_xy s i j v) i1 j1 = 
    if (i == i1) && (j == j1) then v else pget_xy s i1 j1.
Proof.
move=> Hwf Li Lj.
rewrite /pget_xy /pset_xy.
rewrite pset_row_correct //.
case: eqP => // <-.
case: (leqP (size s) j1) => H; last first.
  rewrite (nth_map 0); last first.
    by rewrite size_iota pget_row_size.
  rewrite nth_iota ?pget_row_size // add0n eq_sym.
  by case: eqP.
rewrite nth_default; last first.
  by rewrite size_map size_iota pget_row_size.
case: eqP => /= H1.
  by move: H; rewrite -H1 leqNgt Lj.
by rewrite nth_default ?pget_row_size.
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
Definition entail (ps : psol) (s : sol) :=
  [forall i : 'I_(size ps),
   forall j : 'I_(size ps),
   forall b : bool,
      (pget_xy ps i j == Some b) ==> (get_xy s i j == b)].

Lemma entailP ps s :
  reflect 
   (forall i j b, i < size ps -> j < size ps -> 
       pget_xy ps i j = Some b -> get_xy s i j = b)
   (entail ps s).
Proof.
apply: (iffP forallP) => 
    [H i j b Hi Hj H1|H x].
  have /forallP/(_ (Ordinal Hj))/forallP/(_ b) := H (Ordinal Hi).
  move/implyP=> H2.
  by apply/eqP/H2/eqP.
apply/forallP=> y; apply/forallP=> b; apply/implyP=> /eqP.
by move=> /(H x y b (ltn_ord x) (ltn_ord y))->.
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
 
Lemma entail_pcheck_col ps p (l : seq (seq bool)) i :
  is_square ps -> is_square p -> size ps = size p ->
  entail ps p -> i < size ps ->
  get_col p i \in l ->
  get_col p i \in [seq j <- l | pcheck (pget_col ps i) j].
Proof.
move=> Sps Sp Es He Hs Hg.
rewrite mem_filter Hg andbT.
apply: (pcheck_correct _ _ _ false) => [|i1 b Hi1 Li1].
  by apply: etrans (_ : size ps = _); rewrite size_map.
rewrite -get_row_col.
have /entailP := He.
apply => //.
  by move: Hi1; rewrite size_map.
by rewrite [LHS]pget_row_col.
Qed.

Lemma entail_pcheck_row ps p (l : seq (seq bool)) i :
  is_square ps -> is_square p -> size ps = size p ->
  entail ps p -> i < size ps ->
  get_row p i \in l ->
  get_row p i \in [seq j <- l | pcheck (pget_row ps i) j].
Proof.
move=> Sps Sp Es He Hs Hg.
rewrite mem_filter Hg andbT.
apply: (pcheck_correct _ _ _ false) => [|i1 b Hi1 Li1].
  apply: etrans (_ : size ps = _); first by rewrite pget_row_size.
  by rewrite get_row_size // -Es.
have /entailP := He.
apply => //.
by move: Hi1; rewrite pget_row_size. 
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
  
Lemma interp_gen_form_row (s : sol) x l :
  s != [::] ->
  size (get_row s x) = size s ->
  (Z.of_nat (size s) * Z.of_nat (size s) < Int63Axioms.wB)%Z ->
  x < size s ->
  count (get_row s x) = l ->
  interp (fun u => let: (i, j) := to_ij (nat2int (size s)) u in
                   get_xy s i j)
         (gen_form (fun i => varb (nat2int (x * (size s)) + i))
               l (size s)).
Proof.
move=> HnZ Hus Hm Hs H.
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
have F1 : (0 <= Z.of_nat (size s) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  by apply: BigNumPrelude.Zsquare_le.
have F2 : (0 <= Z.of_nat (size u) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : Z.of_nat (size s) <= _)%Z.
    by apply/inj_le/leP/ltnW.
  by apply: BigNumPrelude.Zsquare_le.
have F3 : (0 <= Z.of_nat (x * size s) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  rewrite Nat2Z.inj_mul.
  apply: Z.le_lt_trans Hm.
  apply: Zmult_le_compat_r.
    by apply/inj_le/leP/ltnW.
  by apply: Zle_0_nat.
have F4 : (0 <= Z.of_nat (x * size s) + Z.of_nat (size u) <
 Int63Axioms.wB)%Z.
  split; first by apply: Z.add_nonneg_nonneg; apply: Zle_0_nat.
  rewrite Nat2Z.inj_mul.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : ((Z.of_nat x + 1) * Z.of_nat (size s)  <= _)%Z).
    rewrite Z.mul_add_distr_r Z.mul_1_l.
    apply: Zplus_le_compat_l.
    by apply/inj_le/leP/ltnW.
  apply: Zmult_le_compat_r; last by apply: Zle_0_nat.
  have-> : (Z.of_nat x + 1 = Z.of_nat x.+1)%Z.
    by rewrite Nat2Z.inj_succ Z.add_1_r.
  by apply/inj_le/leP.
case: {Ha Hv Hl}a.
  rewrite Int63Axioms.div_spec /nat2int.
  rewrite Int63Axioms.add_spec.
  rewrite !Int63Properties.of_Z_spec !add0n.
  rewrite !Zmod_small //.
  rewrite Int63Axioms.mod_spec.
  set u1 := Z.modulo; rewrite -{1}/u1.
  rewrite Int63Axioms.add_spec.
  rewrite !Int63Properties.of_Z_spec.
  rewrite !Zmod_small // {}/u1.
  rewrite !Nat2Z.inj_mul Z.div_add_l; last first.
    by case: (s) HnZ.
  rewrite Z.div_small; last first.
    split; first by apply: Zle_0_nat.
    by apply/inj_lt/ltP.
  rewrite Z.add_0_r Nat2Z.id.
  rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
    by rewrite Nat2Z.id => ->.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Int63Axioms.div_spec /nat2int.
rewrite Int63Axioms.add_spec.
rewrite !Int63Properties.of_Z_spec !add0n.
rewrite !Zmod_small //.
rewrite Int63Axioms.mod_spec.
set u1 := Z.modulo; rewrite -{1}/u1.
rewrite Int63Axioms.add_spec.
rewrite !Int63Properties.of_Z_spec.
rewrite !Zmod_small // {}/u1.
rewrite !Nat2Z.inj_mul Z.div_add_l; last first.
  by case: (s) HnZ.
rewrite Z.div_small; last first.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Z.add_0_r Nat2Z.id.
rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
  by rewrite Nat2Z.id => ->.
split; first by apply: Zle_0_nat.
by apply/inj_lt/ltP.
Qed.

Lemma interp_gen_form_col (s : sol) y l :
  s != [::] ->
  (Z.of_nat (size s) * Z.of_nat (size s) < Int63Axioms.wB)%Z ->
  y < size s ->
  count (get_col s y) = l ->
  interp (fun u => let: (i, j) := to_ij (nat2int (size s)) u in
                   get_xy s i j)
         (gen_form (fun i => varb (i * nat2int (size s) + nat2int y))
               l (size s)).
Proof.
move=> HnZ Hm Hs H.
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
have F1 : (0 <= Z.of_nat (size s) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  by apply: BigNumPrelude.Zsquare_le.
have F2 : (0 <= Z.of_nat y < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  have [_ F2] := F1.
  apply: Z.le_lt_trans F2.
  by apply/inj_le/leP/ltnW.
have F3 : (0 <= Z.of_nat (size u) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : Z.of_nat (size s) <= _)%Z.
    by apply/inj_le/leP/ltnW.
  by apply: BigNumPrelude.Zsquare_le.
have F4 : (0 <= Z.of_nat (size u) * Z.of_nat (size s) < Int63Axioms.wB)%Z.
  split.
    by apply: Z.mul_nonneg_nonneg; apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Zmult_le_compat_r.
    by apply/inj_le/leP/ltnW.
  by apply: Zle_0_nat.
have F6 : (0 <= Z.of_nat (size u) * Z.of_nat (size s) +
 Z.of_nat y < Int63Axioms.wB)%Z.
  split.
    apply: Z.add_nonneg_nonneg; try apply: Zle_0_nat.
    by apply: Z.mul_nonneg_nonneg; apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : ((Z.of_nat (size u) + 1) * Z.of_nat (size s)  <= _)%Z).
    rewrite Z.mul_add_distr_r Z.mul_1_l.
    apply: Zplus_le_compat_l.
    by apply/inj_le/leP/ltnW.
  apply: Zmult_le_compat_r; last by apply: Zle_0_nat.
  have-> : (Z.of_nat (size u) + 1 = Z.of_nat (size u).+1)%Z.
    by rewrite Nat2Z.inj_succ Z.add_1_r.
  by apply/inj_le/leP.
case: {Ha Hv Hl}a.
  rewrite add0n Int63Axioms.div_spec /nat2int.
  rewrite Int63Axioms.add_spec /=.
  rewrite Int63Axioms.mul_spec /=.
  rewrite !Int63Properties.of_Z_spec /=.
  rewrite !Zmod_small //.
  rewrite Int63Axioms.mod_spec.
  set u1 := Z.modulo; rewrite -{1}/u1.
  rewrite Int63Axioms.add_spec.
  rewrite Int63Axioms.mul_spec /=.
  rewrite !Int63Properties.of_Z_spec.
  rewrite !Zmod_small // {}/u1.
  rewrite  Z.div_add_l; last first.
    by case: (s) HnZ.
  rewrite Z.div_small; last first.
    split; first by apply: Zle_0_nat.
    by apply/inj_lt/ltP.
  rewrite Z.add_0_r Nat2Z.id.
  rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
    by rewrite Nat2Z.id => ->.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Int63Axioms.div_spec /nat2int.
rewrite Int63Axioms.add_spec.
rewrite Int63Axioms.mul_spec /=.
rewrite !Int63Properties.of_Z_spec !add0n.
rewrite !Zmod_small //.
rewrite Int63Axioms.mod_spec.
set u1 := Z.modulo; rewrite -{1}/u1.
rewrite Int63Axioms.add_spec.
rewrite Int63Axioms.mul_spec /=.
rewrite !Int63Properties.of_Z_spec.
rewrite !Zmod_small // {}/u1.
rewrite Z.div_add_l; last first.
  by case: (s) HnZ.
rewrite Z.div_small; last first.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Z.add_0_r Nat2Z.id.
rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
  by rewrite Nat2Z.id => ->.
split; first by apply: Zle_0_nat.
by apply/inj_lt/ltP.
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

Lemma interp_pgen_form_row (s : sol) pp x l :
  s != [::] ->
  (Z.of_nat (size s) * Z.of_nat (size s) < Int63Axioms.wB)%Z ->
  x < size s ->
  size pp = size s ->
  is_square pp ->
  is_square s ->
  entail pp s ->
  count (get_row s x) = l ->
  interp (fun u => let: (i, j) := to_ij (nat2int (size s)) u in
                   get_xy s i j)
         (pgen_form (pget_row pp x) 
                (fun i => varb (nat2int (x * (size s)) + i))
               l (size s)).
Proof.
move=> HnZ Hm Hs Hss Spp Sp He H.
have Hus : size (get_row s x) = size s.
  by have /forallP/(_ (Ordinal Hs))/eqP := Sp.
have : get_row s x \in gen_constr l (size s).
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
    by rewrite pget_row_size ?Hss.
  move=> y b Hy Hn.
  have /entailP := He.
  apply; rewrite ?Hss //.
   by move: Hy; rewrite pget_row_size ?Hss.
rewrite /= mk_orb_cons /=.
rewrite mk_andb_map // => i.
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
have F1 : (0 <= Z.of_nat (size s) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  by apply: BigNumPrelude.Zsquare_le.
have F2 : (0 <= Z.of_nat (size u) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : Z.of_nat (size s) <= _)%Z.
    by apply/inj_le/leP/ltnW.
  by apply: BigNumPrelude.Zsquare_le.
have F3 : (0 <= Z.of_nat (x * size s) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  rewrite Nat2Z.inj_mul.
  apply: Z.le_lt_trans Hm.
  apply: Zmult_le_compat_r.
    by apply/inj_le/leP/ltnW.
  by apply: Zle_0_nat.
have F4 : (0 <= Z.of_nat (x * size s) + Z.of_nat (size u) <
 Int63Axioms.wB)%Z.
  split; first by apply: Z.add_nonneg_nonneg; apply: Zle_0_nat.
  rewrite Nat2Z.inj_mul.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : ((Z.of_nat x + 1) * Z.of_nat (size s)  <= _)%Z).
    rewrite Z.mul_add_distr_r Z.mul_1_l.
    apply: Zplus_le_compat_l.
    by apply/inj_le/leP/ltnW.
  apply: Zmult_le_compat_r; last by apply: Zle_0_nat.
  have-> : (Z.of_nat x + 1 = Z.of_nat x.+1)%Z.
    by rewrite Nat2Z.inj_succ Z.add_1_r.
  by apply/inj_le/leP.
case: {Ha Hv Hl}a.
  rewrite Int63Axioms.div_spec /nat2int.
  rewrite Int63Axioms.add_spec.
  rewrite !Int63Properties.of_Z_spec !add0n.
  rewrite !Zmod_small //.
  rewrite Int63Axioms.mod_spec.
  set u1 := Z.modulo; rewrite -{1}/u1.
  rewrite Int63Axioms.add_spec.
  rewrite !Int63Properties.of_Z_spec.
  rewrite !Zmod_small // {}/u1.
  rewrite !Nat2Z.inj_mul Z.div_add_l; last first.
    by case: (s) HnZ.
  rewrite Z.div_small; last first.
    split; first by apply: Zle_0_nat.
    by apply/inj_lt/ltP.
  rewrite Z.add_0_r Nat2Z.id.
  rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
    by rewrite Nat2Z.id => ->.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Int63Axioms.div_spec /nat2int.
rewrite Int63Axioms.add_spec.
rewrite !Int63Properties.of_Z_spec !add0n.
rewrite !Zmod_small //.
rewrite Int63Axioms.mod_spec.
set u1 := Z.modulo; rewrite -{1}/u1.
rewrite Int63Axioms.add_spec.
rewrite !Int63Properties.of_Z_spec.
rewrite !Zmod_small // {}/u1.
rewrite !Nat2Z.inj_mul Z.div_add_l; last first.
  by case: (s) HnZ.
rewrite Z.div_small; last first.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Z.add_0_r Nat2Z.id.
rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
  by rewrite Nat2Z.id => ->.
split; first by apply: Zle_0_nat.
by apply/inj_lt/ltP.
Qed.

Lemma interp_pgen_form_col (s : sol) pp y l :
  s != [::] ->
  (Z.of_nat (size s) * Z.of_nat (size s) < Int63Axioms.wB)%Z ->
  y < size s ->
  size pp = size s ->
  is_square pp ->
  is_square s ->
  entail pp s ->
  count (get_col s y) = l ->
  interp (fun u => let: (i, j) := to_ij (nat2int (size s)) u in
                   get_xy s i j)
         (pgen_form (pget_col pp y) 
                (fun i => varb (i * nat2int (size s) + nat2int y))
               l (size s)).
Proof.
move=> HnZ Hm Hs Hss Spp Sp He H.
have Hus : size (get_col s y) = size s.
  by rewrite size_map.
have : get_col s y \in gen_constr l (size s).
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
    by rewrite size_map ?Hss.
  move=> x b Hx Hn.
  rewrite -get_row_col.
  have /entailP := He.
  apply; rewrite ?Hss //.
    by move: Hx; rewrite size_map ?Hss.
  by move: Hn; rewrite -pget_row_col.
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
have F1 : (0 <= Z.of_nat (size s) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  by apply: BigNumPrelude.Zsquare_le.
have F2 : (0 <= Z.of_nat y < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  have [_ F2] := F1.
  apply: Z.le_lt_trans F2.
  by apply/inj_le/leP/ltnW.
have F3 : (0 <= Z.of_nat (size u) < Int63Axioms.wB)%Z.
  split; first by apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : Z.of_nat (size s) <= _)%Z.
    by apply/inj_le/leP/ltnW.
  by apply: BigNumPrelude.Zsquare_le.
have F4 : (0 <= Z.of_nat (size u) * Z.of_nat (size s) < Int63Axioms.wB)%Z.
  split.
    by apply: Z.mul_nonneg_nonneg; apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Zmult_le_compat_r.
    by apply/inj_le/leP/ltnW.
  by apply: Zle_0_nat.
have F6 : (0 <= Z.of_nat (size u) * Z.of_nat (size s) +
 Z.of_nat y < Int63Axioms.wB)%Z.
  split.
    apply: Z.add_nonneg_nonneg; try apply: Zle_0_nat.
    by apply: Z.mul_nonneg_nonneg; apply: Zle_0_nat.
  apply: Z.le_lt_trans Hm.
  apply: Z.le_trans (_ : ((Z.of_nat (size u) + 1) * Z.of_nat (size s)  <= _)%Z).
    rewrite Z.mul_add_distr_r Z.mul_1_l.
    apply: Zplus_le_compat_l.
    by apply/inj_le/leP/ltnW.
  apply: Zmult_le_compat_r; last by apply: Zle_0_nat.
  have-> : (Z.of_nat (size u) + 1 = Z.of_nat (size u).+1)%Z.
    by rewrite Nat2Z.inj_succ Z.add_1_r.
  by apply/inj_le/leP.
case: {Ha Hv Hl}a.
  rewrite add0n Int63Axioms.div_spec /nat2int.
  rewrite Int63Axioms.add_spec /=.
  rewrite Int63Axioms.mul_spec /=.
  rewrite !Int63Properties.of_Z_spec /=.
  rewrite !Zmod_small //.
  rewrite Int63Axioms.mod_spec.
  set u1 := Z.modulo; rewrite -{1}/u1.
  rewrite Int63Axioms.add_spec.
  rewrite Int63Axioms.mul_spec /=.
  rewrite !Int63Properties.of_Z_spec.
  rewrite !Zmod_small // {}/u1.
  rewrite  Z.div_add_l; last first.
    by case: (s) HnZ.
  rewrite Z.div_small; last first.
    split; first by apply: Zle_0_nat.
    by apply/inj_lt/ltP.
  rewrite Z.add_0_r Nat2Z.id.
  rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
    by rewrite Nat2Z.id => ->.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Int63Axioms.div_spec /nat2int.
rewrite Int63Axioms.add_spec.
rewrite Int63Axioms.mul_spec /=.
rewrite !Int63Properties.of_Z_spec !add0n.
rewrite !Zmod_small //.
rewrite Int63Axioms.mod_spec.
set u1 := Z.modulo; rewrite -{1}/u1.
rewrite Int63Axioms.add_spec.
rewrite Int63Axioms.mul_spec /=.
rewrite !Int63Properties.of_Z_spec.
rewrite !Zmod_small // {}/u1.
rewrite Z.div_add_l; last first.
  by case: (s) HnZ.
rewrite Z.div_small; last first.
  split; first by apply: Zle_0_nat.
  by apply/inj_lt/ltP.
rewrite Z.add_0_r Nat2Z.id.
rewrite Z.add_comm Z_mod_plus_full Z.mod_small //.
  by rewrite Nat2Z.id => ->.
split; first by apply: Zle_0_nat.
by apply/inj_lt/ltP.
Qed.


(*****************************************************************************)
(*                                                                           *)
(*                                 The problem                               *)
(*                                                                           *)
(*****************************************************************************)


(*
Definition psize := 2. 

Definition columns := [::[::1]; [::1]]. 
Definition lines := [::[::1]; [::1]].

Compute [seq (length (gen_constr i psize)) | i <- lines].

Definition known_black :=  [::([::0], 0)].
*)


Definition psize := 25. 

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

Compute [seq (length (gen_constr i 25)) | i <- columns].

Definition verify_col s :=
  all (fun i => count (get_col s i) == nth [::] columns i) (iota 0 psize).

Lemma verify_colP s : 
  reflect (forall i : 'I_psize, count (get_col s i) = nth [::] columns i)
          (verify_col s).
Proof.
apply: (iffP allP) => [H i| H x].
  suff /(H _)/eqP : (i : nat) \in iota 0 psize by [].
  by rewrite -val_enum_ord map_f // mem_enum.
rewrite -val_enum_ord => /mapP /= [y Hy ->].
by rewrite H.
Qed.

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

Compute [seq (length (gen_constr i 25)) | i <- lines].

Definition verify_row s :=
  all (fun i => count (get_row s i) == nth [::] lines i) (iota 0 psize).

Lemma verify_rowP s : 
  reflect (forall i : 'I_psize, count (get_row s i) = nth [::] lines i)
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

Lemma valid_count_lines : all (valid_count psize) lines.
Proof. by compute. Qed.

Lemma valid_count_columns : all (valid_count psize) columns.
Proof. by compute. Qed.

Definition known_black := 
  [::([::3;4;12;13;21], 3);
   ([::6;7;10;14;15;18], 8);
   ([::6;11;16;20], 16);
   ([::3;4;9;10;15;20;21],21)].

Definition verify_known_black s :=
  all (fun y => 
          all (fun x => ~~ get_xy s x y.2) y.1) known_black.


Lemma verify_known_blackP s : 
  reflect (forall (x y : nat) (l : seq nat), 
            x \in l -> (l, y) \in known_black ->
            get_xy s x y = black)
          (verify_known_black s).
Proof.
apply: (iffP allP) => [H x y l xIl lyIb| H [l y] lyIb].
  by have /allP/(_ _ xIl) := H _ lyIb; case: get_xy.
apply/allP=> x /= xIl.
by rewrite (H _ _ _ xIl lyIb).
Qed.

Definition verify_sol s :=
 [&& verify_col s,  verify_row s & verify_known_black s]. 

Lemma verify_correctP s : 
  reflect
    [/\   
        forall i : 'I_psize, count (get_row s i) = nth [::] lines i,
        forall j : 'I_psize, count (get_col s j) = nth [::] columns j &
        forall (x y : nat) (l : seq nat), 
            x \in l -> (l, y) \in known_black -> get_xy s x y = black]
    (verify_sol s).
Proof.
apply: (iffP and3P)=> [[H1 H2 H3]|[H1 H2 H3]]; split.
- by apply: verify_rowP.
- by apply: verify_colP.
- by apply: verify_known_blackP.
- by have /verify_colP := H2.
- by have /verify_rowP := H1.
by have /verify_known_blackP := H3.
Qed.

Definition init_pp : psol := nseq psize (nseq psize None).

Lemma init_pp_square : is_square init_pp.
Proof.
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

Fixpoint vupdate s (l : seq nat) j  :=
  if l is i :: l then
  vupdate (pset_xy s i j (Some black)) l j else
  s.

Lemma vupdate_square s l j : 
  is_square s -> is_square (vupdate s l j).
Proof.
elim: l s => //= a l IH s Hs.
apply: IH.
by apply: pset_xy_square.
Qed.


Fixpoint hupdate s (l : seq (seq nat * nat)) :=
  if l is (vl,j) :: l then
    hupdate (vupdate s vl j) l
  else s.

Lemma hupdate_square s l : 
  is_square s -> is_square (hupdate s l).
Proof.
elim: l s => //= [] [vl a] l IH s Hs.
by apply/IH/vupdate_square.
Qed.

Definition pp := hupdate init_pp known_black.

Lemma pp_square : is_square pp.
Proof. by apply/hupdate_square/init_pp_square. Qed.

Definition cl i pp :=
let l := nth [::] lines i in
let pl := pget_row pp i in
let v := gen_constr l psize in
[seq i <- v | pcheck pl i].

Lemma cl_correct pp p i :  
  is_square pp -> is_square p -> 
  size pp = psize -> size p = psize ->
  entail pp p -> 
  count (get_row p i) = nth [::] lines i->
  i < size pp ->
  get_row p i \in cl i pp.
Proof.
move=> Spp Sp Hspp Hsp Epp Hc Li.
apply: entail_pcheck_row => //.
  by rewrite Hspp Hsp.
apply: gen_constr_mem => //.
have Li1 : i < size p by rewrite Hsp -Hspp.
by have /forallP/(_ (Ordinal Li1))/eqP-> := Sp.
Qed.

Lemma cl_size pp i l :  
  i < size lines -> l \in cl i pp -> size l = psize.
Proof.
move=> Li; rewrite /cl mem_filter => /andP[_ H].
have Vp : valid_count psize (nth [::] lines i).
  by have /allP/(_  _ (mem_nth [::] Li)) := 
            valid_count_lines.
apply: gen_constr_size H _ => [i1|].
  by apply: valid_count_gt_0 Vp.
apply: valid_count_suml Vp.
Qed.
 
Definition lpp pp := foldi (fun n psol => 
   let v := cl n psol in
   if v is [::l] then
    (pset_row psol n [seq Some i | i <- l]) else psol) psize.-1 pp.

Lemma lpp_correct p pp : 
  is_square pp -> is_square p -> size pp = psize -> size p = psize ->
  entail pp p -> 
  (forall i, i < size pp -> count (get_row p i) = nth [::] lines i)->
  entail (lpp pp) p.
Proof.
move=> Spp Sp Hspp Hsp Ep Cp.
rewrite /lpp.
elim: {-2}(_.-1) (leqnn (psize.-1)) pp Hspp Spp Ep Cp => /=;
  last first.
set f := fun _ _ => _.
move=> n IH Ln pp Hspp Spp Ep Cp.
apply: IH => //.
- by apply: ltnW.
- case: cl => // a [|l] //.
  by rewrite size_map size_iota.
- have := cl_size pp n.+1.
   case: cl => // a [|l] //.
   have aI : a \in [::a] by rewrite inE.
   move=> /(_ _ Ln aI) Ha.
  apply: pset_row_square => // _.
  by rewrite size_map Ha Hspp.
- have F1 : n.+1 < size pp by rewrite Hspp.
  have := cl_correct pp p n.+1 Spp Sp Hspp Hsp Ep (Cp _ F1) F1.
  case: cl => // a [|l] //.
  rewrite inE => /eqP<-.
  apply/entailP=> i j b Hi Hj.
  rewrite /pget_xy.
  rewrite pset_row_correct; last by rewrite Hspp.
  case: eqP => [<-|_ U]; last first.
    have/entailP := Ep.
    apply => //.
      by move: Hi; rewrite size_map size_iota.
    by move: Hj; rewrite size_map size_iota.
  rewrite (nth_map false) // => [[<-//]|].
  rewrite get_row_size //.
    by move: Hj; rewrite size_map size_iota Hspp Hsp.
  by rewrite Hsp.
- move=> i Hi.
  apply: Cp => //.
  move: Hi; case: cl => // a [|] //.
  by rewrite size_map size_iota.
move=> L pp Hspp Spp Ep Cp.
have F1 : 0 < size pp by rewrite Hspp.
have := cl_correct pp p 0 Spp Sp Hspp Hsp Ep (Cp _ F1) F1.
case: cl => // a [|l] //.
rewrite inE => /eqP<-.
apply/entailP=> i j b Hi Hj.
rewrite /pget_xy.
rewrite pset_row_correct; last by rewrite Hspp.
case: eqP => [<-|_ U]; last first.
  have/entailP := Ep.
  apply => //.
    by move: Hi; rewrite size_map size_iota.
  by move: Hj; rewrite size_map size_iota.
rewrite (nth_map false) // => [[<-//]|].
rewrite get_row_size //.
  by move: Hj; rewrite size_map size_iota Hspp Hsp.
by rewrite Hsp.
Qed.

  
Definition pp1 := lpp pp.

Compute pp1 == pp.

Definition cp i pp :=
let l := nth [::] columns i in
let pl := pget_col pp i in
let v := gen_constr l psize in
[seq i <- v | pcheck pl i].

Lemma cp_correct pp p j :  
  is_square pp -> is_square p -> 
  size pp = psize -> size p = psize ->
  entail pp p -> 
  count (get_col p j) = nth [::] columns j ->
  j < size pp ->
  get_col p j \in cp j pp.
Proof.
move=> Spp Sp Hspp Hsp Epp Hc Lj.
apply: entail_pcheck_col => //.
  by rewrite Hspp Hsp.
apply: gen_constr_mem => //.
by rewrite size_map.
Qed.

Lemma cp_size pp j l :  
  j < size columns -> l \in cp j pp -> size l = psize.
Proof.
move=> Lj; rewrite /cp mem_filter => /andP[_ H].
have Vp : valid_count psize (nth [::] columns j).
  by have /allP/(_  _ (mem_nth [::] Lj)) := 
            valid_count_columns.
apply: gen_constr_size H _ => [i1|].
  by apply: valid_count_gt_0 Vp.
apply: valid_count_suml Vp.
Qed.


Definition cpp pp := foldi (fun n psol => 
   let v := cp n psol in
   if v is [::l] then
    (pset_col psol n [seq Some i | i <- l]) else psol) psize.-1 pp.

Lemma cpp_correct p pp : 
  is_square pp -> is_square p -> size pp = psize -> size p = psize ->
  entail pp p -> 
  (forall j, j < size pp -> count (get_col p j) = nth [::] columns j)->
  entail (cpp pp) p.
Proof.
move=> Spp Sp Hspp Hsp Ep Cp.
rewrite /cpp.
elim: {-2}(_.-1) (leqnn (psize.-1)) pp Hspp Spp Ep Cp => /=;
  last first.
set f := fun _ _ => _.
move=> n IH Ln pp Hspp Spp Ep Cp.
apply: IH => //.
- by apply: ltnW.
- case: cp => // a [|l] //.
  by rewrite size_map size_iota.
- have := cp_size pp n.+1.
  case: cp => // a [|l] //.
  have aI : a \in [::a] by rewrite inE.
  move=> /(_ _ Ln aI) Ha.
  apply: pset_col_square => //.
  by rewrite size_map Ha Hspp.
- have F1 : n.+1 < size pp by rewrite Hspp.
  have := cp_correct pp p n.+1 Spp Sp Hspp Hsp Ep (Cp _ F1) F1.
  case: cp => // a [|l] //.
  rewrite inE => /eqP<-.
  apply/entailP=> i j b Hi Hj.
  rewrite /pget_xy pget_row_col.
  rewrite pset_col_correct //; last first.
    by rewrite !size_map Hspp.
  case: eqP => [<-|_ U]; last first.
    have/entailP := Ep.
    apply => //.
    - by move: Hi; rewrite size_map size_iota.
    - by move: Hj; rewrite size_map size_iota.
    by rewrite [LHS]pget_row_col.
  rewrite (nth_map false) // => [[<-//]|].
    by rewrite [LHS]get_row_col.
  rewrite size_map.
  by move: Hi; rewrite size_map size_iota Hspp Hsp.
- move=> j Hj.
  apply: Cp => //.
  move: Hj; case: cp => // a [|] //.
  by rewrite size_map size_iota.
move=> L pp Hspp Spp Ep Cp.
have F1 : 0 < size pp by rewrite Hspp.
have := cp_correct pp p 0 Spp Sp Hspp Hsp Ep (Cp _ F1) F1.
case: cp => // a [|l] //.
rewrite inE => /eqP<-.
apply/entailP=> i j b Hi Hj.
rewrite /pget_xy pget_row_col.
rewrite pset_col_correct //; last first.
  by rewrite !size_map Hspp.
case: eqP => [<-|_ U]; last first.
  have/entailP := Ep.
  apply => //.
  - by move: Hi; rewrite size_map size_iota.
  - by move: Hj; rewrite size_map size_iota.
  by rewrite [LHS]pget_row_col.
rewrite (nth_map false) // => [[<-//]|].
  by rewrite [LHS]get_row_col.
rewrite size_map.
by move: Hi; rewrite size_map size_iota Hspp Hsp.
Qed.


Definition pp2 := cpp pp1.

Compute pp2 == pp1.

Definition pp3 := lpp pp2.

Compute pp3 == pp2.

Definition pp4 := cpp pp3.


(*
Definition psize := 4.
Definition isize := nat2int psize. 

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
*)

Definition gen_columns f :=
  andb (map 
    (fun p => let: (i, l) := p in  (gen_form (f i) l psize))
   (zip (int_iota 0 psize) columns)).


Definition gen_lines f :=
  andb (map 
    (fun p => let: (j, l) := p in (gen_form (fun i => f i j) l psize))
   (zip (int_iota 0 psize) lines)).


Definition gen_black f :=
   andb (map
    (fun p => let: (l, j) := p in 
     (andb (map (fun i => (f (nat2int i) (nat2int j))) l)))
    known_black).

Definition gen_all f := andb [::gen_black f; gen_lines f; gen_columns f].


Definition gen_sol f (sol : seq (seq bool)) :=
 andb (map
  (fun p => 
     let: (j, l) := p in
      andb (map
         (fun p1 => 
               let: (i, b) := p1 in
               (if b then (f i j) else negb (f i j)))
       (zip (int_iota 0 psize) l)))
   (zip (int_iota 0 psize) sol)).

