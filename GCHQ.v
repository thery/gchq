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
(*                         Misc THMs                                              *)
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

(* Reification of boolean formulae *)
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


(* We encode the colour as booleans *)
Definition white := true.
Definition black := false.

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

Lemma rev_nseq (T : Type) (t : T) n : rev (nseq n t) = nseq n t.
Proof.
apply: (@eq_from_nth _ t) => [|i].
  by rewrite size_rev.
rewrite size_rev => Hi.
by rewrite nth_rev // !nth_nseq !if_same.
Qed.

Lemma rbool_spec b l : rboolD b l.
Proof.
rewrite -[l]revK.
case: (lbool_spec b (rev l)) => [n|n l1].
  by rewrite rev_nseq; apply: rboolB.
rewrite - cat_nseq rev_cat rev_nseq rev_cons cat_rcons.
by apply: rboolW.
Qed.

Open Scope nat_scope.

Section G.

(* The dimension of the puzzle *)
(*
Variable d : nat.
*)

(*
Definition count (f : nat -> bool) :=
  let fix c m i n :=
    if m is m1.+1 then 
    if ~~ f i then c m1 i.+1 n.+1 else 
    if n is _.+1 then n :: c m1 i.+1 0 else c m1 i.+1 0
    else if n is _.+1 then [::n] else [::] in c d 0 0.
*)

(* counting the lengths of sequence of blacks *)
Fixpoint count_aux l n :=
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
rewrite cat_rcons  count_rcons_black_white rev_cons IH //.
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

(* Solution *)
Definition sol := seq (seq bool).

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

Definition test_m := 
   [:: [:: white; black; white; black; white; white]; 
       [:: white; white; white; white; white; white];
       [:: white; white; black; black; white; white];
       [:: white; white; black; black; white; white];
       [:: white; white; white; white; white; white];
       [:: white; white; white; white; white; white]
    ].

(* Partial Solution *)

Definition psol := seq (seq (option bool)).

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

(*
Inductive boolb := 
|  trueb 
| falseb 
| eqb (_ _ : boolb)
| andb (_ : seq boolb) 
| implb (_ : seq boolb) 
| orb (_ : seq boolb) 
| negb (_ : boolb) 
| varb (_ : int).
)
*)


Fixpoint foldi {T1 : Type} (f : nat -> T1 -> T1) i r :=
   let r1 := f i r in
   if i is i1.+1 then foldi f i1 r1
   else r1.

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

Definition nat2int n := 
  Int63Op.of_Z (Z_of_nat n).

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
Compute gen_form (fun i => varb (0 + i)) [::2] 4.


Definition to_ij d u := 
  let i := Z.to_nat (Int63Op.to_Z (Int63Native.div u d)) in
  let j := Z.to_nat (Int63Op.to_Z (Int63Native.modulo u d)) in (i, j).

Lemma iota_rcons a b :
  iota a b.+1 = rcons (iota a b) (a + b).
Proof.
rewrite /=; elim: b a => /= [a|b IH a].
  by rewrite addn0.
by rewrite IH addnS.
Qed.

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


Definition known_black := 
  [::([::3;4;12;13;21], 3);
   ([::6;7;10;14;15;18], 8);
   ([::6;11;16;20], 16);
   ([::3;4;9;10;15;20;21],21)].


(*
Definition psize := 2. 

Definition columns := [::[::1]; [::1]]. 
Definition lines := [::[::1]; [::1]].

Compute [seq (length (gen_constr i psize)) | i <- lines].

Definition known_black :=  [::([::0], 0)].
*)

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
apply: pset_xy_square.

Fixpoint hupdate s (l : seq (seq nat * nat)) :=
  if l is (vl,j) :: l then
    hupdate (vupdate s vl j) l
  else s.

Definition pp := hupdate init_pp known_black.

Compute pp.

Definition cl i pp :=
let l := nth [::] lines i in
let pl := pget_row pp i in
let v := gen_constr l psize in
[seq i | i <- v & pcheck pl i].

Definition lpp pp := foldi (fun n psol => 
   let v := cl n pp in
   if v is [::l] then
    (pset_row psol n [seq Some i | i <- l]) else psol) psize.-1 pp.

Compute  [seq length (cl i pp) | i <- iota 0 psize].

Definition pp1 := lpp pp.

Compute pp1 == pp.

Definition cp i pp :=
let l := nth [::] columns i in
let pl := pget_col pp i in
let v := gen_constr l psize in
[seq i | i <- v & pcheck pl i].

Definition cpp pp := foldi (fun n psol => 
   let v := cp n pp in
   if v is [::l] then
    (pset_col psol n [seq Some i | i <- l]) else psol) psize.-1 pp.

Definition pp2 := cpp pp1.

Compute pp2 == pp1.

Definition pp3 := lpp pp2.

Compute pp3 == pp2.

Definition pp4 := cpp pp3.

Compute  foldl addn 0 [seq length (cp i pp4) | i <- iota 0 psize].
Compute  foldl addn 0 [seq length (cl i pp4) | i <- iota 0 psize].




Compute ([seq (length (gen_constr i 25)) | i <- columns],
         [seq length (cp i) | i <- iota 0 25]).






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

