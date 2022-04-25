(** 

  bubblesort.v

  Provides a specification and (inefficient, using `bigop`) implementation for Bubble Sort.

  The specification shows the existence of a list of sorted transpositions (bubbles) that 
  can be applied to any sequence to provide a sorted one.

  Caveat: No duplicate values allowed in the sequence.

  Pierre Jouvelot, Mines Paris, PSL University
  April 2022

  Licence: CeCILL-B.

*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nat.

Lemma ltn_addr n m : n < n + m.+1.
Proof. by rewrite -addSnnS leq_addr. Qed.

Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p.
Proof. exact (@leq_trans _ _ _). Qed.

Lemma sumnK (m n p : nat) (lemp : p <= m) (lemn : m <= n) : 
  (m - p) + (n - m) = n - p.
Proof.
rewrite addnBAC //. 
congr (_ - _).
by rewrite subnKC // ?leq_sub2l // (@leq_ltn_trans i) // ?leq_subr.
Qed.

End Nat.

(** Bigops utilities that can be used on `nat`, inspired by `bigop.v`. *)

Section Bigop.

Lemma bigmaxD1_nat m n F : \max_(m <= i < n.+1 | i != n) F i = \max_(m <= i < n) F i.
Proof.
rewrite [RHS]big_nat_cond [RHS](@big_nat_widen _ _ _ m n n.+1) // [LHS]big_nat_cond.
apply: eq_bigl => i.
by rewrite andbT -[RHS]andbA andbb -andbA ltnS ltn_neqAle [X in _ && X]andbC.
Qed.

Lemma eq_bigmax_nat m n F : m < n.+1 ->
  exists ix, \max_(m <= i < n.+1) F i = F ix /\ ix <= n.
Proof.
elim: n=> [|n IH ltmn2]; first by rewrite ltnS leqn0 => /eqP ->; exists 0; rewrite big_nat1.
rewrite // (bigD1_seq n.+1) ?iota_uniq ?mem_iota //=; last first.
- rewrite ltnS in ltmn2. 
  by rewrite {1}ltmn2 subnKC ?ltnSn // (leq_trans ltmn2).
- have [] := boolP (m < n.+1) => [ltmn1|]. 
  - move: (IH ltmn1) => [ix [mx ltx]].
    - have [] := boolP (F n.+1 <= F ix) => le1.
      exists ix; rewrite bigmaxD1_nat mx; split; last by rewrite (leq_trans ltx).
      by apply/maxn_idPr.
    - rewrite -ltnNge in le1.  
      exists n.+1; rewrite bigmaxD1_nat mx; split; last by rewrite ltnSn.
      apply/maxn_idPl. 
      exact: ltnW.
  - rewrite -ltnNge ltnS => ltnm. 
    have/eqP -> : m == n.+1 by rewrite eqn_leq -ltnS ltmn2 ltnm.
    exists n.+1. 
    have -> : \max_(n.+1 <= i < n.+2 | i != n.+1) F i = 0 by rewrite bigmaxD1_nat big_geq.
    by rewrite maxn0.
Qed.

Lemma leq_bigmax F n (i0 : nat) (lei0n : i0 <= n) :
  F i0 <= \max_(0 <= i < n.+1) F i.
Proof. by rewrite (bigD1_seq i0) //= ?mem_iota ?iota_uniq ?andbT //= leq_max leqnn. Qed.

Lemma index_iota i n (lt0i : 0 < i) (lein : i <= n) :
  index i (iota 1 n) = i.-1.
Proof.
have ii : i = 1 + i.-1 by rewrite -subn1 subnKC.
have lti1n : i.-1 < n by rewrite (@leq_trans i) // ltn_predL. 
move: (@nth_iota 0 1 n i.-1 lti1n).
rewrite addnC (addn1 i.-1) prednK // => eqnthi.
by rewrite -{1}eqnthi index_uniq // ?iota_uniq // size_iota.
Qed.

Lemma in_rem i j n (lt0i : 0 < i) (lein : i <= n) (lt0j : 0 < j) (lejn : j <= n) :
  (j \in rem i (iota 1 n)) = (j != i).
Proof.
have [] := boolP (j == i) => [/eqP ->|neji //=]; first by rewrite mem_rem_uniqF //= iota_uniq.
rewrite remE mem_cat.
have [] := boolP (j < i) => [ltji|].
- rewrite in_take ?index_iota ?ltn_predRL ?(ltn_predK lt0j) ?ltji ?orTb //.
  by rewrite mem_iota lt0j addnC addn1 ltnS.
- rewrite -leqNgt leq_eqVlt => /orP [|ltij]; first by rewrite -(negbK (i == j)) eq_sym neji. 
  apply/orP; right.
  rewrite index_iota ?prednK //.
  apply/(nthP 0).
  have ltj1n : j.-1 < n by rewrite (@leq_trans j) // ltn_predL.
  exists (j - i.+1). 
  - rewrite size_drop size_iota subnS predn_sub.
    by rewrite ltn_subLR ?subnKC // -ltnS (ltn_predK ltij).
  - rewrite nth_drop nth_iota 1?addnA ?add1n ?subnKC //. 
    by rewrite subnS -subn1 addnBA ?subnKC // ?subn1 // ?(ltnW ltij) // subn_gt0.
Qed.

Lemma big_pred1_eq (i : nat) n F (ltin1 : i < n.+1) :
  \max_(0 <= j < n.+1 | j == i) F j = F i.
Proof. 
rewrite big_nat_cond (big_rem i) //=; last by rewrite mem_iota (leq0n i) subnKC.
rewrite ifT //= ?ltin1 ?eq_refl //= big_seq_cond.
apply/maxn_idPl.   
under (eq_bigl pred0) => j //=.
  case: ifP => [/eqP <-|ne0i]; 
              first by rewrite mem_iota andbC andbA eqn0Ngt -[X in X && _]andbA andNb andbF.
  rewrite andbA [X in X && _](@andb_id2r _ _ (j != i)) => [|ltjn1]. 
  - by rewrite [X in X && _]andbC -andbA andNb andbF //=. 
  - rewrite in_cons.  
    have [] := boolP (j == 0) => [/eqP ->|nej0]; first by rewrite orTb ne0i. 
    rewrite eq_sym in ne0i.
    by rewrite orFb in_rem // neq0_lt0n // ?(negbTE nej0).
by rewrite big_pred0.
Qed.

Lemma bigmax_in_take s n (lt0s : 0 < length s) (ltns : n < size s) : 
  \max_(0 <= i < n.+1) nth 0 s i \in take n.+1 s. 
Proof.
apply/(nthP 0).
move: (@eq_bigmax_nat 0 n (nth 0 s) (ltn0Sn n)) => [ix [mx lx]]. 
rewrite -ltnS in lx.
have [] := boolP (ix < size s) => [ltxs|].
- exists ix; first by rewrite size_take; case: ifP.
  by rewrite nth_take ?mx.
- rewrite -leqNgt => lesx.
  exists 0 => //; first by rewrite size_take; case: ifP.
  move: (@leq_bigmax (nth 0 s) n 0 (leq0n n)).
  have eq0: nth 0 s ix = 0 by rewrite nth_default. 
  by rewrite nth_take // mx eq0 leqn0 => /eqP.
Qed.

Lemma bigmax_in s n (lt0s : 0 < length s) (ltns : n < size s) : 
  \max_(0 <= i < n.+1) nth 0 s i \in s. 
Proof. by rewrite (@mem_take n.+1) ?bigmax_in_take. Qed.


Lemma index_bigmax_lt0 s n (lt0s : 0 < size s) (ltns : n < size s) :
  index (\max_(0 <= i < n.+1) nth 0 s i) s < n.+1.
Proof. by rewrite index_ltn ?bigmax_in_take. Qed.

Lemma index_bigmax_lt s n (lt0s : 0 < size s)(ltns : n < size s) :
  index (\max_(0 <= i < n.+1) nth 0 s i) s <= n. 
Proof. by rewrite -ltnS index_bigmax_lt0 //. Qed.

End Bigop.

Section BubbleSort.

(** The `Variable` definitions below provide an interface for permutations using indices `i`, 
    inspired in part by `perm.v`, although this one is working on `nat`. 

    Some utility lemmas are also given. *)

Implicit Types (i : nat).

Notation transposition := (nat * nat)%type.

Variable (aperm : seq nat -> transposition -> seq nat).
Variable (aperm_id : forall s n, aperm s (n, n) = s).
Variable (size_aperm : forall s t, size (aperm s t) = size s).
Variable (nth_aperm : forall s n x, 
             n < size s -> x \in s -> nth 0 (aperm s (index x s, n)) n = x).
Variable (nth_aperm_id : forall s i1 i2 i,
             i < size s -> i1 < i -> i2 < i -> 
             nth 0 (aperm s (i1, i2)) i = nth 0 s i).
Variable (perm_eq_aperm : forall s i1 i2, 
             i1 < size s -> i2 < size s -> perm_eq s (aperm s (i1, i2))).
Variable (take_perm_comm : forall s i1 i2 m,
             i1 <= i2 -> i2 < size s -> i2 < m ->
             take m (aperm s (i1, i2)) = aperm (take m s) (i1, i2)).

Lemma perm_eq_take_aperm m s i1 i2 (lti2m1s : i2 + m.+1 < size s) (le12 : i1 <= i2) : 
  perm_eq (take (i2 + m.+1) s) (take (i2 + m.+1) (aperm s (i1, i2))).
Proof.
have -> : take (i2 + m.+1) (aperm s (i1, i2)) = aperm (take (i2 + m.+1) s) (i1, i2).  
  rewrite take_perm_comm // ?nth_take //= // (@leq_ltn_trans i2) ?ltn_addr //.
  by rewrite (@ltn_trans (i2 + m.+1)) ?ltn_addr.
rewrite perm_eq_aperm ?size_take // lti2m1s ?ltn_addr //.
by rewrite (@leq_ltn_trans i2) // ltn_addr.
Qed.

Lemma max_aperm s i1 i2 (ltns : i2 < size s) (lexn : i1 <= i2) :
  \max_(0 <= i < i2.+1) nth 0 s i = \max_(0 <= i < i2.+1) nth 0 (aperm s (i1, i2)) i. 
Proof.
set s' := (aperm _ _). 
rewrite -[in LHS](cat_take_drop i2.+1 s) -[in RHS](cat_take_drop i2.+1 s').
rewrite [LHS](@big_cat_nat _ _ _ i2.+1) // [RHS](@big_cat_nat _ _ _ i2.+1) //=.
set a := (X in maxn X _ = _); set a' := (X in _ = maxn X _).
have: a = \max_(0 <= i < i2.+1) nth 0 (take i2.+1 s) i. 
  rewrite /a big_nat.
  have [] := boolP (i2.+1 < size s) => lt2s.
  - under eq_bigr => i /andP [_ lti2].
      rewrite nth_cat size_take lt2s lti2; over.
    by rewrite [RHS]big_nat.
  - have/eqP eqzn1 : size s == i2.+1 by rewrite eqn_leq ltns leqNgt lt2s.
    under eq_bigr => i /andP [_ lti2].
      rewrite nth_cat size_take eqzn1 ltnn lti2; over.
    by rewrite [RHS]big_nat. 
have: a' = \max_(0 <= i < i2.+1) nth 0 (take i2.+1 s') i. 
  rewrite /a' big_nat.
  have [] := boolP (i2.+1 < size s) => lt2s. 
  - under eq_bigr => i /andP [_ lti2].
      rewrite nth_cat size_take size_aperm lt2s lti2; over.
    by rewrite [RHS]big_nat.
  - have/eqP eqzn1 : size s == i2.+1 by rewrite eqn_leq ltns leqNgt lt2s. 
    under eq_bigr => i /andP [_ lti2].
      rewrite nth_cat size_take -eqzn1 size_aperm ltnn (@ltn_leq_trans i2.+1) // eqzn1; over.
    by rewrite [RHS]big_nat. 
have sztn1: size (take i2.+1 s) = i2.+1.
  rewrite size_take.
  have [] := boolP (i2.+1 < size s) => [//|ne2s].
  by have/eqP eqzn1 : size s == i2.+1 by rewrite eqn_leq ltns leqNgt ne2s.
have sztn1': size (take i2.+1 s') = i2.+1 by rewrite -{2}sztn1  !size_take size_aperm.  
rewrite -{1}sztn1' -{3}sztn1 => -> ->.
congr maxn; last by rewrite !big_geq.
rewrite -!(@big_nth _ _ _ _ _ _ predT id) (perm_big (take i2.+1 s')) //= /s'.
have [] := boolP (i2 + 1 < size s) => lt2s.
- by rewrite -addn1 (@perm_eq_take_aperm 0 s i1 i2).
- have/eqP <- : size s == i2.+1 by rewrite eqn_leq ltns leqNgt -(addn1 i2) lt2s.
  rewrite -{2}(@size_aperm _ (i1, i2)) !take_size perm_eq_aperm //. 
  by rewrite (@leq_ltn_trans i2). 
Qed.

Section Algorithm. 

(** A list of transpositions (to be shown later as forming a list of out-of-order `bubbles`) 
    from indices `0` to `n` (included) in `s`. *)

Fixpoint transpositions (s : seq nat) n : seq transposition :=
  match n with
  | 0 => [::]
  | n'.+1 => let max := \max_(O <= i < n.+1) nth 0 s i in 
            let t := (index max s, n) in 
            let ts := transpositions (aperm s t) n'  in
            t :: ts
  end.

(** `swap` applies the list of transpositions `ts` to `s`, returning the swapped list 
    together with a boolean stating that all these transpositions are bubbles. 

    Using `transpositions s (size s).-1` for `ts` will yield a sorted version of `s`. *)

Definition is_bubble (s : seq nat) (t : transposition) :=
  let: (i1, i2) := t in (i1 == i2) || (i1 < i2) && (nth 0 s i2 <= nth 0 s i1).

Fixpoint swap (s : seq nat) (ts : seq transposition) :=
  match ts with
  | [::] => (true, s)
  | t :: ts' => let bs' := swap (aperm s t) ts' in
             (is_bubble s t && bs'.1, bs'.2)
  end.

End Algorithm.

(* Util lemmas on `swap` and `transpositions`. *)

Lemma swap_size ts s : size (swap s ts).2 = size s. 
Proof. by elim: ts s => [//=|t ts IH s /=]; rewrite IH. Qed.

Lemma perm_eq_take_swap n : forall (s : seq nat),
    n.+1 < size s ->
    perm_eq (take n.+1 s) (take n.+1 (swap s (transpositions s n)).2).
Proof.
suff: forall (s : seq nat),
    forall m, n.+1 + m < size s ->
         perm_eq (take (n + m.+1) s) (take (n + m.+1) (swap s (transpositions s n)).2).
  move=> H s ltn1s. 
  move: (@H s 0).
  by rewrite addn1 addn0 => ->.
elim: n => [//=|n IH s m ltn2ms].
pose ix := index (\max_(0 <= i < n.+2) nth 0 s i) s.
rewrite (@perm_trans _ (take (n.+1 + m.+1) (aperm s (ix, n.+1)))) //.  
- rewrite perm_eq_take_aperm // -?addSnnS // index_bigmax_lt //(@ltn_trans (n.+2 + m)) //.
  by rewrite addSnnS ltn_addr.
- have szap : n.+1 + m.+1 < size (aperm s (ix, n.+1)). 
    by rewrite size_aperm -addSnnS.
  move: (@IH (aperm s (ix, n.+1)) m.+1 szap).
  by have -> // : n + m.+2 = n.+1 + m.+1 by rewrite addnS addSn.
Qed.

Section Bubbles.

(** Check there are only bubbles in `transpositions`. *)

Lemma bubbles_in_swap s (lt0s : 0 < size s) :
  (swap s (transpositions s (size s).-1)).1.
Proof.
suff: forall n s, 0 < size s -> n < size s -> (swap s (transpositions s n)).1. 
  by apply=> //; rewrite prednK.
clear lt0s s.
elim=> [//=|n IH s lt0s ltns /=]. 
apply/andP; split; last by rewrite IH // ?size_aperm // -?lt0n ltnW.
set mx := (\max_(_ <= i < _) _).
have [] := boolP (index mx s == n.+1) => nein1 //=.
move: (@index_bigmax_lt s n.+1 lt0s ltns); rewrite leq_eqVlt. 
set eqixn1 := (X in (X || _)).
rewrite -(negbK eqixn1) nein1 /= => -> //= {eqixn1}. 
by rewrite nth_index ?bigmax_in // leq_bigmax.
Qed.

End Bubbles.

Section Sorted.

(** Check that the `n`-prefix of a `s` swapped with `transpositions` is sorted. *)

Lemma swap_id n s j (ltnj : n < j) (ltjs : j < size s) :
  nth 0 (swap s (transpositions s n)).2 j = nth 0 s j.
Proof.
elim: n s j ltnj ltjs => [//=|n IH s j ltn1j ltjs /=].
rewrite IH // ?size_aperm //; last by rewrite (@ltn_trans n.+1 _ j).
rewrite nth_aperm_id // (@leq_ltn_trans n.+1) // index_bigmax_lt // (@ltn_trans j) //. 
exact: (@ltn_trans n.+1).
Qed.

Lemma max_swap n s (ltn1s : n.+1 < size s) :
  \max_(0 <= i < n.+2) nth 0 s i = \max_(0 <= i < n.+2) nth 0 (swap s (transpositions s n)).2 i.
Proof.
set s' := (swap _ _).2. 
rewrite -[in LHS](cat_take_drop n.+1 s) -[in RHS](cat_take_drop n.+1 s').
rewrite [LHS](@big_cat_nat _ _ _ n.+1) // [RHS](@big_cat_nat _ _ _ n.+1) //=.
set a := (X in maxn X _ = _); set c := (X in maxn _ X = _).
set a' := (X in _ = maxn X _); set c' := (X in _ = maxn _ X). 
have: a = \max_(0 <= i < n.+1) nth 0 (take n.+1 s) i. 
  rewrite /a big_nat. 
  under eq_bigr => i /andP [_ ltin1].
    rewrite nth_cat size_take ltn1s ltin1; over.
  by rewrite [RHS]big_nat.
have: a' = \max_(0 <= i < n.+1) nth 0 (take n.+1 s') i. 
  rewrite /a' big_nat. 
  under eq_bigr => i /andP [_ ltin1].
    rewrite nth_cat size_take swap_size ltn1s ltin1; over.
  by rewrite [RHS]big_nat.  
move: (size_take n.+1 s) => sztn1; rewrite ltn1s in sztn1.
move: (size_take n.+1 s') => sztn1'; rewrite !swap_size ltn1s in sztn1'.
rewrite -{1}sztn1' -{3}sztn1 => -> ->.
congr maxn. 
- rewrite -!(@big_nth _ _ _ _ _ _ predT id) (perm_big (take n.+1 s')) //=.
  exact: perm_eq_take_swap.
- rewrite /c cat_take_drop /c' [RHS]big_nat.
  under [RHS](eq_bigr (nth 0 s)) => i /andP [ltni ltni2].
    rewrite cat_take_drop swap_id // (@leq_ltn_trans n.+1) //; over.
  by rewrite [LHS]big_nat. 
Qed.

Lemma max_swaps n:
  forall s (ltns : n < size s),
    let s' := (swap s (transpositions s n)).2 in
    forall j, j <= n -> nth 0 s' j = \max_(O <= i < j.+1) nth 0 s' i.
Proof.
elim: n => [//= s lt0s j|n IH s ltn1s /= j lejn1];
           first by rewrite leqn0 => /eqP ->; rewrite big_nat1.
have lt0s : 0 < size s by rewrite (@ltn_trans n.+1).
set ix := (index _ _).
have [] := boolP (ix == n.+1) => [/eqP eqixn1|neixn1].
- rewrite eqixn1 aperm_id.
  have [] := boolP (j <= n) => lejn.
  - by rewrite IH // // ?size_aperm (@ltn_trans n.+1).
  - have/eqP -> : j == n.+1 by rewrite eqn_leq lejn1 (ltnNge n j) lejn. 
    by rewrite swap_id // -{1}eqixn1 nth_index // ?bigmax_in // max_swap. 
- set s' := (aperm _ _).
  have [] := boolP (j <= n) => lejn.
  - by rewrite (IH s') // size_aperm (@ltn_trans n.+1).
  - have/eqP -> : j == n.+1 by rewrite eqn_leq lejn1 (ltnNge n j) lejn.
    rewrite swap_id ?size_aperm //.
    rewrite nth_aperm // ?bigmax_in // -max_swap ?size_aperm //.  
    rewrite (@max_aperm _ ix) //. 
    move: (index_bigmax_lt lt0s ltn1s).
    by rewrite leq_eqVlt -(negbK (ix == n.+1)) neixn1.
Qed.

Definition up_sorted (s : seq nat) := sorted leq s.

Lemma swap_sorted s (lt0s : 0 < size s) : 
  up_sorted (swap s (transpositions s (size s).-1)).2.
Proof.
apply: (@path_sorted _ leq 0).
apply/(pathP 0) => i ltiz.
have [] := boolP (i == 0) => [/eqP -> //=|nei0].
rewrite -lt0n in nei0.  
rewrite swap_size in ltiz.
have leiz1 : i <= (size s).-1 by rewrite ?ltn_predL -ltnS prednK.
have lei1z1 : i.-1 <= (size s).-1 by rewrite (@leq_trans i) // leq_pred.
move: (nei0) => /prednK <-.
rewrite -nth_behead /behead prednK //.
rewrite !max_swaps // ?ltn_predL //. 
rewrite [X in _ <= X](@big_cat_nat _ _ _ i.-1.+1) //= ?maxnE ?leq_addr //=.
by rewrite (@leq_ltn_trans i) // ?leq_pred.
Qed.

End Sorted.

(** Specification of BubbleSort. *)

Theorem bubble_sort_spec (s : seq nat) :
  exists (ts : seq transposition),
    let: (all_bubbles, s') := swap s ts in
    all_bubbles /\ up_sorted s'.
Proof.
have [] := boolP (s == [::]) => [/eqP -> //=|]; first by exists [::].
rewrite -size_eq0 -lt0n => lt0s.
exists (transpositions s (size s).-1) => //=.  
set bs' := (swap _ _). 
rewrite (surjective_pairing bs') bubbles_in_swap //.
by split; last exact: swap_sorted. 
Qed.

End BubbleSort.

Section Instance.

(** Provide an implementation of the permutation interface. *)

Notation transposition := (nat * nat)%type.

Implicit Types (t : transposition).

Definition toggle t i := if i == t.1 then t.2 else if i == t.2 then t.1 else i.

Lemma toggle_id i1 i : toggle (i1, i1) i = i.
Proof. by rewrite /toggle /=; case: ifP => [/eqP -> //|_]; case: ifP => [/eqP -> //|_]. Qed.

Lemma toggleR i1 i2 : toggle (i1, i2) i2 = i1.
Proof. rewrite /toggle /=; case: ifP => [/eqP ->//|_]; by rewrite eq_refl. Qed.

Lemma toggleL i1 i2 : toggle (i1, i2) i1 = i2.
Proof. by rewrite /toggle eq_refl. Qed.

Lemma toggleD i1 i2 i (ne1 : (i == i1) = false) (ne2 : (i == i2) = false) : 
  toggle (i1, i2) i = i.
Proof. by rewrite /toggle /= ifF ?ifF. Qed.

Lemma toggle_size (s : seq nat) t i1 i2 i 
      (lt1s : i1 < size s) (lt2s : i2 < size s) (ltis : i < size s) :
  toggle (i1, i2) i < size s.
Proof. by rewrite /toggle; case: ifP => //; case: ifP. Qed.

Lemma toggleK i1 i2 : involutive (toggle (i1, i2)).
Proof.
rewrite /toggle /= => i.
case: ifP.
- by case: ifP => [/eqP -> // /eqP -> //|]; last by case: ifP => [/eqP //|_ -> //].
- case: ifP => [/eqP ->|]; first by rewrite eq_refl.
  by case: ifP => [|-> //]; first by rewrite eq_refl.
Qed.

Definition toggle_iota n i1 i2 := [seq toggle (i1, i2) i | i <- iota 0 n].

Lemma toggleC n i1 i2 : toggle_iota n i2 i1 = toggle_iota n i1 i2.
Proof.
rewrite /toggle_iota.
apply: (@eq_from_nth _ 0) => [|i ltin]; first by rewrite !size_map.
rewrite size_map size_iota in ltin.
rewrite !(@nth_map _ 0) ?size_iota ?nth_iota ?add0n /toggle //=.
by case: ifP => [/eqP ->|ne2]; first by case: ifP => [/eqP -> //|].
Qed.

Lemma perm_catAC_iota n i1 i2  (l1n : i1 < n) (l2n : i2 < n) (lt12 : i1 < i2) :
  let s := toggle_iota n i1 i2 in
  let s1 := take i1 s in 
  let s2 := [:: nth 0 s i1] in
  let s3 := take (i2 - i1 -1) (drop i1.+1 s) in
  let s4 := [:: nth 0 s i2] in
  let s5 := drop i2.+1 s in
  toggle_iota n i1 i2 = (s1 ++ s2) ++ ((s3 ++ s4) ++ s5).
Proof.
have l21n: i2 - i1 - 1 < n - i1.+1. 
  by rewrite [X in _ < X]subnS -subn1 !ltn_sub2r ?ltn_subRL // addn1 (@ltn_leq_trans i2.+1).
apply: (@eq_from_nth _ 0) => [|i lis]. 
- rewrite !size_cat !size_take !size_drop /= !size_map !size_iota l1n ifT //.
  rewrite subnK ?subn_gt0 //. 
  by rewrite addnC ?(@addnC (i2 - i1)) -addnA addn1 addnS subnK ?(@ltnW i1) // subnK.
- rewrite !nth_cat !size_cat /= !size_take !size_drop !size_map !size_iota !l1n !l21n.
  have [] := boolP (i < i1) => lt1; first by rewrite ifT ?nth_take // (@ltn_trans i1) ?ltn_addr.
  rewrite -ltnNge ltnS in lt1.
  have [] := boolP (i == i1) => [/eqP ->|ne1]; first by rewrite subnn /= ifT // ltn_addr. 
  rewrite leq_eqVlt -(negbK (i1 == i)) eq_sym ne1 /= in lt1.
  have [] := boolP (i < i2) => [lt2|].
  - have lt112: i1 + 1 < i2 by rewrite (@leq_ltn_trans i) // addn1.   
    have li12 : i - i1.+1 < i2 - i1 - 1 by rewrite subnS -subn1 ?ltn_sub2r // ?ltn_subRL. 
    have mx //: maxn i1.+1 i = i by apply/maxn_idPr. 
    rewrite ifF ?ifT ?nth_take ?nth_drop addn1 -?maxnE ?mx //.
    rewrite (@ltn_trans (i2 - i1 - 1)) // ltn_addr //.
    by rewrite ltnS leqNgt lt1.
  - rewrite -leqNgt => le2i. 
    have [] := boolP (i == i2) => [/eqP ->|ne2].    
    - by rewrite ifF ?subnDA ?ltn_addr ?ltnn ?subnn //= addn1 ltnS leqNgt lt12.
    - rewrite leq_eqVlt -(negbK (i2 == i)) eq_sym ne2 /= in le2i. 
      rewrite ifF ?subnDA ?ifF ?nth_drop.
      have -> // : i2.+1 + (i - i1 - 1 - (i2 - i1 - 1) -1) = i. 
        rewrite !subn1 -subnS prednK ?subn_gt0 // addnBA.
        rewrite -addn1 -addnA -subn1 subnKC ?subn_gt0 //.
        rewrite addnBCA // ?(@ltnW i1) // -addnBA ?subnn ?addn0 //.
        by rewrite -ltnS prednK ?subn_gt0 // ltn_sub2r.
      rewrite ?subnK ltnNge ?subn1 -ltnS ?prednK ?ltn_sub2r // ?subn_gt0 //.
      rewrite -ltnNge ltnS subn_gt0 //.
      by rewrite addn1 ltnS leqNgt lt1.
Qed.

Lemma perm_id_iota n i1 i2  (l1n : i1 < n) (l2n : i2 < n) (lt12 : i1 < i2) :
  let s := toggle_iota n i1 i2 in
  let s1 := take i1 s in 
  let s2 := [:: nth 0 s i1] in
  let s3 := take (i2 - i1 -1) (drop i1.+1 s) in
  let s4 := [:: nth 0 s i2] in
  let s5 := drop i2.+1 s in
  s1 ++ (s4 ++ (s3 ++ (s2 ++ s5))) = iota 0 n.
Proof.
have l21n: i2 - i1 - 1 < n - i1.+1. 
  by rewrite [X in _ < X]subnS -subn1 !ltn_sub2r ?ltn_subRL // addn1 (@ltn_leq_trans i2.+1).
apply: (@eq_from_nth _ 0) => [|i lis].  
- rewrite !size_cat !size_take !size_drop /= !size_map !size_iota l1n ifT //.
  rewrite (subnS n) (addnC _ _.-1) addn1 prednK ?subn_gt0 // subn1 (addnA 1).
  by rewrite (addnC 1) addn1 prednK ?subn_gt0 // addnC (@sumnK i2) ?subnK // ltnW.
-  rewrite !nth_cat /= !size_take !size_drop !size_map !size_iota !l1n !l21n.
   rewrite !size_cat !size_take !size_drop !size_map !size_iota /= l1n in lis.
   have [] := boolP (i < i1) => [lt1|].
   - rewrite nth_take ?(@nth_map _ 0) ?nth_iota ?size_iota // 1?(@ltn_trans i1) //. 
     by rewrite add0n toggleD // ?ltn_eqF // (@ltn_trans i1).
   - rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP eq1i|lt1i].
     - by rewrite eq1i ifT subnn ?(@nth_map _ 0) ?size_iota ?nth_iota ?add0n -?eq1i ?toggleR.
     - rewrite ltnS leqn0 subn_eq0 leqNgt lt1i /=.
       have [] := boolP (i < i2) => [lti2|].
       - have eqi1 : i1.+1 + (i - i1 - 1) = i by rewrite -subnDA addn1 subnKC.
         have ltin : i < n by rewrite (@ltn_trans i2).
         have lt112 : 1 < i2 - i1 by rewrite ltn_subRL (@leq_ltn_trans i) // addn1.
         rewrite ifT ?ltn_sub2r // ?nth_take ?nth_drop ?ltn_addr.
         rewrite (@nth_map _ 0) ?size_iota ?nth_iota ?add0n ?ltn_addr ?eqi1 //. 
         rewrite toggleD // ?(@gtn_eqF i1) // ltn_eqF //. 
         by rewrite !ltn_sub2r.
       - rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP eqi2|lt2i].
         - rewrite -!subnDA addn1. 
           rewrite ifF ?subnKC eqi2 ?subnn /= ?(@nth_map _ 0) ?nth_iota ?add0n ?size_iota //. 
           rewrite toggleL //.
           rewrite (@leq_ltn_trans i2) // eqi2 leqnn //. 
           by rewrite ltnn. 
         - have eqi2 : i2.+1 + (i - i1.+1 - (i2 - i1.+1 + 1)) = i. 
             by rewrite -subnDA addnBAC // addn1 subnKC ?subnKC // (@ltn_trans i2). 
           have ltin : i < n. 
             move: lis.
             rewrite -(@subnDA _ i2) addn1 ltn_sub2r //.
             rewrite (@addnC _ (n - i2.+1)) addn1 subnSK ?subnS // ?(@addnC _ (n - i2)).
             rewrite -subnSK ?subnSK -?subnS ?(@addnC (n - i2)) //. 
             rewrite (@sumnK i2) // ?(@ltnW i2) //.
             rewrite (@addnC 1) addn1 subnSK // subnKC // ltnW //.
             by rewrite (@leq_ltn_trans i2).
           rewrite ifF ?ifF -!(@subnDA _ _ 1) addn1. 
           rewrite nth_drop // ?(@nth_map _ 0) ?size_iota // ?nth_iota // ?add0n // ?eqi2 //. 
           rewrite toggleD // gtn_eqF //.
           by rewrite subnBA // subnK // ltnS leqNgt subn_gt0 lt2i.
           move: (lt2i). apply: contra_ltnF. rewrite ltnNge.
           by rewrite leq_sub2r // ltnW.
Qed.

Lemma perm_no_toggle n i (lin : i < n) : perm_eq (toggle_iota n i i) (iota 0 n).  
Proof.
have -> : toggle_iota n i i = iota 0 n.
  rewrite /toggle_iota.
  apply: (@eq_from_nth _ 0) => [|j ltjs]; first by rewrite size_map.
  rewrite size_map in ltjs.
  by rewrite (@nth_map _ 0) ?toggle_id.
exact: perm_refl.
Qed.

Lemma perm_toggle n i1 i2 (l1n : i1 < n) (l2n : i2 < n) :
  perm_eq (toggle_iota n i1 i2) (iota 0 n).  
Proof.
rewrite /toggle_iota. 
have [] := boolP (i1 == i2) => [/eqP -> |ne12]; first by exact: perm_no_toggle.
wlog: i1 i2 l1n l2n ne12 / i1 < i2 => [H|lt12].
- move: (ne12).
  rewrite neq_ltn => /orP [lt12|lt21]; first by rewrite H.
  rewrite eq_sym in ne12.
  move: (toggleC n i1 i2) (H i2 i1 l2n l1n ne12 lt21).  
  by rewrite /toggle_iota => ->.
- set s := (X in perm_eq X) => {ne12}.   
  move: (perm_catAC_iota l1n l2n lt12) => /=.
  rewrite /s /toggle_iota => ->.
  set s1 := take i1 s; set s2 := [:: nth 0 s i1];
  set s3 := take (i2 - i1 -1) (drop i1.+1 s).
  set s4 := [:: nth 0 s i2]; set s5 := drop i2.+1 s. 
  rewrite perm_catACA (@perm_trans _ ((s1 ++ s4 ++ s3) ++ s2 ++ s5)) //;
        first by rewrite perm_cat2r (@perm_catl _ s1 _ (s4 ++ s3)) // perm_catC perm_refl.
  by rewrite -catA (perm_id_iota l1n l2n lt12) perm_refl.
Qed.

Definition aperm s t := [seq nth 0 s (toggle t i) | i <- iota 0 (size s)].

Lemma size_aperm s t : size (aperm s t) = size s.
Proof. by rewrite /aperm size_map size_iota. Qed.

Lemma aperm_id s n : aperm s (n, n) = s. 
Proof.
apply: (@eq_from_nth _ 0) => [|i ltis /=]; first by rewrite size_aperm.
rewrite size_aperm in ltis. 
by rewrite (nth_map 0) ?size_iota // nth_iota //= add0n  toggle_id.
Qed.

Lemma nth_aperm s i x (ltns : i < size s) (xins : x \in s) :
  nth 0 (aperm s (index x s, i)) i = x.
Proof. 
rewrite (nth_map 0) // /toggle /= ?size_iota ?nth_iota // add0n.
case: ifP => [/eqP -> |]; first by rewrite nth_index.
by rewrite ifT // nth_index.
Qed.

Lemma nth_aperm_id s i1 i2 i (ltjs : i < size s) (lt1j : i1 < i) (lt2j : i2 < i) : 
  nth 0 (aperm s (i1, i2)) i = nth 0 s i.
Proof.                                                                     
by rewrite /aperm (nth_map 0) // /toggle /= ?size_iota // nth_iota // add0n ifF ?gtn_eqF.
Qed.

Lemma perm_eq_aperm s i1 i2 (lt1s : i1 < size s) (lt2s : i2 < length s) :
  perm_eq s (aperm s (i1, i2)).
Proof.
apply/(perm_iotaP 0).
exists (map (toggle (i1, i2)) (iota 0 (size s))).
- by rewrite size_aperm perm_toggle.
- apply: (@eq_from_nth _ 0) => [|i ltis]; first by rewrite !size_map size_iota.
  rewrite !(@nth_map _ 0) ?size_iota // ?nth_iota // ?add0n ?toggleK // ?toggle_size //.
  by rewrite size_map size_iota.
Qed.

Lemma take_perm_comm s i1 i2 m (le12 : i1 <= i2) (lt2s : i2 < size s) (lt2m : i2 < m):
  take m (aperm s (i1, i2)) = aperm (take m s) (i1, i2).
Proof. 
rewrite -map_take /aperm take_iota size_take.
apply: (@eq_from_nth _ 0) => [|i]; first by rewrite !size_map !size_iota.
rewrite size_map size_iota => ltimn.
rewrite !(@nth_map _ 0) ?size_iota ?nth_iota // ?add0n //. 
have [] := boolP (m <= size s) => [ltim|].
- rewrite nth_take // /toggle /=. 
  case: ifP => // _.
  case: ifP => // _; first by rewrite (@leq_ltn_trans i2). 
  by move: ltim => /minn_idPl => <-.
- rewrite -ltnNge => lemi.
  by rewrite take_oversize // ltnW.
Qed.

Definition bs_spec := 
  (bubble_sort_spec aperm_id 
                    size_aperm
                    nth_aperm
                    nth_aperm_id
                    perm_eq_aperm
                    take_perm_comm).
Check bs_spec.
Print Assumptions bs_spec.
