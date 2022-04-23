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
Proof. 
by rewrite (bigD1_seq i0) //= ?mem_iota ?iota_uniq ?andbT //= leq_max; apply/orP; left.
Qed.

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
  rewrite orFb in_rem // neq0_lt0n // ?(negbTE nej0) //.
  by rewrite big_pred0.
Qed.

Lemma bigmax_in s n (lt0s : 0 < length s) : \max_(0 <= i < n.+1) nth 0 s i \in s. 
Proof.
apply/(nthP 0).
move: (@eq_bigmax_nat 0 n (nth 0 s) (ltn0Sn n)) => [ix [mx lx]].
have [] := boolP (ix < size s) => [ltxs|]; first by exists ix.
rewrite -leqNgt => lesx.
exists 0 => //.
move: (@leq_bigmax (nth 0 s) n 0 (leq0n n)).
have eq0: nth 0 s ix = 0 by rewrite nth_default. 
by rewrite mx eq0 leqn0 => /eqP ->.
Qed.

Lemma index_bigmax_lt0 s n (us : uniq s) (lt0s : 0 < length s) :
  index (\max_(0 <= i < n.+1) nth 0 s i) s <= n.
Proof.
set m := (\max_(_ <= _ < _) _).
move: (@eq_bigmax_nat 0 n (nth 0 s) (ltn0Sn n)) => [ix [mx lx]].
have [] := boolP (n < size s) => [ltns|].
- have : m = nth 0 s (index m s) by rewrite nth_index // bigmax_in.
  rewrite /m mx => /eqP. 
  rewrite nth_uniq // => [/eqP <- //||]; first by rewrite (@leq_ltn_trans n).
  rewrite index_mem.
  apply/(nthP 0).
  by exists ix => //; rewrite (@leq_ltn_trans n).
- rewrite -leqNgt => lesn. 
  have trim: \max_(0 <= i < n.+1) nth 0 s i = \max_(0 <= i < size s) nth 0 s i.
    rewrite (@big_cat_nat _ _ _ (size s)) //=; last by rewrite (@leq_trans n).
    have -> : \max_(size s <= i < n.+1) nth 0 s i = 0. 
      rewrite big_nat.
      under (eq_bigr (fun i => 0)) => i /andP [lesi _]. by rewrite nth_default.
      by elim/big_ind: _ => [|x y /= -> -> |].
    by rewrite maxn0. 
  move: (bigmax_in n lt0s) lesn.
  rewrite -index_mem /m trim => /ltnW.
  exact: leq_trans.
Qed.

Lemma index_bigmax_lt s n (us : uniq s) (ltns : n < size s) :
  index (\max_(0 <= i < n.+1) nth 0 s i) s <= n. 
Proof. by rewrite index_bigmax_lt0 // (@leq_ltn_trans n). Qed.

End Bigop.

Section BubbleSort.

(** The `Variable` definitions below provide an interface for permutations using indices `i`, 
    inspired in part by `perm.v`, although this one is working on `nat`. 

    Some utility lemmas are also given. *)

Implicit Types (i : nat).

Notation transposition := (nat * nat)%type.

Definition iperm s (t : transposition) := (nth 0 s t.1, nth 0 s t.2).

Variable (aperm : seq nat -> transposition -> seq nat).
Variable (aperm_id : forall s n, aperm s (iperm s (n, n)) = s).
Variable (size_aperm : forall s p, size (aperm s p) = size s).
Variable (uniq_aperm : forall s p, uniq s -> uniq (aperm s p)).
Variable (nth_aperm : forall s n x, 
             n < size s -> x \in s -> nth 0 (aperm s (iperm s (index x s, n))) n = x).
Variable (nth_aperm_id : forall s i1 i2 i,
             uniq s -> i < size s -> 
             i1 < i -> i2 < i -> nth 0 (aperm s (iperm s (i1, i2))) i = nth 0 s i).
Variable (perm_eq_aperm : forall s i1 i2, 
             uniq s ->  i1 < size s -> i2 < size s -> 
             perm_eq s (aperm s (iperm s (i1, i2)))).
Variable (take_perm_comm : forall s i1 i2 m,
             i1 <= i2 -> i2 < size s -> i2 < m ->
             take m (aperm s (iperm s (i1, i2))) = aperm (take m s) (iperm s (i1, i2))).

Lemma perm_eq_take_aperm m s i1 i2 
      (us : uniq s) (lti2m1s : i2 + m.+1 < size s) (le12 : i1 <= i2) : 
  perm_eq (take (i2 + m.+1) s) 
          (take (i2 + m.+1) (aperm s (iperm s (i1, i2)))).
Proof.
have -> : take (i2 + m.+1) (aperm s (iperm s (i1, i2))) = 
           aperm (take (i2 + m.+1) s) (iperm (take (i2 + m.+1) s) (i1, i2)). 
  rewrite take_perm_comm // /iperm ?nth_take //= // (@leq_ltn_trans i2) ?ltn_addr //.
  by rewrite (@ltn_trans (i2 + m.+1)) ?ltn_addr.
rewrite perm_eq_aperm ?take_uniq ?size_take // lti2m1s ?ltn_addr //.
by rewrite (@leq_ltn_trans i2) // ltn_addr.
Qed.

Lemma max_aperm s i1 i2 (us : uniq s) (ltns : i2 < size s) (lexn : i1 <= i2) :
  \max_(0 <= i < i2.+1) nth 0 s i = \max_(0 <= i < i2.+1) nth 0 (aperm s (iperm s (i1, i2))) i. 
Proof.
set s' := aperm s (iperm s (i1, i2)). 
rewrite -[in LHS](cat_take_drop i2.+1 s) -[in RHS](cat_take_drop i2.+1 s').
rewrite [LHS](@big_cat_nat _ _ _ i2.+1) // [RHS](@big_cat_nat _ _ _ i2.+1) //=.
set a := (X in maxn X _ = _); set c := (X in maxn _ X = _).
set a' := (X in _ = maxn X _); set c' := (X in _ = maxn _ X).  
have: a = \max_(0 <= i < i2.+1) nth 0 (take i2.+1 s) i. 
  rewrite /a big_nat. 
  have [] := boolP (i2.+1 < size s) => lt2s.
  - under eq_bigr => i /andP [_ lti2].
    rewrite nth_cat size_take lt2s lti2. over.
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
have s'ztn1: size (take i2.+1 s') = i2.+1.
  by rewrite -{2}sztn1  !size_take size_aperm.
rewrite -{1}s'ztn1 -{3}sztn1 => eqa' eqa.
have -> : a = a'.
  rewrite eqa eqa' -!(@big_nth _ _ _ _ _ _ predT id) (perm_big (take i2.+1 s')) //= /s'.
  have [] := boolP (i2 + 1 < size s) => lt2s.
  - by rewrite -addn1 (@perm_eq_take_aperm 0 s i1 i2 us).
  - have/eqP <- : size s == i2.+1 by rewrite eqn_leq ltns leqNgt -(addn1 i2) lt2s.
    rewrite -{2}(@size_aperm _ (iperm s (i1, i2))) !take_size perm_eq_aperm //. 
    by rewrite (@leq_ltn_trans i2). 
by rewrite /c /c' !big_geq.
Qed.

Section Algorithm. 

(** A list of transpositions (to be shown later as forming a list of out-of-order `bubbles`) 
    from indices `0` to `n` (included) in `s`. *)

Fixpoint transpositions (s : seq nat) n : seq transposition :=
  match n with
  | 0 => [::]
  | n'.+1 => let max := \max_(O <= i < n.+1) nth 0 s i in 
            let t := (index max s, n) in 
            let ts := transpositions (aperm s (iperm s t)) n'  in
            t :: ts
  end.

(** `swap` applies a list of transpositions to `s`, returning the swapped list together with 
    a boolean stating that all these transpositions are bubbles. 

    Applying the list `transpositions s (size s).-1` will yield a sorted version of `s`. *)

Definition is_bubble (s : seq nat) (t : transposition) :=
  let: (i1, i2) := t in (i1 == i2) || (i1 < i2) && (nth 0 s i2 < nth 0 s i1).

Fixpoint swap (s : seq nat) (ts : seq transposition) :=
  match ts with
  | [::] => (true, s)
  | t :: ts' => let bs' := swap (aperm s (iperm s t)) ts' in
             (is_bubble s t && bs'.1, bs'.2)
  end.

End Algorithm.

Lemma swap_size ts s : size (swap s ts).2 = size s. 
Proof. by elim: ts s => [//=|t ts IH s /=]; rewrite IH. Qed.

Section Bubbles.

(** Check there are only bubbles in `transpositions`. *)

Lemma bubbles_in_swap s (us : uniq s) (lt0s : 0 < size s) :
  (swap s (transpositions s (size s).-1)).1.
Proof.
suff: forall n s, 0 < size s -> uniq s -> n < size s -> (swap s (transpositions s n)).1. 
  by apply=> //; rewrite prednK.
clear lt0s s us.
elim=> [//=|n IH s lt0s us ltns /=].
apply/andP; split; last by rewrite IH // ?uniq_aperm // ?size_aperm // -?lt0n ltnW.
set m := \max_(0 <= i < n.+2) nth 0 s i.
have [] := boolP (index m s == n.+1) => nein1 //=.
move: (@index_bigmax_lt s n.+1 us ltns); rewrite leq_eqVlt. 
set eqixn1 := (X in (X || _)).
rewrite -(negbK eqixn1) nein1 /= => -> //= {eqixn1}.
rewrite nth_index ?bigmax_in //.
move: (@leq_bigmax (nth 0 s) n.+1 n.+1 (ltnSn n)).
rewrite leq_eqVlt => /orP [|//]. 
have -> //: (nth 0 s n.+1 == \max_(0 <= i < n.+2) nth 0 s i) = false.
  move: (nein1). 
  apply: contraNF => /eqP.
  rewrite -[X in _ = X](nth_index 0 (@bigmax_in s n.+1 lt0s)) => /eqP.
  rewrite nth_uniq // => [/eqP -> //|].
  by rewrite (@leq_ltn_trans n.+1) // index_bigmax_lt.
Qed.

End Bubbles.

Section Sorted.

(** Check that the `n`-prefix of swapped `s` with `transpositions` is sorted. *)

Lemma swap_id n s j :
  uniq s ->  n < j -> j < size s -> nth 0 (swap s (transpositions s n)).2 j = nth 0 s j.
Proof.
elim: n s j=> [//=|n IH s j us ltn1j ltjs /=].
rewrite IH ?uniq_aperm//; last by rewrite size_aperm. 
rewrite nth_aperm_id // (@leq_ltn_trans n.+1) // index_bigmax_lt // (@ltn_trans j) //. 
exact: (@ltn_trans n.+1).
Qed.

Lemma perm_eq_take_swap n : forall (s : seq nat),
    uniq s -> n.+1 < size s ->
    perm_eq (take n.+1 s) (take n.+1 (swap s (transpositions s n)).2).
Proof.
suff: forall (s : seq nat),
    uniq s ->
    forall m, n.+1 + m < size s ->
         perm_eq (take (n + m.+1) s) (take (n + m.+1) (swap s (transpositions s n)).2).
  move=> H s us ltn1s. 
  move: (@H s us 0).
  by rewrite addn1 addn0 => ->.
elim: n => [//=|n IH s us m ltn2ms].
set ix := index (\max_(0 <= i < n.+2) nth 0 s i) s.
rewrite (@perm_trans _ (take (n.+1 + m.+1) (aperm s (iperm s (ix, n.+1))))) //.  
- rewrite perm_eq_take_aperm // -?addSnnS // index_bigmax_lt //.
  rewrite addSnnS in ltn2ms.
  by rewrite (@ltn_trans (n.+1 + m.+1)) // ltn_addr.
- have szap : n.+1 + m.+1 < size (aperm s (iperm s (ix, n.+1))). 
    by rewrite size_aperm -addSnnS.
  have us' : uniq (aperm s (iperm s (ix, n.+1))) by rewrite uniq_aperm.
  move: (@IH (aperm s (iperm s (ix, n.+1))) us' m.+1 szap).
  by have -> // : n + m.+2 = n.+1 + m.+1 by rewrite addnS addSn.
Qed.

Lemma max_swap n s (ltn1s : n.+1 < size s) (us : uniq s) :
  \max_(0 <= i < n.+2) nth 0 s i = \max_(0 <= i < n.+2) nth 0 (swap s (transpositions s n)).2 i.
Proof.
set s' := (swap s (transpositions s n)).2. 
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
move: (size_take n.+1 s') => s'ztn1; rewrite !swap_size ltn1s in s'ztn1.
rewrite -{1}s'ztn1 -{3}sztn1 => eqa' eqa.
have -> : a = a'.
  rewrite eqa eqa' -!(@big_nth _ _ _ _ _ _ predT id) (perm_big (take n.+1 s')) //=.
  exact: perm_eq_take_swap.
have -> : c = \max_(n.+1 <= i < n.+2) nth 0 s i by rewrite /c cat_take_drop.
have -> // : c' = \max_(n.+1 <= i < n.+2) nth 0 s i. 
  rewrite /c' big_nat.
  under (eq_bigr (nth 0 s)) => i /andP [ltni ltni2].
  rewrite cat_take_drop swap_id // (@leq_ltn_trans n.+1) //.
  by rewrite [RHS]big_nat. 
Qed.

Lemma max_swaps n:
  forall s (us : uniq s),
    n < size s ->
    let s' := (swap s (transpositions s n)).2 in
    forall j, j <= n -> nth 0 s' j = \max_(O <= i < j.+1) nth 0 s' i.
Proof.
elim: n => [//= s us lt0s j|n IH s us ltn1s /= j lejn1].
- by rewrite leqn0 => /eqP ->; rewrite big_nat1.
- have lt0s : 0 < size s by rewrite (@ltn_trans n.+1).
  set ix := index (\max_(0 <= i < n.+2) nth 0 s i) s.
  have [] := boolP (ix == n.+1) => [/eqP eqixn1|neixn1].
  - rewrite eqixn1 aperm_id.
    have [] := boolP (j <= n) => lejn.
    - by rewrite IH // ?uniq_aperm // ?size_aperm (@ltn_trans n.+1).
    - have/eqP -> : j == n.+1 by rewrite eqn_leq lejn1 (ltnNge n j) lejn. 
      by rewrite swap_id // -{1}eqixn1 nth_index // ?bigmax_in // max_swap.
  - set p := iperm s (ix, n.+1).
    set s' := aperm s p.
    have [] := boolP (j <= n) => lejn.
    - by rewrite (IH s' (uniq_aperm p us)) // size_aperm (@ltn_trans n.+1).
    - have/eqP -> : j == n.+1 by rewrite eqn_leq lejn1 (ltnNge n j) lejn.
      rewrite swap_id ?uniq_aperm ?size_aperm //.
      rewrite nth_aperm // ?bigmax_in // -max_swap ?size_aperm ?uniq_aperm //.  
      rewrite (@max_aperm _ ix) //. 
      move: (index_bigmax_lt us ltn1s).
      by rewrite leq_eqVlt -(negbK (ix == n.+1)) neixn1.
Qed.

Definition up_sorted (s : seq nat) := sorted leq s.

Lemma swap_sorted s (us : uniq s) (lt0s : 0 < size s) : 
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

(* Alternative definition.

Definition up_sorted' (s : seq nat) :=
  forall i1 i2, i2 < size s -> i1 <= i2 -> nth 0 s i1 <= nth 0 s i2.

Lemma swap_sorted' s (us : uniq s) (lt0s : 0 < size s) : 
  up_sorted' (swap s (transpositions s (size s).-1)).2.
Proof.
move=> i1 i2 lti2s lei1i2. 
have lei2s1 : i2 <= (length s).-1 by rewrite -ltnS prednK; rewrite swap_size in lti2s.
rewrite !max_swaps // ?ltn_predL //.
rewrite [X in _ <= X](@big_cat_nat _ _ _ i1.+1) //= maxnE leq_addr //.
by rewrite (leq_trans lei1i2).
Qed.

*)

End Sorted.

(** Specification of BubbleSort. *)

Lemma bubble_sort_spec (s : seq nat) (us : uniq s) :
  exists (ts : seq transposition),
    let: (all_bubbles, s') := swap s ts in
    all_bubbles /\ up_sorted s'.
Proof.
have [] := boolP (s == [::]) => [/eqP -> //=|]; first by exists [::].
rewrite -size_eq0 -lt0n => lt0s.
exists (transpositions s (size s).-1) => //=.  
set bs' := (swap _ _).
rewrite (surjective_pairing bs') bubbles_in_swap //.
split=> //.
exact: swap_sorted. 
Qed.

End BubbleSort.

(** Provide an implementation of the permutation interface. *)

Notation transposition := (nat * nat)%type.

Definition swapped (t : transposition) := 
  fun i => if i == t.1 then t.2 else if i == t.2 then t.1 else i.

Definition aperm (s : seq nat) (t : transposition) := map (swapped t) s.

Lemma size_aperm s t : size (aperm s t) = size s.
Proof. by rewrite /aperm size_map. Qed.

Lemma aperm_id (s : seq nat) n : aperm s (iperm s (n, n)) = s. 
Proof.
apply: (@eq_from_nth _ 0) => [|i ltis /=]; first by rewrite size_aperm.
rewrite (nth_map 0); last by rewrite size_aperm in ltis.
rewrite /swapped.
by case: ifP => [/eqP -> //|_]; case: ifP => [/eqP -> //|_].
Qed.

Lemma nth_aperm s n x (ltns : n < size s) (xins : x \in s) :
  nth 0 (aperm s (iperm s (index x s, n))) n = x.
Proof. 
rewrite (nth_map 0) // /swapped /iperm /=. 
case: ifP; first by rewrite nth_index // => /eqP ->.
by rewrite ifT // nth_index.
Qed.

Lemma nth_aperm_id s i1 i2 i 
  (us : uniq s) (ltjs : i < size s) (lt1j : i1 < i) (lt2j : i2 < i) : 
  nth 0 (aperm s (iperm s (i1, i2))) i = nth 0 s i.
Proof.                                                                     
have nj i': i' < size s -> i' < i -> (nth 0 s i == nth 0 s i') = false. 
  move=> lti's.
  apply: contra_ltnF.
  by rewrite nth_uniq // => /eqP ->.
by rewrite /swapped (nth_map 0) // /swapped ifF ?nj ?ifF // (@ltn_trans i).
Qed.

Lemma uniq_aperm s p (us : uniq s) : uniq (aperm s p).
Proof.
rewrite map_inj_uniq // /swapped => i1 i2. 
case: ifP => [/eqP ->|nei1p1].
- case: ifP => [/eqP -> //|nei2p1].
  case: ifP => [/eqP -> //|nei2p2 p2i2]; last by rewrite p2i2 eq_refl in nei2p2.
- case: ifP => [/eqP ->|nei1p2].
  - case: ifP => [/eqP -> -> //|nei2p1].
    case: ifP => [/eqP -> //|nei2p2 p1i2]; last by rewrite p1i2 eq_refl in nei2p1.
  - case: ifP => [/eqP -> /eqP i1p2|nei2p1]; first by rewrite i1p2 in nei1p2.
    case: ifP => [/eqP ->|//]; first by apply: contra_eq; rewrite nei1p1.
Qed.    

Lemma perm_eq_aperm s i1 i2
  (us : uniq s) (lt1s : i1 < size s) (lt2s : i2 < length s) :
  perm_eq s (aperm s (iperm s (i1, i2))).
Proof.
rewrite perm_sym.
have [] := boolP (i1 == i2) => [/eqP ->|ne12]; first by rewrite aperm_id perm_refl.
rewrite /aperm uniq_perm // ?uniq_aperm //.
have nonth j1 j2: j1 < size s -> j2 < size s -> j1 != j2 -> (nth 0 s j2 == nth 0 s j1) = false.
  move=> l1s l2s.
  apply: contra_neqF.
  by rewrite nth_uniq // => /eqP ->.
move=> j.
apply/(nthP 0)/(nthP 0); rewrite !size_map. 
move=> [ip ltjps].
have [] := boolP (ip == i1) => [/eqP ->|neip1].
- by exists i2 => //; rewrite -q (nth_map 0) // /swapped /iperm /= ifT // index_mem.
- have [] := boolP (ip == i2) => [/eqP ->|neip2].
  - by exists i1 => //; rewrite -q (nth_map 0) // /swapped /iperm /= ifF ?ifT // nonth.
  - by exists ip => //; by rewrite -q (nth_map 0) // /swapped /iperm /= ifF ?ifF ?nonth 1?eq_sym.
move=> [i ltis].
have [] := boolP (i == i1) => [/eqP ->|neip1].
- by exists i2 => //; rewrite (nth_map 0) // /swapped /iperm /= ifF ?ifT // nonth.
- have [] := boolP (i == i2) => [/eqP ->|neip2].
  - by exists i1 => //; rewrite (nth_map 0) // /swapped /iperm /= ifT.
  - by exists i => //; rewrite (nth_map 0) // /swapped /iperm /= ifF ?ifF // nonth // eq_sym.
Qed.

Lemma take_perm_comm s i1 i2 m 
      (le12 : i1 <= i2) (lt2s : i2 < size s) (lt2m : i2 < m) :
  take m (aperm s (iperm s (i1, i2))) = aperm (take m s) (iperm s (i1, i2)).
Proof. by rewrite -map_take. Qed.

Definition bs_spec := 
  (bubble_sort_spec aperm_id 
                    size_aperm
                    uniq_aperm
                    nth_aperm
                    nth_aperm_id
                    perm_eq_aperm
                    take_perm_comm).
Check bs_spec.
Print Assumptions bs_spec.
