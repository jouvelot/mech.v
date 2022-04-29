(** 

  bubblesort_not_uniq.v

  This file prodes a specification and (inefficient, using `bigop`) implementation for
  a variant of Bubble Sort.

  The specification states the existence of a list of sorted transpositions (bubbles) that 
  can be applied to any sequence to provide a sorted one (see Theorem `bubble_sort_spec`).

  Pierre Jouvelot, Mines Paris, PSL University

  April 2022

  Licence: CeCILL-B.

*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nat.

Lemma ltn_addr n m : n < n + m.+1.
Proof. by rewrite -addSnnS leq_addr. Qed.

Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p.
Proof. exact: leq_trans. Qed.

Lemma sumnK (m n p : nat) (lepm : p <= m) (lemn : m <= n) : 
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

Lemma eq_bigmax_nat m n F : m < n.+1 -> exists ix, \max_(m <= i < n.+1) F i = F ix /\ ix <= n.
Proof.
elim: n=> [|n IH ltmn2]; first by rewrite ltnS leqn0 => /eqP ->; exists 0; rewrite big_nat1.
rewrite // (bigD1_seq n.+1) ?iota_uniq ?mem_iota //=; last first.
- rewrite ltnS in ltmn2. 
  by rewrite {1}ltmn2 subnKC ?ltnSn // (leq_trans ltmn2).
- have [] := boolP (m < n.+1) => [ltmn1|]. 
  - move: (IH ltmn1) => [ix [mx ltx]].
    - have [] := boolP (F n.+1 <= F ix) => leF1.
      exists ix; rewrite bigmaxD1_nat mx; split; last by rewrite (leq_trans ltx).
      by apply/maxn_idPr.
    - rewrite -ltnNge in leF1.  
      exists n.+1; rewrite bigmaxD1_nat mx; split; last by rewrite ltnSn.
      apply/maxn_idPl. 
      exact: ltnW.
  - rewrite -ltnNge ltnS => ltnm. 
    have/eqP -> : m == n.+1 by rewrite eqn_leq -ltnS ltmn2 ltnm.
    by exists n.+1; rewrite bigmaxD1_nat big_geq.
Qed.

Lemma leq_bigmax F n (i0 : nat) (lei0n : i0 <= n) : F i0 <= \max_(0 <= i < n.+1) F i.
Proof. by rewrite (bigD1_seq i0) //= ?mem_iota ?iota_uniq ?andbT //= leq_max leqnn. Qed.

Lemma index_iota i n (lt0i : 0 < i) (lein : i <= n) : index i (iota 1 n) = i.-1.
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

Lemma big_pred1_eq (i : nat) n F (ltin1 : i < n.+1) : \max_(0 <= j < n.+1 | j == i) F j = F i.
Proof. 
rewrite big_nat_cond (big_rem i) //=; last by rewrite mem_iota (leq0n i) subnKC.
rewrite ifT //= ?ltin1 ?eq_refl //= big_seq_cond.
apply/maxn_idPl.   
under (eq_bigl pred0) => j //=.
  case: ifP => [/eqP <-|nei0]; 
              first by rewrite mem_iota andbC andbA eqn0Ngt -[X in X && _]andbA andNb andbF.
  rewrite andbA [X in X && _](@andb_id2r _ _ (j != i)) => [|ltjn1]. 
  - by rewrite [X in X && _]andbC -andbA andNb andbF //=. 
  - rewrite in_cons.  
    have [] := boolP (j == 0) => [/eqP ->|nej0]; first by rewrite orTb nei0. 
    rewrite eq_sym in nei0.
    by rewrite orFb in_rem // neq0_lt0n // ?(negbTE nej0).
by rewrite big_pred0.
Qed.

Lemma bigmax_in_take s n (lt0s : 0 < size s) (ltns : n < size s) : 
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

Lemma bigmax_in s n (lt0s : 0 < size s) (ltns : n < size s) : 
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
Variable (aperm_id : forall s i, aperm s (i, i) = s).
Variable (size_aperm : forall s t, size (aperm s t) = size s).
Variable (nth_aperm : forall s i m, 
             i < size s -> m \in s -> nth 0 (aperm s (index m s, i)) i = m).
Variable (nth_aperm_id : forall s i1 i2 i,
             i < size s -> i != i1 -> i != i2 -> 
             nth 0 (aperm s (i1, i2)) i = nth 0 s i).
Variable (perm_eq_aperm : forall s i1 i2, 
             i1 < size s -> i2 < size s -> perm_eq s (aperm s (i1, i2))).
Variable (take_perm_comm : forall s i1 i2 m,
             i1 <= i2 -> i2 < size s -> i2 < m ->
             take m (aperm s (i1, i2)) = aperm (take m s) (i1, i2)).

Lemma perm_eq_take_aperm m s i1 i2 (lt2m1s : i2 + m.+1 < size s) (le12 : i1 <= i2) : 
  perm_eq (take (i2 + m.+1) s) (take (i2 + m.+1) (aperm s (i1, i2))).
Proof.
have -> : take (i2 + m.+1) (aperm s (i1, i2)) = aperm (take (i2 + m.+1) s) (i1, i2).  
  rewrite take_perm_comm // ?nth_take //= // (@leq_ltn_trans i2) ?ltn_addr //.
  by rewrite (@ltn_trans (i2 + m.+1)) ?ltn_addr.
rewrite perm_eq_aperm ?size_take // lt2m1s ?ltn_addr //.
by rewrite (@leq_ltn_trans i2) // ltn_addr.
Qed.

Lemma max_aperm s i1 i2 (lt2s : i2 < size s) (le12 : i1 <= i2) :
  \max_(0 <= i < i2.+1) nth 0 s i = \max_(0 <= i < i2.+1) nth 0 (aperm s (i1, i2)) i. 
Proof.
set s' := (aperm _ _). 
rewrite -[in LHS](cat_take_drop i2.+1 s) -[in RHS](cat_take_drop i2.+1 s').
rewrite [LHS](@big_cat_nat _ _ _ i2.+1) // [RHS](@big_cat_nat _ _ _ i2.+1) //=.
set a := (X in maxn X _ = _); set a' := (X in _ = maxn X _).
have: a = \max_(0 <= i < i2.+1) nth 0 (take i2.+1 s) i. 
  rewrite /a big_nat.
  have [] := boolP (i2.+1 < size s) => lt21s.
  - under eq_bigr => i /andP [_ lti2]. rewrite nth_cat size_take lt21s lti2; over.
    by rewrite [RHS]big_nat.
  - have/eqP eqzn1 : size s == i2.+1 by rewrite eqn_leq lt2s leqNgt lt21s.
    under eq_bigr => i /andP [_ lti2]. rewrite nth_cat size_take eqzn1 ltnn lti2; over.
    by rewrite [RHS]big_nat. 
have: a' = \max_(0 <= i < i2.+1) nth 0 (take i2.+1 s') i. 
  rewrite /a' big_nat.
  have [] := boolP (i2.+1 < size s) => lt21s. 
  - under eq_bigr => i /andP [_ lti2]. rewrite nth_cat size_take size_aperm lt21s lti2; over.
    by rewrite [RHS]big_nat.
  - have/eqP eqzn1 : size s == i2.+1 by rewrite eqn_leq lt2s leqNgt lt21s. 
    under eq_bigr => i /andP [_ lti2].
      rewrite nth_cat size_take -eqzn1 size_aperm ltnn (@ltn_leq_trans i2.+1) // eqzn1; over.
    by rewrite [RHS]big_nat. 
have szt2: size (take i2.+1 s) = i2.+1.
  rewrite size_take.
  have [] := boolP (i2.+1 < size s) => [//|ne2s].
  by have/eqP eqzn1 : size s == i2.+1 by rewrite eqn_leq lt2s leqNgt ne2s.
have szt2': size (take i2.+1 s') = i2.+1 by rewrite -{2}szt2  !size_take size_aperm.  
rewrite -{1}szt2' -{3}szt2 => -> ->.
congr maxn; last by rewrite !big_geq.
rewrite -!(@big_nth _ _ _ _ _ _ predT id) (perm_big (take i2.+1 s')) //= /s'.
have [] := boolP (i2 + 1 < size s) => lt21s.
- by rewrite -addn1 (@perm_eq_take_aperm 0 s i1 i2).
- have/eqP <- : size s == i2.+1 by rewrite eqn_leq lt2s leqNgt -(addn1 i2) lt21s.
  rewrite -{2}(@size_aperm _ (i1, i2)) !take_size perm_eq_aperm //. 
  by rewrite (@leq_ltn_trans i2). 
Qed.

Section Algorithm. 

(** Bubble Sort is based on transpositions (to be shown later as being out-of-order `bubbles`),
    here on a prefix of `s`, from indices `0` to `n` (included) in `s`. *)

Fixpoint transpositions (s : seq nat) n : seq transposition :=
  match n with
  | 0 => [::]
  | n'.+1 => let max := \max_(O <= i < n.+1) nth 0 s i in 
            let t := (index max s, n) in 
            let ts := transpositions (aperm s t) n'  in
            t :: ts
  end.

(** `swap` applies the list of transpositions `ts` to `s`, returning the swapped list 
    together with a boolean checking whether all these transpositions are bubbles.  *)

Definition is_bubble (s : seq nat) (t : transposition) :=
  let: (i1, i2) := t in 
  (i1 < size s) && (i2 < size s) &&
    ((i1 == i2) || (i1 < i2) && (nth 0 s i2 <= nth 0 s i1)).

Fixpoint swap (s : seq nat) (ts : seq transposition) :=
  match ts with
  | [::] => (true, s)
  | t :: ts' => let bs' := swap (aperm s t) ts' in
             (is_bubble s t && bs'.1, bs'.2)
  end.

Definition bubble_sort (s : seq nat) := (swap s (transpositions s (size s).-1)).2.

End Algorithm.

Section Bubbles.

(** Proof that there are only bubbles in the `n`-prefix of `transpositions s`. *)

Lemma perm_eq_take_swap n : forall (s : seq nat),
    n.+1 < size s -> perm_eq (take n.+1 s) (take n.+1 (swap s (transpositions s n)).2).
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

(* Side lemma, not used in the proof. *)

Lemma bubble_equiv s t :
  is_bubble s t <-> let: (i1, i2) := t in 
                  (i1 < size s) && (i2 < size s) &&
                  ((i1 <= i2) && (nth 0 s i2 <= nth 0 s i1)).
Proof.
rewrite /is_bubble (surjective_pairing t).
split=> [/andP [/andP [-> ->]] /orP [/eqP -> //|/andP [lt12 ->]]|
        /andP [/andP [-> ->]] /andP [le12 ->]].
- - by rewrite !leqnn.
  - by rewrite ltnW.
- rewrite leq_eqVlt in le12.
  by rewrite !andbT le12.
Qed.

Lemma bubbles_in_swap : forall n s (ltns : n < size s),
  (swap s (transpositions s n)).1.
Proof.
elim=> [//=|n IH s ltn1s /=]. 
apply/andP; split; last by rewrite IH // ?size_aperm // -?lt0n ltnW.
set mx := (\max_(_ <= i < _) _).
have lt0s : 0 < size s by rewrite (leq_ltn_trans (leq0n n.+1)).
have [] := boolP (index mx s == n.+1) => [/eqP eqin1 //=|nein1].
- move: (@index_bigmax_lt s n.+1 lt0s ltn1s).
  rewrite leq_eqVlt => /orP [eqixn1|ltxn1]; first by rewrite eqin1 !ltn1s. 
  by rewrite ltn1s !andbT (@ltn_trans n.+1). 
- have ltxn1: index mx s < n.+1 by rewrite (@ltn_neqAle _ n.+1) index_bigmax_lt // andbT.
  by rewrite (@ltn_trans n.+1 _ (size s)) // !ltxn1 ltn1s nth_index ?leq_bigmax ?bigmax_in.
Qed.

End Bubbles.

Section Sorted.

(** Proof that the `n`-prefix of a `s` swapped with `transpositions s n` is sorted. *)

Lemma swap_size ts s : size (swap s ts).2 = size s. 
Proof. by elim: ts s => [//=|t ts IH s /=]; rewrite IH. Qed.

Lemma swap_id : forall n s i (ltni : n < i) (ltis : i < size s),
  nth 0 (swap s (transpositions s n)).2 i = nth 0 s i.
Proof.
elim=> [//=|n IH s j ltn1j ltjs /=].
rewrite IH // ?size_aperm //; last by rewrite (@ltn_trans n.+1 _ j). 
rewrite nth_aperm_id // gtn_eqF //(@leq_ltn_trans n.+1) // index_bigmax_lt // (@ltn_trans j) //. 
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
  under eq_bigr => i /andP [_ ltin1]. rewrite nth_cat size_take ltn1s ltin1; over.
  by rewrite [RHS]big_nat.
have: a' = \max_(0 <= i < n.+1) nth 0 (take n.+1 s') i. 
  rewrite /a' big_nat. 
  under eq_bigr => i /andP [_ ltin1]. rewrite nth_cat size_take swap_size ltn1s ltin1; over.
  by rewrite [RHS]big_nat.  
move: (size_take n.+1 s) => szt1; rewrite ltn1s in szt1.
move: (size_take n.+1 s') => szt1'; rewrite !swap_size ltn1s in szt1'.
rewrite -{1}szt1' -{3}szt1 => -> ->.
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
  have [] := boolP (j <= n) => lejn; first by rewrite (IH s') // size_aperm (@ltn_trans n.+1).
  have/eqP -> : j == n.+1 by rewrite eqn_leq lejn1 (ltnNge n j) lejn.
  rewrite swap_id ?size_aperm //.
  rewrite nth_aperm // ?bigmax_in // -max_swap ?size_aperm //.  
  rewrite (@max_aperm _ ix) //. 
  move: (index_bigmax_lt lt0s ltn1s).
  by rewrite leq_eqVlt -(negbK (ix == n.+1)) neixn1.
Qed.

End Sorted.

Section Specification.

Definition up_sorted (s : seq nat) := sorted leq s.

Lemma bubble_sorted_nil : bubble_sort [::] = [::].
Proof. by []. Qed.

Lemma bubble_sorted s : up_sorted (bubble_sort s).
Proof.
have [] := boolP (s == [::]) => [/eqP ->|]; first by rewrite bubble_sorted_nil.
rewrite -size_eq0 -lt0n => lt0s.
apply: (@path_sorted _ leq 0).
apply/(pathP 0) => i ltiz.
have [] := boolP (i == 0) => [/eqP -> //=|nei0].
rewrite -lt0n in nei0.  
rewrite swap_size in ltiz.
have leiz1 : i <= (size s).-1 by rewrite ?ltn_predL -ltnS prednK.
have lei1z1 : i.-1 <= (size s).-1 by rewrite (@leq_trans i) // leq_pred.
move: (nei0) => /prednK <-. 
rewrite -nth_behead /behead prednK // !max_swaps // ?ltn_predL //. 
rewrite [X in _ <= X](@big_cat_nat _ _ _ i.-1.+1) //= ?maxnE ?leq_addr //=.
by rewrite (@leq_ltn_trans i) // ?leq_pred.
Qed.

Theorem bubble_sort_spec (s : seq nat) :
  exists (ts : seq transposition),
    let: (all_bubbles, s') := swap s ts in 
    all_bubbles /\ up_sorted s'.
Proof.
have [] := boolP (s == [::]) => [/eqP -> |]; first by exists [::].
rewrite -size_eq0 -lt0n => lt0s.
exists (transpositions s (size s).-1) => //=.  
set bs' := (swap _ _). 
rewrite (surjective_pairing bs') bubbles_in_swap // ?ltn_predL //. 
by split=> //; last by exact: bubble_sorted. 
Qed.

End Specification.

End BubbleSort.

Section Permutation.

(** Provide an implementation of the permutation interface. *)

Notation transposition := (nat * nat)%type.

Implicit Types (t : transposition).

Section Transpose.

Definition transpose t i := if i == t.1 then t.2 else if i == t.2 then t.1 else i.

Variable (i i1 i2 : nat).

Lemma transpose_id : transpose (i1, i1) i = i.
Proof. by rewrite /transpose /=; case: ifP => [/eqP -> //|_]; case: ifP => [/eqP -> //|_]. Qed.

Lemma transposeR : transpose (i1, i2) i2 = i1.
Proof. rewrite /transpose /=; case: ifP => [/eqP ->//|_]; by rewrite eq_refl. Qed.

Lemma transposeL : transpose (i1, i2) i1 = i2.
Proof. by rewrite /transpose eq_refl. Qed.

Lemma transposeD (ne1 : (i == i1) = false) (ne2 : (i == i2) = false) : 
  transpose (i1, i2) i = i.
Proof. by rewrite /transpose /= ifF ?ifF. Qed.

Lemma transpose_bound n (lt1n : i1 < n) (lt2n : i2 < n) (ltin : i < n) :
  transpose (i1, i2) i < n.
Proof. by rewrite /transpose; case: ifP => //; case: ifP. Qed.

Lemma transposeK : involutive (transpose (i1, i2)).
Proof.
rewrite /transpose /= => j.
case: ifP.
- by case: ifP => [/eqP -> // /eqP -> //|]; last by case: ifP => [/eqP //|_ -> //].
- case: ifP => [/eqP ->|]; first by rewrite eq_refl.
  by case: ifP => [|-> //]; first by rewrite eq_refl.
Qed.

End Transpose.

Section TransposeIota.

Variable (n : nat).

Definition transposed_iota t := [seq transpose t i | i <- iota 0 n].

Lemma transpose_iotaC i1 i2 : transposed_iota (i2, i1) = transposed_iota (i1, i2).
Proof.
rewrite /transposed_iota.
apply: (@eq_from_nth _ 0) => [|i ltin]; first by rewrite !size_map.
rewrite size_map size_iota in ltin.
rewrite !(@nth_map _ 0) ?size_iota ?nth_iota ?add0n /transpose //=.
by case: ifP => [/eqP ->|ne2]; first by case: ifP => [/eqP -> //|].
Qed.

Definition within (s : seq nat) t := take (t.2 - t.1.+1) (drop t.1.+1 s).

Lemma transpose_iota i1 i2  (l1n : i1 < n) (l2n : i2 < n) (lt12 : i1 < i2) :
  let s := transposed_iota (i1, i2) in
  let: (s1, s2, s3, s4, s5) := 
    (take i1 s, [:: nth 0 s i1], within s (i1, i2), [:: nth 0 s i2], drop i2.+1 s) in
  s = (s1 ++ s2) ++ ((s3 ++ s4) ++ s5).
Proof.
have l21n: i2 - i1.+1 < n - i1.+1 by rewrite ltn_sub2r // (@ltn_leq_trans i2.+1).
apply: (@eq_from_nth _ 0) => [|i lis]. 
- rewrite !size_cat !size_take !size_drop /= !size_map !size_iota l1n ifT //.
  by rewrite addn1 !addnA subnKC // addn1 subnKC.
- rewrite !nth_cat !size_cat /= !size_take !size_drop !size_map !size_iota !l1n !l21n.
  have [] := boolP (i < i1) => lt1; first by rewrite ifT ?nth_take // (@ltn_trans i1) ?ltn_addr.
  rewrite -ltnNge ltnS in lt1.
  have [] := boolP (i == i1) => [/eqP ->|ne1]; first by rewrite subnn /= ifT // ltn_addr. 
  rewrite leq_eqVlt -(negbK (i1 == i)) eq_sym ne1 /= in lt1.
  have [] := boolP (i < i2) => [lt2|].
  - have lt112: i1 + 1 < i2 by rewrite (@leq_ltn_trans i) // addn1.    
    have lti12 : i - i1.+1 < i2 - i1.+1 by rewrite ?ltn_sub2r // (@ltn_leq_trans i.+1).
    have lti121: i - i1.+1 < i2 - i1.+1 + 1 by rewrite (@ltn_trans (i2 - i1.+1)) // ltn_addr.
    have mx //: maxn i1.+1 i = i by apply/maxn_idPr.
    by rewrite ifF ?ifT addn1 //= ?nth_take ?nth_drop -?maxnE ?mx //= ltnS leqNgt lt1.
  - rewrite -leqNgt => le2i. 
    have [] := boolP (i == i2) => [/eqP -> /=|ne2].    
    - by rewrite ifF addn1 ?ltn_addr ?ltnn ?subnn //= ltnS leqNgt lt12.
    - rewrite leq_eqVlt -(negbK (i2 == i)) eq_sym ne2 /= in le2i.  
      rewrite ifF ?subnDA ?ifF ?nth_drop //=; last by rewrite addn1 ltnS leqNgt lt1. 
      have -> // : i2.+1 + (i - i1 - 1 - (i2 - i1.+1) -1) = i. 
        rewrite -(@subnDA i1) -subnDA !addn1 subnSK -?subnDA ?(@addnBCA i1.+1) ?(@ltnW i1 i2) //.
        by rewrite subSnn addn1 subnKC.
      rewrite ?subnK ltnNge ?subn1 -ltnS ?prednK ?ltn_sub2r // ?subn_gt0 //.
      by rewrite addn1 (@subnSK _ i2) // ltn_sub2r.
Qed.

Lemma untranspose_iota i1 i2  (lt1n : i1 < n) (lt2n : i2 < n) (lt12 : i1 < i2) :
  let s := transposed_iota (i1, i2) in
  let: (s1, s2, s3, s4, s5) := 
    (take i1 s, [:: nth 0 s i1], within s (i1, i2), [:: nth 0 s i2], drop i2.+1 s) in
  (((s1 ++ s4) ++ s3) ++ s2) ++ s5 = iota 0 n.
Proof.
have l21n: i2 - i1.+1 < n - i1.+1 by rewrite ltn_sub2r // (@ltn_leq_trans i2.+1).
set s := transposed_iota (i1, i2) => /=.
have -> : drop i2.+1 s = drop i2.+1 (iota 0 n). 
  apply: (@eq_from_nth _ 0) => [|i lis]; first by rewrite !size_drop !size_map.
  rewrite size_drop size_map size_iota ltn_subRL in lis.
  rewrite !nth_drop (nth_map 0) ?nth_iota ?size_iota ?add0n //.
  by rewrite transposeD // ?gtn_eqF // ?(@ltn_trans i2 i1 (i2.+1 + i)) // addSnnS ltn_addr.
have -> : nth 0 s i1 = nth 0 (iota 0 n) i2. 
  by rewrite (nth_map 0) ?size_iota ?nth_iota // !add0n transposeL.
rewrite -catA //= -drop_nth ?size_iota // -[RHS](cat_take_drop i2 (iota 0 n)).
apply/eqP. 
rewrite (@eqseq_cat _ _ _ (drop i2 (iota 0 n))) ?eq_refl ?andbT /within; 
  last by rewrite !size_cat !size_take !size_drop !size_map !size_iota lt1n lt2n l21n
                  addn1 subnKC.  
have -> : take (i2 - i1.+1) (drop i1.+1 s) = take (i2 - i1.+1) (drop i1.+1 (iota 0 n)). 
  apply: (@eq_from_nth _ 0) => [|i ltis]; first by rewrite !size_take !size_drop !size_map. 
  rewrite size_take size_drop !size_map !size_iota l21n in ltis.
  have lt11 : i1.+1 + i < n by rewrite (@ltn_trans i2) // -ltn_subRL.
  rewrite !nth_take ?nth_drop /s /transpose_iota 
          ?(nth_map 0) // ?nth_iota // ?add0n ?size_iota //.
  by rewrite transposeD // ?(@gtn_eqF i1) // addSnnS ?ltn_addr //
             ltn_eqF // -addSnnS -ltn_subRL.
rewrite take_drop subnK //. 
have -> : nth 0 s i2 = nth 0 (take i2 (iota 0 n)) i1. 
  rewrite (nth_map 0) ?size_iota // nth_iota // take_iota transposeR nth_iota ?add0n //.
  have -> // : minn i2 n = i2 by apply/minn_idPl; rewrite ltnW.
rewrite -catA //= -drop_nth ?size_take ?size_map ?size_iota ?lt2n //. 
rewrite -[X in _ == X](cat_take_drop i1) eqseq_cat ?eq_refl ?andbT; 
  last by rewrite !size_take /s !size_map !size_iota lt2n lt1n ifT. 
rewrite take_take 1?ltnW //.
have -> // : take i1 s = take i1 (iota 0 n). 
  apply: (@eq_from_nth _ 0) => [|i ltis]; first by rewrite !size_take size_map.
  rewrite size_take size_map size_iota lt1n in ltis.
  have ltin : i < n by rewrite (@ltn_trans i1).
  rewrite !nth_take ?(nth_map 0) ?size_iota // ?nth_iota ?add0n //. 
  by rewrite transposeD // ?ltn_eqF // (@ltn_trans i1).
Qed.

Lemma perm_eq_no_transpose_iota i (ltin : i < n) : perm_eq (transposed_iota (i, i)) (iota 0 n).  
Proof.
have -> : transposed_iota (i, i) = iota 0 n.
  rewrite /transpose_iota.
  apply: (@eq_from_nth _ 0) => [|j ltjs]; first by rewrite size_map.
  rewrite size_map in ltjs.
  by rewrite (nth_map 0) ?transpose_id.
exact: perm_refl.
Qed.

Lemma perm_eq_transpose_iota i1 i2 (lt1n : i1 < n) (lt2n : i2 < n) :
  perm_eq (transposed_iota (i1, i2)) (iota 0 n).  
Proof.
have [] := boolP (i1 == i2) => [/eqP -> |ne12]; first by exact: perm_eq_no_transpose_iota.
wlog: i1 i2 lt1n lt2n ne12 / i1 < i2 => [H|lt12].
- move: (ne12).
  rewrite neq_ltn => /orP [lt12|lt21]; first by rewrite H.
  rewrite eq_sym in ne12.
  move: (transpose_iotaC i1 i2) (H i2 i1 lt2n lt1n ne12 lt21).  
  by rewrite /transpose_iota => ->.
- set s := (X in perm_eq X) => {ne12}.   
  move: (transpose_iota lt1n lt2n lt12) => /=.
  rewrite /s => ->.
  set s1 := take i1 s; set s2 := [:: nth 0 s i1];
  set s3 := within s (i1, i2);
  set s4 := [:: nth 0 s i2]; set s5 := drop i2.+1 s. 
  rewrite perm_catACA (@perm_trans _ ((s1 ++ s4 ++ s3) ++ s2 ++ s5)) //;
        first by rewrite perm_cat2r (@perm_catl _ s1 _ (s4 ++ s3)) // perm_catC perm_refl.
  by rewrite !catA (untranspose_iota lt1n lt2n lt12) perm_refl.
Qed.

End TransposeIota.

Section Aperm.

Variable (s : seq nat).

Definition aperm t := [seq nth 0 s (transpose t i) | i <- iota 0 (size s)].

Lemma size_aperm t : size (aperm t) = size s.
Proof. by rewrite /aperm size_map size_iota. Qed.

Lemma aperm_id i : aperm (i, i) = s. 
Proof.
apply: (@eq_from_nth _ 0) => [|j ltjs /=]; first by rewrite size_aperm.
rewrite size_aperm in ltjs. 
by rewrite (nth_map 0) ?size_iota // nth_iota //= add0n  transpose_id.
Qed.

Lemma nth_aperm i m (ltis : i < size s) (min : m \in s) :
  nth 0 (aperm (index m s, i)) i = m.
Proof. 
rewrite (nth_map 0) // /transpose /= ?size_iota ?nth_iota // add0n.
case: ifP => [/eqP -> |]; first by rewrite nth_index.
by rewrite ifT // nth_index.
Qed.

Lemma nth_aperm_id i1 i2 i (ltis : i < size s) (nei1 : i != i1) (nei2 : i != i2) : 
  nth 0 (aperm (i1, i2)) i = nth 0 s i.
Proof.                                                                     
have nej j: i != j -> (i == j) = false by apply: contra_neqF => /eqP.
by rewrite /aperm (nth_map 0) // /transpose ?size_iota // nth_iota //= add0n !ifF 2?nej.
Qed.

Lemma perm_eq_aperm i1 i2 (lt1s : i1 < size s) (lt2s : i2 < size s) :
  perm_eq s (aperm (i1, i2)).
Proof.
apply/(perm_iotaP 0).
exists (map (transpose (i1, i2)) (iota 0 (size s))).
- by rewrite size_aperm perm_eq_transpose_iota.
- apply: (@eq_from_nth _ 0) => [|i ltis]; first by rewrite !size_map size_iota.
  rewrite !(nth_map 0) ?size_iota // ?nth_iota // ?add0n ?transposeK // ?transpose_bound //.
  by rewrite size_map size_iota.
Qed.

End Aperm.

Lemma take_perm_comm s i1 i2 m (le12 : i1 <= i2) (lt2s : i2 < size s) (lt2m : i2 < m):
  take m (aperm s (i1, i2)) = aperm (take m s) (i1, i2).
Proof. 
rewrite -map_take /aperm take_iota size_take.
apply: (@eq_from_nth _ 0) => [|i]; first by rewrite !size_map !size_iota.
rewrite size_map size_iota => ltimn.
rewrite !(nth_map 0) ?size_iota ?nth_iota // ?add0n //. 
have [] := boolP (m <= size s) => [ltim|].
- rewrite nth_take // /transpose /=. 
  case: ifP => // _.
  case: ifP => // _; first by rewrite (@leq_ltn_trans i2). 
  by move: ltim => /minn_idPl => <-.
- rewrite -ltnNge => lemi.
  by rewrite take_oversize // ltnW.
Qed.

End Permutation.

Definition bs_spec :=  (bubble_sort_spec aperm_id 
                                         size_aperm
                                         nth_aperm
                                         nth_aperm_id
                                         perm_eq_aperm
                                         take_perm_comm).
Check bs_spec.
Print Assumptions bs_spec.
