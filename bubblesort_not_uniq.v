(** 

  bubblesort_not_uniq.v

  A specification and (inefficient, using `bigop`) implementation for a variant of 
  Bubble Sort.

  The specification states the existence of a list of sorted transpositions (bubbles) that 
  can be applied to any sequence to provide a sorted one (see Theorem `bubble_sort_spec`
  and the `bs_spec` instance).

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

End Nat.

(** Bigop-like utilities for `max` on non-empty intervals of `nat`. *)

Section Bigmax.

Implicit Types (m n : nat) (s : seq nat).

Lemma bigmaxD1r m n F : \max_(m <= i < n.+1 | i != n) F i = \max_(m <= i < n) F i.
Proof.
rewrite [RHS]big_nat_cond [RHS](@big_nat_widen _ _ _ m n n.+1) // [LHS]big_nat_cond.
apply: eq_bigl => i.
by rewrite andbT -[RHS]andbA andbb -andbA ltnS ltn_neqAle [X in _ && X]andbC.
Qed.

Lemma ex_bigmax_index m n F (ltmn1 : m < n.+1) : exists ix, \max_(m <= i < n.+1) F i = F ix /\ ix <= n.
Proof.
elim: n ltmn1 => [|n IH ltmn2]; first by rewrite ltnS leqn0 => /eqP ->; exists 0; rewrite big_nat1.
rewrite // (bigD1_seq n.+1) ?iota_uniq ?mem_iota //=; 
  last by rewrite -ltnS ltmn2 subnKC ?(ltnW ltmn2) ?ltnSn.
have [] := boolP (m < n.+1) => [ltmn1|]. 
- move: (IH ltmn1) => [ix [mx ltx]].  
  case: leqP => leF1; last by exists n.+1; rewrite ltnSn.
  by exists ix; rewrite bigmaxD1r mx; split=> //; last by rewrite (leq_trans ltx).
- rewrite -ltnNge ltnS => ltnm. 
  have/eqP -> : m == n.+1 by rewrite eqn_leq -ltnS ltmn2 ltnm.
  by exists n.+1; rewrite bigmaxD1r big_geq.
Qed.

Lemma leq_bigmax_nat n F i0 (lei0n : i0 <= n) : F i0 <= \max_(0 <= i < n.+1) F i.
Proof. by rewrite (bigD1_seq i0) //= ?mem_iota ?iota_uniq ?andbT //= leq_max leqnn. Qed.

Local Lemma bigmax_nth_in_take s n (lt0s : 0 < size s) (ltns : n < size s) : 
  \max_(0 <= i < n.+1) nth 0 s i \in take n.+1 s. 
Proof.
apply/(nthP 0).
move: (@ex_bigmax_index 0 n (nth 0 s) (ltn0Sn n)) => [ix [mx lx]]. 
rewrite -ltnS in lx.
have [] := boolP (ix < size s) => [ltxs|].
- exists ix; first by rewrite size_take; case: ifP.
  by rewrite nth_take ?mx.
- rewrite -leqNgt => lesx.
  exists 0 => //; first by rewrite size_take; case: ifP.
  move: (@leq_bigmax_nat n (nth 0 s) 0 (leq0n n)).
  have eq0: nth 0 s ix = 0 by rewrite nth_default. 
  by rewrite nth_take // mx eq0 leqn0 => /eqP.
Qed.

Lemma bigmax_nth_in n s (lt0s : 0 < size s) (ltns : n < size s) : 
  \max_(0 <= i < n.+1) nth 0 s i \in s. 
Proof. by rewrite (@mem_take n.+1) ?bigmax_nth_in_take. Qed.

Lemma bigmax_nth_index_leq n s (lt0s : 0 < size s)(ltns : n < size s) :
  index (\max_(0 <= i < n.+1) nth 0 s i) s <= n. 
Proof. by rewrite -ltnS index_ltn ?bigmax_nth_in_take. Qed.

Lemma bigmax_nth_take m n s (ltmn1 : m < n.+1) (ltns : n < size s) :
  \max_(m <= i < n.+1) nth 0 s i = \max_(m <= i < size (take n.+1 s)) nth 0 (take n.+1 s) i. 
Proof.
have sztk: size (take n.+1 s) = n.+1. 
  rewrite size_take.
  have [] := boolP (n.+1 < size s) => [//|nen1s].
  by have/eqP eqzn1 : size s == n.+1 by rewrite eqn_leq ltns leqNgt nen1s.
rewrite -[in LHS](cat_take_drop n.+1 s) [LHS](@big_cat_nat _ _ _ n.+1) 1?(@leq_trans n m) //=. 
rewrite (@big_geq _ _ _ n.+1) // maxn0 !big_nat -{1 2}sztk.
by apply: eq_bigr => i /andP [_ ltn1]; by rewrite nth_cat ltn1.
Qed.

End Bigmax.

(** A dedicated Transposition module for Bubble Sort.

   These definitions provide an implementation for transposition-based permutations, 
   based on indices `i`, inspired in part by `perm.v`, although this one is working on `nat`. *)

Module Transposition.

Notation transposition := (nat * nat)%type.

Implicit Types (i m n : nat) (s : seq nat) (t : transposition).

Section Transpose.

Definition transpose t i := if i == t.1 then t.2 else if i == t.2 then t.1 else i.

Variable (i i1 i2 : nat).

Lemma transpose_id : transpose (i1, i1) i = i.
Proof. by rewrite /transpose /=; case: ifP => [/eqP -> //|_]; case: ifP => [/eqP -> //|_]. Qed.

Lemma transposeR : transpose (i1, i2) i2 = i1.
Proof. rewrite /transpose /=; case: ifP => [/eqP ->//|_]; by rewrite eq_refl. Qed.

Lemma transposeL : transpose (i1, i2) i1 = i2.
Proof. by rewrite /transpose eq_refl. Qed.

Lemma transposeD (ne1 : i != i1) (ne2 : i != i2) : transpose (i1, i2) i = i.
Proof. 
rewrite /transpose /= ifF ?ifF //; first by move: ne2; apply: contra_neqF => /eqP.
by move: ne1; apply: contra_neqF => /eqP.
Qed.

Lemma ltn_transpose n (lt1n : i1 < n) (lt2n : i2 < n) (ltin : i < n) :
  transpose (i1, i2) i < n.
Proof. by rewrite /transpose; case: ifP => //; case: ifP. Qed.

Lemma transposeK : involutive (transpose (i1, i2)).
Proof.
rewrite /transpose /= => j.
case: ifP; first by case: ifP => [/eqP -> // /eqP -> //|]; last by case: ifP => [/eqP //|_ -> //].
case: ifP => [/eqP ->|]; first by rewrite eq_refl.
by case: ifP => [|-> //]; first by rewrite eq_refl.
Qed.

End Transpose.

Section TransposedIota.

Variable (n : nat).

Variable (i1 i2 : nat) (lt1n : i1 < n) (lt2n : i2 < n).

Definition transposed_iota := map (transpose (i1, i2)) (iota 0 n).

Lemma size_transposed : size transposed_iota = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma uniq_transposed_iota : uniq transposed_iota. 
Proof.
rewrite (@map_uniq _ _ (nth 0 transposed_iota)) //. 
set ti := (X in uniq X). 
have -> : ti = iota 0 n.
  apply: (@eq_from_nth _ 0) => [|i ltis]; first by rewrite size_map size_transposed size_iota.
  rewrite size_map size_transposed in ltis.
  rewrite !(nth_map 0) ?size_transposed ?nth_iota ?add0n ?size_iota ?ltn_transpose //.
  exact: transposeK.
exact: iota_uniq.
Qed.

Lemma perm_eq_transposed_iota : perm_eq transposed_iota (iota 0 n).  
Proof.
rewrite uniq_perm ?iota_uniq // ?uniq_transposed_iota // => x. 
apply/(nthP 0)/(nthP 0); rewrite ?size_iota ?size_transposed.
- move=> [i ltit <-].
  have [] := boolP (~~ (i == i1) && ~~ (i == i2)) => [/andP [ne1 ne2]|/nandP].
  - by exists i => //;  rewrite (nth_map 0) ?size_iota ?nth_iota ?add0n ?transposeD.
  - rewrite !negbK; move=> [/eqP ->|/eqP ->]. 
    - by exists i2 => //; rewrite (nth_map 0) ?size_iota ?nth_iota ?add0n ?transposeL.
    - by exists i1 => //; rewrite (nth_map 0) ?size_iota ?nth_iota ?add0n ?transposeR.
- move=> [i ltit].
  rewrite nth_iota ?add0n // => <-.
  have [] := boolP (~~ (i == i1) && ~~ (i == i2)) => [/andP [ne1 ne2]|/nandP].
  - by exists i => //; rewrite (nth_map 0) ?size_iota ?nth_iota ?add0n ?transposeD. 
  - rewrite !negbK; move=> [/eqP ->|/eqP ->]. 
    - by exists i2 => //; rewrite (nth_map 0) ?size_iota ?nth_iota ?add0n ?transposeR.
    - by exists i1 => //; rewrite (nth_map 0) ?size_iota ?nth_iota ?add0n ?transposeL.
Qed.

End TransposedIota.

Section Aperm.

Variable (s : seq nat).

Variable (i1 i2 i : nat) (ltis : i < size s) (lt1s : i1 < size s) (lt2s : i2 < size s).

Definition aperm t := [seq nth 0 s (transpose t i) | i <- iota 0 (size s)].

Lemma size_aperm t : size (aperm t) = size s.
Proof. by rewrite /aperm size_map size_iota. Qed.

Lemma aperm_id : aperm (i, i) = s. 
Proof.
apply: (@eq_from_nth _ 0) => [|j ltjs /=]; first by rewrite size_aperm.
rewrite size_aperm in ltjs. 
by rewrite (nth_map 0) ?size_iota // nth_iota //= add0n  transpose_id.
Qed.

Lemma nth_aperm m (min : m \in s) : nth 0 (aperm (index m s, i)) i = m.
Proof. 
rewrite (nth_map 0) // /transpose /= ?size_iota ?nth_iota // add0n.
case: ifP => [/eqP -> |]; first by rewrite nth_index.
by rewrite ifT // nth_index.
Qed.

Lemma nth_aperm_id (ne1 : i != i1) (ne2 : i != i2) : nth 0 (aperm (i1, i2)) i = nth 0 s i.
Proof.                                                                     
have nej j: i != j -> (i == j) = false by apply: contra_neqF => /eqP.
by rewrite /aperm (nth_map 0) // /transpose ?size_iota // nth_iota //= add0n !ifF 2?nej.
Qed.

Lemma perm_eq_aperm : perm_eq s (aperm (i1, i2)).
Proof.
apply/(perm_iotaP 0).
exists (map (transpose (i1, i2)) (iota 0 (size s))).
- by rewrite size_aperm perm_eq_transposed_iota.
- apply: (@eq_from_nth _ 0) => [|i' lti's]; first by rewrite !size_map size_iota.
  rewrite !(nth_map 0) ?size_iota // ?nth_iota // ?add0n ?transposeK // ?ltn_transpose //.
  by rewrite size_map size_iota.
Qed.

End Aperm.

Lemma take_perm_comm s i1 i2 m (le12 : i1 <= i2) (lt2s : i2 < size s) (lt2m : i2 < m) :
  take m (aperm s (i1, i2)) = aperm (take m s) (i1, i2).
Proof. 
rewrite -map_take /aperm take_iota size_take.
apply: (@eq_from_nth _ 0) => [|i]; first by rewrite !size_map !size_iota.
rewrite size_map size_iota => ltimn.
rewrite !(nth_map 0) ?size_iota ?nth_iota // ?add0n //. 
have [] := boolP (m <= size s) => lems; last by rewrite take_oversize // ltnW // ltnNge.
rewrite nth_take // /transpose /=. 
case: ifP => // _.
case: ifP => // _; first by rewrite (@leq_ltn_trans i2). 
by move: lems => /minn_idPl <-.
Qed.

Lemma perm_eq_take_aperm m s i1 i2 (lt2m1s : i2 + m.+1 < size s) (le12 : i1 <= i2) : 
  perm_eq (take (i2 + m.+1) s) (take (i2 + m.+1) (aperm s (i1, i2))).
Proof.
have -> : take (i2 + m.+1) (aperm s (i1, i2)) = aperm (take (i2 + m.+1) s) (i1, i2).  
  rewrite take_perm_comm // ?nth_take //= // (@leq_ltn_trans i2) ?ltn_addr //.
  by rewrite (@ltn_trans (i2 + m.+1)) ?ltn_addr.
by rewrite perm_eq_aperm ?size_take // lt2m1s ?ltn_addr // (@leq_ltn_trans i2) // ltn_addr.
Qed.

Lemma max_aperm s i n (ltns : n < size s) (lein : i <= n) :
  \max_(0 <= j < n.+1) nth 0 s j = \max_(0 <= j < n.+1) nth 0 (aperm s (i, n)) j. 
Proof.
rewrite bigmax_nth_take // [RHS]bigmax_nth_take // ?size_aperm //.
set s' := (aperm _ _).    
rewrite -!(big_nth 0 predT id) (perm_big (take n.+1 s')) //= /s'.
have [] := boolP (n.+1 < size s) => ltn1s; first by rewrite -addn1 perm_eq_take_aperm // addn1.
have/eqP <- : size s == n.+1 by rewrite eqn_leq ltns leqNgt ltn1s.
by rewrite -{2}(@size_aperm _ (i, n)) !take_size perm_eq_aperm // (@leq_ltn_trans n). 
Qed.

End Transposition.

Module T := Transposition.

(** Bubble Sort definition and specification. *)

Section BubbleSort.

Notation transposition := (nat * nat)%type.

Implicit Types (i n m : nat) (s : seq nat) (t : transposition).

(* Needed definitions from Transposition. *) 

Notation aperm := T.aperm.
Notation aperm_id := T.aperm_id.
Notation size_aperm := T.size_aperm.
Notation nth_aperm := T.nth_aperm.
Notation nth_aperm_id := T.nth_aperm_id.
Notation perm_eq_aperm := T.perm_eq_aperm.
Notation perm_eq_take_aperm := T.perm_eq_take_aperm.
Notation max_aperm := T.max_aperm.

(** Bubble Sort builds upon transpositions (to be shown later as being out-of-order `bubbles`),
    here on a prefix of `s`, from indices `0` to `n` (included) in `s`. *)

Section Algorithm. 

Fixpoint transpositions s n : seq transposition :=
  match n with
  | 0 => [::]
  | n'.+1 => let max := \max_(O <= i < n.+1) nth 0 s i in 
            let t := (index max s, n) in 
            let ts := transpositions (aperm s t) n'  in
            t :: ts
  end.

(* `swap` applies the list of transpositions `ts` to `s`, returning the swapped list 
    together with a boolean checking whether all these transpositions are bubbles.  *)

Definition is_bubble s t : bool :=
  let: (i1, i2) := t in 
  (i1 < size s) && (i2 < size s) &&
    ((i1 == i2) || (i1 < i2) && (nth 0 s i2 <= nth 0 s i1)).

Fixpoint swap s (ts : seq transposition) : bool * seq nat :=
  match ts with
  | [::] => (true, s)
  | t :: ts' => let bs' := swap (aperm s t) ts' in
             (is_bubble s t && bs'.1, bs'.2)
  end.

Definition bubble_sort s : seq nat := (swap s (transpositions s (size s).-1)).2.

End Algorithm.

(** Proof that there are only bubbles in the `n`-prefix of `transpositions s`. *)

Section Bubbles.

Lemma bubbles_in_swap : forall n s (ltns : n < size s), (swap s (transpositions s n)).1.
Proof.
elim=> [//=|n IH s ltn1s /=]. 
apply/andP; split; last by rewrite IH // ?size_aperm // -?lt0n ltnW.
set mx := (\max_(_ <= i < _) _).
have lt0s : 0 < size s by rewrite (leq_ltn_trans (leq0n n.+1)).
have [] := boolP (index mx s == n.+1) => [/eqP eqin1 //=|nein1].
- move: (@bigmax_nth_index_leq n.+1 s lt0s ltn1s).
  rewrite leq_eqVlt => /orP [eqixn1|ltxn1]; first by rewrite eqin1 !ltn1s. 
  by rewrite ltn1s !andbT (@ltn_trans n.+1). 
- have ltxn1: index mx s < n.+1 by rewrite (@ltn_neqAle _ n.+1) bigmax_nth_index_leq // andbT.
  by rewrite (@ltn_trans n.+1 _ (size s)) // !ltxn1 ltn1s nth_index
             ?leq_bigmax_nat ?bigmax_nth_in.
Qed.

End Bubbles.

(** Proof that the `n`-prefix of a sequence `s` swapped with `transpositions s n` is sorted. *)

Section Sorted.

Lemma size_swap ts s : size (swap s ts).2 = size s. 
Proof. by elim: ts s => [//=|t ts IH s /=]; rewrite IH size_aperm. Qed.

Lemma perm_eq_take_swap n : forall s,
    n.+1 < size s -> perm_eq (take n.+1 s) (take n.+1 (swap s (transpositions s n)).2).
Proof.
suff: forall s m, n.+1 + m < size s ->
             perm_eq (take (n + m.+1) s) (take (n + m.+1) (swap s (transpositions s n)).2).
  move=> H s ltn1s. 
  move: (@H s 0).
  by rewrite addn1 addn0 => ->.
elim: n => [//=|n IH s m ltn2ms].
pose ix := index (\max_(0 <= i < n.+2) nth 0 s i) s.
rewrite (@perm_trans _ (take (n.+1 + m.+1) (aperm s (ix, n.+1)))) //.  
- rewrite perm_eq_take_aperm // -?addSnnS // bigmax_nth_index_leq //(@ltn_trans (n.+2 + m)) //.
  by rewrite addSnnS ltn_addr.
- have szap : n.+1 + m.+1 < size (aperm s (ix, n.+1)) by rewrite size_aperm -addSnnS.
  move: (@IH (aperm s (ix, n.+1)) m.+1 szap).
  by have -> // : n + m.+2 = n.+1 + m.+1 by rewrite addnS addSn.
Qed.

Lemma swap_id n : forall s i (ltni : n < i) (ltis : i < size s),
  nth 0 (swap s (transpositions s n)).2 i = nth 0 s i.
Proof.
elim: n => [//=|n IH s j ltn1j ltjs /=].
rewrite IH // ?size_aperm //; last by rewrite (@ltn_trans n.+1 _ j). 
rewrite nth_aperm_id // gtn_eqF //(@leq_ltn_trans n.+1) //. 
by rewrite bigmax_nth_index_leq // (@ltn_trans j) // (@ltn_trans n.+1).
Qed.

Lemma max_swap n s (ltn1s : n.+1 < size s) :
  \max_(0 <= i < n.+2) nth 0 s i = \max_(0 <= i < n.+2) nth 0 (swap s (transpositions s n)).2 i.
Proof. 
rewrite big_nat_recr //= [RHS]big_nat_recr //=.
rewrite bigmax_nth_take ?[in RHS]bigmax_nth_take // ?size_swap ?(@ltn_trans n.+1 n (size s)) //.
congr maxn; last by rewrite swap_id.
set s' := (swap _ _).2.  
by rewrite -!(big_nth 0 predT id) (perm_big (take n.+1 s')) //= perm_eq_take_swap.
Qed.

Lemma max_swaps n : forall s (ltns : n < size s),
    let s' := (swap s (transpositions s n)).2 in
    forall j, j <= n -> nth 0 s' j = \max_(O <= i < j.+1) nth 0 s' i.
Proof.
elim: n => [//= s lt0s j|n IH s ltn1s /= j lejn1];
  first by rewrite leqn0 => /eqP ->; rewrite big_nat1.
have lt0s : 0 < size s by rewrite (@ltn_trans n.+1).
have [] := boolP (j <= n) => lejn; first by rewrite IH // // ?size_aperm (@ltn_trans n.+1).
have/eqP -> : j == n.+1 by rewrite eqn_leq lejn1 (ltnNge n j) lejn. 
set ix := (index _ _). 
have [] := boolP (ix == n.+1) => [/eqP eqixn1|neixn1].
- by rewrite eqixn1 aperm_id swap_id // -{1}eqixn1 nth_index // ?bigmax_nth_in // max_swap. 
- rewrite swap_id ?nth_aperm ?bigmax_nth_in -?max_swap ?size_aperm // (@max_aperm _ ix) //. 
  move: (bigmax_nth_index_leq lt0s ltn1s).
  by rewrite leq_eqVlt -(negbK (ix == n.+1)) neixn1.
Qed.

Lemma swap_sorted n s (ltns : n < size s) :
  let s' := (swap s (transpositions s n)).2 in
  forall j, j < n -> nth 0 s' j <= nth 0 s' j.+1.
Proof.  
move=> /= j ltjn.
by rewrite !max_swaps ?(@ltnW j n) ?[X in _ <= X](@big_cat_nat _ _ _ j.+1) //= ?maxnE ?leq_addr.
Qed.

End Sorted.

(** Bubble Sort specification, as applying a list of bubble swaps, yielding a sorted sequence. *)

Section Specification.

Variable (s : seq nat).

Lemma bubble_sorted : sorted leq (bubble_sort s).
Proof.
have [] := boolP (s == [::]) => [/eqP -> //=|].
rewrite -size_eq0 -lt0n => lt0s.
apply: (@path_sorted _ leq 0).
apply/(pathP 0) => i ltiz.
have [] := boolP (i == 0) => [/eqP -> //=|nei0]. 
rewrite -lt0n in nei0.  
rewrite size_swap in ltiz.
have lti1s1 : i.-1 < (size s).-1 by rewrite (@leq_trans i) ?ltn_predL // -ltnS prednK. 
by rewrite -(@prednK i) // -nth_behead swap_sorted // ltn_predL.
Qed.

Theorem bubble_sort_spec :
  {ts : seq transposition |
    let: (all_bubbles, s') := swap s ts in 
    all_bubbles && sorted leq s'}.
Proof.
have [] := boolP (s == [::]) => [/eqP -> |]; first by exists [::].
rewrite -size_eq0 -lt0n => lt0s.
exists (transpositions s (size s).-1) => //=.  
set bs' := (swap _ _). 
by rewrite (surjective_pairing bs') bubbles_in_swap ?ltn_predL ?bubble_sorted. 
Qed.

End Specification.

End BubbleSort.

Check bubble_sort_spec.
Print Assumptions bubble_sort_spec.
