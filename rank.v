From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ltn_perm_iota n l (p : perm_eq l (iota 0 n.+1)) m : nth 0 l m < n.+1. 
Proof.
have [ltms|] := boolP (m < size l); last by rewrite -leqNgt => lesm; rewrite nth_default.  
move: (perm_mem p) (@mem_nth _ 0 _ _ ltms) => ->.
by rewrite mem_iota add0n => /andP [].
Qed.

Section RankImpl.

Variables (n : nat) (T : eqType) (r : rel T) (s : n.+1.-tuple T).

Variable (tr : transitive r) (rr : reflexive r) (totr : total r) (ar : antisymmetric r).

Let A := 'I_n.+1.

Let ranking := n.+1.-tuple 'I_n.+1.

Notation i0 := ord0.
Notation t0 := (tnth s ord0).

Let si := zip_tuple s (ord_tuple n.+1).

Let ri := 
      [rel si1 si2 : T * 'I_n.+1 | r si1.1 si2.1 && ((si1.1 == si2.1) ==> (si1.2 <= si2.2))].

Lemma transitive_ri: transitive ri.
Proof. 
move=> x y z /=; rewrite /ri /= => /andP [ryx /implyP leyx] /andP [rxy /implyP lexz].
apply/andP; split; first by rewrite (@tr x.1).
apply/implyP => /eqP eqyz.
rewrite -eqyz in lexz.
have [eqxy1|] := boolP (y.1 == x.1). 
- by rewrite (@leq_trans x.2) // ?leyx // ?leyz lexz // eq_sym.
- rewrite -eqyz in rxy.
  have -> // : y.1 = x.1.
    apply: ar; rewrite ryx rxy => //.
    by rewrite eq_refl. 
Qed.  

Lemma reflexive_ri: reflexive ri. 
Proof. move=> j. rewrite /ri /=. by rewrite rr leqnn //= implybT. Qed.

Lemma total_ri: total ri. 
Proof. 
move=> x y; rewrite /ri /=. 
have [|//] := boolP (x.1 == y.1).
- rewrite eq_sym => /eqP ->.
  rewrite eq_refl !implyTb.
  move: (leq_total x.2 y.2) => /orP [le2|le2']; first by rewrite le2 rr.
  by rewrite le2' rr orbT.
- rewrite -(negbK (y.1 == x.1)) eq_sym => -> /=.
  by rewrite !andbT totr.
Qed.

Lemma anti_ri : antisymmetric ri.
Proof. 
move=> x y; rewrite /ri /= => /andP [/andP [rxy lexy2]] /andP [ryx leyx2].
have eq11: x.1 = y.1 by apply: ar; rewrite rxy ryx.
rewrite eq11 eq_refl ?implyTb in lexy2 leyx2.
have/eqP eq22: x.2 == y.2.
  by rewrite -(inj_eq val_inj) /= eqn_leq lexy2 leyx2.
by rewrite (surjective_pairing x) (surjective_pairing y) eq22 eq11.
Qed.

Let si' := sort ri si.

Let is_rank (rank : A -> 'I_n.+1) (rval : 'I_n.+1 -> T) :=
  (forall (i j : A), i <= j -> r (rval i) (rval j))
  /\ (forall i : 'I_n.+1, rval (rank i) = tnth s i).

Local Lemma ltn_pred2k k l (p : perm_eq l (iota 0 n.+1)) :
  find [pred t | t.2 == k] [seq nth (t0, i0) si i | i <- l] < size l.
Proof.
have kinl: val k \in l by rewrite (perm_mem p) mem_iota add0n ltn_ord. 
have nth_si : nth (t0, i0) si k = (tnth s k, k).
  by rewrite [in RHS](tnth_nth t0) nth_zip ?nth_ord_enum 
           1?(tnth_nth t0) ?size_enum_ord ?size_tuple.
set l' := (X in find _ X); set t2k := [pred t | t.2 == k].   
have // : find t2k l' < size l.
  have -> : size l = size l' by rewrite size_map. 
  rewrite -has_find /=.  
  apply/(has_nthP (t0, i0)). 
  exists (index (tnth s k, k) l') => /=; first by rewrite index_mem -nth_si map_f.
  by rewrite nth_index //= -nth_si map_f.  
Qed.

Definition zip_rank : A -> 'I_n.+1.
have zip_rank_bnd (i : A) : find [pred t | t.2 == i] si' < n.+1. 
  rewrite /si' /=; have [l p ->] := perm_iota_sort ri (t0, i0) si. 
  rewrite size_tuple in p.   
  by rewrite (@leq_trans (size l)) ?ltn_pred2k // (perm_size p) size_iota.
exact: (fun (i : A) => Ordinal (zip_rank_bnd i)).
Defined.

Definition zip_rval := (fun (r : 'I_n.+1) => (nth (t0, i0) si' r).1).

Lemma is_rank_zip : is_rank zip_rank zip_rval.
Proof. 
rewrite /zip_rank /zip_rval /=.
have szsn1 : size s = size (enum 'I_n.+1) by rewrite size_tuple ?cardE size_enum_ord.
split=> [i j leij|k].   
- have ssi' : sorted ri si' by rewrite sort_sorted //; exact: total_ri.
  move: (sorted_leq_nth transitive_ri reflexive_ri (t0, i0) ssi' i j).
  by rewrite ?inE ?size_tuple ?ltn_ord // => /(_ erefl erefl leij) /= /andP [].    
- rewrite /si' /=; have [l p ->] := perm_iota_sort ri (t0, i0) si.   
  have kinl: val k \in l. 
    by rewrite (perm_mem p) mem_iota add0n size_zip size_tuple /= size_enum_ord minnn.
  rewrite size_tuple in p.   
  set l' := (X in find _ X); set t2k := [pred t | t.2 == k].  
  have ltfinds : find t2k l' < size l by rewrite ltn_pred2k.
  rewrite (nth_map 0) /=; last by exact: ltfinds.
  rewrite nth_zip ?[RHS](tnth_nth t0) //=. 
  have nthfindl' : nth 0 l (find t2k l') = (nth (t0, i0) l' (find t2k l')).2.
    by rewrite (nth_map 0) ?nth_zip /= ?nth_enum_ord //  ltn_perm_iota.
  rewrite nthfindl'.  
  set ikl' := (find t2k l'); pose ikl := index (val k) l.   
  have eqnths : nth 0 l ikl' = nth 0 l ikl.
    rewrite nth_index //=. 
    move: (ltfinds); have -> : size l = size l' by rewrite size_map. 
    rewrite -has_find => /(has_nthP (t0, i0)) [j ltjs]. 
    rewrite size_map in ltjs.
    rewrite nthfindl' (nth_map 0) // nth_zip /= -?(inj_eq val_inj) //=.
    rewrite (nth_map 0) // nth_zip /= ?nth_enum_ord ?ltn_perm_iota //. 
    have find_zip t (alln1 : forall j, j \in t -> j < n.+1) : 
      find [pred x | x.2 == k] [seq nth (t0, i0) si i | i <- t] = 
        find [pred x | x == val k] t. 
      elim: t alln1 => [//=|x t IH alln1 /=].
      rewrite nth_zip /= -?(inj_eq val_inj) /= ?nth_enum_ord ?alln1 ?mem_head // ?IH //
              ?size_tuple ?cardE ?size_enum_ord // => q qint.
      by rewrite alln1 // inE qint orbT.
    rewrite find_zip // => [nthljk|q /(nthP 0) [? _ <-]]; last by rewrite ltn_perm_iota.
    have -> : (find [pred x | x == val k] l) = j; last by exact/eqP.
       case: findP => [/hasPn /(_ (nth 0 l j)) /=|q ltql pre post]; 
         first by rewrite nthljk mem_nth // => /(_ erefl).
       have/(uniqP 0)/(_ q j): uniq l by rewrite (perm_uniq p) iota_uniq.
       apply; rewrite ?inE //.
       move: (pre 0) => /= /eqP ->.
       by rewrite (eqP nthljk).
   by rewrite -nthfindl' eqnths nth_index.
Qed.

End RankImpl.

Variable (n' : nat).
Let n := n'.+2.

Definition A := 'I_n.

Definition bids := A -> nat.
Definition vals := A -> nat.

Section RankDef.

Definition is_rank (b : bids) (rank : A -> 'I_n) (rval : 'I_n -> nat) :=
  (forall (i j : 'I_n), i <= j -> rval j <= rval i)
  /\ (forall i : 'I_n, rval (rank i) = b i).

Record ranking (b : bids):= Ranking {  
    rank : A -> 'I_n;
    rval : 'I_n -> nat;
    _ : is_rank b rank rval }.

Lemma rval_def (b : bids) (r : ranking b) i : rval r (rank r i) = b i.
Proof. by case: r => ? ? [h1 h2] /=. Qed.

Lemma rval_geq (b : bids) (r : ranking b) (i j : 'I_n) : i <= j -> rval r j <= rval r i. 

Proof. by case: r => ? ? [h1 h2] /h1. Qed.

Definition differ_on (b b' : bids) (i : A):= forall j, i != j -> b j = b' j.

Lemma differ_on_sym (b b' : bids) i : differ_on b b' i -> differ_on b' b i.
Proof. by move=> d j neij; move: d => /(_ j neij) ->. Qed.

Definition buildr (b : bids) : ranking b.
have tr: transitive geq by move=> i j k /= ? ?; exact: (@leq_trans i).
have rr: reflexive geq. by move=> /= ?. 
have totr : total geq by move=> i j /=; exact: leq_total.
have ar : antisymmetric geq by move=> i j /=;rewrite -eqn_leq => /eqP ->. 
pose tb := mktuple b.
have/Ranking //: is_rank b (zip_rank geq tb) (zip_rval geq tb).
  move: (is_rank_zip tb tr rr totr ar) => /= [rk rv].
  by split=> // => i; rewrite -(tnth_mktuple b).
Defined.

Lemma rank_stable (b b' : bids) i (h_diff : differ_on b b' i) :
  let r := buildr b in
  let r' := buildr b' in
  forall (h_notmoved : rank r i = rank r' i) j (h_idx : rank r i != j),
     rval r j = rval r' j.
Proof.
set r := buildr b; set r' := buildr b'.
move=> /= eqrr'i rj.
Admitted.

Lemma rank_shift (b b' : bids)
  (r : ranking b)
  (r' : ranking b')
  i
  (h_diff : differ_on b b' i) 
  (h_rank : rank r i <= rank r' i)
  :
  forall j, rval r' j = if rank r i <= j < rank r' i then rval r (inord j.+1) else rval r j.
(*¨  (forall (j : 'I_n), (j < rank r i) || (rank r' i <= j) -> rval r j = rval r' j)
  /\ (forall (j : 'I_n), 
      (rank r i <= j < rank r i) -> rval r (inord j.+1) = rval r' j). *)
Proof.
Admitted.
 
Definition U_SP (v : vals) (b : bids) (i : A) :=
  let r := buildr b in 
  if rank r i == inord 0 then
    v i - rval r (inord 1)
  else
    0
.

Lemma SP_truthful
   (v : vals) (b b': bids) (i : A)
   (h_diff : differ_on b b' i) (h_truth : b i = v i) :
   U_SP v b i >= U_SP v b' i.
Proof.
rewrite /U_SP.
set r := buildr b.
set r' := buildr b'.
case: ifP => h_r2 => //; case: ifP => h_r1.
- have h_idx: rank r i != inord 1.
    by rewrite (eqP h_r1) -(inj_eq val_inj) /= !inordK.
  have snd_eq : rval r (inord 1) = rval r' (inord 1).
    apply: (rank_stable h_diff _ h_idx) => //.
    by rewrite (eqP h_r1) (eqP h_r2).
  by rewrite snd_eq. 
- (* overbidding case *)
  have -> : rval r' (inord 1) = rval r (inord 0).
    have ltr'r: rank r' i <= rank r i by rewrite (eqP h_r2) inordK. 
    rewrite (rank_shift (differ_on_sym h_diff) ltr'r) ifT ?inordK // (eqP h_r2) inordK //=.
    rewrite (contraFltn _ h_r1) // leq_eqVlt ltn0 h_r1. 
    rewrite -(inj_eq val_inj) /= inordK // in h_r1.
    by rewrite h_r1.
  by rewrite -h_truth -(rval_def r) leq_subCl subn0 (@rval_geq _ _ (inord 0)) // inordK.
Qed.

End RankDef.


