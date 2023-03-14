(** 

  labelling.v

  Lemmas about labelling, for bid ordering management.

  Licence: CeCILL-B.

*)

From Coq Require Import Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp.fingroup Require Import perm fingroup.

From mech Require Import lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Labelling.

Variables (n : nat) (T : eqType) (r : rel T) (s : n.-tuple T).

(* Should be a perm (see [labelling_inj]). EJGA: not necessarily tho *)
Definition labelling := n.-tuple 'I_n.

Implicit Types (l : labelling).

Let s' := [tuple of sort r s].

Definition is_labelling l := (s' == [tuple of [seq tnth s i | i <- l]]).

Lemma exists_labelling : exists l, is_labelling l.
Proof.
by have [l p] := perm_iota_sort_tuple r s; exists l; apply/eqP/val_inj.
Qed.

(* Constructive version *)
Lemma exists_labellingW : { l : n.-tuple 'I_n | is_labelling l}.
Proof. apply: sigW; exact: exists_labelling. Qed.

(* Labelling for a sort operation *)
Definition tlabel : labelling := xchoose exists_labelling.

Lemma tlabelP : is_labelling tlabel.
Proof. exact: xchooseP exists_labelling. Qed.

Definition labelling_spec l : bool :=
  [forall j' : 'I_n, tnth s' j' == tnth s (tnth l j')].

Lemma labellingP : labelling_spec (projT1 exists_labellingW).
Proof.
case: exists_labellingW => [lbl /eqP lblP] /=.
by apply/forallP => j'; rewrite lblP tnth_map.
Qed.

(* If [s] is unique, then the [labelling_singleton] axiom is, in fact, a lemma for 
   inhabited [T]. For auctions, bids are generally supposed to be distinct; otherwise, 
   a random choice is usually performed among winners with equal bids. *)

Axiom labelling_singleton : singleton is_labelling.

Lemma labelling_singleton' (x0 : T) (u : uniq s) :
  singleton is_labelling.
Proof.
move: u => /uniqP u l1 l2 /eqP eqs1 /eqP.
rewrite eqs1 => /eqP eqs.
apply: eq_from_tnth => j.
apply/val_inj/(u x0) => /=; rewrite ?size_tuple ?inE ?ltn_ord //.  
rewrite -!tnth_nth -(tuple_of_tnth l1) -(tuple_of_tnth l2) in eqs *.
rewrite -(inj_eq val_inj) /= -!map_comp -enumT in eqs. 
pose f l := (([eta tnth s] \o [eta tnth l]) \o id).
have/(_ j) /=: forall k, f l1 k = f l2 k.
  move=> k.
  by rewrite (iffRL (eq_in_map (f l1) (f l2) (enum 'I_n))) ?mem_enum //; exact/eqP.
by rewrite !tnth_map !tnth_ord_tuple.
Qed.

Lemma uniq_labelling : projT1 exists_labellingW = tlabel.
Proof.  
apply: labelling_singleton; last by exact tlabelP. 
move: exists_labellingW => [lab islab].
exact: islab.
Qed.

(* If [s] is unique, then the [labelling_inj] axiom is, in fact, a lemma for inhabited [T]
   (see above). *)

Axiom labelling_inj : forall l, is_labelling l -> injective (tnth l).

Lemma labelling_inj' (x0 : T) (u : uniq s) :
  forall l, is_labelling l -> injective (tnth l).
Proof.
move=> l isl.  
have -> : l = tlabel by apply: labelling_singleton => //; exact: tlabelP.
rewrite -(sort_uniq r) in u.
move/(uniqP x0): u.
rewrite !size_sort !size_tuple /= => u j1 j2 eqtn.
apply/val_inj/u; rewrite ?inE ?ltn_ord -?tnth_nth //.
move: labellingP; rewrite /labelling_spec => /forallP f. 
move: (f j1) (f j2) => /eqP -> /eqP ->.
by rewrite uniq_labelling eqtn.
Qed.

Lemma labelling_onto l (islab : is_labelling l) i : 
  {i' | tnth l i' == i}.
Proof.
apply: sigW. 
pose p := perm (labelling_inj islab).
have/codomP [i'->]: i \in codom p by move/(_ i): (perm_onto p); rewrite inE.
by exists i'; rewrite permE.
Qed.

Lemma sorted_diff_agent_spec_ex (i : 'I_n) :
  {i' | tnth tlabel i' = i}.
Proof.
by have [i' H] := labelling_onto tlabelP i; exists i'; apply/eqP.
Qed.

(** [idxa bs i] returns the position of an agent relative to its bid.
 Note we could make positions and agents different, the current type
 seems a bit weird. *)

Definition idxa (i : 'I_n) : 'I_n := sval (sorted_diff_agent_spec_ex i).

Lemma cancel_idxa : cancel idxa (tnth tlabel).
Proof.
rewrite /idxa /sval => j.
by case: sorted_diff_agent_spec_ex => j' <-.
Qed.

Lemma cancel_inv_idxa : cancel (tnth tlabel) idxa.
Proof.
rewrite /idxa => j'.
case: sorted_diff_agent_spec_ex => j''.
apply: labelling_inj.
exact: tlabelP.
Qed.

Lemma cancel_inv_map_idxa m (t : m.-tuple 'I_n)  :
  map_tuple idxa (map_tuple (tnth tlabel) t) = t.
Proof. apply: eq_from_tnth => j; by rewrite !tnth_map cancel_inv_idxa. Qed.

Lemma labelling_spec_idxa j : tnth s' (idxa j) = tnth s j.
Proof.
move: labellingP.
rewrite /labelling_spec => /forallP /(_ (idxa j)) /eqP ->.
congr tnth.
have <- : tlabel = projT1 exists_labellingW.
  move: exists_labellingW => [l'' p''] /=.
  by rewrite (labelling_singleton p'' tlabelP).
by rewrite cancel_idxa.
Qed.

Lemma idxa_inj : injective idxa.
Proof.
move=> i1 i2.
rewrite /idxa /sval.
case: sorted_diff_agent_spec_ex => x1 <-.
by case: sorted_diff_agent_spec_ex => x2 <- ->.
Qed.

Lemma labelling_in k (t : k.-tuple 'I_n) j : 
  (idxa j \in t) = (j \in map_tuple (tnth tlabel) t). 
Proof. by rewrite -(mem_map (labelling_inj tlabelP)) cancel_idxa. Qed.

Lemma uniq_from_idxa k (o : k.-tuple 'I_n) (ut : uniq o) :
  uniq (map_tuple (tnth tlabel) o).
Proof.
rewrite -(map_inj_uniq idxa_inj) -map_comp. 
have/eqP: map_tuple (idxa \o tnth tlabel) o = o.
  apply: @eq_from_tnth => j.
  by rewrite tnth_map /= cancel_inv_idxa.
by rewrite -(inj_eq val_inj) => /= /eqP ->.
Qed.

Lemma uniq_to_idxa k (o : k.-tuple 'I_n) : 
  uniq o -> uniq (map_tuple idxa o).
Proof. by move=> ouniq; rewrite map_inj_uniq //= => i1 i2 /idxa_inj. Qed.

(* [idxa] of agent [i], for a uniq tuple [s], is the index of [i] in the sorted [s]. *)

Lemma idxa_as_index (x0 : T) (us : uniq s) i : idxa i = index (tnth s i) s' :> nat.
Proof.
rewrite /idxa /sval.
case: sorted_diff_agent_spec_ex =>  j <-.
rewrite -labelling_spec_idxa cancel_inv_idxa.
by rewrite (tnth_nth x0) index_uniq // ?size_sort ?size_tuple ?ltn_ord // sort_uniq.
Qed.

Definition labelling_id : labelling := ord_tuple n.

Lemma sorted_tlabel (ss : sorted r s) (tr : transitive r) : tlabel = labelling_id.
Proof.
have islid: is_labelling labelling_id.
  apply/eqP.
  apply: eq_from_tnth => j.
  rewrite tnth_mktuple.
  congr tnth.
  apply/val_inj => /=.
  exact: sorted_sort.
apply: labelling_singleton; last exact: islid.
exact: tlabelP.
Qed.

Lemma idxaK (ss : sorted r s) (tr : transitive r) i : idxa i = i.
Proof.
pose ip := @sorted_diff_agent_spec_ex i.
rewrite -(projT2 ip) /idxa /sval.
case: sorted_diff_agent_spec_ex => j <-.
by rewrite sorted_tlabel // ?tnth_ord_tuple.
Qed.

End Labelling.

Section Tperm.

Variables (n : nat) (T : eqType) (r : rel T) (s : n.+1.-tuple T).

Variable (uniq_bids : uniq s).

Notation idxa := (idxa r).
Notation x0 := (tnth s ord0).

Variable (totr : total r) (asymr : antisymmetric r) (trs : transitive r).

Lemma idxa_perm (p : 'S_n.+1) i : idxa ([tuple tnth s (p i)  | i < n.+1]) i = idxa s (p i). 
Proof.
apply: val_inj => /=. 
rewrite !(idxa_as_index r x0) /= ?uniq_bids //. 
- rewrite tnth_map tnth_ord_tuple.
  congr index. 
  apply/perm_sortP/tuple_permP => //.
  by exists p.
- rewrite map_inj_in_uniq ?enum_uniq // => j1 j2 in1 in2 /(tuple_uniqP x0).
  by move/(_ uniq_bids)/perm_inj.
Qed.

Notation "[ 'swap' s | i1 , i2 ]" := 
  ([tuple tnth s (tperm i1 i2 i)  | i < n.+1]) (at level 0).

Variable (i1 i2 : 'I_n.+1).

Lemma idxa_tpermL : idxa [swap s | i1 , i2] i1 = idxa s i2. 
Proof. by rewrite idxa_perm tpermL. Qed.

Lemma idxa_tpermR : idxa [swap s | i1 , i2] i2 = idxa s i1.
Proof. by rewrite idxa_perm tpermR. Qed.

Lemma idxa_tpermD i (ne1 : i != i1) (ne2 : i != i2) : idxa [swap s | i1, i2] i = idxa s i.
Proof. by rewrite idxa_perm tpermD 1?eq_sym. Qed.

End Tperm.

Section DifferOn.

Variables (n : nat) (T : eqType) (r : rel T) (i : 'I_n.+1) (s s' : n.+1.-tuple T).

Variable transitive_r : transitive r.
Variable reflexive_r : reflexive r.
Variable total_r : total r.
Variable antisymmetric_r : antisymmetric r.

Notation t := ([tuple of sort r s]).
Notation t' := ([tuple of sort r s']).

Variable (differ_on : forall j, j != i -> tnth s' j = tnth s j).

Notation ix := (idxa r s i).
Notation ix' := (idxa r s' i).

Definition lt_index j := if j == ix' then ix else if ix' < j <= ix then ord_pred j else j.

Definition lt_labelling l : labelling n.+1 := [tuple tnth l (lt_index j) | j < n.+1].

Lemma labelling_differ_on_lt l :
  ix' < ix -> is_labelling r s l -> is_labelling r s' (lt_labelling l).
Proof.
Admitted.

Definition ge_index j := 
  if j == ix' then ix else if ix <= j < ix' then ord_succ j else j.

Definition ge_labelling l : labelling n.+1 := [tuple tnth l (ge_index j) | j < n.+1].

Lemma labelling_differ_on_ge l :
  ix <= ix' -> is_labelling r s l -> is_labelling r s' (ge_labelling l).
Proof.
Admitted.

Lemma labelling_differ_on_eq l :
  ix' = ix -> is_labelling r s l -> is_labelling r s' l.
Proof.
move=> eqii' isl. 
have <- : ge_labelling l = l.
  apply: eq_from_tnth => j.
  rewrite /ge_labelling /ge_index tnth_mktuple eqii'.
  case: ifP => [/eqP -> |_]; last by rewrite ifF // leqNgt andNb.
  have -> : l = tlabel r s.
    apply: (@labelling_singleton _ _ r s) => //.
    by exact: tlabelP. 
  by rewrite cancel_idxa.
apply: labelling_differ_on_ge => //=.
by rewrite leq_eqVlt eq_sym eqii' eq_refl orTb.
Qed.

End DifferOn.

(* Not used anymore. Keeping it for reference.

Import Order.Theory.

Module IdxOrder.

Section IdxOrder.

Variables (n : nat) (T : eqType) (r : rel T) (s : n.+1.-tuple T).

Notation ix := (ix r s).

Definition le i1 i2 := ix i1 <= ix i2.
Definition lt i1 i2 := ix i1 < ix i2.

Lemma ix_inj: injective (fun j => val (ix j)). 
Proof. by move=> j1 j2 /val_inj/ix_inj. Qed.

Lemma le_refl : reflexive le.
Proof. by move=> x; rewrite /le. Qed.

Lemma le_anti : antisymmetric le.
Proof.  
move=> x y /andP [].
rewrite /le leq_eqVlt => /orP [/eqP/ix_inj //|ltxy].
rewrite leq_eqVlt => /orP [/eqP/ix_inj //|/ltnW].
by rewrite leqNgt ltxy.
Qed.

Lemma le_trans : transitive le. 
Proof. move=> y x z; exact: leq_trans. Qed.

Lemma ltNeq x y : lt x y = (y != x) && le x y.
Proof.
rewrite /lt /le [in RHS]leq_eqVlt andb_orr.
by rewrite -(inj_eq ix_inj) eq_sym /= andNb orFb andb_idl // => /ltn_eqF ->.
Qed.

Lemma le_total x y : le x y || le y x. 
Proof. by rewrite leq_total. Qed.

Definition orderMixin := LeOrderMixin ltNeq (fun _ _ => erefl) (fun _ _ => erefl)
                                      le_anti le_trans le_total.

Definition bot_idx := tnth (tlabel r s) ord0.

Notation A := 'I_n.+1.

Lemma ord0bot (x : A) : le bot_idx x.
Proof. by rewrite /le cancel_inv_ix /= leq0n. Qed.

Canonical porderType := POrderType tt A orderMixin.
Canonical latticeType := LatticeType A orderMixin.
Canonical bLatticeType := BLatticeType A (BottomMixin ord0bot).
Canonical distrLatticeType := DistrLatticeType A orderMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of A].
Canonical orderType := OrderType A orderMixin.
Canonical finPOrderType := [finPOrderType of A].

Lemma ltEnat (i1 i2 : A) : lt i1 i2 = (ix i1 < ix i2)%nat.
Proof. by []. Qed.

Lemma leEnat (i1 i2 : A) : le i1 i2 = (ix i1 <= ix i2)%nat.
Proof. by []. Qed.

(*

Lemma minEnat : min = minn. 

Lemma maxEnat : max = maxn. 

*)

Lemma botEnat : 0%O = 0%N :> nat. Proof. by []. Qed.

End IdxOrder.

End IdxOrder.

*)

