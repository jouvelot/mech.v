(** 

  labelling.v

  Lemmas about labelling, for bid ordering management.

  Licence: CeCILL-B.

*)

From Coq Require Import Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp.fingroup Require Import perm.

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

Definition is_labelling l := s' == [tuple of [seq tnth s i | i <- l]].

Axiom labelling_inj : forall l, is_labelling l -> injective (tnth l).

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

Lemma labelling_onto l (islab : is_labelling l) i : {i' | tnth l i' == i}.
Proof.
apply: sigW.
pose p := perm (labelling_inj islab).
have/codomP: i \in codom p.
  move/(_ i): (perm_onto p).
  by rewrite inE.
move=> [i'] ->.
by exists i'; rewrite permE.
Qed.

Axiom labelling_singleton : singleton is_labelling.

Lemma uniq_labelling : projT1 exists_labellingW = tlabel.
Proof.  
apply: labelling_singleton.
move: exists_labellingW => [lab islab].
exact: islab.
exact tlabelP. 
Qed.

Lemma sorted_diff_agent_spec_ex (i : 'I_n) :
  {i' | tnth tlabel i' = i}.
Proof.
by have [i' H] := labelling_onto tlabelP i; exists i'; apply/eqP.
Qed.

(** [idxa bs i] returns the position of an agent relative to its bid.
 Note we could make positions and agents different, the current type
 seems a bit weird. *)

Definition idxa (i : 'I_n) : 'I_n.
by have [i' _] := sorted_diff_agent_spec_ex i; exact: i'.
Defined.

Lemma cancel_idxa : cancel idxa (tnth tlabel).
Proof.
rewrite /idxa /ssr_have => j.
by case: sorted_diff_agent_spec_ex => j' <-.
Qed.

Lemma cancel_inv_idxa : cancel (tnth tlabel) idxa.
Proof.
rewrite /idxa /ssr_have => j'.
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
rewrite cancel_idxa //.
Qed.

Lemma idxa_inj : injective idxa.  
Proof.
move=> i1 i2.
rewrite /idxa /ssr_have /=. 
case: sorted_diff_agent_spec_ex => x1 <-.
case: sorted_diff_agent_spec_ex => x2 <-.
by move=> ->.
Qed.

Lemma labelling_in k (t : k.-tuple 'I_n) j : 
  (idxa j \in t) = (j \in map_tuple (tnth tlabel) t). 
Proof. by rewrite -(mem_map (labelling_inj tlabelP)) cancel_idxa. Qed.

Lemma uniq_from_idxa k (o : k.-tuple 'I_n) (ut : uniq o) :
  uniq (map_tuple (tnth tlabel) o).
Proof.
rewrite -(map_inj_uniq idxa_inj) -map_comp.
have/eqP: map_tuple (idxa \o tnth tlabel) o = o.
  apply: (@eq_from_tnth) => j.
  by rewrite tnth_map /= cancel_inv_idxa.
by rewrite -(inj_eq val_inj) => /= /eqP ->.
Qed.

Lemma uniq_to_idxa k (o : k.-tuple 'I_n) : 
  uniq o -> uniq (map_tuple idxa o).
Proof. by move=> ouniq; rewrite map_inj_uniq //= => i1 i2 /idxa_inj. Qed.

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
apply: labelling_singleton.
apply: tlabelP.

exact: islid.
Qed.

Lemma idxaK (ss : sorted r s) (tr : transitive r) i : idxa i = i.
Proof.
pose ip := (@sorted_diff_agent_spec_ex i). 
rewrite -(projT2  ip) /idxa /ssr_have.
case: sorted_diff_agent_spec_ex => j <-.
by rewrite sorted_tlabel // ?tnth_ord_tuple.
Qed.

End Labelling.

Section DifferOn.

Variables (n : nat) (T : eqType) (r : rel T) (i : 'I_n.+1) (s s' : n.+1.-tuple T).

Variable (differ_on : forall j, j != i -> tnth s' j = tnth s j).

Notation idxa' := (idxa r s' i).
Notation idxa := (idxa r s i).

Definition lt_index j := 
  if j == idxa' then idxa else if idxa' < j <= idxa then ord_pred j else j.

Definition lt_labelling l : labelling n.+1 := 
  [tuple tnth l (lt_index j) | j < n.+1].

Lemma labelling_differ_on_lt l :
  idxa' < idxa -> is_labelling r s l -> is_labelling r s' (lt_labelling l).
Proof.
Admitted.

Definition ge_index j := 
  if j == idxa' then idxa else if idxa <= j < idxa' then ord_succ j else j.

Definition ge_labelling l : labelling n.+1 := [tuple tnth l (ge_index j) | j < n.+1].

Lemma labelling_differ_on_ge l :
  idxa <= idxa' -> is_labelling r s l -> is_labelling r s' (ge_labelling l).
Proof.
Admitted.

Lemma labelling_differ_on_eq l :
  idxa' = idxa -> is_labelling r s l -> is_labelling r s' l.
Proof.
move=> eqii' isl.
have <- : ge_labelling l = l.
  apply: eq_from_tnth => j.
  rewrite /ge_labelling /ge_index tnth_mktuple eqii'.
  case: ifP => [/eqP -> |_].
  - have -> : l = tlabel r s by apply: (@labelling_singleton _ _ r s) => //; exact: tlabelP.
    by rewrite cancel_idxa.
  - by rewrite ifF // leqNgt andNb.
apply: labelling_differ_on_ge => //=.
by rewrite leq_eqVlt eq_sym eqii' eq_refl orTb.
Qed.

End DifferOn.

(* Not used anymore. Keeping it for reference.

Import Order.Theory.

Module IdxOrder.

Section IdxOrder.

Variables (n : nat) (T : eqType) (r : rel T) (s : n.+1.-tuple T).

Notation idxa := (idxa r s).

Definition le i1 i2 := idxa i1 <= idxa i2.
Definition lt i1 i2 := idxa i1 < idxa i2.

Lemma idxa_inj: injective (fun j => val (idxa j)). 
Proof. by move=> j1 j2 /val_inj/idxa_inj. Qed.

Lemma le_refl : reflexive le.
Proof. by move=> x; rewrite /le. Qed.

Lemma le_anti : antisymmetric le.
Proof.  
move=> x y /andP [].
rewrite /le leq_eqVlt => /orP [/eqP/idxa_inj //|ltxy].
rewrite leq_eqVlt => /orP [/eqP/idxa_inj //|/ltnW].
by rewrite leqNgt ltxy.
Qed.

Lemma le_trans : transitive le. 
Proof. move=> y x z; exact: leq_trans. Qed.

Lemma ltNeq x y : lt x y = (y != x) && le x y.
Proof.
rewrite /lt /le [in RHS]leq_eqVlt andb_orr.
by rewrite -(inj_eq idxa_inj) eq_sym /= andNb orFb andb_idl // => /ltn_eqF ->.
Qed.

Lemma le_total x y : le x y || le y x. 
Proof. by rewrite leq_total. Qed.

Definition orderMixin := LeOrderMixin ltNeq (fun _ _ => erefl) (fun _ _ => erefl)
                                      le_anti le_trans le_total.

Definition bot_idx := tnth (tlabel r s) ord0.

Notation A := 'I_n.+1.

Lemma ord0bot (x : A) : le bot_idx x.
Proof. by rewrite /le cancel_inv_idxa /= leq0n. Qed.

Canonical porderType := POrderType tt A orderMixin.
Canonical latticeType := LatticeType A orderMixin.
Canonical bLatticeType := BLatticeType A (BottomMixin ord0bot).
Canonical distrLatticeType := DistrLatticeType A orderMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of A].
Canonical orderType := OrderType A orderMixin.
Canonical finPOrderType := [finPOrderType of A].

Lemma ltEnat (i1 i2 : A) : lt i1 i2 = (idxa i1 < idxa i2)%nat.
Proof. by []. Qed.

Lemma leEnat (i1 i2 : A) : le i1 i2 = (idxa i1 <= idxa i2)%nat.
Proof. by []. Qed.

(*

Lemma minEnat : min = minn. 

Lemma maxEnat : max = maxn. 

*)

Lemma botEnat : 0%O = 0%N :> nat. Proof. by []. Qed.

End IdxOrder.

End IdxOrder.

*)

