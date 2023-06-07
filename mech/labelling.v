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

Variables (n : nat) (T : eqType) (r : rel T)  (s : n.+1.-tuple T).

Variable (tr : transitive r) (rr : reflexive r) (totr : total r) (ar : antisymmetric r).

(* Should be a perm (see [labelling_inj]). EJGA: not necessarily tho *)
Definition labelling := n.+1.-tuple 'I_n.+1.

Implicit Types (l : labelling).

Let ri := [rel i1 i2 | r (tnth s i1) (tnth s i2)].

Lemma ri_tr : transitive ri.
Proof. by move=> x y z /=; exact: tr. Qed.

Lemma ri_rr : reflexive ri.
Proof. by move=> x /=; exact: rr. Qed.

Lemma ri_tot : total ri.
Proof. by move=> x y /=; exact: totr. Qed.

Let ri_lex := [rel i1 i2 | ri i1 i2 && (ri i2 i1 ==> (i1 <= i2))].

Lemma ri_lex_tr : transitive ri_lex.  
Proof.
move=> x y z /= => /andP [ryx /implyP yx] /andP [rxz /implyP xz].
have ryz: r (tnth s y) (tnth s z)  by rewrite (@tr (tnth s x)) // andTb.
rewrite ryz andTb.
apply/implyP => rzy.
rewrite (@leq_trans x) //.
- by rewrite yx //; move: (@ri_tr z x y) => //= ->.
- by rewrite xz //; move: (@ri_tr y z x) => //= ->.
Qed.

Lemma ri_lex_rr : reflexive ri_lex.  
Proof. by move=> x /=; rewrite rr leqnn. Qed.

Lemma ri_lex_as : antisymmetric ri_lex.  
Proof.
move=> x y /= => /andP [/andP [xy /implyP rxy]] /andP [yx /implyP ryx].
apply: val_inj => /=; apply/eqP.
by rewrite eqn_leq rxy // ryx.
Qed.

Lemma ri_lex_tot : total ri_lex. 
Proof.
move=> x y /=.   
wlog: x y / x <= y. 
  move: (leq_total x y) => /orP [xy /(_ x y) -> //|yx /(_ y x)].
  by rewrite orbC => ->.
rewrite leq_eqVlt => /orP [/eqP xy|xy].
- move: (ri_rr y) => /=. 
  have -> /= : x = y by apply/val_inj.
  move=> ->.
  by rewrite eq_refl !orTb.
- move: (ri_tot x y) => /= /orP [->|ryx]. 
  - apply/orP; left.
    rewrite xy andTb orbT.
    exact/implyP.
  - rewrite ryx xy. 
    case: (r (tnth s x) (tnth s y)) => //=.
    by rewrite orbT orTb.
Qed.      

Let l0 := [tuple of sort ri_lex (ord_tuple n.+1)].

Let s' := [tuple of sort r s]. 

Definition is_labelling l := (s' == [tuple of [seq tnth s i | i <- l]]) && (l == l0).

(* Labelling specs. *)

Lemma labelling_singleton : singleton is_labelling.
Proof. by move=> l1 l2 /andP [_ /eqP ->] /andP [_ /eqP ->]. Qed.

Definition x0 : 'I_n.+1 := locked ord0. 

Lemma labelling_inj : forall l, is_labelling l -> injective (tnth l).
Proof.
move=> l /andP [/eqP ss' /eqP sl] x y. 
rewrite !(tnth_nth x0) => eqnth. 
apply: val_inj => /=.
have/(_ x y) //: {in gtn (size l) &, injective (nth x0 l)}. 
  apply/uniqP => /=. 
  by rewrite -(@perm_uniq _ (enum 'I_n.+1)) ?enum_uniq // sl /= perm_sym perm_sort perm_refl.
by rewrite !inE !size_tuple => /(_ (ltn_ord x) (ltn_ord y) eqnth).
Qed.

Lemma exists_labelling : exists l, is_labelling l.
Proof. 
exists l0. 
rewrite /is_labelling eq_refl -(inj_eq val_inj) /= andbT.
apply/eqP.
apply: (@sorted_eq _ r). 
- exact: tr.
- exact: ar.
- exact: sort_sorted.
- rewrite sorted_map. 
  have srx : subrel ri_lex (relpre [eta tnth s] r) by move=> x y /andP [].
  move: (@sub_sorted _ ri_lex ri srx) => /(_ (sort ri_lex (enum 'I_n.+1))) -> //. 
  rewrite sort_sorted //. 
  exact: ri_lex_tot.
rewrite (@perm_trans _ s) ?perm_sort ?perm_refl //.
by rewrite -map_tnth_enum perm_map // perm_sym perm_sort perm_refl.
Qed.

(* Constructive version *)
Lemma exists_labellingW : { l : n.+1.-tuple 'I_n.+1 | is_labelling l}.
Proof. apply: sigW; exact: exists_labelling. Qed.

(* Labelling for a sort operation *)
Definition tlabel : labelling := xchoose exists_labelling.

Lemma tlabelP : is_labelling tlabel.
Proof. exact: xchooseP exists_labelling. Qed.

Definition labelling_spec l : bool :=
  [forall j' : 'I_n.+1, tnth s' j' == tnth s (tnth l j')].

Lemma labellingP : labelling_spec (projT1 exists_labellingW).
Proof.
case: exists_labellingW => [lbl /eqP] /=. 
rewrite eqb_id => /andP [/eqP lblP _].
by apply/forallP => j; rewrite lblP tnth_map.
Qed.

Lemma uniq_labelling : projT1 exists_labellingW = tlabel.
Proof.  
apply: labelling_singleton; last by exact tlabelP. 
move: exists_labellingW => [lab islab].
exact: islab.
Qed.

Lemma labelling_onto l (islab : is_labelling l) i : {i' | tnth l i' == i}.
Proof.
apply: sigW. 
pose p := perm (labelling_inj islab).
have/codomP [i'->]: i \in codom p by move/(_ i): (perm_onto p); rewrite inE.
by exists i'; rewrite permE.
Qed.

Lemma sorted_diff_agent_spec_ex (i : 'I_n.+1) : {i' | tnth tlabel i' = i}.
Proof.
by have [i' H] := labelling_onto tlabelP i; exists i'; apply/eqP.
Qed.

(** [idxa bs i] returns the position of an agent relative to its bid.
 Note we could make positions and agents different, the current type
 seems a bit weird. *)

Definition idxa (i : 'I_n.+1) : 'I_n.+1.
by have [i' _] := sorted_diff_agent_spec_ex i; exact: i'.
Defined.

Lemma cancel_idxa : cancel idxa (tnth tlabel).
Proof.
rewrite /idxa /sval => j.
by case: sorted_diff_agent_spec_ex => j' <-.
Qed.

Lemma cancel_inv_idxa : cancel (tnth tlabel) idxa.
Proof.
rewrite /idxa /sval => j'.
case: sorted_diff_agent_spec_ex => j''.
apply: labelling_inj.
exact: tlabelP.
Qed.

Lemma cancel_inv_map_idxa m (t : m.-tuple 'I_n.+1)  :
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

Definition t0 := locked (tnth s ord0).

Lemma idxa_eq_mon (i j : 'I_n.+1) :
  tnth s i = tnth s j -> idxa i <= idxa j -> i <= j.
Proof.
move=> sisj ixij. 
have sl0: sorted ri_lex tlabel.
  move: tlabelP => /andP [_ /eqP ->].
  rewrite sort_sorted //.
  exact: ri_lex_tot.
move: (@sorted_leq_nth _ _ ri_lex_tr ri_lex_rr ord0 tlabel sl0 (idxa i) (idxa j)).
rewrite !inE size_tuple !ltn_ord => /(_ erefl erefl ixij). 
rewrite -!tnth_nth !cancel_idxa.
by rewrite /ri_lex /= sisj rr implyTb.
Qed.

Lemma idxa_inj : injective idxa.  
Proof.
move=> i1 i2.
rewrite /idxa /sval /=.  
case: sorted_diff_agent_spec_ex => x1 <-.
by case: sorted_diff_agent_spec_ex => x2 <- ->.
Qed.

Lemma labelling_in k (t : k.-tuple 'I_n.+1) j : 
  (idxa j \in t) = (j \in map_tuple (tnth tlabel) t). 
Proof. by rewrite -(mem_map (labelling_inj tlabelP)) cancel_idxa. Qed.

Lemma uniq_from_idxa k (o : k.-tuple 'I_n.+1) (ut : uniq o) :
  uniq (map_tuple (tnth tlabel) o).
Proof.
rewrite -(map_inj_uniq idxa_inj) -map_comp. 
have/eqP: map_tuple (idxa \o tnth tlabel) o = o.
  apply: (@eq_from_tnth) => j.
  by rewrite tnth_map /= cancel_inv_idxa.
by rewrite -(inj_eq val_inj) => /= /eqP ->.
Qed.

Lemma uniq_to_idxa k (o : k.-tuple 'I_n.+1) : 
  uniq o -> uniq (map_tuple idxa o).
Proof. by move=> ouniq; rewrite map_inj_uniq //= => i1 i2 /idxa_inj. Qed.

Definition labelling_id : labelling := ord_tuple n.+1.

Lemma sorted_tlabel (ss : sorted r s) : tlabel = labelling_id.
Proof.
move: tlabelP => /andP [_ /eqP ->].
apply: eq_from_tnth => j.
rewrite tnth_ord_tuple (tnth_nth x0) /= sorted_sort ?nth_ord_enum //.
exact: ri_lex_tr.
rewrite sorted_pairwise; last by exact: ri_lex_tr.
apply/(pairwiseP x0) => x y ltx lty xy /=.
rewrite size_enum_ord !inE in ltx lty.
rewrite !(@tnth_nth _ _ t0) !nth_enum_ord ?xy ?implybT ?andbT //.
move: ss.
rewrite sorted_pairwise; last by exact: tr.
move/(@pairwiseP _ r t0 (val s))/(_ x y) => /=.
by rewrite size_tuple !inE (ltnW xy) /= implybT andbT => ->.
Qed.

Lemma idxaK (ss : sorted r s) i : idxa i = i.
Proof.
pose ip := (@sorted_diff_agent_spec_ex i). 
rewrite -(projT2 ip) /idxa /sval.
case: sorted_diff_agent_spec_ex => j <-.
by rewrite sorted_tlabel // ?tnth_ord_tuple.
Qed.

End Labelling.

Section DifferOn.

Variables (n : nat) (T : eqType) (r : rel T) (i : 'I_n.+1) (s s' : n.+1.-tuple T).

Variable tr : transitive r.
Variable rr : reflexive r.
Variable totr : total r.
Variable ar : antisymmetric r.

Variable (differ_on : forall j, j != i -> tnth s' j = tnth s j).

Notation ix := (@idxa _ _ r s tr rr totr ar i).
Notation ix' := (@idxa _ _ r s' tr rr totr ar i).

Definition lt_index j := if j == ix' then ix else if ix' < j <= ix then ord_pred j else j.

Definition lt_labelling l : labelling n := [tuple tnth l (lt_index j) | j < n.+1].

Lemma labelling_differ_on_lt l :
  ix' < ix -> is_labelling r s l -> is_labelling r s' (lt_labelling l).
Proof.
Admitted.

Definition ge_index j := 
  if j == ix' then ix else if ix <= j < ix' then ord_succ j else j.

Definition ge_labelling l : labelling n := [tuple tnth l (ge_index j) | j < n.+1].

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
  have -> : l = tlabel s tr rr totr ar 
    by apply: (@labelling_singleton _ _ r s) => //; exact: tlabelP.
  by rewrite cancel_idxa.
apply: labelling_differ_on_ge => //=.
by rewrite leq_eqVlt eq_sym eqii' eq_refl orTb.
Qed.

End DifferOn.

Section Tperm.

Variables (n : nat) (T : eqType) (r : rel T) (s : n.+1.-tuple T).

Variable (u : uniq s).

Variable tr : transitive r.
Variable rr : reflexive r.
Variable totr : total r.
Variable ar : antisymmetric r.
 
Notation x0 := (tnth s ord0).
Notation idxa s i := (@idxa _ _ r s tr rr totr ar i).

Notation ss p := ([tuple tnth s (p i)  | i < n.+1]).

Lemma idxa_as_index (s' : n.+1.-tuple T) (u' : uniq s') i : 
  idxa s' i = index (tnth s' i) (sort r s') :> nat.
Proof.
rewrite /sval.
case: (@sorted_diff_agent_spec_ex _ _ r s' tr rr totr ar i) =>  j <-.
rewrite -(@labelling_spec_idxa _ _ r) cancel_inv_idxa.
by rewrite (tnth_nth x0) index_uniq // ?size_sort ?size_tuple ?ltn_ord // sort_uniq.
Qed.

Lemma us (p : 'S_n.+1) : uniq (ss p).
Proof.
rewrite map_inj_uniq /= ?enum_uniq // => j1 j2 /eqP. 
rewrite (tnth_uniq x0) // => /eqP.
exact: perm_inj.
Qed.

Lemma idxa_perm (p : 'S_n.+1) i : idxa (ss p) i = idxa s (p i).
Proof.
apply: val_inj => /=. 
rewrite (@idxa_as_index (ss p) (us p)) (@idxa_as_index s u).
rewrite tnth_map tnth_ord_tuple.
congr index. 
apply/perm_sortP/tuple_permP => //.
by exists p.
Qed.

Variable (i1 i2 : 'I_n.+1).

Lemma idxa_tpermL : idxa (ss (tperm i1 i2)) i1 = idxa s i2. 
Proof. by rewrite idxa_perm tpermL. Qed. 

Lemma idxa_tpermR : idxa (ss (tperm i1 i2)) i2 = idxa s i1.
Proof. by rewrite idxa_perm tpermR. Qed.

Lemma idxa_tpermD i (ne1 : i != i1) (ne2 : i != i2) : 
  idxa (ss (tperm i1 i2)) i = idxa s i.
Proof. by rewrite idxa_perm tpermD 1?eq_sym. Qed. 

End Tperm.



