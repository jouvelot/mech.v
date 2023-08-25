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

Let l_lex := [tuple of sort ri_lex (ord_tuple n.+1)].

Let s' := [tuple of sort r s]. 

Theorem sorted_lex_labelling : s' = [tuple of [seq tnth s i | i <- l_lex]].
Proof.
apply/val_inj => /=.
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

Definition is_labelling l := (s' == [tuple of [seq tnth s i | i <- l]]) && (l == l_lex).

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
Proof. by exists l_lex; rewrite /is_labelling sorted_lex_labelling !eq_refl. Qed.

Lemma is_labelling_lex : s' = [tuple of [seq tnth s i | i <- l_lex]].
Proof. by have [l] := exists_labelling => /andP [/eqP eqs /eqP <-]. Qed.

(* Constructive version *)
Lemma exists_labellingW : { l : n.+1.-tuple 'I_n.+1 | is_labelling l}.
Proof. apply: sigW; exact: exists_labelling. Qed.

(* Labelling for a sort operation *)
Definition tlabel : labelling := xchoose exists_labelling.

Lemma tlabelP : is_labelling tlabel.
Proof. exact: xchooseP exists_labelling. Qed.

Definition labelling_spec l : bool := [forall j' : 'I_n.+1, tnth s' j' == tnth s (tnth l j')].

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

Lemma perm_labelling (l : labelling) : 
  is_labelling l -> perm_eq [seq tnth l j | j <- enum 'I_n.+1] (enum 'I_n.+1).
Proof. 
move=> /andP [_ /eqP ->].
by rewrite map_tnth_enum perm_sort perm_refl.
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

Lemma idxa_as_index (u : uniq s) i : idxa i = index (tnth s i) s' :> nat.
Proof.
rewrite /sval.
case: (sorted_diff_agent_spec_ex i) =>  j <-.
rewrite -labelling_spec_idxa cancel_inv_idxa.
by rewrite (tnth_nth t0) index_uniq // ?size_sort ?size_tuple ?ltn_ord // sort_uniq.
Qed.

Lemma sorted_lex_tlabel: sorted ri_lex tlabel.
Proof. by move: tlabelP => /andP [_ /eqP ->]; rewrite sort_sorted //; exact: ri_lex_tot. Qed.

Lemma tnth_mon_idxa j1 j2 : idxa j1 <= idxa j2 -> r (tnth s j1) (tnth s j2).
Proof.
move=> j1j2.
move: (@sorted_leq_nth _ _ ri_lex_tr ri_lex_rr ord0 tlabel sorted_lex_tlabel (idxa j1) (idxa j2)).
rewrite !inE size_tuple !ltn_ord => /(_ erefl erefl j1j2). 
by rewrite -!tnth_nth !cancel_idxa /ri_lex /= => /andP [].
Qed.

Lemma idxa_eq_mon (i j : 'I_n.+1) :
  tnth s i = tnth s j -> idxa i <= idxa j -> i <= j.
Proof.
move=> sisj ixij.  
move: (@sorted_leq_nth _ _ ri_lex_tr ri_lex_rr ord0 tlabel sorted_lex_tlabel (idxa i) (idxa j)).
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

Section Update.

Variables (n : nat) (T : eqType) (r : rel T). 

Variable tr : transitive r.
Variable rr : reflexive r.
Variable totr : total r.
Variable ar : antisymmetric r.

Variable (i : 'I_n.+1) (s s' : n.+1.-tuple T).

Variable (differ_on : forall j, j != i -> tnth s' j = tnth s j).

Notation idxa s := (@idxa _ _ r s tr rr totr ar).
Notation ix := (idxa s i).
Notation ix' := (idxa s' i).

Lemma stable j :
  let: jx := idxa s j in 
  (jx < minn ix ix') || (maxn ix ix' < jx) -> idxa s' j = jx.
Admitted.

Lemma shift j (jx' : 'I_n.+1) (ge : bool): 
  let: jx := idxa s j in 
  let: sh := if ge then @ord_succ n else @ord_pred n.+1 in
  sh jx' = jx -> minn ix ix' < jx' + ge <= maxn ix ix' -> idxa s' j = jx'.
Admitted.

Section Lt.

Variable (ix'x : ix' < ix).

Lemma maxx : maxn ix ix' = val ix.
Proof. by apply/maxn_idPl; rewrite ltnW. Qed.

Lemma minx' : minn ix ix' = val ix'.
Proof. by apply/minn_idPr; rewrite ltnW. Qed.

Lemma lt_stable j : let: jx := idxa s j in (jx < ix') || (ix < jx) -> idxa s' j = jx.
 Proof. by rewrite -maxx -{1}minx'; exact: stable. Qed.

Lemma lt_shift j (jx' : 'I_n.+1) : 
  let: jx := idxa s j in 
  ord_pred jx' = jx -> ix' < jx' <= ix -> idxa s' j = jx'.
Proof. by move: (@shift j jx' false); rewrite minx' maxx addn0. Qed.

End Lt.

Section Ge.

Variable (ixx' : ix <= ix').

Lemma maxx' : maxn ix ix' = val ix'.
Proof. by apply/maxn_idPr. Qed.

Lemma minx : minn ix ix' = val ix.
Proof. by apply/minn_idPl. Qed.

Lemma ge_stable j : let: jx := idxa s j in (jx < ix) || (ix' < jx) -> idxa s' j = jx. 
Proof. by rewrite -maxx' -{1}minx; exact: stable. Qed.

Lemma ge_shift j (jx' : 'I_n.+1) : 
  let: jx := idxa s j in 
  ord_succ jx' = jx -> ix <= jx' < ix' -> idxa s' j = jx'.
Proof. by move: (@shift j jx' true); rewrite minx maxx' addn1 ltnS. Qed.

End Ge.

End Update.

Section DifferOn.

Variables (n : nat) (T : eqType) (r : rel T) (i : 'I_n.+1) (s s' : n.+1.-tuple T).

Variable tr : transitive r.
Variable rr : reflexive r.
Variable totr : total r.
Variable ar : antisymmetric r.

Variable (differ_on : forall j, j != i -> tnth s' j = tnth s j).

Notation idxa s := (@idxa _ _ r s tr rr totr ar).
Notation tlabel s := (@tlabel _ _ r s tr rr totr ar).

Variable (l : labelling n) (isl : is_labelling r s l). 

Notation ix := (idxa s i).
Notation ix' := (idxa s' i).

Section Lt.

Variable (ix'x : ix' < ix).

Lemma lt_stable_pre j (pre : idxa s j < ix') : idxa s' j = idxa s j.
Proof. by rewrite (lt_stable differ_on ix'x) // pre. Qed.

Lemma lt_stable_post j (post : ix < idxa s j) : idxa s' j = idxa s j.
Proof. by rewrite( lt_stable differ_on) // post orbT. Qed.

Definition lt_index jx := if jx == ix' then ix else if ix' < jx <= ix then ord_pred jx else jx.

Definition lt_labelling : labelling n := [tuple tnth l (lt_index jx) | jx < n.+1].

Lemma labelling_differ_on_lt : is_labelling r s' lt_labelling.
Proof.
move: isl => /andP [/eqP eqs /eqP]. 
rewrite /lt_labelling.
set ri := (X in sort X) => ->. 
rewrite /is_labelling andb_idl => [|/eqP ->]; last by rewrite sorted_lex_labelling. 
set ri' := (X in _ == [tuple of sort X _]). 
apply/eqP/eq_from_tnth => jx. 
rewrite /lt_labelling /lt_index tnth_map tnth_ord_tuple.
have -> : [tuple of sort ri (ord_tuple n.+1)] = tlabel s.
  apply: (@labelling_singleton _ _ r s); last by exact: tlabelP. 
  have := isl.
  by rewrite /is_labelling eqs !eq_refl andTb andbT => /eqP ->.
have -> : [tuple of sort ri' (ord_tuple n.+1)] = tlabel s'.
  apply: (@labelling_singleton _ _ r s'); last by exact: tlabelP.
  by rewrite /is_labelling eq_refl andbT is_labelling_lex.
have [/eqP ->|] := boolP (jx == ix'); first by rewrite !cancel_idxa. 
have [j smx]: exists j, idxa s j = jx by exists (tnth (tlabel s) jx); rewrite cancel_inv_idxa. 
rewrite neq_ltn => /orP [ljx'|lx'j].  
- rewrite ifF; last by rewrite ltnNge (ltnW ljx').  
  by rewrite -smx -[in RHS]lt_stable_pre ?cancel_idxa // smx. 
- rewrite lx'j andTb; case: ifP => [jxix|]; last first.
  - move=> b; have {b} ixjx: ix < jx by rewrite ltnNge; apply/negPf.
    by rewrite -smx -[in RHS]lt_stable_post ?cancel_idxa // smx.
  - have [pj smpx]: exists j, ord_pred jx = idxa s j.
      by exists (tnth (tlabel s) (ord_pred jx)); rewrite cancel_inv_idxa.
    by rewrite smpx -(lt_shift differ_on ix'x smpx) ?cancel_idxa // lx'j jxix. 
Qed.

End Lt.

Section Ge.

Variable (ix'x : ix <= ix').

Lemma ge_stable_pre j (pre : idxa s j < ix) : idxa s' j = idxa s j.
Proof. by rewrite (ge_stable differ_on ix'x) // pre. Qed.

Lemma ge_stable_post j (post : ix' < idxa s j) : idxa s' j = idxa s j.
Proof. by rewrite( ge_stable differ_on) // post orbT. Qed.

Definition ge_index j := 
  if j == ix' then ix else if ix <= j < ix' then ord_succ j else j.

Definition ge_labelling l : labelling n := [tuple tnth l (ge_index j) | j < n.+1].

Lemma labelling_differ_on_ge : is_labelling r s' (ge_labelling l).
Proof.
move: isl => /andP [/eqP eqs /eqP]. 
rewrite /lt_labelling.
set ri := (X in sort X) => ->. 
rewrite /is_labelling andb_idl => [|/eqP ->]; last by rewrite sorted_lex_labelling. 
set ri' := (X in _ == [tuple of sort X _]). 
apply/eqP/eq_from_tnth => jx. 
rewrite /ge_labelling /ge_index tnth_map tnth_ord_tuple.
have -> : [tuple of sort ri (ord_tuple n.+1)] = tlabel s.
  apply: (@labelling_singleton _ _ r s); last by exact: tlabelP. 
  have := isl.
  by rewrite /is_labelling eqs !eq_refl andTb andbT => /eqP ->.
have -> : [tuple of sort ri' (ord_tuple n.+1)] = tlabel s'.
  apply: (@labelling_singleton _ _ r s'); last by exact: tlabelP.
  by rewrite /is_labelling eq_refl andbT is_labelling_lex.
have [/eqP ->|] := boolP (jx == ix'); first by rewrite !cancel_idxa. 
have [j smx]: exists j, idxa s j = jx by exists (tnth (tlabel s) jx); rewrite cancel_inv_idxa. 
rewrite neq_ltn => /orP [ljx'|lx'j]; last first.
- rewrite ifF; last by rewrite ltnNge (@leq_eqVlt ix') lx'j orbT andbF. 
  by rewrite -smx -[in RHS]ge_stable_post?cancel_idxa // smx. 
- rewrite ljx' andbT; case: ifP => [jxix|]; last first.
  - move=> b; have {b} ixjx: jx < ix by rewrite ltnNge; apply/negPf.
    by rewrite -smx -[in RHS]ge_stable_pre ?cancel_idxa // smx.
  - have [pj smpx]: exists j, ord_succ jx = idxa s j.
      by exists (tnth (tlabel s) (ord_succ jx)); rewrite cancel_inv_idxa.
    by rewrite smpx -(ge_shift differ_on ix'x smpx) ?cancel_idxa // ljx' jxix. 
Qed.

Lemma labelling_differ_on_eq :
  ix' = ix -> is_labelling r s' l.
Proof.
move=> eqii'.
have <- : ge_labelling l = l.
  apply: eq_from_tnth => j.
  rewrite /ge_labelling /ge_index tnth_mktuple eqii'.
  case: ifP => [/eqP -> |_]; last by rewrite ifF // leqNgt andNb.
  have -> : l = tlabel s by apply: (@labelling_singleton _ _ r s) => //; exact: tlabelP.
  by rewrite cancel_idxa.
exact: labelling_differ_on_ge.
Qed.

End Ge.

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

Lemma us (p : 'S_n.+1) : uniq (ss p).
Proof.
rewrite map_inj_uniq /= ?enum_uniq // => j1 j2 /eqP. 
rewrite (tnth_uniq x0) // => /eqP.
exact: perm_inj.
Qed.

Lemma idxa_perm (p : 'S_n.+1) i : idxa (ss p) i = idxa s (p i).
Proof.
apply: val_inj => /=. 
rewrite (idxa_as_index tr rr totr ar (us p)) (idxa_as_index tr rr totr ar u).
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
