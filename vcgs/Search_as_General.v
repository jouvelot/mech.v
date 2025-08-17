(**

  Search_as_General_VCG.v

  A formalization project for the Vickrey‑Clarke‑Groves auctions, targeting:

  - a specification of the "VCG for Search" auction variant (we assume that the bidders'
    weights are all equal to 1).

  This embedding of "VCG for Search" into the "General VCG" mechanism enables short proofs
  that this variant also enjoys these key properties.

  Note that, contrarily to the "vcg" folder, unicity of bids and ctrs is not assumed here. 
  The General VCG specification (see General.v) handles sets of optimal welfare outcomes.

  Authors: Zhan Jing (+++), Pierre Jouvelot(+), Lucas Sguerra, Emilio Gallego Arias(++).

  Date: August, 2025.

  (+) Mines Paris, PSL University, France
  (++) IRIF, France
  (+++) Jiao Tong U., Shanghai

  Thanks for their insights to the ssreflect community, and in particular:

   - Yves Bertot ([sum_split_sOi]),
   - Georges Gonthier ([slot_of]),
   - Cyril Cohen ([widen_ord_inj]).

  Licence: CeCILL-B.

*)
 
From Coq Require Import Unicode.Utf8 Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect order.
From mathcomp.fingroup Require Import perm.

From mech.lib Require Import lib labelling mech.
From mech.vcgs Require Import General. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* [n] agents are bidding. *)

Notation A := (@agent.type n).

Notation last_agent := (@agent.last n').
Notation agent_succ := (@agent.succ n').
Notation agent_pred := (@agent.pred n).

Definition agents := agent.agents n.+1.

(* [k] slots to allocate. *)

Variable (k' : nat).
Definition k := k'.+1.

(* One can use padding to validate the 'lt_k_n' hypothesis (see 'padded_bs'). *)

Hypothesis lt_k_n : k < n.

Section Slot.

Definition slot := 'I_k.

Lemma lt_slot_n' (s : slot) : s < n'.
Proof. rewrite (leq_ltn_trans (leq_ord s)) //; exact: lt_k_n. Qed.

Lemma le_k_n : k <= n.
Proof. exact: ltnW lt_k_n. Qed.

Definition slot_pred (s : slot) : slot := @ord_pred k s.
Definition slot_succ (s : slot) : slot := ord_succ s.

Definition last_slot : slot := ord_max.

Definition slot_as_agent (s : slot) : A.
have slot_as_agent_p : s < n by exact: leq_trans (ltn_ord s) le_k_n.
exact: (Ordinal slot_as_agent_p).
Defined.

Lemma slot_as_agent_inj : injective slot_as_agent.
Proof.
move=> s1 s2 /eqP.
rewrite /slot_as_agent /sval -(inj_eq val_inj) /= => /eqP.
exact: val_inj.
Qed.

End Slot.

(* Each slot has a click-through rate. *)

Variable (q' : nat).
Definition q := q'.+1.
Definition ctr := 'I_q.
Definition ctr0 : ctr := Ordinal (ltn0Sn q').

Definition ctrs := k.-tuple ctr.

Variable (cs : ctrs).
Notation "'ctr_ s" := (tnth cs s) (at level 10).

Hypothesis sorted_ctrs : sorted_tuple cs.
Hypothesis last_ctr_eq0 : 'ctr_(last_slot) = ctr0.

(* Agents submit bids for slots. *)

Variable p' : nat.
Definition p := p'.+1.
Definition bid := 'I_p.
Definition bid0 : bid := Ordinal (ltn0Sn p').
Definition bid_max : bid := ord_max.

Definition bids := n.-tuple bid.

Let geq_bid := @geq_bid p'.

Notation tr := (@transitive_geq_bid p').
Notation totr := (@total_geq_bid p').
Notation ar := (@anti_geq_bid p').
Notation rr := (@reflexive_geq_bid p').

Notation labelling_spec_idxa bs := (@labelling_spec_idxa _ _ _ bs tr totr ar).
Notation tlabel bs := (@tlabel n' _ geq_bid bs tr totr ar). 
Notation tlabelP bs := (@tlabelP n' _ geq_bid bs tr totr ar). 
Notation idxa_inj bs := (@idxa_inj _ _ geq_bid bs tr totr ar). 
Notation labelling_inj bs := (@labelling_inj _ _ geq_bid bs (tlabel bs)).  
Notation cancel_inv_idxa bs := (@cancel_inv_idxa _ _ geq_bid bs tr totr ar).
Notation uniq_to_idxa bs u := (@uniq_to_idxa _ _ geq_bid bs tr totr ar _ _ u). 
Notation uniq_from_idxa bs u := (@uniq_from_idxa _ _ geq_bid bs tr totr ar _ _ u). 

Notation tsort := (tsort geq_bid).
Notation idxa bs i := (@idxa n' _ geq_bid bs tr totr ar i). 

(* Bids need to be sorted in the VCG for Search algorithm. *)
 
Let labelling := @labelling n'.

Lemma tsortK (bs : bids) (sortedbs : sorted_bids bs) : tsort bs = bs.
Proof. 
apply: (sorted_tsort (@transitive_geq_bid p.-1)).
by apply/(@sorted_bids_sorted p' _).
Qed.
 
Lemma idxaK (bs : bids) (sortedbs : sorted_bids bs) j : idxa bs j = j.
Proof.
apply: labelling.idxaK. 
exact/sorted_bids_sorted.
Qed.

(** VCG for Search algorithm. *)

Section VCGforSearchAlgorithm.

Variable (bs0 : bids) (i : A).

Let bs := tsort bs0.
Let i' := idxa bs0 i.

Definition is_winner := i' < k'.

Lemma slot_won_is_slot : minn i' last_slot < k.
Proof. exact: geq_minr. Qed.

Definition slot_won : slot := Ordinal slot_won_is_slot.

Definition externality (bs : bids) s :=
  let j := slot_as_agent s in
  tnth bs j * ('ctr_(slot_pred s) - ('ctr_s)).

(* Price per impression (divide by [ctr_slot_won] for price per click). *)

Definition price :=
  if is_winner then \sum_(s < k | i'.+1 <= s) externality bs s else 0.

End VCGforSearchAlgorithm.

(** Definitions of General VCG's parameters for mapping VCG for Search. *)

Notation "'winners" := (k.-tuple A) (at level 10).

Record O :=
   Outcome {obidders : 'winners;
            ouniq : uniq obidders}.

(** Checking inhabitant existence for type O. *)

Local Definition exists_o : O.
have minnkn : minn k n = k by apply/minn_idPl; exact: le_k_n.
have/Outcome // : uniq (tcast minnkn (@take_tuple _ k _ (ord_tuple n))).
  apply/(tuple_uniqP ord0) => i1 i2.
  rewrite !(tnth_nth ord_max) !val_tcast /= !nth_take ?ltn_ord //.   
  have ltsn (s : 'I_k) : s < n by rewrite (@ltn_trans k) ?ltn_ord ?lt_k_n.
  rewrite !nth_agent_enum /= => /eqP.  
  rewrite -(inj_eq val_inj) /= => /eqP eq12.
  by apply: val_inj.
Defined.

Coercion obidders : O >-> tuple_of.

(* new type O, most of time a tuple is used, so i want it coercion automatic towards tuple *)
Canonical O_subType := Eval hnf in [subType for obidders].
Canonical O_eqType := Eval hnf in EqType _ [eqMixin     of O by <: ].
Canonical O_choiceType := Eval hnf in ChoiceType _ [choiceMixin of O by <:].
Canonical O_countType := Eval hnf in CountType _ [countMixin  of O by <:].
Canonical O_subCountType := Eval hnf in [subCountType of O].
Canonical O_finType := Eval hnf in FinType _ [finMixin    of O by <:].
Canonical O_subFinType := Eval hnf in [subFinType of O].

(* mathcomp system, complementary O_finTy*)

Set Warnings "-projection-no-head-constant".
Canonical O_predType := PredType (fun o x => x \in obidders o).
Set Warnings "projection-no-head-constant".

Lemma o_injective (o : O) : injective (tnth o).
Proof. by move=> x y /eqP; rewrite (tnth_uniq (inord 0)) ?ouniq // => /eqP. Qed.

Lemma uniq_map_o (bs : bids) (o : O) : uniq (map_tuple (tnth (tlabel bs)) o).
Proof.
rewrite map_inj_uniq => [|s1 s2 eq12]; first by exact: (ouniq o).
apply: (labelling_inj bs) => //.
exact: (tlabelP bs).
Qed.

Definition tlabel_o bs o := Outcome (uniq_map_o bs o).
Definition tidxa_o bs o := Outcome (uniq_to_idxa bs (ouniq o)). 

Definition set_o (o : O) (s : 'I_k) (a : A) :=
  mktuple (fun s' => if s == s' then a else tnth o s').

Lemma uniq_set_o (o : O) s a : (forall x, tnth o x != a) -> uniq (set_o o s a).
Proof.
move=> out /=.
rewrite map_inj_uniq ?enum_uniq// => x y.
case: ifP => [/eqP|].
- case: ifP => [/eqP <- <- //| nsy _ /eqP].
  by rewrite -(negbK (a == tnth o y)) eq_sym out.
- case: ifP => [_ _ /eqP|_ _ /o_injective//].
  by rewrite -(negbK (tnth o x == a)) out.
Qed.  

Lemma set_o_tnth (o : O) (s : 'I_k) (a : A) : tnth (set_o o s a) s = a.
Proof. by rewrite tnth_map tnth_ord_tuple eq_refl. Qed.

Lemma tuple_tperm_in a (o : O) s s' : (a \in tuple_tperm s s' o) = (a \in o).
Proof.
apply/tnthP/tnthP => [[sa pa]|[sa pa]]. 
- by rewrite /tuple_tperm tnth_map tnth_ord_tuple in pa; exists (tperm s s' sa).
- have [/eqP ->|nsa] := boolP (s == sa).
  - by exists s'; rewrite tnth_map tnth_ord_tuple tpermR.
  - have [/eqP ->|ns'] := boolP (s' == sa).
    by exists s; rewrite tnth_map tnth_ord_tuple tpermL.
  - by exists sa; rewrite tnth_map tnth_ord_tuple tpermD.
Qed.

Lemma not_in_set_o (o : O) s j a (nja : j != a) (njo : (j \in o) = false) : 
  (j \in set_o o s a) = false.
Proof. 
move: njo.
apply: contraFF => /= /tnthP [js ps].
apply/tnthP.
exists js.
move: ps; rewrite tnth_map tnth_ord_tuple. 
by case: ifP => [_ /eqP|//]; first by rewrite -(negbK (j == a)) nja.
Qed.

Lemma not_tnth_in_set_o (o : O) s  a (nja : tnth o s != a) : 
  (tnth o s \in set_o o s a) = false. 
Proof.
move: nja.
apply: contra_neqF => /tnthP [ja].
rewrite tnth_map tnth_ord_tuple.
case: ifP => [//|nsja /o_injective /eqP].
by rewrite nsja.
Qed.

(* Slot of an agent in an outcome. *)

Section SlotOf.

Definition slot_of (j : A) (o : 'winners) : slot :=
  match (tnthP o j) with
  | ReflectT p => proj1_sig (sig_eqW p)
  | ReflectF _ =>  last_slot
  end.

Lemma cancel_slot (o : O) (s : slot) : slot_of (tnth o s) o = s.
Proof.
rewrite /slot_of; case: tnthP => [[w hw]|]; last by case; exists s.
by case: sig_eqW => ? /= /o_injective ->.
Qed.

Lemma cancel_slot_inv (o : O) i : i \in o -> tnth o (slot_of i o) = i.
Proof.
rewrite /slot_of. 
case: tnthP => [[w hw //]|_ //=].
case: sig_eqW => s' p' /=.
by rewrite p'.
Qed. 

Lemma slot_not_in i o : i \in o = false -> slot_of i o = last_slot.
Proof.
apply: contraFeq.
rewrite below_last_ord /slot_of. 
case: tnthP => [[w hw //]|_ //=].
by rewrite ltnn.
Qed.

Lemma tperm_slot (o : O) (s1 s2 s : slot) :
  let tp_o := Outcome (tuple_tperm_uniq s1 s2 (ouniq o)) in
  slot_of (tnth o s) tp_o  = slot_of (tnth o (tperm s1 s2 s)) o.
Proof.
case: (s1 == s) / eqP => [<-|/eqP neq_s1].
  rewrite tpermL cancel_slot /slot_of.
  case: tnthP => p; last by case: p; exists s2; rewrite tnth_mktuple tpermR.
  case: sig_eqW => s' /=.
  by rewrite -[in LHS](tpermR s1 s2) tnth_mktuple => /o_injective/perm_inj.
case: (s2 == s) / eqP => [<-|/eqP neq_s2].
  rewrite tpermR cancel_slot /slot_of.
  case: tnthP => p; last by case: p; exists s1; rewrite tnth_mktuple tpermL.
  case: sig_eqW => s' /=.
  by rewrite -[in LHS](tpermL s1 s2) tnth_mktuple => /o_injective/perm_inj.
rewrite tpermD // cancel_slot /slot_of.
case: tnthP => p; last by case: p; exists s; rewrite tnth_mktuple tpermD.
case: sig_eqW => s' /=.
by rewrite -[in LHS](@tpermD _ s1 s2 s) // tnth_mktuple => /o_injective/perm_inj.
Qed.

Lemma relabel_slot (bs : bids) (o : O) (j : A) (idxino : idxa bs j \in o) : 
  slot_of (idxa bs j) o = slot_of j (map_tuple (tnth (tlabel bs)) o).
Proof.
rewrite /slot_of. 
case: tnthP => [[w hw]|]; last by have // : ∃ i : 'I_k, idxa bs j = tnth o i by apply/tnthP.
case: sig_eqW => s p /=.
case: tnthP => [[w' hw']|]; last first.
- have //: ∃ i : 'I_k, j = tnth (map_tuple (tnth (tlabel bs)) o) i.
    by apply/tnthP; rewrite -labelling_in.
- case: sig_eqW => s' p' /=. 
  rewrite !tnth_map in hw' p'.
  rewrite p' (cancel_inv_idxa bs) in p.
  exact: (@o_injective o).
Qed.

Lemma index_slot (bs : bids) (o : O) (j : A) (jo : j \in o) : slot_of j o = inord (index j o).
Proof.
rewrite /slot_of. 
case: tnthP => [[w hw]|]; last by have // : ∃ i : 'I_k, j = tnth o i; apply/tnthP.
case: sig_eqW => s p /=.
rewrite p /=.
apply: val_inj => /=.
rewrite inordK.
- by rewrite (tnth_nth ord0) index_uniq// ?size_tuple ?ltn_ord ?ouniq.
- by rewrite -[X in _ < X](size_tuple o) index_mem -p.
Qed.

Lemma slot_inj f (injf : injective f) (o : O) i : slot_of (f i) (map_tuple f o) = slot_of i o.
Proof.
rewrite /slot_of. 
case: tnthP => [[w hw //]|x //=].
- case: sig_eqW => s p /=. 
  rewrite !tnth_map in hw p.
  case: tnthP => [[w' hw' //]|x' //=].
  - case: sig_eqW => s' p' /=.
    apply: (@o_injective o).
    move: p => /injf <-.
    by rewrite p'.
  - have // : (∃ i0 : 'I_k, i = tnth o i0) by exists s; move: p => /injf.
- case: tnthP => [[w hw //]|y //=].
  have //: (∃ i0 : 'I_k, f i = tnth (map_tuple f o) i0).
    by exists w; by rewrite tnth_map hw.
Qed.

Lemma in_inj_o (T : eqType) (f : A -> T) (injf : injective f) (o : O) j : 
  (f j \in (map_tuple f o)) = (j \in o). 
Proof. by rewrite -(mem_map injf). Qed.

End SlotOf.

Lemma after_last_slot a bs : k' <= idxa bs a -> 'ctr_(slot_won bs a) = ctr0.
Proof.
move=> lek'i.
apply: val_inj => /=. 
rewrite (tnth_nth ord0) /=.
move: lek'i last_ctr_eq0 => /minn_idPr ->.
rewrite (@tnth_nth _ _ ord0) => /eqP. 
by rewrite -(inj_eq val_inj) /= => /eqP.
Qed.

(** VCG-for-Search-specific bidding function for General VCG. *)

Section Biddings.

Variable (bs : bids).

Notation "'bid_ j" := (tnth bs j) (at level 10).

Definition bid_in (j : A) (s : slot) := 'bid_j * 'ctr_s.

Definition t_bidding (j : A) (o : 'winners) :=
    if j \in o then bid_in j (slot_of j o) else 0.

Definition bidding (j : A) := [ffun o : O => t_bidding j o].

Definition biddings := [tuple bidding j | j < n].

End Biddings.

(** VCG-for-Search-specific optimal outcome for General VCG. *)

Module OStar.

Section Welfare.

Variable (bs : bids).

Notation "'bid_ j" := (tnth bs j) (at level 10).

Notation "'a* s" := (tnth (tlabel bs) (slot_as_agent s)) (at level 10).

Definition t_oStar := [tuple 'a* s | s < k].

Lemma oStar_uniq : uniq t_oStar.
Proof.
rewrite map_inj_uniq => [|s1 s2 eq12]; first by rewrite val_ord_tuple enum_uniq.
apply/slot_as_agent_inj/(labelling_inj bs) => //.
exact: (tlabelP bs).
Qed.

Definition oStar := Outcome oStar_uniq.

Notation "'b* s" := (bidding bs ('a* s) oStar) (at level 10).
Notation "'idxa j" := (idxa bs j) (at level 10).

Definition sorted_o o := ∀ s1 s2 : slot, s1 <= s2 → 'idxa (tnth o s1) <= 'idxa (tnth o s2).

Definition welfare (o : O) := 
  \sum_(s < k) bidding bs (tnth o s) o.

Lemma alt_welfare j o :
  \sum_(s < k) bidding bs (j s) (o s) =
      \sum_(s < k) t_bidding bs (j s) (obidders (o s)).
Proof. by apply: eq_bigr=> s _; rewrite /bidding ffunE. Qed.

Definition max_welfare := welfare oStar.

Lemma le_ioStar_io (o : O) (sorted_o : sorted_o o) :
  forall (s : slot), 'idxa ('a* s) <= 'idxa (tnth o s).
Proof.
case.
elim=> [lt0k //=|s IH lts1k]; first by rewrite (cancel_inv_idxa bs) /slot_as_agent.
have lt_s_k: s < k by rewrite (@ltn_trans (S s)). 
set s' := Ordinal lt_s_k; set s'1 := Ordinal lts1k. 
have: idxa bs (tnth o s') < idxa bs (tnth o s'1). 
  move: (@sorted_o s' s'1 (leqnSn s')).
  rewrite leq_eqVlt => /orP [/eqP /=|//].
  move/val_inj/(idxa_inj bs)/o_injective => /eqP.
  by rewrite -(inj_eq val_inj) /= -[X in X == _]addn0 -addn1 eqn_add2l.
move: (IH lt_s_k).
rewrite !(cancel_inv_idxa bs) /slot_as_agent /=.
exact: leq_ltn_trans.
Qed.

Lemma leq_bid (i1 i2 : A) : 'idxa i1 <= 'idxa i2 -> 'bid_i2 <= 'bid_i1.
Proof.
move=> lti1I2.
rewrite -(labelling_spec_idxa bs) -[X in _ <= val X](labelling_spec_idxa bs).
rewrite (tnth_nth ord0) [X in _ <= val X](tnth_nth ord0). 
apply: (sorted_leq_nth (@transitive_geq_bid p.-1)) => //; first by exact: reflexive_geq_bid.
- apply/(@sorted_bids_sorted p' _).
  by rewrite /tsort sorted_bids_sorted sort_sorted.
- rewrite inE size_sort size_tuple ltn_ord //.
  by rewrite inE size_sort size_tuple ltn_ord.
Qed.

Lemma le_welfare_sorted_o_oStar (o : O) (sorted_o : sorted_o o) :
  welfare o <= max_welfare.
Proof.
apply: leq_sum => s _. 
rewrite /bidding !ffunE /t_bidding. 
case aio: (tnth o s \in o); last by rewrite !leq0n.
rewrite !cancel_slot ifT; last by exact: mem_tnth.
by rewrite !leq_mul2r /oStar /= /t_oStar tnth_map tnth_ord_tuple leq_bid ?orbT // le_ioStar_io.
Qed.

Lemma itperm_id o s : o = Outcome (it_aperm_uniq s s (ouniq o)).
Proof. apply: val_inj => /=; rewrite apermE permE; exact: tuple_tperm_id. Qed.

Lemma le_transposed_welfare (x : 'I_k * 'I_k) (o : O) :
  uniq_is_bubble (tidxa_o bs o) x ->
  welfare o <= welfare (Outcome (it_aperm_uniq x.1 x.2 (ouniq o))).
Proof.
rewrite (surjective_pairing x) /= => /orP [/eqP -> /=|/andP [ltx1x2 ltt2t1]];
  first by rewrite eq_leq // [in LHS](@itperm_id o x.2).
rewrite /welfare (bigD1 x.2) 1?(bigD1 x.1) //=; last by move/ltn_eqF/negbT: ltx1x2.
rewrite [X in _ <= X](bigD1 x.2) ?[X in _ <= _ + X](bigD1 x.1) //=;
  last by move/ltn_eqF/negbT: ltx1x2. 
rewrite addnA [X in _ <= X]addnA leq_add //; last first.
- apply: eq_leq. 
  set F2 := (X in _ = \sum_(i < k | _) X i).
  rewrite (eq_bigr F2) // => i /andP [neis2 neis1].
  rewrite eq_sym in neis1; rewrite eq_sym in neis2.
  rewrite /F2 /bidding !ffunE /t_bidding/= apermE permE tnth_mktuple tpermD //.
  rewrite !mem_tnth /tuple_tperm memtE /=.  
  have ipx1x2: i = tperm x.1 x.2 i by rewrite tpermD.
  rewrite ipx1x2 (@mem_map  _ _ (fun j => tnth o (tperm x.1 x.2 j))) ?mem_enum;
    last by move=> j s; move/o_injective/perm_inj.
  rewrite !tpermD // cancel_slot [in RHS]/slot_of.
  case: tnthP => p.
  - case: sig_eqW => s /=.
    rewrite tnth_mktuple ipx1x2 => /o_injective /perm_inj <-.
    by rewrite tpermD.
  - have //=: ∃ s, tnth o i = tnth [tuple tnth o (tperm x.1 x.2 i) | i < k] s
      by exists i; rewrite tnth_mktuple tpermD.
- rewrite /bidding !ffunE /= /t_bidding !mem_tnth !apermE permE !tnth_mktuple tpermR tpermL.
  rewrite (@tperm_slot _ x.1 x.2 x.1) (@tperm_slot _ x.1 x.2 x.2).
  rewrite tpermL tpermR /bid_in !cancel_slot. 
  rewrite !tnth_map in ltt2t1. 
  rewrite [X in _ <= X]addnC leq_transpose //; first by rewrite leq_bid // ltnW.
  by move/ltnW/sorted_ctrs: ltx1x2.
Qed.

Lemma le_welfare_o_oStar (o : O) : welfare o <= max_welfare.
Proof.
suff {o}: forall xs o,
    let xo := uswap (tidxa_o bs o) xs in
    let uxo := ububble_uniq (ouniq (tidxa_o bs o)) xs in
    xo.1 -> welfare o <= welfare (Outcome (uniq_from_idxa bs uxo)).
  move: (uniq_bubble_sort_spec (ouniq (tidxa_o bs o))) => [xs] [bx sortedxo] /(_ xs o bx).
  set mo := (X in _ <= welfare X) => ltwo.
  have/le_welfare_sorted_o_oStar : sorted_o mo.   
    move=> s1 s2.
    rewrite leq_eqVlt => /orP [/eqP/val_inj -> //| lt12]. 
    move: (sortedxo s1 s2 lt12) => {sortedxo}.
    by rewrite !tnth_map !(cancel_inv_idxa bs) => /ltnW.
  exact: leq_trans. 
elim=> [o _ //=|x xs IH o /= /andP [bi xoi]].
- rewrite eq_leq //.
  apply: eq_bigr => s _.
  rewrite !ffunE !tnth_map /= !cancel_idxa. 
  congr (t_bidding _ _ _).
  apply: eq_from_tnth => s'.
  by rewrite !tnth_map cancel_idxa.
- pose uxoi := ububble_uniq (ouniq (tidxa_o bs o)) xs; 
               pose ouxoi := Outcome (uniq_from_idxa bs uxoi).
  move: (@le_transposed_welfare x ouxoi) => /=. 
  rewrite !cancel_inv_map_idxa => /(_ bi) /=.  
  move: (IH o xoi) => le1 le2.
  move: (leq_trans le1 le2) => {le1 le2}.   
  set s1 := (X in _ <= X -> _) => lew1.
  rewrite (@leq_trans s1) // eq_leq // => {lew1}.
  apply: eq_bigr => s _ /=.
  rewrite /bidding !ffunE /t_bidding.
  congr (if _ then _ else _); first by rewrite !mem_tnth. 
  set t1 := (X in bid_in _ (tnth X _)); set t2 := (X in _ = bid_in _ (tnth X _) _).
  have permC : t1 = t2. 
    rewrite /t1 /t2 !apermE !permE /=.
    apply: eq_from_tnth => s'.
    by rewrite !tnth_map tnth_ord_tuple.
  by rewrite permC; congr (bid_in _ (tnth _ _) (slot_of (tnth _ _) _)).
Qed.

End Welfare.

Section Properties.

Variable (bs : bids).

Lemma slot_in_oStar (j : A) : 
  (j \in (oStar bs)) -> slot_of j (oStar bs) = inord (idxa bs j).
Proof.
move=> jino.
rewrite /slot_of. 
move: (@elimT _ _ (tnthP (oStar bs) j) jino).
case: tnthP => pj _ /=.
case: sig_eqW => sj //=.
rewrite tnth_mktuple => -> /=.
by rewrite (cancel_inv_idxa bs) inord_val. 
have //: exists s, j = tnth (oStar bs) s.
  exists (inord (idxa bs j)).
  rewrite tnth_mktuple.
  apply: val_inj => /=.
  have -> : slot_as_agent (inord (idxa bs j)) = idxa bs j.
    apply: val_inj => /=.
    rewrite inordK //.
    by move/tnthP: jino.
by rewrite cancel_idxa.
Qed.

Lemma mem_oStar (j : A) (jisslot: idxa bs j < k) : j \in (oStar bs).
Proof.
apply/tnthP.
exists (inord (idxa bs j)).
rewrite /oStar /t_oStar tnth_map tnth_ord_tuple. 
have -> : slot_as_agent (inord (idxa bs j)) = idxa bs j. 
  apply: val_inj => /=.
  by rewrite inordK.
by rewrite cancel_idxa.
Qed.

Lemma mem_oStar_inv j : j \in (oStar bs) → idxa bs j < k.
Proof.
move/tnthP => [ij] ->.
rewrite tnth_map tnth_ord_tuple. 
have -> : slot_as_agent ij = inord ij. 
  apply: val_inj => /=. 
  by rewrite inordK // (ltn_trans (ltn_ord ij) lt_k_n).
by rewrite (cancel_inv_idxa bs) inordK ?ltn_ord // (ltn_trans (ltn_ord ij) lt_k_n).
Qed.

Lemma mem_oStar_equiv j : idxa bs j < k <-> j \in oStar bs.
Proof. 
split; first by exact: mem_oStar. 
exact: mem_oStar_inv. 
Qed.

End Properties.

End OStar.

(** Optimal outcome for sorted bids. *)

Section OStarSorted.

Variable (bs : bids).

Variable (sorted_bs : sorted_bids bs).

Definition t_oStar := [tuple widen_ord le_k_n j | j < k].

Lemma oStar_uniq : uniq t_oStar.
Proof.
rewrite map_inj_uniq; last by exact: widen_ord_inj.
by rewrite val_ord_tuple enum_uniq.
Qed.

Definition oStar := Outcome oStar_uniq.

Lemma oStar_id (s : slot) : tnth oStar s = slot_as_agent s.
Proof. rewrite tnth_mktuple; exact: val_inj. Qed.

Definition welfare := OStar.welfare.

Definition max_welfare := welfare bs oStar.

Definition sorted_o := uniq_up_sorted_tuple.

Lemma eq_oStar_iota : OStar.oStar bs = oStar.
Proof.
apply: val_inj => /=.
rewrite /OStar.t_oStar /t_oStar sorted_tlabel. 
- apply: eq_from_tnth => s.
  rewrite /labelling_id !tnth_map tnth_ord_tuple.
  exact: val_inj.
- by apply/sorted_bids_sorted.
Qed.

Lemma le_welfare_o_oStar (o : O) : welfare bs o <= max_welfare.
Proof. by rewrite /max_welfare -eq_oStar_iota (OStar.le_welfare_o_oStar bs o). Qed.
  
Lemma slot_in_oStar (j : A) : (j \in oStar) -> slot_of j oStar = inord j.
Proof. rewrite -!eq_oStar_iota -{3}(idxaK sorted_bs j); exact: OStar.slot_in_oStar. Qed.

Lemma mem_oStar_inv (j : A) : j \in oStar -> j < k.
Proof. 
rewrite -eq_oStar_iota -{2}(idxaK sorted_bs j).
exact: OStar.mem_oStar_inv.
Qed.

Lemma mem_oStar (j : A) (jisslot: j < k) : j \in oStar.
Proof.
move: jisslot.
rewrite -eq_oStar_iota -{1}(idxaK sorted_bs j).
exact: OStar.mem_oStar.
Qed.

Lemma not_in_oStar' (j : A ) : k' < j <-> (j \in oStar) = false.
Proof. 
rewrite ltnNge.
split; first by apply: contraNF; exact: mem_oStar_inv. 
by apply: contraFN; exact: mem_oStar.
Qed.

Definition not_in_oStar j := (iffLR (not_in_oStar' j)).
Definition not_in_oStar_inv j := (iffRL (not_in_oStar' j)).

Lemma eq_losing_last_slot j
      (jino : j \in oStar)
      (jloses : j < k' = false) :
  slot_of j oStar = last_slot.
Proof.
move: (jino) => /mem_oStar_inv.   
rewrite ltn_neqAle => /andP [_].
rewrite leq_eqVlt ltnS leq_eqVlt jloses orbF.
move=> /orP [|/eqP eqijk']; first by move/mem_oStar_inv/ltn_eqF: (jino) => ->. 
rewrite slot_in_oStar; last by rewrite mem_oStar // eqijk'.
by apply: val_inj => /=; rewrite inordK ?eqijk'.
Qed.

Lemma wonE j (jwins : idxa bs j < k') : slot_won bs j = inord (idxa bs j).
Proof.
apply: val_inj => /=.
move: (jwins) => /ltnW. 
rewrite minnE -subn_eq0 => /eqP ->.
by rewrite subn0 inordK // (@ltn_trans k').
Qed.

Lemma eq_slot_won (j : A) (jwins : idxa bs j < k') : 
  slot_won bs j = slot_of (idxa bs j) oStar.
Proof. by rewrite slot_in_oStar ?wonE; last by rewrite mem_oStar // (@ltn_trans k'). Qed.

End OStarSorted.

Module EqualPrice.

Definition o0 := oStar.

(** Properties for [bidSum] function in General VCG. *)

Section BidSum.

Variable (i : A) (bs : bids).

Notation "'bid_ j" := (tnth bs j) (at level 10).

Definition bidSum := @VCG.bidSum O_finType (biddings bs).

Lemma bidSumE o : bidSum o = \sum_(b <- biddings bs) b o.
Proof. by rewrite /bidSum VCG.bidSumE. Qed.

Lemma valid_bidSum (o : O) :
  bidSum o = \sum_(j < n) (bidding bs) j o.
Proof. by apply: congr_big => //= s _; rewrite tnth_mktuple. Qed.

Lemma bidSum_out_o (o : O) :
  \sum_(j < n | j \notin o) (bidding bs) j o = 0.
Proof.
apply/eqP; rewrite sum_nat_eq0.
apply/forall_inP => j outo; apply/eqP.
rewrite ffunE.
exact: ifN.
Qed.

Lemma bidSum_slot (o : O) :
  bidSum o = \sum_(s < k) (bidding bs) (tnth o s) o.
Proof.
rewrite valid_bidSum (bigID (fun j : A => j \in o)) bidSum_out_o /= addn0.
by rewrite -(@big_tuple _ _ _ _ _ _ predT (fun j => bidding bs j o)) big_uniq ?ouniq.
Qed.

Notation "'a* s" := (tnth OStar.oStar s) (at level 10).

Notation "'b* s" := (bidding bs ('a* s) OStar.oStar) (at level 10).

Lemma bidsSum_sumBid (P : A -> bool) (o : O) :
  forall bs, \sum_(j < n | P j) tnth (biddings bs) j o = \sum_(j < n | P j) bidding bs j o.
Proof. by move=> ?; apply: congr_big => //= j _; rewrite tnth_mktuple. Qed.

Definition VCG_oStars := @VCG.oStars O_finType (biddings bs).

Lemma HoStar : (OStar.oStar bs) \in VCG_oStars.
Proof.
rewrite in_set; apply/andP; split; first by [].
apply/forallP=> x; rewrite implyTb.
rewrite /VCG.bidSum !bidsSum_sumBid -!valid_bidSum !bidSum_slot.
exact: OStar.le_welfare_o_oStar.
Qed.

Definition VCG_oStar := VCG.o (VCG.mkOStar HoStar).

Definition stable_choice (set_oStars : {set O_finType}) := VCG.mkOStar HoStar.

Definition max_bidSum_spec := (@extremum_spec [eqType of nat] geq O_finType predT bidSum).

Lemma VCG_oStar_extremum : max_bidSum_spec VCG_oStar.
Proof.
rewrite/max_bidSum_spec; apply: ExtremumSpec; first by [].
move=> j pj.
rewrite/geq/=.
rewrite -(@bigmax_eq_args _ predT bidSum VCG_oStar) ;
  first by rewrite leq_bigmax_cond.
exact: HoStar.
Qed.

Lemma oStar_extremum : max_bidSum_spec (OStar.oStar bs).
Proof.
apply: ExtremumSpec => [//|o _].
rewrite bidSum_slot /bidSum /VCG.bidSum // !bidsSum_sumBid.
move: (OStar.le_welfare_o_oStar bs o).
by rewrite /OStar.max_welfare /OStar.welfare -bidSum_slot valid_bidSum.
Qed.

(* We focus on sorted bids, since this is how one can better relate bidSum to the VCG for
   its VCG for Search-specific variant. *)

Variable sorted_bs : sorted_bids bs.

Definition bid_ctr_slot s := 'bid_(slot_as_agent s) * 'ctr_s.
Definition bid_ctr_agent j := 'bid_j * 'ctr_(slot_of j oStar).

Lemma widen_slot_as_agent (s : slot) : widen_ord le_k_n s = slot_as_agent s.
by rewrite /slot_as_agent; apply: val_inj.
Qed.

Lemma eq_bid_ctr (j : A) : bid_ctr_agent j = bid_ctr_slot (slot_of j oStar).
Proof.
rewrite /bid_ctr_agent /bid_ctr_slot /slot_of.  
have: tnth oStar (slot_of j oStar) \in oStar by exact: mem_tnth.
case: tnthP => p; last by rewrite last_ctr_eq0 ?muln0 .
case: sig_eqW => s' p' //=.
rewrite -widen_slot_as_agent  => _.
by rewrite p' tnth_mktuple.
Qed.

Lemma s_bid_as_bid_x_ctr (s : slot) : bidding bs (tnth oStar s) oStar = bid_ctr_slot s.
Proof.
rewrite /bidding ffunE /t_bidding tnth_mktuple mem_map; last by exact: widen_ord_inj.
rewrite ifT; last by apply/tnthP; exists s; rewrite tnth_ord_tuple.
by rewrite widen_slot_as_agent -oStar_id cancel_slot tnth_mktuple widen_slot_as_agent.
Qed.

Lemma bidSum_bid_ctr_slot : bidSum oStar = \sum_(s < k) bid_ctr_slot s.
Proof.
rewrite bidSum_slot.
apply: congr_big => //= s _.
exact: s_bid_as_bid_x_ctr.
Qed.

Definition bidSum_i := @VCG.bidSum_i O_finType i (biddings bs).

Lemma bidSum_i_bid_ctr_agent : bidSum_i oStar = bidSum oStar - bid_ctr_agent i.
Proof.
rewrite /bidSum_i /VCG.bidSum_i /bidSum /VCG.bidSum.
rewrite [X in _ = X - _](bigD1 i) => //=.
rewrite addnC -[LHS]addn0 -addnBA.
congr (_ + _).
- rewrite tnth_mktuple ffunE /t_bidding.
  case: (i \in oStar); first by rewrite subnn.
  by rewrite sub0n.
- rewrite tnth_mktuple ffunE /t_bidding.
  case iino: (i \in oStar); first by apply: eq_leq.
  rewrite /bid_ctr_agent /slot_of.
  move: (@elimF _ (i \in oStar) (tnthP oStar i) iino).
  case: tnthP => [p|p _] //.
  by rewrite leqn0 muln_eq0 last_ctr_eq0 ?eq_refl ?orbT.
Qed.

Lemma bidSum_i_bid_ctr_slot :
  bidSum_i oStar = \sum_(s < k) bid_ctr_slot s - bid_ctr_agent i.
Proof. by move: bidSum_i_bid_ctr_agent; rewrite bidSum_bid_ctr_slot. Qed.

End BidSum.
(* New *)

Lemma eq_bidSum bs (sorted_bs : sorted_bids bs) :
  bidSum bs (VCG_oStar bs) = bidSum bs oStar.
Proof.
rewrite -(eq_oStar_iota sorted_bs).
move: VCG_oStar_extremum oStar_extremum => [] o1 _ mo1 [] o2 _ mo2.
apply/eqP.
rewrite eqn_leq.
by move: (mo1 o2 erefl) (mo2 o1 erefl) => /= -> ->.
Qed.

(** VCG for Search price as an instance of General VCG (for sorted bids). *)

Variable (n_bidders : nat).

Variable (bs_bidders : n_bidders.-tuple bid).

Lemma cast_n_tuple : minn n (n_bidders + (n - n_bidders)) = n.
Proof.
case lenbn: (n_bidders <= n); first by rewrite subnKC ?minnn.
move/negbT: lenbn; rewrite -ltnNge; move/ltnW=> lennb.
move: (lennb); rewrite -subn_eq0 => /eqP ->; rewrite addn0.
by apply/minn_idPl.
Qed.

Definition padded_bs_bidders : bids :=
  tcast cast_n_tuple (take_tuple n (cat_tuple bs_bidders (nseq_tuple (n - n_bidders) bid0))).

Definition bs0 := locked padded_bs_bidders.

(* Right padding with 0s ensures that k < n is valid, whatever the number
   n_bidders of actual bidders is.

  Wlog, we can assume that bs0 is already sorted (padding is with 0s). *)

Section SortedVCGforSearchPrice.

Variable (i : A).

Variable (bs0 : bids).

Variable sorted_bs0 : sorted_bids bs0.

Notation not_in_oStar_inv := (not_in_oStar_inv sorted_bs0).
Notation mem_oStar_inv := (mem_oStar_inv sorted_bs0).

Definition bs := bs0.

Notation "'bid_ j" := (tnth bs j) (at level 10).

Lemma sorted_bs : sorted_bids bs.
Proof. exact: sorted_bs0. Qed.

Definition labelling_id : labelling := labelling.labelling_id n'.

Definition ls : labelling := labelling_id.

Notation "'lab_ j" := (tnth ls j) (at level 10).

(* Helper lemmas when i is not in an outcome. *)

Section NotInOutcome.

Definition no_i_in (o : O) := i \notin o.

Lemma no_i_tnth o s : no_i_in o -> (tnth o s == i) = false.
Proof. by move/memPn/allP/all_tnthP/(_ s) => /negPf. Qed. 

Definition t_bidding_i j o := if j != i then t_bidding bs j o else 0.

Definition bidding_i (j : A) := [ffun o : O => t_bidding_i j o].

Definition biddings_i := [tuple bidding_i j | j < n].

Definition welfare_i (o : O) := \sum_(s < k) bidding_i (tnth o s) o.

Lemma alt_welfare_i j o :
  \sum_(s < k) bidding_i (j s) (o s) =
      \sum_(s < k) t_bidding_i (j s) (o s).
Proof. by apply: eq_bigr=> s _; rewrite /bidding_i ffunE. Qed.

Lemma sum_out_perm_i s1 s2 (o : O) (noio : no_i_in o) :
  let permo := Outcome (it_aperm_uniq s1 s2 (ouniq o)) in
  \sum_(i < k | (i != s2) && (i != s1)) bidding_i (tnth o i) o =
  \sum_(i < k | (i != s2) && (i != s1)) 
   bidding_i (tnth (aperm (obidders o) (@itperm _ _ s1 s2)) i) permo.
Proof.
move=> /=.
set permo := (X in _ = \sum_(i < k | _) _ X); set F2 := (X in _ = \sum_(i < k | _) X i).
rewrite (eq_bigr F2) // => s /andP [neis2 neis1].
rewrite eq_sym in neis1; rewrite eq_sym in neis2.
rewrite /F2 /bidding_i !ffunE /t_bidding_i /= eq_sym.
rewrite eq_sym no_i_tnth //= (@no_i_tnth permo s) //=; 
  last by rewrite /no_i_in /= notin_itperm.
rewrite apermE permE tnth_mktuple tpermD //= /t_bidding !mem_tnth memtE /=.
have {F2} ipi1i2: s = tperm s1 s2 s by rewrite tpermD.
rewrite ipi1i2 (@mem_map  _ _ (fun j => tnth o (tperm s1 s2 j))) ?mem_enum => [|j s'];
  last by move/o_injective/perm_inj.
rewrite !tpermD // cancel_slot [in RHS]/slot_of.
case: tnthP => p. 
- case: sig_eqW => s' /=.
  rewrite tnth_mktuple ipi1i2.
  move/o_injective/perm_inj => <-.
  by rewrite tpermD. 
- have //=: ∃ s', tnth o s = tnth (tuple_tperm s1 s2 o) s'; by exists s; rewrite tnth_mktuple tpermD.
Qed.

Lemma o_without_i_uniq (o : O) (i' : A)
      (neii' : i != i')
      (noi'ino : i' \notin o) :
  let t_o_without_i :=  map_tuple (fun j : A => if j != i then j else i') o in
  uniq o -> uniq t_o_without_i.
Proof.
move=> uniqo.
rewrite map_inj_in_uniq // => j1 j2 j1ino j2ino. 
case: (j1 == i) / eqP => [->|_] /=. 
- case: (j2 == i) / eqP => [-> //=|_ //= eqi'j2] /=.
  by move: noi'ino; rewrite eqi'j2 j2ino.
- have [] := boolP (j2 != i) => _ //= eqi'j1.
  by move: noi'ino; rewrite -eqi'j1 j1ino.
Qed.

Lemma o_without_i_spec (o : O) (iino : i \in o) :
  exists (o' : O), exists (i' : A), forall (s : slot),
        (tnth o s = i -> tnth o' s = i') /\
        (tnth o s != i -> tnth o' s = tnth o s) /\
        i' \notin o /\
        i' != i.
Proof.
have [i' _ noi'ino]: exists2 i', i' \in A & i' \notin o.
  apply/subsetPn.
  rewrite proper_subn // properE.
  apply/andP. 
  split; first by apply/subsetP. 
  have (T: finType) (A B : predPredType T) : #|A| < #|B| -> ~~ (B \subset A). 
    apply: contraL.
    rewrite -leqNgt.
    exact: subset_leq_card.
  apply.
  move: (ouniq o) => /card_uniqP ->.
  by rewrite size_tuple card_ord lt_k_n.
have neii': i != i' by move: noi'ino; apply: contra => /eqP <-.
exists (Outcome (o_without_i_uniq neii' noi'ino (ouniq o))).
exists i' => s /=.
- split.
  rewrite tnth_map => ->.
  by rewrite eq_refl.
- split; last by rewrite eq_sym.
  by rewrite tnth_map => ->.
Qed.

Definition star_prefix (o oS : O) := forall s, tnth oS s <= tnth o s.

Lemma le_welfare_sorted_o_oS (o oS : O)
      (noio : no_i_in o) (noioS : no_i_in oS)
      (sortedo : sorted_o o)
      (pref : star_prefix o oS) :
  welfare_i o <= welfare_i oS.
Proof.
apply: leq_sum => s _.
rewrite /bidding_i !ffunE /t_bidding_i /t_bidding.
rewrite no_i_tnth //= (no_i_tnth s noioS) //=.
rewrite !cancel_slot !ifT ?mem_tnth //.
by rewrite leq_mul2r sorted_bs ?orbT.
Qed.

Lemma le_transposed_welfare_i (x : 'I_k * 'I_k) (o : O)
      (noio : no_i_in o) :
  uniq_is_bubble o x ->
  welfare_i o <= welfare_i (Outcome (it_aperm_uniq x.1 x.2 (ouniq o))).
Proof.
rewrite (surjective_pairing x) /= => /orP [/eqP -> /=|/andP [ltx1x2 ltt2t1]];
  first by rewrite eq_leq //= [in LHS](@OStar.itperm_id o x.2).
rewrite /welfare_i (bigD1 x.2) 1?(bigD1 x.1) //=; last by move/ltn_eqF/negbT: ltx1x2.
rewrite [X in _ <= X](bigD1 x.2) ?[X in _ <= _ + X](bigD1 x.1) //=;
  last by move/ltn_eqF/negbT: ltx1x2.
rewrite addnA [X in _ <= X]addnA -sum_out_perm_i //.
rewrite leq_add2r /bidding !ffunE /= /t_bidding_i /t_bidding.
rewrite !mem_tnth !apermE permE !tnth_mktuple tpermR tpermL.
rewrite (@tperm_slot _ x.1 x.2 x.1) (@tperm_slot _ x.1 x.2 x.2).
rewrite tpermL tpermR /bid_in !cancel_slot. 
set i1 := tnth o x.1; set i2 := tnth o x.2.
have leb1b2: 'bid_i1 <= 'bid_i2 by rewrite sorted_bs // ltnW.
have lec2c1: 'ctr_x.2 <= 'ctr_x.1 by move/ltnW/sorted_ctrs: ltx1x2.
by rewrite [X in _ <= X]addnC eq_sym no_i_tnth //= eq_sym no_i_tnth //= leq_transpose.
Qed.

Lemma le_bubble_sort_welfare : forall xs (o : O) (noio : no_i_in o),
    let xo := uswap o xs in
    xo.1 -> welfare_i o <= welfare_i (Outcome (ububble_uniq (ouniq o) xs)).
Proof. 
rewrite /=. 
elim=> [o _ _|x xs IH o noio /= /andP [isb x12s']]; first by apply: leq_sum => s _; rewrite !ffunE.
pose xo := Outcome (ububble_uniq (ouniq o) xs).
have noixo: no_i_in xo by exact: (@notin_ububble _ _ o xs i). 
move: (IH o noio x12s') (le_transposed_welfare_i noixo isb).
rewrite /welfare_i /= !alt_welfare_i /=.
exact: leq_trans.
Qed.

End NotInOutcome.

Lemma le_welfare_o_oStar_i (o oS : O) 
      (noio : ~~ (no_i_in o)) 
      (lew : ∀ o : O, no_i_in o → welfare_i o <= welfare_i oS) :
  welfare_i o <= welfare_i oS.
Proof. 
have/(_ noio) iino: ~~ no_i_in o -> i \in o by apply: contraR.
move: (@o_without_i_spec o iino) => [o'] [i' diff_i].
have/lew lew': no_i_in o'.
  apply/memPnC/allP/all_tnthP => s. 
  move: (diff_i s) => [eqi [neqi [noi'ino neii']]].
  rewrite eq_sym.
  have [] := boolP (tnth o s == i) => eqosi; first by move/eqP/eqi: eqosi => ->.
  by move: (eqosi) => /neqi ->.
rewrite (@leq_trans (welfare_i o')) //.
apply: leq_sum => s _.
rewrite /bidding_i !ffunE /t_bidding_i.
move: (diff_i s) => [eqi [neqi [noi'ino neii']]].
have [] := boolP (tnth o s != i) => nei //.
rewrite !(neqi nei) nei /t_bidding cancel_slot.
by rewrite -{3 5}(neqi nei) cancel_slot !mem_tnth.
Qed.

Definition VCG_bidSum'' := VCG.bidSum'' i (biddings bs).

Section ArgBidSum.

Lemma argmax_bidSum_oS'' (oS : O) (lew : forall o, welfare_i o <= welfare_i oS) :
  VCG_bidSum'' [arg max_(o > o0) VCG_bidSum'' o] = VCG_bidSum'' oS.
Proof.
apply/anti_leq/andP; split; last by 
  rewrite -bigmax_eq_arg ?leq_bigmax.
rewrite -bigmax_eq_arg //.
apply/bigmax_leqP => o _.
rewrite /VCG_bidSum'' /VCG.bidSum''. 
have body o': \sum_(j < n) tnth (VCG.bs'' i (biddings bs)) j o' =
              \sum_(j < n) t_bidding_i j o'.
  by apply: eq_bigr => j _; rewrite !tnth_mktuple !ffunE /t_bidding_i. 
rewrite (body o) (body oS) => {body}.
have bidSum_out_o_i (o' : O) : \sum_(j < n | j \notin o') t_bidding_i j o' = 0.
  apply/eqP; rewrite sum_nat_eq0.
  apply/forall_inP => j outo; apply/eqP. 
  rewrite /t_bidding_i /t_bidding.
  case: (j != i) => //.
  by rewrite ifN. 
rewrite (bigID (fun j : A => j \in o)) bidSum_out_o_i /= addn0.
rewrite [X in _ <= X](bigID (fun j : A => j \in oS)) bidSum_out_o_i /= addn0.
have eqww o': welfare_i o' = \sum_(i in o') t_bidding_i i o'.
  rewrite /welfare_i -(@big_tuple _ _ _ _ _ _ predT (fun j => bidding_i j o')).
  rewrite big_uniq /=; last by exact: ouniq.
  rewrite (eq_bigr (fun j => t_bidding_i j o')) // => j _.
  by rewrite /bidding_i !ffunE.
by rewrite -!eqww. 
Qed.

End ArgBidSum.

Definition welfare_with_i := (@VCG.welfare_with_i O_finType i (biddings bs) (stable_choice bs)).

Definition welfare_without_i'' := VCG.welfare_without_i'' i (biddings bs).

Section Loses.

Variable not_i_in_oStar : i \in oStar = false.

(* Welfare with i. *)

Lemma eq_t_oStar_oStar : OStar.t_oStar bs = oStar.
Proof.
rewrite /OStar.t_oStar /t_oStar sorted_tlabel.
- apply: eq_from_tnth => s.
  rewrite /labelling.labelling_id !tnth_map tnth_ord_tuple.
  exact: val_inj.
- by apply/sorted_bids_sorted.
Qed.

Lemma bidding_i_eq0 : bidding bs i (VCG_oStar bs) = 0.
Proof.
rewrite /bidding ffunE /t_bidding /bid_in.
rewrite ifF // /VCG_oStar /=.
by rewrite eq_t_oStar_oStar.
Qed.

Let eq_welfare_with_i :
  welfare_with_i = \sum_(s < k) bid_ctr_slot bs s.
Proof.
rewrite /welfare_with_i /VCG.welfare_with_i /VCG.bidSum_i -/(VCG_oStar bs).
rewrite -bidSum_bid_ctr_slot bidsSum_sumBid. 
apply/eqP; rewrite -(eqn_add2l (bidding bs i (VCG_oStar bs))); apply/eqP.
under (eq_bigl (fun j => true && (j != i))) => j; first by rewrite andTb.
rewrite -(bigD1 i) //= -valid_bidSum bidding_i_eq0.
by rewrite add0n eq_bidSum.
Qed.

(* Welfare without i. *)

Notation oStar_i := (oStar).

Section OStarForSearch_i.

Let oStar_id_i (s : slot) : tnth oStar_i s = slot_as_agent s.
Proof. by rewrite tnth_mktuple widen_slot_as_agent. Qed.

Let le_ioStar_io_i (o : O)
    (sortedo : sorted_o o)
    (noio : no_i_in o) :
  star_prefix o oStar_i.
Proof.
case.
elim=> [lt0k|s IH lts1k]; first by rewrite oStar_id_i.
have lt_s_k: s < k by rewrite (@ltn_trans s.+1).
move: (IH lt_s_k). 
set s' := Ordinal lt_s_k; set s'1 := Ordinal lts1k.
have ltos'os'1: tnth o s' < tnth o s'1 by move: (@sortedo s' s'1 (ltnSn s')).
rewrite !oStar_id_i => ltos'os'.
by rewrite (@leq_ltn_trans (tnth o s')).
Qed.

Let no_i_in_oStar_i : no_i_in oStar_i.
Proof.
apply/memPnC/allP/all_tnthP => s. 
rewrite oStar_id -(inj_eq val_inj) /=.
apply/negPf.  
by rewrite gtn_eqF // (@leq_ltn_trans k') // ?leq_ord // not_in_oStar_inv.
Qed.

Let le_welfare_sorted_o_oStar_i (o : O)
    (sortedo : sorted_o o) 
    (noio : no_i_in o) := 
  le_welfare_sorted_o_oS noio no_i_in_oStar_i sortedo (le_ioStar_io_i sortedo noio).

Let le_welfare_noio_o_oStar_i (o : O)
      (noio : no_i_in o) :
  welfare_i o <= welfare_i oStar_i.
Proof.
move: (uniq_bubble_sort_spec (ouniq o)) => [xs] /= [x] sorted_bo.
move: (@le_bubble_sort_welfare xs o noio x). 
set bo := (X in _ <= welfare_i X) => ltwowbo. 
rewrite (@leq_trans (welfare_i bo)) // le_welfare_sorted_o_oStar_i //.
exact: (@notin_ububble _ _ o xs i). 
Qed.

Lemma le_welfare_o_oStar_i_loses (o : O) : welfare_i o <= welfare_i oStar_i.
Proof.
have [] := boolP (no_i_in o) => noio; first exact: le_welfare_noio_o_oStar_i. 
exact: le_welfare_o_oStar_i.
Qed.

End OStarForSearch_i.

Notation bs' := bs.
Notation ls' := ls.

Let argmax_bidSum'': VCG_bidSum'' [arg max_(o > o0) VCG_bidSum'' o] = VCG_bidSum'' oStar_i.
Proof. exact: (argmax_bidSum_oS'' le_welfare_o_oStar_i_loses). Qed.

Let bidSum' := @VCG.bidSum O_finType (biddings bs'). 

Let eq_welfare_without_i''_bidSum' : welfare_without_i'' = bidSum' oStar.
Proof.
rewrite /welfare_without_i'' /VCG.welfare_without_i'' /bidSum'.
rewrite (@bigmax_eq_arg _ o0 _ (fun o => VCG.bidSum'' i (biddings bs) o))//.
move: argmax_bidSum''; rewrite /VCG_bidSum'' => ->.
rewrite /VCG.bidSum'' /VCG.bidSum.
apply: eq_bigr => j _.
rewrite /VCG.bs'' tnth_map ffunE tnth_ord_tuple. 
have [] := boolP (j != i) => [neji|] //.
rewrite negbK => /eqP ->.
by rewrite tnth_map /bidding /t_bidding ffunE tnth_ord_tuple not_i_in_oStar.
Qed.

Let eq_welfare_without_i'' :
  welfare_without_i'' = \sum_(s < k) bid_ctr_slot bs s.
Proof.
rewrite eq_welfare_without_i''_bidSum' /bidSum' /VCG.bidSum.
rewrite bidsSum_sumBid -valid_bidSum bidSum_slot.
apply: eq_bigr => j _.
rewrite /bidding ffunE /bidding /t_bidding /bid_ctr_slot !tnth_map !tnth_ord_tuple.
- have [] := boolP (widen_ord le_k_n j \in oStar_i) => jin.  
  congr ('bid_ _ * 'ctr_ _); first by exact: widen_slot_as_agent.
  rewrite (@slot_in_oStar bs0) //.
  apply: val_inj => /=.
  by rewrite inordK.
- have/not_in_oStar_inv: (widen_ord le_k_n j \in oStar_i) = false. 
    move: jin.
    by apply: contraNF.
  by rewrite ltnNge (leq_ord j).
Qed.  

(** Price equality, when agent [i] loses. *)

Lemma eq_sorted_VCG_price_loses :  
  price bs i = @VCG.price O_finType i (biddings bs) (stable_choice bs).
Proof.
rewrite /price /is_winner tsortK ?idxaK // /price /externality VCG.eq_price'' /VCG.price''.
rewrite -/welfare_without_i'' -/welfare_with_i.
rewrite eq_welfare_without_i'' eq_welfare_with_i.
by rewrite ifF ?subnn // ltnNge leq_eqVlt (not_in_oStar_inv not_i_in_oStar) orbT.
Qed.

End Loses.

Section Wins.

Variable i_in_oStar : i \in oStar.

Definition sOi : slot := slot_of i oStar.

Lemma i_has_slot: (∃ s : slot, i = tnth oStar s).
Proof.
exists (slot_of i oStar).
move: (@elimT _ (i \in oStar) (tnthP oStar i) i_in_oStar).
rewrite /slot_of.
case: tnthP => p //=.
by case: sig_eqW.
Qed.

Lemma not_lt_last_slot_i : (last_slot < i) = false.
Proof.
move: i_has_slot i_in_oStar => [s] ->.
rewrite tnth_map tnth_ord_tuple /=.
by move/ltn_geF: (ltn_ord s).
Qed.

Lemma eq_i_ord0 (eq0k' : k' = 0) : i = ord0.
Proof.
have: i <= k' by rewrite leqNgt; move: not_lt_last_slot_i => ->.
rewrite eq0k' leqn0 => /eqP eqi0.
exact: val_inj.
Qed.

Lemma sum_out F (eq0k' : k' = 0) : \sum_(s < k | i < s) F s = 0.
Proof.
rewrite (eq_bigl (fun s => false)) => [|s]; first exact: big_pred0_eq.
rewrite leq_gtF // eq_i_ord0 // leq_eqVlt.
move/negbT: (only_ord0 s eq0k').
by rewrite negbK => /eqP ->.
Qed.

Lemma sum_split_ge_i F :
  \sum_(s < k | i <= s) F s = F sOi + \sum_(s < k | i < s) F s.
Proof.
rewrite (bigID (fun s : slot => i < s) (fun s : slot => i <= s)) addnC /=.
congr (_ + _).
rewrite [in LHS](eq_bigl (fun s : slot => i < s)) //;
  last by move=> s; rewrite andb_idl //; move/ltnW.
apply: (@big_pred1 _ _ _ _ sOi (fun s => (i <= s) && ~~ (i < s)) F) => s.
rewrite -leqNgt -eqn_leq pred1E /sOi.
move: i_has_slot => [s' -> //=].
rewrite /slot_of.
case: tnthP => p; last by have //=: ∃ i , tnth t_oStar s' = tnth t_oStar i by exists s'.
case: sig_eqW => s'' /=.
by rewrite !tnth_mktuple => /widen_ord_inj ->.
Qed.

Lemma sum_split_i F :
  \sum_(s < k) F s = \sum_(s < k | s < i) F s + F sOi + \sum_(s < k | i < s) F s.
Proof.
rewrite (bigID (fun s : slot => s < i)) /= -addnA.
congr (_ + _).
rewrite (@eq_bigl _ _ _ _ _ (fun s : slot => ~~ (s < i)) (fun s => i <= s));
  last by move=> s; rewrite -leqNgt.
exact: sum_split_ge_i.
Qed.

(* Welfare with i. *)

Lemma eq_VCG_oStar_oStar : (VCG_oStar bs) = oStar.
Proof.
rewrite /(VCG_oStar bs)/(stable_choice bs)/VCG.oStar.
apply: val_inj; rewrite /=.
rewrite eq_t_oStar_oStar.
by apply: val_inj.
Qed.

Let eq_welfare_with_i :
  welfare_with_i = 
  \sum_(s < k | s < i) bid_ctr_slot bs s + \sum_(s < k | i < s) bid_ctr_slot bs s.
Proof. 
rewrite /welfare_with_i /VCG.welfare_with_i /VCG.bidSum_i -/(VCG_oStar bs).
rewrite (bidsSum_sumBid (fun j => j != i)).
apply/eqP; rewrite -(eqn_add2l (bidding bs i (VCG_oStar bs))); apply/eqP.
under (eq_bigl (fun j => true && (j != i))) => j; first by rewrite andTb.
rewrite -(bigD1 i) //= -valid_bidSum /bidding ffunE /t_bidding.  
set siVo := slot_of i (VCG_oStar bs); pose sio := slot_of i oStar.
have finbid : 
  bidSum bs oStar =
    bid_in bs i sio +
      (\sum_(s < k | s < i) bid_ctr_slot bs s + \sum_(s < k | i < s) bid_ctr_slot bs s).
  rewrite /bid_in -/(bid_ctr_agent bs i) eq_bid_ctr -/sOi. 
  rewrite addnA [X in _ = X + _]addnC -(sum_split_i (bid_ctr_slot bs)). 
  exact: bidSum_bid_ctr_slot.
rewrite ifT // /VCG_oStar /=; last by rewrite eq_t_oStar_oStar.
rewrite/siVo eq_VCG_oStar_oStar -/sio.
by rewrite eq_bidSum// finbid.
Qed.

(* Welfare without i. *)

Lemma tcast_bids'' : minn i n + (1 + (n - i.+1)) = n.
Proof.
move/ltnW/minn_idPl: (ltn_ord i) => ->.
by rewrite addnA addn1 addnC subnK.
Qed.

Definition bs'' : bids :=
  tcast tcast_bids'' [tuple of take i bs ++ [:: bid0] ++ (drop i.+1 bs)].

Definition succ_last_slot_agent : A := inord last_slot.+1.

Lemma oStar_i_uniq : uniq (succ_last_slot_agent :: oStar).
Proof.
rewrite cons_uniq.
apply/andP; split; last first.
- rewrite map_inj_uniq /=; first exact: enum_uniq.
  exact: widen_ord_inj.
- rewrite -(@mem_map _ _ val val_inj).
  set l := (X in _ \notin X). 
  have -> /=: l = iota 0 k.
    have sz_oStar: size oStar = k by rewrite !size_map -enumT size_enum_ord.
    apply: (@eq_from_nth _ 0) => [|s]; first by rewrite size_iota size_map.
    rewrite !size_map -enumT size_enum_ord => ltsk.
    rewrite nth_iota // add0n.
    rewrite (@nth_map _ last_agent); last by rewrite sz_oStar.
    rewrite (@nth_map _ last_slot); last by rewrite size_enum_ord.
    by rewrite /= nth_enum_ord.
  rewrite inordK /=; last by exact: lt_k_n.
  by have/(_ k'.+1): forall m, m \notin iota 0 m by move=> ?; rewrite mem_iota add0n ltnn andbF.
Qed.

Definition t_oStar_i := tuple_i oStar succ_last_slot_agent (mem_oStar_inv i_in_oStar).
Definition oStar_i :=  Outcome (tuple_i_uniq (mem_oStar_inv i_in_oStar) oStar_i_uniq).

Section OStarForSearch_i.

Let oStar_id_i (s : slot) :
  tnth oStar_i s = if s < i then slot_as_agent s else agent_succ (slot_as_agent s).
Proof.
move/ltn_eqF: (lt_slot_n' s) => neqsn'.
- have [] := boolP (s < i) => [ltsi|].
  by rewrite id_tuple_i // oStar_id.
- rewrite -leqNgt => leis.
  have [] := boolP (s < k') => [ltsk'|].
  rewrite shifted_tuple_i // tnth_mktuple.
  apply: val_inj => /=.
  by rewrite eq_proper_addS /= neqsn'.
- rewrite -below_last_ord negbK => /eqP ->.
  rewrite last_tuple_i /succ_last_slot_agent /=.
  apply: val_inj => /=.
  move/ltn_eqF: (lt_slot_n' (inord k')); rewrite inordK // => ->.
  by rewrite inordK ?ltnSn ?lt_k_n.
Qed.

Lemma lt_oStar_succ (s : slot) : tnth oStar_i s <= agent_succ (slot_as_agent s).
Proof.
rewrite oStar_id_i.
have [] := boolP (s < i) => ltsi //.
by rewrite ltnW // lt_ord_succ //= lt_slot_n'.
Qed.

Let le_ioStar_io_i (o : O)
      (sortedo : sorted_o o)
      (noio : no_i_in o) :
  forall (s : slot), tnth oStar_i s <= tnth o s.
Proof.
case.
elim=> [lt0k|s IH lts1k]. 
- rewrite oStar_id_i.
  have [] := boolP (0 < i) => [lt0i|] //=.
  rewrite -leqNgt leqn0 => /eqP lei0.
  move: (no_i_tnth (Ordinal lt0k) noio).
  rewrite -(inj_eq val_inj) /= lei0 => /negPf.
  exact: neq0_lt0n. 
- have lt_s_k: s < k by rewrite (@ltn_trans s.+1).
  move: (IH lt_s_k).
  set s' := Ordinal lt_s_k; set s'1 := Ordinal lts1k.
  have ltos'os'1: tnth o s' < tnth o s'1 by move: (@sortedo s' s'1 (ltnSn s')). 
  have eqsuccs's'1: agent_succ (slot_as_agent s') = slot_as_agent s'1.
    apply: val_inj => /=.
    by move/ltn_eqF: (lt_slot_n' s') => ->.
  have nes'1last : slot_as_agent s'1 != last_agent.
    rewrite -(inj_eq val_inj) /=.
    by move/ltn_eqF: (lt_slot_n' s'1) => ->.
  rewrite !oStar_id_i.
  - have [] := boolP (s'1 < i) => [lts'1i|].
    rewrite ifT => [lesos'|]; last by rewrite (@ltn_trans s'.+1). 
    exact: leq_ltn_trans lesos' ltos'os'1.
  - rewrite -leqNgt leq_eqVlt => /orP [/eqP eqis'1|ltis'1].
    - rewrite ifT // => [lesos'|]; last by rewrite eqis'1.
      have: agent_succ (tnth o s') <= tnth o s'1.
       rewrite /agent_succ /= eq_proper_addS //=.   
       exact: leq_trans ltos'os'1 (leq_ord (tnth o s'1)).
      have ltsuccs': agent_succ (slot_as_agent s') <= agent_succ (tnth o s') 
        by exact: ord_succ_mon.
      move=> /(leq_trans ltsuccs').
      rewrite leq_eqVlt => /orP []; last by rewrite lt_le_agent eqsuccs's'1.
      have -> : agent_succ (slot_as_agent s') = i.
        apply: val_inj => /=.
        by rewrite eqis'1 ifF // ltn_eqF //  (lt_slot_n' s').
      by rewrite val_eqE eq_sym no_i_tnth.  
    - rewrite ifF => [ltsuccs'|]; last by rewrite ltnS in ltis'1; move/leq_gtF: ltis'1.
      move: (leq_ltn_trans ltsuccs' ltos'os'1).
      by rewrite lt_le_agent eqsuccs's'1.
Qed.

Let no_i_in_oStar_i : no_i_in oStar_i.
Proof.
apply/memPnC/allP/all_tnthP => s. 
apply/negPf.
- have [] := boolP (s < i) => ltsi.
  by rewrite id_tuple_i // oStar_id -(inj_eq val_inj) /= gtn_eqF.
- have [] := boolP (s < k') => [ltsk'|].
  rewrite shifted_tuple_i //; last by rewrite leqNgt.
  rewrite /t_oStar tnth_mktuple -(inj_eq val_inj) /= eq_proper_addS /=.
  rewrite -leqNgt in ltsi.
  by move/ltn_eqF: (leq_ltn_trans ltsi (ltnSn s)).
- rewrite -below_last_ord negbK => /eqP ->.
  rewrite last_tuple_i /succ_last_slot_agent /=.
  rewrite -(inj_eq val_inj) /= inordK ; last by exact: lt_k_n.
  by move/ltn_eqF: (mem_oStar_inv i_in_oStar).
Qed.

Let le_welfare_sorted_o_oStar_i (o : O)
      (sortedo : sorted_o o)
      (noio : no_i_in o) := 
  le_welfare_sorted_o_oS noio no_i_in_oStar_i sortedo (le_ioStar_io_i sortedo noio).

Let le_welfare_noio_o_oStar_i (o : O)
      (noio : no_i_in o) :
  welfare_i o <= welfare_i oStar_i.
Proof.
move: (uniq_bubble_sort_spec (ouniq o)) => [xs] /= [x] sortedbo.
move: (@le_bubble_sort_welfare xs o noio x). 
set bo := (X in _ <= welfare_i X) => ltwowbo.
have noibo: no_i_in bo by exact: (@notin_ububble _ _ o xs i). 
have: uniq_up_sorted_tuple bo by [].
move/le_welfare_sorted_o_oStar_i => /(_ noibo).
exact: leq_trans.
Qed.

Lemma le_welfare_o_oStar_i_wins (o : O) : welfare_i o <= welfare_i oStar_i.
Proof.
have [] := boolP (no_i_in o) => noio; first exact: le_welfare_noio_o_oStar_i. 
exact: le_welfare_o_oStar_i.
Qed.

End OStarForSearch_i.

Definition bs' := tuple_i bs bid0 (ltn_ord i).

Notation "'bid'_ j" := (tnth bs' j) (at level 10).

Definition ls' := tuple_i ls (tnth ls i) (ltn_ord i).

Notation "'lab'_ j" := (tnth ls' j) (at level 10).

Lemma eq_lab'_id (j : A) : j < i -> 'lab'_j = j.
Proof. by move=> ltji; rewrite id_tuple_i // tnth_ord_tuple. Qed.

Lemma eq_lab'_succ (j : A) (leij: i <= j) (ltjn1 : j < n.-1) : 'lab'_j = agent_succ j.
Proof. by rewrite shifted_tuple_i // tnth_ord_tuple. Qed.

Lemma eq_lab'_last : 'lab'_ord_max = i.
Proof. by rewrite last_tuple_i tnth_ord_tuple. Qed.

Lemma commuting_succ_agent (s : slot) (leis : i <= s) (ltsk' : s < k') :
  slot_as_agent (slot_succ s) = agent_succ (slot_as_agent s).
Proof.
apply: val_inj => //=.
case: s leis ltsk' => [s' p] /= leis lts'k'.
move/ltn_eqF: (lts'k') => -> //=.
by have/ltn_eqF ->: s' < n' by exact: leq_trans lts'k' le_k_n.
Qed.

Lemma eq_in_oStars_out (j : A) (ltk'j : k' < j) :
  (j  \in oStar) = ('lab'_ j  \in oStar_i).
Proof.
move: (mem_oStar_inv i_in_oStar); rewrite ltnS => leik'.
move/ltnW: (leq_ltn_trans leik' ltk'j) => leij.
rewrite (not_in_oStar sorted_bs0) //.
apply/esym/negbTE.
have [] := boolP (j < n') => [ltjn'|].
- rewrite shifted_tuple_i // tnth_ord_tuple -has_pred1 -all_predC.
  apply/all_tnthP => s /=.
  rewrite neq_ltn; apply/orP; left.
  have: agent_succ (slot_as_agent s) < ord_succ j.
    move/ltn_eqF: (lt_slot_n' s) => /= -> /=.
    rewrite /= eq_proper_addS /= ltnS.
    by rewrite (leq_ltn_trans (leq_ord s)). 
  exact: (leq_ltn_trans (lt_oStar_succ s)).
- rewrite -below_last_ord negbK => /eqP ->.
  rewrite eq_lab'_last -has_pred1 -all_predC.
  apply/all_tnthP => s /=.
  have [] := boolP (s < i) => ltsi;
    first by rewrite id_tuple_i // tnth_mktuple -(inj_eq val_inj) ltn_eqF.
  have [] := boolP (s < k') => [ltsk'|].
  - move: ltsi; rewrite -leqNgt => leis.
    rewrite shifted_tuple_i // neq_ltn; apply/orP; right.
    rewrite tnth_mktuple widen_slot_as_agent /=.
    by move: leis; rewrite -ltnS eq_proper_addS.
  - rewrite -below_last_ord negbK => /eqP ->.
    rewrite last_tuple_i -(inj_eq val_inj) /= inordK; last by exact: lt_k_n.
    rewrite neq_ltn; apply/orP; right.
    by rewrite ltnS.
Qed.

Ltac inord_in_oStar j :=
   exists (inord j); rewrite tnth_mktuple;
   apply: val_inj => /=; rewrite inordK //.

Lemma eq_in_oStars (j : A) : (j \in oStar) = ('lab'_j \in oStar_i). 
Proof.
- have [] := boolP (j < i) => [ltji|].
  rewrite eq_lab'_id //=.
  apply/tnthP/tnthP=> [[sj psj]|[sj psj]].
  exists sj; rewrite id_tuple_i //.
  by move: psj ltji => ->; rewrite tnth_mktuple.
  inord_in_oStar j.
  exact: (ltn_trans _ (mem_oStar_inv i_in_oStar)).
- have [] := boolP (j < k') => ltjk'.
  rewrite -leqNgt => leij.
  move: (ltn_trans ltjk' (ltnSn k')) => ltjk.
  move: (leq_trans ltjk' lt_k_n) => lejn'.
  have ltk'n' : k' < n' by move: lt_k_n.
  rewrite eq_lab'_succ //; last by exact: ltn_trans ltjk' ltk'n'.
  apply/tnthP/tnthP=> [[sj psj]|[sj psj]]; last by inord_in_oStar j.
  exists (inord j); rewrite shifted_tuple_i //= ?inordK //. 
  rewrite tnth_mktuple widen_slot_as_agent commuting_succ_agent ?inordK //. 
  congr agent_succ.
  by apply: val_inj => /=; rewrite inordK. 
- rewrite -leqNgt => leij.
  move: ltjk'; rewrite -leqNgt leq_eqVlt => /orP [/eqP eqk'j|ltk'j]; last exact: eq_in_oStars_out.
  apply/tnthP/tnthP => [[sj psj]|[sj psj]].
  - move: (psj) => ->; rewrite tnth_mktuple.
    exists ord_max; rewrite last_tuple_i shifted_tuple_i /= ?tnth_ord_tuple; last first.
    - exact: lt_slot_n'.
    - by move/eqP: psj;  rewrite tnth_mktuple -(inj_eq val_inj) /= => /eqP <-.
    - rewrite /succ_last_slot_agent widen_slot_as_agent.
      have -> /=: sj = last_slot.
        by apply: val_inj => /=; rewrite eqk'j psj tnth_mktuple.
      apply: val_inj => /=; rewrite inordK ?ifF //; last by exact: lt_k_n.
      exact: (ltn_eqF (lt_slot_n' last_slot)).
  - inord_in_oStar j.
    by rewrite eqk'j ltnSn.
Qed.

Lemma eq_slots (j : A) :
  (j \in oStar) -> slot_of j oStar = slot_of ('lab'_j) oStar_i.
Proof.
move=> jino.
move: (jino).
rewrite eq_in_oStars => jino_i.
rewrite (@slot_in_oStar bs) // /slot_of.
move: (@elimT _ _ (tnthP oStar_i ('lab'_j)) jino_i).
case: tnthP => [pj /=|//]. 
case: sig_eqW => sj psj _ //=.
have: 'lab'_j = tnth oStar_i (inord j); last by rewrite psj; move/(@o_injective oStar_i).
have [] := boolP (j < i) => [ltji|].
- have ltjk'1 : j < k'.+1 by exact: ltn_trans ltji (mem_oStar_inv i_in_oStar).
  rewrite eq_lab'_id ?id_tuple_i ?tnth_mktuple // ?inordK //.
  by apply: val_inj => /=; rewrite inordK.
- rewrite -leqNgt => leij.
  have [] := boolP (j < k') => [ltjk'|].
  - have ltjn': j < n' by move: lt_k_n; rewrite -subn_gt0 subSS subn_gt0; exact: ltn_trans ltjk'.
    have ltjk: j < k by exact: ltn_trans ltjk' (ltnSn k').
    rewrite eq_lab'_succ // shifted_tuple_i // ?inordK //.
    rewrite tnth_mktuple; apply: val_inj => /=.
    by rewrite !eq_proper_addS /= ?inordK.
  - rewrite -leqNgt leq_eqVlt => /orP [/eqP eqk'j|];
      last by have -> : (k' < j) = false by 
        move: jino; apply: contraTF => /(not_in_oStar sorted_bs0)/negbT.
    have ltjn': j < n' by rewrite -eqk'j; apply: lt_k_n.
    rewrite eq_lab'_succ //.   
    have -> : tnth oStar_i (inord j) = tnth oStar_i ord_max.
      congr tnth.
      apply: val_inj => /=.
      by rewrite inordK ?eq_sym // -eqk'j ltnSn.
    rewrite last_tuple_i /= /succ_last_slot_agent.
    apply: val_inj => /=.
    by rewrite eq_proper_addS /= inordK eqk'j.
Qed.

Let argmax_bidSum'' : VCG_bidSum'' [arg max_(o > o0) VCG_bidSum'' o] = VCG_bidSum'' oStar_i.
Proof. exact: (argmax_bidSum_oS'' le_welfare_o_oStar_i_wins). Qed.

Let bidSum' := @VCG.bidSum O_finType (biddings bs'). 

Let eq_welfare_without_i''_bidSum' : welfare_without_i'' = bidSum' oStar.
Proof.
rewrite /welfare_without_i'' /VCG.welfare_without_i'' /bidSum'.
rewrite (@bigmax_eq_arg _ o0 _ (fun o => VCG.bidSum'' i (biddings bs) o)) //.
move: argmax_bidSum''; rewrite /VCG_bidSum'' => ->.
rewrite /VCG.bidSum'' /VCG.bidSum.
rewrite (bigID (fun j : A => j < i)) [in RHS](bigID (fun j : A => j < i)) /=.
congr (_ + _).
- apply: eq_bigr => j ltji.
  rewrite !tnth_mktuple !ffunE ifT //; last by move/ltn_eqF/negbT: (ltji).
  rewrite /t_bidding /bid_in id_tuple_i //.
  move: (eq_in_oStars j); rewrite eq_lab'_id // => <-.
  case: ifP => inoS //.
  by rewrite eq_slots ?eq_lab'_id.
- rewrite (bigID (fun j => j == i)) [in RHS](bigID (fun j => j == last_agent)) /=. 
  congr (_ + _).
  - rewrite (big_pred1 i) ?(big_pred1 last_agent) => [|j|j].
    - rewrite !tnth_mktuple !ffunE eq_refl /= /t_bidding. 
      by have/(not_in_oStar sorted_bs0) ->: k' < last_agent by exact: lt_k_n.
    - rewrite pred1E andb_idl; first by rewrite eq_sym.
      by move=> /eqP ->; rewrite -leqNgt leq_ord.
    - rewrite pred1E andb_idl; first by rewrite eq_sym.
      by move=> /eqP ->; rewrite ltnn.  
  - rewrite (@eq_bigl _ _ _ _ _ _ (fun j : A => i < j));
      last by move=> j; rewrite -leqNgt ltn_neqAle eq_sym andbC.
    rewrite [RHS](@eq_bigl _ _ _ _ _ _ (fun j : A => i <= j < last_agent));
      last by move=> j; rewrite -leqNgt below_last_ord.
    rewrite reindex_ge_i ?ltn0Sn //=; last exact: leq_ltn_trans (mem_oStar_inv i_in_oStar) lt_k_n.
    apply: eq_bigr => j /andP [leij ltjn'].
    rewrite !tnth_mktuple !ffunE ifT; 
      last by move/gtn_eqF/negbT: (leq_ltn_trans leij (lt_ord_succ ltjn')).
    rewrite /t_bidding /bid_in shifted_tuple_i //.
    move: (eq_in_oStars j); rewrite eq_lab'_succ /agent_succ // => <-.
    case: ifP => inoS //.
    by rewrite eq_slots ?eq_lab'_succ.
Qed.

Let eq_welfare_without_i'' :
  welfare_without_i'' =
    \sum_(s < k | s < i) bid_ctr_slot bs s +
    \sum_(s < k | i <= s) 'bid_(agent_succ (slot_as_agent s)) * 'ctr_s.
Proof.
rewrite eq_welfare_without_i''_bidSum' /bidSum' /VCG.bidSum.
rewrite bidsSum_sumBid -valid_bidSum bidSum_slot.
rewrite (bigID (fun s : slot => s < i)) //=.
congr (_ + _ ).
- rewrite (eq_bigr (bid_ctr_slot bs)) //= => s ltsi.
  rewrite /bidding ffunE /t_bidding.
  rewrite mem_tnth /bid_in /bid_ctr_slot /slot_of //=.
  case: tnthP => p; last by have //=: ∃ s' : slot, tnth oStar s = tnth oStar s' by exists s.
  case: sig_eqW => s' p' //=.
  rewrite tnth_mktuple widen_slot_as_agent id_tuple_i //. 
  congr (_ * 'ctr__).
  exact: (@o_injective oStar).
- apply: eq_big => s; first by rewrite -leqNgt.
  rewrite -leqNgt /bidding ffunE /t_bidding /bid_in => leis.
  rewrite mem_tnth.
  congr (_ * _); 
    first by rewrite shifted_tuple_i tnth_mktuple -?widen_slot_as_agent //= lt_slot_n'.
  rewrite /slot_of.
  case: tnthP => p; last by have //=: ∃ i : 'I_k, tnth t_oStar s = tnth t_oStar i by exists s.
  case: sig_eqW => s'' /=.
  rewrite !tnth_mktuple.
  by move/widen_ord_inj => ->.
Qed.

(** Price equality, when agent [i] wins. *)

Lemma eq_sorted_VCG_price_wins :  
  price bs i = @VCG.price O_finType i (biddings bs) (stable_choice bs).
Proof.
rewrite /price /is_winner tsortK ?idxaK //. 
rewrite /price /is_winner /externality VCG.eq_price'' /VCG.price''.
rewrite -/welfare_without_i'' -/welfare_with_i.
rewrite eq_welfare_without_i'' eq_welfare_with_i.
rewrite -/bs subnDl.  
- have [] := boolP (k' == 0) => [/eqP eq0k'|].
  rewrite [X in _ = X - _]sum_ord0 //; last by apply: eq_leq; rewrite eq_i_ord0.
  rewrite !sum_out // subn0. 
  have ->: ord0 = last_slot by exact: val_inj.
  by rewrite if_same last_ctr_eq0 /= ?muln0 // eq0k'. 
- have iisslot := (mem_oStar_inv i_in_oStar).
  rewrite -lt0n => lt0k'. 
  under eq_bigr do rewrite mulnBr.
  under big_split_subn => s ltis.
    rewrite leq_mul2l; apply/orP; right. 
    by apply: sorted_ctrs; rewrite leq_pred.
  case: ifP => ltik'; last first.
    have eqik' /= : i = inord k'.
      apply: val_inj => /=.
      rewrite inordK ?(ltn_trans _ lt_k_n)//.
      move: iisslot => /ltnSE.
      by rewrite leq_eqVlt ltik' orbF => /eqP.
    set t := (X in _ = X - _).
    have -> : t = \sum_(s < k | k' == s) 0.
      apply: eq_big => [s|s leis].
      - rewrite leq_eqVlt eqik' inordK ?(ltn_trans _ lt_k_n)//.
        by move: (leq_ord s); rewrite leqNgt => /negPf ->; rewrite orbF.
      - have -> : s = last_slot. 
          apply: val_inj => /=.
          move: leis.
          rewrite eqik' inordK ?(ltn_trans _ lt_k_n)//.
          move: (leq_ord s).
          by rewrite leq_eqVlt ltnNge => /orP [/eqP ->//|/negPf ->].
        by rewrite last_ctr_eq0/= muln0.
     by rewrite sum_nat_const muln0.
  set t := (X in _ - X = _).
  apply/eqP; rewrite -(eqn_add2r t); apply/eqP.
  rewrite !subnK; last first.
  - rewrite leq_sum //= => s _.
    by rewrite leq_mul2l sorted_ctrs ?orbT ?leq_pred.
  - have [] := boolP (i < last_slot) => [ltilast|].
    - rewrite reindex_ge_i ?[X in _ <= X](bigD1 ord_max) //. 
      rewrite big_cropr last_ctr_eq0 //= muln0 add0n leq_sum // => s /andP [leis ltsk'].
      rewrite leq_mul //; last by rewrite sorted_ctrs ?le_ord_succ.
      by rewrite commuting_succ_agent.
    - rewrite -leqNgt leq_eqVlt => /orP [/eqP <-|]; first by rewrite sum0_gt_last.
      by rewrite not_lt_last_slot_i.
  - have [] := boolP (i < last_slot) => [ltilast|].
    - rewrite reindex_ge_i // [in RHS](bigD1 ord_max) //=.
      rewrite big_cropr last_ctr_eq0  //= muln0 add0n. 
      apply: eq_bigr => s /andP [leis ltsk'].
      rewrite /slot_pred /slot_succ cancel_ord_succ //.
      by rewrite commuting_succ_agent.
    - rewrite -leqNgt leq_eqVlt => /orP [/eqP <-|]; last by rewrite not_lt_last_slot_i.
      rewrite sum0_gt_last (bigD1 last_slot) //= last_ctr_eq0 //= muln0 add0n.
      rewrite big_pred0 /last_slot // => j.
      by rewrite below_last_ord ltnNge andbN.
Qed.

End Wins.

Lemma eq_sorted_VCG_price :
  price bs i = @VCG.price O_finType i (biddings bs) (stable_choice bs).
Proof.
have [] := boolP (i < k) => iisslot; 
  first by rewrite eq_sorted_VCG_price_wins // (mem_oStar sorted_bs0).
by rewrite eq_sorted_VCG_price_loses // (not_in_oStar sorted_bs0) // ltnNge.
Qed.

End SortedVCGforSearchPrice.

Section VCGforSearchPrice.

(** VCG for Search price as an instance of General VCG (for unsorted bids). *)

Variable (bs : bids) (i : A).

Let bs' := tsort bs.
Let i' := idxa bs i.
Let l' := tlabel bs. (* not used *)

Lemma sorted_bids_sorted : sorted_bids bs'.
Proof. by apply/sorted_bids_sorted/sort_sorted/total_geq_bid. Qed.

Lemma eq_relabelled_price : price bs' i' = price bs i.
Proof.
rewrite /price /is_winner tsortK //; last exact: sorted_bids_sorted. 
rewrite idxaK //; last exact: sorted_bids_sorted.
Qed.

Definition instance_bidding bs (j : A) := 
  [ffun o' : O => t_bidding (tsort bs) (idxa bs j) o'].

Definition instance_biddings bs := [tuple instance_bidding bs j | j < n].

Lemma relabelled_bidding j o': instance_bidding bs' (idxa bs j) o' = instance_bidding bs j o'.
Proof.
rewrite!ffunE.
rewrite/t_bidding.
rewrite !(idxaK sorted_bids_sorted).
rewrite !(tsortK sorted_bids_sorted).
by [].
Qed.

Lemma sorted_relabelled_bidding j o': instance_bidding bs' j o' = bidding bs' j o'.
Proof.
have sbs' := sorted_bids_sorted.
rewrite !ffunE /t_bidding. 
congr (if _ then _ else _).
by rewrite idxaK.
by rewrite idxaK // tsortK.
Qed. 

Lemma sorted_relabelled_biddings: instance_biddings bs' = biddings bs'.
Proof.
apply: eq_from_tnth => j.
rewrite !tnth_mktuple.
by apply/ffunP => o'; rewrite sorted_relabelled_bidding.
Qed.

Lemma instance_perm_biddings : perm_eq (instance_biddings bs') (instance_biddings bs). 
Proof.
apply/tuple_permP.
exists (perm (@labelling.labelling_inj _ _ _ _ _ (tlabelP bs))).
rewrite -[X in _ = _ X](@eq_from_tnth _ _ (instance_biddings bs')) // => j.
rewrite !tnth_mktuple.
by apply/ffunP => o'; rewrite -relabelled_bidding permE -{1}(cancel_inv_idxa bs j).
Qed.

Definition instance_oStars' := @VCG.oStars O_finType (instance_biddings bs').

Lemma instance_HoStar' : OStar.oStar bs' \in instance_oStars'.
Proof.
rewrite in_set; apply/andP; split; first by [].
apply/forallP=> x; rewrite implyTb.
rewrite ?sorted_relabelled_biddings.
rewrite /VCG.bidSum.
rewrite !bidsSum_sumBid.
rewrite -!valid_bidSum.
rewrite !bidSum_slot.
exact: OStar.le_welfare_o_oStar.
Qed.

Definition instance_stable_choice' (set_oStars : {set O_finType}) := 
  VCG.mkOStar instance_HoStar'.

Definition instance_vcg_price' := 
  @VCG.price O_finType i' (instance_biddings bs') (instance_stable_choice').

Definition instance_oStars := @VCG.oStars O_finType (instance_biddings bs).

Lemma instance_HoStar : OStar.oStar bs' \in instance_oStars.
Proof. 
by rewrite /instance_oStars/= (VCG.perm_oStars instance_perm_biddings) instance_HoStar'.
Qed.

Definition instance_stable_choice (set_oStars : {set O_finType}) := 
  (VCG.mkOStar instance_HoStar).

Definition instance_vcg_price := 
  @VCG.price O_finType i (instance_biddings bs) (instance_stable_choice).

Lemma eq_instance_vcg_price : instance_vcg_price' = instance_vcg_price.
Proof. 
rewrite /instance_vcg_price /instance_vcg_price'.
apply: (@VCG.relabelled_price _ (instance_biddings bs) (instance_biddings bs') _ i i');
  last by [].
- exact: instance_perm_biddings.
- rewrite !tnth_mktuple.
  apply/ffunP => o'.
  exact: relabelled_bidding. 
Qed.

(** Price equality, in all cases. *)
 
Theorem eq_instance_VCG_price :
  price bs i = @VCG.price O_finType i (instance_biddings bs) (instance_stable_choice).
Proof.
rewrite -eq_relabelled_price.
rewrite -/instance_vcg_price.
rewrite -eq_instance_vcg_price //.
rewrite eq_sorted_VCG_price //; last first.
- exact: sorted_bids_sorted.
rewrite/EqualPrice.bs/stable_choice/=.
rewrite/instance_vcg_price'/instance_stable_choice'.
rewrite/VCG.price/VCG.welfare_with_i/VCG.o/=.
rewrite ?sorted_relabelled_biddings.
have eq_bs' : (Tuple (sort_tupleP geq_bid bs)) = bs' by [].
rewrite eq_bs'.
by [].
Qed.
End VCGforSearchPrice.

End EqualPrice.

Check EqualPrice.eq_instance_VCG_price.  
Print Assumptions EqualPrice.eq_instance_VCG_price.


