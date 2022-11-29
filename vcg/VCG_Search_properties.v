(**

  VCG_Search_Properties.v

  A formalization project for the Vickrey‑Clarke‑Groves auctions.

  Properties of the "VCG for Search" auction variant.
  - no positive transfer;
  - rationality;
  - truthfulness.

  See Tim Roughtgarden lecture notes for more details.
  (http://timroughgarden.org/f16/l/l15.pdf)

  Authors: Pierre Jouvelot(+), Lucas Sguerra(+), Emilio Gallego Arias(++).

  Date: October, 2021.

  (+) MINES ParisTech, PSL University, France
  (++) Inria, France

  Thanks for their insights to the ssreflect community, and in particular:

   - Cyril Cohen ([VCG_for_Search_truthful], [Canonical]).

  Licence: CeCILL-B.

*)

From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm.

From mech.lib Require Import lib labelling mech.
From mech.vcg Require Import General_VCG VCG_Search_as_General_VCG.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module S := VCG_Search_as_General_VCG.
Module G := VCG.

Let k' := S.k'.
Let p' := S.p'.
Let geq_bid := @geq_bid p'.
Let idxa : bids -> A -> A := idxa geq_bid.

Hypothesis uniq_oStar : forall bs, singleton (max_bidSum_spec bs).

(** No positive transfer. *)

Section No_positive_transfer.

(* 0 <= externality *) 
Theorem VCG_for_search_no_positive_transfer s : 'ctr_s <= 'ctr_(slot_pred s).
Proof. by rewrite S.sorted_ctrs // leq_pred. Qed.

End No_positive_transfer.

(* True value per click *)
Variable (true_value : A -> bid).

(** Rationality *)

Section Rationality.

Variable (bs : bids) (a : A). 

Definition value := true_value a * 'ctr_(slot_won bs a).

Notation bs' := (tsort bs). 
Notation i := (idxa bs a).

Variable (awins : i < S.k').

Variable (value_is_bid : bid_in bs' i (slot_won bs a) = value).

Lemma bidding_value : bidding bs' i (G.oStar o0 (biddings bs')) = value.
Proof.
rewrite /bidding ffunE /t_bidding -/(VCG_oStar bs').
have sortedbs': sorted_bids bs' by exact: sorted_bids_sorted.
move: (oStar_extremum bs'); rewrite eq_oStar_iota // => ox.
move: (@uniq_oStar bs' (VCG_oStar bs') oStar) => /(_  (VCG_oStar_extremum bs') ox) ->. 
rewrite ifT; last by rewrite (mem_oStar sortedbs') // ltnW. 
rewrite -value_is_bid.
by rewrite (@slot_in_oStar bs') // ?wonE // (mem_oStar sortedbs') // ltnW.
Qed.

Definition utility := value - price bs a.

(* 0 <= utility *)
Theorem VCG_for_Search_rational : price bs a  <= value.
Proof.
rewrite (eq_instance_VCG_price uniq_oStar). 
move: (eq_instance_vcg_price uniq_oStar bs a).
rewrite /instance_vcg_price => <-.
move: (@G.rational _ o0 i (biddings bs') (tnth (biddings bs') i) erefl).
by rewrite -bidding_value ?tnth_mktuple // /instance_vcg_price' // sorted_relabelled_biddings.
Qed.

End Rationality.

(** Truthfulness. *)

Section TruthfulnessCases.

Let labelling := @labelling n.

Notation is_labelling := (is_labelling geq_bid).
Notation labelling_spec_idxa := (labelling_spec_idxa geq_bid).

Lemma antimonotone_sorted (bs : bids) : 
  antimonotone (λ s : slot, tnth (tsort bs) (slot_as_agent s)).
Proof.
move=> x y lexy.  
move: (sorted_leq_nth (@transitive_geq_bid p') (@reflexive_geq_bid p')). 
rewrite !(tnth_nth bid0) /lib.geq_bid. 
apply=> //; last by rewrite inE size_tuple ltn_ord. 
- by rewrite sort_sorted //; apply: total_geq_bid.
- by rewrite inE size_tuple ltn_ord.
Qed.

Variable (bs bs' : bids) (a : A) (diff : differ_on bs bs' a).

Local Definition i := idxa bs a.

Local Definition i' := idxa bs' a.

Variable (bid_true_value : action_on bs a = true_value a).

Lemma rational (awins : i < k') : price bs a <= value bs a.
Proof. 
apply: VCG_for_Search_rational => //.
by rewrite /bid_in /value -bid_true_value labelling_spec_idxa.
Qed.

Definition l := tlabel bs.

Lemma l_inj : injective (tnth l).
Proof. exact: labelling_inj (tlabelP geq_bid bs). Qed.

Lemma cancel_a : a = tnth l i. 
Proof. by rewrite cancel_idxa. Qed.

Section iLoses.

Variable (iloses : is_winner bs a = false) (iwins' : is_winner bs' a).

Lemma lt_i'_i : i' < i.
Proof. by rewrite (@leq_trans k') // leqNgt negbT. Qed.

Let l' := lt_labelling geq_bid a bs bs' l.

Lemma is_labelling_iloses : is_labelling bs' l'.
Proof. apply: (labelling_differ_on_lt diff lt_i'_i); exact: tlabelP. Qed.

Lemma eq_labelling_loses : projT1 (exists_labellingW geq_bid bs') = l'.
Proof.
apply: (@labelling_singleton _ _ geq_bid bs'); last by rewrite is_labelling_iloses. 
move: (exists_labellingW geq_bid bs') => [lab islab]. 
exact: islab.
Qed.

Lemma leq_value_loses (s : slot) (lti's : i' < s) : 
  tnth bs a <= tnth (tsort bs') (slot_as_agent s).
Proof.
move: diff; rewrite /differ_on /action_on => d.
move: iloses; rewrite /is_winner => /negbT lek'i. 
apply: (@contraR _ _ _ lek'i).
rewrite -ltnNge.
set sa := slot_as_agent s. 
move: (labellingP geq_bid bs') => /forallP /(_ sa)/eqP ->.  
rewrite eq_labelling_loses.
have nea: tnth l' sa != a. 
  apply: (@contraTneq _ _ _ _ _ lti's).
  have <- : tnth l' i' = a by rewrite tnth_mktuple /lt_index //= eq_refl cancel_idxa.
  move/(labelling_inj is_labelling_iloses)/eqP.
  rewrite -(inj_eq val_inj) /= => /eqP ->.
  by rewrite ltnn.
rewrite d // -(labelling_spec_idxa bs a) -?(labelling_spec_idxa bs (tnth l' sa)). 
have -> : tnth l' sa = tnth l (agent_pred sa).
    rewrite tnth_mktuple /lt_index ifF; last by apply: gtn_eqF.
    by rewrite lti's andTb (@leq_trans k') //= ?leq_ord // leqNgt.
rewrite /l !cancel_inv_idxa => leis.
have ltis1: i < agent_pred sa.
  apply: (@contraLR _ _ _ leis).
  rewrite -!ltnNge !ltnS.
  exact: sorted_bids_sorted.
rewrite (@ltn_trans (agent_pred sa)) //= (@leq_trans s) // ?leq_ord //.
by rewrite ltn_predL (@leq_ltn_trans i').
Qed.

Lemma truthful_i_loses : value bs' a <= price bs' a. 
Proof.
rewrite /value.
move: bid_true_value => tv; rewrite /action_on in tv. 
set sw := slot_won bs' a.
have -> : val ('ctr_sw) = 'ctr_sw - 'ctr_last_slot by rewrite S.last_ctr_eq0 /= subn0.
have mini' : minn i' k' = i' by rewrite /minn ifT.
have ltsw : sw < k' by rewrite /sw /slot_won /= mini'.
have -> //:   'ctr_sw - 'ctr_last_slot = \sum_(s < k | sw < s) ('ctr_(slot_pred s) - 'ctr_s). 
  rewrite (eq_bigl (fun s : slot => sw < s <= (last_ord k'))) => [|s]; last by rewrite leq_ord andbT.
  by rewrite sum_diffs // => x y; exact: S.sorted_ctrs.
rewrite big_distrr /= /price /externality (ltn_trans _ (ltnSn k')) //. 
rewrite mini' leq_sum // => s lti's.
by rewrite -tv leq_mul // leq_value_loses.
Qed.

End iLoses.

Section iWins.

Variable (iwins : i < k') (iwins' : i' < k').

Section Overbid.

Variable lt_i'_i : i' < i. 

Let l' := lt_labelling geq_bid a bs bs' l.

Lemma eq_labelling_over : projT1 (exists_labellingW geq_bid bs') = l'.
Proof.
apply: labelling_singleton.
- move: (exists_labellingW geq_bid bs') => [lab islab]. 
  exact: islab.
- by rewrite labelling_differ_on_lt // tlabelP. 
Qed.

Lemma eq_price_bs_over : price bs a = \sum_(s < k | i < s) externality (tsort bs) s.
Proof. by rewrite /price ifT // (@ltn_trans k'). Qed.

Lemma eq_price_bs'_over : 
  price bs' a = \sum_(s < k | i' < s <= i) externality (tsort bs') s + price bs a.
Proof.
rewrite /price /externality ifT; last by rewrite (@ltn_trans k').
rewrite ifT; last by rewrite (@ltn_trans k').
rewrite (split_sum_ord lt_i'_i).  
congr (_ + _).
apply: eq_bigr => s ltis.
set j := slot_as_agent s. 
move: (labellingP geq_bid bs') => /forallP /(_ j) /eqP ->. 
rewrite eq_labelling_over. 
move: (labellingP geq_bid bs) => /forallP /(_ j) /eqP ->. 
rewrite uniq_labelling /l' /lt_labelling tnth_mktuple /lt_index.
rewrite ifF; last by rewrite -(inj_eq val_inj) /=; apply: gtn_eqF; rewrite (@ltn_trans i).
rewrite ifF; last by rewrite [X in _ && X = _]leqNgt ltis /= andbF.
move: diff; rewrite /differ_on /action_on => d.
rewrite d // cancel_a. 
have: j != idxa bs a by rewrite negbT //;apply: gtn_eqF. 
apply: contraTneq => /l_inj ->.
by rewrite negbK.
Qed.

Lemma truthful_over_ind (B C : slot -> nat) (K : bid)
      (sortedC : antimonotone C)
      (sortedB : antimonotone B) m 
      (Kbound : forall m (ltimi : i' + m < i), K <= B (inord (i' + m.+1))) :
  i' + m <= i ->
  K * (C (inord i') - C (inord (i' + m))) <=
  \sum_(s < k | i' < s <= i' + m) B s * (C (ord_pred s) - C s). 
Proof.
elim: m => [_|m IH lti'm1i]; first by rewrite addn0 subnn muln0. 
have lti'mi : i' + m < i by move: lti'm1i; rewrite addnS.
have lti'mk'1 : i' + m < k'.+1 by rewrite (@leq_trans i) // (@leq_trans k') // ltnW.
have lti'm1k'1 : i' + m.+1 < k'.+1 by rewrite ltnS (@leq_trans i) // ltnW.
rewrite (@sum_diff (C (inord (i' + m)))) ?mulnDr; last first. 
rewrite sortedC // ?inordK ?leq_addl // ?leq_addr // (@ltn_trans k') //. 
rewrite sortedC // !inordK // ?leq_add2l //. 
rewrite (bigD1 (inord (i' + m.+1))) /=; last first.
  rewrite inordK // ?leqnn ?andbT.
  by rewrite -[X in X <= _]addn0 -addn1 -addnA addn0 leq_add2l.
rewrite big_trim_bound_P //leq_add //; last by apply: IH; rewrite ltnW.
by rewrite ord_predK // leq_mul2r Kbound ?orbT // ltnW.
Qed.

Lemma leq_value_over m (lti'mi : i' + m < i) :
  tnth bs a <= tnth (tsort bs') (slot_as_agent (inord (i' + m.+1))).
Proof.
move: iwins iwins' => iw iw'.
rewrite /is_winner in iw iw'.
have lti'mk'1 : i' + m < k'.+1 by rewrite (@leq_trans i) // (@leq_trans k') // ltnW.
have lti'm1k'1 : i' + m.+1 < k'.+1.
  by rewrite addnS; move: (ltn_trans lti'mi iw); rewrite -(@ltn_add2r 1) !addn1.
set j := slot_as_agent (inord (i' + m.+1)).
move: (labellingP geq_bid bs') => /forallP /(_ j) /eqP ->. 
rewrite eq_labelling_over tnth_mktuple /lt_index.
rewrite ifF; last by apply: gtn_eqF => /=; rewrite inordK // -[X in X <= _]addn0 ltn_add2l.
rewrite ifT; last by rewrite /j /= inordK // -[X in X < _ <= _]addn0 ltn_add2l //= addnS.
move: diff; rewrite /differ_on /action_on => d.
rewrite d // cancel_a.
move: (labellingP geq_bid bs) => /forallP /(_ i) /eqP. 
move: (labellingP geq_bid bs) => /forallP /(_ (ord_pred j)) /eqP. 
rewrite !uniq_labelling => <- <-.
apply: sorted_bids_sorted => /=.
rewrite inordK // addnS /= ltnW // cancel_a -/i.
have: ord_pred j != i by rewrite -(inj_eq val_inj) /= inordK // addnS /= negbT // ltn_eqF.
apply: contraTneq => /l_inj <-.
by rewrite negbK.
Qed.

Lemma truthful_over : utility bs' a <= utility bs a.
Proof.
rewrite /utility /value.
have mini : minn i k' = i by rewrite /minn ifT. 
rewrite swap_dist_subl // ?S.sorted_ctrs //= ?rational //.
- have ->:  minn i' k' = i' by rewrite /minn ifT.
  by rewrite mini // ltnW.
- by rewrite eq_price_bs'_over leq_addl.
- move: iwins iwins' => iw iw'.
  rewrite /is_winner in iw iw'.
  rewrite eq_price_bs'_over -addnBA // subnn addn0 -bid_true_value /action_on /externality.
  have -> : val i = i' + (i - i') by rewrite subnKC //= ltnW. 
  have -> : slot_won bs a = inord (i' + (i - i')).
    apply: val_inj => /=.
    by rewrite mini inordK subnKC // ltnW.
  have -> : slot_won bs' a = inord i' by rewrite wonE. 
  apply: truthful_over_ind; last by rewrite subnKC // ltnW.
  - by rewrite /antimonotone => x y; exact: S.sorted_ctrs.
  - exact: antimonotone_sorted. 
  - exact: leq_value_over.
Qed.

End Overbid.

Section Underbid.

Variable lt_i_i' : i < i'. 

Let l' := ge_labelling geq_bid a bs bs' l.

Lemma eq_labelling_under : projT1 (exists_labellingW geq_bid bs') = l'. 
Proof.
apply: labelling_singleton.
move: (exists_labellingW geq_bid bs') => [lab islab]; first exact: islab.
by rewrite labelling_differ_on_ge // ?tlabelP // ltnW.
Qed.

Lemma eq_price_bs'_under : price bs' a = \sum_(s < k | i' < s) externality (tsort bs) s.
Proof.
rewrite /price ifT; last by rewrite (@ltn_trans k').
apply: eq_bigr => s lti's.
rewrite /externality.
set j := slot_as_agent s.
move: (labellingP geq_bid bs') => /forallP /(_ j) /eqP ->. 
rewrite eq_labelling_under. 
move: (labellingP geq_bid bs) => /forallP /(_ j) /eqP ->. 
rewrite uniq_labelling tnth_mktuple /ge_index.
rewrite ifF; last by rewrite -(inj_eq val_inj) /=; apply: gtn_eqF.
rewrite ifF; last by rewrite ltnNge (ltnW lti's) //= andbF.
move: diff; rewrite /differ_on /action_on => d.
rewrite d // cancel_a. 
have: j != idxa bs a by rewrite negbT //; apply: gtn_eqF; rewrite (@ltn_trans i').
by apply: contraTneq => /l_inj ->; last by rewrite negbK.
Qed.

Lemma eq_price_bs_under : 
  price bs a = \sum_(s < k | i < s <= i') externality (tsort bs) s + price bs' a.
Proof.
rewrite /(price bs) ifT; last by rewrite (@ltn_trans k').
by rewrite (split_sum_ord lt_i_i') eq_price_bs'_under addnC.
Qed.

Lemma truthful_under_ind (B C : slot -> nat) (K : bid)
      (sortedC : antimonotone C)
      (sortedB : antimonotone B) m 
      (Kbound : forall m (ltimm' : i + m <= i'), B (inord (i + m)) <= K) :
  i + m <= i' ->
  \sum_(s < k | i < s <= i + m) B s * (C (ord_pred s) - C s) <= 
  K * (C (inord i) - C (inord (i + m))).
elim: m => [_|m IH ltim1i'].
- rewrite addn0.
  under eq_bigl => s do rewrite ltnNge andNb.
  by rewrite big_pred0_eq.
- have ltimi'1 : i + m < i'.+1.
    by rewrite (@ltn_trans i') // (@leq_trans (i + m.+1)) //  ltn_add2l. 
  have ltimk' : i + m < k' by rewrite (@leq_ltn_trans i').
  have tltim1k1 : i + m.+1 < k'.+1 by rewrite addnS.
  rewrite (@sum_diff (C (inord (i + m))) (C (inord i))) //; last first. 
  - by rewrite sortedC // ?inordK ?leq_addr // (@ltn_trans k').
  - by rewrite sortedC // !inordK // ?leq_add2l // (@ltn_trans k') // (@leq_ltn_trans i').
  - rewrite (bigD1 (inord (i + m.+1))) /=; last first.
    - rewrite inordK // ?leqnn ?andbT. 
      by rewrite -[X in X <= _]addn0 -addn1 -addnA addn0 leq_add2l.
    - rewrite big_trim_bound_P //mulnDr leq_add //; last by apply: IH.
      by rewrite ord_predK // leq_mul2r Kbound ?orbT.
Qed.

Lemma geq_value_under m (ltmi'i : i + m <= i') :
  tnth (tsort bs) (slot_as_agent (inord (i + m))) <= true_value a.
Proof.
rewrite -bid_true_value /action_on -[X in _ <= nat_of_ord X]labelling_spec_idxa. 
apply: sorted_bids_sorted.
have -> : val (slot_as_agent (inord (i + m))) = i + m; last by exact: leq_addr.
  by rewrite /= inordK // (@leq_ltn_trans i') // (@ltn_trans k').
Qed.

Lemma truthful_under : utility bs' a <= utility bs a.
Proof.
rewrite /utility.
have mini' : minn i' k' = i' by rewrite /minn ifT. 
rewrite swap_dist_subr // ?S.sorted_ctrs //=. 
- have ->:  minn i k' = i by rewrite /minn ifT.
  by rewrite mini' // ltnW.
- by rewrite eq_price_bs_under leq_addl.
- move: iwins iwins' => iw iw'.
  rewrite /is_winner in iw iw'.
  rewrite /price -/i -/i'.
  have -> : i < k by exact: (ltn_trans iw (ltnSn k')).
  have -> : i' < k by exact: (ltn_trans iw' (ltnSn k')). 
  have eq_ends : \sum_(s < k | i' < s) externality (tsort bs') s = 
                 \sum_(s < k | i' < s) externality (tsort bs) s.
    by rewrite -eq_price_bs'_under // /price ifT //  (@ltn_trans k').
  rewrite (split_sum_ord lt_i_i') eq_ends -addnBA // subnn addn0 /externality.
  have -> : val i' = i + (i' - i) by rewrite subnKC //= ltnW.
  have -> : slot_won bs' a = inord (i + (i' - i)).
    apply: val_inj => /=.
    by rewrite mini' inordK subnKC // ltnW.
  rewrite wonE //.
  apply: truthful_under_ind; last by rewrite subnKC // ltnW. 
  - by rewrite /antimonotone => x y; exact: S.sorted_ctrs.
  - exact: antimonotone_sorted.
  - exact: geq_value_under.
Qed.
  
End Underbid.

Section Stable.

Variable eq_i_i' : i' = i.

Let l' := l.

Lemma eq_labellling_stable : projT1 (exists_labellingW geq_bid bs') = l'.
Proof.
apply: (@labelling_singleton _ _ geq_bid bs').
move: (exists_labellingW geq_bid bs') => [lab islab] //.
by apply/(labelling_differ_on_eq diff eq_i_i')/tlabelP.
Qed.

Lemma truthful_stable : utility bs' a <= utility bs a.
Proof.
rewrite /utility /value.
move: diff; rewrite /differ_on /action_on => d.
have -> : slot_won bs' a = slot_won bs a.
  apply: val_inj => /=.  
  by rewrite (_ : S.idxa bs' a = i') // (_ : S.idxa bs a = i) // -/i -/i' eq_i_i'.
rewrite leq_sub // /price !ifT 1?(@ltn_trans k') // eq_leq //.
rewrite (@eq_big _ _ _ _ _ (fun s : slot => i < s) (fun s : slot => i' < s)
                 _ (externality (tsort bs'))) => // [s|s ltis];
  first by rewrite eq_i_i'.
congr (_ * _). 
set sa := slot_as_agent s.
move: (labellingP geq_bid bs') => /forallP /(_ sa) /eqP ->.
rewrite eq_labellling_stable.
move: (labellingP geq_bid bs) => /forallP /(_ sa) /eqP ->.
rewrite uniq_labelling /l' d // cancel_a -/i.
apply: (@contraTneq _ _ _ _ _ ltis) => /(labelling_inj (tlabelP geq_bid bs)) => <- /=.
by rewrite ltnn.
Qed.

End Stable.

Lemma truthful_i_wins : utility bs' a <= utility bs a.
Proof.
have [] := boolP (i' == i) => [/eqP|]; first exact: truthful_stable. 
rewrite neq_ltn => /orP [lti'i|ltii']; first exact: truthful_over.
exact: truthful_under.  
Qed.

End iWins.

End TruthfulnessCases.

(** Direct proof of truthfulness. *)

Section Truthfulness.

Structure R := Result {awins : bool;
                       price : nat;
                       what : slot}.

Definition A := bid.

Definition O : Type := n.-tuple R.

Definition m := 
  mech.new (fun bs => map_tuple (fun a => Result (is_winner bs a) (S.price bs a) (slot_won bs a))
                             (agent.agents n)).

Definition v : agent.type n -> A := true_value.

Definition p : prefs.type m :=
  prefs.new v 
            (fun a (o : mech.O m) => let r := tnth o a in
                                  if awins r then v a * 'ctr_(what r) - price r else 0)
            v.

Theorem truthful_VCG_for_Search : truthful p.
Proof.  
move=> bs bs' a d tv /=. 
rewrite !tnth_map !tnth_ord_tuple /=. 
case: ifP => iw' //.
case: ifP => iw; first by exact: truthful_i_wins.
by rewrite leqn0 subn_eq0 (@truthful_i_loses bs).
Qed.

End Truthfulness.

(** Relational proof of truthfulness, using General VCG. *)

Section Relational.

Section MechG1. (* General VCG *)

Definition O'1 := O_finType.

Definition o'01 : O'1 := o0.

Definition A1 := G.bidding O'1.

Definition O1 := (n.-tuple nat * O'1)%type.

Definition m1 := G.m o'01.

Definition v1 : agent.type n -> A1 := fun i => [ffun o'1 : O'1 => v i * 'ctr_(slot_of i o'1)].

Definition p1 := G.p o'01 v1.

End MechG1.

Definition Ra i (a1 : A1) (a : A) := forall o'1 : O'1, a1 o'1 = a * 'ctr_(slot_of i o'1).

Definition Ro (o1 : O1) (o : O) := 
  forall j, let r := tnth o j in 
       let: (ps, ws) := o1 in
       let s := slot_of j ws in
       awins r = (s != last_slot) /\ (awins r -> what r = s /\ price r = tnth ps j).

Definition fR i (a : A) : A1 := [ffun o'1 : O'1 => a * 'ctr_(slot_of i o'1)].

Lemma fRP i (a : A) : Ra i (fR i a) a.
Proof. rewrite /Ra /fR /= => o'1. by rewrite ffunE. Qed.

Lemma fRvP i : fR i (v i) = v1 i.
Proof. by []. Qed.

Variable (bs1 : n.-tuple A1) (bs : n.-tuple A).

Variable (Ri1 : Ri Ra bs1 bs).

Lemma eq_GoStar : G.oStar o'01 bs1 = OStar.oStar bs.
Proof.
move: Ri1; rewrite /Ri /Ra /action_on => R'i1.
rewrite -(uniq_oStar (VCG_oStar_extremum bs) (oStar_extremum bs)) /VCG_oStar.
congr G.oStar.
apply: eq_from_tnth => s. 
rewrite tnth_map.
apply/ffunP => o.
rewrite ffunE tnth_ord_tuple /t_bidding /bid_in R'i1.
case: ifP => [//|/slot_not_in ->]; last by rewrite S.last_ctr_eq0 /= muln0.
Qed.

Lemma slot_as_idxa j :
  slot_of j (G.oStar o'01 bs1) = if idxa bs j < k then inord (idxa bs j) else last_slot.
Proof.
rewrite eq_GoStar //.
case: ifP => jino.
- rewrite OStar.slot_in_oStar; last by exact: OStar.mem_oStar.
  by apply: val_inj => /=; rewrite inordK.  
- apply: S.slot_not_in.
  apply: (@contraFF _ _ _ jino).
  exact: OStar.mem_oStar_inv.
Qed.

Lemma idxa_wins_as_slot j :
  (idxa bs j < k') = (slot_of j (G.oStar o'01 bs1) != last_slot).
Proof.
rewrite slot_as_idxa //.  
have [] := boolP (idxa bs j < k') => [ltjk'|].
- rewrite ifT; last by rewrite (@ltn_trans k').
  by rewrite below_last_ord inordK // ltnW.
- rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP eqk'j|];
    last by move=> ltk'j; rewrite ifF ?eq_refl // leq_gtF.                                    
  rewrite (_ : inord (idxa bs j) = last_slot) ?if_same ?eq_refl //.
  apply: val_inj => /=.
  by rewrite inordK // -eqk'j.
Qed.

Lemma slot_won_as_slot_of j (ltijk' : idxa bs j < k') :
  slot_won bs j = slot_of j (G.oStar o'01 bs1).
Proof. by rewrite slot_as_idxa // ifT // ?wonE; last by rewrite (@ltn_trans k'). Qed.

Lemma eq_welfares_i j : 
  VCG.welfare_without_i j (instance_biddings bs) = VCG.welfare_without_i j bs1.
Proof.
rewrite /G.welfare_without_i /G.bidSum_i /G.bidSum.   
pose h := (fun o => Outcome (uniq_map_o bs o)).
pose F := (fun o => \sum_(j0 < n | j0 != j) tnth bs1 j0 o).
rewrite [in RHS](@reindex_inj _ _ _ _ h _ F) /= => [|o1 o2 h12]; last first.
  apply: val_inj => /=. 
  apply: (inj_map_tuple (labelling_inj (tlabelP geq_bid bs))).
  by move/eqP: h12; rewrite -(inj_eq val_inj) => /eqP.
apply: eq_bigr => o _.
apply: eq_bigr => j' _.
rewrite /instance_biddings /instance_bidding /t_bidding tnth_map ffunE !tnth_ord_tuple.
move: (Ri1 j' (h o)); rewrite /action_on => ->.
rewrite /bid_in labelling_spec_idxa.
case: ifP => j'ino; first by rewrite relabel_slot.  
have -> : slot_of j' (h o) = S.last_slot; last by rewrite S.last_ctr_eq0 /= muln0.
  rewrite /slot_of.
  case: tnthP => p //.
  case: sig_eqW => s /= eqj'. 
  apply: (@contraFeq _ _ _ _ _ j'ino) => _.
  by apply/tnthP; exists s; rewrite eqj' tnth_map /S.idxa cancel_inv_idxa.
Qed.

Local Lemma mem_oStar j (ltj'k : idxa bs j < k) : idxa bs j \in oStar. 
Proof.
apply/tnthP; exists (inord (idxa bs j)); rewrite tnth_map tnth_ord_tuple.
apply: val_inj => /=.
by rewrite inordK.
Qed.

Lemma eq_welfares j (ltjk' : idxa bs j < k') :
  VCG.welfare_with_i o0 j (instance_biddings bs) = VCG.welfare_with_i o'01 j bs1.
Proof.
rewrite /G.welfare_with_i /G.bidSum_i /G.bidSum.
rewrite (eq_bigr (fun j => tnth bs1 j (G.oStar o'01 bs1))) // => j' nej'j. 
rewrite eq_instance_vcg_oStar_oStar; last by exact: uniq_oStar. 
rewrite !tnth_mktuple !ffunE /instance_biddings /instance_bidding /t_bidding. 
move: (Ri1 j' (G.oStar o'01 bs1)); rewrite /action_on => ->. 
case: ifP => j'ino.
- rewrite /bid_in labelling_spec_idxa relabel_slot //. 
  congr (_ * 'ctr_ (slot_of _ _)). 
  apply: eq_from_tnth => s /=.
  rewrite eq_GoStar // /OStar.t_oStar !tnth_map.
  congr tnth.
  exact: val_inj.
- have -> : slot_of j' (G.oStar o'01 bs1) = last_slot; last by rewrite S.last_ctr_eq0 /= muln0.
    rewrite slot_as_idxa // ifF //.
    apply: (@contraFF _ _ _ j'ino) => ltj'k. 
    exact: mem_oStar.
Qed.

Lemma MR : Ro (m1 bs1) (m bs).
Proof.
move=> j /=. 
rewrite !tnth_map /= /is_winner !tnth_ord_tuple.   
split=> [|ltjk']; first exact: idxa_wins_as_slot.
split; first exact: slot_won_as_slot_of.
rewrite eq_instance_VCG_price 1?(@ltn_trans k') //; last by exact: uniq_oStar.
by rewrite /instance_vcg_price /VCG.price eq_welfares_i eq_welfares.
Qed.

Notation U := (prefs.U p).
Notation U1 := (prefs.U p1).

Lemma RelFP (o1 : O1) (o : O) : Ro o1 o -> U1^~o1 =1 U^~o. 
Proof.
move=> Ro1 j. 
rewrite /prefs.U /= /v1 (surjective_pairing o1) ffunE. 
move: (Ro1 j).  
rewrite (surjective_pairing o1). 
case: ifP => [w //= [_ /(_ w) [-> ->]] //| /= -> [] /esym /eqP -> _].
by rewrite S.last_ctr_eq0 /= muln0 sub0n.
Qed.

End Relational.

Theorem truthful_VCG_for_Search_rel : truthful p.
Proof.  
apply: (@MP n A1 A m1 m Ra fR p1 p fRP fRvP Ro MR RelFP).
exact: G.truthful_General_VCG.
Qed.

Section Sumn.

Lemma set_nthE T (s : seq T) x0 n x :
  set_nth x0 s n x = if n < size s
    then take n s ++ x :: drop n.+1 s
    else s ++ ncons (n - size s) x0 [:: x].
Admitted.

Lemma sumn_nconsE (s : seq nat) x0 n : sumn (ncons n x0 s) = n * x0 + sumn s.
Proof.
rewrite sumnE (big_nth x0) size_ncons /=.
elim: n => [/=|n IH]; first by rewrite !add0n sumnE [RHS](big_nth x0).
by rewrite addSn big_nat_recl // nth_ncons /= -addn1 IH addnA -mulSn addn1.
Qed.

Lemma sumn_set_nthE (s : seq nat) x0 n x :
  let x' := x + (size s <= n) * (nth x0 s n + (n - size s) * x0) in 
  sumn (set_nth x0 s n x)  = sumn s + x' - nth x0 s n.
Proof.
rewrite set_nthE !sumnE /= [in RHS]leqNgt.
case: ifP => [ltns|_] /=.
- rewrite big_cat big_cons /= mul0n addn0.  
  rewrite (big_nth x0) [X in x + X](big_nth x0) [in RHS](big_nth x0). 
  rewrite big_nat size_take size_drop ltns.  
  under eq_bigr => ? /andP [_ ltis] do rewrite nth_take //. 
  under [X in x + X]eq_bigr => ? _ do rewrite nth_drop. 
  rewrite -big_nat addnC -addnA [in RHS]addnC -addnBA //.
  - congr addn; rewrite [in RHS](@big_cat_nat _ _ _ n) //=; last by rewrite ltnW.  
    rewrite addnC -addnBA //; last by rewrite big_ltn // leq_addr.
    congr addn; rewrite -{3}(add0n n) [in RHS]big_addn.  
    rewrite subnS. 
    under eq_bigr do rewrite addSnnS addnC.
    rewrite -(@big_add1 _ _ _ _ _ predT (fun i => nth x0 s (i + n))).
    by rewrite [in RHS]big_ltn //= ?subn_gt0 // addnC -addnBA ?subnn ?addn0 ?add0n.
  - by rewrite (bigD1_seq n) ?leq_addr ?mem_index_iota /index_iota ?subn0 ?ltns ?iota_uniq.
- rewrite mul1n big_cat //= -addnBA; last by rewrite addnC -addnA leq_addr.
  congr addn; rewrite -sumnE sumn_nconsE /= addn0.
  by rewrite -addnBA ?leq_addr // [nth _ _ _ + _]addnC -addnBA // subnn addn0 addnC.
Qed.

End Sumn.

(** SP is a special case of VCG for Search.

   See Tim Roughgarden (http://timroughgarden.org/f05/ca.pdf) *)
    
Section Surplus.

(* 3 hypotheses to map VCG for Search into Second Prize. *)

Hypothesis a_single_slot_is_auctionned : S.k' = 0.

Hypothesis max_ctr_is_1 : S.q' = 1.

Lemma lt1q : 1 < q.
Proof. by rewrite /q max_ctr_is_1. Qed.
Definition ctr1 := Ordinal lt1q.
Hypothesis all_ctrs_are_1 : forall s, 'ctr_s = ctr1.

(*  A second-price Vickrey auction maximizes surplus, when bidding truthfully, i.e.,
    surplus is equal to max welfare. *)

Variable bs : bids.

Record C := new {
               val : n.-tuple nat;
               _ : sumn val = 1
             }.

Coercion val : C >-> tuple_of.

Variable (c0 : C).

Definition surplus c := \sum_(i < n) v i * tnth c i.

Definition iw := tnth (tlabel bs) ord0.       (* winning agent in SP. *)

Notation sw := (set_nth 0 [tuple 0 | i < n] iw 1).
Local Lemma szn : size sw = n.
Proof.
rewrite size_set_nth /= size_map size_enum_ord.
apply/maxn_idPr.
exact: ltn_ord.
Qed.
Definition vw := tcast szn (in_tuple sw).

Lemma isCvw : sumn vw = 1. 
Proof.
rewrite val_tcast sumn_set_nthE /sumn size_map /= !(nth_map iw) ?size_enum_ord ?ltn_ord //.
rewrite leqNgt ltn_ord /= mul0n subn0 addn0 foldrE (big_nth 0) big_nat.
under eq_bigr => i /andP [_ ltin].
  rewrite (nth_map iw). over.
  by rewrite size_map in ltin.
by rewrite big1_eq.
Qed. 
Definition cw := new isCvw.

Lemma eq_surplus : surplus cw = v iw.
Proof.
rewrite /surplus /cw /welfare /OStar.welfare /bidding /t_bidding /bid_in.
rewrite (@bigD1 _ _ _ _ iw) //= (@tnth_nth _ _ 0) val_tcast /= nth_set_nth /= eq_refl muln1.
under eq_bigr => i ltin.
  rewrite (@tnth_nth _ _ 0) val_tcast /= nth_set_nth /= ifF /=; last exact: negbTE.
  rewrite (nth_map ord0) ?muln0 ?size_enum_ord ?ltn_ord //=. 
  by over => //=.
by rewrite big1_eq addn0. 
Qed.

Lemma surplus_is_VCG_max_welfare (tv : tnth bs =1 v) :
  surplus cw = OStar.max_welfare bs.
Proof. 
rewrite eq_surplus /OStar.max_welfare /OStar.welfare /bidding /t_bidding /OStar.oStar /=.
under [RHS]eq_bigr => s _.
  rewrite ffunE /= mem_tnth /bid_in all_ctrs_are_1 muln1 /OStar.t_oStar tnth_map.
  rewrite -(labelling_spec_idxa geq_bid) cancel_inv_idxa tnth_ord_tuple.
  over.
have -> : \sum_(s < k) tnth [tuple of sort geq_bid bs] (slot_as_agent s) =
         \sum_(0 <= s < k) tnth [tuple of sort geq_bid bs] (inord s). 
  rewrite big_mkord; apply: eq_bigr => s _ /=.
  have -> // : inord s = slot_as_agent s.
    by apply: val_inj => /=; rewrite inordK // (@ltn_trans k) // S.lt_k_n.
rewrite /k a_single_slot_is_auctionned big_nat1 /iw. 
rewrite -(cancel_inv_idxa geq_bid bs (inord 0)) labelling_spec_idxa tv /=.
congr (v (tnth _ _)).
by apply: val_inj => /=; rewrite inordK.
Qed.

End Surplus.

(** Rationality. *)

(* Assume for now divisibility on nats, for simplicity. *)
Hypothesis divisR : forall R, 'ctr_(what R) %| price R.

Definition a := auction.new 
                  (fun (o : mech.O m) i => 
                     let r := tnth o i in
                     if awins r then Some (price r %/ 'ctr_(what r)) else None).

Variable (bid_true_value : forall bs i, action_on bs i = true_value i).

Theorem rational_VCG_for_Search : auction.rational a v. 
Proof.
move=> i o. 
rewrite /auction.p /v /=. 
case: ifP => [|//]. 
rewrite leq_divLR ?divisR //.
have [bs -> /= iw] : exists bs, tnth o i = Result (idxa bs i < S.k') (S.price bs i) (slot_won bs i).
  by admit. 
by rewrite VCG_for_Search_rational // /bid_in /value labelling_spec_idxa 
           -/action_on bid_true_value.
Admitted.


(* Print Assumptions truthful_VCG_for_Search. *)
(* Print Assumptions truthful_VCG_for_Search_rel. *)

