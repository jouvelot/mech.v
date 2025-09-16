(**

  VCG_Search_Properties.v

  A formalization project for the Vickrey‑Clarke‑Groves auction.

  Properties of the VCG for Search auction variant:

  - no positive transfer;
  - rationality;
  - truthfulness (for uniq bids and specified optimal outcomes);
  - SP as a special case of VCG for Search;
  - surplus as maximum welfare.

  See Tim Roughtgarden lecture notes for more details.
  (http://timroughgarden.org/f16/l/l15.pdf)

  Authors: Pierre Jouvelot(+), Lucas Sguerra(+), Emilio Gallego Arias(++), Zhan Jing (+, +++)

  Date: October, 2021-2025.

  (+) Mines Paris, PSL University, France
  (++) Inria, France
  (+++) Jiao Tong University, China

  Thanks for their insights to the ssreflect community, and in particular Cyril Cohen.

  Licence: CeCILL-B.

*)

From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm.

From mech.lib Require Import lib labelling mech.
From mech.absvcg Require Import General Search_as_General.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module S := Search_as_General.

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

Definition utility := if (is_winner bs a) then (value - price bs a) else 0.
Notation bs' := (tsort bs). 
Notation i := (idxa bs a).

Variable (awins : is_winner bs a).

Variable (true_value_is_bid : tnth bs a = true_value a).

Lemma value_is_bid : bid_in bs' i (slot_won bs a) = value.
Proof. by congr (_ * _); rewrite -true_value_is_bid (labelling_spec_idxa bs). Qed.

(* Definition utility := value - price bs a. *)

(* 0 <= utility *)

Lemma leq_price_bidding : price bs a <= tnth bs' i * 'ctr_ (slot_won bs a).
Proof.
rewrite /price/externality ifT; last by exact: awins.
set S := (X in X <= _). 
have : S <= \sum_(s < k | i < s) 
             tnth bs' (slot_as_agent (inord i)) * ('ctr_ (slot_pred s) - 'ctr_ s).
  apply: leq_sum => s lis.
  rewrite leq_mul2r.
  move: (@S.tsorted_bids_sorted bs (slot_as_agent (inord i)) (slot_as_agent s)) => /= -> //.
  apply/orP; right=> //.
  by rewrite inordK ltnW.
rewrite -big_distrr/=. 
have -> : \sum_(s < k | i < s) ('ctr_ (slot_pred s) - 'ctr_ s) = 'ctr_ (inord i). 
  have -> : \sum_(s < k | i < s) ('ctr_ (slot_pred s) - 'ctr_ s) =
             \sum_(i.+1 <= s < k) (nth ctr0 S.cs s.-1 - nth ctr0 S.cs s). 
    rewrite (@big_nat_widenl _ _ _ _ 0)//= big_mkord.
    by apply: eq_bigr => s lis; last by rewrite !(@tnth_nth _ _ ctr0).
  pose F x y := (nth ctr0 S.cs x.-1 - nth ctr0 S.cs y.-1). 
  rewrite (@telescope_big _ _ _ F)/= => [|s /andP [i1s sk]].
  - rewrite ifT// /F.
    move: S.last_ctr_eq0 => /eqP.
    rewrite -(inj_eq val_inj)/= (@tnth_nth _ _ ctr0)/= => /eqP ->.
    by rewrite subn0 (@tnth_nth _ _ ctr0) inordK// (@ltn_trans S.k').
  - have s1k : s.-1 < k by rewrite (@leq_ltn_trans s)// leq_pred.
    rewrite addnC -sum_diff//=.
    - move: (@S.sorted_ctrs (Ordinal s1k) (Ordinal sk)) => /= /(_ (leq_pred s))/=.
      by rewrite !(@tnth_nth _ _ ctr0).
    - have ik : i < k by rewrite (@ltn_trans S.k').
      have is1 : i <= s.-1 by rewrite -(leq_add2r 1) !addn1 prednK ?1(@ltn_trans i.+1).
      move: (@S.sorted_ctrs (Ordinal ik) (Ordinal s1k)) => /= /(_ is1)/=.
      by rewrite !(@tnth_nth _ _ ctr0).
set bc := (X in _ <= X -> _); set bc' := (X in _ -> _ <= X) => Sbc.
have bb : bc <= bc'.
  rewrite leq_mul// eq_leq//.
  - congr (_ (tnth _ _)).
    rewrite -widen_slot_as_agent/=.
    by apply: val_inj => /=; rewrite inordK// (@ltn_trans S.k').
  - congr (_ (tnth _ _)).
    apply: val_inj => /=.
    rewrite inordK; last by rewrite (@ltn_trans S.k').
    apply: esym.
    by apply/minn_idPl; last by rewrite ltnW.
exact: (leq_trans Sbc).
Qed.

Theorem VCG_for_Search_rational : price bs a  <= value.
Proof.
by rewrite -value_is_bid /bid_in leq_price_bidding.
Qed.

Corollary leq0utility : 0 <= utility.
Proof. by have [] := boolP (is_winner bs a)=> aw; rewrite //. Qed.
End Rationality.

Check VCG_for_Search_rational.
Print Assumptions VCG_for_Search_rational.

(* Analysis of swaps of equal bids on utility. *)

Section EqualSwap.

Variable bs0 : bids.

Variable a1 a2 : A. (* i1 et i2 *)

Variable uniq_ctrs : uniq S.cs.

Hypothesis eq_bid0 : tnth bs0 a1 = tnth bs0 a2.

Let rho : {perm A} := tperm a1 a2.

Let c0 := [tuple (tnth bs0 (rho k)) | k < n].

Lemma bids0_swap_eqI : bs0 = c0.
Proof.
apply eq_from_tnth => x; rewrite tnth_map tnth_ord_tuple.
have [/eqP ->|x1] := boolP (x == a1); first by rewrite tpermL eq_bid0.
have [/eqP ->|x2] := boolP (x == a2); first by rewrite tpermR eq_bid0.
by rewrite tpermD 1?eq_sym.
Qed.

Let bs := tsort bs0.

Let i := idxa bs0 a1.

Let j := idxa bs0 a2.

Lemma eq_bid : tnth bs i  = tnth bs j.
Proof.
by rewrite /bs/i/j !labelling.labelling_spec_idxa eq_bid0.
Qed.

Lemma bs_sorted: sorted_bids bs.
Proof. 
by apply/tsorted_bids_sorted.
Qed.

Let sorted_bs := bs_sorted.

Variable true_click_value : A -> nat.

Definition U a v := if is_winner bs0 a then v - price bs0 a else 0.

Definition utility_local a := U a (true_click_value a * 'ctr_(slot_won bs0 a)).
Definition utility_swap a := U (rho a) (true_click_value a * 'ctr_(slot_won bs0 (rho a))).

Corollary stableUtility_notijf a : 
 a1 != a /\ a2 != a -> utility_local a = utility_swap a.
Proof.
rewrite /utility_local/utility_swap/U/is_winner; move=> [ai aj].
by rewrite !tpermD.
Qed.

Hypothesis a1a2 : a1 < a2.

Lemma stable_sort : i < j.
Proof.
move: a1a2; apply: contraLR.
rewrite -!leqNgt.
apply: labelling.idxa_eq_mon; last by [].
exact: reflexive_geq_bid.
Qed.

Let ij := stable_sort.

Lemma slot_as_agentK F (P : slot -> bool) : 
 (forall s : slot, P s -> i <= s <= j) ->
 \sum_(s < k | P s) tnth bs (slot_as_agent s) * F s = tnth bs i * \sum_(s < k | P s) F s.
Proof.
move=> Hij.
rewrite big_distrr/=.
apply: eq_bigr => //= i0 Pi0.
apply/eqP; rewrite eqn_mul2r; apply/orP; right.
rewrite eq_sym eqn_leq {1}eq_bid.
move: (Hij i0 Pi0) => /andP [ii0 i0j].
by apply/andP; split; apply: sorted_bs.
Qed.

Lemma anti_monotonous_ctrs : antimonotone (λ s : 'I_S.k'.+1, 'ctr_ s).
Proof.  by rewrite /antimonotone => x y; exact: S.sorted_ctrs. Qed.

Let ac := anti_monotonous_ctrs.

Lemma a_winner a : is_winner bs0 a = (idxa bs0 a < S.k').
Proof. 
by rewrite /is_winner.
Qed.

Lemma a1winsi : i < S.k' -> slot_won bs i = slot_won bs0 a1.
Proof.
by move=> a1wins; rewrite !wonE -/i ?inordK// ?idxaK// 1?(ltn_trans a1wins).
Qed.

Lemma a2winsj : j < S.k' -> slot_won bs j = slot_won bs0 a2.
Proof.
move=> a2wins; rewrite !wonE -/j ?inordK// ?idxaK// 1?(ltn_trans a2wins).
Qed.

Lemma Uterm : U a1 (tnth bs0 a1 * 'ctr_ (slot_won bs0 a1)) =
                U a2 (tnth bs0 a2 * 'ctr_ (slot_won bs0 a2)).
rewrite -eq_bid0/U/is_winner  -/i -/j.
have [] := boolP (is_winner bs0 a1); rewrite a_winner -/i => a1wins.
- rewrite {1}/price /is_winner -/i a1wins.
  have [] := boolP (is_winner bs0 a2); rewrite a_winner; [|rewrite -leqNgt -/j]=> a2wins.
  - rewrite (split_sum_ord ij) slot_as_agentK=> [|s /andP [lis ->]]; last by rewrite ltnW.
    rewrite addnC subnDAC.
    under eq_bigl=> i0.
      have -> : (i < i0 <= j) = (slot_won bs i < i0 <= slot_won bs j).
        by rewrite !wonE !idxaK ?inordK// 1?(ltn_trans a1wins) // 1?(ltn_trans a2wins).
    over.
    rewrite sum_diffs //=; last by rewrite !idxaK// /minn !ifT.
    rewrite mulnBr subnA //; last first.
    - rewrite labelling.labelling_spec_idxa
      leq_mul2l; apply/orP; right; apply: S.sorted_ctrs.
      by rewrite a1winsi.
    - rewrite leq_mul2l//; apply/orP; right. 
      rewrite !wonE// !idxaK//; apply: S.sorted_ctrs.
      by rewrite !inordK 1?(ltnW ij)// ?(ltn_trans jwins (ltnSn S.k'))// 1?(@ltn_trans S.k').
    - rewrite a2wins labelling.labelling_spec_idxa.
      by rewrite a1winsi // subnn add0n /price /is_winner -/j a2wins a2winsj.
  - rewrite /externality.
    rewrite slot_as_agentK => [|s lis]; last by rewrite ltnW// andTb (@leq_trans S.k')// leq_ord.
    rewrite labelling.labelling_spec_idxa -mulnBr ltnNge a2wins//=.
    apply/eqP; rewrite muln_eq0; apply/orP; right.
    under eq_bigl=> i0.
      have -> : (i < i0) = (slot_won bs i < i0 <= last_slot).
        by rewrite leq_ord andbT wonE idxaK // inordK // (ltn_trans a1wins).
    over.
    rewrite sum_diffs //=; last by rewrite idxaK // /minn ifT.
    by rewrite S.last_ctr_eq0 subn0 a1winsi// subnn.
- rewrite -(negbK (i < S.k')) a1wins//= ifF//.
  apply: negbTE; rewrite -leqNgt leq_eqVlt;  apply/orP; right. 
  by rewrite (leq_ltn_trans _ ij)// leqNgt.
Qed.

Lemma utility_swap_invariant_a1 :
  true_click_value a1 = tnth bs0 a1 -> utility_local a1 = utility_swap a1.
Proof.
move=> vb.
rewrite/utility_local/utility_swap vb {2}eq_bid0 tpermL.
exact: Uterm.
Qed.

Lemma utility_swap_invariant_a2 : 
  true_click_value a2 = tnth bs0 a2 -> utility_swap a2 = utility_local a2.
Proof.
move=> vb.
rewrite/utility_local/utility_swap vb -{1}eq_bid0 tpermR.
exact: Uterm.
Qed.

Lemma truthful_utility_swap_invariant a :
  true_click_value a = tnth bs0 a -> utility_local a = utility_swap a.
Proof.
have [/eqP|] := boolP (a1 == a) => ifa1; first by
  rewrite -ifa1; apply utility_swap_invariant_a1.
- have [/eqP|] := boolP (a2 == a) => ifa2. 
  - rewrite -ifa2 => truthfula2.
    apply/eqP; rewrite eq_sym; apply/eqP.
    move: truthfula2.
    apply utility_swap_invariant_a2.
- by rewrite stableUtility_notijf.
Qed.

Lemma bs0_labelling_spec_idxa a : tnth bs0 a = tnth bs (idxa bs0 a).
Proof.
by rewrite labelling.labelling_spec_idxa.
Qed.

Lemma positive_ctrs (s : slot) : s < last_slot -> 0 < 'ctr_ s. 
Proof.
apply: contra_ltn. 
rewrite leqn0.
move: S.last_ctr_eq0 => /eqP.
rewrite -(inj_eq val_inj)/= !(tnth_nth ord0) => /eqP <- /eqP eqnn.
move: uniq_ctrs => /(uniqP ord0)/(_ s S.last_slot).
rewrite !inE !size_tuple => /(_ (ltn_ord s) (ltn_ord S.last_slot)) => ->//=.
exact: val_inj.
Qed.

Lemma leq_price_bid a : 
  price bs0 a <= tnth bs0 a * 'ctr_ (slot_won bs0 a).
Proof.
rewrite/price.
have [] := boolP (is_winner bs0 a); [|rewrite a_winner; rewrite -leqNgt]=> awins//.
move: (leq_price_bidding awins).
by rewrite/price ifT// bs0_labelling_spec_idxa.
Qed.

Lemma underbid_utility_swap_inferior_a1 :
  tnth bs0 a1 < true_click_value a1 -> utility_swap a1 <= utility_local a1.
Proof.
move=> underbida1.
rewrite/utility_local/utility_swap tpermL/U.
have [] := boolP (is_winner bs0 a1); rewrite a_winner -/i; [|rewrite -leqNgt] => a1wins.
- have [] := boolP (is_winner bs0 a2); last by [].
  rewrite a_winner -/j => a2wins.
  (* LHS *)
  rewrite -(@subn0 (true_click_value a1 * 'ctr_ (slot_won bs0 a2))).
  rewrite -(@subnn (tnth bs0 a2 * 'ctr_ (slot_won bs0 a2))).
  rewrite subnA //; last first.
    rewrite leq_pmul2r.
      by rewrite -eq_bid0; apply: ltnW.
    apply: positive_ctrs.
    by rewrite wonE -/j ?inordK //; apply: (ltn_trans a2wins); rewrite ltnSn.
  (* RHS *)
  rewrite -(@subn0 (true_click_value a1 * 'ctr_ (slot_won bs0 a1))).
  rewrite -(@subnn (tnth bs0 a1 * 'ctr_ (slot_won bs0 a1))).
  rewrite subnA //; last first.
    rewrite leq_pmul2r.
      exact: ltnW.
    apply: positive_ctrs.
    by rewrite wonE -/i ?inordK //; apply: (ltn_trans a1wins); rewrite ltnSn.
  rewrite -!mulnBl -addnBA; last by apply: leq_price_bid.
  rewrite -addnBA; last by apply: leq_price_bid.
  apply: leq_add.
  - rewrite -eq_bid0.
    rewrite leq_mul2l; apply/orP; right.
    apply: ac.
    rewrite !wonE // -/i-/j !inordK ltnW //.
  - rewrite leq_eqVlt; apply/orP; left.
    move/eqP: Uterm.
    by rewrite {1}eq_sym/U !ifT.
- rewrite ifF // a_winner -/j.
  apply: negbTE; rewrite -leqNgt.
  by apply: (leq_trans a1wins); apply: ltnW.
Qed.

Lemma overbid_utility_swap_superior_a1 : 
  true_click_value a1 < tnth bs0 a1 -> utility_local a1 <= utility_swap a1.
move=> overbida1.
rewrite/utility_local/utility_swap tpermL/U.
have [] := boolP (is_winner bs0 a1); rewrite a_winner -/i; [|rewrite -leqNgt //] => a1wins.
have overbida1_imp : true_click_value a1 * 'ctr_ (slot_won bs0 a1) <=
  tnth bs0 a1 * 'ctr_ (slot_won bs0 a1).
by rewrite leq_pmul2r ?(ltnW overbida1) //;
 apply: positive_ctrs;
 rewrite wonE -/i -/j ?inordK //; apply: (ltn_trans a1wins); rewrite ltnSn.
have [] := boolP (is_winner bs0 a2); rewrite a_winner -/j; [|rewrite -leqNgt] => a2wins.
- (* LHS *)
  all: rewrite -(@subn0 (true_click_value a1 * 'ctr_ (slot_won bs0 a1))).
  all: rewrite -(@subnn (tnth bs0 a1 * 'ctr_ (slot_won bs0 a1))).
  (* RHS *)
  rewrite -(@subn0 (true_click_value a1 * 'ctr_ (slot_won bs0 a2))).
  rewrite -(@subnn (tnth bs0 a2 * 'ctr_ (slot_won bs0 a2))).
  all: rewrite !subnCBA //. (* SEE HERE *)
  all: rewrite subnAC.
  rewrite (@subnAC _ (tnth bs0 a2 * 'ctr_ (slot_won bs0 a2)) (price bs0 a2)).
  all: rewrite addnC.
  rewrite (@addnC (tnth bs0 a2 * 'ctr_ (slot_won bs0 a2))).
  all: rewrite -addnBA; last by apply: leq_price_bid.
  rewrite -(@addnBA (true_click_value a1 * 'ctr_ (slot_won bs0 a2)) _ _);
    last by apply: leq_price_bid.
  all: rewrite subDnCAC ?overbida1_imp //.
  rewrite subDnCAC; 
    [|by rewrite -eq_bid0; rewrite leq_pmul2r ?(ltnW overbida1) //;
     apply: positive_ctrs;
     rewrite wonE -/i -/j ?inordK //; apply: (ltn_trans a2wins); rewrite ltnSn].
  apply: leq_sub.
  - rewrite leq_eqVlt; apply/orP; left.
    move/eqP: Uterm.
    by rewrite /U !ifT //.
  - rewrite -eq_bid0 -!mulnBl leq_pmul2l; last by rewrite subn_gt0.
    apply: ac.
    by rewrite !wonE // -/i-/j !inordK ltnW.
rewrite subBnAC.
apply: leq_sub; first by [].
have eq_price_bid : price bs0 a1 = tnth bs0 a1 * 'ctr_ (slot_won bs0 a1).
(* similar proof as part of Uterm *)
  rewrite/price ifT // /externality -/i.
  rewrite slot_as_agentK => [|s lis]; last by rewrite ltnW// andTb (@leq_trans S.k')// leq_ord.
  rewrite labelling.labelling_spec_idxa.
  apply/eqP; rewrite eqn_mul2l; apply/orP; right.
  under eq_bigl=> i0.
      have -> : (i < i0) = (slot_won bs i < i0 <= last_slot).
        by rewrite leq_ord andbT wonE idxaK // inordK // (ltn_trans a1wins).
  over.
  rewrite sum_diffs //=; last by rewrite idxaK // /minn ifT.
  by rewrite S.last_ctr_eq0 subn0 a1winsi// subnn.
by rewrite -addnABC ?eq_price_bid ?overbida1_imp // leq_addr.
Qed.

End EqualSwap. 

Check utility_swap_invariant_a1.
Check underbid_utility_swap_inferior_a1.
Check overbid_utility_swap_superior_a1.

(** Relational proof of truthfulness of m2 = VCG for Search, using m1 = General VCG. *)

Section Relational.

Notation agent := 'I_n.
Notation agents := (ord_tuple n).

(* Type for prices, and, via rationality, prices are always less than 
   |agents| * |bids| * |ctrs|. *)

Variable r : nat.

Definition P := 'I_(n * r).+1.

Notation A2 := bid.
Notation A2s := (n.-tuple A2).

Definition a2s0 : A2s := mktuple (fun b => S.bid0).

Definition O := [finType of (S.O * k.-tuple P * A2s)].

Definition o0 : O := ((S.o0, mktuple (fun p => ord0)), mktuple (fun b => bid0)).

(* Mech2 = VCG for Search. *)

Definition O2 := O.

Definition O2_winners a2s := OStar.oStar a2s. 

Definition O2_prices (a2s : A2s) : k.-tuple P := 
  map_tuple (inord \o (fun i => price a2s i)) (O2_winners a2s).  

Definition O2_outcome a2s := (O2_winners a2s, O2_prices a2s, a2s).

Definition M2 : A2s -> O2 := O2_outcome.

Definition m2 : mech.type n := mech.new M2.

Definition v2 : agent -> A2 := true_value.

Definition is_winner2 w2 i := slot_of i w2 != last_slot.

Definition p2 : prefs.type m2 :=
  prefs.new v2 
            (fun i (o2 : mech.O m2) => 
               let: s := slot_of i o2.1.1 in
               if is_winner2 o2.1.1 i then v2 i * 'ctr_s - tnth o2.1.2 s 
               else 0)
            v2.

(* Mech1 = General VCG *)

Notation O1 := O.

Definition o10 : O1 := o0.

Notation A1 := (VCG.bidding O1). 
Notation A1s := (VCG.biddings O1).

Section M1.

Variable G_choice : VCG.OStar_choice O1.

Definition O1_winners (a1s : A1s) := (proj1_sig (G_choice (VCG.oStars_ne0 o10 a1s))).1.1.

Definition O1_prices (a1s : A1s) : k.-tuple P := 
  map_tuple 
    (inord \o (fun i => VCG.price o10 i a1s G_choice))
    (O1_winners a1s).

Definition O1_outcome a1s := (O1_winners a1s, O1_prices a1s, a2s0).

Definition M1 : A1s -> O1 := O1_outcome.

Definition m1 : mech.type n := mech.new M1.

Definition v1 (i : agent) : A1 := [ffun o : O1 => true_value i * 'ctr_ (slot_of i o.1.1)].

Definition is_winner1 w1 i := slot_of i w1 != last_slot.

Definition p1 : prefs.type m1 :=
  prefs.new 
    v1
    (fun i (o1 : mech.O m1) => 
       if is_winner1 o1.1.1 i then 
         v1 i o1 - tnth o1.1.2 (slot_of i o1.1.1)
       else 0)
    v1.

Variable bid_bounded : forall (a1s : A1s) i o, tnth a1s i o <= r. 

Lemma price_bounded a1s i : VCG.price o10 i a1s G_choice < (n * r).+1.
Proof.
rewrite /VCG.price.
apply: (@leq_ltn_trans (VCG.welfare_without_i i a1s)); first by rewrite leq_subr.
apply/bigmax_leqP => o1 _.
rewrite /VCG.bidSum_i.
apply: (@leq_trans (\sum_(j < n) tnth a1s j o1)); first by rewrite [leqRHS](bigD1 i)//= leq_addl.
apply: (@leq_trans (\sum_(j < n) r)).
- apply: (@leq_sum _ _ _ (fun j => tnth a1s j o1) (fun j => r)) => j _; first by exact: bid_bounded.
  by rewrite sum_nat_const cardE size_enum_ord.
Qed.

(* Truthfulness theorem for m1. *)

Lemma slot_in i o : slot_of i o != last_slot -> i \in o.
Proof. by apply: contra_neqT => /negPf/slot_not_in. Qed.

Lemma truthful_General_VCG : truthful p1.
Proof.
move=> bs bs' i d tv.  
pose oGc1 := G_choice (VCG.oStars_ne0 o10 bs).
have tvi : action_on bs i = prefs.v (VCG.p (proj1_sig oGc1) G_choice v1) i by rewrite tv.
move: (@VCG.truthful_General _ o10 G_choice v1 bs bs' i d tvi). 
rewrite /VCG.p /VCG.m/=.
case: ifP => // iw'.
case: ifP => iw.
- rewrite /is_winner1 in iw' iw.
  rewrite !tnth_map !tnth_ord_tuple/= !ffunE. 
  by rewrite !inordK  !cancel_slot_inv ?slot_in ?price_bounded //.
- rewrite !ffunE /is_winner1 /O1_winners/= in iw *.
  have -> : (slot_of i (proj1_sig oGc1).1.1 = last_slot) 
    by move: iw; apply: contraFeq.
  rewrite S.last_ctr_eq0/= muln0 sub0n leqn0 => /eqP/=.
  rewrite !tnth_map !tnth_ord_tuple.
  by rewrite !inordK !cancel_slot_inv ?slot_in// ?price_bounded// leqn0 => ->.
Qed.

End M1.

(* m1-m2 relations, inspired by mech.v but adapted to position-dependant bids (a2s). *)

Definition set_pick' (T : finType) (s : {set T}) : s != set0 -> {o | o \in s}.
move=> /set0Pn/sigW [x p].
exact: (exist (fun x => x \in s) x p).
Defined.

Definition P1 := fun s : {set O1} => {o1 : O1 | o1 \in s}.

Definition G_choice (a1s : A1s) (op : O1) (s : {set O1}) (s0 : s != set0) : {o | o \in s} :=
  let: os := VCG.oStars a1s in
  match inspect (os == s) with
  | exist true a1ss =>
      match inspect (op \in os) with
      | exist true opin => @eq_rect _ os P1 (@VCG.sig_OStar O1 a1s op opin) s (eqP a1ss)
      | exist false _ => set_pick' s0
      end
  | exist false _ => set_pick' s0
end.

Lemma G_choice_op (a1s : A1s) (op : O1) (s : {set O1}) (s0 : s != set0) 
  (opin : op \in VCG.oStars a1s) (oss : VCG.oStars a1s = s) :
  G_choice a1s op s0 = @eq_rect _ (VCG.oStars a1s) P1 (@VCG.sig_OStar O1 a1s op opin) s oss.
Proof.
rewrite /G_choice. 
case: (inspect (VCG.oStars a1s == s)).
case=> [ps|]; last by move=> oss'; rewrite oss eqxx in oss'.
case: (inspect (op \in VCG.oStars a1s)).
case=> [po //|p]; last by rewrite opin in p.
have/(_ (op \in VCG.oStars a1s) po opin) -> // : forall b (p1 : b = true) (p2 : b), p1 = p2.
  by case => [/= p1 p2| p1 p2//]; apply: eq_irrelevance.
by congr (eq_rect _); by apply: eq_irrelevance.
Qed.

Lemma G_choice_nop (a1s : A1s) (op : O1) (s : {set O1}) (s0 : s != set0) 
  (opnin : op \notin VCG.oStars a1s) : 
    G_choice a1s op s0 = set_pick' s0. 
Proof.
rewrite /G_choice.
case: (inspect (VCG.oStars a1s == s)).
case=> [ps|//].  
case: (inspect (op \in VCG.oStars a1s)). 
by case=> [p|p //]; first by rewrite p in opnin.
Qed.

Section Relations.

Definition Ra (i : agent) (a1 : A1) (a2 : A2) : Prop :=
   forall o1 : O1, a1 o1 = a2 * 'ctr_(slot_of i o1.1.1).
 
Definition fR (i : agent) (a2 : A2) : A1 := 
  [ffun o1 : O1 =>  a2 * 'ctr_(slot_of i o1.1.1)].

Definition fRi (a2s : A2s) : A1s := [tuple fR i (tnth a2s i) | i < n].

Lemma o2_in_ofRi2 a2s : O2_outcome a2s \in VCG.oStars (fRi a2s).
Proof.
rewrite inE andTb. 
apply/forallP => o1.
apply/implyP => _.
rewrite /O2_outcome /O2_winners/=. 
move: (OStar.le_welfare_o_oStar a2s o1.1.1). 
rewrite /OStar.max_welfare /OStar.welfare -!bidSum_slot => bx.
rewrite /VCG.bidSum.
under eq_bigr => i _. rewrite tnth_map ffunE tnth_ord_tuple; over.
under [in leqRHS]eq_bigr => i _. rewrite tnth_map ffunE tnth_ord_tuple; over.
move: bx => /=.
have eqo : forall o, bidSum a2s o = \sum_(i < n) tnth a2s i * 'ctr_ (slot_of i o).
  move=> o.
  apply: eq_bigr => i _.
  rewrite tnth_map ffunE tnth_ord_tuple /t_bidding /bid_in.
  case: ifP => [//|/slot_not_in ->].
  by rewrite S.last_ctr_eq0/= muln0.
by rewrite !eqo.
Qed.

Lemma Ri_ofRi a1s a2s : mech.Ri Ra a1s a2s -> a1s = fRi a2s.
Proof.
move=> mri.
apply: eq_from_tnth => j.
rewrite /mech.Ri /action_on /Ra in mri.
apply/ffunP => o1.
by rewrite mri /fRi tnth_map /fR ffunE tnth_ord_tuple.
Qed.

Definition Ri (a1s : A1s) (a2s : A2s) : Prop :=
  (forall i, Ra i (action_on a1s i) (action_on a2s i)) /\ 
    let: o2 := O2_outcome a2s in
    let: oS := VCG.oStars a1s in
    o2 \in oS.

Lemma fRP : forall (i : agent) (a2 : A2), Ra i (fR i a2) a2. 
Proof. 
by move=> i a2 o; rewrite ffunE /=.
Qed.

Lemma fRvP : forall i, fR i (v2 i) = v1 i.
Proof. by []. Qed.

End Relations.

Section Outcome.

Lemma fRiP (a2s : A2s) :  Ri (fRi a2s) a2s .
Proof.
split; first by move=> i o; rewrite /action_on tnth_map /fR ffunE tnth_ord_tuple. 
by have o2f : O2_outcome a2s \in VCG.oStars (fRi a2s) by exact: o2_in_ofRi2.  
Qed.

Lemma fRdP a2s a2s' i (hd : differ_on a2s a2s' i) : differ_on (fRi a2s) (fRi a2s') i.
Proof. 
move=> j /hd ha; rewrite /action_on in ha.
rewrite /fRi /action_on !tnth_map !tnth_ord_tuple /fR /=.
apply: eq_ffun => o.
by rewrite ha.
Qed.

Lemma fRviP a2s i (ha : action_on a2s i = v2 i) : action_on (fRi a2s) i = v1 i.
Proof. 
rewrite /action_on /fRi !tnth_map !tnth_ord_tuple in ha *. 
rewrite /fR /v1.
apply: eq_ffun => o.
by rewrite ha.
Qed.

End Outcome.

Definition Ro (o1 : O1) (o2 : O2) := o1.1 = o2.1.

Definition p0 : P := @ord0 (n * r).

Definition ps0 : k.-tuple P := [tuple p0 | j < k].  
 
Notation cancel_idxa bs := (@labelling.cancel_idxa _ _ geq_bid bs tr totr ar).

Lemma MRx a1s a2s (acts : (forall i, Ra i (action_on a1s i) (action_on a2s i)))i  :
  \max_o \sum_(j < n | j != i) tnth a1s j o =
    \max_o \sum_(j < n | j != i) tnth (instance_biddings a2s) j o.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply/bigmax_leqP => o _.
  have uidxa : forall o : S.O, uniq (map_tuple (fun i => idxa a2s i) o).
    move=> o'; apply/(tuple_uniqP ord0).
    by move=> i1 i2; rewrite !tnth_map => /(idxa_inj a2s)/o_injective.
  have -> : \sum_(j < n | j != i) tnth a1s j o =
             \sum_(j < n | j != i) tnth (instance_biddings a2s) j (Outcome (uidxa o.1.1)).
    apply: eq_bigr => j nji.
    rewrite acts tnth_map ffunE /t_bidding /bid_in !tnth_ord_tuple (labelling_spec_idxa a2s)/=.
    rewrite slot_inj; last by exact: (idxa_inj a2s).
    rewrite in_inj_o; last by exact: (idxa_inj a2s).
    by case: ifP => // /slot_not_in ->; rewrite S.last_ctr_eq0 muln0.
  by rewrite leq_bigmax_cond.
- apply/bigmax_leqP => o _.
  have ulab : forall o : S.O, (uniq (map_tuple (tnth (tlabel a2s)) o)).
    by move=> o'; exact: (uniq_from_idxa a2s (ouniq o')). 
  have -> : \sum_(j < n | j != i) tnth (instance_biddings a2s) j o =
             \sum_(j < n | j != i) tnth a1s j (Outcome (ulab o), ps0, a2s).
    apply: eq_bigr => j nji.
    rewrite acts tnth_map ffunE /t_bidding /bid_in !tnth_ord_tuple (labelling_spec_idxa a2s)/=.
    have -> : (slot_of j (map_tuple (tnth (tlabel a2s)) o)) = 
               (slot_of (tnth (tlabel a2s) (idxa a2s j)) (map_tuple (tnth (tlabel a2s)) o)).
      by congr (slot_of _); rewrite labelling.cancel_idxa.
    rewrite slot_inj; last by exact: (labelling_inj a2s (tlabelP a2s)).
    by case: ifP => // /slot_not_in ->; rewrite S.last_ctr_eq0 muln0.
  by rewrite leq_bigmax_cond.
Qed.

Lemma MR (a1s : A1s) (a2s : A2s) (ri : Ri a1s a2s) : 
  Ro (m1 (G_choice a1s (O2_outcome a2s)) a1s) (m2 a2s).
Proof.
move: (ri) => [acts o2in].
have Gc1:     
  let: o2 := O2_outcome a2s in
  let: oS := VCG.oStars a1s in
  forall (o2in : o2 \in oS), G_choice a1s o2 (VCG.oStars_ne0 o10 a1s) = VCG.sig_OStar o2in.
  move=> o2in'.
  by rewrite G_choice_op.
congr (_, _) => //; first by rewrite /O1_winners /O2_winners /= Gc1.
apply: eq_from_tnth => s.
rewrite !tnth_map/= /O1_winners tnth_ord_tuple.
congr (inord _).
rewrite eq_instance_VCG_price/=.
rewrite Gc1 tnth_map tnth_ord_tuple.
set i := (X in VCG.price _ X).
have <- : i = tnth (tlabel a2s) (slot_as_agent s) by []. 
rewrite /VCG.price /VCG.welfare_with_i /VCG.welfare_without_i /=.  
rewrite /VCG.bidSum /VCG.bidSum_i.
congr (_ - _); first by exact: MRx.
rewrite /Ra /action_on in acts.
have tOs : (map_tuple (tnth (tlabel a2s)) oStar) = OStar.t_oStar a2s.
  by apply: eq_from_tnth => t; rewrite !tnth_map widen_slot_as_agent.
apply: eq_bigr => j _.
rewrite acts tnth_map -relabelled_bidding tnth_ord_tuple sorted_relabelled_bidding /VCG.oStar.  
pose oo := (OStar.oStar (tsort a2s) \in VCG.oStars (instance_biddings a2s)).
 case: (inspect oo). 
case=> [p/=|p].  
- rewrite OStar.stable_choice_in// G_choice_op/=.
  rewrite /bidding ffunE /t_bidding /bid_in (labelling_spec_idxa a2s).
  case: ifP => [jin|/=].
  - congr (_ * 'ctr_ _) => /=.
    rewrite (relabel_slot jin) -tOs eq_oStar_iota//.
    exact: tsorted_bids_sorted.
  - rewrite [in LHS]eq_t_oStar_oStar; last by exact: tsorted_bids_sorted. 
    move=> xi.
    move: (slot_not_in xi).
    have -> : slot_of (idxa a2s j) oStar = slot_of j (OStar.t_oStar a2s).
      rewrite /OStar.t_oStar /slot_of.
      case: tnthP => [[w hw]|hw]; first by rewrite hw /oStar/= mem_tnth in xi. 
      case: tnthP => [[l pj]|//].
      rewrite pj tnth_map tnth_ord_tuple labelling.cancel_inv_idxa in hw.
      have // : (∃ i : 'I_k, slot_as_agent l = tnth oStar i).
        exists l.
        rewrite tnth_map tnth_ord_tuple.
        by apply: val_inj.
    move=> ->.
    by rewrite S.last_ctr_eq0/= muln0.
- move: (instance_HoStar' a2s) => q.
  rewrite /instance_oStars' -(VCG.perm_oStars (instance_perm_biddings a2s)) in q.
  by rewrite /oo q in p.
Qed.

Definition U1 a1s (o1 : O1) := (@prefs.U A1 _ (m1 (G_choice a1s o1)) (p1 (G_choice a1s o1))).
Definition U2 := (@prefs.U A2 _ m2 p2).

Lemma RelFP (a1s : A1s) (o1 : O1) (o2 : O2) : 
  Ro o1 o2 -> forall (i : A), (@U1 a1s o1) i o1 = @U2 i o2.
Proof. 
move=> ro i.
rewrite /U1/U2 /p1 /p2/=.
rewrite /Ro in ro.
by rewrite /v1 /v2 !ffunE !ro.
Qed.

(*
  All prices are bounded in VCG for Search. This needs to be added to General VCG explicitly.
*)

Hypothesis bid_bounded : forall (a1s : A1s) i o, tnth a1s i o <= r. 

(* 
  We define a new "singleton_truthful" property that is restricted only to a2s tuples 
  that have the singleton property (in a way similar to "uniq_truthful").
*)

Definition oStars_singleton (a2s : A2s) := #|VCG.oStars (fRi a2s)| = 1.

(* 
   For informations, we relaten oStars_singleton to the direct VCG for Search "singleton" 
   restriction. 
*)

Lemma fRi_max_bidSum (a2s : A2s) : 
  oStars_singleton a2s -> singleton (max_bidSum_spec a2s).
Proof.
move=> oS1.
move=> o1 o2 {o1 o2} [o1 _ x1] [o2 _ x2].
pose o1': O1 := (o1, mktuple (fun p => ord0), a2s); 
pose o2' : O1 := (o2, mktuple (fun p => ord0), a2s).
have bGb : forall (o' : O), bidSum a2s o'.1.1 = VCG.bidSum (fRi a2s) o'.
  move=> o'. 
  apply: eq_bigr => i _.
  rewrite /fRi /fR /biddings /bidding /t_bidding /bid_in !tnth_map tnth_ord_tuple !ffunE /=.
  case: ifP => [//|/slot_not_in ->]; last by rewrite S.last_ctr_eq0/= muln0. 
have o'S (o' : O) : 
  (∀ j : S.O, predT j -> geq (bidSum a2s o'.1.1) (bidSum a2s j)) -> o' \in VCG.oStars (fRi a2s).
  move=> x'.
  rewrite inE andTb.
  apply/forallP => o.
  apply/implyP => _.
  rewrite -!bGb. 
  exact: x'.
have eqos (x y : O1) (xin : x \in VCG.oStars (fRi a2s)) (yin : y \in VCG.oStars (fRi a2s)) : 
  x = y by have /eq_leq/cards01P/(_ x y) := oS1; apply.
move: (eqos o1' o2' (o'S o1' x1) (o'S o2' x2)).
by case.
Qed.

Lemma max_bidSum_fRi a2s x : VCG.oStars (fRi a2s) = [set x] -> max_bidSum_spec a2s x.1.1.
Proof.
move=> oSx.
move: (set11 x); rewrite -oSx => xin.
apply: ExtremumSpec=> // o _ /=.
have bGb : forall (o : O_finType), let: o' := (o, mktuple (fun p => ord0), a2s) in
                              bidSum a2s o = VCG.bidSum (fRi a2s) o'.
  move=> o'. 
  apply: eq_bigr => i _.
  rewrite /fRi /fR /biddings /bidding /t_bidding /bid_in !tnth_map tnth_ord_tuple !ffunE /=.
  by case: ifP => [//|/slot_not_in ->]; last by rewrite S.last_ctr_eq0/= muln0. 
rewrite (bGb o).
have bGbx : bidSum a2s x.1.1 = VCG.bidSum (fRi a2s) x.
  apply: eq_bigr => i _.
  rewrite /fRi /fR /biddings /bidding /t_bidding /bid_in !tnth_map tnth_ord_tuple !ffunE /=.
  by case: ifP => [//|/slot_not_in ->]; last by rewrite S.last_ctr_eq0/= muln0. 
rewrite bGbx.
move: xin.
pose o' : O1 := (o, [tuple ord0  | _ < k], a2s).
by rewrite inE => /andP [_]/forallP /(_ o')/implyP/(_ erefl).
Qed.

Notation partial_truthful := @Partial.partial_truthful.
Notation partial_MP := @Partial.partial_MP.

Lemma Search_singleton_truthful_rel : @partial_truthful _ _ oStars_singleton _ p2.
Proof. 
move=> [a2s g2] [a2s' g2'] i hd2 hv2.  
have ho := MR (fRiP a2s).
have ho' := MR (fRiP a2s').
rewrite /Ro in ho ho'.
set g' := G_choice (fRi a2s') (O2_outcome a2s').
set G' := G_choice (fRi a2s') (m1 g' (fRi a2s')).
have eqGc' bs o : 
  oStars_singleton bs -> (m1 (G_choice (fRi bs) o) (fRi bs)).1 = (m1 G' (fRi bs)).1.
  move=> /eq_leq/cards01P eqos.
  pose oS := VCG.oStars (fRi bs); pose oSne0 := VCG.oStars_ne0 o10 (fRi bs).
  have o2in : sval (G_choice (fRi bs) o oSne0) \in oS.
    exact: (@proj2_sig _ (fun x => x \in oS)). 
  have g'in : sval (G_choice (fRi a2s') (M1 g' (fRi a2s')) oSne0) \in oS.
    exact: (@proj2_sig _ (fun x => x \in oS)). 
  congr (_, _); first by rewrite /O1_winners (@eqos _ _ o2in g'in).
  apply: eq_from_tnth => s.
  rewrite !tnth_map/= /O1_winners/= /m1 (@eqos _ _ o2in g'in). 
  rewrite /VCG.price /VCG.welfare_with_i/= /VCG.bidSum_i.
  congr (inord (_ - _)).
  apply: eq_bigr => j no2.
  by rewrite !tnth_map/= !tnth_ord_tuple /fR !ffunE /VCG.oStar (@eqos _ _ o2in g'in).
have MR' : ∀ (bs1 : n.-tuple A1) (bs2 : A2s),
    oStars_singleton bs2 -> mech.Ri Ra bs1 bs2 → Ro (m1 G' bs1) (m2 bs2). 
  move=> bs1 bs2 g1 mri.
  have := @MR bs1 bs2. 
  rewrite (Ri_ofRi mri) /Ro eqGc'//.
  apply=> //.
  split=> //; last by rewrite o2_in_ofRi2.
  by rewrite /mech.Ri -(Ri_ofRi mri).
have RelFP' : ∀ (o1 : mech.O (m1 G')) (o2 : mech.O m2),
    Ro o1 o2 → (prefs.U (p1 G'))^~ o1 =1 (prefs.U p2)^~ o2.
  by move=> o1 o2 ro12; apply: RelFP; first by exists (fRi a2s); rewrite size_tuple.
apply: (partial_MP _ _ _ oStars_singleton _ _ (p1 G') p2 _ _ fRP fRvP _ MR' RelFP') => //.
exact: truthful_General_VCG.
Qed.

End Relational.

Check Search_singleton_truthful_rel.
Print Assumptions Search_singleton_truthful_rel.



