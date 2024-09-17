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

  Authors: Pierre Jouvelot(+), Lucas Sguerra(+), Emilio Gallego Arias(++).

  Date: October, 2021-2024.

  (+) Mines Paris, PSL University, France
  (++) Inria, France

  Thanks for their insights to the ssreflect community, and in particular Cyril Cohen.

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

Definition utility := value - price bs a.

(* 0 <= utility *)

Theorem VCG_for_Search_rational : price bs a  <= value.
Proof.
rewrite /price -value_is_bid /externality /bid_in ifT; last by exact: awins.
set S := (X in X <= _). 
have : S <= \sum_(s < k | i < s) 
             tnth bs' (slot_as_agent (inord i)) * ('ctr_ (slot_pred s) - 'ctr_ s).
  apply: leq_sum => s lis.
  rewrite leq_mul2r.
  move: (@sorted_bids_sorted bs (slot_as_agent (inord i)) (slot_as_agent s)) => /= -> //.
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
    by rewrite subn0 (@tnth_nth _ _ ctr0) inordK// (@ltn_trans k').
  - have s1k : s.-1 < k by rewrite (@leq_ltn_trans s)// leq_pred.
    rewrite addnC -sum_diff//=.
    - move: (@S.sorted_ctrs (Ordinal s1k) (Ordinal sk)) => /= /(_ (leq_pred s))/=.
      by rewrite !(@tnth_nth _ _ ctr0).
    - have ik : i < k by rewrite (@ltn_trans k').
      have is1 : i <= s.-1 by rewrite -(leq_add2r 1) !addn1 prednK ?1(@ltn_trans i.+1).
      move: (@S.sorted_ctrs (Ordinal ik) (Ordinal s1k)) => /= /(_ is1)/=.
      by rewrite !(@tnth_nth _ _ ctr0).
set bc := (X in _ <= X -> _); set bc' := (X in _ -> _ <= X) => Sbc.
have bb : bc <= bc'.
  rewrite leq_mul// eq_leq//.
  - congr (_ (tnth _ _)).
    rewrite -widen_slot_as_agent/=.
    by apply: val_inj => /=; rewrite inordK// (@ltn_trans k').
  - congr (_ (tnth _ _)).
    apply: val_inj => /=.
    rewrite inordK; last by rewrite (@ltn_trans k').
    apply: esym.
    by apply/minn_idPl; last by rewrite ltnW.
exact: (leq_trans Sbc).
Qed.

End Rationality.

Check VCG_for_Search_rational.
Print Assumptions VCG_for_Search_rational.

(** Relational proof of truthfulness of m2 = VCG for Search, using m1 = General VCG. *)

Section Relational.

Notation agent := 'I_n.
Notation agents := (ord_tuple n).

Definition tlabel_o bs o := Outcome (uniq_map_o bs o).

Definition tidxa_o bs o := Outcome (uniq_to_idxa bs (ouniq o)). 

(* prices and winners *)

(* Type for prices, and, via rationality, prices are always less than bids times ctrs. *)

Definition P := 'I_(p * q).

Definition O := (S.O * k.-tuple P)%type. 

Definition o0 : O := (S.o0, [tuple ord0 | s < k]).

(* Mech2 = VCG for Search. *)

Definition O2 := O.

Notation A2 := bid.
Notation A2s := (n.-tuple A2).

Definition O2_winners a2s := OStar.oStar a2s. 

Definition O2_prices (a2s : A2s) : k.-tuple P := 
  map_tuple (inord \o (fun i => price a2s i)) (O2_winners a2s).  

Definition O2_outcome a2s := (O2_winners a2s, O2_prices a2s).

Definition M2 : A2s -> O2 := O2_outcome.

Definition m2 : mech.type n := mech.new M2.

Definition v2 :agent -> A2 := true_value.

Definition is_winner2 w2 i := slot_of i w2 != last_slot.

Definition p2 : prefs.type m2 :=
  prefs.new v2 
            (fun i (o2 : mech.O m2) => 
               let: s := slot_of i o2.1 in
               if is_winner2 o2.1 i then v2 i * 'ctr_s - tnth o2.2 s 
               else 0)
            v2.

(* Mech1 = General VCG *)

Definition O1 := [finType of O].

Definition G_bound (a1 : {ffun O1 -> nat}) := forall o, a1 o < p * q. (* rationality *)

Definition A1 := {f : {ffun O1 -> nat} | G_bound f}.

Definition f_of_a1 := (@proj1_sig _ G_bound).

Definition S_f_of_a1 (a1 : A1) := [ffun o : S.O => f_of_a1 a1 (o, o0.2)].

Notation A1s := (n.-tuple A1). 

Notation G_biddings a1s := (map_tuple S_f_of_a1 a1s).

Definition O1_winners (a1s : A1s) := G.oStar S.o0 (G_biddings a1s).

Definition O1_prices (a1s : A1s) : k.-tuple P :=
  map_tuple (inord \o (G.price S.o0 ^~ (G_biddings a1s))) (O1_winners a1s).

Definition O1_outcome a1s := (O1_winners a1s, O1_prices a1s).

Definition M1 : A1s -> O1 := O1_outcome.

Definition m1 : mech.type n := mech.new M1.

Definition sig_b (i : agent) (a2 : A2) : {f : {ffun O1 -> nat} | G_bound f}.
Proof. 
exists [ffun o1 : O1 =>  a2 * 'ctr_(slot_of i o1.1)] => o.
by rewrite !ffunE /= ltn_mul.
Defined.

Definition v1 (i : agent) := sig_b i (true_value i). 

Definition p1 : prefs.type m1 :=
  prefs.new 
    v1
    (fun i (o1 : mech.O m1) =>
       if is_winner2 o1.1 i then v2 i * 'ctr_(slot_of i o1.1) - tnth o1.2 (slot_of i o1.1) 
       else 0)
    v1.

(* Truthfulness theorem for m1. *)

Lemma G_rational i (t : A1s) : G.price S.o0 i (map S_f_of_a1 t) < p * q.
Proof. 
move: (G.bid_rational S.o0 i (map S_f_of_a1 t))
        (proj2_sig (tnth t i) (G.oStar S.o0 (map_tuple S_f_of_a1 t), o0.2)). 
rewrite tnth_map ffunE.
exact: leq_ltn_trans.
Qed.

Lemma truthful_General_VCG : truthful p1. 
Proof.
pose v := (fun i => [ffun o : S.O => v2 i * 'ctr_(slot_of i o)]).
move: (@G.truthful_General_VCG [finType of S.O] S.o0 v) => G_truth bs bs' i d av.  
have df : differ_on (map_tuple S_f_of_a1 bs) (map_tuple S_f_of_a1 bs') i.
  move=> j nji.
  rewrite /differ_on /action_on in d *.  
  by rewrite !tnth_map d.
have avf : action_on (map_tuple S_f_of_a1 bs) i = S_f_of_a1 (prefs.v p1 i).
  rewrite /action_on in av *.  
  by rewrite tnth_map av.
have tws : forall (t : A1s) (iw : is_winner2 (O1_winners t) i), 
    tnth (O1_winners t) (slot_of i (O1_winners t)) = i.
  move=> t iw.
  rewrite cancel_slot_inv//.
  move: iw.
  apply: contra_neqT => /negbTE niw.
  by rewrite slot_not_in. 
move: (@G_truth (map S_f_of_a1 bs) (map S_f_of_a1 bs') i) => {G_truth} /(_ df).
rewrite /action_on tnth_map in av avf *.
rewrite avf /v /p1 /= !tnth_map !ffunE !tnth_ord_tuple. 
set ff := (X in S_f_of_a1 _ = X). 
have -> : S_f_of_a1 (v1 i) = ff. by apply: eq_ffun => o; rewrite ffunE. 
move=> /(_ erefl).
have [i't|//] := boolP (is_winner2 (O1_winners bs') i).  
case: ifP => [it /=|/negbFE /eqP nit//]. 
- by rewrite !inordK ?G_rational// /O1_winners !tws.
- by rewrite nit S.last_ctr_eq0/= muln0/= sub0n inordK// ?G_rational// tws.
Qed.

(* Relations, inspired by mech.v but adapted to uniq and position-dependant bids. *)

Definition Ra (as2 : A2s) (i : agent) (a1 : A1) (a2 : A2) : Prop :=
   forall o1 : O1, f_of_a1 a1 o1 = a2 * 'ctr_(slot_of i o1.1).

Definition Ri (as2 : A2s) (as1 : n.-tuple A1) : Prop :=
  (forall i, Ra as2 i (action_on as1 i) (action_on as2 i)) /\
    M1 as1 = M2 as2.
 
Definition fR (as2 : A2s) (i : agent) (a2 : A2) : A1 := sig_b i a2. 

Definition fRi (as2 : A2s) : A1s := [tuple fR as2 i (tnth as2 i) | i < n].

Lemma fRP : forall (as2 : A2s) (i : agent) (a2 : A2), Ra as2 i (fR as2 i a2) a2. 
Proof. 
by move=> as2 i a2 o; rewrite ffunE /=.
Qed.

Lemma fRvP : forall (as2 : A2s) i, fR as2 i (v2 i) = v1 i.
Proof. 
move=> as2 i. 
by apply: eq_sig_hprop => [f|//=]; first exact: Classical_Prop.proof_irrelevance.  
Qed.

(* We prove that, for uniq bids and ctrs, there is unicity of the optimal outcome, 
   except for last_slot, since its ctr being 0, any agent can be used there.

   For non-uniq bids or ctrs, unicity is lost since two agents with equal bids or ctrs
   can be swapped without changing bidSum, i.e., the welfare. *)

Notation diff_last o1 o2 := (forall s : slot, s != last_slot -> tnth o1 s = tnth o2 s).

Lemma max_bidSum_diff_last (a2s : A2s) (o1 o : S.O) (d : diff_last o o1 ) :
  max_bidSum_spec a2s o1 -> max_bidSum_spec a2s o.
Proof.
move=> mx1.
apply: ExtremumSpec => [//|o' _ /=].
rewrite (@leq_trans (bidSum a2s o1))//; first by move: mx1 => [o1'] _ /(_ o' erefl).
rewrite leq_eqVlt; apply/orP; left; apply/eqP.
rewrite !bidSum_slot.
apply: eq_bigr => s _.
rewrite /bidding !ffunE /t_bidding /bid_in !cancel_slot. 
have [/eqP ->|] := boolP (s == last_slot); last by rewrite !mem_tnth => /d ->.
by rewrite !S.last_ctr_eq0 !muln0 !if_same.
Qed.

(* There are thus multiple optimal outcomes oStar in General VCG for VCG for Search, 
   since the last slot has a 'ctr_last_slot equal to 0, which allows any agent to be used
   for that slot in oStar. We impose here in the tuple of agents in the outcome the choice 
   that is defined in VCG_for_Search_as_General_VCG. 

   Recall that, for any bids bs, with VCG_oStar := G.oStar S.o0 (biddings bs), we have
   the lemma VCG_oStar_extremum : max_bidSum_spec VCG_oStar.

   Note that this choice is compatible with the uniqueness required of the outcomes, as proven
   by the lemmas G_oStar_G_biddings lemmas below. *)

Hypothesis G_oStar_biddings_last :
  forall as2 : A2s , 
    tnth (G.oStar S.o0 (biddings as2)) last_slot = tnth (tlabel as2) (slot_as_agent last_slot).

Lemma perm_instance_tsort_biddings (as2 : A2s) :
  perm_eq (instance_biddings as2) (biddings (tsort as2)).
Proof.
apply/tuple_permP.
pose tri := @transitive_geq_bid S.p'.
pose toti := @total_geq_bid S.p'.
pose ai := @anti_geq_bid S.p'.
exists (perm (@labelling.idxa_inj _ _ _ as2 tri toti ai)).
apply: (@eq_from_nth _ [ffun o => 0])=> [|j lj /=]; first by rewrite !size_map.
rewrite !size_map -enumT size_enum_ord in lj.
rewrite (nth_map ord0) ?size_enum_ord// [RHS](nth_map ord0) ?tnth_map ?size_enum_ord//.
by apply: eq_ffun => j'; rewrite permE tnth_ord_tuple. 
Qed.

Lemma G_oStar_instance_biddings_last (as2 : A2s) :
    tnth (G.oStar S.o0 (instance_biddings as2)) last_slot  = slot_as_agent last_slot.
Proof. 
move: (G_oStar_biddings_last (tsort as2)). 
rewrite (@G.eq_oStar _ _ _ (instance_biddings as2)) => [->|]; 
  last exact: perm_instance_tsort_biddings.
by rewrite sorted_tlabel ?tnth_ord_tuple//= sort_sorted.
Qed.

Section Outcome.

Variable (as2 : A2s) (uniq_bs : uniq as2) (uniq_ctrs : uniq S.cs).

Definition a1s_of := [tuple sig_b i (tnth as2 i) | i < n]. 

Lemma S_biddings : G_biddings a1s_of = biddings as2.
Proof.
apply: eq_from_tnth => j.
rewrite !tnth_map !tnth_ord_tuple. 
apply: eq_ffun => o; rewrite ffunE /t_bidding /= /bid_in.
have [//|/negbTE njo] := boolP (j \in o).
by rewrite slot_not_in// ?S.last_ctr_eq0/= ?muln0.
Qed.

Lemma G_oStar_instance : G.oStar S.o0 (instance_biddings as2) = oStar. 
Proof.
apply: val_inj => /=. 
pose as2' := tsort as2.  
have uas2' : uniq as2' by rewrite sort_uniq uniq_bs.
move: (@bidSum_extremums as2') => 
      /(_ _ _ (VCG_oStar_extremum as2') (oStar_extremum as2') uas2' uniq_ctrs) => teq.
apply: eq_from_tnth => s.
have [/eqP ->|/not_ctr0 c0] := boolP (s == last_slot);
  first by rewrite G_oStar_instance_biddings_last tnth_map tnth_ord_tuple widen_slot_as_agent. 
rewrite /VCG_oStar in teq.
move: (teq s c0).
rewrite (@G.eq_oStar _ _ _ (instance_biddings as2)); last by rewrite perm_instance_tsort_biddings.
rewrite eq_oStar_iota//.
exact: sorted_bids_sorted.
Qed.

Lemma G_oStar_G_biddings : G.oStar S.o0 (G_biddings a1s_of) = tlabel_o as2 oStar.
Proof.
rewrite S_biddings.
move: (@bidSum_extremums as2) => 
      /(_ _ _ (VCG_oStar_extremum as2) (oStar_extremum as2) uniq_bs uniq_ctrs) => teq.
apply/val_inj/eq_from_tnth => s/=.
have [/eqP ->|/not_ctr0 c0] := boolP (s == last_slot);
  last by rewrite teq ?tnth_map // widen_slot_as_agent.
by rewrite G_oStar_biddings_last/= !tnth_map tnth_ord_tuple widen_slot_as_agent.
Qed.

Lemma eq_winners : O1_winners a1s_of = O2_winners as2.
Proof.
apply/val_inj/eq_from_tnth => s. 
rewrite !tnth_map tnth_ord_tuple /O1_winners G_oStar_G_biddings !tnth_map.
congr tnth.
by apply/val_inj; rewrite tnth_ord_tuple.
Qed.

Lemma eq_prices : O1_prices a1s_of = O2_prices as2. 
Proof.
apply: eq_from_tnth => s. 
rewrite 2!tnth_map.   
congr (inord _).
rewrite eq_winners.
set i := (tnth _ _). 
rewrite  S_biddings eq_instance_VCG_price ?sorted_relabelled_biddings ?uniq_ctrs//.
rewrite /instance_biddings /instance_bidding /biddings /bidding /t_bidding /bid_in.
congr (_ - _). 
- apply/eqP; rewrite eqn_leq; apply/andP; split. 
  - apply/bigmax_leqP => o _. 
    under [X in X <= _]eq_bigr => j _. rewrite tnth_map ffunE !tnth_ord_tuple. by over.
    rewrite (bigmax_sup (tidxa_o as2 o))//.
    have ij := idxa_inj as2.
    under [X in _ <= X]eq_bigr => j _.
      rewrite tnth_map ffunE !tnth_ord_tuple (labelling_spec_idxa as2) slot_inj ?in_inj_o//. 
    by over => //.
    by [].
  - apply/bigmax_leqP => o _.
    under [X in X <= _]eq_bigr => j _. rewrite tnth_map ffunE !tnth_ord_tuple. by over.
    rewrite (bigmax_sup (tlabel_o as2 o))//.
    under [X in _ <= X]eq_bigr => j _. rewrite tnth_map ffunE !tnth_ord_tuple. by over.
    rewrite eq_leq//.
    apply: eq_bigr => j _.
    rewrite (labelling_spec_idxa as2).
    case: ifP => io; first by rewrite relabel_slot// -labelling_in io.
    by rewrite -labelling_in io.
- rewrite /G.welfare_with_i /G.bidSum_i.
  set oS := (G.oStar _ _); set ioS := (G.oStar _ _).
  under [in LHS]eq_bigr => j _. rewrite tnth_map ffunE !tnth_ord_tuple. by over.
  under [in RHS]eq_bigr => j _. rewrite tnth_map ffunE !tnth_ord_tuple. by over.
  have -> : oS = tlabel_o as2 ioS. 
    by rewrite /ioS G_oStar_instance -G_oStar_G_biddings S_biddings.
  apply: eq_bigr => j _.
  case: ifP => io; first by rewrite relabel_slot// labelling_in io// (labelling_spec_idxa as2).
  by rewrite labelling_in io.
Qed.

Lemma Ri12 : O1_outcome a1s_of = O2_outcome as2.
Proof. by rewrite /O1_outcome eq_winners// eq_prices. Qed.

Lemma fRiP :  Ri as2 (fRi as2).
Proof.
split=> [i|]; last by rewrite /M1 /M2 /O1_winners /fRi /fR -Ri12. 
rewrite /action_on /fRi /Ri tnth_map tnth_ord_tuple /fR /Ra => o /=. 
by rewrite ffunE.
Qed.

Lemma fRdP as2' i (hd : differ_on as2 as2' i) : differ_on (fRi as2) (fRi as2') i.
Proof.
move=> j /hd ha; rewrite /action_on in ha.
rewrite /fRi /action_on !tnth_map !tnth_ord_tuple /fR /=.
apply: eq_sig_hprop => [f|//=]; first by exact: Classical_Prop.proof_irrelevance.  
by apply/ffunP => o; rewrite !ffunE ha.
Qed.

Lemma fRviP i (ha : action_on as2 i = v2 i) : action_on (fRi as2) i = v1 i.
Proof. 
rewrite /action_on /fRi !tnth_map !tnth_ord_tuple in ha *. 
rewrite /fR /v1.
apply: eq_sig_hprop => [f|//=]; first by exact: Classical_Prop.proof_irrelevance.  
by apply/ffunP => o; rewrite !ffunE ha. 
Qed.

End Outcome.

Definition Ro (o1 : O1) (o2 : O2) := o1 = o2.

Lemma MR : forall (bs1 : A1s) (as2 : A2s) (ri : Ri as2 bs1), Ro (m1 bs1) (m2 as2).
Proof.
move=> bs1 as2 [ri1 [ri2 ri3]] /=.
congr (_, _).
rewrite ri2//. 
by apply: val_inj => /=.
Qed. 

Notation U1 := (@prefs.U A1 _ m1 p1).
Notation U2 := (@prefs.U A2 _ m2 p2).

Lemma RelFP : forall o1 o2, Ro o1 o2 -> U1^~o1 =1 U2^~o2.
Proof. 
move=> o1 o2 o12 i.
rewrite /U1 /U2 /p1 /p2.
rewrite /Ro in o12. 
by rewrite !o12.
Qed.

Lemma MP (uniq_ctrs : uniq S.cs) : truthful p1 -> uniq_truthful p2.
Proof. 
move=> h1 as2 u2 as2' u2' i hd1 ht1.
have ho := MR (fRiP u2 uniq_ctrs).
have ho' := MR (fRiP u2' uniq_ctrs).
have hu := RelFP ho.
have hu' := RelFP ho'.
rewrite -hu -hu'.
by apply/h1; [apply/fRdP|apply/fRviP].
Qed.

Lemma VCG_for_Search_uniq_truthful_rel (uniq_ctrs : uniq S.cs) : uniq_truthful p2.
Proof. by apply: MP=> //; exact: truthful_General_VCG. Qed.

End Relational.
 
Check VCG_for_Search_uniq_truthful_rel.
Print Assumptions VCG_for_Search_uniq_truthful_rel.

(* WIP: a direct proof attemps of thruthfulness. *)

Let geq_bid := @geq_bid p'.

Notation lt_labelling a bs bs' l := (@lt_labelling _ _ geq_bid a bs bs' tr totr ar l).
Notation ge_labelling a bs bs' l := (@ge_labelling _ _ geq_bid a bs bs' tr totr ar l).
Notation labelling_differ_on_eq a bs bs' := 
  (@labelling_differ_on_eq _ _ geq_bid a bs bs' tr rr totr ar).
Notation is_labelling bs l := (@is_labelling _ _ geq_bid bs l).  
Notation labellingP bs := (@labellingP _ _ geq_bid bs tr totr ar). 
Notation exists_labellingW bs := (@exists_labellingW _ _ geq_bid bs tr totr ar).

Section TruthfulnessCases.

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

Variable (bs bs' : bids) (a : A).

Variable (ubs : uniq bs) (ubs' : uniq bs').

Variable (diff : differ_on bs bs' a).

Local Definition i := idxa bs a.
Local Definition i' := idxa bs' a.

Variable (bid_true_value : action_on bs a = true_value a).

Lemma rational (awins : i < k') : price bs a <= value bs a.
Proof. 
apply: VCG_for_Search_rational => //.
by rewrite /bid_in /value -bid_true_value (labelling_spec_idxa bs).
Qed.

Definition l := tlabel bs.

Lemma l_inj : injective (tnth l).
Proof. apply: (labelling_inj bs). exact: (tlabelP bs). Qed.

Lemma cancel_a : a = tnth l i. 
Proof. by rewrite cancel_idxa. Qed.

Section iLoses.

Variable (iloses : is_winner bs a = false) (iwins' : is_winner bs' a).

Lemma lt_i'_i : i' < i.
Proof. by rewrite (@leq_trans k') // leqNgt negbT. Qed.

Let l' := lt_labelling a bs bs' l.

Lemma is_labelling_iloses : is_labelling bs' l'.
Proof. 
rewrite /l' /geq_bid.
apply: labelling_differ_on_lt.
- exact: rr.
- exact: diff.
- exact: (tlabelP bs).
- exact: lt_i'_i. 
Qed.

Lemma eq_labelling_loses : projT1 (exists_labellingW bs') = l'.
Proof.
apply: (@labelling_singleton _ _ geq_bid bs'); last by rewrite is_labelling_iloses. 
move: (exists_labellingW bs') => [lab islab]. 
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
move: (labellingP bs') => /forallP /(_ sa)/eqP ->.  
rewrite eq_labelling_loses.
have nea: tnth l' sa != a. 
  apply: (@contraTneq _ _ _ _ _ lti's).
  have <- : tnth l' i' = a by rewrite tnth_mktuple /lt_index //= eq_refl cancel_idxa.
  move/(@labelling.labelling_inj _ _ geq_bid bs' l' is_labelling_iloses)/eqP.
  rewrite -(inj_eq val_inj) /= => /eqP ->.
  by rewrite ltnn.
rewrite d // -(labelling_spec_idxa bs a) -?(labelling_spec_idxa bs (tnth l' sa)).  
have -> : tnth l' sa = tnth l (agent_pred sa).
    rewrite tnth_mktuple /lt_index ifF; last by apply: gtn_eqF.
    by rewrite lti's andTb (@leq_trans k') //= ?leq_ord // leqNgt.
rewrite /l !(cancel_inv_idxa bs) => leis.
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
have -> //:  'ctr_sw - 'ctr_last_slot = \sum_(s < k | sw < s) ('ctr_(slot_pred s) - 'ctr_s).  
  under eq_bigl=> s.
  have -> : (sw < s) = (sw < s <= (last_ord k')). by rewrite leq_ord andbT. over.
  by rewrite sum_diffs // => x y; exact: S.sorted_ctrs.
rewrite big_distrr /= /price /externality// ifT; last by exact: iwins'.
rewrite mini' leq_sum // => s lti's.
by rewrite -tv leq_mul // leq_value_loses.
Qed.

End iLoses.

Section iWins.

Variable (iwins : i < k') (iwins' : i' < k').

Section Overbid.

Variable lt_i'_i : i' < i. 

Let l' := lt_labelling a bs bs' l.

Lemma eq_labelling_over : projT1 (exists_labellingW bs') = l'.
Proof.
apply: labelling_singleton.
- move: (exists_labellingW bs') => [lab islab]. 
  exact: islab.
- apply: labelling_differ_on_lt. 
  - exact: rr.
  - exact: diff.
  - exact: (tlabelP bs).
  - exact: lt_i'_i.
Qed.

Lemma eq_price_bs_over : price bs a = \sum_(s < k | i < s) externality (tsort bs) s.
Proof. by rewrite /price ifT // (@ltn_trans k'). Qed.

Lemma eq_price_bs'_over : 
  price bs' a = \sum_(s < k | i' < s <= i) externality (tsort bs') s + price bs a.
Proof.
rewrite /price /is_winner /externality ifT; last by exact: iwins'.
rewrite ifT; last by rewrite iwins.
rewrite (split_sum_ord lt_i'_i).  
congr (_ + _).
apply: eq_bigr => s ltis.
set j := slot_as_agent s. 
move: (labellingP bs') => /forallP /(_ j) /eqP ->. 
rewrite eq_labelling_over. 
move: (labellingP bs) => /forallP /(_ j) /eqP ->. 
rewrite uniq_labelling /l' tnth_mktuple /lt_index.
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
- rewrite inordK // ?leqnn ?andbT.
  by rewrite -[X in X <= _]addn0 -addn1 -addnA addn0 leq_add2l.
- rewrite big_trim_bound_P //leq_add //; last by apply: IH; rewrite ltnW.
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
move: (labellingP bs') => /forallP /(_ j) /eqP ->. 
rewrite eq_labelling_over tnth_mktuple /lt_index.
rewrite ifF; last by apply: gtn_eqF => /=; rewrite inordK // -[X in X <= _]addn0 ltn_add2l.
rewrite ifT; last by rewrite /j /= inordK // -[X in X < _ <= _]addn0 ltn_add2l //= addnS.
move: diff; rewrite /differ_on /action_on => d.
rewrite d // cancel_a.
move: (labellingP bs) => /forallP /(_ i) /eqP. 
move: (labellingP bs) => /forallP /(_ (ord_pred j)) /eqP. 
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

Let l' := ge_labelling a bs bs' l.

Lemma eq_labelling_under : projT1 (exists_labellingW bs') = l'. 
Proof.
apply: labelling_singleton.
move: (exists_labellingW bs') => [lab islab]; first exact: islab.
apply: labelling_differ_on_ge. 
- exact: rr.
- exact: diff.
- exact: (tlabelP bs).
- by rewrite ltnW.
Qed.

Lemma eq_price_bs'_under : price bs' a = \sum_(s < k | i' < s) externality (tsort bs) s.
Proof.
rewrite /price /is_winner ifT; last by rewrite iwins'.
apply: eq_bigr => s lti's.
rewrite /externality.
set j := slot_as_agent s.
move: (labellingP bs') => /forallP /(_ j) /eqP ->. 
rewrite eq_labelling_under. 
move: (labellingP bs) => /forallP /(_ j) /eqP ->. 
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
rewrite /(price bs) /is_winner ifT; last by rewrite iwins.
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
rewrite -bid_true_value /action_on -[X in _ <= nat_of_ord X](labelling_spec_idxa bs).
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
  rewrite /price /is_winner -/i -/i' iw iw'.
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

Lemma eq_labellling_stable : projT1 (exists_labellingW bs') = l'.
Proof.
apply: (@labelling_singleton _ _ geq_bid bs').
move: (exists_labellingW bs') => [lab islab] //.
apply: (labelling_differ_on_eq a bs bs').
- exact: diff.
- exact: (tlabelP bs).
- by move: eq_i_i'; rewrite /i' leq_eqVlt => ->; rewrite eq_refl.
- exact: eq_i_i'.
Qed.

Lemma truthful_stable : utility bs' a <= utility bs a.
Proof.
rewrite /utility /value.
move: diff; rewrite /differ_on /action_on => d.
have -> : slot_won bs' a = slot_won bs a.
  apply: val_inj => /=.  
  by rewrite (_ : S.idxa bs' a = i') // (_ : S.idxa bs a = i) // -/i -/i' eq_i_i'.
rewrite leq_sub // /price !ifT ?iwins' // eq_leq //.
rewrite (@eq_big _ _ _ _ _ (fun s : slot => i < s) (fun s : slot => i' < s)
                 _ (externality (tsort bs'))) => // [s|s ltis];
  first by rewrite eq_i_i'.
congr (_ * _). 
set sa := slot_as_agent s.
move: (labellingP bs') => /forallP /(_ sa) /eqP ->.
rewrite eq_labellling_stable.
move: (labellingP bs) => /forallP /(_ sa) /eqP ->.
rewrite uniq_labelling /l' d // cancel_a -/i.
apply: (@contraTneq _ _ _ _ _ ltis) => /(labelling_inj bs) => <- /=.
by rewrite ltnn.
exact: (tlabelP bs).
Qed.

End Stable.

Lemma truthful_i_wins : utility bs' a <= utility bs a.
Proof.
have [] := boolP (i' == i) => [/eqP|]; first exact: truthful_stable. 
rewrite neq_ltn => /orP [lti'i|ltii']; first exact: truthful_over.
exact: truthful_under.  
Qed.

End iWins.

Theorem truthful_VCG_for_Search_dir : utility bs' a <= utility bs a.
Proof.  
rewrite /utility. 
have [] := boolP (is_winner bs' a) => [iw'|]. 
- rewrite /is_winner in iw'.
  have [] := boolP(is_winner bs a) => iw //; first by rewrite truthful_i_wins.
  rewrite (@leq_trans 0) // leqn0 subn_eq0 truthful_i_loses //.
  exact: negbTE.
- rewrite /is_winner -leqNgt /value => lek'i'.
  by rewrite after_last_slot // muln0.
Qed.

End TruthfulnessCases.

(** SP is a special case of VCG for Search.

   See Tim Roughgarden (http://timroughgarden.org/f05/ca.pdf) *)
    
Section Sumn.

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

Section Surplus.

(* 3 hypotheses to map VCG for Search into Second Prize. *)

Hypothesis a_single_slot_is_auctionned : S.k' = 0. 

Hypothesis max_ctr_is_1 : S.q' = 1.

Definition ctr1 : 'I_q.  
have lt1q : 1 < q by rewrite /q max_ctr_is_1. 
exact: (Ordinal lt1q).
Defined.

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

Variable v : A -> bid.

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

Definition cw : C.  
have isCvw : sumn vw = 1. 
  rewrite val_tcast sumn_set_nthE /sumn size_map /= !(nth_map iw) ?size_enum_ord ?ltn_ord //.
  rewrite leqNgt ltn_ord /= mul0n subn0 addn0 foldrE (big_nth 0) big_nat.
  under eq_bigr => i /andP [_ ltin].
    rewrite (nth_map iw). over.
    by rewrite size_map in ltin.
  by rewrite big1_eq.
exact (new isCvw).
Defined.

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
  rewrite -(labelling_spec_idxa bs) (cancel_inv_idxa bs) tnth_ord_tuple.
  over.
have -> : \sum_(s < k) tnth [tuple of sort geq_bid bs] (slot_as_agent s) =
         \sum_(0 <= s < k) tnth [tuple of sort geq_bid bs] (inord s). 
  rewrite big_mkord; apply: eq_bigr => s _ /=. 
  congr (_ (tnth _ _)).
  by apply: val_inj => /=; rewrite inordK // (@ltn_trans k) // S.lt_k_n.
rewrite /k a_single_slot_is_auctionned big_nat1 /iw. 
rewrite -(cancel_inv_idxa bs (inord 0)) (labelling_spec_idxa bs) tv /=.
congr (v (tnth _ _)).
by apply: val_inj => /=; rewrite inordK.
Qed.

End Surplus.
