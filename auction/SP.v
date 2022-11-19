(**

  SP.v
  
  Second Prize, as mech.v mechanism.

  Reference: see Tim Roughgarden's Lecture note #13 CS269I.

  Proofs :
  - SP is rational.
  - SP is truthful.
  - SP is Pareto-optimal.
  - Provide 2 Nash equilibria (default and "Wolf and Sheep").

  Pierre Jouvelot (30/6/2021).

  Licence: CeCILL-B.

*)
 
From Coq Require Import Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp.fingroup Require Import perm.

From mech.lib Require Import lib labelling mech.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variable (n'' : nat).

Definition n' := n''.+1.
Definition n := n'.+1.

Definition A := agent.type n.

Notation last_agent := (@agent.last n).
Notation agent_succ := (@agent.succ n').
Notation agent_pred := (@agent.pred n).

Variable p' : nat.
Definition p := p'.+1.
Definition bid := 'I_p.
Definition bid0 : bid := Ordinal (ltn0Sn p').
Definition bids := n.-tuple bid.

Let geq_bid := @geq_bid p'.

Notation tsort := (tsort geq_bid).
Notation idxa := (idxa geq_bid).

Section Algorithm.

Variable (bs0 : bids) (i : A).

Let bs := tsort bs0.
Let i' := idxa bs0 i.

Definition i0 : A := ord0.

Definition is_winner := (i' == i0).
Definition price : nat := tnth bs (agent_succ i').

End Algorithm.

Section Prices.

Notation is_labelling := (is_labelling geq_bid).
Notation tlabel := (tlabel geq_bid).

Definition labelling_of (bs : bids) : labelling _ := xchoose (exists_labelling geq_bid bs).

Lemma tsorted_bids_sorted (bs : bids) : sorted_bids (tsort bs).
Proof.
apply/sorted_bids_sorted.
apply: sort_sorted.
exact: total_geq_bid.
Qed.

Section BothWin.

Variable (bs bs' : bids) (a : A) (diff : differ_on bs bs' a).

Let i := idxa bs a.
Let i' := idxa bs' a.

Variable (iwins : i = i0) (iwins' : i' = i0).

Let l := tlabel bs.

Lemma bs_uniq_labelling : projT1 (exists_labellingW geq_bid bs) = l. 
Proof. exact: uniq_labelling. Qed.

Let l' := l.

Definition over_bids := [tuple tnth bs' (tnth l' j) | j < n].

Lemma max_first j : tnth bs' j <= tnth bs' a.
Proof.
rewrite -(labelling_spec_idxa geq_bid bs' a) -(labelling_spec_idxa geq_bid bs' j).
apply: tsorted_bids_sorted.
by move: iwins'; rewrite /i' => ->.
Qed.

Lemma sorted_over_bids : sorted_bids over_bids. 
Proof.
move=> j1 j2 lej1j2.
rewrite !tnth_map !tnth_ord_tuple.
move: diff.
rewrite /differ_on /action_on => d.
- have [] := boolP (j1 == i0) => [/eqP eqj10|].
  - have [] := boolP (j2 == i0) => /eqP eqj20.
    by rewrite eqj10 eqj20.
  - by rewrite eqj10 -iwins cancel_idxa  max_first.
- rewrite -lt0n => lt0j1. 
  have inva : a = tnth l i by rewrite cancel_idxa.
  have netnth (j : A) : j != i -> tnth (projT1 (exists_labellingW geq_bid bs)) j != tnth l i.
    apply: contra_neq.
    rewrite bs_uniq_labelling.
    apply: labelling_inj.
    exact: tlabelP.
  rewrite !d /l' -?bs_uniq_labelling ?inva.
  move: (labellingP geq_bid bs) => /forallP /(_ j2) /eqP <-.
  move: (labellingP geq_bid bs) => /forallP /(_ j1) /eqP <-. 
  exact: tsorted_bids_sorted.  
  by have/netnth: j1 != i by rewrite iwins -(inj_eq val_inj) /= -lt0n.
  by have/netnth: j2 != i by rewrite neq_ltn [X in _ || X](@leq_trans j1) // iwins ?orbT.
Qed.

Lemma perm_over_bids : perm_eq bs' over_bids.
Proof.
have xbs' : bs' = [tuple tnth bs' j | j < n].
  apply: eq_from_tnth => j.
  by rewrite tnth_map tnth_ord_tuple.
rewrite {1}xbs' /=. 
set arg2 := (X in perm_eq _ X).
have -> : arg2 = [seq tnth bs' j | j <- map (tnth l') (enum 'I_n)]. 
  apply: (@eq_from_nth _ bid0) => [|j ltjs]; first by rewrite !size_map.
  rewrite size_map size_enum_ord in ltjs.
  by rewrite !(@nth_map _ i0) // ?size_map -?enumT ?size_enum_ord. 
apply: perm_map.
rewrite map_tnth_enum -(sort_inj_ord (labelling_inj (tlabelP geq_bid bs))). 
by rewrite perm_sort perm_refl.
Qed.

Lemma is_over_labelling : labelling_of bs' = l'.
Proof.
have sorted: sorted_bids over_bids by exact: sorted_over_bids.
have sorting := 
  sorted_sort (@transitive_geq_bid p') (iffLR (sorted_bids_sorted over_bids) sorted).
have sortedbs': sort geq_bid bs' = over_bids.
  rewrite -sorting.
  apply/perm_sortP => //.
  exact: total_geq_bid.
  exact: transitive_geq_bid. 
  exact: anti_geq_bid.
  exact: perm_over_bids.
have: is_labelling bs' l'.
  apply/eqP.
  apply: eq_from_tnth => j.
  rewrite !tnth_map !(tnth_nth bid0) tupleE /= sortedbs'.
  rewrite (@nth_map _ j _ bid0) ?(tnth_nth bid0);
    last by rewrite size_enum_ord ltn_ord.
  by rewrite val_ord_tuple nth_ord_enum.
have: is_labelling bs' (labelling_of bs') by apply: xchooseP.
exact: labelling_singleton.
Qed.  

Lemma eq_winning_price  :
  tnth (tsort bs') (agent_succ i0) = tnth (tsort bs) (agent_succ i0). 
Proof.
set i1 := agent_succ i0. 
move: (labellingP geq_bid bs') => /forallP /(_ i1) /eqP ->.
move: (labellingP geq_bid bs) => /forallP /(_ i1) /eqP ->.
have -> : projT1 (exists_labellingW geq_bid bs') = l'.
  apply: labelling_singleton.
  move: (exists_labellingW geq_bid bs') => [lab islab].
  exact: islab.
  by rewrite -is_over_labelling tlabelP.
rewrite bs_uniq_labelling.
apply: diff.
have -> : a = tnth l' i by rewrite cancel_idxa.
have: i1 != i by rewrite iwins. 
apply: contra_neq.
apply: (@labelling_inj _ _ _ _ l).
exact: tlabelP.
Qed.

End BothWin.

Section iLoses.

Variable (bs bs' : bids) (a : A) (diff : differ_on bs bs' a).

Let i := idxa bs a.
Let i' := idxa bs' a.

Variable (iloses : i != i0) (iwins' : i' = i0).

Let l := tlabel bs.

Lemma l_inj : injective (tnth l).
Proof. exact: labelling_inj (tlabelP geq_bid bs). Qed.

Lemma cancel_a : a = tnth l (idxa bs a). 
Proof. by rewrite cancel_idxa. Qed.

Let under_index (j : A) := if j == i0 then 
                             a
                           else if i0 < j <= i then 
                                  tnth l (agent_pred j)
                                else 
                                  tnth l j.
Let l' := [tuple under_index j | j < n].

Definition under_bids := [tuple tnth bs' (tnth l' j) | j < n].

Lemma sorted_under_bids : sorted_bids under_bids.
Proof.
move=> j1 j2 lej1j2.
move: diff; rewrite /differ_on /action_on => d.
rewrite !tnth_map !tnth_ord_tuple.
have relabpred (j : A) (lt0j : 0 < j) (leji : j <= i) : 
  tnth bs' (tnth l (agent_pred j)) =  tnth (tsort bs) (agent_pred j). 
  move: (labellingP geq_bid bs) => /forallP /(_ (agent_pred j)) /eqP.  
  rewrite d ?[X in _ != X]cancel_a.
  rewrite uniq_labelling => <- //.
  have: agent_pred j != i.
    rewrite neq_ltn. apply/orP. left=> //=. 
    by rewrite (@leq_trans j) // ltn_predL.
  by apply: contra => /eqP /l_inj /eqP.
have relab (j : A) (ltij : i < j): tnth bs' (tnth l j) =  tnth (tsort bs) j.
  move: (labellingP geq_bid bs) => /forallP /(_ j) /eqP. 
  rewrite d ?[X in _ != X]cancel_a. 
  rewrite uniq_labelling => <- //.
  have: j != i by rewrite neq_ltn ltij orbT.
  by apply: contra => /eqP /l_inj /eqP.
- have [] := boolP (j1 == i0) => eqj10 //.
  have [] := boolP (j2 == i0) => eqj20; first by rewrite /under_index !ifT.
  - have [] := boolP (j2 <= i) => ltj2i.
    rewrite /under_index ifF ?ifT ?max_first //; last by exact: negbTE.
    rewrite -(inj_eq val_inj) /= in eqj20. 
    by rewrite /= lt0n ltj2i eqj20 // negbTE. 
  - rewrite /under_index ifF; last by exact: negbTE. 
    rewrite ifF ?ifT ?max_first //.
    by rewrite (negbTE ltj2i) andbF.
- have [] := boolP (j1 <= i) => ltj1i.
  rewrite /under_index (@ifF _ (j1 == i0)); last by exact: negbTE.
  rewrite -lt0n in eqj10.
  rewrite (@ifT _ (i0 < j1 <= i)); last by rewrite eqj10 ltj1i.
  - have [] := boolP (j2 == i0) => [/eqP|] eqj20; first by rewrite eqj20 leqNgt eqj10 in lej1j2.
  - rewrite -lt0n in eqj20.
    - have [] := boolP (j2 <= i) => ltj2i.
      rewrite !ifT //; last by rewrite eqj20.  
      by rewrite !relabpred // tsorted_bids_sorted //= -!subn1 leq_sub2r.
    - rewrite andbF relabpred // relab // ?ltnNge //. 
      by rewrite tsorted_bids_sorted //= (@leq_trans j1) // leq_pred.
- rewrite /under_index (@ifF _ (j1 == i0)); last by exact: negbTE.
  rewrite (@ifF _ (i0 < j1 <= i)); last by rewrite lt0n eqj10 (negbTE ltj1i).
  - have [] := boolP (j2 == i0) => [/eqP|] eqj20.
    by rewrite eqj20 leqNgt lt0n eqj10 in lej1j2.
  - have [] := boolP (j2 <= i) => ltj2i.  
    by rewrite leqNgt (@leq_ltn_trans i) ?ltnNge in lej1j2.
  - by rewrite andbF !relab ?ltnNge // tsorted_bids_sorted.
Qed.

Lemma under_inj : injective under_index.
Proof.
move=> j1 j2.
wlog: j1 j2 / j1 <= j2 => [H|].
  move: (leq_total j1 j2) => /orP [lej1j2|lej2j /esym ei21]; first by exact: H. 
  apply: esym.
  exact: H.
have [] := boolP (j1 == j2) => [/eqP ->|]; first by [].
rewrite /under_index cancel_a -(inj_eq val_inj) /= leq_eqVlt => /negbTE ->.
rewrite orFb.
have [] := boolP (j1 == i0) => [/eqP eqj10|nej10]. 
- have [] := boolP (j2 == i0) => [/eqP eqj20|nej20]; first by rewrite eqj10 eqj20.   
  have [] := boolP (j2 <= i) => ltj2i ltj1j2.
  - rewrite eqj10 /= lt0n nej20 /= => /l_inj /eqP.
    rewrite -(inj_eq val_inj) //= => /eqP eqij21. 
    move: ltj2i.
    rewrite eqij21 leqNgt ltn_predL lt0n.
    rewrite -(inj_eq val_inj) /= in nej20.
    by rewrite nej20.
  - rewrite andbF => /l_inj /eqP.
    rewrite -ltnNge /i in ltj2i.
    move/ltn_eqF: ltj2i.
    by rewrite -(inj_eq val_inj) => /= ->.
- have [] := boolP (j1 <= i) => ltj1i.
  rewrite -lt0n in nej10.
  have [] := boolP (j2 == i0) => [/eqP ->|eqj20 _]; first by rewrite ltn0. 
  rewrite nej10 /= lt0n eqj20. 
  have [] := boolP (j2 <= i) => ltj2i /= /l_inj eqpred.
  - rewrite -lt0n in eqj20.
    apply: val_inj => /=. 
    move: eqpred => /(ord_pred_inj nej10 eqj20) /eqP.
    by rewrite -(inj_eq val_inj) //= => /eqP.
  - rewrite -ltnNge in ltj2i.
    move: (leq_ltn_trans ltj1i ltj2i). 
    by rewrite ltnNge -eqpred /= leq_pred.
- rewrite lt0n nej10 //= [X in _ && X]leqNgt => ltj1j2.
  rewrite -ltnNge in ltj1i.
  move: (ltn_trans ltj1i ltj1j2) => -> /=.
  rewrite -lt0n in nej10.
  move: (ltn_trans nej10 ltj1j2).
  rewrite andbF -(inj_eq val_inj) /= lt0n => /negbTE -> /=.
  exact: l_inj.
Qed.

Lemma perm_under_bids : perm_eq bs' under_bids.
Proof.
rewrite perm_sym.
apply/tuple_permP.
exists (perm under_inj) => /=.
apply: (@eq_from_nth _ bid0) => [|j]; first by rewrite !size_map.
rewrite size_map size_enum_ord => ltjn.
rewrite [LHS](@nth_map _ i0); last by rewrite size_enum_ord.
rewrite [RHS](@nth_map _ i0); last by rewrite size_enum_ord.
by rewrite permE tnth_map tnth_ord_tuple.
Qed.

Lemma is_under_labelling : labelling_of bs' = l'.
Proof.
have sorted: sorted_bids under_bids by exact: sorted_under_bids.
have sorting := 
  sorted_sort (@transitive_geq_bid p') (iffLR (sorted_bids_sorted under_bids) sorted).
have sortedbs': sort geq_bid bs' = under_bids.
  rewrite -sorting.
  apply/perm_sortP => //.
  exact: total_geq_bid.
  exact: transitive_geq_bid. 
  exact: anti_geq_bid.
  exact: perm_under_bids.
have: is_labelling bs' l'.
  apply/eqP.
  apply: eq_from_tnth => j.
  rewrite !tnth_map !(tnth_nth bid0) tupleE /= sortedbs'.
  rewrite tnth_ord_tuple. 
  rewrite (@nth_map _ j _ bid0) ?(tnth_nth bid0);
    last by rewrite size_enum_ord ltn_ord.
  congr nth.
  rewrite /l' tnth_map (tnth_nth i0).
  by rewrite !val_ord_tuple !nth_ord_enum.
have: is_labelling bs' (labelling_of bs') by apply: xchooseP.
exact: labelling_singleton.
Qed.  

Lemma eq_losing_price : tnth (tsort bs') (agent_succ i0) = tnth (tsort bs) i0.
Proof.
set i1 := agent_succ i0. 
move: (labellingP geq_bid bs') => /forallP /(_ i1) /eqP ->.
move: (labellingP geq_bid bs) => /forallP /(_ i0) /eqP ->.
have -> : projT1 (exists_labellingW geq_bid bs') = l'.
  apply: labelling_singleton.
  move: (exists_labellingW geq_bid bs') => [lab islab].
  exact: islab.
  by rewrite -is_under_labelling tlabelP.
rewrite /l' tnth_map tnth_ord_tuple bs_uniq_labelling.
rewrite /under_index ifT /=; last by rewrite lt0n.
have -> : (agent_pred i1) = i0 by exact: val_inj.
apply: diff.
have -> : a = tnth l i by rewrite cancel_idxa.
have: i0 != i by rewrite eq_sym.
apply: contra_neq.
apply: (@labelling_inj _ _ _ _ l).
exact: tlabelP.
Qed.

End iLoses.

End Prices.

Definition m := 
  mech.new (fun bs => map_tuple (fun i => (is_winner bs i, bs)) (agent.agents n)).

Definition a := 
  auction.new (fun (o : mech.O m) i => 
                 let: (w, bs) := tnth o i in if w then Some (price bs i) else None).

Variable v : agent.type n -> bid.

Definition prefs := auction.prefs a v.

Section Properties.

(** SP is rational, if one bids truthfully. *) 

Theorem rational (tv : forall bs, tnth bs =1 v) : auction.rational a v.
Proof. 
rewrite /auction.rational /auction.p /= => i o. 
case: (tnth o i) => iw' bs'.
case: ifP => [_|//]. 
by rewrite -(tv bs' i) -(labelling_spec_idxa geq_bid bs' i) tsorted_bids_sorted // le_ord_succ.
Qed.

(** SP is truthful *)

Theorem truthful_SP : truthful prefs.
Proof. 
rewrite /truthful => bs bs' i diff /=.
rewrite /auction.U /auction.p /= !tnth_map /= !tnth_ord_tuple. 
case: ifP => [iw'|//].
case: ifP => iw. 
- rewrite leq_sub2l // /price.
  move: (iw) (iw') => /eqP -> /eqP ->.
  rewrite /is_winner in iw iw'. 
  rewrite (eq_winning_price diff) //; last by apply/eqP.
  by apply/eqP.
- rewrite /action_on => <-.
  rewrite leqn0 subn_eq0 /price.
  move: (iw') => /eqP ->.
  rewrite /is_winner in iw iw'.
  rewrite (eq_losing_price diff) // -?(labelling_spec_idxa geq_bid bs).  
  exact: tsorted_bids_sorted.
  by move: iw; apply: contraFneq => ->.
  by apply/eqP.
Qed. 

(** Two proofs that SP with truthful bidding is a Nash equilibrium:
    - direct
    - using weak dominance property. *)

Lemma SP_Nash_truthful_direct: Nash_equilibrium prefs v.
Proof.
rewrite /Nash_equilibrium => i s'. 
rewrite /U /prefs.U /= /auction.U /auction.p /= !tnth_map !tnth_ord_tuple.
case: ifP => [iw'|//].
move: iw'; rewrite /is_winner /actions /price => /eqP eqix'0.  
case: ifP => [iw|neiw]; last first.
- pose bs := [tuple v j | j < n]; set bs' := (X in tsort X).
  rewrite eqix'0 (@eq_losing_price bs bs' i) //; last by rewrite negbT.
  - have -> : v i = tnth (tsort bs) (idxa bs i) 
      by rewrite labelling_spec_idxa tnth_map tnth_ord_tuple.
    by rewrite leqn0 subn_eq0 tsorted_bids_sorted. 
  - rewrite /differ_on /action_on => j. 
    by rewrite !tnth_map !tnth_ord_tuple -{2}(negbK (j == i)) => ->.
- rewrite leq_sub2l // /price.
  move: (iw); rewrite /is_winner => /eqP eqix0.
  set bs := actions v; set bs' := set_in_actions v s' i.
  rewrite eqix0 eqix'0 (@eq_winning_price bs bs' i) // => j neji.
  by rewrite /differ_on /action_on !tnth_map !tnth_ord_tuple ifF // (negbTE neji).
Qed.

(* SP being a truthful auction, it is a Nash equilibrium. *)

Definition m_t := truthfulMech.new truthful_SP.

Definition a_t := 
  auction.new (fun (o : mech.O m_t) i => 
                 let: (w, bs) := tnth o i in if w then Some (price bs i) else None).

Definition prefs_t := auction.prefs a_t v.

Lemma SP_Nash_truthful : Nash_equilibrium prefs_t v.
Proof. exact: truthfulMech.Nash_truthful. Qed.

(** Truthful bidding in SP is a Pareto optimum. *)

Lemma Pareto_optimal_SP : Pareto_optimal prefs (true_value_strategy prefs).
Proof.
rewrite /Pareto_optimal /action_on => s' i. 
set bs := [tuple v j  | j < n].
set bs' := [tuple if j == i then s' j else v j  | j < n].
have diff : differ_on bs bs' i.
  move=> j.
  rewrite /action_on /bs' !tnth_map !tnth_ord_tuple.
  by case: ifP.
set U := (X in X < _); set U' := (X in _ < X) => ltUU'. 
move: (ltUU'). 
have -> // : 0 < U' -> U' = U; last by rewrite (@leq_ltn_trans U).
  rewrite /U /U' /prefs.U /= /auction.U /auction.p /=.
  rewrite !tnth_map /= !tnth_ord_tuple => lt0U'.
  case: ifP => [/eqP iw'|niw']; last by move: lt0U'; rewrite niw'. 
  case: ifP => [/eqP iw|niw].
  - congr (_ - _).
    by rewrite /price iw iw' (@eq_winning_price bs bs' i).
  - apply/eqP; rewrite subn_eq0 /price.
    rewrite /is_winner in niw iw'.  
    rewrite iw' (@eq_losing_price bs bs' i) //; last by rewrite niw.     
    rewrite (@leq_trans (tnth (tsort bs) (idxa bs i))) //; last by exact: tsorted_bids_sorted.
    by rewrite !labelling_spec_idxa tnth_map tnth_ord_tuple. 
by rewrite ltnn. 
Qed.

(** "Wolf and sheep" bidding is another Nash equilibrium for SP when bidding truthfully. 
     See https://homepages.cwi.nl/~apt/stra/ch7.pdf. *)

Section Wolf.

Notation cancel_inv_idxa := (cancel_inv_idxa geq_bid).
Notation labelling_spec_idxa := (labelling_spec_idxa geq_bid).
Notation tlabel := (tlabel geq_bid).

Variable bs : bids.

Definition l := tlabel bs.

Definition wolf := [tuple if idxa bs j == i0 then v j else bid0 | j < n].

Definition sorted_wolf := [tuple of (v (tnth l i0)) :: nseq n' bid0].

Local Lemma refold (b : bid) : b :: nseq n'' b = nseq n' b. 
Proof. by []. Qed.

Lemma sorted_sorted_wolf : sorted_bids sorted_wolf.
Proof.
move=> j1 j2 le12.
rewrite !(tnth_nth bid0).
have [/eqP -> |] := boolP (j1 == i0).
- have [/eqP -> //=|ne20] := boolP (j2 == i0).
  have lt02: 0 < j2 by move: ne20;  rewrite -(inj_eq val_inj) /= lt0n.
  by rewrite -(@prednK j2) //= refold nth_nseq if_same.
- rewrite -(inj_eq val_inj) /= -lt0n => lt01. 
  have lt02: 0 < j2 by rewrite (@leq_trans j1). 
  by rewrite -(@prednK j2) // -(@prednK j1) //= !refold nth_nseq if_same.
Qed.

Lemma perm_eq_wolf : perm_eq sorted_wolf wolf. 
Proof.
apply/tuple_permP.
exists (tperm i0 (tnth l i0)).
apply: (@eq_from_nth _ ord0) => [|i ltin]; first by rewrite !size_tuple.
rewrite /= size_nseq in ltin. 
rewrite !(nth_map ord_max) -?enumT ?size_enum_ord //.
have [/eqP eqi0|] := boolP (i == i0).
- rewrite eqi0 /= nth_agent_enum.
  have -> : @Ordinal (S n') O is_true_true = ord0 by exact: val_inj.
  by rewrite tpermL /= tnth_map tnth_ord_tuple /wolf cancel_inv_idxa -(inj_eq val_inj).
- rewrite nth_agent_enum /= => nei0. 
  rewrite -lt0n in nei0. 
  have [/eqP eqil0|neil0] := boolP (Ordinal ltin == tnth l i0).
  - rewrite eqil0 tpermR /= tnth_map tnth_ord_tuple /wolf.
    rewrite -(@prednK i) //= ?refold ?nth_nseq ?if_same ifF //.
    apply: (contra_eqF _ eqil0) => /eqP <-.
    by rewrite cancel_idxa -(inj_eq val_inj) /= -lt0n.
  - rewrite -[in LHS](@prednK i) //= refold nth_nseq if_same. 
    rewrite tpermD ?tnth_map ?tnth_ord_tupl /wolf; last exact: (contra_neq _ neil0).
    - rewrite tnth_ord_tuple ifF //.
      apply: (contra_neqF _ neil0) => /eqP <-.
      by rewrite cancel_idxa.
    - by rewrite -(inj_eq val_inj) /= eq_sym -lt0n.
Qed.

Lemma sort_wolf : tsort wolf = sorted_wolf. 
Proof.
have tr: transitive geq_bid by exact: transitive_geq_bid.
apply: val_inj => /=. 
have := perm_eq_wolf => /(@perm_sortP _ geq_bid) <- //; last by exact: anti_geq_bid.
- rewrite sorted_sort => [//|//|].  
  rewrite (iffLR (sorted_bids_sorted sorted_wolf)) //.
  exact: sorted_sorted_wolf.
- exact: total_geq_bid.
Qed.                                      

Lemma Nash_wolf_and_sheep (tv : tnth bs =1 v) : Nash_equilibrium prefs (tnth wolf).
Proof.
rewrite /Nash_equilibrium => i s'. 
rewrite /U /prefs.U /= /auction.U /auction.p /= !tnth_map !tnth_ord_tuple. 
set b' := (X in price X).
case: ifP => [iw'|//]. 
move: iw'; rewrite /is_winner /actions /price => /eqP eqix'0.  
case: ifP => [/eqP iw|neiw].  
- rewrite /price leq_sub2l // /set_in_actions /actions.
  rewrite tuple_of_tnth in iw *.
  rewrite eqix'0 (@eq_winning_price wolf b' i) // => [|j neji]. 
  - by rewrite tsorted_bids_sorted // iw.
  - by rewrite /action_on !tnth_map !tnth_ord_tuple ifF // (negbTE neji).
- rewrite eqix'0 -tv leqn0 subn_eq0 (@eq_losing_price wolf b' i) ?negbT //; last first. 
  - by rewrite tuple_of_tnth in neiw.
  - rewrite /differ_on /action_on => j.
    by rewrite !tnth_map !tnth_ord_tuple -{2}(negbK (j == i)) => ->.
  - have -> : tnth (tsort wolf) i0 = tnth (tsort bs) i0. 
      rewrite sort_wolf (tnth_nth bid0) /=. 
      by rewrite -[in RHS](cancel_inv_idxa bs i0) (labelling_spec_idxa bs) -tv.
    by rewrite -(labelling_spec_idxa bs) tsorted_bids_sorted.
Qed.

End Wolf.

End Properties.

(* Check truthful_SP. *)
(* Print Assumptions truthful_SP. *)

