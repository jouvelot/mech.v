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

Notation agents := (enum 'I_n).

Notation last_agent := (@agent.last n).
Notation agent_succ := (@agent.succ n').
Notation agent_pred := (@agent.pred n).

Variable p' : nat.
Definition p := p'.+1.
Definition bid := 'I_p.
Definition bid0 : bid := Ordinal (ltn0Sn p').
Definition bids := n.-tuple bid.

Notation geq_bid := (@geq_bid p').

Notation tr := (@transitive_geq_bid p').
Notation totr := (@total_geq_bid p').
Notation ar := (@anti_geq_bid p').
Notation rr := (@reflexive_geq_bid p').

Notation labelling_spec_idxa bs := (@labelling_spec_idxa _ _ _ bs tr rr totr ar).
Notation labellingP bs := (@labellingP _ _ _ bs tr rr totr ar).
 
Notation is_labelling bs := (@is_labelling _ _ geq_bid bs). 
Notation tlabel bs := (@tlabel n' _ geq_bid bs tr rr totr ar). 
Notation tlabelP bs := (@tlabelP n' _ geq_bid bs tr rr totr ar). 
Notation idxa_eq_mon bs := (@idxa_eq_mon _ _ geq_bid bs tr rr totr ar). 
Notation idxa_inj bs := (@idxa_inj _ _ geq_bid bs tr rr totr ar).

Notation ri bs := [rel i1 i2 | tnth bs i2 <= tnth bs i1].
Notation ri_lex bs := [rel i1 i2 | ri bs i1 i2 && (ri bs i2 i1 ==> (i1 <= i2))].

Notation tsort := (tsort geq_bid).
Notation idxa bs i := (@idxa n' _ geq_bid bs tr rr totr ar i).

Section Algorithm.

Variable (bs0 : bids) (i : A).

Let bs := tsort bs0.
Let i' := idxa bs0 i.

Definition i0 : A := ord0.

Definition is_winner := (i' == i0).
Definition price : nat := tnth bs (agent_succ i').

End Algorithm.

Lemma sorted_lex_lex (b : bids) : sorted (ri_lex b) (sort (ri_lex b) (enum 'I_n)).
Proof.
apply: sort_sorted.
move: (@ri_lex_tot _ _ geq_bid b) => /=.
apply.
exact: leqnn.
by move=> x y; rewrite leq_total.
Qed.

Lemma perm_labelling b (lab : labelling n') : 
  is_labelling b lab -> perm_eq [seq tnth lab j | j <- enum 'I_n] (enum 'I_n).
Proof. 
move=> /andP [_ /eqP ->].
by rewrite map_tnth_enum perm_sort perm_refl.
Qed.

Section Prices.

Definition labelling_of (bs : bids) : labelling _ := 
  xchoose (@exists_labelling _ _ geq_bid bs tr rr totr ar).

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

Lemma bs_uniq_labelling : projT1 (@exists_labellingW _ _ geq_bid bs tr rr totr ar) = l. 
Proof. exact: uniq_labelling. Qed.

Let l' := l.

Definition over_bids := [tuple tnth bs' (tnth l' j) | j < n].

Lemma max_first (b : bids) j : idxa b a = i0 -> tnth b j <= tnth b a.
Proof.
rewrite -(labelling_spec_idxa b a) -(labelling_spec_idxa b j) => ->.
exact: tsorted_bids_sorted.
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
  have netnth (j : A) : 
    j != i -> tnth (projT1 (@exists_labellingW _ _ geq_bid bs tr rr totr ar)) j != tnth l i.
    apply: contra_neq.
    rewrite bs_uniq_labelling.
    apply: labelling_inj.
    exact: (tlabelP bs).
  rewrite !d /l' -?bs_uniq_labelling ?inva.
  move: (labellingP bs) => /forallP /(_ j2) /eqP <-.
  move: (labellingP bs) => /forallP /(_ j1) /eqP <-. 
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
rewrite map_tnth_enum -(sort_inj_ord (labelling_inj (tlabelP bs))).
by rewrite perm_sort perm_refl.
Qed.

Lemma sorted_over_lex (b : bids): sorted (ri_lex b) (sort (ri b) (enum 'I_n)).
Proof.
apply: (@sort_stable _ (ri b) le_ord).
- apply: (@ri_tot _ _ geq_bid).
  exact: total_geq_bid.
- exact: leq_trans.
- by rewrite -sort_enum sort_sorted // => x y /=; exact: leq_total.
Qed.

Lemma sorted_over_lex_lex' : sorted (ri_lex bs) (sort (ri_lex bs') (enum 'I_n'.+1)).
Proof.
set e' := (sort _ _).
move: diff => d.
rewrite /differ_on /action_on in d.
apply: pairwise_sorted.
apply/(pairwiseP ord0) => i1 i2 lt1 lt2 i1i2.
rewrite !inE size_sort size_enum_ord in lt1 lt2. 
have: sorted (ri_lex bs') e' by exact: sorted_lex_lex.
have lextr' : transitive (ri_lex bs') 
  by apply: (@ri_lex_tr _ _ geq_bid bs'); exact: transitive_geq_bid.
move/(@sorted_ltn_nth _ (ri_lex bs') _ ord0 _) => /(_ lextr' i1 i2).
rewrite !inE size_sort size_enum_ord => /(_ lt1 lt2 i1i2).
set e1' := (nth _ _ i1); set e2' := (nth _ _ i2) => /=.
have [/andP [a1 a2]|] := boolP ((e1' != a) && (e2' != a)); first by rewrite !d.  
rewrite negb_and !negbK => /orP [/eqP e1a |/eqP ->].  
- rewrite e1a. 
  have [e2a|] := boolP (e2' != a); last by rewrite negbK => /eqP ->; rewrite !leqnn.
  rewrite !(d e2') //. 
  have [ltae2'|] := boolP (tnth bs' a <= tnth bs e2').  
  - have -> : tnth bs' a = tnth bs e2'.
      apply: val_inj => /=.
      by apply/eqP; rewrite eqn_leq ltae2' -(d e2') // max_first.
    have [ltae2|] := boolP (tnth bs a <= tnth bs e2');
                     last by rewrite -ltnNge leqnn implyTb implyFb andTb andbT => /ltnW.
    have -> // : tnth bs a = tnth bs e2'. 
      apply: val_inj => /=.
      by apply/eqP; rewrite eqn_leq ltae2 max_first.
  - rewrite -ltnNge implyFb andbT => le2' _.
    rewrite max_first // andTb.
    have [/eqP ae2|] := boolP (tnth bs a == tnth bs e2').
    - by rewrite ae2 leqnn implyTb (idxa_eq_mon bs) //= -/i iwins.
    - rewrite leq_eqVlt -(@negbK (val (tnth bs a) == val (tnth bs e2'))) /= => -> /=.
      by rewrite ltnNge max_first.
- rewrite !max_first // !implyTb => /andP. 
  rewrite leq_eqVlt => [[/orP [/eqP ae1 lte1'a|]]]; last by rewrite ltnNge max_first.
  rewrite lte1'a andbT leqNgt ltn_neqAle max_first // andbT negbK.
  have [/eqP -> //|e1'a] := boolP (e1' == a).
  move: (idxa_eq_mon bs') => /(_ a e1' (ord_inj ae1)).
  rewrite -/i' iwins' /= leq0n => /(_ erefl).
  by rewrite leq_eqVlt ltnNge lte1'a /= orbF -(@negbK (val a == val e1')) /= eq_sym e1'a.
Qed.

Lemma sort_eq_over : sort (ri_lex bs) (enum 'I_n) = sort (ri_lex bs') (enum 'I_n).
Proof.
apply: (@sorted_eq _ (ri_lex bs)).  
- apply: (@ri_lex_tr _ _ geq_bid bs).
  exact: transitive_geq_bid.
- exact: (@ri_lex_as _ _ geq_bid bs).  
- rewrite sort_sorted //.
  move: (@ri_lex_tot _ _ geq_bid bs); rewrite /geq_bid /=.
  apply.
  exact: leqnn.
  exact: total_geq_bid. 
- exact: sorted_over_lex_lex'. 
- by rewrite (@perm_trans _ (enum 'I_n)) // ?(@perm_sym _ (enum 'I_n)) perm_sort perm_refl.
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
have isl': is_labelling bs' (labelling_of bs') by apply: xchooseP.
have: is_labelling bs' l'.
  apply/andP; split.
  - apply/eqP.
    apply: eq_from_tnth => j.
    rewrite !tnth_map !(tnth_nth bid0) tupleE /= sortedbs'.
    rewrite (@nth_map _ j _ bid0) ?(tnth_nth bid0);
      last by rewrite size_enum_ord ltn_ord.
    by rewrite val_ord_tuple nth_ord_enum. 
  - apply/eqP.   
    rewrite /l' /l.
    have := tlabelP bs => /andP [_ /eqP ->]. 
    rewrite /geq_bid /=.
    apply: val_inj => /=.
    exact: sort_eq_over.
exact: labelling_singleton.
Qed.

Lemma eq_winning_price  :
  tnth (tsort bs') (agent_succ i0) = tnth (tsort bs) (agent_succ i0). 
Proof.
set i1 := agent_succ i0. 
move: (labellingP bs') => /forallP /(_ i1) /eqP ->.
move: (labellingP bs) => /forallP /(_ i1) /eqP ->. 
have -> : projT1 (@exists_labellingW _ _ geq_bid bs' tr rr totr ar) = l'.
  apply: labelling_singleton.
  move: (@exists_labellingW _ _ geq_bid bs' tr rr totr ar) => [lab islab].
  exact: islab.
  by rewrite -is_over_labelling (tlabelP bs').
rewrite bs_uniq_labelling.
apply: diff.
have -> : a = tnth l' i by rewrite cancel_idxa.
have: i1 != i by rewrite iwins. 
apply: contra_neq.
apply: (@labelling_inj _ _ _ _ l).
exact: (tlabelP bs).
Qed.

End BothWin.

Section iLoses.

Variable (bs bs' : bids) (a : A) (diff : differ_on bs bs' a).

Let i := idxa bs a.
Let i' := idxa bs' a.

Variable (iloses : i != i0) (iwins' : i' = i0).

Let l := tlabel bs.

Lemma l_inj : injective (tnth l).
Proof. exact: labelling_inj (tlabelP bs). Qed.

Lemma cancel_a : a = tnth l (idxa bs a). 
Proof. by rewrite cancel_idxa. Qed.

Let under_index (j' : A) := if j' == i0 then 
                             i
                           else if 0 < j' <= i then 
                                  ord_pred j'
                                else 
                                  j'.
Let l' := [tuple tnth l (under_index j) | j < n].

Definition under_bids := [tuple tnth bs' (tnth l' j) | j < n].

Lemma sorted_under_bids : sorted_bids under_bids. 
Proof.
move=> j1 j2 lej1j2.
move: diff; rewrite /differ_on /action_on => d.
rewrite !tnth_map !tnth_ord_tuple.
have relabpred (j : A) (lt0j : 0 < j) (leji : j <= i) : 
  tnth bs' (tnth l (agent_pred j)) =  tnth (tsort bs) (agent_pred j). 
  move: (labellingP bs) => /forallP /(_ (agent_pred j)) /eqP.  
  rewrite d ?[X in _ != X]cancel_a.
  rewrite uniq_labelling => <- //.
  have: agent_pred j != i.
    rewrite neq_ltn. apply/orP. left=> //=. 
    by rewrite (@leq_trans j) // ltn_predL.
  by apply: contra => /eqP /l_inj /eqP.
have relab (j : A) (ltij : i < j): tnth bs' (tnth l j) =  tnth (tsort bs) j.
  move: (labellingP bs) => /forallP /(_ j) /eqP. 
  rewrite d ?[X in _ != X]cancel_a. 
  rewrite uniq_labelling => <- //.
  have: j != i by rewrite neq_ltn ltij orbT.
  by apply: contra => /eqP /l_inj /eqP. 
- have [] := boolP (j1 == i0) => eqj10 //.
  have [] := boolP (j2 == i0) => eqj20; first by rewrite /under_index !ifT.
  rewrite -lt0n in eqj20.
  - have [] := boolP (j2 <= i) => ltj2i.
    rewrite /under_index ifF ?ifT ?max_first // ?ltj2i ?eqj20 //=;
            last by rewrite (@negbTE (j2 == i0)) // -lt0n.
    by rewrite -cancel_a.
  - rewrite /under_index ifF; last by rewrite (@negbTE (j2 == i0)) // -lt0n.
    by rewrite ifF ?ifT ?max_first // ?eqj20 ?andTb ?(negbTE ltj2i) // -cancel_a.
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

Lemma ord_pred_enum j (ltj : j < n') :
  ord_pred (nth ord0 (enum 'I_n) (j.+1)) = nth ord0 (enum 'I_n) j. 
Proof. by apply: val_inj => /=; rewrite !nth_enum_ord //= (ltn_trans ltj). Qed.

Lemma mon_tnth (b : bids) j1 j2 : idxa b j1 <= idxa b j2 -> tnth b j2 <= tnth b j1.
Proof.
rewrite -(labelling_spec_idxa b j1) -(labelling_spec_idxa b j2).
exact: tsorted_bids_sorted.
Qed.

Lemma stable_sorted  (x1 x2 : 'I_n) :
  let: a1 := tnth l x1 in
  let: a2 := tnth l x2 in
  x1 <= x2 ->
  (tnth bs a2 <= tnth bs a1)  && ((tnth bs a1 <= tnth bs a2) ==> (a1 <= a2)).
Proof.
move=> x1x2.
have l21' : (tnth bs (tnth l x2) <= tnth bs (tnth l x1)).
  by rewrite mon_tnth // !cancel_inv_idxa ?(ltnW i1i2). 
rewrite !(@mon_tnth _ (tnth l x1) (tnth l x2)) ?cancel_inv_idxa // 
        ?nth_enum_ord ?(ltnW i1i2) // ?andTb.
apply/implyP => l12.
have/(idxa_eq_mon bs) -> //: tnth bs (tnth l x1) = tnth bs(tnth l x2).
  by apply/val_inj/eqP => /=; rewrite eqn_leq l21' l12. 
by rewrite !cancel_inv_idxa ?(ltnW i1i2).
Qed.

Lemma not_a_lt (j : 'I_n) : j < i -> j < n -> tnth l j != a. 
Proof.
move=> xi xn.
rewrite cancel_a.
have : j != i by rewrite negbT // -(inj_eq val_inj) /= ltn_eqF.
by apply: contra_neq => /l_inj.
Qed.

Lemma not_a_le j : 0 < j -> j <= i -> j < n -> tnth l (ord_pred (nth ord0 (enum 'I_n) j)) != a. 
Proof.
move=> x0 xi xn.
by rewrite not_a_lt // (@leq_trans j) //= nth_enum_ord ?ltn_predL // (@leq_trans i).
Qed.

Lemma not_a_gt j : i < j -> j < n -> tnth l (nth ord0 (enum 'I_n) j) != a.
Proof.
move=> ij jn. 
rewrite cancel_a.
have : nth ord0 (enum 'I_n) j != i 
   by rewrite negbT // -(inj_eq val_inj) /= gtn_eqF // nth_enum_ord.
by apply: contra_neq => /l_inj.
Qed.

Lemma sorted_under_lex : sorted (ri_lex bs') l'.
Proof.
move: diff => d.
rewrite /differ_on /action_on in d.
apply: pairwise_sorted.
apply/(pairwiseP ord0) => i1 i2 lt1 lt2 i1i2 /=.
rewrite !inE size_map size_enum_ord in lt1 lt2. 
rewrite !(nth_map ord0) -?enumT ?size_enum_ord /under_index //=.
rewrite -!(inj_eq val_inj) /= !nth_enum_ord /ord_pred //. 
- have [] := boolP (i1 == i0) => i10 //.
  - have [|] := boolP (i2 == i0) => i20; first by rewrite !leqnn. 
    set ie2 := (nth ord0 (enum 'I_n) i2); set a2m := tnth l (ord_pred ie2). 
    have [] := boolP (i2 <= i) => j2i. 
    - rewrite -lt0n in i20. 
      rewrite i20 //=. 
      have ne2i: ord_pred ie2 != i.
        rewrite -(inj_eq val_inj) /= nth_enum_ord ?negbT ?ltn_eqF //.
        by rewrite (@leq_trans i2) ?ltn_predL.
      have nea2m : a2m != a 
        by move: ne2i; apply: contra_neq; rewrite cancel_a  => /l_inj.
      rewrite !(d a2m) //.
      have la2a : tnth bs a2m <= tnth bs' (tnth l i) 
        by rewrite -(d a2m) ?max_first // -?cancel_a. 
      rewrite la2a andTb. 
      move: (la2a); rewrite leq_eqVlt => /orP [/eqP a2mi|]; 
                                        last by rewrite ltnNge => /negbTE ->; exact: implyFb.
      rewrite -(d a2m) // in la2a *.
      apply/implyP => laa2.
      have/(idxa_eq_mon bs'): tnth bs' a = tnth bs' a2m. 
        by apply/val_inj/eqP => /=; rewrite eqn_leq cancel_a -/i la2a laa2.
      by rewrite -/i' iwins' /= cancel_a => ->.
    - rewrite -ltnNge in j2i.
      rewrite andbF -cancel_a.
      have la2a: tnth bs' (tnth l ie2) <= tnth bs' a by rewrite max_first.
      rewrite la2a andTb.
      apply/implyP => laa2.
      have/(idxa_eq_mon bs') -> //: tnth bs' a = tnth bs' (tnth l ie2).
        by apply/val_inj/eqP => /=; rewrite eqn_leq la2a laa2.
      by rewrite -/i' iwins'.
  - rewrite -lt0n in i10. 
    rewrite !i10.
    have [] := boolP (i1 <= i) => l1i. 
    - have [/= /eqP|] := boolP (i2 == i0) => i20; first by rewrite i20 ltn0 in i1i2.  
      rewrite -lt0n in i20. 
      rewrite !i20 /=.
      set ie1 := (nth ord0 (enum 'I_n) i1); set ie2 := (nth ord0 (enum 'I_n) i2). 
      set a1m := tnth l (ord_pred ie1).
      have [] := boolP (i2 <= i) => j2i.
      - set a2m := tnth l (ord_pred ie2). 
        rewrite !d // ?not_a_le // stable_sorted // /ie1 -(@prednK i1) /ie2 -1?(@prednK i2) //. 
        have ljn' j : j < n -> j.-1 < n' 
          by move=> jn; rewrite (_ : n' = n.-1) // -!subn1 ltn_sub2r.
        have ljn j : j < n -> j.-1 < n by move=> jn; rewrite (@leq_ltn_trans j) ?leq_pred.
        rewrite !ord_pred_enum ?ljn' //.
        by rewrite !nth_enum_ord ?ljn // -?subn1 ?leq_sub2r // ltnW.
      - rewrite -ltnNge in j2i.
        rewrite !d ?not_a_gt // ?stable_sorted // ?not_a_le //. 
        by rewrite nth_enum_ord //= nth_enum_ord // (@leq_trans i1) ?leq_pred // ltnW.
    - rewrite -ltnNge in l1i.
      rewrite ifF; last by rewrite gtn_eqF // (@leq_trans i1) // ltnW.   
      rewrite ifF /=; last by rewrite (ltn_trans i10 i1i2) leqNgt (ltn_trans l1i).
      by rewrite !d ?not_a_gt // 1?(ltn_trans l1i i1i2) ?stable_sorted ?nth_enum_ord // ltnW.
Qed.

Notation ux := (fun (j : A) => if j == i0 then i else if i0 < j <= i then (agent_pred j) else j).

Lemma perm_under_ux_lt :
  i.+1 < n -> let ex := [seq ux j | j <- enum 'I_n] in
             let e := enum 'I_n in
             let tx := take i.+1 ex in
             let t := take i.+1 e in
  perm_eql (drop 1 tx ++ take 1 tx) (take i t ++ drop i t).
Proof.
move=> li1 /= .
set ex := [seq ux j | j <- enum 'I_n]; set e := enum 'I_n.
set tx := take i.+1 ex; set t := take i.+1 e.
have l0i : 0 < i by move: iloses; rewrite -(inj_eq val_inj) /= lt0n.
  have -> : drop 1 tx = take i t.
    apply: (@eq_from_nth _ ord0) => [|j ltj]. 
    - rewrite size_drop !size_take !size_map -?enumT !size_enum_ord li1 ltnS. 
      by rewrite leqnn subSn // subn1 prednK. 
    - rewrite size_drop size_take size_map size_enum_ord li1 subn1 /= in ltj.  
      have lt1j : 1 + j < n by rewrite (@ltn_trans (1 + i)).
      rewrite nth_drop !nth_take // ?(ltn_trans ltj) // (nth_map ord0) ?size_enum_ord //.
      rewrite ifF ?nth_enum_ord //; last by rewrite -(inj_eq val_inj) /= nth_enum_ord // add1n.
      rewrite ifT /=; last by rewrite add1n.
      by rewrite /agent_pred ord_pred_enum.
  have -> : take 1 tx = drop i t.
    have li11 : 1 < i.+1 by rewrite -[X in _ < X]addn1 addnC -ltn_psubLR.  
    apply: (@eq_from_nth _ ord0) => [|j ltj]. 
    - rewrite size_drop !size_take !size_map -!enumT !size_enum_ord li1.
      move: iloses; rewrite -(inj_eq val_inj) /= => il.
      by rewrite ifT ?subSnn.
    - move: ltj; rewrite !size_take size_map size_enum_ord li1 li11.
      rewrite ltnS leq_eqVlt ltn0 orbF => /eqP ->.
      rewrite !nth_drop !nth_take // ?addn0 ?nth_ord_enum //= (nth_map ord0) ?size_enum_ord //.
      by rewrite -(inj_eq val_inj) /= nth_enum_ord // eq_refl.
  apply/permPl.
  exact: perm_refl.
Qed.

Lemma perm_under_ux_max : 
  i = ord_max -> let ex := [seq ux j | j <- enum 'I_n] in
                let e := enum 'I_n in
                let tx := take i.+1 ex in
                let t := take i.+1 e in
  perm_eql (drop 1 tx ++ take 1 tx) (take i t ++ drop i t).
Proof.
move=> eqi /=.
have li1: (i.+1 < n) = false by rewrite eqi /= ltnn.
set ex := [seq ux j | j <- enum 'I_n]; set e := enum 'I_n.
set tx := take i.+1 ex; set t := take i.+1 e.
- have l0i : 0 < i by move: iloses; rewrite -(inj_eq val_inj) /= lt0n.
  have -> : drop 1 tx = take i t.
    apply: (@eq_from_nth _ ord0) => [|j ltj]. 
    - by rewrite size_drop !size_take !size_map -?enumT !size_enum_ord li1 ifT eqi.
    - rewrite size_drop size_take size_map size_enum_ord li1 subn1 /= in ltj. 
      rewrite nth_drop !nth_take ?eqi //= 1?(ltn_trans ltj) // (nth_map ord0) ?size_enum_ord //.
      rewrite ifF ?nth_enum_ord //; last by rewrite -(inj_eq val_inj) /= nth_enum_ord // add1n.
      rewrite eqi ifT /=; last by rewrite add1n.
      by rewrite /agent_pred ord_pred_enum.
  have -> : take 1 tx = drop i t. 
    have li11 : 1 < i.+1 by rewrite -[X in _ < X]addn1 addnC -ltn_psubLR.  
    apply: (@eq_from_nth _ ord0) => [|j ltj]. 
    - rewrite size_drop !size_take !size_map -!enumT !size_enum_ord li1.
      move: iloses; rewrite -(inj_eq val_inj) /= => il.
      by rewrite eqi /= subSnn.
    - move: ltj; rewrite !size_take size_map size_enum_ord li1. 
      rewrite (@ifT _ (1 < n)) //=.
      rewrite ltnS leq_eqVlt ltn0 orbF => /eqP ->.
      rewrite !nth_drop !nth_take // ?addn0 ?nth_ord_enum //= (nth_map ord0) ?size_enum_ord //.
      by rewrite -(inj_eq val_inj) /= nth_enum_ord // eq_refl.
  apply/permPl.
  exact: perm_refl.
Qed.

Lemma perm_under : perm_eq [seq ux j | j <- enum 'I_n] (enum 'I_n).
Proof.
set ex := (X in perm_eq X); set e := enum 'I_n. 
rewrite -(cat_take_drop i.+1 e) -(cat_take_drop i.+1 ex). 
have -> : drop i.+1 ex = drop i.+1 e.
  apply: (@eq_from_nth _ ord0) => [|j ltj]; first by rewrite !size_drop size_map size_enum_ord.
  rewrite size_drop size_map size_enum_ord in ltj.
  rewrite !nth_drop (nth_map ord0) ?nth_enum_ord ?size_enum_ord -?ltn_subRL //.
  rewrite -(inj_eq val_inj) /= ifF; first by rewrite subnn ltn0. 
  rewrite nth_enum_ord addSn. constructor.
  by rewrite -addSn -ltn_subRL.
rewrite (@perm_catr _ _ (take i.+1 e)) ?perm_refl //.
set tx := (take _ ex); set t := (take _ e).
rewrite -(cat_take_drop i t) -(cat_take_drop 1 tx).  
- rewrite (@perm_trans _ (drop 1 tx ++ take 1 tx)) // permEl //. 
  exact: perm_catC.
- have [lj1|] := boolP (i.+1 < n); first by exact: perm_under_ux_lt.
  rewrite -leqNgt /leq subSS -/(leq n' i) => ln'.
  apply: perm_under_ux_max.
  by apply: val_inj => /=; move: (leq_ord i); rewrite leq_eqVlt ltnNge ln' orbF => /eqP ->. 
Qed.

Lemma perm_under_l : perm_eq [seq tnth l (ux j) | j <- enum 'I_n] (enum 'I_n). 
Proof.
rewrite (@perm_trans _ [seq tnth l j | j <- enum 'I_n]) //;
        last by rewrite (@perm_labelling bs) //; exact: (tlabelP bs).
pose f k := ux k.
under (@eq_map _ _ _ (tnth l)) => k. 
  by rewrite /under_index -?enumT // -!(fun_if (tnth l)).
rewrite (perm_map_inj (idxa_inj bs)) // -!map_comp /comp.
under eq_map => j do rewrite cancel_inv_idxa.
under [X in perm_eq _ X]eq_map => j do rewrite cancel_inv_idxa.
by rewrite map_id -!enumT perm_under.
Qed.

Lemma sort_eq_under : 
  [seq tnth l (ux j) | j <- enum 'I_n] = sort (ri_lex bs') (ord_tuple n).
Proof.
apply: (@sorted_eq _ (ri_lex bs')).  
- apply: (@ri_lex_tr _ _ geq_bid bs').
  exact: transitive_geq_bid.
- exact: (@ri_lex_as _ _ geq_bid bs').  
- exact: sorted_under_lex.
- exact: sorted_lex_lex.
- by rewrite perm_sym (@perm_trans _ (enum 'I_n)) ?perm_sort ?perm_refl // perm_sym perm_under_l.
Qed.

Lemma perm_under_bids : perm_eq bs' under_bids.
Proof.
rewrite perm_sym.
apply/tuple_permP.
have under_inj : injective (tnth l').
  by apply/(tuple_uniqP ord0) => /=; rewrite (perm_uniq (perm_under_l)) enum_uniq. 
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
have sorting := sorted_sort tr (iffLR (sorted_bids_sorted under_bids) sorted).
have sortedbs': sort geq_bid bs' = under_bids.
  rewrite -sorting.
  apply/perm_sortP => //.
  exact: total_geq_bid.
  exact: transitive_geq_bid. 
  exact: anti_geq_bid.
  exact: perm_under_bids.
have: is_labelling bs' l'. 
  apply/andP; split; last by rewrite -(inj_eq val_inj) /= sort_eq_under.
  apply/eqP.
  apply: eq_from_tnth => j.
  rewrite !tnth_map !(tnth_nth bid0) tupleE /= sortedbs'.
  rewrite (@nth_map _ j _ bid0) ?(tnth_nth bid0);
    last by rewrite size_enum_ord ltn_ord.
  by rewrite val_ord_tuple nth_ord_enum tnth_map.
have: is_labelling bs' (labelling_of bs') by apply: xchooseP.
exact: labelling_singleton.
Qed.

Lemma eq_losing_price : tnth (tsort bs') (agent_succ i0) = tnth (tsort bs) i0.
Proof.
set i1 := agent_succ i0. 
move: (labellingP bs') => /forallP /(_ i1) /eqP ->.
move: (labellingP bs) => /forallP /(_ i0) /eqP ->.
have -> : projT1 (@exists_labellingW _ _ geq_bid bs' tr rr totr ar) = l'.
  apply: labelling_singleton.
  move: (@exists_labellingW _ _ geq_bid bs' tr rr totr ar) => [lab islab].
  exact: islab.
  by rewrite -is_under_labelling (tlabelP bs').
rewrite /l' tnth_map tnth_ord_tuple bs_uniq_labelling.
rewrite /under_index ifT /=; last by rewrite lt0n.
have -> : (ord_pred i1) = i0 by exact: val_inj.
apply: diff.
have -> : a = tnth l i by rewrite cancel_idxa.
have: i0 != i by rewrite eq_sym.
apply: contra_neq.
apply: (@labelling_inj _ _ _ _ l).
exact: (tlabelP bs).
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

Theorem individual_rational i (tv : forall bs, tnth bs i = v i) : auction.individual_rational a v i.
Proof. 
rewrite /auction.individual_rational /auction.p /= => o. 
case: (tnth o i) => iw' bs'.
case: ifP => [_|//]. 
by rewrite -(tv bs') -(labelling_spec_idxa bs' i) tsorted_bids_sorted // le_ord_succ.
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
  rewrite (eq_losing_price diff) // -?(labelling_spec_idxa bs).  
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
      by rewrite (labelling_spec_idxa bs) tnth_map tnth_ord_tuple.
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
    by rewrite (labelling_spec_idxa bs) tnth_map tnth_ord_tuple. 
by rewrite ltnn. 
Qed.

(** "Wolf and sheep" bidding is another Nash equilibrium for SP when bidding truthfully. 
     See https://homepages.cwi.nl/~apt/stra/ch7.pdf. *)

Section Wolf.
 
Notation cancel_inv_idxa bs := (@cancel_inv_idxa n' _ geq_bid bs
                             (@transitive_geq_bid p')
                             (@reflexive_geq_bid p') 
                             (@total_geq_bid p')
                             (@anti_geq_bid p')).
Variable bs : bids.

Definition l := (tlabel bs). 

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
  by rewrite tpermL /= tnth_map tnth_ord_tuple /wolf (cancel_inv_idxa bs) -(inj_eq val_inj).
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
    by rewrite -(labelling_spec_idxa bs) // tsorted_bids_sorted.
Qed.

End Wolf.

End Properties.

Check truthful_SP.
Print Assumptions truthful_SP. 
