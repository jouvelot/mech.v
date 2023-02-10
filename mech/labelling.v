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

Lemma labelling_singleton' (x0 : T) : uniq s -> singleton is_labelling.
Proof.
move/uniqP => u l1 l2 /eqP eqs1 /eqP.
rewrite eqs1 => /eqP eqs.
apply: eq_from_tnth => j.
apply: val_inj => /=. 
apply: (u x0); first by rewrite size_tuple inE ltn_ord.
- by rewrite size_tuple inE ltn_ord. 
- rewrite -!tnth_nth.
  move: (eqs).
  rewrite -(tuple_of_tnth l1) -(tuple_of_tnth l2).
  rewrite -(inj_eq val_inj) /= -!map_comp -enumT => /eqP eqt.  
  pose f1 := (([eta tnth s] \o [eta tnth l1]) \o id).
  pose f2 := (([eta tnth s] \o [eta tnth l2]) \o id).
  have/(_ j) /=: forall k, f1 k = f2 k.
    move=> k.
    by rewrite (iffRL (eq_in_map f1 f2 (enum 'I_n))) // -deprecated_filter_index_enum map_f.
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
move: u; rewrite -(sort_uniq r) => /(uniqP x0). 
rewrite !size_sort !size_tuple /= => u j1 j2 eqtn.
apply/val_inj/u; first by rewrite !inE ltn_ord.
- by rewrite !inE ltn_ord.
- rewrite -!tnth_nth.
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
by rewrite cancel_idxa.
Qed.

Lemma idxa_inj : injective idxa.  
Proof.
move=> i1 i2.
rewrite /idxa /ssr_have /=.  
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
  apply: (@eq_from_tnth) => j.
  by rewrite tnth_map /= cancel_inv_idxa.
by rewrite -(inj_eq val_inj) => /= /eqP ->.
Qed.

Lemma uniq_to_idxa k (o : k.-tuple 'I_n) : 
  uniq o -> uniq (map_tuple idxa o).
Proof. by move=> ouniq; rewrite map_inj_uniq //= => i1 i2 /idxa_inj. Qed.

Conjecture uniq_s : forall l, injective (tnth l) -> uniq s.

Lemma idxa_as_index (x0 : T) (us : uniq s) i : idxa i = index (tnth s i) s' :> nat.
Proof.
rewrite /idxa /ssr_have /=.
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
pose ip := (@sorted_diff_agent_spec_ex i). 
rewrite -(projT2 ip) /idxa /ssr_have.
case: sorted_diff_agent_spec_ex => j <-.
by rewrite sorted_tlabel // ?tnth_ord_tuple.
Qed.

End Labelling.

Section Tperm.

Variables (n : nat) (T : eqType) (r : rel T) (s : n.+1.-tuple T).

Notation idxa := (idxa r).

Lemma idxa_perm (p : 'S_n.+1) i : idxa ([tuple tnth s (p i)  | i < n.+1]) i = idxa s (p i).
Admitted.

Variable (i1 i2 : 'I_n.+1).

Notation "[ 'swap' s | i1 , i2 ]" := 
  ([tuple tnth s (tperm i1 i2 i)  | i < n.+1]) (at level 0).

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

Section Lt.

Variable (lti'i : ix' < ix).

Variable (l : labelling n.+1) (islab : is_labelling r s l).

Definition lx j := if j == ix' then ix else if ix' < j <= ix then ord_pred j else j.

Definition lx_inv j := if j == ix then ix' else if ix' <= j < ix then ord_succ j else j.

Lemma cancel_lx : cancel lx_inv lx.
Proof.
move=> j.
rewrite /lx /lx_inv. 
have [/eqP ->|neix] := boolP (j == ix); first by rewrite eq_refl.
have [/eqP|nejix'] := boolP (j == ix'). 
- rewrite (@leq_eqVlt ix' j) => ->.
  rewrite eq_refl orTb andTb lti'i ifF; 
    last by rewrite -(inj_eq val_inj) /= gtn_eqF // lt_ord_succ // (@leq_trans ix) // leq_ord.
  rewrite -lt_le_agent /= ?below_last_ord; last by rewrite (@leq_trans ix) // leq_ord.
  by rewrite lt_ord_succ ?ltii' /= ?cancel_ord_succ // (@leq_trans ix) // leq_ord.
- rewrite (@leq_eqVlt ix' j) (eq_sym (val ix')) /=.    
  have -> : (val j == val ix') = false.
    move: nejix'; apply: contra_neqF => /eqP eqjx; exact: val_inj.
  rewrite orFb.
  have [/andP [ltix'j ltjix]|/nandP [lejix'|ltjix]] := boolP (ix' < j < ix).
  - rewrite ifF; last by rewrite -(inj_eq val_inj) /= gtn_eqF // (@leq_trans j) // le_ord_succ.
    rewrite ifT; first by rewrite cancel_ord_succ // (@leq_trans ix) // leq_ord.
    apply/andP; split; 
      last by rewrite -lt_le_agent // ?below_last_ord (@leq_trans ix) // leq_ord.
    by rewrite (@ltn_trans j) // lt_ord_succ // (@leq_trans ix) // leq_ord.
  - rewrite -leqNgt in lejix'.
    rewrite ifF; last by move: nejix'; apply: contra_neqF => /eqP eqjx. 
    rewrite ifF => //; last by rewrite ltnNge lejix' /=.
  - rewrite -leqNgt in ltjix.
    rewrite ifF; last by move: nejix'; apply: contra_neqF => /eqP eqjx. 
    rewrite ifF // (leq_eqVlt j ix) // (ltnNge j) ltjix /= orbF (@leq_trans ix) // andTb.
    by move: neix; apply: contra_neqF => /eqP eqjx; apply: val_inj.
Qed.

Definition l' := [tuple tnth l (lx j) | j < n.+1]. 

Local Lemma l'_in_iota : [seq val (nth ord0 l (lx j)) | j <- enum 'I_n.+1] =i iota 0 n.+1.
Proof.  
move=> j. 
apply/(nthP 0)/(nthP 0) => [[x ltxn1 <-]|[x ltxn1 <-]].
- rewrite size_map size_enum_ord in ltxn1.
  rewrite size_iota. 
  exists (nth 0 [seq val (nth ord0 l (lx j0)) | j0 <- enum 'I_n.+1] x);
    first by rewrite (nth_map ord0) ?size_enum_ord //=.    
  by rewrite nth_iota ?add0n // (nth_map ord0) ?size_enum_ord //=.    
- rewrite size_iota in ltxn1.
  rewrite size_map size_enum_ord nth_iota // add0n.
  have [ixx ->] : exists ixx, x = tnth l ixx.
    move: (labelling_onto islab) => /(_ (Ordinal ltxn1)) [] => ixx0 /eqP eq0.
    by exists ixx0; rewrite eq0.
  exists (lx_inv ixx) => //.
  rewrite !(nth_map ord0) ?size_map -?enumT ?size_enum_ord //= -tnth_nth.   
  have -> : nth ord0 (enum 'I_n.+1) (lx_inv ixx) = lx_inv ixx.
    by apply: val_inj => /=; rewrite nth_ord_enum. 
  by rewrite cancel_lx.
Qed.

Lemma l'_in_enum : l' =i enum 'I_n.+1.
Proof.
apply/perm_mem/(@perm_map_inj _ _ val); first by exact: val_inj.   
have mvl' : map val l' =i iota 0 n.+1.
  have -> : map val l' = [seq val (nth ord0 l (lx j)) | j <- enum 'I_n.+1]. 
    apply: (@eq_from_nth _ 0) => [|j ltjn1]; first by rewrite !size_map -enumT size_enum_ord.
    rewrite !size_map -enumT size_enum_ord in ltjn1.
    by rewrite !(nth_map ord0) ?size_map -?enumT ?size_enum_ord // -tnth_nth.
  exact: l'_in_iota.
rewrite uniq_perm ?val_enum_ord ?(@eq_uniq _ _ (iota 0 n.+1)) ?iota_uniq //.
by rewrite size_iota !size_map -enumT size_enum_ord.
Qed.

Lemma sorted_leq_tnth :
  ∀ (T : Type) (x : T) (leT : rel T),
    transitive leT
    → reflexive leT
    → ∀ (n : nat) (s : n.-tuple T),
        sorted leT s
        → {homo tnth s : i j / i <= j >-> leT i j}.
Proof.
move=> T0 x0 leT tr refl n0 s0 ss0 i1 i2 lei1i2 /=.
by rewrite !(@tnth_nth _ _ x0) sorted_leq_nth ?inE // ?size_tuple ?ltn_ord.
Qed.

Local Lemma eq_l_tlabel : l = tlabel r s.
Proof. 
apply: (@labelling_singleton _ _ r s); first by rewrite islab. 
exact: tlabelP.
Qed. 

Lemma sorted_lt_index (i0 : T) : sorted r [tuple tnth s' (tnth l' j) | j < n.+1].
(*
Proof.
apply: (@path_sorted _ _ i0).
have -> : [tuple tnth s' (tnth l' j)  | j < n.+1]
            = [tuple tnth s' (tnth l (lx j))  | j < n.+1]. 
  apply: eq_from_tnth => j.
  by rewrite !tnth_map !tnth_ord_tuple.
apply/(pathP i0) => j ltjs.
rewrite !size_map -enumT size_enum_ord in ltjs.
rewrite !(nth_map ord0) ?size_map -?enumT ?size_enum_ord //.
have [/eqP -> //=|nej0] := boolP (j == 0).
rewrite -(@prednK j) // ?lt0n //=.
rewrite !(nth_map ord_max) ?size_map -?enumT ?size_enum_ord ?prednK ?lt0n // 1?ltnW //.
have ltj1s : j.-1 < n.+1 by rewrite (@leq_ltn_trans j) // leq_pred.
rewrite /lx eq_l_tlabel !(nth_agent_enum ltjs) !(nth_agent_enum ltj1s).
set oj := Ordinal ltjs; set oj1 := Ordinal ltj1s.
have [/orP [ltji'|ltj1i]|/norP] := boolP ((oj < ix') || (ix < oj1)). 
- rewrite ifF; last by rewrite -(inj_eq val_inj) ltn_eqF // (@leq_ltn_trans oj) ?leq_pred.
  rewrite ifF; last by rewrite ltnNge (@leq_trans oj) ?leq_pred // ltnW.
  rewrite ifF; last by rewrite -(inj_eq val_inj) /= ltn_eqF.
  rewrite ifF; last by rewrite ltnNge (ltnW ltji'). 
  have/differ_on -> : tnth (tlabel r s) oj1 != i.
    rewrite -(cancel_idxa r s i) (@contra_neq _ _ oj1 ix) //. 
    apply: (labelling_inj (tlabelP r s)). 
    rewrite negbT // -(inj_eq val_inj) /= ltn_eqF //. 
    by rewrite (@leq_ltn_trans oj) ?leq_pred // (@ltn_trans ix').
  have/differ_on -> : tnth (tlabel r s) oj != i.
    rewrite -(cancel_idxa r s i) (@contra_neq _ _ oj ix) //. 
    apply: (labelling_inj (tlabelP r s)). 
    by rewrite negbT // -(inj_eq val_inj) /= ltn_eqF // (@ltn_trans ix').
  rewrite -!(labelling_spec_idxa r s) !cancel_inv_idxa.
  by rewrite (@sorted_leq_tnth _ _ r) //= ?sort_sorted // leq_pred.
- rewrite ifF; last by rewrite -(inj_eq val_inj) gtn_eqF // (ltn_trans lti'i).
  rewrite ifF; last by rewrite (@leqNgt oj1) ltj1i /= andbF.
  rewrite ifF; last by rewrite -(inj_eq val_inj) gtn_eqF //= (@ltn_trans ix) // 
                                                 (@leq_trans oj1) // leq_pred.
  rewrite ifF; last by rewrite (@leqNgt oj) (@ltn_trans oj1 ix) ?andbF // ltn_predL lt0n.
  have/differ_on -> : (tnth (tlabel r s) oj1) != i.
    rewrite -(cancel_idxa r s i) (@contra_neq _ _ oj1 ix) //. 
    apply: (labelling_inj (tlabelP r s)). 
    by rewrite negbT // -(inj_eq val_inj) /= gtn_eqF.
  have/differ_on -> : (tnth (tlabel r s) oj) != i.
    rewrite -(cancel_idxa r s i) (@contra_neq _ _ oj ix) //. 
    apply: (labelling_inj (tlabelP r s)). 
    by rewrite negbT // -(inj_eq val_inj) /= gtn_eqF // (@leq_trans oj1) ?leq_pred.
  rewrite -!(labelling_spec_idxa r s) !cancel_inv_idxa.
  by rewrite (@sorted_leq_tnth _ _ r) //= ?sort_sorted // leq_pred.
- rewrite -!leqNgt; move=> [lei'j lej1i].
  have [/eqP eqji' {lei'j}|neji'] := boolP (oj == ix'). 
  - rewrite ifF; last by rewrite -eqji' -(inj_eq val_inj) /= ltn_eqF // ltn_predL lt0n.
    rewrite ifF; last by rewrite -eqji' ltnNge leq_pred. 
    rewrite cancel_idxa. 
    have nej1i : tnth (tlabel r s) oj1 != i. 
      rewrite -(cancel_idxa r s i) (@contra_neq _ _ oj1 ix) //. 
      apply: (labelling_inj (tlabelP r s)). 
      rewrite negbT // -(inj_eq val_inj) /= ltn_eqF //. 
      by rewrite (@leq_ltn_trans ix') // -eqji' ?leq_pred.
    rewrite differ_on // -(labelling_spec_idxa r s) cancel_inv_idxa. 
    apply: (@transitive_r (tnth t ix')).
    - by admit.
    - rewrite -(labelling_spec_idxa r s').
     
    by admit.
- have [/eqP eqj1i'|nej1i'] := boolP (oj1 == ix').  
  - rewrite ifT; last first.
    - apply/andP; split; first by rewrite -eqj1i' ltn_predL lt0n.
      have -> : val oj = oj1.+1 by rewrite (@ltn_predK 0) //= lt0n.
      by rewrite eqj1i'.
    - rewrite cancel_idxa. 
      have -> : ord_pred oj = oj1 by apply: val_inj.
      rewrite eqj1i'.
*)
Admitted.

Local Lemma l'_uniq' : uniq [seq val (nth ord0 l (lx j)) | j <- enum 'I_n.+1].
Proof.
apply/(uniqP 0) => j j' ltj ltj'.
rewrite !inE !size_map -enumT size_enum_ord in ltj ltj'.
rewrite !(nth_map ord0) -?enumT ?size_enum_ord ?size_tuple ?ltn_ord //=.
rewrite (nth_ord_enum _ (Ordinal ltj)) (nth_ord_enum _ (Ordinal ltj')) /=.
suff have: forall j j' (ltj : j < n.+1) (ltj' : j' < n.+1), 
    j <= j' -> nth ord0 l (lx (Ordinal ltj)) = nth ord0 l (lx (Ordinal ltj')) → j = j'.
  move: (leq_total j j') => /orP [lejj' lH eqn|lej'j /(_ j' j ltj' ltj lej'j) /= f eqt]; 
    first by apply/lH/val_inj. 
  exact/esym/f/val_inj.
apply => {j j' ltj ltj'} => j j' ltj ltj'.
rewrite leq_eqVlt /lx => /orP [/eqP //|ltjj']. 
set oj := Ordinal ltj; set oj' := Ordinal ltj'.
set oj1 := ord_pred oj; set oj'1 := ord_pred oj'; set linj := labelling_inj islab.
rewrite -!tnth_nth.
case: ifP => [|neji'].
- case: ifP => [/eqP <-|nej'i']; first by rewrite -(inj_eq val_inj) /= => /eqP.   
  case: ifP => [/andP [lti'j' ltj'i /eqP] eqji' /linj /eqP|/nandP].    
  - rewrite -(inj_eq val_inj) /= -{2}(@prednK j'); last by rewrite (@leq_ltn_trans ix').
    by rewrite gtn_eqF // (@leq_trans j') // ltn_predL (@leq_ltn_trans ix').
  - rewrite -leqNgt -ltnNge => ort eqt /linj.
    move: ort => [lej'i' eqji'|ltij' eqji']; first by move: lej'i'; rewrite -eqji' leqNgt lti'i.
    by move: ltij' => /ltn_eqF; rewrite eqji' eq_refl.
 - case: ifP => [/andP [lti'j leji]|/nandP].
   - case: ifP => [/eqP eqj'i' /linj eqt|nej'i'];
       first by move: (lti'i) leji; rewrite -eqt -eqj'i' lenn1 // (@leq_ltn_trans ix').
     case: ifP => [/andP [lti'j' ltj'i] /linj/ord_pred_inj|/nandP]. 
     - move/(_ (leq_ltn_trans (leq0n ix') lti'j) (leq_ltn_trans (leq0n ix') lti'j')) => /eqP.
       by rewrite -(inj_eq val_inj) /= => /eqP ->.
     - rewrite -leqNgt -ltnNge => ot /linj /eqP. 
       rewrite -(inj_eq val_inj) /=.
       move: ot => [|ltij'].
       - move: nej'i'; rewrite leq_eqVlt -(inj_eq val_inj) /= => ->.   
         rewrite orFb => ltj'i'.
         by rewrite gtn_eqF // (@leq_trans ix') // 
                 -(@ltn_predK j' ix') //= ltn_predRL (@ltn_predK j').
      - rewrite ltn_eqF // (@leq_trans ix) //; last by exact: ltnW.
        by rewrite (@leq_trans j) //= ltn_predL (@leq_ltn_trans ix').
- rewrite -leqNgt -ltnNge; move=> [leji'|ltij].  
  - case: ifP => [eqj'i' /linj/eqP|nej'i'].
    - rewrite -!(inj_eq val_inj) /= in neji' *.
      rewrite ltn_eqF // (@ltn_trans ix') //.
      by move: leji'; rewrite leq_eqVlt /= neji' orFb.
    - case: ifP => [/andP [lti'j' ltj'ij]|/nandP _] /linj /eqP;
        last by rewrite -(inj_eq val_inj) /= => /eqP.
      rewrite -!(inj_eq val_inj) /= in neji' *. 
      rewrite ltn_eqF // (@leq_trans ix') //; 
        first by move: leji'; rewrite leq_eqVlt /= neji' orFb.
      by move: (lti'j') => /=; rewrite -{1}(ltn_predK ltjj') ltnS. 
  - case: ifP => [eqj'i' /linj /eqP|nej'i']; first by rewrite -(inj_eq val_inj) /= gtn_eqF.
    case: ifP => [/andP [/= lti'j' /= ltj'i]|/nandP _ /linj /eqP];
        first by move: (leq_ltn_trans ltj'i ltij) => /=; rewrite ltnNge leq_eqVlt ltjj' orbT. 
    by rewrite -(inj_eq val_inj) /= => /eqP.
Qed.

Lemma l'_uniq : uniq l'.
Proof.
move=> /=.
rewrite (@map_uniq _ _ val) //.
have -> : [seq val i | i <- [seq tnth l (lx j) | j <- enum 'I_n.+1]] = 
           [seq val (nth ord0 l (lx j)) | j <- enum 'I_n.+1].
  apply: (@eq_from_nth _ 0) => [|j ltjs /=]; first by rewrite !size_map.
  rewrite !size_map -enumT size_enum_ord in ltjs.
  by rewrite !(nth_map ord0) ?size_map -?enumT ?size_enum_ord // (tnth_nth ord0).
exact: l'_uniq'.
Qed.

Definition lt_labelling := l'.

Variable i0 : T.

Lemma labelling_differ_on_lt : is_labelling r s' l'.
Proof.
rewrite /is_labelling -(inj_eq val_inj) /=. 
rewrite -map_comp /=.
set ss' := (X in _ == X). 
have {ss'} -> : ss' = [seq (tnth s' (tnth l (lx j))) | j <- enum 'I_n.+1].
  apply: (@eq_from_nth _ i0) => [|j ltjs]; first by rewrite size_map.
  rewrite (@nth_map _ ord0) // size_enum_ord. 
  by rewrite size_map size_enum_ord in ltjs.
set ss' := (X in _ == X). 
have sortedss' : sorted r ss'. 
  have -> : ss' = [tuple tnth s' (tnth l' j)  | j < n.+1].
    apply: (@eq_from_nth _ i0) => [|/= j ltjs]; first by rewrite !size_map.
    rewrite size_map size_enum_ord in ltjs.
    rewrite /ss' !(nth_map ord0) -?enumT ?size_enum_ord //; congr tnth.
    by rewrite /l' tnth_map tnth_ord_tuple.
  exact: sorted_lt_index.  
rewrite -(sorted_sort transitive_r sortedss').
apply/eqP/perm_sortP => //.
rewrite perm_sym.  
apply/(perm_iotaP i0).    
exists [seq nth 0 (map val l) (lx j) | j <- enum 'I_n.+1].  
- have -> : [seq nth 0 [seq val i | i <- l] (lx j) | j <- enum 'I_n.+1] =
             [seq val (nth ord0 l (lx j)) | j <- enum 'I_n.+1].
    apply: (@eq_from_nth _ 0) => [|j ltjs]; first by rewrite !size_map.
    rewrite size_map ?size_enum_ord in ltjs.
    rewrite (nth_map ord0) ?size_enum_ord //=.
    by rewrite !(nth_map ord0) -?enumT ?size_enum_ord ?size_tuple ?ltn_ord.  
  rewrite size_tuple uniq_perm ?iota_uniq //; last by exact: l'_in_iota.  
  exact: l'_uniq'.
- apply: (@eq_from_nth _ i0) => [|j ltjs]; first by rewrite !size_map.
  rewrite size_tuple card_ord in ltjs.
  rewrite !(nth_map 0) ?(@nth_map _ ord0 _ i0) ?(tnth_nth i0) 
          ?size_map -?enumT ?size_enum_ord //=.
  congr nth.
  rewrite (nth_map ord0) ?size_enum_ord // (tnth_nth ord0).
  rewrite (@nth_ord_enum n.+1 ord0 (Ordinal ltjs)).
  by rewrite !(nth_map ord0) -?enumT ?size_enum_ord ?size_tuple ?ltn_ord.
Qed.

End Lt.

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
  have -> : l = tlabel r s by apply: (@labelling_singleton _ _ r s) => //; exact: tlabelP.
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

