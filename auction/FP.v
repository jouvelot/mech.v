(**

  FP.v
  
  First Prize.

  Proof of 0-utility, rationality and, by counter-example, that FP is not truthful.

  Pierre Jouvelot (30/1/2022).

  Licence: CeCILL-B.

*)
 
From Coq Require Import Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp.fingroup Require Import perm.

From mech.lib Require Import lib labelling mech.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FP.

Variable (n' : nat).
Definition n := n'.+1.

Definition A := agent.type n.

Notation agent_succ := (@agent.succ n').

Variable p' : nat.
Definition p := p'.+1.
Definition bid := 'I_p.
Definition bid0 : bid := Ordinal (ltn0Sn p').
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
Notation cancel_inv_idxa bs := (@cancel_inv_idxa _ _ geq_bid bs tr rr totr ar).
Notation uniq_to_idxa bs u := (@uniq_to_idxa _ _ geq_bid bs tr rr totr ar _ _ u). 
Notation uniq_from_idxa bs u := (@uniq_from_idxa _ _ geq_bid bs tr rr totr ar _ _ u). 

Notation tsort := (tsort geq_bid).
Notation idxa bs i := (@idxa n' _ geq_bid bs tr totr ar i). 

Section Algorithm.

Variable (bs0 : bids) (i : A).

Let bs := tsort bs0.
Let i' := idxa bs0 i.

Definition is_winner := i' == ord0.

Notation "'[bid' j 'in' bs ']'" := (tnth bs j) (at level 10).

Definition price : nat := [bid i' in bs].

End Algorithm.

End FP.

Section Theorems.

Variable (a_n' : nat).

Notation A := (A a_n').
Notation n := (n a_n').

Variable (a_p' : nat).

Notation bid := 'I_(p a_p').
Notation bids := (bids a_n' a_p').

Notation is_winner := (@is_winner a_n' a_p').

Let m := mech.new (fun (bs : bids) => map_tuple (fun i => (is_winner bs i, bs)) (agent.agents n)).

Let a := 
  @auction.new _ _ m (fun o i => 
                        let: (w, bs) := tnth o i in
                        if w then Some (price bs i) else None).

Variable (vs : n.-tuple bid).

Definition ps := auction.prefs a (tnth vs).

Definition U := prefs.U ps.

(** FP has zero utility for the winner if s/he bids truthfully. *)

Lemma zero_utility (bs : bids) (i : A) (i_wins : is_winner bs i) :
  tnth bs i = tnth vs i -> U i (m bs) = 0.
Proof.
move=> tv.
rewrite /U /prefs.U /= /auction.U /auction.p /= tnth_map ifT -?tv.
rewrite /price labelling_spec_idxa ?subnn //=.
by move: i_wins => /=; rewrite /is_winner tnth_ord_tuple.
Qed.

(** FP is rational if one bids truthfully. *)

Theorem rational (bs : bids) (i : A) : 
  tnth bs i = tnth vs i -> price bs i <= tnth vs i.
Proof. by rewrite /price labelling_spec_idxa => ->. Qed.

(** FP is anonymous, if bids are always assumed unique. *)

Section Anonymous.

Theorem anonymous_XP (uniq_bids : forall bs : bids, uniq bs) : 
  auction.anonymous a.
Proof.
move=> bs i1 i2 /= w1.
rewrite /auction.is_winner /auction.price /price /= in w1.
rewrite !tnth_map !tnth_ord_tuple /is_winner /price in w1.
rewrite (labelling_spec_idxa bs) in w1.
split=> [//|]. 
- rewrite /auction.is_winner /auction.price /price /=.
  rewrite !tnth_map !tnth_ord_tuple /is_winner /price.
  set abs := (X in idxa X). 
  rewrite (labelling_spec_idxa abs).
  by rewrite !tnth_map !tnth_ord_tuple !apermE !tpermR idxa_tpermR // ?uniq_bids.
- split.
- rewrite /auction.is_winner /auction.price /price /=.
  rewrite !tnth_map !tnth_ord_tuple /is_winner /price.
  rewrite (labelling_spec_idxa bs).
  set abs := (X in idxa X _ _ _ i2). 
  rewrite (labelling_spec_idxa abs).
  by rewrite !tnth_map !tnth_ord_tuple !apermE !tpermR idxa_tpermR // ?uniq_bids.
- move=> i [n1 n2].
- rewrite !tnth_map !tnth_ord_tuple /is_winner idxa_tpermD // ?uniq_bids //.
  rewrite /price.
  rewrite (labelling_spec_idxa [tuple tnth bs (aperm i0 (tperm i1 i2))  | i0 < n]).
  by rewrite (labelling_spec_idxa bs) !tnth_map apermE !tnth_ord_tuple tpermD 1?eq_sym.
Qed.

End Anonymous.

End Theorems.

(** Non truthfulness. *)

Section NotTruthfulness.

(* 2 bidders *)
Definition a_n' := 1.

Notation A := (A a_n').
Notation agent_succ := (@agent.succ a_n').

Definition a0 : A := ord0.
Definition a1 : A := agent_succ a0.

(* Range of bids *)
Definition a_p' := 10.

Notation tr := (@transitive_geq_bid a_p').
Notation totr := (@total_geq_bid a_p').
Notation ar := (@anti_geq_bid a_p').
Notation rr := (@reflexive_geq_bid a_p').

Notation bid := (bid a_p').
Notation geq_bid := (@geq_bid a_p'). 
Notation tlabel bs := (@tlabel a_n' _ geq_bid bs tr totr ar).
Notation idxa bs i := (@idxa a_n' _ geq_bid bs tr totr ar i).
Notation labelling_spec_idxa :=  (@labelling_spec_idxa _ _ _ _ tr totr ar).

Notation bids := (bids a_n' a_p').

(* true values = 10, 8 *)
Definition vs : bids := map_tuple sub_ord [tuple 0; 2].

(* bs1: all ais bid their true value. *)
Definition bs1 : bids := vs.

(* bs2: a0 underbids = 9, 8 *)
Definition bs2 : bids := map_tuple sub_ord [tuple 1; 2].

Definition tlabel_bs2 := [tuple a0; a1].

Lemma idxaK_bs2 : idxa bs2 a0 = a0.
Proof.
rewrite /labelling.idxa /sval. 
case: sorted_diff_agent_spec_ex => j. 
have eqtlabel : tlabel bs2 = tlabel_bs2.
  rewrite sorted_tlabel => //=.
  - apply: val_inj => /=.
    apply: (inj_map val_inj) => /=.
    by rewrite val_enum_ord /a_n'.
rewrite [in RHS](_ : a0 = tnth tlabel_bs2 a0) // -eqtlabel. 
apply: labelling_inj. 
exact: tlabelP.
Qed.

Notation n := (n a_n').
Notation is_winner := (@is_winner a_n' a_p').

Let m := mech.new (fun (bs : bids) => map_tuple (fun i => (is_winner bs i, bs)) (agent.agents n)).

Let a := 
  @auction.new _ _ m (fun o i => 
                        let: (w, bs) := tnth o i in
                        if w then Some (price bs i) else None).

Definition prefs := auction.prefs a (tnth vs).

Lemma not_truthful_FP : not (truthful prefs).
Proof.
apply: not_truthful.
exists a0. exists bs1. exists bs2.
have diff: differ_on bs1 bs2 a0.
  move=> j. 
  rewrite /action_on /bs2 /bs1 /vs /a0 /a_n'.
  have [] := boolP (0 < j) => [lt0j|]; last by rewrite lt0n negbK -(inj_eq val_inj) /= => /eqP ->.
  rewrite !(tnth_nth (sub_ord 0)) /= -lt0n => /prednK <-.
  by rewrite -nth_behead.
split => //.
split => //=.
rewrite /auction.U /auction.p //= !tnth_map !tnth_ord_tuple /is_winner /= /price. 
rewrite idxaK //= ?idxaK_bs2 //=.
Qed.

End NotTruthfulness.

Check not_truthful_FP.
Print Assumptions not_truthful_FP.
