(**

  FP.v
  
  First Prize.

  Proof by counter-example that FP is not truthful.

  Pierre Jouvelot (30/1/2022).

  Licence: CeCILL-B.

*)
 
From Coq Require Import Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp.fingroup Require Import perm.

From vcg Require Import lib labelling mech.

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

Notation tsort := (tsort geq_bid).
Notation idxa := (idxa geq_bid).

Section Algorithm.

Variable (bs0 : bids) (i : A).

Let bs := tsort bs0.
Let i' := idxa bs0 i.

Definition is_winner := i' == ord0.

Notation "'[bid' j 'in' bs ']'" := (tnth bs j) (at level 10).

Definition price : nat := [bid i' in bs].

End Algorithm.

End FP.

(** FP has zero utility for the winner if s/he bids truthfully. *)

Section ZeroUtility.

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

Lemma zero_utility (bs : bids) (i : A) (i_wins : is_winner bs i) :
  tnth bs i = tnth vs i -> U i (m bs) = 0.
Proof.
move=> tv.
rewrite /U /prefs.U /= /auction.U /auction.p /= tnth_map ifT -?tv; 
  first by rewrite /price labelling_spec_idxa subnn.
by move: i_wins => /=; rewrite /is_winner tnth_ord_tuple.
Qed.

End ZeroUtility.

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

Notation bid := (bid a_p').
Notation geq_bid := (@geq_bid a_p').
Notation tlabel := (tlabel geq_bid).
Notation idxa := (idxa geq_bid).

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
rewrite /idxa /ssr_have. 
case: sorted_diff_agent_spec_ex => j. 
have eqtlabel : tlabel bs2 = tlabel_bs2.
  apply: labelling_singleton; first by exact: tlabelP.
  by rewrite /is_labelling -(inj_eq val_inj). 
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
exact: transitive_geq_bid.
Qed.

End NotTruthfulness.

Check not_truthful_FP.
Print Assumptions not_truthful_FP.
