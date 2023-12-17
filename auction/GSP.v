(**

  GSP.v
  
  Generalized Second Prize (see Tim Roughgarden's Lecture note #13 CS269I).

  Proof of rationality and, by counter-example, that GSP is not truthful.

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

Section GSP.

Variable (n' : nat).
Definition n := n'.+1.

Definition A := agent.type n.

Notation agent_succ := (@agent.succ n').

Variable (k' : nat).
Definition k := k'.+1.
Definition slot := 'I_k.

Variable (q' : nat).
Definition q := q'.+1.
Definition ctr := 'I_q.
Definition ctrs := k.-tuple ctr.

Variable (cs : ctrs).
Notation "'ctr_ s" := (tnth cs s) (at level 10).

Variable p' : nat.
Definition p := p'.+1.
Definition bid := 'I_p.
Definition bid0 : bid := Ordinal (ltn0Sn p').
Definition bids := n.-tuple bid.

Let geq_bid := @geq_bid p'.

Notation tsort := (tsort geq_bid).
Notation idxa bs i := (@idxa n' _ geq_bid bs
                             (@transitive_geq_bid p')
                             (@total_geq_bid p')
                             (@anti_geq_bid p')
                             i).

Section Algorithm.

Variable (bs0 : bids) (i : A).

Let bs := tsort bs0.
Let i' := idxa bs0 i.

Definition is_winner := i' < k.

Notation "'[bid' j 'in' bs ']'" := (tnth bs j) (at level 10).

Definition slot_won := @sub_ord k' (k' - i').

Definition price := [bid (agent_succ i') in bs] * 'ctr_slot_won.

End Algorithm.

(** GSP is rational if one bids one's true value `v`. *)

Notation labelling_spec_idxa := 
  (@labelling_spec_idxa _ _ _ _ 
                        (@transitive_geq_bid p')
                        (@total_geq_bid p')
                        (@anti_geq_bid p')).
Variable v : A -> bid.

Theorem rational (bs : bids) (i : A) (i_wins : is_winner  bs i) : 
  tnth bs i = v i -> price bs i <= v i * 'ctr_(slot_won bs i).
Proof. 
move: i_wins; rewrite /is_winner => /eqP _ <-.
have tsorted_bids_sorted: sorted_bids (tsort bs).
  apply/sorted_bids_sorted.
  apply: sort_sorted.
  exact: total_geq_bid.
rewrite /price -(labelling_spec_idxa i).
case s0: ('ctr_ (slot_won bs i) == ord0); first by move: s0 => /eqP -> /=; rewrite !muln0.
by rewrite leq_pmul2r ?lt0n ?negbT // tsorted_bids_sorted // le_ord_succ.
Qed.

End GSP.

Section NotTruthfulness.

(* 3 bidders *)
Definition a_n' := 2.

Notation A := (A a_n').
Notation agent_succ := (@agent.succ a_n').

Definition a0 : A := ord0.
Definition a1 : A := agent_succ a0.
Definition a2 : A := agent_succ a1.

(* 3 slots *)
Definition a_k' := 2.

(* Ranges of ctrs and bids *)
Definition a_q' := 10.
Definition a_p' := 10.

Notation bid := (bid a_p').

Notation tsort := (tsort (@geq_bid a_p')).
Notation tlabel bs := (@tlabel a_n' _ (@geq_bid a_p') bs
                             (@transitive_geq_bid a_p')
                             (@total_geq_bid a_p')
                             (@anti_geq_bid a_p')).
Notation idxa bs i := (@idxa a_n' _ (@geq_bid a_p') bs
                             (@transitive_geq_bid a_p')
                             (@total_geq_bid a_p')
                             (@anti_geq_bid a_p')
                             i).

Notation sub_ord := (@sub_ord 10).

(* ctrs = 10, 5, 0 *)
Definition cs : ctrs a_k' a_q' := map_tuple sub_ord [tuple 0; 5; 10].  

(* true values = 10, 9, 6 *)
Definition vs : bids a_n' a_p' := map_tuple sub_ord [tuple 0; 1; 4].

(* bs1: all ais bid their true value. *)
Definition bs1 : bids a_n' a_p' := vs.

(* bs2: a0 underbids = 8, 9, 6 *)
Definition bs2 : bids a_n' a_p' := cons_tuple (sub_ord 2) (behead_tuple bs1). 

Definition tlabel_bs2 := [tuple a1; a0; a2].

Lemma idxaK_bs2 : idxa bs2 a0 = a1.
Proof. 
rewrite /labelling.idxa. 
case: sorted_diff_agent_spec_ex => j.
have eqtlabel : tlabel bs2 = tlabel_bs2.
  apply: labelling_singleton; first by exact: tlabelP.
  apply/andP; split.
  - apply/eqP.
    apply: val_inj => /=. 
    set r := (X in sort X).
    have -> //=: sort r [:: sub_ord 2; sub_ord 1; sub_ord 4] = [:: sub_ord 1; sub_ord 2; sub_ord 4].
      by rewrite sortE.
  - rewrite /is_labelling -(inj_eq val_inj) /a_n' /=.
    have -> // : enum 'I_3 = [:: a0; a1; a2].
      apply: (@eq_from_nth _ a0)=> [/=|k ltks]; first by rewrite size_enum_ord /n /a_n'. 
      rewrite /n /a_n' /= in ltks *.
      case: k ltks => k'.
      - by have -> : nth a0 (enum 'I_3) 0 = a0 by apply: val_inj => /=; rewrite nth_enum_ord.
      - case: k' => //= k''.
        - by have -> : nth a0 (enum 'I_3) 1 = a1 by apply: val_inj => /=; rewrite nth_enum_ord.
        - case: k'' => //= k'''.
          - by have -> //: nth a0 (enum 'I_3) 2 = a2 by apply: val_inj => /=; rewrite nth_enum_ord.
          - by rewrite size_enum_ord /n.
rewrite (_ : a0 = tnth tlabel_bs2 a1) // -eqtlabel. 
apply: labelling_inj.
exact: tlabelP.
Qed.

Notation n := (n a_n').
Notation k' := a_k'.
Notation is_winner := (@is_winner a_n' a_p').

Definition m : mech.type n := 
  mech.new (fun bs => map_tuple (fun a => let i' := idxa bs a in
                                    (is_winner bs a, (price cs bs a, slot_won k' bs a)))
                             (agent.agents n)).

Definition pr : prefs.type m :=
  prefs.new (tnth vs) 
            (fun i (o : mech.O m) => 
               let: (w, (p, s)) := tnth o i in
               if w then tnth vs i * tnth cs s - p else 0)
            (tnth vs).

Lemma not_truthful_GSP : not (truthful pr).
Proof.
apply: not_truthful.
exists a0. exists bs1. exists bs2.
have diff: differ_on bs1 bs2 a0.
  move=> j. 
  rewrite /action_on /bs2 /bs1 /vs /a0 /a_n'.
  have [] := boolP (0 < j) => [lt0j|]; last by rewrite lt0n negbK -(inj_eq val_inj) /= => /eqP ->.
  rewrite !(tnth_nth ord0) /= -lt0n => /prednK <-.
  by rewrite -nth_behead.
split => //.
split => /=; first by congr sub_ord.
rewrite !tnth_map !tnth_ord_tuple /is_winner /= /price /slot_won.
by rewrite idxaK //= ?idxaK_bs2.
Qed.

End NotTruthfulness.

Check not_truthful_GSP. 
Print Assumptions not_truthful_GSP.
