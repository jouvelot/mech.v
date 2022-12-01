(**

  XP.v

  Fixed Price, as a mech.v instance.

  Proofs of rationality, truthfulness and Pareto-optimality.

  Pierre Jouvelot (7/2021).

  Licence: CeCILL-B.

*)

From Coq Require Import Unicode.Utf8.
From mathcomp Require Import all_ssreflect all_algebra.

From mech.lib Require Import lib mech.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variable n : nat.     (* number of bidders *)

Variable b : nat.     (* max value of bid *)

Variable fixed_price : nat.

Section Algorithm.

Variable bids : n.-tuple 'I_b.

Variable i : agent.type n.

Definition is_winner := fixed_price <= tnth bids i.

Definition price := fixed_price.

End Algorithm.

Definition m := mech.new (fun bs => map_tuple (is_winner bs) (agent.agents n)).

Definition a := auction.new (fun (o : mech.O m) i => if tnth o i then Some price else None).

Variable v : agent.type n -> 'I_b.

Definition p := auction.prefs a v.

Section Properties.

(** XP is rational if one bids one's true value `v`. *)

Notation bids := (n.-tuple 'I_b).

Lemma rational (bs : bids) (i : agent.type n) (i_wins : is_winner  bs i) : 
  tnth bs i = v i -> price <= v i.
Proof. by move=> <-. Qed.

Lemma truthful_XP : truthful p.
Proof. 
rewrite /truthful => bs bs' i tv /=.
rewrite /action_on /auction.U /auction.p /= !tnth_map !tnth_ord_tuple => <-. 
have [] := boolP (is_winner bs' i) => [_|] //.
have [] := boolP (is_winner bs i) => [//|niw]. 
rewrite /is_winner -ltnNge in niw.
by rewrite leq_eqVlt subn_eq0 (ltnW niw).
Qed.

Lemma Pareto_optimal_XP : Pareto_optimal p (true_value_strategy p).
Proof.
rewrite /Pareto_optimal /action_on => s' i.  
set U := (X in X < _); set U' := (X in _ < X) => ltUU'. 
move: (ltUU').
have -> // : 0 < U' -> U' = U; last by rewrite (@leq_ltn_trans U). 
  rewrite /U /U' /mech.U /prefs.U /= /auction.U /= !tnth_map /= !tnth_ord_tuple => lt0U'.
  case: ifP => [/eqP iw'|niw']; last by move: lt0U'; rewrite niw'. 
  case: ifP => [/eqP iw //|niw].
  apply/eqP; rewrite subn_eq0 /price.
  move: niw.
  rewrite /is_winner /actions tnth_map tnth_ord_tuple leqNgt => /negbFE.
  exact: ltnW.
by rewrite ltnn. 
Qed.

End Properties.

(* Print Assumptions truthful_XP. *)
(* Check truthful_XP. *)
