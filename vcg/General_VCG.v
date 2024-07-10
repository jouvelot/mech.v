(**

  General_VCG_mechanism.v

  A formalization project for the Vickrey‑Clarke‑Groves auction mechanism, 
  targeting:

  - a specification of the "General VCG" algorithm;

  - a proof of its key properties:
    . no positive transfer,
    . agent rationality,
    . and truthfulness;

  See Tim Roughtgarden lecture notes for more details.
  (http://timroughgarden.org/f16/l/l15.pdf)

  Authors: Pierre Jouvelot(+), Lucas Sguerra(+), Emilio J. Gallego Arias(++).

  Date: November, 2020.

  (+) MINES ParisTech, PSL University, France
  (++) Inria, France

  Thanks for their insights to the ssreflect community, and in particular:

   - Yves Bertot ([below_last_ord]),

  Licence: CeCILL-B.

*)

From Coq Require Import Init.Prelude Unicode.Utf8 Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mech.lib Require Import lib labelling mech.

Variable (n'' : nat).

Definition n' := n''.+1.
Definition n := n'.+1.

Notation A := (@agent.type n).

Definition differ_only_i A n i (bs bs' : n.-tuple A) :=
  forall j, j != i -> tnth bs' j = tnth bs j.

Module VCG.

(** General VCG and key properties. *)

Section Algorithm.

Variable (O : finType) (o0 : O) (i : A).

Definition bidding := {ffun O -> nat}.
Definition biddings := n.-tuple bidding.

Variable (bs : biddings).
Local Notation "'bidding_ j" := (tnth bs j) (at level 10).

Implicit Types (o : O) (bs : biddings).

Definition bidSum o := \sum_(j < n) 'bidding_j o.
Definition bidSum_i o := \sum_(j < n | j != i) 'bidding_j o.

Definition oStar := [arg max_(o > o0) (bidSum o)].

Definition welfare_with_i := bidSum_i oStar.

Definition welfare_without_i := \max_o bidSum_i o.

Definition price := welfare_without_i - welfare_with_i.

Lemma bidSumD1 o : bidSum o = 'bidding_i o + bidSum_i o.
Proof. by rewrite /bidSum (bigD1 i). Qed.

(** No positive transfer. *)

Theorem no_positive_transfer : (* 0 <= price *)
  welfare_with_i <= welfare_without_i.
Proof. exact: leq_bigmax. Qed.

(** Rationality. *)

Variable (value : bidding).

Hypothesis value_is_bid : 'bidding_i = value.

Theorem rational : price <= value oStar.
Proof.
rewrite -value_is_bid leq_subLR addnC -bidSumD1 -bigmax_eq_arg //.
apply: max_monotonic => o.
by rewrite (bidSumD1 o) leq_addl.
Qed.

Section BidSumProps.

Lemma bidSumE o : bidSum o = \sum_(b <- bs) b o.
Proof. exact/esym/big_tuple. Qed.

End BidSumProps.

End Algorithm.

(** Truthfulness. *)

Section Truthfulness.

Variable (O : finType) (o0 : O).

Definition m : mech.type n := 
  mech.new (fun bs => (map_tuple (price o0 ^~ bs) (agent.agents n), 
                    oStar o0 bs)).

Variable v : A -> bidding O.

Definition p : prefs.type m :=
  prefs.new v 
            (fun i (o : mech.O m) => let: (ps, oStar) := o in v i oStar - tnth ps i)
            v.

Lemma truthful_General_VCG : truthful p.
Proof.
move=> bs bs' i diff value_is_bid /=.
rewrite !tnth_map.
rewrite /price /welfare_without_i /welfare_with_i tnth_ord_tuple.
have eq_Sum_i : bidSum_i i bs =1 bidSum_i i bs'.
  move=> o; apply: eq_bigr => j neji. 
  move: (diff j neji).
  by rewrite /action_on => ->.
rewrite (@eq_bigr _ _ _ _ _ _ (bidSum_i i bs) (bidSum_i i bs')) //.
rewrite ?2!subnBA ?leq_sub2r //; last by exact: bigmax_sup.
rewrite /action_on /prefs.v /= in value_is_bid.  
rewrite -value_is_bid -eq_Sum_i.
rewrite -!bidSumD1 /(oStar o0 bs) -bigmax_eq_arg //.
exact: bigmax_sup.
by rewrite eq_Sum_i; apply: bigmax_sup.
Qed.

End Truthfulness.

(* Useful properties for the alternative formulation. *)

Section Alternative.

Variable (O : finType) (o0 : O) (i : A).

Variable (bs : biddings O).

Notation "'bidding_ j" := (tnth bs j) (at level 10).
Notation "'o* bs" := (@oStar O o0 bs) (at level 10).

(* Alternative definition for welfare_without_i (i=0). *)
Definition bs'' : biddings _ :=
  [tuple [ffun o : O => (if j != i then 'bidding_j o else 0)]| j < n].

Notation "'bidding''_ j" := (tnth bs'' j) (at level 10).

Definition bidSum'' o := \sum_(j < n) 'bidding''_j o.

Definition welfare_without_i'' := \max_o bidSum'' o.

Definition price'' := welfare_without_i'' - welfare_with_i o0 i bs.

Lemma eq_bidSum'' o : bidSum'' o = bidSum_i i bs o.
Proof.
rewrite /bidSum'' /bidSum_i.
rewrite (big_mkcond (fun j => j != i)) //=.
set F2 := (X in _ = \sum_(i0 < n) X i0).
rewrite (eq_bigr F2) => [//=|j _].
by rewrite tnth_mktuple ffunE /F2.
Qed.

Lemma eq_welfare'' : welfare_without_i i bs = welfare_without_i''.
Proof.
rewrite /welfare_without_i /welfare_without_i''.
rewrite (eq_bigr bidSum'') => [//=|o _].
by rewrite eq_bidSum''.
Qed.

Lemma eq_price'' : price o0 i bs = price''.
Proof. by rewrite /price'' -eq_welfare''. Qed.

End Alternative.

(** Invariance via permutations. *)

Section Perm.

Variable (O : finType) (o0 : O).

Variable (bs : biddings O).

Variable (bs' : biddings O) (permbsbs' : perm_eq bs' bs).

Variable (i i' : A) (relabi : tnth bs' i' = tnth bs i).

Lemma perm_bidSum o : bidSum bs o = bidSum bs' o.
Proof. by rewrite !bidSumE (perm_big bs') 1?perm_sym ?permbsbs'. Qed.

Lemma perm_bidSum_i o : bidSum_i i bs o = bidSum_i i' bs' o.
Proof.
rewrite /bidSum_i.
apply/eqP; rewrite -(eqn_add2l (tnth bs' i' o)) -bidSumD1; apply/eqP.
rewrite bidSumE (perm_big bs) ?permbsbs' //= relabi -bidSumE /bidSum.
by rewrite [\sum_(j < n) _](bigD1 i).
Qed.

Lemma eq_oStar : oStar o0 bs = oStar o0 bs'.
Proof.
congr arg_max. 
apply: functional_extensionality_dep => o.
exact: perm_bidSum.
Qed.

Lemma relabelled_price : @price O o0 i' bs' = @price O o0 i bs.
Proof.
congr (_ - _); last by rewrite /welfare_with_i eq_oStar // perm_bidSum_i.
rewrite /welfare_without_i. 
apply/eqP; rewrite eqn_leq. 
apply/andP. 
split; first by rewrite (bigmax_eq_arg o0) // -perm_bidSum_i leq_bigmax.
by rewrite (bigmax_eq_arg o0) // perm_bidSum_i leq_bigmax.
Qed.

End Perm.

End VCG.

Check VCG.truthful_General_VCG.
Print Assumptions VCG.truthful_General_VCG.
