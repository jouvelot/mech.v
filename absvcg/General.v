(**

  General.v

  A formalization project for the Abstract Vickrey‑Clarke‑Groves auction mechanism, 
  targeting:

  - a specification of the "General VCG" algorithm (here, an abstract version that manages
    multiple optimal outcomes);

  - a proof of its key properties:
    . no positive transfer,
    . agent rationality,
    . and truthfulness;

  Authors: Zhan Jing (+++), Pierre Jouvelot(+), Lucas Sguerra, Emilio Gallego Arias(++).

  Date: August, 2025.

  (+) Mines Paris, PSL University, France
  (++) IRIF, France
  (+++) Jiao Tong U., Shanghai

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

(** Agents **)

Variable (n'' : nat).

Definition n' := n''.+1.
Definition n := n'.+1.

Notation A := (@agent.type n).

(** General VCG and key properties. *)

Module VCG.

Section Algorithm.

Variable (O : finType) (o0 : O).

Definition OStar_choice : Type := forall (s : {set O}) (_ : s != set0), {o : O | o \in s}. 

Variable (i : A).

Definition bidding := {ffun O -> nat}.
Definition biddings := n.-tuple bidding.

Variable (bs : biddings).
Local Notation "'bidding_ j" := (tnth bs j) (at level 10).

Implicit Types (o : O) (bs : biddings).

Definition bidSum o := \sum_(j < n) 'bidding_j o.
Definition bidSum_i o := \sum_(j < n | j != i) 'bidding_j o.

Definition oStars := arg_maxs xpredT bidSum.

Definition OStar := {o : O | o \in oStars}.

Variable oStar_choice : OStar_choice.

Definition arg_OStar_o := [arg max_(o > o0) (bidSum o)].

Lemma arg_OStar_in : arg_OStar_o \in oStars.
Proof.
rewrite inE andTb. 
apply/forallP => a.
by apply/implyP => _; rewrite -bigmax_eq_arg // leq_bigmax.
Qed.

Definition sig_OStar (o : O) (oin : o \in oStars): OStar.
by exists o.
Defined.

Definition arg_OStar := sig_OStar arg_OStar_in.

Lemma oStars_ne0 : oStars != set0.
Proof. apply/set0Pn; exists arg_OStar_o; exact: arg_OStar_in. Qed.

Definition oStar := oStar_choice oStars_ne0.

Definition welfare_with_i := bidSum_i (sval oStar).

Definition welfare_without_i := \max_o bidSum_i o.

Definition price := welfare_without_i - welfare_with_i.

Lemma bidSumD1 o : bidSum o = 'bidding_i o + bidSum_i o.
Proof. by rewrite /bidSum (bigD1 i). Qed.

Theorem no_positive_transfer : (* 0 <= price *)
 welfare_with_i <= welfare_without_i.
Proof. exact: leq_bigmax. Qed.

Theorem bid_rational : price <= tnth bs i (sval oStar).
Proof.
rewrite leq_subLR addnC -bidSumD1.
move: (proj2_sig oStar) => oin /=.
rewrite -(bigmax_eq_args oin) //.
apply: max_monotonic => o.
by rewrite (bidSumD1 o) leq_addl.
Qed.

Variable (value : bidding).

Hypothesis value_is_bid : 'bidding_i = value.

Theorem rational : price <= value (sval oStar).
Proof. by rewrite -value_is_bid bid_rational. Qed.

Section BidSumProps.

Lemma bidSumE o : bidSum o = \sum_(b <- bs) b o.
Proof. exact/esym/big_tuple. Qed.

End BidSumProps.

End Algorithm.

Section Truthfulness.

Variable (O : finType) (o0 : O).

Variable oStar_choice : OStar_choice O.

Definition m : mech.type n := 
  mech.new (fun bs => (map_tuple 
                      (fun a => @price _ o0 a bs oStar_choice)
                      (agent.agents n),
                       sval (oStar o0 bs oStar_choice))).

Variable v : A -> bidding O.

Definition p : prefs.type m :=
  prefs.new v 
    (fun i (mo : mech.O m) => 
       let: (ps, oSc) := mo in 
       v i oSc - tnth ps i)
    v.

Theorem truthful_General : truthful p.
Proof.
move=> bs bs' i diff value_is_bid /=.
rewrite !tnth_map /price /welfare_without_i /welfare_with_i tnth_ord_tuple.
have eq_Sum_i : bidSum_i i bs =1 bidSum_i i bs'.
  move=> o; apply: eq_bigr => j neji. 
  by move: (diff j neji); rewrite /action_on => ->.
rewrite (@eq_bigr _ _ _ _ _ _ (bidSum_i i bs) (bidSum_i i bs')) //.
rewrite ?2!subnBA ?leq_sub2r //; 
  [|by rewrite eq_Sum_i; apply: bigmax_sup|by apply: bigmax_sup].
rewrite /action_on /prefs.v /= in value_is_bid.
rewrite -value_is_bid -eq_Sum_i/= /oStar -!bidSumD1.   
move: (proj2_sig (oStar_choice (oStars_ne0 o0 bs))).  
set oc' := (sval (oStar_choice (oStars_ne0 o0 bs'))). 
by rewrite !inE andTb => /forallP/(_ oc')/implyP/(_ erefl). 
Qed.

End Truthfulness.

Section Indifference2.

(**
Each truthful agent is indifferent among the outcomes induced by the 
VCG mechanism.
*)

Variable (O : finType) (o0 : O).

Variable oStar_choice1 oStar_choice2 : OStar_choice O.

Variable (bs : biddings O).

Definition outcomes oStar_choice' :=  m o0 oStar_choice' bs.

Definition outcome1 := outcomes oStar_choice1.
Definition outcome2 := outcomes oStar_choice2.

Variable (v : A -> bidding O).

Variable (i : A).

Hypothesis truthful_bid : v i = tnth bs i.

Definition oStar1 := sval (oStar o0 bs oStar_choice1).
Definition oStar2 := sval (oStar o0 bs oStar_choice2).

Definition u := fun outcome => 
  let: (ps, oSc) := outcome in v i oSc - tnth ps i.

Lemma truthful_breaking_indifferent2 : u outcome1 = u outcome2.
Proof.
rewrite /= !tnth_map /price /welfare_with_i /welfare_without_i 
  tnth_ord_tuple.
rewrite !subnCBA ?leq_bigmax //.
rewrite truthful_bid addnC -bidSumD1 addnC -bidSumD1.
rewrite -(@bigmax_eq_args _ xpredT (bidSum bs) oStar1).
rewrite -(@bigmax_eq_args _ xpredT (bidSum bs) oStar2) //.
all: apply: valP.
Qed.

End Indifference2.

Check truthful_breaking_indifferent2.

(* Alternative formulation, and useful properties *)

Section Alternative.

Variable (O : finType) (i : A).
Variable (o0 : O).

Variable (bs : biddings O).
Variable (op : O) (oStar_choice : OStar_choice O).

Notation "'set_o* bs" := (@oStars O bs) (at level 10).
Notation "'bidding_ j" := (tnth bs j) (at level 10).
Notation "'o* bs" := (@oStar O bs oStar_choice) (at level 10).

Definition bs'' : biddings _ :=
  [tuple [ffun o : O => (if j != i then 'bidding_j o else 0)]| j < n].

Notation "'bidding''_ j" := (tnth bs'' j) (at level 10).

Definition bidSum'' o := \sum_(j < n) 'bidding''_j o.

Definition welfare_without_i'' := \max_o bidSum'' o.

Definition price'' := welfare_without_i'' - welfare_with_i o0 i bs oStar_choice.

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

Lemma eq_price'' : price o0 i bs oStar_choice = price''.
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

Lemma perm_oStars : oStars bs = oStars bs'.
Proof.
congr arg_maxs.
apply: functional_extensionality => o.
exact: perm_bidSum.
Qed.

Variable (oStar_choice : OStar_choice O).

Hypothesis eq_oStar : 
  sval (oStar o0 bs oStar_choice) = sval (oStar o0 bs' oStar_choice).

Lemma relabelled_price : price o0 i' bs' oStar_choice = price o0 i bs oStar_choice.
Proof.
congr (_ - _); last by rewrite /welfare_with_i eq_oStar // perm_bidSum_i.
apply/eqP; rewrite eqn_leq /welfare_without_i.
apply/andP. 
rewrite (@eq_bigr _ _ _ _ _ _ (bidSum_i i bs) (bidSum_i i' bs')) // => o _. 
by rewrite perm_bidSum_i.
Qed.

End Perm.

End VCG.

