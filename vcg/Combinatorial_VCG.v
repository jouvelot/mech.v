
(**
  
  Combinatorial_VCG.v

  A specification of the "Combinatorial VCGh" auction variant, and proof of truthfulness.

  See "Proving soundness of combinatorial Vickrey auctions and generating verified 
  executable code", Marco B. Caminati1, Manfred Kerber2, Christoph Lange2, and Colin Rowat.

  Authors: Pierre Jouvelot(+), Emilio Gallego Arias(++).

  Date: February, 2022.

  (+) MINES ParisTech, PSL University, France
  (++) Inria, France

  Licence: CeCILL-B.

*)

From mathcomp Require Import all_ssreflect.

From mech.lib Require Import mech.
From mech.vcg Require Import General_VCG.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Combinatorial VCG auction, as an instance of General VCG. *) 

Section CombinatorialAuction.

Notation agent := (@agent.type n).

Variable (T : finType) (endowment : {set T}).   (* Goods in seller's endowment *)

Variable (q : nat).

Notation A := {ffun {set T} -> 'I_q}.     (* Actions are bids for a subset of goods *)

Notation bundle := (n.-tuple {set T}).

Definition subpartition' (b : bundle) := \bigcup_(i < n) tnth b i \subset endowment.
Definition disjoint' (b : bundle) := [forall i1, forall i2, [disjoint (tnth b i1) & (tnth b i2)]].

Record O := 
  Outcome {
      b :> bundle;
      _ : subpartition' b && disjoint' b
    }.

Lemma disjoint (o : O) : forall i1 i2, [disjoint (tnth o i1) & (tnth o i2)].
Proof. 
by case: o => [? /= /andP [_ d]] i1 i2; move: d => /forallP /(_ i1) /forallP /(_ i2).
Qed.
Lemma subpartition (o : O) : \bigcup_(i < n) tnth o i \subset endowment.
Proof. by case: o => [? /= /andP [s _]]. Qed.

Canonical O_subType := Eval hnf in [subType for b].
Canonical O_eqType := Eval hnf in EqType _ [eqMixin     of O by <:].
Canonical O_choiceType := Eval hnf in ChoiceType _ [choiceMixin of O by <:].
Canonical O_countType := Eval hnf in CountType _ [countMixin  of O by <:].
Canonical O_subCountType := Eval hnf in [subCountType of O].
Canonical O_finType := Eval hnf in FinType _ [finMixin    of O by <:].
Canonical O_subFinType := Eval hnf in [subFinType of O].

Definition o0 : O.
pose b0 : bundle := [tuple set0 | i < n].
have pd0: subpartition' b0 && disjoint' b0.
  apply/andP; split; first by apply/bigcupsP => i _; rewrite tnth_mktuple sub0set. 
  apply/forallP => i1; apply/forallP => i2.
  by rewrite -setI_eq0 !tnth_mktuple setI0.
exact: Outcome pd0.
Defined.

Definition m := VCG.m o0.

Variable (v : n.-tuple A).

Definition bidding_of (acts : n.-tuple A) i := [ffun o : O => val (tnth acts i (tnth o i))].  

Definition value_bidding := bidding_of v.

Definition p := VCG.p o0 value_bidding.

(** Truthfulness. *)

Theorem truthful_Combinatorial_VCG : truthful p.
Proof. exact: VCG.truthful_General_VCG. Qed.

(** Rationality. *)

Section Rationality.

Variable (acts : n.-tuple A) (i : agent).

Definition biddings := map_tuple (bidding_of acts) (@agent.agents n).

Definition price := VCG.price o0 i biddings.      (* Combinatorial VCG price *)

Definition oStar := VCG.oStar o0 biddings.      (* Combinatorial VCG outcome *)

Lemma rational: tnth acts i = tnth v i -> price <= tnth v i (tnth oStar i).
Proof. 
move=> bidv. 
have biddingv: tnth biddings i = value_bidding i.
  rewrite tnth_map tnth_ord_tuple.
  apply/ffunP => o.
  by rewrite !ffunE /= bidv.
have := (VCG.rational o0 biddingv).
by rewrite ffunE.
Qed.

End Rationality.

End CombinatorialAuction.

(* Disabled until we get a flag in Coq to do so *)
(* Check truthful_Combinatorial_VCG. *)
(* Print Assumptions truthful_Combinatorial_VCG. *)
