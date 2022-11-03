(**

  mech.v

  A Mechanism definition framework, for "pure" (i.e., "deterministic") strategies.

  Extensions could include agent-specific actions [A_i], interdependent true values,
  the implementation problem and non-deterministism.

  References:
  - [0] N. Nisan, T. Roughgarden, E. Tardos, & V. Vazirani (Eds.), Algorithmic 
        Game Theory (pp. 3-26). Cambridge: Cambridge University Press.
  - [1] Tardos, E., and Vazirani, V. (2007). Basic Solution Concepts and 
        Computational Issues. In [0] (pp. 3-26).
  - [2] www.cril.univ-artois.fr/~konieczny/enseignement/TheorieDesJeux.pdf
  - [3] Nisan, N. (2007). Introduction to Mechanism Design (for Computer Scientists). 
        In [0] (pp. 209-242).
  - [4] www.soas.ac.uk/cedep-demos/000_P570_IEEP_K3736-Demo/unit1/page_26.htm
  - [5] A good overview paper for more theorems to include: 
        https://www.nobelprize.org/uploads/2018/06/advanced-economicsciences2007.pdf

  Authors: Emilio J. Gallego Arias (++), Pierre Jouvelot (+).

  Date: November, 2021.

  (+) Mines Paris, PSL University, France
  (++) Inria, France

  Licence: CeCILL-B.

*)

From mathcomp Require Import all_ssreflect all_algebra all_fingroup.

Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Decidable.

From mech Require Import lib labelling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Agent. *)

Module agent.

Section Agent.

Variable n : nat.     (* number of agents in the mechanism *)

Definition type := 'I_n.

Definition pred := @ord_pred n.
Definition succ (n : nat) := @ord_succ n.
Definition last (n : nat) : 'I_n.+1 := ord_max.

Definition agents : n.-tuple type := ord_tuple n.

End Agent.

End agent.

(** Mechanism, for a given domain [A] of actions, also called "messages", of [n] agents *) 

Module mech.

Section Mech.

Record type {A : Type} (n : nat) := 
    new {
        O : Type;            (* domain of outcomes *)
        M : n.-tuple A -> O;  (* social outcome for the agents' actions *)
      }.
 
End Mech.

End mech.

Coercion mech.M : mech.type >-> Funclass.

(** Maps of agents' preferences, also called "profiles", for a given mechanism [m]. *)

Module prefs.

Section Prefs.

Variable (A : Type) (n : nat).

Definition mech : Type := @mech.type A n.

Notation agent := (agent.type n).
Notation strategy := (agent -> A).

Record type (m : mech) :=
  new {
      v : strategy;               (* "true value" strategy, mapping each agent private true 
                                     value, or "type", to an action/message *)
      U : agent -> mech.O m -> nat;   (* utility *)
      s : strategy                (* strategy used in [m] *)
    }. 

End Prefs.

End prefs.

(** Strategy, dominance, Nash equilibrium and Pareto properties. *)

Section Strategy.

Variable (A : eqType) (n : nat).

Variable (m : @mech.type A n).
Variable (p : @prefs.type A n m).

Definition U := prefs.U p.

Definition true_value_strategy := prefs.v p.

Notation agent := (agent.type n).
Notation strategy := (agent -> A).

Definition actions (s : strategy) := [tuple s j | j < n].
Definition set_in_actions (s s' : strategy) i :=
  [tuple if j == i then s' j else s j | j < n].

Section Dominance. (* See [1] *)

Definition dominates (g : rel nat) (s s' : strategy) (i : agent) :=
  g (U i (m (set_in_actions s' s i))) (U i (m (actions s'))).

Variable (s : strategy).

Definition weakly_dominant := forall i s', dominates geq s s' i.
Definition strictly_dominant := forall i s', ~ (s =1 s') -> dominates gtn s s' i.

Lemma dominant_strict_is_weak : strictly_dominant -> weakly_dominant.
Proof.
move=> d i s'. 
move: (d i s').  
have [eqss' _|/eqfunP ness' /(_ ness')] := boolP ([forall i, s i == s' i]); last by exact: ltnW.
rewrite /dominates /= eq_leq //.
congr (U _ (_ _)).
apply: eq_from_tnth => j.
rewrite !tnth_map tnth_ord_tuple.
move: eqss' => /forallP /(_ j) /eqP ->.
by rewrite if_same.
Qed.

End Dominance.

Section Nash. (* See [1] *)

Definition Nash_equilibrium (s : strategy) :=
  forall (i : agent) (s' : strategy),
    U i (m (actions s)) >= U i (m (set_in_actions s s' i)).

Variable s : strategy.

Lemma dominant_is_Nash : weakly_dominant s -> Nash_equilibrium s.
Proof.
move=> d i s' /=.  
move: (d i (fun j => if j == i then s' j else s j)).
have [eqss'|_ ltuu'] := boolP ([forall i, s i == s' i]).
- rewrite eq_leq //; congr (U i (m _)).
  apply: eq_from_tnth => j.
  rewrite !tnth_map !tnth_ord_tuple.
  move: eqss' => /forallP /(_ j) /eqP ->.
  by rewrite if_same.
- apply: (leq_trans ltuu').
  rewrite eq_leq //; congr (U i (m _)).
  apply: eq_from_tnth => j.
  rewrite !tnth_mktuple.
  by case: (j == i).
Qed.

Lemma Nash_uniq : strictly_dominant s -> forall s', Nash_equilibrium s' -> s' =1 s.
Proof.
rewrite /strictly_dominant /dominates /Nash_equilibrium /= => d s' N i.
move: (d i s'). 
have [/eqfunP -> //|/eqfunP ness' /(_ ness')] := boolP ([forall i, s i == s' i]).
by rewrite ltnNge N.
Qed.

(* Another version of Nash_uniq. *)

Notation finstrategy := {ffun agent -> A}.

Variant Nash_equilibrium_spec : finstrategy -> Type :=
  NashEquilibriumSpec (s : finstrategy) of Nash_equilibrium s : Nash_equilibrium_spec s.

Definition fins := [ffun i : agent => s i].

Lemma fins_Nash_equilibrium_spec : Nash_equilibrium s -> Nash_equilibrium_spec fins.
Proof.
move=> NE. 
have/NashEquilibriumSpec //: Nash_equilibrium fins.
  move=> i s'.
  rewrite /actions /set_in_actions. 
  have -> : [tuple fins j | j < n] = [tuple s j | j < n].
    apply: eq_from_tnth => j.
    by rewrite !tnth_mktuple ffunE.
  have -> : [tuple if j == i then s' j else fins j  | j < n] =
           [tuple if j == i then s' j else s j  | j < n].
    apply: eq_from_tnth => j.
    by rewrite !tnth_mktuple ffunE.
  exact: NE.
Qed.  

Lemma Nash_singleton : strictly_dominant s -> singleton Nash_equilibrium_spec.
Proof.
move=> d _ _ [s1 NE1] [s2 NE2].
apply/ffunP => i.
move: (d i s1). 
have [/forallP/(_ i)/eqP <-|/eqfunP ness1 /(_ ness1)] := boolP ([forall i, s i == s1 i]);
  last by rewrite /dominates /= ltnNge NE1. 
move: (d i s2).
have [/forallP/(_ i)/eqP <- //|/eqfunP ness2 /(_ ness2)] := boolP ([forall i, s i == s2 i]).
by rewrite /dominates /= ltnNge NE2. 
Qed.

(* Multiple equilibria. See [2]. *)

Definition Nash_equiv (s' : strategy) :=
  Nash_equilibrium s /\ Nash_equilibrium s' ->
  forall i, U i (m (actions s)) = U i (m (actions s')).

Definition Nash_exchangeable (s' : strategy) :=
  Nash_equilibrium s /\ Nash_equilibrium s' ->
  (forall i, Nash_equilibrium (fun j => if j == i then s j else s' j) /\
        Nash_equilibrium (fun j => if j == i then s' j else s j)).

End Nash.

Section Pareto.

Variable (s : strategy).

Definition Pareto_optimal :=  (* See [4] *)
  forall (s' : strategy) (i: agent), 
    let aa := actions s in
    let a'a := set_in_actions s s' i in
    U i (m a'a) > U i (m aa) -> (exists i', U i' (m a'a) < U i' (m aa)).

(* See [2] *)

Variable (s' : strategy).

Definition Pareto_strictly_dominates :=
  (forall i, U i (m (actions s')) < U i (m (actions s))).

Definition Pareto_dominates :=
  (forall i, U i (m (actions s')) <= U i (m (actions s))) /\
  (exists i, U i (m (actions s')) < U i (m (actions s))).

Lemma Pareto_weaken_strict :
  0 < n -> Pareto_strictly_dominates -> Pareto_dominates.
Proof.
move=> lt0n ps.
split => [i|]; first by exact: ltnW.
exists (Ordinal lt0n).
exact: ps.
Qed.

End Pareto.

End Strategy.

(** Truthfulness (i.e., "incentive-compatible") Prop and bool definitions and properties. *)

Section Truthfulness. (* for arbitrary action types *)

Variable (n : nat) (A : Type).

Notation prefs := (@prefs.type A n).

Variable m : @mech.type A n.

Variable p : @prefs m.

Notation "'v_ i" := (prefs.v p i) (at level 10).
Notation "'U_ i" := (prefs.U p i) (at level 10).
Notation "'s_ i" := (prefs.s p i) (at level 10).

Notation bids := (n.-tuple A).

Definition action_on := tnth.

Definition differ_on (bs bs' : bids) i := 
  forall j, j != i -> action_on bs' j = action_on bs j.

Definition truthful' (bs bs' : bids) i :=
  differ_on bs bs' i -> action_on bs i = 'v_i -> 'U_i (m bs') <= 'U_i (m bs).

Definition truthful := forall bs bs' i, truthful' bs bs' i.

Section CounterExample.

Definition counter_example bs bs' i := 
  differ_on bs bs' i /\ action_on bs i = 'v_i /\ 'U_i (m bs) < 'U_i (m bs').

Lemma not_truthful : 
  (exists i bs bs', counter_example bs bs' i) -> ~ truthful.
Proof.
move=> [i] [bs] [bs'] [d [a /= ltuu']].
apply: ex_not_not_all; exists bs.
apply: ex_not_not_all; exists bs'.
apply: ex_not_not_all; exists i.
move: ltuu'.
apply: contraPnot => /(_ d a) /=.
rewrite leqNgt.
by apply: contraNnot.
Qed. 

Lemma not_truthful_inv
      (decbs : forall bs, decidable (exists y z, ~ truthful' bs y z))
      (decbsbs' : forall bs bs', decidable (exists z, ~ truthful' bs bs' z)) :
  ~ truthful -> exists i bs bs', counter_example bs bs' i.
Proof.
have cl3 : forall T T' T'' (P : T -> T' -> T'' -> Prop)
             (dec1 : forall x, decidable (exists y z, ~ P x y z))
             (dec2 : forall x y, decidable (exists z, ~ P x y z)),
      (~ forall x y z, P x y z) -> exists x y z, ~ P x y z.
  move=> T T' T'' P dec1 dec2 na.
  apply: not_all_not_ex. 
  move: (@not_all_ex_not _ _ na) => [x] nx /(_ x).
  apply/(not_not_iff (exists y z, ~ P x y z)) => //.
  apply: not_all_not_ex.
  move: (@not_all_ex_not _ _ nx) => [y] ny /(_ y).
  apply/(not_not_iff (exists z, ~ P x y z)) => //.
  apply: not_all_not_ex.
  by move: (@not_all_ex_not _ _ ny) => [z] nz /(_ z) /NNPP.
move/(@cl3 _ _ _ _ decbs decbsbs') => /constructive_indefinite_description [xbs].
move=> /constructive_indefinite_description [xbs'].
move=> /constructive_indefinite_description [xi].   
move/(@imply_to_and (differ_on xbs xbs' xi)) => [diff].
move/(@imply_to_and (action_on xbs xi = 'v_xi)) => [tv] /=.
exists xi. exists xbs. exists xbs'.
split => //. split => //=.
by rewrite ltnNge (@contra_notN (('U_xi (mech.M m xbs')) <= ('U_xi (mech.M m xbs)))).
Qed.

End CounterExample.
 
End Truthfulness.

Section Truthfulnessb. (* for finite action types -- no decidability issues *)

Variable (n : nat) (A : finType).

Notation agent := (agent.type n).
Notation prefs := (@prefs.type A n).

Variable m : @mech.type A n.

Variable p : @prefs m.

Notation "'v_ i" := (prefs.v p i) (at level 10).
Notation "'U_ i" := (prefs.U p i) (at level 10).

Notation bids := (n.-tuple A).

Definition differ_onb (bs bs' : bids) i := 
  [forall j, (j != i) ==> (action_on bs' j == action_on bs j)].

Lemma equiv_diff bs bs' i: differ_onb bs bs' i <-> differ_on bs bs' i. 
Proof.
split => [d j neji|d]; first by apply/eqP; move/forallP/(_ j)/implyP/(_ neji): d.
apply/forallP => j.
apply/implyP => neji.
apply/eqP.
exact: d.
Qed.

Definition truthfulb' bs bs' i := 
  differ_onb bs bs' i ==> (action_on bs i == 'v_i) ==> ('U_i (m bs') <= 'U_i (m bs)).

Definition truthfulb := [forall bs, forall bs', forall i, truthfulb' bs bs' i].

Lemma truthfulP : reflect (truthful p) truthfulb.
Proof.
apply: forallPP => bs.
apply: forallPP => bs'.
apply: forallPP => i. 
apply: introP => [imp d a|].
- have ab : action_on bs i == 'v_ i by apply/eqP.
  by move/implyP/(_ (iffRL (equiv_diff bs bs' i) d))/implyP/(_ ab): imp.
- apply: contraNnot => imp.
  apply/implyP => db.
  apply/implyP => ab.
  apply: imp; first by exact: (iffLR (equiv_diff bs bs' i) db).
  exact: eqP.
Qed.

Section CounterExample.

Definition counter_exampleb bs bs' i := ~~ truthfulb' bs bs' i.

Lemma is_counter_exampleb bs bs' i :
  counter_exampleb bs bs' i= (differ_onb bs bs' i &&
                              (action_on bs i == 'v_i) &&
                              ('U_i (m bs) < 'U_i (m bs'))).
Proof. by rewrite /counter_exampleb !negb_imply ltnNge andbA. Qed.

Lemma not_truthfulb :
  ~~ truthfulb <-> exists i, exists bs, exists bs', counter_exampleb bs bs' i.
Proof.
split. 
- move/forallPn/sigW => [xbs] /forallPn /sigW [xbs'] /forallPn /sigW [xi] ntP.
  exists xi. exists xbs. exists xbs'.
  rewrite is_counter_exampleb /=.
  rewrite /truthfulb' in ntP.
  by move: ntP; rewrite ltnNge !negb_imply => /andP [-> /andP [-> ->]].
- move=> [xi] [xbs] [xbs']. 
  rewrite is_counter_exampleb => /andP [/andP [d a]] ub.
  apply/truthfulP/not_truthful.
  exists xi. exists xbs. exists xbs'.
  split; first by exact: (iffLR (equiv_diff xbs xbs' xi) d).
  by split; first by apply/eqP.
Qed.

Lemma not_truthful_invb :
  ~ truthful p -> exists i, exists bs, exists bs', counter_example p bs bs' i.
Proof.
move=> /truthfulP /not_truthfulb [i] [bs] [bs'].
rewrite /counter_exampleb !negb_imply => /and3P [d /eqP a u].
exists i. exists bs. exists bs'.
rewrite /counter_example a ltnNge u /differ_on. 
split => [j neji|]; last by split.
by move: d => /forallP /(_ j) /implyP /(_ neji) /eqP.
Qed.

End CounterExample.

End Truthfulnessb.

(** Class [truthfulMech] of truthful mechanisms, as a subclass of [mech]. *) 

Module truthfulMech.

Section TruthfulMech.

Variable (A : Type) (n : nat).

Record type := 
    new {
        b :> @mech.type A n;             (* base mechanism *)
        p : prefs.type b;                (* preferences *)
        _ : truthful p                   (* truthful prop *)
      }.

End TruthfulMech.

Section Properties.

Variable (A : eqType) (n : nat).

Variable m : @truthfulMech.type A n.

Notation agent := (agent.type n).
Notation prefs := (@prefs.type A n).

Notation p := (p m).

Notation "'v_ i" := (prefs.v p i) (at level 10).

Notation bids := (n.-tuple A).

Notation weakly_dominates := (dominates p geq).

Local Lemma eq_bsbs'_bs (bs bs' : bids) (i : agent) (d : differ_on bs bs' i) : 
  [tuple if j == i then action_on bs j else action_on bs' j  | j < n] = bs.
Proof.
apply: eq_from_tnth => j.
rewrite tnth_map tnth_ord_tuple.
case eqji: (j == i) => //. 
exact: (d j (negbT _)).  
Qed.

Lemma truthful_iff_weakly_dominates_i i bs (tvi : action_on bs i = 'v_i)
      bs' (d : differ_on bs bs' i) :
  truthful' p bs bs' i <-> weakly_dominates (action_on bs) (action_on bs') i.
Proof.
rewrite /dominates /truthful' /actions /set_in_actions /prefs.U /=.  
rewrite /differ_on /action_on in d tvi *.
rewrite tuple_of_tnth eq_bsbs'_bs //.
split => //.
by move=> ->.
Qed.

Local Lemma truthful_iff_weakly_dominant_i i bs (tvi : action_on bs i = 'v_i) :
  (forall bs', truthful' p bs bs' i) <-> 
  (forall bs', differ_on bs bs' i -> weakly_dominates (action_on bs) (action_on bs') i).
Proof.
split => [/(_ _)/(truthful_iff_weakly_dominates_i tvi) //|dom bs' d _].
apply/(iffRL (truthful_iff_weakly_dominates_i tvi d)) => //. 
exact: dom.
Qed.

Lemma truthful_iff_weakly_dominant :
  truthful p <-> weakly_dominant p (true_value_strategy p).
Proof.
rewrite /truthful /truthful' /differ_on /action_on /weakly_dominant /dominates.
split=> [t i s' /=|/= d bs bs' i diff tv].
- apply: t => [j nejij|]; last by rewrite tnth_mktuple eq_refl.
  by rewrite !tnth_mktuple ifF // (@negbTE (j == i)).
- move: (d i (tnth bs')). 
  rewrite /actions /set_action tuple_of_tnth => ltuu.
  rewrite (leq_trans ltuu) // eq_leq //; congr (U _ _ (m _)). 
  apply: eq_from_tnth => j.
  rewrite tnth_map tnth_ord_tuple.
  have [/eqP ->|/diff //] := boolP (j == i).
  by rewrite tv.
Qed.

Lemma Nash_truthful: Nash_equilibrium p (true_value_strategy p).
Proof. by apply/dominant_is_Nash/(iffLR truthful_iff_weakly_dominant); case: m. Qed.

End Properties.

End truthfulMech.

Coercion truthfulMech.b : truthfulMech.type >-> mech.type.

(** Invariance of mechanisms over agent permutations and sorting. *)

Section Perm.

Variable (n : nat) (A : eqType).

Variable m : @mech.type A n.

Notation O := (mech.O m).

Variable p : prefs.type m.

Notation v := (prefs.v p).
Notation U := (prefs.U p).

Import GroupScope.

Definition ptuple Pi (bs : n.-tuple A) := [tuple tnth bs (Pi i)| i < n].

Variable M_perm_ind : forall Pi bs, m (ptuple Pi bs) = m bs.

Variable (bs bs' : n.-tuple A).

Variable (s : (@agent.type n -> A)).

Variable Pi : {perm 'I_n}.

Let Pm := @mech.new A n O (m \o (ptuple Pi)).  
Let Pp := @prefs.new A n Pm (v \o Pi) (U \o Pi) s.

Lemma truthful_permP i:
  truthful' Pp (ptuple Pi bs) (ptuple Pi bs') (Pi^-1 i) <-> truthful' p bs bs' i.
Proof.
split; move=> H d_i a_t /=.
- rewrite /truthful' in H. 
  have dinv: differ_on (ptuple Pi bs) (ptuple Pi bs') (Pi^-1 i).
    rewrite /differ_on in d_i * => j neji.
    have/(d_i (Pi j)): Pi j != i.
      move: neji.
      apply: contra_neq => <-.
      by rewrite permK.
    by rewrite /action_on /ptuple !tnth_map !tnth_ord_tuple.
  have tvinv: action_on (ptuple Pi bs) (Pi^-1 i) = (v \o Pi) (Pi^-1 i).
    move: a_t.
    by rewrite /action_on /ptuple !tnth_map !tnth_ord_tuple /= permKV.
  move: (H dinv tvinv) => /=.
  by rewrite permKV !M_perm_ind.
- rewrite permKV !M_perm_ind.
  apply: H.
  - rewrite /differ_on /action_on in d_i * => j neji.
    have/(d_i (Pi^-1 j)): Pi^-1 j != Pi^-1 i.
      move: neji.
      by apply: contra_neq => /perm_inj ->.
    by rewrite /ptuple !tnth_map !tnth_ord_tuple permKV.
  - rewrite /action_on /ptuple in a_t *.
    move: a_t.
    rewrite !tnth_map !tnth_ord_tuple permKV => -> /=.
    by rewrite permKV.
Qed.

End Perm.

Section Sorted.

Variable (n : nat) (A : eqType).

Variable m : @mech.type A n.

Notation O := (mech.O m).

Variable p : prefs.type m.

Notation v := (prefs.v p).
Notation U := (prefs.U p).

Variable M_perm_ind : forall Pi bs,  m (ptuple Pi bs) = m bs.

Variable (bs bs' : n.-tuple A) (i : 'I_n).

Variable (s : @agent.type n -> A).

Variable leq_act : rel A.

Definition idx := idxa leq_act bs i.

Let sorting_fun := tnth (tlabel leq_act bs).

Lemma sorting_inj: injective sorting_fun.
Proof. apply: labelling_inj. exact: tlabelP. Qed.

Let Pi := perm sorting_inj.

Import GroupScope.

Definition Pm := @mech.new A n O (m \o (ptuple Pi)).  
Definition Pp := @prefs.new A n Pm (v \o Pi) (U \o Pi) s.

Lemma truthful_sorted :
  truthful' Pp (tsort leq_act bs) (ptuple Pi bs') idx -> truthful' p bs bs' i.
Proof.  
have -> : idx = Pi^-1 i.
  have: injective Pi by exact: perm_inj.
  apply.
  by rewrite permKV permE /sorting_fun cancel_idxa.
have -> : tsort leq_act bs = ptuple Pi bs; last by rewrite truthful_permP.
  apply: eq_from_tnth => j. 
  rewrite tnth_map tnth_ord_tuple permE /sorting_fun. 
  move: (labellingP leq_act bs) => /forallP /(_ j) /eqP ->. 
  congr (tnth _ (tnth _ _)); last exact: uniq_labelling.
Qed.

End Sorted.

(** Relational mapping between mechanisms. *)

Section Relational.

Variable (n : nat ) (A1 A2 : Type).

Notation agent := (agent.type n).

Variable (m1 : @mech.type A1 n) (m2 : @mech.type A2 n).

Notation O1 := (mech.O m1).
Notation O2 := (mech.O m2).

(* Relation between inputs. *)

Variable Ra : agent -> A1 -> A2 -> Prop.

Definition Ri (i1 : n.-tuple A1) (i2 : n.-tuple A2) : Prop :=
  forall i, Ra i (action_on i1 i) (action_on i2 i).

(* Special case when the input for M1 can be produced from the input for M2. *)

Variable fR : agent -> A2 -> A1.

Definition fRi (bs2 : n.-tuple A2) := [tuple fR i (tnth bs2 i) | i < n].

Variable p1 : prefs.type m1.
Variable p2 : prefs.type m2.

Notation v1 := (@prefs.v _ n m1 p1).
Notation v2 := (@prefs.v _ n m2 p2).

Hypothesis fRP : forall i a2, Ra i (fR i a2) a2.
Hypothesis fRvP : forall i, fR i (v2 i) = v1 i.

Lemma fRiP bs2:  Ri (fRi bs2) bs2.
Proof. by rewrite /fRi /Ri => i; rewrite /action_on !tnth_map !tnth_ord_tuple. Qed.

Lemma fRdP bs2 bs2' i (hd : differ_on bs2 bs2' i) :
  differ_on (fRi bs2) (fRi bs2') i.
Proof.
move=> j /hd ha; rewrite /action_on in ha.
by rewrite /fRi /action_on !tnth_map !tnth_ord_tuple ha.
Qed.

Lemma fRviP cs i (ha : action_on cs i = v2 i) : action_on (fRi cs) i = v1 i.
Proof. by rewrite /action_on /fRi !tnth_map !tnth_ord_tuple in ha *; rewrite ha fRvP. Qed.

(* There are two lemmas to prove to use the relational framework:

   - refinement: M1 M2 send related inputs to related outputs;
   - compatibility of Ro with utility: if outcomes are related, utilities
      are related (here, with equality).  *)

Variable Ro : O1 -> O2 -> Prop.

Variable MR : forall bs1 bs2 (ri : Ri bs1 bs2), Ro (m1 bs1) (m2 bs2).

Notation U1 := (@prefs.U A1 _ m1 p1).
Notation U2 := (@prefs.U A2 _ m2 p2).

Variable RelFP : forall o1 o2, Ro o1 o2 -> U1^~o1 =1 U2^~o2.

Lemma MP : truthful p1 -> truthful p2.
Proof.
move=> h1 bs2 bs2' i hd1 ht1 /=.
have ho := MR (fRiP bs2).
have ho' := MR (fRiP bs2').
have hu := RelFP ho.
have hu' := RelFP ho'.
rewrite -hu -hu'.
by apply/h1; [apply/fRdP|apply/fRviP].
Qed.

End Relational.

(** Direct revelation mechanism, as a [mech] instance. *)

Module directRevelation. (* See [3] *)

Section DirectRevelation.

Variable (n' : nat).

Definition n := n'.+1.

Definition players := agent.agents n.

Variable (V : {ffun 'I_n -> Type}).

Definition V0 : Type := V ord0.

Definition V1n : Type := foldl prod V0 (map V (behead players)).

Variable (A : Type).

Definition choice := V1n -> A.

Definition price := 'I_n -> V1n -> nat.

Variable (c : choice) (p : price).

Definition mech := mech.new (fun u : n.-tuple unit => (c, p)).

End DirectRevelation.

End directRevelation.

(** Auction, as a subclass of [mech]. *) 

Module auction.

Section Auction.

Variable (n m : nat).

Notation A := ('I_m).       (* Actions are bids, coded as ordinals, less than [m] *)
Notation agent := (@agent.type n).

Record type := 
    new {
        b :> @mech.type A n;              (* base mechanism *)
        p : mech.O b -> agent -> option nat   
                                  (* price to pay for the outcome, per (winning) agent *)
      }.

Variable (a : type) (v : agent -> A).

(* Default auction a utility, given a true value strategy v. *)

Definition U := fun i (o : mech.O a) => 
                  match p o i with
                  | Some p => v i - p
                  | _ => 0
                  end.

(* Default [prefs] for auction [a], given true value [v] (and [s] = [v]). *)

Definition prefs := prefs.new v U v.

(* Properties *)

(* This definition of [no_posiive_transfer] would ony make sense with [int] prices! *)

Definition no_positive_transfer := forall i (o : mech.O a), 0 <= p o i.

Theorem trivial_no_positive_transfer : no_positive_transfer.
Proof. by move=> i o. Qed.

Definition rational := forall i (o : mech.O a),
    match p o i with
    | Some p => p <= v i
    | _ => true
    end.

End Auction.

End auction.

Coercion auction.b : auction.type >-> mech.type.

