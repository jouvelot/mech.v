(* Cut and paste from other files *)
From mathcomp Require Import all_ssreflect.

(** Notes from the meeting:

  - Equivalence of mechanisms goes a bit beyond equivalence
    of outputs, in a sense the way the things work are
    similar to imperative programming
  - Output of the utility vs the price.
 *)

Module MiniVCG.

(* Type of agents. *)
Variable (A : finType).

(* Slots *)
Variable (k : nat).

(* Ctrs *)
Variable ctrs : {ffun 'I_k -> nat}.

(* Ranking *)
Definition O := {ffun A -> option 'I_k}.
Variable (o0 : O).

(* Valuations (per-click) *)
Variable (v : {ffun A -> nat}).

(* Price array *)
Definition P := {ffun A -> nat}.

(* Ranking of i in the sorted bids *)
Definition r (o : O) (i : A) : option 'I_k.
Admitted.

(* Ctrs for a particular ranking *)
Definition c (o : O) (i : A) : nat :=
match r o i with
| None => 0
| Some idx => ctrs idx
end.

Definition c_prev (o : O) (i : A) : nat.
Admitted.

Definition idx (o : O) (i : A) : nat :=
  match r o i with
  | None => k
  | Some idx => idx
  end.

(* General VCG (for Search) *)
Module G.

(* Bids (total valuation including the ctr multiplier) *)
Definition B := {ffun A -> {ffun O -> nat}}.

Definition oStar (b : B) := [arg max_(o > o0) \sum_i b i o].

Definition price (b : B) (i : A) :=
  \max_o \sum_(j | i != j) b j o -
  \sum_(j | i != j) b j (oStar b).

Definition prices (b : B) : P :=
  [ffun i => price b i]. 

End G.

Module S.

Definition B := {ffun A -> nat}.

(* TODO: Outcome generated by sorting. *)
Definition oStar (b : B): O. Admitted.

(* *)
Definition price (b : B) (i : A) := 
  let o := oStar b in
  \sum_(j < k | idx o i < j)
      b i * (c_prev o i - c o i).
  
Definition prices (b : B) : P :=
  [ffun i => price b i]. 

End S.

(* Relation on the inputs. *)
Definition R_a (b_l : G.B) (b_r : S.B) : Prop :=
  forall i o, b_l i o = c o i * b_r i.

(* We need to remember how prices are computed. *)
Definition R_o
  (o_l : O) (p_l : P) (o_r : O) (p_r : P) :=
  forall i,
    v i * c o_l i - p_l i =
    v i * c o_r i - p_r i 
  .

Lemma base (b_l : G.B) (b_r : S.B) (h_i : R_a b_l b_r) :
  R_o (G.oStar b_l) (G.prices b_l)
      (S.oStar b_r) (S.prices b_r).
Proof.
move=> i; rewrite /G.prices /G.price /S.prices /S.price.
rewrite !ffunE.
set go := G.oStar _.
set so := S.oStar _.
set gc := c _ _.
set sc := c _ _.
rewrite /= in go so gc sc *.

Admitted.

End MiniVCG.