From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RankDef.

Variable (n' : nat).
Let n := n'.+2.

Definition A := 'I_n.
Definition bids := 'I_n -> nat.
Definition vals := 'I_n -> nat.

Definition is_rank (b : bids) (rank : 'I_n -> 'I_n) (rval : 'I_n -> nat) :=
  (forall (i j : 'I_n), i <= j -> rval j <= rval i)
  /\ (forall i : 'I_n, rval (rank i) = b i).

Record ranking (b : bids):= {
    rank : 'I_n -> 'I_n;
    rval : 'I_n -> nat;
    _ : is_rank b rank rval
}.

Definition differ_on (b b' : bids) (i : A):=
  forall j, i != j -> b j = b' j.

Definition buildr (b : bids) : ranking b. Admitted.

Lemma rank_stable (b b' : bids) i (h_diff : differ_on b b' i) :
  let r := buildr b in
  let r' := buildr b' in
  forall (h_notmoved : rank r i = rank r' i) j (h_idx : rank r i != j),
     rval r j = rval r' j.
Proof.
Qed.

(** Note! This lemma needs verifying before use,
    likely the indexes are not yet correct. *)
Lemma rank_shift (b b' : bids)
  (r : ranking b)
  (r' : ranking b')
  i
  (h_diff : differ_on b b' i) 
  (h_rank : rank r i <= rank r' i)
  :
  (forall (j : 'I_n), (j < rank r i) || (rank r' i <= j) -> rval r j = rval r' j)
  /\ (forall (j : 'I_n), 
      (rank r i <= j < rank r i) -> rval r (inord j.+1) = rval r' j).
Proof.
Qed.
 
Lemma rval_def (b : bids) (r : ranking b) i : rval r (rank r i) = b i.
Proof. by case: r => ? ? [h1 h2] /=. Qed.

Lemma rval_leq (b b' : bids) (r : ranking b) (r' : ranking b')
   (i j : 'I_n) :
    i <= j -> rval r' j <= rval r i.
Proof.
Qed. 

Definition U_SP (v : vals) (b : bids) (i : 'I_n) :=
  let r := buildr b in 
  if rank r i == inord 0 then
    v i - rval r (inord 1)
  else
    0
.

Lemma SP_truthful
   (v : vals) (b b': bids) (i : 'I_n)
   (h_diff : differ_on b b' i) (h_truth : b i = v i) :
   U_SP v b i >= U_SP v b' i.
Proof.
rewrite /U_SP.
set r := buildr b.
set r' := buildr b'.
case: ifP => h_r2; case: ifP => h_r1.
- have h_idx: rank r i != inord 1.
    by rewrite (eqP h_r1) -(inj_eq val_inj) /= !inordK.
  have snd_eq : rval r (inord 1) = rval r' (inord 1).
    apply: (rank_stable h_diff _ h_idx) => //.
    by rewrite (eqP h_r1) (eqP h_r2).
  by rewrite snd_eq.
- have under_bid: v i <= rval r' (inord 1).
    rewrite -h_truth -(rval_def r).
    admit.
  by rewrite leq_subLR addn0.
- have under_bid : rval r (inord 1) <= v i.
    admit.
  by rewrite leq_subRL ?addn0.
- by [].
Qed.

End RankDef.


