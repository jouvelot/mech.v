(** 

  lib.v

  Auxiliary lemmas used in the VCG development.

  Licence: CeCILL-B.

*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import fingroup.perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Misc. *)

Section Misc.

Definition singleton (T : eqType) (P : T -> Type) := forall (x y : T), P x -> P y -> x = y. 

End Misc.

(** Arithmetic lemmas *)

Section Arith.

Lemma leq_transpose b1 b2 c1 c2
      (leb2b1 : b1 >= b2)
      (lec2c1 : c1 >= c2) :
  b1 * c2 + b2 * c1 <= b1 * c1 + b2 * c2.
Proof.
have f: (b1 - b2) * (c1 - c2) = b1 * c1 + b2 * c2 - (b1 * c2 + b2 * c1).
  rewrite mulnBr 2!mulnBl ?subnBA;
    last by rewrite leq_mul2r leb2b1 orbT.
  rewrite [X in _ = _ - X]addnC subnDA addnBAC //;
    last by rewrite leq_mul2r leb2b1 orbT.
- have [] := boolP (b2 == b1) => [/eqP -> |].
  by rewrite addnC.
- have [] := boolP (c2 == c1) => [/eqP -> //|].
  rewrite !neq_ltn.
  move/leq_gtF: lec2c1; move/leq_gtF: leb2b1 => -> ->.
  rewrite !orbF => ltc2c1 ltb2b1.
  apply: ltnW.
  by rewrite -subn_gt0 -f muln_gt0 2!subn_gt0 ltb2b1 ltc2c1.
Qed.

Lemma lenn1 j (lt0j : 0 < j) : j <= j.-1 = false.
Proof. by rewrite -[X in (X <= _) = _](prednK lt0j) ltnn. Qed.

Lemma sum_diff (y x z : nat) (leyz : z <= y) (leyx : y <= x) : 
  x - z = (y - z) + (x - y).
Proof.
rewrite addnBAC //. 
congr (_ - _).
by rewrite subnKC // ?leq_sub2l // (@leq_ltn_trans i) // ?leq_subr.
Qed.

Lemma swap_dist_subl x x' y y' v 
      (lexx' : x <= x') (leyy' : y <= y')
      (leyvx : y <= v * x) :
  v * (x' - x) <= y' - y  -> v * x' - y' <= v * x - y.
Proof.
- have [] := boolP (v * x' < y') => ltvx'y'.
  by have /eqP // -> : v * x' - y' == 0 by rewrite -leqn0 -(subnn y') leq_sub2r // ltnW.
- move: ltvx'y'; rewrite -ltnNge ltnS.
  rewrite leq_eqVlt => /orP [/eqP -> |lty'vx']; first by rewrite subnn.
  move: lexx'; rewrite leq_eqVlt => /orP [/eqP -> _ |ltx'x g]. 
  rewrite leq_sub2l //.
  rewrite leq_subCl subnA //; last by rewrite leq_mul2l ltnW // orbT.
  by rewrite -mulnBr addnC -leq_subRL.
Qed.

Lemma swap_dist_subr x x' y y' v 
      (lex'x : x' <= x) (ley'y : y' <= y) :
    y - y' <= v * (x - x') -> v * x' - y' <= v * x - y.
Proof.
- have [] := boolP (v * x' < y') => ltvx'y'.
  by have /eqP // -> : v * x' - y' == 0 by rewrite -leqn0 -(subnn y') leq_sub2r // ltnW.
- move: ltvx'y'; rewrite -ltnNge ltnS.
  rewrite leq_eqVlt => /orP [/eqP -> |lty'vx']; first by rewrite subnn.
  move: ley'y; rewrite leq_eqVlt => /orP [/eqP -> _ |lty'y]; first by rewrite leq_sub2r // leq_mul.
  rewrite leq_psubRL; last by rewrite subn_gt0.
  rewrite addnBA; last by rewrite ltnW.
  rewrite addnC -addnBA; last by rewrite ltnW.
  rewrite -leq_psubRL; last by rewrite subn_gt0.
  by rewrite -mulnBr.
Qed.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Lemma ler_swap [R : numDomainType] (x y z t : R) (h : x - y <= z - t) : t - y <= z - x.
Proof.
by rewrite ler_subr_addl addrA [X in X - y <= _]addrC -addrA -ler_subr_addl in h.
Qed.

Close Scope ring_scope.
End Arith.

(** Sequences *)

Section Seq.

Variable (T : eqType).

Lemma subseq_dropS (s : seq T) j : subseq (drop j.+1 s) (drop j s).
Proof. by elim: s j => //= x s ihs [|j] //; rewrite ?drop0 ?subseq_cons //=. Qed.

Lemma surjective_consing (x : T) l : 0 < size l -> l = head x l :: behead l.
Proof. by case: l. Qed.

End Seq.

(** Ordinals *)

Section Ordinal.

Lemma only_ord0 m (s : 'I_m.+1) : m = 0 -> (s != ord0) = false.
Proof.
move=> eq0m.
move: s (ltn_ord s) => [s' p] /=.
by rewrite -!(inj_eq val_inj) /= eq0m ltnS leqNgt -eqn0Ngt => /eqP ->.
Qed.

Definition addS_ord m (j : 'I_(m.+1)) :=
  match j with
  | Ordinal v p => if v == m then m else v.+1
  end.

Let lt_j1_m m (j : 'I_(m.+1)) (ltjm : j < m) : j.+1 < m.+1.
Proof. by []. Qed.
Definition proper_addS_ord m (j : 'I_(m.+1)) (ltjm : j < m) :=
  Ordinal (lt_j1_m ltjm).

Lemma eq_proper_addS m (j : 'I_(m.+1)) (ltjm : j < m) :
  @addS_ord m j = @proper_addS_ord m j ltjm.
Proof. by case: j ltjm => //= j ltjn /ltn_eqF ->. Qed.

Lemma ltn_addS_ord m (j : 'I_m.+1) : addS_ord j < m.+1.
Proof.
move: j => [j ltjm1] //=.
case eqjm: (j == m); first by rewrite ltnSn.
by move: eqjm; rewrite -eqSS ltn_neqAle => ->.
Qed.

Lemma widen_ord_inj n m (le_n_m : n < m): injective (widen_ord le_n_m).
Proof. by move => ? ? [] /val_inj. Qed.

Definition ord_succ m (j : 'I_(m.+1)) := Ordinal (@ltn_addS_ord m j).

Lemma lt_ord_succ m (j : 'I_m.+1) : j < m -> j < ord_succ j.
Proof. by case: j => [s p] /= /ltn_eqF ->. Qed.

Lemma le_ord_succ m (j : 'I_m.+1) : j <= ord_succ j.
Proof. by case: j => [s p] /=; case: (s == m); last by rewrite leqnSn. Qed.

Lemma ltn_subS_ord m (j : 'I_m) : j.-1 < m.
Proof. by move: (leq_pred j) (ltn_ord j); apply: leq_ltn_trans. Qed.

Definition ord_pred m j := Ordinal (@ltn_subS_ord m j).

Lemma le_ord_pred m (j : 'I_(m.+1)) : ord_pred j <= j.
Proof. by move: j => [s p] /=; exact: leq_pred. Qed.

Lemma lt_ord_pred m (j : 'I_(m.+1)) : 0 < j -> ord_pred j < j.
Proof. by move: j => [s p] /=; rewrite ltn_predL. Qed.

Lemma below_last_ord m (j : 'I_(m.+1)) : (j != ord_max) = (j < m).
Proof.
by move: j => [j p]; rewrite -(inj_eq val_inj) ltn_neqAle -ltnS p andbT.
Qed.

Lemma cancel_ord_pred m (j : 'I_m.+1) : 0 < j -> ord_succ (ord_pred j) = j.
Proof.
move: j => [s p] /= lt0s.
apply: ord_inj; rewrite /= prednK //; move: p.
by rewrite -[X in X < m.+1](@prednK s) // -eqSS => /ltn_eqF ->.
Qed.

Definition last_ord m := Ordinal (ltnSn m).

Lemma cancel_ord_succ m (j : 'I_m.+1) :
  j < last_ord m -> ord_pred (ord_succ j) = j.
Proof.
move: j => [s p] /= ltsm.
apply: ord_inj => //=.
by move/ltn_eqF: ltsm => ->.
Qed.

Lemma ord_succ_mon n (j j' : 'I_n.+1) : j <= j' -> ord_succ j <= ord_succ j'.
Proof.
move=> lejj' /=.
have [] := boolP (j' != ord_max) => j'notlast.
- rewrite !eq_proper_addS //=.
  rewrite below_last_ord in j'notlast => //.
  exact: leq_ltn_trans lejj' j'notlast.
  by rewrite below_last_ord in j'notlast.
- move: j'notlast; rewrite negbK => /eqP -> /=.
  rewrite ifT //=.
  exact: ltn_addS_ord.
Qed.

Lemma ord_pred_inj n (j j' : 'I_n.+1) (lt0j : 0 < j) (lt0j' : 0 < j') :
  ord_pred j = ord_pred j' -> j = j'.
Proof.
move/eqP.
rewrite -(inj_eq val_inj) /=.
(* move: (@PeanoNat.Nat.pred_inj j1 j2). *)
rewrite -!subn1.
rewrite -(eqn_add2r 1) -!addnABC // ?subnn ?addn0 => /eqP.
exact: ord_inj.
Qed.

Lemma ord_predK i m p (bound : i + m.+1 < p.+1) : 
  ord_pred (@inord p (i + m.+1)) = inord (i + m).
Proof.
apply/val_inj => /=.
by rewrite !inordK // -?subn1 -?addnBA // ?subn1 //= (@ltn_trans (i + m.+1)) // ltn_add2l.
Qed.

Lemma lt_ordS n (j j' : 'I_n.+1) (ltj'j : j' < j) : j' <= j.-1.
Proof. by move: (ltj'j); rewrite -[X in _ < X -> _](@ltn_predK j' j) ?ltnS. Qed.

Lemma lt_le_agent n (j j' : 'I_n.+1) (jnotlast : j != ord_max) :
  (j < j') = (ord_succ j <= j').
Proof. by rewrite /= !eq_proper_addS; rewrite below_last_ord in jnotlast. Qed.

Lemma lt_le_agent_succ n (j j' : 'I_n.+1) :
  j < j' -> ord_succ j <= j'.
Proof.
move=> ltjj'.
rewrite -lt_le_agent // -(inj_eq val_inj) /=.
have/ltn_eqF -> // : j < n.
move: (ltn_ord j').
rewrite ltnS.
by apply: leq_trans.
Qed.

Definition le_ord {n : nat} := [rel j1 j2 : 'I_n | j1 <= j2].

Lemma nth_agent_enum (j : nat) n (ltjn : j < n.+1) : nth ord_max (enum 'I_n.+1) j = Ordinal ltjn.
Proof. by apply: val_inj => /=; rewrite nth_enum_ord. Qed.

Lemma sort_enum : forall n, sort le_ord (enum 'I_n) = enum 'I_n.
Proof.
case=> [|n]. 
have -> //: enum 'I_0 = [::] by apply: size0nil; rewrite size_enum_ord.
have r_transitive: transitive (@le_ord n.+1) by move=> j1 j2 j3 /=; apply: leq_trans.
rewrite sorted_sort //= (@path_sorted _ _ (inord 0)) //.
apply/(pathP (inord 0)) => //= j ltjs. 
rewrite size_enum_ord in ltjs.
rewrite nth_enum_ord //. 
have [] := boolP (j == 0) => [/eqP -> //=|]; first by rewrite inordK.
rewrite -lt0n => lt0j.
by rewrite -(prednK lt0j) /= nth_enum_ord //= (@leq_trans j) // ?ltn_predL // ltnW.
Qed.

Lemma le1_ord n (j : 'I_n.+1) (lt0j : 0 < j) : j.-1 <= n.
Proof. rewrite (@leq_trans j) // ?leq_pred ?leq_ord //. Qed.

End Ordinal.

(** Tuples *)

Section Tuple.

Lemma tuple_of_tnth (T : Type) m (t : m.-tuple T) : [tuple tnth t j | j < m] = t.
Proof. by apply: eq_from_tnth => j; rewrite tnth_map tnth_ord_tuple. Qed.

Lemma val_tcast (T : Type) m n (tc : n = m) (t : n.-tuple T) : val (tcast tc t) = val t.
Proof. by case: m / tc. Qed.

Variable (T : eqType).

Lemma tnth_uniq m (x : T) (t : m.+1.-tuple T) i j :
  uniq t -> (tnth t i == tnth t j) = (i == j).
Proof.
move=> ut.
rewrite !(tnth_nth x) ?nth_uniq //; last by rewrite size_tuple ltn_ord.
by rewrite size_tuple ltn_ord.
Qed.

Lemma size_take_drop n (l : n.-tuple T) m m' (ltm'n : m' < n) (ltmm' : m < m') : 
  size (take (m'.+1 - m) (drop m l)) = m'.+1 - m.
Proof.
rewrite size_take size_drop size_tuple.
case: ifP => [//|/negbT].
rewrite -leqNgt leq_eqVlt => /orP [/eqP //|]. 
rewrite ltnNge. 
by have -> // : m'.+1 - m <= n - m by rewrite leq_sub2r.
Qed.

Lemma sort_inj_ord : forall n (t : n.-tuple 'I_n) (tinj : injective (tnth t)),
  sort le_ord t = enum 'I_n.
Proof. 
case=> [t _|n t tinj]; first by rewrite tuple0 sortE /= [RHS]size0nil // size_enum_ord.
have r_transitive: transitive le_ord by move=> j1 j2 j3 /=; apply: leq_trans.
move: (@perm_iota_sort _ le_ord (inord 0) t) => [s p] eqs. 
rewrite -sort_enum.
apply/perm_sortP => //; last first.
rewrite perm_sym.
apply/tuple_permP. 
have inv_l_inj : injective (invF tinj) by apply: (@can_inj _ _ _ (tnth t)); exact: f_invF.
exists (perm inv_l_inj) => //=.
apply: (@eq_from_nth _ (inord 0)) => [|j ltjs]; 
  first by rewrite size_enum_ord size_map size_enum_ord.
apply: val_inj => /=.
rewrite size_enum_ord in ltjs.
rewrite nth_enum_ord ?(@nth_map _ (inord 0) _ _ (fun j => tnth t (perm inv_l_inj j))) //;
  last by rewrite size_enum_ord.
rewrite permE canF_sym ?nth_enum_ord //.
apply: invF_f.
by move=> j1 j2 /=; rewrite -eqn_leq => /eqP; apply: val_inj.
exact: leq_trans.
exact: leq_total.
Qed.

Lemma inj_map_tuple (T1 T2 : eqType) (f : T1 -> T2) n :
  injective f -> injective (@map_tuple n _ _ f).
Proof.
move=> inj t1 t2 /eqP.
rewrite -!(inj_eq val_inj) /= => /eqP eq12. 
apply: val_inj => /=.
exact: (inj_map inj).
Qed.

Section Tuple_i.

Variable (n : nat) (i : 'I_n).

Lemma tcast_tuple_i m (lt_i_m : i < m) : minn i m + (m - i.+1 + 1) = m.
Proof.
move/ltnW/minn_idPl: (lt_i_m) => ->.
have -> :  m - i.+1 + 1 = m - i by rewrite addn1 subnSK.
rewrite addnBCA //; last by move/ltnW: lt_i_m.
by rewrite subnn addn0.
Qed.

Definition tuple_i m (t : m.-tuple T) (x : T) (lt_i_m : i < m) :=
  tcast (tcast_tuple_i lt_i_m) [tuple of take i t ++ (drop i.+1 t ++ [:: x])].

Lemma tuple_i_last m (t : m.+1.-tuple T) (x : T) :
  tnth t ord_max = last x (val t).
Proof.
rewrite (tnth_nth x) /=.
have eqns1: m = (size t).-1 by rewrite size_tuple.
rewrite [X in nth _ _ X]eqns1.
exact: nth_last.
Qed.

Ltac nth_split_i j ltji :=
  rewrite nth_cat size_takel ?size_tuple ?(ltnW ltn_ord) //;
  first move: (ltji) => -> /=.

Lemma id_tuple_i m (t : m.-tuple T) (x : T) (lt_i_m : i < m) (j : 'I_m ) :
  j < i  -> tnth (tuple_i t x lt_i_m) j = tnth t j.
Proof.
move=> ltji.
rewrite tcastE !(tnth_nth x) //=.
nth_split_i j ltji; last by move/ltnW: lt_i_m.
by rewrite nth_take.
Qed.

Lemma shifted_tuple_i m (t : m.+1.-tuple T) (x : T) (lt_i_m : i < m.+1)
  (j : 'I_m.+1) :
  i <= j -> j < m -> tnth (@tuple_i m.+1 t x lt_i_m) j = tnth t (ord_succ j).
Proof.
move=> leij ltjn1.
move/ltnW: (ltn_ord i) => lein.
rewrite tcastE !(tnth_nth x) /=.
rewrite nth_cat size_takel; last by rewrite size_tuple; move/ltnW: lt_i_m.
rewrite leq_gtF // nth_cat size_drop size_tuple subnS ltn_predRL -subSn //.
rewrite ltn_sub2r ?nth_drop //; last first.
have -> // : i.+1 + (j - i) = j.+1
  by rewrite addnC addnBAC -?addnBA // subSn ?subnn ?addn1.
by rewrite eq_proper_addS.
Qed.

Lemma last_tuple_i m (t : m.+1.-tuple T) (x : T) (lt_i_m : i < m.+1) :
 tnth (@tuple_i m.+1 t x lt_i_m) ord_max = x.
Proof.
rewrite (@tuple_i_last m _ x).
by rewrite val_tcast /= cats1 last_cat last_rcons.
Qed.

Lemma tuple_i_uniq m (t : m.-tuple T) (x : T) (lt_i_m : i < m) :
  uniq (x :: t) -> uniq (tuple_i t x lt_i_m).
Proof.
have H : subseq (take i t ++ drop i.+1 t) t.
  by rewrite -{3}(cat_take_drop i t) cat_subseq ?subseq_dropS.
rewrite /tuple_i val_tcast /= catA cat_uniq /= andbT orbF => /andP[h1 h2].
by rewrite (subseq_uniq H) //; apply: contra h1 => ?; rewrite (mem_subseq H).
Qed.

End Tuple_i.

End Tuple.

(** Bigops *)

Section BigOp.

Lemma big_cropr m F (i : nat) :
  \sum_(s < m.+1 |(i <= s) && (s != ord_max)) F s =
    \sum_(s < m.+1 | i <= s < m) F s.
Proof. by apply: eq_bigl => s; rewrite below_last_ord. Qed.

Lemma sum0_gt_last m (F : 'I_m.+1 -> nat) : \sum_(s < m.+1 | m < s) F s = 0.
Proof. apply: big_pred0 => s; exact: (leq_gtF (leq_ord s)). Qed.

Lemma big_distrmr k F x y i :
  \sum_(s < k | i < s) F s * (x + y) =
  \sum_(s < k | i < s) F s * x + \sum_(s < k | i < s) F s * y.
Proof. by rewrite -big_distrl /= mulnDr !big_distrl. Qed.

Lemma big_unrolll k F m i (ltmi : m < i) (ltimk1 : i - m < k.+1) :
  \sum_(s < k.+1 | i - m.+1 < s <= i) F s = 
  \sum_(s < k.+1 | i - m < s <= i) F s + F (inord (i - m)).
Proof.
rewrite [LHS](@bigID _ _ _ _ _ (fun s => val s == i - m)) /= addnC.
congr (_ + _).
- apply: eq_bigl => s.
  rewrite andbC andbA (@andb_id2r _ _ (i - m < s)) //= => _.
  rewrite leq_eqVlt andb_orr subnSK //. 
  rewrite eq_sym andNb orFb andb_idl // => /ltn_eqF //.
  move/negbT => //.
- rewrite (big_pred1 (inord (i - m))) // => s.
  rewrite andb_idl /= => [|/eqP ->]; last by rewrite subnSK ?leqnn ?leq_subr.
  congr (_ == _). 
 by rewrite inordK.
Qed.

Lemma big_shrinkl m F i i' (lti'i : i' < i) : 
  \sum_(s : 'I_m| (i' < s) && (i < s)) F s = \sum_(s : 'I_m | i < s) F s.
Proof. apply: eq_bigl => s; apply: andb_idl; exact: (ltn_trans lti'i). Qed.

Lemma big_shrinkr m F i i' (lti'i : i' < i) :
  \sum_(s : 'I_m | (i' < s) && ~~ (i < s)) F s = \sum_(s : 'I_m| i' < s <= i) F s.
Proof. by apply: eq_bigl => s; rewrite -leqNgt. Qed.

Lemma big_trim_bound_P l (i : 'I_l) m p (F : 'I_p.+1 -> nat) (ltim1p1 : i + m.+1 < p.+1) : 
  \sum_(s < p.+1 | (i < s <= i + m.+1) && (s != inord (i + m.+1))) F s = 
  \sum_(s < p.+1 | i < s <= i + m) F s.
Proof.
apply: eq_bigl => s. 
rewrite -andbA.
congr (_ && _).
have -> /= : (s != inord (i + m.+1)) = (val s != i + m.+1). 
  move: s => [s p'].
  by rewrite -(inj_eq val_inj) /= inordK.
rewrite leq_eqVlt andb_orl andbN orFb addnS ltnS andb_idr // -ltnS => /ltn_eqF.
exact: negbT.
Qed.

Lemma max_monotonic
  (T : finType)
  (F F' : T -> nat)
  (ltFF' : forall o : T, F o <= F' o) :
  \max_o F o <= \max_o F' o.
Proof.
by elim/big_ind2:_ => // m1 m2 n1 n2 h1 h2; rewrite geq_max !leq_max h1 h2 orbT.
Qed.

Lemma split_sum_ord (j j' k : nat) (ltjj' : j < j') F :
  \sum_(s < k | j < s) F s = \sum_(s < k | j < s <= j') F s + \sum_(s < k | j' < s) F s.
Proof.
rewrite (bigID (fun s : 'I_k => s <= j')) /=.
congr (_ + _).
apply: eq_bigl => s.
rewrite -ltnNge andb_idl //.
exact: ltn_trans.
Qed.

Lemma reindex_ge_i n (i : 'I_n) m (F : 'I_m.+1 -> nat) 
      (lt0m : 0 < m) (ltil : i < last_ord m) :
      \sum_(s < m.+1 | i < s) F s = \sum_(s < m.+1 | i <= s < m) F (ord_succ s).
Proof.
rewrite (bigD1 ord_max) //=.
rewrite [in RHS](bigD1 (ord_pred ord_max)) //=; last first.
  apply/andP. split; last by rewrite ltn_predL.
  rewrite -ltnS (ltn_predK lt0m) //.
rewrite cancel_ord_pred //=.
congr (_ + _).
set P := (X in \sum_(s < m.+1 | X s) _ = _). 
rewrite (@reindex_onto _ _ _ _ _
               (@ord_succ m) (@ord_pred m.+1) P) //= => [|s /andP [ltis nesx]]; last first.
- rewrite cancel_ord_pred //.
  exact: (leq_ltn_trans (leq0n i)).
- apply: eq_bigl => s.
  rewrite /P below_last_ord //=.
  case: s => [s' p] /=.
  rewrite -![X in _ = _ && ~~ X](inj_eq val_inj) /=.
  - case eqs'm: (s' == m).
    rewrite ltnn andbF andFb.
    move: eqs'm => /eqP ->.
    by rewrite ltnn andbF andFb.
  - rewrite cancel_ord_succ //= ?eqxx ?andbT.
    rewrite ltnS -ltn_predRL.
    rewrite -andbA [X in _ = _ && X]andbC.
    rewrite -(@prednK m lt0m) ltnS.
    by rewrite -ltn_neqAle.
  move: eqs'm p; rewrite ltnS leq_eqVlt => ->.
  by rewrite orFb.
Qed.

Lemma big_split_subn k (P : 'I_k -> bool) F1 F2
      (H : forall s : 'I_k, P s -> F2 s <= F1 s) :
  \sum_(s < k | P s) (F1 s - F2 s) = \sum_(s < k | P s) F1 s - \sum_(s < k | P s) F2 s.
Proof.
suff:
  \sum_(s < k | P s) (F1 s - F2 s) =
    \sum_(s < k | P s) F1 s - \sum_(s < k | P s) F2 s /\
    \sum_(s < k | P s) F2 s <= \sum_(s < k | P s) F1 s by case.
pose K x y z := x = y - z /\ z <= y.
apply: (big_rec3 K); first by []; rewrite {}/K.
move=> i b_x b_y b_z /H Pi [] -> Hz; split; last exact: leq_add.
by rewrite addnBA ?addnBAC ?subnDA.
Qed.

Lemma sum_ord0 m (P : 'I_m.+1 -> bool) F :
  m = 0 -> P ord0 -> \sum_(s < m.+1 | P s) F s = F ord0.
Proof.
move=> eq0m P0.
rewrite (bigD1 ord0) // -[in RHS](addn0 (F ord0)).
congr (_ + _) => //=.
set sum := (X in X = 0).
have -> : sum = \sum_(i < m.+1 | false) F i.
  apply: eq_bigl => i.
  by rewrite only_ord0 // andbF.
exact: big_pred0_eq.
Qed.

Section Telescope.

Variable (R : Type) (idx : R) (op : Monoid.law idx).

Variable (f : nat -> nat -> R) (n : nat).

Definition shrink m := 
  forall p q r, p < q < r -> (n <= p /\ r <= m) -> op (f p q) (f q r) = f p r.
Definition empty m := n = m -> f n n = idx.

Lemma telescope_op m : 
  n <= m -> shrink m -> empty m -> 
  \big[op/idx]_(n <= i < m) f i i.+1 = if n <= m then f n m else idx.
Proof.
rewrite leq_eqVlt => /orP [/eqP eqnm _ idf|ltnm s _].
- by rewrite big_geq -eqnm ?leqnn // eq_refl orTb idf. 
- have tel p : shrink (n + p.+1) -> 
               \big[op/idx]_(n <= i < n + p.+1) f i i.+1 = f n (n + p.+1).
    elim: p => [rf|p IH rf]; first by rewrite addn1 big_nat1.  
    rewrite addnS big_nat_recr ?leq_addr //.
    rewrite IH => [|p' q r /andP [ltnp ltqr] [lenp lern]].
    - by rewrite rf // -?[X in X < _](addn0 n) ?ltn_add2l //= leqnn /= ltnSn.
    - rewrite rf // ?ltnp ?ltqr //= lenp (@leq_trans (n + p.+1)) //=.
      by rewrite (@leq_trans (n + p.+1)) //= leq_add2l.
  pose p := m - n.+1.
  have eqm : m = n + p.+1 by rewrite subnSK ?subnKC // ltnW.
  rewrite eqm tel // ?ifT //; last by rewrite eqm in s.
  by rewrite -{3}(addn0 n) ltn_add2l ltn0Sn orbT.
Qed.

End Telescope.

Section SumOfDifferences.

Lemma telescope_addn n m f : 
  n <= m -> {in [pred i | n <= i <= m] &, {homo f : x y /~ x <= y}} ->
  \sum_(n <= k < m) (f k - f k.+1) = f n - f m.
Proof.
pose tadd := @telescope_op nat 0 addn_monoid => lenm lef.
have ssub : shrink addn_monoid (fun p q => f p - f q) n m.
  move=> p q r /= /andP [/ltnW lepq /ltnW leqr] [lenp lerm].  
  have lenqm : n <= q <= m. 
    rewrite (leq_trans _ (leq_trans leqr lerm)) //.
    by rewrite (leq_trans _ (leq_trans lenp lepq)).
  rewrite addnC -sum_diff // ?(lef q p) ?(lef r q) //= ?unfold_in /=.
  rewrite lerm (leq_trans (leq_trans lenp lepq)) //.
  by rewrite lenp (leq_trans _ (leq_trans leqr lerm)).
by rewrite (@tadd _ _ _ _ ssub) ?ifT //= /empty subnn.
Qed.

(* See 8.15. *)

Lemma big_nat_widenl (m1 m2 n : nat) (P : pred nat) : forall F, 
  m2 <= m1 ->
  \sum_(m1 <= i < n | P i) F i =
  \sum_(m2 <= i < n | P i && (m1 <= i)) F i.
Proof.
move=> F le21.
have [] := boolP (m1 <= n) => [lem1n|].
- rewrite big_nat_cond.
  rewrite [RHS](@big_cat_nat _ _ _ m1) //=. 
  have -> : \sum_(m2 <= i < m1 | P i && (m1 <= i)) F i = 0.
    rewrite big_nat_cond.
    by admit.
  rewrite big_nat_cond [RHS]big_nat_cond. 
  by admit.
- rewrite -ltnNge.
  by admit.
Admitted.

Definition antimonotone n (F : 'I_n -> nat) := {homo F : x y /~ x <= y}.

Variable (k :nat) (F : 'I_k.+1 -> nat ) (aF : antimonotone F).

Lemma sum_diffs (l h : 'I_k.+1) : 
  l < h -> \sum_(s < k.+1 | l < s <= h) (F (ord_pred s) - F s) = F l - F h.
Proof.
move=> ltlh.
pose f := fun s => F (inord s). 
set g := fun s => f s.-1 - f s.
under (eq_bigr (fun (s : 'I_k.+1) => g s)) => i /andP [ltli leih].
  congr (F _ - F _); last by apply: val_inj => /=; rewrite inordK.
  apply: val_inj => /=.
  by rewrite inordK // (@ltn_trans i) // ltn_predL (@leq_ltn_trans l).
rewrite -(@big_mkord _ _ _ _ (fun s => l < s <= h) g).
have -> : \sum_(0 <= i < k.+1 | l < i <= h) g i = \sum_(l.+1 <= i < h.+1) g i. 
  by rewrite (@big_nat_widenl l.+1 0) // (@big_nat_widen _ _ _ _ h.+1 k.+1) ?ltn_ord.
rewrite telescope_addn ?(ltn_trans ltlh) // => [|x y xin yin leyx].
- congr (F _ - F _); first by apply: val_inj => /=; rewrite inordK.
  by apply: val_inj => /=; rewrite inordK. 
- have ltk1 n : n \in [pred n | l < n & n <= h.+1] -> n - 1 < k.+1.
    rewrite unfold_in /= => /andP [_]. 
    rewrite -addn1 addnC -leq_subLR => lenh1.
    by rewrite (leq_ltn_trans _ (ltn_ord h)).
  by rewrite aF // !inordK -!subn1 ?leq_sub2r // ltk1.
Qed.

End SumOfDifferences.

End BigOp.

(** Sorting lemmas *)

Section Sort.

Lemma sort_tupleP T n r (t : n.-tuple T): size (sort r t) == n.
Proof. by rewrite size_sort size_tuple. Qed.
Canonical sort_tuple T n r t := Tuple (@sort_tupleP T n r t).

(* convenient *)
Definition tsort T n r (t : n.-tuple T) := [tuple of sort r t].

Lemma sorted_tsort T n r (rtr : transitive r) (t : n.-tuple T) :
  sorted r t -> tsort r t = t.
Proof. by move/(sorted_sort rtr) => hs; apply/val_inj/hs. Qed.

Lemma perm_iota_sort_tuple (T : eqType) leT n (t : n.-tuple T) :
  { lbl : n.-tuple 'I_n | sort leT t = [seq tnth t i | i <- lbl] }.
Proof.
case: n t => [|n] t; first by exists [tuple]; rewrite tuple0.
have x : T by have [x t'] := tupleP t.
have [lbl h_perm h_idx] := perm_iota_sort leT x t.
have lbl_tuple: size (map (@inord n) lbl) == n.+1.
  by rewrite size_map (perm_size h_perm) size_iota size_tuple.
exists (Tuple lbl_tuple).
rewrite h_idx -map_comp -eq_in_map => z.
rewrite (perm_mem h_perm) mem_iota add0n size_tuple /= => h_mem.
by rewrite (tnth_nth x) inordK.
Qed.

Section Tuple_i.

Definition down_sorted_tuple n k (t : k.-tuple 'I_n) :=
  forall (s1 s2 : 'I_k), s1 <= s2 -> tnth t s2 <= tnth t s1.

Definition sorted_tuple := down_sorted_tuple.

Variable (k n : nat) (i : 'I_n).
Implicit Types (t : k.+1.-tuple 'I_n.+1).

Lemma sorted_tuple_i t (lt_i_m : i < k.+1) :
  sorted_tuple t -> sorted_tuple (tuple_i t ord0 lt_i_m).
Proof.
move=> st s1 s2 lts1s2.
- have [] := boolP (s1 < i) => [lts1i|].
  rewrite [X in _ <= nat_of_ord X]id_tuple_i //.
  have [] := boolP (s2 < i) => [lts2i|]; first by rewrite id_tuple_i //; exact: st.
  rewrite -leqNgt => leis2.
  - have [] := boolP (s2 < k) => [lts2m1|].
    rewrite shifted_tuple_i //.
    apply: (@leq_trans (tnth t s2)); last exact: (st).
    apply: st.
    by rewrite /ord_succ /= eq_proper_addS //=.
  - rewrite -below_last_ord negbK => /eqP ->.
    by rewrite last_tuple_i leq0n.
- rewrite -leqNgt => leis1.
  - have [] := boolP (s1 < k) => [lts1m1|].
    rewrite [X in _ <= nat_of_ord X]shifted_tuple_i //.
    - have [] := boolP (s2 < i) => [lts2i|].
      have: s1 < i by exact: leq_ltn_trans lts1s2 lts2i.
      by rewrite ltnNge leis1.
    - rewrite -leqNgt => leis2.
      - have [] := boolP (s2 < k) => [lts2m1|].
        rewrite shifted_tuple_i //.
        have: ord_succ s1 <= ord_succ s2 by rewrite /ord_succ /= !eq_proper_addS.
        exact: st.
      - rewrite -below_last_ord negbK => /eqP ->.
        by rewrite last_tuple_i leq0n.
  - rewrite -below_last_ord negbK => /eqP eqs1m.
    rewrite eqs1m.
    have ->: s2 = ord_max.
      apply: val_inj => /=.
      move: (conj lts1s2 (leq_ord s2)) => /andP.
      by rewrite eqs1m /= -eqn_leq eq_sym => /eqP.
    exact: leqnn.
Qed.

End Tuple_i.

Section Transposition.

Variable (k : nat) (T : finType).

Variable (i1 i2 : 'I_k.+1) (t : k.+1.-tuple T).

Definition tuple_tperm (t : k.+1.-tuple T) := [tuple tnth t (tperm i1 i2 i) | i < k.+1].

Lemma tuple_perm_inj : injective tuple_tperm.
Proof.
move=> t1 t2 /eqP.
rewrite eqEtuple => /forallP eq_tp.
apply/eqP; rewrite eqEtuple; apply/forallP => j.
- have [] := boolP ((i1 != j) && (i2 != j)) => [/andP [nei1 nei2]|/nandP].
  by move: (eq_tp j); rewrite !tnth_mktuple !tpermD.
- rewrite !negbK.
  move=> [/eqP <- |/eqP <-].
  by move: (eq_tp i2); rewrite !tnth_mktuple tpermR.
  by move: (eq_tp i1); rewrite !tnth_mktuple tpermL.
Qed.

Definition itperm : {perm (k.+1.-tuple T)} := perm tuple_perm_inj.

Let x0 : T := tnth t ord0.

Lemma tuple_tperm_uniq   
      (ut : uniq t) :
  uniq (tuple_tperm t). 
Proof.
rewrite map_inj_uniq => [|x y]; first by rewrite val_ord_tuple enum_uniq.
- have [] := boolP ((i1 != x) && (i2 != x)) => [/andP [nexi1 nexi2]|/nandP].
  rewrite tpermD //.
  - have [] := boolP ((i1 != y) && (i2 != y)) => [/andP [neyi1 neyi2]|/nandP].
    rewrite tpermD // => /eqP.
    by rewrite (tnth_uniq x0) // => /eqP.
  - rewrite !negbK;move=> [/eqP <- |/eqP <-].
    - rewrite tpermL => /eqP.
      rewrite (tnth_uniq x0) // eq_sym.
      by move/negPn; rewrite nexi2.
    - rewrite tpermR => /eqP.
      rewrite (tnth_uniq x0) // eq_sym.
      by move/negPn; rewrite nexi1.
- rewrite !negbK; move=> [/eqP <-|/eqP <-].
  - - have [] := boolP ((i1 != y) && (i2 != y)) => [/andP [neyi1 neyi2]|/nandP].
      rewrite tpermL tpermD // => /eqP.
      rewrite (tnth_uniq x0) //.
      by move/negPn; rewrite neyi2.
    - rewrite !negbK; move=> [/eqP <- |/eqP <-]; first by rewrite tpermL.
      rewrite tpermR tpermL => /eqP.
      by rewrite (tnth_uniq x0) // => /eqP.
  - - have [] := boolP ((i1 != y) && (i2 != y)) => [/andP [neyi1 neyi2]|/nandP].
      rewrite tpermR tpermD // => /eqP.
      rewrite (tnth_uniq x0) //.
      by move/negPn; rewrite neyi1.
    - rewrite !negbK; move=> [/eqP <- |/eqP <-] //.
      rewrite tpermR tpermL => /eqP.
      by rewrite (tnth_uniq x0) // eq_sym => /eqP.
Qed.

Lemma notin_itperm (j : T) :
  j \notin t -> j \notin (aperm t itperm).
Proof.
apply: contraNN => /tnthP [i'] ->.
rewrite apermE permE !tnth_mktuple.
by apply/tnthP; exists (tperm i1 i2 i').
Qed.

Lemma it_aperm_uniq  :
  uniq t -> uniq (aperm t itperm).
Proof. by move=> ut; rewrite apermE permE tuple_tperm_uniq. Qed.

End Transposition.

Section BubbleSort.

Import Order.Theory.

Local Open Scope order_scope.

Variable (k : nat) (T : finPOrderType tt).

Definition up_sorted_tuple (t : k.+1.-tuple T) :=
  forall (s1 s2 : 'I_k.+1), (s1 < s2)%N ->  (tnth t s1 < tnth t s2)%O.

Definition is_bubble (t : k.+1.-tuple T) (i1i2 : 'I_k.+1 * 'I_k.+1) :=
    (i1i2.1 < i1i2.2)%N && (tnth t i1i2.2 < tnth t i1i2.1)%O.

(* bubble_swap t i1i2s = (all pairs in i1i2s satisfy bubble_swap, bubble-swapped t) *)

Definition bubbles_swap (t : k.+1.-tuple T) (i1i2s : seq ('I_k.+1 * 'I_k.+1)) :=
  foldr (fun i1i2 xo =>
           let bubble_swapped := xo.1 in
           let sorted_tuple := xo.2 in
           (is_bubble sorted_tuple i1i2 && bubble_swapped,
            aperm sorted_tuple (itperm T i1i2.1 i1i2.2)))
        (true, t)
        i1i2s.

Lemma bubble_uniq (t : k.+1.-tuple T) (i1i2s : seq ('I_k.+1 * 'I_k.+1)) :
  uniq t -> uniq (bubbles_swap t i1i2s).2.
Proof. by move=> ut; elim: i1i2s => [//|? ?]; exact: it_aperm_uniq. Qed.

Lemma notin_bubble (t : k.+1.-tuple T) (i1i2s : seq ('I_k.+1 * 'I_k.+1)) 
      (j : T) (nojin : j \notin t) :
  j \notin (bubbles_swap t i1i2s).2.
Proof.
elim: i1i2s => [//=|i1i2 i1i2s /=]. 
apply: contraNN.
rewrite apermE permE /tuple_tperm => /tnthP [s'].
rewrite tnth_mktuple => ->. 
by apply/tnthP; exists (tperm i1i2.1 i1i2.2 s').
Qed.

Close Scope order_scope.

End BubbleSort.

Section Insert.

Open Scope order_scope.

Variable (T : finPOrderType tt).

(* b is a list of bubbles (m, m.+1), each encoded as m. *)

Fixpoint insert_up' x (t : seq T) (n : nat) b := 
  match t with
    | [::] => ([:: x], b)
    | hd :: tl => if (x < hd)%O then
                  (x :: hd :: tl, b)
                else
                  let t'b' := insert_up' x tl n.+1 (rcons b n) in
                  (hd :: t'b'.1, t'b'.2)
  end.

Definition insert_up x (t : seq T) := @insert_up' x t 0 [::].

Lemma size_insert m x (t : m.-tuple T) : size (insert_up x t).1 = m.+1.
Proof.
suff: forall n b, size (insert_up' x t n b).1 = m.+1; first by apply. 
move=> n b.
case: t.  
elim: m n b => [n b l /eqP sz /=|m IH n b]; first by rewrite (size0nil sz).
case=> //= hd tl sztl.
apply/eqP.
case : (x < hd) => /=; first by rewrite eqSS. 
by rewrite eqSS IH.
Qed.

Lemma bound_bubbles m x (t : m.-tuple T) (i1 : nat) :
    i1 \in (insert_up x t).2 -> i1 < m.
Proof.
case: t => t sz /= i1in.
move: sz i1in => /eqP <-.
suff: forall (t : seq T) n (b : seq nat),
    (forall (i1 : nat), i1 \in b -> i1 < size t + n) -> i1 \in (insert_up' x t n b).2 -> i1 < size t + n;
      first by move/(_ t 0 [::]); rewrite addn0; apply => i1'; rewrite in_nil. 
elim=> [n b p /= /p //|a l IH n b p /=].
case: (x < a)%O => [/= /p //=|].
move: (@IH n.+1 (rcons b n)).
have -> : size l + n.+1 = (size l).+1 + n.
  by rewrite -addn1 -(addn1 (size l)) -[RHS]addnA (addnC 1%nat n).
apply => i1'.
rewrite mem_rcons in_cons => /orP [/eqP -> |].
rewrite -{1}(add0n n) ltEnat/= ltn_add2r //.
by move/p. 
Qed.

Fixpoint bubbles_swap' m (t : m.+1.-tuple T) (i1s : seq nat) :=
  match i1s with
  | [::] => t
  | hd :: tl => let t' := bubbles_swap' t tl in
              aperm t' (itperm T (inord hd) (inord hd.+1))
end.

Lemma bubble_insert_spec m (x : T) (t : m.+1.-tuple T) :
  up_sorted_tuple t ->
  exists i1i2s, up_sorted_tuple (bubbles_swap' [tuple of x :: t] i1i2s).
Proof.
move=> ut.
exists (insert_up x t).2.
Admitted.

Fixpoint bb_insert_sort' (t : seq T) n b :=
  match t with
  | [::] => ([::], b)
  | hd :: tl => let tl'b' := bb_insert_sort' tl n.+1 b in
              insert_up' hd tl'b'.1 n tl'b'.2
  end.

Definition bb_insert_sort (t : seq T) := bb_insert_sort' t 0 [::].

Close Scope order_scope.

End Insert.

Let lt1 m j (ltjm : j < m) : j.+1 < m.+1.
Proof. by []. Qed.
Definition bump1 m (x : 'I_m) := Ordinal (lt1 (ltn_ord x)).

Lemma bubble_sort_spec m (T : finPOrderType tt) (t : m.+1.-tuple T) (u : uniq t) :
  exists (i1i2s : seq ('I_m.+1 * 'I_m.+1)),
    let xo := bubbles_swap t i1i2s in
    xo.1 /\ up_sorted_tuple xo.2. 
Proof.
case: t u => s. 
elim: m s => [s sz1 u1|n IH]. 
- exists [::] => /=.
  split=> //.
  rewrite /up_sorted_tuple => s1 s2.
  have/fintype1P [s0]: #|'I_1| == 1 by move/eqP: (card_ord 1).
  move=> eqs0.
  by rewrite (eqs0 s1) (eqs0 s2) ltnn.
- case=> [//=|hd tl sz u].
  have sztl: size tl == n.+1 by [].
  have utl: uniq tl by move: u => /= /andP [].
  move: (IH tl sztl utl) => [i1i2tl [swaptl sorttl]].
  exists (map (fun i1 => (inord i1, inord i1.+1)) (bb_insert_sort (hd :: tl)).2) => /=.
Admitted.

Section Equiv.

Variable (n : nat) (k : nat).

Definition geq_bid (b1 b2 : 'I_n.+1) := b1 >= b2.

Lemma transitive_geq_bid : transitive geq_bid.
Proof. exact/rev_trans/leq_trans. Qed.

Lemma reflexive_geq_bid : reflexive geq_bid.
Proof. move=> x. exact: leqnn. Qed.

Lemma anti_geq_bid: antisymmetric geq_bid.
Proof. by move=> x y /anti_leq /val_inj. Qed.

Lemma total_geq_bid: total geq_bid.
Proof. by move=> b1 b2; exact: leq_total. Qed.

Implicit Types (bs : k.-tuple 'I_n.+1).
Definition sorted_bids bs := sorted_tuple bs.

Lemma sorted_bids_sorted bs : sorted_bids bs <-> sorted geq_bid bs.
Proof.
split=> sortedbs => [|j1 j2 lej1j2].
- apply: (@path_sorted _ geq_bid ord_max).
  apply/(pathP ord0) => j ltjz.
  move: j ltjz => [_|m m1].
  - have -> : nth ord0 (ord_max :: bs) 0 = ord_max by rewrite nth0.
    by move: (ltn_ord (nth ord0 bs 0)).
  - rewrite -nth_behead /behead /geq_bid. 
    rewrite size_tuple in m1. 
    rewrite (_ : m.+1 = Ordinal m1) // -tnth_nth.
    rewrite [X in nth ord0 _ X](_ : m = Ordinal (ltn_trans (ltnSn m) m1)) // -tnth_nth.
    by rewrite sortedbs //=.
- rewrite !(tnth_nth ord0).
  have jin (j : 'I_k) : j \in [pred j' : 'I_k | j' < size bs].
    by rewrite unfold_in /= size_tuple ltn_ord.
  apply: (sorted_leq_nth transitive_geq_bid leqnn) => //; first exact: jin.
  exact: jin.
Qed.

End Equiv.

End Sort.

(** Should use order.v version (> 8.13). *)

Module OrdinalOrder.

Section OrdinalOrder.

Variable (n : nat).

Definition le (i1 i2 : 'I_n.+1) := i1 <= i2.
Definition lt (i1 i2 : 'I_n.+1) := i1 < i2.

Lemma le_refl : reflexive le.
Proof. by rewrite /le. Qed.

Lemma le_anti : antisymmetric le.
Proof. move=> x y /= lexyx. apply: val_inj => /=. exact: anti_leq. Qed.

Lemma le_trans : transitive le. 
Proof. move=> x y z. rewrite /le /=. exact: leq_trans. Qed.

Lemma ltNeq x y : lt x y = (y != x) && le x y.
Proof. by rewrite /lt /le ltn_neqAle -(inj_eq val_inj) eq_sym. Qed.

Lemma le_total x y : le x y || le y x. 
Proof. exact: leq_total. Qed.

Definition orderMixin := LeOrderMixin ltNeq (fun _ _ => erefl) (fun _ _ => erefl)
                                      le_anti le_trans le_total.

Notation A := 'I_n.+1.

Lemma ord0bot (x : A) : le ord0 x.
Proof. by []. Qed.

Canonical porderType := POrderType tt A orderMixin.
Canonical latticeType := LatticeType A orderMixin.
Canonical bLatticeType := BLatticeType A (BottomMixin ord0bot).
Canonical distrLatticeType := DistrLatticeType A orderMixin.
Canonical bDistrLatticeType := [bDistrLatticeType of A].
Canonical orderType := OrderType A orderMixin.
Canonical finPOrderType := [finPOrderType of A].

Lemma ltEnat (i1 i2 : A) : lt i1 i2 = (i1 < i2)%nat.
Proof. by []. Qed.

Lemma leEnat (i1 i2 : A) : le i1 i2 = (i1 <= i2)%nat.
Proof. by []. Qed.

(*

Lemma minEnat : min = minn. 

Lemma maxEnat : max = maxn. 

*)

Lemma botEnat : 0%O = 0%N :> nat. 
Proof. by []. Qed.

End OrdinalOrder.

End OrdinalOrder.
