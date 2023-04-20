(**

  SD.v
  
  Sequential Dictator mechanism.

  Proof of truthfulness.
  https://ml2.inf.ethz.ch/courses/agt/lectures/AGT_HS21_lecture8.pdf
  
  - Algorithm  
  - Truthfulness
  - Order-compatible utility 

  Pierre Jouvelot (Mines Paris, PSL University)

  Thanks to Laurent Théry (proof of f_surj) and François Irigoin (eq_wins_alloc_with_diff).

  Licence: CeCILL-B.

*)
 
From Coq Require Import Unicode.Utf8.
From mathcomp Require Import all_ssreflect.

From mech.lib Require Import lib labelling mech.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Present in newer versions of mathcomp *)
Lemma leq_sub2lE (m n p : nat) : n <= m -> (m - p <= m - n) = (n <= p).
Admitted.

Lemma find_predT : forall T (s : seq T), find xpredT s = 0. 
Admitted.
(* End newer versions *)

Section Utils.

Lemma subnKK n m p : m <= n -> p <= n -> (n - m == n - p) = (m == p). 
Proof.
wlog: m p / m <= p. 
  move : (@leq_total m p) => /orP [lemp f lemn lepn|lepm f lemn lepn]; first by exact: f. 
  by move: (@f p m); rewrite eq_sym => ->. 
elim: n m p => [m p // _|n IH m p lemp]; first by rewrite !leqn0 => /eqP -> /eqP ->.
rewrite leq_eqVlt => /orP [/eqP ->|ltmn1].
- rewrite leq_eqVlt => /orP [/eqP ->|ltpn1]; first by rewrite !eq_refl.
  by rewrite ltn_eqF ?gtn_eqF // subnn subn_gt0.
- rewrite leq_eqVlt => /orP [/eqP ->|ltpn1]; last by rewrite !subSn ?eqSS ?IH // ltnW.
  by rewrite subSn ?subnn -1?ltnS //gtn_eqF // ltn_eqF.
Qed.

Lemma f_surj n (T : eqType) (t : n.-tuple T)
  (f : 'I_n -> T) (injf : injective f) (fint : forall i : 'I_n, f i \in t) g :
  g \in t -> exists i : 'I_n, f i = g.
Proof.
suff <- : codom f =i t by case/codomP => i ->;  exists i. 
have [|y /codomP[i ->]//||//] := uniq_min_size _ (_ : {subset (codom f) <= t})  _.
  by rewrite map_inj_uniq // enum_uniq.
by rewrite size_map size_enum_ord size_tuple.
Qed.

Lemma find_first (T : eqType) (a : pred T) s s0 i : a (nth s0 s i) -> find a s <= i. 
Proof. by apply: contraTleq => lti; by rewrite before_find. Qed.

Lemma ltn_perm_iota s n i : 0 < n -> perm_eq s (iota 0 n) -> nth 0 s i < n.
Proof.
move=> lt0n p.
have [ltin|] := boolP (i < n); 
  last by rewrite -leqNgt => leni; rewrite nth_default // (perm_size p) size_iota.
move: (p) => /perm_mem /(_ (nth 0 s i)).
rewrite mem_iota leq0n add0n andTb => <-.
by rewrite mem_nth // (perm_size p) size_iota.
Qed.

End Utils.

Section Count.

Variable (T : eqType).

Lemma gt_count_rem(s s' : seq T) x : 
  count [pred x0 | x0 \notin s'] s <= count [pred x0 | x0 \notin s'] (rem x s) + 1. 
Proof.
have [xis|nxis] := boolP (x \in s); last by rewrite rem_id // addn1. 
rewrite count_rem xis andTb /=.
case: (x \notin s') => /=; last by rewrite subn0 addn1.
by rewrite -addnBn leq_addr.
Qed.

Lemma count_not_in (s s' : seq T) x :
  x \notin s -> count [pred x' | x' \notin x :: s'] s = count [pred x' | x' \notin s'] s. 
Proof.
move=> nxis.
apply: eq_in_count => i iis /=.
rewrite !inE negb_or eq_sym andb_idl // => _.
by rewrite (@contraNN _ _ _ nxis) // => /eqP ->.
Qed.

Lemma count_uniq_cons (s s' : seq T) x (u : uniq s) :
  x \in s -> x \notin s' ->
  count [pred x' | x' \notin s'] s = count [pred x' | x' \notin x :: s'] s + 1.
Proof. 
move=> xis nxis'.
elim: s u xis => [//=|a s IH /= /andP [nais u]].  
rewrite !inE => /orP [/eqP eqxa|xias].
- rewrite eqxa in nxis' *.  
  by rewrite eq_refl orTb /= add0n nxis' /= count_not_in // addnC.
- have [ais' /=|nais' /=] := boolP (a \in s'); first by rewrite orbT /= !add0n IH.
  by rewrite orbF IH // (@contraNN _ _ _ nais) // => /eqP ->.
Qed.

Lemma count_remR (s s' : seq T) x (u : uniq s) (xis : x \in s) :
  count [pred x0 | x0 \notin x :: s'] s = count [pred x0 | x0 \notin s'] (rem x s).
Proof. 
rewrite count_rem /= xis andTb.
have [nxis' /=|] := boolP (x \notin s');
  first by rewrite [in RHS](@count_uniq_cons _ _ x) // -subnBA //= subnn subn0.
rewrite negbK /= subn0 => xis'. 
apply: eq_in_count => i iis /=. 
rewrite !inE negb_or andb_idl //. 
by apply: contraNN => /eqP ->.
Qed.  

Lemma count_remL (s s' : seq T) x : 
  x \notin s -> count [pred x0 | x0 \notin rem x s'] s = count [pred x0 | x0 \notin s'] s.
Proof.
move=> nxis.
apply: eq_in_count => i iis /=. 
congr (~~ _).
elim: s' => [//=|a s' IH /=]. 
rewrite !inE.
case: ifP => [/eqP eqax|neax]; last by rewrite in_cons IH. 
have [/eqP eqia|] := boolP (i == a); last by rewrite orFb. 
rewrite ?eqia ?eqax in iis nxis.
by rewrite iis in nxis.
Qed.

Lemma count_cons : forall (s s' : seq T) x' (u : uniq s),
    size s' < size s -> 
    (count [pred x | x \notin s'] s).-1 <= count [pred x | x \notin x' :: s'] s.
Proof.
elim=> [s x' //= us sz|x s IH s' x' /= /andP [xns u] sz].
have [nexx'|eqxx'] := boolP (x != x'). 
- have -> //=: (x \notin x' :: s') = (x \notin s') by rewrite !inE -(@negbK (x == x')) nexx'.
  have [xns' /=| /= nxns'] := boolP (x \in s'). 
  - rewrite !add0n.   
    pose f (s' : seq T) := count [pred x0 | x0 \notin s'] s.
    have -> // : (f (rem x s')).-1 <= f (x' :: (rem x s')) -> (f s').-1 <= f (x' :: s'). 
      have -> : x' :: rem x s' = rem x (x' :: s'). 
        by rewrite rem_cons -(@negbK (x' == x)) eq_sym nexx'.  
      by rewrite /f !count_remL.
    rewrite /f (@IH (rem x s') x' u) // size_rem // -subn1 ltn_subLR 1?addnC ?addn1 //.
    by rewrite (@leq_ltn_trans (index x s')) // index_mem.
  - have [x'ns|nx'ns] := boolP (x' \in s); last by rewrite count_not_in. 
    by rewrite count_remR // addnC gt_count_rem.
- rewrite negbK in eqxx'.
  rewrite in_cons eqxx' orTb /= add0n. 
  have [xns' /=|] := boolP (x \notin s'); first by rewrite count_not_in // -(eqP eqxx').
  rewrite negbK ?add0n => xns' /=.
  by rewrite count_not_in ?leq_pred // -(eqP eqxx').
Qed.

Lemma count_not_in_uniq (s s' : seq T) : 
    uniq s -> size s' < size s -> size s - size s' <= count [pred x | x \notin s'] s.
Proof.
elim: s' s => [s /=|x' s' IH' /= s us sz]; first by rewrite subn0 count_predT.  
rewrite subnS (@leq_trans (count [pred x | x \notin s'] s).-1) //;
        first by rewrite -!subn1 leq_sub2r // IH' // (ltn_trans _ sz).   
by rewrite count_cons // (leq_ltn_trans _ sz).
Qed.

Lemma find_not_in_uniq (s s' : seq T) :
  uniq s -> size s' < size s -> find [pred x | x \notin s'] s < size s.
Proof.
move=> u sz.
rewrite -has_find /= has_count.
by rewrite (@leq_trans (size s - size s')) ?count_not_in_uniq ?uniq_pref // subn_gt0.
Qed.

End Count.

Section SequentialDictator.

(* n agents. *)

Variable (n' : nat).

Let n := n'.+1.

Notation agent := (agent.type n).

(* n items from G. *)

Variable (G : eqType).

Variable (g0 : G).

Variable all_items : n.-tuple G.

Variable uniq_all_items : uniq all_items.

Variable no_g0 : g0 \notin all_items.

(* An agent's preference as a (strictly) decreasing-ordered list of items. *)

Record order := 
  Order {
      gt : rel G;
      tr : transitive gt;
      ir : irreflexive gt;
      to : total gt;
    }.

Definition index_ordered o gs := forall (i1 i2 : 'I_n), i1 < i2 -> gt o (tnth gs i1) (tnth gs i2).

Record pref := 
  Pref {
      items :> n.-tuple G;
      o : order;
      _ : perm_eq items all_items;
      _ : index_ordered o items;
    }.

(* The pref for each agent, seen as a nat, for historical reasons. *)

Definition prefs := nat -> pref. 

Variable ps : prefs.

Section Algorithm.

(* SD allocation of (item g : G, l : seq G) for agent a.
   - l is the trail of already allocated items
   - b finds the best item not already in a trail for an agent. *)

Fixpoint wins_alloc (a : nat) b : G * seq G :=
  match a with
  | 0 => let g := b a [::] in
        (g, [:: g])
  | a'.+1 => let gl := wins_alloc a' b in
            let l := gl.2 in 
            let g := b a l in
            (g, g :: l)
  end.

Definition best_item (s : seq G) (l : seq G) : G := nth g0 s (find [pred g | g \notin l] s).

Notation b := (best_item \o ps).

Definition wins (a : agent) := (wins_alloc a b).1. 
Definition alloc (a : agent) := (wins_alloc a b).2.

End Algorithm.

Section Properties.

Lemma pref_uniq (p : pref) : uniq p.
Proof.   
case: p => t [rp tr ir totr] prm sorted /=.  
by rewrite (perm_uniq prm) uniq_all_items.
Qed.

Lemma no_g0_pref (p : pref) i : i < n -> g0 != nth g0 p i.
Proof.
move=> ltin.
case: p => s o p' r /=.
apply: (@contraNN _ _ _ no_g0) => /eqP eqg0.
by rewrite (@perm_mem _ all_items s) 1?perm_sym // eqg0 mem_nth // size_tuple.
Qed.

Lemma alloc_size (a : agent) : size (alloc a) = a.+1.
Proof. by case: a; elim=> [//=|a IH /= lta1n]; rewrite (IH (ltn_trans (ltnSn a) lta1n)). Qed.

Lemma wins_in_items (a : agent) : wins a \in all_items. 
Proof.
case: a.
elim => [lt0|a IH /= lta1n].
- rewrite /wins /best_item /= find_predT.   
  case: (ps 0) => s0 _ /perm_iotaP rw0 _ /=.
  move: (rw0 g0) => [i0 p0] ->. 
  rewrite (nth_map 0) ?(perm_size p0) ?size_iota ?size_tuple //.
  move: (memPn no_g0 (nth g0 all_items (nth 0 i0 0))). 
  rewrite memt_nth // ltn_perm_iota //.
  by rewrite size_tuple in p0. 
- rewrite /wins /= /best_item.
  case: (ps a.+1) => s o p' r /=.
  rewrite (@perm_mem _ all_items s) 1?perm_sym // mem_nth // find_not_in_uniq //. 
  rewrite (perm_uniq p') uniq_all_items //. 
  have ltan : a < n by rewrite (ltn_trans (ltnSn a)).
  by rewrite (alloc_size (Ordinal ltan)) /= size_tuple.
Qed.

Lemma best_item_not_in (s : seq G) (l : seq G) : 
  g0 \notin l -> best_item s l \notin l.
Proof. by rewrite /best_item /find => g0l; elim: s => [//=|g' s' IH]; case: ifP. Qed.

Notation b := (best_item \o ps).

Lemma wins_not_alloc (a : agent) : 
  g0 \notin alloc a /\ (0 < a -> wins a \notin (wins_alloc a.-1 b).2).
Proof.
case: a.
elim=> [lt0n //=|a /= IH lta1n];
      first by split=> //=; first by rewrite /alloc /best_item /= find_predT inE no_g0_pref.  
have ltan : a < n by rewrite (ltn_trans (ltnSn a)).
split=> [|_]; last by rewrite /wins /= best_item_not_in //; move: (IH ltan) => [->].
rewrite /alloc /wins_alloc /= in_cons negb_or. 
apply/andP; split; last by move: (IH ltan) => [->].
rewrite no_g0_pref //.
have {3}-> : n = size (ps a.+1) by rewrite size_tuple.
rewrite find_not_in_uniq // ?pref_uniq ?uniq_all_items //.
by rewrite (alloc_size (Ordinal ltan)) /= size_tuple.
Qed.

Lemma pred_wins_in_alloc (a : agent) : forall (a' : agent), a' < a -> wins a' \in alloc a.
Proof.
case: a.
elim=> [lt0n //=|a /= IH lta1n a' lta'a1].
have ltan : a < n by rewrite (ltn_trans (ltnSn a)).
- have [/eqP -> |] := boolP (a' == (Ordinal ltan)).
  rewrite /wins /= /alloc /= in_cons.
  apply/orP; right.
  have [/eqP -> /= |] := boolP (a == 0); first by rewrite inE.
  rewrite -lt0n => /prednK <-.
  by rewrite in_cons eq_refl orTb.
- rewrite /alloc -(inj_eq val_inj) /= => nea'a.
  rewrite in_cons IH // ?orbT //. 
  by rewrite ltnS leq_eqVlt -(@negbK (val a' == a)) /= nea'a orFb in lta'a1.
Qed. 

Lemma pred_wins_diff (a : agent) : forall (a' : agent), a' < a -> wins a != wins a'.
Proof.
case: a. 
case=> [lt0n //=|a /= lta1n a' lta'a1].
have ltan : a < n by rewrite (ltn_trans (ltnSn a)).  
set oa1 := Ordinal lta1n; set oa := Ordinal ltan. 
- have [/eqP -> |] := boolP (a' == oa). 
  move: (wins_not_alloc oa1) => [_ /(_ erefl)].
  apply: contraNneq => -> /=.
  rewrite /wins /=.
  have [/eqP -> /=|] := boolP (a == 0); first by rewrite inE eq_refl.
  rewrite -lt0n => lt0a. 
  by rewrite -(@prednK a) //= in_cons eq_refl orTb.
- rewrite /alloc -(inj_eq val_inj) /= => nea'a.
  move: (wins_not_alloc oa1) => [_ /(_ erefl)].
  apply: contraNneq => -> /=.
  rewrite /wins /=. 
  have lt0a : 0 < a.
    move: lta'a1; rewrite ltnS leq_eqVlt -(@negbK (val a' ==  a)) nea'a /= => lta'a.
    by rewrite (@leq_ltn_trans a' 0).  
  move: (@pred_wins_in_alloc oa a') => /=.
  rewrite /wins /alloc => -> //.
  by move: lta'a1; rewrite ltnS leq_eqVlt -(@negbK (val a' == a)) /= nea'a orFb.
Qed.

Lemma wins_inj : injective wins. 
Proof.
move=> i j. 
wlog ltji: i j / j < i; last by apply: contra_eq; rewrite pred_wins_diff.
move: (leq_total j i) => /orP [];
  first by rewrite leq_eqVlt => /orP [/eqP/val_inj -> //|ltji]; apply.
by rewrite leq_eqVlt => /orP [/eqP/val_inj -> //|ltij /(_ j i ltij) eqw /esym /eqw ->]. 
Qed.

Lemma wins_surj (g : G) (ga : g \in all_items) : exists a, wins a = g.  
Proof. exact: (@f_surj _ _ all_items _ wins_inj wins_in_items). Qed.

End Properties.

End SequentialDictator.

Variable (G : finType) (g0 : G).

Variable (n' : nat).
Definition n := n'.+1.

Notation agent := 'I_n.

Variable (a : agent).

Variable all_items : n.-tuple G.

Variable uniq_all_items : uniq all_items.

Variable no_g0 : g0 \notin all_items.

Notation "'prefs" := (@prefs n' _ all_items).

Definition differ_on (ps1 ps2 : 'prefs) a := forall (j : agent), j != a -> ps1 j = ps2 j.

Lemma eq_wins_alloc_with_diff (ps1 ps2 : 'prefs) (a : agent) (d : differ_on ps1 ps2 a) : 
  let walloc a ps := wins_alloc a ((best_item g0) \o ps) in
  forall (j : agent), j < a -> walloc j ps1 = walloc j ps2.
Proof. 
move=> /= j ltja. 
rewrite /wins.
pose b (ps : 'prefs) := (best_item g0) \o ps; pose walloc a ps := wins_alloc a (b ps).
have bb: forall j, j < a -> b ps1 j = b ps2 j. 
  move=> k ltka; rewrite /b /=. 
  pose k' := Ordinal (ltn_trans ltka (ltn_ord a)).
  by rewrite (d k') //= -(inj_eq val_inj) /= (ltn_eqF ltka).
have/(_ a bb j ltja) : forall a (bb : forall j, j < a -> b ps1 j = b ps2 j) j, 
    j < a -> walloc j ps1 = walloc j ps2. 
  elim; first by move=> bb' j'.
  move=> a' IH bb' j' ltj'a'1. 
  have [/eqP -> |] := boolP (j' == 0); first by rewrite /walloc /wins_alloc bb'.
  rewrite /walloc in IH *. 
  rewrite -lt0n => lt0j'. 
  rewrite -{1 2}(@prednK j') //=. 
  have bb'' k (ltka' : k < a') : b ps1 k = b ps2 k by rewrite bb' // (@ltn_trans a').
  have ltj'1a' : j'.-1 < a' by rewrite prednK -ltnS.
  move: (IH bb'' j'.-1 ltj'1a').
  by rewrite [LHS]surjective_pairing [RHS]surjective_pairing bb' // => [] [] _ ->. 
by rewrite 2?surjective_pairing.
Qed.

Lemma eq_alloc_with_diff (ps1 ps2 : 'prefs) (a : agent) (d : differ_on ps1 ps2 a) : 
  forall (j : agent), j < a -> alloc g0 ps1 j = alloc g0 ps2 j.
Proof.
move=> j ltja.
move: (eq_wins_alloc_with_diff d ltja). 
by rewrite [LHS]surjective_pairing [RHS]surjective_pairing /alloc => [] [] _ ->.
Qed.

(* An action by an agent is his preference, i.e., an ordered list of items. *)

Notation mpref := (@pref n' _ all_items).

Definition A := mpref.

Variable p0 : A.

(* An outcome in O is a preference perfO of the dictator, i.e., a n.-tuple of won items
   among all_items, one for each agent, taken from all the mprefs. *)

Definition O := mpref.

Definition itemsO (ps : n.-tuple A) := map_tuple (wins g0 (tnth ps \o inord)) (agent.agents n).

Notation w_in_items := (wins_in_items uniq_all_items no_g0).

Lemma permO ps : perm_eq (itemsO ps) all_items.
Proof.
rewrite uniq_perm ?uniq_all_items // => [|g].
- rewrite /itemsO.
  apply/(tuple_uniqP g0) => i j . 
  rewrite !(tnth_nth g0) /= !(nth_map ord0) -?enumT ?nth_ord_enum ?size_enum_ord ?ltn_ord //.
  exact: (wins_inj uniq_all_items no_g0). 
- apply/(nthP g0)/(nthP g0) => [[i ltin na]|[i ltin na]]. 
  - rewrite size_tuple in ltin.
    exists (index g all_items); 
      last by rewrite nth_index // -na /itemsO /= (nth_map ord0) ?size_enum_ord // w_in_items.
    rewrite size_tuple -na /itemsO /= (nth_map ord0) ?size_enum_ord //.
    by rewrite -[X in _ < X](size_tuple all_items) index_mem w_in_items.
  - rewrite ?size_map -?enumT ?size_enum_ord size_tuple in ltin *.  
    have ga  : g \in all_items by apply/(nthP g0); exists i => //; rewrite size_tuple. 
    move: (wins_surj uniq_all_items no_g0 (tnth ps \o inord)) => /(_ g ga) [a pa].
    exists a; rewrite ?ltn_ord //.
    by rewrite /itemsO /= (nth_map ord0) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.    

Variable oO : order G.

Variable ordered_oO : forall ps, index_ordered oO (itemsO ps).

Definition prefO (ps : n.-tuple A) := Pref (permO ps) (ordered_oO ps).

(* SD as a mechanism. *)

Let m : mech.type n := mech.new prefO.

Variable vs : agent -> A.

Definition mps := mech.prefs.new vs (fun a (o : mech.O m) => n - index (tnth o a) (vs a)) vs.

Definition U := prefs.U mps.

Lemma order_compatible_utility a (s s' : mech.O m) : 
  U a s' < U a s -> gt (o (vs a)) (tnth s a) (tnth s' a).
Proof.
rewrite /U /=. 
case: (vs a) => sva ov pv rv. 
have ltta : forall (t : mech.O m), index (tnth t a) sva < n.
  move=> t.
  have -> : n = size sva by rewrite size_tuple.
  case: t => ss os /= ps _. 
  rewrite -(perm_sym all_items ss) in ps.
  by rewrite index_mem (perm_mem pv) (perm_mem ps) mem_tnth.
have lta /= : index (tnth s a) sva < n by []. 
have lta' /= : index (tnth s' a) sva < n by [].
have [/eqP ->|nei] := boolP (index (tnth s' a) sva == index (tnth s a) sva);
                      first by rewrite ltnn. 
rewrite ltn_neqAle subnKK // ?nei ?leq_sub2lE // 1?(@ltnW _ n) // leq_eqVlt => /orP [/eqP eqii|].
- by rewrite eqii eq_refl in nei.
- move/(@rv (Ordinal lta) (Ordinal lta')) => /=. 
  by do 2 rewrite !(tnth_nth g0) /= nth_index -?index_mem ?size_tuple //.
Qed.

Lemma uniq_pref (p : A) : uniq p.
Proof. by rewrite pref_uniq // uniq_all_items. Qed.

Lemma leq_index_vs (ps ps' : n.-tuple A) (a : agent) (lt0a : 0 < a) :
  let: b := best_item g0 \o (tnth ps \o inord) in
  let: l := (wins_alloc a.-1 b).2 in
  index (best_item g0 (vs a) l) (vs a) <= index (best_item g0 (tnth ps' a) l) (vs a).
Proof.
set l := (wins_alloc _ _).2.
have szn : size l < n.
  have lta1 : a.-1 < n by rewrite (@ltn_trans a) // ltn_predL.
  by rewrite (@leq_ltn_trans a) // (alloc_size g0 (tnth ps \o inord) (Ordinal lta1)) ltn_predL.
rewrite /best_item ?index_uniq ?uniq_pref //; 
  last by rewrite find_not_in_uniq ?uniq_pref // size_tuple. 
case: (vs a) => sv ov pv rv. 
case: (tnth ps' a) => sp' op' pp' tp' /=.
have usv : uniq sv by rewrite (perm_uniq pv) // uniq_all_items. 
have/(perm_trans pp')/(perm_iotaP g0) [ip' pip' ->]: perm_eq all_items sv 
  by rewrite (perm_sym all_items sv). 
rewrite size_tuple in pip'.
rewrite (nth_map 0).
- set i' := (nth 0 _ _). 
  have szi' : i' < size sv by rewrite (perm_size pv) size_tuple ltn_perm_iota.
  rewrite (@index_uniq _ g0 i' sv) // (@find_first _ _ _ g0) //= /i' find_map /preim //=.
  have <- : forall x, [pred x | nth g0 sv x \notin l] x = (nth g0 sv x \notin l) by [].
  rewrite nth_find //.
  apply/hasP => /=. 
  pose f (ps : n.-tuple A) := (tnth ps) \o inord.
  exists (index (@wins _ _ g0 all_items (f ps) a) sv) => /=.      
  - rewrite (perm_mem pip') mem_iota leq0n andTb add0n.
    by rewrite -{2}(size_tuple sv) index_mem (perm_mem pv) w_in_items.
  - rewrite nth_index; first by move: (wins_not_alloc uniq_all_items no_g0 (f ps) a) => [_ ->].
    by rewrite (perm_mem pv) w_in_items. 
- rewrite -(size_map (nth g0 sv)) find_not_in_uniq //= ?(@perm_uniq _ _ sv) ?usva //. 
  apply/(perm_iotaP g0); exists ip' => //; rewrite size_tuple //.
  by rewrite size_map (perm_size pip') size_iota.
Qed.
 
Lemma truthful_SD : truthful mps.
Proof.
move => ps ps' a d tv /=.   
rewrite /action_on /prefs.v /= in tv. 
rewrite leq_sub2l //= !(tnth_nth g0) !(nth_map ord0) -?enumT ?size_enum_ord ?ltn_ord //. 
rewrite !nth_ord_enum -tv /wins. 
case: a d tv => a. 
have [/eqP -> lt0n d tv|] := boolP (a == 0);
  first by rewrite /best_item /= !find_predT !(tnth_nth p0) /=
                   !inordK // !index_uniq ?size_tuple ?uniq_pref. 
rewrite -lt0n => lt0a ltan d tv.  
rewrite !(tnth_nth p0) /= -(@prednK a) //=.
set l := (wins_alloc _ _).2; set l' := (wins_alloc _ _).2.  
have lta1n : a.-1 < n by rewrite (@leq_ltn_trans a) ?leq_pred.
pose oa := Ordinal ltan; pose oa1 := Ordinal lta1n.
pose f (ps : n.-tuple A) := tnth ps \o inord.
have d' : differ_on (f ps) (f ps') oa.
  move=> j /= neq.
  rewrite /mech.differ_on /action_on in d.
  by rewrite /f /= d // -(inj_eq val_inj) /= inordK. 
move: (@eq_alloc_with_diff (f ps) (f ps') oa d' oa1). 
rewrite /alloc /l' (prednK lt0a) ?leqnn // => <- //.
have [/eqP -> //=|nenil] := boolP (l == [::]);
  first by rewrite /best_item /= !find_predT !(tnth_nth p0) /= inordK // 
                   index_uniq // ?uniq_pref ?size_tuple.
have inK : forall ps, tnth ps (inord a) = tnth ps oa.
  by move=> ? ?; congr tnth; apply: val_inj => /=; rewrite inordK. 
by rewrite !inK -(@tnth_nth _ _ _ _ oa) !tv leq_index_vs.
Qed.

Check truthful_SD.
Print Assumptions truthful_SD.

(* SD as a matching mechanism. *)

Definition set_items := [set i in all_items].

Lemma no_g0' : g0 \notin set_items. 
Proof. by rewrite in_set no_g0. Qed.

Definition oO' : matching.order G := matching.Order (@tr _ oO) (ir oO) (to oO).

Let O' := matching.pref set_items n.

Notation A' := O'.

Definition itemsO' (ps' : n.-tuple A') :=
  map_tuple (fun i : agent => 
               (wins_alloc i (best_item g0 \o (fun j => (matching.items (tnth ps' (inord j)))))).1) 
            (agent.agents n).

Variable AofA' : forall (ps' : n.-tuple A'), n.-tuple A. 
Variable A'ofA : forall (ps : n.-tuple A), n.-tuple A'.

Lemma all_items_in_set (ps' : n.-tuple A') (i : agent) : 
  tnth (itemsO' ps') i \in set_items. 
Proof.
rewrite tnth_map tnth_ord_tuple in_set.
move: (wins_in_items uniq_all_items no_g0 (fun i => tnth (AofA' ps') (inord i)) i).
rewrite /wins.
Admitted.

Lemma ordered_oO' ps' : @matching.index_ordered G n oO' (itemsO' ps').
Proof. 
rewrite /matching.index_ordered => i1 i2 /andP [lt12 sz]. 
rewrite size_tuple in sz. 
have l1n : i1 < n by rewrite (@ltn_trans i2). 
move: (@ordered_oO (AofA' ps') (Ordinal l1n) (Ordinal sz)) => /(_ lt12) /=.
rewrite /itemsO' !tnth_map /wins /=.
Admitted.

Variable uniq_itemsO' : forall ps', uniq (itemsO' ps').

Definition perfO' (ps' : n.-tuple A') := 
  matching.Pref (uniq_itemsO' ps') (all_items_in_set ps') (@ordered_oO' ps').

Let m' := mech.new perfO'.

Let g' (o' : mech.O m') (i : agent.type n) := Some (tnth (matching.items o') i).

Let m'' : @matching.type n G set_items n := matching.new g'.

Let v'' : agent.type n -> matching.pref set_items n :=
      fun i => matching.Pref (uniq_itemsO' (A'ofA (mktuple vs)))
                          (all_items_in_set (A'ofA (mktuple vs)))
                          (@ordered_oO' (A'ofA (mktuple vs))).

Lemma is_U_order_compatible a (s s' : mech.O m'') : 
    matching.U v'' a s' < matching.U v'' a s -> 
    gt (o (vs a)) (tnth (matching.items s) a) (tnth (matching.items s') a).
Proof.
move=> ltUU.
have s'av'' : tnth (matching.items s') a \in matching.items (v'' a) by admit.
move: (matching.utility_is_order_compatible no_g0' ltUU s'av'') => /=.
case: (o (vs a)) => go tro iro too /=.
Admitted.

