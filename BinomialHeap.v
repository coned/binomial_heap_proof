Require Import List.
Import ListNotations.
Import Nat.
Require Import Coq.Sorting.Sorted.
Require Import Relation_Definitions.
Import Coq.Relations.Relation_Operators.

Variable INF : nat.

Inductive BiT : Type :=
Node (v:nat) | Comb (bt1:BiT) (bt2:BiT).

Definition BiH : Type := list BiT.
Definition empty_heap : BiH := [].

Definition BiHO : Type := list (option BiT).
Definition none_tree : option BiT := None.

Fixpoint root (t:BiT) :=
match t with
| Node v => v
| Comb bt1 _ => root bt1
end.

Fixpoint order (t:BiT) :=
match t with
| Node _ => 0
| Comb bt1 _ => order bt1
end.

Definition combineTree (bt1:BiT) (bt2:BiT)
:= if (root bt1) <? (root bt2)
   then Comb bt1 bt2
   else Comb bt2 bt1.

Inductive sim_order: BiH -> BiHO -> Prop :=
| simo_nil: sim_order [] []
| simo_some (bt:BiT) (bh:BiH)
    (bho:BiHO) (E: sim_order bh bho): sim_order (bt::bh) ((Some bt)::bho)
| simo_none (bh:BiH) (bho:BiHO) (E: sim_order bh bho): sim_order bh (none_tree::bho).

Inductive sim_place (n:nat) : BiHO -> Prop :=
| simp_nil: sim_place n []
| simp_none (bho:BiHO) (E: sim_place (S n) bho): sim_place (n) (none_tree::bho)
| simp_some (bt:BiT) (bho:BiHO) (E0: sim_place (S n) bho) (E1: order bt = n):
      sim_place n ((Some bt)::bho).

Inductive sim_high_some : BiHO -> Prop :=
| high_one (bt:BiT): sim_high_some [(Some bt)]
| high_more (p:option BiT) (bho:BiHO) (E: sim_high_some bho): sim_high_some (p::bho).

Inductive sim_high : BiHO -> Prop := 
| high_nil : sim_high []
| high_some (bho:BiHO) (E: sim_high_some bho) : sim_high bho.

Definition sim (bh: BiH) (bho: BiHO) := (sim_order bh bho) /\ (sim_place 0 bho) /\ (sim_high bho).

Fixpoint mergeTreeO (bt:option BiT) (o:BiHO) : BiHO :=
match bt with 
| None => o
| Some b => match o with 
    | nil => [bt]
    | h::t => match h with 
        | None => bt::t
        | Some h' => mergeTreeO (Some (combineTree h' b)) t
        end
    end
end.

Fixpoint mergeHeapOption (p: option BiT) (b1 b2: BiHO):BiHO:=
match p, b1, b2 with
| None, [], _ => b2
| None, _, [] => b1
| Some bt, [], [] => [p]
| Some bt, (Some h1)::t1, [] => none_tree::(mergeTreeO (Some (combineTree bt h1)) t1)
| Some bt, [], (Some h2)::t2 => none_tree::(mergeTreeO (Some (combineTree bt h2)) t2)
| Some bt, None::t1, [] => p::t1
| Some bt, [], None::t2 => p::t2
| _, None::t1,     None::t2 => p::(mergeHeapOption none_tree t1 t2)
| None, (Some h1)::t1, None::t2 => (Some h1)::(mergeHeapOption none_tree t1 t2)
| None, None::t1, (Some h2)::t2 => (Some h2)::(mergeHeapOption none_tree t1 t2)
| _, (Some h1)::t1, (Some h2)::t2 => p::(mergeHeapOption (Some (combineTree h1 h2)) t1 t2)
| Some bt, (Some h1)::t1, None::t2 => none_tree::(mergeHeapOption (Some (combineTree bt h1)) t1 t2)
| Some bt, None::t1, (Some h2)::t2 => none_tree::(mergeHeapOption (Some (combineTree bt h2)) t1 t2)
end.


Fixpoint mergeTree (bt:BiT) (bh:BiH) : BiH :=
match bh with
| [] => [bt]
| h::t => if (order bt <? order h)
             then (bt::bh)
             else if (order bt =? order h)
                  then mergeTree (combineTree bt h) t
                  else h::(mergeTree bt t)
end.

Inductive state :=
|stat: BiH->BiH->BiH->(option BiT)->state.

Inductive merge_alg: state -> state -> Prop :=
|alg_san (v:BiT) (bh1:BiH) (c:BiH):
    merge_alg (stat bh1 [] c (Some v)) (stat [] [] (c ++ (mergeTree v bh1)) none_tree)
|alg_sna (v:BiT) (bh2:BiH) (c:BiH):
    merge_alg (stat [] bh2 c (Some v)) (stat [] [] (c ++ (mergeTree v bh2)) none_tree)
|alg_nna (bh2:BiH) (c:BiH):
    merge_alg (stat [] bh2 c none_tree) (stat [] [] (c ++ bh2) none_tree)
|alg_nan (bh1:BiH) (c:BiH):
    merge_alg (stat bh1 [] c none_tree) (stat [] [] (c ++ bh1) none_tree)
|alg_nss0 (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (c:BiH) (E: order h1 = order h2):
    merge_alg (stat (h1::t1) (h2::t2) c none_tree) (stat t1 t2 c (Some (combineTree h1 h2)))
|alg_nss1 (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (c:BiH) (E: order h1 < order h2):
    merge_alg (stat (h1::t1) (h2::t2) c none_tree) (stat t1 (h2::t2) (c ++ [h1]) none_tree)
|alg_nss2 (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (c:BiH) (E: order h1 > order h2):
    merge_alg (stat (h1::t1) (h2::t2) c none_tree) (stat (h1::t1) t2 (c ++ [h2]) none_tree)
|alg_sss0 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (c:BiH) (E: order h1 = order h2):
    merge_alg (stat (h1::t1) (h2::t2) c (Some v)) (stat t1 t2 (c ++ [v]) (Some (combineTree h1 h2)))
|alg_sss1 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (c:BiH)
          (E0: ~ order h1 = order h2) (E1: order v = order h1):
    merge_alg (stat (h1::t1) (h2::t2) c (Some v)) (stat t1 (h2::t2) c (Some (combineTree v h1)))
|alg_sss2 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (c:BiH)
          (E0: ~ order h1 = order h2) (E1: ~ order v = order h1) (E2: order v = order h2):
    merge_alg (stat (h1::t1) (h2::t2) c (Some v)) (stat (h1::t1) t2 c (Some (combineTree v h2)))
|alg_sss3 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (c:BiH)
          (E0: ~ order h1 = order h2) (E1: ~ order v = order h1) (E2: ~ order v = order h2):
    merge_alg (stat (h1::t1) (h2::t2) c (Some v)) (stat (h1::t1) (h2::t2) (c ++ [v]) none_tree).

(*
Fixpoint mergeHeap' (p:option BiT) (bh1:BiH) (bh2:BiH) :=
match p, bh1, bh2 with
| None, [], [] => []
| Some v, _,[] => mergeTree v bh1
| Some v, [],_ => mergeTree v bh2
| None, [], _  => bh2
| None, _, []  => bh1
| None, h1::t1, h2::t2 => if (order h1 =? order h2)
                          then mergeHeap' (Some (combineTree h1 h2)) t1 t2
                          else if (order h1 <? order h2)
                               then h1::(mergeHeap' None t1 bh2)
                               else h2::(mergeHeap' None bh1 t2)
| Some v,h1::t1,h2::t2 => if (order h1 =? order h2)
                          then v::(mergeHeap' (Some (combineTree h1 h2)) t1 t2)
                          else if (order v =? order h1)
                               then mergeHeap' (Some (combineTree h1 v)) t1 bh2
                               else if (order v =? order h2)
                                    then mergeHeap' (Some (combineTree h2 v)) bh1 t2
                                    else v::(mergeHeap' None bh1 bh2)
end.
*)

Definition insert (v:nat) (bh:BiH) : BiH := mergeTree (Node v) bh.

Fixpoint findMin (bh:BiH) :=
match bh with
| [] => INF
| t::h => min (root t) (findMin h)
end.
(*
Fixpoint delMinInTree (bt:BiT) :=
match bt with
| Node _ => []
| Comb _ _ bt1 bt2 => delMinInTree bt1 ++ [bt2]
end.

Fixpoint delMin (bh:BiH) :=
match bh with
| [] => (INF, [])
| t::h => if (root t) <? (fst (delMin h))
          then (root t, mergeHeap (delMinInTree t) h)
          else (fst (delMin h), t::(snd (delMin h)))
end.
*)

Inductive minHeap : BiT -> Prop :=
| Heap_0 (v: nat) : minHeap (Node v)
| Heap_n (t1: BiT) (t2: BiT) (E1: minHeap t1) (E2: minHeap t2) (E3: root t1 < root t2) :
        minHeap (Comb t1 t2).

Inductive orderEq : BiT -> Prop :=
| OE_0 (v:nat) : orderEq (Node v)
| OE_n (t1: BiT) (t2: BiT) (E1: orderEq t1) (E2: orderEq t2)
       (E3: order t1 = order t2) : orderEq (Comb t1 t2).

Definition BiTrue (bt:BiT) := minHeap bt /\ orderEq bt.

Definition orderBiT (bt1:BiT) (bt2:BiT) := lt (order bt1) (order bt2).
Definition orderedList (bh:BiH) := StronglySorted orderBiT bh.

Definition everyBiT (bh: BiH) := Forall BiTrue bh.

Definition BiHTure (bh:BiH) := orderedList bh /\ everyBiT bh.
(*
Theorem combine_binomial_tree: forall (t1 t2: BiT),
BiTrue t1 /\ BiTrue t2 /\ (order t1) = (order t2)
-> BiTrue (combineTree t1 t2) /\ (order (combineTree t1 t2)) = S (order t2).
Proof. Admitted.


Theorem mergeTree_is_BiH: forall (bt: BiT) (bh: BiH), BiTrue bt ->
BiHTrue bh -> BiHTrue (mergeTree bt bh).
Proof. Admitted.


Theorem insert_is_BiH: forall (v:nat) (bh:BiH), BiH bh -> BiH (insert v bh).
Proof. Admitted.

Theorem delMin_is_BiH: forall (bh:BiH), BiH bh -> BiH (snd (delMin bh)).
Proof. Admitted.
*)

Check clos_refl_trans.

Theorem merge_to_empty: forall (v:BiT) (a1 : BiH), mergeTree v a1 = [] -> False.
Proof.
intros.
generalize dependent v.
induction a1.
- intros. inversion H.
- intros. inversion H.
  destruct (order v <? order a).
  + inversion H1.
  + destruct (order v =? order a).
    * apply IHa1 in H1. apply H1.
    * inversion H1.
Qed.

Theorem sim_empty: forall (bh : BiHO), sim [] bh -> bh = [].
Admitted.

Theorem merge_alg_remain_correct: forall (p1 p2: option BiT) (a1 b1 a2 b2:BiH)
(a1' b1' a2' b2':BiHO) (s1 s2:state),
  s1 = stat a1 b1 nil p1 ->
  s2 = stat a2 b2 nil p2 ->
  merge_alg s1 s2 ->
  sim a1 a1' ->
  sim b1 b1' ->
  sim a2 a2' ->
  sim b2 b2' ->
  mergeHeapOption p1 a1' b1' = mergeHeapOption p2 a2' b2'.
Proof.
intros p1 p2 a1 b1 a2 b2 a1' b1' a2' b2' s1 s2.
intros H1 H2 H3 H4 H5 H6 H7.
rewrite H1 in H3. rewrite H2 in H3.
inversion H3.
- apply merge_to_empty in H13. destruct H13.
- apply merge_to_empty in H13. destruct H13.
- rewrite <- H0 in H4. rewrite H13 in H5.
  rewrite <- H in H6. rewrite <- H12 in H7.
  apply sim_empty in H4.
  apply sim_empty in H5.
  apply sim_empty in H6.
  apply sim_empty in H7.
  rewrite H4. rewrite H5. rewrite H6. rewrite H7. reflexivity.
- rewrite H13 in H4. rewrite <- H8 in H5.
  rewrite <- H in H6. rewrite <- H12 in H7.
  apply sim_empty in H4.
  apply sim_empty in H5.
  apply sim_empty in H6.
  apply sim_empty in H7.
  rewrite H4. rewrite H5. rewrite H6. rewrite H7. reflexivity.
- 

Admitted.

Theorem merge_alg_sing: forall (a b c : BiH) (a' b' c' : BiHO)
(x y : state),
x = stat a b [] none_tree ->
y = stat [] [] c none_tree ->
merge_alg x y ->
sim a a' ->
sim b b' ->
sim c c' ->
c' = mergeHeapOption none_tree a' b'.
Proof.
intros.
destruct H1.
- discriminate H.
- discriminate H.
- inversion H.
  inversion H0.
  Admitted.

Theorem sim_empty_heap: forall (a : BiHO), sim empty_heap a -> a = [].
Proof.
  intros a [H1 [H2 H3]].
  inversion H1.
  - reflexivity.
  - Admitted.

Theorem merge_alg_correct: forall (a b c:BiH) (a' b' c':BiHO) (s1 s2:state),
  s1 = stat a b nil none_tree ->
  s2 = stat nil nil c none_tree ->
  clos_refl_trans state merge_alg s1 s2 ->
  sim a a' ->
  sim b b' ->
  sim c c' ->
  c' = mergeHeapOption none_tree a' b'.
Proof.
intros a b c a' b' c' s1 s2.
intros Es1 Es2 H0 Ha Hb Hc.
induction H0.
- apply (merge_alg_sing a b c _ _ _ x y).
  auto. auto. auto. auto. auto. auto.
- rewrite Es2 in Es1.
  inversion Es1.
  rewrite <- H0 in Ha.
  rewrite <- H1 in Hb.
  rewrite -> H2 in Hc.
  apply sim_empty_heap in Ha.
  apply sim_empty_heap in Hb.
  apply sim_empty_heap in Hc.
  rewrite Ha. rewrite Hb. rewrite Hc.
  simpl. reflexivity.
- 










