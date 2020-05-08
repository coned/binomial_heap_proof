Require Import List.
Import ListNotations.
Import Nat.
Require Import Coq.Sorting.Sorted.

Variable INF : nat.

Inductive BinomialTree : Type :=
Node (v:nat) | Comb (r:nat) (o:nat) (bt1:BinomialTree) (bt2:BinomialTree).

Definition BinomialHeap : Type := list BinomialTree.
Definition EmptyHeap : BinomialHeap := [].

Definition BinomialHeapOption : Type := list (option BinomialTree).

Fixpoint root (t:BinomialTree) :=
match t with
| Node v => v
| Comb r _ _ _ => r
end.

Fixpoint order (t:BinomialTree) :=
match t with
| Node _ => 0
| Comb _ n _ _ => n
end.

Definition combineTree (bt1:BinomialTree) (bt2:BinomialTree)
:= if (root bt1) <? (root bt2)
   then Comb (root bt1) (S (order bt1)) bt1 bt2
   else Comb (root bt2) (S (order bt2)) bt2 bt1.

Fixpoint mergeTree (bt:BinomialTree) (bh:BinomialHeap) : BinomialHeap :=
match bh with
| [] => [bt]
| h::t => if (order bt <? order h)
             then (bt::bh)
             else if (order bt =? order h)
                  then mergeTree (combineTree bt h) t
                  else h::(mergeTree bt t)
end.

Fixpoint mergeHeap (bh1:BinomialHeap) (bh2:BinomialHeap) :=
match bh1 with
| [] => bh2
| h::t => mergeHeap t (mergeTree h bh2)
end.
(*
Fixpoint mergeHeap' (p:option BinomialTree) (bh1:BinomialHeap) (bh2:BinomialHeap) :=
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
Definition insert (v:nat) (bh:BinomialHeap) : BinomialHeap := mergeTree (Node v) bh.

Fixpoint findMin (bh:BinomialHeap) :=
match bh with
| [] => INF
| t::h => min (root t) (findMin h)
end.

Fixpoint delMinInTree (bt:BinomialTree) :=
match bt with
| Node _ => []
| Comb _ _ bt1 bt2 => delMinInTree bt1 ++ [bt2]
end.

Fixpoint delMin (bh:BinomialHeap) :=
match bh with
| [] => (INF, [])
| t::h => if (root t) <? (fst (delMin h))
          then (root t, mergeHeap (delMinInTree t) h)
          else (fst (delMin h), t::(snd (delMin h)))
end.

Inductive minHeap : BinomialTree -> Prop :=
| Heap_0 (v:nat) : minHeap (Node v)
| Heap_n (o:nat) (t1: BinomialTree) (t2:BinomialTree)
         (E1: minHeap t1) (E2: minHeap t2) (E3: root t1 < root t2) :
minHeap (Comb o (root t1) t1 t2).


Inductive orderEq : BinomialTree -> Prop :=
| OE_0 (v:nat) : orderEq (Node v)
| OE_n (r:nat) (t1: BinomialTree) (t2:BinomialTree) (E1: orderEq t1) (E2: orderEq t2)
       (E3: order t1 = order t2) : orderEq (Comb (S (order t1)) r t1 t2).

Definition BT (bt:BinomialTree) := minHeap bt /\ orderEq bt.

Definition orderBT (bt1:BinomialTree) (bt2:BinomialTree) := lt (order bt1) (order bt2).

Definition orderedList' (bh:BinomialHeap) := StronglySorted orderBT bh.
(*maybe not every useful*)

Inductive orderedList : BinomialHeap -> Prop :=
| OL_nil : orderedList []
| OL_one (bt: BinomialTree) : orderedList [bt]
| OL_more (bt1:BinomialTree) (bt2:BinomialTree) (bh_tail:BinomialHeap)
          (E1: orderedList (bt2::bh_tail))
          (E2:order bt1 < order bt2) : orderedList (bt1::bt2::bh_tail).

Definition everyBT (bh: BinomialHeap) := Forall BT bh.

Definition BH (bh:BinomialHeap) := orderedList bh /\ everyBT bh.

Theorem combine_binomial_tree: forall (t1 t2: BinomialTree),
BT t1 /\ BT t2 /\ (order t1) = (order t2)
-> BT (combineTree t1 t2) /\ (order (combineTree t1 t2)) = S (order t2).
Proof. Admitted.

Theorem mergeTree_is_BH: forall (bt: BinomialTree) (bh: BinomialHeap), BT bt ->
BH bh -> BH (mergeTree bt bh).
Proof. Admitted.

Theorem insert_is_BH: forall (v:nat) (bh:BinomialHeap), BH bh -> BH (insert v bh).
Proof. Admitted.

Theorem delMin_is_BH: forall (bh:BinomialHeap), BH bh -> BH (snd (delMin bh)).
Proof. Admitted.









