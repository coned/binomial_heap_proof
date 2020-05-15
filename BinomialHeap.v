Require Import List.
Import ListNotations.
Import Nat.
Require Import Coq.Sorting.Sorted.

Variable INF : nat.

Inductive BiT : Type :=
Node (v:nat) | Comb (bt1:BiT) (bt2:BiT).

Definition BiH : Type := list BiT.
(*Definition empty_heap : BiH := [].*)

Definition BiHO : Type := list (option BiT).
Definition none_tree : option BiT := None.
(*
Inductive sim: BiH -> BiHO -> Prop :=
| sim_nil: sim [] []
| sim_some (bt:BiT) (bh:BiH)
    (bho:BiHO) (E: sim bh bho): sim (bt::bh) ((Some bt)::bho)
| sim_none (bh:BiH) (bho:BiHO) (E: sim bh bho): sim bh (none_tree::bho).
*)

(*
Inductive sim : BiH -> BiHO -> nat -> Prop :=
| sim_1 (n: nat): sim nil nil n
| sim_2 (n: nat) (h: bt) (t: BiH) (tail: BiHO):
    sim (h::t) tail (S n) -> sim (h::t) (None::tail) n
| sim_3 (n: nat) (h: bt) (t: BiH) (tail: BiHO) (b: bt):
    same b h /\ order b = n /\ sim t tail (S n) 
    -> sim (h::t) ((Some b)::tail) n.
*)

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
| _, (Some h1)::t1, (Some h2)::t2 => p::(mergeHeapOption none_tree t1 t2)
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
|alg_san (v:BiT) (bh1:BiH): merge_alg (stat bh1 [] [] (Some v)) (stat [] [] (mergeTree v bh1) none_tree)
|alg_sna (v:BiT) (bh2:BiH): merge_alg (stat [] bh2 [] (Some v)) (stat [] [] (mergeTree v bh2) none_tree)
|alg_nna (bh2:BiH): merge_alg (stat [] bh2 [] none_tree) (stat [] [] bh2 none_tree)
|alg_nan (bh1:BiH): merge_alg (stat bh1 [] [] none_tree) (stat [] [] bh1 none_tree)
|alg_nss0 (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (E: order h1 = order h2):
    merge_alg (stat (h1::t1) (h2::t2) [] none_tree) (stat t1 t2 [] (Some (combineTree h1 h2)))
|alg_nss1 (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (E: order h1 < order h2):
    merge_alg (stat (h1::t1) (h2::t2) [] none_tree) (stat t1 (h2::t2) [h1] none_tree)
|alg_nss2 (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (E: order h1 > order h2):
    merge_alg (stat (h1::t1) (h2::t2) [] none_tree) (stat (h1::t1) t2 [h2] none_tree)
|alg_sss0 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (E: order h1 = order h2):
    merge_alg (stat (h1::t1) (h2::t2) [] (Some v)) (stat t1 t2 [v] (Some (combineTree h1 h2)))
|alg_sss1 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH) (E0: ~ order h1 = order h2) (E1: order v = order h1):
    merge_alg (stat (h1::t1) (h2::t2) [] (Some v)) (stat t1 (h2::t2) [] (Some (combineTree v h1)))
|alg_sss2 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH)
          (E0: ~ order h1 = order h2) (E1: ~ order v = order h1) (E2: order v = order h2):
    merge_alg (stat (h1::t1) (h2::t2) [] (Some v)) (stat (h1::t1) t2 [] (Some (combineTree v h2)))
|alg_sss3 (v:BiT) (h1:BiT) (h2:BiT) (t1:BiH) (t2:BiH)
          (E0: ~ order h1 = order h2) (E1: ~ order v = order h1) (E2: ~ order v = order h2):
    merge_alg (stat (h1::t1) (h2::t2) [] (Some v)) (stat (h1::t1) (h2::t2) [v] none_tree).

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

(*maybe not every useful*)
(*
Inductive orderedList : BiH -> Prop :=
| OL_nil : orderedList []
| OL_one (bt: BiT) : orderedList [bt]
| OL_more (bt1:BiT) (bt2:BiT) (bh_tail:BiH)
          (E1: orderedList (bt2::bh_tail))
          (E2:order bt1 < order bt2) : orderedList (bt1::bt2::bh_tail).*)

Definition everyBiT (bh: BiH) := Forall BiTrue bh.

Definition BiH (bh:BiH) := orderedList bh /\ everyBiT bh.

Theorem combine_binomial_tree: forall (t1 t2: BiT),
BiT t1 /\ BiT t2 /\ (order t1) = (order t2)
-> BiT (combineTree t1 t2) /\ (order (combineTree t1 t2)) = S (order t2).
Proof. Admitted.

Theorem mergeTree_is_BiH: forall (bt: BiT) (bh: BiH), BiT bt ->
BiH bh -> BiH (mergeTree bt bh).
Proof. Admitted.

Theorem insert_is_BiH: forall (v:nat) (bh:BiH), BiH bh -> BiH (insert v bh).
Proof. Admitted.

Theorem delMin_is_BiH: forall (bh:BiH), BiH bh -> BiH (snd (delMin bh)).
Proof. Admitted.









