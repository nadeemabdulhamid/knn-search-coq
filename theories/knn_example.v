
(* data from https://www.listendata.com/2017/12/k-nearest-neighbor-step-by-step-tutorial.html *)

From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Bool.
From Coq Require Import Lists.List.
Import ListNotations.

From NN Require Import bounding_boxes.
From NN Require Import quick_select_partition.
From NN Require Import max_pqueue.
From NN Require Import kdtree.
From NN Require Import knn_search.

Module MaxPQ := List_MaxPQ NatTTLB.
Module KNNS_LPQ := KNNS MaxPQ.
Import KNNS_LPQ.

Definition
    data_table := 
    [ [158  ;58] ;
      [158  ;59] ;
      [158  ;63	] ;
      [160	;59	] ;
      [160	;60	] ;
      [163	;60	] ;
      [163	;61	] ;
      [160	;64	] ;
      [163	;64	] ;
      [165	;61	] ;
      [165	;62	] ;
      [165	;65	] ;
      [168	;62	] ;
      [168	;63	] ;
      [168	;66	] ;
      [170	;63	] ;
      [170	;64	] ;
      [170	;68] ].

Definition 
    data_tree := Eval cbv in (build_kdtree 2 data_table).


Definition 
    query := [ 161 ; 61 ].


Eval compute in (knn_search 5 2 data_tree query).
    
Eval compute in (knn_search 4 2 data_tree query).

Eval compute in (knn_search 6 2 data_tree query).




Check (proj1 (Nat.ltb_lt 0 5) (refl_equal _)).
Lemma valid_len
 :(forall v' : datapt, In v' data_table -> length v' = 2).
 simpl.
 intros v' H.
 repeat (destruct H as [ H | H]; [rewrite <- H; auto | ]).
 inversion H.
Qed.


Check (knn_search_build_kdtree_correct 5 2 data_table
    (proj1 (Nat.ltb_lt 0 5) (refl_equal _))
    (proj1 (Nat.ltb_lt 0 (length data_table)) (refl_equal _))
    (proj1 (Nat.ltb_lt 0 2) (refl_equal _))
    valid_len
    data_tree
    query
    (knn_search 5 2 data_tree query)
    (refl_equal _)
    (refl_equal _)).