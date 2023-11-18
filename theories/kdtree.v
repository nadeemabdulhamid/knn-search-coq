From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Bool.
From Coq Require Import Lists.List.
Require Import Lia.
Import ListNotations.

From NN Require Import tactics.
From NN Require Import bounding_boxes.
From NN Require Import quick_select_partition.


Definition ith_leb (i:nat) (vs ws: list nat) : bool :=
    nth i vs 0 <=? nth i ws 0.


Inductive kdtree :=
| mt_tree : kdtree
| node : nat -> datapt -> kdtree -> kdtree -> kdtree.
(* the nat is the index of the axis on which this node splits *)

(*
Definition median_partition (data:list datapt) (depth_mod:nat) 
    : option (list datapt * datapt * list datapt) :=
    quick_select (div2 (length data)) data (ith_leb depth_mod).
*)

Compute (median_partition [ [50; 10]; [60; 10]; [70; 10]] (ith_leb 0)).

(* Compute (median_partition [ [1 ; 2; 3] ] 2). *)

Definition next_depth (k:nat) (d:nat) : nat :=
    if (k <=? d+1) then 0 else d+1.

Example ex1 : next_depth 5 4 = 0 := refl_equal.
Example ex2 : next_depth 5 2 = 3 := refl_equal.


(* k is the length of datapt lists *)
Fixpoint build_kdtree_ (fuel:nat) (k:nat) (data:list datapt) (depth_mod:nat) : kdtree :=
    match fuel with 
    | 0 => mt_tree (* case should never happen *)
    | S fuel' => 
        match data with
        | [] => mt_tree
        | _ => match median_partition data (ith_leb depth_mod) with
        | None => mt_tree
        | Some (sm, pvt, lg) =>
            node depth_mod pvt 
                (build_kdtree_ fuel' k sm (next_depth k depth_mod))
                (build_kdtree_ fuel' k lg (next_depth k depth_mod))
        end end
    end.

Definition build_kdtree (k:nat) (data:list datapt) : kdtree :=
    build_kdtree_ (length data) k data 0.

Definition 
    two_tree := Eval cbv in (build_kdtree 2 [ [5 ; 10] ; [4 ; 3] ; [8 ; 2] ; [7 ; 12] ; [5  ; 23] ; [9 ; 10] ]).

Print two_tree.

Fixpoint kdtree_bounded (tree:kdtree) (bb:bbox) : bool :=
    match tree with
    | mt_tree => true
    | node ax pt lft rgt => 
        bb_contains bb pt
         && kdtree_bounded lft (fst (bb_split bb ax (nth ax pt 0)))
         && kdtree_bounded rgt (snd (bb_split bb ax (nth ax pt 0)))
    end.

Example ex3 : (kdtree_bounded two_tree (mk_bbox [None ; None] [None ; None]))=true := refl_equal.
Example ex4 : (kdtree_bounded two_tree (mk_bbox [Some 7 ; None] [None ; None]))=false := refl_equal.
Example ex5 : (kdtree_bounded two_tree (mk_bbox [Some 3 ; None] [None ; None]))=true := refl_equal.
Example ex6 : (kdtree_bounded two_tree (mk_bbox [Some 3 ; Some 1] [Some 15 ; Some 25]))=true := refl_equal.
Example ex7 : (kdtree_bounded two_tree (mk_bbox [Some 3 ; Some 1] [Some 15 ; Some 20]))=false := refl_equal.


Lemma le_props_ith_leb : forall depth_mod, le_props (ith_leb depth_mod).
Proof.
    repeat split; intros.
    unfold ith_leb in *; rewrite Nat.leb_le in *; lia.
    unfold ith_leb in *; repeat rewrite Nat.leb_le; lia.
Qed.

Lemma length_div_2 : forall A (h:A) t, div2 (length (h :: t)) < length (h :: t).
Proof.
    induction t; auto.
    simpl. 
    simpl length in IHt.
    destruct (length t); auto.
    simpl in IHt.
    generalize (Nat.le_div2 n); intros.
    lia.
Qed.



Lemma next_depth_lt : forall k d, 0 < k -> next_depth k d < k.
Proof.
    intros; unfold next_depth.
    destruct (k <=? d + 1) eqn:He.
    apply Nat.leb_le in He; lia.
    apply leb_complete_conv in He; auto.
Qed.

Lemma all_ubd_update :
    forall v' i v bb_max,
        all_ubd v' bb_max = true ->
        (nth i v' 0 <=? nth i v 0) = true ->
        all_ubd v' (list_set bb_max i (Some (nth i v 0))) = true.
Proof.
    induction v'; simpl; intros.
    - destruct bb_max as [ | h t ]; auto; inversion H.
    - destruct bb_max as [ | h t ]; auto; simpl.
      destruct i as [ | i']; auto.
      -- apply andb_prop in H; apply Nat.leb_le in H0; inversion_clear H.
          apply andb_true_intro; split; auto.
          destruct v as [ | vh vt]; auto; simpl in *; apply Nat.leb_le; auto.
      --  apply andb_prop in H; apply Nat.leb_le in H0; inversion_clear H.
          apply andb_true_intro; split; auto.
          destruct v as [ | vh vt]; auto. replace (nth (S i') [] 0) with (nth i' [] 0); auto.
          apply IHv'; auto.
          apply Nat.leb_le; auto. destruct i'; auto.
          destruct i'; auto.
          simpl nth; apply IHv'; auto.
          simpl in H0; apply Nat.leb_le; auto.
Qed.

Lemma all_lbd_update :
    forall v' i v bb_min,
        all_lbd bb_min v' = true ->
        (nth i v 0 <=? nth i v' 0) = true ->
        all_lbd (list_set bb_min i (Some (nth i v 0))) v' = true.
Proof.
    induction v'; simpl; intros.
    - destruct bb_min as [ | h t ]; auto; inversion H.
    - destruct bb_min as [ | h t ]; auto; simpl.
      destruct i as [ | i']; auto.
      --  apply andb_prop in H; apply Nat.leb_le in H0; inversion_clear H.
      apply andb_true_intro; split; auto.
      destruct v as [ | vh vt]; auto; simpl in *; apply Nat.leb_le; auto.
      --  apply andb_prop in H; apply Nat.leb_le in H0; inversion_clear H.
      apply andb_true_intro; split; auto.
      destruct v as [ | vh vt]; auto. replace (nth (S i') [] 0) with (nth i' [] 0); auto.
      apply IHv'; auto.
      apply Nat.leb_le; auto. destruct i'; auto.
      destruct i'; auto.
      simpl nth; apply IHv'; auto.
      simpl in H0; apply Nat.leb_le; auto.
Qed.


(* initial bb : (mk_bbox (repeat None k) (repeat None k)) *)


Lemma kdtree_build_bounded : forall fuel (k:nat) (data:list datapt) depth_mod bb
    (Hk : 0 < k)
    (Hdm : depth_mod < k)
    (Hfuel : length data <= fuel)
    (Hlen : (forall v', In v' data -> length v' = k))
    (Hbb: forall v', In v' data -> bb_contains bb v' = true),
    kdtree_bounded (build_kdtree_ fuel k data depth_mod) bb = true.
Proof.
    induction fuel as [ | fuel'].
    - intros. destruct data; simpl; auto.
    - intros. destruct data as [ | dp data']; simpl; auto.
      unfold median_partition.
      generalize (quick_select_exists_correct datapt (div2 (length (dp :: data'))) (dp :: data') 
                            (ith_leb depth_mod) 
                            (le_props_ith_leb _)
                            (length_div_2 _ _ _)).
     intros (l1, (v, (l2, (Hq1, (Hq2, (Hq3, (Hq4, Hq5))))))).
     rewrite Hq1; simpl.
     assert (In v (dp :: data')).
     1: {
        apply Permutation.Permutation_in with (l1 ++ v :: l2).
        auto using (Permutation.Permutation_sym).
        apply in_elt.
     }
     repeat (apply andb_true_intro; split); auto.
     1: {
      apply IHfuel'; auto.
      -- auto using next_depth_lt.
      -- generalize (Nat.le_div2 (length data')); intros.
         simpl length in Hq3, Hfuel.
         assert (length l1 <= length data'); try lia.
      -- intros; apply Hlen.
            apply Permutation.Permutation_in with (l1 ++ v :: l2).
            auto using (Permutation.Permutation_sym).
            apply in_or_app; auto.
      -- intros.
         destruct bb as [ bb_min bb_max ]; simpl.
         apply Hq4 in H0 as H0'.
         assert (In v' (dp :: data')).
         1: { 
            apply Permutation.Permutation_in with (l1 ++ v :: l2).
            auto using (Permutation.Permutation_sym).
            apply in_or_app; auto.
         }
         apply Hbb in H1 as H1'; simpl in H1'.
         split_andb_leb; auto.
         unfold ith_leb in H0'; auto using all_ubd_update.
     }

    apply IHfuel'; auto.
    -- auto using next_depth_lt.
    --  generalize (Nat.le_div2 (length data')); intros.
        simpl length in Hq3, Hfuel.
        apply Permutation.Permutation_length in Hq2 as Hq2'.
        apply Nat.le_trans with (length data'); try lia.
        rewrite app_length in Hq2'. simpl in Hq2'. lia.
    --  intros; apply Hlen.
            apply Permutation.Permutation_in with (l1 ++ v :: l2).
            auto using (Permutation.Permutation_sym).
            apply in_or_app; right. simpl; auto.
    -- intros.
        destruct bb as [ bb_min bb_max ]; simpl.
        apply Hq5 in H0 as H0'.
        assert (In v' (dp :: data')).
        1: { 
           apply Permutation.Permutation_in with (l1 ++ v :: l2).
           auto using (Permutation.Permutation_sym).
           apply in_or_app; right; simpl; auto.
        }
        apply Hbb in H1 as H1'; simpl in H1'; split_andb_leb; auto.
        unfold ith_leb in H0'; auto using all_lbd_update.
Qed.


Lemma build_kdtree_bounded : forall (k:nat) (data:list datapt),
    0 < k ->
    (forall v', In v' data -> length v' = k) ->
    kdtree_bounded (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k)) = true.
Proof.
    unfold build_kdtree; intros.
    apply kdtree_build_bounded; auto.
    intros. simpl.
    split_andb_leb.
    apply all_lbd_none; auto.
    apply all_ubd_none; auto.
Qed.




(*  ******************************************************************
    ******************************************************************
    ******************************************************************
    ******************************************************************
    ******************************************************************
    ******************************************************************
    ****************************************************************** *)

Fixpoint nn (k:nat) (tree:kdtree) (bb:bbox)
                    (goal:datapt) (besto:option datapt) : option datapt :=
    match tree with 
    | mt_tree => besto
    | node ax pt lft rgt => 
       let closer := (match besto with (* check the tree root against current best candidate, if any *)
                        | None => pt
                        | Some best => if (sum_dist goal pt) <? (sum_dist goal best) then pt else best
                      end) in
        let dx := nth ax pt 0 in (* the coordinate value of the tree root at the current axis/dimension *)
        let newbb := bb_split bb ax dx in (* the bounding boxes split around that value along the current axis *)
        let body (closer:datapt) := if (ith_leb ax pt goal) 
                            then (nn k rgt (snd newbb) goal
                                     (nn k lft (fst newbb) goal (Some closer)))
                            else (nn k lft (fst newbb) goal
                                      (nn k rgt (snd newbb) goal (Some closer)))
        in
        match besto with
            | Some best => if ((sum_dist goal best) <=? (sum_dist goal (closest_edge_point goal bb)))
                           then besto
                           else (body closer)
            | None => (body closer)
        end
    end.


Definition nn_search (k:nat) (tree:kdtree) (goal:datapt) : option datapt :=
    nn k tree (mk_bbox (repeat None k) (repeat None k)) goal None.


Example ex9 : nn_search 2 two_tree [7; 20] = Some [5 ; 23] := refl_equal.
Example ex10 : nn_search 2 two_tree [100; 10] = Some [9 ; 10] := refl_equal.



Fixpoint In_kdtree (v: datapt) (tree:kdtree) : Prop :=
    match tree with 
    | mt_tree => False
    | node ax pt lft rgt => pt = v \/ In_kdtree v lft \/ In_kdtree v rgt
    end.


Lemma nn_some_result : forall k tree bb goal best,
    exists result, nn k tree bb goal (Some best) = (Some result).
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ].
    simpl; intros ; eauto.
    simpl; intros.
    destruct (sum_dist goal best <=? sum_dist goal (closest_edge_point goal bb)) eqn:Heq1; eauto.
    destruct (ith_leb ax pt goal) eqn:Heq2; eauto.
    - destruct (IHlft (fst (bb_split bb ax (nth ax pt 0))) 
                    goal 
                    (if sum_dist goal pt <? sum_dist goal best then pt else best)) as [ v Hlft ]; rewrite Hlft.
      destruct (IHrgt (snd (bb_split bb ax (nth ax pt 0))) goal v) as [ v' Hrgt ]; rewrite Hrgt; eauto.
    - destruct (IHrgt (snd (bb_split bb ax (nth ax pt 0)))
                      goal 
                      (if sum_dist goal pt <? sum_dist goal best then pt else best))  as [ v Hrgt ]; rewrite Hrgt.
      destruct (IHlft (fst (bb_split bb ax (nth ax pt 0))) goal v) as [ v' Hlft ] ; rewrite Hlft; eauto.
Qed.


Definition Non_Empty_Tree : kdtree -> Prop := 
    fun tree => match tree with
    | mt_tree => False
    | _ => True
    end.


Lemma nn_always_some_result : forall k tree bb goal besto,
    Non_Empty_Tree tree ->
    exists result, nn k tree bb goal besto = Some result.
Proof.
    destruct besto as [ best | ]; intros Hne.
    apply nn_some_result.
    destruct tree as [ | ax pt lft rgt ].
    simpl in *; tauto.
    simpl.
    destruct (ith_leb ax pt goal) eqn:He1.
    destruct (nn_some_result k lft (fst (bb_split bb ax (nth ax pt 0))) goal pt) as [v1 Hv1]; rewrite Hv1;
    destruct (nn_some_result k rgt (snd (bb_split bb ax (nth ax pt 0))) goal v1) as [v2 Hv2]; rewrite Hv2; eauto.
    destruct (nn_some_result k rgt (snd (bb_split bb ax (nth ax pt 0))) goal pt) as [v1 Hv1]; rewrite Hv1.
    destruct (nn_some_result k lft (fst (bb_split bb ax (nth ax pt 0))) goal v1) as [v2 Hv2]; rewrite Hv2; eauto.
Qed.



Lemma kdtree_bounded_relax_within :
    forall tree bbX bbY
        (H1: bb_within bbX bbY)
        (H2: kdtree_bounded tree bbX = true),
        kdtree_bounded tree bbY = true.
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ]; auto; simpl; intros; split_andb_leb.
    unfold bb_within in H1; auto.

    -   apply IHlft with (fst (bb_split bbX ax (nth ax pt 0))); auto.
        clear H0 H3 IHlft IHrgt lft rgt.
        intros pt' Hpt'.
        assert (bb_contains bbY pt' = true).
        2: {
            destruct bbX as [bbX_min bbX_max]; destruct bbY as [bbY_min bbY_max].
            simpl in *; split_andb_leb; auto.

            clear H1 H0 H H5. clear bbX_min bbY_min.
            generalize bbY_max ax pt bbX_max pt' H3 H4 H6; repeat match goal with H : _ |- _ => clear H end.
            induction bbY_max as [ | h_ymax t_ymax ]; auto.
            intros.
            destruct bbX_max as [ | h_xmax t_xmax ]; destruct pt' as [ | h' t' ]; simpl in *; try discriminate.
            destruct ax as [ | ax' ]; split_andb_leb; auto.
            destruct pt as [ | h t ]; simpl in *; try discriminate; split_andb_leb.
            apply IHt_ymax with t_xmax; auto.
        }
        apply H1.
        clear bbY H1.
        destruct bbX as [bbX_min bbX_max]; simpl in *; split_andb_leb; auto.
        clear H H1 bbX_min.
        generalize bbX_max ax pt pt' H0 H3; clear bbX_max ax pt pt' H0 H3.
        induction bbX_max as [ | h_xmax t_xmax ]; destruct pt as [ | h t ]; simpl in *; try discriminate; auto;
            destruct pt' as [ | h' t' ]; destruct ax as [ | ax' ]; simpl in *; try discriminate; auto;
            intros; split_andb_leb; auto.
        unfold ubd in *; destruct h_xmax as [ x | ]; split_andb_leb; auto; lia.
        apply IHt_xmax with ax' t; auto.

    -   apply IHrgt with (snd (bb_split bbX ax (nth ax pt 0))); auto.
        clear H0 H3 IHlft IHrgt lft rgt.
        intros pt' Hpt'.
        assert (bb_contains bbY pt' = true).
        2: {
            destruct bbX as [bbX_min bbX_max]; destruct bbY as [bbY_min bbY_max].
            simpl in *; split_andb_leb; auto.
            clear H1 H3 H4 H6 bbX_max bbY_max.
            generalize bbY_min ax pt bbX_min pt' H H0 H5; repeat match goal with H : _ |- _ => clear H end.
            induction bbY_min as [ | h_ymin t_ymin ]; auto.
            intros.
            destruct bbX_min as [ | h_xmin t_xmin ]; destruct pt' as [ | h' t' ]; simpl in *; try discriminate.
            destruct ax as [ | ax' ]; split_andb_leb; auto.
            destruct pt as [ | h t ]; simpl in *; try discriminate; split_andb_leb; auto.
            destruct pt as [ | h t ]; simpl in *; try discriminate; split_andb_leb; auto.
            apply IHt_ymin with t_xmin; auto.
        }
        apply H1.
        clear bbY H1.
        destruct bbX as [bbX_min bbX_max]; simpl in *; split_andb_leb; auto.
        clear H0 H3 bbX_max.

        generalize bbX_min ax pt pt' H H1; repeat match goal with H : _ |- _ => clear H end.
        induction bbX_min as [ | h_xm t_xm ]; destruct pt as [ | h t ]; simpl in *; try discriminate; auto;
            destruct pt' as [ | h' t' ]; destruct ax as [ | ax' ]; simpl in *; try discriminate; auto;
            intros; split_andb_leb; auto.
        unfold lbd in *; destruct h_xm as [ x | ]; split_andb_leb; auto; lia.
        apply IHt_xm with ax' t; auto.
Qed.




Lemma In_kdtree_bounded_bb_contains :
    forall tree bb v, kdtree_bounded tree bb = true -> In_kdtree v tree -> bb_contains bb v = true.
Proof.
    induction tree; simpl; try tauto; intros.
    apply andb_prop in H; destruct H as [ H Ha ].
    apply andb_prop in H; destruct H as [ Hb Hc ].
    destruct H0 as [ H | [ H | H ] ].
    -   rewrite <- H; auto.
    -   apply IHtree1; auto. apply kdtree_bounded_relax_within with (fst (bb_split bb n (nth n d 0))); 
            auto using bb_within_split_lft.
    -   apply IHtree2; auto. apply kdtree_bounded_relax_within with (snd (bb_split bb n (nth n d 0))); 
    auto using bb_within_split_rgt.
Qed.


Lemma nn_correct_2a : forall k tree bb goal best result,
    nn k tree bb goal (Some best) = Some result ->
    result = best \/ In_kdtree result tree.
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ].
    1: { simpl; intros; inversion H; auto. }

    intros bb goal best result H; simpl in H.
    destruct (sum_dist goal best <=? sum_dist goal (closest_edge_point goal bb)) eqn:Hd1.
    left; inversion H; auto.

    destruct (ith_leb ax pt goal) eqn:Hd2.
    - 
    destruct (nn_some_result k lft (fst (bb_split bb ax (nth ax pt 0))) goal
        (if sum_dist goal pt <? sum_dist goal best then pt else best)) as
            [vl1 Hvl1]; rewrite Hvl1 in H.
    destruct (nn_some_result k rgt (snd (bb_split bb ax (nth ax pt 0))) goal vl1) as
            [vr1 Hvr1]; rewrite Hvr1 in H.
    apply IHrgt in Hvr1; auto.
    apply IHlft in Hvl1; auto.
    injection H as H; rewrite <- H.
    inversion_clear Hvr1.
    -- 
        rewrite H0.
        destruct (sum_dist goal pt <? sum_dist goal best).
        inversion_clear Hvl1. rewrite H1; right; left; auto.
        right; right; left; auto.
        inversion_clear Hvl1. left; auto.
        right; right; left; auto.
    --
        right; right; right; auto.

    -
    destruct (nn_some_result k rgt (snd (bb_split bb ax (nth ax pt 0))) goal
        (if sum_dist goal pt <? sum_dist goal best then pt else best)) as [vr Hvr]; rewrite Hvr in H.
    destruct (nn_some_result k lft (fst (bb_split bb ax (nth ax pt 0))) goal vr) as [vl Hvl]; rewrite Hvl in H.
    apply IHrgt in Hvr; auto.
    apply IHlft in Hvl; auto.
    injection H as H; rewrite <- H.
    inversion_clear Hvl.
    -- rewrite H0.
        destruct (sum_dist goal pt <? sum_dist goal best); inversion_clear Hvr.
        right; left; auto.
        right; right; right; auto.
        left; auto.
        right; right; right; auto.
    -- right; right; left; auto.
Qed.

Lemma nn_correct_2b : forall k tree bb goal result,
    nn k tree bb goal None = Some result ->
    In_kdtree result tree.
Proof.
    destruct tree; simpl nn; intros; try discriminate.

    destruct (ith_leb n d goal).
    - 
    destruct (nn_some_result k tree1 (fst (bb_split bb n (nth n d 0))) goal d) as [v Hv]; rewrite Hv in H.
    apply nn_correct_2a in H; apply nn_correct_2a in Hv.
    inversion_clear H; inversion_clear Hv; try rewrite H0.
    left; auto.
    right; left; auto.
    right; right; auto.
    right; right; auto.
    -
    destruct (nn_some_result k tree2 (snd (bb_split bb n (nth n d 0))) goal d) as [v Hv]; rewrite Hv in H.
    apply nn_correct_2a in H; apply nn_correct_2a in Hv.
    inversion_clear H; inversion_clear Hv; try rewrite H0.
    left; auto.
    right; right; auto.
    right; left; auto.
    right; left; auto.
Qed.




Lemma nn_result_le : forall k tree bb goal best v,
    nn k tree bb goal (Some best) = Some v -> sum_dist goal v <= sum_dist goal best.
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ].
    1: { simpl; intros. injection H as H; rewrite H; auto. }
    simpl; intros bb goal best v Hnn.
    destruct (sum_dist goal best <=? sum_dist goal (closest_edge_point goal bb)) eqn:He1.
    injection Hnn as Hnn; rewrite Hnn; auto.
    destruct (ith_leb ax pt goal) eqn:He2;
        destruct (sum_dist goal pt <? sum_dist goal best) eqn:He3;
        match goal with H : (nn ?a ?b ?c ?d 
                                (nn ?e ?f ?g ?h (Some ?i)) = Some ?j) |- _ =>
            destruct (nn_some_result e f g h i) as [v1 Hv1]; rewrite Hv1 in Hnn;
            destruct (nn_some_result a b c d v1) as [v2 Hv2]; rewrite Hv2 in Hnn end;
        repeat match goal with H : (nn k lft _ _ _ = _) |- _ => apply IHlft in H 
                      | H : (nn k rgt _ _ _ = _) |- _ => apply IHrgt in H end; split_andb_leb;
        injection Hnn as Hnn; rewrite Hnn in *; lia.
Qed.



Lemma nn_correct_1 : forall k tree bb goal besto result,
    kdtree_bounded tree bb = true ->
    nn k tree bb goal besto = Some result ->
    forall v', In_kdtree v' tree -> 
    sum_dist goal result <= sum_dist goal v'.
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ].
    1: { simpl; intros; inversion H1. }
    intros bb goal besto result Hbnd Hnn v' Hinv'.
    destruct bb as [ bb_min bb_max ].
    destruct besto as [ best | ].
    2: { 
        destruct Hinv' as [ Hin_pt | [Hin_lft | Hin_rgt] ].

        (* here we are checking v' = pt , the value at the current node of the tree *)
        - rewrite <- Hin_pt in *; clear Hin_pt v'.
          simpl in Hnn.
          destruct (ith_leb ax pt goal) eqn:Hleb_ax.
          -- 
            destruct (nn_some_result k lft (mk_bbox bb_min (list_set bb_max ax (Some (nth ax pt 0)))) goal pt)
                as [vl Hvl]; rewrite Hvl in Hnn.
            destruct (nn_some_result k rgt (mk_bbox (list_set bb_min ax (Some (nth ax pt 0))) bb_max) goal vl)
                as [vr Hvr]; rewrite Hvr in Hnn.
            rewrite Hnn in *; clear Hnn vr.
            apply Nat.le_trans with (sum_dist goal vl);
            eapply nn_result_le; eauto.
          -- destruct (nn_some_result k rgt (mk_bbox (list_set bb_min ax (Some (nth ax pt 0))) bb_max) goal pt) 
            as [vr Hvr]; rewrite Hvr in Hnn.
             destruct (nn_some_result k lft (mk_bbox bb_min (list_set bb_max ax (Some (nth ax pt 0)))) goal vr)
            as [vl Hvl]; rewrite Hvl in Hnn.
            rewrite Hnn in *; clear Hnn vl.
            apply Nat.le_trans with (sum_dist goal vr); eapply nn_result_le; eauto.
        - simpl in Hnn.
          destruct (ith_leb ax pt goal) eqn:Hleb_ax.
            -- destruct (nn_some_result k lft (mk_bbox bb_min (list_set bb_max ax (Some (nth ax pt 0)))) goal pt)
                as [vl Hvl]; rewrite Hvl in Hnn.
                apply Nat.le_trans with (sum_dist goal vl).
                eapply nn_result_le; eauto.
                apply (IHlft (mk_bbox bb_min (list_set bb_max ax (Some (nth ax pt 0)))) goal (Some pt) vl); auto.
                simpl in Hbnd.
                apply andb_prop in Hbnd; destruct Hbnd as [ Hba Hbb ].
                apply andb_prop in Hba; destruct Hba as [Hba Hbc]; auto.
            -- apply IHlft with (bb := (mk_bbox bb_min (list_set bb_max ax (Some (nth ax pt 0))))) 
                                (besto := (nn k rgt (mk_bbox (list_set bb_min ax (Some (nth ax pt 0))) bb_max) goal (Some pt))); auto.
                simpl in Hbnd.
                apply andb_prop in Hbnd; destruct Hbnd as [ Hba Hbb ].
                apply andb_prop in Hba; destruct Hba as [Hba Hbc]; auto.
        - simpl in Hnn.
        destruct (ith_leb ax pt goal) eqn:Hleb_ax.
        -- eapply IHrgt; eauto.
            simpl in Hbnd.
            apply andb_prop in Hbnd; destruct Hbnd as [ Hba Hbb ].
            apply andb_prop in Hba; destruct Hba as [Hba Hbc]; auto.        
        -- destruct (nn_some_result k rgt (mk_bbox (list_set bb_min ax (Some (nth ax pt 0))) bb_max) goal pt)
            as [vr Hvr]; rewrite Hvr in Hnn.
            apply Nat.le_trans with (sum_dist goal vr).
            eapply nn_result_le; eauto.
            eapply IHrgt; eauto.
                simpl in Hbnd.    (* make this a lemma *)
                apply andb_prop in Hbnd; destruct Hbnd as [ Hba Hbb ].
                apply andb_prop in Hba; destruct Hba as [Hba Hbc]; auto.
    }


    1: {
        apply nn_result_le in Hnn as Hle.
        simpl in Hnn.
        (* check COND (1) first   ---  Heq3 *)
        destruct (sum_dist goal best <=? sum_dist goal (cep goal bb_min bb_max)) eqn:Heq3; split_andb_leb.
        --  injection Hnn as Hnn; rewrite Hnn in *; clear best Hnn.
            (* so result is closer than anything in the bb of this tree *)
            apply Nat.le_trans with (sum_dist goal (cep goal bb_min bb_max)); auto.
            apply (cep_min_dist goal bb_min bb_max); auto.
            eapply In_kdtree_bounded_bb_contains; eauto.

        --
        destruct (nn_some_result k rgt (mk_bbox (list_set bb_min ax (Some (nth ax pt 0))) bb_max) goal
        (if sum_dist goal pt <? sum_dist goal best then pt else best)) as
        [vr1 Hvr1]; rewrite Hvr1 in Hnn.
        destruct (nn_some_result k lft (mk_bbox bb_min (list_set bb_max ax (Some (nth ax pt 0)))) goal
                    (if sum_dist goal pt <? sum_dist goal best then pt else best)) as
        [vl1 Hvl1]; rewrite Hvl1 in Hnn.
        destruct (nn_some_result k rgt (mk_bbox (list_set bb_min ax (Some (nth ax pt 0))) bb_max) goal vl1)
        as [vr2 Hvr2]; rewrite Hvr2 in Hnn.
        destruct (nn_some_result k lft (mk_bbox bb_min (list_set bb_max ax (Some (nth ax pt 0)))) goal vr1)
        as [vl2 Hvl2]; rewrite Hvl2 in Hnn.
        apply nn_result_le in Hvr1 as Hnr1; apply nn_result_le in Hvr2 as Hnr2; 
            apply nn_result_le in Hvl1 as Hnl1; apply nn_result_le in Hvl2 as Hnl2.

        (* Here COND (1) is false -- i.e. best is in the bb of this tree *)  
        destruct Hinv' as [ Hin_pt | [Hin_lft | Hin_rgt] ].
        --- (* considering v' = the datapt at the root of the tree *)
            rewrite <- Hin_pt in *; clear Hin_pt v'.
            destruct (ith_leb ax pt goal) eqn:Hleb; (* COND (3) *)
                injection Hnn as Hnn; rewrite <- Hnn in *;
                destruct (sum_dist goal pt <? sum_dist goal best) eqn:Hcond2; (* COND (2) *)
                    split_andb_leb; lia.
        --- (* considering v' is in the lft subtree *)
            simpl in Hbnd; split_andb_leb; auto.
            generalize (IHlft _ _ _ _ H2 Hvl1 _ Hin_lft); intros IHle1;
            generalize (IHlft _ _ _ _ H2 Hvl2 _ Hin_lft); intros IHle2.
            destruct (ith_leb ax pt goal) eqn:Hleb; (* COND (3) *)
                injection Hnn as Hnn; rewrite <- Hnn in *; auto; lia.

        --- (* considering v' is in the rgt subtree *)
            simpl in Hbnd; split_andb_leb; auto.
            generalize (IHrgt _ _ _ _ H0 Hvr1 _ Hin_rgt); intros IHle1;
            generalize (IHrgt _ _ _ _ H0 Hvr2 _ Hin_rgt); intros IHle2.
            destruct (ith_leb ax pt goal) eqn:Hleb; (* COND (3) *)
                injection Hnn as Hnn; rewrite <- Hnn in *; auto; lia.
    }
Qed.




Theorem nn_search_correct : 
    forall k tree goal,
    Non_Empty_Tree tree ->
    kdtree_bounded tree (mk_bbox (repeat None k) (repeat None k)) = true ->
    exists result, 
        nn_search k tree goal = Some result
        /\ In_kdtree result tree
        /\ (forall v', In_kdtree v' tree -> sum_dist goal result <= sum_dist goal v').
Proof.
    intros k tree goal Hne.
    unfold nn_search.
    destruct (nn_always_some_result k tree (mk_bbox (repeat None k) (repeat None k)) goal None Hne) as
        [result Hnn].
    exists result; repeat split; auto.
    apply (nn_correct_2b k tree (mk_bbox (repeat None k) (repeat None k)) goal); auto.
    eapply nn_correct_1; eauto.
Qed.




Lemma median_partition_some : forall h t depth_mod,
    exists l1, exists m, exists l2, @median_partition datapt (h :: t) (ith_leb depth_mod) = Some (l1, m, l2).
Proof.
    intros; destruct (median_partition (h :: t) (ith_leb depth_mod)) as [ ((l1, m), l2) | ] eqn:Heq.
    exists l1; exists m; exists l2; auto.
    unfold median_partition in Heq.
    destruct (quick_select_always_some _ (div2 (length (h :: t))) (h::t) (ith_leb depth_mod))
        as (a, (b, (c, Heqs))).
    apply Nat.lt_div2; simpl; lia.
    rewrite Heqs in Heq; discriminate.
Qed.





Lemma data_tree_same_build_kdtree_ :
    forall fuel k data depth_mod tree
    (Hk : 0 < k)
    (Hdm : depth_mod < k)
    (Hfuel : length data <= fuel)
    (Htree : tree = build_kdtree_ fuel k data depth_mod),
    forall v, In_kdtree v tree <-> In v data.
Proof.
    induction fuel as [ | f].
    simpl; intros;  
    destruct data as [ | h t]; [rewrite Htree; simpl; tauto
      | inversion Hfuel ].
    destruct data as [ | h t]; simpl; intros. rewrite Htree; simpl; tauto.
    -
    destruct (median_partition_some h t depth_mod) as (l1, (m, (l2, Heq))). rewrite Heq in Htree.
    apply le_S_n in Hfuel.
    unfold median_partition in Heq.
    apply qsp_lengths_le in Heq as Hlens; simpl in Hlens;
        destruct Hlens as (Hlens1, Hlens2).
    assert (length l1 <= f) as Hlenl1; assert (length l2 <= f) as Hlenl2; try lia.

    split; intros Hin.
    --   (* left to right direction of the <-> *)
        rewrite Htree in Hin; simpl in Hin.
        destruct Hin as [ Hin1 | [ Hin2 | Hin3 ]].
        --- 
            assert (In m (h :: t)).
            1: {
                apply quick_select_permutation in Heq.
                apply Permutation.Permutation_sym in Heq.
                apply Permutation.Permutation_in with (x := m) in Heq; auto.
                apply in_elt.
            }
            destruct H as [ H1 | H2 ].
            left; rewrite H1; auto.
            right; rewrite <- Hin1; auto.
        --- (* left sub kdtree *)
            unfold quick_select in Heq.
            destruct (IHf k l1 (next_depth k depth_mod) (build_kdtree_ f k l1 (next_depth k depth_mod))
                     Hk (next_depth_lt _ _ Hk) Hlenl1 (refl_equal ) v) as (IHl1a, IHl1b).
            apply IHl1a in Hin2.
            apply quick_select_permutation in Heq.
            assert (In v (l1 ++ m :: l2)).
            apply in_or_app; left; auto.
            apply Permutation.Permutation_sym in Heq.
            apply Permutation.Permutation_in with (x := v) in Heq; auto.
        
        --- (* right sub kdtree *) 
            unfold quick_select in Heq.
            destruct (IHf k l2 (next_depth k depth_mod) (build_kdtree_ f k l2 (next_depth k depth_mod))
                     Hk (next_depth_lt _ _ Hk) Hlenl2 (refl_equal ) v) as (IHl2a, IHl2b).
            apply IHl2a in Hin3.
            apply quick_select_permutation in Heq.
            assert (In v (l1 ++ m :: l2)).
            apply in_or_app; right; right; auto.
            apply Permutation.Permutation_sym in Heq.
            apply Permutation.Permutation_in with (x := v) in Heq; auto.
         
    -- (* right to left direction of the <-> *) 
        rewrite Htree.
        apply quick_select_permutation in Heq as Hperm.
        apply Permutation.Permutation_in with (x := v) in Hperm as Hpermin; auto.
        destruct (IHf k l1 (next_depth k depth_mod) (build_kdtree_ f k l1 (next_depth k depth_mod))
            Hk (next_depth_lt _ _ Hk) Hlenl1 (refl_equal ) v) as (_, IHl1b).
        destruct (IHf k l2 (next_depth k depth_mod) (build_kdtree_ f k l2 (next_depth k depth_mod))
                    Hk (next_depth_lt _ _ Hk) Hlenl2 (refl_equal ) v) as (_, IHl2b).
        apply in_app_or in Hpermin; destruct (Hpermin) as [Hp1 | Hp2]; clear Hpermin.
        right; left; auto.
        destruct Hp2 as [Hp2 | Hp3].
        left; auto.
        right; right; auto.
Qed.


Lemma data_tree_same :
    forall k (data : list datapt) tree,
    0 < k ->
    tree = (build_kdtree k data) ->
    forall v, In_kdtree v tree <-> In v data.
Proof.
    unfold build_kdtree; intros.
    eapply data_tree_same_build_kdtree_; eauto.
Qed.



Theorem nn_search_build_kdtree_correct :
    forall (k : nat) (data : list datapt),
    0 < length data ->
    0 < k ->
    (forall v' : datapt, In v' data -> length v' = k) ->
    forall tree goal result,
    tree = (build_kdtree k data) ->
    nn_search k tree goal = Some result ->
       In result data /\ (forall v', In v' data -> sum_dist goal result <= sum_dist goal v').
Proof.
    intros k data Hlen Hk Hin tree goal result Htree Hnn.
    rewrite Htree in *; clear Htree tree.
    split.
    -   destruct (data_tree_same k data (build_kdtree k data) Hk (refl_equal ) result); auto.
        apply H.
        apply (nn_correct_2b k _ (mk_bbox (repeat None k) (repeat None k)) goal); auto.
    -   intros v' Hin'.
        destruct (data_tree_same k data (build_kdtree k data) Hk (refl_equal ) v'); auto.
        apply H0 in Hin'.
        eapply nn_correct_1; eauto.
        apply (build_kdtree_bounded _ _ Hk Hin).
Qed.


Theorem nn_search_build_kdtree_always_result_correct :
    forall (k : nat) (data : list datapt),
    0 < length data ->
    0 < k ->
    (forall v' : datapt, In v' data -> length v' = k) ->
    forall tree goal,
    tree = (build_kdtree k data) ->
    exists result, 
        nn_search k tree goal = Some result
        /\ In result data
        /\ (forall v', In v' data -> sum_dist goal result <= sum_dist goal v').
Proof.
    intros k data Hlen Hk Hin tree goal Htree.
    generalize (build_kdtree_bounded _ _ Hk Hin); intros Hbound.

    assert (Non_Empty_Tree tree).
    1:{ destruct data as [ | h t].
        inversion Hlen.
        rewrite Htree; unfold build_kdtree; simpl.
        destruct (median_partition (h :: t) (ith_leb 0)) as [ ((a, b), c) | ] eqn:Hmed.
        simpl; auto.
        destruct (quick_select_exists_correct _  (div2 (length (h :: t))) (h::t) (ith_leb 0)) as (l1, (v, (l2, (Hex, _)))).
        - split; unfold ith_leb; intros; split_andb_leb; try lia.
        destruct (Nat.le_ge_cases (nth 0 a 0) (nth 0 b 0)); [ left | right ]; split_andb_leb; lia.
        - apply Nat.lt_div2; auto.
        - unfold median_partition in Hmed; rewrite Hex in Hmed; discriminate.
    }

    rewrite Htree in H.
    apply (nn_search_correct k (build_kdtree k data) goal) in H; auto.
    destruct H as (result, (H1, (H2, H3))).
    exists result; rewrite Htree; repeat split; auto.
    destruct  (data_tree_same k data (build_kdtree k data) Hk (refl_equal ) result); auto.
    intros v' Hinv';
      destruct  (data_tree_same k data (build_kdtree k data) Hk (refl_equal ) v'); auto.
Qed.

