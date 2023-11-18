
From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Lists.List.
Require Import Lia.
Import ListNotations.
From NN Require Import tactics.

Inductive bbox : Set :=
    | mk_bbox : (list (option nat))  -> (list (option nat))  -> bbox.

Definition datapt := list nat.

Definition bb_ex01 : bbox := (mk_bbox [Some 20; Some 10; Some 15]
                                     [Some 30; Some 20; Some 35]).

Fixpoint list_set {A} (lst:list A) (n:nat) (v:A) : list A :=
    match lst with
    | [] => []
    | h :: t => match n with 
                | 0 => v :: t
                | S n' => h :: (list_set t n' v)
                end
    end.

Example ex1 : (list_set [Some 20; None; Some 15] 1 (Some 10))
                = [Some 20; Some 10; Some 15].
auto. Qed.



Definition bb_split (bb:bbox) (d:nat) (v:nat) : bbox * bbox :=
    let '(mk_bbox bb_min bb_max) := bb in
    ( mk_bbox bb_min (list_set bb_max d (Some v)),
      mk_bbox (list_set bb_min d (Some v)) bb_max ).


Example ex2 :
    (bb_split (mk_bbox [Some 10; None; Some 4] [None; Some 30; Some 20]) 1 11)
    = (mk_bbox [Some 10; None; Some 4] [None; Some 11; Some 20] ,
       mk_bbox [Some 10; Some 11; Some 4] [None; Some 30; Some 20]).
auto. Qed.


Definition lbd (xo:option nat) (y:nat) : bool :=
    match xo with 
    | None => true
    | Some x => x <=? y
    end.

Definition ubd (x:nat) (yo:option nat) : bool :=
    match yo with
    | None => true
    | Some y => x <=? y
    end.

Fixpoint all_lbd (mins:list (option nat)) (vals: list nat) : bool :=
    match mins, vals with
    | [], [] => true
    | xo::t, y::t' => andb (lbd xo y) (all_lbd t t')
    | _, _ => false
    end.

Fixpoint all_ubd (vals: list nat) (maxs:list (option nat)) : bool :=
    match vals, maxs with
    | [], [] => true
    | x::t, yo::t' => andb (ubd x yo) (all_ubd t t')
    | _, _ => false
    end.

Definition bb_contains (bb:bbox) (pt:datapt) : bool :=
    match bb with (mk_bbox bb_min bb_max) =>
        all_lbd bb_min pt && all_ubd pt bb_max
    end.
    

Example ex3 :
    bb_contains (mk_bbox [Some 10; None; Some 4] [None; Some 30; Some 20])
                [20 ; 30 ; 16] = true 
    := refl_equal.


Fixpoint cep (vals:list nat) (mins:list (option nat)) (maxs:list (option nat)) : list nat :=
    match vals with 
    | [] => []
    | i :: t =>
      match mins with [] => [] | j :: tmin =>
      match maxs with [] => [] | k :: tmax =>
      (if (andb (lbd j i) (ubd i k)) then i
        else if (ubd i j) then match j with None => i | Some j' => j' end
        else match k with None => i | Some k' => k' end) 
      :: cep t tmin tmax
    end end end.

Definition closest_edge_point (pt:datapt) (bb:bbox) : datapt :=
    match bb with (mk_bbox bb_min bb_max) =>
       cep pt bb_min bb_max
    end.

Example ex4 :
    closest_edge_point [10 ; 20 ; 40] (mk_bbox [Some 5 ; Some 0; Some 45] [Some 70; Some 2; None])
        = [10 ; 2 ; 45 ] 
    := refl_equal.

Example ex4b :
    closest_edge_point [10 ; 20 ; 40] (mk_bbox [Some 5 ; Some 0; None] [Some 70; Some 2; Some 45])
        = [10 ; 2 ; 40 ] 
    := refl_equal.


Definition bb_within (bbX bbY:bbox) : Prop :=
    forall pt, bb_contains bbX pt = true -> bb_contains bbY pt = true.






Definition abs_diff (x y : nat) : nat :=
    if (x <? y) then y - x else x - y .

Lemma abs_diff_0 : forall x, abs_diff x x = 0.
Proof.
    intros; unfold abs_diff. 
    rewrite Nat.ltb_irrefl.
    lia.
Qed.

Example ex5 : abs_diff 5 9 = 4 := refl_equal.
Example ex6 : abs_diff 9 5 = 4 := refl_equal.
Example ex7 : abs_diff 7 7 = 0 := refl_equal.

Fixpoint sum_dist (vs ws:list nat) : nat :=
    match vs, ws with 
    | [], [] => 0
    | x :: vs', y :: ws' => abs_diff x y + sum_dist vs' ws'
    | _, _ => 0
    end.


Example ex8 : sum_dist [10 ; 20 ; 5] [15 ; 12 ; 8] = 5+8+3 := refl_equal.


Lemma cep_min_dist :
    forall vs mins maxs ws, 
        cep vs mins maxs = ws -> 
            forall pt, bb_contains (mk_bbox mins maxs) pt = true ->
            sum_dist vs ws <= sum_dist vs pt.
Proof.
    induction vs as [ | v vs']; simpl; intros; try (rewrite <- H; apply Nat.le_0_l).
    destruct mins as [ | jo mins' ]; try (rewrite <- H; apply Nat.le_0_l).
    destruct maxs as [ | ko maxs' ]; try (rewrite <- H; apply Nat.le_0_l).
    destruct ws as [ | w ws']; try apply Nat.le_0_l.
    injection H; clear H; intros.
    destruct pt as [ | p pt']; [ inversion H0 |  simpl in H0].
    apply andb_prop in H0; inversion_clear H0.
    apply andb_prop in H2; apply andb_prop in H3.
    inversion_clear H2; inversion_clear H3.
    assert (abs_diff v w <= abs_diff v p).
    2: {
        assert (sum_dist vs' ws' <= sum_dist vs' pt'); try lia.
        apply IHvs' with mins' maxs'; auto.
        simpl. apply andb_true_intro; auto.
    }
    clear H4 H5 H pt' ws' mins' maxs' IHvs' vs'.
    destruct jo as [ j | ]; destruct ko as [ k | ]; simpl in *.
    3: {
        assert (v = w). (destruct (v <=? k); auto).
        replace w with v.
        rewrite abs_diff_0.
        lia.
    }
    3: {
        replace w with v.
        rewrite abs_diff_0.
        lia.
    }
    1: {
        apply leb_complete in H0, H2.
        destruct (j <=? v) eqn:Hjv; destruct (v <=? k) eqn:Hvk.
        - replace w with v; rewrite abs_diff_0; lia.
        - simpl in H1. destruct (v <=? j) eqn:Hvj.
          --  apply leb_complete in Hjv, Hvj. replace v with j in *; try lia.  
              rewrite H1; rewrite abs_diff_0; lia.
          -- apply leb_complete in Hjv. rewrite H1 in *; clear H1 k.
             unfold abs_diff. replace (v <? w) with false.     
             apply leb_complete_conv in Hvk, Hvj.
             destruct (v <? p) eqn:Hvp; try lia. apply leb_complete in Hvp; lia.
             apply leb_complete_conv in Hvk.
             symmetry. apply leb_correct_conv. lia.
        - simpl in H1. destruct (v <=? j) eqn:Hvj.
          -- apply leb_complete in Hvk, Hvj; apply leb_complete_conv in Hjv.
             rewrite H1 in *; clear H1 j.
             unfold abs_diff.
             replace (v <? w) with true; try (symmetry; apply Nat.ltb_lt; auto).
             destruct (v <? p) eqn:Hvp; try lia.   
             apply leb_complete_conv in Hvp; lia.
          --  apply leb_complete in Hvk; apply leb_complete_conv in Hjv, Hvj.
              lia. (* absurd *)
        - simpl in H1. unfold abs_diff; destruct (v <=? j) eqn:Hvj.
          apply leb_complete in Hvj; apply leb_complete_conv in Hjv, Hvk. try lia.
          apply leb_complete_conv in Hjv, Hvk, Hvj; lia.
    }
    apply leb_complete in H0. clear H2.
    destruct (j <=? v) eqn:Hjv; simpl in H1.
    replace w with v; rewrite abs_diff_0; lia.
    destruct (v <=? j) eqn:Hvj.
    - apply leb_complete in Hvj; apply leb_complete_conv in Hjv.
      rewrite <- H1; clear H1 w; unfold abs_diff.
      replace (v <? j) with true; try (symmetry; apply Nat.ltb_lt; auto).
      destruct (v <? p) eqn:Hvp; try lia.  
      apply leb_complete_conv in Hvp; lia.
    - apply leb_complete_conv in Hjv, Hvj.
    rewrite H1; rewrite abs_diff_0; lia.
Qed.


Lemma closest_edge_point_min_dist :
    forall bb pt pt', 
        bb_contains bb pt' = true ->
        sum_dist pt (closest_edge_point pt bb) <= sum_dist pt pt'.
Proof.
    destruct bb as [mins maxs]; simpl; intros.
    eapply cep_min_dist; eauto.
Qed.




Lemma all_lbd_none : forall k v, length v = k -> all_lbd (repeat None k) v = true.
Proof.
    induction k; intros; simpl; destruct v as [ | h t]; auto; try inversion H.
Qed.

Lemma all_ubd_none : forall k v, length v = k -> all_ubd v (repeat None k) = true.
Proof.
    induction k; intros; simpl; destruct v as [ | h t]; auto.
    inversion H.
    inversion H.
    apply IHk; auto.
Qed.


Lemma all_ubd_trans_set : 
    forall bb_max v v' n
        (H1 : all_ubd v bb_max = true)
        (H2 : all_ubd v' (list_set bb_max n (Some (nth n v 0))) = true),
        all_ubd v' bb_max = true.
Proof.
    induction bb_max; simpl; auto; intros.
    destruct v as [ | h t ]; simpl in *; try discriminate.
    destruct v' as [ | h' t' ]; simpl in *; try discriminate; try (destruct n; discriminate).
    destruct n as [ | n']. 
    -   split_andb_leb; auto.
        unfold ubd in *.
        destruct a as [ a | ]; auto.
        split_andb_leb; lia.
    -   split_andb_leb; auto.
        eapply IHbb_max; eauto.
Qed.

Lemma all_lbd_trans_set : 
    forall bb_min v v' n
        (H1 : all_lbd bb_min v = true)
        (H2 : all_lbd (list_set bb_min n (Some (nth n v 0))) v' = true),
        all_lbd bb_min v' = true.
Proof.
    induction bb_min; simpl; auto; intros.
    destruct v as [ | h t ]; simpl in *; try discriminate.
    destruct v' as [ | h' t' ]; simpl in *; try discriminate; try (destruct n; discriminate).
    destruct n as [ | n']; simpl in *.
    -   split_andb_leb; auto.
        unfold lbd in *.
        destruct a as [ a | ]; auto.
        split_andb_leb; lia.
    -   split_andb_leb; auto.
        eapply IHbb_min; eauto.
Qed.




Lemma unbounded_contains : 
    forall k v
        (Hk : 0 < k)
        (Hv : length v = k),
        bb_contains (mk_bbox (repeat None k) (repeat None k)) v = true.
Proof.
    induction k as [ | k']; intros; try lia.
    destruct v as [ | v' ]; try discriminate.
    simpl.
    apply Bool.andb_true_iff; split.
    apply all_lbd_none; auto.
    apply all_ubd_none; auto.
Qed.


Lemma bb_within_split_lft :
    forall bb n d (H1: bb_contains bb d = true),
      bb_within (fst (bb_split bb n (nth n d 0))) bb.
Proof.
    destruct bb as [bb_min bb_max]; unfold bb_within; simpl; intros.
    split_andb_leb; auto.
    eapply all_ubd_trans_set; eauto.
Qed.


Lemma bb_within_split_rgt :
    forall bb n d (H1: bb_contains bb d = true),
      bb_within (snd (bb_split bb n (nth n d 0))) bb.
Proof.
    destruct bb as [bb_min bb_max]; unfold bb_within; simpl; intros.
    split_andb_leb; auto.
    eapply all_lbd_trans_set; eauto.
Qed.

