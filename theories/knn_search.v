
From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Bool.
From Coq Require Import Lists.List.
Require Import Lia.
Require Import Orders.
Import ListNotations.

From NN Require Import tactics.
From NN Require Import bounding_boxes.
From NN Require Import quick_select_partition.
From NN Require Import max_pqueue.
From NN Require Import kdtree.
    


(*  ******************************************************************
    ******************************************************************
    ******************************************************************
    ******************************************************************
    ******************************************************************
    ******************************************************************
    ****************************************************************** *)

Module NatTTLB := OTF_to_TTLB Nat.
    (*
Module MaxPQ := List_MaxPQ NatTTLB.
Import MaxPQ.
    *)

Module KNNS (Import MPQ : MaxPQ NatTTLB).

#[export] Hint Resolve empty_priq insert_priq insert_relate abs_perm : core.

Definition insert_bounded (K:nat) A key (e:A) (pq:priqueue A key) : priqueue A key :=
    let updpq := (insert A key e pq)
    in if K <? (size A key updpq) then 
        match delete_max _ key updpq with 
        | None => updpq  (* should never happen *)
        | Some (_ , updpq') => updpq'
        end
        else updpq.

Fixpoint pq_to_list_ {A} {key} fuel (pq : priqueue A key) : list A :=
    match fuel with 
    | 0 => nil
    | S fuel' => match (delete_max A key pq) with 
                | None => nil
                | Some (e, pq') => e :: (pq_to_list_ fuel' pq')
                end
    end.

Definition pq_to_list {A} {key} (pq : priqueue A key) : list A := pq_to_list_ (size _ _ pq) pq.



(* K - capital - is the # of neighbors to select 
   k - little - is the dimension of the data points
*)    
Fixpoint knn (K:nat) (k:nat) (tree:kdtree) (bb:bbox) (query:datapt) (pq:priqueue datapt (sum_dist query)) 
  : priqueue datapt (sum_dist query) 
  := match tree with 
        | mt_tree => pq
        | node ax pt lft rgt =>
            let body (pq':priqueue datapt (sum_dist query)) := 
                let dx := nth ax pt 0 in (* the coordinate value of the tree root at the current axis/dimension *)
                let bbs := bb_split bb ax dx in (* the bounding boxes split around that value along the current axis *)
                if (ith_leb ax pt query) 
                then (knn K k rgt (snd bbs) query
                        (knn K k lft (fst bbs) query pq'))
                else (knn K k lft (fst bbs) query
                        (knn K k rgt (snd bbs) query pq')) 
            in
            match (peek_max _ _ pq) with
            | None => body (insert_bounded K _ _ pt pq)
            | Some top => if (K <=? (size _ _ pq))
                                && ((sum_dist query top) <? (sum_dist query (closest_edge_point query bb)))
                        then pq
                        else body (insert_bounded K _ _ pt pq)
            end
     end.

Definition knn_search (K:nat) (k:nat) (tree:kdtree) (query:datapt) : list datapt :=
   pq_to_list 
     (knn K k tree (mk_bbox (repeat None k) (repeat None k)) query (empty datapt (sum_dist query))).

(*
Compute (insert_bounded 4 _ _ [8; 2] 
            (insert_bounded 4 _ _ [9; 10] 
            (insert_bounded 4 _ _ [5; 23] 
            (insert_bounded 4 _ _ [4; 3] 
            (insert_bounded 4 _ _ [5; 10] 
            (insert_bounded 4 _ _ [7;12] (empty datapt (sum_dist [5; 5])))))))).
*)



Inductive Contents_kdtree : kdtree -> list datapt -> Prop :=
    | cont_nil : Contents_kdtree mt_tree nil
    | cont_cons : forall ax pt lft rgt lst1 lst2,
                Contents_kdtree lft lst1 -> Contents_kdtree rgt lst2 ->
                Contents_kdtree (node ax pt lft rgt) (pt :: (lst1 ++ lst2)).
    


Lemma cont_node_inv :
    forall data ax pt lft rgt,
        Contents_kdtree (node ax pt lft rgt) data ->
        exists lst1, exists lst2,
            Contents_kdtree lft lst1 /\
            Contents_kdtree rgt lst2 /\
            data = pt :: (lst1 ++ lst2).
Proof.
    intros data ax pt lft rgt Hcont; inversion Hcont.
    exists lst1; exists lst2; repeat split; auto.
Qed.


Lemma contents_in_kdtree :
    forall tree data pt,
    Contents_kdtree tree data -> 
    In pt data -> 
    In_kdtree pt tree.
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ];
        intros data pt' Hcont.
    inversion Hcont; intros Hin; inversion Hin.
    apply cont_node_inv in Hcont as (lst1, (lst2, (H1, (H2, H3)))).
    rewrite H3; intros Hin; inversion_clear Hin.
    rewrite H; constructor; auto.
    destruct (in_app_or lst1 lst2 pt') in H; auto; right; eauto.
Qed.



Lemma build_kdtree_contents_perm_gen
    : forall fuel k data depth_mod
        (Hk : 0 < k)   (* need for next_depth_lt *)
        (Hdm : depth_mod < k)
        (Hfuel : length data <= fuel),
        exists lst,
            Contents_kdtree (build_kdtree_ fuel k data depth_mod) lst /\ Permutation data lst.
Proof.
    induction fuel as [ | f].
    1: { 
        simpl; intros; destruct data as [ | h t].
        exists nil; split; constructor.
        inversion Hfuel.
    }  
    destruct data as [ | h t]; simpl; intros.
    exists nil; split; constructor.
    destruct (median_partition_some h t depth_mod) as (l1, (m, (l2, Heq))); rewrite Heq.
    unfold median_partition in Heq.
    apply qsp_lengths_le in Heq as Hlens; simpl in Hlens;
        destruct Hlens as (Hlens1, Hlens2).
    assert (length l1 <= f) as Hlenf1; try lia.
    assert (length l2 <= f) as Hlenf2; try lia.
    pose proof (IHf _ _ _ Hk (next_depth_lt k depth_mod Hk) Hlenf1) as (lst1, (Hc1, Hp1)).
    pose proof (IHf _ _ _ Hk (next_depth_lt k depth_mod Hk) Hlenf2) as (lst2, (Hc2, Hp2)).
    exists (m :: (lst1 ++ lst2)); split; try constructor; auto.
    apply quick_select_permutation in Heq as Hqsp.
    permtrans (l1 ++ m :: l2).
    permtrans (m :: l1 ++ l2).
Qed.


Lemma build_kdtree_contents_perm
    : forall k data (Hk : 0 < k), 
        exists lst, Contents_kdtree (build_kdtree k data) lst /\ Permutation data lst.
Proof.
    intros; apply build_kdtree_contents_perm_gen; auto.
Qed.


Lemma pq_to_list_nil_empty : forall A key pq
    (Hp : priq A key pq)
    (Hpq : pq_to_list_ (size A key pq) pq = []),
    Abs _ _ pq [].
Proof.
    intros.
    destruct (size A key pq) eqn:Hsz.
    -   apply size_zero_relate; auto.
    -   simpl in Hpq.
        destruct (delete_max A key pq) eqn:Hdm.
        destruct p; discriminate.
        apply delete_max_None_relate; auto.
Qed.


Lemma pq_to_list_relate_ : forall n A key pq lst lst'
    (Hpriq : priq A key pq)
    (Habs : Abs  _ _ pq lst')
    (Hn : size A key pq = n)
    (Hrem : pq_to_list_ n pq = lst),
    Permutation lst lst'.
Proof.
    induction n; intros.
    1:{ 
        simpl in Hrem; inversion Hn; rewrite <- Hrem. apply size_zero_relate in H0; auto.
        pose proof (abs_perm _ _ _ _ _ Hpriq Habs H0); apply Permutation_sym; auto.
    }

    simpl in Hrem.
    destruct (delete_max A key pq) as [ (e', pq') | ] eqn:Hdm.
    2: { rewrite <- Hrem. apply delete_max_empty_None in Hdm. 
         apply empty_relate in Hdm.
         pose proof (abs_perm _ _ _ _ _ Hpriq Habs Hdm); apply Permutation_sym; auto. }
    pose proof (delete_max_ex_Some_relate _ _ _ _ _ _ Hpriq Habs Hdm) as 
        (ql, (H1, (H2, _))).
    destruct lst as [ | h t]; try discriminate.
    injection Hrem as Hr1 Hr2. rewrite Hr1 in *; clear e' Hr1.
    apply delete_max_Some_priq in Hdm as Hdmp; auto.
    enough (size A key pq' = n).
    pose proof (IHn _ _ _ _ _ Hdmp H1 H Hr2).
    permtrans (h :: ql); auto; apply Permutation_sym; auto.
    apply (delete_max_Some_size _ _ n pq pq' h lst'); auto.
Qed.


Lemma pq_to_list_relate : forall A key pq lst lst'
    (Hpriq : priq A key pq)
    (Habs : Abs _ _ pq lst')
    (Hrem : pq_to_list pq = lst),
    Permutation lst lst'.
Proof.
    intros; eapply pq_to_list_relate_; eauto.
Qed.


Lemma list_nil_or_in : 
    forall {A} (lst:list A), lst = [] \/ exists x, In x lst.
Proof.
    destruct lst as [ | h t]; [left|right; exists h; simpl]; auto.
Qed. 

(*
Lemma insert_size_add1 :
    forall A key e pq,
    priq A key pq ->
    Abs A key pq lst ->
    size A key (insert A key e pq) = 1 + size A key pq.
Proof.
    intros.
    rewrite size_relate.


*)



Lemma insert_delete_max_some :
    forall A key e pq al
    (Hpriq : priq A key pq)
    (Habs : Abs A key pq al),
    exists k, exists q, delete_max A key (insert A key e pq) = Some (k, q).
Proof.
    intros.
    pose proof (insert_relate A key pq al e Hpriq Habs) as Habs_ins.
    pose proof (delete_max_relate_cons_Some A key _ e al (insert_priq _ _ _ _ Hpriq) Habs_ins) as (k, (q, Hdm)).
    eauto.
Qed.


Definition all_in_leb {A} key (lst1 lst2 : list A) :=
    forall e1 e2, In e1 lst1 -> In e2 lst2 -> key e1 <=? key e2 = true.

Definition geb_all_in {A} key (e : A) (lst : list A) :=
    forall e', In e' lst -> (key e' <=? key e) = true.

Definition leb_all_in {A} key (e : A) (lst : list A) :=
    forall e', In e' lst -> (key e <=? key e') = true.



Lemma all_in_leb_nil_any : 
    forall A key lst, @all_in_leb A key [] lst.
Proof.
    intros A key lst e1 e2 He1 He2; inversion He1.
Qed.

Lemma all_in_leb_any_nil : 
    forall A key lst, @all_in_leb A key lst [].
Proof.
    intros A key lst e1 e2 He1 He2; inversion He2.
Qed.

#[export] Hint Resolve all_in_leb_nil_any all_in_leb_any_nil : core.


Lemma all_in_leb_perm_trans :
    forall A key l1 l2 l3,
    @all_in_leb A key l1 l3 ->
    Permutation l1 l2 ->
    all_in_leb key l2 l3.
Proof.
    intros; intros e1 e3 He1 He2.
    apply H; auto.
    apply Permutation_sym in H0.
    eapply Permutation_in; eauto.
Qed.

#[export] Hint Resolve all_in_leb_perm_trans : core.

Lemma all_in_leb_trans :
    forall A key l1 l2 l3,
    @all_in_leb A key l1 l2 ->
    @all_in_leb A key l2 l3 ->
    (exists x, In x l2) ->
    all_in_leb key l1 l3.
Proof.
    intros; intros e1 e3 He1 He2.
    destruct H1 as (e2, H1).
    split_andb_leb.
    unfold all_in_leb in *.
    assert (key e1 <= key e2 /\ key e2 <= key e3); repeat split; auto.
    apply leb_complete; auto.
    apply leb_complete; auto.
    lia.
Qed.


Lemma all_in_leb_app_head_1 :
    forall A key l1 l2 otherlst,
        @all_in_leb A key (l1 ++ l2) otherlst ->
        all_in_leb key l1 otherlst.
Proof.
    intros A key l1 l2 otherlst H1 e1 e2 Hi1 Hi2.
    apply H1; auto.
    apply in_or_app; auto.
Qed.

Lemma all_in_leb_app_head_2 :
    forall A key l1 l2 otherlst,
        @all_in_leb A key (l1 ++ l2) otherlst ->
        all_in_leb key l2 otherlst.
Proof.
    intros A key l1 l2 otherlst H1 e1 e2 Hi1 Hi2.
    apply H1; auto.
    apply in_or_app; auto.
Qed.

Lemma all_in_leb_app_tail_1 :
    forall A key l1 l2 somelst,
        @all_in_leb A key somelst (l1 ++ l2) ->
        all_in_leb key somelst l1.
Proof.
    intros A key l1 l2 somelst H1 e1 e2 Hi1 Hi2.
    apply H1; auto.
    apply in_or_app; auto.
Qed.

Lemma all_in_leb_app_tail_2 :
    forall A key l1 l2 somelst,
        @all_in_leb A key somelst (l1 ++ l2) ->
        all_in_leb key somelst l2.
Proof.
    intros A key l1 l2 somelst H1 e1 e2 Hi1 Hi2.
    apply H1; auto.
    apply in_or_app; auto.
Qed.


Lemma all_in_leb_perm : 
    forall A key l1 l2 l3 l4,
    Permutation l1 l2 ->
    Permutation l3 l4 ->
    @all_in_leb A key l1 l3 ->
    all_in_leb key l2 l4.
Proof.
    intros A key l1 l2 l3 l4 Hp1 Hp2 Hall e1 e2 Hi1 Hi2.
    assert (In e1 l1); eauto using Permutation_in, Permutation_sym.
Qed.

#[export] Hint Resolve 
                all_in_leb_app_tail_1 all_in_leb_app_tail_2
             all_in_leb_app_head_2 all_in_leb_app_head_1
             all_in_leb_perm
              : core.


Lemma all_in_leb_app_lst :
    forall A key lst l1 l2,
    @all_in_leb A key l1 lst ->
    all_in_leb key l2 lst ->
    all_in_leb key (l1 ++ l2) lst.
Proof.
    intros.
    intros e1 e2 Hi1 Hi2.
    apply in_app_or in Hi1.
    inversion_clear Hi1; auto.
Qed.


Lemma all_in_leb_lst_app :
    forall A key lst l1 l2,
    @all_in_leb A key lst l1 ->
    all_in_leb key lst l2 ->
    all_in_leb key lst (l1 ++ l2).
Proof.
    intros.
    intros e1 e2 Hi1 Hi2.
    apply in_app_or in Hi2.
    inversion_clear Hi2; auto.
Qed.

#[export] Hint Resolve all_in_leb_app_lst all_in_leb_lst_app : core.


Lemma perm_app_in_or :
    forall A (a b c : list A) x,
    Permutation (a ++ b) c ->
    In x c ->
    In x a \/ In x b.
Proof.
    intros.
    apply in_app_or.
    apply Permutation_in with c; auto.
Qed.


Lemma all_in_leb_perm_combine :
    forall A key eSm eLg lstSm lstLg result leftover,
    Permutation (eSm ++ lstSm) result ->
    Permutation (eLg ++ lstLg) leftover ->
    @all_in_leb A key result leftover ->
    all_in_leb key eSm eLg /\
    all_in_leb key eSm lstLg /\
    all_in_leb key lstSm eLg /\
    all_in_leb key lstSm lstLg.
Proof.
    intros; repeat split.
    apply all_in_leb_app_head_1 with lstSm; apply all_in_leb_app_tail_1 with lstLg; eauto.
    apply all_in_leb_app_head_1 with lstSm; apply all_in_leb_app_tail_2 with eLg; eauto.
    apply all_in_leb_app_head_2 with eSm; apply all_in_leb_app_tail_1 with lstLg; eauto.
    apply all_in_leb_app_head_2 with eSm; apply all_in_leb_app_tail_2 with eLg; eauto.
Qed.



Lemma insert_bounded_relate_perm :
    forall K A key e pq lst
    (Hpriq : priq A key pq)
    (Habs : Abs A key pq lst),
    exists eSm eLg lstSm lstLg result leftover,
        priq A key (insert_bounded K A key e pq) /\
        Abs A key (insert_bounded K A key e pq) result /\
        Permutation (eSm ++ eLg) [e] /\
        Permutation (lstSm ++ lstLg) lst /\
        Permutation (eSm ++ lstSm) result /\
        Permutation (eLg ++ lstLg) leftover /\
        all_in_leb key result leftover /\
        (size A key pq < K -> eSm = [e] /\ eLg = [] /\ lstSm = lst /\ lstLg = []) /\
        (K <= size A key pq -> exists e', Permutation (eLg ++ lstLg) [e']).
Proof.
    unfold insert_bounded; intros.
    destruct (K <? size A key (insert A key e pq)) eqn:Hlt; split_andb_leb.
    {
        pose proof (insert_delete_max_some A key e _ _ Hpriq Habs) as (k, (q, Hdm));
        rewrite Hdm.
        pose proof (delete_max_Some_priq _ _ _ _ _ (insert_priq _ _ _ _ Hpriq) Hdm) as Hpriqq.
        pose proof (delete_max_ex_Some_relate A key (insert A key e pq) q k (e :: lst) (insert_priq _ _ _ _ Hpriq)
                    (insert_relate _ _ _ _ _ Hpriq Habs) Hdm) as (ql, (Habs', _)).
        pose proof Hdm as Hdm'.
        apply delete_insert_relate_perm with (pl:=lst) (ql:=ql) in Hdm'; auto.
        inversion_clear Hdm'; split_andb_leb.
        {
            exists []; exists [e]; exists lst; exists [].
            exists ql; exists [e]; repeat split; auto.
            rewrite app_nil_end; auto.
            pose proof Hdm as Hdm';
            apply delete_max_Some_relate with (pl := e::lst) (ql := ql) in Hdm' as (Hdms, Hcomp); auto using insert_priq, insert_relate;
            fold compare in Hcomp.
            rewrite forallb_forall in *.
            intros e1 e2 He1 He2.
            replace e2 with e.
            2: { inversion He2; auto. inversion H. }
            replace k with e in *; auto.
            pose proof (Hcomp _ He1). destruct (key e1 ?= key e) eqn:Heq; try discriminate;
            split_andb_leb. apply Nat.compare_eq in Heq; lia.
            apply nat_compare_Lt_lt in Heq; lia.
            intros; rewrite insert_size with (al := lst) in Hlt; auto; try lia.
            intros; rewrite insert_size with (al := lst) in Hlt; auto; try lia.
            intros; exists e; rewrite <- app_nil_end; auto.
        }
        {
            pose proof Hdm as Hdm';
            apply delete_max_Some_relate with (pl := e::lst) (ql := ql) in Hdm' as (Hdms, Hcomp); auto using insert_priq, insert_relate;
                    fold compare in Hcomp.
            destruct H as (pl', (ql', (Hp1, (Hp2, Hp3)))).
            exists [e]; exists [].
            exists pl'. exists [k].
            exists ql; exists [k]. simpl; repeat split; auto.
            permtrans ([k] ++ pl'); auto.
            permtrans (e :: ql'); auto.
            assert (@forallb A (fun (a : A) => (NatTTLB.leb (key a) (key k))) ql = true); auto.
            rewrite forallb_forall in *.
            intros e1 e2 He1 He2.
            replace e2 with k. 2: { inversion He2; auto. inversion H0. }
            apply leb_correct, NatTTLB.leb_le; auto.
            rewrite insert_size with (al := lst) in Hlt; auto; try lia.
            rewrite insert_size with (al := lst) in Hlt; auto; try lia.
            intros; eauto.
        }
    }
    {
        exists [e]; exists [].
        exists lst; exists [].
        exists (e :: lst); exists [].
        repeat split; try rewrite <- app_nil_end; auto.
        rewrite insert_size with (al := lst) in Hlt; auto; try lia.
    }
Qed.




Lemma insert_bounded_relate :
    forall K A key e pq lst
    (Hpriq : priq A key pq)
    (Habs : Abs A key pq lst),
    exists result,
        priq A key (insert_bounded K A key e pq) /\
        Abs A key (insert_bounded K A key e pq) result /\
        (size A key pq < K -> Permutation result (e :: lst)) /\
        (K <= size A key pq -> exists e', Permutation (e' :: result) (e :: lst)
                                        /\ geb_all_in key e' result).
Proof.
    intros.
    pose proof (insert_bounded_relate_perm K A key e pq lst Hpriq Habs)
        as (eSm, (eLg, (lstSm, (lstLg, (result, (leftover, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, H9)))))))))))))).
    exists result.
    repeat split; auto.
    intros Hsz.
    apply H8 in Hsz; split_andb_leb.
    replace (e :: lst) with ([e] ++ lst); auto.
    replace [e] with eSm; replace lst with lstSm; auto.
    intros Hsz.
    apply H9 in Hsz as (e', He').
    exists e'; split; auto.
    {
        replace (e' :: result) with ([e'] ++ result); auto.
        permtrans ((eLg ++ lstLg) ++ result).
        permtrans ((eLg ++ lstLg) ++ (eSm ++ lstSm)).
        permtrans (eSm ++ (eLg ++ lstLg) ++ lstSm).
        replace (eSm ++ (eLg ++ lstLg) ++ lstSm) with ((eSm ++ (eLg ++ lstLg)) ++ lstSm); auto.
        replace (eSm ++ eLg ++ lstLg) with ((eSm ++ eLg) ++ lstLg); auto.
        replace (((eSm ++ eLg) ++ lstLg) ++ lstSm) with ((eSm ++ eLg) ++ lstLg ++ lstSm); auto.
        permtrans ([e] ++ lstLg ++ lstSm).
        simpl; apply perm_skip.
        permtrans (lstSm ++ lstLg); eauto.
    }
    {
        intros r Hr.
        apply H7; auto.
        apply Permutation_sym in He'.
        eapply Permutation_in; eauto.
        apply Permutation_in with [e']; auto. left; auto.
    }
Qed.




Lemma NatTTLBleb_le : forall a b, NatTTLB.leb a b = true -> a <= b.
Proof.
    intros.
    unfold NatTTLB.leb in H; fold compare in *.
    destruct (a ?= b) eqn:Hceq; try lia.
    apply nat_compare_eq in Hceq; lia.
    apply nat_compare_Lt_lt in Hceq; lia.
Qed.

Lemma NatTTLBleb_leb : forall a b, NatTTLB.leb a b = true -> a <=? b = true.
Proof.
    intros.
    split_andb_leb.
    auto using NatTTLBleb_le.
Qed.




Lemma knn_relate :
    forall K k tree bb query pq lst
    (Hpriq : priq datapt (sum_dist query) pq)
    (Habs : Abs _ _ pq lst),
    exists lst', priq _ _ (knn K k tree bb query pq) /\ Abs _ _ (knn K k tree bb query pq) lst'.
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ]; intros; [ simpl; eauto | ].
    pose proof (insert_bounded_relate K _ _ pt _ _ Hpriq Habs) as (lsti, (Hi1, (Hi2, _))).
    destruct (IHlft (fst (bb_split bb ax (nth ax pt 0))) query 
            (insert_bounded K datapt (sum_dist query) pt pq)
                lsti) as (lstLft, (Hlft1, Hlft2)); auto.
    destruct (IHrgt (snd (bb_split bb ax (nth ax pt 0))) query 
                (insert_bounded K datapt (sum_dist query) pt pq)
                    lsti) as (lstRgt, (Hrgt1, Hrgt2)); auto.
    simpl.
    destruct (peek_max datapt (sum_dist query) pq) as [ top | ] eqn:Hpeek.
    1: {
        destruct ((K <=? size datapt (sum_dist query) pq) &&
                (sum_dist query top <? sum_dist query (closest_edge_point query bb))).
        eauto.
        destruct (ith_leb ax pt query) eqn:Hith.
        apply IHrgt with lstLft; auto.
        apply IHlft with lstRgt; auto.
    }
    1: {
        destruct (ith_leb ax pt query) eqn:Hith.
        apply IHrgt with lstLft; auto.
        apply IHlft with lstRgt; auto.
    }
Qed.


Lemma insert_bounded_preserve_max :
        forall K A key e pq lst
        (Hpriq: priq A key pq)
        (Habs: Abs A key pq lst)
        (HK: size A key pq = K),
        size A key (insert_bounded K A key e pq) = K.
Proof.
    unfold insert_bounded; intros.
    rewrite insert_size with (al:=lst); auto.
    rewrite HK.
    replace (K <? 1 + K) with true.
    2: { destruct (K <? 1 + K) eqn:Hk; auto; split_andb_leb; lia. }
    pose proof (insert_delete_max_some _ _ e _ _ Hpriq Habs) as (k, (q, Hd)).
    rewrite Hd.
    apply delete_max_Some_size with (p:=(insert A key e pq)) (k:=k) (pl:=e::lst) ; auto.
    rewrite <- HK.
    eapply insert_size; eauto.
Qed.


Lemma insert_bounded_preserve_max_le :
        forall K A key e pq lst
        (Hpriq: priq A key pq)
        (Habs: Abs A key pq lst)
        (HK: K <= size A key pq),
        K <= size A key (insert_bounded K A key e pq).
Proof.
    unfold insert_bounded; intros.
    rewrite insert_size with (al:=lst); auto.
    replace (K <? 1 + size A key pq) with true.
    2:{ symmetry. apply Nat.ltb_lt. lia. }
    pose proof (insert_delete_max_some _ _ e _ _ Hpriq Habs) as (k, (q, Hd)); auto.
    rewrite Hd; auto.
    pose proof (insert_size _ _ _ _ e Hpriq Habs).
    assert (size A key q = size A key pq); try lia.
    apply delete_max_Some_size with (p:=(insert A key e pq)) (k:=k) (pl:=e::lst) ; auto.
Qed.


Lemma insert_bounded_preserve_max_eq :
        forall K A key e pq lst
        (Hpriq: priq A key pq)
        (Habs: Abs A key pq lst)
        (HK: K <= size A key pq),
        size A key pq = size A key (insert_bounded K A key e pq).
Proof.
    unfold insert_bounded; intros.
    rewrite insert_size with (al:=lst); auto.
    replace (K <? 1 + size A key pq) with true.
    2:{ symmetry. apply Nat.ltb_lt. lia. }
    pose proof (insert_delete_max_some _ _ e _ _ Hpriq Habs) as (k, (q, Hd)); auto.
    rewrite Hd; auto.
    pose proof (insert_size _ _ _ _ e Hpriq Habs).
    assert (size A key q = size A key pq); try lia.
    apply delete_max_Some_size with (p:=(insert A key e pq)) (k:=k) (pl:=e::lst) ; auto.
Qed.


Lemma insert_bounded_lt_preserve_max :
        forall K A key e pq lst
        (Hpriq: priq A key pq)
        (Habs: Abs A key pq lst)
        (HK: size A key pq < K),
        size A key (insert_bounded K A key e pq) = 1 + size A key pq.
Proof.
    unfold insert_bounded; intros.
    rewrite insert_size with (al:=lst); auto.
    destruct (K <? 1 + size A key pq) eqn:Hklt; split_andb_leb; try lia.
    eapply insert_size; eauto.
Qed.


Lemma insert_bounded_le_preserve_max :
        forall K A key e pq lst,
        priq A key pq ->
        Abs A key pq lst ->
        size A key pq <= K ->
        size A key (insert_bounded K A key e pq) <= K.
Proof.
    intros.
    assert (size A key pq = K \/ size A key pq < K) as Hor; try lia.
    inversion Hor.
    assert (size A key (insert_bounded K A key e pq) = K); try lia.
    eapply insert_bounded_preserve_max; eauto.
    erewrite insert_bounded_lt_preserve_max; eauto.
Qed.




Lemma knn_search_build_size_gen :
    forall tree bb K k data query pq lst
    (Hpriq : priq _ _ pq)
    (Habs  : Abs _ _ pq lst)
    (Htree : Contents_kdtree tree data)
    (Hpqsz : size _ _ pq <= K),
    size datapt (sum_dist query) (knn K k tree bb query pq) = (min K ((length data) + (size _ _ pq))).
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ].
    - 
    intros; simpl.
    inversion Htree.
    simpl. lia.
    - 
    intros; simpl.
    inversion Htree; clear ax0 pt0 lft0 rgt0 H H0 H2 H3.
    pose proof (insert_bounded_relate K _ _ pt _ _ Hpriq Habs) as (lst', (Hpriq', (Habs', _))).
    pose proof (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query
    (insert_bounded K datapt (sum_dist query) pt pq) lst' Hpriq' Habs') as 
        (lst'', (Hpriq'', Habs'')).
    pose proof (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
        (insert_bounded K datapt (sum_dist query) pt pq) lst' Hpriq' Habs') as 
            (lst''', (Hpriq''', Habs''')); auto.

    destruct (peek_max datapt (sum_dist query) pq) as [ top | ] eqn:Hpeek.
    --  
        destruct (K <=? size datapt (sum_dist query) pq) eqn:Hksz; simpl.
        destruct (sum_dist query top <? sum_dist query (closest_edge_point query bb)) eqn:Hsd.
        split_andb_leb; simpl; lia.
        split_andb_leb.
        assert (size datapt (sum_dist query) pq = K); try lia.
        eapply insert_bounded_preserve_max with (e := pt) in H as Hib; eauto.
        1: {
            destruct (ith_leb ax pt query) eqn:Hith.
            ---
                rewrite IHrgt with (data:=lst2) (lst:=lst''); auto; try lia.
                rewrite IHlft with (data:=lst1) (lst:=lst'); auto; try lia.
                rewrite IHlft with (data:=lst1) (lst:=lst'); auto; try lia.
            ---
                rewrite IHlft with (data:=lst1) (lst:=lst'''); auto; try lia.
                rewrite IHrgt with (data:=lst2) (lst:=lst'); auto; try lia.
                rewrite IHrgt with (data:=lst2) (lst:=lst'); auto; try lia.
        }

        split_andb_leb.
        apply (insert_bounded_lt_preserve_max) with (e := pt) (lst := lst) in Hksz  as Hib; eauto. 
        destruct (ith_leb ax pt query) eqn:Hith.
        ---
        rewrite IHrgt with (data:=lst2) (lst:=lst''); auto; try (rewrite Hib; lia).
        rewrite IHlft with (data:=lst1) (lst:=lst'); auto; try (rewrite Hib; lia).
        simpl; rewrite app_length; simpl.
        rewrite Hib; lia.
        rewrite IHlft with (data:=lst1) (lst:=lst'); auto; try (rewrite Hib; lia).
        ---
        rewrite IHlft with (data:=lst1) (lst:=lst'''); auto; try (rewrite Hib; lia).
        rewrite IHrgt with (data:=lst2) (lst:=lst'); auto; try (rewrite Hib; lia).
        simpl; rewrite app_length; rewrite Hib; lia.
        rewrite IHrgt with (data:=lst2) (lst:=lst'); auto; try (rewrite Hib; lia).


    --
    eapply insert_bounded_le_preserve_max with (e:=pt) in Hpqsz as Hible; eauto.

    assert (0 = K \/ 0 < K) as Hkor; try lia.
    inversion_clear Hkor as [ Hk0 | Hklt ]; try lia.
    1: {
        destruct (ith_leb ax pt query) eqn:Hith.
        rewrite IHrgt with (data:=lst2) (lst:=lst''); auto; try lia.
        rewrite IHlft with (data:=lst1) (lst:=lst'); auto; try lia.
        rewrite IHlft with (data:=lst1) (lst:=lst'''); auto; try lia.
        rewrite IHrgt with (data:=lst2) (lst:=lst'); auto; try lia.
    }

    assert (size _ _ pq = 0) as Hsz.
    1: {
        assert (Abs _ _ pq []).
        apply peek_max_None_relate; auto.
        apply size_zero_relate; auto.
    }
    assert (size _ _ pq < K) as Hszltk; try lia.
    eapply insert_bounded_lt_preserve_max with (e:=pt) in Hszltk as Hib; eauto.
    rewrite Hsz. replace (length (pt :: lst1 ++ lst2) + 0) with (length (pt :: lst1 ++ lst2)); 
            try lia.
    destruct (ith_leb ax pt query) eqn:Hith.
        ---
        rewrite IHrgt with (data:=lst2) (lst:=lst''); auto; try (rewrite Hib; lia).
        rewrite IHlft with (data:=lst1) (lst:=lst'); auto; try (rewrite Hib; lia).
        simpl; rewrite app_length; rewrite Hib; lia.
        rewrite IHlft with (data:=lst1) (lst:=lst'); auto; try (rewrite Hib; lia).
        ---
        rewrite IHlft with (data:=lst1) (lst:=lst'''); auto; try (rewrite Hib; lia).
        rewrite IHrgt with (data:=lst2) (lst:=lst'); auto; try (rewrite Hib; lia).
        simpl; rewrite app_length; rewrite Hib; lia.
        rewrite IHrgt with (data:=lst2) (lst:=lst'); auto; try (rewrite Hib; lia).
Qed.




Lemma knn_search_build_size :
    forall K k data query
    (Hk : 0 < k),
    size datapt (sum_dist query) 
        (knn K k (build_kdtree k data)
                 (mk_bbox (repeat None k) (repeat None k)) 
                 query (empty _ _)) 
        = min K (length data).
Proof.
    intros.
    pose proof (build_kdtree_contents_perm _ data Hk) as (lst, (Hc1, Hc2)).
    assert (Abs _ _ (empty datapt (sum_dist query)) []) as Habs.
    1: { apply empty_relate; auto. }
    assert (size datapt (sum_dist query) (empty datapt (sum_dist query)) = 0).
    1: { apply size_zero_relate; auto. }
    rewrite (Permutation_length Hc2).
    rewrite knn_search_build_size_gen with (data := lst) (lst := []); auto; try lia.
Qed.




Ltac inversion_In := 
    try (match goal with 
        | H : (In _ []) |- _ => inversion H
        | H : (In _ (_ :: _)) |- _ => destruct H as [ H | H ]
         end).


Lemma in_perm : 
    forall A (x:A) a (Hin: In x a), exists a', Permutation a (x :: a').
Proof.
    induction a as [ | h t ]; intros; inversion_In.
    rewrite Hin; eauto.
    specialize (IHt Hin) as (a', Ha'); eauto.
    (* apply IHt in Hin as (a', Ha'). *)
Qed.

Lemma perm_app_cons_inv : 
    forall A a b h t
    (Hperm: @Permutation A (a ++ b) (h :: t)),
    (exists a', Permutation a (h :: a')) \/
    (exists b', Permutation b (h :: b')).
Proof.
    intros.
    assert (In h (a ++ b)).
    apply Permutation_in with (h :: t); auto; left; auto.
    destruct (in_app_or _ _ _ H); [ left | right ].
    eapply in_perm; eauto.
    eapply in_perm; eauto.
Qed.




Lemma perm_app_cons_inv_tail_left : 
    forall A a a' b h t 
      (Hp1: Permutation (a ++ b) (h :: t))
      (Hp2: Permutation a (h :: a')),
     @Permutation A (a' ++ b) t.
Proof.
    intros.
    assert (Permutation (h :: (a' ++ b)) (h :: t)).
    permtrans (a ++ b).
    replace (h :: a' ++ b) with ((h :: a') ++ b); auto.
    eapply Permutation_cons_inv; eauto.
Qed.

Lemma perm_app_cons_inv_tail_right : 
    forall A a b b' h t 
      (Hp1: Permutation (a ++ b) (h :: t))
      (Hp2: Permutation b (h :: b')),
     @Permutation A (a ++ b') t.
Proof.
    intros.
    assert (Permutation (h :: a ++ b') (h :: t)).
    permtrans (a ++ b).
    permtrans (a ++ h :: b').
    eapply Permutation_cons_inv; eauto.
Qed.


#[export] Hint Resolve perm_app_cons_inv_tail_left perm_app_cons_inv_tail_right : core.


Lemma perm_split_rearrange :
    forall A lst (a:list A) b c d
        (Hab : Permutation (a ++ b) lst)
        (Hde : Permutation (c ++ d) lst),
        exists a1 a2 b1 b2, Permutation (a1 ++ a2) a /\
                            Permutation (b1 ++ b2) b /\
                            Permutation (a1 ++ b1) c /\
                            Permutation (a2 ++ b2) d.
Proof.
    induction lst as [ | h t]; intros.
    {
        exists []; exists []; exists []; exists []; simpl.
        apply Permutation_sym in Hab, Hde.
        apply Permutation_nil in Hab, Hde.
        apply app_eq_nil in Hab, Hde; split_andb_leb.
        repeat match goal with H : _ = [] |- _ => rewrite H; clear H end.
        repeat split; auto.
    }
    {
        pose proof Hab as Hab'; apply perm_app_cons_inv in Hab'.
        pose proof Hde as Hde'; apply perm_app_cons_inv in Hde'.
        inversion_clear Hab'; inversion_clear Hde'.
        -
            destruct H as (a', Ha'); destruct H0 as (c', Hd').
            assert (Permutation (a' ++ b) t); eauto.
            assert (Permutation (c' ++ d) t); eauto.
            pose proof (IHt a' b c' d H H0) as (a1, (a2, (b1, (b2, (Ha, (Hb, (Hd, He))))))).
            exists (h :: a1); exists a2; exists b1; exists b2; repeat split; auto.
            simpl; permtrans (h :: a').
            simpl; permtrans (h :: c').
        -
            destruct H as (a', Ha'); destruct H0 as (d', He').
            assert (Permutation (a' ++ b) t); eauto.
            assert (Permutation (c ++ d') t); eauto.
            pose proof (IHt a' b c d' H H0) as (a1, (a2, (b1, (b2, (Ha, (Hb, (Hd, He))))))).
            exists a1; exists (h :: a2); exists b1; exists b2; repeat split; auto.
            simpl; permtrans (h :: a').
            permtrans (h :: a1 ++ a2).
            simpl; permtrans (h :: d').
        -
            destruct H as (b', Hb'); destruct H0 as (c', Hd').
            assert (Permutation (a ++ b') t); eauto.
            assert (Permutation (c' ++ d) t); eauto.
            pose proof (IHt a b' c' d H H0) as (a1, (a2, (b1, (b2, (Ha, (Hb, (Hd, He))))))).
            exists a1; exists a2; exists (h :: b1); exists b2; repeat split; auto.
            simpl; permtrans (h :: b').
            simpl; permtrans (h :: c').
            permtrans (h :: a1 ++ b1).
        - 
            destruct H as (b', Hb'); destruct H0 as (d', He').
            assert (Permutation (a ++ b') t); eauto.
            assert (Permutation (c ++ d') t); eauto.
            pose proof (IHt a b' c d' H H0) as (a1, (a2, (b1, (b2, (Ha, (Hb, (Hd, He))))))).
            exists a1; exists a2; exists b1; exists (h::b2); repeat split; auto.
            simpl; permtrans (h :: b').
            permtrans (h :: b1 ++ b2).
            permtrans (h :: a2 ++ b2).
            permtrans (h :: d').
    }
Qed.


Lemma perm_split_all_in_leb : 
    forall A key (lst:list A) a b c d f g
    (Hplst : Permutation (a ++ b) lst)
    (Hpf : Permutation (a ++ c) f)
    (Hpg : Permutation (b ++ d) g)
    (Hleb : @all_in_leb A key f g),
    all_in_leb key a b.
Proof.
    destruct lst as [ | h t]; intros.
    {  
        apply Permutation_sym, Permutation_nil, app_eq_nil in Hplst; split_andb_leb.
        intros e1 e2 He1 He2; replace a with (@nil A) in He1; auto; inversion He1.
    }
    {
        intros e1 e2 He1 He2.
        apply Hleb.
        apply Permutation_in with (a ++ c); auto; apply in_or_app; auto.
        apply Permutation_in with (b ++ d); auto; apply in_or_app; auto.
    }
Qed.

#[export] Hint Resolve perm_split_all_in_leb : core.


Lemma perm_split_rearrange_all_in_leb :
    forall A key lst (a:list A) b c d
        (Hab : Permutation (a ++ b) lst)
        (Hde : Permutation (c ++ d) lst)
        (Hleb : @all_in_leb A key c d),
        exists a1 a2 b1 b2, Permutation (a1 ++ a2) a /\
                            Permutation (b1 ++ b2) b /\
                            Permutation (a1 ++ b1) c /\
                            Permutation (a2 ++ b2) d /\
                            all_in_leb key a1 a2 /\
                            all_in_leb key b1 b2.
Proof.
    intros.
    pose proof (perm_split_rearrange _ _ _ _ _ _ Hab Hde) as (a1, (a2, (b1, (b2, (H1, (H2, (H3, H4))))))).
    exists a1; exists a2; exists b1; exists b2; repeat split; auto.
    eapply perm_split_all_in_leb; eauto.
    rewrite Permutation_app_comm in Hab, H3, H4.
    eapply perm_split_all_in_leb; eauto.
Qed.






Lemma knn_preserve_size_max :
    forall K k tree bb query pq lst
    (Hpriq : priq datapt (sum_dist query) pq)
    (Habs : Abs _ _ pq lst)
    (Heq_Ksize: K <= size datapt (sum_dist query) pq),
    size datapt (sum_dist query) pq = size datapt (sum_dist query) (knn K k tree bb query pq).
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ]; intros; auto.
    simpl.

    pose proof (insert_bounded_relate K _ _ pt pq lst Hpriq Habs) as (resi, (Hp1, (Ha1, _))).
    assert (K <= size datapt (sum_dist query) (insert_bounded K datapt (sum_dist query) pt pq)); try lia.
    { erewrite <- insert_bounded_preserve_max_eq; eauto. }
    assert (size datapt (sum_dist query) pq = size datapt (sum_dist query) (insert_bounded K datapt (sum_dist query) pt pq)).
    { erewrite <- insert_bounded_preserve_max_eq; eauto. }

    assert (size datapt (sum_dist query) pq =
        size datapt (sum_dist query)
          (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
             (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query (insert_bounded K datapt (sum_dist query) pt pq))))
            as Hsz_knn_lft_rgt.         
    {
        pose proof (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query _ _ Hp1 Ha1)
            as (pqlstLft, (Hp2, Ha2)).
        pose proof (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query _ _ Hp2 Ha2)
            as (pqlstRgt, (Hp3, Ha3)).
        erewrite <- IHrgt; eauto.
        erewrite <- IHlft; eauto.
        erewrite <- IHlft; eauto.
    }

    assert (size datapt (sum_dist query) pq =
    size datapt (sum_dist query)
      (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
         (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query (insert_bounded K datapt (sum_dist query) pt pq)))
    ) as Hsz_knn_rgt_lft.
    {
        pose proof (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query _ _ Hp1 Ha1)
            as (pqlstRgt, (Hp2, Ha2)).
        pose proof (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query _ _ Hp2 Ha2)
            as (pqlstLft, (Hp3, Ha3)).
            erewrite <- IHlft; eauto.
            erewrite <- IHrgt; eauto.
            erewrite <- IHrgt; eauto.
    }

    destruct (peek_max datapt (sum_dist query) pq) eqn:Heq1; [ | destruct (ith_leb ax pt query) eqn:Heq3 ]; auto.
    destruct ((K <=? size datapt (sum_dist query) pq) && (sum_dist query d <? sum_dist query (closest_edge_point query bb))) eqn:Heq2; auto.
    destruct (ith_leb ax pt query) eqn:Heq3; auto.
Qed.



Lemma knn_preserve_size_lt_inv :
    forall K k tree bb query pq lst data
    (Hpriq : priq datapt (sum_dist query) pq)
    (Habs : Abs _ _ pq lst)
    (Hcont : Contents_kdtree tree data)
    (HltK : size datapt (sum_dist query) (knn K k tree bb query pq) < K),
    size datapt (sum_dist query) pq < K.
Proof.
    intros.
    destruct (Nat.lt_ge_cases (size datapt (sum_dist query) pq) K); auto.
    erewrite knn_preserve_size_max; eauto.
Qed.


(*
  This lemma's proof is ridiculously long and needs to be refactored.
  Problems: - duplicate proofs for the different execution paths in the 
            function (when `destruct`ing on the conditionals)
            - permutation stuff needs to be automated
*)
Lemma knn_full_relate_gen :
    forall K k tree bb query pq lst data result
    (HK : 0 < K)
    (Hb : kdtree_bounded tree bb = true)
    (Htree : Contents_kdtree tree data)
    (Hpriq : priq datapt (sum_dist query) pq)
    (Habs : Abs _ _ pq lst)
    (Hpriq' : priq _ _ (knn K k tree bb query pq))
    (Habs' : Abs _ _ (knn K k tree bb query pq) result),

    exists lstSm lstLg dataSm dataLg leftover,
        Permutation (lstSm ++ lstLg) lst /\
        Permutation (dataSm ++ dataLg) data /\
        Permutation (lstSm ++ dataSm) result /\
        Permutation (lstLg ++ dataLg) leftover /\
        (size _ _ (knn K k tree bb query pq) < K -> leftover = []) /\
        all_in_leb (sum_dist query) result leftover.
Proof.
    induction tree as [ | ax pt lft IHlft rgt IHrgt ]; intros.
    { (* empty tree *)
        simpl in *.
        replace data with (@nil datapt) in *. 2: { inversion Htree; auto. }
        assert (Permutation lst result)as Hperm; eauto.
        assert (lst ++ [] = lst); auto.
        exists lst; exists []; exists []; exists []; exists []; simpl; rewrite H; repeat split; auto.
    }

    simpl in Habs', Hpriq'.
    destruct (peek_max datapt (sum_dist query) pq) eqn:Heq_peek.
    { (* peek is some *)
        destruct (K <=? size datapt (sum_dist query) pq) eqn:Heq_Ksize; simpl in Habs', Hpriq'.
        { (* K <= size pq *)
            assert (size datapt (sum_dist query) (knn K k (node ax pt lft rgt) bb query pq) < K -> data = [])
                    as Hnon_applicable.
            {
                split_andb_leb.
                intros Hcontra.
                erewrite <- knn_preserve_size_max in Hcontra; eauto. lia.
            }

            destruct (sum_dist query d <? sum_dist query (closest_edge_point query bb)) eqn:Heq_sumdist.
            { (* closest edge point is farther than the largest thing in the pq *)
                split_andb_leb.
                assert (Permutation lst result); eauto using abs_perm.
                exists lst; exists []; exists []; exists data; exists data.

                replace (lst ++ []) with lst; simpl; auto.
                repeat split; auto.
                intros e1 e2 He1 He2; split_andb_leb.
                assert (sum_dist query e1 <= sum_dist query d).
                {
                    pose proof (peek_max_Some_relate _ (sum_dist query) pq d result Hpriq Habs' Heq_peek) as 
                        (Hin, Hcmp);         rewrite forallb_forall in Hcmp.
                    pose proof (Hcmp e1 He1); fold compare in H0.
                    destruct (sum_dist query e1 ?= sum_dist query d) eqn:Heqd; try discriminate.
                    rewrite Nat.compare_eq_iff in Heqd; lia.
                    rewrite Nat.compare_lt_iff in Heqd; lia.
                }
                {
                assert (sum_dist query (closest_edge_point query bb) <= sum_dist query e2); try lia.
                apply closest_edge_point_min_dist.
                apply In_kdtree_bounded_bb_contains with (node ax pt lft rgt); auto.
                apply contents_in_kdtree with data; eauto using Permutation_in, Permutation_sym.
                }
            }

            { (* closest edge point is potentially closer than the top (largest thing) in the pq *)
                split_andb_leb.
                destruct (insert_bounded_relate_perm K datapt (sum_dist query) pt pq lst Hpriq Habs)
                    as (eSm, (eLg, (lstSm, (lstLg, (resi, (leftoveri, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, H9)))))))))))))).
                pose proof Heq_Ksize as Heq_Ksize'; apply H9 in Heq_Ksize' as (e', Hpermi).

                destruct (ith_leb ax pt query) eqn:Heq_ith.
                { (* ith = true --- insert_bounded (maxed out) then lft then rgt *)
                    destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query 
                                        (insert_bounded K datapt (sum_dist query) pt pq) _ H1 H2) as
                            (pqlstLft, (Hplft, Halft)).
                    destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0)))
                                        query _ _ Hplft Halft) as (pqlstRgt, (Hprgt, Hargt)).
                    pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                    destruct (cont_node_inv _ _ _ _ _ Htree) as (lftConts, (rgtConts, (Hcontlft, (Hcontrgt, Hconteq)))).
                    destruct (IHlft _ _ _ _ _ _
                            HK H11 Hcontlft H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                    destruct (IHrgt _ _ _ _ _ _ 
                            HK H0 Hcontrgt Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                    clear IHlft IHrgt.
                    rewrite Hconteq.
                    assert (Permutation result pqlstRgt).
                    { apply abs_perm with (sum_dist query)
                            (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                            (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                    }

                    assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                        H5 Hl1 HresiSm_Lg) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff)))).
                    assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                        Hl3 Hr1 HlresSm_Lg) as
                                    (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                    assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                    { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                    assert (Permutation (eSmSm ++ lstSmSm) resiSm) as HeSm1; try tauto.
                    assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                    assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                        HeSm1 HeSm2 HeSm3) as
                                        (eSmSmSm, (eSmSmLg, (lstSmSmSm, (lstSmSmLg, HresiStuff2)))).
                    assert (Permutation (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) lresSm).
                    {
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        replace (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) with ((eSmSmSm ++ lstSmSmSm) ++ lfttreeSmSm); auto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                    }

                    exists lstSmSmSm.
                    exists (lstLg ++ lstSmLg ++ lstSmSmLg).
                    exists (eSmSmSm ++ lfttreeSmSm ++ rgttreeSm).
                    exists (eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    exists (leftoveri ++ loLft ++ loRgt).
                    assert (Permutation (lstSmSmSm ++ lstLg ++ lstSmLg ++ lstSmSmLg) lst).
                    {
                        permtrans (lstLg ++ lstSmSmSm ++ lstSmLg ++ lstSmSmLg).
                        rewrite Permutation_app_comm in H4.
                        permtrans (lstLg ++ lstSm).
                        apply Permutation_app; auto.
                        assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                        rewrite Permutation_app_comm in H13.
                        permtrans (lstSmLg ++ lstSmSmSm ++ lstSmSmLg).
                        permtrans (lstSmLg ++ lstSmSm); auto.
                        apply Permutation_app; auto.
                        tauto.
                    }

                    assert (Permutation
                        ((eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                        (pt :: lftConts ++ rgtConts)).
                    {
                        repeat rewrite <- app_assoc; auto.
                        assert (eSmSmSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg =
                            eSmSmSm ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        rewrite app_assoc. repeat rewrite <- app_assoc; auto.
                        assert (Permutation
                        (eSmSmSm ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg) (pt :: lftConts ++ rgtConts)).
                        2:{ rewrite <- H14 in H15; auto. }
                        permtrans (eSmSmSm ++ eSmSmLg ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        assert (Permutation (eSmSmSm ++ eSmSmLg) eSmSm ); try tauto.
                        replace (eSmSmSm ++ eSmSmLg ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with ((eSmSmSm ++ eSmSmLg) ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        permtrans (eSmSm ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        replace (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) with ((lfttreeSmSm ++ rgttreeSm ++ eLg) ++ eSmLg); auto.
                        2:{ repeat rewrite <- app_assoc; auto. }
                        rewrite app_assoc.
                        permtrans ((eSmSm ++ eSmLg ++ (lfttreeSmSm ++ rgttreeSm ++ eLg)) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        repeat rewrite <- app_assoc; rewrite app_assoc.
                        assert (Permutation (eSmSm ++ eSmLg) eSm); try tauto.
                        permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        assert (Permutation (eSm ++ (lfttreeSmSm ++ rgttreeSm) ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                                (pt :: lftConts ++ rgtConts)).
                        2:{  repeat rewrite <- app_assoc in H17 ; auto. }
                        permtrans (eSm ++ eLg ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        replace (eSm ++ eLg ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with ((eSm ++ eLg) ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        permtrans ([pt] ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        replace (pt :: lftConts ++ rgtConts) with ([pt] ++ lftConts ++ rgtConts); auto.
                        apply Permutation_app; auto.
                        (* done [pt] !! *)
                        repeat rewrite <- app_assoc.
                        permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        assert (Permutation (lfttreeSmSm ++ lfttreeSmLg) lfttreeSm); try tauto.
                        rewrite app_assoc.
                        permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                        rewrite app_assoc.
                        permtrans (lftConts ++ rgttreeSm ++ rgttreeLg).
                    }
                    assert (Permutation (lstSmSmSm ++ eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                    {
                        permtrans pqlstRgt.
                        rewrite app_assoc. rewrite app_assoc.
                        permtrans (lresSm ++ rgttreeSm).
                        rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                        apply Permutation_app; apply Permutation_sym; auto.
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                        assert (Permutation (lstSmSmSm ++ eSmSmSm) resiSmSm); auto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        permtrans (eSmSmSm ++ lstSmSmSm).
                    }
                    assert (Permutation
                    ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                    (leftoveri ++ loLft ++ loRgt)).
                    {
                        permtrans (leftoveri ++ loLft ++ (lresLg ++ rgttreeLg)).
                        replace ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with (((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        replace (leftoveri ++ loLft ++ lresLg ++ rgttreeLg) with ((leftoveri ++ loLft ++ lresLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.
                        assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                        permtrans ((leftoveri ++ loLft) ++ (resiSmLg ++ lfttreeSmLg)).
                        2:{ replace (leftoveri ++ loLft ++ lresLg) with ((leftoveri ++ loLft) ++ lresLg); auto. }       
                        repeat rewrite <- app_assoc.
                        do 5 (rewrite app_assoc).
                        permtrans ((((((lstLg ++ lstSmLg) ++ lstSmSmLg) ++ eLg) ++ eSmLg) ++ eSmSmLg) ++ lfttreeLg ++ lfttreeSmLg).
                        rewrite app_assoc.
                        replace (leftoveri ++ loLft ++ resiSmLg ++ lfttreeSmLg) with ((leftoveri ++ loLft ++ resiSmLg) ++ lfttreeSmLg); 
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.

                        assert (Permutation (eSmSmLg ++ lstSmSmLg) resiSmLg); try tauto.
                        replace (leftoveri ++ loLft ++ resiSmLg) with ((leftoveri ++ loLft) ++ resiSmLg); auto.
                        permtrans (resiSmLg ++ (leftoveri ++ loLft)).
                        do 3 rewrite <- app_assoc.
                        permtrans ((lstSmSmLg ++ (lstLg ++ lstSmLg)) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeLg).
                        do 2 rewrite app_assoc.
                        permtrans (eSmSmLg ++ (((lstSmSmLg ++ lstLg ++ lstSmLg) ++ eLg) ++ eSmLg) ++ lfttreeLg).
                        repeat rewrite <- app_assoc.
                        rewrite app_assoc; apply Permutation_app; auto.
                        do 2 rewrite app_assoc.
                        permtrans  ((eLg ++ (lstLg ++ lstSmLg)) ++ eSmLg ++ lfttreeLg).
                        replace (eLg ++ lstLg ++ lstSmLg) with ((eLg ++ lstLg) ++ lstSmLg); auto.
                        rewrite <- app_assoc.
                        apply Permutation_app; auto.

                        assert (Permutation (eSmLg ++ lstSmLg) resiLg); try tauto.
                        assert (Permutation (lstSmLg ++ eSmLg) resiLg); [ permtrans (eSmLg ++ lstSmLg) | ].
                        rewrite app_assoc.
                        permtrans (resiLg ++ lfttreeLg).
                    }

                    repeat split; auto.
                    { (* non-applicable *)
                        intros Hcontra.
                        erewrite <- knn_preserve_size_max in Hcontra; eauto. lia.
                    }

                    {
                        assert (all_in_leb (sum_dist query) pqlstRgt (leftoveri ++ loLft ++ loRgt)).
                        2:{ apply all_in_leb_perm with pqlstRgt (leftoveri ++ loLft ++ loRgt); auto. }

                        rewrite app_assoc; apply all_in_leb_lst_app; auto.
                        assert (all_in_leb (sum_dist query) lresSm loLft) as H20.
                        {
                            apply all_in_leb_app_head_1 with lresLg.
                            apply all_in_leb_perm with pqlstLft loLft; auto.   
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_1 with rgttreeLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }
                        assert (all_in_leb (sum_dist query) lresLg loLft) as H40.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as H50.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_2 with lresLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }

                        pose proof Heq_Ksize as Heq_Ksize'; eapply insert_bounded_preserve_max_eq with (lst:=lst) in Heq_Ksize'; auto.
                        assert (K <= size datapt (sum_dist query) (insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        rewrite <- Heq_Ksize'; auto.

                        assert (K <= length pqlstLft) as H60.
                        {
                            replace (length pqlstLft) with (length lst).
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite Heq_Ksize'.
                            erewrite knn_preserve_size_max; eauto.
                        }
                        assert (length pqlstLft = length pqlstRgt) as H61.
                        {
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                   (insert_bounded K datapt (sum_dist query) pt pq)))); auto.
                            erewrite knn_preserve_size_max; eauto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                        { rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto. }

                        assert (length resi = length pqlstLft) as H63.
                        {
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                            rewrite <- Heq_Ksize'.
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length lst = length resi) as H64.
                        {
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        }

                        assert (length (resiSm ++ resiLg) = length (lresSm ++ lresLg)) as H65.
                        { rewrite (Permutation_length Hl1). rewrite (Permutation_length Hr1). auto. }

                        assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                        {
                            destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                            -   left.
                                rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length rgttreeSm = 0) as H66; try lia.
                                apply length_zero_iff_nil in H66.
                                rewrite H66; auto.
                            -   right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x rgttreeSm).
                                destruct rgttreeSm; simpl in *; try lia; eauto.
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl; eauto.
                        }

                        assert (length (resiSm ++ resiLg) = length (resiSm ++ lfttreeSm)) as H68.
                        {
                            rewrite (Permutation_length Hl3). rewrite <- H63. 
                            rewrite (Permutation_length Hl1); auto.
                        }
                        assert (lfttreeSm = [] \/ (exists x, In x lfttreeSm) /\ all_in_leb (sum_dist query) lfttreeSm leftoveri) as H69.
                        {
                            destruct resiLg as [ | x xs ] eqn:Heq_resiLg.
                            - left.
                                repeat rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length lfttreeSm = 0) as H69'; try lia.
                                apply length_zero_iff_nil in H69'.
                                rewrite H69'; auto.
                            - right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x lfttreeSm).
                                destruct lfttreeSm; simpl in *; try lia; eauto.
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                exists x; auto.
                        }

                        assert (all_in_leb (sum_dist query) lfttreeSm lfttreeLg) as H90.
                        {
                            apply all_in_leb_app_head_2 with resiSm; auto.
                            apply all_in_leb_app_tail_2  with resiLg; auto.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }

                        apply all_in_leb_lst_app; auto.

                        { (* pqlstRgt <= leftoveri*)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) leftoveri; auto.
                            apply all_in_leb_app_lst; auto.
                            { (* lresSm <= leftoveri *)
                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                -
                                rewrite Hd1 in *; repeat rewrite <- app_nil_end in *; rewrite app_length in *.
                                assert (lfttreeSm = []) as Hd3.
                                {
                                    destruct lfttreeSm; auto; simpl in H68; lia.
                                }
                                rewrite Hd3 in *; repeat rewrite <- app_nil_end in *; simpl in *.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                permtrans resiSm; auto.
                                permtrans pqlstLft; auto.
                                -
                                apply all_in_leb_trans with resiLg; auto.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                            }
                            { (* rgttreeSm <= leftoveri *)
                                destruct H67 as [ H67 | H67 ].
                                rewrite H67; auto.
                                
                                assert (all_in_leb (sum_dist query) rgttreeSm resiLg) as H95.
                                {
                                    apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                    inversion_clear H67.
                                    apply all_in_leb_perm with rgttreeSm loLft; auto.
                                }

                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                {   (* resiLg = [] *)
                                    repeat rewrite Hd1 in *; simpl in *.
                                    repeat rewrite <- app_nil_end in *.
                                    assert (lfttreeSm = []).
                                    -   simpl in *; repeat rewrite app_length in H68.
                                        destruct lfttreeSm; try (simpl in H68; lia); auto.
                                    -
                                    rewrite H18 in *; simpl in *; repeat rewrite <- app_nil_end in *.
                                    clear H69 H95 H90.
                                    destruct H67 as (H67a, H67b).
                                    assert (Permutation resiSm (lresSm ++ lresLg)).
                                    permtrans pqlstLft; auto.
                                    destruct (list_nil_or_in lresLg) as [ Habsurd | Hd2 ].
                                    { rewrite Habsurd in H62; rewrite <- app_nil_end in H62; repeat rewrite app_length in H62; simpl in H62.
                                      assert (0 < length rgttreeSm). destruct H67a; destruct rgttreeSm. inversion H21. simpl; lia.
                                      lia.
                                    }                                      

                                    apply all_in_leb_trans with lresLg; auto.
                                    apply all_in_leb_app_head_2 with lresSm; auto.
                                    apply all_in_leb_perm with resiSm leftoveri; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                                { (* exists x \in resiLg *)
                                    apply all_in_leb_trans with resiLg; auto.
                                    apply all_in_leb_app_head_2 with resiSm; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                            }
                        }
                        {  (* pqlstRgt <= loLft *)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                            apply all_in_leb_app_lst; auto.
                            destruct H67 as [ H67 | (H67a, H67b) ]; auto.
                            rewrite H67; auto.
                        }
                    }
                }

                { (* ith = false --- rgt then lft *)
                    (* apply MAGIC. *)
                    destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query 
                                        (insert_bounded K datapt (sum_dist query) pt pq) _ H1 H2) as
                            (pqlstLft, (Hplft, Halft)).
                    destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0)))
                                        query _ _ Hplft Halft) as (pqlstRgt, (Hprgt, Hargt)).
                    pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                    destruct (cont_node_inv _ _ _ _ _ Htree) as (lftConts, (rgtConts, (Hcontlft, (Hcontrgt, Hconteq)))).
                    destruct (IHrgt _ _ _ _ _ _
                            HK H0 Hcontrgt H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                    destruct (IHlft _ _ _ _ _ _ 
                            HK H11 Hcontlft Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                    clear IHlft IHrgt.
                    rewrite Hconteq.
                    assert (Permutation result pqlstRgt).
                    { apply abs_perm with (sum_dist query)
                            (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                            (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                    }

                    assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                        H5 Hl1 HresiSm_Lg) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff)))).
                    assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                        Hl3 Hr1 HlresSm_Lg) as
                                    (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                    assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                    { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                    assert (Permutation (eSmSm ++ lstSmSm) resiSm) as HeSm1; try tauto.
                    assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                    assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                        HeSm1 HeSm2 HeSm3) as
                                        (eSmSmSm, (eSmSmLg, (lstSmSmSm, (lstSmSmLg, HresiStuff2)))).
                    assert (Permutation (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) lresSm).
                    {
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        replace (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) with ((eSmSmSm ++ lstSmSmSm) ++ lfttreeSmSm); auto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                    }

                    exists lstSmSmSm.
                    exists (lstLg ++ lstSmLg ++ lstSmSmLg).
                    exists (eSmSmSm ++ lfttreeSmSm ++ rgttreeSm).
                    exists (eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    exists (leftoveri ++ loLft ++ loRgt).
                    assert (Permutation (lstSmSmSm ++ lstLg ++ lstSmLg ++ lstSmSmLg) lst).
                    {
                        permtrans (lstLg ++ lstSmSmSm ++ lstSmLg ++ lstSmSmLg).
                        rewrite Permutation_app_comm in H4.
                        permtrans (lstLg ++ lstSm).
                        apply Permutation_app; auto.
                        assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                        rewrite Permutation_app_comm in H13.
                        permtrans (lstSmLg ++ lstSmSmSm ++ lstSmSmLg).
                        permtrans (lstSmLg ++ lstSmSm); auto.
                        apply Permutation_app; auto.
                        tauto.
                    }

                    assert (Permutation
                        ((eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                        (pt :: lftConts ++ rgtConts)).
                    {
                        repeat rewrite <- app_assoc; auto.
                        do 4 rewrite app_assoc.
                        permtrans (eSmSmLg ++ ((((eSmSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg) ++ eSmLg) ++
                        lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto; repeat rewrite <- app_assoc.
                        permtrans (eSmSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; apply Permutation_app; auto.
                        permtrans (eSmSmSm ++ eSmSmLg). tauto.
                        do 3 rewrite app_assoc.
                        permtrans (eSmLg ++ (((eSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); repeat rewrite <- app_assoc.
                        replace (pt :: lftConts ++ rgtConts) with ([pt] ++ lftConts ++ rgtConts); auto.
                        permtrans (eSmSm ++ eSmLg ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        apply Permutation_app; auto. tauto.
                        do 2 rewrite app_assoc.
                        permtrans (eLg ++ ((eSm ++ lfttreeSmSm) ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); repeat rewrite <- app_assoc.
                        permtrans (eSm ++ eLg ++ lfttreeSmSm ++ rgttreeSm ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; apply Permutation_app; auto.
                        (* done [pt] *)
                        permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        apply Permutation_app; auto; tauto.
                        permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                        rewrite app_assoc; permtrans (rgtConts ++ rgttreeSm ++ rgttreeLg).
                        permtrans (rgtConts ++ lftConts).
                    }
                    assert (Permutation (lstSmSmSm ++ eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                    {
                        permtrans pqlstRgt.
                        rewrite app_assoc. rewrite app_assoc.
                        permtrans (lresSm ++ rgttreeSm).
                        rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                        apply Permutation_app; apply Permutation_sym; auto.
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                        assert (Permutation (lstSmSmSm ++ eSmSmSm) resiSmSm); auto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        permtrans (eSmSmSm ++ lstSmSmSm).
                    }
                    assert (Permutation
                    ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                    (leftoveri ++ loLft ++ loRgt)).
                    {
                        permtrans (leftoveri ++ loLft ++ (lresLg ++ rgttreeLg)).
                        replace ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with (((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        replace (leftoveri ++ loLft ++ lresLg ++ rgttreeLg) with ((leftoveri ++ loLft ++ lresLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.
                        assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                        permtrans ((leftoveri ++ loLft) ++ (resiSmLg ++ lfttreeSmLg)).
                        2:{ replace (leftoveri ++ loLft ++ lresLg) with ((leftoveri ++ loLft) ++ lresLg); auto. }       
                        repeat rewrite <- app_assoc.
                        do 5 (rewrite app_assoc).
                        permtrans ((((((lstLg ++ lstSmLg) ++ lstSmSmLg) ++ eLg) ++ eSmLg) ++ eSmSmLg) ++ lfttreeLg ++ lfttreeSmLg).
                        rewrite app_assoc.
                        replace (leftoveri ++ loLft ++ resiSmLg ++ lfttreeSmLg) with ((leftoveri ++ loLft ++ resiSmLg) ++ lfttreeSmLg); 
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.

                        assert (Permutation (eSmSmLg ++ lstSmSmLg) resiSmLg); try tauto.
                        replace (leftoveri ++ loLft ++ resiSmLg) with ((leftoveri ++ loLft) ++ resiSmLg); auto.
                        permtrans (resiSmLg ++ (leftoveri ++ loLft)).
                        do 3 rewrite <- app_assoc.
                        permtrans ((lstSmSmLg ++ (lstLg ++ lstSmLg)) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeLg).
                        do 2 rewrite app_assoc.
                        permtrans (eSmSmLg ++ (((lstSmSmLg ++ lstLg ++ lstSmLg) ++ eLg) ++ eSmLg) ++ lfttreeLg).
                        repeat rewrite <- app_assoc.
                        rewrite app_assoc; apply Permutation_app; auto.
                        do 2 rewrite app_assoc.
                        permtrans  ((eLg ++ (lstLg ++ lstSmLg)) ++ eSmLg ++ lfttreeLg).
                        replace (eLg ++ lstLg ++ lstSmLg) with ((eLg ++ lstLg) ++ lstSmLg); auto.
                        rewrite <- app_assoc.
                        apply Permutation_app; auto.

                        assert (Permutation (eSmLg ++ lstSmLg) resiLg); try tauto.
                        assert (Permutation (lstSmLg ++ eSmLg) resiLg); [ permtrans (eSmLg ++ lstSmLg) | ].
                        rewrite app_assoc.
                        permtrans (resiLg ++ lfttreeLg).
                    }

                    repeat split; auto.
                    { (* non-applicable *)
                        intros Hcontra.
                        erewrite <- knn_preserve_size_max in Hcontra; eauto. lia.
                    }

                    {
                        assert (all_in_leb (sum_dist query) pqlstRgt (leftoveri ++ loLft ++ loRgt)).
                        2:{ apply all_in_leb_perm with pqlstRgt (leftoveri ++ loLft ++ loRgt); auto. }

                        rewrite app_assoc; apply all_in_leb_lst_app; auto.
                        assert (all_in_leb (sum_dist query) lresSm loLft) as H20.
                        {
                            apply all_in_leb_app_head_1 with lresLg.
                            apply all_in_leb_perm with pqlstLft loLft; auto.   
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_1 with rgttreeLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }
                        assert (all_in_leb (sum_dist query) lresLg loLft) as H40.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as H50.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_2 with lresLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }

                        pose proof Heq_Ksize as Heq_Ksize'; eapply insert_bounded_preserve_max_eq with (lst:=lst) in Heq_Ksize'; auto.
                        assert (K <= size datapt (sum_dist query) (insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        rewrite <- Heq_Ksize'; auto.

                        assert (K <= length pqlstLft) as H60.
                        {
                            replace (length pqlstLft) with (length lst).
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite Heq_Ksize'.
                            erewrite knn_preserve_size_max; eauto.
                        }
                        assert (length pqlstLft = length pqlstRgt) as H61.
                        {
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                   (insert_bounded K datapt (sum_dist query) pt pq)))); auto.
                            erewrite knn_preserve_size_max; eauto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                        { rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto. }

                        assert (length resi = length pqlstLft) as H63.
                        {
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                            rewrite <- Heq_Ksize'.
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length lst = length resi) as H64.
                        {
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        }

                        assert (length (resiSm ++ resiLg) = length (lresSm ++ lresLg)) as H65.
                        { rewrite (Permutation_length Hl1). rewrite (Permutation_length Hr1). auto. }

                        assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                        {
                            destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                            -   left.
                                rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length rgttreeSm = 0) as H66; try lia.
                                apply length_zero_iff_nil in H66.
                                rewrite H66; auto.
                            -   right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x rgttreeSm).
                                destruct rgttreeSm; simpl in *; try lia. exists d0; auto.
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl. exists x; auto.
                        }

                        assert (length (resiSm ++ resiLg) = length (resiSm ++ lfttreeSm)) as H68.
                        {
                            rewrite (Permutation_length Hl3). rewrite <- H63. 
                            rewrite (Permutation_length Hl1); auto.
                        }
                        assert (lfttreeSm = [] \/ (exists x, In x lfttreeSm) /\ all_in_leb (sum_dist query) lfttreeSm leftoveri) as H69.
                        {
                            destruct resiLg as [ | x xs ] eqn:Heq_resiLg.
                            - left.
                                repeat rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length lfttreeSm = 0) as H69'; try lia.
                                apply length_zero_iff_nil in H69'.
                                rewrite H69'; auto.
                            - right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x lfttreeSm).
                                destruct lfttreeSm; simpl in *; try lia. exists d0; auto.
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                exists x; auto.
                        }

                        assert (all_in_leb (sum_dist query) lfttreeSm lfttreeLg) as H90.
                        {
                            apply all_in_leb_app_head_2 with resiSm; auto.
                            apply all_in_leb_app_tail_2  with resiLg; auto.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }

                        apply all_in_leb_lst_app; auto.

                        { (* pqlstRgt <= leftoveri*)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) leftoveri; auto.
                            apply all_in_leb_app_lst; auto.
                            { (* lresSm <= leftoveri *)
                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                -
                                rewrite Hd1 in *; repeat rewrite <- app_nil_end in *; rewrite app_length in *.
                                assert (lfttreeSm = []) as Hd3.
                                {
                                    destruct lfttreeSm; auto; simpl in H68; lia.
                                }
                                rewrite Hd3 in *; repeat rewrite <- app_nil_end in *; simpl in *.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                permtrans resiSm; auto.
                                permtrans pqlstLft; auto.
                                -
                                apply all_in_leb_trans with resiLg; auto.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                            }
                            { (* rgttreeSm <= leftoveri *)
                                destruct H67 as [ H67 | H67 ].
                                rewrite H67; auto.
                                
                                assert (all_in_leb (sum_dist query) rgttreeSm resiLg) as H95.
                                {
                                    apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                    inversion_clear H67.
                                    apply all_in_leb_perm with rgttreeSm loLft; auto.
                                }

                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                {   (* resiLg = [] *)
                                    repeat rewrite Hd1 in *; simpl in *.
                                    repeat rewrite <- app_nil_end in *.
                                    assert (lfttreeSm = []).
                                    -   simpl in *; repeat rewrite app_length in H68.
                                        destruct lfttreeSm; try (simpl in H68; lia); auto.
                                    -
                                    rewrite H18 in *; simpl in *; repeat rewrite <- app_nil_end in *.
                                    clear H69 H95 H90.
                                    destruct H67 as (H67a, H67b).
                                    assert (Permutation resiSm (lresSm ++ lresLg)).
                                    permtrans pqlstLft; auto.
                                    destruct (list_nil_or_in lresLg) as [ Habsurd | Hd2 ].
                                    { rewrite Habsurd in H62; rewrite <- app_nil_end in H62; repeat rewrite app_length in H62; simpl in H62.
                                      assert (0 < length rgttreeSm). destruct H67a; destruct rgttreeSm. inversion H21. simpl; lia.
                                      lia.
                                    }                                      

                                    apply all_in_leb_trans with lresLg; auto.
                                    apply all_in_leb_app_head_2 with lresSm; auto.
                                    apply all_in_leb_perm with resiSm leftoveri; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                                { (* exists x \in resiLg *)
                                    apply all_in_leb_trans with resiLg; auto.
                                    apply all_in_leb_app_head_2 with resiSm; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                            }
                        }
                        {  (* pqlstRgt <= loLft *)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                            apply all_in_leb_app_lst; auto.
                            destruct H67 as [ H67 | (H67a, H67b) ]; auto.
                            rewrite H67; auto.
                        }
                    }
                }
            }
        }


        { (* size pq < K*)
            simpl; rewrite Heq_peek; rewrite Heq_Ksize; simpl.
            split_andb_leb.
            destruct (insert_bounded_relate_perm K datapt (sum_dist query) pt pq lst Hpriq Habs)
                as (eSm, (eLg, (lstSm, (lstLg, (resi, (leftoveri, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, H9)))))))))))))).
            apply H8 in Heq_Ksize as H8stuff; clear H9 H8.
            assert (leftoveri = []).
            {
                split_andb_leb.
                replace eLg with (@nil datapt) in H6; auto.
                replace lstLg with (@nil datapt) in H6; auto.
                simpl in H6.
                apply Permutation_nil; auto.
            }
            replace leftoveri with (@nil datapt) in *; auto; clear H H6 H7 leftoveri.
            replace lstSm with lst in *; auto. 2:{ split_andb_leb; auto. }
            replace eSm with [pt] in *; auto. 2:{ split_andb_leb; auto. }
            clear lstSm eSm lstLg eLg H3 H4 H8stuff.
            assert (size _ _ (insert_bounded K _ _ pt pq) = 1 + size _ _  pq).
            { eapply insert_bounded_lt_preserve_max; eauto. }
            generalize dependent (insert_bounded K datapt (sum_dist query) pt pq); intros pq'; intros.

            destruct (ith_leb ax pt query) eqn:Heq_ith.
            { (* ith = true --- lft then rgt *)
                destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq' _ H1 H2) 
                    as (pqlstLft, (Hplft, Halft)).
                destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query _ _ Hplft Halft) 
                    as (pqlstRgt, (Hprgt, Hargt)).
                
                pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                destruct (cont_node_inv _ _ _ _ _ Htree) as (lftConts, (rgtConts, (Hcontlft, (Hcontrgt, Hconteq)))).
                destruct (IHlft _ _ _ _ _ _
                        HK H6 Hcontlft H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                destruct (IHrgt _ _ _ _ _ _ 
                        HK H3 Hcontrgt Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                clear IHlft IHrgt.
                rewrite Hconteq.
                assert (Permutation result pqlstRgt).
                { apply abs_perm with (sum_dist query)
                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')); auto. }
        
                assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                    H5 Hl1 HresiSm_Lg) as
                                (eSm, (eLg, (lstSm, (lstLg, HresiStuff)))).
                assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                    Hl3 Hr1 HlresSm_Lg) as
                                (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                assert (Permutation (eSm ++ lstSm) resiSm) as HeSm1; try tauto.
                assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                    HeSm1 HeSm2 HeSm3) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff2)))).
                assert (Permutation (eSmSm ++ lstSmSm ++ lfttreeSmSm) lresSm).
                {
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    replace (eSmSm ++ lstSmSm ++ lfttreeSmSm) with ((eSmSm ++ lstSmSm) ++ lfttreeSmSm); auto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                }
    
                exists lstSmSm.
                exists (lstSmLg ++ lstLg).
                exists (eSmSm ++ lfttreeSmSm ++ rgttreeSm).
                exists (eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                exists (loLft ++ loRgt).
                assert (Permutation (lstSmSm ++ lstSmLg ++ lstLg) lst).
                {
                    permtrans (lstSm ++ lstLg); try tauto.
                    assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                    rewrite app_assoc.
                    apply Permutation_app; auto.
                }
                
                assert (Permutation ((eSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                (pt :: lftConts ++ rgtConts)).
                {
                    repeat rewrite <- app_assoc; auto.
                    do 3 rewrite app_assoc.
                    permtrans (eSmLg ++ (((eSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg)
                                    ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    do 2 rewrite app_assoc.
                    permtrans (eLg ++ ((eSm ++ lfttreeSmSm) ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans ([pt] ++ lfttreeSmSm ++ rgttreeSm ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    replace (pt :: lftConts ++ rgtConts) with ([pt] ++ lftConts ++ rgtConts); auto.
                    apply Permutation_app; auto.
                    (* done [pt] *)                    
                    permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    assert (Permutation (lfttreeSmSm ++ lfttreeSmLg) lfttreeSm); try tauto.
                    rewrite app_assoc.
                    permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                    rewrite app_assoc.
                    permtrans (lftConts ++ rgttreeSm ++ rgttreeLg).
                }

                assert (Permutation (lstSmSm ++ eSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                {
                    permtrans pqlstRgt.
                    rewrite app_assoc. rewrite app_assoc.
                    permtrans (lresSm ++ rgttreeSm).
                    rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                    apply Permutation_app; apply Permutation_sym; auto.
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                    assert (Permutation (lstSmSm ++ eSmSm) resiSmSm); auto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    permtrans (eSmSm ++ lstSmSm).
                }

                assert (Permutation ((lstSmLg ++ lstLg) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg) (loLft ++ loRgt)).
                {
                    permtrans (eLg ++ (lstSmLg ++ lstLg) ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite <- app_assoc.
                    permtrans (eLg ++ lstLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite app_assoc.
                    assert (Permutation (eLg ++ lstLg) resiLg); try tauto.
                    permtrans (resiLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    do 3 rewrite app_assoc.
                    permtrans (lfttreeLg ++ (((resiLg ++ lstSmLg) ++ eSmLg) ++ lfttreeSmLg) ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    apply Permutation_app. rewrite Permutation_app_comm; tauto.
                    assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                    assert (Permutation (eSmLg ++ lstSmLg) resiSmLg); try tauto.
                    permtrans (eSmLg ++ lstSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (resiSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (lresLg ++ rgttreeLg).
                }

                assert (size datapt (sum_dist query)
                (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')) < K -> loLft = [] /\ loRgt = []).
                { (* size / leftover empty *)
                    intros HltK.
                    apply Hr6 in HltK as Hr6'.
                    eapply knn_preserve_size_lt_inv in HltK as HltK'; eauto.
                }

                repeat split; auto.

                {
                    intros HszK.
                    apply H12 in HszK as (Hsz1, Hsz2).
                    replace loLft with (@nil datapt); replace loRgt with (@nil datapt); auto.
                }
                { (* pqlstRgt <= loLft ++ loRgt *)
                    apply all_in_leb_perm with pqlstRgt (loLft ++ loRgt); auto.
                    apply all_in_leb_lst_app; auto.

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query)
                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                    (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')))
                        K); auto.
                    {
                        apply H12 in H13 as (Hsz1, Hsz2).
                        replace loLft with (@nil datapt); auto.
                    }

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query) (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq'))
                                        K); auto.
                    {
                        apply Hl6 in H14. replace loLft with (@nil datapt); auto.
                    }

                    assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                    {
                        apply all_in_leb_app_head_2 with lresSm.
                        apply all_in_leb_app_tail_1 with rgttreeLg.
                        apply all_in_leb_perm with pqlstRgt loRgt; auto.
                    }

                    assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                    { 
                        rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto.
                        rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')); auto.
                        rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq'))); auto.
                        erewrite knn_preserve_size_max; eauto.
                    }

                    assert (all_in_leb (sum_dist query) lresLg loLft).
                    {
                        apply all_in_leb_app_head_2 with lresSm; auto.
                        apply all_in_leb_perm with pqlstLft loLft; auto.
                    }

                    assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                    {
                        destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                        -   left.
                            rewrite <- app_nil_end in *.
                            repeat rewrite app_length in *.
                            assert (length rgttreeSm = 0) as H66; try lia.
                            apply length_zero_iff_nil in H66.
                            rewrite H66; auto.
                        -   right.
                            repeat rewrite app_length in *.
                            assert (exists x, In x rgttreeSm).
                            destruct rgttreeSm; simpl in *; try lia. exists d0; auto.
                            split; auto.
                            apply all_in_leb_trans with (x :: xs); auto; simpl. exists x; auto.
                    }

                    apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                    apply all_in_leb_app_lst; auto.
                    apply all_in_leb_app_head_1 with lresLg; auto.
                    apply all_in_leb_perm with pqlstLft loLft; auto.
                    destruct H67 as [ H67 | (H67a, H67b)]; auto.
                    rewrite H67; auto.
                }
            }

            { (* ith = false --- rgt then lft *)
                (* apply MAGIC.  *)
                destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq' _ H1 H2) 
                    as (pqlstLft, (Hplft, Halft)).
                destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query _ _ Hplft Halft) 
                    as (pqlstRgt, (Hprgt, Hargt)).
                
                pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                destruct (cont_node_inv _ _ _ _ _ Htree) as (rgtConts, (lftConts, (Hcontrgt, (Hcontlft, Hconteq)))).
                destruct (IHrgt _ _ _ _ _ _
                        HK H3 Hcontlft H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                destruct (IHlft _ _ _ _ _ _ 
                        HK H6 Hcontrgt Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                clear IHlft IHrgt.
                rewrite Hconteq.
                assert (Permutation result pqlstRgt).
                { apply abs_perm with (sum_dist query)
                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')); auto. }

                assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                    H5 Hl1 HresiSm_Lg) as
                                (eSm, (eLg, (lstSm, (lstLg, HresiStuff)))).
                assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                    Hl3 Hr1 HlresSm_Lg) as
                                (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                assert (Permutation (eSm ++ lstSm) resiSm) as HeSm1; try tauto.
                assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                    HeSm1 HeSm2 HeSm3) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff2)))).
                assert (Permutation (eSmSm ++ lstSmSm ++ lfttreeSmSm) lresSm).
                {
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    replace (eSmSm ++ lstSmSm ++ lfttreeSmSm) with ((eSmSm ++ lstSmSm) ++ lfttreeSmSm); auto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                }

                exists lstSmSm.
                exists (lstSmLg ++ lstLg).
                exists (eSmSm ++ lfttreeSmSm ++ rgttreeSm).
                exists (eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                exists (loLft ++ loRgt).
                assert (Permutation (lstSmSm ++ lstSmLg ++ lstLg) lst).
                {
                    permtrans (lstSm ++ lstLg); try tauto.
                    assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                    rewrite app_assoc.
                    apply Permutation_app; auto.
                }
                
                assert (Permutation ((eSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                (pt :: rgtConts ++ lftConts)).
                {
                    repeat rewrite <- app_assoc; auto.
                    do 3 rewrite app_assoc.
                    permtrans (eSmLg ++ (((eSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg)
                                    ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    do 2 rewrite app_assoc.
                    permtrans (eLg ++ ((eSm ++ lfttreeSmSm) ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans ([pt] ++ lfttreeSmSm ++ rgttreeSm ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    replace (pt :: rgtConts ++ lftConts) with ([pt] ++ rgtConts ++ lftConts); auto.
                    apply Permutation_app; auto.
                    (* done [pt] *)                    
                    permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    assert (Permutation (lfttreeSmSm ++ lfttreeSmLg) lfttreeSm); try tauto.
                    rewrite app_assoc.
                    permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                    rewrite app_assoc.
                    permtrans (lftConts ++ rgttreeSm ++ rgttreeLg).
                    permtrans (lftConts ++ rgtConts).
                }

                assert (Permutation (lstSmSm ++ eSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                {
                    permtrans pqlstRgt.
                    rewrite app_assoc. rewrite app_assoc.
                    permtrans (lresSm ++ rgttreeSm).
                    rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                    apply Permutation_app; apply Permutation_sym; auto.
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                    assert (Permutation (lstSmSm ++ eSmSm) resiSmSm); auto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    permtrans (eSmSm ++ lstSmSm).
                }

                assert (Permutation ((lstSmLg ++ lstLg) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg) (loLft ++ loRgt)).
                {
                    permtrans (eLg ++ (lstSmLg ++ lstLg) ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite <- app_assoc.
                    permtrans (eLg ++ lstLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite app_assoc.
                    assert (Permutation (eLg ++ lstLg) resiLg); try tauto.
                    permtrans (resiLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    do 3 rewrite app_assoc.
                    permtrans (lfttreeLg ++ (((resiLg ++ lstSmLg) ++ eSmLg) ++ lfttreeSmLg) ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    apply Permutation_app. rewrite Permutation_app_comm; tauto.
                    assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                    assert (Permutation (eSmLg ++ lstSmLg) resiSmLg); try tauto.
                    permtrans (eSmLg ++ lstSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (resiSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (lresLg ++ rgttreeLg).
                }

                assert (size datapt (sum_dist query)
                (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')) < K -> loLft = [] /\ loRgt = []).
                { (* size / leftover empty *)
                    intros HltK.
                    apply Hr6 in HltK as Hr6'.
                    eapply knn_preserve_size_lt_inv in HltK as HltK'; eauto.
                }

                repeat split; auto.

                {
                    intros HszK.
                    apply H12 in HszK as (Hsz1, Hsz2).
                    replace loLft with (@nil datapt); replace loRgt with (@nil datapt); auto.
                }
                { (* pqlstRgt <= loLft ++ loRgt *)
                    apply all_in_leb_perm with pqlstRgt (loLft ++ loRgt); auto.
                    apply all_in_leb_lst_app; auto.

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query)
                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                    (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')))
                        K); auto.
                    {
                        apply H12 in H13 as (Hsz1, Hsz2).
                        replace loLft with (@nil datapt); auto.
                    }

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query) (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq'))
                                        K); auto.
                    {
                        apply Hl6 in H14. replace loLft with (@nil datapt); auto.
                    }

                    assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                    {
                        apply all_in_leb_app_head_2 with lresSm.
                        apply all_in_leb_app_tail_1 with rgttreeLg.
                        apply all_in_leb_perm with pqlstRgt loRgt; auto.
                    }

                    assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                    { 
                        rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto.
                        rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')); auto.
                        rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq'))); auto.
                        erewrite knn_preserve_size_max; eauto.
                    }

                    assert (all_in_leb (sum_dist query) lresLg loLft).
                    {
                        apply all_in_leb_app_head_2 with lresSm; auto.
                        apply all_in_leb_perm with pqlstLft loLft; auto.
                    }

                    assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                    {
                        destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                        -   left.
                            rewrite <- app_nil_end in *.
                            repeat rewrite app_length in *.
                            assert (length rgttreeSm = 0) as H66; try lia.
                            apply length_zero_iff_nil in H66.
                            rewrite H66; auto.
                        -   right.
                            repeat rewrite app_length in *.
                            assert (exists x, In x rgttreeSm).
                            destruct rgttreeSm; simpl in *; try lia. exists d0; auto.
                            split; auto.
                            apply all_in_leb_trans with (x :: xs); auto; simpl. exists x; auto.
                    }

                    apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                    apply all_in_leb_app_lst; auto.
                    apply all_in_leb_app_head_1 with lresLg; auto.
                    apply all_in_leb_perm with pqlstLft loLft; auto.
                    destruct H67 as [ H67 | (H67a, H67b)]; auto.
                    rewrite H67; auto.
                }
                        
            }
        }
    }






    (* this is repeated from "peek is some" *)
    { (* peek is none *)
        destruct (K <=? size datapt (sum_dist query) pq) eqn:Heq_Ksize; simpl in Habs', Hpriq'.
        { (* K <= size pq *)
            assert (size datapt (sum_dist query) (knn K k (node ax pt lft rgt) bb query pq) < K -> data = [])
                    as Hnon_applicable.
            {
                split_andb_leb.
                intros Hcontra.
                erewrite <- knn_preserve_size_max in Hcontra; eauto. lia.
            }

            split_andb_leb.
                destruct (insert_bounded_relate_perm K datapt (sum_dist query) pt pq lst Hpriq Habs)
                    as (eSm, (eLg, (lstSm, (lstLg, (resi, (leftoveri, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, H9)))))))))))))).
                pose proof Heq_Ksize as Heq_Ksize'; apply H9 in Heq_Ksize' as (e', Hpermi).

                destruct (ith_leb ax pt query) eqn:Heq_ith.
                { (* ith = true --- insert_bounded (maxed out) then lft then rgt *)
                    destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query 
                                        (insert_bounded K datapt (sum_dist query) pt pq) _ H1 H2) as
                            (pqlstLft, (Hplft, Halft)).
                    destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0)))
                                        query _ _ Hplft Halft) as (pqlstRgt, (Hprgt, Hargt)).
                    pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                    destruct (cont_node_inv _ _ _ _ _ Htree) as (lftConts, (rgtConts, (Hcontlft, (Hcontrgt, Hconteq)))).
                    destruct (IHlft _ _ _ _ _ _
                            HK H11 Hcontlft H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                    destruct (IHrgt _ _ _ _ _ _ 
                            HK H0 Hcontrgt Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                    clear IHlft IHrgt.
                    rewrite Hconteq.
                    assert (Permutation result pqlstRgt).
                    { apply abs_perm with (sum_dist query)
                            (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                            (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                    }

                    assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                        H5 Hl1 HresiSm_Lg) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff)))).
                    assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                        Hl3 Hr1 HlresSm_Lg) as
                                    (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                    assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                    { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                    assert (Permutation (eSmSm ++ lstSmSm) resiSm) as HeSm1; try tauto.
                    assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                    assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                        HeSm1 HeSm2 HeSm3) as
                                        (eSmSmSm, (eSmSmLg, (lstSmSmSm, (lstSmSmLg, HresiStuff2)))).
                    assert (Permutation (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) lresSm).
                    {
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        replace (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) with ((eSmSmSm ++ lstSmSmSm) ++ lfttreeSmSm); auto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                    }

                    exists lstSmSmSm.
                    exists (lstLg ++ lstSmLg ++ lstSmSmLg).
                    exists (eSmSmSm ++ lfttreeSmSm ++ rgttreeSm).
                    exists (eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    exists (leftoveri ++ loLft ++ loRgt).
                    assert (Permutation (lstSmSmSm ++ lstLg ++ lstSmLg ++ lstSmSmLg) lst).
                    {
                        permtrans (lstLg ++ lstSmSmSm ++ lstSmLg ++ lstSmSmLg).
                        rewrite Permutation_app_comm in H4.
                        permtrans (lstLg ++ lstSm).
                        apply Permutation_app; auto.
                        assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                        rewrite Permutation_app_comm in H13.
                        permtrans (lstSmLg ++ lstSmSmSm ++ lstSmSmLg).
                        permtrans (lstSmLg ++ lstSmSm); auto.
                        apply Permutation_app; auto.
                        tauto.
                    }

                    assert (Permutation
                        ((eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                        (pt :: lftConts ++ rgtConts)).
                    {
                        repeat rewrite <- app_assoc; auto.
                        assert (eSmSmSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg =
                            eSmSmSm ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        rewrite app_assoc. repeat rewrite <- app_assoc; auto.
                        assert (Permutation
                        (eSmSmSm ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg) (pt :: lftConts ++ rgtConts)).
                        2:{ rewrite <- H14 in H15; auto. }
                        permtrans (eSmSmSm ++ eSmSmLg ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        assert (Permutation (eSmSmSm ++ eSmSmLg) eSmSm ); try tauto.
                        replace (eSmSmSm ++ eSmSmLg ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with ((eSmSmSm ++ eSmSmLg) ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        permtrans (eSmSm ++ (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        replace (lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg) with ((lfttreeSmSm ++ rgttreeSm ++ eLg) ++ eSmLg); auto.
                        2:{ repeat rewrite <- app_assoc; auto. }
                        rewrite app_assoc.
                        permtrans ((eSmSm ++ eSmLg ++ (lfttreeSmSm ++ rgttreeSm ++ eLg)) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        repeat rewrite <- app_assoc; rewrite app_assoc.
                        assert (Permutation (eSmSm ++ eSmLg) eSm); try tauto.
                        permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        assert (Permutation (eSm ++ (lfttreeSmSm ++ rgttreeSm) ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                                (pt :: lftConts ++ rgtConts)).
                        2:{  repeat rewrite <- app_assoc in H17 ; auto. }
                        permtrans (eSm ++ eLg ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        replace (eSm ++ eLg ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with ((eSm ++ eLg) ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                        permtrans ([pt] ++ (lfttreeSmSm ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        replace (pt :: lftConts ++ rgtConts) with ([pt] ++ lftConts ++ rgtConts); auto.
                        apply Permutation_app; auto.
                        (* done [pt] !! *)
                        repeat rewrite <- app_assoc.
                        permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        assert (Permutation (lfttreeSmSm ++ lfttreeSmLg) lfttreeSm); try tauto.
                        rewrite app_assoc.
                        permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                        rewrite app_assoc.
                        permtrans (lftConts ++ rgttreeSm ++ rgttreeLg).
                    }
                    assert (Permutation (lstSmSmSm ++ eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                    {
                        permtrans pqlstRgt.
                        rewrite app_assoc. rewrite app_assoc.
                        permtrans (lresSm ++ rgttreeSm).
                        rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                        apply Permutation_app; apply Permutation_sym; auto.
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                        assert (Permutation (lstSmSmSm ++ eSmSmSm) resiSmSm); auto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        permtrans (eSmSmSm ++ lstSmSmSm).
                    }
                    assert (Permutation
                    ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                    (leftoveri ++ loLft ++ loRgt)).
                    {
                        permtrans (leftoveri ++ loLft ++ (lresLg ++ rgttreeLg)).
                        replace ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with (((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        replace (leftoveri ++ loLft ++ lresLg ++ rgttreeLg) with ((leftoveri ++ loLft ++ lresLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.
                        assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                        permtrans ((leftoveri ++ loLft) ++ (resiSmLg ++ lfttreeSmLg)).
                        2:{ replace (leftoveri ++ loLft ++ lresLg) with ((leftoveri ++ loLft) ++ lresLg); auto. }       
                        repeat rewrite <- app_assoc.
                        do 5 (rewrite app_assoc).
                        permtrans ((((((lstLg ++ lstSmLg) ++ lstSmSmLg) ++ eLg) ++ eSmLg) ++ eSmSmLg) ++ lfttreeLg ++ lfttreeSmLg).
                        rewrite app_assoc.
                        replace (leftoveri ++ loLft ++ resiSmLg ++ lfttreeSmLg) with ((leftoveri ++ loLft ++ resiSmLg) ++ lfttreeSmLg); 
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.

                        assert (Permutation (eSmSmLg ++ lstSmSmLg) resiSmLg); try tauto.
                        replace (leftoveri ++ loLft ++ resiSmLg) with ((leftoveri ++ loLft) ++ resiSmLg); auto.
                        permtrans (resiSmLg ++ (leftoveri ++ loLft)).
                        do 3 rewrite <- app_assoc.
                        permtrans ((lstSmSmLg ++ (lstLg ++ lstSmLg)) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeLg).
                        do 2 rewrite app_assoc.
                        permtrans (eSmSmLg ++ (((lstSmSmLg ++ lstLg ++ lstSmLg) ++ eLg) ++ eSmLg) ++ lfttreeLg).
                        repeat rewrite <- app_assoc.
                        rewrite app_assoc; apply Permutation_app; auto.
                        do 2 rewrite app_assoc.
                        permtrans  ((eLg ++ (lstLg ++ lstSmLg)) ++ eSmLg ++ lfttreeLg).
                        replace (eLg ++ lstLg ++ lstSmLg) with ((eLg ++ lstLg) ++ lstSmLg); auto.
                        rewrite <- app_assoc.
                        apply Permutation_app; auto.

                        assert (Permutation (eSmLg ++ lstSmLg) resiLg); try tauto.
                        assert (Permutation (lstSmLg ++ eSmLg) resiLg); [ permtrans (eSmLg ++ lstSmLg) | ].
                        rewrite app_assoc.
                        permtrans (resiLg ++ lfttreeLg).
                    }

                    repeat split; auto.
                    { (* non-applicable *)
                        intros Hcontra.
                        erewrite <- knn_preserve_size_max in Hcontra; eauto. lia.
                    }

                    {
                        assert (all_in_leb (sum_dist query) pqlstRgt (leftoveri ++ loLft ++ loRgt)).
                        2:{ apply all_in_leb_perm with pqlstRgt (leftoveri ++ loLft ++ loRgt); auto. }

                        rewrite app_assoc; apply all_in_leb_lst_app; auto.
                        assert (all_in_leb (sum_dist query) lresSm loLft) as H20.
                        {
                            apply all_in_leb_app_head_1 with lresLg.
                            apply all_in_leb_perm with pqlstLft loLft; auto.   
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_1 with rgttreeLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }
                        assert (all_in_leb (sum_dist query) lresLg loLft) as H40.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as H50.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_2 with lresLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }

                        pose proof Heq_Ksize as Heq_Ksize'; eapply insert_bounded_preserve_max_eq with (lst:=lst) in Heq_Ksize'; auto.
                        assert (K <= size datapt (sum_dist query) (insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        rewrite <- Heq_Ksize'; auto.

                        assert (K <= length pqlstLft) as H60.
                        {
                            replace (length pqlstLft) with (length lst).
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite Heq_Ksize'.
                            erewrite knn_preserve_size_max; eauto.
                        }
                        assert (length pqlstLft = length pqlstRgt) as H61.
                        {
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                   (insert_bounded K datapt (sum_dist query) pt pq)))); auto.
                            erewrite knn_preserve_size_max; eauto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                        { rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto. }

                        assert (length resi = length pqlstLft) as H63.
                        {
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                            rewrite <- Heq_Ksize'.
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length lst = length resi) as H64.
                        {
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        }

                        assert (length (resiSm ++ resiLg) = length (lresSm ++ lresLg)) as H65.
                        { rewrite (Permutation_length Hl1). rewrite (Permutation_length Hr1). auto. }

                        assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                        {
                            destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                            -   left.
                                rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length rgttreeSm = 0) as H66; try lia.
                                apply length_zero_iff_nil in H66.
                                rewrite H66; auto.
                            -   right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x rgttreeSm).
                                destruct rgttreeSm; simpl in *; try lia. exists d; auto.
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl. exists x; auto.
                        }

                        assert (length (resiSm ++ resiLg) = length (resiSm ++ lfttreeSm)) as H68.
                        {
                            rewrite (Permutation_length Hl3). rewrite <- H63. 
                            rewrite (Permutation_length Hl1); auto.
                        }
                        assert (lfttreeSm = [] \/ (exists x, In x lfttreeSm) /\ all_in_leb (sum_dist query) lfttreeSm leftoveri) as H69.
                        {
                            destruct resiLg as [ | x xs ] eqn:Heq_resiLg.
                            - left.
                                repeat rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length lfttreeSm = 0) as H69'; try lia.
                                apply length_zero_iff_nil in H69'.
                                rewrite H69'; auto.
                            - right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x lfttreeSm).
                                destruct lfttreeSm; simpl in *; try lia. exists d; auto. 
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                exists x; auto.
                        }

                        assert (all_in_leb (sum_dist query) lfttreeSm lfttreeLg) as H90.
                        {
                            apply all_in_leb_app_head_2 with resiSm; auto.
                            apply all_in_leb_app_tail_2  with resiLg; auto.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }

                        apply all_in_leb_lst_app; auto.

                        { (* pqlstRgt <= leftoveri*)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) leftoveri; auto.
                            apply all_in_leb_app_lst; auto.
                            { (* lresSm <= leftoveri *)
                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                -
                                rewrite Hd1 in *; repeat rewrite <- app_nil_end in *; rewrite app_length in *.
                                assert (lfttreeSm = []) as Hd3.
                                {
                                    destruct lfttreeSm; auto; simpl in H68; lia.
                                }
                                rewrite Hd3 in *; repeat rewrite <- app_nil_end in *; simpl in *.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                permtrans resiSm; auto.
                                permtrans pqlstLft; auto.
                                -
                                apply all_in_leb_trans with resiLg; auto.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                            }
                            { (* rgttreeSm <= leftoveri *)
                                destruct H67 as [ H67 | H67 ].
                                rewrite H67; auto.
                                
                                assert (all_in_leb (sum_dist query) rgttreeSm resiLg) as H95.
                                {
                                    apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                    inversion_clear H67.
                                    apply all_in_leb_perm with rgttreeSm loLft; auto.
                                }

                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                {   (* resiLg = [] *)
                                    repeat rewrite Hd1 in *; simpl in *.
                                    repeat rewrite <- app_nil_end in *.
                                    assert (lfttreeSm = []).
                                    -   simpl in *; repeat rewrite app_length in H68.
                                        destruct lfttreeSm; try (simpl in H68; lia); auto.
                                    -
                                    rewrite H18 in *; simpl in *; repeat rewrite <- app_nil_end in *.
                                    clear H69 H95 H90.
                                    destruct H67 as (H67a, H67b).
                                    assert (Permutation resiSm (lresSm ++ lresLg)).
                                    permtrans pqlstLft; auto.
                                    destruct (list_nil_or_in lresLg) as [ Habsurd | Hd2 ].
                                    { rewrite Habsurd in H62; rewrite <- app_nil_end in H62; repeat rewrite app_length in H62; simpl in H62.
                                      assert (0 < length rgttreeSm). destruct H67a; destruct rgttreeSm. inversion H21. simpl; lia.
                                      lia.
                                    }                                      

                                    apply all_in_leb_trans with lresLg; auto.
                                    apply all_in_leb_app_head_2 with lresSm; auto.
                                    apply all_in_leb_perm with resiSm leftoveri; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                                { (* exists x \in resiLg *)
                                    apply all_in_leb_trans with resiLg; auto.
                                    apply all_in_leb_app_head_2 with resiSm; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                            }
                        }
                        {  (* pqlstRgt <= loLft *)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                            apply all_in_leb_app_lst; auto.
                            destruct H67 as [ H67 | (H67a, H67b) ]; auto.
                            rewrite H67; auto.
                        }
                    }
                }

                { (* ith = false --- rgt then lft *)
                    (* apply MAGIC. *)
                    destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query 
                                        (insert_bounded K datapt (sum_dist query) pt pq) _ H1 H2) as
                            (pqlstLft, (Hplft, Halft)).
                    destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0)))
                                        query _ _ Hplft Halft) as (pqlstRgt, (Hprgt, Hargt)).
                    pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                    destruct (cont_node_inv _ _ _ _ _ Htree) as (lftConts, (rgtConts, (Hcontlft, (Hcontrgt, Hconteq)))).
                    destruct (IHrgt _ _ _ _ _ _
                            HK H0 Hcontrgt H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                    destruct (IHlft _ _ _ _ _ _ 
                            HK H11 Hcontlft Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                    clear IHlft IHrgt.
                    rewrite Hconteq.
                    assert (Permutation result pqlstRgt).
                    { apply abs_perm with (sum_dist query)
                            (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                            (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                    }

                    assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                        H5 Hl1 HresiSm_Lg) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff)))).
                    assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                    { eapply perm_split_all_in_leb; eauto. }
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                        Hl3 Hr1 HlresSm_Lg) as
                                    (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                    assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                    { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                    assert (Permutation (eSmSm ++ lstSmSm) resiSm) as HeSm1; try tauto.
                    assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                    assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                    pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                        HeSm1 HeSm2 HeSm3) as
                                        (eSmSmSm, (eSmSmLg, (lstSmSmSm, (lstSmSmLg, HresiStuff2)))).
                    assert (Permutation (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) lresSm).
                    {
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        replace (eSmSmSm ++ lstSmSmSm ++ lfttreeSmSm) with ((eSmSmSm ++ lstSmSmSm) ++ lfttreeSmSm); auto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                    }

                    exists lstSmSmSm.
                    exists (lstLg ++ lstSmLg ++ lstSmSmLg).
                    exists (eSmSmSm ++ lfttreeSmSm ++ rgttreeSm).
                    exists (eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    exists (leftoveri ++ loLft ++ loRgt).
                    assert (Permutation (lstSmSmSm ++ lstLg ++ lstSmLg ++ lstSmSmLg) lst).
                    {
                        permtrans (lstLg ++ lstSmSmSm ++ lstSmLg ++ lstSmSmLg).
                        rewrite Permutation_app_comm in H4.
                        permtrans (lstLg ++ lstSm).
                        apply Permutation_app; auto.
                        assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                        rewrite Permutation_app_comm in H13.
                        permtrans (lstSmLg ++ lstSmSmSm ++ lstSmSmLg).
                        permtrans (lstSmLg ++ lstSmSm); auto.
                        apply Permutation_app; auto.
                        tauto.
                    }

                    assert (Permutation
                        ((eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                        (pt :: lftConts ++ rgtConts)).
                    {
                        repeat rewrite <- app_assoc; auto.
                        do 4 rewrite app_assoc.
                        permtrans (eSmSmLg ++ ((((eSmSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg) ++ eSmLg) ++
                        lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto; repeat rewrite <- app_assoc.
                        permtrans (eSmSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; apply Permutation_app; auto.
                        permtrans (eSmSmSm ++ eSmSmLg). tauto.
                        do 3 rewrite app_assoc.
                        permtrans (eSmLg ++ (((eSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); repeat rewrite <- app_assoc.
                        replace (pt :: lftConts ++ rgtConts) with ([pt] ++ lftConts ++ rgtConts); auto.
                        permtrans (eSmSm ++ eSmLg ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        apply Permutation_app; auto. tauto.
                        do 2 rewrite app_assoc.
                        permtrans (eLg ++ ((eSm ++ lfttreeSmSm) ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); repeat rewrite <- app_assoc.
                        permtrans (eSm ++ eLg ++ lfttreeSmSm ++ rgttreeSm ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; apply Permutation_app; auto.
                        (* done [pt] *)
                        permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        rewrite app_assoc; permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                        apply Permutation_app; auto; tauto.
                        permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                        rewrite app_assoc; permtrans (rgtConts ++ rgttreeSm ++ rgttreeLg).
                        permtrans (rgtConts ++ lftConts).
                    }
                    assert (Permutation (lstSmSmSm ++ eSmSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                    {
                        permtrans pqlstRgt.
                        rewrite app_assoc. rewrite app_assoc.
                        permtrans (lresSm ++ rgttreeSm).
                        rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                        apply Permutation_app; apply Permutation_sym; auto.
                        assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                        permtrans (resiSmSm ++ lfttreeSmSm).
                        assert (Permutation (lstSmSmSm ++ eSmSmSm) resiSmSm); auto.
                        assert (Permutation (eSmSmSm ++ lstSmSmSm) resiSmSm); try tauto.
                        permtrans (eSmSmSm ++ lstSmSmSm).
                    }
                    assert (Permutation
                    ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                    (leftoveri ++ loLft ++ loRgt)).
                    {
                        permtrans (leftoveri ++ loLft ++ (lresLg ++ rgttreeLg)).
                        replace ((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                            with (((lstLg ++ lstSmLg ++ lstSmSmLg) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeSmLg ++ lfttreeLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        replace (leftoveri ++ loLft ++ lresLg ++ rgttreeLg) with ((leftoveri ++ loLft ++ lresLg) ++ rgttreeLg);
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.
                        assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                        permtrans ((leftoveri ++ loLft) ++ (resiSmLg ++ lfttreeSmLg)).
                        2:{ replace (leftoveri ++ loLft ++ lresLg) with ((leftoveri ++ loLft) ++ lresLg); auto. }       
                        repeat rewrite <- app_assoc.
                        do 5 (rewrite app_assoc).
                        permtrans ((((((lstLg ++ lstSmLg) ++ lstSmSmLg) ++ eLg) ++ eSmLg) ++ eSmSmLg) ++ lfttreeLg ++ lfttreeSmLg).
                        rewrite app_assoc.
                        replace (leftoveri ++ loLft ++ resiSmLg ++ lfttreeSmLg) with ((leftoveri ++ loLft ++ resiSmLg) ++ lfttreeSmLg); 
                                [ | (repeat rewrite <- app_assoc; auto)].
                        rewrite Permutation_app_tail; auto.

                        assert (Permutation (eSmSmLg ++ lstSmSmLg) resiSmLg); try tauto.
                        replace (leftoveri ++ loLft ++ resiSmLg) with ((leftoveri ++ loLft) ++ resiSmLg); auto.
                        permtrans (resiSmLg ++ (leftoveri ++ loLft)).
                        do 3 rewrite <- app_assoc.
                        permtrans ((lstSmSmLg ++ (lstLg ++ lstSmLg)) ++ eLg ++ eSmLg ++ eSmSmLg ++ lfttreeLg).
                        do 2 rewrite app_assoc.
                        permtrans (eSmSmLg ++ (((lstSmSmLg ++ lstLg ++ lstSmLg) ++ eLg) ++ eSmLg) ++ lfttreeLg).
                        repeat rewrite <- app_assoc.
                        rewrite app_assoc; apply Permutation_app; auto.
                        do 2 rewrite app_assoc.
                        permtrans  ((eLg ++ (lstLg ++ lstSmLg)) ++ eSmLg ++ lfttreeLg).
                        replace (eLg ++ lstLg ++ lstSmLg) with ((eLg ++ lstLg) ++ lstSmLg); auto.
                        rewrite <- app_assoc.
                        apply Permutation_app; auto.

                        assert (Permutation (eSmLg ++ lstSmLg) resiLg); try tauto.
                        assert (Permutation (lstSmLg ++ eSmLg) resiLg); [ permtrans (eSmLg ++ lstSmLg) | ].
                        rewrite app_assoc.
                        permtrans (resiLg ++ lfttreeLg).
                    }

                    repeat split; auto.
                    { (* non-applicable *)
                        intros Hcontra.
                        erewrite <- knn_preserve_size_max in Hcontra; eauto. lia.
                    }

                    {
                        assert (all_in_leb (sum_dist query) pqlstRgt (leftoveri ++ loLft ++ loRgt)).
                        2:{ apply all_in_leb_perm with pqlstRgt (leftoveri ++ loLft ++ loRgt); auto. }

                        rewrite app_assoc; apply all_in_leb_lst_app; auto.
                        assert (all_in_leb (sum_dist query) lresSm loLft) as H20.
                        {
                            apply all_in_leb_app_head_1 with lresLg.
                            apply all_in_leb_perm with pqlstLft loLft; auto.   
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_1 with rgttreeLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }
                        assert (all_in_leb (sum_dist query) lresLg loLft) as H40.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }
                        assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as H50.
                        {
                            apply all_in_leb_app_head_2 with lresSm.
                            apply all_in_leb_app_tail_2 with lresLg.
                            apply all_in_leb_perm with pqlstRgt loRgt; auto.
                        }

                        pose proof Heq_Ksize as Heq_Ksize'; eapply insert_bounded_preserve_max_eq with (lst:=lst) in Heq_Ksize'; auto.
                        assert (K <= size datapt (sum_dist query) (insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        rewrite <- Heq_Ksize'; auto.

                        assert (K <= length pqlstLft) as H60.
                        {
                            replace (length pqlstLft) with (length lst).
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite Heq_Ksize'.
                            erewrite knn_preserve_size_max; eauto.
                        }
                        assert (length pqlstLft = length pqlstRgt) as H61.
                        {
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                   (insert_bounded K datapt (sum_dist query) pt pq)))); auto.
                            erewrite knn_preserve_size_max; eauto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                        { rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto. }

                        assert (length resi = length pqlstLft) as H63.
                        {
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                            rewrite <- Heq_Ksize'.
                            rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                (insert_bounded K datapt (sum_dist query) pt pq))); auto.
                            erewrite <- knn_preserve_size_max; eauto.
                        }
                        assert (length lst = length resi) as H64.
                        {
                            rewrite <- size_relate with (p:=pq); auto.
                            rewrite <- size_relate with (p:=(insert_bounded K datapt (sum_dist query) pt pq)); auto.
                        }

                        assert (length (resiSm ++ resiLg) = length (lresSm ++ lresLg)) as H65.
                        { rewrite (Permutation_length Hl1). rewrite (Permutation_length Hr1). auto. }

                        assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                        {
                            destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                            -   left.
                                rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length rgttreeSm = 0) as H66; try lia.
                                apply length_zero_iff_nil in H66.
                                rewrite H66; auto.
                            -   right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x rgttreeSm).
                                destruct rgttreeSm; simpl in *; try lia. exists d; auto.
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl.  exists x; auto.
                        }

                        assert (length (resiSm ++ resiLg) = length (resiSm ++ lfttreeSm)) as H68.
                        {
                            rewrite (Permutation_length Hl3). rewrite <- H63. 
                            rewrite (Permutation_length Hl1); auto.
                        }
                        assert (lfttreeSm = [] \/ (exists x, In x lfttreeSm) /\ all_in_leb (sum_dist query) lfttreeSm leftoveri) as H69.
                        {
                            destruct resiLg as [ | x xs ] eqn:Heq_resiLg.
                            - left.
                                repeat rewrite <- app_nil_end in *.
                                repeat rewrite app_length in *.
                                assert (length lfttreeSm = 0) as H69'; try lia.
                                apply length_zero_iff_nil in H69'.
                                rewrite H69'; auto.
                            - right.
                                repeat rewrite app_length in *.
                                assert (exists x, In x lfttreeSm).
                                destruct lfttreeSm; simpl in *; try lia. exists d; auto.
                                split; auto.
                                apply all_in_leb_trans with (x :: xs); auto; simpl. 
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                exists x; auto.
                        }

                        assert (all_in_leb (sum_dist query) lfttreeSm lfttreeLg) as H90.
                        {
                            apply all_in_leb_app_head_2 with resiSm; auto.
                            apply all_in_leb_app_tail_2  with resiLg; auto.
                            apply all_in_leb_perm with pqlstLft loLft; auto.
                        }

                        apply all_in_leb_lst_app; auto.

                        { (* pqlstRgt <= leftoveri*)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) leftoveri; auto.
                            apply all_in_leb_app_lst; auto.
                            { (* lresSm <= leftoveri *)
                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                -
                                rewrite Hd1 in *; repeat rewrite <- app_nil_end in *; rewrite app_length in *.
                                assert (lfttreeSm = []) as Hd3.
                                {
                                    destruct lfttreeSm; auto; simpl in H68; lia.
                                }
                                rewrite Hd3 in *; repeat rewrite <- app_nil_end in *; simpl in *.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                                permtrans resiSm; auto.
                                permtrans pqlstLft; auto.
                                -
                                apply all_in_leb_trans with resiLg; auto.
                                apply all_in_leb_app_head_1 with lresLg; auto.
                                apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                apply all_in_leb_perm with pqlstLft loLft; auto.
                                apply all_in_leb_app_head_2 with resiSm; auto.
                                apply all_in_leb_perm with resi leftoveri; auto.
                            }
                            { (* rgttreeSm <= leftoveri *)
                                destruct H67 as [ H67 | H67 ].
                                rewrite H67; auto.
                                
                                assert (all_in_leb (sum_dist query) rgttreeSm resiLg) as H95.
                                {
                                    apply all_in_leb_app_tail_1 with lfttreeLg; auto.
                                    inversion_clear H67.
                                    apply all_in_leb_perm with rgttreeSm loLft; auto.
                                }

                                destruct (list_nil_or_in resiLg) as [ Hd1 | Hd1 ].
                                {   (* resiLg = [] *)
                                    repeat rewrite Hd1 in *; simpl in *.
                                    repeat rewrite <- app_nil_end in *.
                                    assert (lfttreeSm = []).
                                    -   simpl in *; repeat rewrite app_length in H68.
                                        destruct lfttreeSm; try (simpl in H68; lia); auto.
                                    -
                                    rewrite H18 in *; simpl in *; repeat rewrite <- app_nil_end in *.
                                    clear H69 H95 H90.
                                    destruct H67 as (H67a, H67b).
                                    assert (Permutation resiSm (lresSm ++ lresLg)).
                                    permtrans pqlstLft; auto.
                                    destruct (list_nil_or_in lresLg) as [ Habsurd | Hd2 ].
                                    { rewrite Habsurd in H62; rewrite <- app_nil_end in H62; repeat rewrite app_length in H62; simpl in H62.
                                      assert (0 < length rgttreeSm). destruct H67a; destruct rgttreeSm. inversion H21. simpl; lia.
                                      lia.
                                    }                                      

                                    apply all_in_leb_trans with lresLg; auto.
                                    apply all_in_leb_app_head_2 with lresSm; auto.
                                    apply all_in_leb_perm with resiSm leftoveri; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                                { (* exists x \in resiLg *)
                                    apply all_in_leb_trans with resiLg; auto.
                                    apply all_in_leb_app_head_2 with resiSm; auto.
                                    apply all_in_leb_perm with resi leftoveri; auto.
                                }
                            }
                        }
                        {  (* pqlstRgt <= loLft *)
                            apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                            apply all_in_leb_app_lst; auto.
                            destruct H67 as [ H67 | (H67a, H67b) ]; auto.
                            rewrite H67; auto.
                        }
                    }
                }
            }



        { (* size pq < K*)
            simpl.  
            split_andb_leb.
            simpl; rewrite Heq_peek; simpl.
            destruct (insert_bounded_relate_perm K datapt (sum_dist query) pt pq lst Hpriq Habs)
                as (eSm, (eLg, (lstSm, (lstLg, (resi, (leftoveri, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, H9)))))))))))))).
            apply H8 in Heq_Ksize as H8stuff; clear H9 H8.
            assert (leftoveri = []).
            {
                split_andb_leb.
                replace eLg with (@nil datapt) in H6; auto.
                replace lstLg with (@nil datapt) in H6; auto.
                simpl in H6.
                apply Permutation_nil; auto.
            }
            replace leftoveri with (@nil datapt) in *; auto; clear H H6 H7 leftoveri.
            replace lstSm with lst in *; auto. 2:{ split_andb_leb; auto. }
            replace eSm with [pt] in *; auto. 2:{ split_andb_leb; auto. }
            clear lstSm eSm lstLg eLg H3 H4 H8stuff.
            assert (size _ _ (insert_bounded K _ _ pt pq) = 1 + size _ _  pq).
            { eapply insert_bounded_lt_preserve_max; eauto. }
            generalize dependent (insert_bounded K datapt (sum_dist query) pt pq); intros pq'; intros.

            destruct (ith_leb ax pt query) eqn:Heq_ith.
            { (* ith = true --- lft then rgt *)
                destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq' _ H1 H2) 
                    as (pqlstLft, (Hplft, Halft)).
                destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query _ _ Hplft Halft) 
                    as (pqlstRgt, (Hprgt, Hargt)).
                
                pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                destruct (cont_node_inv _ _ _ _ _ Htree) as (lftConts, (rgtConts, (Hcontlft, (Hcontrgt, Hconteq)))).
                destruct (IHlft _ _ _ _ _ _
                        HK H6 Hcontlft H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                destruct (IHrgt _ _ _ _ _ _ 
                        HK H3 Hcontrgt Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                clear IHlft IHrgt.
                rewrite Hconteq.
                assert (Permutation result pqlstRgt).
                { apply abs_perm with (sum_dist query)
                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')); auto. }
        
                assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                    H5 Hl1 HresiSm_Lg) as
                                (eSm, (eLg, (lstSm, (lstLg, HresiStuff)))).
                assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                    Hl3 Hr1 HlresSm_Lg) as
                                (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                assert (Permutation (eSm ++ lstSm) resiSm) as HeSm1; try tauto.
                assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                    HeSm1 HeSm2 HeSm3) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff2)))).
                assert (Permutation (eSmSm ++ lstSmSm ++ lfttreeSmSm) lresSm).
                {
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    replace (eSmSm ++ lstSmSm ++ lfttreeSmSm) with ((eSmSm ++ lstSmSm) ++ lfttreeSmSm); auto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                }
    
                exists lstSmSm.
                exists (lstSmLg ++ lstLg).
                exists (eSmSm ++ lfttreeSmSm ++ rgttreeSm).
                exists (eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                exists (loLft ++ loRgt).
                assert (Permutation (lstSmSm ++ lstSmLg ++ lstLg) lst).
                {
                    permtrans (lstSm ++ lstLg); try tauto.
                    assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                    rewrite app_assoc.
                    apply Permutation_app; auto.
                }
                
                assert (Permutation ((eSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                (pt :: lftConts ++ rgtConts)).
                {
                    repeat rewrite <- app_assoc; auto.
                    do 3 rewrite app_assoc.
                    permtrans (eSmLg ++ (((eSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg)
                                    ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    do 2 rewrite app_assoc.
                    permtrans (eLg ++ ((eSm ++ lfttreeSmSm) ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans ([pt] ++ lfttreeSmSm ++ rgttreeSm ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    replace (pt :: lftConts ++ rgtConts) with ([pt] ++ lftConts ++ rgtConts); auto.
                    apply Permutation_app; auto.
                    (* done [pt] *)                    
                    permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    assert (Permutation (lfttreeSmSm ++ lfttreeSmLg) lfttreeSm); try tauto.
                    rewrite app_assoc.
                    permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                    rewrite app_assoc.
                    permtrans (lftConts ++ rgttreeSm ++ rgttreeLg).
                }

                assert (Permutation (lstSmSm ++ eSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                {
                    permtrans pqlstRgt.
                    rewrite app_assoc. rewrite app_assoc.
                    permtrans (lresSm ++ rgttreeSm).
                    rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                    apply Permutation_app; apply Permutation_sym; auto.
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                    assert (Permutation (lstSmSm ++ eSmSm) resiSmSm); auto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    permtrans (eSmSm ++ lstSmSm).
                }

                assert (Permutation ((lstSmLg ++ lstLg) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg) (loLft ++ loRgt)).
                {
                    permtrans (eLg ++ (lstSmLg ++ lstLg) ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite <- app_assoc.
                    permtrans (eLg ++ lstLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite app_assoc.
                    assert (Permutation (eLg ++ lstLg) resiLg); try tauto.
                    permtrans (resiLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    do 3 rewrite app_assoc.
                    permtrans (lfttreeLg ++ (((resiLg ++ lstSmLg) ++ eSmLg) ++ lfttreeSmLg) ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    apply Permutation_app. rewrite Permutation_app_comm; tauto.
                    assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                    assert (Permutation (eSmLg ++ lstSmLg) resiSmLg); try tauto.
                    permtrans (eSmLg ++ lstSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (resiSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (lresLg ++ rgttreeLg).
                }

                assert (size datapt (sum_dist query)
                (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')) < K -> loLft = [] /\ loRgt = []).
                { (* size / leftover empty *)
                    intros HltK.
                    apply Hr6 in HltK as Hr6'.
                    eapply knn_preserve_size_lt_inv in HltK as HltK'; eauto.
                }

                repeat split; auto.

                {
                    intros HszK.
                    apply H12 in HszK as (Hsz1, Hsz2).
                    replace loLft with (@nil datapt); replace loRgt with (@nil datapt); auto.
                }
                { (* pqlstRgt <= loLft ++ loRgt *)
                    apply all_in_leb_perm with pqlstRgt (loLft ++ loRgt); auto.
                    apply all_in_leb_lst_app; auto.

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query)
                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                    (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')))
                        K); auto.
                    {
                        apply H12 in H13 as (Hsz1, Hsz2).
                        replace loLft with (@nil datapt); auto.
                    }

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query) (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq'))
                                        K); auto.
                    {
                        apply Hl6 in H14. replace loLft with (@nil datapt); auto.
                    }

                    assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                    {
                        apply all_in_leb_app_head_2 with lresSm.
                        apply all_in_leb_app_tail_1 with rgttreeLg.
                        apply all_in_leb_perm with pqlstRgt loRgt; auto.
                    }

                    assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                    { 
                        rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto.
                        rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq')); auto.
                        rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query
                                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query pq'))); auto.
                        erewrite knn_preserve_size_max; eauto.
                    }

                    assert (all_in_leb (sum_dist query) lresLg loLft).
                    {
                        apply all_in_leb_app_head_2 with lresSm; auto.
                        apply all_in_leb_perm with pqlstLft loLft; auto.
                    }

                    assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                    {
                        destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                        -   left.
                            rewrite <- app_nil_end in *.
                            repeat rewrite app_length in *.
                            assert (length rgttreeSm = 0) as H66; try lia.
                            apply length_zero_iff_nil in H66.
                            rewrite H66; auto.
                        -   right.
                            repeat rewrite app_length in *.
                            assert (exists x, In x rgttreeSm).
                            destruct rgttreeSm; simpl in *; try lia. exists d; auto.
                            split; auto.
                            apply all_in_leb_trans with (x :: xs); auto; simpl. exists x; auto.
                    }

                    apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                    apply all_in_leb_app_lst; auto.
                    apply all_in_leb_app_head_1 with lresLg; auto.
                    apply all_in_leb_perm with pqlstLft loLft; auto.
                    destruct H67 as [ H67 | (H67a, H67b)]; auto.
                    rewrite H67; auto.
                }
            }

            { (* ith = false --- rgt then lft *)
                (*apply MAGIC.*)
                destruct (knn_relate K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq' _ H1 H2) 
                    as (pqlstLft, (Hplft, Halft)).
                destruct (knn_relate K k lft (fst (bb_split bb ax (nth ax pt 0))) query _ _ Hplft Halft) 
                    as (pqlstRgt, (Hprgt, Hargt)).
                
                pose proof Hb as Hb'; simpl in Hb'; split_andb_leb.
                destruct (cont_node_inv _ _ _ _ _ Htree) as (rgtConts, (lftConts, (Hcontrgt, (Hcontlft, Hconteq)))).
                destruct (IHrgt _ _ _ _ _ _
                        HK H3 Hcontlft H1 H2 Hplft Halft) as (resiSm, (resiLg, (lfttreeSm, (lfttreeLg, (loLft, (Hl1, (Hl2, (Hl3, (Hl4, (Hl6, Hl5)))))))))).
                destruct (IHlft _ _ _ _ _ _ 
                        HK H6 Hcontrgt Hplft Halft Hprgt Hargt) as (lresSm, (lresLg, (rgttreeSm, (rgttreeLg, (loRgt, (Hr1, (Hr2, (Hr3, (Hr4, (Hr6, Hr5)))))))))).
                clear IHlft IHrgt.
                rewrite Hconteq.
                assert (Permutation result pqlstRgt).
                { apply abs_perm with (sum_dist query)
                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')); auto. }
        
                assert (all_in_leb (sum_dist query) resiSm resiLg) as HresiSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resi _ _ _ _ 
                                    H5 Hl1 HresiSm_Lg) as
                                (eSm, (eLg, (lstSm, (lstLg, HresiStuff)))).
                assert (all_in_leb (sum_dist query) lresSm lresLg) as HlresSm_Lg.
                { eapply perm_split_all_in_leb; eauto. }
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) pqlstLft _ _ _ _ 
                                    Hl3 Hr1 HlresSm_Lg) as
                                (resiSmSm, (resiSmLg, (lfttreeSmSm, (lfttreeSmLg, HpqlstLftStuff)))).
                assert (all_in_leb (sum_dist query) rgttreeSm rgttreeLg) as HrgttreeSm_Lg.
                { rewrite Permutation_app_comm in Hr3, Hr4. eapply perm_split_all_in_leb; eauto.  }
                assert (Permutation (eSm ++ lstSm) resiSm) as HeSm1; try tauto.
                assert (Permutation (resiSmSm ++ resiSmLg) resiSm) as HeSm2; try tauto.
                assert (all_in_leb (sum_dist query) resiSmSm resiSmLg) as HeSm3; try tauto.
                pose proof (perm_split_rearrange_all_in_leb _ (sum_dist query) resiSm _ _ _ _ 
                                    HeSm1 HeSm2 HeSm3) as
                                    (eSmSm, (eSmLg, (lstSmSm, (lstSmLg, HresiStuff2)))).
                assert (Permutation (eSmSm ++ lstSmSm ++ lfttreeSmSm) lresSm).
                {
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    replace (eSmSm ++ lstSmSm ++ lfttreeSmSm) with ((eSmSm ++ lstSmSm) ++ lfttreeSmSm); auto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                }
    
                exists lstSmSm.
                exists (lstSmLg ++ lstLg).
                exists (eSmSm ++ lfttreeSmSm ++ rgttreeSm).
                exists (eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                exists (loLft ++ loRgt).
                assert (Permutation (lstSmSm ++ lstSmLg ++ lstLg) lst).
                {
                    permtrans (lstSm ++ lstLg); try tauto.
                    assert (Permutation (lstSmSm ++ lstSmLg) lstSm); try tauto.
                    rewrite app_assoc.
                    apply Permutation_app; auto.
                }
                
                assert (Permutation ((eSmSm ++ lfttreeSmSm ++ rgttreeSm) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg)
                (pt :: rgtConts ++ lftConts)).
                {
                    repeat rewrite <- app_assoc; auto.
                    do 3 rewrite app_assoc.
                    permtrans (eSmLg ++ (((eSmSm ++ lfttreeSmSm) ++ rgttreeSm) ++ eLg)
                                    ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans (eSm ++ lfttreeSmSm ++ rgttreeSm ++ eLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    do 2 rewrite app_assoc.
                    permtrans (eLg ++ ((eSm ++ lfttreeSmSm) ++ rgttreeSm) ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    permtrans ([pt] ++ lfttreeSmSm ++ rgttreeSm ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg); auto.
                    apply Permutation_app; auto; rewrite Permutation_app_comm; tauto.
                    replace (pt :: rgtConts ++ lftConts) with ([pt] ++ rgtConts ++ lftConts); auto.
                    apply Permutation_app; auto.
                    (* done [pt] *)                    
                    permtrans (lfttreeSmSm ++ lfttreeSmLg ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    assert (Permutation (lfttreeSmSm ++ lfttreeSmLg) lfttreeSm); try tauto.
                    rewrite app_assoc.
                    permtrans (lfttreeSm ++ rgttreeSm ++ lfttreeLg ++ rgttreeLg).
                    permtrans (lfttreeSm ++ lfttreeLg ++ rgttreeSm ++ rgttreeLg).
                    rewrite app_assoc.
                    permtrans (lftConts ++ rgttreeSm ++ rgttreeLg).
                    permtrans (lftConts ++ rgtConts).
                }

                assert (Permutation (lstSmSm ++ eSmSm ++ lfttreeSmSm ++ rgttreeSm) result).
                {
                    permtrans pqlstRgt.
                    rewrite app_assoc. rewrite app_assoc.
                    permtrans (lresSm ++ rgttreeSm).
                    rewrite Permutation_app_comm. apply Permutation_sym; rewrite Permutation_app_comm.
                    apply Permutation_app; apply Permutation_sym; auto.
                    assert (Permutation (resiSmSm ++ lfttreeSmSm) lresSm); try tauto.
                    permtrans (resiSmSm ++ lfttreeSmSm).
                    assert (Permutation (lstSmSm ++ eSmSm) resiSmSm); auto.
                    assert (Permutation (eSmSm ++ lstSmSm) resiSmSm); try tauto.
                    permtrans (eSmSm ++ lstSmSm).
                }

                assert (Permutation ((lstSmLg ++ lstLg) ++ eLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg) (loLft ++ loRgt)).
                {
                    permtrans (eLg ++ (lstSmLg ++ lstLg) ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite <- app_assoc.
                    permtrans (eLg ++ lstLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    rewrite app_assoc.
                    assert (Permutation (eLg ++ lstLg) resiLg); try tauto.
                    permtrans (resiLg ++ lstSmLg ++ eSmLg ++ lfttreeSmLg ++ lfttreeLg ++ rgttreeLg).
                    do 3 rewrite app_assoc.
                    permtrans (lfttreeLg ++ (((resiLg ++ lstSmLg) ++ eSmLg) ++ lfttreeSmLg) ++ rgttreeLg).
                    repeat rewrite <- app_assoc; rewrite app_assoc.
                    apply Permutation_app. rewrite Permutation_app_comm; tauto.
                    assert (Permutation (resiSmLg ++ lfttreeSmLg) lresLg); try tauto.
                    assert (Permutation (eSmLg ++ lstSmLg) resiSmLg); try tauto.
                    permtrans (eSmLg ++ lstSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (resiSmLg ++ lfttreeSmLg ++ rgttreeLg).
                    rewrite app_assoc. permtrans (lresLg ++ rgttreeLg).
                }

                assert (size datapt (sum_dist query)
                (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')) < K -> loLft = [] /\ loRgt = []).
                { (* size / leftover empty *)
                    intros HltK.
                    apply Hr6 in HltK as Hr6'.
                    eapply knn_preserve_size_lt_inv in HltK as HltK'; eauto.
                }

                repeat split; auto.

                {
                    intros HszK.
                    apply H12 in HszK as (Hsz1, Hsz2).
                    replace loLft with (@nil datapt); replace loRgt with (@nil datapt); auto.
                }
                { (* pqlstRgt <= loLft ++ loRgt *)
                    apply all_in_leb_perm with pqlstRgt (loLft ++ loRgt); auto.
                    apply all_in_leb_lst_app; auto.

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query)
                        (knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                    (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')))
                        K); auto.
                    {
                        apply H12 in H13 as (Hsz1, Hsz2).
                        replace loLft with (@nil datapt); auto.
                    }

                    destruct (Nat.lt_ge_cases (size datapt (sum_dist query) (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq'))
                                        K); auto.
                    {
                        apply Hl6 in H14. replace loLft with (@nil datapt); auto.
                    }

                    assert (all_in_leb (sum_dist query) rgttreeSm lresLg) as H30.
                    {
                        apply all_in_leb_app_head_2 with lresSm.
                        apply all_in_leb_app_tail_1 with rgttreeLg.
                        apply all_in_leb_perm with pqlstRgt loRgt; auto.
                    }

                    assert (length (lresSm ++ lresLg) = length (lresSm ++ rgttreeSm)) as H62.
                    { 
                        rewrite (Permutation_length Hr1). rewrite (Permutation_length Hr3); auto.
                        rewrite <- size_relate with (p:=(knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq')); auto.
                        rewrite <- size_relate with (p:=(knn K k lft (fst (bb_split bb ax (nth ax pt 0))) query
                                        (knn K k rgt (snd (bb_split bb ax (nth ax pt 0))) query pq'))); auto.
                        erewrite knn_preserve_size_max; eauto.
                    }

                    assert (all_in_leb (sum_dist query) lresLg loLft).
                    {
                        apply all_in_leb_app_head_2 with lresSm; auto.
                        apply all_in_leb_perm with pqlstLft loLft; auto.
                    }

                    assert (rgttreeSm = [] \/ (exists x, In x rgttreeSm) /\ all_in_leb (sum_dist query) rgttreeSm loLft) as H67.
                    {
                        destruct lresLg as [ | x xs ] eqn:Heq_lresLg.
                        -   left.
                            rewrite <- app_nil_end in *.
                            repeat rewrite app_length in *.
                            assert (length rgttreeSm = 0) as H66; try lia.
                            apply length_zero_iff_nil in H66.
                            rewrite H66; auto.
                        -   right.
                            repeat rewrite app_length in *.
                            assert (exists x, In x rgttreeSm).
                            destruct rgttreeSm; simpl in *; try lia. exists d; auto.
                            split; auto.
                            apply all_in_leb_trans with (x :: xs); auto; simpl. exists x; auto.
                    }

                    apply all_in_leb_perm with (lresSm ++ rgttreeSm) loLft; auto.
                    apply all_in_leb_app_lst; auto.
                    apply all_in_leb_app_head_1 with lresLg; auto.
                    apply all_in_leb_perm with pqlstLft loLft; auto.
                    destruct H67 as [ H67 | (H67a, H67b)]; auto.
                    rewrite H67; auto.
                }                
            }
        }
    }

Qed.




Lemma knn_full_relate :
    forall K k data query,
    0 < K ->
    0 < length data ->
    0 < k ->
    (forall v' : datapt, In v' data -> length v' = k) ->
    forall pq, 
    pq = (knn K k (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k)) query
                                            (empty datapt (sum_dist query))) ->
    exists result leftover : list datapt,
        Permutation data (result ++ leftover) /\
        Abs datapt (sum_dist query) pq result /\
        all_in_leb (sum_dist query) result leftover.
Proof.
    intros K k data query HK Hlen Hk Hd pq Hpq.
    assert (kdtree_bounded (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k)) = true) as Hb.
    apply build_kdtree_bounded; auto.
    destruct (build_kdtree_contents_perm k data Hk) as (data', (Hcont, Hperm')).

    assert (Abs datapt (sum_dist query) (empty datapt (sum_dist query)) []).
    apply empty_relate; auto.

    destruct (knn_relate K k (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k))
    query (empty datapt (sum_dist query)) []) as (result, (H1, H2)); auto.

    destruct (knn_full_relate_gen K k (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k))
    query (empty datapt (sum_dist query)) [] data' result HK) 
        as (lstSm, (lstLg, (dataSm, (dataLg, (leftover, Hstuff))))); auto.

    exists result, leftover.
    split_andb_leb; repeat split; auto.
    permtrans data'.
    permtrans (dataSm ++ dataLg).
    apply Permutation_sym, Permutation_nil, app_eq_nil in H0 as (H0a, H0b).
    rewrite H0a in *; rewrite H0b in *; simpl in *; auto.
    rewrite Hpq; auto.
Qed.



Theorem knn_search_build_kdtree_correct :
    forall (K:nat) (k : nat) (data : list datapt),
    0 < K ->
    0 < length data ->
    0 < k ->
    (forall v' : datapt, In v' data -> length v' = k) ->
    forall tree query result,
    tree = (build_kdtree k data) ->
    knn_search K k tree query = result ->
    exists leftover, 
        length result = min K (length data)
        /\ Permutation data (result ++ leftover)
        /\ all_in_leb (sum_dist query) result leftover.
Proof.
    intros K k data HK Hlen Hk Hin tree query result Htree Hknn.
    rewrite Htree in *; clear Htree tree.
    unfold knn_search in Hknn.
    pose proof (build_kdtree_contents_perm k data Hk) as (lst, (Hc, Hp)).
    
    assert (priq _ _ (knn K k (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k)) query
        (empty datapt (sum_dist query)))) as Hpriq.
    {
        destruct (knn_relate K k (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k)) query
        (empty datapt (sum_dist query)) []) as (lst', (Hpriq, Habs)); auto.
        apply empty_relate; auto.
    }

    assert (exists top, exists leftover,
                Permutation data (top ++ leftover) /\
                (Abs _ _ (knn K k (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k)) query
                        (empty datapt (sum_dist query))) top) /\
                all_in_leb (sum_dist query) top leftover)
        (*(forall k, In k top -> (forall j, In j leftover -> sum_dist query k <=? sum_dist query j = true))) *)
    as (top, (leftover, (Hperm, (Habs, Hle)))).
    {
        apply (knn_full_relate K k data query HK Hlen Hk Hin (knn K k (build_kdtree k data) (mk_bbox (repeat None k) (repeat None k)) query
    (empty datapt (sum_dist query)))); auto.
    }
        
    pose proof (pq_to_list_relate _ _ _ _ _ Hpriq Habs Hknn).
    exists leftover; repeat split.
    -   apply size_relate in Habs as Hsz; auto.
        pose proof (knn_search_build_size K k data query Hk).
        rewrite Hsz in H0. apply Permutation_length in H as Hresultlen. rewrite Hresultlen.
        auto.
    -   permtrans (top ++ leftover).
    -   apply all_in_leb_perm with top leftover; auto.
Qed.





End KNNS.

Module MaxPQ := List_MaxPQ NatTTLB.
Module KNNS_LPQ := KNNS MaxPQ.
Import KNNS_LPQ.

Example ex1 : (rev (knn_search 3 2 two_tree [ 5 ; 5 ])) = [[4; 3]; [5; 10]; [8; 2]]  := refl_equal.
Example ex2 : (rev (knn_search 1 2 two_tree [ 5 ; 5 ])) = [[4; 3]] := refl_equal.
Example ex3 : (rev (knn_search 5 2 two_tree [ 5 ; 5 ])) = [[4; 3]; [5; 10]; [8; 2]; [7; 12]; [9; 10]] := refl_equal.



