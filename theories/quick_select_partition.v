
From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Bool.
From Coq Require Import Lists.List.
Require Export Permutation.
Import ListNotations.
Require Import Lia.




Definition partition_larger {X:Set} (pivot:X) (l:list X) (le:X -> X -> bool) : list X :=  
    filter (fun x => andb (le pivot x) (negb (le x pivot))) l.

Example test_partitionLF_1: partition_larger 3 (1 :: 2:: 4 :: 5 :: nil) Nat.leb = (4 :: 5 :: nil).
Proof. reflexivity. Qed.

Definition partition_smaller {X:Set} (pivot:X) (l:list X) (le:X -> X -> bool) : list X :=  
    filter (fun x => (negb (le pivot x))) l.

Definition partition_equal {X:Set} (pivot:X) (l:list X) (le:X -> X -> bool) : list X :=  
  filter (fun x => andb (le x pivot) (le pivot x)) l.

Definition partition_sm_eq_lg {X:Set} (pivot:X) (l:list X) (le:X -> X -> bool) : (list X * list X * list X) :=
  (partition_smaller pivot l le, partition_equal pivot l le, partition_larger pivot l le).


Fixpoint dropn {A:Type} (n:nat) (lst:list A) : list A :=
  match n with 
    | 0 => lst
    | S n' => match lst with 
              | [] => []
              | h :: t => dropn n' t
    end
  end.


Fixpoint qsp {X:Set} (steps:nat) (k:nat) (l:list X) (le:X -> X -> bool) : option (list X * X * list X) :=
  match steps with 
  | 0 => None (* case should never happen *)
  | S steps' =>
    match l with 
      | nil => None
      (* difference betw/ the Racket impl and this: the pivot here is *not* part
          of the partitioned lists *)
      | pivot :: lst => 
            let '(sm, eq, lg) := partition_sm_eq_lg pivot lst le in
      (*let lg := partition_larger pivot lst le in
                        let sm := partition_smaller pivot lst le in
                        let eq := partition_equal pivot lst le in*)
            if k <? length sm then
              match qsp steps' k sm le with
              | None => None
              | Some (a, x, b) => Some (a, x,  b ++ ((pivot::eq) ++ lg))
              end
            else if (length sm + length eq ) <? k then
            match qsp steps' (k - S (length sm + length eq)) lg le with
            | None => None
            | Some (a, x, b) => Some (a ++ (sm ++ (pivot::eq)), x, b)
            end
            else
             Some (sm ++ (firstn (k - length sm) eq), 
                   pivot, 
                   (dropn (k - length sm) eq) ++ lg)
    end
  end.

  Require Import Program.
  From Coq.Program Require Import Wf.
Program Fixpoint qsp_m {X:Set} (k:nat) (l:list X) (le:X -> X -> bool) {measure (length l)}: option (list X * X * list X) :=
    match l with 
      | nil => None
      (* difference betw/ the Racket impl and this: the pivot here is *not* part
          of the partitioned lists *)
      | pivot :: lst => 
            let '(sm, eq, lg) := partition_sm_eq_lg pivot lst le in
      (*let lg := partition_larger pivot lst le in
                        let sm := partition_smaller pivot lst le in
                        let eq := partition_equal pivot lst le in*)
            if k <? length sm then
              match qsp_m k sm le with
              | None => None
              | Some (a, x, b) => Some (a, x,  b ++ ((pivot::eq) ++ lg))
              end
            else if (length sm + length eq ) <? k then
            match qsp_m (k - S (length sm + length eq)) lg le with
            | None => None
            | Some (a, x, b) => Some (a ++ (sm ++ (pivot::eq)), x, b)
            end
            else
              Some (sm ++ (firstn (k - length sm) eq), 
                    pivot, 
                    (dropn (k - length sm) eq) ++ lg)
    end.
Next Obligation.
  generalize le pivot lst.
  clear k le pivot lst qsp_m.
  induction lst; simpl; auto.
  destruct (negb (le pivot a)); simpl in *; try lia.
Qed.
Next Obligation.
generalize le pivot lst.
clear k le pivot lst qsp_m.
induction lst; simpl; auto.
destruct (le pivot a && negb (le a pivot)); simpl in *; try lia.
Qed.

Definition quick_select {X} k l le := @qsp X (length l) k l le.
   (* {X:Set} (k:nat) (l:list X) (le:X -> X -> bool) : option (list X * X * list X) *)

 
Definition median_partition {X:Set} (l:list X) (le:X -> X -> bool) 
  (* : option (list X * X * list X) *)
  := quick_select (div2 (length l)) l le.


Example test_qsp1 :
  (quick_select 0 (4 :: 9 :: 1 :: 3 :: 7 :: 5 :: 12 :: 8 :: 3 :: 5 :: 4 :: nil) Nat.leb)
    = Some (nil, 1, (3::3::4::4::9::7::5::12::8::5::nil)).
reflexivity. Qed.

Example test_qsp2 :
  (quick_select 4 (4 :: 9 :: 1 :: 3 :: 7 :: 5 :: 12 :: 8 :: 3 :: 5 :: 4 :: nil) Nat.leb)
    = Some ((1 :: 3 :: 3 :: 4 :: nil) ,  4 , (9 :: 7 :: 5 :: 12 :: 8 :: 5 :: nil)).
reflexivity. Qed.

Example test_qsp1_m :
  (qsp_m 0 (4 :: 9 :: 1 :: 3 :: 7 :: 5 :: 12 :: 8 :: 3 :: 5 :: 4 :: nil) Nat.leb)
    = Some (nil, 1, (3::3::4::4::9::7::5::12::8::5::nil)).
reflexivity. Qed.

Example test_qsp2_m :
  (qsp_m 4 (4 :: 9 :: 1 :: 3 :: 7 :: 5 :: 12 :: 8 :: 3 :: 5 :: 4 :: nil) Nat.leb)
    = Some ((1 :: 3 :: 3 :: 4 :: nil) ,  4 , (9 :: 7 :: 5 :: 12 :: 8 :: 5 :: nil)).
reflexivity. Qed.


(* 
Example test_qsp3 :              
  (quick_select 3 '(4 9 1 3 7 5 12 8 3 5 4) <=)
              '( (1 3 3)   4    (4 9 7 5 12 8 5)))

Example test_qsp4 :              
  (quick_select 7 '(5 4 9  1 3 7 5 12 5 8 3 5 4 6 5) <=)
              '((4 1 3 3 4 5 5)   5   (5 5 9 7 12 8 6)))

Example test_qsp5 : 
  (quick_select 7 '(4 5 9  1 3 7 5 12 5 8 3 5 4 6 5) <=)
              '((1 3 3 4 4 5 5)   5   (5 5 9 7 12 8 6)))
*)              






Lemma k_list_lengths : 
  forall X (l1:list X) (l2:list X) k, 
  (k <? length l1 = true) \/ 
  (k <? length l1 = false /\ length l1 + length l2 <? k = true) \/ 
  (k <? length l1 = false /\ length l1 + length l2 <? k = false
    /\ k <=? length l1 + length l2 = true /\ length l1 <=? k = true).
Proof.
  intros.
  destruct (le_lt_dec (length l1) k) as [Hk1 | Hk2].
  2: {  (* k < length l1 *)
    rewrite <- Nat.ltb_lt in Hk2; auto.
  }

  destruct (le_lt_dec k (length l1 + length l2)) as [Hk3 | Hk4].
  right; right; repeat split; try rewrite Nat.ltb_ge; auto;
   rewrite Nat.leb_le; auto.

  right; left; split; 
  rewrite <- Nat.ltb_lt in Hk4; auto.
  rewrite Nat.ltb_ge; auto.
Qed.


Lemma partitions_permutation :
  forall (X:Set) v le (lst:list X), 
    Permutation lst 
      (partition_smaller v lst le ++ partition_equal v lst le ++ partition_larger v lst le).
Proof.
  induction lst; auto.
  simpl.
  apply perm_trans with (a :: (partition_smaller v lst le ++
                        partition_equal v lst le ++ partition_larger v lst le)).
  - auto using perm_skip.
  - destruct (le a v) eqn:Hav;
     destruct (le v a) eqn:Hva; simpl; try auto using Permutation_middle.
    replace (partition_smaller v lst le ++ partition_equal v lst le ++ a :: partition_larger v lst le) 
      with ((partition_smaller v lst le ++ partition_equal v lst le) ++ a :: partition_larger v lst le); 
        try rewrite app_assoc; auto.
    replace (a :: partition_smaller v lst le ++ partition_equal v lst le ++ partition_larger v lst le)
      with (a :: (partition_smaller v lst le ++ partition_equal v lst le) ++ partition_larger v lst le);
        try rewrite app_assoc; auto.
    auto using Permutation_middle.
Qed.


Lemma perm_smaller :
  forall (X:Set) (h v:X) t l1 l2 sm eq lg,
    Permutation sm (l1 ++ v :: l2) ->
    Permutation t (sm ++ eq ++ lg) ->
    Permutation (h::t) (l1 ++ v :: l2 ++ h :: eq ++ lg).
Proof.
  intros.
  apply perm_trans with (h:: l1 ++ v :: l2 ++ eq ++ lg).
  apply perm_skip.
  apply perm_trans with (sm ++ eq ++ lg); auto.
  apply perm_trans with ((l1 ++ v :: l2) ++ eq ++ lg).
  auto using Permutation_app_tail.
  rewrite app_assoc_reverse; auto.

  apply perm_trans with (l1 ++ h :: v :: l2 ++ eq ++ lg).
  apply Permutation_middle.
  apply Permutation_app_head.
  apply (Permutation_middle (v::l2)).
Qed.


Lemma perm_larger :
    forall (X:Set) (h v:X) t l1 l2 sm eq lg,
      Permutation lg (l1 ++ v :: l2) ->
      Permutation t (sm ++ eq ++ lg) ->
      Permutation (h::t) ((l1 ++ sm ++ h :: eq) ++ v :: l2).
Proof.
  intros.
  apply perm_trans with (h :: ((l1 ++ sm ++ eq) ++ v :: l2)).
  - apply perm_skip.
    rewrite app_assoc_reverse.
    apply perm_trans with ((sm ++ eq) ++ l1 ++ (v :: l2)).
    apply perm_trans with (sm ++ eq ++ lg); auto.
    rewrite app_assoc_reverse.
    auto using Permutation_app_head.

    apply Permutation_app_swap_app.
  - replace (h :: (l1 ++ sm ++ eq) ++ v :: l2)
        with ((h :: (l1 ++ sm ++ eq)) ++ v :: l2); auto.
      apply  Permutation_app_tail.
      apply perm_trans with (l1 ++ h :: sm ++ eq); 
         auto using Permutation_middle, Permutation_app_head.
Qed.


Lemma firstn_dropn_full : 
  forall X k (lst:list X),
  firstn k lst ++ dropn k lst = lst.
Proof.
  induction k as
    [ (* k = 0 *)
     | k' (* k = 1 + k' *) IHk ]; auto.
  destruct lst as
    [ (* lst = [] *) 
     | h t (* lst = h :: t *) IHlst ]; auto.
  simpl. (* h :: firstn k' t ++ dropn k' t = h :: t *)
  rewrite IHk; auto.
Qed.


Lemma perm_equal :
  forall (X:Set) (h v:X) t l1 l2 sm eq lg k,
    sm ++ firstn k eq = l1 ->
    dropn k eq ++ lg = l2 ->
    Permutation t (sm ++ eq ++ lg) ->
    Permutation (h::t) (l1 ++ h :: l2).
Proof.
  intros X h v t l1 l2 sm eq lg k H1 H2 H3.
  rewrite <- H1; rewrite <- H2.
  apply perm_trans with (h :: (sm ++ firstn k eq) ++ dropn k eq ++ lg); auto.
  apply perm_skip.
  rewrite <- app_assoc.
  replace (firstn k eq ++ dropn k eq ++ lg) 
    with ((firstn k eq ++ dropn k eq) ++ lg).
  rewrite firstn_dropn_full; auto. 
  rewrite app_assoc; auto.
  apply Permutation_middle.
Qed.


Theorem qsp_permutation : forall (X:Set) steps (k:nat) (l:list X) (le:X -> X -> bool) 
  l1 l2 v,
  qsp steps k l le = Some (l1, v, l2) -> 
  Permutation l (l1 ++ v :: l2).
Proof.
  induction steps as [ | steps' IH]; intros k l le l1 l2 v Hq; try discriminate.
  destruct l as [ | h t ]; try discriminate.
  simpl in Hq.
  generalize (partitions_permutation _ h le t); intros Hperm.
  destruct (k_list_lengths _ (partition_smaller h t le) (partition_equal h t le) k)
    as [Hk | [(Hk, Hk1) | (Hk, (Hk1, (Hk2, Hk3)))]]; try rewrite Hk in Hq; try rewrite Hk1 in Hq.

  - destruct (qsp steps' k (partition_smaller h t le) le) as [ ((l1',v'),l2') | ]
      eqn:Hq1; try discriminate.
    apply IH in Hq1.
    injection Hq as He1 He2 He3.
    rewrite He1 in *; rewrite He2 in *. clear He1 He2 l1' v'.
    rewrite <- He3; clear He3 l2.
    eapply perm_smaller; eauto.

  - destruct (qsp steps' (k - S (length (partition_smaller h t le) + length (partition_equal h t le)))
                      (partition_larger h t le) le) as [ ((l1',v'),l2') | ]
      eqn:Hq1; try discriminate.
    apply IH in Hq1.
    injection Hq as He1 He2 He3.
    rewrite He2 in *; rewrite He3 in *. clear He2 He3 l2' v'.
    rewrite <- He1; clear He1 l1.
    eapply perm_larger; eauto.

  - injection Hq as He1 He2 He3.
    rewrite <- He2 in *; clear He2 v.
    eapply perm_equal; eauto.
Qed.



Theorem quick_select_permutation :
  forall (X:Set) (k:nat) (l:list X) (le:X -> X -> bool) 
  l1 l2 v,
  quick_select k l le = Some (l1, v, l2) -> 
  Permutation l (l1 ++ v :: l2).
Proof.
  intros; unfold quick_select in *.
  eapply qsp_permutation; eauto.
Qed.



(* ***************************************************************************** *)


Theorem qsp_position : forall (X:Set) steps (k:nat) (l:list X) (le:X -> X -> bool) 
  l1 l2 v,
  qsp steps k l le = Some (l1, v, l2) -> 
  length l1 = k.
Proof.
  induction steps as [ | steps' IH]; intros k l le l1 l2 v Hq; try discriminate.
  destruct l as [ | h t ]; try discriminate.
  simpl in Hq.
  destruct (k_list_lengths _ (partition_smaller h t le) (partition_equal h t le) k)
    as [Hk | [(Hk, Hk1) | (Hk, (Hk1, (Hk2, Hk3)))]]; try rewrite Hk in Hq; try rewrite Hk1 in Hq.

  - destruct (qsp steps' k (partition_smaller h t le) le) as [ ((l1',v'),l2') | ]
        eqn:Hq1; try discriminate.
    apply IH in Hq1.
    injection Hq as He1 He2 He3. rewrite <- He1; auto.

    - destruct (qsp steps' (k - S (length (partition_smaller h t le) + length (partition_equal h t le)))
          (partition_larger h t le) le) as [ ((l1',v'),l2') | ]
          eqn:Hq1; try discriminate.
      apply IH in Hq1.
      injection Hq as He1 He2 He3.
      rewrite <- He1.
      repeat rewrite app_length; simpl.
      rewrite Nat.ltb_lt in Hk1; auto.
      lia.

    - injection Hq as He1 He2 He3.
    try rewrite Nat.leb_le in *; try rewrite Nat.ltb_ge in *.
    rewrite <- He1.
    rewrite app_length.
    rewrite firstn_length_le; lia.
Qed.






(* ***************************************************************************** *)


Definition le_props {X:Set} (le:X -> X -> bool) : Prop :=
    (forall a b c, le a b = true -> le b c = true -> le a c = true) /\
    (forall a b, le a b = true \/ le b a = true).

Lemma le_trans : forall (X:Set) (le:X -> X -> bool) (Hle:le_props le),
  forall a b c, le a b = true -> le b c = true -> le a c = true.
Proof.
  intros X le (Hle1, Hle2) a b c H1 H2; eapply Hle1; eauto.
Qed.

Lemma not_le_le : forall (X:Set) (le:X -> X -> bool) (Hle:le_props le),
  forall a b, le a b = false -> le b a = true.
Proof.
  intros X le (Hle1, Hle2) a b H1.
  destruct (Hle2 a b); auto.
  rewrite H in H1; discriminate.
Qed.



(* ***************************************************************************** *)

Lemma in_partition_smaller :
  forall (X:Set) (x:X) p (lst:list X) le,
  In x (partition_smaller p lst le) ->
  le p x = false.
Proof.
  induction lst; simpl; intros.
  inversion H.
  destruct (le p a) eqn:Hpa; simpl in H; auto.
  - inversion H; [ idtac | try apply IHlst; auto].
    rewrite H0 in *; auto.
Qed.

Lemma in_partition_larger :
  forall (X:Set) (x:X) p (lst:list X) le,
  In x (partition_larger p lst le) ->
  le p x = true /\ le x p = false.
Proof.
  induction lst; simpl; intros.
  inversion H.
  destruct (le p a) eqn:Hpa; destruct (le a p) eqn:Hap; simpl in H; auto.
  - inversion H; [ idtac | try apply IHlst; auto].
    rewrite H0 in *; auto.
Qed.

Lemma in_partition_equal :
  forall (X:Set) (x:X) p (lst:list X) le,
  In x (partition_equal p lst le) ->
  le p x = true /\ le x p = true.
Proof.
  induction lst; simpl; intros.
  inversion H.
  destruct (le p a) eqn:Hpa; destruct (le a p) eqn:Hap; simpl in H; auto.
  - inversion H; [ idtac | try apply IHlst; auto].
    rewrite H0 in *; auto.
Qed.


Lemma in_firstn : forall X (x:X) k lst, In x (firstn k lst) -> In x lst.    
Proof.
  induction k; simpl; intros.
  inversion H.
  destruct lst; inversion H.
  rewrite H0; left; auto.
  right; apply IHk; auto.
Qed.

Lemma in_dropn : forall X (x:X) k lst, In x (dropn k lst) -> In x lst.    
Proof.
  induction k; simpl; intros; auto.
  destruct lst.
  inversion H.
  right; auto.
Qed.


Theorem qsp_all_smaller : forall (X:Set) steps (k:nat) (l:list X) (le:X -> X -> bool) 
  l1 l2 v (Hle:le_props le),
  qsp steps k l le = Some (l1, v, l2) -> 
  forall x, In x l1 -> le x v = true.
Proof.
  induction steps as [ | steps' IH]; intros k l le l1 l2 v Hle Hq; try discriminate.
  destruct l as [ | h t ]; try discriminate.
  simpl in Hq.
  destruct (k_list_lengths _ (partition_smaller h t le) (partition_equal h t le) k)
    as [Hk | [(Hk, Hk1) | (Hk, (Hk1, (Hk2, Hk3)))]]; try rewrite Hk in Hq; try rewrite Hk1 in Hq;
      intros x Hin.

  - destruct (qsp steps' k (partition_smaller h t le) le) as [ ((l1',v'),l2') | ]
      eqn:Hq1; try discriminate.
    generalize (IH _ _ _ _ _ _ Hle Hq1); intros IHq.
    injection Hq as He1 He2 He3. 
    rewrite <- He2; apply IHq; rewrite He1; auto.

  - destruct (qsp steps' (k - S (length (partition_smaller h t le) + length (partition_equal h t le)))
      (partition_larger h t le) le) as [ ((l1',v'),l2') | ]
      eqn:Hq1; try discriminate.
    generalize (IH _ _ _ _ _ _ Hle Hq1); intros IHq.
    injection Hq as He1 He2 He3. 
    rewrite He2 in *; rewrite <- He1 in *; clear v' He2 l1 He1.

    destruct (in_app_or _ _ _ Hin).
    apply IHq; auto.


    (* idea: from Hq1 --- need to use qsp_permutation
          to say that v is in partition_larger, and then
          that everything in partition_larger is > h (the pivot),  so
                      in particular v > h
          and that everything in partition_smaller is < h .
          So if x is in partition_smaller (H0), then  x < h  .
          But then, that means x < v.
          *)

    generalize (qsp_permutation _ _ _ _ _ _ _ _ Hq1); intros Hperm.
    apply Permutation_sym in Hperm.

    destruct (in_app_or _ _ _ H).
    -- apply Permutation_in with (x := v) in Hperm; try apply in_elt.
      apply in_partition_smaller in H0.
      apply in_partition_larger in Hperm.
      destruct Hperm as [Hperm1 Hperm2].
      apply not_le_le in H0; auto.
      apply le_trans with h; auto.

    -- apply Permutation_in with (x := v) in Hperm; try apply in_elt.
       destruct H0 as [Hxh | Hxpart].

       apply in_partition_larger in Hperm.
       destruct Hperm as [Hperm1 Hperm2].
       rewrite <- Hxh; auto.

       apply in_partition_larger in Hperm.
       destruct Hperm as [Hperm1 Hperm2].
       apply in_partition_equal in Hxpart.
       destruct Hxpart as [Hx1 Hx2].
       destruct Hle as (Hle1, Hle2).
       apply Hle1 with h; auto.

  - injection Hq as He1 He2 He3. 
    rewrite He2 in *; rewrite <- He1 in *; clear h He2 l1 He1.
    destruct (in_app_or _ _ _ Hin).

    -- apply in_partition_smaller in H.
    destruct Hle as (_, Hle2).
    destruct (Hle2 x v); auto.
    rewrite H in *; discriminate.

    -- apply in_firstn in H.
    apply in_partition_equal in H.
    destruct H as [Hx1 Hx2]; auto.
Qed.



(* ***************************************************************************** *)

Theorem qsp_all_larger : forall (X:Set) steps (k:nat) (l:list X) (le:X -> X -> bool) 
  l1 l2 v (Hle:le_props le),
  qsp steps k l le = Some (l1, v, l2) -> 
  forall x, In x l2 -> le v x = true.
Proof.
  induction steps as [ | steps' IH]; intros k l le l1 l2 v Hle Hq; try discriminate.
  destruct l as [ | h t ]; try discriminate.
  simpl in Hq.
  destruct (k_list_lengths _ (partition_smaller h t le) (partition_equal h t le) k)
    as [Hk | [(Hk, Hk1) | (Hk, (Hk1, (Hk2, Hk3)))]]; try rewrite Hk in Hq; try rewrite Hk1 in Hq;
      intros x Hin.

  - destruct (qsp steps' k (partition_smaller h t le) le) as [ ((l1',v'),l2') | ]
      eqn:Hq1; try discriminate.
    generalize (IH _ _ _ _ _ _ Hle Hq1); intros IHq.
    injection Hq as He1 He2 He3.
    rewrite He2 in *; rewrite He1 in *; clear v' He2 l1' He1.
    rewrite <- He3 in Hin.

    assert (le v h = true).
    1: {
      generalize (qsp_permutation _ _ _ _ _ _ _ _ Hq1); intros Hperm.
      apply Permutation_sym in Hperm.
      apply Permutation_in with (x := v) in Hperm; try apply in_elt.
      apply in_partition_smaller in Hperm.
      apply not_le_le in Hperm; auto.
    }

    destruct (in_app_or _ _ _ Hin) as [Hin1 | Hin']; auto.
    destruct Hin' as [Hin2 | Hin3]; auto.
    rewrite <- Hin2 in *; auto.
    destruct (in_app_or _ _ _ Hin3) as [Hin4 | Hin5]; auto.
    apply in_partition_equal in Hin4.
    apply le_trans with h; destruct Hin4; auto.
    apply in_partition_larger in Hin5.
    apply le_trans with h; destruct Hin5; auto.
  
  - destruct (qsp steps' (k - S (length (partition_smaller h t le) + length (partition_equal h t le)))
        (partition_larger h t le) le) as [ ((l1',v'),l2') | ]
        eqn:Hq1; try discriminate.
    generalize (IH _ _ _ _ _ _ Hle Hq1); intros IHq.
    injection Hq as He1 He2 He3. 
    rewrite He2 in *; rewrite  He3 in *; auto.

  - injection Hq as He1 He2 He3. 
    rewrite He2 in *; rewrite <- He3 in *; clear h He2 l2 He3.
    destruct (in_app_or _ _ _ Hin) as [Hin1 | Hin2]; auto.
    -- apply in_dropn in Hin1.
        apply in_partition_equal in Hin1; destruct Hin1; auto.
    --  apply in_partition_larger in Hin2; destruct Hin2; auto.
Qed.



(* ***************************************************************************** *)

Lemma partition_smaller_length :
  forall (X:Set) (p:X) (lst:list X) le, length (partition_smaller p lst le) <= length lst.
Proof.
  induction lst as [ | h t IH]; simpl; auto; intros le.
  destruct (le p h); simpl.
  apply Nat.le_trans with (length t); auto.
  generalize (IH le); lia.
Qed.

Lemma partition_larger_length :
  forall (X:Set) (p:X) (lst:list X) le, length (partition_larger p lst le) <= length lst.
Proof.
  induction lst as [ | h t IH]; simpl; auto; intros le.
  destruct (le p h); destruct (le h p); simpl.
  apply Nat.le_trans with (length t); auto.
  generalize (IH le); lia.
  apply Nat.le_trans with (length t); auto.
  apply Nat.le_trans with (length t); auto.
Qed.

Lemma partition_equal_length :
  forall (X:Set) (p:X) (lst:list X) le, length (partition_equal p lst le) <= length lst.
Proof.
  induction lst as [ | h t IH]; simpl; auto; intros le.
  destruct (le p h); destruct (le h p); simpl; 
  try (generalize (IH le); lia);
  try (apply Nat.le_trans with (length t); auto).
Qed.


Theorem qsp_lengths_le : forall (X:Set) steps (k:nat) (l:list X) (le:X -> X -> bool) 
  l1 l2 v
  (Hqsp : qsp steps k l le = Some (l1, v, l2)),
  length l1 < length l /\ length l2 < length l.
Proof.
  intros.
  apply qsp_permutation in Hqsp as Hperm.
  apply Permutation_length in Hperm as Hlen.
  rewrite app_length in Hlen; simpl in Hlen.
  lia.
Qed.




Theorem qsp_works :
  forall (X:Set) steps (k:nat) (l:list X) (le:X -> X -> bool),
  k < length l ->
  length l <= steps ->
  exists p, qsp steps k l le = Some p.
Proof.
  induction steps as [ | steps']; intros.
   lia.

  destruct l as [ | h t ].
  inversion H.
  assert (length t <= steps'); try (simpl in *; lia).
  simpl.

  destruct (k_list_lengths _ (partition_smaller h t le) (partition_equal h t le) k)
    as [Hk | [(Hk, Hk1) | (Hk, (Hk1, (Hk2, Hk3)))]]; try rewrite Hk; try rewrite Hk1.

  - destruct (IHsteps' k (partition_smaller h t le) le).
    rewrite Nat.ltb_lt in Hk; auto.
    apply Nat.le_trans with (length t); auto using partition_smaller_length.
    rewrite H2. destruct x as ((a, b), c); eauto.

  - destruct (IHsteps' (k - S (length (partition_smaller h t le) + length (partition_equal h t le)))
                     (partition_larger h t le) le).
    -- rewrite Nat.ltb_lt in Hk1.
       rewrite Nat.ltb_ge in Hk.
       simpl in H.
       generalize (partitions_permutation _ h le t); intros Hperm.
       apply Permutation_length in Hperm.
       repeat rewrite app_length in Hperm.
       lia.

    -- apply Nat.le_trans with (length t); auto using partition_larger_length.
    -- rewrite H2. destruct x as ((a, b), c); eauto.

  - eauto. 
Qed.


Lemma quick_select_always_some :
  forall (X:Set) (k:nat) (l:list X) (le:X -> X -> bool),
  k < length l ->
  exists l1 v l2, quick_select k l le = Some (l1,v,l2).
Proof.
  unfold quick_select; intros.
  edestruct qsp_works; eauto.
  destruct x as ((a, b), c); exists a; exists b; exists c; eauto.
Qed.



(* ***************************************************************************** *)
(* ***************************************************************************** *)
(* ***************************************************************************** *)

Theorem quick_select_correct :
  forall (X:Set) (k:nat) (l:list X) (le:X -> X -> bool),
  le_props le ->
  forall l1 v l2, quick_select k l le = Some (l1,v,l2) ->
    Permutation l (l1 ++ v :: l2) /\
    length l1 = k /\
    (forall x, In x l1 -> le x v = true) /\
    (forall x, In x l2 -> le v x = true).
Proof.
  intros.
  repeat split; auto.
  eapply quick_select_permutation; eauto.
  eapply qsp_position; eauto.
  eapply qsp_all_smaller; eauto.
  eapply qsp_all_larger; eauto.
Qed.


Theorem quick_select_exists_correct :
  forall (X:Set) (k:nat) (l:list X) (le:X -> X -> bool),
  le_props le ->
  k < length l ->
  exists l1 v l2, 
    quick_select k l le = Some (l1,v,l2) /\
    Permutation l (l1 ++ v :: l2) /\
    length l1 = k /\
    (forall x, In x l1 -> le x v = true) /\
    (forall x, In x l2 -> le v x = true).
Proof.
  intros X k l le Hle Hlen.
  generalize (quick_select_always_some X k l le Hlen);
    intros (l1, (v, (l2, Hq))).
  exists l1; exists v; exists l2.

  split; auto.
  apply quick_select_correct; auto.
Qed.

