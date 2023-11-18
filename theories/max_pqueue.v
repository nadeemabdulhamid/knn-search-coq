
From Coq Require Import Bool.
Require Import Orders.
From Coq Require Import Lists.List.
From Coq Require Import Permutation.
From NN Require Import tactics.

(* the ' means has Notation *)

Module Type MaxPQ (Import Ord : TotalTransitiveLeBool').
  Parameter priqueue: forall A:Type, (A -> t) -> Type.

  Parameter empty: forall A key, priqueue A key.
  Parameter insert: forall A key, A -> priqueue A key -> priqueue A key.
  Parameter delete_max: forall A key, priqueue A key -> option (A * priqueue A key).
  Parameter peek_max: forall A key, priqueue A key -> option A.
  Parameter size: forall A key, priqueue A key -> nat.

  Parameter priq: forall A key, priqueue A key -> Prop.
  Parameter Abs: forall A key, priqueue A key -> list A -> Prop.

  Axiom can_relate: forall A key p, priq A key p -> exists al, Abs A key p al.
  Axiom abs_perm: forall A key p al bl, 
   priq A key p -> Abs A key p al -> Abs A key p bl -> Permutation al bl.

  Axiom empty_priq: forall A key, priq A key (empty A key).
  Axiom empty_relate: forall A key pq, Abs A key pq nil <-> pq = (empty A key).

  Axiom insert_priq: forall A key k p, priq A key p -> priq A key (insert A key k p).
  Axiom insert_relate:
        forall A key p al k, priq A key p -> Abs A key p al -> Abs A key (insert A key k p) (k::al).

  Axiom delete_max_None_relate:
        forall A key p, priq A key p -> (Abs A key p nil <-> delete_max A key p = None).
  Axiom delete_max_Some_priq:
      forall A key p q k, priq A key p -> delete_max A key p = Some(k,q) -> priq A key q.
  Axiom delete_max_Some_relate:
        forall A key (p q: priqueue A key) (k:A) (pl ql: list A), priq A key p ->
        Abs A key p pl ->
        delete_max A key p = Some (k,q) ->
        Abs A key q ql ->
        Permutation pl (k::ql) /\ @forallb A (fun (a : A) => (leb (key a) (key k))) ql = true.
   Axiom delete_max_ex_Some_relate:
    forall A key (p q: priqueue A key) (k:A) (pl: list A), priq A key p ->
        Abs A key p pl ->
        delete_max A key p = Some (k,q) ->
        exists ql, 
            Abs A key q ql /\
            Permutation pl (k::ql) /\ 
            @forallb A (fun (a : A) => (leb (key a) (key k))) ql = true.
   Axiom delete_max_Some_size :
    forall A key n (p q: priqueue A key) (k:A) (pl ql: list A), priq A key p ->
        Abs A key p pl ->
        size A key p = S n ->
        delete_max A key p = Some (k,q) ->
        size A key q = n.
 
    Axiom delete_max_relate_cons_Some :
        forall A key p a al,
        priq A key p ->
        Abs A key p (a :: al) ->
        exists k, exists q, delete_max A key p = Some (k, q).

    Axiom delete_insert_relate_perm :
        forall A key p pl e k q ql, 
            priq A key p -> 
            Abs A key p pl -> 
            Abs A key q ql ->
            delete_max A key (insert A key e p) = Some (k, q) ->
            (e = k /\ Permutation pl ql) 
                \/ exists pl' ql', Permutation pl (k :: pl') /\ Permutation ql (e :: ql') /\ Permutation pl' ql'.
    

   Axiom peek_max_None_relate:
        forall A key p, priq A key p -> (Abs A key p nil <-> peek_max A key p = None).
   Axiom peek_max_Some_relate:
        forall A key (p: priqueue A key) (k:A) (pl: list A), 
        priq A key p ->
        Abs A key p pl ->
        peek_max A key p = Some k  ->
        In k pl /\ @forallb A (fun (a : A) => (leb (key a) (key k))) pl = true.

   Axiom size_relate: forall A key p al, priq A key p -> Abs A key p al -> size A key p = length al.
   Axiom size_zero_relate : forall A key p, (size A key p = 0) <-> (Abs A key p nil).

   Axiom delete_max_empty_None :
    forall A key pq, delete_max A key pq = None <-> pq = (empty A key).


    (* derived *)
   Axiom insert_size:
    forall A key p al e, priq A key p -> Abs A key p al -> 
    size A key (insert A key e p) = 1 + size A key p.


End MaxPQ.




Module List_MaxPQ (Import Ord : TotalTransitiveLeBool') <: MaxPQ Ord.

Fixpoint select {elt:Type} (key:elt -> t) (i: elt) (l: list elt) : elt * list elt :=
match l with
|  nil => (i, nil)
|  h::t => if key h <=? key i
               then let (j, l') := select key i t in (j, h::l')
               else let (j,l') := select key h t in (j, i::l')
end.

Lemma select_perm: forall elt (key:elt->t) i l, 
  let (j,r) := select key i l in
   Permutation (i::l) (j::r).
Proof.
intros elt key i l; revert i.
induction l; intros; simpl in *; auto.

destruct (key a <=? key i).
specialize (IHl i).
destruct (select key i l).
permtrans (a :: i :: l).
permtrans (a :: e :: l0).

specialize (IHl a).
destruct (select key a l).
permtrans (i :: e :: l0).
Qed.

Lemma leb_refl : forall x, x <=? x = true.
Proof.
    intros x; destruct (leb_total x x); auto.
Qed.

Theorem forallb_perm :
    forall T P (l r : list T), Permutation l r -> forallb P l = true -> forallb P r = true.
Proof.
    intros T P l r Hperm.
    induction Hperm; intros; auto.
    simpl in *.
    split_andb_leb; auto.

    simpl in *.
    split_andb_leb; auto.
Qed.

Lemma select_largest_aux:
  forall elt key i al (j:elt) bl,
    forallb (fun x => key x <=? key j) bl = true ->
    select key i al = (j,bl) ->
    key i <=? key j = true.
Proof. 
intros.
assert (H1 := select_perm elt key i al). rewrite H0 in H1.
apply Permutation_sym in H1.
assert (forallb (fun x => key x <=? key j) (j::bl) = true).
simpl. apply andb_true_intro; split; auto; apply leb_refl; auto.
eapply forallb_perm in H1; eauto.
simpl in *; split_andb_leb; auto.
Qed.


Theorem select_largest:
  forall elt (key:elt -> t) i al j bl, select key i al = (j,bl) ->
     forallb (fun x => key x <=? key j) bl = true.
Proof.
intros elt key i al; revert i; induction al; intros; simpl in *.
injection H as H1 H2; rewrite <- H2; simpl; auto.
destruct (key a <=? key i) eqn:Heq.
*
destruct (select key i al) eqn:H0.
injection H as H1 H2; rewrite <- H2; simpl; split_andb_leb; rewrite H1 in *; auto.
eapply select_largest_aux in H0; eauto.
apply (@leb_trans (key a) (key i) (key j) Heq H0).
eapply IHal; eauto.
*
destruct (select key a al) eqn:?H0.
injection H as H1 H2; rewrite <- H2 in *; rewrite <- H1 in *; simpl; auto.
specialize (IHal _ _ _ H0).
split_andb_leb; auto.
pose proof (select_largest_aux _ _ _ _ _ _ IHal H0).
destruct (leb_total (key a) (key i)) as [ Ht | Ht ]; auto.
rewrite Ht in Heq; discriminate.
apply (@leb_trans (key i) (key a) (key e) Ht); auto.
Qed.

(*
Look up:
pose proof
    revert
    specialize
*)

(** ** The Program *)

Definition priqueue A (key : A -> t) := list A.

Definition empty elt key : priqueue elt key := nil.

Definition insert elt key (k: elt)(p: priqueue elt key) := k::p.

Definition delete_max elt key (p: priqueue elt key) :=
    match p with
    | i::p' => Some (select key i p')
    | nil => None
    end.

Definition peek_max elt key (p: priqueue elt key) :=
    match p with
    | i::p' => Some (fst (select key i p'))
    | nil => None
    end.

Definition size elt key (p: priqueue elt key) := length p.

Definition priq elt key (p: priqueue elt key) := True.

Inductive Abs' elt key : priqueue elt key -> list elt -> Prop :=
Abs_intro : forall p, Abs' elt key p p.

Definition Abs := Abs'.

Lemma can_relate :
    forall elt key (p : (priqueue elt key)), priq elt key p -> exists al : list elt, Abs elt key p al.
Proof.
    intros. exists p; constructor.
Qed.

Lemma abs_perm :
    forall elt key (p : priqueue elt key) (al bl : list elt),
        priq elt key p -> Abs elt key p al -> Abs elt key p bl -> Permutation al bl.
Proof.
    intros.
    inversion H0; inversion H1. rewrite <- H3; rewrite <- H5; apply Permutation_refl.
Qed.

Lemma empty_priq: forall elt key, priq elt key (empty elt key ) .
Proof. constructor. Qed.

Lemma empty_relate:  forall A key pq, Abs A key pq nil <-> pq = (empty A key).
Proof. split; intros H; try rewrite H. inversion H; auto. constructor; auto. Qed.

Lemma insert_priq: forall elt key k p, priq elt key p -> priq elt key (insert elt key k p).
Proof. intros; constructor. Qed.

Lemma insert_relate:
    forall elt key p al k, priq elt key p -> Abs elt key p al -> Abs elt key (insert elt key k p) (k::al).
Proof. intros. unfold insert. inversion H0. constructor. Qed.

Lemma delete_max_Some_priq:
      forall elt key p q k, priq elt key p -> delete_max elt key p = Some(k,q) -> priq elt key q.
Proof. constructor. Qed.

Lemma delete_max_None_relate:
  forall elt key p, priq elt key p -> 
      (Abs elt key p nil <-> delete_max elt key p = None).
Proof.
 intros; split; intro.
 inversion H0. auto.
 unfold delete_max in H0.
 destruct p; inversion H0; constructor.
Qed.



Lemma delete_max_Some_relate:
  forall elt key (p q: priqueue elt key) k (pl ql: list elt), priq elt key p ->
   Abs elt key p pl ->
   delete_max elt key p = Some (k,q) ->
   Abs elt key q ql ->
   Permutation pl (k::ql) /\ @forallb elt (fun (a : elt) => (key a) <=? (key k)) ql = true.
Proof.
    intros.
    inversion H0; inversion H2.
    rewrite H4 in *.
    destruct pl; simpl in H1; try discriminate.
    pose proof (select_perm elt key e pl).
    injection H1 as H1; rewrite H1 in H7.
    split; rewrite <- H6; auto.
    apply select_largest in H1; auto.
Qed.

Lemma delete_max_ex_Some_relate:
    forall A key (p q: priqueue A key) (k:A) (pl: list A), priq A key p ->
    Abs A key p pl ->
    delete_max A key p = Some (k,q) ->
    exists ql, 
        Abs A key q ql /\
        Permutation pl (k::ql) /\ 
        @forallb A (fun (a : A) => (key a) <=? (key k)) ql = true.
Proof.
    intros.
    inversion H0.
    rewrite H3 in *; clear p p0 H2 H3.
    generalize H H0 H1; clear H H0 H1.
    induction pl as [ | h t]; simpl; intros; try discriminate.
    injection H1 as H1.
    pose proof (select_perm _ key h t).
    rewrite H1 in H2.
    exists q; repeat split; auto.
    eapply select_largest; eauto.
Qed.

Lemma delete_max_Some_size :
    forall A key n (p q: priqueue A key) (k:A) (pl ql: list A), priq A key p ->
        Abs A key p pl ->
        size A key p = S n ->
        delete_max A key p = Some (k,q) ->
        size A key q = n.
Proof.
    intros.
    destruct p as [ | h t]; try discriminate.
    simpl in *.
    injection H1 as H1.
    injection H2 as H2.
    pose proof (select_perm A key h t) as H3; rewrite H2 in H3.
    unfold size in *.
    apply Permutation_length in H3 as H3p.
    simpl in H3p; injection H3p as H3p.
    rewrite <- H3p; auto.
Qed.



Lemma delete_max_relate_cons_Some :
    forall A key p a al,
    priq A key p ->
    Abs A key p (a :: al) ->
    exists k, exists q, delete_max A key p = Some (k, q).
Proof.
    intros.
    destruct p as [ | h t]; try discriminate; simpl in *.
    inversion H0.
    exists (fst (select key h t)).
    exists (snd (select key h t)).
    destruct (select key h t); auto.
Qed.

Lemma delete_insert_relate_perm :
forall A key p pl e k q ql, 
    priq A key p -> 
    Abs A key p pl -> 
    Abs A key q ql ->
    delete_max A key (insert A key e p) = Some (k, q) ->
            (e = k /\ Permutation pl ql) 
                \/ exists pl' ql', Permutation pl (k :: pl') /\ Permutation ql (e :: ql')
                        /\ Permutation pl' ql'.
Proof.
    intros.
    injection H2.
    generalize  e k q ql pl H0 H1; clear e k q ql pl H H0 H1 H2.
    induction p as [ | h t]; simpl in *; intros.
    {
        inversion H.
        left; split; auto.
        inversion H0; replace q with (@nil A) in H1; inversion H1; auto.
    }
    {
        inversion H0; inversion H1; clear H0 H1 p H2 p0 H4.
        destruct (key h <=? key e) eqn:Heq.
        {
            destruct (select key e t) as (k', q') eqn:Hsel.
            pose proof (IHt e k' q' q' t (Abs_intro _ _ _) (Abs_intro _ _ _) Hsel).
            replace ql with (h :: q') in *.
            2: { injection H; intros; replace ql with q; auto. }
            replace k' with k in *. clear k' H.
            2: { injection H; auto. }
            inversion_clear H0.
            inversion_clear H.
            left; split; auto.
            destruct H as (pl', (ql', (Hp1, (Hp2, Hp3)))).
            right.
            exists (h :: pl'). exists (h :: ql'); repeat split; auto.
            apply Permutation_trans with (h :: k :: pl'); auto using perm_swap.
            apply Permutation_trans with (h :: e :: ql'); auto using perm_swap.
        }
        {
            destruct (select key h t) as (k', q') eqn:Hsel.
            pose proof (IHt h k' q' q' t (Abs_intro _ _ _) (Abs_intro _ _ _) Hsel).
            replace ql with (e :: q') in *.
            2: { injection H; intros; replace ql with q; auto. }
            replace k' with k in *. clear k' H.
            2: { injection H; auto. }
            inversion_clear H0.
            inversion_clear H. replace k with h in *; auto.
            right; exists t; exists q'; split; auto.
            destruct H as (pl', (ql', (Hp1, (Hp2, Hp3)))).
            right.
            exists (h :: pl'); exists q'; repeat split; auto.
            apply Permutation_trans with (h :: k :: pl'); auto using perm_swap.
            apply Permutation_trans with (h :: ql'); auto using Permutation_sym.
        }
    }
Qed.


Lemma size_relate: forall A key p al, priq A key p -> Abs A key p al -> size A key p = length al.
Proof.
    intros; inversion H0; auto.
Qed.

Lemma size_zero_relate : forall A key p, (size A key p = 0) <-> (Abs A key p nil).
Proof.
    split; intros Hp.
    unfold size in Hp. 
    apply length_zero_iff_nil in Hp; rewrite Hp; constructor.
    inversion Hp; auto.
Qed.

Lemma peek_max_None_relate:
    forall A key p, priq A key p -> (Abs A key p nil <-> peek_max A key p = None).
Proof.
    intros; split; intro.
    inversion H0; auto.
    unfold peek_max in H0.
    destruct p; inversion H0; constructor.
Qed.
   

Lemma peek_max_Some_relate:
    forall A key (p: priqueue A key) (k:A) (pl: list A), 
        priq A key p ->
        Abs A key p pl ->
        peek_max A key p = Some k  ->
        In k pl /\ @forallb A (fun (a : A) => (leb (key a) (key k))) pl = true.
Proof.
    intros.
    inversion H0.
    rewrite H3 in *; clear p0 H2 H3.
    destruct pl; simpl in H1; try discriminate.
    destruct (select key a pl) as (e, ql) eqn:Hsel; injection H1 as H1.
    pose proof (select_perm A key a pl) as Hperm; rewrite Hsel in Hperm.
    rewrite H1 in *; clear e H1.
    split; auto.
    apply Permutation_sym in Hperm; apply Permutation_in with (k :: ql); auto using in_eq.
    apply forallb_perm with (k :: ql); try apply Permutation_sym; auto.
    apply select_largest in Hsel as Hsl; auto.
    apply select_largest_aux in Hsel as Hsla; auto.
    simpl; split_andb_leb; auto.
    destruct (leb_total (key k) (key k)); auto.
Qed.



Lemma delete_max_empty_None :
    forall A key pq, delete_max A key pq = None <-> pq = (empty A key).
Proof.
    split; intros.
    destruct pq; auto; discriminate.
    rewrite H; auto.
Qed.


Lemma insert_size:
forall A key p al e, priq A key p -> Abs A key p al -> 
size A key (insert A key e p) = 1 + size A key p.
Proof.
    intros A key p al e Hpriq Habs.
    eapply insert_relate with (k:=e) in Habs as Habs'; eauto.
(*    rewrite size_relate with (al:=e::al); auto.
    rewrite size_relate with (al:=al); auto.
    apply insert_priq; auto. *)
Qed.


End List_MaxPQ.

