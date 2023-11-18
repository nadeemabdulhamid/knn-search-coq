
From Coq Require Import Bool.
Require Import Orders.
From Coq Require Import Lists.List.
From Coq Require Import Permutation.

Ltac split_andb
    :=     repeat match goal with 
    | H : _ && _ = true |- _ => apply andb_prop in H; inversion_clear H 
    | |- (_ && _ = true) => apply andb_true_intro; split
(*    | H : (_ <=? _ = true) |- _ => apply Nat.leb_le in H
    | H : (_ <=? _ = false) |- _ => apply leb_complete_conv in H
    | |- (_ <=? _ = true) => apply Nat.leb_le
    | |- (_ <=? _ = false) => apply leb_correct_conv
    | H : (_ <? _ = false) |- _ => apply Nat.ltb_ge in H
    | H : (_ <? _ = true) |- _ => apply Nat.ltb_lt in H*)
    end.



Check Forall.

(* the ' means has Notation *)

Module Type MinPQ (Import Ord : TotalTransitiveLeBool').
  Parameter priqueue: forall A:Type, (A -> t) -> Type.

  Parameter empty: forall A key, priqueue A key.
  Parameter insert: forall A key, A -> priqueue A key -> priqueue A key.
  Parameter delete_min: forall A key, priqueue A key -> option (A * priqueue A key).
  Parameter size: forall A key, priqueue A key -> nat.

  Parameter priq: forall A key, priqueue A key -> Prop.
  Parameter Abs: forall A key, priqueue A key -> list A -> Prop.

  Axiom can_relate: forall A key p, priq A key p -> exists al, Abs A key p al.
  Axiom abs_perm: forall A key p al bl, 
   priq A key p -> Abs A key p al -> Abs A key p bl -> Permutation al bl.

  Axiom empty_priq: forall A key, priq A key (empty A key).
  Axiom empty_relate: forall A key, Abs A key (empty A key) nil.

  Axiom insert_priq: forall A key k p, priq A key p -> priq A key (insert A key k p).
  Axiom insert_relate:
        forall A key p al k, priq A key p -> Abs A key p al -> Abs A key (insert A key k p) (k::al).

  Axiom delete_min_None_relate:
        forall A key p, priq A key p -> (Abs A key p nil <-> delete_min A key p = None).
  Axiom delete_min_Some_priq:
      forall A key p q k, priq A key p -> delete_min A key p = Some(k,q) -> priq A key q.
  Axiom delete_min_Some_relate:
  forall A key (p q: priqueue A key) (k:A) (pl ql: list A), priq A key p ->
   Abs A key p pl ->
   delete_min A key p = Some (k,q) ->
   Abs A key q ql ->
   Permutation pl (k::ql) /\ @forallb A (fun (a : A) => (leb (key k) (key a))) ql = true.
   Axiom delete_min_ex_Some_relate:
   forall A key (p q: priqueue A key) (k:A) (pl: list A), priq A key p ->
    Abs A key p pl ->
    delete_min A key p = Some (k,q) ->
    exists ql, 
        Abs A key q ql /\
        Permutation pl (k::ql) /\ 
        @forallb A (fun (a : A) => (leb (key k) (key a))) ql = true.
 
   (* Derived *)
   Axiom delete_min_empty_None :
    forall A key, delete_min A key (empty A key) = None.

   Axiom size_relate: forall A key p al, priq A key p -> Abs A key p al -> size A key p = length al.

End MinPQ.




Module List_MinPQ (Import Ord : TotalTransitiveLeBool') <: MinPQ Ord.

Fixpoint select {elt:Type} (key:elt -> t) (i: elt) (l: list elt) : elt * list elt :=
match l with
|  nil => (i, nil)
|  h::t => if key i <=? key h 
               then let (j, l') := select key i t in (j, h::l')
               else let (j,l') := select key h t in (j, i::l')
end.

Lemma select_perm: forall elt (key:elt->t) i l, 
  let (j,r) := select key i l in
   Permutation (i::l) (j::r).
Proof.
intros elt key i l; revert i.
induction l; intros; simpl in *.

apply Permutation_refl.
destruct (key i <=? key a).
specialize (IHl i).
destruct (select key i l).
eapply perm_trans.
apply perm_swap.
apply Permutation_sym.
eapply perm_trans.
apply perm_swap.
apply Permutation_cons; auto.
apply Permutation_sym.
apply IHl.
specialize (IHl a).
destruct (select key a l).
apply Permutation_sym.
eapply perm_trans.
apply perm_swap.
apply Permutation_cons; auto.
apply Permutation_sym.
apply IHl.
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
    split_andb; auto.

    simpl in *.
    split_andb; auto.
Qed.

Lemma select_smallest_aux:
  forall elt key i al (j:elt) bl,
    forallb (fun x => key j <=? key x) bl = true ->
    select key i al = (j,bl) ->
    key j <=? key i = true.
Proof. 
intros.
assert (H1 := select_perm elt key i al). rewrite H0 in H1.
apply Permutation_sym in H1.
assert (forallb (fun x => key j <=? key x) (j::bl) = true).
simpl. apply andb_true_intro; split; auto; apply leb_refl; auto.
eapply forallb_perm in H1; eauto.
simpl in *; split_andb; auto.
Qed.


Theorem select_smallest:
  forall elt (key:elt -> t) i al j bl, select key i al = (j,bl) ->
     forallb (fun x => key j <=? key x) bl = true.
Proof.
intros elt key i al; revert i; induction al; intros; simpl in *.
injection H as H1 H2; rewrite <- H2; simpl; auto.
destruct (key i <=? key a) eqn:Heq.
*
destruct (select key i al) eqn:H0.
injection H as H1 H2; rewrite <- H2; simpl; split_andb; rewrite H1 in *; auto.
eapply select_smallest_aux in H0; eauto.
apply (@leb_trans (key j) (key i) (key a) H0 Heq).
eapply IHal; eauto.
*
destruct (select key a al) eqn:?H0.
injection H as H1 H2; rewrite <- H2 in *; rewrite <- H1 in *; simpl; auto.
specialize (IHal _ _ _ H0).
split_andb; auto.
pose proof (select_smallest_aux _ _ _ _ _ _ IHal H0).
apply (@leb_trans (key e) (key a) (key i) H).
unfold is_true.
destruct (leb_total (key a) (key i)); auto.
rewrite H3 in Heq; discriminate.
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

Definition delete_min elt key (p: priqueue elt key) :=
    match p with
    | i::p' => Some (select key i p')
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

Lemma empty_relate:  forall elt key, Abs elt key (empty elt key) nil.
Proof. constructor. Qed.

Lemma insert_priq: forall elt key k p, priq elt key p -> priq elt key (insert elt key k p).
Proof. intros; constructor. Qed.

Lemma insert_relate:
    forall elt key p al k, priq elt key p -> Abs elt key p al -> Abs elt key (insert elt key k p) (k::al).
Proof. intros. unfold insert. inversion H0. constructor. Qed.

Lemma delete_min_Some_priq:
      forall elt key p q k, priq elt key p -> delete_min elt key p = Some(k,q) -> priq elt key q.
Proof. constructor. Qed.

Lemma delete_min_None_relate:
  forall elt key p, priq elt key p -> 
      (Abs elt key p nil <-> delete_min elt key p = None).
Proof.
 intros; split; intro.
 inversion H0. auto.
 unfold delete_min in H0.
 destruct p; inversion H0; constructor.
Qed.



Lemma delete_min_Some_relate:
  forall elt key (p q: priqueue elt key) k (pl ql: list elt), priq elt key p ->
   Abs elt key p pl ->
   delete_min elt key p = Some (k,q) ->
   Abs elt key q ql ->
   Permutation pl (k::ql) /\ @forallb elt (fun (a : elt) => (leb (key k) (key a))) ql = true.
Proof.
    intros.
    inversion H0; inversion H2.
    rewrite H4 in *.
    destruct pl; simpl in H1; try discriminate.
    pose proof (select_perm elt key e pl).
    injection H1 as H1; rewrite H1 in H7.
    split; rewrite <- H6; auto.
    apply select_smallest in H1; auto.
Qed.

Lemma delete_min_ex_Some_relate:
    forall A key (p q: priqueue A key) (k:A) (pl: list A), priq A key p ->
    Abs A key p pl ->
    delete_min A key p = Some (k,q) ->
    exists ql, 
        Abs A key q ql /\
        Permutation pl (k::ql) /\ 
        @forallb A (fun (a : A) => (leb (key k) (key a))) ql = true.
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
    eapply select_smallest; eauto.
Qed.


Lemma size_relate: forall A key p al, priq A key p -> Abs A key p al -> size A key p = length al.
Proof.
    intros; inversion H0; auto.
Qed.

(* Derived *)

Lemma delete_min_empty_None :
    forall A key, delete_min A key (empty A key) = None.
Proof.
intros.
pose proof (delete_min_None_relate A key _ (empty_priq _ _)) as (H1, H2).
apply H1. apply empty_relate.
Qed.



End List_MinPQ.

