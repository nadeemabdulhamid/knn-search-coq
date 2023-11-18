
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapInterface.
Require Import OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
(*
Require Import Orders.
Require Import SetoidList.  
*)
Require Import List.
Require Import Lia.
Require Import PeanoNat.


Module ListOrderedType <: UsualOrderedType. 

Definition t := list nat. 

Definition eq := @eq (list nat).

(* should be lexicographic ordering *)
Inductive ltA : t -> t -> Prop :=
  | ltlist_nil : forall x' l', ltA nil (x'::l')
  | ltlist_head : forall x x' l l', x < x' -> ltA (x::l) (x'::l')
  | ltlist_tail : forall x x' l l', x = x' -> ltA l l' -> ltA (x::l) (x'::l').

Definition lt := ltA.

Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
intros x; induction x;
intros y z H1 H2; inversion  H1.
-   rewrite <- H0 in H2; inversion H2; constructor.
-   rewrite <- H0 in H2.
    inversion H2.
    constructor; lia.
    constructor; try lia; auto.
-   clear H0 H l x0.
    rewrite <- H4 in H2, H1; inversion H2.
    --
    clear H x0 l H6.
    rewrite <- H0 in H2; clear z H0.
    rewrite H3 in *; clear a H3.
    constructor; auto.
    --
    clear x0 H l H0.
    rewrite <- H7 in *; clear z H7; rewrite <- H6 in *; clear x'0 H6 y H4.
    apply ltlist_tail; auto.
    apply IHx with l'; auto.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
    intros x y Hlt; induction Hlt; intro.
    inversion H.
    inversion H0.
    lia.
    inversion H0.
    apply IHHlt; auto.
Qed.


Fixpoint cmp (x y : t) : comparison :=
    match (x, y) with 
    | (nil, nil) => Eq
    | (nil, _)   => Lt
    | (_, nil)   => Gt
    | (a :: x', b :: y') => match Nat.compare a b with
                                    | Eq => cmp x' y'
                                    | e => e
    end 
    end.


    Lemma compare_Eq_eq : forall x y, cmp x y = Eq -> eq x y.
    Proof.
            induction x; intros.
            destruct y eqn:Hy.
            -
            reflexivity.
            -
            inversion H.
            -
            simpl in H.
            destruct y eqn:Hy.
            inversion H.
            destruct (Nat.compare a n) eqn:Hc; try inversion H.
            apply Compare_dec.nat_compare_eq in Hc.
            rewrite Hc; replace t0 with x; try reflexivity.
            apply IHx; auto.
    Qed.
        
    Lemma compare_Lt_lt : forall x y, cmp x y = Lt -> lt x y.
    Proof.
        induction x; intros.
        -
            destruct y eqn:Hy.
            -- inversion H.
            -- constructor.
        -
            inversion H.
            destruct y eqn:Hy.
            --
            inversion H1.
            --
            destruct (a ?= n) eqn:Hc; try inversion H1.
            apply ltlist_tail; auto.
            apply Compare_dec.nat_compare_eq in Hc; auto.
            apply IHx; auto.
            apply ltlist_head; apply Compare_dec.nat_compare_lt; auto.
    Qed.
        
    Lemma compare_Gt_gt : forall x y, cmp x y = Gt -> lt y x.
    Proof.
        induction x; intros.
        -
            destruct y eqn:Hy; inversion H.
        -
            inversion H.
            destruct y eqn:Hy.
            constructor; auto.
            destruct (a ?= n) eqn:Hc; try inversion H1.
            apply ltlist_tail; auto.
            apply Compare_dec.nat_compare_eq in Hc; auto.
            apply IHx; auto.
            apply ltlist_head. apply Compare_dec.nat_compare_gt; auto.
    Qed.
    
Definition compare (x y : t) : Compare lt eq x y :=
    match cmp x y as z return _ = z -> _ with  
    | Lt => fun E => LT (compare_Lt_lt x y E)
    | Gt => fun E => GT (compare_Gt_gt x y E)
    | Eq => fun E => EQ (compare_Eq_eq x y E)
    end Logic.eq_refl.

Definition eq_dec (x y : t) : { eq x y } + { ~ eq x y }.
Proof.
    generalize dependent y.
    induction x.
    -
    destruct y.
    left; reflexivity.
    right; intro H; inversion H.
    -
    destruct y.
    right; intro H; inversion H.
    compare a n; intros Hc.
    rewrite Hc.
    destruct (IHx y).
    rewrite e; left; reflexivity.
    right; intro.
    inversion H; auto.

    right; intro.
    inversion H; auto.
Defined.

End ListOrderedType.


