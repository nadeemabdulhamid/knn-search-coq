









Require Import FunInd.
Require Import PeanoNat.
Require Import List.
Require Import countTest.


Inductive mynat : Set :=
    | Z : mynat
    | PLUS1 : mynat -> mynat.

Check 
  (nat_ind : forall (P : nat -> Prop)  (* P(n) := "n + 0 = n" *)
                    (prf0 : P 0)       (*       "0 + 0 = 0" *)    
                    (prfS : (forall n : nat, P n -> P (S n))), (* fun n pn => ....*)
                    forall (m : nat), P m).

Fixpoint my_nat_ind (P : nat -> Prop)  
                    (prf0 : P 0)      
                    (prfS : (forall n : nat, P n -> P (S n)))
                    (m : nat) :  P m 
                    := 
    match m with
    | 0 => prf0 
    | S m' =>   prfS m'  (my_nat_ind P prf0 prfS m')
    end.

(*
nat-func :  nat (X) (X nat -> X)  ->  X
(define (nat-func m base comb) 
   (cond [(zero? m)  base]
         [(positive? m) (comb (nat-func (sub1 m)) m)]))    *)





         (*
Lemma zeroSame : forall n, n + 0 = n 
    := nat_ind (fun n => n + 0 = n)  __ __. 
    *)

Lemma zeroSame : forall n, n + 0 = n.
Proof.
   apply (nat_ind (fun n => n + 0 = n)). 
(*   induction n.*)
    Show Proof.

(*  induction n as [ | m IH].   *)

    - apply eq_refl. (* auto. *)
    Show Proof.
    - intros m IH.
    Show Proof.
    simpl. auto.
    Show Proof.
Qed.



(*Fixpoint plus (n m : nat) {struct n} : nat :=
    match n with
    | 0 => m
    | S p => 1 + (plus p m)
    end.
*)

Lemma plus (n m : nat) : nat.
Proof.
    induction n as [ | p pluspm ].
    - exact m.
    - exact (1 + pluspm).
Defined.

(* Transparent plus. *)
Compute (plus 4 5).








Check plus_ind.

Function majority (vals : list nat) : option nat * nat:=
    match vals with 
    | nil => (None, 0)
    | h :: t => match (majority t) with
                | (None, c) => let c' := (1 + count t h) in 
                    if c <? c' then (Some h, c')
                    else (None, c)
                |(Some x, c) => let c' := (1 + count t h) in
                    if c =? c' then (None, c)
                    else if c <? c' then (Some h, c')
                    else (Some x, c)
                    end
            end.

Check majority_ind.








From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Control.


(* this is what we're going to implement *)
Ltac find_contra :=
  lazymatch goal with
  | [ H1: ?E = true, H2: ?E = false |- _ ] =>
    rewrite H1 in H2; inversion H2
  end.

Theorem use_contra_ltac1
        (H: andb true false = true)
        (H': andb true false = false) : False.
Proof.
  ltac1:(find_contra).
Qed.

Ltac2 find_contra () :=
  lazy_match! goal with
    (* First of all, pattern variables must be lower-case. *)
  | [ h1: ?e = true, h2: ?e = false |- _ ] =>
    (* Here the pattern-matching machinery (the lazy_match! macro) has bound
    (h1 h2: ident) and (e: constr). *)

    (* There are three notions that are easily confused here: h1 is an Ltac2
    variable of type ident which holds the name of an identifier in the
    context (it'll be H below), and also there's the constr H which is of type
    andb true false = true in the Gallina type system (but is just a constr in
    the Ltac2 type system) *)

    (* we might be able to use &h1 for this but it doesn't work as an argument
    to the rewrite notation; this gives the constr for the hypothesis from its
    name *)
    let h1 := hyp h1 in
    (* we need to refer to both h2 the variable holding the identifier and the
    hypothesis below, so don't shadow h2 *)
    let h2c := Control.hyp h2 in
    (* Now that we have Ltac2 variables for everything, use them (as opposed
    to literally referring to the hypothesis "h2" or "h2c") *)
    rewrite $h1 in $h2; inversion $h2c
end.

Theorem use_contra
        (H: andb true false = true)
        (H': andb true false = false) : False.
Proof.
  find_contra ().
Qed.






From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Nat.




Parameter T : Set.
Parameter bin_op : T -> T -> T.
Parameter TProp : T -> Prop.





Inductive nattree : Type :=
    | leaf : nat -> nattree
    | branch : nattree -> nattree -> nattree.

Parameter null : T.

Fixpoint nattree_to_bin_op (nt : nattree) (env : list (T*nat)) : T :=
    match nt with
    | leaf n => match (find (fun pair => ((snd pair) =? n)) env) with Some t => (fst t) | None => null end
    | branch nt1 nt2 => bin_op (nattree_to_bin_op nt1 env) (nattree_to_bin_op nt2 env)
    end.





Lemma ex : forall (a b c : T),
    TProp (bin_op c (bin_op a b)) ->
    TProp (bin_op a (bin_op b c)).
Proof.
    intros.

    pose (env := [ (a, 1); (c, 2); (b, 3) ]).

    replace (bin_op a (bin_op b c))
        with (nattree_to_bin_op (branch (leaf 1)
                                    (branch (leaf 3) (leaf 2))) env); [ | reflexivity ].







STOP.



    








    From Coq Require Import Bool.
    Require Import Orders.
    From Coq Require Import Lists.List.
    From Coq Require Import Permutation.
    Require Import Lia.
    Require Import ZifyClasses.
    Require Import tactics.
    Require Import classify.
    Require Import quick_select_partition.
    Import ListNotations.
    Require Import kdtree.
    
    




Check quick_select.

Check [1;2].

Compute (quick_select 3 [15; 90; 32; 7; 86] Nat.leb).
Check build_kdtree.

Compute (build_kdtree 2 [[1;10]; [50;50]; [55;95]; [60;80]; [55;1]; [35;90]; [10;30]; [25;40]; [70;70]; [51;75]]).



Require Import FMaps.
Module Import M := FMapList.Make(Nat_as_OT).

(*
Variable A: Type.
Variables (a b c d e f : list A).
Check add.

Definition m1 : M.t (list A) := (add 0 a (empty (list A))).
Compute (find 0 m1).
Compute (find 1 m1).
*)

Inductive nattree : Type :=
    | leaf : nat -> nattree
    | branch : nattree -> nattree -> nattree.

Fixpoint nattree_to_list {A} (nt : nattree) (env : M.t (list A)) : list A :=
    match nt with
    | leaf n => match (find n env) with Some v => v | None => nil end
    | branch nt1 nt2 => (nattree_to_list nt1 env) ++ (nattree_to_list nt2 env)
    end.

Fixpoint nattree_isomorphic (nt1 nt2 : nattree) : bool :=
    true.

Lemma nt_iso_perm : forall A nt1 nt2 env, 
    nattree_isomorphic nt1 nt2 = true ->
    Permutation (@nattree_to_list A nt1 env) (nattree_to_list nt2 env).
Admitted.

Lemma ex : forall A (a:list A) b c d e f,
    Permutation (a ++ b) c ->
    Permutation (d ++ e) f ->
    Permutation (a ++ d ++ e ++ b) (f ++ c).
Proof.
    intros.
    pose (env := add 6 f (add 5 e (add 2 b (add 3 c( add 4 d (add 1 a (empty _))))))).

    replace (f ++ c) with (nattree_to_list (branch (leaf 6) (leaf 3)) env); auto.
    replace (a ++ d ++ e ++ b) with 
        (nattree_to_list (branch (leaf 1) (branch (leaf 4) (branch (leaf 5) (leaf 2)))) env); auto.
    apply nt_iso_perm; auto.

    (*
    permtrans (c ++ f).
    permtrans ((a ++ b) ++ f).
    rewrite <- (app_assoc).
    apply Permutation_app_head.
    permtrans (b ++ d ++ e).
    permtrans (d ++ b ++ e).
    *)
Qed.




(* 
https://twitter.com/pi8027/status/1385065690114138112
https://github.com/math-comp/mczify/blob/master/theories/zify_algebra.v
https://coq.inria.fr/library/Coq.micromega.ZifyClasses.html#InjTyp
https://coq.inria.fr/library/Coq.micromega.ZifyInst.html


*)
Module Test (Import Ord :  OrderedTypeFull').

Show Zify InjTyp.

Instance Inj_t_Z : InjTyp t Z :=
    { inj := Z_of_int; pred _ := True; cstr _ := I }.
      
    inj : S -> T;
    pred : T -> Prop;
    
    cstr : forall x, pred (inj x)


Add Zify InjTyp t.

Lemma trans :
    (forall (a b c : t), le a b -> le b c -> le a c).
    lia.








Lemma odd_div2_plus_1 : forall m n,
n < m ->
Nat.Odd n ->
n = 1 + div2 n + div2 n.
Proof.
induction m.
- intros. lia.
- intros.
    destruct n as [ | n'].
    inversion H0; lia.
    destruct n' as [ | n']; auto.
    rewrite Nat.Odd_succ_succ in H0 .
    assert ((S n') = div2 (S (S n')) + div2 (S (S n'))); [ | apply eq_S]; auto.
    replace (div2 (S (S n'))) with (1 + div2 n'); auto.
    assert (n' = div2 n' + (1 + div2 n')); [ | apply eq_S]; auto.
    rewrite IHm at 1; try lia; auto.
Qed.
