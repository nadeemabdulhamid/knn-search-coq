(*
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
*)

(*
to compile for meeee it was coqc -R . NN (nameOfFile).v. Needed to be the same as what was in CoqProject
*)

From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Bool.
From Coq Require Import Lists.List.
Require Import Lia.
Require Import Orders.
From Coq Require Import Permutation.

Ltac split_andb_leb
    :=     repeat match goal with 
    | H : _ && _ = true |- _ => apply andb_prop in H; inversion_clear H 
    | |- (_ && _ = true) => apply andb_true_intro; split
    | H : _ && _ = false |- _ => apply andb_false_iff in H
    | H : (_ <=? _ = true) |- _ => apply Nat.leb_le in H
    | H : (_ <=? _ = false) |- _ => apply leb_complete_conv in H
    | |- (_ <=? _ = true) => apply Nat.leb_le
    | |- (_ <=? _ = false) => apply leb_correct_conv
    | H : (_ <? _ = false) |- _ => apply Nat.ltb_ge in H
    | H : (_ <? _ = true) |- _ => apply Nat.ltb_lt in H
    | H : (_ =? _ = false) |- _ => apply Nat.eqb_neq in H
    | H : (_ =? _ = true) |- _ => apply Nat.eqb_eq in H
    | H : _ /\ _ |- _ => inversion_clear H
    end.


#[export] Hint Resolve Permutation_sym Permutation_middle Permutation_app Permutation_app_comm 
            Permutation_app_swap_app Permutation_app_tail Permutation_app_inv_r
                     app_assoc app_nil_end : core.
#[export] Hint Constructors Permutation : core.
#[export] Hint Rewrite <- app_assoc : core.
#[export] Hint Rewrite -> app_assoc Permutation_app_tail : core.

Ltac permtrans x := apply perm_trans with x; auto.
Ltac permtranse x := apply perm_trans with x; eauto.
