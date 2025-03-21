From Perennial.goose_lang Require Import prelude. 
From iris.algebra Require Import ofe auth excl gmap.
 From Perennial.goose_lang Require Import notation typing.
 From Perennial.goose_lang Require Import proofmode wpc_proofmode.
 From Perennial.goose_lang.lib Require Import typed_mem.
 From Perennial.program_proof Require Import std_proof. 
 From Perennial.algebra Require Import ghost_var.

Context `{hG: heapGS Σ, !ext_types _, !inG Σ (authR (optionUR (prodR fracR natR)))}.
Implicit Types (v:val).


Definition own_chan_counter_frag (γ : gname) (n : nat) (q : Qp) : iProp Σ :=
 own γ (◯ Some (q, n)).

Definition own_chan_counter_auth (γ : gname) (m : nat) : iProp Σ :=
 own γ (● Some (1%Qp, m)).

Lemma alloc_initial_chan_counter :
⊢ |==> ∃ γ, own_chan_counter_auth γ 0 ∗ own_chan_counter_frag γ 0 1%Qp .
Proof.
setoid_rewrite <-own_op.
iApply own_alloc.
apply auth_both_valid_discrete.
split.
- reflexivity.
- apply Some_valid.
  apply pair_valid.
  split.
  + apply frac_valid.
    reflexivity.
  + cbv.
    done.
Qed. 

Lemma chan_counter_split_merge (γ : gname) (n m : nat) (p q : Qp) :
   own_chan_counter_frag γ (n + m) (p + q) ⊣⊢ own_chan_counter_frag γ n p ∗ own_chan_counter_frag γ m q.
Proof.
setoid_rewrite <-own_op.
done.
Qed.

Lemma chan_counter_lower_frag_bound γ (m n : nat) (q : Qp) :
  own_chan_counter_auth γ m -∗
  own_chan_counter_frag γ n q -∗ 
  ⌜n ≤ m⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_pair_included in H.
  destruct H as [_ H].
  rewrite Some_included_total in H.
  apply nat_included in H.
  done.
Qed.

Lemma chan_counter_full_ownership γ (n m : nat) :
  own_chan_counter_auth γ m -∗
  own_chan_counter_frag γ n 1%Qp -∗ 
  ⌜m = n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_included_exclusive in H.
  - destruct H as [_ H]; cbn in H.
    apply leibniz_equiv in H.
    done.
  - apply _.
  - done.
Qed.

Lemma chan_counter_inc γ n m (q : Qp) :
  own_chan_counter_auth γ n ∗ own_chan_counter_frag γ m q ==∗
  own_chan_counter_auth γ (S n) ∗ own_chan_counter_frag γ (S m) q.
Proof.
  iIntros "H".
  rewrite -!own_op.
  iApply (own_update with "H").
  apply auth_update.
  apply option_local_update.
  apply prod_local_update_2.
  apply (op_local_update_discrete _ _ 1).
  done.
Qed.
