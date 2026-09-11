Require Import New.proof.proof_prelude.
From New.golang.theory.chan.idioms Require Import base.
From New.golang.theory.chan.idioms Require Export contrib.
From New.golang.theory Require Import chan.
From iris.algebra Require Import gmultiset big_op.
From iris.algebra Require Export csum.
From stdpp Require Export sets gmultiset countable.

(** * Multiple Producer Multiple Consumer (MPMC) Channel Verification

    Key insight: Each producer/consumer tracks their OWN history using multisets.

    - Producer i has sent: sent_i (a multiset)
    - Consumer j has received: recv_j (a multiset)
    - Invariant: ⊎ sent_i = ⊎ recv_j ⊎ inflight

    Uses contribution theory with gmultisetR V.
    Requires Countable V because gmultiset V = gmap V positive.
*)

#[local] Transparent is_chan own_chan.

Section mpmc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Context `[!EqDecision V] `[!Countable V].
Context `{!contributionG Σ (gmultisetR V)}.
Collection W := sem + IntoValTyped0.

Record mpmc_names := {
  mpmc_chan_name : chan_names;
  mpmc_sent_name : gname;
  mpmc_recv_name : gname;
  mpmc_closed_name : gname
}.

Lemma delete_client γ n (X Y Z: gmultiset V) :
  n > 0 ->
  Z ⊆ Y →
  server γ n X -∗ client γ Y ==∗ server γ n (X ∖ Z) ∗ client γ (Y ∖ Z).
Proof.
  iIntros (Hgt HsubY) "Hs Hc".
  unfold server, client.
  destruct (decide (n = 0)); try lia.
  assert (Hupd : (X, Y) ~l~> ((X ∖ Z), (Y ∖ Z))).
  {
    apply gmultiset_local_update_dealloc.
    done.
  }
  Local Notation B := (exclR unitO).
  iMod (own_update_2 with "Hs Hc") as "[$ $]"; last done.
  by apply auth_update, option_local_update,
        csum_local_update_l, prod_local_update_2.
Qed.

Lemma delete_client_for_good γ n (X Y Z: gmultiset V) :
  n > 0 ->
  server γ n X -∗ client γ Y ==∗ server γ n (X ∖ Y) ∗ client γ (∅: gmultiset V) ∗ ⌜Y ⊆ X⌝.
Proof.
  iIntros (Hgt) "Hs Hc".
  iDestruct ((server_agree γ n X Y) with "Hs Hc") as %H.
  destruct H as [H1 H2].
  assert (Y ⊆ X).
  {
    apply gmultiset_included.
    exact H2.
  }
  iFrame "%".
  replace (∅) with (Y ∖ Y).
  {
    iApply ((delete_client _ _ X Y Y) with "Hs Hc"); first done.
    done.
  }
  {
    apply gmultiset_difference_diag.
  }
Qed.

Lemma bulk_cancel_and_dealloc γ n (X Y: gmultiset V) :
  n > 0 ->
  server γ n X -∗ client γ Y ==∗ server γ (pred n) (X ∖ Y) ∗ ⌜Y ⊆ X⌝.
Proof.
  iIntros (Hgt) "Hs Hc".
  iDestruct (delete_client_for_good with "Hs Hc") as ">(H1 & H2 & %H3)"; try done.
  iFrame "%".
  iApply (dealloc_client with "H1 H2").
Qed.

Lemma bulk_dealloc_all γ (X : gmultiset V) (ys : list (gmultiset V)) :
  let Z_total := fold_right (λ acc y, acc ⊎ y) ∅ ys in
  server γ (length ys) X -∗ ([∗ list] y_i ∈ ys, client γ y_i) ==∗ server γ 0 (∅: (gmultiset V)) ∗ ⌜X = Z_total⌝.
Proof.
  clear IntoValTyped0 ZeroVal0 TypedPointsto0.
  intros.
  iIntros "Hs Hcs".
  destruct ys.
  {
    simpl. simpl in Z_total. subst Z_total. unfold server. simpl.
    iDestruct "Hs" as "(%H1 & H2 & H3)".
    iModIntro. iFrame. iPureIntro. done.
  }
  iInduction ys as [|g' ys'] "IH" forall (X).
  - simpl. iDestruct "Hcs" as "[Hc _]".
    simpl in Z_total. subst Z_total. replace (g ⊎ ∅) with g by multiset_solver.
    iDestruct ((server_1_agree γ X g) with "[$Hs] [$Hc]") as %H.
    iSplitR "".
    {
      iDestruct ((bulk_cancel_and_dealloc γ 1 X g) with "Hs Hc") as ">Hnew"; try lia.
      replace g with X by multiset_solver. simpl. replace ∅ with (X ∖ X) by multiset_solver.
      iModIntro. iDestruct "Hnew" as "[H1 %H2]". iFrame.
    }
    iModIntro. iPureIntro. multiset_solver.
  - iDestruct (big_sepL_cons with "Hcs") as "[Hc Hcs]".
    iDestruct (big_sepL_cons with "Hcs") as "[Hc' Hcs]".
    iAssert ([∗ list] y ∈ (g :: ys'), client γ y)%I with "[Hc Hcs]" as "Hcs".
    { iFrame. }
    iDestruct ((bulk_cancel_and_dealloc γ (length (g :: g' :: ys')) X g') with "Hs Hc'") as ">Hnew".
    {
      rewrite length_cons. lia.
    }
    replace (Init.Nat.pred (length (g :: g' :: ys'))) with (length (g :: ys')) by done.
    iSpecialize ("IH" $! (X ∖ g')).
    iDestruct "Hnew" as "[Hnew %Hss]".
    iApply "IH" in "Hnew".
    iMod ("Hnew" with "Hcs") as "[Hr %HX]".
    iFrame.
    iModIntro. subst Z_total.
    iPureIntro.
    simpl.
    simpl in HX.
    replace X with ((X ∖ g') ⊎ g').
    { rewrite HX. multiset_solver. }
    simpl.
    symmetry.
    rewrite gmultiset_disj_union_comm.
    apply gmultiset_disj_union_difference.
    done.
Qed.

Lemma bulk_alloc_clients γ (ys : list (gmultiset V)) :
  let X := fold_right (λ acc y, acc ⊎ y) ∅ ys in
  server γ 0 (∅: gmultiset V) ==∗ server γ (length ys) X ∗ ([∗ list] y_i ∈ ys, client γ y_i).
Proof.
  clear IntoValTyped0 ZeroVal0 TypedPointsto0.
  intros X.
  iIntros "Hs".
  iInduction ys as [|y ys'] "IH".
  { simpl. iModIntro. iFrame. }
  {
    simpl. simpl in X.
    iMod ("IH" with "Hs") as "[Hs Hcs']".
    iMod (alloc_client with "Hs") as "[Hs Hc]".
    iMod ((update_client γ _ (foldr (λ acc y0 : gmultiset V, acc ⊎ y0) ∅ ys') ε X y) with "Hs Hc") as "[Hs Hc]".
    {
      subst X.
      rewrite comm.
      apply gmultiset_local_update.
      multiset_solver.
    }
    iModIntro. iFrame.
  }
Qed.

Lemma auth_map_agree γ (X : gmultiset V) (ys : list (gmultiset V)) :
  let Z_total := fold_right (λ acc y, acc ⊎ y) ∅ ys in
  server γ (length ys) X -∗ ([∗ list] y_i ∈ ys, client γ y_i) ==∗
    ⌜X = Z_total⌝ ∗ server γ (length ys) X ∗ ([∗ list] y_i ∈ ys, client γ y_i).
Proof.
  intros Z_total.
  iIntros "Hs Hcs".
  iMod (bulk_dealloc_all with "Hs Hcs") as "[Hnew %HX]".
  iFrame "%".
  iMod (bulk_alloc_clients γ ys with "Hnew") as "[Hs Hcs]".
  iFrame. subst X. iFrame.
  iModIntro. done.
Qed.

(** [is_drained γ] says the channel is closed *and every sent value has been
    received* -- i.e. the logical state has reached [chanstate.Closed []].  It is
    NOT "close was called": the invariant below persists this flag only at
    [Closed []], so closing a buffered channel that still holds values leaves it
    unset, and [recv_drain_au] sets it when a receiver takes the last value.
    This is why [wp_mpmc_close] cannot hand it back, and why
    [mpmc_get_final_resource] demands it: [R] is the final resource, which
    cannot be available while values are still in flight. *)
Definition is_drained (γ:mpmc_names) : iProp Σ :=
  dghost_var γ.(mpmc_closed_name) DfracDiscarded true.

Global Instance is_drained_persistent γ : Persistent (is_drained γ) := _.

Definition mpmc_producer (γ:mpmc_names) (sent:gmultiset V) : iProp Σ :=
  client γ.(mpmc_sent_name) sent.

Definition mpmc_consumer (γ:mpmc_names) (received:gmultiset V) : iProp Σ :=
  client γ.(mpmc_recv_name) received.

Definition inflight_mset (s : chanstate.t V) : gmultiset V :=
  match s with
  | chanstate.Buffered buff => list_to_set_disj buff
  | chanstate.SndWait v | chanstate.SndDone v => {[+ v +]}
  | chanstate.Closed drain => list_to_set_disj drain
  | _ => ∅
  end.

Definition is_mpmc (γ:mpmc_names) (ch:loc) (n_prod n_cons:nat)
                   (P: V → iProp Σ) (R: gmultiset V → iProp Σ) : iProp Σ :=
    is_chan ch γ.(mpmc_chan_name) V ∗
    inv nroot (
      ∃ s sent recv,
        "Hch" ∷ own_chan γ.(mpmc_chan_name) V s ∗
        "HsentI" ∷ server γ.(mpmc_sent_name) n_prod sent ∗
        "HrecvI" ∷ server γ.(mpmc_recv_name) n_cons recv ∗
        "%Hrel" ∷ ⌜sent = recv ⊎ inflight_mset s⌝ ∗
        "%Hncons" ∷ ⌜n_cons > 0⌝ ∗
        "%Hnprod" ∷ ⌜n_prod > 0⌝ ∗
        "Hclosed" ∷ (match s with
                     | chanstate.Closed [] => dghost_var γ.(mpmc_closed_name) DfracDiscarded true
                     | _ => dghost_var γ.(mpmc_closed_name) (DfracOwn 1) false
                     end) ∗
        (match s with
        | chanstate.Buffered buff => "Hbuff" ∷ [∗ list] v ∈ buff, P v
        | chanstate.SndWait v => "HPv" ∷ P v
        | chanstate.SndDone v => "HPv" ∷ P v
        | chanstate.Closed [] =>
            "%Hsent_recv" ∷ ⌜sent = recv⌝ ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γ s_i) ∗
            "HR_or_clients" ∷ (R sent ∨ (∃ conss : list (gmultiset V), ⌜length conss = n_cons⌝ ∗
                                          [∗ list] r_i ∈ conss, mpmc_consumer γ r_i))
        | chanstate.Closed drain =>
            "Hdrain" ∷ ([∗ list] v ∈ drain, P v) ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γ s_i) ∗
            "HR" ∷ R sent
        | _ => True
        end)
    )%I.

Lemma gmultiset_disj_union_local_update (X Y Z : gmultiset V) :
  (X, Y) ~l~> (X ⊎ Z, Y ⊎ Z).
Proof.
  apply gmultiset_local_update_alloc.
Qed.

Lemma start_mpmc ch (P : V → iProp Σ) (R : gmultiset V → iProp Σ) γ (n_prod n_cons : nat) s:
  match s with
  | chanstate.Buffered [] => True
  | chanstate.Idle => True
  | _ => False
  end ->
  n_prod > 0 ->
  n_cons > 0 ->
  is_chan ch γ V -∗
  (own_chan γ V s) ={⊤}=∗
  (∃ γmpmc, is_mpmc γmpmc ch n_prod n_cons P R ∗
            ([∗ list] _ ∈ seq 0 n_prod, mpmc_producer γmpmc ∅) ∗
            ([∗ list] _ ∈ seq 0 n_cons, mpmc_consumer γmpmc ∅)).
Proof.
  intros Hs Hprod Hcons.
  iIntros "#Hch Hoc".
  iMod (dghost_var_alloc false) as (γclosed) "Hclosed".
  iMod (contribution_init_pow n_prod (A := gmultisetR V)) as (γsent) "[HsentAuth HsentFrags]".
  iMod (contribution_init_pow n_cons (A := gmultisetR V)) as (γrecv) "[HrecvAuth HrecvFrags]".
  set (γmpmc := {| mpmc_chan_name := γ;
                   mpmc_sent_name := γsent;
                   mpmc_recv_name := γrecv;
                   mpmc_closed_name := γclosed |}).
  destruct s; try done.
  {
    destruct buff; try done.
    iMod (inv_alloc nroot _ (
      ∃ s sent recv,
        "Hch" ∷ own_chan γ V s ∗
        "HsentI" ∷ server γsent n_prod sent ∗
        "HrecvI" ∷ server γrecv n_cons recv ∗
        "%Hrel" ∷ ⌜sent = recv ⊎ inflight_mset s⌝ ∗
        "%Hncons" ∷ ⌜n_cons > 0⌝ ∗
        "%Hnprod" ∷ ⌜n_prod > 0⌝ ∗
        "Hclosed" ∷ (match s with
                     | chanstate.Closed [] => dghost_var γclosed DfracDiscarded true
                     | _ => dghost_var γclosed (DfracOwn 1) false
                     end) ∗
        (match s with
        | chanstate.Buffered buff => "Hbuff" ∷ [∗ list] v ∈ buff, P v
        | chanstate.SndWait v => "HPv" ∷ P v
        | chanstate.SndDone v => "HPv" ∷ P v
        | chanstate.Closed [] =>
            "%Hsent_recv" ∷ ⌜sent = recv⌝ ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR_or_clients" ∷ (R sent ∨ (∃ conss : list (gmultiset V), ⌜length conss = n_cons⌝ ∗
                                          [∗ list] r_i ∈ conss, mpmc_consumer γmpmc r_i))
        | chanstate.Closed drain =>
            "Hdrain" ∷ ([∗ list] v ∈ drain, P v) ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR" ∷ R sent
        | _ => True
        end)
    ) with "[Hoc HsentAuth HrecvAuth Hclosed]") as "#Hinv".
    {
      iNext.
      iFrame.
      iSplitL ""; first done.
      iFrame.
      simpl. done.
    }
    iModIntro. iExists γmpmc.
    unfold is_mpmc. iFrame. iSplitL "". { iFrame "#". }
    iSplitL "HsentFrags".
    - unfold mpmc_producer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
    - unfold mpmc_consumer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
  }
  {
    iMod (inv_alloc nroot _ (
      ∃ s sent recv,
        "Hch" ∷ own_chan γ V s ∗
        "HsentI" ∷ server γsent n_prod sent ∗
        "HrecvI" ∷ server γrecv n_cons recv ∗
        "%Hrel" ∷ ⌜sent = recv ⊎ inflight_mset s⌝ ∗
        "%Hncons" ∷ ⌜n_cons > 0⌝ ∗
        "%Hnprod" ∷ ⌜n_prod > 0⌝ ∗
        "Hclosed" ∷ (match s with
                     | chanstate.Closed [] => dghost_var γclosed DfracDiscarded true
                     | _ => dghost_var γclosed (DfracOwn 1) false
                     end) ∗
        (match s with
        | chanstate.Buffered buff => "Hbuff" ∷ [∗ list] v ∈ buff, P v
        | chanstate.SndWait v => "HPv" ∷ P v
        | chanstate.SndDone v => "HPv" ∷ P v
        | chanstate.Closed [] =>
            "%Hsent_recv" ∷ ⌜sent = recv⌝ ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR_or_clients" ∷ (R sent ∨ (∃ conss : list (gmultiset V), ⌜length conss = n_cons⌝ ∗
                                          [∗ list] r_i ∈ conss, mpmc_consumer γmpmc r_i))
        | chanstate.Closed drain =>
            "Hdrain" ∷ ([∗ list] v ∈ drain, P v) ∗
            "Hprods" ∷ (∃ prods : list (gmultiset V), ⌜length prods = n_prod⌝ ∗
                        [∗ list] s_i ∈ prods, mpmc_producer γmpmc s_i) ∗
            "HR" ∷ R sent
        | _ => True
        end)
    ) with "[Hoc HsentAuth HrecvAuth Hclosed]") as "#Hinv".
    {
      iNext.
      iFrame.
      iSplitL ""; first done.
      iFrame.
      iPureIntro. done.
    }
    iModIntro. iExists γmpmc.
    unfold is_mpmc. iFrame. iSplitL "". { iFrame "#". }
    iSplitL "HsentFrags".
    - unfold mpmc_producer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
    - unfold mpmc_consumer.
      assert (∅ = (ε : gmultiset V)) as Heq by reflexivity.
      rewrite -Heq.
      iApply big_sepL_replicate.
      rewrite length_seq. done.
  }
Qed.

(* Open the mpmc invariant and hand the arm the invariant's half of [own_chan]. *)
Local Ltac mp_open :=
  iInv "Hinv" as "Hi" "Hclose";
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi";
  iNamed "Hi".
(* One credit strips the invariant body and the client's continuation together:
   [▷A ∗ ▷B ⊣⊢ ▷(A ∗ B)].  Phase two of a two-phase arm uses [mp_open], since
   the continuation was already stripped in phase one. *)
Local Ltac mp_openc :=
  iInv "Hinv" as "Hi" "Hclose";
  iCombine "Hi Hcont" as "Hic";
  iMod (lc_fupd_elim_later with "Hlc Hic") as "[Hi Hcont]";
  iNamed "Hi".
Local Ltac mp_agree := iDestruct (own_chan_agree with "Hch Himpl") as %->; simpl.
(* [h] names the capacity fact read off the half the arm was handed; it is
   what discharges [chan_cap_valid] for the post-state. *)
Local Ltac mp_step st h :=
  mp_agree;
  iDestruct (own_chan_cap_valid with "Himpl") as %h;
  iMod (own_chan_halves_update st with "Hch Himpl") as "[H1 H2]";
  [ simpl in h |- *; lia | ].

(* No later credits needed: each conjunct names a concrete pre-state, so the
   invariant is reconciled by agreement with the half the arm is handed. *)
Lemma mpmc_send_au γ ch (n_prod n_cons:nat) (P : V → iProp Σ) (R : gmultiset V → iProp Σ)
                   (sent : gmultiset V) (v : V) Φ :
  is_mpmc γ ch n_prod n_cons P R -∗
  mpmc_producer γ sent ∗ P v -∗
  ▷(mpmc_producer γ (sent ⊎ {[+ v +]}) -∗ Φ) -∗
  send_au γ.(mpmc_chan_name) V v Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#Hmpmc [Hprod HP] Hcont".
  iDestruct "Hmpmc" as "[Hchan Hinv]".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au : RcvWait -> SndDone v *)
    iIntros "[Hlc Himpl]". mp_openc. mp_step (chanstate.SndDone v) Hcv1.
    iMod (update_client γ.(mpmc_sent_name) n_prod sent0 sent
                       (sent0 ⊎ {[+ v +]}) (sent ⊎ {[+ v +]})
           with "HsentI Hprod") as "[HsentI Hprod]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hclose" with "[H1 HsentI HrecvI Hclosed HP]") as "_".
    { iNext. iExists (chanstate.SndDone v), (sent0 ⊎ {[+ v +]}), recv.
      iFrame "H1 HsentI HrecvI Hclosed HP".
      iPureIntro. split_and!; try done.
      simpl in Hrel |- *. multiset_solver. }
    iModIntro. iFrame "H2". by iApply ("Hcont" with "Hprod").
  - (* send_slow_path_au : Idle -> SndWait v, then RcvDone -> Idle *)
    iIntros "[Hlc Himpl]". mp_openc. mp_step (chanstate.SndWait v) Hcv2.
    iMod (update_client γ.(mpmc_sent_name) n_prod sent0 sent
                       (sent0 ⊎ {[+ v +]}) (sent ⊎ {[+ v +]})
           with "HsentI Hprod") as "[HsentI Hprod]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hclose" with "[H1 HsentI HrecvI Hclosed HP]") as "_".
    { iNext. iExists (chanstate.SndWait v), (sent0 ⊎ {[+ v +]}), recv.
      iFrame "H1 HsentI HrecvI Hclosed HP".
      iPureIntro. split_and!; try done.
      simpl in Hrel |- *. multiset_solver. }
    iModIntro. iFrame "H2". try iClear "Hi".
    (* phase two, fired once the receiver has committed *)
    iIntros "[Hlc Himpl]". mp_open. mp_step (@chanstate.Idle V) Hcv3.
    iMod ("Hclose" with "[H1 HsentI HrecvI Hclosed]") as "_".
    { iNext. iExists chanstate.Idle, sent1, recv0.
      iFrame "H1 HsentI HrecvI Hclosed".
      iPureIntro. split_and!; try done. }
    iModIntro. iFrame "H2". by iApply ("Hcont" with "Hprod").
  - (* send_enq_au : the implementation has already checked there is room *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". mp_openc. mp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iMod (own_chan_halves_update (chanstate.Buffered (buf ++ [v]))
           with "Hch Himpl") as "[H1 H2]".
    { simpl. rewrite length_app /=. lia. } iNamed "Hi".
    iMod (update_client γ.(mpmc_sent_name) n_prod sent0 sent
                       (sent0 ⊎ {[+ v +]}) (sent ⊎ {[+ v +]})
           with "HsentI Hprod") as "[HsentI Hprod]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hclose" with "[H1 HsentI HrecvI Hclosed HP Hbuff]") as "_".
    { iNext. iExists (chanstate.Buffered (buf ++ [v])), (sent0 ⊎ {[+ v +]}), recv.
      iFrame "H1 HsentI HrecvI Hclosed".
      iSplitR.
      { iPureIntro. rewrite Hrel. simpl.
        rewrite list_to_set_disj_app /=. multiset_solver. }
      simpl. rewrite big_sepL_app /=. iFrame "Hbuff HP". iFrame "%". }
    iModIntro. iFrame "H2". by iApply ("Hcont" with "Hprod").
  - (* send_closed_au : at Closed the invariant holds every producer client, so
       our own [mpmc_producer] is one client too many.  NOTE: [server_agree]
       needs its carrier passed explicitly -- left implicit, resolving
       [contributionG Σ ?A] diverges and the proof never terminates. *)
    iIntros (drain) "[Hlc Himpl]". mp_openc. mp_agree.
    destruct drain as [|d ds]; unfold mpmc_producer; iNamed "Hi"; iNamed "Hprods";
      iDestruct "Hprods" as "[%Hlen Hprods]"; subst n_prod;
      iMod (bulk_dealloc_all with "HsentI Hprods") as "[Hserver0 _]";
      (destruct prods as [|p ps]; first (simpl in Hnprod; lia));
      iDestruct (server_agree γ.(mpmc_sent_name) 0 (∅ : gmultiset V) sent
                  with "Hserver0 Hprod") as %[Hcontra _]; done.
Qed.

Lemma wp_mpmc_send γ ch (n_prod n_cons:nat) (P : V → iProp Σ) (R : gmultiset V → iProp Σ)
                   (sent : gmultiset V) (v : V) :
  {{{ is_mpmc γ ch n_prod n_cons P R ∗
      mpmc_producer γ sent ∗
      P v }}}
    chan.send t #ch #v
  {{{ RET #(); mpmc_producer γ (sent ⊎ {[+ v +]}) }}}.
Proof using W.
  iIntros (Φ) "(#Hmpmc & Hprod & HP) Hcont".
  unfold is_mpmc. iPoseProof "Hmpmc" as "[#Hchan _]".
  iApply (chan.wp_send ch v γ.(mpmc_chan_name) with "[$Hchan]").
  iIntros "_".
  iApply (mpmc_send_au with "[$Hmpmc] [$Hprod $HP]").
  done.
Qed.

Lemma mpmc_rcv_au γ ch (n_prod n_cons:nat) (P : V → iProp Σ) (R : gmultiset V → iProp Σ)
                      (received : gmultiset V) Φ :
  is_mpmc γ ch n_prod n_cons P R -∗
  mpmc_consumer γ received -∗
  ▷(∀ (v: V) (ok: bool),
    (if ok
      then P v ∗ mpmc_consumer γ (received ⊎ {[+ v +]})
      else is_drained γ ∗ mpmc_consumer γ received ∗ ⌜ v = (zero_val V) ⌝ ) -∗ Φ v ok) -∗
  recv_au γ.(mpmc_chan_name) V Φ.
Proof.
  clear IntoValTyped0.
  iIntros "#Hmpmc Hcons Hcont".
  unfold is_mpmc. iDestruct "Hmpmc" as "[Hchan Hinv]".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au : SndWait w -> RcvDone *)
    iIntros (w) "[Hlc Himpl]". mp_openc. mp_step (@chanstate.RcvDone V) Hcv1.
    iNamed "Hi".
    iMod (update_client γ.(mpmc_recv_name) n_cons recv received
                       (recv ⊎ {[+ w +]}) (received ⊎ {[+ w +]})
           with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hclose" with "[H1 HsentI HrecvI_new Hclosed]") as "_".
    { iNext. iExists chanstate.RcvDone, sent, (recv ⊎ {[+ w +]}).
      iFrame "H1 HsentI HrecvI_new Hclosed".
      iPureIntro. split_and!; try done.
      simpl in Hrel |- *. multiset_solver. }
    iModIntro. iFrame "H2". iApply "Hcont". iFrame "HPv Hcons_new".
  - (* recv_slow_path_au : Idle -> RcvWait, then SndDone w -> Idle *)
    iIntros "[Hlc Himpl]". mp_openc. mp_step (@chanstate.RcvWait V) Hcv2.
    iMod ("Hclose" with "[H1 HsentI HrecvI Hclosed]") as "_".
    { iNext. iExists chanstate.RcvWait, sent, recv.
      iFrame "H1 HsentI HrecvI Hclosed". iPureIntro. split_and!; try done. }
    iModIntro. iFrame "H2". try iClear "Hi".
    (* phase two, fired once the sender has committed *)
    iIntros (w) "[Hlc Himpl]". mp_open. mp_step (@chanstate.Idle V) Hcv3.
    iNamed "Hi".
    iMod (update_client γ.(mpmc_recv_name) n_cons recv0 received
                       (recv0 ⊎ {[+ w +]}) (received ⊎ {[+ w +]})
           with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hclose" with "[H1 HsentI HrecvI_new Hclosed]") as "_".
    { iNext. iExists chanstate.Idle, sent0, (recv0 ⊎ {[+ w +]}).
      iFrame "H1 HsentI HrecvI_new Hclosed".
      iPureIntro. split_and!; try done.
      simpl in Hrel0 |- *. multiset_solver. }
    iModIntro. iFrame "H2". iApply "Hcont". iFrame "HPv Hcons_new".
  - (* recv_deq_au : take the head off the buffer *)
    iIntros (w rest) "[Hlc Himpl]". mp_openc. mp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iMod (own_chan_halves_update (chanstate.Buffered rest) with "Hch Himpl") as "[H1 H2]".
    { simpl in Hlen |- *. split; lia. } iNamed "Hi".
    iDestruct "Hbuff" as "[HPv Hrest]".
    iMod (update_client γ.(mpmc_recv_name) n_cons recv received
                       (recv ⊎ {[+ w +]}) (received ⊎ {[+ w +]})
           with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
    { apply gmultiset_disj_union_local_update. }
    iMod ("Hclose" with "[H1 HsentI HrecvI_new Hclosed Hrest]") as "_".
    { iNext. iExists (chanstate.Buffered rest), sent, (recv ⊎ {[+ w +]}).
      iFrame "H1 HsentI HrecvI_new Hclosed Hrest".
      iPureIntro. split_and!; try done.
      rewrite Hrel. simpl. multiset_solver. }
    iModIntro. iFrame "H2". iApply "Hcont". iFrame "HPv Hcons_new".
  - (* recv_drain_au : take the head off a closed channel's drain *)
    iIntros (w rest) "[Hlc Himpl]". mp_openc. mp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iNamed "Hi". iDestruct "Hdrain" as "[HPv Hrest]".
    iMod (update_client γ.(mpmc_recv_name) n_cons recv received
                       (recv ⊎ {[+ w +]}) (received ⊎ {[+ w +]})
           with "HrecvI Hcons") as "[HrecvI_new Hcons_new]".
    { apply gmultiset_disj_union_local_update. }
    destruct rest as [|r rs].
    + (* last drained value: the channel becomes fully closed *)
      iMod (own_chan_halves_update (@chanstate.Closed V []) with "Hch Himpl") as "[H1 H2]".
      { simpl in Hlen |- *. lia. }
      iMod (dghost_var_update true with "Hclosed") as "Hclosed".
      iMod (dghost_var_persist with "Hclosed") as "#Hclosed'".
      iMod ("Hclose" with "[H1 HsentI HrecvI_new Hprods HR]") as "_".
      { iNext. iExists (chanstate.Closed []), sent, (recv ⊎ {[+ w +]}).
        iFrame "H1 HsentI HrecvI_new". iFrame "#". iFrame "Hprods".
        (* Hrel, n_cons, n_prod, Hsent_recv, then the [R sent] disjunct *)
        iSplitR; [ iPureIntro; simpl in Hrel |- *; multiset_solver | ].
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; simpl in Hrel |- *; multiset_solver | ].
        iLeft. iFrame "HR". }
      iModIntro. iFrame "H2". iApply "Hcont". iFrame "HPv Hcons_new".
    + (* more values still to drain *)
      iMod (own_chan_halves_update (chanstate.Closed (r :: rs)) with "Hch Himpl")
        as "[H1 H2]".
      { simpl in Hlen |- *. split; lia. }
      iMod ("Hclose" with "[H1 HsentI HrecvI_new Hclosed Hrest Hprods HR]") as "_".
      { iNext. iExists (chanstate.Closed (r :: rs)), sent, (recv ⊎ {[+ w +]}).
        iFrame "H1 HsentI HrecvI_new Hclosed Hrest Hprods HR".
        iPureIntro. split_and!; try done.
        rewrite Hrel. simpl. multiset_solver. }
      iModIntro. iFrame "H2". iApply "Hcont". iFrame "HPv Hcons_new".
  - (* recv_closed_au : drained and closed, so the receive fails *)
    iIntros "[Hlc Himpl]". mp_openc. mp_agree.
    iNamed "Hi".
    iDestruct "HR_or_clients" as "[HR_final | Hconss]".
    + iDestruct "Hclosed" as "#Hclosed".
      iMod ("Hclose" with "[Hch HsentI HrecvI Hprods HR_final]") as "_".
      { iNext. iExists (chanstate.Closed []), sent, recv.
        iFrame "Hch HsentI HrecvI Hprods". iFrame "#".
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; done | ].
        iLeft. iFrame "HR_final". }
      iModIntro. iFrame "Himpl". iApply "Hcont".
      iFrame "Hcons". unfold is_drained. iFrame "#". done.
    + (* the invariant already holds every consumer client, so ours is one too many *)
      unfold mpmc_consumer. iNamed "Hconss".
      iDestruct "Hconss" as "[%Hlen2 Hcons1]". subst n_cons.
      iMod (bulk_dealloc_all with "HrecvI Hcons1") as "[Hserver0 _]".
      destruct conss as [|p ps]; first (simpl in Hncons; lia).
      iDestruct (server_agree γ.(mpmc_recv_name) 0 (∅ : gmultiset V) received
                  with "Hserver0 Hcons") as %[Hcontra _].
      exfalso; exact (Hcontra eq_refl).
Qed.

Lemma wp_mpmc_receive γ ch (n_prod n_cons:nat) (P : V → iProp Σ) (R : gmultiset V → iProp Σ)
                      (received : gmultiset V) :
  {{{  is_mpmc γ ch n_prod n_cons P R ∗
      mpmc_consumer γ received }}}
    chan.receive t #ch
  {{{ (v:V) (ok:bool), RET (#v, #ok);
      if ok
      then P v ∗ mpmc_consumer γ (received ⊎ {[+ v +]})
      else is_drained γ ∗ mpmc_consumer γ received ∗ ⌜ v = (zero_val V) ⌝ }}}.
Proof using W.
  iIntros (Φ) "( #Hmpmc & Hcons) Hcont".
  unfold is_mpmc.
  iPoseProof "Hmpmc" as "[#Hchan _]".
  iApply (chan.wp_receive ch γ.(mpmc_chan_name) with "[$Hchan]").
  iIntros "_".
  iApply (mpmc_rcv_au with "[$Hmpmc] [$Hcons]").
  done.
Qed.

(* Close only has to consider Idle and Buffered: [tryClose] spins on every
   pending/committed state, so those are unreachable here. *)
Lemma mpmc_close_au γ ch (n_prod n_cons:nat) P R (producers : list (gmultiset V)) Φ :
  length producers = n_prod →
  is_mpmc γ ch n_prod n_cons P R -∗
  ([∗ list] s_i ∈ producers, mpmc_producer γ s_i) ∗
        R (foldr (⊎) ∅ producers) -∗
  ▷ Φ -∗
  close_au γ.(mpmc_chan_name) V Φ.
Proof.
  clear IntoValTyped0.
  intros Hnp.
  iIntros "#Hmpmc (Hprods1 & HR) Hcont".
  unfold is_mpmc. iDestruct "Hmpmc" as "[Hchan Hinv]".
  rewrite /close_au. repeat iSplit.
  - (* close_idle_au : Idle -> Closed [] *)
    iIntros "[Hlc Himpl]". mp_openc. mp_step (@chanstate.Closed V []) Hcv1.
    iMod (dghost_var_update true with "Hclosed") as "Hclosed".
    iMod (dghost_var_persist with "Hclosed") as "#Hclosed'".
    unfold mpmc_producer. subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods1]")
      as "(%Hsent_eq & HsentI & Hprods1)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    iMod ("Hclose" with "[H1 HsentI HrecvI Hprods1 HR]") as "_".
    { iNext. iExists (chanstate.Closed []), sent, recv.
      iFrame "H1 HsentI HrecvI". iFrame "#".
      iSplitR; [ iPureIntro; simpl in Hrel |- *; multiset_solver | ].
      iSplitR; [ iPureIntro; done | ].
      iSplitR; [ iPureIntro; done | ].
      iSplitR; [ iPureIntro; simpl in Hrel |- *; multiset_solver | ].
      iFrame "Hprods1". iSplitR; [ iPureIntro; done | ]. iLeft. iFrame "HR". }
    iModIntro. iFrame "H2 Hcont".
  - (* close_buf_au : the buffered values become the drain *)
    iIntros (buf) "[Hlc Himpl]". mp_openc. mp_agree.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    unfold mpmc_producer. subst n_prod.
    iMod (auth_map_agree γ.(mpmc_sent_name) sent producers with "[$HsentI] [$Hprods1]")
      as "(%Hsent_eq & HsentI & Hprods1)".
    replace (foldr (λ acc y : gmultiset V, acc ⊎ y) ∅ producers) with sent by done.
    destruct buf as [|d ds].
    + (* nothing buffered, so the channel is closed and already drained *)
      iMod (own_chan_halves_update (@chanstate.Closed V []) with "Hch Himpl") as "[H1 H2]".
      { simpl in Hlen |- *. lia. }
      iMod (dghost_var_update true with "Hclosed") as "Hclosed".
      iMod (dghost_var_persist with "Hclosed") as "#Hclosed'".
      iMod ("Hclose" with "[H1 HsentI HrecvI Hprods1 HR]") as "_".
      { iNext. iExists (chanstate.Closed []), sent, recv.
        iFrame "H1 HsentI HrecvI". iFrame "#".
        iSplitR; [ iPureIntro; simpl in Hrel |- *; multiset_solver | ].
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; simpl in Hrel |- *; multiset_solver | ].
        iFrame "Hprods1". iSplitR; [ iPureIntro; done | ]. iLeft. iFrame "HR". }
      iModIntro. iFrame "H2 Hcont".
    + iMod (own_chan_halves_update (chanstate.Closed (d :: ds)) with "Hch Himpl")
        as "[H1 H2]".
      { simpl in Hlen |- *. split; lia. } iNamed "Hi".
      iMod ("Hclose" with "[H1 HsentI HrecvI Hclosed Hbuff Hprods1 HR]") as "_".
      { iNext. iExists (chanstate.Closed (d :: ds)), sent, recv.
        iFrame "H1 HsentI HrecvI Hclosed".
        iSplitR; [ iPureIntro; simpl in Hrel |- *; multiset_solver | ].
        iSplitR; [ iPureIntro; done | ].
        iSplitR; [ iPureIntro; done | ].
        iFrame "Hbuff HR Hprods1". try (iPureIntro; done). }
      iModIntro. iFrame "H2 Hcont".
  - (* close_closed_au : the invariant already holds every producer client, so the
       [mpmc_producer]s we were handed are too many.  [server_agree] and
       [auth_map_agree] both need their carrier given explicitly. *)
    iIntros (drain) "[Hlc Himpl]". mp_openc. mp_agree.
    unfold mpmc_producer.
    destruct drain as [|d ds].
    + iNamed "Hi". iDestruct "Hprods" as (prods) "[%Hgood H2]".
      replace n_prod with (length prods) by lia.
      iMod (auth_map_agree γ.(mpmc_sent_name) sent prods with "[$HsentI] [$H2]")
        as "(%Hsent_eq1 & HsentI2 & Hprods2)".
      iMod (bulk_dealloc_all with "HsentI2 Hprods2") as "[Hserver0 _]".
      destruct producers as [|p ps]; first (simpl in Hnp; lia).
      iDestruct "Hprods1" as "[Hp _]".
      iDestruct (server_agree γ.(mpmc_sent_name) 0 (∅ : gmultiset V) p
                  with "Hserver0 Hp") as %[Hcontra _].
      lia.
    + (* [iNamed] stops after [Hdrain] here, leaving the rest parked under [Hi] *)
      iNamed "Hi". iDestruct "Hi" as "(Hprods & HR2)".
      iDestruct "Hprods" as (prods) "[%Hgood H2]".
      replace n_prod with (length prods) by lia.
      iMod (auth_map_agree γ.(mpmc_sent_name) sent prods with "[$HsentI] [$H2]")
        as "(%Hsent_eq1 & HsentI2 & Hprods2)".
      iMod (bulk_dealloc_all with "HsentI2 Hprods2") as "[Hserver0 _]".
      destruct producers as [|p ps]; first (simpl in Hnp; lia).
      iDestruct "Hprods1" as "[Hp _]".
      iDestruct (server_agree γ.(mpmc_sent_name) 0 (∅ : gmultiset V) p
                  with "Hserver0 Hp") as %[Hcontra _].
      lia.
Qed.

Lemma wp_mpmc_close γ ch (n_prod n_cons:nat) P R (producers : list (gmultiset V)) `[ct ↓u go.ChannelType dir t]:
  length producers = n_prod →
  {{{ is_mpmc γ ch n_prod n_cons P R ∗
      ([∗ list] s_i ∈ producers, mpmc_producer γ s_i) ∗
      R (foldr (⊎) ∅ producers) }}}
    #(functions go.close [ct]) #ch
  {{{ RET #(); True }}}.
Proof using W.
  intros.
  iIntros "(#Hmpmc & Hprods & HR) Hcont".
  iPoseProof "Hmpmc" as "[#Hchan _]".
  iApply (chan.wp_close with "Hchan").
  iIntros "_".
  iApply (mpmc_close_au with "[$Hmpmc] [$Hprods $HR]").
  { done. }
  iModIntro. by iApply "Hcont".
Qed.

Lemma mpmc_get_final_resource
  γ ch (n_prod n_cons : nat) P R (consumers : list (gmultiset V)) :
  length consumers = n_cons →
  £ 1 -∗
  is_mpmc γ ch n_prod n_cons P R -∗
  is_drained γ -∗
  ([∗ list] r_i ∈ consumers, mpmc_consumer γ r_i)
  ={⊤}=∗ R (foldr disj_union ∅ consumers).
Proof.
  clear IntoValTyped0.
  iIntros (Hlen) "Hlc #Hmpmc #Hclosed Hcons".
  unfold is_mpmc. iDestruct "Hmpmc" as "[#Hchan #Hinv]".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iNamed "Hinv_open".
  iMod (lc_fupd_elim_later with "Hlc Hinv_open") as "Hinv_open".
  iDestruct "Hclosed" as "#Hclosed1".
  iNamed "Hinv_open".
  unfold is_drained.
  destruct s; try (iExFalso;(iDestruct (dghost_var_agree with "Hclosed1 Hclosed") as %Hbad);done).
  destruct drain.
  - iNamed "Hinv_open".
    iDestruct "HR_or_clients" as "[HR | Hconss]".
    + unfold mpmc_consumer.
      subst n_cons.
      iMod (auth_map_agree γ.(mpmc_recv_name) recv consumers with "HrecvI Hcons") as
        "(%Hrecv_eq & HrecvI & Hcons)". rewrite Hsent_recv. rewrite Hrecv_eq.
      iFrame.
      iMod ("Hinv_close" with "[Hch HsentI HrecvI Hclosed Hprods Hcons]") as "_".
      {
        iNext. iFrame "#%". iFrame.
        rewrite Hsent_recv. rewrite Hrecv_eq.
        iFrame.
        iRight.
        iFrame.
        done.
      }
      iModIntro. done.
    + unfold mpmc_consumer.
      subst n_cons.
      iMod (auth_map_agree γ.(mpmc_recv_name) recv consumers with "HrecvI Hcons") as
        "(%Hrecv_eq & HrecvI & Hcons)". rewrite Hsent_recv. rewrite Hrecv_eq.
      iFrame.
      iExFalso.
      iDestruct "Hconss" as (conss Hlen_conss) "Hconss_list".
      iMod (bulk_dealloc_all with "HrecvI Hcons") as "[Hserver0 _]".
      destruct conss as [|c cs]; first (simpl in *;lia).
      iDestruct (big_sepL_cons with "Hconss_list") as "[Hc _]".
      iDestruct (server_agree with "Hserver0 Hc") as %[Hcontra _].
      lia.
  - iNamed "Hinv_open".
    unfold is_mpmc.
    iDestruct (dghost_var_agree with "Hclosed1 Hclosed") as %Hclosed_eq.
    done.
Qed.

End mpmc.
