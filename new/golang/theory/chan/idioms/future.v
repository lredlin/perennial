Require Import New.proof.proof_prelude.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.idioms Require Export base.
From New.golang.theory Require Import chan.


(** Future Channel

    This file provides the future idiom - a pattern where
    multiple workers fulfill promises independently and a single consumer awaits all results.

    ** Go Pattern

    This idiom is designed for code where you launch multiple independent
    goroutines to compute results concurrently, then collect all their results
    without caring about the order they complete. A canonical example is the
    replicated search pattern from Rob Pike's "Go Concurrency Patterns"
    (https://go.dev/talks/2012/concurrency.slide#46) talk:


    func Google(query string) (results []Result) {
        c := make(chan Result, 3)
        go func() { c <- Web(query) }()
        go func() { c <- Image(query) }()
        go func() { c <- Video(query) }()

        for i := 0; i < 3; i++ {
            result := <-c
            results = append(results, result)
        }
        return
    }

    ** How to Use

    1. Initialize a channel for use as a future with [start_future]
    2. For each producer, allocate a [Fulfill] with [future_alloc_promise],
       giving it a predicate contract P_i that describes what that producer will provide
    3. Each worker sends its result using [wp_future_fulfill], providing
       [Fulfill γ contract ∗ contract v], bundled as [Fulfilled γ v]
    4. The consumer receives using [wp_future_await]; each receive resolves
       one contract from [pending], returning [P v] for some [P] that was
       removed from [pending]
    5. When [pending] is empty, all contracts have been satisfied

    ** Understanding the Protocol

    Matching happens *at receive time*. Each receive identifies which contract
    was fulfilled (via ghost state agreement) and removes it from [pending].

    The postcondition of [wp_future_await] tells you:
    - [pending] splits as [pre ++ P :: post]
    - You get [P v] — the contract applied to the received value
    - You get [Await γ (pre ++ post)] — the remaining pending contracts
    - You don't know *which* [P] was resolved — that depends on scheduling
*)

Section future.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `{!allG Σ}.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Set Default Proof Using "All".


Record future_names := {
  chan_name : chan_names;
  pending_set_name : gname
}.

(** [Fulfill γ contract] is a token representing a registered contract.
    The holder commits to eventually sending a value [v] satisfying [contract v].
    Internally, it holds half of a saved predicate and an auth_set fragment. *)
Definition Fulfill (γ : future_names) (contract : V → iProp Σ) : iProp Σ :=
  ∃ (gn : gname),
    saved_pred_own gn (DfracOwn (1/2)) contract ∗
    auth_set_frag γ.(pending_set_name) gn.

(** [Fulfilled γ v] bundles a [Fulfill] with evidence that the contract is
    satisfied. This is what gets transferred through the channel. *)
Definition Fulfilled (γ : future_names) (v: V) : iProp Σ :=
  ∃ contract,
    Fulfill γ contract ∗ contract v.

(** [Await γ pending] is the consumer's tracking state.
    [pending] is the list of contracts not yet matched to a received value.

    Internally, an auth_set tracks which ghost names are pending, and
    saved predicates associate each ghost name with its contract. *)
Definition Await (γ : future_names)
    (pending : list (V → iProp Σ)) : iProp Σ :=
  ∃ (pending_map : gmap gname (V → iProp Σ)),
    auth_set_auth γ.(pending_set_name) (dom pending_map) ∗
    ⌜(map_to_list pending_map).*2 ≡ₚ pending⌝ ∗
    [∗ map] gn ↦ P ∈ pending_map,
      saved_pred_own gn (DfracOwn (1/2)) P.

(** [is_future γ ch] is the persistent channel invariant. The channel
    carries [Fulfilled] tokens — values bundled with their contract evidence. *)
Definition is_future (γ : future_names) (ch : loc) : iProp Σ :=
  is_chan ch γ.(chan_name) V ∗
  inv nroot (
    ∃ (s : chanstate.t V),
      "Hch" ∷ own_chan  γ.(chan_name) V s ∗
      match s with
      | chanstate.Buffered msgs => [∗ list] v ∈ msgs, Fulfilled γ v
      | chanstate.SndWait v => Fulfilled γ v
      | chanstate.SndDone v => Fulfilled γ v
      | chanstate.Idle | chanstate.RcvWait | chanstate.RcvDone => True
      | _ => False
      end
  )%I.

Local Lemma map_to_list_snd_insert {K} `{Countable K} {A}
  (m : gmap K A) (k : K) (v : A) :
  m !! k = None →
  (map_to_list (<[k := v]> m)).*2 ≡ₚ v :: (map_to_list m).*2.
Proof.
  intros Hlookup.

  have Hperm_pairs :
      map_to_list (<[k:=v]> m) ≡ₚ (k, v) :: map_to_list m.
  {
    exact (map_to_list_insert (K:=K) (M:=gmap K) (A:=A) m k v Hlookup).
  }

  have Hperm_vals :
      map snd (map_to_list (<[k:=v]> m)) ≡ₚ map snd ((k,v) :: map_to_list m) :=
    Permutation_map snd Hperm_pairs.

    done.

Qed.

Local Lemma map_to_list_snd_delete {K} `{Countable K} {A}
  (m : gmap K A) (k : K) (v : A) :
  m !! k = Some v →
  (map_to_list m).*2 ≡ₚ v :: (map_to_list (delete k m)).*2.
Proof.
  intros Hlookup.

  have Hperm_pairs :
      map_to_list m ≡ₚ (k, v) :: map_to_list (delete k m).
  { exact (Permutation_sym (map_to_list_delete m k v Hlookup)). }

  have Hperm_vals :
      map snd (map_to_list m) ≡ₚ map snd ((k, v) :: map_to_list (delete k m)) :=
    Permutation_map snd Hperm_pairs.

    done.
Qed.

Local Lemma Permutation_cons_split {A} (x : A) (l l' : list A) :
  l ≡ₚ x :: l' →
  ∃ pre post, l = pre ++ x :: post ∧ l' ≡ₚ pre ++ post.
Proof.
  intros Hperm.
  destruct (Permutation_cons_inv_r l' l x Hperm) as [pre [post [Hl Hperm']]].
  exists pre, post. split; [exact Hl | exact Hperm'].
Qed.

Lemma start_future (ch : loc) (γ : chan_names) (s : chanstate.t V) :
s = chanstate.Idle ∨ s = chanstate.Buffered [] ->
  is_chan ch γ V -∗
  own_chan γ V s
 ={⊤}=∗
  ∃ γmf, is_future γmf ch ∗ Await γmf [].
Proof.
  intros Hs.
  iIntros "#Hch Hoc".
  iMod (auth_set_init (A:=gname)) as (γpending) "Hset_auth".
  set (γmf := {|
    chan_name := γ;
    pending_set_name := γpending
  |}).
  iMod (inv_alloc nroot _ (
    ∃ s',
      "Hch" ∷ own_chan γ V s' ∗
      match s' with
      | chanstate.Buffered msgs => [∗ list] v ∈ msgs, Fulfilled γmf v
      | chanstate.SndWait v => Fulfilled γmf v
      | chanstate.SndDone v => Fulfilled γmf v
      | chanstate.Idle | chanstate.RcvWait | chanstate.RcvDone => True
      | _ => False
      end
  )%I with "[Hoc]") as "#Hinv".
  {
    iNext. iExists s. iFrame.
    destruct Hs as [-> | ->]; simpl; done.
  }
  iModIntro. iExists γmf.
  iSplitL "".
  { iFrame "#". }
  iExists ∅.
  rewrite dom_empty_L. iFrame.
  iSplitL "". { iPureIntro. rewrite map_to_list_empty. done. }
  simpl. done.
Qed.

Lemma future_alloc_promise γ ch (contract : V → iProp Σ)
    (pending : list (V → iProp Σ)) :
  is_future γ ch -∗
  Await γ pending ={⊤}=∗
  Fulfill γ contract ∗ Await γ (pending ++ [contract]).
  Proof .
  iIntros "#Hmf HAwait".
  iDestruct "HAwait" as (pending_map) "(Hauth & %Hperm & Hfrags)".
  iMod (saved_pred_alloc_cofinite contract (dom pending_map) (DfracOwn 1))
    as (gn) "[%Hfresh Hpred]".
  { done. }
  iDestruct "Hpred" as "[Hpred1 Hpred2]".
  iMod (auth_set_alloc gn with "Hauth") as "[Hauth Hfrag]".
  { done. }
  iModIntro.
  iSplitL "Hpred1 Hfrag".
  { iExists gn. iFrame. }
  iExists (<[gn := contract]> pending_map).
  rewrite dom_insert_L. iFrame "Hauth".
  iSplitR "Hfrags Hpred2".
  - iPureIntro.
    etrans; first apply map_to_list_snd_insert.
    + apply not_elem_of_dom. done.
    + rewrite Hperm. apply Permutation_cons_append.
  - iApply big_sepM_insert; first (apply not_elem_of_dom; done).
    iFrame.
Qed.

(* Open the future invariant and hand the arm the invariant's half. *)
Local Ltac fu_open :=
  iInv "Hinv" as "Hi" "Hclose";
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi";
  iDestruct "Hi" as (s) "[Hoc HI]".
(* One credit strips the invariant body and the client's continuation together:
   [▷A ∗ ▷B ⊣⊢ ▷(A ∗ B)].  Phase two of a two-phase arm uses [fu_open], since
   the continuation was already stripped in phase one. *)
Local Ltac fu_openc :=
  iInv "Hinv" as "Hi" "Hclose";
  iCombine "Hi Hau" as "Hic";
  iMod (lc_fupd_elim_later with "Hlc Hic") as "[Hi Hau]";
  iDestruct "Hi" as (s) "[Hoc HI]".
Local Ltac fu_agree := iDestruct (own_chan_agree with "Hoc Himpl") as %->; simpl.
(* Closed states are banned by the invariant. *)
Local Ltac fu_absurd := fu_agree; iDestruct "HI" as "[]".
Local Ltac fu_step st :=
  fu_agree;
  iDestruct (own_chan_cap_valid with "Himpl") as %?;
  iMod (own_chan_halves_update st with "Hoc Himpl") as "[H1 H2]";
  [ simpl in *; lia | ].

Lemma future_fulfill_au γ ch (v : V) :
  ∀ (Φ: iProp Σ),
  is_future γ ch -∗
  Fulfilled γ v -∗
  ▷ (True -∗ Φ) -∗
  send_au γ.(chan_name) V v Φ.
Proof.
  iIntros (Φ) "#Hmf HFulfilled Hau".
  rewrite /is_future. iDestruct "Hmf" as "[#Hisch #Hinv]".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au: RcvWait -> SndDone v *)
    iIntros "[Hlc Himpl]". fu_openc. fu_step (chanstate.SndDone v).
    iMod ("Hclose" with "[H1 HFulfilled]") as "_".
    { iNext. iExists (chanstate.SndDone v). iFrame. }
    iModIntro. iFrame. by iApply "Hau".
  - (* send_slow_path_au: Idle -> SndWait v, then RcvDone -> Idle *)
    iIntros "[Hlc Himpl]". fu_openc. fu_step (chanstate.SndWait v).
    iMod ("Hclose" with "[H1 HFulfilled]") as "_".
    { iNext. iExists (chanstate.SndWait v). iFrame. }
    iModIntro. iFrame. try iClear "HI".
    iIntros "[Hlc Himpl]". fu_open. fu_step (@chanstate.Idle V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.Idle. by iFrame. }
    iModIntro. iFrame. by iApply "Hau".
  - (* send_enq_au *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". fu_openc. fu_agree.
    iMod (own_chan_halves_update (chanstate.Buffered (buf ++ [v])) with "Hoc Himpl")
      as "[H1 H2]".
    { simpl. rewrite length_app /=. lia. }
    iMod ("Hclose" with "[H1 HI HFulfilled]") as "_".
    { iNext. iExists (chanstate.Buffered (buf ++ [v])).
      rewrite big_sepL_app /=. iFrame. }
    iModIntro. iFrame. by iApply "Hau".
  - (* send_closed_au: this idiom never closes *)
    iIntros (drain) "[Hlc Himpl]". fu_openc. fu_absurd.
Qed.

Lemma wp_future_fulfill γ ch (v : V) :
  {{{ is_future γ ch ∗ Fulfilled γ v }}}
    chan.send t #ch #v
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hmf & HFulfilled) HΦ".
  rewrite /is_future.
  iDestruct "Hmf" as "[#Hch #Hinv]".
  iApply (chan.wp_send ch v γ.(chan_name) with "[$Hch]").
  iIntros "_".
  iApply (future_fulfill_au with "[$Hch $Hinv] [$HFulfilled]").
  done.
Qed.

(** The core receive lemma. Each receive:
    1. Pulls a [Fulfilled γ v] from the channel invariant
    2. Uses saved predicate agreement to identify which contract was fulfilled
    3. Removes the matched contract from [pending]
    4. Returns [P v] directly to the caller *)
Lemma future_await_au γ ch
    (pending : list (V → iProp Σ)) :
  ∀ (Φ: V → bool → iProp Σ),
  is_future γ ch -∗
  £1 ∗ Await γ pending -∗
  ▷ (∀ (v : V) (P : V → iProp Σ) (pre post : list (V → iProp Σ)),
      ⌜pending = pre ++ P :: post⌝ -∗
      P v -∗
      Await γ (pre ++ post) -∗
      Φ v true) -∗
  recv_au γ.(chan_name) V Φ.
Proof.
  iIntros (Φ) "#Hmf (Hlc0 & HAwait) Hau".
  rewrite /is_future.
  iDestruct "Hmf" as "[#isHch #Hinv]".

  iAssert (
    ∀ (v_rcv : V),
      £1 -∗
      Fulfilled γ v_rcv -∗
      Await γ pending -∗
      |={⊤}=> ∃ (P : V → iProp Σ) (pre post : list (V → iProp Σ)),
        ⌜pending = pre ++ P :: post⌝ ∗ P v_rcv ∗ Await γ (pre ++ post)
  )%I as "Hmatch".
  {
    iIntros (v_rcv) "Hlc HFulfilled HAwait".
    iDestruct "HFulfilled" as (contract_f) "[HFulfill Hcontract_v]".
    iDestruct "HFulfill" as (gn_f) "[Hpred_f Hfrag_f]".
    iDestruct "HAwait" as (pending_map) "(Hauth & %Hperm & Hfrags)".
    iDestruct (auth_set_elem with "Hauth Hfrag_f") as %Hin.
    assert (∃ P, pending_map !! gn_f = Some P) as [P Hlookup].
    { apply elem_of_dom. done. }
    iDestruct (big_sepM_delete _ _ gn_f with "Hfrags")
      as "[Hpred_p Hfrags_rest]"; first done.
    iDestruct (saved_pred_agree gn_f _ _ contract_f P v_rcv
      with "Hpred_f Hpred_p") as "Hag".
    iMod (lc_fupd_elim_later with "Hlc Hag") as "Hag".
    iRewrite "Hag" in "Hcontract_v".
    iMod (auth_set_dealloc with "[$Hauth $Hfrag_f]") as "Hauth".
    pose proof (map_to_list_snd_delete _ _ _ Hlookup) as Hmap_perm.
    assert (pending ≡ₚ P :: (map_to_list (delete gn_f pending_map)).*2) as Hcons.
    { rewrite -Hmap_perm. done. }
    apply Permutation_cons_split in Hcons
      as (pre & post & Hsplit & Hrest_perm).
    iModIntro. iExists P, pre, post.
    iFrame "Hcontract_v".
    iSplitR; first done.
    iExists (delete gn_f pending_map).
    rewrite dom_delete_L. iFrame "Hauth Hfrags_rest". iPureIntro.
    by symmetry.
  }

  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au: SndWait w -> RcvDone *)
    iIntros (w) "[Hlc Himpl]". fu_openc. fu_step (@chanstate.RcvDone V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.RcvDone. by iFrame. }
    iMod ("Hmatch" with "Hlc0 HI HAwait") as (P pre post) "(%Hsplit & HP & HAwait')".
    iModIntro. iFrame "H2". iApply ("Hau" with "[%] HP HAwait'"). done.
  - (* recv_slow_path_au: Idle -> RcvWait, then SndDone w -> Idle *)
    iIntros "[Hlc Himpl]". fu_openc. fu_step (@chanstate.RcvWait V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.RcvWait. by iFrame. }
    iModIntro. iFrame "H2". try iClear "HI".
    iIntros (w) "[Hlc Himpl]". fu_open. fu_step (@chanstate.Idle V).
    iMod ("Hclose" with "[H1]") as "_".
    { iNext. iExists chanstate.Idle. by iFrame. }
    iMod ("Hmatch" with "Hlc0 HI HAwait") as (P pre post) "(%Hsplit & HP & HAwait')".
    iModIntro. iFrame "H2". iApply ("Hau" with "[%] HP HAwait'"). done.
  - (* recv_deq_au *)
    iIntros (w rest) "[Hlc Himpl]". fu_openc. fu_agree.
    iDestruct "HI" as "[HFul HRest]".
    iDestruct (own_chan_cap_valid with "Himpl") as %?.
    iMod (own_chan_halves_update (chanstate.Buffered rest) with "Hoc Himpl") as "[H1 H2]".
    { simpl in *. lia. }
    iMod ("Hclose" with "[H1 HRest]") as "_".
    { iNext. iExists (chanstate.Buffered rest). iFrame. }
    iMod ("Hmatch" with "Hlc0 HFul HAwait") as (P pre post) "(%Hsplit & HP & HAwait')".
    iModIntro. iFrame "H2". iApply ("Hau" with "[%] HP HAwait'"). done.
  - (* recv_drain_au: this idiom never closes *)
    iIntros (w rest) "[Hlc Himpl]". fu_openc. fu_absurd.
  - (* recv_closed_au *)
    iIntros "[Hlc Himpl]". fu_openc. fu_absurd.
Qed.

Lemma wp_future_await γ ch
    (pending : list (V → iProp Σ)) :
  {{{ is_future γ ch ∗ Await γ pending }}}
    chan.receive t #ch
  {{{ (v : V) (P : V → iProp Σ) (pre post : list (V → iProp Σ)),
      RET (#v, #true);
      ⌜pending = pre ++ P :: post⌝ ∗ P v ∗ Await γ (pre ++ post) }}}.
Proof.
  iIntros (Φ) "(#Hmf & HAwait) HΦ".
  rewrite /is_future.
  iDestruct "Hmf" as "[#Hch #Hinv]".
  iApply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (future_await_au with "[$Hch $Hinv] [$Hlc1 $HAwait]").
  iNext. iIntros (v P pre post) "%Hsplit HP HAwait".
  iApply ("HΦ" $! v P pre post).
  iFrame. done.
Qed.

End future.
