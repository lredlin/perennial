From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples Require Import channel_examples_init.
From New.golang.theory.chan.idioms.mixtris Require Import mixtris mixtris_proofmode.
From New.golang Require Import theory.
From New.code Require Import github_com.mit_pdos.perennial.goose.testdata.examples.channel.
Import channel_examples.

Set Default Proof Using "Type".

(** * Three-way leader election

    The example from §2.4 of the Mixtris paper, over Go channels. Three
    participants race on a mixed-choice [select]; mixed choice guarantees at
    most one exchange happens, hence at most one leader.

    The paper hands the leader a reference [l] and has it run [free l], so that
    a second election would be a use-after-free. Go has no [free], but it does
    have a single-use operation with the same character: closing an
    already-closed channel panics. So the leader's privilege here is the
    permission to [close done], and [{True} ThreeWayElection {True}] certifies
    leader uniqueness by way of Iris's adequacy theorem, exactly as in the
    paper.

    Note that [done] is an ordinary Go channel, not part of the Mixtris session:
    the session's own edge channels are never closed, and [chan_slot_inv] rules
    the closed state out entirely. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : channel_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context `{!mixtrisG Σ w64}.

(** Participant [i]'s protocol: either send [v] to its clockwise neighbour
    [nxt], or receive from its counter-clockwise neighbour [prv] and be handed
    the leader's resources [P]. *)
Definition party_prot (nxt prv : nat) (v : w64) (P : iProp Σ) : iProto Σ w64 :=
  ((<![nxt]> MSG v; END) <+> (<?[prv] w> MSG w {{ P }}; END))%proto.

(** Let choice selection see through the definition. *)
Global Instance party_prot_unfold nxt prv v P :
  ProtoUnfold (party_prot nxt prv v P)
    ((<![nxt]> MSG v; END) <+> (<?[prv] w> MSG w {{ P }}; END))%proto.
Proof. apply proto_unfold_eq. by rewrite /party_prot. Qed.
(** Required: without it, resolution unfolds [party_prot] inside the instance's
    own premise, matches this instance again, and loops. *)
Global Typeclasses Opaque party_prot.

(** ** Protocol consistency

    Consistency is proved by simulating every possible communication, as in the
    paper. Mixed choice makes the branching factor larger than for a non-mixed
    protocol pool, but for three participants the simulation is short: three
    possible exchanges, each leading to a pool in which only one participant is
    left with anything to do. *)

Local Lemma elem_of_END_False (a : action) (m : iMsg Σ w64) :
  iProto_elem_of (<a> m)%proto (END : iProto Σ w64)%proto ⊢ False.
Proof.
  iIntros "H". iDestruct (iProto_elem_of_end_inv_r with "H") as "H".
  by iApply iProto_message_end_equivI.
Qed.

(** Membership in a party protocol pins the action down to one of its two
    choices. *)
Local Lemma elem_of_party_inv (nxt prv : nat) (v : w64) (P : iProp Σ) a m :
  iProto_elem_of (<a> m)%proto (party_prot nxt prv v P) ⊢
    (⌜a = (Send, nxt)⌝ ∧ (MSG v; END)%msg ≡ m) ∨
    (⌜a = (Recv, prv)⌝ ∧ (∃ w, MSG w {{ P }}; END)%msg ≡ m).
Proof.
  rewrite /party_prot. iIntros "H".
  iDestruct (iProto_elem_of_union_inv with "H") as "[H|H]".
  - iLeft. iDestruct (iProto_elem_of_message_inv with "H") as "[%Ha $]".
    by rewrite Ha.
  - iRight. iDestruct (iProto_elem_of_message_inv with "H") as "[%Ha $]".
    by rewrite Ha.
Qed.

(** A pool in which at most one participant still has a protocol is consistent:
    that participant can only ever talk to someone who has already finished. *)
Local Lemma consistent_one (n k nxt prv : nat) (v : w64) (P : iProp Σ)
    (ps : list (iProto Σ w64)) :
  length ps = n → nxt < n → prv < n →
  ps !! k = Some (party_prot nxt prv v P) →
  (∀ i, i ≠ k → ps !!! i = (END : iProto Σ w64)%proto) →
  ⊢ iProto_consistent ps.
Proof.
  intros Hlen Hnxt Hprv Hk Hrest.
  rewrite iProto_consistent_unfold. iSplit.
  - iIntros (i j a m) "Hin".
    destruct (decide (i = k)) as [->|Hne]; last first.
    { rewrite Hrest //. by iDestruct (elem_of_END_False with "Hin") as "[]". }
    rewrite (list_lookup_total_correct _ _ _ Hk).
    iDestruct (elem_of_party_inv with "Hin") as "[[%Ha _]|[%Ha _]]";
      simplify_eq; iPureIntro; apply lookup_lt_is_Some_2; lia.
  - iIntros (i j m1 m2) "%Hneq Hin1 Hin2".
    destruct (decide (i = k)) as [->|Hne]; last first.
    { rewrite Hrest //. by iDestruct (elem_of_END_False with "Hin1") as "[]". }
    rewrite (list_lookup_total_correct _ _ _ Hk).
    iDestruct (elem_of_party_inv with "Hin1") as "[[%Ha _]|[%Ha _]]";
      simplify_eq.
    rewrite Hrest; last done.
    by iDestruct (elem_of_END_False with "Hin2") as "[]".
Qed.

(** Unfolding and building message payloads, wrapped up so that proofs do not
    have to rewrite with the seals directly. *)
Local Lemma iMsg_base_inv (w : w64) (P : iProp Σ) (q : iProto Σ w64) v lp :
  iMsg_car (MSG w {{ P }}; q)%msg v lp ⊢ ⌜w = v⌝ ∗ (Next q ≡ lp) ∗ P.
Proof. rewrite iMsg_base_eq /=. auto. Qed.

Local Lemma iMsg_base_intro (w : w64) (P : iProp Σ) (q : iProto Σ w64) :
  P ⊢ iMsg_car (MSG w {{ P }}; q)%msg w (Next q).
Proof. rewrite iMsg_base_eq /=. auto. Qed.

Local Lemma iMsg_exist_intro {A} (m : A → iMsg Σ w64) (x : A) v lp :
  iMsg_car (m x) v lp ⊢ iMsg_car (iMsg_exist m) v lp.
Proof. rewrite iMsg_exist_eq /=. eauto. Qed.

(** The pool of the three ring participants. *)
Definition election_pool (P : iProp Σ) : list (iProto Σ w64) :=
  [party_prot 1 2 (W64 0) P; party_prot 2 0 (W64 1) P; party_prot 0 1 (W64 2) P].

(** Only one of the three exchanges can happen, so [P] — the leader's
    resources — is handed out at most once. *)
Lemma election_consistent (P : iProp Σ) : P -∗ iProto_consistent (election_pool P).
Proof.
  iIntros "HP".
  rewrite iProto_consistent_unfold. iSplit.
  - iIntros (i j a m) "Hin".
    destruct i as [|[|[|i]]]; simpl;
      last by iDestruct (elem_of_END_False with "Hin") as "[]".
    all: iDestruct (elem_of_party_inv with "Hin") as "[[%Ha _]|[%Ha _]]";
         simplify_eq; iPureIntro; apply lookup_lt_is_Some_2; simpl; lia.
  - iIntros (i j m1 m2) "%Hneq Hin1 Hin2".
    destruct i as [|[|[|i]]]; simpl;
      last by iDestruct (elem_of_END_False with "Hin1") as "[]".
    (* A sends to B *)
    + iDestruct (elem_of_party_inv with "Hin1") as "[[%Ha #Hm1eq]|[%Ha _]]";
        simplify_eq. simpl.
      iDestruct (elem_of_party_inv with "Hin2") as "[[%Ha _]|[%Ha #Hm2eq]]";
        simplify_eq.
      iIntros (v p1) "Hm1". rewrite !iMsg_equivI.
      iDestruct ("Hm1eq" $! v (Next p1)) as "Hm1eq2".
      iRewrite -"Hm1eq2" in "Hm1".
      iDestruct (iMsg_base_inv with "Hm1") as "(_ & #Hp1 & _)".
      iExists (END : iProto Σ w64)%proto. iSplitL "HP".
      { iDestruct ("Hm2eq" $! v (Next (END : iProto Σ w64)%proto)) as "Hm2eq2".
        iRewrite -"Hm2eq2". iApply (iMsg_exist_intro _ v). by iApply iMsg_base_intro. }
      rewrite later_equivI_1. iNext. iRewrite -"Hp1". simpl.
      iApply (consistent_one 3 2%nat 0%nat 1%nat (W64 2) P); simpl; try lia; try done.
      intros i' ?. repeat (destruct i' as [|i']; simpl; try done).
    (* B sends to C *)
    + iDestruct (elem_of_party_inv with "Hin1") as "[[%Ha #Hm1eq]|[%Ha _]]";
        simplify_eq. simpl.
      iDestruct (elem_of_party_inv with "Hin2") as "[[%Ha _]|[%Ha #Hm2eq]]";
        simplify_eq.
      iIntros (v p1) "Hm1". rewrite !iMsg_equivI.
      iDestruct ("Hm1eq" $! v (Next p1)) as "Hm1eq2".
      iRewrite -"Hm1eq2" in "Hm1".
      iDestruct (iMsg_base_inv with "Hm1") as "(_ & #Hp1 & _)".
      iExists (END : iProto Σ w64)%proto. iSplitL "HP".
      { iDestruct ("Hm2eq" $! v (Next (END : iProto Σ w64)%proto)) as "Hm2eq2".
        iRewrite -"Hm2eq2". iApply (iMsg_exist_intro _ v). by iApply iMsg_base_intro. }
      rewrite later_equivI_1. iNext. iRewrite -"Hp1". simpl.
      iApply (consistent_one 3 0%nat 1%nat 2%nat (W64 0) P); simpl; try lia; try done.
      intros i' ?. repeat (destruct i' as [|i']; simpl; try done).
    (* C sends to A *)
    + iDestruct (elem_of_party_inv with "Hin1") as "[[%Ha #Hm1eq]|[%Ha _]]";
        simplify_eq. simpl.
      iDestruct (elem_of_party_inv with "Hin2") as "[[%Ha _]|[%Ha #Hm2eq]]";
        simplify_eq.
      iIntros (v p1) "Hm1". rewrite !iMsg_equivI.
      iDestruct ("Hm1eq" $! v (Next p1)) as "Hm1eq2".
      iRewrite -"Hm1eq2" in "Hm1".
      iDestruct (iMsg_base_inv with "Hm1") as "(_ & #Hp1 & _)".
      iExists (END : iProto Σ w64)%proto. iSplitL "HP".
      { iDestruct ("Hm2eq" $! v (Next (END : iProto Σ w64)%proto)) as "Hm2eq2".
        iRewrite -"Hm2eq2". iApply (iMsg_exist_intro _ v). by iApply iMsg_base_intro. }
      rewrite later_equivI_1. iNext. iRewrite -"Hp1". simpl.
      iApply (consistent_one 3 1%nat 2%nat 0%nat (W64 1) P); simpl; try lia; try done.
      intros i' ?. repeat (destruct i' as [|i']; simpl; try done).
Qed.

(** ** One participant *)

(** The leader's privilege: permission to close [done]. Closing a closed
    channel is a panic, and [close_au] reflects that by demanding [False] in the
    [Closed] state -- [close_closed_au] demands [False] there -- so this resource
    is exactly as single-use as the paper's
    [l ↦ −] is for [free l]. *)
Definition leader_privilege (γdone : chan_names) : iProp Σ :=
  own_chan γdone w64 chanstate.Idle.

Lemma wp_ThreeWayElectionParty
    γ (send recv done : chan.t) γsend γrecv γdone (i nxt prv : nat) (id : w64) :
  {{{ is_pkg_init channel_examples ∗
      is_chan done γdone w64 ∗
      is_edge_chan γ send γsend i nxt ∗
      is_edge_chan γ recv γrecv prv i ∗
      i ↣[γ] party_prot nxt prv id (leader_privilege γdone) }}}
    @! channel_examples.ThreeWayElectionParty #send #recv #id #done
  {{{ RET #(); True }}}.
Proof using W.
  wp_start as "(#Hdone & #Hsend & #Hrecv & Hown)".
  wp_auto_lc 4.
  wp_apply chan.wp_select_blocking. simpl.
  iSplit.
  { (* Send clause: we lose the election. The [Send] choice towards [nxt] is
       found by typeclass search from the channel's edge. *)
    mixtris_send_case with "[$] Hsend Hown [-]".
    iSplitR; [done|]. iSplitR; [done|].
    iIntros "!> _". wp_auto. by iApply "HΦ". }
  iSplitL; last done.
  { (* Receive clause: we are the leader, and get to close [done]. *)
    mixtris_recv_case with "[$] Hrecv Hown [-]".
    iIntros "!>" (w) "Hpriv _".
    wp_auto. wp_apply (chan.wp_close with "Hdone").
    iIntros "_". rewrite /close_au. repeat iSplit.
    - (* close_idle_au: the privilege is the [Idle] half, so spend it here *)
      iIntros "[Hlc Himpl]".
      iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
      iMod (own_chan_halves_update (@chanstate.Closed w64 []) with "Hpriv Himpl")
        as "[H1 H2]"; [ simpl in Hcap |- *; lia | ].
      iModIntro. iFrame "H2". wp_auto. by iApply "HΦ".
    - (* close_buf_au: [done] is unbuffered *)
      iIntros (buf) "[Hlc Himpl]".
      iDestruct (own_chan_agree with "Hpriv Himpl") as %Hbad. done.
    - (* close_closed_au: the privilege is single-use, so [done] is still open *)
      iIntros (drain) "[Hlc Himpl]".
      iDestruct (own_chan_agree with "Hpriv Himpl") as %Hbad. done. }
Qed.

(** ** The whole program

    The specification is [{True} ThreeWayElection {True}], exactly as in the
    paper. All of its content is in Iris's adequacy theorem: a provable weakest
    precondition means the program is safe, and the program contains a
    [close done] that panics if reached twice. So this triple says that the
    election elects at most one leader. *)
Lemma wp_ThreeWayElection :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.ThreeWayElection #()
  {{{ RET #(); True }}}.
Proof using W mixtrisG0.
  wp_start. wp_auto.
  wp_apply chan.wp_make1. iIntros (ab γab) "(#Hab & _ & Hab_own)". wp_auto.
  wp_apply chan.wp_make1. iIntros (bc γbc) "(#Hbc & _ & Hbc_own)". wp_auto.
  wp_apply chan.wp_make1. iIntros (ca γca) "(#Hca & _ & Hca_own)". wp_auto.
  wp_apply chan.wp_make1. iIntros (dn γdn) "(#Hdn & _ & Hdn_own)". wp_auto.
  (* The pool of three protocols is consistent, using the leader's privilege as
     the resource that only the elected leader receives. *)
  iMod (mixtris_init _ (election_pool (leader_privilege γdn)) with "[Hdn_own]")
    as (γ) "[%Hlen Hown]".
  { iNext. by iApply election_consistent. }
  (* One channel per directed edge of the ring, assigned in one step. *)
  iMod (mixtris_chans_init _ γ
          {[ (0%nat, 1%nat) := (ab, γab);
             (1%nat, 2%nat) := (bc, γbc);
             (2%nat, 0%nat) := (ca, γca) ]}
         with "[Hab_own Hbc_own Hca_own]") as "#Hedges".
  { rewrite !big_sepM_insert //= ?big_sepM_singleton; try by rewrite lookup_insert_None.
    by iFrame "∗#". }
  iDestruct (is_edge_chans_lookup _ _ 0 1 with "Hedges") as "#Hab_edge"; [by simplify_map_eq|].
  iDestruct (is_edge_chans_lookup _ _ 1 2 with "Hedges") as "#Hbc_edge"; [by simplify_map_eq|].
  iDestruct (is_edge_chans_lookup _ _ 2 0 with "Hedges") as "#Hca_edge"; [by simplify_map_eq|].
  iDestruct "Hown" as "(H0 & H1 & H2 & _)". simpl.
  iPersist "ab bc ca done".
  wp_apply (wp_fork with "[H0]").
  { wp_auto. wp_apply (wp_ThreeWayElectionParty with "[$H0]"); [|done].
    iFrame "#". }
  wp_apply (wp_fork with "[H1]").
  { wp_apply (wp_ThreeWayElectionParty with "[$H1]"); [|done].
    iFrame "#". }
  wp_apply (wp_fork with "[H2]").
  { wp_apply (wp_ThreeWayElectionParty with "[$H2]"); [|done].
    iFrame "#". }
  by iApply "HΦ".
Qed.

End proof.
