From Perennial.Helpers Require Import List.
From New.golang.defn Require Export chan.
From New.golang.theory.chan.au_spec
  Require Export chan_au_base.
From New.golang.theory.chan.au_spec
  Require Import chan_init chan_au_send chan_au_new chan_au_recv.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Export pre.
From Perennial Require Import base.

Open Scope Z_scope.

Set Default Proof Using "Type".

Module chan.

#[local] Transparent chan.receive chan.send chan.for_range.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.

Global Instance pure_wp_chan_for_range (c : chan.t) elem_type (body : val) :
  PureWp True (chan.for_range elem_type #c body)%E
    ((for: (λ: <>, #true)%V; (λ: <>, #())%V :=
        λ: <>,
          let: ("v", "ok") := chan.receive elem_type #c in
          if: "ok" then
            body "v"
          else
            (* channel is closed *)
            break: #()
    )).
Proof using sem_fn + pre_sem + sem.
  iIntros (?????) "HΦ". unfold chan.for_range.
  wp_pure_lc "?". wp_pure. wp_pure. by iApply "HΦ".
Qed.

(* These are carefully ordered so that when the lemmas are applied, typeclass
   search can fill everything in. Do not change the order or add new things here
   without considering how it will affect TC search when lemmas are applied. *)
Context [ct dir t] [Hunder : ct ↓u go.ChannelType dir t].
Context [V] `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].

Collection W := sem_fn + pre_sem + sem + IntoValTyped0.

Implicit Types (ch : loc) (v : V) (γ : chan_names).

Lemma wp_make2 (cap : w64) :
  {{{ ⌜ 0 ≤ sint.Z cap ⌝ }}}
    #(functions go.make2 [ct]) #cap
  {{{ ch γ, RET #ch;
      is_chan ch γ V ∗
      ⌜ chan_cap γ = cap ⌝ ∗
      own_chan γ V (if decide (cap = W64 0) then chanstate.Idle else chanstate.Buffered (@nil V))
  }}}.
Proof using W Hunder IntoValTyped0.
  wp_start as "%Hle".
  wp_apply wp_NewChannel; first done.
  iFrame.
Qed.

Lemma wp_make1 :
  {{{ True }}}
    #(functions go.make1 [ct]) #()
  {{{ ch γ, RET #ch;
      is_chan ch γ V ∗
      ⌜ chan_cap γ = W64 0 ⌝ ∗
      own_chan γ V chanstate.Idle
  }}}.
Proof using W Hunder IntoValTyped0.
  wp_start.
  wp_apply wp_make2; first done.
  iFrame.
Qed.

Lemma wp_send ch v γ:
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au γ V v (Φ #())) -∗
  WP chan.send t #ch #v {{ Φ }}.
Proof using W.
  wp_start as "#Hch".
  wp_apply (wp_Send with "[$]").
  iFrame.
Qed.

Lemma wp_close ch γ :
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au γ V (Φ #())) -∗
  WP #(functions go.close [ct]) #ch {{ Φ }}.
Proof using W Hunder.
  wp_start as "#Hch".
  wp_apply (wp_Close with "[$]").
  iFrame.
Qed.

Lemma wp_receive ch γ :
  ∀ Φ,
  is_chan ch γ V -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ recv_au γ V (λ v ok, Φ (#v, #ok)%V)) -∗
  WP chan.receive t #ch {{ Φ }}.
Proof using W.
  wp_start as "#Hch".
  wp_apply (wp_Receive with "[$]").
  iFrame.
Qed.

Lemma wp_cap ch γ :
  {{{ is_chan ch γ V }}}
    #(functions go.cap [ct]) #ch
  {{{ RET #(chan_cap γ); True }}}.
Proof using W Hunder.
  wp_start as "#Hch".
  wp_apply (wp_Cap with "[$Hch]").
  by iApply "HΦ".
Qed.

End proof.

Section select_proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.

(** ** Per-clause obligations

    Every select rule asks the same thing of each communication clause: name the
    channel, its element type and its ghost name, prove the clause's expressions
    really denote that channel and that value, and supply an atomic update whose
    success continuation is the clause's handler.  The three definitions below
    differ only in *which* atomic update is demanded. *)

(** Blocking select: the clause must be prepared for any reachable transition. *)
Definition select_clause_blocking (Ψ : val → iProp Σ) (c : comm_clause) : iProp Σ :=
  match c with
  | CommClause (SendCase t chan_expr send_val) handler =>
      ∃ V ch γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ send_val = #v ∧ chan_expr = #ch ⌝ ∗
        is_chan ch γ V ∗
        send_au γ V v (WP handler {{ Ψ }})
  | CommClause (RecvCase t chan_expr) handler =>
      ∃ V ch γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ chan_expr = #ch ⌝ ∗
        is_chan ch γ V ∗
        recv_au γ V (λ v ok, WP handler (#v, #ok)%V {{ Ψ }})
  end.

(** Nonblocking select: a clause may also decline outright, keeping nothing. *)
Definition select_clause_nonblocking (Ψ : val → iProp Σ) (c : comm_clause) : iProp Σ :=
  match c with
  | CommClause (SendCase t chan_expr send_val) handler =>
      ∃ V ch γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ send_val = #v ∧ chan_expr = #ch ⌝ ∗
        is_chan ch γ V ∗
        nonblocking_send_au γ V v (WP handler {{ Ψ }}) True
  | CommClause (RecvCase t chan_expr) handler =>
      ∃ V ch γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ chan_expr = #ch ⌝ ∗
        is_chan ch γ V ∗
        nonblocking_recv_au γ V (λ v ok, WP handler (#v, #ok)%V {{ Ψ }}) True
  end.

(** Nonblocking select, strong form: declining is no longer free.  The clause
    must look at the channel and hand back [Q] as evidence it was not ready. *)
Definition select_clause_nonblocking_alt (Ψ : val → iProp Σ) (Q : iProp Σ)
    (c : comm_clause) : iProp Σ :=
  match c with
  | CommClause (SendCase t chan_expr send_val) handler =>
      ∃ V ch γ (v : V) `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ send_val = #v ∧ chan_expr = #ch ⌝ ∗
        is_chan ch γ V ∗
        nonblocking_send_au_alt γ V v (WP handler {{ Ψ }}) Q
  | CommClause (RecvCase t chan_expr) handler =>
      ∃ V ch γ `(!ZeroVal V) `(!TypedPointsto V) `(!IntoValTyped V t),
        ⌜ chan_expr = #ch ⌝ ∗
        is_chan ch γ V ∗
        nonblocking_recv_au_alt γ V (λ v ok, WP handler (#v, #ok)%V {{ Ψ }}) Q
  end.

Local Set Default Proof Using "All".

(* The lemmas use Ψ because the original client-provided [send_au]/[recv_au] will
   have some specific postcondition predicate. We don't want to force the caller
   to transform that into a [send_au] of a different postcondition. So, these
   lemmas are written to take a wand that turns Ψ into Φ. *)
Local Lemma wp_try_comm_clause_blocking c Ψ :
  ∀ Φ,
  select_clause_blocking Ψ c ∧ (Φ (#(), #false)%V) -∗
  (∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_comm_clause c #true {{ Φ }}.
Proof.
  destruct c as [[|]]; simpl.
  - iIntros (Φ) "HΦ Hwand".
    wp_call.
    repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V send_chan γ v' ? ? ?) "HΦ".
    iNamed "HΦ".
    iAssert (⌜ e = #v' ∧ ch = #send_chan ⌝ ∗ is_chan send_chan γ V)%I with "[-]" as "[[-> ->] #?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TrySend with "[$]").
    iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      rewrite /send_au. repeat iSplit.
      * (* send_fast_path_au *)
        iLeft in "Hau". iIntros "[Hlc Hoc]".
        iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont"). iIntros (v) "HΦ".
        wp_auto. iApply "Hwand". iFrame.
      * (* send_slow_path_au *)
        iRight in "Hau". iLeft in "Hau".
        iIntros "[Hlc Hoc]".
        iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hau]". iModIntro.
        iIntros "[Hlc Hoc]".
        iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
        wp_auto. wp_apply (wp_wand with "Hcont") as (v) "HΦ". iApply "Hwand". iFrame.
      * (* send_enq_au *)
        iRight in "Hau". iRight in "Hau". iLeft in "Hau".
        iIntros (buf) "(Hlc & %Hlt & Hoc)".
        iMod ("Hau" $! buf with "[$Hlc $Hoc]") as "[$ Hcont]"; first (iPureIntro; lia).
        iModIntro. wp_auto.
        wp_apply (wp_wand with "Hcont") as (?) "HΦ". iApply "Hwand". iFrame.
      * (* send_closed_au *)
        iRight in "Hau". iRight in "Hau". iRight in "Hau". iFrame.
    + wp_auto. iRight in "HΦ". done.
  - iIntros (Φ) "HΦ Hwand".
    wp_call.
    repeat setoid_rewrite bi.and_exist_r.
    iDestruct "HΦ" as (V recv_chan γ ? ? ?) "HΦ".
    iAssert (⌜ ch = #recv_chan ⌝ ∗ is_chan recv_chan γ V)%I with "[-]" as "#[-> ?]".
    { iLeft in "HΦ". iDestruct "HΦ" as "(% & ? & _)". iFrame "∗%". }
    simpl. wp_auto.
    wp_apply (wp_TryReceive with "[$]").
    iSplit.
    + iLeft in "HΦ". iDestruct "HΦ" as "(_ & _ & Hau)".
      rewrite /recv_au. repeat iSplit.
      * (* recv_fast_path_au *)
        iLeft in "Hau". iIntros (w) "[Hlc Hoc]".
        iMod ("Hau" $! w with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
        wp_auto. wp_bind (body _).
        iApply (wp_wand with "Hcont"). iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * (* recv_slow_path_au *)
        iRight in "Hau". iLeft in "Hau".
        iIntros "[Hlc Hoc]".
        iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hau]". iModIntro.
        iIntros (w) "[Hlc Hoc]".
        iMod ("Hau" $! w with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
        wp_auto. wp_bind (body _).
        iApply (wp_wand with "Hcont"). iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * (* recv_deq_au *)
        iRight in "Hau". iRight in "Hau". iLeft in "Hau".
        iIntros (w rest) "[Hlc Hoc]".
        iMod ("Hau" $! w rest with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
        wp_auto. wp_bind (body _).
        iApply (wp_wand with "Hcont"). iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * (* recv_drain_au *)
        iRight in "Hau". iRight in "Hau". iRight in "Hau". iLeft in "Hau".
        iIntros (w rest) "[Hlc Hoc]".
        iMod ("Hau" $! w rest with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
        wp_auto. wp_bind (body _).
        iApply (wp_wand with "Hcont"). iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
      * (* recv_closed_au *)
        iRight in "Hau". iRight in "Hau". iRight in "Hau". iRight in "Hau".
        iIntros "[Hlc Hoc]".
        iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
        wp_auto. wp_bind (body _).
        iApply (wp_wand with "Hcont"). iIntros (?) "HΦ". wp_auto. iApply "Hwand". iFrame.
    + wp_auto. iRight in "HΦ". iFrame.
Qed.

Local Lemma wp_try_select_blocking (clauses : list comm_clause) :
  ∀ Ψ Φ,
  ([∧ list] c ∈ clauses, select_clause_blocking Ψ c) ∧ (Φ (#(), #false)%V) -∗
  □(∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_select true clauses {{ Φ }}.
Proof.
  simpl. iIntros (Ψ Φ) "HΦ #Hwand".
  iLöb as "IH" forall (clauses).
  destruct clauses.
  { wp_auto. iRight in "HΦ". iApply "HΦ". }
  simpl.
  wp_apply (wp_try_comm_clause_blocking _ Ψ with "[-Hwand] [Hwand]").
  2:{ iIntros (?) "HΨ". wp_auto. iApply "Hwand". iFrame. }
  iSplit.
  { simpl. iLeft in "HΦ". iLeft in "HΦ". iFrame. }
  wp_auto. iApply ("IH" with "[HΦ]"); try iFrame.
  iSplit.
  - iLeft in "HΦ". simpl. iRight in "HΦ". iFrame.
  - iRight in "HΦ". done.
Qed.

Local Lemma wp_SelectStmt_blocking {stk E} clauses Φ :
  (∀ clauses',
     ⌜ clauses' ≡ₚ clauses ⌝ -∗
     WP (let: ("v", "succeeded") := chan.try_select true clauses' in
          if: "succeeded" then "v"
          else (λ: <>, SelectStmt (SelectStmtClauses None clauses))%V #()) @ stk; E {{ Φ }}
  ) -∗
  WP SelectStmt (SelectStmtClausesV None clauses) @ stk; E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_apply (wp_GoInstruction []).
  { intros. eexists. repeat econstructor. erewrite go.chan_select_blocking.
    exists clauses; split; done. }
  simpl. iIntros "* %Hstep". rewrite go.chan_select_blocking in Hstep.
  destruct Hstep as [[? []]]. subst. iIntros "_ $ !>". simpl. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_select_blocking (clauses : list comm_clause) :
  ∀ Φ,
  ([∧ list] c ∈ clauses, select_clause_blocking Φ c) -∗
  WP SelectStmt (SelectStmtClausesV None clauses) {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  iLöb as "IH" forall (Φ).
  wp_apply wp_SelectStmt_blocking.
  iIntros (clauses') "%Hperm".
  wp_apply (wp_try_select_blocking with "[-]").
  - rewrite Hperm.
    iSplit; first iFrame.
    wp_auto. iApply "IH". iFrame.
  - iModIntro. iIntros "% HΦ". wp_auto. iFrame.
Qed.

(** Pull persistent content out from under an [∧] without spending the [∧]:
    needed to read a clause's witnesses out of the plain select precondition
    while still having it available for the not-ready payload. *)
Local Lemma and_sep_persistent (R Q P : iProp Σ) `{!Persistent R} :
  (R ∗ Q) ∧ P ⊢ R ∗ (Q ∧ P).
Proof.
  iIntros "H". iApply bi.persistent_and_sep_1. iSplit.
  - iDestruct "H" as "[[$ _] _]".
  - iSplit.
    + iDestruct "H" as "[[_ $] _]".
    + iDestruct "H" as "[_ $]".
Qed.

Local Lemma wp_SelectStmt_nonblocking {stk E} (def : expr) clauses Φ :
  (∀ clauses' : list comm_clause,
     ⌜clauses' ≡ₚ clauses⌝ -∗
     WP (let: "__p" := chan.try_select false clauses' in
         let: "v" := Fst "__p" in
         let: "succeeded" := Snd "__p" in
         if: "succeeded" then "v" else (λ: <>, def)%V #()) @ stk; E {{ v, Φ v }}) -∗
  WP SelectStmt (SelectStmtClausesV (Some def) clauses) @ stk; E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_apply (wp_GoInstruction []).
  { intros. eexists. repeat econstructor. erewrite go.chan_select_nonblocking.
    exists clauses; split; done. }
  simpl. iIntros "* %Hstep". rewrite go.chan_select_nonblocking in Hstep.
  destruct Hstep as [[? []]]. subst. iIntros "_ $ !>". simpl. wp_pures. by iApply "HΦ".
Qed.

Local Lemma wp_try_select_case_nonblocking_alt c Ψ Ψnotready :
  ∀ Φ,
  select_clause_nonblocking_alt Ψ Ψnotready c -∗
  ((∀ retv, Ψ retv -∗ Φ (retv, #true)%V) ∧ (Ψnotready -∗ Φ (#(), #false)%V)) -∗
  WP chan.try_comm_clause c #false {{ Φ }}.
Proof.
  destruct c as [[|]]; simpl.
  - iIntros (Φ) "HΦ Hwand".
    wp_call.
    iNamed "HΦ". iDestruct "HΦ" as "([-> ->] & #? & Hau)". simpl. wp_auto.
    wp_apply (wp_TrySend with "[$]").
    iRight.
    rewrite {2}/nonblocking_send_au_alt. repeat iSplit.
    + (* send_fast_path_au *)
      iLeft in "Hau". iIntros "[Hlc Hoc]".
      iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro. wp_auto.
      wp_apply (wp_wand with "Hcont"). iIntros (?) "HΨ".
      iLeft in "Hwand". wp_auto. iApply "Hwand". iFrame.
    + (* send_enq_au *)
      iRight in "Hau". iLeft in "Hau". iIntros (buf) "(Hlc & %Hlt & Hoc)".
      iMod ("Hau" $! buf with "[$Hlc $Hoc]") as "[$ Hcont]"; first (iPureIntro; lia).
      iModIntro. wp_auto.
      wp_apply (wp_wand with "Hcont"). iIntros (?) "HΨ".
      iLeft in "Hwand". wp_auto. iApply "Hwand". iFrame.
    + (* send_closed_au *)
      iRight in "Hau". iRight in "Hau". iLeft in "Hau". iFrame.
    + (* send_not_ready_au *)
      iRight in "Hau". iRight in "Hau". iRight in "Hau".
      iIntros (s) "(Hlc & %Hnr & Hoc)".
      iMod ("Hau" $! s with "[$Hlc $Hoc]") as "[$ Hnr]"; first (iPureIntro; done).
      iModIntro. wp_auto.
      iRight in "Hwand". iApply ("Hwand" with "[$]").
  - iIntros (Φ) "HΦ Hwand".
    wp_call.
    iNamed "HΦ". iDestruct "HΦ" as "(-> & #? & Hau)". simpl. wp_auto.
    wp_apply (wp_TryReceive with "[$]").
    iRight.
    rewrite {2}/nonblocking_recv_au_alt. repeat iSplit.
    + (* recv_fast_path_au *)
      iLeft in "Hau". iIntros (w) "[Hlc Hoc]".
      iMod ("Hau" $! w with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
      wp_auto. wp_bind (body _). iApply (wp_wand with "Hcont").
      iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
    + (* recv_deq_au *)
      iRight in "Hau". iLeft in "Hau". iIntros (w rest) "[Hlc Hoc]".
      iMod ("Hau" $! w rest with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
      wp_auto. wp_bind (body _). iApply (wp_wand with "Hcont").
      iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
    + (* recv_drain_au *)
      iRight in "Hau". iRight in "Hau". iLeft in "Hau". iIntros (w rest) "[Hlc Hoc]".
      iMod ("Hau" $! w rest with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
      wp_auto. wp_bind (body _). iApply (wp_wand with "Hcont").
      iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
    + (* recv_closed_au *)
      iRight in "Hau". iRight in "Hau". iRight in "Hau". iLeft in "Hau".
      iIntros "[Hlc Hoc]".
      iMod ("Hau" with "[$Hlc $Hoc]") as "[$ Hcont]". iModIntro.
      wp_auto. wp_bind (body _). iApply (wp_wand with "Hcont").
      iIntros (?) "HΦ". wp_auto. by iApply "Hwand".
    + (* recv_not_ready_au *)
      iRight in "Hau". iRight in "Hau". iRight in "Hau". iRight in "Hau".
      iIntros (s) "(Hlc & %Hnr & Hoc)".
      iMod ("Hau" $! s with "[$Hlc $Hoc]") as "[$ Hnr]"; first (iPureIntro; done).
      iModIntro. wp_auto. iRight in "Hwand". iApply ("Hwand" with "[$]").
Qed.

Local Lemma wp_try_select_nonblocking_alt Φnrs (clauses : list comm_clause) :
  ∀ P Ψ Φ,
  ([∗ list] c; Φnr ∈ clauses; Φnrs,
     P -∗ select_clause_nonblocking_alt Ψ (P ∗ Φnr) c) -∗
  P -∗
  (P -∗ [∗] Φnrs -∗ (Φ (#(), #false)%V)) -∗
  □(∀ retv, Ψ retv -∗ Φ (retv, #true)%V) -∗
  WP chan.try_select false clauses {{ Φ }}.
Proof.
  simpl. iIntros (P Ψ Φ) "HΦ HP Hwandnr #Hwand".
  iLöb as "IH" forall (clauses Φnrs).
  destruct clauses.
  { wp_auto. iDestruct (big_sepL2_nil_inv_l with "HΦ") as %?. subst.
    iApply ("Hwandnr" with "[$]"). done. }
  simpl.
  iDestruct (big_sepL2_cons_inv_l with "HΦ") as (Φnr Φnrs' Heq) "[H HΦ]". subst.
  wp_apply (wp_try_select_case_nonblocking_alt _ Ψ (P ∗ Φnr) with "[HP H]").
  { iDestruct ("H" with "HP") as "H". simpl. iFrame. }
  iSplit.
  - iIntros "% HΨ". wp_auto. iApply "Hwand". iFrame.
  - iIntros "[HP Hnr]". wp_auto.
    wp_apply ("IH" with "[HΦ] [$]"); try iFrame.
    simpl. iIntros "P Hnrs". iApply ("Hwandnr" with "[$] [$]").
Qed.

(** This specification requires proving _separate_ atomic updates for each case,
    and requires a proposition [P] to represent the resources that are available
    to ALL of the handlers (rather than having to be split up among the cases).
    Users should do:
     wp_apply (wp_select_nonblocking_alt [Φnr1; Φnr2;] with
               "[list of props for proving atomic updates] [-]"); [|iNamedAccu|].

    The reason this uses [au1 ∗ au2 ∗ ...] instead of [au1 ∧ au2 ∧ ...] is
    because in the event that the default case is chosen, ALL of the case's
    atomic updates will have to be fired to produce witnesses that all the cases
    were not ready ([[∗] Φnrs]). *)
Lemma wp_select_nonblocking_alt Φnrs P (clauses : list comm_clause) (def : expr) :
  ∀ Φ,
  ([∗ list] c; Φnr ∈ clauses; Φnrs,
     P -∗ select_clause_nonblocking_alt Φ (P ∗ Φnr) c) -∗
  P -∗
  (P -∗ [∗] Φnrs -∗ WP def {{ Φ }}) -∗
  WP SelectStmt (SelectStmtClausesV (Some def) clauses) {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases HP Hdef".
  wp_apply wp_SelectStmt_nonblocking.
  iIntros (clauses') "%Hperm".
  iDestruct (big_sepL2_alt with "Hcases") as "[%Hlen Hcases]".
  destruct (permutation_zip clauses clauses' Φnrs) as [Φnrs' [Hperm_Φnrs Hperm_zip]]; [done|done|].
  rewrite Hperm_zip.
  rewrite Hperm_Φnrs.
  wp_apply (wp_try_select_nonblocking_alt with "[Hcases] HP [Hdef]").
  - iApply big_sepL2_alt.
    iFrame "Hcases".
    apply Permutation_length in Hperm, Hperm_Φnrs.
    iPureIntro. lia.
  - iIntros "HP Hnrs". wp_auto. iApply ("Hdef" with "[$] [$]").
  - iModIntro. iIntros. wp_auto. iFrame.
Qed.

(** The plain nonblocking select spec is a corollary of the [Alt] one: take the
    private precondition [P] to be the whole plain precondition and every [Φnr]
    to be [True].  Callers never see [P]. *)
Lemma wp_select_nonblocking (clauses : list comm_clause) def :
  ∀ Φ,
  ([∧ list] c ∈ clauses, select_clause_nonblocking Φ c) ∧ WP def {{ Φ }} -∗
  WP SelectStmt (SelectStmtClausesV (Some def) clauses) {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  set (P := (([∧ list] c ∈ clauses, select_clause_nonblocking Φ c) ∧ WP def {{ Φ }})%I).
  iApply (wp_select_nonblocking_alt (replicate (length clauses) True%I) P clauses def
           with "[] Hcases []").
  - iApply big_sepL2_intro; first by rewrite length_replicate.
    iIntros "!>" (k c Φnr Hc HΦnr) "HP".
    apply lookup_replicate in HΦnr as [-> _].
    iAssert (select_clause_nonblocking Φ c ∧ P)%I with "[HP]" as "H".
    { iSplit; [ iLeft in "HP"; by iApply (big_andL_lookup _ _ _ _ Hc) | iFrame ]. }
    destruct c as [[|] ?]; simpl.
    + repeat setoid_rewrite bi.and_exist_r.
      iDestruct "H" as (V sch g v ???) "H".
      iDestruct (and_sep_persistent with "H") as "[%Heq H]".
      iDestruct (and_sep_persistent with "H") as "[#Hch H]".
      iExists V, sch, g, v, _, _, _.
      iSplitR; [ iPureIntro; exact Heq | ]. iFrame "Hch".
      iApply (nonblocking_send_au_to_alt sch).
      rewrite /nonblocking_send_au. iSplit; [| iSplit; [| iSplit ] ].
      * iLeft in "H". iLeft in "H". iFrame; try done.
      * iLeft in "H". iRight in "H". iLeft in "H". iFrame; try done.
      * iLeft in "H". iRight in "H". iRight in "H". iLeft in "H". iFrame; try done.
      * iRight in "H". iSplitL "H"; [ iExact "H" | done ].
    + repeat setoid_rewrite bi.and_exist_r.
      iDestruct "H" as (V rch g ???) "H".
      iDestruct (and_sep_persistent with "H") as "[%Heq H]".
      iDestruct (and_sep_persistent with "H") as "[#Hch H]".
      iExists V, rch, g, _, _, _.
      iSplitR; [ iPureIntro; exact Heq | ]. iFrame "Hch".
      iApply (nonblocking_recv_au_to_alt rch).
      rewrite /nonblocking_recv_au. iSplit; [| iSplit; [| iSplit; [| iSplit ] ] ].
      * iLeft in "H". iLeft in "H". iFrame; try done.
      * iLeft in "H". iRight in "H". iLeft in "H". iFrame; try done.
      * iLeft in "H". iRight in "H". iRight in "H". iLeft in "H". iFrame; try done.
      * iLeft in "H". iRight in "H". iRight in "H". iRight in "H". iLeft in "H". iFrame; try done.
      * iRight in "H". iSplitL "H"; [ iExact "H" | done ].
  - iIntros "HP _". iRight in "HP". iFrame.
Qed.



End select_proof.

End chan.
