Require Import New.proof.proof_prelude.
From New.golang.theory.chan.au_spec
     Require Export chan_au_base.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.idioms.dsp
     Require Export dsp_ghost_theory.
From New.ghost Require Import token.

(** * Dependent Separation Protocols (DSP) over Go Channels

    This file implements dependent separation protocols using bidirectional Go channels.

    Key concepts:
    - Protocol endpoints communicate via two Go channels
    - LR channel: left endpoint sends values to right endpoint
    - RL channel: right endpoint sends values to left endpoint
    - Protocol state is tracked using Actris iProto with sum types
    - Channel closure is protocol-aware - only allowed when protocol permits
*)

(* Include [chanG Σ V] etc. here or not? *)
Class dspG Σ V := {
  chanG_protoG :: protoG Σ V;
}.

Record dsp_names := DSPNames {
  chan_lr_name : chan_names;
  chan_rl_name : chan_names;
  token_lr_name : gname;            (* Token for excluding closed state of lr channel  *)
  token_rl_name : gname;            (* Token for excluding closed state of rl channel*)
  dsp_lr_name : gname;              (* Protocol ownership for lr channel *)
  dsp_rl_name : gname;              (* Protocol ownership for rl channel *)
}.

Definition flip_dsp_names (γdsp_names : dsp_names) : dsp_names :=
  DSPNames
    γdsp_names.(chan_rl_name)
    γdsp_names.(chan_lr_name)
    γdsp_names.(token_rl_name)
    γdsp_names.(token_lr_name)
    γdsp_names.(dsp_rl_name)
    γdsp_names.(dsp_lr_name).

Section dsp.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `{!dspG Σ V}.

Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.
Collection W := sem + IntoValTyped0.

Let N := nroot .@ "dsp_chan".

(** ** Buffer Matching Predicates *)

(** Defines when Go channel state matches expected message queue *)
Definition buffer_matches {V}
    (state : chanstate.t V) (vs : list V) : Prop :=
  match state with
  | chanstate.Buffered queue => vs = queue
  | chanstate.SndWait v | chanstate.SndDone v => vs = [v]
  | chanstate.Closed drain => vs = drain
  | _ => vs = []
  end.

(** ** DSP Session Context *)

(** DSP session invariant - owns both channels and maintains protocol state *)
Definition dsp_session_inv
    (γdsp_names : dsp_names)
    (lr_chan rl_chan : loc)
     : iProp Σ :=
  ∃ lr_state rl_state (vsl vsr : list V),
    ⌜buffer_matches lr_state vsl⌝ ∗
    ⌜buffer_matches rl_state vsr⌝ ∗
    own_chan (γdsp_names.(chan_lr_name)) V lr_state ∗
    own_chan (γdsp_names.(chan_rl_name)) V rl_state ∗
    match lr_state with
    | chanstate.Closed _ => iProto_own (γdsp_names.(dsp_lr_name)) END
    | _ => token (γdsp_names.(token_lr_name))
    end ∗
    match rl_state with
    | chanstate.Closed _ => iProto_own (γdsp_names.(dsp_rl_name)) END
    | _ => token (γdsp_names.(token_rl_name))
    end ∗
    iProto_ctx (γdsp_names.(dsp_lr_name)) (γdsp_names.(dsp_rl_name)) vsl vsr.

Lemma dsp_session_inv_sym
    γdsp_names lr_chan rl_chan :
   dsp_session_inv γdsp_names lr_chan rl_chan ⊣⊢
   dsp_session_inv (flip_dsp_names γdsp_names) rl_chan lr_chan .
Proof.
  iSplit.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. simpl. iFrame. by iApply iProto_ctx_sym.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. by iApply iProto_ctx_sym.
Qed.

(** DSP session context - public interface with persistent channel handles *)
Definition dsp_session
             (γdsp_names : dsp_names)
    (lr_chan rl_chan : loc)
     : iProp Σ :=
  is_chan lr_chan γdsp_names.(chan_lr_name) V ∗
  is_chan rl_chan γdsp_names.(chan_rl_name) V ∗
  inv N (dsp_session_inv γdsp_names lr_chan rl_chan).

(** ** DSP Endpoints *)

(** Left endpoint - can send V_LR via lr_chan, receive V_RL via rl_chan *)
Definition dsp_endpoint
  (γdsp_names : dsp_names)
    (chans : (chan.t * chan.t))
    (p : option $ iProto Σ V) : iProp Σ :=
    dsp_session γdsp_names chans.1 chans.2 ∗
    match p with
    | None => token γdsp_names.(token_lr_name)
    | Some p => iProto_own γdsp_names.(dsp_lr_name) p
    end.

Notation "c ↣{ γ } p" := (dsp_endpoint γ c (Some p)) (at level 20, format "c  ↣{  γ  }  p").
Notation "↯{ γ } c" := (dsp_endpoint γ c None) (at level 20, format "↯{  γ  }  c").

Global Instance dsp_endpoint_ne γ c : NonExpansive (dsp_endpoint γ c).
Proof. solve_proper. Qed.
Global Instance dsp_endpoint_proper γ c : Proper ((≡) ==> (≡)) (dsp_endpoint γ c).
Proof. apply (ne_proper _). Qed.

Lemma iProto_pointsto_le γ c p1 p2 : c ↣{γ}  p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣{γ}  p2.
Proof.
  iDestruct 1 as "[Hc Hp]".
  iIntros "Hle'". iSplit; [done|].
  by iApply (iProto_own_le with "Hp").
Qed.

(** ** Initialization *)

(** Initialize a new DSP session from basic channels *)
Lemma dsp_session_init
    E (lr_chan rl_chan : loc) (lr_state rl_state : chanstate.t V)
    (γlr_names γrl_names : chan_names)
    (p : iProto Σ V) :
  (lr_state = chanstate.Idle ∨ lr_state = chanstate.Buffered []) →
  (rl_state = chanstate.Idle ∨ rl_state = chanstate.Buffered []) →
  is_chan lr_chan γlr_names V -∗
  is_chan rl_chan γrl_names V -∗
  own_chan γlr_names V lr_state -∗
  own_chan γrl_names V rl_state ={E}=∗
  ∃ γdsp1 γdsp2,
  (lr_chan,rl_chan) ↣{γdsp1}  p ∗ (rl_chan,lr_chan) ↣{γdsp2} iProto_dual p.
Proof.
  iIntros (Hlr Hrl) "#Hcl_is #Hcr_is Hcl_own Hcr_own".
  iMod (iProto_init) as (γl γr) "(Hctx & Hpl & Hpr)".
  iMod (token_alloc) as (γtl) "Htl".
  iMod (token_alloc) as (γtr) "Htr".
  set γdsp_names := (DSPNames γlr_names γrl_names γtl γtr γl γr).
  iMod (inv_alloc N _ (dsp_session_inv γdsp_names lr_chan rl_chan) with "[Hcl_own Hcr_own Htl Htr Hctx]")
    as "#Hinv".
  { iExists lr_state,rl_state,[],[]. iIntros "!>". iFrame.
    by destruct Hlr,Hrl; simplify_eq; do 2 (iSplit; [done|]); iFrame. }
  iModIntro.
  iExists γdsp_names, (flip_dsp_names γdsp_names).
  iSplitL "Hpl".
  - iFrame "Hpl Hinv". iFrame "∗#".
  - rewrite dsp_session_inv_sym. iFrame "Hinv".
    iFrame "∗#".
Qed.

(** ** Endpoint Operations *)


(** Endpoint sends value *)
(* Open the dsp session invariant.  It owns both channels, so each arm agrees
   against the half for its own direction. *)
Local Ltac dsp_open :=
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|];
  iMod (lc_fupd_elim_later with "Hlc IH") as "IH";
  iDestruct "IH" as (????)
    "(%Hbml & %Hbmr & Hownl & Hownr & Hclosel & Hcloser & Hctx)".
(* One credit strips the session invariant and the client's continuation
   together.  Phase two of a two-phase arm uses [dsp_open]. *)
Local Ltac dsp_openc :=
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|];
  iCombine "IH HΦ" as "IHc";
  iMod (lc_fupd_elim_later with "Hlc IHc") as "[IH HΦ]";
  iDestruct "IH" as (????)
    "(%Hbml & %Hbmr & Hownl & Hownr & Hclosel & Hcloser & Hctx)".

Lemma dsp_send_au γ (lr_chan rl_chan : loc) (v : V) (p : iProto Σ V) Φ :
  (lr_chan,rl_chan) ↣{γ} (<!> MSG v; p)%proto -∗
  ▷((lr_chan,rl_chan) ↣{γ} p -∗ Φ) -∗
  send_au γ.(chan_lr_name) V v Φ.
Proof.
  iIntros "Hc HΦ".
  iDestruct "Hc" as "(#(Hcl&Hcr&HI)&Hp)".
  rewrite /send_au. repeat iSplit.
  - (* send_fast_path_au : RcvWait -> SndDone v *)
    iIntros "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
    iMod (own_chan_halves_update (chanstate.SndDone v) with "Hownl Himpl")
      as "[H1 H2]"; [ simpl in Hcv |- *; lia | ].
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx Hp []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hctx2 Hown]".
    iMod ("Hclose" with "[H1 Hownr Hclosel Hcloser Hctx2]").
    { iIntros "!>". iExists _,_,_,_. iFrame. try (simpl in Hbml; subst).
      iFrame "Hclosel". iPureIntro. split_and!; done. }
    iModIntro. iFrame "H2". iApply "HΦ". by iFrame "#∗".
  - (* send_slow_path_au : Idle -> SndWait v, then RcvDone -> Idle *)
    iIntros "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv.
    iMod (own_chan_halves_update (chanstate.SndWait v) with "Hownl Himpl")
      as "[H1 H2]"; [ simpl in Hcv |- *; lia | ].
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx Hp []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hctx2 Hown]".
    iMod ("Hclose" with "[H1 Hownr Hclosel Hcloser Hctx2]").
    { iIntros "!>". iExists _,_,_,_. iFrame. try (simpl in Hbml; subst).
      iFrame "Hclosel". iPureIntro. split_and!; done. }
    iModIntro. iFrame "H2".
    (* phase two, fired once the receiver has committed *)
    iIntros "[Hlc Himpl]".
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "Hlc IH") as "IH".
    iDestruct "IH" as (????)
      "(%Hbml2 & %Hbmr2 & Hownl & Hownr & Hclosel & Hcloser & Hctx)".
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcv2.
    iMod (own_chan_halves_update (@chanstate.Idle V) with "Hownl Himpl")
      as "[H1 H2]"; [ simpl in Hcv2 |- *; lia | ].
    iMod ("Hclose" with "[H1 Hownr Hclosel Hcloser Hctx]").
    { iIntros "!>". iExists _,_,_,_. iFrame. try (simpl in Hbml2; subst).
      iFrame "Hclosel". iPureIntro. split_and!; done. }
    iModIntro. iFrame "H2". iApply "HΦ". by iFrame "#∗".
  - (* send_enq_au : append to the buffer *)
    iIntros (buf) "(Hlc & %Hlt & Himpl)". dsp_openc.
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iMod (own_chan_halves_update (chanstate.Buffered (buf ++ [v])) with "Hownl Himpl")
      as "[H1 H2]"; [ simpl; rewrite length_app /=; lia | ].
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx Hp []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hctx2 Hown]".
    iMod ("Hclose" with "[H1 Hownr Hclosel Hcloser Hctx2]").
    { iIntros "!>". iExists _,_,_,_. iFrame. try (simpl in Hbml; subst).
      iFrame "Hclosel". iPureIntro. split_and!; done. }
    iModIntro. iFrame "H2". iApply "HΦ". by iFrame "#∗".
  - (* send_closed_au : the session invariant holds [iProto_own END], which is
       exclusive with the endpoint's own protocol ownership *)
    iIntros (drain) "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (iProto_own_excl with "Hp Hclosel") as "[]".
Qed.

Lemma wp_dsp_send (lr_chan rl_chan : loc) γ (v : V) (p : iProto Σ V) :
  {{{ (lr_chan,rl_chan) ↣{γ} <!> MSG v; p }}}
    chan.send t #lr_chan #v
  {{{ RET #(); (lr_chan,rl_chan) ↣{γ} p }}}.
Proof using W.
  iIntros (Φ) "Hc HΦ".
  iDestruct "Hc" as "(#(Hcl&Hcr&HI)&Hp)".
  iApply (chan.wp_send with "Hcl").
  iIntros "_".
  iApply (dsp_send_au with "[$Hp]").
  { iFrame "#". }
  done.
Qed.

Lemma dsp_send_tele_au
  {TT : tele} (tt:TT)
  γ (lr_chan rl_chan : loc) (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) Φ :
  (lr_chan,rl_chan) ↣{γ} ((<!.. x> MSG (v x) {{ P x }}; p x))%proto -∗
  P tt -∗
  ((lr_chan,rl_chan) ↣{γ} p tt -∗ Φ) -∗
  send_au γ.(chan_lr_name) V (v tt) Φ.
Proof.
  iIntros "Hc HP HΦ".
  iDestruct (iProto_pointsto_le _ _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
    as "Hc".
  { iIntros "!>".
    iApply iProto_le_trans;
      [iApply iProto_le_texist_intro_l|].
    by iFrame "HP". }
  iApply (dsp_send_au with "Hc HΦ").
Qed.

Lemma wp_dsp_send_tele
  {TT : tele} (tt:TT)
  (lr_chan rl_chan : loc) γ (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) :
  {{{ (lr_chan,rl_chan) ↣{γ} (<!.. x> MSG (v x) {{ P x }}; p x) ∗ P tt }}}
    chan.send t #lr_chan #(v tt)
  {{{ RET #(); (lr_chan,rl_chan) ↣{γ} p tt }}}.
Proof using W.
  iIntros (Φ) "[Hc HP] HΦ".
  iDestruct (iProto_pointsto_le _ _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
    as "Hc".
  { iIntros "!>".
    iApply iProto_le_trans;
      [iApply iProto_le_texist_intro_l|].
    by iFrame "HP". }
  by iApply (wp_dsp_send with "Hc").
Qed.

(** Endpoint receives value *)
(* Common tail once the arm has moved the channel to its post-state in [H1]/[H2]:
   take the protocol step and hand the message to the continuation.  The later
   credits are for the protocol's own laters, not for the invariant. *)
Local Ltac dsp_recv_finish :=
  iDestruct (iProto_recv with "Hctx Hp") as "Hp";
  iMod "Hp" as (xs) "(Hctx2 & Hown & Hm)";
  iMod ("Hclose" with "[Hownl H1 Hclosel Hcloser Hctx2]") as "_";
  [ iIntros "!>"; iExists _,_,_,_; iFrame "H1 ∗"; iSplit; [done|];
    iPureIntro; simpl in *; by simplify_eq | ];
  iDestruct "H£s" as "[H£ H£s]";
  iCombine "Hown Hm" as "H";
  iMod (lc_fupd_elim_later with "H£ H") as "[Hown Hm]";
  rewrite iMsg_base_eq;
  iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]";
  simpl in *; simplify_eq;
  iDestruct "H£s" as "[H£ H£s]";
  rewrite later_equivI_1;
  iCombine "HP Hp" as "H";
  iMod (lc_fupd_elim_later with "H£ H") as "[HP Hp]";
  iModIntro; iFrame "H2"; iApply "HΦ"; iRewrite "Hp"; by iFrame "#∗".

Lemma dsp_recv_au {TT:tele}
    γ (lr_chan rl_chan : loc) (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) Φ :
  (£1 ∗ £1) -∗
  (lr_chan,rl_chan) ↣{γ} (<?.. x> MSG (v x) {{ ▷ P x }}; p x)%proto -∗
   ▷(∀ x, (lr_chan,rl_chan) ↣{γ} p x ∗ P x -∗ Φ (v x) true) -∗
  recv_au γ.(chan_rl_name) V Φ.
Proof.
  iIntros "H£s Hc HΦ".
  iDestruct "Hc" as "(#(Hcl&Hcr&HI)&Hp)".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au : SndWait w -> RcvDone *)
    iIntros (w) "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
    iMod (own_chan_halves_update (@chanstate.RcvDone V) with "Hownr Himpl")
      as "[H1 H2]"; [ simpl in Hcap |- *; lia | ].
    simpl in *. simplify_eq. dsp_recv_finish.
  - (* recv_slow_path_au : Idle -> RcvWait, then SndDone w -> Idle *)
    iIntros "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
    iMod (own_chan_halves_update (@chanstate.RcvWait V) with "Hownr Himpl")
      as "[H1 H2]"; [ simpl in Hcap |- *; lia | ].
    iMod ("Hclose" with "[Hownl H1 Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "H1 ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iModIntro. iFrame "H2".
    (* phase two, fired once the sender has committed *)
    iIntros (w) "[Hlc Himpl]".
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "Hlc IH") as "IH".
    iDestruct "IH" as (????)
      "(%Hbml2 & %Hbmr2 & Hownl & Hownr & Hclosel & Hcloser & Hctx)".
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap2.
    iMod (own_chan_halves_update (@chanstate.Idle V) with "Hownr Himpl")
      as "[H1 H2]"; [ simpl in Hcap2 |- *; lia | ].
    simpl in *. simplify_eq. dsp_recv_finish.
  - (* recv_deq_au : take the head off the buffer *)
    iIntros (w rest) "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
    iMod (own_chan_halves_update (chanstate.Buffered rest) with "Hownr Himpl")
      as "[H1 H2]"; [ simpl in Hcap |- *; split; lia | ].
    simpl in *. simplify_eq. dsp_recv_finish.
  - (* recv_drain_au : take the head off a closed channel's drain *)
    iIntros (w rest) "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
    iMod (own_chan_halves_update (chanstate.Closed rest) with "Hownr Himpl")
      as "[H1 H2]"; [ destruct rest; simpl in Hcap |- *; [ lia | split; lia ] | ].
    simpl in *. simplify_eq. dsp_recv_finish.
  - (* recv_closed_au : a drained, closed channel contradicts an outstanding
       receive obligation on the protocol *)
    iIntros "[Hlc Himpl]". dsp_openc.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    simpl in *. simplify_eq.
    iDestruct (iProto_recv_end_inv_l with "Hctx Hp Hcloser") as "H".
    iDestruct "H£s" as "[H£ H£s]".
    iMod (lc_fupd_elim_later with "H£ H") as "[]".
Qed.

Lemma wp_dsp_recv {TT:tele}
    γ (lr_chan rl_chan : loc) (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) :
  {{{ (lr_chan,rl_chan) ↣{γ} <?.. x> MSG (v x) {{ ▷ P x }}; p x }}}
    chan.receive t #rl_chan
  {{{ x, RET (#(v x), #true); (lr_chan,rl_chan) ↣{γ} p x ∗ P x }}}.
Proof using W.
  iIntros (Φ) "Hc HΦ".
  iDestruct "Hc" as "(#(Hcl&Hcr&HI)&Hp)".
  iApply (chan.wp_receive with "Hcr").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (dsp_recv_au with "[$] [$Hp]").
  { iFrame "#". }
  done.
Qed.

(** Endpoint closes (stops sending val) *)
Lemma wp_dsp_close γ (lr_chan rl_chan : loc) (p : iProto Σ V) Φ :
  (lr_chan,rl_chan) ↣{γ} END -∗
  (↯{γ} (lr_chan,rl_chan) -∗ Φ) -∗
  close_au γ.(chan_lr_name) V Φ.
Proof using W.
  iIntros "Hc HΦ".
  iDestruct "Hc" as  "(#(Hcl&Hcr&HI)&Hp)".
  rewrite /close_au. repeat iSplit.
  - (* close_idle_au : Idle -> Closed [] *)
    iIntros "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
    iMod (own_chan_halves_update (@chanstate.Closed V []) with "Hownl Himpl")
      as "[H1 H2]"; [ simpl in Hcap |- *; lia | ].
    iMod ("Hclose" with "[H1 Hownr Hcloser Hctx Hp]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "H1 ∗". try iFrame "Hp". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iModIntro. iFrame "H2". iApply "HΦ". by iFrame "#∗".
  - (* close_buf_au : Buffered buf -> Closed buf *)
    iIntros (buf) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %[Hlen Hpos].
    iMod (own_chan_halves_update (chanstate.Closed buf) with "Hownl Himpl")
      as "[H1 H2]";
      [ destruct buf; simpl in Hlen |- *; [ lia | split; lia ] | ].
    iMod ("Hclose" with "[H1 Hownr Hcloser Hctx Hp]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "H1 ∗". try iFrame "Hp". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iModIntro. iFrame "H2". iApply "HΦ". by iFrame "#∗".
  - (* close_closed_au : the invariant already holds [iProto_own END] *)
    iIntros (drain) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownl Himpl") as %->.
    iDestruct (iProto_own_excl with "Hp Hclosel") as "[]".
Qed.

(* With the protocol ended the peer has nothing in flight, so every arm naming a
   nonempty rl-buffer is contradictory; only the drained-closed arm fires. *)
Local Ltac dsp_end_absurd :=
  simpl in *; simplify_eq;
  iDestruct (iProto_end_inv_l with "Hctx Hp") as "H";
  iDestruct "H£s" as "[H£ H£s]";
  iMod (lc_fupd_elim_later with "H£ H") as %?;
  by simplify_eq.

(** Endpoint receives on a closed or ended channel *)
Lemma wp_dsp_recv_end γ (lr_chan rl_chan : loc) Φ :
  (£1 ∗ £1) -∗
  (lr_chan,rl_chan) ↣{γ} END-∗
  ((lr_chan,rl_chan) ↣{γ} END -∗ Φ (zero_val V) false) -∗
  recv_au γ.(chan_rl_name) V Φ.
Proof using W.
  iIntros "H£s Hc HΦ".
  iDestruct "Hc" as "(#(Hcl&Hcr&HI)&Hp)".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au *)
    iIntros (w) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->. dsp_end_absurd.
  - (* recv_slow_path_au : the offer can be posted, but never accepted *)
    iIntros "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
    iMod (own_chan_halves_update (@chanstate.RcvWait V) with "Hownr Himpl")
      as "[H1 H2]"; [ simpl in Hcap |- *; lia | ].
    iMod ("Hclose" with "[Hownl H1 Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "H1 ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iModIntro. iFrame "H2".
    iIntros (w) "[Hlc Himpl]".
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "Hlc IH") as "IH".
    iDestruct "IH" as (????)
      "(%Hbml2 & %Hbmr2 & Hownl & Hownr & Hclosel & Hcloser & Hctx)".
    iDestruct (own_chan_agree with "Hownr Himpl") as %->. dsp_end_absurd.
  - (* recv_deq_au *)
    iIntros (w rest) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->. dsp_end_absurd.
  - (* recv_drain_au *)
    iIntros (w rest) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->. dsp_end_absurd.
  - (* recv_closed_au : drained and closed, so the receive fails *)
    iIntros "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    simpl in *. simplify_eq.
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iModIntro. iFrame "Himpl". iApply "HΦ". by iFrame "#∗".
Qed.

(* Same shape, but here the *invariant* owns [iProto_own END]; the endpoint is a
   bare token, so the empty-queue fact comes from [Hclosel] rather than [Hp]. *)
Local Ltac dsp_closed_vsr ls :=
  iCombine "Hctx Hclosel" as "H";
  iDestruct "H£s" as "[H£ H£s]";
  iMod (lc_fupd_elim_later with "H£ H") as "[Hctx Hclosel]";
  destruct ls; (try by iDestruct (token_exclusive with "Hp Hclosel") as "[]");
  iDestruct (iProto_end_inv_l with "Hctx Hclosel") as "#>->".

(** Endpoint receives on a closed or ended channel *)
Lemma wp_dsp_recv_closed γ (lr_chan rl_chan : loc) Φ :
  (£1 ∗ £1) -∗
  ↯{γ} (lr_chan,rl_chan) -∗
  (↯{γ} (lr_chan,rl_chan) -∗ Φ (zero_val V) false) -∗
  recv_au γ.(chan_rl_name) V Φ.
Proof using W.
  iIntros "H£s Hc HΦ".
  iDestruct "Hc" as "(#(Hcl&Hcr&HI)&Hp)".
  rewrite /recv_au. repeat iSplit.
  - (* recv_fast_path_au *)
    iIntros (w) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    dsp_closed_vsr lr_state. simpl in *. by simplify_eq.
  - (* recv_slow_path_au : the offer can be posted, but never accepted *)
    iIntros "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    dsp_closed_vsr lr_state.
    iDestruct (own_chan_cap_valid with "Himpl") as %Hcap.
    iMod (own_chan_halves_update (@chanstate.RcvWait V) with "Hownr Himpl")
      as "[H1 H2]"; [ simpl in Hcap |- *; lia | ].
    iMod ("Hclose" with "[Hownl H1 Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "H1 ∗". iSplit; [done|]. by iFrame. }
    iModIntro. iFrame "H2".
    iIntros (w) "[Hlc Himpl]".
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "Hlc IH") as "IH".
    iDestruct "IH" as (????)
      "(%Hbml2 & %Hbmr2 & Hownl & Hownr & Hclosel & Hcloser & Hctx)".
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    dsp_closed_vsr lr_state. simpl in *. by simplify_eq.
  - (* recv_deq_au *)
    iIntros (w rest) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    dsp_closed_vsr lr_state. simpl in *. by simplify_eq.
  - (* recv_drain_au *)
    iIntros (w rest) "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    dsp_closed_vsr lr_state. simpl in *. by simplify_eq.
  - (* recv_closed_au : drained and closed, so the receive fails *)
    iIntros "[Hlc Himpl]". dsp_open.
    iDestruct (own_chan_agree with "Hownr Himpl") as %->.
    dsp_closed_vsr lr_state.
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|]. by iFrame. }
    iModIntro. iFrame "Himpl". iApply "HΦ". by iFrame "#∗".
Qed.

Lemma wp_dsp_recv_false (b : bool) γ (lr_chan rl_chan : loc) Φ :
  (£1 ∗ £1) -∗
  (if b then (lr_chan,rl_chan) ↣{γ} END else ↯{γ} (lr_chan,rl_chan)) -∗
  ((if b then (lr_chan,rl_chan) ↣{γ} END else ↯{γ} (lr_chan,rl_chan)) -∗ Φ (zero_val V) false) -∗
  recv_au γ.(chan_rl_name) V Φ.
Proof using W. destruct b; [apply wp_dsp_recv_end|apply wp_dsp_recv_closed]. Qed.

End dsp.

Notation "c ↣{ γ } p" := (dsp_endpoint γ c (Some p)) (at level 20, format "c  ↣{  γ  }  p").
Notation "↯{ γ } c" := (dsp_endpoint γ c None) (at level 20, format "↯{  γ  }  c").
