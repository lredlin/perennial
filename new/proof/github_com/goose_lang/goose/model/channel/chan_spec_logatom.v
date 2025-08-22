From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channelv2 Require Import chan_ghost_state  chan_init.
Require Export New.code.github_com.goose_lang.goose.model.channel_v2.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel_v2.
From New.proof Require Import proof_prelude.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!goGlobalsGS Σ}.
Context  `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.


(* Channel state constants *)
Definition encode_offer_state (s : chan_state.UnbufferedChannel V) : u64 :=
  match s with
  | chan_state.Idle => W64 0
  | chan_state.SndWait _  => W64 1
  | chan_state.RcvWait => W64 2
  | chan_state.SndDone _ => W64 3
  | chan_state.RcvDone => W64 4
  end.

  #[global] Transparent encode_offer_state.

  Definition get_buffer_info (bc: chan_state.BufferedChannel V) : list V * nat :=
  match bc with
  | chan_state.Buffer queue capacity => (queue, capacity)
  end.


(* I am looking to figure out a way to have single threaded specs for when you don't share the channel with other goroutines/before you open any invariants and hoping to abstract it to the client with the same convention as free lock *)

  (* Option 2: Separate predicates for buffered vs unbuffered *)
Definition free_buffered_chan (ch: loc) (bc: chan_state.BufferedChannel V) (mu: loc) (slice_val: slice.t): iProp Σ :=
  let (queue, cap) := get_buffer_info bc in
  "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 0) ∗  
  "slice" ∷ own_slice slice_val (DfracOwn 1) queue ∗
  "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val ∗
  "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 cap) ∗ 
  "mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"]□ mu.

Definition free_unbuffered_chan (ch: loc) (ub: chan_state.UnbufferedChannel V) (mu: loc): iProp Σ :=
  "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state ub) ∗ 
  "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 0) ∗ 
  "mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"]□ mu.

Definition own_chan (ch: loc) (s: chan_state.Channel V) (γ: chan_names): iProp Σ := 
  "chan_ghost_frag" ∷ ghost_var γ.(state_name) (1/2)%Qp s.

  

Definition closed_chan (ch: loc) : iProp Σ := 
  "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"]□ (W64 5).

Definition unbuff_ghost_state (γ: chan_names) (s: chan_state.Channel V) : iProp Σ :=
  match s with
  | chan_state.Open (chan_state.Unbuffered ub) =>
      match ub with
      | chan_state.Idle => 
          idle_tok γ.(offer_name)
      | chan_state.SndWait v => 
          snd_wait_tok γ.(offer_name) v
      | chan_state.RcvWait => 
          rcv_wait_tok γ.(offer_name)
      | chan_state.SndDone v => 
          rcv_wait_tok γ.(offer_name)
      | chan_state.RcvDone => 
          (∃ v, snd_wait_tok γ.(offer_name) v)
      end
  | _ => emp
  end.

(* Channel invariant using new types *)
Definition chan_inv (s: chan_state.Channel V) (γ: chan_names): iProp Σ := 
  match s with
  | chan_state.Open (chan_state.Buffered bc) =>
      let (queue, cap) := get_buffer_info bc in
      "%HBuffCap" ∷ ⌜length queue ≤ cap⌝ ∗
      "HGhostState" ∷ chan_ghost_state γ s
  | _ =>
      "HGhostState" ∷ chan_ghost_state γ s
  end.

(* Updated is_chan predicates *)
Definition is_chan_inner (ch: loc) γ : iProp Σ :=
  ∃ (s : chan_state.Channel V) (mu_loc: loc), 
  "chan_phys" ∷ free_chan ch s mu_loc ∗
  "chan_ghost_auth" ∷ ghost_var γ.(state_name) (1/2)%Qp s ∗
  "chan_inv" ∷ chan_inv s γ.

Definition is_chan (ch: loc) γ : iProp Σ :=
  ∃ (s : chan_state.Channel V) (mu_loc: loc), 
  "#mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"]□ mu_loc ∗ 
  "chan_ghost_auth" ∷ ghost_var γ.(state_name) (1/2)%Qp s ∗
  "#Hlock" ∷ is_Mutex mu_loc (is_chan_inner ch γ).

Definition chan_inv (s: chan_state.t V) (γ: chan_names): iProp Σ := 
  ("%HBuffCap" ∷ ⌜length s.(chan_state.buff) ≤ (uint.nat s.(chan_state.cap))⌝ ∗
  "HOfferState" ∷ offer_ghost_state γ s.(chan_state.state) s.(chan_state.value)
   )%I .

(* Here and elsewhere: I need to add some sort of function for converting the v pointer to an option monad mathematical representation *)
  Definition is_chan_inner (ch: loc) γ : iProp Σ :=
  ∃ (s : chan_state.t V), 
   (* "value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] s.(chan_state.value) ∗ *)
  "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state s.(chan_state.state)) ∗ 
  "slice" ∷ own_slice s.(chan_state.buff_slice) (DfracOwn 1) s.(chan_state.buff) ∗
  "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] s.(chan_state.buff_slice) ∗
  "cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"] s.(chan_state.cap) ∗ 
  "mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"] s.(chan_state.mu) ∗ 
  "chan_ghost_auth" ∷ ghost_var γ.(state_name) (1/2)%Qp s ∗
  "chan_inv" ∷ chan_inv s γ 
  .

Definition is_chan (ch: loc) γ : iProp Σ :=
  ∃ (s : chan_state.t V), 
  "#mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"]□  s.(chan_state.mu) ∗ 
  "chan_ghost_auth" ∷ ghost_var γ.(state_name) (1/2)%Qp s ∗
  "#Hlock" ∷ is_Mutex s.(chan_state.mu) (is_chan_inner ch γ)
  .
  
#[global] Opaque is_chan.
#[local] Transparent is_chan.
Global Instance is_chan_pers ch γ  : Persistent (is_chan ch γ ).
Admitted.   
#[global] Instance own_chan_timeless ch s γ  : Timeless (own_chan ch s γ).
Admitted.


Lemma own_chan_is_chan ch s γ  :
  own_chan ch s γ  -∗ is_chan ch γ.
Proof.
Admitted.

Lemma is_chan_not_nil ch γ  :
  is_chan ch γ -∗ ⌜ ch ≠ chan.nil ⌝.
Proof.
Admitted.

  (* Helper to check if channel has available capacity *)
Definition has_capacity (s: chan_state.t V) : Prop :=
  length s.(chan_state.buff) < uint.nat s.(chan_state.cap).

(* Helper to enqueue a value to the buffer *)
Definition enqueue_value (s: chan_state.t V) (v: V) : chan_state.t V :=
  s <| chan_state.buff := s.(chan_state.buff) ++ [v] |>.

Definition try_buff_send_AU 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess Φfailure: iProp Σ) (s: chan_state.t V) : iProp Σ :=
  is_chan ch γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    ⌜uint.nat s.(chan_state.cap) > 0⌝ ∗           (* Buffered channel *)
    ⌜s.(chan_state.state) ≠ Closed⌝ ∗             (* Not closed *)
    (* Branch on available capacity *)
    (if decide (has_capacity s) then
       (* Success path: enqueue the value *)
       let s_new := enqueue_value s v in
       (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess)
     else
       (* Failure path: buffer is full *)
       ⌜length s.(chan_state.buff) = uint.nat s.(chan_state.cap)⌝ ∗
       (own_chan ch s γ ={∅,⊤}=∗ Φfailure)).

Definition buff_send_AU 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess: iProp Σ) (s: chan_state.t V) : iProp Σ :=
  is_chan ch γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.nat s.(chan_state.cap) > 0⌝ ∗           
    ⌜s.(chan_state.state) ≠ Closed⌝ ∗             
    (* Will eventually succeed when capacity becomes available *)
    (* This abstracts away the retry loop *)
    let s_new := enqueue_value s v in
    (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess).

Lemma wp_buf_trysend 
  (ch: loc) (v: V) (γ: chan_names) s :
  ∀ Φ,
  uint.nat s.(chan_state.cap) > 0 →
  s.(chan_state.state) ≠ Closed →
  is_pkg_init channel -∗
  ▷(try_buff_send_AU ch v γ (Φ #true) (Φ #false) s) -∗
  WP ch @ channel @ "Channel'ptr" @ "TrySend" #t #v #false {{ Φ }}.
Proof.
Admitted.

(* Usage theorem showing the connection to implementation *)
Lemma wp_buff_send 
  (ch: loc) (v: V) (γ: chan_names) s :
  uint.nat s.(chan_state.cap) > 0 ->
  ∀ Φ,
  is_pkg_init channel ∗ is_chan ch γ -∗
  ▷(buff_send_AU ch v γ (Φ #()) s) -∗
  WP ch @ channel @ "Channel'ptr" @ "Send" #t #v  {{ Φ }}.
Proof.
  iIntros "%Hbuff".
  wp_start as "#His".
  wp_auto.
Admitted.

(* Helper to check if channel has available items *)
Definition has_items (s: chan_state.t V) : Prop :=
  length s.(chan_state.buff) > 0.

(* Helper to dequeue a value from the buffer *)
Definition dequeue_value {H: IntoVal V} {t} {H': IntoValTyped V t}  (s: chan_state.t V) : (chan_state.t V * V) :=
  match s.(chan_state.buff) with
  | [] => (s, default_val V)  (* Shouldn't happen if has_items *)
  | v :: rest => (s <| chan_state.buff := rest |>, v)
  end.

(* Non-blocking buffered receive *)
Definition try_buff_receive_AU {H: IntoVal V} {t} {H': IntoValTyped V t} 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) (Φfailure: iProp Σ) s : iProp Σ :=
  is_chan ch γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.nat s.(chan_state.cap) > 0⌝ ∗           (* Buffered channel *)
    (* Branch on available items *)
    (if decide (has_items s) then
       (* Success path: dequeue a value *)
       let '(s_new, v) := dequeue_value s in
       (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess v true)
     else if decide (s.(chan_state.state) = Closed) then
       (* Closed and empty: return zero value and false *)
       (own_chan ch s γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
     else
       (* No items available and not closed: would block *)
       (own_chan ch s γ ={∅,⊤}=∗ Φfailure)).

Definition buff_receive_AU 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    (* Will eventually succeed when items become available or channel closes *)
    (* This abstracts away the retry loop *)
    (if decide (s.(chan_state.state) = Closed ∧ ¬has_items s) then
       (* Closed and empty *)
       (own_chan ch s γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
     else
       (* Will eventually get a value *)
       ∃ v, let '(s_new, _) := dequeue_value s in
       (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess v true)).


(* Usage theorems *)
Lemma wp_try_buff_receive 
  (ch: loc) (γ: chan_names) s :
  ∀ Φ,
  is_pkg_init channel ∗ is_chan ch s γ -∗
  ▷(try_buff_receive_AU ch γ (λ v ok, Φ (#v, #ok)%V) (Φ (#(default_val V), #false)%V) s) -∗
    WP ch @ channel @ "Channel'ptr" @ "BufferedTryReceive" #t #() {{ Φ }}.
Proof.
Admitted.

Lemma wp_buff_receive 
  (ch: loc) (γ: chan_names) s :
  ∀ Φ,
  uint.nat s.(chan_state.cap) > 0 ->
  is_pkg_init channel ∗ is_chan ch s γ -∗
  ▷(buff_receive_AU ch γ (λ v ok, Φ (#v, #ok)%V) s) -∗
  WP ch @ channel @ "Channel'ptr" @ "Receive" #t #() {{ Φ }}.
Proof.
Admitted.

(* Unbuffered channel logically atomic specifications *)

(* Non-blocking send attempt - single atomic step *)
Definition try_unbuffered_nonblocking_send_AU 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess Φfailure: iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.Z s.(chan_state.cap) = 0⌝ ∗           (* Unbuffered channel *)
    ⌜s.(chan_state.state) ≠ Closed⌝ ∗             (* Not closed *)
    (* Branch on current state *)
    (if decide (s.(chan_state.state) = Offer ∧ s.(chan_state.value) = None) then
       (* Success path: complete waiting receiver's offer *)
       let s_new := s <| chan_state.state := Accept |> <| chan_state.value := Some v |> in
       (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess)
     else
       (* Failure path: no receiver waiting, don't block *)
       (own_chan ch s γ ={∅,⊤}=∗ Φfailure)).

(* Blocking send attempt - may require multiple phases *)
Definition try_unbuffered_blocking_send_AU 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess Φfailure: iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.Z s.(chan_state.cap) = 0⌝ ∗           
    ⌜s.(chan_state.state) ≠ Closed⌝ ∗             
    (* Three possible outcomes *)
    ((* Case 1: Complete existing receiver offer *)
     ⌜s.(chan_state.state) = Offer ∧ s.(chan_state.value) = None⌝ ∗
     let s_new := s <| chan_state.state := Accept |> <| chan_state.value := Some v |> in
     (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess)
    ∨
     (* Case 2: Make sender offer (will need second phase) *)
     ⌜s.(chan_state.state) = Idle⌝ ∗
     let s_offer := s <| chan_state.state := Offer |> <| chan_state.value := Some v |> in
     (own_chan ch s_offer γ ={∅,⊤}=∗ 
       (* Second phase: check offer result *)
       |={⊤,∅}=> ▷∃ s', own_chan ch s' γ ∗
       (if decide (s'.(chan_state.state) = Accept) then
          (* Offer accepted *)
          let s_final := s' <| chan_state.state := Idle |> <| chan_state.value := None |> in
          (own_chan ch s_final γ ={∅,⊤}=∗ Φsuccess)
        else
          (* Offer rescinded *)
          ⌜s'.(chan_state.state) = Offer⌝ ∗
          let s_final := s' <| chan_state.state := Idle |> <| chan_state.value := None |> in
          (own_chan ch s_final γ ={∅,⊤}=∗ Φfailure)))
    ∨
     (* Case 3: Exchange in progress, cannot proceed *)
     ⌜s.(chan_state.state) = Offer ∧ s.(chan_state.value) ≠ None ∨ 
      s.(chan_state.state) = Accept⌝ ∗
     (own_chan ch s γ ={∅,⊤}=∗ Φfailure)).

(* Guaranteed eventual success for blocking send *)
Definition unbuffered_send_AU 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess: iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.Z s.(chan_state.cap) = 0⌝ ∗           
    ⌜s.(chan_state.state) ≠ Closed⌝ ∗             
    (* Will eventually succeed through one of two paths *)
    ((* Path 1: Immediate completion with waiting receiver *)
     ∃ s_recv, ⌜s_recv.(chan_state.state) = Offer ∧ s_recv.(chan_state.value) = None⌝ ∗
     let s_new := s_recv <| chan_state.state := Accept |> <| chan_state.value := Some v |> in
     (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess)
    ∨
     (* Path 2: Make offer and eventually get accepted *)
     ∃ s_idle, ⌜s_idle.(chan_state.state) = Idle⌝ ∗
     let s_offer := s_idle <| chan_state.state := Offer |> <| chan_state.value := Some v |> in
     (own_chan ch s_offer γ ={∅,⊤}=∗ 
       |={⊤,∅}=> ▷∃ s_accept, own_chan ch s_accept γ ∗
       ⌜s_accept.(chan_state.state) = Accept⌝ ∗
       let s_final := s_accept <| chan_state.state := Idle |> <| chan_state.value := None |> in
       (own_chan ch s_final γ ={∅,⊤}=∗ Φsuccess))).

(* Non-blocking receive attempt - single atomic step *)
Definition try_unbuffered_nonblocking_receive_AU 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) (Φfailure: iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.Z s.(chan_state.cap) = 0⌝ ∗           
    (* Branch on current state *)
    (if decide (s.(chan_state.state) = Closed) then
       (* Closed: return zero value and false *)
       (own_chan ch s γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
     else if decide (s.(chan_state.state) = Offer ∧ s.(chan_state.value) ≠ None) then
       (* Success path: complete waiting sender's offer *)
       ∃ v, ⌜s.(chan_state.value) = Some v⌝ ∗
       let s_new := s <| chan_state.state := Accept |> in
       (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess v true)
     else
       (* Failure path: no sender waiting, don't block *)
       (own_chan ch s γ ={∅,⊤}=∗ Φfailure)).

(* Blocking receive attempt - may require multiple phases *)
Definition try_unbuffered_blocking_receive_AU 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) (Φfailure: iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.Z s.(chan_state.cap) = 0⌝ ∗           
    (* Three possible outcomes *)
    ((* Case 1: Channel closed *)
     ⌜s.(chan_state.state) = Closed⌝ ∗
     (own_chan ch s γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
    ∨
     (* Case 2: Complete existing sender offer *)
     ⌜s.(chan_state.state) = Offer ∧ s.(chan_state.value) ≠ None⌝ ∗
     ∃ v, ⌜s.(chan_state.value) = Some v⌝ ∗
     let s_new := s <| chan_state.state := Accept |> in
     (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess v true)
    ∨
     (* Case 3: Make receiver offer (will need second phase) *)
     ⌜s.(chan_state.state) = Idle⌝ ∗
     let s_offer := s <| chan_state.state := Offer |> <| chan_state.value := None |> in
     (own_chan ch s_offer γ ={∅,⊤}=∗ 
       (* Second phase: check offer result *)
       |={⊤,∅}=> ▷∃ s', own_chan ch s' γ ∗
       (if decide (s'.(chan_state.state) = Closed) then
          (* Channel was closed *)
          (own_chan ch s' γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
        else if decide (s'.(chan_state.state) = Accept) then
          (* Offer accepted *)
          ∃ v, ⌜s'.(chan_state.value) = Some v⌝ ∗
          let s_final := s' <| chan_state.state := Idle |> <| chan_state.value := None |> in
          (own_chan ch s_final γ ={∅,⊤}=∗ Φsuccess v true)
        else
          (* Offer rescinded *)
          ⌜s'.(chan_state.state) = Offer⌝ ∗
          let s_final := s' <| chan_state.state := Idle |> <| chan_state.value := None |> in
          (own_chan ch s_final γ ={∅,⊤}=∗ Φfailure)))
    ∨
     (* Case 4: Exchange in progress, cannot proceed *)
     ⌜s.(chan_state.state) = Offer ∧ s.(chan_state.value) = None ∨ 
      s.(chan_state.state) = Accept⌝ ∗
     (own_chan ch s γ ={∅,⊤}=∗ Φfailure)).

(* Guaranteed eventual success for blocking receive *)
Definition unbuffered_receive_AU 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s, own_chan ch s γ ∗
    (* Preconditions *)
    ⌜uint.Z s.(chan_state.cap) = 0⌝ ∗           
    (* Will eventually succeed through one of two paths *)
    ((* Path 1: Channel is/becomes closed *)
     ∃ s_closed, ⌜s_closed.(chan_state.state) = Closed⌝ ∗
     (own_chan ch s_closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
    ∨
     (* Path 2: Immediate completion with waiting sender *)
     ∃ s_send v, ⌜s_send.(chan_state.state) = Offer ∧ s_send.(chan_state.value) = Some v⌝ ∗
     let s_new := s_send <| chan_state.state := Accept |> in
     (own_chan ch s_new γ ={∅,⊤}=∗ Φsuccess v true)
    ∨
     (* Path 3: Make offer and eventually get accepted *)
     ∃ s_idle, ⌜s_idle.(chan_state.state) = Idle⌝ ∗
     let s_offer := s_idle <| chan_state.state := Offer |> <| chan_state.value := None |> in
     (own_chan ch s_offer γ ={∅,⊤}=∗ 
       |={⊤,∅}=> ▷∃ s_accept v, own_chan ch s_accept γ ∗
       ⌜s_accept.(chan_state.state) = Accept ∧ s_accept.(chan_state.value) = Some v⌝ ∗
       let s_final := s_accept <| chan_state.state := Idle |> <| chan_state.value := None |> in
       (own_chan ch s_final γ ={∅,⊤}=∗ Φsuccess v true))).

(* This I believe is the abstraction free version we could have that would be client facing *)
Definition unbuffered_receive_client_facing_AU 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) s : iProp Σ :=
  is_chan ch s γ ∗
  |={⊤,∅}=> 
    ▷∃ s,
    (* Preconditions *)
    ⌜uint.Z s.(chan_state.cap) = 0⌝ ∗           
    (* Will eventually succeed through one of two paths *)
    ((* Path 1: Channel is/becomes closed *)
     "value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] s.(chan_state.value) ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Closed) ∗ 
      (("value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] s.(chan_state.value) ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Closed))
      ={∅,⊤}=∗ Φsuccess (default_val V) false))
    ∨
     (* Path 2: Immediate completion with waiting sender *)
     (* Receiver accepts, client invariant would allow receiver to consume P v in exchange for setting to Accept and offering Q i.e. Accept and v = None -> Q  *)
     "value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] Some v ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Offer) ∗ 
     (
      ("value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] None ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Accept)) 
     ={∅,⊤}=∗ Φsuccess v true)
    ∨
     (* Path 3: Make offer and eventually get accepted *)
     (* Idle to offer, client invariant would put Q up for sender to consume i.e. Offer and v=None -> Q *)
      "value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] None ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Idle) ∗ 
     ( ("value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] None ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Offer)) ={∅,⊤}=∗ 

       |={⊤,∅}=> 
     (* Sender accepted, client invariant would allow receiver to consume P v in exchange for setting idle i.e. Accept and v = Some v -> P v  *)
       ▷("value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] Some v ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Accept)) ∗
       (("value" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] None ∗ 
     "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (encode_offer_state Idle))
      ={∅,⊤}=∗ Φsuccess v true)).

(* Usage theorems linking specs to implementation *)
Lemma wp_try_unbuffered_nonblocking_send
  (ch: loc) (v: V) (γ: chan_names) s :
  ∀ Φ,
  uint.Z s.(chan_state.cap) = 0 →
  is_pkg_init channel ∗ is_chan ch s γ -∗
  ▷(try_unbuffered_nonblocking_send_AU ch v γ (Φ #true) (Φ #false) s) -∗
  WP ch @ channel @ "Channel'ptr" @ "TrySend" #t #v #false {{ Φ }}.
Proof.
Admitted.

Lemma wp_unbuffered_send 
  (ch: loc) (v: V) (γ: chan_names) s :
  ∀ Φ,
  uint.Z s.(chan_state.cap) = 0 →
  is_pkg_init channel ∗ is_chan ch s γ -∗
  ▷(unbuffered_send_AU ch v γ (Φ #()) s) -∗
  WP ch @ channel @ "Channel'ptr" @ "Send" #t #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_try_unbuffered_nonblocking_receive 
  (ch: loc) (γ: chan_names) s :
  ∀ Φ,
  uint.Z s.(chan_state.cap) = 0 →
  is_pkg_init channel ∗ is_chan ch s γ -∗
  ▷(try_unbuffered_nonblocking_receive_AU ch γ (λ v ok, Φ (#v, #ok)%V) (Φ (#(default_val V), #false)%V) s) -∗
  WP ch @ channel @ "Channel'ptr" @ "TryReceive" #t #false {{ Φ }}.
Proof.
Admitted.

Lemma wp_unbuffered_receive 
  (ch: loc) (γ: chan_names) s :
  ∀ Φ,
  uint.Z s.(chan_state.cap) = 0 →
  is_pkg_init channel ∗ is_chan ch s γ -∗
  ▷(unbuffered_receive_AU ch γ (λ v ok, Φ (#v, #ok)%V) s) -∗
  WP ch @ channel @ "Channel'ptr" @ "Receive" #t #() {{ Φ }}.
Proof.
Admitted.


(* Buffer matching invariants for DSP-Go channel connection *)
Definition lr_buffer_matches {V_LR} (lr_state : chan_state.t V_LR) (vsl : list V_LR) : Prop :=
  if decide (uint.nat lr_state.(chan_state.cap) > 0) then
    (* Buffered channel: logical buffer exactly matches physical buffer *)
    vsl = lr_state.(chan_state.buff)
  else
    (* Unbuffered channel: logical buffer reflects offer state *)
    match lr_state.(chan_state.state), lr_state.(chan_state.value) with
    | Offer, Some v => vsl = [v]      (* Pending send: buffer contains offered value *)
    | Offer, None => vsl = []      (* Pending receiver: buffer empty *)
    | Idle, None => vsl = []          (* Idle: buffer empty *)
    | Accept, Some v => vsl = [v]      (* Sender accepted: buffer contains sent value*)
    | Accept, None => vsl = []      (* Receiver accepted: receiver dequeued offered value, buffer empty*)
    | Closed, None => vsl = []        (* Closed: buffer empty *)
    | _, _ => False                   (* Invalid state combinations *)
    end.

(* Same for the other direction... *)

Definition chan_dsp_ctx {V_LR V_RL} (γl γr : gname) 
  (lr_go_chan rl_go_chan : loc) (vsl : list V_LR) (vsr : list V_RL) : iProp Σ :=
  ∃ lr_state rl_state lr_names rl_names,
    is_chan lr_go_chan lr_state lr_names ∗
    is_chan rl_go_chan rl_state rl_names ∗
    ⌜lr_buffer_matches lr_state vsl⌝ ∗
    ⌜rl_buffer_matches rl_state vsr⌝ ∗
    iProto_ctx γl γr vsl vsr.


End proof.

    
    
