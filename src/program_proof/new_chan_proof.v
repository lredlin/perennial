From Perennial.Helpers Require Import List ModArith.

From Goose.github_com.goose_lang Require Import chan_code.

From iris.algebra Require Import excl gset.
From Perennial.algebra Require Import ghost_var.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.automation Require Import extra_tactics.
From Perennial.goose_lang Require Import prelude. 
From Perennial.goose_lang.lib Require Export
     persistent_readonly slice slice.typed_slice struct loop lock control map.typed_map time proph rand string.
From Perennial.goose_lang Require Export proofmode wpc_proofmode array.
From Perennial.goose_lang Require Export into_val.
From Perennial.program_proof Require Import std_proof. 

Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.
Context `{ghost_varG0: ghost_varG Σ nat}.

Implicit Types (v:val).

Open Scope Z_scope.

Section RBSHV2.
Context `{ghost_varG1: ghost_varG Σ (list (iProp Σ))}.
Context `{ghost_varG2: ghost_varG Σ (list w64)}.
Context `{ghost_varG3: ghost_varG Σ bool}.

(* The state where neither the receiver nor sender is waiting and we haven't
closed yet. *)
Definition start_state_prop (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (closed_b: bool): Prop :=
     
    (((sender_ready_b = false)) 
     ∧ ((receiver_ready_b = false) )
     ∧ ((sender_done_b = false) )
     ∧ ((receiver_done_b = false))
     ∧ (closed_b = false)) 
.
Definition start_state_bool (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (closed_b: bool): bool :=
     bool_decide (start_state_prop sender_ready_b receiver_ready_b sender_done_b receiver_done_b closed_b)
.

(* Either the receiver or sender is waiting somewhere. *)
Definition any_bool_true (sender_ready_b: bool) 
     (sender_done_b: bool) (receiver_done_b: bool): bool :=
     bool_decide
    (((sender_ready_b = true)) 
     ∨  ((sender_done_b = true))
     ∨  ((receiver_done_b = true)))  
.

(* We have sent/received all expected values so we can close now. *)
Definition closeable_prop (sender_ready_b: bool) (receiver_ready_b: bool) 
     (sender_done_b: bool) (receiver_done_b: bool) (index: nat) (num_uses: nat): Prop :=
    bool_decide (( ((sender_done_b = false))
     ∧ ((receiver_done_b = false))
     ∧ (index = num_uses)))
     .
Definition closeable_bool (sender_ready_b: bool) (receiver_ready_b: bool) 
     (sender_done_b: bool) (receiver_done_b: bool) (index: nat) (num_uses: nat): bool :=
    bool_decide ((
      
     (* ((sender_ready_b = false)) 
     ∧ *)
      ((sender_done_b = false))
     ∧ ((receiver_done_b = false))
     ∧ (index = num_uses)))
     .

(* If any of our receiver/sender bools are true, we know we aren't done using
the channel yet. Note that only 1 will be true which is tested with valid_state. *)
Definition not_final_state_bool (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (index: nat) (max: nat): bool :=
   bool_decide (((sender_ready_b)) 
     ∨ ((receiver_ready_b))
     ∨ ((sender_done_b))
     ∨ ((receiver_done_b))
     ∨ (index < max)) 
     .

(* A one-hot boolean decier thing to make sure we either have no waiting 
sender/receiver, the channel is closed or only one. If there is an easier
way to do a 5-way xor I would love to make it so but this works for now.  *)
Definition valid_state_bool (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (closed_b: bool): bool :=
    bool_decide ((((sender_ready_b) = false) 
     /\ ((receiver_ready_b) = false)
     /\ ((sender_done_b) = false)
     /\ ((receiver_done_b) = false)
     /\ (closed_b = false))
     \/ 
     (((sender_ready_b) = true) 
     /\ ((receiver_ready_b) = false)
     /\ ((sender_done_b) = false)
     /\ ((receiver_done_b) = false)
     /\ (closed_b = false))
      \/ 
     (((sender_ready_b) = false) 
     /\ ((receiver_ready_b) = true)
     /\ ((sender_done_b) = false)
     /\ ((receiver_done_b) = false)
    /\ (closed_b = false))
      \/ 
     (((sender_ready_b) = false) 
     /\ ((receiver_ready_b) = false)
     /\ ((sender_done_b) = true)
     /\ ((receiver_done_b) = false)
     /\ (closed_b = false))
      \/ 
     (((sender_ready_b) = false) 
     /\ ((receiver_ready_b) = false)
     /\ ((sender_done_b) = false)
     /\ ((receiver_done_b) = true)
     /\ (closed_b = false))
      \/ 
     (((sender_ready_b) = false) 
     /\ ((receiver_ready_b) = false)
     /\ ((sender_done_b) = false)
     /\ ((receiver_done_b) = false)
     /\ (closed_b = true))
     ) 
.

(* We had to be closeable to close but not the other way around. *)
Definition closed_closeable_relation (closed_b: bool) (closeable_b: bool): Prop :=
closed_b -> closeable_b.

(* R is the proposition that the sender must prove to close the channel.
The receiver can gain this proposition on the first receive after close only
since it will not block and return the null value each time after.
The lists Ps, Qs, and Vs denote the sender/receiver propositions and values 
respectively that will be used to pass messages/ownership between channel 
endpoints. num_uses is the number of times we will send/receive on the channel.
If num_uses is greater than the size of any of the 3 lists, then the default
values of True/0 will be required. This means that we can use only one aspect
of these specs gracefully but also demands that the user sends the default
value of 0 if they only intend to use the channel for synchronization, which 
I think is a reasonable style point anyway. *)
Definition is_ChanHandleV3 (l: loc) 
(Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) (R: iProp Σ) (num_uses: nat)
 γs γr γ1 γ2 γ3 γ4 γ5: iProp _ :=
  ∃ (mu_l: loc) ,
  "#mu" ∷ l ↦[ChanHandleV3 :: "mu"]□ #mu_l ∗
  "#Hlock" ∷ is_lock (nroot .@ "ChanHandleV3") (#mu_l)
     (∃ (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (closed_b: bool) (closeable_b: bool) (close_prop_ready_b: bool) (own_val: dfrac) (value: w64)
     (index: nat), 
    (* List of props that the sender must prove each time it sends. *)
    "HPs" ∷ ghost_var γ1 (DfracOwn (1/2)) Ps ∗
    (* List of props that the receiver must prove each time it sends. *)
    "HQs" ∷ ghost_var γ2 (DfracOwn (1/2)) Qs ∗
    (* List of values that the sender must send. *)
    "HVs" ∷ ghost_var γ3 (DfracOwn (1/2)) Vs  ∗
    (* The number of times we intend to use this channel. *)
    (*"HNumUses" ∷ ⌜ (length Vs) ≤ num_uses ⌝ ∗ *)
    (* Whether the channel can be closed. This gets set to true persistently 
    after all sends and receives have completed. *)
    "HCloseableGhostVar"  ∷ ghost_var γ4 own_val closeable_b  ∗
    (* When true, the receiver has not yet consumed the proposition that can be 
    gained on the first receive after a close *)
    "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) close_prop_ready_b ∗  
    (* This is somewhat obvious since we can only close when the index 
    is maxed out but having a prop here makes it easy to destruct whether
    we are in the final state or not when all of the ready/done booleans
    are false *)
    "%HMaxIndex" ∷ ⌜ index ≤ num_uses ⌝ ∗ 
    (* When all booleans are false and index is maxed out, we know we will not 
    send any more values. Closeable becomes persistent at this point so that we 
    don't try to reuse the channel. *)
    "HCloseable"  ∷ 
    (if (closeable_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b index num_uses )
    then 
    ( "%HCloseableTrue" ∷ ⌜ closeable_b = true ∧ own_val = DfracDiscarded ⌝)
    else 
     ( "%HCloseableFalse" ∷  ⌜ closeable_b = false ∧  own_val = (DfracOwn 1) ⌝)) ∗ 
     (* Once we set closeable we don't try to set any of the bools or change 
     the index again so this can be an iff which makes it easier to get the 
     index and prove everything else is false for the close specs *)
    "HCloseableIff"  ∷ 
    (if closeable_b then 
    ( "%HAllFalseIndMax" ∷ ⌜ (closeable_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b index num_uses ) ⌝)
    else True) ∗ 
     (* Make it easy to get the value of closeable from closed *)
    "HClosedCloseable"  ∷ ⌜closed_closeable_relation closed_b closeable_b ⌝ ∗ 
    (* When we can close the channel, the lock takes receiver permissions. 
    This is to allow the closer to be aware that the receiver is not attempting 
    to receive a real value. *)
    "HCloseableTakeReceiverIndex"  ∷ (if closeable_b then ((ghost_var γr (DfracOwn (1/2)) index) ∗ (ghost_var γs (DfracOwn (1/2)) index)) else True) ∗  
    (* The receiver can gain the closed prop only once. It will take ownership from the 
    lock by setting close_prop_ready_b to false and making it persistent. *)
    "HClosePropConsumed" ∷ (if closed_b then if close_prop_ready_b then R else True else True ) ∗ 
    (* Send side permissions are required to close but the sender gives up permission after closing. 
    This is to prevent sending on a closed channel which panics. 
    This also provides a means to prove that closed is false on the send side 
    since we need to ghost_var_agree with the sender index to match with the 
    Send precondition that states that index is less than max(length Vs), 
    which will produce a contradiction. *)
    "HClosedTakeSenderPermission" ∷ (if closed_b then (ghost_var γs (DfracOwn (1/2)) index) else True) ∗ 
    (* Various struct fields *)
    "Hsender_ready_b" ∷ l ↦[ChanHandleV3 :: "sender_ready"] #sender_ready_b ∗
    "Hreceiver_ready_b" ∷ l ↦[ChanHandleV3 :: "receiver_ready"] #receiver_ready_b ∗
    "Hsender_done_b" ∷ l ↦[ChanHandleV3 :: "sender_done"] #sender_done_b ∗
    "Hreceiver_done_b" ∷ l ↦[ChanHandleV3 :: "receiver_done"] #receiver_done_b ∗
    "Hclosed_b" ∷ l ↦[ChanHandleV3 :: "closed"] #closed_b ∗
    "Hvalue" ∷ l ↦[ChanHandleV3 :: "v"] #value ∗
    (* At most 1 of these bools can be true at a time.  *)
    "%HValidState" ∷ ⌜valid_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b closed_b ⌝ ∗  
    (* Make it easy to conclude that we haven't closed yet when the sender/receiver is trying to send/receive
    or we haven't yet sent/received all of our values.  *)
    "HClosedFinal" ∷ (
      if (not_final_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b index num_uses) then  
     ⌜ closed_b = false ⌝ else True) ∗  
     (* When a sender or receiver is waiting, we can't be at our max index yet *)
    "HInProgressIndexNotCapped" ∷ (
      if (any_bool_true sender_ready_b sender_done_b receiver_done_b) then  
    ("%HIndexLessThanCap" ∷  ⌜ index < num_uses ⌝) else True) ∗  
    (* The send/receive permissions that are owned by the lock. 
    These also allow us to relate the sender/receiver index so that we can
    know that the other side is at most 1 off even when we aren't holding
    the lock. *)
    "HSendFirst" ∷ (if sender_ready_b then 
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index Ps True) ∗ ⌜ value = (nth index Vs (W64 0)) ⌝)  else True)  ∗  
     "HRecFirst" ∷ (if receiver_ready_b then if bool_decide (closeable_b = false) then
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index Qs True)) else True else True) ∗  
     "HRecSecond" ∷ (if receiver_done_b then 
    (((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) (index + 1)%nat ))  ∗ (nth index Qs True)) else True)  ∗  
     "HSendSecond" ∷ (if sender_done_b then 
    ((ghost_var γs (DfracOwn (1/2)) (index + 1)%nat ) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index Ps True) ∗ ⌜ value = (nth index Vs (W64 0)) ⌝) else True  ) ∗ 
    (* 'start state' here refers to when neither the receiver nor the sender are waiting for the other.  *) 
    "HStart" ∷ (if (start_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b closeable_b )
    then
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index)) else True )  
    )
     
.       

(* Permission to send on the channel *)
Definition is_ChanHandleV3_Sender (l: loc) (i: nat) γs: iProp _ :=
  "HSenderIndex" ∷ ghost_var γs (DfracOwn (1/2)) i
.

Definition is_ChanHandleV3_SenderProps (l: loc) (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs: iProp _ :=
  ∃ 
  (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) γ1 γ2 γ3 γ4 γ5 γr,
  "#HChanHandle" ∷  is_ChanHandleV3 l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
  "HChanHandleSenderPermission" ∷  is_ChanHandleV3_Sender l i γs ∗
  (* Make sure we don't have permission when we have sent everything *)
   "%HMax" ∷  ⌜ i < num_uses ⌝  ∗ 
  (* These allow us to specify the props/value that we will 
  acquire/prove/send next *)
   "%HPssender" ∷  ⌜ (nth i Ps True%I) = P ⌝ ∗
   "%HQssender" ∷  ⌜ (nth i Qs True%I) = Q ⌝ ∗
   "%Hvssender" ∷ ⌜ (nth i Vs 0) = v ⌝
.

(* This is the permission we need to close. We use the sender permissions
here since we can give them up to the lock and not try to close twice. 
It also does not make sense to close on the receiving end so we don't allow
this. *)
Definition is_ChanHandleV3_CloserProps (l: loc) (i: nat) (R: iProp Σ) γs: iProp _ :=
  ∃ (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) (num_uses: nat) γ1 γ2 γ3 γ4 γ5 γr,
  "Hchanhand" ∷  is_ChanHandleV3 l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
  "Hchanhandsender" ∷  is_ChanHandleV3_Sender l i γs ∗
  (* Might not be necessary but should make it easier to connect this 
  with the lock invariants *)
  "%HCap" ∷  ⌜ i = num_uses ⌝ ∗ 
  (* We gain this on exit of the last send which makes it easy to prove 
  that all of the other booleans are false when we try to close *)
    "#Hcloseable"  ∷ ghost_var γ4 DfracDiscarded true 
.

(* If we have sent everything, we can only close. *)
Definition is_ChanHandleV3_SenderProps_Or_Closed
 (l: loc) (i: nat) (num_uses: nat) (R: iProp Σ) γs: iProp _ :=
match bool_decide(i < num_uses) with
  | false => is_ChanHandleV3_CloserProps l i R γs
  | true => is_ChanHandleV3_Sender  l i γs
end
 .

Definition is_ChanHandleV3_Receiver (l: loc) (i: nat) γr: iProp _ :=
  "Hreceiverindex" ∷ ghost_var γr (DfracOwn (1/2)) i
.

Definition is_ChanHandleV3_ReceiverProps (l: loc) (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses:nat) γr γ5: iProp _ :=
  ∃ 
  (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64)  γ1 γ2 γ3 γ4 γs,
  "#HChanHandle" ∷  is_ChanHandleV3 l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
   "HChanHandleReceiver" ∷  is_ChanHandleV3_Receiver l i γr ∗
    "%HPsreceiver" ∷  ⌜(nth i Ps True%I) = P⌝ ∗
    "%HQsreceiver" ∷  ⌜ (nth i Qs True%I) = Q ⌝ ∗
    "%Hvsreceiver" ∷ ⌜ (nth i Vs 0) = v ⌝ ∗ 
    "%HMax" ∷  ⌜ i < num_uses  ⌝ ∗ 
    (* The receiver must keep track of whether or not they have 
    consumed the close propositon, which can only happen once *)
    "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) true
.

(* Notably, we don't need receiver permissions to receive on a closed channel. 
Once we know a channel is able to be closed, we know the sender 
won't send anything else and receive on a closed channel always returns the
same thing. *)
Definition is_ChanHandleV3_ReceiverClosed (l: loc) (i: nat) (R: iProp Σ) γr γ5: iProp _ :=
  ∃ (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) (num_uses: nat) γ1 γ2 γ3 γ4 γs,
  "#Hchanhand" ∷  is_ChanHandleV3 l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
  "%HCap" ∷  ⌜ i = num_uses ⌝ ∗ 
  "#Hcloseable"  ∷ ghost_var γ4 DfracDiscarded true 
.

(* γ5 gives a single receiver the permission to acquire the closed 
proposition from the sender the first time a blocking receive on a closed 
channel is complete. After that point, while there wouldn't be much useful
semantics for it, it is perfectly valid to duplicate the receiver permissions
so that other threads can pointlessly receive on a closed channel and 
return the null value. I am trying to be minimal here since it may be 
possible in the future to regain the original permissions *)
Definition is_ChanHandleV3_ReceiverConsumeCloseProp (l: loc) (i: nat) (R: iProp Σ) γr γ5: iProp _ :=
  "#HRecClosed" ∷ is_ChanHandleV3_ReceiverClosed l i R γr γ5 ∗ 
  "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) true   
.

(* Once we have received all of the values we know the sender will not send
anymore but may close the channel. Note that we can regain 
is_ChanHandleV3_Receiver from the persistent props so we only need to retain
the receiver permission to receive again. *)
Definition is_ChanHandleV3_ReceiverProps_Or_Closed
 (l: loc) (i: nat) (num_uses: nat) (R: iProp Σ) γr γ5: iProp _ :=
match bool_decide(i < num_uses) with
  | false =>  is_ChanHandleV3_ReceiverConsumeCloseProp l i R γr γ5
  | true => is_ChanHandleV3_Receiver l i γr
end
 .

Lemma wp_ChanHandleV3__Close (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) γs :
i + 1 < 2 ^ 63 ->
  {{{ is_ChanHandleV3_CloserProps l i R γs ∗ R}}}
   ChanHandleV3__Close #l
  {{{RET #(); True }}}.
  Proof.
  iIntros "%Hilt %Φ [HcloserProps HR] HΦ".
  iNamed "HcloserProps". unfold is_ChanHandleV3_Sender. 
  unfold is_ChanHandleV3. iNamed "Hchanhand".
  iNamed "Hchanhandsender".
  wp_rec.
  wp_loadField.
   wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked inv]" . wp_pures. 
  iNamed "inv". 
 iDestruct (ghost_var_agree with "HCloseableGhostVar Hcloseable") as %->.
  unfold closeable_bool. iNamed "HCloseableIff".
  apply bool_decide_unpack in HAllFalseIndMax.
  destruct HAllFalseIndMax as (Hsr & Hsd & Hrd & Hind).
  subst.
  iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
  destruct closed_b. {
    iCombine "HSenderIndex HClosedTakeSenderPermission" as "Hsi2".
    iDestruct (ghost_var_valid_2 with "Hsi Hsi2") as "%Hf". 
    simpl in Hf. destruct Hf as [Hf1 Hf2]. done.
  }
  {
    wp_loadField. wp_pures.
  wp_storeField. wp_storeField.
  wp_loadField. 
  
  wp_apply (wp_Mutex__Unlock
     with "[ Hreceiver_ready_b 
      Hclosed_b HSenderIndex Hcloseable  HR Hri Hsi
     Hvalue HReceiverClosedProp
     Hsender_ready_b Hsender_done_b Hreceiver_done_b
       HQs HPs HVs $locked]").
       {
        iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
        unfold closed_closeable_relation. unfold not_final_state_bool.
        iSimpl. iFrame. 
        destruct close_prop_ready_b.
        {
         iFrame. iSimpl. rewrite bool_decide_true.
         { rewrite bool_decide_false.
          { done.  }
          { lia. }
         }
         { done. }
        }
        {
         iFrame. iSimpl. rewrite bool_decide_true.
         { rewrite bool_decide_false.
          { done.  }
          { lia. }
         }
         { done. }
        }
        }
        wp_pures. iModIntro. iApply "HΦ". done. 
  }
    Qed.

(* By proving P and sending v, we can gain Q. i is the number of times we 
have sent so far which is used as an index into the lists of propositions
 and values that we declare when we initialize the channel. *)
Lemma wp_ChanHandleV3__Send (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs :
i + 1 < 2 ^ 63 ->
  {{{ is_ChanHandleV3_SenderProps l P Q R v i num_uses γs ∗ P }}}
   ChanHandleV3__Send #l #v
  {{{ RET #(); 
  is_ChanHandleV3_SenderProps_Or_Closed l (i + 1) num_uses R γs ∗ Q  }}}.
Proof.
  iIntros "%Hilt %Φ [Hchanhandle HP] HΦ".
  unfold is_ChanHandleV3_SenderProps. iNamed "Hchanhandle". 
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_early). iIntros "HRetEarly". wp_pures.
  unfold is_ChanHandleV3_Sender. 
  unfold is_ChanHandleV3. 
  iNamed "HChanHandle".
   wp_apply (wp_forBreak (λ continue,
   (
    "LoopInv_ClosedThings" ∷  ( ∃ (ret_early_b: bool) (send_index: nat), 
    "LoopInv_RetEarlyFalse" ∷ (return_early ↦[boolT] #ret_early_b) ∗
    "LoopInv_RecIndex" ∷  (ghost_var γs (DfracOwn (1/2)) send_index) ∗   
    "%LoopInv_Break" ∷  (if continue
    then ("%LoopInv_Cont" ∷ ⌜ret_early_b = false ∧ (send_index = i)⌝%I ∗ 
    "HP" ∷ P)
    else ( if ret_early_b then (Q ∗ ⌜send_index = (i + 1)%nat⌝ )%I else ⌜send_index = i⌝  )%I) 
    ) 
    (* We know we are closed, should stay the default *)
    ))%I
    with "[] [HP HRetEarly HChanHandleSenderPermission] [HΦ]").
    {
      clear Φ.
      iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".
      wp_loadField.  
     wp_apply (wp_Mutex__Lock with "Hlock"). 
      iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
      destruct LoopInv_Cont as [Hre Hsi].
      destruct receiver_ready_b.
      {
       iAssert (⌜closed_b = false⌝)%I with "[HClosedFinal]" as "%Hcb".
       { unfold not_final_state_bool. 
       rewrite bool_decide_true.  
       { done.  }
       { set_solver. }
       }
       subst closed_b.
       destruct (bool_decide (index < num_uses)) eqn: H.
       { 
         apply bool_decide_eq_true in H. 
         iAssert (⌜closeable_b = false ∧ own_val = DfracOwn 1⌝)%I with "[HCloseable]" as "%Hcb".
         { unfold closeable_bool. 
          rewrite bool_decide_false.
          { iNamed "HCloseable". iPureIntro. done. }
          { lia. }
         }
         destruct Hcb as (Hcb & Hov).
         subst closeable_b. iSimpl in "HRecFirst". iDestruct "HRecFirst" as "(Hsi & Hri & HQ)".
         subst send_index. 
         iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
          iAssert (bupd((ghost_var γs (DfracOwn 1) (i + 1)%nat)%I)) with
              "[LoopInv_RecIndex Hsi]" as "Hsi".
              {
                iMod (ghost_var_update_2 (i + 1)%nat with "LoopInv_RecIndex Hsi") as "[H1 H2]".
                { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
                { iModIntro.  iFrame. }
              }
          iDestruct "Hsi" as ">Hsi".
          iDestruct "Hsi" as "[Hs1 Hs2]".
          wp_pures. wp_storeField. wp_storeField.
          wp_storeField. wp_loadField.
          unfold valid_state_bool in HValidState.
          assert (sender_ready_b = false).
          { set_solver. }
          assert (sender_done_b = false).
          { set_solver. }
          subst. 
          
          wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          HRecSecond HReceiverClosedProp 
           HP Hs1 HSendFirst Hri 
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl. iPureIntro. simpl.
            unfold closed_closeable_relation. unfold valid_state_bool.
            rewrite bool_decide_true.
            { set_solver. }
            { set_solver. }
          }
          {
           wp_pures. wp_store. iModIntro. iApply "HΦ". iFrame. iFrame "HQ". done. 
          }
       }
       {
         apply bool_decide_eq_false in H. 
        wp_pures. wp_storeField. wp_storeField. wp_storeField. wp_loadField.
        unfold valid_state_bool in HValidState.
        assert (sender_ready_b = false).
        { set_solver. }
        assert (receiver_done_b = false).
        { set_solver. }
        subst.
        assert (sender_done_b = false).
        { set_solver. }
        subst.
         iAssert (⌜closeable_b = true ∧ own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hcb".
         { unfold closeable_bool. 
          rewrite bool_decide_true.
          { iNamed "HCloseable". iPureIntro. done. }
          { lia. }
         }
         destruct Hcb as (Hcb & Hov).
         subst closeable_b.
         unfold closeable_bool. iNamed "HCloseableIff".
         iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
         iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
         done.
       }
      }
      {
        wp_pures.
        destruct (bool_decide((sender_ready_b = false) ∧ (sender_done_b = false) ∧ (receiver_done_b = false))) eqn: H.
        {
          apply bool_decide_eq_true in H.
          destruct closeable_b. {
          iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
          subst send_index.
          iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
          unfold closeable_bool.
          iAssert (⌜true = false ∧ own_val = DfracOwn 1⌝)%I with "[HCloseable]"
          as "%Hf".
          { rewrite bool_decide_false.
            { done.  }
            { lia.  }  
          }
          set_solver.
          }
          {
            unfold closed_closeable_relation.
            iDestruct "HClosedCloseable" as "%HClosedCloseable".
           assert (closed_b = false).
           { case closed_b eqn: Hf.
            { set_solver. }
            { done. }   
           }
           subst closed_b. 
           wp_loadField. wp_pures. wp_loadField. wp_pures. wp_loadField.
           wp_pures. destruct H as (Hsr & Hsd & Hrd).
           subst. wp_pures. wp_loadField. wp_pures. wp_loadField. wp_pures.
           wp_storeField. wp_storeField. wp_loadField. 
           unfold start_state_bool. iSimpl in "HStart".
           iDestruct "HStart" as "[Hsi Hri]".
          iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
          unfold closeable_bool.
          iSimpl in "HCloseable".
          iAssert (⌜false = false ∧ own_val = DfracOwn 1⌝%I) with "[HCloseable]" as "%HCloseable".
          { rewrite bool_decide_false.
            { done.  }
            { lia.  }
          }

           wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          HRecSecond HReceiverClosedProp 
           HP HSendFirst Hsi Hri
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. unfold closeable_bool. iSimpl.
            iPureIntro. simpl. done.
          }
          {
            wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
          }
          }
        }
        {
          apply bool_decide_eq_false in H.
          unfold not_final_state_bool.
          iAssert (⌜closed_b = false⌝)%I with "[HClosedFinal]" as "%Hclosed".
          { rewrite bool_decide_true.
            { done. }
            { simpl in H. simpl.
             destruct (sender_ready_b).
             { set_solver. }
             { destruct sender_done_b.
              { set_solver. }
              {
                destruct receiver_done_b.
                { set_solver. }
                {
                 set_solver. 
                }
              }  
             }
            }  
          }
          subst closed_b. wp_loadField. wp_pures.
          wp_loadField. wp_pures. wp_loadField.
          destruct sender_ready_b.
          {
           wp_pures. wp_loadField.
           unfold valid_state_bool in HValidState.
           assert (sender_done_b = false).
           { set_solver. }
           assert (receiver_done_b = false).
           { set_solver. }
           subst sender_done_b. subst receiver_done_b.
           iDestruct "HSendFirst" as "(Hsi & Hri & HP2 & %Hv)".
           iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
           subst send_index. replace (nth i Ps True%I) with P.
            wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HRecSecond HReceiverClosedProp HP
             HCloseable HCloseableIff Hsi Hri
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl. unfold closed_closeable_relation.
            replace (nth i Ps True%I) with P. iFrame.
            iPureIntro. simpl. set_solver.
          }
          {
           wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
          }
          }
          {
           destruct sender_done_b.
           {
           wp_pures. wp_loadField.  
           
           unfold valid_state_bool in HValidState.
           assert (receiver_done_b = false).
           { set_solver. }
            subst receiver_done_b.
            wp_pures. wp_loadField. wp_pures.
            wp_loadField.
              wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HRecSecond HReceiverClosedProp HClosedCloseable
             HCloseable HCloseableIff HInProgressIndexNotCapped HSendSecond HStart
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl. done.
          }
          {
           wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
          }
          }
          {
           wp_pures. wp_loadField. 
           destruct receiver_done_b.
           {
            wp_pures. wp_loadField. unfold any_bool_true.
            iSimpl in "HInProgressIndexNotCapped".
            iNamed "HInProgressIndexNotCapped".
              wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HRecSecond HReceiverClosedProp HClosedCloseable
            
             HCloseable HCloseableIff HSendSecond HStart
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
            { 
              iFrame "#". iModIntro. iFrame. iSimpl. done. 
            }
            {
            wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
            }
           }
           {
            set_solver.
           } 
          }
        }
      }
      }
    }
    {
     iFrame. done.
    }
    {
      iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
      wp_pures. wp_load. 
      destruct ret_early_b.
      {
           wp_pures. 
           wp_apply (wp_forBreak (λ continue,
          (
            "LoopInv_ClosedThings" ∷  ( ∃  (send_index: nat), 
            "LoopInv_RecIndex" ∷  (ghost_var γs (DfracOwn (1/2)) send_index) ∗
            "LoopInv_PreExisting"  ∷  ((("HQ" ∷  Q) ∗ ("%Hriplus" ∷ ⌜send_index = (i + 1)%nat⌝) )%I) ∗     
            "%LoopInv_Break" ∷  (if continue
            then (True)
            else ( if (bool_decide((i + 1)%nat = num_uses)) then ( ghost_var γ4 DfracDiscarded true )%I else True )%I) 
            ) 
            (* We know we are closed, should stay the default *)
            ))%I
            with "[] [LoopInv_ClosedThings LoopInv_RecIndex LoopInv_RetEarlyFalse] [HΦ]").
            {
              clear Φ.
              iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
              wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
              iIntros "[locked inv]". wp_pures. iNamed "inv". 
              destruct (bool_decide(receiver_ready_b = false ∧ sender_done_b = false ∧ receiver_done_b = false ∧ sender_ready_b = false)) eqn: H.
              {
                rewrite bool_decide_eq_true in H. destruct H as (Hrr & Hsd & Hrd & Hsr).
                subst. iSimpl. unfold start_state_bool. iSimpl in "HStart".
                wp_loadField. wp_loadField. wp_loadField. wp_loadField. wp_pures.
                iNamed "LoopInv_PreExisting". subst send_index0.
                destruct closeable_b.
                {
                  iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]". 
                  iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                  iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
                  iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hcb".
                  { unfold closeable_bool. apply bool_decide_unpack in HAllFalseIndMax.
                    rewrite bool_decide_true.
                    { iNamed. iPureIntro. set_solver. }
                    { set_solver. }
                  }
                  subst own_val. iDestruct "HCloseableGhostVar" as "#HCloseableGhostVar".
                  iModIntro. iApply "HΦ". iFrame "#". iFrame. 
                  apply bool_decide_unpack in HAllFalseIndMax.
                  assert ( bool_decide ((i + 1)%nat = num_uses)).
                  { rewrite bool_decide_true.
                   { done. }
                   { lia.  }  
                  }
                  replace (bool_decide ((i + 1)%nat = num_uses)) with true.
                  { iFrame "#". done. }
                  rewrite bool_decide_eq_true_2. 
                  { done. }
                  { set_solver. }
                }
                { 
                  unfold closeable_bool. iSimpl in "HCloseable".
                  destruct (bool_decide(index = num_uses)) eqn: H.
                  { apply bool_decide_eq_true in H.
                    iSimpl in "HCloseable".
                    iAssert (⌜false = true ∧ own_val = DfracDiscarded⌝)%I with "[HCloseable]"
                    as "%Hcb". 
                    { rewrite bool_decide_true.
                      { done. }
                      { set_solver.  }
                    }
                    set_solver.
                  }
                  {
                     apply bool_decide_eq_false in H.
                     assert (index < num_uses).
                     { lia. }

                  

                 iSimpl in "HStart".
                 iDestruct "HStart" as "[Hsi Hri]".
                 iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                 iModIntro. iApply "HΦ". iFrame. 
                 replace (bool_decide((i+1)%nat = num_uses)) with false.
                 { done.  }
                 { rewrite bool_decide_eq_false_2. 
                  { done. }
                  { done. }
                 }
                }
                }
                }
                { 
                  destruct receiver_ready_b.
                  { 
                    unfold not_final_state_bool. iSimpl in "HClosedFinal".
                    iAssert (⌜closed_b = false⌝)%I with "[HClosedFinal]" as "%Hclosed".
                    { rewrite bool_decide_true.
                      { done. }
                      { set_solver. }
                    }
                    subst closed_b.
                    wp_loadField. wp_pures. wp_loadField. 
                    unfold valid_state_bool in HValidState.
                    assert (sender_done_b = false).
                    { set_solver. }
                    assert (receiver_done_b = false).
                    { set_solver. }
                    assert (sender_ready_b = false).
                    { set_solver. }
                    subst. unfold closeable_bool. unfold any_bool_true.
                    iSimpl in "HInProgressIndexNotCapped".
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
                      unfold closed_closeable_relation. unfold valid_state_bool.
                      iSimpl. set_solver. 
                    } 
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                    }
                  }
                  {
                   wp_loadField. wp_pures.
                   destruct sender_ready_b.
                   {
                    wp_loadField. wp_pures. wp_loadField.
                    unfold closeable_bool. iSimpl in "HCloseable". 
                    iNamed "HCloseable".
                    destruct HCloseableFalse as [Hcbf Hov].
                    subst closeable_b. unfold closed_closeable_relation.
                    iDestruct "HClosedCloseable" as "%Hcc".
                    assert (closed_b = false).
                    { case closed_b eqn: Hs.
                     { set_solver. }
                     done.  
                     }
                     subst closed_b.
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                     HClosedFinal HRecFirst HRecSecond HReceiverClosedProp 
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    {
                      iFrame "#". iModIntro. iFrame. iSimpl. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame.  
                    } 
                   }
                   {
                     wp_loadField. wp_pures. wp_loadField.
                     destruct receiver_done_b.
                     {
                       unfold valid_state_bool in HValidState.
                       assert(sender_done_b = false).
                       { set_solver.  }
                       subst sender_done_b.
                       wp_pures. wp_loadField.
                       unfold closeable_bool. iSimpl in "HCloseable". 
                      iNamed "HCloseable".
                      destruct HCloseableFalse as [Hcbf Hov].
                      subst closeable_b. unfold closed_closeable_relation.
                      iDestruct "HClosedCloseable" as "%Hcc".
                      assert (closed_b = false).
                      { case closed_b eqn: Hs.
                      { set_solver. }
                      done.  
                      }
                      subst closed_b.
                      wp_apply (wp_Mutex__Unlock
                      with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                      HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                      HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                      {
                        iFrame "#". iModIntro. iFrame. iExists index. iFrame.
                         iSimpl. done.
                      }
                      {
                        wp_pures. iModIntro. iApply "HΦ". iFrame. 
                      }
                     }
                     {
                      wp_pures. wp_loadField.
                      unfold valid_state_bool in HValidState.
                      assert (sender_done_b = true).
                      { set_solver. }
                      subst sender_done_b.
                      wp_pures. wp_loadField. 
                       unfold closeable_bool. iSimpl in "HCloseable". 
                      iNamed "HCloseable".
                      destruct HCloseableFalse as [Hcbf Hov].
                      subst closeable_b. unfold closed_closeable_relation.
                      iDestruct "HClosedCloseable" as "%Hcc".
                      assert (closed_b = false).
                      { case closed_b eqn: Hs.
                      { set_solver. }
                      done.  
                      }
                      subst closed_b.
                      wp_apply (wp_Mutex__Unlock
                      with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                      HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                      HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                      {
                        iFrame "#". iModIntro. iFrame. iSimpl. done.

                      }
                      {
                        wp_pures. iModIntro. iApply "HΦ". iFrame. 
                      }

                     }
                   } 
                  }
                } 
              }
              {
               iFrame. 
              }
              {
               iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
               wp_pures. iModIntro. subst v. iApply "HΦ".
               unfold is_ChanHandleV3_SenderProps_Or_Closed.
               destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
               {
                apply bool_decide_eq_true in H.
                unfold is_ChanHandleV3_Receiver.
                iNamed "LoopInv_PreExisting".
                subst send_index0.
                iFrame.
               }
               {
                apply bool_decide_eq_false in H.
                assert ((i + 1)%nat = num_uses).
                {
                  lia.
                }
                iFrame. unfold is_ChanHandleV3_CloserProps.
                unfold is_ChanHandleV3_Sender.
                iFrame "#". iFrame. subst num_uses. rewrite bool_decide_true.
                { iFrame. iNamed "LoopInv_PreExisting". iFrame. subst send_index0. iFrame.
                 done.  }
                 done.

               }
              }
          }
          {
            wp_pures. 
            wp_apply (wp_forBreak (λ continue,
            (
              "LoopInv_ClosedThings" ∷  ( ∃ (return_val: w64) (send_index: nat), 
              "LoopInv_RecIndex" ∷  (ghost_var γs (DfracOwn (1/2)) send_index) ∗
              "%LoopInv_Break" ∷  (if continue
              then ("%LoopInv_Cont" ∷ ⌜(send_index = i)⌝%I )
              else ( (Q ∗ ⌜send_index = (i + 1)%nat⌝ )%I)%I) ∗ 
               "%LoopInv_Break2" ∷ (if continue then True else (if (bool_decide((i + 1)%nat = num_uses)) then ( ghost_var γ4 DfracDiscarded true )%I else True ))  
              ) 
              (* We know we are closed, should stay the default *)
              ))%I
              with "[] [ LoopInv_RecIndex LoopInv_ClosedThings] [HΦ]").
              {
                 clear Φ.
                iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
                wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
                iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
                 destruct closeable_b.
                { 
                  iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
                  apply bool_decide_unpack in HAllFalseIndMax. 
                  replace send_index0 with i. 
                  {
                  iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
                  iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                  lia. 
                  }
                }
                {
                  iDestruct "HClosedCloseable" as "%HClosedCloseable".
                  assert(closed_b = false).
                  {
                   unfold closed_closeable_relation in HClosedCloseable.
                    case closed_b eqn: H.
                    { set_solver. }
                    { done. } 
                  }
                  subst closed_b.
                  wp_pures.
                  destruct receiver_done_b.
                  {
                   unfold valid_state_bool in HValidState.
                  wp_pures. 
                   wp_storeField. wp_loadField. 
                 
                    assert (receiver_ready_b = false).
                    { set_solver. }
                    assert (sender_done_b = false).
                    { set_solver. }
                    assert (sender_ready_b = false).
                    { set_solver. }
                    subst. unfold closeable_bool. unfold any_bool_true.
                    iSimpl in "HInProgressIndexNotCapped".
                    iDestruct "HRecSecond" as "(Hsi & HQ)".
                    iDestruct "Hsi" as "[Hsi Hri]".
                    iDestruct (ghost_var_agree with "LoopInv_RecIndex Hsi") as %<-.
                    iAssert (bupd((ghost_var γs (DfracOwn 1) (i + 1)%nat)%I)) with
                        "[LoopInv_RecIndex Hsi]" as "Hsi".
                        {
                          iMod (ghost_var_update_2 (i + 1)%nat with "LoopInv_RecIndex Hsi") as "[H1 H2]".
                          { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
                          { iModIntro.  iFrame. }
                        }
                        destruct (bool_decide((i + 1)%nat = num_uses)) eqn: H.
                        {
                                apply bool_decide_eq_true in H.
                                
                              
            
                          iDestruct "Hsi" as ">Hsi".
                          iDestruct "Hsi" as "[Hs1 Hs2]". 
                          iAssert (⌜false = false⌝ ∗ ⌜own_val = (DfracOwn 1)⌝)%I with 
                          "[HCloseable]" as "[%Hcb %Hov]".
                          { unfold start_state_bool. rewrite bool_decide_false.
                            { iNamed "HCloseable". done. }
                            { lia. }
                          }
                          subst.
                          
                          iAssert (bupd((ghost_var γ4 DfracDiscarded true)%I)) with
                              "[HCloseableGhostVar]" as "HCloseableGhostVar".
                              {
                                iMod (ghost_var_update true with "HCloseableGhostVar") as "HCloseable2".
                                
                                { iApply ghost_var_persist. iFrame.  }
                              }
                              iDestruct "HCloseableGhostVar" as ">HcloseableGhostVar".
                              iDestruct "HcloseableGhostVar" as "#HcloseableGhostVar".
                          wp_apply (wp_Mutex__Unlock
                          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                          HRecFirst HReceiverClosedProp Hri
                          Hs1 HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HcloseableGhostVar
                          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                          {
                            iFrame "#". iModIntro. iFrame. iSimpl. iFrame "#". iSimpl. iExists (i+1)%nat.
                            rewrite bool_decide_true.
                            { iSimpl. unfold not_final_state_bool. iSimpl. unfold closed_closeable_relation.
                              iSimpl. 
                              rewrite bool_decide_false.
                              { iFrame. done. }
                              { lia. } 
                            } done. 
                          }
                          {
                            wp_pures. iModIntro. iApply "HΦ". iFrame. iFrame "#". done. 
                          }
                        }
                        {
                          apply bool_decide_eq_false in H.
                          iAssert (⌜false = false⌝ ∗ ⌜own_val = (DfracOwn 1)⌝)%I with 
                          "[HCloseable]" as "[%Hcb %Hov]".
                          { unfold start_state_bool. rewrite bool_decide_false.
                            { iNamed "HCloseable". done. }
                            { lia. }
                          }
                          subst. iDestruct "Hsi" as ">Hsi".
                          iDestruct "Hsi" as "[Hsi1 Hsi2]".
                          wp_apply (wp_Mutex__Unlock
                          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                          HRecFirst HReceiverClosedProp 
                          HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                          Hsender_done_b Hreceiver_ready_b Hsender_ready_b Hri Hsi1 HCloseableGhostVar
                          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                          {
                            iFrame "#". iModIntro. iFrame. iExists (i + 1)%nat.
                            iSimpl. iFrame. 
                            rewrite bool_decide_false. 
                            { unfold closed_closeable_relation. unfold not_final_state_bool.
                              iSimpl. 
                              rewrite bool_decide_true.
                              { iPureIntro. assert (False -> False).
                                { done. }
                                  assert((i + 1)%nat ≤ num_uses).
                                  { lia. }
                                  set_solver.
                              }
                              { lia. }
                            }
                            {
                             set_solver. 
                            }
                          }
                          {
                            wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                          }
                        }
                  }
                  {
                    wp_loadField. wp_loadField. 
                    wp_apply (wp_Mutex__Unlock
                        with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                        HRecFirst HSendSecond HReceiverClosedProp HCloseable HClosedFinal
                        HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                        Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                        HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                        {
                          iFrame "#". iModIntro. iFrame. iSimpl. unfold closed_closeable_relation.
                          iSimpl. unfold valid_state_bool. iPureIntro. set_solver.
                        }
                        {
                          wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                        }
                  }
                }
              }
              { 
               iFrame. done.
              }
              {
               iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
               wp_pures. iDestruct "LoopInv_ClosedThings" as "(HQ & Hgv)".
               iDestruct "HQ" as "[HQ %Hsi]".

               subst v. wp_pures. iModIntro.
                iApply "HΦ". iFrame. unfold is_ChanHandleV3_SenderProps_Or_Closed.
                case bool_decide eqn:H.
                {
                 apply bool_decide_eq_true in H.
                rewrite bool_decide_false.
                {  
                 unfold is_ChanHandleV3_CloserProps.
                 unfold is_ChanHandleV3_Sender.

                 iFrame. iFrame "#". subst send_index0. iFrame. done.
                }
                { lia.  }
                }
                {

                 apply bool_decide_eq_false in H. 
                 rewrite bool_decide_true.
                 {
                  unfold is_ChanHandleV3_Sender.
                  subst send_index0. iFrame.
                 } 
                 lia.
                }
               

              }
          }

                  }
Qed. 

(* By proving Q, we can gain P and know that the return value is v. 
i is the number of times we have received so far which is used as an index
into the lists of propositions and values. *)
Lemma wp_ReusableChanHandle__Receive (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γr γ5 :
  {{{ is_ChanHandleV3_ReceiverProps l P Q R v i num_uses γr γ5 ∗ Q }}}
    ChanHandleV3__Receive3 #l
  {{{ RET (#v, #false); is_ChanHandleV3_ReceiverProps_Or_Closed
    l (i + 1) num_uses R γr γ5 ∗ P }}}.
Proof.
   iIntros "%Φ [Hchanhand HQ] HΦ".
  unfold is_ChanHandleV3_ReceiverProps. iNamed "Hchanhand".
  iNamed "HChanHandle".
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_early). iIntros "HRetEarly". wp_pures.
  unfold is_ChanHandleV3_Receiver. 
  unfold is_ChanHandleV3. 
  wp_apply wp_ref_to.
    { val_ty. }
  iIntros (closed_local) "HClosedLocal".
  wp_pures.
  wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_value). iIntros "HReturnValue". wp_pures.
   wp_apply (wp_forBreak (λ continue,
   (
    "LoopInv_ClosedThings" ∷  ( ∃ (ret_early_b: bool) (return_val: w64) (rec_index: nat), 
    "LoopInv_ClosedLocal" ∷ (closed_local ↦[boolT] #false) ∗
    "LoopInv_RetEarlyFalse" ∷ (return_early ↦[boolT] #ret_early_b) ∗
    "LoopInv_ClosedPropReady" ∷  (ghost_var γ5 (DfracOwn (1/2)) true) ∗
    "LoopInv_RecIndex" ∷  (ghost_var γr (DfracOwn (1/2)) rec_index) ∗
    "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #return_val)  ∗     
    "%LoopInv_Break" ∷  (if continue
    then ("%LoopInv_Cont" ∷ ⌜ret_early_b = false ∧ (rec_index = i)⌝%I ∗ 
    "HQ" ∷ Q)
    else ( if ret_early_b then (P ∗ ⌜rec_index = (i + 1)%nat⌝ ∗ ⌜return_val = (nth i Vs (W64 0))%nat⌝ )%I else ⌜rec_index = i⌝ )%I) 
    ) 
    (* We know we are closed, should stay the default *)
    ))%I
    with "[] [HReturnValue HClosedLocal HRetEarly HQ HChanHandleReceiver HReceiverClosedProp] [HΦ]").
    {
      clear Φ.
      iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
      wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
      iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
      destruct closeable_b.
      { 
        iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
        apply bool_decide_unpack in HAllFalseIndMax. 
        replace rec_index with i. 
        {
          iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
        iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
        lia. 
        }
        { lia. } 
      }
      { iDestruct "HClosedCloseable" as "%HCloseCloseable".
        assert(closed_b = false).
        { unfold closed_closeable_relation in HCloseCloseable.
         simpl in HCloseCloseable.
        destruct closed_b.
        { simpl in HCloseCloseable. done. }
        { done.  }
        }
        subst closed_b.
        destruct sender_ready_b.
        {
          wp_pures. wp_loadField. wp_storeField. wp_storeField. wp_loadField.
          wp_store. wp_loadField. unfold valid_state_bool in HValidState.
          assert (receiver_ready_b = false).
          {  set_solver. }
          assert (sender_done_b = false).
          { set_solver. }
          subst receiver_ready_b. subst sender_done_b. 
          assert (receiver_done_b = false).
          { set_solver. }
          subst receiver_done_b.
          iDestruct "HSendFirst" as "(Hsi & Hri & HP & %Hvs)".
          destruct LoopInv_Cont as (Hre & Hri_pure).
          subst rec_index.
          iDestruct (ghost_var_agree with "LoopInv_RecIndex Hri") as %<-.
          iAssert (bupd((ghost_var γr (DfracOwn 1) (i + 1)%nat)%I)) with
              "[LoopInv_RecIndex Hri]" as "Hri".
              {
                iMod (ghost_var_update_2 (i + 1)%nat with "LoopInv_RecIndex Hri") as "[H1 H2]".
                { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
                { iModIntro.  iFrame. }
              }
          iDestruct "Hri" as ">Hri".
          iDestruct "Hri" as "[Hr1 Hr2]". 
          subst value.
          wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
          HSendSecond HInProgressIndexNotCapped Hr1 HQ Hsi
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iExists i. replace (nth i Qs True%I) with Q.
            iFrame. done. 
          }
          {
            wp_pures. wp_store. iModIntro. iApply "HΦ". replace (nth i Ps True%I) with P.
            iFrame. 
            iSplitL "HP". 
            { done. }    
            done.
          }
        }
        { 
          destruct (bool_decide(receiver_ready_b = false ∧ sender_done_b = false ∧ receiver_done_b = false)) eqn: H.
          {
            rewrite bool_decide_eq_true in H. destruct H as (Hrr & Hsd & Hrd).
            subst. iSimpl. unfold start_state_bool. iSimpl in "HStart".
            iDestruct "HStart" as "[Hsi Hri]".
            destruct LoopInv_Cont as [Hre Hripure].  
            subst rec_index.
            iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
            unfold closeable_bool. wp_pures. wp_loadField. wp_pures.
            wp_loadField. wp_pures. wp_loadField. wp_pures. wp_loadField.
            wp_pures. wp_loadField. wp_storeField. wp_loadField.
            wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
            HSendSecond HInProgressIndexNotCapped Hri HQ Hsi
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
            { 
              iFrame "#". iModIntro. iFrame. done.
            } 
          {
           wp_pures. iModIntro. iApply "HΦ". iFrame. subst ret_early_b. done. 
          }
        }
        {
          wp_pures. wp_loadField. wp_pures. wp_loadField. 
          destruct receiver_ready_b.
          {
            wp_pures. wp_loadField.
            wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
            HSendSecond HInProgressIndexNotCapped  
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
            { 
              iFrame "#". iModIntro. iFrame. done.
            }
            {
              wp_pures. iModIntro. iApply "HΦ". iFrame. done.
            }
          }
          destruct sender_done_b. 
          {
            wp_pures. wp_loadField. wp_pures. wp_loadField.
            assert (receiver_done_b = false).
            { unfold valid_state_bool in HValidState. set_solver. }
            subst receiver_done_b. wp_pures. wp_loadField. wp_pures.
            wp_loadField.
            wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
            HSendSecond HInProgressIndexNotCapped  
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
            { 
              iFrame "#". iModIntro. iFrame. done.
            }
            {
             wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
            }
          }
          wp_pures. wp_loadField. wp_pures. wp_loadField. 
          destruct receiver_done_b.
          {
           wp_pures. wp_loadField.
           wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
            HSendSecond HInProgressIndexNotCapped 
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
            { 
              iFrame "#". iModIntro. iFrame. iExists index. iFrame. done.
            }
            {
             wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
            }
          }
          {
           wp_pures. wp_loadField. wp_pures. wp_storeField. wp_loadField. 
           iSimpl in "HStart". 
          destruct LoopInv_Cont as (Hre & Hri_pure).
          subst rec_index. iDestruct "HStart" as "[Hsi Hri]".
          iDestruct (ghost_var_agree with "LoopInv_RecIndex Hri") as %<-.
           wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
            HSendSecond HInProgressIndexNotCapped HQ Hsi Hri
            Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
            HClosedTakeSenderPermission  HQs HPs HVs $locked]").
            { 
              iFrame "#". iModIntro. iFrame. replace (nth i Qs True%I) with Q.
              iSimpl. iFrame. done.
            }
            {
              wp_pures. iModIntro. iApply "HΦ". iFrame. subst ret_early_b. done. 
            }
            }
            }
            }
            }
          }
        {
          iFrame. done.
        }
        {
          iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
          wp_pures. wp_load. wp_pures. wp_load. 
          destruct ret_early_b.
          {
           wp_pures. 
           wp_apply (wp_forBreak (λ continue,
          (
            "LoopInv_ClosedThings" ∷  ( ∃  (rec_index: nat), 
            "LoopInv_ClosedPropReady" ∷  (ghost_var γ5 (DfracOwn (1/2)) true) ∗
            "LoopInv_RecIndex" ∷  (ghost_var γr (DfracOwn (1/2)) rec_index) ∗
            "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #(nth i Vs (W64 0)))  ∗
            "LoopInv_PreExisting"  ∷  ((("HP" ∷  P) ∗ ("%Hriplus" ∷ ⌜rec_index = (i + 1)%nat⌝) )%I) ∗     
            "%LoopInv_Break" ∷  (if continue
            then (True)
            else ( if (bool_decide((i + 1)%nat = num_uses)) then ( ghost_var γ4 DfracDiscarded true )%I else True )%I) 
            ) 
            (* We know we are closed, should stay the default *)
            ))%I
            with "[] [LoopInv_ClosedPropReady LoopInv_RecIndex LoopInv_ReturnValue LoopInv_ClosedThings] [HΦ]").
            {
              clear Φ.
              iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
              wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
              iIntros "[locked inv]". wp_pures. iNamed "inv". 
              destruct (bool_decide(receiver_ready_b = false ∧ sender_done_b = false ∧ receiver_done_b = false ∧ sender_ready_b = false)) eqn: H.
              {
                rewrite bool_decide_eq_true in H. destruct H as (Hrr & Hsd & Hrd & Hsr).
                subst. iSimpl. unfold start_state_bool. iSimpl in "HStart".
                wp_loadField. wp_loadField. wp_loadField. wp_loadField. wp_pures.
                iNamed "LoopInv_PreExisting". subst rec_index0.
                destruct closeable_b.
                { 
                  iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
                  iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                  iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
                  iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hcb".
                  { unfold closeable_bool. apply bool_decide_unpack in HAllFalseIndMax.
                    rewrite bool_decide_true.
                    { iNamed. iPureIntro. set_solver. }
                    { set_solver. }
                  }
                  subst own_val. iDestruct "HCloseableGhostVar" as "#HCloseableGhostVar".
                  iModIntro. iApply "HΦ". iFrame "#". iFrame. 
                  apply bool_decide_unpack in HAllFalseIndMax.
                  assert ( bool_decide ((i + 1)%nat = num_uses)).
                  { rewrite bool_decide_true.
                   { done. }
                   { lia.  }  
                  }
                  replace (bool_decide ((i + 1)%nat = num_uses)) with true.
                  { iFrame "#". done. }
                  rewrite bool_decide_eq_true_2. 
                  { done. }
                  { set_solver. }
                }
                { 
                  unfold closeable_bool. iSimpl in "HCloseable".
                  destruct (bool_decide(index = num_uses)) eqn: H.
                  { apply bool_decide_eq_true in H.
                    iSimpl in "HCloseable".
                    iAssert (⌜false = true ∧ own_val = DfracDiscarded⌝)%I with "[HCloseable]"
                    as "%Hcb". 
                    { rewrite bool_decide_true.
                      { done. }
                      { set_solver.  }
                    }
                    set_solver.
                  }
                  {
                     apply bool_decide_eq_false in H.
                     assert (index < num_uses).
                     { lia. }

                  

                 iSimpl in "HStart".
                 iDestruct "HStart" as "[Hsi Hri]".
                 iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                 iModIntro. iApply "HΦ". iFrame. 
                 replace (bool_decide((i+1)%nat = num_uses)) with false.
                 { done.  }
                 { rewrite bool_decide_eq_false_2. 
                  { done. }
                  { done. }
                 }
                }
                }
                }
                { 
                  destruct receiver_ready_b.
                  { 
                    unfold not_final_state_bool. iSimpl in "HClosedFinal".
                    iAssert (⌜closed_b = false⌝)%I with "[HClosedFinal]" as "%Hclosed".
                    { rewrite bool_decide_true.
                      { done. }
                      { set_solver. }
                    }
                    subst closed_b.
                    wp_loadField. wp_pures. wp_loadField. 
                    unfold valid_state_bool in HValidState.
                    assert (sender_done_b = false).
                    { set_solver. }
                    assert (receiver_done_b = false).
                    { set_solver. }
                    assert (sender_ready_b = false).
                    { set_solver. }
                    subst. unfold closeable_bool. unfold any_bool_true.
                    iSimpl in "HInProgressIndexNotCapped".
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
                      unfold closed_closeable_relation. unfold valid_state_bool.
                      iSimpl. set_solver. 
                    } 
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                    }
                  }
                  {
                   wp_loadField. wp_pures.
                   destruct sender_ready_b.
                   {
                    wp_loadField. wp_pures. wp_loadField.
                    unfold closeable_bool. iSimpl in "HCloseable". 
                    iNamed "HCloseable".
                    destruct HCloseableFalse as [Hcbf Hov].
                    subst closeable_b. unfold closed_closeable_relation.
                    iDestruct "HClosedCloseable" as "%Hcc".
                    assert (closed_b = false).
                    { case closed_b eqn: Hs.
                     { set_solver. }
                     done.  
                     }
                     subst closed_b.
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                     HClosedFinal HRecFirst HRecSecond HReceiverClosedProp 
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    {
                      iFrame "#". iModIntro. iFrame. iSimpl. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame.  
                    } 
                   }
                   {
                     wp_loadField. wp_pures. wp_loadField.
                     destruct receiver_done_b.
                     {
                       unfold valid_state_bool in HValidState.
                       assert(sender_done_b = false).
                       { set_solver.  }
                       subst sender_done_b.
                       wp_pures. wp_loadField.
                       unfold closeable_bool. iSimpl in "HCloseable". 
                      iNamed "HCloseable".
                      destruct HCloseableFalse as [Hcbf Hov].
                      subst closeable_b. unfold closed_closeable_relation.
                      iDestruct "HClosedCloseable" as "%Hcc".
                      assert (closed_b = false).
                      { case closed_b eqn: Hs.
                      { set_solver. }
                      done.  
                      }
                      subst closed_b.
                      wp_apply (wp_Mutex__Unlock
                      with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                      HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                      HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                      {
                        iFrame "#". iModIntro. iFrame. iExists index. iFrame.
                         iSimpl. done.
                      }
                      {
                        wp_pures. iModIntro. iApply "HΦ". iFrame. 
                      }
                     }
                     {
                      wp_pures. wp_loadField.
                      unfold valid_state_bool in HValidState.
                      assert (sender_done_b = true).
                      { set_solver. }
                      subst sender_done_b.
                      wp_pures. wp_loadField. 
                       unfold closeable_bool. iSimpl in "HCloseable". 
                      iNamed "HCloseable".
                      destruct HCloseableFalse as [Hcbf Hov].
                      subst closeable_b. unfold closed_closeable_relation.
                      iDestruct "HClosedCloseable" as "%Hcc".
                      assert (closed_b = false).
                      { case closed_b eqn: Hs.
                      { set_solver. }
                      done.  
                      }
                      subst closed_b.
                      wp_apply (wp_Mutex__Unlock
                      with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                      HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                      HSendSecond HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                      {
                        iFrame "#". iModIntro. iFrame. iSimpl. done.

                      }
                      {
                        wp_pures. iModIntro. iApply "HΦ". iFrame. 
                      }

                     }
                   } 
                  }
                } 
              }
              {
               iFrame. iDestruct "LoopInv_ClosedThings" as 
               "(HP & %Hri & %Hrv)". iFrame. subst return_val.
               iFrame. done. 
              }
              {
               iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
               wp_pures. wp_load. wp_pures. iModIntro. subst v. iApply "HΦ".
               unfold is_ChanHandleV3_ReceiverProps_Or_Closed.
               destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
               {
                apply bool_decide_eq_true in H.
                unfold is_ChanHandleV3_Receiver.
                iNamed "LoopInv_PreExisting".
                subst rec_index0.
                iFrame.
               }
               {
                apply bool_decide_eq_false in H.
                assert ((i + 1)%nat = num_uses).
                {
                  lia.
                }
                unfold is_ChanHandleV3_ReceiverConsumeCloseProp.
                iFrame. unfold is_ChanHandleV3_ReceiverClosed.
                iFrame "#". iFrame. subst num_uses. rewrite bool_decide_true.
                { iFrame. iNamed "LoopInv_PreExisting". iFrame. done.  }
                 done.

               }
              }
          }
          {
            wp_pures. 
            wp_apply (wp_forBreak (λ continue,
            (
              "LoopInv_ClosedThings" ∷  ( ∃ (return_val: w64) (rec_index: nat), 
              "LoopInv_ClosedLocal" ∷ (closed_local ↦[boolT] #false) ∗
              "LoopInv_ClosedPropReady" ∷  (ghost_var γ5 (DfracOwn (1/2)) true) ∗
              "LoopInv_RecIndex" ∷  (ghost_var γr (DfracOwn (1/2)) rec_index) ∗
              "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #return_val)  ∗     
              "%LoopInv_Break" ∷  (if continue
              then ("%LoopInv_Cont" ∷ ⌜(rec_index = i)⌝%I )
              else ( (P ∗ ⌜rec_index = (i + 1)%nat⌝ ∗ ⌜return_val = (nth i Vs (W64 0))%nat⌝ )%I)%I) ∗ 
               "%LoopInv_Break2" ∷ (if continue then True else (if (bool_decide((i + 1)%nat = num_uses)) then ( ghost_var γ4 DfracDiscarded true )%I else True ))  
              ) 
              (* We know we are closed, should stay the default *)
              ))%I
              with "[] [LoopInv_ClosedLocal LoopInv_RetEarlyFalse LoopInv_ClosedPropReady LoopInv_RecIndex LoopInv_ReturnValue LoopInv_ClosedThings] [HΦ]").
              {
                 clear Φ.
                iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
                wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
                iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
                 destruct closeable_b.
                { 
                  iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
                  apply bool_decide_unpack in HAllFalseIndMax. 
                  replace rec_index0 with i. 
                  {
                    iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
                  iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                  lia. 
                  }
                }
                {
                  iDestruct "HClosedCloseable" as "%HClosedCloseable".
                  assert(closed_b = false).
                  {
                   unfold closed_closeable_relation in HClosedCloseable.
                    case closed_b eqn: H.
                    { set_solver. }
                    { done. } 
                  }
                  subst closed_b.
                  wp_pures.
                  destruct sender_done_b.
                  {
                   unfold valid_state_bool in HValidState.
                   wp_loadField. wp_pures.
                   wp_storeField. wp_loadField. wp_store.
                   wp_loadField. 
                    assert (receiver_ready_b = false).
                    { set_solver. }
                    assert (receiver_done_b = false).
                    { set_solver. }
                    assert (sender_ready_b = false).
                    { set_solver. }
                    subst. unfold closeable_bool. unfold any_bool_true.
                    iSimpl in "HInProgressIndexNotCapped".
                    iDestruct "HSendSecond" as "(Hsi & Hri & HP & %Hvs)".
                    subst value.
                    iDestruct (ghost_var_agree with "LoopInv_RecIndex Hri") as %<-.
                    iAssert (bupd((ghost_var γr (DfracOwn 1) (i + 1)%nat)%I)) with
                        "[LoopInv_RecIndex Hri]" as "Hri".
                        {
                          iMod (ghost_var_update_2 (i + 1)%nat with "LoopInv_RecIndex Hri") as "[H1 H2]".
                          { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
                          { iModIntro.  iFrame. }
                        }
                        destruct (bool_decide((i + 1)%nat = num_uses)) eqn: H.
                        {
                                apply bool_decide_eq_true in H.
                                
                              
            
                          iDestruct "Hri" as ">Hri".
                          iDestruct "Hri" as "[Hr1 Hr2]". 
                          iAssert (⌜false = false⌝ ∗ ⌜own_val = (DfracOwn 1)⌝)%I with 
                          "[HCloseable]" as "[%Hcb %Hov]".
                          { unfold start_state_bool. rewrite bool_decide_false.
                            { iNamed "HCloseable". done. }
                            { lia. }
                          }
                          subst.
                          
                          iAssert (bupd((ghost_var γ4 DfracDiscarded true)%I)) with
                              "[HCloseableGhostVar]" as "HCloseableGhostVar".
                              {
                                iMod (ghost_var_update true with "HCloseableGhostVar") as "HCloseable2".
                                
                                { iApply ghost_var_persist. iFrame.  }
                              }
                              iDestruct "HCloseableGhostVar" as ">HcloseableGhostVar".
                              iDestruct "HcloseableGhostVar" as "#HcloseableGhostVar".
                          wp_apply (wp_Mutex__Unlock
                          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                          HRecFirst HRecSecond HReceiverClosedProp Hsi
                          Hr1 HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HcloseableGhostVar
                          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                          {
                            iFrame "#". iModIntro. iFrame. iSimpl. iFrame "#". iSimpl. iExists (i+1)%nat.
                            rewrite bool_decide_true.
                            { iSimpl. unfold not_final_state_bool. iSimpl. unfold closed_closeable_relation.
                              iSimpl. 
                              rewrite bool_decide_false.
                              { iFrame. done. }
                              { lia. } 
                            } done. 
                          }
                          {
                            wp_pures. iModIntro. iApply "HΦ". iFrame. iFrame "#". done. 
                          }
                        }
                        {
                          apply bool_decide_eq_false in H.
                          iAssert (⌜false = false⌝ ∗ ⌜own_val = (DfracOwn 1)⌝)%I with 
                          "[HCloseable]" as "[%Hcb %Hov]".
                          { unfold start_state_bool. rewrite bool_decide_false.
                            { iNamed "HCloseable". done. }
                            { lia. }
                          }
                          subst. iDestruct "Hri" as ">Hri".
                          iDestruct "Hri" as "[Hri1 Hri2]".
                          wp_apply (wp_Mutex__Unlock
                          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                          HRecFirst HRecSecond HReceiverClosedProp 
                          HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                          Hsender_done_b Hreceiver_ready_b Hsender_ready_b Hsi Hri1 HCloseableGhostVar
                          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                          {
                            iFrame "#". iModIntro. iFrame. iExists (i + 1)%nat.
                            iSimpl. iFrame. 
                            rewrite bool_decide_false. 
                            { unfold closed_closeable_relation. unfold not_final_state_bool.
                              iSimpl. 
                              rewrite bool_decide_true.
                              { iPureIntro. assert (False -> False).
                                { done. }
                                  assert((i + 1)%nat ≤ num_uses).
                                  { lia. }
                                  set_solver.
                              }
                              { lia. }
                            }
                            {
                             set_solver. 
                            }
                          }
                          {
                            wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                          }
                        }
                  }
                  {
                    wp_loadField. wp_loadField. 
                    wp_apply (wp_Mutex__Unlock
                        with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                        HRecFirst HRecSecond HReceiverClosedProp HCloseable HClosedFinal
                        HInProgressIndexNotCapped HStart HSendFirst HCloseableIff
                        Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                        HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                        {
                          iFrame "#". iModIntro. iFrame. iSimpl. unfold closed_closeable_relation.
                          iSimpl. unfold valid_state_bool. iPureIntro. set_solver.
                        }
                        {
                          wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                        }
                  }
                }
              }
              {
               iFrame.  
              }
              {
               iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
               wp_pures. wp_load. wp_load. iDestruct "LoopInv_ClosedThings" as "(HP & Hgv)".
               iDestruct "HP" as "(HP & %Hiv & %Hvs)".
               subst return_val0. subst v. wp_pures. iModIntro.
                iApply "HΦ". iFrame. unfold is_ChanHandleV3_ReceiverProps_Or_Closed.
                case bool_decide eqn:H.
                {
                 apply bool_decide_eq_true in H.
                rewrite bool_decide_false.
                {  
                 unfold is_ChanHandleV3_Receiver.
                 subst rec_index0. iFrame. iFrame "#". done.
                }
                { lia.  }
                }
                {

                 apply bool_decide_eq_false in H. 
                 rewrite bool_decide_true.
                 {
                  unfold is_ChanHandleV3_Receiver.
                  subst rec_index0. iFrame.
                 } 
                 lia.
                }
               

              }
          }

                  }
Qed. 



(* This should be used when we are using a channel closure as a notification. 
For example, we can use a channel as a join handle by passing it to a goroutine
that will close when it is done with its work and having the launching goroutine
receive as a 'join'. We would formalize the result of this work with the 
proposition R which can only be gained once. *)
Lemma wp_ReusableChanHandle__ReceiveConsumeCloseProp 
 (l: loc) (R: iProp Σ) (i: nat) γr γ5:
 {{{ is_ChanHandleV3_ReceiverConsumeCloseProp l i R γr γ5 }}}
    ChanHandleV3__Receive3 #l
  {{{ RET ( #(W64 0), #true); is_ChanHandleV3_ReceiverClosed l i R γr γ5 ∗ R }}}.
Proof.
   iIntros "%Φ Hchanhand HΦ".
  unfold is_ChanHandleV3_ReceiverConsumeCloseProp. iNamed "Hchanhand".
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_early). iIntros "HRetEarly". wp_pures.
  unfold is_ChanHandleV3_ReceiverClosed. iNamed "HRecClosed".
  unfold is_ChanHandleV3. iNamed "Hchanhand".
  wp_apply wp_ref_to.
    { val_ty. }
  iIntros (closed_local) "HClosedLocal".
  wp_pures.
  wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_value). iIntros "HReturnValue". wp_pures.
   wp_apply (wp_forBreak (λ continue,
   (
    "LoopInv_ClosedThings" ∷  ( ∃ (closed_local_b: bool) (closed_prop_ready_b: bool) , 
    "LoopInv_ClosedLocal" ∷ (closed_local ↦[boolT] #closed_local_b) ∗
    "LoopInv_RetEarlyFalse" ∷ (return_early ↦[boolT] #false) ∗
    "LoopInv_ClosedPropReady" ∷  (ghost_var γ5 (DfracOwn (1/2)) closed_prop_ready_b) ∗
    "%LoopInv_Break" ∷  (if continue
    then ⌜closed_local_b = false ∧ closed_prop_ready_b = true⌝ 
    else ( if closed_local_b then (⌜closed_prop_ready_b = false⌝ ∗ R)%I else (⌜closed_prop_ready_b = true⌝)%I )%I) 
    ) ∗
    (* We know we are closed, should stay the default *)
    "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #(W64 0))       
    ))%I
    with "[] [HReturnValue HClosedLocal HReceiverClosedProp HRetEarly] [HΦ]").
    { clear Φ.
      iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
      wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
      iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
      iDestruct (ghost_var_agree with "HCloseableGhostVar Hcloseable") as %->.
      iNamed. unfold closeable_bool in HAllFalseIndMax. apply bool_decide_unpack in HAllFalseIndMax.
      destruct HAllFalseIndMax as (Hsr & Hrr & Hsd & Hind). 
      subst. unfold not_final_state_bool. 
      destruct closed_b. {
      assert (receiver_ready_b = false).
      { unfold valid_state_bool in HValidState. set_solver.  }
      subst receiver_ready_b.
      wp_loadField. destruct LoopInv_Break as (Hclosedlocal & Hclosed_prop_ready).
       subst closed_prop_ready_b. subst closed_local_b.    
       unfold closeable_bool. 
      iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hov".
      { rewrite bool_decide_true. 
        { iNamed "HCloseable". iPureIntro. set_solver. }
        { done.  }
      }
      subst own_val.
      iDestruct (ghost_var_agree with "LoopInv_ClosedPropReady HReceiverClosedProp") as %<-.
      iAssert (bupd((ghost_var γ5 (DfracOwn 1) false)%I)) with
       "[LoopInv_ClosedPropReady HReceiverClosedProp]" as "HReceiverClosedProp".
       {
         iMod (ghost_var_update_2 false with "LoopInv_ClosedPropReady HReceiverClosedProp")
          as "[H1 H2]".
         { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
         { iModIntro. iFrame. }
       } iDestruct "HReceiverClosedProp" as ">HReceiverClosedProp".
      iDestruct "HReceiverClosedProp" as "[Hrc1 Hrc2]".
      wp_apply (wp_Mutex__Unlock
      with "[Hvalue Hclosed_b Hreceiver_done_b Hrc1 HCloseableTakeReceiverIndex
      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
       { 
         iFrame "#". iModIntro. iExists false. iExists false. iExists false. iExists false. 
         iExists true. iExists true. iExists false. iExists DfracDiscarded. iExists value. 
         iExists num_uses. iFrame "#". iFrame. unfold start_state_bool. iSimpl.
         rewrite bool_decide_true. 
         { iSimpl. 
          rewrite bool_decide_false.
          { iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
           iFrame.  done. }
          { lia. }  
         } 
         { done. }
       }
       {
        wp_pures. wp_store. iModIntro. iApply "HΦ". iFrame. iFrame "HClosePropConsumed".
        done.
       }
      }
      {
      destruct receiver_ready_b. {
      wp_loadField. wp_loadField. wp_loadField.
      iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hov".
      { unfold closeable_bool. rewrite bool_decide_true. 
        { iNamed "HCloseable". iPureIntro. set_solver. }
        { done.  }
      }
      subst own_val. iSimpl in "HRecFirst".
       wp_apply (wp_Mutex__Unlock
       with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
       Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
       HReceiverClosedProp HRecFirst
       HClosedTakeSenderPermission  HQs HPs HVs $locked]").
       { iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
        iSimpl. 
        rewrite bool_decide_true. 
        { iFrame. iPureIntro. unfold closed_closeable_relation. set_solver. }
        { done.  }
       }
       { wp_pures. iModIntro. iApply "HΦ". iFrame. done.
       }
      }
      {
       wp_loadField. wp_loadField. wp_pures. wp_loadField.
       wp_loadField. wp_loadField. subst. wp_storeField.
       wp_loadField.
       unfold closeable_bool. iSimpl in "HCloseable".
       iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hov".
      { rewrite bool_decide_true. 
        { iNamed "HCloseable". iPureIntro. set_solver. }
        { done.  }
      }
      subst own_val. destruct LoopInv_Break as (Hcb & Hcpr). subst.
      iSimpl in "HInProgressIndexNotCapped".

       wp_apply (wp_Mutex__Unlock
       with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
       Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
       HReceiverClosedProp HRecFirst 
       HClosedTakeSenderPermission  HQs HPs HVs $locked]").
       {
       iFrame "#". iModIntro. iFrame. iSimpl.
        rewrite bool_decide_true.
        { iPureIntro. done. }
        { done. }
      }
      wp_pures. iModIntro. iApply "HΦ". iFrame "LoopInv_ReturnValue".
      iFrame. done.
      }
    }
  }
  { iFrame. done.
  }
  {
    iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
    destruct closed_local_b.
    {
      wp_pures. wp_load. wp_pures. iModIntro. iApply "HΦ". iFrame "#". iFrame.
      iDestruct "LoopInv_ClosedThings" as "[%Hcr HR]". iFrame. done.
    }
    {
      wp_pures. wp_load. wp_pures. wp_load. wp_pures.
      wp_apply (wp_forBreak (λ continue,
      (
      "LoopInv_ClosedThings" ∷  ( ∃ (closed_local_b: bool) (closed_prop_ready_b: bool) , 
      "LoopInv_ClosedLocal" ∷ (closed_local ↦[boolT] #closed_local_b) ∗
      "LoopInv_ClosedPropReady" ∷  (ghost_var γ5 (DfracOwn (1/2)) closed_prop_ready_b) ∗
      "%LoopInv_Break" ∷  (if continue
      then ⌜closed_local_b = false ∧ closed_prop_ready_b = true⌝ 
      else (  (⌜closed_local_b = true ∧ closed_prop_ready_b = false⌝ ∗ R)%I )%I) 
      ) ∗
      (* We know we are closed, should stay the default *)
      "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #(W64 0))       
      ))%I
      with "[] [LoopInv_ClosedLocal LoopInv_RetEarlyFalse LoopInv_ClosedPropReady LoopInv_ReturnValue LoopInv_ClosedThings] [HΦ]").
      {
        clear Φ.
        iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
        wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
        iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
        iDestruct (ghost_var_agree with "HCloseableGhostVar Hcloseable") as %->.
        iNamed. unfold closeable_bool in HAllFalseIndMax. apply bool_decide_unpack in HAllFalseIndMax.
        destruct HAllFalseIndMax as (Hsr & Hrr & Hsd & Hind). 
        subst. unfold not_final_state_bool. 
        destruct closed_b. {
          wp_pures. wp_loadField.
          assert (receiver_ready_b = false).
          { unfold valid_state_bool in HValidState. set_solver.  }
          subst receiver_ready_b.
          destruct LoopInv_Break as (Hclosedlocal & Hclosed_prop_ready).
          subst closed_prop_ready_b0. subst closed_local_b.    
          unfold closeable_bool. 
          iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hov".
          { rewrite bool_decide_true. 
            { iNamed "HCloseable". iPureIntro. set_solver. }
            { done.  }
          }
          subst own_val.
          iDestruct (ghost_var_agree with "LoopInv_ClosedPropReady HReceiverClosedProp") as %<-.
          iAssert (bupd((ghost_var γ5 (DfracOwn 1) false)%I)) with
          "[LoopInv_ClosedPropReady HReceiverClosedProp]" as "HReceiverClosedProp".
          {
            iMod (ghost_var_update_2 false with "LoopInv_ClosedPropReady HReceiverClosedProp")
              as "[H1 H2]".
            { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
            { iModIntro. iFrame. }
          } iDestruct "HReceiverClosedProp" as ">HReceiverClosedProp".
          iDestruct "HReceiverClosedProp" as "[Hrc1 Hrc2]".
          wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b Hrc1 HCloseableTakeReceiverIndex
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iExists false. iExists false. iExists false. iExists false. 
            iExists true. iExists true. iExists false. iExists DfracDiscarded. iExists value. 
            iExists num_uses. iFrame "#". iFrame. unfold start_state_bool. iSimpl.
            rewrite bool_decide_true. 
            { iSimpl. 
              rewrite bool_decide_false.
              { iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
              iFrame. done. }
              { lia. }  
            } 
            { done. }
          }
          {
            wp_pures. wp_store. iModIntro. iApply "HΦ". iFrame. done.
          }
        }
        { wp_pures. wp_loadField. wp_pures. wp_loadField.
          wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HReceiverClosedProp HRecFirst HStart HCloseable HClosedCloseable
          HClosedFinal
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
            rewrite bool_decide_true. 
            { done. }
            { done. }  
          }
          { 
            wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
          } 
        }
      }
      { 
       iFrame. iNamed "LoopInv_ClosedThings". done.
      }
      { iModIntro. iIntros "IH". iNamed "IH". iDestruct "LoopInv_ClosedThings" as 
      "[%Ht HR]". wp_pures. wp_load. iNamed "HR". wp_load. wp_pures.
      iModIntro. iDestruct "HR" as "[%Ht2 HR]". 
      assert(Ht = true). 
      { set_solver. }
      subst Ht.
      iApply "HΦ". iFrame "#". iFrame. done. 
      }
    }
  }       
Qed. 


(* Initializing a channel requires specifying 3 lists. Ps is the list 
of propositions  *)
(*Lemma wp_ChanHandleV3__New 
(P: iProp Σ) (Q: iProp Σ) (v: w64) (size: w64)
(Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) 
  :
  length (v :: Vs) > 0 ->
  {{{ True }}}
    NewChanHandleV3 #()
  {{{(l: loc) γs γr γ1 γ2 γ3 γ4, RET #l; 
  is_ChanHandleV3_ReceiverProps l P Q v 0 γr ∗
  is_ChanHandleV3_SenderProps l P Q v 0 (length (v :: Vs)) γs  ∗
   is_ChanHandleV3 l (P :: Ps) (Q :: Qs) (v :: Vs) γs γr γ1 γ2 γ3 γ4 
   }}}.
Proof.
  iIntros "%Hvlen %Φ %HT HΦ".
  wp_rec.
 

  wp_apply (wp_new_free_lock). iIntros (mu_l) "Hlock".
  rewrite -wp_fupd.
 wp_apply wp_allocStruct.
 { val_ty. }
 iIntros (l). iIntros "Hchan".
  iNamedStruct "Hchan".
  iMod (struct_field_pointsto_persist with "mu") as "#mu".
  iMod (ghost_var_alloc (0)%nat) as (γs) "[Hsi1 Hsi2]".
  iMod (ghost_var_alloc (0)%nat) as (γr) "[Hri1 Hri2]".
  iMod (ghost_var_alloc (cons P Ps)) as (γ1) "[HPs1 HPS2]".
  iMod (ghost_var_alloc (cons Q Qs)) as (γ2) "[HQs1 HQs2]".
  iMod (ghost_var_alloc (cons v Vs)) as (γ3) "[HVs1 HVs2]".
  iMod (ghost_var_alloc ()) as (γ4) "Hcloseablealloc".
  iMod (alloc_lock (nroot .@ "ChanHandleV3") _ _
            (∃ (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (closed_b: bool) (value: w64)
     (index: nat), 
    "HPs" ∷ ghost_var γ1 (DfracOwn (1/2)) (P :: Ps) ∗
    "HQs" ∷ ghost_var γ2 (DfracOwn (1/2)) (Q :: Qs) ∗
    "HVs" ∷ ghost_var γ3 (DfracOwn (1/2)) (v :: Vs)  ∗
    "HCloseable"  ∷ 
    (if (start_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b closed_b index (length (v :: Vs)) )
    then 
    ghost_var γ4 (DfracDiscarded) () 
    else True)  ∗
      "HCloseable2"  ∷ 
    (ghost_var γ4 (DfracDiscarded) ()
     -∗  start_state sender_ready_b receiver_ready_b sender_done_b receiver_done_b
    )  ∗
       "HCloseable3"  ∷ 
     (if closeable_b then (start_state sender_ready_b receiver_ready_b sender_done_b receiver_done_b) else True)  ∗
    "HClosed" ∷ (if closed_b then (ghost_var γs (DfracOwn (1/2)) index) else True) ∗ 
    "Hsender_ready_b" ∷ l ↦[ChanHandleV3 :: "sender_ready"] #sender_ready_b ∗
    "Hreceiver_ready_b" ∷ l ↦[ChanHandleV3 :: "receiver_ready"] #receiver_ready_b ∗
    "Hsender_done_b" ∷ l ↦[ChanHandleV3 :: "sender_done"] #sender_done_b ∗
    "Hreceiver_done_b" ∷ l ↦[ChanHandleV3 :: "receiver_done"] #receiver_done_b ∗
    "Hclosed_b" ∷ l ↦[ChanHandleV3 :: "closed"] #closed_b ∗
    "Hvalue" ∷ l ↦[ChanHandleV3 :: "v"] #value 
      ∗  
    "HStates" ∷ valid_state sender_ready_b receiver_ready_b sender_done_b receiver_done_b ∗  
    "HStart" ∷ ((start_state sender_ready_b receiver_ready_b sender_done_b receiver_done_b ) -∗ 
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index)) ) ∗ 
    "HClosedFinal" ∷ (((not_final_state sender_ready_b receiver_ready_b sender_done_b receiver_done_b index (length (v :: Vs)))) -∗ 
     ⌜ closed_b = false ⌝) 
     ∗  
    "HSendFirst" ∷ (⌜ sender_ready_b = true ⌝ -∗ 
    (((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index)) ∗ (nth index (P :: Ps) emp) ∗ ⌜ value = (nth index (v :: Vs) (W64 0)) ⌝ ∗ ⌜ index < length (v :: Vs)  ⌝) )  ∗  
     "HRecFirst" ∷ (⌜ receiver_ready_b = true ⌝ -∗ 
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index (Q :: Qs) emp)  ∗ ⌜ index < length (v :: Vs)  ⌝) )  ∗  
     "HRecSecond" ∷ (⌜ receiver_done_b = true ⌝ -∗ 
    (((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) (index + 1)%nat ))  ∗ (nth index (Q :: Qs) emp)  ∗ ⌜ index < length (v :: Vs)  ⌝) )  ∗  
     "HSendSecond" ∷ (⌜ sender_done_b = true ⌝ -∗ 
    ((ghost_var γs (DfracOwn (1/2)) (index + 1)%nat ) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index (P :: Ps) emp) ∗ ⌜ value = (nth index (v :: Vs) (W64 0)) ⌝  ∗ ⌜ index < length (v :: Vs)  ⌝)   )
    
    ) with "Hlock [
   Hsi2 Hri2 HPs1 HQs1 HVs1 $closed 
    $receiver_ready $sender_ready $receiver_done $sender_done $v]"
        ) as "#Hlock".
       {
  iModIntro.  iExists 0%nat. iFrame.  iSplitL "".
  { unfold start_state_bool. simpl. unfold valid_state.  iPureIntro. lia.  }
  iSplitL "".
  { iPureIntro. lia. }
  iSplitL "".
  {   iIntros "%Ht". done. }
  iSplitL "".
  {  iIntros "%Hf". done. }
  iSplitL "".
  {  iIntros "%Hf". done. }
  iSplitL "".
  {  iIntros "%Hf". done. }
  iIntros "%Hf". done.
       } iModIntro. iApply "HΦ".
  iAssert (is_ChanHandleV3 l (P :: Ps) (Q :: Qs) (v :: Vs)
  γs γr γ1 γ2 γ3 γ4
  ) with "[]" as "#Hch".
  {  unfold is_ChanHandleV3.
  iExists mu_l.  iFrame "#".  
  }
  {
    iFrame "#".
    iSplitL "Hri1".
    { iSplitL "Hri1".
    { unfold is_ChanHandleV3_Receiver.
    done.  }
    iPureIntro.
    done.
      }
    { iSplitL "Hsi1".
    { unfold is_ChanHandleV3_Sender.
    done.  }
    iPureIntro.
    done.
      }

  }
  Qed. *)

Definition TrySend_Success (l: loc) 
(Q: iProp Σ) (v: w64) (i: nat) γs : iProp _ :=
is_ChanHandleV3_Sender l (i + 1) γs ∗ Q.

Definition TrySend_Failure (l: loc) 
(P: iProp Σ)  (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (cap: nat) γs : iProp _ :=
 is_ChanHandleV3_SenderProps l P Q R v i cap γs  ∗ P.

Definition TrySend_Xor (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (cap: nat) γs ret_val : iProp _ :=
 
match ret_val with
  | false => TrySend_Failure l P Q R v i cap γs 
  | true => TrySend_Success l Q v i γs  
end
.



    


(*Lemma wp_ChanHandleV3__TrySend (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (v: w64) (i: nat) γs :
i + 1 < 2 ^ 63 ->
  {{{ is_ChanHandleV3_SenderProps l P Q v i γs ∗ P }}}
   ChanHandleV3__TrySend #l #v
  {{{ (ret_val: bool), RET #ret_val; TrySend_Xor l P Q v i γs ret_val }}}.
Proof.
  iIntros "%Hilt %Φ [Hchanhandle HP] HΦ".
  unfold is_ChanHandleV3_SenderProps. iNamed "Hchanhandle". 
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
   iIntros (ret_b). iIntros "Hret_b".
  wp_pures.
   iNamed "Hchanhand".
   unfold is_ChanHandleV3_Sender.
    iNamed "Hchanhandsender".    
       wp_loadField.
      
   wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked inv]" . wp_pures. 
  iNamed "inv". wp_loadField.
  wp_if_destruct.
  {
    wp_storeField. wp_storeField.
    wp_storeField. wp_store. wp_pures.
    wp_loadField.
     iAssert ((ghost_var γs (1 / 2) index ∗ ghost_var γr (1 / 2) index) ∗ nth index Qs emp)%I
     with "[HRecFirst]" as "HRecFirst".
     {
      iApply "HRecFirst". done.
      

     }
     iDestruct "HRecFirst" as "[[Hsi Hri] HQ] ".
 iDestruct (ghost_var_agree with "Hsi Hsenderindex") as %->. 
  iAssert (bupd((ghost_var γs (1) (i + 1)%nat)%I)) with
       "[Hsi Hsenderindex]" as "Hgv".
       {
         iMod (ghost_var_update_2 (i + 1)%nat with "Hsi Hsenderindex") as "[Hsi Hgvi]".
         { apply Qp.half_half. }
         { iModIntro.  iFrame. }
       }

   iDestruct "Hgv" as ">Hgv".
   iDestruct "Hgv" as "[Hs1 Hs2]".
    replace (nth i Qs emp%I) with Q. 
  
     wp_apply (wp_Mutex__Unlock
     with "[HStart Hreceiver_ready_b 
     Hs1 Hri  HP
     Hvalue HStates HSendFirst HRecSecond HSendSecond
     Hsender_ready_b Hsender_done_b Hreceiver_done_b
       HQs HPs HVs $locked]").
       {
      
      
  iDestruct "HStates" as "%HStates".
         assert (sender_done_b = false). {
       set_solver.
    }
    assert(receiver_done_b = false).
     {
      set_solver.
    }
     assert(sender_ready_b = false).
     {
      set_solver.
    }
      subst.
        iFrame "#". iExists false. iExists false. iExists true. iExists false.
        iExists (nth i Vs (W64 0)).
        iModIntro.
        iExists i. 
        iFrame "HQs". 
        iFrame "HPs". 
        iFrame "HVs".
        iFrame "Hvalue".
        iFrame "Hsender_ready_b".
        iFrame "Hsender_done_b".
        iFrame "Hreceiver_done_b".
        iFrame "Hreceiver_ready_b".
        
        iSplitR "HP  Hs1 Hri".
        { unfold valid_state. iPureIntro. set_solver.  } 
        iSplitR "HP  Hs1 Hri".
        { unfold start_state. iIntros "%HF". set_solver.   }
        iSplitR "HP  Hs1 Hri".
        { iIntros "%HF". set_solver.

        }
        iSplitR "HP  Hs1 Hri".
        {
          iIntros "%HF". done.

        }
        {
          iSplitL "". { iIntros "%HF". done. }
          iIntros "%HT".
           iFrame. done.

        }
       }
       {
        wp_pures.
        wp_load. iModIntro.
        iApply "HΦ".
        unfold TrySend_Xor.
        unfold TrySend_Success.
        unfold is_ChanHandleV3_Sender. iFrame.


       }
  }
  {
    wp_pures. wp_loadField.
    
      wp_apply (wp_Mutex__Unlock
     with "[HStart Hreceiver_ready_b 
      
     Hvalue HStates HSendFirst HRecSecond HSendSecond
     Hsender_ready_b Hsender_done_b Hreceiver_done_b
       HQs HPs HVs $locked]").
       {
         subst.
        iFrame "#". iFrame.
        iModIntro. iIntros "%HF". done.


       }
       {
        wp_pures. wp_load.
        iModIntro. iApply "HΦ". 
        unfold TrySend_Xor.
        unfold is_ChanHandleV3_Sender.
        unfold TrySend_Failure.
        iFrame.
        unfold is_ChanHandleV3.
         iFrame "#".
         iSplitL "". { iPureIntro. done. }
         iSplitL "". { iPureIntro. done. }
         iPureIntro. done.


       }


  }
  
  Qed. *)

Qed. 

Definition TryReceive_Success (l: loc) 
(P: iProp Σ) (v: w64) (i: nat) γr : iProp _ :=
is_ChanHandleV3_Receiver l (i + 1) γr ∗ P.

Definition TryReceive_Failure (l: loc) 
(P: iProp Σ)  (Q: iProp Σ) (v: w64) (i: nat) γr : iProp _ :=
 is_ChanHandleV3_ReceiverProps l P Q v i γr ∗ Q.

Definition TryReceive_Xor (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (v: w64) (i: nat) γr ret_bool ret_val : iProp _ :=
 
match ret_bool with
  | false => TryReceive_Failure l P Q v i γr ∗ ⌜ret_val = (W64 0)⌝
  | true => TryReceive_Success l P v i γr ∗ ⌜ret_val = v⌝
end
. 

Lemma wp_ReusableChanHandle__TryReceive (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (v: w64) (i: nat) γr :
  {{{ is_ChanHandleV3_ReceiverProps l P Q v i γr ∗ Q }}}
    ChanHandleV3__TryReceive #l
  {{{ (ret_bool: bool) (ret_val: w64), RET (#ret_val, #ret_bool); TryReceive_Xor l P Q v i γr ret_bool ret_val }}}.
Proof.
    iIntros " %Φ [Hchanhandle HQ] HΦ".
  unfold is_ChanHandleV3_ReceiverProps.
   iNamed "Hchanhandle". 
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
   iIntros (ret_b). iIntros "Hret_b".
  wp_pures.
   iNamed "Hchanhand".
   unfold is_ChanHandleV3_Receiver.
    iNamed "Hchanhandreceiver". wp_pures.
    wp_apply wp_ref_to.
    { val_ty. }
    iIntros (ret_bool).
    iIntros "Hretbool".

       wp_loadField.
      
   wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked inv]" . wp_pures. 
  iNamed "inv". wp_loadField.
  wp_if_destruct.
  {
    wp_storeField. wp_storeField.
    wp_loadField.
    wp_store. wp_pures. wp_store.
    wp_pures.
    
     iAssert ((ghost_var γs (1 / 2) index ∗ ghost_var γr (1 / 2) index) ∗ nth index Ps emp ∗ ⌜value = nth index Vs (W64 0)⌝)%I
     with "[HSendFirst]" as "HSendFirst".
     {
      iApply "HSendFirst". done.
      

     }
     iDestruct "HSendFirst" as "[Hsi HP] ".
     iDestruct "HP" as "[HP %Hgvi]".
     iDestruct "Hsi" as "[Hsi Hri]".
 iDestruct (ghost_var_agree with "Hri Hreceiverindex") as %->. 
  iAssert (bupd((ghost_var γr (1) (i + 1)%nat)%I)) with
       "[Hri Hreceiverindex]" as "Hgv".
       {
         iMod (ghost_var_update_2 (i + 1)%nat with "Hri Hreceiverindex") as "[Hri Hgvi]".
         { apply Qp.half_half. }
         { iModIntro.  iFrame. }
       }

   iDestruct "Hgv" as ">Hgv".
   iDestruct "Hgv" as "[Hr1 Hr2]".
    replace (nth i Ps emp%I) with P.
    wp_loadField.
   
  
     wp_apply (wp_Mutex__Unlock
     with "[HStart Hreceiver_ready_b 
     Hr1 Hsi  HQ
     Hvalue HStates HRecFirst HRecSecond HSendSecond
     Hsender_ready_b Hsender_done_b Hreceiver_done_b
       HQs HPs HVs $locked]").
       {
      
      
  iDestruct "HStates" as "%HStates".
         assert (sender_done_b = false). {
       set_solver.
    }
    assert(receiver_done_b = false).
     {
      set_solver.
    }
     assert(receiver_ready_b = false).
     {
      set_solver.
    }
      subst.
        iFrame "#". iExists false. iExists false. iExists false. iExists true.
        iExists (nth i Vs (W64 0)).
        iModIntro.
        iExists i. 
        iFrame "HQs". 
        iFrame "HPs". 
        iFrame "HVs".
        iFrame "Hvalue".
        iFrame "Hsender_ready_b".
        iFrame "Hsender_done_b".
        iFrame "Hreceiver_done_b".
        iFrame "Hreceiver_ready_b".
        
        iSplitR "HQ  Hr1 Hsi".
        { unfold valid_state. iPureIntro. set_solver.  } 
        iSplitR "HQ  Hr1 Hsi".
        { unfold start_state. iIntros "%HF". set_solver.   }
        iSplitR "HQ  Hr1 Hsi".
        { iIntros "%HF". set_solver.

        }
        iSplitR "HQ  Hr1 Hsi".
        {
          iIntros "%HF". done.

        }
        {
          iSplitR "". { iFrame.  done. }
          iIntros "%HT".
           iFrame. done.

        }
       }
       {
        wp_pures.
        wp_load. wp_load. wp_pures. iModIntro.
        replace v with (nth i Vs (W64 0)). subst.
        iApply "HΦ".
        iFrame. done.
   


       }
  }
  {
    wp_pures. wp_loadField.
    
      wp_apply (wp_Mutex__Unlock
     with "[HStart Hreceiver_ready_b 
      
     Hvalue HStates HSendFirst HRecSecond HSendSecond HRecFirst
     Hsender_ready_b Hsender_done_b Hreceiver_done_b
       HQs HPs HVs $locked]").
       {
         subst.
        iFrame "#". iFrame.
   


       }
       {
        wp_pures. wp_load.
        wp_load. wp_pures.
        iModIntro.
        wp_pures. iApply "HΦ". 
        unfold TrySend_Xor.
        unfold is_ChanHandleV3_Sender.
        unfold TrySend_Failure.
        iFrame.
        unfold is_ChanHandleV3.
         iFrame "#".
         iSplitL "". { iPureIntro. done. }
         done.
      



       }


  }
  Qed.

End RBSHV2.
