From Perennial.Helpers Require Import List ModArith.

From Goose.github_com.goose_lang Require Import unbuffered_chan_code.

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

(* Either the receiver or sender is waiting somewhere, which is used to determine
if the channel can be closed. This at one point also specified 
receiver_ready_b = true but this proved not to be necessary and it makes proofs
slightly easier when this is minimalistic.  *)
Definition any_bool_true 
     (sender_ready_b: bool) (sender_done_b: bool) (receiver_done_b: bool): bool :=
     bool_decide
    ( (sender_ready_b = true) 
    ∨ 
    ((sender_done_b = true))
    ∨  
    ((receiver_done_b = true)))  
.

(* We have sent/received all expected values so we can close now. *)
Definition closeable_prop 
     (sender_done_b: bool) (receiver_done_b: bool) (index: nat) (num_uses: nat): Prop :=
    bool_decide (( ((sender_done_b = false))
     ∧ ((receiver_done_b = false))
     ∧ (index = num_uses)))
     .
Definition closeable_bool  
     (sender_done_b: bool) (receiver_done_b: bool) (index: nat) (num_uses: nat): bool :=
    bool_decide ((
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
Definition is_UnbufferedChannel (l: loc) 
(Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) (R: iProp Σ) (num_uses: nat)
 γs γr γ1 γ2 γ3 γ4 γ5: iProp _ :=
  ∃ (mu_l: loc) ,
  "#mu" ∷ l ↦[UnbufferedChannel :: "mu"]□ #mu_l ∗
  "#Hlock" ∷ is_lock (nroot .@ "UnbufferedChannel") (#mu_l)
     (∃ (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (closed_b: bool) (closeable_b: bool) (close_prop_ready_b: bool) (own_val: dfrac) (value: w64)
     (index: nat), 
    (* List of props that the sender must prove each time it sends. *)
    "HPs" ∷ ghost_var γ1 (DfracOwn (1/2)) Ps ∗
    (* List of props that the receiver must prove each time it sends. *)
    "HQs" ∷ ghost_var γ2 (DfracOwn (1/2)) Qs ∗
    (* List of values that the sender must send. *)
    "HVs" ∷ ghost_var γ3 (DfracOwn (1/2)) Vs  ∗
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
    (if (closeable_bool sender_done_b receiver_done_b index num_uses )
    then 
    ( "%HCloseableTrue" ∷ ⌜ closeable_b = true ∧ own_val = DfracDiscarded ⌝)
    else 
     ( "%HCloseableFalse" ∷  ⌜ closeable_b = false ∧  own_val = (DfracOwn 1) ⌝)) ∗ 
     (* Once we set closeable we don't try to set any of the bools or change 
     the index again so this can be an iff which makes it easier to get the 
     index and prove everything else is false for the close specs *)
    "HCloseableIff"  ∷ 
    (if closeable_b then 
    ( "%HAllFalseIndMax" ∷ ⌜ (closeable_bool sender_done_b receiver_done_b index num_uses ) ⌝)
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
    "Hsender_ready_b" ∷ l ↦[UnbufferedChannel :: "sender_ready"] #sender_ready_b ∗
    "Hreceiver_ready_b" ∷ l ↦[UnbufferedChannel :: "receiver_ready"] #receiver_ready_b ∗
    "Hsender_done_b" ∷ l ↦[UnbufferedChannel :: "sender_done"] #sender_done_b ∗
    "Hreceiver_done_b" ∷ l ↦[UnbufferedChannel :: "receiver_done"] #receiver_done_b ∗
    "Hclosed_b" ∷ l ↦[UnbufferedChannel :: "closed"] #closed_b ∗
    "Hvalue" ∷ l ↦[UnbufferedChannel :: "v"] #value ∗
    (* At most 1 of these bools can be true at a time.  *)
    "%HValidState" ∷ ⌜valid_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b closed_b ⌝ ∗  
    (* Make it easy to conclude that we haven't closed yet when the sender/receiver is trying to send/receive
    or we haven't yet sent/received all of our values.  *)
    "HClosedFinal" ∷ (
      if (not_final_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b index num_uses) then  
     ⌜ closed_b = false ⌝ else True) ∗  
     (* When a sender or receiver is waiting, we can't be at our max index yet *)
    "HInProgressIndexNotCapped" ∷ (
      if (any_bool_true sender_ready_b  sender_done_b receiver_done_b) then  
    ("%HIndexLessThanCap" ∷  ⌜ index < num_uses ⌝) else True) ∗  
    (* The send/receive permissions that are owned by the lock. 
    These also allow us to relate the sender/receiver index so that we can
    know that the other side is at most 1 off even when we aren't holding
    the lock. *)
    "HSendFirst" ∷ (if sender_ready_b  then if bool_decide (closeable_b = false) then 
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index Ps True) ∗ ⌜ value = (nth index Vs (W64 0)) ⌝)  else True else True)  ∗  
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
Definition is_UnbufferedChannel_Sender (l: loc) (i: nat) γs: iProp _ :=
  "HSenderIndex" ∷ ghost_var γs (DfracOwn (1/2)) i
.

Definition is_UnbufferedChannel_SenderProps (l: loc) (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs: iProp _ :=
  ∃ 
  (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) γ1 γ2 γ3 γ4 γ5 γr,
  "#HChanHandle" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
  "HChanHandleSenderPermission" ∷  is_UnbufferedChannel_Sender l i γs ∗
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
Definition is_UnbufferedChannel_CloserProps (l: loc) (i: nat) (R: iProp Σ) γs: iProp _ :=
  ∃ (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) (num_uses: nat) γ1 γ2 γ3 γ4 γ5 γr,
  "Hchanhand" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
  "Hchanhandsender" ∷  is_UnbufferedChannel_Sender l i γs ∗
  (* Might not be necessary but should make it easier to connect this 
  with the lock invariants *)
  "%HCap" ∷  ⌜ i = num_uses ⌝ ∗ 
  (* We gain this on exit of the last send which makes it easy to prove 
  that all of the other booleans are false when we try to close *)
  "#Hcloseable"  ∷ ghost_var γ4 DfracDiscarded true 
.

(* If we have sent everything, we can only close. *)
Definition is_UnbufferedChannel_SenderProps_Or_Closeable
 (l: loc) (i: nat) (num_uses: nat) (R: iProp Σ) γs: iProp _ :=
match bool_decide(i < num_uses) with
  | false => is_UnbufferedChannel_CloserProps l i R γs
  | true => is_UnbufferedChannel_Sender  l i γs
end
 .

Definition is_UnbufferedChannel_Receiver (l: loc) (i: nat) γr: iProp _ :=
  "Hreceiverindex" ∷ ghost_var γr (DfracOwn (1/2)) i
.

Definition is_UnbufferedChannel_ReceiverProps (l: loc) (P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses:nat) γr γ5: iProp _ :=
  ∃ 
  (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64)  γ1 γ2 γ3 γ4 γs,
  "#HChanHandle" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
   "HChanHandleReceiver" ∷  is_UnbufferedChannel_Receiver l i γr ∗
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
Definition is_UnbufferedChannel_ReceiverClosed (l: loc) (i: nat) (R: iProp Σ) γr γ5: iProp _ :=
  ∃ (Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) (num_uses: nat) γ1 γ2 γ3 γ4 γs,
  "#Hchanhand" ∷  is_UnbufferedChannel l Ps Qs Vs R num_uses γs γr γ1 γ2 γ3 γ4 γ5 ∗
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
Definition is_UnbufferedChannel_ReceiverConsumeCloseProp (l: loc) (i: nat) (R: iProp Σ) γr γ5: iProp _ :=
  "#HRecClosed" ∷ is_UnbufferedChannel_ReceiverClosed l i R γr γ5 ∗ 
  "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) true   
.

(* Once we have received all of the values we know the sender will not send
anymore but may close the channel. Note that we can regain 
is_UnbufferedChannel_Receiver from the persistent props so we only need to retain
the receiver permission to receive again. *)
Definition is_UnbufferedChannel_ReceiverProps_Or_Closed
 (l: loc) (i: nat) (num_uses: nat) (R: iProp Σ) γr γ5: iProp _ :=
match bool_decide(i < num_uses) with
  | false =>  is_UnbufferedChannel_ReceiverConsumeCloseProp l i R γr γ5
  | true => is_UnbufferedChannel_Receiver l i γr
end
 .

Definition TryReceive_Success (l: loc) 
(P: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γr γ5 : iProp _ :=
is_UnbufferedChannel_ReceiverProps_Or_Closed
    l (i + 1) num_uses R γr γ5 ∗ P.

Definition TryReceive_SenderNotReady (l: loc) 
(P: iProp Σ)  (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γr γ5 : iProp _ :=
 is_UnbufferedChannel_ReceiverProps l P Q R v i num_uses γr γ5 ∗ Q.

Definition TryReceive_Xor (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γr γ5 ret_bool ret_val : iProp _ :=
(* If there is no sender waiting, we just keep the same iProps, otherwise 
this is the same as Receive *) 
match ret_bool with
  | false => TryReceive_SenderNotReady l P Q R v i num_uses γr γ5 ∗ ⌜ret_val = (W64 0)⌝
  | true => TryReceive_Success l P R v i num_uses γr γ5 ∗ ⌜ret_val = v⌝
end
. 

(* Initializing a channel requires specifying 3 lists. 
Ps is the list of propositions that the sender must prove to send.
Qs is the list of propositions the receiver must prove to receive.
Vs is the list of values the sender sends and the receiver receives.
R is the proposition the sender must prove to close and the receiver
can gain on the first receive after close. *)
Lemma wp_UnbufferedChannel__New 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (num_uses: nat)
(Ps: list (iProp Σ)) (Qs: list (iProp Σ)) (Vs: list w64) 
  :
  num_uses > 0%nat ->
  {{{ True }}}
    NewUnbufferedChannel #()
  {{{(l: loc) γs γr γ1 γ2 γ3 γ4 γ5, RET #l; 
  is_UnbufferedChannel_ReceiverProps l P Q R v 0 num_uses γr γ5 ∗
  is_UnbufferedChannel_SenderProps l P Q R v 0 num_uses γs  ∗
   is_UnbufferedChannel l (P :: Ps) (Q :: Qs) (v :: Vs) R num_uses γs γr γ1 γ2 γ3 γ4 γ5
   }}}.
Proof.
  intros Hnu.
  wp_start.
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
  iMod (ghost_var_alloc (false)) as (γ4) "Hcloseablealloc".
  iMod (ghost_var_alloc (true)) as (γ5) "[HCp1 HCp2]".
  iMod (alloc_lock (nroot .@ "UnbufferedChannel") _ _
            (∃ (sender_ready_b: bool) (receiver_ready_b: bool)
     (sender_done_b: bool) (receiver_done_b: bool) (closed_b: bool) (closeable_b: bool) (close_prop_ready_b: bool) (own_val: dfrac) (value: w64)
     (index: nat), 
    "HPs" ∷ ghost_var γ1 (DfracOwn (1/2)) (P :: Ps) ∗
    "HQs" ∷ ghost_var γ2 (DfracOwn (1/2)) (Q :: Qs) ∗
    "HVs" ∷ ghost_var γ3 (DfracOwn (1/2)) (v :: Vs)  ∗
    "HCloseableGhostVar"  ∷ ghost_var γ4 own_val closeable_b  ∗
    "HReceiverClosedProp" ∷  ghost_var γ5 (DfracOwn (1/2)) close_prop_ready_b ∗  
    "%HMaxIndex" ∷ ⌜ index ≤ num_uses ⌝ ∗ 
    "HCloseable"  ∷ 
    (if (closeable_bool sender_done_b receiver_done_b index num_uses )
    then 
    ( "%HCloseableTrue" ∷ ⌜ closeable_b = true ∧ own_val = DfracDiscarded ⌝)
    else 
     ( "%HCloseableFalse" ∷  ⌜ closeable_b = false ∧  own_val = (DfracOwn 1) ⌝)) ∗ 
    "HCloseableIff"  ∷ 
    (if closeable_b then 
    ( "%HAllFalseIndMax" ∷ ⌜ (closeable_bool sender_done_b receiver_done_b index num_uses ) ⌝)
    else True) ∗ 
    "HClosedCloseable"  ∷ ⌜closed_closeable_relation closed_b closeable_b ⌝ ∗ 
    "HCloseableTakeReceiverIndex"  ∷ (if closeable_b then ((ghost_var γr (DfracOwn (1/2)) index) ∗ (ghost_var γs (DfracOwn (1/2)) index)) else True) ∗  
    "HClosePropConsumed" ∷ (if closed_b then if close_prop_ready_b then R else True else True ) ∗ 
    "HClosedTakeSenderPermission" ∷ (if closed_b then (ghost_var γs (DfracOwn (1/2)) index) else True) ∗ 
    "Hsender_ready_b" ∷ l ↦[UnbufferedChannel :: "sender_ready"] #sender_ready_b ∗
    "Hreceiver_ready_b" ∷ l ↦[UnbufferedChannel :: "receiver_ready"] #receiver_ready_b ∗
    "Hsender_done_b" ∷ l ↦[UnbufferedChannel :: "sender_done"] #sender_done_b ∗
    "Hreceiver_done_b" ∷ l ↦[UnbufferedChannel :: "receiver_done"] #receiver_done_b ∗
    "Hclosed_b" ∷ l ↦[UnbufferedChannel :: "closed"] #closed_b ∗
    "Hvalue" ∷ l ↦[UnbufferedChannel :: "v"] #value ∗
    "%HValidState" ∷ ⌜valid_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b closed_b ⌝ ∗  
    "HClosedFinal" ∷ (
      if (not_final_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b index num_uses) then  
     ⌜ closed_b = false ⌝ else True) ∗  
    "HInProgressIndexNotCapped" ∷ (
      if (any_bool_true sender_ready_b  sender_done_b receiver_done_b) then  
    ("%HIndexLessThanCap" ∷  ⌜ index < num_uses ⌝) else True) ∗  
    "HSendFirst" ∷ (if sender_ready_b  then if bool_decide (closeable_b = false) then 
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index (P :: Ps) True) ∗ ⌜ value = (nth index (v :: Vs) (W64 0)) ⌝)  else True else True)  ∗  
     "HRecFirst" ∷ (if receiver_ready_b then if bool_decide (closeable_b = false) then
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index (Q :: Qs) True)) else True else True) ∗  
     "HRecSecond" ∷ (if receiver_done_b then 
    (((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) (index + 1)%nat ))  ∗ (nth index (Q :: Qs) True)) else True)  ∗  
     "HSendSecond" ∷ (if sender_done_b then 
    ((ghost_var γs (DfracOwn (1/2)) (index + 1)%nat ) ∗ (ghost_var γr (DfracOwn (1/2)) index) ∗ (nth index (P :: Ps) True) ∗ ⌜ value = (nth index (v :: Vs) (W64 0)) ⌝) else True  ) ∗ 
    "HStart" ∷ (if (start_state_bool sender_ready_b receiver_ready_b sender_done_b receiver_done_b closeable_b )
    then
    ((ghost_var γs (DfracOwn (1/2)) index) ∗ (ghost_var γr (DfracOwn (1/2)) index)) else True )  
    
    ) with "Hlock [
   Hsi2 Hri2 HPs1 HQs1 HVs1 Hcloseablealloc HCp1 $closed 
    $receiver_ready $sender_ready $receiver_done $sender_done $v]"
        ) as "#Hlock".
       {
  iModIntro. iFrame. unfold closeable_bool. unfold closed_closeable_relation.
  unfold not_final_state_bool. iSimpl. rewrite bool_decide_false.
  { rewrite bool_decide_true.
  { iPureIntro. simpl. split.
  { lia. }
  { done. }
   }
   { lia.  }  
   }
   { lia. }
    }
    iModIntro. iApply "HΦ".
  iAssert (is_UnbufferedChannel l (P :: Ps) (Q :: Qs) (v :: Vs) R num_uses
  γs γr γ1 γ2 γ3 γ4 γ5
  ) with "[]" as "#Hch".
  {  unfold is_UnbufferedChannel.
  iExists mu_l.  iFrame "#".  
  }
  {
    iFrame "#". iFrame. iPureIntro. simpl. split.
    { split. { done. }
    { split. { done. }
    split. { done. }
    lia. } }
    split.
    { lia. }
    done.
  }
Qed.

(* By proving P and sending v, we can gain Q. i is the number of times we 
have sent so far which is used as an index into the lists of propositions
 and values that we declare when we initialize the channel.
 If i is num_uses-1, we will get permission to close the channel. 
*)
Lemma wp_UnbufferedChannel__Send (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs :
i + 1 < 2 ^ 63 ->
  {{{ is_UnbufferedChannel_SenderProps l P Q R v i num_uses γs ∗ P }}}
   UnbufferedChannel__Send #l #v
  {{{ RET #(); 
  is_UnbufferedChannel_SenderProps_Or_Closeable l (i + 1) num_uses R γs ∗ Q  }}}.
Proof.
  iIntros "%Hilt %Φ [Hchanhandle HP] HΦ".
  unfold is_UnbufferedChannel_SenderProps. iNamed "Hchanhandle". 
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_early). iIntros "HRetEarly". wp_pures.
  unfold is_UnbufferedChannel_Sender. 
  unfold is_UnbufferedChannel. 
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
        destruct (bool_decide((sender_done_b = false) ∧ (receiver_done_b = false))) eqn: H.
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
           wp_pures. destruct H as (Hsd & Hrd).
           subst. wp_pures.
           
           destruct sender_ready_b. {
         
            wp_loadField.
               wp_apply (wp_Mutex__Unlock
            with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
            HRecSecond HReceiverClosedProp 
            HSendFirst HCloseable HInProgressIndexNotCapped
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
            wp_loadField. wp_pures. wp_loadField. wp_pures.
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
            rewrite bool_decide_false.
            { iPureIntro. done. }
            { simpl. lia. }
          }
          {
            wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
          }
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
           iAssert (⌜closeable_b = false ∧ own_val = DfracOwn 1⌝)%I
           with "[HCloseable]" as "%Hcb".
           {
            unfold closeable_bool. 
            rewrite bool_decide_false.
            { done. }
            { lia. }
           }
           destruct Hcb as [Hcb Hov].
           subst closeable_b. iSimpl in "HSendFirst".
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
            ))%I
            with "[] [LoopInv_ClosedThings LoopInv_RecIndex LoopInv_RetEarlyFalse] [HΦ]").
            {
              clear Φ.
              iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
              wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
              iIntros "[locked inv]". wp_pures. iNamed "inv". 
              destruct (sender_done_b). {
                destruct closeable_b.
                {
                  iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]". 
                  iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                  iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
                  done.
                }
                {
                 wp_loadField. wp_pures. wp_loadField. 
                  wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp HClosedCloseable HClosePropConsumed
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
              {
                 iSimpl. unfold start_state_bool. iSimpl in "HStart".
                wp_loadField. wp_loadField.  
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
                  apply bool_decide_unpack in HAllFalseIndMax.
                  destruct HAllFalseIndMax as (Ht & Hrd & Hinu).
                  subst.
                   wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b Hri Hsi HClosePropConsumed 
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HClosedCloseable
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iFrame "#".
                      iSimpl. unfold closeable_bool. iSimpl. iPureIntro.
                      set_solver. 
                    }
                  wp_pures.
                  iModIntro. iApply "HΦ". iFrame "#". iFrame. 
                  iSimpl. rewrite bool_decide_true. 
                  { iFrame "#". done. }
                  { done.  }
                }
                {
                  unfold closeable_bool.
                  destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
                    {
                     apply bool_decide_eq_true in H.
                   wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HClosedCloseable
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iFrame "#". done. 
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                     iSplitL. 
                     { iPureIntro. done. }
                     rewrite bool_decide_false.
                     { done. }
                     { lia.  } 
                    }
                    }
                    {
                     apply bool_decide_eq_false in H.
                     assert ((i + 1)%nat = num_uses). {
                      lia.
                     }
                    destruct receiver_done_b.
                    {
                    iDestruct "HRecSecond" as "(Hsi & HQ2)".
                    iDestruct "Hsi" as "[Hsi Hri]".
                    iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                    unfold any_bool_true.
                    iSimpl in "HInProgressIndexNotCapped". iNamed.
                    iAssert (⌜(i + 1)%nat < num_uses⌝)%I with "[HInProgressIndexNotCapped]" as "%Hf".
                    { rewrite bool_decide_true.  
                     { done. }
                     { set_solver.  }
                    }
                    done.
                    }
                    {
                    destruct (bool_decide(index = num_uses)) eqn: H1.
                    {
                     apply bool_decide_eq_true in H1.
                     iAssert(⌜false = true ∧ own_val = DfracDiscarded⌝)%I with 
                     "[HCloseable]" as "%Ht".
                     { rewrite bool_decide_true.
                      { done. }
                      { done.  }
                     }
                     lia.
                    }
                    {
                      apply bool_decide_eq_false in H1.
                     iAssert(⌜false = false ∧ own_val = DfracOwn 1⌝)%I with 
                     "[HCloseable]" as "%Ht".
                     { rewrite bool_decide_false.
                      { done. }
                      { set_solver.  }
                     }
                     destruct Ht as (Ht1 & Ht2).
                     subst.
                      destruct sender_ready_b.
                      {
                       iSimpl in "HSendFirst".
                       iDestruct "HSendFirst" as "(Hsi & Hri2 & HQ2)". 
                       iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                      assert(receiver_ready_b = false).
                      { set_solver. }
                      subst.
                      wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart 
                    Hsi Hri2 HClosedCloseable HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HQ2
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. iFrame "#". unfold valid_state_bool.
                      iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                  }
                  {
                   destruct receiver_ready_b.
                   {
                     iSimpl in "HRecFirst".
                     iDestruct "HRecFirst" as "(Hsi & Hri2 & HQ2)". 
                     iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal Hsi Hri2 HQ2 HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart 
                    HClosedCloseable HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. done. 
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                   }
                   {
                    iSimpl in "HStart".
                    iDestruct "HStart" as "[Hsi Hri]".
                    unfold closed_closeable_relation.
                    iDestruct "HClosedCloseable" as "%HClosedCloseable".
                    assert(closed_b = false).
                    {
                      case closed_b eqn: H2.
                      {
                        simpl in HClosedCloseable. done.
                      }
                      {
                       done. 
                      }
                    } subst. 
                    iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                    
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal Hsi Hri HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                   }
                  }
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
               unfold is_UnbufferedChannel_SenderProps_Or_Closeable.
               destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
               {
                apply bool_decide_eq_true in H.
                unfold is_UnbufferedChannel_Receiver.
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
                iFrame. unfold is_UnbufferedChannel_CloserProps.
                unfold is_UnbufferedChannel_Sender.
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
                iApply "HΦ". iFrame. unfold is_UnbufferedChannel_SenderProps_Or_Closeable.
                case bool_decide eqn:H.
                {
                 apply bool_decide_eq_true in H.
                rewrite bool_decide_false.
                {  
                 unfold is_UnbufferedChannel_CloserProps.
                 unfold is_UnbufferedChannel_Sender.

                 iFrame. iFrame "#". subst send_index0. iFrame. done.
                }
                { lia.  }
                }
                {

                 apply bool_decide_eq_false in H. 
                 rewrite bool_decide_true.
                 {
                  unfold is_UnbufferedChannel_Sender.
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
  {{{ is_UnbufferedChannel_ReceiverProps l P Q R v i num_uses γr γ5 ∗ Q }}}
    UnbufferedChannel__Receive #l
  {{{ RET (#v, #false); is_UnbufferedChannel_ReceiverProps_Or_Closed
    l (i + 1) num_uses R γr γ5 ∗ P }}}.
Proof.
   iIntros "%Φ [Hchanhand HQ] HΦ".
  unfold is_UnbufferedChannel_ReceiverProps. iNamed "Hchanhand".
  iNamed "HChanHandle".
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_early). iIntros "HRetEarly". wp_pures.
  unfold is_UnbufferedChannel_Receiver. 
  unfold is_UnbufferedChannel. 
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
          unfold closeable_bool.
          iAssert (⌜false = false ∧ own_val = DfracOwn 1⌝)%I with "[HCloseable]" as "%Hcb".
          { rewrite bool_decide_false.
            { done. }
            { lia. } 
          }
          destruct Hcb as [Hf Hov].
          subst own_val.
          wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
          HSendSecond HInProgressIndexNotCapped Hr1 HQ Hsi
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iExists false. iExists false. iExists false. iExists true. 
            iExists false. iExists false. iExists close_prop_ready_b.
            iExists (DfracOwn 1). iExists (nth i Vs (W64 0)). iExists i. iFrame. 
              replace (nth i Qs True%I) with Q. iFrame. iSimpl. done.
            
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
            ))%I
            with "[] [LoopInv_ClosedPropReady LoopInv_RecIndex LoopInv_ReturnValue LoopInv_ClosedThings] [HΦ]").
            {
              clear Φ.
              iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
              wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
              iIntros "[locked inv]". wp_pures. iNamed "inv". 
              wp_loadField.
               destruct (receiver_done_b). {
                destruct closeable_b.
                {
                  iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]". 
                  iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                  iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
                  set_solver.
                }
                {
                 wp_loadField. wp_pures. 
                  wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp HClosedCloseable HClosePropConsumed
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
              {
                 iSimpl. unfold start_state_bool. iSimpl in "HStart".
                wp_loadField. 
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
                  apply bool_decide_unpack in HAllFalseIndMax.
                  destruct HAllFalseIndMax as (Ht & Hrd & Hinu).
                  subst.
                   wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b Hri Hsi HClosePropConsumed 
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HClosedCloseable
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iFrame "#".
                      iSimpl. unfold closeable_bool. iSimpl. 
                      rewrite bool_decide_false.
                      { rewrite bool_decide_true.
                        { done. }
                        { done. } 
                      } { unfold start_state_prop. lia. }
                    }
                    {
                  wp_pures.
                  iModIntro. iApply "HΦ". iFrame "#". iFrame. 
                  iSimpl. rewrite bool_decide_true. 
                  { iFrame "#". done. }
                  { done.  }
                }
                }
                {
                  unfold closeable_bool.
                  destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
                    {
                      apply bool_decide_eq_true in H.
                   wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HClosedCloseable
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iFrame "#". unfold valid_state_bool. 
                      set_solver. 
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                     iSplitL. 
                     { iPureIntro. done. }
                     rewrite bool_decide_false.
                     { done. }
                     { lia.  } 
                    }
                    }
                    {
                     apply bool_decide_eq_false in H.
                     assert ((i + 1)%nat = num_uses). {
                      lia.
                     }
                    destruct sender_done_b.
                    {
                    iDestruct "HSendSecond" as "(Hsi & HP2)".
                    iDestruct "HP2" as "[Hri HP2]".
                    iDestruct "HP2" as "[HP2 %Hval]".
                    iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                    unfold any_bool_true.
                    iSimpl in "HInProgressIndexNotCapped". iNamed.
                    iAssert (⌜(i + 1)%nat < num_uses⌝)%I with "[HInProgressIndexNotCapped]" as "%Hf".
                    { rewrite bool_decide_true.  
                     { done. }
                     { set_solver.  }
                    }
                    
                    done.
                    }
                    {
                    destruct (bool_decide(index = num_uses)) eqn: H1.
                    {
                     apply bool_decide_eq_true in H1.
                     iAssert(⌜false = true ∧ own_val = DfracDiscarded⌝)%I with 
                     "[HCloseable]" as "%Ht".
                     { rewrite bool_decide_true.
                      { done. }
                      { done.  }
                     }
                     lia.
                    }
                    {
                      apply bool_decide_eq_false in H1.
                     iAssert(⌜false = false ∧ own_val = DfracOwn 1⌝)%I with 
                     "[HCloseable]" as "%Ht".
                     { rewrite bool_decide_false.
                      { done. }
                      { set_solver.  }
                     }
                     destruct Ht as (Ht1 & Ht2).
                     subst.
                      destruct receiver_ready_b.
                      {
                       iSimpl in "HRecFirst".
                       iDestruct "HRecFirst" as "(Hsi & Hri2 & HQ2)". 
                       iDestruct (ghost_var_agree with "Hri2 LoopInv_RecIndex") as %->.
                      assert(sender_ready_b = false).
                      { set_solver. }
                      subst.
                      wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal HSendFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart 
                    Hsi Hri2 HClosedCloseable HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HQ2
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. iFrame "#". unfold valid_state_bool.
                      iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                  }
                  {
                   destruct sender_ready_b.
                   {
                     iSimpl in "HSendFirst".
                     iDestruct "HSendFirst" as "(Hsi & Hri2 & HQ2)". 
                     iDestruct (ghost_var_agree with "Hri2 LoopInv_RecIndex") as %->.
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal Hsi Hri2 HQ2 HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart 
                    HClosedCloseable HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. done. 
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                   }
                   {
                    iSimpl in "HStart".
                    iDestruct "HStart" as "[Hsi Hri]".
                    unfold closed_closeable_relation.
                    iDestruct "HClosedCloseable" as "%HClosedCloseable".
                    assert(closed_b = false).
                    {
                      case closed_b eqn: H2.
                      {
                        simpl in HClosedCloseable. done.
                      }
                      {
                       done. 
                      }
                    } subst. 
                    iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                    
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal Hsi Hri HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                   }
                  }
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
               unfold is_UnbufferedChannel_ReceiverProps_Or_Closed.
               destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
               {
                apply bool_decide_eq_true in H.
                unfold is_UnbufferedChannel_Receiver.
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
                unfold is_UnbufferedChannel_ReceiverConsumeCloseProp.
                iFrame. unfold is_UnbufferedChannel_ReceiverClosed.
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
                iApply "HΦ". iFrame. unfold is_UnbufferedChannel_ReceiverProps_Or_Closed.
                case bool_decide eqn:H.
                {
                 apply bool_decide_eq_true in H.
                rewrite bool_decide_false.
                {  
                 unfold is_UnbufferedChannel_Receiver.
                 subst rec_index0. iFrame. iFrame "#". done.
                }
                { lia.  }
                }
                {
                 apply bool_decide_eq_false in H. 
                 rewrite bool_decide_true.
                 {
                  unfold is_UnbufferedChannel_Receiver.
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
 {{{ is_UnbufferedChannel_ReceiverConsumeCloseProp l i R γr γ5 }}}
    UnbufferedChannel__Receive #l
  {{{ RET ( #(W64 0), #true); is_UnbufferedChannel_ReceiverClosed l i R γr γ5 ∗ R }}}.
Proof.
   iIntros "%Φ Hchanhand HΦ".
  unfold is_UnbufferedChannel_ReceiverConsumeCloseProp. iNamed "Hchanhand".
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_early). iIntros "HRetEarly". wp_pures.
  unfold is_UnbufferedChannel_ReceiverClosed. iNamed "HRecClosed".
  unfold is_UnbufferedChannel. iNamed "Hchanhand".
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
      destruct HAllFalseIndMax as (Hrd & Hsd & Hind). 
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
      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar HClosedCloseable
      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
       { 
         iFrame "#". iModIntro. iExists sender_ready_b. iExists false. iExists false. iExists false. 
         iExists true. iExists true. iExists false. iExists DfracDiscarded. iExists value. 
         iExists num_uses. iFrame "#". iFrame. unfold start_state_bool. iSimpl.
         rewrite bool_decide_true. 
         { iSimpl. 
          rewrite bool_decide_false.
          { iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
           iFrame. iSimpl. rewrite bool_decide_false.
           { iSimpl. unfold valid_state_bool. unfold valid_state_bool in HValidState.
           rewrite bool_decide_true. 
            { iSimpl. iFrame. set_solver. }
            { set_solver.  }
          }
          { unfold start_state_prop. lia. } }
          { unfold valid_state_bool in HValidState.
           apply bool_decide_unpack in HValidState.
           assert (sender_ready_b = false).
           { set_solver. }
           subst. simpl. lia. }  
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
      assert(sender_ready_b = false).
      { unfold valid_state_bool in HValidState. set_solver. }
      subst.
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
       wp_loadField.
       destruct LoopInv_Break as [Hcl Hcp].
         subst. 
        destruct sender_ready_b.
        {
          wp_pures. wp_storeField. wp_storeField. wp_loadField. wp_store. wp_loadField.
          unfold closeable_bool. unfold closed_closeable_relation. iDestruct "HClosedCloseable" as "%Hf".
          unfold any_bool_true.
          iSimpl in "HInProgressIndexNotCapped". iNamed.
          lia.
        }
        {
         wp_pures. wp_loadField. wp_loadField. wp_loadField. wp_loadField. wp_storeField. wp_loadField.

           wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HReceiverClosedProp HRecFirst HRecSecond HCloseable HClosedCloseable 
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          {
          iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
          iSimpl. iPureIntro. set_solver.
          }
          {
           wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
          } 
        }
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
        destruct HAllFalseIndMax as (Hsd & Hrd & Hind). 
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
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar HInProgressIndexNotCapped 
          HStart HCloseable
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iExists sender_ready_b. iExists false. iExists false. iExists false. 
            iExists true. iExists true. iExists false. iExists DfracDiscarded. iExists value. 
            iExists num_uses. iFrame "#". iFrame. unfold start_state_bool. iSimpl.
            rewrite bool_decide_true. 
            { iSimpl. assert (sender_ready_b = false).
            { unfold valid_state_bool in HValidState. set_solver. }
            subst. iSimpl. iFrame.
              rewrite bool_decide_false.
              { iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
              iFrame. iSimpl.
              done.
               }
              { simpl. lia. }  
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
          HInProgressIndexNotCapped
          HClosedFinal
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
            rewrite bool_decide_true. 
            { iSimpl. destruct sender_ready_b.
            { 
             iSimpl. done. 
            }
            {
             iSimpl. done. 
            } }
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


(* Receive after the closed prop has been gained. This spec is somewhat unlikely
to be useful since checking multiple times for closed is redundant but makes 
clear that receiving multiple times on a closed channel is benign. If you are 
using this, consider if you could instead use a select statement in Go which will 
use TryReceive in Goose.  *)
Lemma wp_ReusableChanHandle__ReceiveClosed 
 (l: loc) (R: iProp Σ) (i: nat) γr γ5:
 {{{  is_UnbufferedChannel_ReceiverClosed l i R γr γ5  }}}
    UnbufferedChannel__Receive #l
  {{{ RET ( #(W64 0), #true); True }}}.
Proof.
   iIntros "%Φ Hchanhand HΦ".
  unfold is_UnbufferedChannel_ReceiverClosed. iNamed "Hchanhand".
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_early). iIntros "HRetEarly". wp_pures.
  unfold is_UnbufferedChannel_ReceiverClosed.
  unfold is_UnbufferedChannel. iNamed "Hchanhand".
  wp_apply wp_ref_to.
    { val_ty. }
  iIntros (closed_local) "HClosedLocal".
  wp_pures.
  wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_value). iIntros "HReturnValue". wp_pures.
   wp_apply (wp_forBreak (λ continue,
   (
    "LoopInv_ClosedThings" ∷  ( ∃ (closed_local_b: bool) , 
    "LoopInv_ClosedLocal" ∷ (closed_local ↦[boolT] #closed_local_b) ∗
    "LoopInv_RetEarlyFalse" ∷ (return_early ↦[boolT] #false)
    )
     ∗
    "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #(W64 0))       
    ))%I
    with "[] [HReturnValue HClosedLocal HRetEarly] [HΦ]").
    { clear Φ.
      iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
      wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
      iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
      iDestruct (ghost_var_agree with "HCloseableGhostVar Hcloseable") as %->.
      iNamed. unfold closeable_bool in HAllFalseIndMax. apply bool_decide_unpack in HAllFalseIndMax.
      destruct HAllFalseIndMax as (Hrd & Hsd & Hind). 
      subst. unfold not_final_state_bool. 
      destruct closed_b. {
      assert (receiver_ready_b = false).
      { unfold valid_state_bool in HValidState. set_solver.  }
      subst receiver_ready_b.
      wp_loadField. 
       unfold closeable_bool. 
      iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hov".
      { rewrite bool_decide_true. 
        { iNamed "HCloseable". iPureIntro. set_solver. }
        { done.  }
      }
      subst own_val.
    
      wp_apply (wp_Mutex__Unlock
      with "[Hvalue Hclosed_b Hreceiver_done_b HReceiverClosedProp HCloseableTakeReceiverIndex
      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar HClosedCloseable
      HClosePropConsumed HInProgressIndexNotCapped HCloseable
      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
       { 
         iFrame "#". iModIntro. iExists sender_ready_b. iExists false. iExists false. iExists false. 
         iExists true. iExists true. iExists close_prop_ready_b. iExists DfracDiscarded. iExists value. 
         iExists num_uses. iFrame "#". iFrame. unfold start_state_bool. iSimpl.
         rewrite bool_decide_true. 
         { iSimpl. 
          rewrite bool_decide_false.
          { iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
           iFrame. iSimpl. rewrite bool_decide_false.
           { iSimpl. unfold valid_state_bool. unfold valid_state_bool in HValidState.
           rewrite bool_decide_true. 
            { iSimpl. iFrame. set_solver. }
            { set_solver.  }
          }
          { unfold start_state_prop. lia. } }
          { unfold valid_state_bool in HValidState.
           apply bool_decide_unpack in HValidState.
           assert (sender_ready_b = false).
           { set_solver. }
           subst. simpl. lia. }  
         } 
         { done. }
       }
       {
        wp_pures. wp_store. iModIntro. iApply "HΦ". iFrame. 

       }
      }
      {
      destruct receiver_ready_b. {
      assert(sender_ready_b = false).
      { unfold valid_state_bool in HValidState. set_solver. }
      subst.
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
       { wp_pures. iModIntro. iApply "HΦ". iFrame.
       }
      }
      {
       wp_loadField.
    
        destruct sender_ready_b.
        {
          wp_pures. wp_storeField. wp_storeField. wp_loadField. wp_store. wp_loadField.
          unfold closeable_bool. unfold closed_closeable_relation. iDestruct "HClosedCloseable" as "%Hf".
          unfold any_bool_true.
          iSimpl in "HInProgressIndexNotCapped". iNamed.
          lia.
        }
        {
         wp_pures. wp_loadField. wp_loadField. wp_loadField. wp_loadField. wp_storeField. wp_loadField.

           wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HReceiverClosedProp HRecFirst HRecSecond HCloseable HClosedCloseable 
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          {
          iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
          iSimpl. iPureIntro. set_solver.
          }
          {
           wp_pures. iModIntro. iApply "HΦ". iFrame.  
          } 
        }
      }
    }
    }
  { iFrame. 
  }
  {
    iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
    destruct closed_local_b.
    {
      wp_pures. wp_load. wp_pures. iModIntro. iApply "HΦ". iFrame "#". iFrame.
      done.
    }
    {
      wp_pures. wp_load. wp_pures. wp_load. wp_pures.
      wp_apply (wp_forBreak (λ continue,
      (
      "LoopInv_ClosedThings" ∷  ( ∃ (closed_local_b: bool) , 
      "LoopInv_ClosedLocal" ∷ (closed_local ↦[boolT] #closed_local_b) ∗
      "%LoopInv_Break" ∷  (if continue
      then ⌜closed_local_b = false ⌝ 
      else (  (⌜closed_local_b = true ⌝ )%I )%I) 
      ) ∗
      "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #(W64 0))       
      ))%I
      with "[] [LoopInv_ClosedLocal LoopInv_RetEarlyFalse LoopInv_ReturnValue] [HΦ]").
      {
        clear Φ.
        iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
        wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
        iIntros "[locked inv]". wp_pures. iNamed "inv". wp_loadField.
        iDestruct (ghost_var_agree with "HCloseableGhostVar Hcloseable") as %->.
        iNamed. unfold closeable_bool in HAllFalseIndMax. apply bool_decide_unpack in HAllFalseIndMax.
        destruct HAllFalseIndMax as (Hsd & Hrd & Hind). 
        subst. unfold not_final_state_bool. 
        destruct closed_b. {
          wp_pures. wp_loadField.
          assert (receiver_ready_b = false).
          { unfold valid_state_bool in HValidState. set_solver.  }
          subst receiver_ready_b.
          unfold closeable_bool. 
          iAssert (⌜own_val = DfracDiscarded⌝)%I with "[HCloseable]" as "%Hov".
          { rewrite bool_decide_true. 
            { iNamed "HCloseable". iPureIntro. set_solver. }
            { done.  }
          }
          subst own_val.
          wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b  HCloseableTakeReceiverIndex
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar HInProgressIndexNotCapped 
          HStart HCloseable HReceiverClosedProp HClosePropConsumed
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iExists sender_ready_b. iExists false. iExists false. iExists false. 
            iExists true. iExists true. iExists close_prop_ready_b. iExists DfracDiscarded. iExists value. 
            iExists num_uses. iFrame "#". iFrame. unfold start_state_bool. iSimpl.
            rewrite bool_decide_true. 
            { iSimpl. assert (sender_ready_b = false).
            { unfold valid_state_bool in HValidState. set_solver. }
            subst. iSimpl. iFrame.
              rewrite bool_decide_false.
              { iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
              iFrame. iSimpl.
              done.
               }
              { simpl. lia. }  
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
          HInProgressIndexNotCapped
          HClosedFinal
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
            rewrite bool_decide_true. 
            { iSimpl. destruct sender_ready_b.
            { 
             iSimpl. done. 
            }
            {
             iSimpl. done. 
            } }
            { done. }  
          }
          { 
            wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
          } 
        }
      }
      { 
       iFrame. done.
      }
      { iModIntro. iIntros "IH". iNamed "IH". iDestruct "LoopInv_ClosedThings" as 
      "[%Ht HR]". wp_pures. wp_load. iNamed "HR". wp_load. wp_pures.
      iModIntro.
      assert(Ht = true). 
      { set_solver. }
      subst Ht.
      iApply "HΦ". iFrame "#". iFrame. done. 
      }
    }
  }       
Qed. 

(* We can close once and must own the closer iProp R to do so. This should be 
true if closing is not meant to synchronize. *)
Lemma wp_UnbufferedChannel__Close (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) γs :
i + 1 < 2 ^ 63 ->
  {{{ is_UnbufferedChannel_CloserProps l i R γs ∗ R}}}
   UnbufferedChannel__Close #l
  {{{RET #(); True }}}.
  Proof.
  iIntros "%Hilt %Φ [HcloserProps HR] HΦ".
  iNamed "HcloserProps". unfold is_UnbufferedChannel_Sender. 
  unfold is_UnbufferedChannel. iNamed "Hchanhand".
  iNamed "Hchanhandsender".
  wp_rec.
  wp_loadField.
   wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked inv]" . wp_pures. 
  iNamed "inv". 
 iDestruct (ghost_var_agree with "HCloseableGhostVar Hcloseable") as %->.
  unfold closeable_bool. iNamed "HCloseableIff".
  apply bool_decide_unpack in HAllFalseIndMax.
  destruct HAllFalseIndMax as (Hsd & Hrd & Hind).
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
  wp_storeField.
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

Lemma wp_ReusableChanHandle__TryReceive (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γr γ5 :
  {{{ is_UnbufferedChannel_ReceiverProps l P Q R v i num_uses γr γ5 ∗ Q }}}
    UnbufferedChannel__TryReceive #l
  {{{ (ret_bool: bool) (ret_val: w64),  
    RET (#ret_val, #ret_bool); 
    TryReceive_Xor l P Q R v i num_uses γr γ5 ret_bool ret_val 
     }}}.
Proof.
   iIntros "%Φ [Hchanhand HQ] HΦ".
  unfold is_UnbufferedChannel_ReceiverProps. iNamed "Hchanhand".
  iNamed "HChanHandle".
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_value). iIntros "HRetValue". wp_pures.
  unfold is_UnbufferedChannel_Receiver. 
  unfold is_UnbufferedChannel. 
  wp_apply wp_ref_to.
    { val_ty. }
  iIntros (return_bool) "HReturnBool".
  wp_pures. wp_loadField.
  wp_apply (wp_Mutex__Lock with "Hlock"). 
      iIntros "[locked inv]". wp_pures.
      iDestruct "HReceiverClosedProp" as "HRClosedRecProp".
       iNamed "inv".
      destruct closeable_b.
      { 
        iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
        apply bool_decide_unpack in HAllFalseIndMax. 
        
          iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
        iDestruct (ghost_var_agree with "Hri HChanHandleReceiver") as %->.
        lia. 
      }
        {
       iDestruct "HClosedCloseable" as "%HCloseCloseable".
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
          wp_pures. wp_loadField.
          wp_pures. wp_loadField. wp_pures.
           wp_storeField. wp_storeField. wp_loadField. wp_store.
          wp_store. wp_loadField.
           unfold valid_state_bool in HValidState.
          assert (receiver_ready_b = false).
          {  set_solver. }
          assert (sender_done_b = false).
          { set_solver. }
          subst receiver_ready_b. subst sender_done_b. 
          assert (receiver_done_b = false).
          { set_solver. }
          subst receiver_done_b.
          iDestruct "HSendFirst" as "(Hsi & Hri & HP & %Hvs)".
  
          iDestruct (ghost_var_agree with "HChanHandleReceiver Hri") as %<-.
          iAssert (bupd((ghost_var γr (DfracOwn 1) (i + 1)%nat)%I)) with
              "[HChanHandleReceiver Hri]" as "Hri".
              {
                iMod (ghost_var_update_2 (i + 1)%nat with "HChanHandleReceiver Hri") as "[H1 H2]".
                { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
                { iModIntro.  iFrame. }
              }
          iDestruct "Hri" as ">Hri".
          iDestruct "Hri" as "[Hr1 Hr2]". 
          subst value.
          unfold closeable_bool.
          iAssert (⌜false = false ∧ own_val = DfracOwn 1⌝)%I with "[HCloseable]" as "%Hcb".
          { rewrite bool_decide_false.
            { done. }
            { lia. } 
          }
          destruct Hcb as [Hf Hov].
          subst own_val.
          wp_apply (wp_Mutex__Unlock
          with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
          HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
          HSendSecond HInProgressIndexNotCapped Hr1 HQ Hsi
          Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
          HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iExists false. iExists false. iExists false. iExists true. 
            iExists false. iExists false. iExists close_prop_ready_b.
            iExists (DfracOwn 1). iExists (nth i Vs (W64 0)). iExists i. iFrame. 
            replace (nth i Qs True%I) with Q. iFrame. iSimpl. done.
          }
          {
           wp_pures. wp_load. wp_pures.
           wp_apply (wp_forBreak (λ continue,
          (
            "LoopInv_ClosedThings" ∷  ( ∃  (rec_index: nat), 
            "LoopInv_ClosedPropReady" ∷  (ghost_var γ5 (DfracOwn (1/2)) true) ∗
            "LoopInv_RecIndex" ∷  (ghost_var γr (DfracOwn (1/2)) rec_index) ∗
            "LoopInv_ReturnValue" ∷  (return_value ↦[uint64T] #(nth i Vs (W64 0)))  ∗
            "LoopInv_ReturnBool" ∷  (return_bool ↦[boolT] #true)  ∗
            "LoopInv_PreExisting"  ∷  ((("HP" ∷  P) ∗ ("%Hriplus" ∷ ⌜rec_index = (i + 1)%nat⌝) )%I) ∗     
            "%LoopInv_Break" ∷  (if continue
            then (True)
            else ( if (bool_decide((i + 1)%nat = num_uses)) then ( ghost_var γ4 DfracDiscarded true )%I else True )%I) 
            ) 
            ))%I
            with "[] [HRetValue HReturnBool HP HStart Hr2 HRClosedRecProp] [HΦ]").
            {
              clear Φ.
              iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
              wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
              iIntros "[locked inv]". wp_pures. iNamed "inv". 
              wp_loadField.
               destruct (receiver_done_b). {
                destruct closeable_b.
                {
                  iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]". 
                  iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                  iNamed "HCloseableIff". unfold closeable_bool in HAllFalseIndMax.
                  set_solver.
                }
                {
                 wp_loadField. wp_pures. 
                  wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp HClosedCloseable HClosePropConsumed
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
              {
                 iSimpl. unfold start_state_bool. iSimpl in "HStart".
                wp_loadField. 
                iNamed "LoopInv_PreExisting". subst rec_index.
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
                  apply bool_decide_unpack in HAllFalseIndMax.
                  destruct HAllFalseIndMax as (Ht & Hrd & Hinu).
                  subst.
                   wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b Hri Hsi HClosePropConsumed 
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HClosedCloseable
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iFrame "#".
                      iSimpl. unfold closeable_bool. iSimpl. 
                      rewrite bool_decide_false.
                      { rewrite bool_decide_true.
                        { done. }
                        { done. } 
                      } { unfold start_state_prop. lia. }
                    }
                    {
                  wp_pures.
                  iModIntro. iApply "HΦ". iFrame "#". iFrame. 
                  iSimpl. rewrite bool_decide_true. 
                  { iFrame "#". done. }
                  { done.  }
                }
                }
                {
                  unfold closeable_bool.
                  destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
                    {
                    apply bool_decide_eq_true in H.
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart HSendFirst HClosedCloseable
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iFrame "#". unfold valid_state_bool. 
                      set_solver. 
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                     iSplitL. 
                     { iPureIntro. done. }
                     rewrite bool_decide_false.
                     { done. }
                     { lia.  } 
                    }
                    }
                    {
                     apply bool_decide_eq_false in H.
                     assert ((i + 1)%nat = num_uses). {
                      lia.
                     }
                    destruct sender_done_b.
                    {
                    iDestruct "HSendSecond" as "(Hsi & HP2)".
                    iDestruct "HP2" as "[Hri HP2]".
                    iDestruct "HP2" as "[HP2 %Hval]".
                    iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                    unfold any_bool_true.
                    iSimpl in "HInProgressIndexNotCapped". iNamed.
                    iAssert (⌜(i + 1)%nat < num_uses⌝)%I with "[HInProgressIndexNotCapped]" as "%Hf2".
                    { rewrite bool_decide_true.  
                     { done. }
                     { set_solver.  }
                    }
                    
                    done.
                    }
                    {
                    destruct (bool_decide(index = num_uses)) eqn: H1.
                    {
                     apply bool_decide_eq_true in H1.
                     iAssert(⌜false = true ∧ own_val = DfracDiscarded⌝)%I with 
                     "[HCloseable]" as "%Ht".
                     { rewrite bool_decide_true.
                      { done. }
                      { done.  }
                     }
                     lia.
                    }
                    {
                      apply bool_decide_eq_false in H1.
                     iAssert(⌜false = false ∧ own_val = DfracOwn 1⌝)%I with 
                     "[HCloseable]" as "%Ht".
                     { rewrite bool_decide_false.
                      { done. }
                      { set_solver.  }
                     }
                     destruct Ht as (Ht1 & Ht2).
                     subst.
                      destruct receiver_ready_b.
                      {
                       iSimpl in "HRecFirst".
                       iDestruct "HRecFirst" as "(Hsi & Hri2 & HQ2)". 
                       iDestruct (ghost_var_agree with "Hri2 LoopInv_RecIndex") as %->.
                      assert(sender_ready_b = false).
                      { set_solver. }
                      subst.
                      wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal HSendFirst HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart 
                    Hsi Hri2 HClosedCloseable HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HQ2
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. iFrame "#". unfold valid_state_bool.
                      iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                  }
                  {
                   destruct sender_ready_b.
                   {
                     iSimpl in "HSendFirst".
                     iDestruct "HSendFirst" as "(Hsi & Hri2 & HQ2)". 
                     iDestruct (ghost_var_agree with "Hri2 LoopInv_RecIndex") as %->.
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal Hsi Hri2 HQ2 HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HStart 
                    HClosedCloseable HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. done. 
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                   }
                   {
                    iSimpl in "HStart".
                    iDestruct "HStart" as "[Hsi Hri]".
                    unfold closed_closeable_relation.
                    iDestruct "HClosedCloseable" as "%HClosedCloseable".
                    assert(closed_b = false).
                    {
                      case closed_b eqn: H2.
                      {
                        simpl in HClosedCloseable. done.
                      }
                      {
                       done. 
                      }
                    } subst. 
                    iDestruct (ghost_var_agree with "Hri LoopInv_RecIndex") as %->.
                    
                    wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal Hsi Hri HRecSecond HReceiverClosedProp
                    HSendSecond HInProgressIndexNotCapped HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. done. 
                    }
                   }
                  }
                        }
                      }
                    }
                  }

                }          
              }
              {
               replace (nth i Ps True%I) with P. iFrame. done. 
              }
              {
               iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
               wp_pures. wp_load. wp_pures. subst v. wp_load. wp_pures. iApply "HΦ".
               iModIntro. unfold TryReceive_Xor. unfold TryReceive_Success.
               unfold is_UnbufferedChannel_ReceiverProps_Or_Closed.
               destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
               {
                apply bool_decide_eq_true in H.
                unfold is_UnbufferedChannel_Receiver.
                iNamed "LoopInv_PreExisting".
                subst rec_index.
                iFrame. done.
               }
               {
                apply bool_decide_eq_false in H.
                assert ((i + 1)%nat = num_uses).
                {
                  lia.
                }
                unfold is_UnbufferedChannel_ReceiverConsumeCloseProp.
                iFrame. unfold is_UnbufferedChannel_ReceiverClosed.
                iFrame "#". iFrame. subst num_uses. rewrite bool_decide_true.
                { iFrame. iNamed "LoopInv_PreExisting". iFrame. done.  }
                 done.

               }
              }
          }
        }
          {
            wp_pures. wp_loadField. wp_pures. wp_loadField. wp_pures. wp_loadField.
              wp_apply (wp_Mutex__Unlock
                    with "[Hvalue Hclosed_b Hreceiver_done_b  HClosePropConsumed 
                    HCloseable HClosedFinal HRecSecond HReceiverClosedProp
                    HRecFirst HStart
                    HSendSecond HInProgressIndexNotCapped HCloseableGhostVar
                    Hsender_done_b Hreceiver_ready_b Hsender_ready_b 
                    HClosedTakeSenderPermission  HQs HPs HVs $locked]").
                    { 
                      iFrame "#". iModIntro. iFrame. iSimpl. iFrame. done.
                    }
                    {
                     wp_pures. wp_load. wp_pures. wp_load. wp_load.
                     wp_pures. iModIntro.
                      iApply "HΦ". iFrame. iFrame "#". done. 
                    }
          }
        }
Qed.

(* We cannot use TryReceive to gain the closed proposition R since it will 
not block even if the channel isn't closed. This spec can be used after all 
receive propositions/values have been gained, i.e. in a range for loop where we 
receive until the sender closes, at which point the spec here tells us we 
return false. *)
Lemma wp_ReusableChanHandle__TryReceiveClosed 
 (l: loc) (R: iProp Σ) (i: nat) γr γ5:
 {{{ is_UnbufferedChannel_ReceiverClosed l i R γr γ5 }}}
    UnbufferedChannel__TryReceive #l
  {{{ RET ( #(W64 0), #false); True }}}.
Proof.
   iIntros "%Φ Hchanhand HΦ".
  unfold is_UnbufferedChannel_ReceiverProps. iNamed "Hchanhand".
  unfold is_UnbufferedChannel. iNamed "Hchanhand".
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
  iIntros (return_value). iIntros "HRetValue". wp_pures.
  unfold is_UnbufferedChannel_Receiver. 
  unfold is_UnbufferedChannel. 
  wp_apply wp_ref_to.
    { val_ty. }
  iIntros (return_bool) "HReturnBool".
  wp_pures. wp_loadField.
  wp_apply (wp_Mutex__Lock with "Hlock"). 
      iIntros "[locked inv]". wp_pures.
       iNamed "inv".
      iDestruct (ghost_var_agree with "HCloseableGhostVar Hcloseable") as %->.
      iNamed. unfold closeable_bool in HAllFalseIndMax. apply bool_decide_unpack in HAllFalseIndMax.
      destruct HAllFalseIndMax as (Hrd & Hsd & Hind). 
      subst. unfold not_final_state_bool. 
      destruct closed_b. {
      assert (receiver_ready_b = false).
      { unfold valid_state_bool in HValidState. set_solver.  }
      subst receiver_ready_b.
      wp_loadField.
      wp_pures. wp_store. wp_loadField.
      wp_apply (wp_Mutex__Unlock
      with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
      HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
      HSendSecond HInProgressIndexNotCapped 
      HClosedCloseable HClosePropConsumed 
      HSendFirst HStart
      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl. iFrame. iPureIntro.
            unfold valid_state_bool in HValidState. unfold closeable_bool.
            rewrite bool_decide_true.
            { done. }
            { done. }
          }
          {
           wp_pures. wp_load. wp_pures. wp_load. wp_load. wp_pures. iModIntro.
           iApply "HΦ". done. 
          }
      }
      {
        wp_loadField. wp_pures. wp_loadField. wp_pures.
        destruct sender_ready_b.
        {
          unfold any_bool_true. 
          iAssert (⌜num_uses < num_uses⌝)%I with "HInProgressIndexNotCapped" as "%Hf".
          lia.
        }
        {
         unfold closeable_bool. wp_pures. wp_loadField.
         wp_apply (wp_Mutex__Unlock
      with "[Hvalue Hclosed_b Hreceiver_done_b HCloseableTakeReceiverIndex
      HCloseable HClosedFinal HRecFirst HRecSecond HReceiverClosedProp
      HSendSecond HInProgressIndexNotCapped 
      HClosedCloseable HClosePropConsumed 
      HSendFirst HStart
      Hsender_done_b Hreceiver_ready_b Hsender_ready_b HCloseableGhostVar
      HClosedTakeSenderPermission  HQs HPs HVs $locked]").
          { 
            iFrame "#". iModIntro. iFrame. iSimpl.  iPureIntro.
            unfold valid_state_bool in HValidState. unfold closeable_bool.
            rewrite bool_decide_true.
            { done. }
            { done. }
          }
          {
           wp_pures. wp_load. wp_pures. wp_load. wp_load. wp_pures. iModIntro.
           iApply "HΦ". done. 
          }
        }
      }
Qed.

Definition TrySend_Success (l: loc) 
(Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs : iProp _ :=
is_UnbufferedChannel_SenderProps_Or_Closeable l (i + 1) num_uses R γs ∗ Q.

Definition TrySend_Failure (l: loc) 
(P: iProp Σ)  (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs : iProp _ :=
  is_UnbufferedChannel_SenderProps l P Q R v i num_uses γs ∗ P.

Definition TrySend_Xor (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs ret_val : iProp _ :=
(* If a receiver isn't ready, we simply keep all of our iProps. If one is, 
we have the same postcondition as send *) 
match ret_val with
  | false => TrySend_Failure l P Q R v i num_uses γs 
  | true => TrySend_Success l Q R v i num_uses γs  
end
.

Lemma wp_UnbufferedChannel__TrySend (l: loc) 
(P: iProp Σ) (Q: iProp Σ) (R: iProp Σ) (v: w64) (i: nat) (num_uses: nat) γs :
i + 1 < 2 ^ 63 ->
  {{{ is_UnbufferedChannel_SenderProps l P Q R v i num_uses γs ∗ P }}}
   UnbufferedChannel__TrySend #l #v
  {{{ (ret_val: bool), RET #ret_val;
  TrySend_Xor l P Q R v i num_uses γs ret_val }}}.
Proof.
  iIntros "%Hilt %Φ [Hchanhandle HP] HΦ".
  unfold is_UnbufferedChannel_SenderProps. iNamed "Hchanhandle". 
  wp_rec; wp_pures. wp_apply wp_ref_to.
  { val_ty. }
   iIntros (ret_b). iIntros "Hret_b".
  wp_pures.
  iNamed "HChanHandle".
  unfold is_UnbufferedChannel_Sender.
  iNamed "HChanHandleSenderPermission".    
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "Hlock").
  iIntros "[locked inv]" . wp_pures. 
  iNamed "inv". wp_loadField.
  destruct closed_b.
  {
   unfold not_final_state_bool.
   iDestruct (ghost_var_agree with "HClosedTakeSenderPermission HSenderIndex") as %->.
   iAssert (⌜true = false⌝)%I with "[HClosedFinal]" as "%Hf".
   { rewrite bool_decide_true.
   {
    done.
   }
  { set_solver.  }  
   }
   done.
  }
  { wp_pures. wp_loadField.
   destruct receiver_ready_b.
   {
    wp_storeField. wp_storeField.
    wp_storeField. wp_store. wp_pures.
    wp_loadField.
    destruct closeable_b.
    { unfold closeable_bool. iNamed. apply bool_decide_unpack in HAllFalseIndMax.
    destruct HAllFalseIndMax as (Hsd & Hrd & Hid). subst.
    assert(sender_ready_b = false).
    { unfold valid_state_bool in HValidState. set_solver. }
      subst. iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
      iDestruct (ghost_var_agree with "Hsi HSenderIndex") as %->.
      lia.
    }
    {
      unfold valid_state_bool in HValidState.
      assert(sender_ready_b = false).
      { set_solver. } 
      assert(receiver_done_b = false).
      { set_solver. } 
      assert (sender_done_b = false).
      { set_solver. }
      subst sender_ready_b. subst receiver_done_b. subst sender_done_b.
      iSimpl in "HRecFirst".
      iDestruct "HRecFirst" as "(Hsi & Hri & HQ)".
      iDestruct (ghost_var_agree with "Hsi HSenderIndex") as %->.
      iAssert (bupd((ghost_var γs (DfracOwn 1) (i + 1)%nat)%I)) with
       "[Hsi HSenderIndex]" as "Hgv".
       {
         iMod (ghost_var_update_2 (i + 1)%nat with "Hsi HSenderIndex") as "[Hsi Hgvi]".
         { rewrite dfrac_op_own. rewrite Qp.half_half. done. }
         { iModIntro.  iFrame. }
       }
      iDestruct "Hgv" as ">Hgv".
      iDestruct "Hgv" as "[Hs1 Hs2]".
      wp_apply (wp_Mutex__Unlock
      with "[HStart Hreceiver_ready_b 
      Hs1 Hri  HP Hclosed_b
      Hvalue HSendFirst HRecSecond HSendSecond HCloseableGhostVar
      HCloseable HCloseableIff HReceiverClosedProp
      HClosedFinal HClosedCloseable HInProgressIndexNotCapped
      Hsender_ready_b Hsender_done_b Hreceiver_done_b
        HQs HPs HVs $locked]").
        {
          iFrame "#". iModIntro. iFrame. iSimpl. unfold closeable_bool.
          rewrite bool_decide_false.
          { iNamed. subst P. iFrame. iPureIntro. simpl. done. }
          { lia. }
        }
        {
         wp_pures. wp_load.
          wp_pures. 
          wp_apply (wp_forBreak (λ continue,
          (
            "LoopInv_ClosedThings" ∷  ( ∃  (send_index: nat), 
            "LoopInv_RecIndex" ∷  (ghost_var γs (DfracOwn (1/2)) send_index) ∗
            "LoopInv_PreExisting"  ∷  ((("Hrb" ∷ ret_b ↦[boolT] #true) ∗ ("HQ" ∷  Q) ∗ ("%Hriplus" ∷ ⌜send_index = (i + 1)%nat⌝) )%I) ∗     
            "%LoopInv_Break" ∷  (if continue
            then (True)
            else ( if (bool_decide((i + 1)%nat = num_uses)) then ( ghost_var γ4 DfracDiscarded true )%I else True )%I) 
            ) 
            ))%I
            with "[] [HQ Hs2 Hret_b ] [HΦ]").
            {
              clear Φ.
              iIntros "!>" (Φ) "IH HΦ". iNamed "IH". iNamed "LoopInv_ClosedThings".  
              wp_loadField. wp_apply (wp_Mutex__Lock with "Hlock"). 
              iIntros "[locked inv]". wp_pures. iNamed "inv". 
              destruct (bool_decide((i + 1)%nat < num_uses)) eqn: H.
              {
                apply bool_decide_eq_true in H.
                destruct (sender_done_b). {
                destruct closeable_b.
                {
                iDestruct "HCloseableTakeReceiverIndex" as "[Hri Hsi]".
                iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                unfold closeable_bool.
                iAssert (⌜true = false ∧ own_val0 = DfracOwn 1⌝)%I with "[HCloseable]"
                as "%Hf".
                { rewrite bool_decide_false.
                  { done.  }
                  { lia.  }  
                }
                set_solver.
                }
                {
                 wp_loadField. wp_pures. wp_loadField. 
                  wp_apply (wp_Mutex__Unlock
                  with "[HStart Hreceiver_ready_b 
                   Hclosed_b
                  Hvalue HSendFirst HRecSecond HSendSecond HCloseableGhostVar
                  HCloseable HCloseableIff HReceiverClosedProp HClosePropConsumed HClosedTakeSenderPermission
                  HClosedFinal HClosedCloseable HInProgressIndexNotCapped
                  HRecFirst
                  Hsender_ready_b Hsender_done_b Hreceiver_done_b
                    HQs HPs HVs $locked]").
                    {
                      iFrame "#". iModIntro. iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                    }
                }
              }
              {    
               wp_loadField. wp_pures. wp_loadField. 
               assert ((bool_decide ((i + 1)%nat = num_uses)) = false).
               { rewrite bool_decide_false.
               { done. }
               { lia.  } 
                }
               replace (bool_decide ((i + 1)%nat = num_uses)) with false.
                wp_apply (wp_Mutex__Unlock
                  with "[HStart Hreceiver_ready_b 
                   Hclosed_b
                  Hvalue HSendFirst HRecSecond HSendSecond HCloseableGhostVar
                  HCloseable HCloseableIff HReceiverClosedProp HClosePropConsumed HClosedTakeSenderPermission
                  HClosedFinal HClosedCloseable HInProgressIndexNotCapped
                  HRecFirst HCloseableTakeReceiverIndex
                  Hsender_ready_b Hsender_done_b Hreceiver_done_b
                    HQs HPs HVs $locked]").
                    {
                      iFrame "#". iModIntro. iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                    }
              }
              }
              { wp_loadField. 
                apply bool_decide_eq_false in H.
              destruct (sender_done_b). {
                destruct closeable_b.
                {
                  wp_loadField. 
                   wp_apply (wp_Mutex__Unlock
                  with "[HStart Hreceiver_ready_b 
                   Hclosed_b
                  Hvalue HSendFirst HRecSecond HSendSecond HCloseableGhostVar
                  HCloseable HCloseableIff HReceiverClosedProp HClosePropConsumed HClosedTakeSenderPermission
                  HClosedFinal HClosedCloseable HInProgressIndexNotCapped
                  HRecFirst HCloseableTakeReceiverIndex
                  Hsender_ready_b Hsender_done_b Hreceiver_done_b
                    HQs HPs HVs $locked]").
                    {
                      iFrame "#". iModIntro. iFrame. unfold valid_state_bool.
                      iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                    }
                }
                {
                 wp_loadField. wp_pures.  
                   wp_apply (wp_Mutex__Unlock
                  with "[HStart Hreceiver_ready_b 
                   Hclosed_b
                  Hvalue HSendFirst HRecSecond HSendSecond HCloseableGhostVar
                  HCloseable HCloseableIff HReceiverClosedProp HClosePropConsumed HClosedTakeSenderPermission
                  HClosedFinal HClosedCloseable HInProgressIndexNotCapped
                  HRecFirst HCloseableTakeReceiverIndex
                  Hsender_ready_b Hsender_done_b Hreceiver_done_b
                    HQs HPs HVs $locked]").
                    {
                      iFrame "#". iModIntro. iFrame. unfold valid_state_bool.
                      iFrame. done.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. 
                    }
                }
                }
                {  wp_loadField. wp_pures. 
                 
                destruct closeable_b.
                {
                  iNamed. unfold closeable_bool in HAllFalseIndMax.
                  apply bool_decide_unpack in HAllFalseIndMax.
                  destruct HAllFalseIndMax as (Ht & Hrd & Hind).
                  assert ((i + 1)%nat = num_uses).
                  {
                    lia. 
                  }
                  assert (index = (i+1)%nat).
                  {
                    set_solver. 
                  }
                  subst index.
                  destruct receiver_done_b.
                  {
                    unfold any_bool_true. iSimpl in "HInProgressIndexNotCapped".
                    iAssert (⌜num_uses < num_uses⌝)%I with "[HInProgressIndexNotCapped]" as "%Hf".
                    { rewrite bool_decide_true. { done.  } { set_solver. }  }
                    done.
                  }
                  {
                  unfold closeable_bool.
                  iAssert (⌜own_val0 = DfracDiscarded⌝)%I 
                  with "[HCloseable]" as "%Hov".
                  {
                  unfold closeable_bool. 
                  rewrite bool_decide_true.
                  { iNamed. iPureIntro. set_solver.  }
                  done.
                  }

                  subst own_val0. 
                  iDestruct "HCloseableGhostVar" as "#HCloseableGhostVar".
                  iFrame "#". iFrame. iFrame "#".
                  assert ((bool_decide ((i + 1)%nat = num_uses)) = true).
                  {
                    rewrite bool_decide_true. 
                    { done. }
                    { lia. }
                  }
                  replace (bool_decide ((i + 1)%nat = num_uses)) with true.
                  wp_apply (wp_Mutex__Unlock
                  with "[HStart Hreceiver_ready_b 
                  Hclosed_b
                  Hvalue HSendFirst HRecSecond HSendSecond HCloseableGhostVar
                  HCloseable HReceiverClosedProp HClosePropConsumed HClosedTakeSenderPermission
                  HClosedFinal HClosedCloseable HInProgressIndexNotCapped
                  HRecFirst HCloseableTakeReceiverIndex
                  Hsender_ready_b Hsender_done_b Hreceiver_done_b
                    HQs HPs HVs $locked]").
                    {
                      iFrame "#". iModIntro. iFrame. unfold valid_state_bool.
                      iFrame "#". iFrame. iPureIntro.
                      set_solver.
                    }
                    {
                     wp_pures. iModIntro. iApply "HΦ". iFrame. iFrame "#".
                    }
                  }
                  }
                  {
                  iDestruct "LoopInv_PreExisting" as "(Hrb & HQ & %hsi)".
                   subst send_index.
                   destruct receiver_done_b.
                   { 
                   iDestruct "HRecSecond" as "[Hsi2 HQ2]".
                   iDestruct "Hsi2" as "[Hsi Hri]".
                   iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->.
                   unfold any_bool_true.
                   iAssert (⌜(i + 1)%nat < num_uses⌝)%I with "[HInProgressIndexNotCapped]"
                   as "%Hin".
                   { iSimpl in "HInProgressIndexNotCapped".
                   assert (bool_decide(sender_ready_b = true ∨ false = true ∨ true = true) = true).
                   { rewrite bool_decide_true. { done. } { set_solver. }  }
                   replace  (bool_decide(sender_ready_b = true ∨ false = true ∨ true = true)) with true.
                   done.
                    }
                    done.
                   }
                   {
                    destruct sender_ready_b. 
                    {
                      unfold any_bool_true.
                      unfold closeable_bool.
                      iSimpl in "HSendFirst".
                      iDestruct "HSendFirst" as "[Hsi Hrest]".
                      iDestruct "Hrest" as "(Hri & HP & %Hv)".
                      iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->. 
                      iAssert (⌜(i + 1)%nat < num_uses⌝)%I with "HInProgressIndexNotCapped" 
                      as "%Ht". done. 
                    }
                    {
                      destruct receiver_ready_b.
                      {
                      iSimpl in "HRecFirst".
                      iDestruct "HRecFirst" as "[Hsi Hrest]".
                      iDestruct "Hrest" as "(Hri & HQ2)".
                      iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->. 
                      unfold closeable_bool.
                      iAssert (⌜false = true ∧ own_val0 = DfracDiscarded⌝)%I with 
                      "[HCloseable]" as "%Hf".
                      { rewrite bool_decide_true.
                      { done. }
                      { lia. }
                      }
                      lia.
                      }
                      { iSimpl in "HStart".
                      iDestruct "HStart" as "[Hsi Hri]".
                      iDestruct (ghost_var_agree with "Hsi LoopInv_RecIndex") as %->. 
                       unfold closeable_bool.
                      iAssert (⌜false = true ∧ own_val0 = DfracDiscarded⌝)%I with 
                      "[HCloseable]" as "%Hf".
                      { rewrite bool_decide_true.
                      { done. }
                      { lia. }
                      } lia.
                      }
                    }
                   }
                  }
                }
              }
            }
            {
              iFrame. replace (nth i Qs True%I) with Q. iFrame. done.
            }
            {
             iModIntro. iIntros "IH". iNamed "IH". iNamed "LoopInv_ClosedThings".
             wp_pures. iNamed "LoopInv_PreExisting".
              wp_load. iModIntro. iApply "HΦ". unfold TrySend_Xor.
              unfold TrySend_Success. unfold is_UnbufferedChannel_SenderProps_Or_Closeable.
              iFrame.
              destruct (bool_decide ((i + 1)%nat < num_uses)) eqn: H1.
              {
               apply bool_decide_eq_true in H1.
               unfold is_UnbufferedChannel_Sender.
               subst send_index.
               iFrame. 
              }
              {
               unfold is_UnbufferedChannel_CloserProps.
               iFrame "#". rewrite bool_decide_true.
               { iFrame. unfold is_UnbufferedChannel_Sender.
               subst send_index.
               iFrame. iPureIntro. apply bool_decide_eq_false in H1.
               lia. }
               apply bool_decide_eq_false in H1.
               lia. 
              }
            }
        }
    }
   }
   {
    wp_pures. wp_loadField.
    wp_apply (wp_Mutex__Unlock
    with "[HStart Hreceiver_ready_b 
    Hclosed_b HCloseableIff
    Hvalue HSendFirst HRecSecond HSendSecond HCloseableGhostVar
    HCloseable HReceiverClosedProp HClosePropConsumed HClosedTakeSenderPermission
    HClosedFinal HClosedCloseable HInProgressIndexNotCapped
    HRecFirst HCloseableTakeReceiverIndex
    Hsender_ready_b Hsender_done_b Hreceiver_done_b
    HQs HPs HVs $locked]").
    {
      iFrame "#". iModIntro. iFrame. unfold valid_state_bool.
      iFrame "#". iFrame. iSimpl. 
        iPureIntro.
      set_solver.
    }
    {
      wp_pures. wp_load. wp_pures. wp_load. iModIntro. iApply "HΦ". iFrame. iFrame "#". done.
    }
   }
  }
Qed.

End RBSHV2.