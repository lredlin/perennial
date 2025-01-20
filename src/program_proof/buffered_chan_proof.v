From Perennial.Helpers Require Import List ModArith.

From Goose.github_com.goose_lang Require Import buffered_chan_code.

From iris.algebra Require Import excl gset.
From iris.base_logic Require Import lib.ghost_var mono_nat.
From Perennial.algebra Require Import ghost_var.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.automation Require Import extra_tactics.
From Perennial.goose_lang Require Import prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import std_proof.

Class multiparG Σ : Set :=
   { #[global] multiparG_auth :: inG Σ (gset_disjR nat);
     #[global] multiparG_tok :: inG Σ (exclR unitO) }.
Definition multiparΣ := #[GFunctor (gset_disjR nat); GFunctor (exclR unitO)].
Global Instance subG_multiparΣ {Σ} :
  subG multiparΣ Σ → multiparG Σ.
Proof. solve_inG. Qed.

Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.
Context `{ghost_varG0: ghost_varG Σ nat}.


Implicit Types (v:val).

Local Lemma take_S_lookup_ne {T} (xs : list T) i j :
  i ≠ j →
  take (S i) xs !! j = take i xs !! j.
Proof.
  destruct (le_lt_dec i j) as [Hle|Hlt].
  - intros ?. rewrite lookup_take_ge; last by lia.
    rewrite lookup_take_ge; last by lia. done.
  - rewrite lookup_take. 2:lia.
    rewrite lookup_take. 2:lia.
    done.
Qed.

Lemma inv_litint (i1 i2: w64) :
  #i1 = #i2 ↔ i1 = i2.
Proof.
  split; [ | congruence ].
  inversion 1; auto.
Qed.

Section HOCAP_Q.

(* HOCAP specification
  The specification below is a per-element HOCAP specfication that supports 
  unbuffered channels with multiple sends and receives. It is based on an 
  existing specification of a locked queue at 
  https://github.com/mit-pdos/perennial/blob/master/external/Goose/github_com/mit_pdos/gokv/tutorial/queue.v
  with extensions for closed channels and a new specification. 
 *)

Record qt :=
  mk { queue: list u64;
       first: u64;
       count: u64; }.

Definition valid_elems (slice : list u64) (first : u64) (count : u64) : list u64 :=
  subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).

Definition queue_size_inv (count : u64) (first : u64) (queue_size : Z): iProp Σ :=
  (⌜word.unsigned count <= queue_size⌝ ∗ ⌜word.unsigned first < queue_size⌝ ∗ ⌜queue_size > 0⌝ 
  ∗ ⌜queue_size + 1 < 2 ^ 63⌝)%I.

Definition buffered_chan_inv_inner (q : loc) (queue : list u64) (first : u64) (count : u64) (queueSlice: Slice.t) (closed: bool) : iProp Σ :=
  "#Hqueue" ∷ q ↦[Buffered_Chan :: "queue"]□ (slice_val queueSlice) ∗
  "Hfirst" ∷ (q ↦[Buffered_Chan :: "first"] #first) ∗
  "Hcount" ∷ (q ↦[Buffered_Chan :: "count"] #count) ∗
  "Hclosed" ∷ (q ↦[Buffered_Chan :: "closed"] #closed) ∗
  "isSlice" ∷ own_slice_small queueSlice uint64T (DfracOwn 1) queue ∗
  "%Hqueue_size_inv" ∷ queue_size_inv count first (length queue).

Definition buffered_chan_inv_ghost (first : u64) (count : u64) (queue : list u64) (P : u64 -> iProp Σ) : iProp Σ :=
 "Helem" ∷ ([∗ list] _ ↦ elem ∈ valid_elems queue first count, P elem).

Definition buffered_chan_inv (q : loc) (queueSlice: Slice.t) (closed: bool) (P : u64 -> iProp Σ): iProp Σ :=
  ∃ (first : u64) (count : u64) (queue : list u64),
    "Hinner" ∷ buffered_chan_inv_inner q queue first count queueSlice closed ∗
    "Helem" ∷ ([∗ list] _ ↦ elem ∈ valid_elems queue first count, P elem). 

Definition is_buffered_chan (q : loc) (closed: bool) (P : u64 -> iProp Σ) : iProp Σ :=
  ∃ (lk : loc) (cond : loc) (queueSlice: Slice.t),  
    "#Hlock" ∷ q ↦[Buffered_Chan :: "lock"]□ #lk ∗
    "#HlockC" ∷ is_lock nroot #lk (buffered_chan_inv q queueSlice closed P) ∗
    "#Hrcond" ∷ q ↦[Buffered_Chan :: "cond"]□ #cond ∗
    "#HrcondC" ∷ is_cond cond #lk.

Theorem init : forall slice, valid_elems slice 0 0 = nil.
Proof.
  eauto.
Qed.

Lemma add_one_lemma_1 : forall slice (first : u64) (count : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  subslice (uint.nat first) (uint.nat first + uint.nat count)
  (<[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice ++
   <[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice) = subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).
Proof.
  intuition.
  assert (uint.nat first0 + uint.nat count0 < length slice ∨ (length slice <= uint.nat first0 + uint.nat count0 < length slice + length slice)).
  { word. }
  destruct H3.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0)).
    + rewrite subslice_take_drop.
      rewrite take_app_le.
      2: { rewrite length_insert. word. }
      rewrite subslice_take_drop.
      rewrite take_app_le.
      2: { word. }
      rewrite take_insert.
      { done. }
      word.
    + word_cleanup.
      rewrite Z.mod_small.
      { done. }
      word.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0 - length slice)).
    + epose proof (subslice_split_r (uint.nat first0) (length slice) _ (_ ++ _)).
      rewrite H4.
      2: word.
      2: { rewrite length_app. rewrite length_insert. word. }
      epose proof (subslice_split_r (uint.nat first0) (length slice) _ (slice ++ slice)).
      rewrite H5.
      2: word.
      2: { rewrite length_app. word. }
      assert (subslice (uint.nat first0) (length slice)
      (<[uint.nat
           (uint.nat first0 + uint.nat count0 -
            length slice):=e]> slice ++
       <[uint.nat
           (uint.nat first0 + uint.nat count0 -
            length slice):=e]> slice) = subslice (uint.nat first0) (length slice)
            (slice ++ slice)).
        {
          rewrite <- subslice_before_app_eq.
          2: { rewrite length_insert. word. }
          rewrite <- subslice_before_app_eq.
          2: word.
          rewrite subslice_take_drop.
          rewrite subslice_take_drop.
          epose proof (length_insert slice (uint.nat (uint.nat first0 + uint.nat count0 - length slice)) e).
          rewrite firstn_all.
          replace ((take (length slice)
          (<[uint.nat
               (uint.nat first0 + uint.nat count0 -
                length slice):=e]> slice))) with (take (length (<[uint.nat
                (uint.nat first0 + uint.nat count0 -
                 length slice):=e]> slice))
                (<[uint.nat
                     (uint.nat first0 + uint.nat count0 -
                      length slice):=e]> slice)).
          2: { rewrite H6. eauto. }
          rewrite firstn_all.
          rewrite drop_insert_gt. 
          {done. }
          word_cleanup.
        }
      rewrite H6.
      rewrite app_inv_head_iff.
      rewrite subslice_comm.
      rewrite subslice_comm.
      rewrite drop_app_length.
      epose proof (length_insert slice (uint.nat (uint.nat first0 + uint.nat count0 - length slice)) e).
      replace ((drop (length slice)
                (<[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice ++
                <[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice))) with (drop (length (<[uint.nat
                (uint.nat first0 + uint.nat count0 -
                 length slice):=e]> slice))
                 (<[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice ++
                 <[uint.nat (uint.nat first0 + uint.nat count0 - length slice):=e]> slice)).
      2: { rewrite H7. eauto. }
      rewrite drop_app_length.
      rewrite take_insert.
      { eauto. }
      word_cleanup.
    + 
      rewrite -(Z_mod_plus_full _ (-1)).
      rewrite Z.mod_small; word.
  Unshelve.
  { exact u64. }
  { exact (uint.nat first0 + uint.nat count0)%nat. }
  { exact (<[uint.nat
  (uint.nat first0 + uint.nat count0 - length slice)%Z:=e]>
slice). }
  { exact (<[uint.nat
  (uint.nat first0 + uint.nat count0 - length slice)%Z:=e]>
slice). }
  exact (uint.nat first0 + uint.nat count0)%nat.
Qed.

Lemma add_one_lemma_2 : forall slice (first : u64) (count : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  subslice (uint.nat first + uint.nat count) (uint.nat first + Z.to_nat(uint.Z count + 1))
  (<[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice ++
   <[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice) = [e].
Proof.
  intuition.
  assert (uint.nat first0 + uint.nat count0 < length slice ∨ (length slice <= uint.nat first0 + uint.nat count0 < length slice + length slice)).
  { word. }
  destruct H3.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0)).
    + rewrite subslice_comm.
      rewrite drop_app_le.
      2: { rewrite length_insert. word. }
      rewrite drop_insert_le.
      2: { word. }
      assert ((uint.nat (uint.nat first0 + uint.nat count0)%Z -
      (uint.nat first0 + uint.nat count0))%nat = uint.nat 0).
      { word_cleanup. }
      rewrite H4.
      match goal with
        | |- context [take ?n _] => replace n with 1%nat
      end.
      { rewrite insert_take_drop.
        { rewrite take_0.
          rewrite app_nil_l.
          rewrite firstn_cons.
          rewrite take_0.
          done.
        }
        rewrite length_drop.
        word.
      }
      word_cleanup.
    + 
      rewrite Z.mod_small; word.
  - replace (Z.to_nat(uint.Z (word.add first0 count0) `mod` length slice)) with (uint.nat(uint.nat first0 + uint.nat count0 - length slice)).
    + rewrite subslice_comm.
      rewrite drop_app_ge.
      2: { rewrite length_insert. word. }
      rewrite length_insert.
      rewrite drop_insert_le.
      2: { word. }
      assert ((uint.nat (uint.nat first0 + uint.nat count0 - length slice)%Z -
      (uint.nat first0 + uint.nat count0 - length slice))%nat = uint.nat 0).
      { word_cleanup. }
      rewrite H4.
      match goal with
        | |- context [take ?n _] => replace n with 1%nat
      end.
      { rewrite insert_take_drop.
        { rewrite take_0.
          rewrite app_nil_l.
          rewrite firstn_cons.
          rewrite take_0.
          done.
        }
        rewrite length_drop.
        word.
      }
      word.
    + 
      rewrite -(Z_mod_plus_full _ (-1)).
      rewrite Z.mod_small; word.
Qed.

Theorem add_one : forall slice (first : u64) (count : u64) e, 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  valid_elems (<[uint.nat (word.modu ((word.add) first count) (length slice)):= e]> slice) first (word.add count 1) 
  = valid_elems slice first count ++ [e].
Proof.
  intuition.
  unfold valid_elems.
  rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
    ?word.unsigned_modu_nowrap, ?unsigned_U64; [ | word .. ].
  rewrite -> !wrap_small by word.
  rewrite (subslice_split_r (uint.nat first0) (uint.nat first0 + uint.nat count0) _ (_ ++ _)).
  - rewrite add_one_lemma_1; eauto.
    rewrite app_inv_head_iff.
    apply add_one_lemma_2; eauto.
  - word.
  - rewrite length_app.
    rewrite length_insert.
    word.
Qed.

Lemma remove_one_lemma_1 : forall slice (first : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  slice !! uint.nat first = Some e -> 
  subslice (uint.nat first) (uint.nat first + 1) (slice ++ slice) = [e].
Proof.
  intuition.
  rewrite subslice_comm.
  match goal with
    | |- context [take ?n _] => replace n with 1%nat
  end.
  2: { word. }
  rewrite drop_app_le.
  2: word.
  rewrite <- (take_drop_middle (slice) (uint.nat first0) e).
  2: eauto.
  rewrite drop_app_length'.
  2: { rewrite length_take. word. }
  rewrite firstn_cons.
  rewrite take_0.
  done.
Qed.

Lemma remove_one_lemma_2 : forall (slice : list u64) (first : u64) (count : u64) (e : u64),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  0 < uint.Z count <= length slice ->
  subslice (uint.nat first + 1) (uint.nat first + uint.nat count) (slice ++ slice) = 
  subslice (Z.to_nat
  (uint.Z (word.add first 1)
    `mod` length slice))
  (Z.to_nat
    (uint.Z (word.add first 1)
    `mod` length slice) + Z.to_nat (uint.Z count - 1)) (slice ++ slice).
Proof.
  intuition.
  assert (uint.Z first0 < length slice - 1 ∨ uint.Z first0 = length slice - 1).
  { word. }
  destruct H2.
  - rewrite Z.mod_small. 2: word.
    f_equal; word.
  - rewrite H2.
    replace (Init.Nat.add (Z.to_nat (Z.sub (Datatypes.length slice) 1)) 1) with ((length slice)).
    2: word.
    replace (word.unsigned (word.add first0 1)) with (uint.Z (length slice)).
    2: word.
    replace ((uint.Z (length slice) `mod` length slice)) with 0.
    2: { rewrite Z_u64. { rewrite Z_mod_same. { done. } word. } word. }
    rewrite subslice_comm.
    rewrite drop_app_length.
    rewrite subslice_comm.
    rewrite drop_0.
    rewrite take_app_le. 2: word.
    f_equal. word.
Qed.

Theorem remove_one : forall slice (first : u64) (count : u64) e, 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  0 < uint.Z count <= length slice ->
  slice !! uint.nat first = Some e -> 
  valid_elems slice first count = cons e (valid_elems slice (word.modu ((word.add) first 1) (length slice)) (word.sub count 1)).
Proof.
  intuition.
  unfold valid_elems.
  rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
    ?word.unsigned_modu_nowrap, ?unsigned_U64; [ | word .. ].
  rewrite -> !wrap_small by word.
  rewrite (subslice_split_r (uint.nat first0) (uint.nat first0 + 1) _ (_++_)).
  - rewrite (remove_one_lemma_1 slice first0 e); eauto.
    rewrite app_inv_head_iff.
    apply remove_one_lemma_2; eauto.
  - word.
  - rewrite length_app. word.
Qed.

Lemma own_buffered_chan_ghost_alloc (first : u64) (count : u64) (queue : list u64) (P : u64 -> iProp Σ) :
count = 0 -> first = 0 ->
⊢ |={⊤}=> 
buffered_chan_inv_ghost first count queue P.
Proof.
intros. iModIntro. unfold buffered_chan_inv_ghost.  unfold valid_elems. 
replace (uint.nat count) with (0)%nat.
{ replace (uint.nat first) with (0)%nat.
  { simpl. done.  }
  { set_solver.  }
} set_solver.
Qed.

Lemma wp_buffered_chan_send (q : loc) (a : u64) (P : u64 -> iProp Σ):
  {{{ is_buffered_chan q false P ∗ P a}}} 
  Buffered_Chan__Send #q #a 
  {{{ RET #(); is_buffered_chan q false P  }}}.
Proof.
  iIntros (Φ) "[#Pre HP] Post".
  unfold Buffered_Chan__Send.
  wp_pures.
  iNamed "Pre".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "HlockC").
  iIntros "[H0 H1]".
  iNamed "H1".
  wp_pures.
  iIntros. iNamed "Hinner". 
  wp_loadField . wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to. {val_ty. }
  iIntros (queue_size) "H2".
  wp_pures. 
  iPoseProof (own_slice_small_sz with "isSlice") as "%".
  wp_apply (wp_forBreak_cond 
      (fun r =>
      ∃ (first : u64) (count : u64) (queue : list u64) ,
                buffered_chan_inv_inner q queue first count queueSlice false ∗ 
                "Helem" ∷ ([∗ list] _ ↦ elem ∈ valid_elems queue first count, P elem) ∗ 
                queue_size ↦[uint64T] #queueSlice.(Slice.sz) ∗ 
                lock.locked #lk ∗ 
                match r with
                  | false => ⌜uint.Z queueSlice.(Slice.sz) > uint.Z (count)⌝
                  | true => True
                end
                )%I with "[] [H0 Hqueue Hfirst Hcount isSlice H2 Helem Hclosed]"). 
  - iIntros (Φ') "".
    iModIntro.
    iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 &H3)".
    iIntros "Post".
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0". 
    wp_load.
    wp_loadField.
    wp_if_destruct.
    + wp_loadField.
      wp_apply (wp_Cond__Wait with "[H2 Hfirst Hcount isSlice Helem Hclosed]").
      { iFrame "# H2". iExists first1, count1, queue1. iFrame. eauto. }
      iIntros "[H0 H2]".
      wp_pures.
      unfold buffered_chan_inv.
      iNamed "H2".
      iDestruct "Hinner" as "[#Hq Hrest]".
      iNamed "Hrest".
      wp_loadField. wp_pures.
      iModIntro.
      iApply "Post".
      iFrame.
      iRename "Hqueue" into "Hqueue1".
      iFrame.  iFrame "Hqueue1". iPureIntro. done.
    + iModIntro.
      iApply "Post".
      iFrame.
      iFrame "Hqueue".
      apply Z.lt_nge in Heqb.
      iPureIntro.
      word.
  - iFrame "H2".
    iFrame "H0".
    iExists first0, count0, queue0.
    iFrame.
    iFrame "Hqueue".
    eauto.
  - iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 & %Hcount)".
    wp_pures.
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0".
    wp_loadField.
    wp_loadField.
    wp_load.
    wp_pures.
    wp_apply wp_ref_to.
    { val_ty. }
    iIntros (l) "Hl".
    wp_pures.
    wp_load.
    wp_loadField.
    iPoseProof (own_slice_small_sz with "isSlice") as "%".
    wp_apply (wp_SliceSet (V:=u64) with "[isSlice]").
    { iFrame. iPureIntro. apply lookup_lt_is_Some_2. word. }
    iIntros "H4".
    wp_pures.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[H2 Hqueue Hfirst Hcount H4 Helem HP Hclosed]").
    { iFrame "HlockC". 
      iFrame "H2". iNext. iExists _, (word.add count1 1).
      iExists (<[uint.nat
      (word.modu
         (word.add first1 count1)
         queueSlice.(Slice.sz)):=a]> queue1). 
      iFrame.
      iFrame "Hqueue".
      iSplitR.
      { 
        iPureIntro.
        rewrite length_insert.
        word.
      }
      edestruct (list_lookup_Z_lt queue1 (uint.nat
      (word.modu
        (word.add first1 count1)
        queueSlice.(Slice.sz)))).
        { word. }
          replace queueSlice.(Slice.sz) with (W64 (length queue1)).
          { rewrite add_one. 
            { rewrite big_sepL_app. simpl. iFrame. }
            { destruct Hqueue_size_inv. word. }
            { intuition. }
            { word. }
            word.
          }
          word. }
    wp_pures.
    wp_loadField.
    wp_apply (wp_Cond__Broadcast with "HrcondC").
    wp_pures.
    iModIntro.
    iApply "Post". unfold is_buffered_chan. iExists lk. iExists cond. iExists queueSlice.
    iSplitL. { iApply "Hlock". }
    iSplitL. { iApply "HlockC". }
    iSplitL. { iApply "Hrcond". }
    iApply "HrcondC".
Qed.

Lemma wp_buffered_chan_closed_receive (q : loc) (gamma : namespace) (lk : val) (P : u64 -> iProp Σ):
  {{{ is_buffered_chan q true P }}} Buffered_Chan__Receive #q {{{  RET (#null, #false); True}}}.
Proof.
  iIntros (Φ) "#Pre Post". unfold Buffered_Chan__Receive. wp_pures. iNamed "Pre". wp_loadField. 
  wp_apply wp_Mutex__Lock.
  { iFrame "HlockC". }
  wp_pures. iIntros "[Hlocked H0]". wp_pures. iNamed "H0".
  iNamed "Hinner". wp_loadField. wp_pures. iModIntro.  iApply "Post". done.
Qed.


Lemma wp_buffered_chan_receive (q : loc) (P : u64 -> iProp Σ):
  {{{ is_buffered_chan q false P   }}} Buffered_Chan__Receive #q {{{ (a:u64), RET (#a, #true); P a }}}.
Proof.
  iIntros (Φ) "#Pre Post".
  unfold Buffered_Chan__Receive.
  wp_pures.
  iNamed "Pre".
  wp_loadField.
  wp_apply wp_Mutex__Lock.
  { iFrame "HlockC". }
  iIntros "[H0 H1]".
  wp_pures.
  iNamed "H1".
  iNamed "Hinner".
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to. {val_ty. }
  iIntros (queue_size) "H2".
  wp_pures.
  iPoseProof (own_slice_small_sz with "isSlice") as "%".
  wp_apply (wp_forBreak_cond 
  (fun r =>
  ∃ (first : u64) (count : u64) (queue : list u64),
            buffered_chan_inv_inner q queue first count queueSlice false ∗ 
            "Helem" ∷ ([∗ list] _ ↦ elem ∈ valid_elems queue first count, P elem) ∗ 
            queue_size ↦[uint64T] #queueSlice.(Slice.sz) ∗ 
            lock.locked #lk ∗ 
            match r with
              | false => ⌜uint.Z (count) ≠ 0⌝
              | true => True
            end
            )%I with "[] [H0 Hqueue Hfirst Hcount isSlice H2 Helem Hclosed]").
  - iIntros (Φ') "".
    iModIntro.
    iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 & H3)".
    iIntros "Post".
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0".
    wp_loadField.
    wp_if_destruct.
    + wp_pures.
      wp_loadField.
      wp_apply (wp_Cond__Wait with "[H2 Hfirst Hcount isSlice Helem Hclosed]").
      { iFrame "# H2". iExists first1, (W64 0), queue1. iFrame. eauto. }
      iIntros "[H2 H4]".
      wp_pures.
      iModIntro.
      iApply "Post".
      iFrame.
      iRename "Hqueue" into "Hqueue1".
      iNamed "H4".
      iExists first2, count1, queue2.
      iFrame.
    + iModIntro.
      iApply "Post".
      iFrame.
      iFrame "Hqueue".
      iPureIntro.
      word.
  - iExists first0, count0, queue0.
    iFrame.
    iFrame "Hqueue".
    eauto.
  - iIntros "H0".
    iDestruct "H0" as (first1 count1 queue1) "(H0 & Helem & H1 & H2 & %Hcount)".
    wp_pures.
    iRename "Hqueue" into "Hqueue0".
    iNamed "H0".
    wp_loadField.
    wp_loadField.
    iPoseProof (own_slice_small_sz with "isSlice") as "%".
    edestruct (list_lookup_Z_lt queue1 (uint.Z first1)).
    { word. }
    wp_apply (wp_SliceGet with "[isSlice]"). 
    { 
      iFrame "isSlice".
      eauto.
    }
    iIntros "H3".
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_load.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    erewrite (remove_one queue1 first1 count1); eauto; try word.
    iDestruct "Helem" as "[Hp Helem]". 
    wp_apply (wp_Mutex__Unlock with "[HlockC H2 Hqueue Hfirst Hcount H3 Helem Hclosed]").
    { iFrame "∗#". 
      iNext.
      iExists _, (word.sub count1 1).
      iExists _. 
      iFrame "Hfirst Hcount H3 Hclosed". 
      iFrame "Hqueue".
      iSplitR.
      { 
        word.
      }
      iExactEq "Helem". unfold named. rewrite H0. f_equal. f_equal. word.
    }
    wp_pures.
    wp_loadField.
    wp_apply (wp_Cond__Broadcast with "HrcondC").
    wp_pures.
    iModIntro.
    iApply "Post".
    iFrame.
Qed.

Lemma wp_new_buffered_chan (size: w64) (P: u64 → iProp Σ) :
 {{{ ⌜0 < uint.Z size⌝ ∗ ⌜uint.Z size + 1 < 2 ^ 63⌝  }}} 
   NewBuffered_Chan #size
  {{{ (ch: loc), RET #ch; 
  is_buffered_chan ch false P }}}.
  Proof.
  wp_start.
  iDestruct "Hpre" as "%Hpre".
  rewrite -wp_fupd.
  wp_apply (wp_new_free_lock).
  iIntros (lk) "Hislock". wp_pures.
  wp_apply wp_new_slice_cap.
   { done. }
   { done. } 
  iIntros (ptr) "[H H2]". 
  wp_apply (wp_newCond' with "Hislock").
  iIntros (c) "[Hlock #Hcond]". wp_pures. wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (l). iIntros "H1".
  iDestruct (struct_fields_split with "H1") as "HH".
  iNamed "HH".  
  iMod (struct_field_pointsto_persist with "lock") as "#mu".
  iMod (struct_field_pointsto_persist with "cond") as "#cond".
  iMod (struct_field_pointsto_persist with "queue") as "#queue".
  iMod ( own_buffered_chan_ghost_alloc (W64 0) (W64 0) (replicate (uint.nat size) (W64 0)) P) as "#Hg".
  { done. }
  { done. }
  iMod (alloc_lock (nroot) _ _
    (buffered_chan_inv l (Slice.mk ptr size size) false P)   with "Hlock [ H H2 Hcond queue first count closed mu cond]"
  ) as "#Hlock".
    {
    unfold buffered_chan_inv. iModIntro. iExists (W64 0). iExists (W64 0). 
    iExists (replicate (uint.nat size) (W64 0)). unfold buffered_chan_inv_inner.
    iFrame. iSplitL "H".
      {  
        iFrame.
        iSplitR "H".
        { 
          done.
        }
        simpl. unfold queue_size_inv.
        iSplitL.  { 
        assert((zero_val uint64T) = #(W64 0)). { done. }
        replace (zero_val uint64T) with #(W64 0).
        iEval (rewrite /slice.own_slice_small /own_slice_small ?untype_replicate ?length_replicate).
        simpl. done.
        }
        iSplitL. { iPureIntro. rewrite length_replicate. word.  }
        iSplitL. { iPureIntro. rewrite length_replicate. word.  }
        iPureIntro. rewrite length_replicate. word.
      }
      iSimpl. iFrame. done.
      } 
      iApply "HΦ".
      iModIntro.
      unfold is_buffered_chan. iExists lk. iExists c.
      iExists (Slice.mk ptr size size). iFrame "#".
Qed. 
End HOCAP_Q.