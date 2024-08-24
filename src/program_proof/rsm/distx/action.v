From Perennial.program_proof Require Import grove_prelude.
(* TODO: remove this once invariance proof moved to their places. *)
From Perennial.program_proof.rsm.pure Require Import list.
From Perennial.program_proof.rsm.distx Require Import base.

Definition head_commit (l : list action) (ts : nat) (wrs : dbmap) :=
  head l = Some (ActCommit ts wrs).

Definition head_read (l : list action) (ts : nat) (key : dbkey) :=
  head l = Some (ActRead ts key).

Definition no_commit (l : list action) (tid : nat) :=
  ∀ wrs, ActCommit tid wrs ∉ l.

Definition compatible (ts : nat) (wrs : dbmap) (a : action) :=
  match a with
  | ActCommit tsa wrsa => (tsa < ts)%nat ∨ (dom wrs) ∩ (dom wrsa) = ∅
  | ActRead tsa key => (tsa ≤ ts)%nat ∨ key ∉ (dom wrs)
  end.

#[local]
Instance compatible_dec ts wrs a : Decision (compatible ts wrs a).
Proof. destruct a; simpl; apply _. Defined.

Definition incompatible (ts : nat) (wrs : dbmap) (a : action) := not (compatible ts wrs a).

Definition compatible_all (l : list action) (ts : nat) (wrs : dbmap) :=
  Forall (compatible ts wrs) l.

Definition incompatible_exists (l : list action) (ts : nat) (wrs : dbmap) :=
  Exists (incompatible ts wrs) l.

Lemma not_compatible_all_incompatible_exists l ts wrs :
  not (compatible_all l ts wrs) ↔ incompatible_exists l ts wrs.
Proof.
  split; intros H.
  - by apply not_Forall_Exists in H; last apply _.
  - by apply Exists_not_Forall in H.
Qed.

(** A more natural definition of [first_commit] would be hiding [lp] and [ls]
with exists, but and intuitively it says "the first commit action in [l] with
timestamp [ts] is [ActCommit ts wrs]". However, [first_commit_incompatible]
needs access to the first part of [l] (i.e., the one without any commit action
of timestamp [ts], so we expose [lp] and [ls] as well. *)

Definition first_commit (l lp ls : list action) (ts : nat) (wrs : dbmap) :=
  l = lp ++ ls ∧
  no_commit lp ts ∧
  head ls = Some (ActCommit ts wrs).

Definition first_commit_incompatible (l1 l2 : list action) (ts : nat) (wrs : dbmap) :=
  ∃ lp ls,
    first_commit l2 lp ls ts wrs ∧
    incompatible_exists (l1 ++ lp) ts wrs.

Definition first_commit_compatible (l : list action) (ts : nat) (wrs : dbmap) :=
  ∃ lp ls,
    first_commit l lp ls ts wrs ∧
    compatible_all lp ts wrs.

Fixpoint find_max_prefix_before_commit (ts : nat) (lp ls : list action) : (list action * list action) :=
  match ls with
  | [] => (lp, ls)
  | hd :: tl => match hd with
              | ActCommit tshd _ => if decide (tshd = ts)
                                   then (lp, ls)
                                   else find_max_prefix_before_commit ts (lp ++ [hd]) tl
              | ActRead _ _ => find_max_prefix_before_commit ts (lp ++ [hd]) tl
              end
  end.

Lemma find_max_prefix_before_commit_spec ts lp ls :
  ∃ ls1 ls2,
    find_max_prefix_before_commit ts lp ls = (lp ++ ls1, ls2) ∧
    ls = ls1 ++ ls2 ∧
    no_commit ls1 ts ∧
    (ls2 = [] ∨ ∃ wrs, head ls2 = Some (ActCommit ts wrs)).
Proof.
  generalize dependent lp.
  induction ls as [| a ls IH]; intros lp; simpl.
  { exists [], [].
    split; first by rewrite app_nil_r.
    split; first done.
    split.
    { rewrite /no_commit. set_solver. }
    by left.
  }
  destruct a as [tsa wrs | tsa key] eqn:Ha; rewrite -Ha; last first.
  { destruct (IH (lp ++ [a])) as (ls1 & ls2 & Heq & Hls2 & Hnc & Hhead).
    exists ([a] ++ ls1), ls2.
    split; first by rewrite app_assoc Heq.
    split; first set_solver.
    split.
    { intros wrsa.
      rewrite not_elem_of_app.
      split; [set_solver | done].
    }
    done.
  }
  case_decide as Htsa; last first.
  { destruct (IH (lp ++ [a])) as (ls1 & ls2 & Heq & Hls2 & Hnc & Hhead).
    exists ([a] ++ ls1), ls2.
    split; first by rewrite app_assoc Heq.
    split; first set_solver.
    split.
    { intros wrsa.
      rewrite not_elem_of_app.
      split; [set_solver | done].
    }
    done.
  }
  exists [], (a :: ls).
  split; first by rewrite app_nil_r.
  split; first by rewrite app_nil_l.
  split.
  { rewrite /no_commit. set_solver. }
  right.
  rewrite Ha Htsa.
  by eauto.
Qed.

Inductive tcform :=
(* no commit in the entire list of actions *)
| NC
(* first commit incompatible with some previous actions *)
| FCI (wrs : dbmap)
(* first commit compatible with some previous actions *)
| FCC (wrs : dbmap).

Definition peek (l : list action) (ts : nat) : tcform :=
  let (lp, ls) := find_max_prefix_before_commit ts [] l in
  match head ls with
  | None => NC
  | Some a => match a with
             | ActCommit _ wrs => if decide (compatible_all lp ts wrs)
                                 then FCC wrs
                                 else FCI wrs
             | _ => NC (* impossible case *)
             end
  end.

Theorem peek_spec l ts :
  match peek l ts with
  | NC => no_commit l ts
  | FCI wrs => first_commit_incompatible [] l ts wrs
  | FCC wrs => first_commit_compatible l ts wrs
  end.
Proof.
  unfold peek.
  destruct (find_max_prefix_before_commit_spec ts [] l) as (lp & ls & -> & Hl & Hnc & Hls).
  destruct Hls as [Hls | [wrs Hls]].
  { subst ls. by rewrite /= Hl app_nil_r. }
  rewrite Hls.
  case_decide as Hcomp.
  { by exists lp, ls. }
  { exists lp, ls. by rewrite -not_compatible_all_incompatible_exists. }
Qed.

Lemma no_commit_inv_tail_future future ts :
  no_commit future ts ->
  no_commit (tail future) ts.
Proof. intros Hnc wrs. by apply not_elem_of_tail. Qed.

Lemma first_commit_incompatible_inv_snoc_past_tail_future past future ts wrs a :
  a ≠ ActCommit ts wrs ->
  head future = Some a ->
  first_commit_incompatible past future ts wrs ->
  first_commit_incompatible (past ++ [a]) (tail future) ts wrs.
Proof.
  intros Hne Hhead (lp & ls & (Happ & Hnc & Hheadls) & Hincomp).
  assert (Hnnil : lp ≠ nil).
  { intros Hlp. subst lp.
    simpl in Happ. subst ls.
    rewrite Hhead in Hheadls.
    inv Hheadls.
  }
  exists (tail lp), ls.
  split.
  { split.
    { rewrite Happ. apply tail_app_l, Hnnil. }
    by split; first apply no_commit_inv_tail_future.
  }
  rewrite -app_assoc /=.
  replace (_ :: _) with lp; first apply Hincomp.
  rewrite -hd_error_tl_repr.
  split; last done.
  rewrite -Hhead.
  apply head_prefix; first apply Hnnil.
  rewrite Happ.
  by apply prefix_app_r.
Qed.

Lemma first_commit_compatible_inv_tail_future future ts wrs a :
  a ≠ ActCommit ts wrs ->
  head future = Some a ->
  first_commit_compatible future ts wrs ->
  first_commit_compatible (tail future) ts wrs.
Proof.
  intros Hne Hhead (lp & ls & (Happ & Hnc & Hheadls) & Hincomp).
  assert (Hnnil : lp ≠ nil).
  { intros Hlp. subst lp.
    simpl in Happ. subst ls.
    rewrite Hhead in Hheadls.
    inv Hheadls.
  }
  exists (tail lp), ls.
  split.
  { split.
    { rewrite Happ. apply tail_app_l, Hnnil. }
    by split; first apply no_commit_inv_tail_future.
  }
  by apply Forall_tail.
Qed.
