(*
   This file is part of Mixtris (https://zenodo.org/records/18749895).

   Copyright (c) Mixtris developers and contributors.
   Distributed under the terms of the BSD 3-Clause License; see
   https://gitlab.mpi-sws.org/iris/actris/-/blob/master/LICENSE
   for the full license text.
*)

(** This file defines the model of mixed choice multiparty dependent separation protocols as the solution of a recursive domain equation, along with various primitive operations, such as map.

Important: This file should not be used directly, but rather the wrappers in
[proto.v] should be used.

Multiparty Mixed Choice Dependent Separation Protocols are modeled as the solution of the following recursive domain equation:

[proto = List (action * (V → ▶ proto → PROP))]

Here, the list represents the different choies that a protocol can make.
Hence, an empty list represents the protocol with no options.
The elements of the list are the communication constructors.
The type [action] is a pair of a an inductively defined datatype [tag] with two
constructors [Send] and [Recv], and a synchronosation id of [nat].
Compared to having an additional sum in [proto], this makes it
possible to factorize the code in a better way.

The remainder [V → ▶ proto → PROP] is a predicate that ranges over the
communicated value [V] and the tail protocol [proto]. Note that to solve this
recursive domain equation using Iris's COFE solver, the recursive occurrence
of [proto] appear under the later [▶].

On top of the type [proto], we define the constructors:

- [proto_end], which constructs the empty list.
- [proto_msg], which takes an action and a predicate and constructs a singleton list with the list element constructors accordingly.
- [proto_union], which takes two protocol (lists) and concatenates them.

The defined functions on the type [proto] are:

- [proto_map], which can be used to map the actions and the propositions of
  a given protocol. *)
From iris.algebra Require Import gmap.
From iris.base_logic Require Import base_logic.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From New.golang.theory.chan.idioms.mixtris Require Import cofe_solver_2.

Set Default Proof Using "Type".

Module Export action.
  Inductive tag := Send | Recv.
  Canonical Structure tagO := leibnizO tag.
  Global Instance tag_decidable : EqDecision tag.
  Proof. solve_decision. Qed.
  Global Program Instance tag_countable : Countable tag :=
     {|
  encode t := match t with | Send => 1%positive | Recv => 2%positive end;
  decode p := Some match p return tag with 1%positive => Send | _ => Recv end
     |}.
  Next Obligation. by intros []. Qed.
  Definition action : Set := tag * nat.
  Global Instance action_inhabited : Inhabited action := populate (Send,0).
  Canonical Structure actionO := leibnizO action.
  Global Instance action_countable : Countable action.
  Proof. unfold action. apply prod_countable. Qed.
  Definition action_dual (a : action) : action :=
    match a with (Send, n) => (Recv, n) | (Recv, n) => (Send, n) end.
  Global Instance action_dual_involutive : Involutive (=) action_dual.
  Proof. by intros [[]]. Qed.
End action.

Definition proto_aux V PROP A :=
  (list (prod action (V -d> laterO A -n> PROP))).
Definition proto_auxO V PROP A :=
  (listO (prod actionO (V -d> laterO A -n> PROP))).
Definition proto_auxOF V PROP :=
  (listOF (actionO * ((V -d> ▶ ∙ -n> PROP)))).

Definition proto_result (V : Type) := result_2 (proto_auxOF V).
Definition pre_protoO (V : Type) (PROPn PROP : ofe) `{!Cofe PROPn, !Cofe PROP} : ofe :=
  solution_2_car (proto_result V) PROPn _ PROP _.
Global Instance pre_proto_cofe {V} `{!Cofe PROPn, !Cofe PROP} : Cofe (pre_protoO V PROPn PROP).
Proof. apply _. Qed.

Definition protoO (V : Type) (PROPn PROP : ofe) `{!Cofe PROPn, !Cofe PROP} : ofe :=
  proto_auxO V PROP (pre_protoO V PROP PROPn).
Global Instance protoO_cofe {V} `{!Cofe PROPn, !Cofe PROP} : Cofe (protoO V PROPn PROP).
Proof. apply _. Qed.
Lemma protoO_iso {V} `{!Cofe PROPn, !Cofe PROP} :
  ofe_iso (protoO V PROPn PROP) (pre_protoO V PROPn PROP).
Proof. apply proto_result. Qed.

Definition proto (V : Type) (PROPn PROP : ofe) `{!Cofe PROPn, !Cofe PROP} : ofe :=
  proto_aux V PROP (pre_protoO V PROP PROPn).
Global Instance proto_cofe {V} `{!Cofe PROPn, !Cofe PROP} : Cofe (proto V PROPn PROP).
Proof. apply _. Qed.
Lemma proto_iso {V} `{!Cofe PROPn, !Cofe PROP} :
  ofe_iso (proto V PROPn PROP) (pre_protoO V PROPn PROP).
Proof. apply proto_result. Qed.

Definition proto_unfold {V} `{!Cofe PROPn, !Cofe PROP} :
  proto V PROPn PROP -n> pre_protoO V PROPn PROP := ofe_iso_1 proto_iso.
Definition proto_fold {V} `{!Cofe PROPn, !Cofe PROP} :
  pre_protoO V PROPn PROP -n> proto V PROPn PROP := ofe_iso_2 proto_iso.
Lemma proto_fold_unfold {V} `{!Cofe PROPn, !Cofe PROP} (p : proto V PROPn PROP) :
  proto_fold (proto_unfold p) ≡ p.
Proof. apply (ofe_iso_21 proto_iso). Qed.
Lemma proto_unfold_fold {V} `{!Cofe PROPn, !Cofe PROP}
    (p : pre_protoO V PROP PROPn) :
  proto_unfold (proto_fold p) ≡ p.
Proof. apply (ofe_iso_12 proto_iso). Qed.

Definition proto_end {V} `{!Cofe PROPn, !Cofe PROP} : proto V PROPn PROP := [].
Definition proto_message {V} `{!Cofe PROPn, !Cofe PROP} (a : action)
  (m : V -d> later (proto V PROP PROPn) -n> PROP) : proto V PROPn PROP :=
  ([(a,(λ v, m v ◎ laterO_map proto_fold))]).
Definition proto_union {V} `{!Cofe PROPn, !Cofe PROP} (p1 p2 : proto V PROPn PROP) : proto V PROPn PROP :=
  p1 ++ p2.

Global Instance proto_message_ne {V} `{!Cofe PROPn, !Cofe PROP} a n :
  Proper (pointwise_relation V (dist n) ==> dist n)
         (proto_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof.
  intros c1 c2 Hc. rewrite /proto_message. f_equiv; [|done].
  apply pair_ne; [done|]. solve_proper.
Qed.

Global Instance proto_message_proper {V} `{!Cofe PROPn, !Cofe PROP} a :
  Proper (pointwise_relation V (≡) ==> (≡))
         (proto_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof. intros c1 c2 Hc. rewrite /proto_message. repeat f_equiv. solve_proper. Qed.

Global Instance proto_union_ne {V} `{!Cofe PROPn, !Cofe PROP} n :
  Proper ((dist n) ==> (dist n) ==> dist n)
         (proto_union (V:=V) (PROPn:=PROPn) (PROP:=PROP)).
Proof. intros p11 p12 Hp1 p21 p22 Hp2. rewrite /proto_union. by f_equiv. Qed.

Global Instance proto_union_proper {V} `{!Cofe PROPn, !Cofe PROP} :
  Proper ((≡) ==> (≡) ==> (≡))
         (proto_union (V:=V) (PROPn:=PROPn) (PROP:=PROP)).
Proof. intros p11 p12 Hp1 p21 p22 Hp2. rewrite /proto_union. by f_equiv. Qed.

Lemma proto_ind {V} `{!Cofe PROPn, !Cofe PROP} (P : proto V PROPn PROP → Prop) :
  Proper ((≡) ==> impl) P →
  P proto_end → (∀ i x p, P p → P (proto_union (proto_message i x) p)) → ∀ m, P m.
Proof.
  intros.
  induction m; [done|].
  destruct a.
  apply (H1 o (λ v, o0 v ◎ laterO_map proto_unfold) _) in IHm.
  simpl in *.
  assert (o0 ≡ λ v : V, o0 v ◎ laterO_map proto_unfold ◎ laterO_map proto_fold).
  { intros v m'. simpl. rewrite -later_map_compose. f_equiv.
    destruct m'. rewrite later_map_Next. simpl. rewrite proto_unfold_fold. done. }
  rewrite H2. done.
Qed.

Lemma proto_case {V} `{!Cofe PROPn, !Cofe PROP} (p : proto V PROPn PROP) :
  p ≡ proto_end ∨ ∃ a m p', p ≡ proto_union (proto_message a m) p'.
Proof.
  destruct p as [|[a m] p'] eqn:E; simpl in *.
  - left. done.
  - right. exists a, (λ v, m v ◎ laterO_map proto_unfold), p'.
  f_equiv. f_equiv.
  intros v m'. simpl. rewrite -later_map_compose. f_equiv.
  destruct m'. rewrite later_map_Next. simpl. rewrite proto_unfold_fold. done.
Qed.
Global Instance proto_inhabited {V} `{!Cofe PROPn, !Cofe PROP} :
  Inhabited (proto V PROPn PROP) := populate proto_end.

Lemma proto_message_equivI {Σ} {V} `{!Cofe PROPn, !Cofe PROP} a1 a2 m1 m2 :
  proto_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a1 m1 ≡ proto_message a2 m2
  ⊣⊢@{iProp Σ} ⌜ a1 = a2 ⌝ ∧ (∀ v p', m1 v p' ≡ m2 v p').
Proof.
  rewrite /proto_message list_equivI /=.
  iSplit.
  { iIntros "H".
    iSpecialize ("H" $! 0).
    simpl.
    rewrite option_equivI.
    rewrite prod_equivI.
    simpl.
    iDestruct "H" as "[%Haeq H]".
    iSplit; [done|].
    iIntros (v p). rewrite discrete_fun_equivI.
    iSpecialize ("H" $! v).
    rewrite ofe_morO_equivI=> /=.
    iSpecialize ("H" $! (laterO_map proto_unfold p)).
    assert (p ≡ later_map proto_fold (later_map proto_unfold p)) as <-; last by done.
    rewrite -later_map_compose. rewrite -(later_map_id p).
    apply later_map_ext=> p' /=. by rewrite proto_fold_unfold. }
  iIntros "[%Heq H2]" (i). rewrite Heq.
  destruct i; [|done]. simpl.
  rewrite option_equivI. rewrite prod_equivI. simpl.
  iSplit; [done|].
  rewrite discrete_fun_equivI.
  iIntros (v). rewrite ofe_morO_equivI. by iIntros (p).
Qed.
Lemma proto_message_end_equivI  {Σ} {V} `{!Cofe PROPn, !Cofe PROP} a m :
  proto_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a m ≡ proto_end ⊢@{iProp Σ} False.
Proof.
  rewrite /proto_message /proto_end. rewrite list_equivI.
  iIntros "H". iSpecialize ("H" $! 0). simpl.
  by rewrite option_equivI.
Qed.
Lemma proto_end_message_equivI {Σ} {V} `{!Cofe PROPn, !Cofe PROP} a m :
  proto_end ≡ proto_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a m ⊢@{iProp Σ} False.
Proof. by rewrite internal_eq_sym proto_message_end_equivI. Qed.

(** Utility *)
Lemma fold_left_ne {A B : ofe} n (f1 f2 : A → B → A) (xs1 xs2 : list B) (y1 y2 : A) :
  (∀ a1 a2 y1 y2, a1 ≡{n}≡ a2 → y1 ≡{n}≡ y2 → f1 a1 y1 ≡{n}≡ f2 a2 y2) →
  y1 ≡{n}≡ y2 → xs1 ≡{n}≡ xs2 →
  fold_left f1 xs1 y1 ≡{n}≡ fold_left f2 xs2 y2.
Proof.
  revert xs2. revert y1 y2.
  induction xs1 as [|x1 xs1 IHxs1].
  - by intros y1 y2 [] Hf Hx Hxs; [done|by inversion Hxs].
  - intros y1 y2 [] Hf Hx Hxs; inversion Hxs. subst. simpl.
    apply IHxs1; [done|by apply Hf|done].
Qed.

Definition proto_elim {V} `{!Cofe PROPn, !Cofe PROP} {A}
    (x y : A) (f : A → action → (V → laterO (proto V PROP PROPn) -n> PROP) → A)
    (p : proto V PROPn PROP) : A :=
  match p with
  | [] => x
  | p  => fold_left (λ acc am, f acc (am.1) (λ v, am.2 v ◎ laterO_map proto_unfold)) p y
  end.
Global Arguments proto_elim : simpl never.

Lemma proto_elim_ne {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x y : A) (f1 f2 : A → action → (V → laterO (proto V PROP PROPn) -n> PROP) → A) p1 p2 n :
  (∀ x1 x2 a m1 m2, x1 ≡{n}≡ x2 → (∀ v, m1 v ≡{n}≡ m2 v) → f1 x1 a m1 ≡{n}≡ f2 x2 a m2) →
  p1 ≡{n}≡ p2 →
  proto_elim x y f1 p1 ≡{n}≡ proto_elim x y f2 p2.
Proof.
  rewrite /proto_elim. intros Hf. revert p2.
  destruct p1 as [|[a m] p1].
  - intros p2 Hp. by inversion Hp.
  - intros p2 Hp. destruct p2 as [|[a2 m2]]; [by inversion Hp|].
    apply (fold_left_ne _ _ _ ((a, m) :: p1)); try done.
    intros *. intros Ha Hx. destruct y1, y2. simpl in *.
    destruct Hx. simpl in *. destruct H.
    apply Hf; try done. intros *. f_equiv. done.
Qed.

Lemma proto_elim_end {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x y : A) (f : A → action → (V → laterO (proto V PROP PROPn) -n> PROP) → A) :
  proto_elim x y f proto_end ≡ x.
Proof. done. Qed.

Lemma proto_elim_message {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x y : A) (f : A → action → (V → laterO (proto V PROP PROPn) -n> PROP) → A) (a:action) m :
  (Proper ((≡) ==> (=) ==> (pointwise_relation _ (≡)) ==> (≡)) f) →
  proto_elim x y f (proto_message a m) ≡ f y a m.
Proof.
  intros. rewrite /proto_elim /proto_message /=. f_equiv=> v p /=. f_equiv.
  rewrite -later_map_compose -{2}(later_map_id p).
  apply later_map_ext=> p' /=. by rewrite proto_fold_unfold.
Qed.

Lemma proto_elim_union {V} `{!Cofe PROPn, !Cofe PROP} {A : ofe}
    (x y : A) (f : A → action → (V → laterO (proto V PROP PROPn) -n> PROP) → A) p1 p2 :
  (Proper ((≡) ==> (=) ==> (pointwise_relation _ (≡)) ==> (≡)) f) →
  p1 ≠ [] → p2 ≠ [] →
  proto_elim x y f (proto_union p1 p2) ≡ proto_elim x (proto_elim x y f p1) f p2 .
Proof.
  intros Hf Hp1 Hp2. rewrite /proto_elim /proto_message /=.
  rewrite /proto_union.
  destruct p1, p2=> /=; try done.
  rewrite fold_left_app.
  solve_proper.
Qed.

(** Functor *)
Program Definition proto_map_aux {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (g : PROP -n> PROP') (rec : proto V PROP' PROPn' -n> proto V PROP PROPn) :
  proto V PROPn PROP -n> proto V PROPn' PROP' := λne p,
    (λ am, (f am.1, λ v, g ◎ am.2 v ◎ laterO_map proto_unfold ◎ laterO_map rec ◎ laterO_map proto_fold)) <$> p.
Next Obligation.
  intros V PROPn ? PROPn' ? PROP ? PROP' ? f g rec n p1 p2 Hp.
  apply: (list_fmap_ne n _ _ _ p1 p2); [|done].
  intros [a1 m1] [a2 m2] [Haeq Hmeq]. simpl in *.
  apply pair_ne; solve_proper.
Qed.

Global Instance proto_map_aux_contractive {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'} f (g : PROP -n> PROP') :
  Contractive (proto_map_aux (V:=V) (PROPn:=PROPn) (PROPn':=PROPn') f g).
Proof.
  intros n rec1 rec2 Hrec p. simpl.
  apply: (list_fmap_ne n _ _ _ p); [|done].
  intros [a1 m1] [a2 m2] Hm=> /=. apply pair_ne.
  - f_equiv. by inversion Hm.
  - inversion Hm. intros v m. simpl. do 2 f_equiv; [done|].
    do 1 f_equiv.
    apply Next_contractive; by dist_later_intro as n' Hn'.
Qed.

Definition proto_map_aux_2 {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    f (gn : PROPn' -n> PROPn) (g : PROP -n> PROP')
    (rec : proto V PROPn PROP -n> proto V PROPn' PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' :=
  proto_map_aux f g (proto_map_aux f gn rec).
Global Instance proto_map_aux_2_contractive {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    f (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  Contractive (proto_map_aux_2 (V:=V) f gn g).
Proof.
  intros n rec1 rec2 Hrec. rewrite /proto_map_aux_2.
  f_equiv. by apply proto_map_aux_contractive.
Qed.
Definition proto_map {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    f (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' :=
  fixpoint (proto_map_aux_2 f gn g).

Lemma proto_map_unfold {V}
    `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hc:!Cofe PROP, Hc':!Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') p :
  proto_map (V:=V) f gn g p ≡ proto_map_aux f g (proto_map f g gn) p.
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn g p.
  induction (lt_wf n) as [n _ IH]=>
    PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn g p.
  etrans; [apply equiv_dist, (fixpoint_unfold (proto_map_aux_2 f gn g))|].
  apply proto_map_aux_contractive; constructor=> n' ?. symmetry. apply: IH. by eauto.
Qed.
Lemma proto_map_end {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    f (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  proto_map (V:=V) f gn g proto_end ≡ proto_end.
Proof.
  rewrite proto_map_unfold /proto_map_aux /=.
  done.
Qed.
Lemma proto_map_message {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    f (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') a m :
  proto_map (V:=V) f gn g (proto_message a m)
  ≡ proto_message (f a) (λ v, g ◎ m v ◎ laterO_map (proto_map f g gn)).
Proof.
  rewrite proto_map_unfold /proto_map_aux /=.
  rewrite /proto_message. f_equiv. f_equiv. intros v. simpl. repeat f_equiv.
  intros m'. simpl. repeat f_equiv. rewrite -later_map_compose.
  destruct m'. simpl. rewrite later_map_Next. simpl. rewrite proto_fold_unfold.
  done.
Qed.
Lemma proto_map_union {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    f (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') p1 p2 :
  proto_map (V:=V) f gn g (proto_union p1 p2)
  ≡ proto_union (proto_map f gn g p1) (proto_map f gn g p2).
Proof.
  rewrite !proto_map_unfold !/proto_map_aux /=.
  rewrite !/proto_union.
  rewrite fmap_app. done.
Qed.

Lemma proto_map_ne {V}
    `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hc:!Cofe PROP, Hc':!Cofe PROP'}
    f (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') p n :
  gn1 ≡{n}≡ gn2 → g1 ≡{n}≡ g2 →
  proto_map (V:=V) f gn1 g1 p ≡{n}≡ proto_map (V:=V) f gn2 g2 p.
Proof.
  revert PROPn Hcn PROPn' Hcn' PROP Hc PROP' Hc' gn1 gn2 g1 g2 p.
  induction (lt_wf n) as [n _ IH]=>
              PROPn ? PROPn' ? PROP ? PROP' ? gn1 gn2 g1 g2 p Hgn Hg /=.
  pattern p. apply proto_ind.
  { intros p1 p2 Hp H'. rewrite -Hp. done. }
  { rewrite !proto_map_end. done. }
  intros a m p' Hp'.
  rewrite !proto_map_union.
  apply proto_union_ne; [|done].
  { rewrite !proto_map_message /=.
    apply proto_message_ne => // v p'' /=. f_equiv; [done|]. f_equiv.
    apply Next_contractive; dist_later_intro as n' Hn'; eauto using dist_lt with lia. }
Qed.
Lemma proto_map_ext {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (gn1 gn2 : PROPn' -n> PROPn) f (g1 g2 : PROP -n> PROP') p :
  gn1 ≡ gn2 → g1 ≡ g2 → proto_map (V:=V) f gn1 g1 p ≡ proto_map (V:=V) f gn2 g2 p.
Proof.
  intros Hgn Hg. apply equiv_dist=> n.
  apply proto_map_ne=> // ?; by apply equiv_dist.
Qed.
Lemma proto_map_id {V} `{Hcn:!Cofe PROPn, Hc:!Cofe PROP} (p : proto V PROPn PROP) :
  proto_map id cid cid p ≡ p.
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROP Hc p.
  induction (lt_wf n) as [n _ IH]=> PROPn ? PROP ? p /=.
  pattern p.
  apply proto_ind.
  { intros p1 p2 Hp H'. rewrite -Hp. done. }
  { rewrite !proto_map_end. done. }
  intros a m p' Hp'.
  rewrite proto_map_union. f_equiv.
  { rewrite !proto_map_message /=. apply proto_message_ne=> // v p'' /=. f_equiv.
    apply Next_contractive; dist_later_intro as n' Hn'; auto. }
  done.
Qed.
Lemma proto_map_compose {V}
   `{Hcn:!Cofe PROPn, Hcn':!Cofe PROPn', Hcn'':!Cofe PROPn'',
     Hc:!Cofe PROP, Hc':!Cofe PROP', Hc'':!Cofe PROP''}
    (gn1 : PROPn'' -n> PROPn') (gn2 : PROPn' -n> PROPn)
    (g1 : PROP -n> PROP') (g2 : PROP' -n> PROP'') (p : proto V PROPn PROP) :
  proto_map id (gn2 ◎ gn1) (g2 ◎ g1) p ≡ proto_map id gn1 g2 (proto_map id gn2 g1 p).
Proof.
  apply equiv_dist=> n. revert PROPn Hcn PROPn' Hcn' PROPn'' Hcn''
    PROP Hc PROP' Hc' PROP'' Hc'' gn1 gn2 g1 g2 p.
  induction (lt_wf n) as [n _ IH]=> PROPn ? PROPn' ? PROPn'' ?
    PROP ? PROP' ? PROP'' ? gn1 gn2 g1 g2 p /=.
  pattern p. apply proto_ind.
  { intros p1 p2 Hp H'. rewrite -Hp. done. }
  { rewrite !proto_map_end. done. }
  intros a m p' Hp'.
  rewrite !proto_map_union. f_equiv.
  { rewrite !proto_map_message /=. apply proto_message_ne=> // v p'' /=. do 3 f_equiv.
    apply Next_contractive; dist_later_intro as n' Hn'; auto. }
  done.
Qed.

Program Definition protoOF (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} : oFunctor := {|
  oFunctor_car A _ B _ := proto V (oFunctor_car Fn B A) (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    proto_map id (oFunctor_map Fn (fg.2, fg.1)) (oFunctor_map F fg)
|}.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? B1 ? B2 ? n f g [??] p; simpl in *.
  apply proto_map_ne=> // y; by apply oFunctor_map_ne.
Qed.
Next Obligation.
  intros V Fn F ?? A ? B ? p; simpl in *. rewrite /= -{2}(proto_map_id p).
  apply proto_map_ext=> //= y; by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' p; simpl in *.
  rewrite -proto_map_compose.
  apply proto_map_ext=> //= y; by rewrite ofe.oFunctor_map_compose.
Qed.

Global Instance protoOF_contractive (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} :
  oFunctorContractive Fn → oFunctorContractive F →
  oFunctorContractive (protoOF V Fn F).
Proof.
  intros HFn HF A1 ? A2 ? B1 ? B2 ? n f g Hfg p; simpl in *.
  apply proto_map_ne=> y //=.
  + apply HFn. dist_later_intro as n' Hn'. f_equiv; apply Hfg.
  + apply HF. by dist_later_intro as n' Hn'.
Qed.
