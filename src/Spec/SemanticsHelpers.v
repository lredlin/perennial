From Classes Require Import EqualDec.
From stdpp Require Import base.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecoveryRefinement Require Import Spec.Proc.

Set Implicit Arguments.

Arguments existT {A P} _ _.
Import EqNotations.

Import RelationNotations.

(* modeling non-atomic operations as pairs of begin/end ops *)
Inductive NonAtomicArgs T :=
| FinishArgs (args:T)
| Begin.
Arguments Begin {T}.
(* NOTE: this does not allow dependent return values *)
Definition retT T (args:NonAtomicArgs T) T' : Type := if args then T' else unit.

(* nonAtomicOp takes an operation partially applied to some key identifying
  the object (assuming the operation does separate over some resources, such as
  addresses or references) *)
Definition nonAtomicOp {Op ArgT T}
           (op: forall (args:NonAtomicArgs ArgT), Op (retT args T))
  : ArgT -> proc Op T :=
  fun args => Bind (Call (op Begin)) (fun _ => Call (op (FinishArgs args))).


(* this is represented as an inductive rather than a combination of ObjΣ and a
  boolean state to make misuse harder (there's no reasonable way to use the
  state without knowing the status) *)
Inductive NonAtomicState ObjΣ : Type :=
| Clean (s:ObjΣ)
| Dirty (s:ObjΣ).

Definition readClean {State} ObjΣ (s: NonAtomicState ObjΣ) : relation State State ObjΣ :=
  match s with
  | Clean s => pure s
  | Dirty _ => error
  end.

Definition readDirty {State} ObjΣ (s: NonAtomicState ObjΣ) : relation State State ObjΣ :=
  match s with
  | Clean _ => error
  | Dirty s  => pure s
  end.

Definition nonAtomicStep
           {ArgT} (args: NonAtomicArgs ArgT) {T} (* the operation *)
           {ObjΣ} (obj_s: NonAtomicState ObjΣ)
           {State}
           (mkDirty: ObjΣ -> relation State State unit)
           (opStep: ObjΣ -> ArgT -> relation State State T)
  : relation State State (retT args T) :=
  match args with
  | Begin => s <- readClean obj_s;
              mkDirty s
  | FinishArgs x => s <- readDirty obj_s;
                     opStep s x
  end.

Record DynMap A (Ref: A -> Type) (Model: A -> Type) :=
  { dynMap : sigT Ref -> option (sigT Model);
    dynMap_wf : forall T v, match dynMap (existT T v) with
                       | Some (existT T' _) => T' = T
                       | None => True
                       end;
    dynMap_dom : list (sigT Ref);
    dynMap_dom_spec : forall x, dynMap x <> None <-> In x dynMap_dom;
    dynMap_dom_nodup : NoDup dynMap_dom;
}.

Module OptionNotations.
  Delimit Scope option_monad with opt.
  Notation "'Some!' x <- a ; f" :=
    (match a with
     | Some x => f
     | _ => None
     end)
      (right associativity, at level 70, x pattern) : option_monad.

  Notation "'left!' H <- a ; f" :=
    (match a with
     | left H => f
     | right _ => None
     end)
      (right associativity, at level 60, f at level 200) : option_monad.

  Notation "'ret!' a" := (Some a) (at level 60) : option_monad.
End OptionNotations.

Import EqualDecNotation.
Import OptionNotations.
Local Open Scope option_monad.

Definition getDyn A (Ref Model: A -> Type)
           (m: DynMap Ref Model) a (r: Ref a) : option (Model a).
Proof.
  pose proof (m.(dynMap_wf) _ r).
  destruct (m.(dynMap) (existT a r)); [ apply Some | exact None ].
  destruct s.
  exact (rew H in m0).
Defined.

Require Import Program.

Lemma getDyn_lookup1 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) (v: Model a) :
  m.(dynMap) (existT _ r) = Some (existT _ v) →
  getDyn m a r = Some v.
Proof.
  unfold getDyn. destruct m as [map wf]. simpl.
  generalize (wf a r). generalize (map (existT a r)).
  intros ret Heq. clear.
  destruct ret as [(?&?)|]; inversion 1.
  subst. apply Eqdep.EqdepTheory.inj_pair2 in H2; subst; auto.
Qed.

Lemma getDyn_lookup2 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) (v: Model a) :
  getDyn m a r = Some v →
  m.(dynMap) (existT _ r) = Some (existT _ v).
Proof.
  unfold getDyn. destruct m as [map wf]. simpl.
  generalize (wf a r). generalize (map (existT a r)).
  intros ret Heq. clear.
  destruct ret as [(?&?)|]; inversion 1.
  subst. unfold eq_rect. auto.
Qed.

Lemma getDyn_lookup_none A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) :
  getDyn m a r = None <->
  m.(dynMap) (existT _ r) = None.
Proof.
  unfold getDyn. destruct m as [map wf]. simpl.
  generalize (wf a r). generalize (map (existT a r)).
  intros ret Heq. clear.
  destruct ret as [(?&?)|]; [| intuition].
  split; inversion 1.
Qed.

Lemma getDyn_lookup_none1 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) :
  m.(dynMap) (existT _ r) = None ->
  getDyn m a r = None.
Proof. edestruct getDyn_lookup_none; eauto. Qed.

Lemma getDyn_lookup_none2 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) :
  getDyn m a r = None ->
  m.(dynMap) (existT _ r) = None.
Proof. edestruct getDyn_lookup_none; eauto. Qed.

Arguments getDyn {A Ref Model} m {a} r.
From stdpp Require Import list.

Instance In_dec {T} {dec: EqualDec T} (a: T) l:
  Decision (In a l).
Proof.
  assert (EqDecision T).
  { unfold EqDecision, EqualDec, Decision in *; eauto. }
  edestruct (@elem_of_list_dec _ _ a l).
  * left. by apply elem_of_list_In.
  * right. intros Hfalse. eapply n. by apply elem_of_list_In.
Qed.

Definition updDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
           a (v: Ref a) (x: Model a) (m: DynMap Ref Model) : DynMap Ref Model.
Proof.
  refine {| dynMap := fun r => if r == existT a v then ret! existT a x else m.(dynMap) r;
            dynMap_dom := if decide (In (existT a v) m.(dynMap_dom)) then
                            m.(dynMap_dom)
                          else
                            existT a v :: m.(dynMap_dom) |}.
  { intros.
    destruct (existT _ v0 == existT _ v).
    - inversion e; auto.
    - apply (m.(dynMap_wf) _ v0). }
  { intros (a'&v').
    destruct (existT _ _ == existT _ v).
    - abstract (split; auto; intros _; inversion e; subst;
                apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto;
                case (decide); eauto; intros; by left).
    - abstract (rewrite dynMap_dom_spec; split; case (decide); auto; intros ?;
                [ by right | intros [|]; eauto; congruence ]).
  }
  { case (decide).
    - intros; apply dynMap_dom_nodup.
    - intros Hnotin. econstructor; [| apply dynMap_dom_nodup].
      by rewrite elem_of_list_In.
  }
Defined.

Lemma remove_In_ne {A: Type} dec (l: list A) (x y : A):
  ~ (x = y) -> In y (remove dec x l) <-> In y l.
Proof.
  induction l; eauto.
  intros Hneq. simpl. destruct dec; subst.
  * rewrite IHl; intuition.
  * simpl. rewrite IHl; eauto.
Qed.

Lemma remove_NoDup {A: Type} dec (l: list A) (x : A):
  NoDup l → NoDup (remove dec x l).
Proof.
  induction 1; simpl. econstructor.
  destruct dec; subst; eauto.
  econstructor; eauto. rewrite elem_of_list_In, remove_In_ne; eauto.
  by rewrite <-elem_of_list_In.
Qed.

Definition deleteDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
           a (v: Ref a) (m: DynMap Ref Model) : DynMap Ref Model.
Proof.
  refine {| dynMap := fun r => if r == existT a v then None else m.(dynMap) r;
            dynMap_dom := remove dec (existT a v) m.(dynMap_dom) |}.
  intros.
  destruct (existT _ v0 == existT _ v).
  - auto.
  - apply (m.(dynMap_wf) _ v0).
  - { intros (a'&v').
      destruct (existT _ _ == existT _ v).
      - split; auto; intros Hin.
        * by eauto.
        * inversion e. subst.
          apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto.
          exfalso; eapply remove_In; eauto.
      - rewrite dynMap_dom_spec. rewrite remove_In_ne; auto.
    }
  - apply remove_NoDup, dynMap_dom_nodup.
Defined.

Arguments updDyn {A Ref Model dec a} v x m.
Arguments deleteDyn {A Ref Model dec a} v m.

Instance empty_dynmap A Ref Model : Empty (@DynMap A Ref Model).
refine {| dynMap := fun _ => None; dynMap_dom := nil |}.
- intros; auto.
- abstract (intros; split; try inversion 1; congruence).
- econstructor.
Defined.

Lemma getDyn_deleteDyn_ne A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a (r1 r2: Ref a) :
  ~ (r1 = r2) ->
  getDyn (deleteDyn r1 m) r2 =
  getDyn m r2.
Proof.
  intros.
  unfold getDyn, deleteDyn. destruct m as [map wf]. simpl.
  destruct (equal).
  { apply Eqdep.EqdepTheory.inj_pair2 in e; subst; congruence. }
  generalize (wf a r2).
  generalize (map (existT a r2)).
  simpl.
  intros ret Heq.
  destruct ret as [(?&?)|]; [| intuition].
  unfold eq_rect. auto.
Qed.