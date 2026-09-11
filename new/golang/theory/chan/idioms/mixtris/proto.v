(*
   This file is part of Mixtris (https://zenodo.org/records/18749895).

   Copyright (c) Mixtris developers and contributors.
   Distributed under the terms of the BSD 3-Clause License; see
   https://gitlab.mpi-sws.org/iris/actris/-/blob/master/LICENSE
   for the full license text.
*)

(** This file defines the core of the Mixtris logic: It defines Mixed Choice Multiparty Dependent Separation Protocols and the associated Iris ghost theory.

Mixed Choice Multiparty Dependent Separation Protocols [iProto] are defined by instantiating the parameterized version in [proto_model] with the type of propositions [iProp] of Iris.
We define ways of constructing instances of the instantiated type via two
constructors:
- [iProto_end], which is identical to [proto_end].
- [iProto_message], which takes an [action] and an [iMsg]. The type [iMsg] is a
  sequence of binders [iMsg_exist], terminated by the payload constructed with
  [iMsg_base] based on arguments [v], [P] and [prot], which are the value, the
  carried proposition and the [iProto] tail, respectively.
- [iProto_union], which is identical to [proto_union].

For convenience sake, we provide the following notations:
- [END], which is simply [iProto_end].
- [∃ x, m], which is [iMsg_exist] with argument [m].
- [MSG v {{ P }}; prot], which is [iMsg_Base] with arguments [v], [P] and [prot].
- [<a> m], which is [iProto_message] with arguments [a] and [m].
- [p1 <+> p2], which is [iProto_union] with arguments [p1] and [p2].

We also include custom notation to more easily construct complete constructions:
- [<a x1 .. xn> m], which is [<a> ∃ x1, .. ∃ xn, m].
- [<a x1 .. xn> MSG v; {{ P }}; prot], which constructs a full protocol.

In addition we define the subprotocol relation [iProto_le] [⊑].
For mixed choice, this most notable allow us to discard choices:

                                     p1 ⊑ p1'   p2 ⊑ p2'
--------------   --------------    -----------------------
p1 <+> p2 ⊑ p1   p1 <+> p2 ⊑ p2    p1 <+> p2 ⊑ p1' <+> p2'

Lastly, relevant type classes instances are defined for each of the above
notions, such as contractiveness and non-expansiveness, after which the
specifications of the message-passing primitives are defined in terms of the
protocol connectives. *)
From iris.algebra Require Import gmap excl_auth gmap_view.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From iris.program_logic Require Import language.
From New.golang.theory.chan.idioms.mixtris Require Import proto_model.
Set Default Proof Using "Type".
Export action.

(** * Setup of Iris's cameras *)
Class protoG Σ V :=
  protoG_authG ::
    inG Σ (gmap_viewR natO
      (optionUR (exclR (laterO (proto (leibnizO V) (iPropO Σ) (iPropO Σ)))))).

Definition protoΣ V := #[
  GFunctor ((gmap_viewRF natO (optionRF (exclRF (laterOF (protoOF (leibnizO V) idOF idOF))))))
].
Global Instance subG_chanΣ {Σ V} : subG (protoΣ V) Σ → protoG Σ V.
Proof. solve_inG. Qed.

(** * Types *)
Definition iProto Σ V := proto V (iPropO Σ) (iPropO Σ).
Declare Scope proto_scope.
Delimit Scope proto_scope with proto.
Bind Scope proto_scope with iProto.
Local Open Scope proto.

(** * Messages *)
Section iMsg.
  Set Primitive Projections.
  Record iMsg Σ V := IMsg { iMsg_car : V → laterO (iProto Σ V) -n> iPropO Σ }.
End iMsg.
Arguments IMsg {_ _} _.
Arguments iMsg_car {_ _} _.

Declare Scope msg_scope.
Delimit Scope msg_scope with msg.
Bind Scope msg_scope with iMsg.
Global Instance iMsg_inhabited {Σ V} : Inhabited (iMsg Σ V) := populate (IMsg inhabitant).

Section imsg_ofe.
  Context {Σ : gFunctors} {V : Type}.

  Global Instance iMsg_equiv : Equiv (iMsg Σ V) := λ m1 m2,
    ∀ w p, iMsg_car m1 w p ≡ iMsg_car m2 w p.
  Global Instance iMsg_dist : Dist (iMsg Σ V) := λ n m1 m2,
    ∀ w p, iMsg_car m1 w p ≡{n}≡ iMsg_car m2 w p.

  Lemma iMsg_ofe_mixin : OfeMixin (iMsg Σ V).
  Proof. by apply (iso_ofe_mixin (iMsg_car : _ → V -d> _ -n> _)). Qed.
  Canonical Structure iMsgO := Ofe (iMsg Σ V) iMsg_ofe_mixin.

  Global Instance iMsg_cofe : Cofe iMsgO.
  Proof. by apply (iso_cofe (IMsg : (V -d> _ -n> _) → _) iMsg_car). Qed.
End imsg_ofe.

Program Definition iMsg_base_def {Σ V}
    (v : V) (P : iProp Σ) (p : iProto Σ V) : iMsg Σ V :=
  IMsg (λ v', λne p', ⌜ v = v' ⌝ ∗ Next p ≡ p' ∗ P)%I.
Next Obligation. solve_proper. Qed.
Definition iMsg_base_aux : seal (@iMsg_base_def). by eexists. Qed.
Definition iMsg_base := iMsg_base_aux.(unseal).
Definition iMsg_base_eq : @iMsg_base = @iMsg_base_def := iMsg_base_aux.(seal_eq).
Arguments iMsg_base {_ _} _%_V _%_I _%_proto.
Global Instance: Params (@iMsg_base) 3 := {}.

Program Definition iMsg_exist_def {Σ V A} (m : A → iMsg Σ V) : iMsg Σ V :=
  IMsg (λ v', λne p', ∃ x, iMsg_car (m x) v' p')%I.
Next Obligation. solve_proper. Qed.
Definition iMsg_exist_aux : seal (@iMsg_exist_def). by eexists. Qed.
Definition iMsg_exist := iMsg_exist_aux.(unseal).
Definition iMsg_exist_eq : @iMsg_exist = @iMsg_exist_def := iMsg_exist_aux.(seal_eq).
Arguments iMsg_exist {_ _ _} _%_msg.
Global Instance: Params (@iMsg_exist) 3 := {}.

Definition iMsg_texist {Σ V} {TT : tele} (m : TT → iMsg Σ V) : iMsg Σ V :=
  tele_fold (@iMsg_exist Σ V) (λ x, x) (tele_bind m).
Arguments iMsg_texist {_ _ !_} _%_msg /.

Lemma iMsg_fold_unfold {Σ V} (m : iMsg Σ V) v lp :
  iMsg_car m v lp ≡ iMsg_car m v (later_map proto_fold (later_map proto_unfold lp)).
Proof. by rewrite later_map_Next proto_fold_unfold. Qed.

Notation "'MSG' v {{ P } } ; p" := (iMsg_base v P p)
  (at level 200, v at level 20, right associativity,
   format "MSG  v  {{  P  } } ;  p") : msg_scope.
Notation "'MSG' v ; p" := (iMsg_base v True p)
  (at level 200, v at level 20, right associativity,
   format "MSG  v ;  p") : msg_scope.
Notation "∃ x .. y , m" :=
  (iMsg_exist (λ x, .. (iMsg_exist (λ y, m)) ..)%msg) : msg_scope.
Notation "'∃..' x .. y , m" :=
  (iMsg_texist (λ x, .. (iMsg_texist (λ y, m)) .. )%msg)
  (at level 200, x binder, y binder, right associativity,
   format "∃..  x  ..  y ,  m") : msg_scope.

Lemma iMsg_texist_exist {Σ V} {TT : tele} w lp (m : TT → iMsg Σ V) :
  iMsg_car (∃.. x, m x)%msg w lp ⊣⊢ (∃.. x, iMsg_car (m x) w lp).
Proof.
  rewrite /iMsg_texist iMsg_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. apply IH.
Qed.

(** * Operators *)
Definition iProto_end_def {Σ V} : iProto Σ V := proto_end.
Definition iProto_end_aux : seal (@iProto_end_def). by eexists. Qed.
Definition iProto_end := iProto_end_aux.(unseal).
Definition iProto_end_eq : @iProto_end = @iProto_end_def := iProto_end_aux.(seal_eq).
Arguments iProto_end {_ _}.

Definition iProto_message_def {Σ V} (a : action) (m : iMsg Σ V) : iProto Σ V :=
  proto_message a (iMsg_car m).
Definition iProto_message_aux : seal (@iProto_message_def). by eexists. Qed.
Definition iProto_message := iProto_message_aux.(unseal).
Definition iProto_message_eq :
  @iProto_message = @iProto_message_def := iProto_message_aux.(seal_eq).
Arguments iProto_message {_ _} _ _%_msg.
Global Instance: Params (@iProto_message) 3 := {}.

Definition iProto_union_def {Σ V} (p1 p2 : iProto Σ V) : iProto Σ V :=
  proto_union p1 p2.
Definition iProto_union_aux : seal (@iProto_union_def). by eexists. Qed.
Definition iProto_union := iProto_union_aux.(unseal).
Definition iProto_union_eq :
  @iProto_union = @iProto_union_def := iProto_union_aux.(seal_eq).
Arguments iProto_union {_ _} _ _.
Global Instance: Params (@iProto_union) 2 := {}.

Notation "'END'" := iProto_end : proto_scope.

Notation "< a > m" := (iProto_message a m)
  (at level 200, a at level 10, m at level 200,
   format "<  a  >  m") : proto_scope.
Notation "< a @ x1 .. xn > m" := (iProto_message a (∃ x1, .. (∃ xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "<  a  @  x1  ..  xn  >  m") : proto_scope.
Notation "< a @.. x1 .. xn > m" := (iProto_message a (∃.. x1, .. (∃.. xn, m) ..))
  (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
   format "<  a  @..  x1  ..  xn  >  m") : proto_scope.

Notation "<![ i ]> m" := (< (Send,i) > m) (at level 200, m at level 200) : proto_scope.
Notation "<![ i ] x1 .. xn > m" := (< (Send,i) > ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<![  i  ]  x1  ..  xn >  m") : proto_scope.
Notation "<![ i ].. x1 .. xn > m" := (< (Send,i) > ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<![  i  ]..  x1  ..  xn >  m") : proto_scope.

Notation "<?[ i ]> m" := (< (Recv,i) > m) (at level 200, m at level 200) : proto_scope.
Notation "<?[ i ] x1 .. xn > m" := (< (Recv,i) > ∃ x1, .. (∃ xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<?[  i  ]  x1  ..  xn >  m") : proto_scope.
Notation "<?[ i ].. x1 .. xn > m" := (< (Recv,i) > ∃.. x1, .. (∃.. xn, m) ..)
  (at level 200, x1 closed binder, xn closed binder, m at level 200,
   format "<?[  i  ]..  x1  ..  xn >  m") : proto_scope.

Infix "<+>" := iProto_union (at level 20) : proto_scope.

Class MsgTele {Σ V} {TT : tele} (m : iMsg Σ V)
    (tv : TT -t> V) (tP : TT -t> iProp Σ) (tp : TT -t> iProto Σ V) :=
  msg_tele : m ≡ (∃.. x, MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x)%msg.
Global Hint Mode MsgTele ! ! - ! - - - : typeclass_instances.

(** * Operations *)
Program Definition iMsg_map {Σ V}
    (rec : iProto Σ V → iProto Σ V) (m : iMsg Σ V) : iMsg Σ V :=
  IMsg (λ v, λne p1', ∃ p1, iMsg_car m v (Next p1) ∗ p1' ≡ Next (rec p1))%I.
Next Obligation. solve_proper. Qed.

Program Definition iProto_map_app_aux {Σ V}
  (f : action → action)
  (p2 : iProto Σ V)
  (rec: iProto Σ V -n> iProto Σ V)
  : iProto Σ V -n> iProto Σ V := λne p,
  proto_elim p2 proto_end
    (λ acc a (m : V → laterO (iProto Σ V) -n> iProp Σ),
      proto_union
        (proto_message (f a) (iMsg_car (iMsg_map rec (IMsg m)))) acc) p.
Next Obligation.
  intros Σ V f p2 rec n p1 p1' Hp. apply proto_elim_ne=> // p1'' p2' m1 m2 Ha Hp' Hm.
  apply proto_union_ne; [|done].
  simpl.
  apply proto_message_ne=> v p' /=. by repeat f_equiv.
Qed.
Global Arguments iProto_map_app_aux : simpl never.

Global Instance iProto_map_app_aux_contractive {Σ V} f (p2 : iProto Σ V) :
  Contractive (iProto_map_app_aux f p2).
Proof.
  intros n rec1 rec2 Hrec p1; simpl. apply proto_elim_ne=> // p1' p2' m1 m2 Ha Hm Hf.
  f_equiv; [|done].
  apply pair_ne; [solve_proper|].
  intros v m. simpl.
  by repeat (f_contractive || f_equiv).
Qed.

Definition iProto_map_app {Σ V} (f : action → action)
    (p2 : iProto Σ V) : iProto Σ V -n> iProto Σ V :=
  fixpoint (iProto_map_app_aux f p2).

Definition iProto_app_def {Σ V} (p1 p2 : iProto Σ V) : iProto Σ V :=
  iProto_map_app id p2 p1.
Definition iProto_app_aux : seal (@iProto_app_def). Proof. by eexists. Qed.
Definition iProto_app := iProto_app_aux.(unseal).
Definition iProto_app_eq : @iProto_app = @iProto_app_def := iProto_app_aux.(seal_eq).
Arguments iProto_app {_ _} _%_proto _%_proto.
Global Instance: Params (@iProto_app) 2 := {}.
Infix "<++>" := iProto_app (at level 60) : proto_scope.
Notation "m <++> p" := (iMsg_map (flip iProto_app p) m) : msg_scope.
Lemma iProto_app_unfold {Σ V} (p1 p2 : iProto Σ V) :
  iProto_app p1 p2 ≡ iProto_map_app_aux id p2 (iProto_map_app id p2) p1.
Proof. rewrite iProto_app_eq. rewrite /iProto_app_def /iProto_map_app.
       apply: (fixpoint_unfold (iProto_map_app_aux id p2)). Qed.

Definition iProto_dual_def {Σ V} (p : iProto Σ V) : iProto Σ V :=
  iProto_map_app action_dual proto_end p.
Definition iProto_dual_aux : seal (@iProto_dual_def). Proof. by eexists. Qed.
Definition iProto_dual := iProto_dual_aux.(unseal).
Definition iProto_dual_eq :
  @iProto_dual = @iProto_dual_def := iProto_dual_aux.(seal_eq).
Arguments iProto_dual {_ _} _%_proto.
Global Instance: Params (@iProto_dual) 2 := {}.
Notation iMsg_dual := (iMsg_map iProto_dual).

Definition iProto_dual_if {Σ V} (d : bool) (p : iProto Σ V) : iProto Σ V :=
  if d then iProto_dual p else p.
Arguments iProto_dual_if {_ _} _ _%_proto.
Global Instance: Params (@iProto_dual_if) 3 := {}.

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types v : V.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  (** ** Equality *)
  Lemma iProto_case p : p ≡ END ∨ ∃ t n m ps, p ≡ iProto_union (iProto_message (t, n) m) ps.
  Proof.
    destruct (proto_case p) as [|([t n] & m & ps & Hps)]; [left; by rewrite iProto_end_eq|].
    right. exists t, n, (IMsg m), ps. rewrite iProto_message_eq iProto_union_eq. done.
  Qed.
  Lemma iProto_message_equivI a1 a2 m1 m2 :
    (<a1> m1) ≡ (<a2> m2) ⊣⊢@{iProp Σ} ⌜ a1 = a2 ⌝ ∧
      (∀ v lp, iMsg_car m1 v lp ≡ iMsg_car m2 v lp).
  Proof. rewrite iProto_message_eq. apply proto_message_equivI. Qed.

  Lemma iProto_message_end_equivI a m :
    (<a> m) ≡ END ⊢@{iProp Σ} False.
  Proof. rewrite iProto_message_eq iProto_end_eq. apply proto_message_end_equivI. Qed.
  Lemma iProto_end_message_equivI a m :
    END ≡ (<a> m) ⊢@{iProp Σ} False.
  Proof. by rewrite internal_eq_sym iProto_message_end_equivI. Qed.

  (** ** Non-expansiveness of operators *)
  Global Instance iMsg_car_proper :
    Proper ((≡) ==> (=) ==> (≡) ==> (≡)) (iMsg_car (Σ:=Σ) (V:=V)).
  Proof.
    intros m1 m2 meq v1 v2 veq p1 p2 peq. specialize (meq v1 p1). rewrite meq.
    f_equiv; [ by f_equiv | done ].
  Qed.
  Global Instance iMsg_car_ne n :
    Proper ((dist n) ==> (=) ==> (dist n) ==> (dist n)) (iMsg_car (Σ:=Σ) (V:=V)).
  Proof.
    intros m1 m2 meq v1 v2 veq p1 p2 peq. specialize (meq v1 p1). rewrite meq.
    f_equiv; [ by f_equiv | done ].
  Qed.

  Global Instance iMsg_contractive v n :
    Proper (dist n ==> dist_later n ==> dist n) (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_contractive. Qed.
  Global Instance iMsg_ne v : NonExpansive2 (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. rewrite iMsg_base_eq=> P1 P2 HP p1 p2 Hp w q /=. solve_proper. Qed.
  Global Instance iMsg_proper v :
    Proper ((≡) ==> (≡) ==> (≡)) (iMsg_base (Σ:=Σ) (V:=V) v).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance iMsg_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@iMsg_exist Σ V A).
  Proof. rewrite iMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.
  Global Instance iMsg_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@iMsg_exist Σ V A).
  Proof. rewrite iMsg_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.

  Global Instance msg_tele_base (v:V) (P : iProp Σ) (p : iProto Σ V) :
    MsgTele (TT:=TeleO) (MSG v {{ P }}; p) v P p.
  Proof. done. Qed.
  Global Instance msg_tele_exist {A} {TT : A → tele} (m : A → iMsg Σ V) tv tP tp :
  (∀ x, MsgTele (TT:=TT x) (m x) (tv x) (tP x) (tp x)) →
  MsgTele (TT:=TeleS TT) (∃ x, m x) tv tP tp.
  Proof. intros Hm. rewrite /MsgTele /=. f_equiv=> x. apply Hm. Qed.

  Global Instance iProto_message_ne a :
    NonExpansive (iProto_message (Σ:=Σ) (V:=V) a).
  Proof. rewrite iProto_message_eq. solve_proper. Qed.
  Global Instance iProto_message_proper a :
    Proper ((≡) ==> (≡)) (iProto_message (Σ:=Σ) (V:=V) a).
  Proof. apply (ne_proper _). Qed.

  Global Instance iProto_union_ne n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (iProto_union (Σ:=Σ) (V:=V)).
  Proof. rewrite iProto_union_eq. solve_proper. Qed.
  Global Instance iProto_union_proper n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (iProto_union (Σ:=Σ) (V:=V)).
  Proof. rewrite iProto_union_eq. solve_proper. Qed.

  Lemma iProto_message_equiv {TT1 TT2 : tele} a1 a2
        (m1 m2 : iMsg Σ V)
        (v1 : TT1 -t> V) (v2 : TT2 -t> V)
        (P1 : TT1 -t> iProp Σ) (P2 : TT2 -t> iProp Σ)
        (prot1 : TT1 -t> iProto Σ V) (prot2 : TT2 -t> iProto Σ V) :
    MsgTele m1 v1 P1 prot1 →
    MsgTele m2 v2 P2 prot2 →
    ⌜ a1 = a2 ⌝ -∗
    (■ ∀.. (xs1 : TT1), tele_app P1 xs1 -∗
       ∃.. (xs2 : TT2), ⌜tele_app v1 xs1 = tele_app v2 xs2⌝ ∗
                        ▷ (tele_app prot1 xs1 ≡ tele_app prot2 xs2) ∗
                        tele_app P2 xs2) -∗
    (■ ∀.. (xs2 : TT2), tele_app P2 xs2 -∗
       ∃.. (xs1 : TT1), ⌜tele_app v1 xs1 = tele_app v2 xs2⌝ ∗
                        ▷ (tele_app prot1 xs1 ≡ tele_app prot2 xs2) ∗
                        tele_app P1 xs1) -∗
      (<a1> m1) ≡ (<a2> m2).
  Proof.
    iIntros (Hm1 Hm2 Heq) "#Heq1 #Heq2".
    unfold MsgTele in Hm1. rewrite Hm1. clear Hm1.
    unfold MsgTele in Hm2. rewrite Hm2. clear Hm2.
    rewrite iProto_message_eq proto_message_equivI.
    iSplit; [ done | ].
    iIntros (v p').
    do 2 rewrite iMsg_texist_exist.
    rewrite iMsg_base_eq /=.
    iApply prop_ext.
    iIntros "!>". iSplit.
    - iDestruct 1 as (xs1 Hveq1) "[Hrec1 HP1]".
      iDestruct ("Heq1" with "HP1") as (xs2 Hveq2) "[Hrec2 HP2]".
      iExists xs2. rewrite -Hveq1 Hveq2.
      iSplitR; [ done | ]. iSplitR "HP2"; [ | done ].
      iRewrite -"Hrec1". iApply later_equivI. iIntros "!>". by iRewrite "Hrec2".
    - iDestruct 1 as (xs2 Hveq2) "[Hrec2 HP2]".
      iDestruct ("Heq2" with "HP2") as (xs1 Hveq1) "[Hrec1 HP1]".
      iExists xs1. rewrite -Hveq2 Hveq1.
      iSplitR; [ done | ]. iSplitR "HP1"; [ | done ].
      iRewrite -"Hrec2". iApply later_equivI. iIntros "!>". by iRewrite "Hrec1".
  Qed.

  (** Helpers *)
  Lemma iMsg_map_base f v P p :
    NonExpansive f →
    iMsg_map f (MSG v {{ P }}; p) ≡ (MSG v {{ P }}; f p)%msg.
  Proof.
    rewrite iMsg_base_eq. intros ? v' p'; simpl. iSplit.
    - iDestruct 1 as (p'') "[(->&Hp&$) Hp']". iSplit; [done|].
      iRewrite "Hp'". iIntros "!>". by iRewrite "Hp".
    - iIntros "(->&Hp'&$)". iExists p. iRewrite -"Hp'". auto.
  Qed.
  Lemma iMsg_map_exist {A} f (m : A → iMsg Σ V) :
    iMsg_map f (∃ x, m x) ≡ (∃ x, iMsg_map f (m x))%msg.
  Proof.
    rewrite iMsg_exist_eq. intros v' p'; simpl. iSplit.
    - iDestruct 1 as (p'') "[H Hp']". iDestruct "H" as (x) "H"; auto.
    - iDestruct 1 as (x p'') "[Hm Hp']". auto.
  Qed.

  (** ** Dual *)
  Global Instance iProto_dual_ne : NonExpansive (@iProto_dual Σ V).
  Proof. rewrite iProto_dual_eq. solve_proper. Qed.
  Global Instance iProto_dual_proper : Proper ((≡) ==> (≡)) (@iProto_dual Σ V).
  Proof. apply (ne_proper _). Qed.
  Global Instance iProto_dual_if_ne d : NonExpansive (@iProto_dual_if Σ V d).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_if_proper d :
    Proper ((≡) ==> (≡)) (@iProto_dual_if Σ V d).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_dual_end : iProto_dual (Σ:=Σ) (V:=V) END ≡ END.
  Proof.
    rewrite iProto_end_eq iProto_dual_eq /iProto_dual_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    by rewrite proto_elim_end.
  Qed.
  Lemma iProto_dual_message a m :
    iProto_dual (<a> m) ≡ <action_dual a> iMsg_dual m.
  Proof.
    rewrite iProto_message_eq iProto_dual_eq /iProto_dual_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    rewrite /iProto_message_def. rewrite ->proto_elim_message; [done|].
    intros p1 p2 Hp a' ? <- m1 m2 Hm. f_equiv; [|done]. f_equiv. solve_proper.
  Qed.

  Lemma iMsg_dual_base v P p :
    iMsg_dual (MSG v {{ P }}; p) ≡ (MSG v {{ P }}; iProto_dual p)%msg.
  Proof. apply iMsg_map_base, _. Qed.
  Lemma iMsg_dual_exist {A} (m : A → iMsg Σ V) :
    iMsg_dual (∃ x, m x) ≡ (∃ x, iMsg_dual (m x))%msg.
  Proof. apply iMsg_map_exist. Qed.

  (** ** Append *)
  Global Instance iProto_app_end_l : LeftId (≡) END (@iProto_app Σ V).
  Proof.
    intros p. rewrite iProto_end_eq iProto_app_eq /iProto_app_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|]; simpl.
    by rewrite proto_elim_end.
  Qed.
  Lemma iProto_app_message a m p : (<a> m) <++> p ≡ <a> m <++> p.
  Proof.
    rewrite iProto_message_eq iProto_app_eq /iProto_app_def /iProto_map_app.
    etrans; [apply (fixpoint_unfold (iProto_map_app_aux _ _))|].
    rewrite /iProto_message_def. simpl.
    rewrite ->proto_elim_message; [done|].
    intros p1 p2 Hp a1 a2 Ha m1 m2 Hm. f_equiv; [|solve_proper].
    f_equiv; [done|]. solve_proper.
  Qed.

End proto.

Global Instance iProto_inhabited {Σ V} : Inhabited (iProto Σ V) := populate END.

Definition iProto_lookup {Σ V} (p:iProto Σ V) (i:nat) : iProto Σ V :=
  match (p !! i) with
  | None => END%proto
  | Some am => [am]
  end.

Global Instance iProto_lookup_ne {Σ V} n :
  Proper ((dist n) ==> (=) ==> (dist n)) (iProto_lookup (Σ:=Σ) (V:=V)).
Proof.
  intros p1 p2 Hp i1 i2 ->. rewrite /iProto_lookup.
  rewrite list_dist_Forall2 in Hp.
  rewrite Forall2_lookup in Hp.
  specialize (Hp i2).
  destruct (p1 !! i2) eqn:Heqn1; destruct (p2 !! i2) eqn:Heqn2; rewrite Heqn1 Heqn2 in Hp.
  - inversion Hp. inversion H1. simpl in *. inversion H2. simplify_eq.
    f_equiv. solve_proper.
  - by inversion Hp.
  - by inversion Hp.
  - done.
Qed.

Global Instance iProto_lookup_proper {Σ V} :
  Proper ((≡) ==> (=) ==> (≡)) (iProto_lookup (Σ:=Σ) (V:=V)).
Proof.
  intros p1 p2 Hp i1 i2 ->. rewrite /iProto_lookup.
  rewrite list_equiv_Forall2 in Hp.
  rewrite Forall2_lookup in Hp.
  specialize (Hp i2).
  destruct (p1 !! i2) eqn:Heqn1; destruct (p2 !! i2) eqn:Heqn2; rewrite Heqn1 Heqn2 in Hp.
  - inversion Hp. inversion H1. simpl in *. inversion H2. simplify_eq.
    f_equiv. solve_proper.
  - by inversion Hp.
  - by inversion Hp.
  - done.
Qed.

Definition iProto_elem_of {Σ V} (p1 p2 :iProto Σ V) : iProp Σ :=
  ∃ i, iProto_lookup p2 i ≡ p1.

Global Instance iProto_elem_of_ne {Σ V} n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (iProto_elem_of (Σ:=Σ) (V:=V)).
Proof. solve_proper. Qed.

Global Instance iProto_elem_of_proper {Σ V} :
  Proper ((≡) ==> (≡) ==> (≡)) (iProto_elem_of (Σ:=Σ) (V:=V)).
Proof. solve_proper. Qed.

Definition can_step {Σ V} (rec : list (iProto Σ V) → iProp Σ)
  (ps : list (iProto Σ V)) : iProp Σ :=
  ∀ i j (m1 m2 : iMsg Σ V),
    ⌜i ≠ j⌝ -∗
    iProto_elem_of (<![j]> m1) (ps !!! i) -∗
    iProto_elem_of (<?[i]> m2) (ps !!! j) -∗
    ∀ v p1, (iMsg_car m1 v (Next p1)) -∗
            ∃ p2, iMsg_car m2 v (Next p2) ∗
                  ▷ (rec (<[i:=p1]>(<[j:=p2]>ps))).

Definition valid_target {Σ V} (ps : list (iProto Σ V)) : iProp Σ :=
  ∀ i j a m, iProto_elem_of (<(a, j)> m) (ps !!! i) -∗ ⌜is_Some (ps !! j)⌝.

Global Instance valid_target_ne {Σ V} n :
  Proper ((dist n) ==> (dist n)) (valid_target (Σ:=Σ) (V:=V)).
Proof. rewrite /valid_target. intros ps1 ps2 Hs. repeat f_equiv; by rewrite Hs. Qed.

Global Instance valid_target_proper {Σ V} :
  Proper ((≡) ==> (≡)) (valid_target (Σ:=Σ) (V:=V)).
Proof. rewrite /valid_target. intros ps1 ps2 Hs. repeat f_equiv; by rewrite Hs.
       Unshelve. apply 0.
Qed.

Definition iProto_consistent_pre {Σ V} (rec : list (iProto Σ V) → iProp Σ)
  (ps : list (iProto Σ V)) : iProp Σ :=
  valid_target ps ∧ can_step rec ps.

Global Instance iProto_consistent_pre_ne {Σ V}
       (rec : listO (iProto Σ V) -n> iPropO Σ) :
  NonExpansive (iProto_consistent_pre rec).
Proof.
  intros n p1 p2 Hp.
  rewrite /iProto_consistent_pre /can_step. simpl. solve_proper.
Qed.

Program Definition iProto_consistent_pre' {Σ V}
  (rec : listO (iProto Σ V) -n> iPropO Σ) :
  listO (iProto Σ V) -n> iPropO Σ :=
  λne ps, iProto_consistent_pre (λ ps, rec ps) ps.

Local Instance iProto_consistent_pre_contractive {Σ V} : Contractive (@iProto_consistent_pre' Σ V).
Proof.
  rewrite /iProto_consistent_pre' /iProto_consistent_pre /can_step.
  solve_contractive.
Qed.

Definition iProto_consistent {Σ V} (ps : list (iProto Σ V)) : iProp Σ :=
  fixpoint iProto_consistent_pre' ps.

Arguments iProto_consistent {_ _} _%_proto.
Global Instance: Params (@iProto_consistent) 1 := {}.

Global Instance iProto_consistent_ne {Σ V} : NonExpansive (@iProto_consistent Σ V).
Proof. solve_proper. Qed.
Global Instance iProto_consistent_proper {Σ V} : Proper ((≡) ==> (⊣⊢)) (@iProto_consistent Σ V).
Proof. solve_proper. Qed.

Lemma iProto_consistent_unfold {Σ V} (ps : list (iProto Σ V)) :
  iProto_consistent ps ≡ (iProto_consistent_pre iProto_consistent) ps.
Proof.
  apply: (fixpoint_unfold iProto_consistent_pre').
Qed.

Lemma iProto_lookup_is_Some' {Σ V} (p : list $ iProto Σ V) i i' a j (m:iMsg Σ V) :
     (iProto_lookup (p !!! i) i' ≡ (<(a,j)> m)) ⊢@{iProp Σ} ⌜is_Some (p !! i)⌝.
Proof.
  rewrite list_lookup_total_alt. destruct (p !! i); simpl; [by eauto|].
  by rewrite iProto_end_eq iProto_end_message_equivI; eauto.
Qed.

(** * Protocol entailment *)
Definition iProto_le_pre {Σ V}
  (rec : iProto Σ V → iProto Σ V → iProp Σ) (p1 p2 : iProto Σ V) : iProp Σ :=
  (∀ j a m2,
     iProto_elem_of (<(a,j)>m2) p2 -∗
     ∃ m1,
       iProto_elem_of (<(a,j)>m1) p1 ∗
       match a with
       | Send => (∀ v p2', iMsg_car m2 v (Next p2') -∗
                           ∃ p1', ▷ rec p1' p2' ∗ iMsg_car m1 v (Next p1'))
       | Recv => (∀ v p1', iMsg_car m1 v (Next p1') -∗
                           ∃ p2', ▷ rec p1' p2' ∗ iMsg_car m2 v (Next p2'))
       end).
Global Instance iProto_le_pre_ne {Σ V} (rec : iProto Σ V → iProto Σ V → iProp Σ) :
  NonExpansive2 (iProto_le_pre rec).
Proof. solve_proper. Qed.

Program Definition iProto_le_pre' {Σ V}
    (rec : iProto Σ V -n> iProto Σ V -n> iPropO Σ) :
    iProto Σ V -n> iProto Σ V -n> iPropO Σ := λne p1 p2,
  iProto_le_pre (λ p1' p2', rec p1' p2') p1 p2.
Solve Obligations with solve_proper.
Local Instance iProto_le_pre_contractive {Σ V} : Contractive (@iProto_le_pre' Σ V).
Proof.
  intros n rec1 rec2 Hrec p1 p2. rewrite /iProto_le_pre' /iProto_le_pre /=.
  by repeat (f_contractive || f_equiv).
Qed.
Definition iProto_le {Σ V} (p1 p2 : iProto Σ V) : iProp Σ :=
  fixpoint iProto_le_pre' p1 p2.
Arguments iProto_le {_ _} _%_proto _%_proto.
Global Instance: Params (@iProto_le) 2 := {}.
Notation "p ⊑ q" := (iProto_le p q) : bi_scope.

Global Instance iProto_le_ne {Σ V} : NonExpansive2 (@iProto_le Σ V).
Proof. solve_proper. Qed.
Global Instance iProto_le_proper {Σ V} : Proper ((≡) ==> (≡) ==> (⊣⊢)) (@iProto_le Σ V).
Proof. solve_proper. Qed.

Record proto_name := ProtName { proto_names : gmap nat gname }.
Global Instance proto_name_inhabited : Inhabited proto_name :=
  populate (ProtName inhabitant).
Global Instance proto_name_eq_dec : EqDecision proto_name.
Proof. solve_decision. Qed.
Global Instance proto_name_countable : Countable proto_name.
Proof.
 refine (inj_countable (λ '(ProtName γs), (γs))
   (λ '(γs), Some (ProtName γs)) _); by intros [].
Qed.

Definition iProto_own_frag `{!protoG Σ V} (γ : gname)
    (i : nat) (p : iProto Σ V) : iProp Σ :=
  own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p))).

Definition iProto_own_auth `{!protoG Σ V} (γ : gname)
    (ps : list (iProto Σ V)) : iProp Σ :=
  own γ (gmap_view_auth (DfracOwn 1) ((λ p, Excl' (Next p)) <$> map_seq 0 ps)).

Definition iProto_ctx `{protoG Σ V}
    (γ : gname) (ps_len : nat) : iProp Σ :=
  ∃ ps, ⌜length ps = ps_len⌝ ∗ iProto_own_auth γ ps ∗ ▷ iProto_consistent ps.

(** * The connective for ownership of channel ends *)
Definition iProto_own `{!protoG Σ V}
    (γ : gname) (i : nat) (p : iProto Σ V) : iProp Σ :=
  ∃ p', ▷ (p' ⊑ p) ∗ iProto_own_frag γ i p'.
Arguments iProto_own {_ _ _} _ _ _%_proto.
Global Instance: Params (@iProto_own) 3 := {}.

Global Instance iProto_own_frag_contractive `{protoG Σ V} γ i :
  Contractive (iProto_own_frag γ i).
Proof. solve_contractive. Qed.

Global Instance iProto_own_contractive `{protoG Σ V} γ i :
  Contractive (iProto_own γ i).
Proof. solve_contractive. Qed.
Global Instance iProto_own_ne `{protoG Σ V} γ s : NonExpansive (iProto_own γ s).
Proof. solve_proper. Qed.
Global Instance iProto_own_proper `{protoG Σ V} γ s :
  Proper ((≡) ==> (≡)) (iProto_own γ s).
Proof. apply (ne_proper _). Qed.

Lemma iMsg_equivI {Σ V} (m1 m2 : iMsg Σ V) :
  m1 ≡ m2 ⊣⊢@{iProp Σ} (∀ v lp, iMsg_car m1 v lp ≡ iMsg_car m2 v lp).
Proof.
  trans ((iMsg_car m1 ≡@{V -d> laterO (iProto Σ V) -n> iProp Σ} iMsg_car m2) : iProp Σ)%I.
  - apply (anti_symm _).
    + by apply (f_equivI )=> n [m1'] [m2'] Hm.
    + destruct m1, m2; simpl. apply f_equivI. solve_proper.
  - rewrite discrete_fun_equivI. do 2 f_equiv. by rewrite ofe_morO_equivI.
Qed.

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types v : V.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  Lemma own_prot_idx γ i j (p1 p2 : iProto Σ V) :
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p1))) -∗
    own γ (gmap_view_frag j (DfracOwn 1) (Excl' (Next p2))) -∗
    ⌜i ≠ j⌝.
  Proof.
    iIntros "Hown Hown'" (->).
    iDestruct (own_valid_2 with "Hown Hown'") as "H".
    rewrite internal_cmra_valid_elim.
    by iDestruct "H" as %[]%gmap_view_frag_op_validN.
  Qed.

  Lemma own_prot_excl γ i (p1 p2 : iProto Σ V) :
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p1))) -∗
    own γ (gmap_view_frag i (DfracOwn 1) (Excl' (Next p2))) -∗
    False.
  Proof. iIntros "Hi Hj". by iDestruct (own_prot_idx with "Hi Hj") as %?. Qed.

  Lemma later_map_proto_fold_unfold (lp : laterO $ iProto Σ V) :
    (later_map proto_fold (later_map proto_unfold lp)) ≡ lp.
  Proof. destruct lp. by rewrite later_map_Next /= proto_fold_unfold. Qed.

  Lemma iProto_lookup_end i : iProto_lookup (END:iProto Σ V) i ≡ END.
  Proof. rewrite !iProto_end_eq /iProto_lookup. simpl. rewrite iProto_end_eq. done. Qed.
  Lemma iProto_lookup_message_inv i (a a' : action) (m m':iMsg Σ V) :
    (iProto_lookup (<a> m) i ≡ (<a'> m')) ⊢@{iProp Σ}
    ⌜i = 0⌝ ∧ ⌜a = a'⌝ ∧ m ≡ m'.
  Proof.
    rewrite /iProto_lookup iProto_message_eq /iProto_message_def /proto_message /=.
    rewrite iProto_end_eq /iProto_end_def /proto_end.
    destruct i; rewrite /=.
    - iIntros "H". rewrite list_equivI.
      iSpecialize ("H" $! 0). simpl. rewrite option_equivI.
      rewrite prod_equivI. simpl. iDestruct "H" as (<-) "H".
      iSplit; [done|].
      iSplit; [done|].
      rewrite iMsg_equivI.
      iIntros (v lp). rewrite discrete_fun_equivI.
      iSpecialize ("H" $! v).
      rewrite ofe_morO_equivI.
      iSpecialize ("H" $! (later_map proto_unfold lp)).
      simpl. rewrite !later_map_proto_fold_unfold.
      done.
    - iIntros "H". rewrite list_equivI. iSpecialize ("H" $! 0). simpl.
      by rewrite option_equivI.
  Qed.
  Lemma iProto_lookup_inv p i (a : action) (m:iMsg Σ V) :
    (iProto_lookup p i ≡ (<a> m)) ⊢@{iProp Σ} ⌜i < length p⌝.
  Proof.
    rewrite /iProto_lookup iProto_message_eq /iProto_message_def /proto_message /=.
    rewrite iProto_end_eq /iProto_end_def /proto_end.
    destruct (p !! i) eqn:Heqn.
    - apply lookup_lt_Some in Heqn. eauto.
    - iIntros "H". rewrite list_equivI. iSpecialize ("H" $! 0). simpl.
      by rewrite option_equivI.
  Qed.

  Lemma iProto_lookup_perm i p1 p2 a (m:iMsg Σ V) :
    p1 ≡ₚ p2 →
    (iProto_lookup p1 i ≡ (<a> m)) ⊢@{iProp Σ}
    ∃ j, iProto_lookup p2 j ≡ (<a> m).
  Proof.
    iIntros (Hperm) "Heq".
    rewrite /iProto_lookup.
    destruct (p1 !! i) as [p|] eqn:Heqn.
    - assert (p ∈ p1) as Hin.
      { by eapply list_elem_of_lookup_2. }
      rewrite Hperm in Hin.
      apply list_elem_of_lookup_1 in Hin as [j Hin].
      iExists j. rewrite Hin. done.
    - by rewrite iProto_end_message_equivI.
  Qed.

  Lemma iProto_lookup_message (a : action) (m :iMsg Σ V) :
    (iProto_lookup (<a> m) 0 ≡ (<a> m)).
  Proof.
    rewrite /iProto_lookup.
    rewrite iProto_message_eq /iProto_message_def /proto_message.
    simpl. done.
  Qed.

  Lemma iProto_lookup_union_l p1 p2 i :
    i < length p1 → (iProto_lookup (p1 <+> p2) i ≡ iProto_lookup p1 i).
  Proof.
    iIntros (Hlen).
    by rewrite /iProto_lookup iProto_union_eq /iProto_union_def /proto_union lookup_app_l.
  Qed.

  Lemma iProto_lookup_union_r p1 p2 i :
    length p1 ≤ i → (iProto_lookup (p1 <+> p2) i ≡ iProto_lookup p2 (i - length p1)).
  Proof.
    intros Hlen.
    by rewrite /iProto_lookup iProto_union_eq /iProto_union_def /proto_union lookup_app_r.
  Qed.

  Lemma iProto_lookup_union_l_weak (a : action) (m :iMsg Σ V) p :
    (iProto_lookup ((<a> m) <+> p) 0 ≡ <a> m).
  Proof.
    rewrite iProto_lookup_union_l.
    - by rewrite iProto_lookup_message.
    - rewrite iProto_message_eq /=. lia.
  Qed.

  Lemma iProto_lookup_union_r_weak (a : action) (m :iMsg Σ V) p i :
    (iProto_lookup ((<a> m) <+> p) (S i) ≡ iProto_lookup p i).
  Proof.
    rewrite iProto_message_eq /= iProto_lookup_union_r /=; [by rewrite right_id|lia].
  Qed.

  Lemma iProto_elem_of_message_inv (a a' : action) (m m':iMsg Σ V) :
    (iProto_elem_of (<a'> m') (<a> m)) ⊢@{iProp Σ} ⌜a = a'⌝ ∧ m ≡ m'.
  Proof.
    rewrite /iProto_elem_of. iDestruct 1 as (i) "H".
    iDestruct (iProto_lookup_message_inv with "H") as (??) "H". naive_solver.
  Qed.

  Lemma iProto_elem_of_message (a : action) (m :iMsg Σ V) :
    ⊢ iProto_elem_of (<a> m) (<a> m).
  Proof. rewrite /iProto_elem_of. iExists 0. by rewrite iProto_lookup_message. Qed.

  Lemma iProto_elem_of_union_l (a : action) (m :iMsg Σ V) p1 p2 :
    iProto_elem_of (<a> m) (p1) ⊢
    iProto_elem_of (<a> m) (p1 <+> p2).
  Proof.
    rewrite /iProto_elem_of.
    iDestruct 1 as (i) "H".
    iAssert (⌜i < length p1⌝)%I with "[H]" as %Hle.
    { by iApply iProto_lookup_inv. }
    iExists i. by rewrite iProto_lookup_union_l.
  Qed.

  Lemma iProto_elem_of_union_r (a : action) (m :iMsg Σ V) p1 p2 :
    iProto_elem_of (<a> m) (p2) ⊢
    iProto_elem_of (<a> m) (p1 <+> p2).
  Proof.
    rewrite /iProto_elem_of.
    iDestruct 1 as (i) "H".
    iExists (length p1 + i).
    rewrite iProto_lookup_union_r; [|lia].
    by rewrite Nat.add_sub'.
  Qed.

  Lemma iProto_elem_of_union_inv (a : action) (m :iMsg Σ V) p1 p2 :
    iProto_elem_of (<a> m) (p1 <+> p2) ⊢
    iProto_elem_of (<a> m) p1 ∨ iProto_elem_of (<a> m) p2.
  Proof.
    rewrite /iProto_elem_of.
    iDestruct 1 as (i) "H".
    destruct (decide (i < length p1)) as [Hlen|Hlen].
    + rewrite iProto_lookup_union_l; [|done].
      iLeft. by iExists _.
    + rewrite iProto_lookup_union_r; [|lia].
      iRight. by iExists _.
  Qed.

  Lemma iProto_elem_of_perm p1 p2 a (m:iMsg Σ V) :
    p1 ≡ₚ p2 →
    iProto_elem_of (<a> m) p1 ⊢@{iProp Σ}
    iProto_elem_of (<a> m) p2.
  Proof.
    iIntros (Hperm) "Heq".
    rewrite /iProto_elem_of.
    iDestruct "Heq" as (i) "Heq".
    by iApply iProto_lookup_perm.
  Qed.

  Lemma iProto_elem_of_end_inv_r p : iProto_elem_of p (END:iProto Σ V) ⊢ p ≡ END.
  Proof. iDestruct 1 as (i) "H". rewrite iProto_lookup_end. by iRewrite "H". Qed.

  (** ** Protocol entailment **)
  Lemma iProto_le_unfold p1 p2 : iProto_le p1 p2 ≡ iProto_le_pre iProto_le p1 p2.
  Proof. apply: (fixpoint_unfold iProto_le_pre'). Qed.

  Lemma iProto_le_refl p : ⊢ p ⊑ p.
  Proof.
    iLöb as "IH" forall (p).
    iEval (rewrite iProto_le_unfold /iProto_le_pre).
    iIntros (j [] m2) "Hi".
    - iExists m2.
      iSplit; [done|].
      iIntros (v p2') "Hm2". iExists _. iFrame. iNext. iApply "IH".
    - iExists m2.
      iSplit; [done|].
      iIntros (v p2') "Hm2". iExists _. iFrame. iNext. iApply "IH".
  Qed.

  Lemma iProto_le_end : ⊢ END ⊑ (END : iProto Σ V).
  Proof. iApply iProto_le_refl. Qed.

  Lemma iProto_le_send i m1 m2 :
    (∀ v p2', iMsg_car m2 v (Next p2') -∗ ∃ p1',
      ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1')) -∗
    (<![i]> m1) ⊑ (<![i]> m2).
  Proof.
    iIntros "Hle". rewrite iProto_le_unfold.
    iIntros (j [] m2') "Hi".
    - rewrite iProto_elem_of_message_inv.
      iDestruct "Hi" as (Hj) "#Hi".
      simplify_eq.
      iExists _.
      iSplitR; [by iApply iProto_elem_of_message|].
      iIntros (v p2') "Hm". simpl.
      rewrite iMsg_equivI. iSpecialize ("Hi" $!v (Next p2')).
      simpl. iRewrite -"Hi" in "Hm".
      iDestruct ("Hle" with "Hm") as (p1') "[Hle Hm1]".
      iExists p1'. simpl. iFrame.
    - rewrite iProto_elem_of_message_inv.
      by iDestruct "Hi" as (Hj) "#Hi".
  Qed.

  Lemma iProto_le_recv i m1 m2 :
    (∀ v p1', iMsg_car m1 v (Next p1') -∗ ∃ p2',
      ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2')) -∗
    (<?[i]> m1) ⊑ (<?[i]> m2).
  Proof.
    iIntros "Hle". rewrite iProto_le_unfold.
    iIntros (j [] m2') "Hi".
    - rewrite iProto_elem_of_message_inv.
      by iDestruct "Hi" as (Hj) "#Hi".
    - rewrite iProto_elem_of_message_inv.
      iDestruct "Hi" as (Hj) "#Hi".
      iExists _. simplify_eq.
      iSplit; [by iApply iProto_elem_of_message|].
      iIntros (v p2') "Hm". simpl.
      iDestruct ("Hle" with "Hm") as (p1') "[Hle Hm1]".
      rewrite iMsg_equivI. iSpecialize ("Hi" $!v (Next p1')).
      iExists p1'. simpl.
      iFrame.
      iRewrite -"Hi".
      iApply "Hm1".
  Qed.

  Lemma iProto_le_union_message i a m p :
    ⊢ iProto_union (<(a,i)> m) p ⊑ p.
  Proof.
    rewrite iProto_le_unfold.
    iIntros (j [] m2) "Hi".
    - iExists m2.
      iSplit.
      { by iApply iProto_elem_of_union_r. }
      iIntros (v p2') "H". iExists _. iFrame. iApply iProto_le_refl.
    - iExists m2.
      rewrite iProto_elem_of_union_r.
      iSplit; [done|].
      iIntros (v p2') "H". iExists _. iFrame. iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_perm p1 p2 :
    p1 ≡ₚ p2 → ⊢ p1 ⊑ p2.
  Proof.
    rewrite iProto_le_unfold.
    iIntros (Hperm j [] m2) "Hi".
    - rewrite iProto_elem_of_perm; [|done].
      iExists m2.
      iSplit; [done|].
      iIntros (??) "$". iApply iProto_le_refl.
    - rewrite iProto_elem_of_perm; [|done].
      iExists m2.
      iSplit; [done|].
      iIntros (??) "$". iApply iProto_le_refl.
  Qed.

  Lemma list_lookup_Some_le (ps : list $ iProto Σ V) (i : nat) (p1 : iProto Σ V) :
    ⊢@{iProp Σ} ps !! i ≡ Some p1 -∗ ⌜i < length ps⌝.
  Proof.
    iIntros "HSome".
    rewrite option_equivI.
    destruct (ps !! i) eqn:Heqn; [|done].
    iPureIntro.
    by apply lookup_lt_is_Some_1.
  Qed.

  Lemma iProto_le_union_l p1 p2 p3 :
    p1 ⊑ p2 -∗ iProto_union p1 p3 ⊑ iProto_union p2 p3.
  Proof.
    rewrite !iProto_le_unfold.
    iIntros "Hle".
    iIntros (j a m) "#Hi".
    iDestruct (iProto_elem_of_union_inv with "Hi") as "[Hi'|Hi']".
    - iDestruct ("Hle" with "Hi'") as (m1) "[#Hi'' Hm1]".
      iExists m1. iFrame. by iApply iProto_elem_of_union_l.
    - iExists m. iSplit; [by iApply iProto_elem_of_union_r|].
      destruct a.
      * iIntros (v p2') "Hm". iExists _. iFrame. iApply iProto_le_refl.
      * iIntros (v p2') "Hm". iExists _. iFrame. iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_union_r p1 p2 p3 :
    p2 ⊑ p3 -∗ iProto_union p1 p2 ⊑ iProto_union p1 p3.
  Proof.
    rewrite !iProto_le_unfold.
    iIntros "Hle".
    iIntros (j a m) "#Hi".
    iDestruct (iProto_elem_of_union_inv with "Hi") as "[Hi'|Hi']".
    - iExists m. iSplit; [by iApply iProto_elem_of_union_l|].
      destruct a.
      * iIntros (v p2') "Hm". iExists _. iFrame. iApply iProto_le_refl.
      * iIntros (v p2') "Hm". iExists _. iFrame. iApply iProto_le_refl.
    - iDestruct ("Hle" with "Hi'") as (m1) "[#Hi'' Hm1]".
      iExists m1. iFrame. by iApply iProto_elem_of_union_r.
  Qed.

  Lemma iProto_le_union_l_l p1 p2 :
    ⊢ iProto_union p1 p2 ⊑ p1.
  Proof.
    rewrite iProto_le_unfold. iIntros (j a m) "Hi". iExists m.
    iSplit; [by iApply iProto_elem_of_union_l|].
    destruct a; iIntros (v p') "H"; iExists _; iFrame; iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_union_r_r p1 p2 :
    ⊢ iProto_union p1 p2 ⊑ p2.
  Proof.
    rewrite iProto_le_unfold. iIntros (j a m) "Hi". iExists m.
    iSplit; [by iApply iProto_elem_of_union_r|].
    destruct a; iIntros (v p') "H"; iExists _; iFrame; iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_trans p1 p2 p3 :
    p1 ⊑ p2 -∗ p2 ⊑ p3 -∗ p1 ⊑ p3.
  Proof.
    iLöb as "IH" forall (p1 p2 p3).
    iEval (rewrite !iProto_le_unfold /iProto_le_pre).
    iIntros "Hle1 Hle2".
    iIntros (j a m2) "Hi".
    iDestruct ("Hle2" with "Hi") as (m') "[Hi' Hle]".
    iDestruct ("Hle1" with "Hi'") as (m'') "[Hi'' Hle']".
    iExists _. iFrame.
    destruct a.
    - iIntros (v p2') "Hm".
      iDestruct ("Hle" with "Hm") as (p1') "[Hle Hm]".
      iDestruct ("Hle'" with "Hm") as (p2'') "[Hle' Hm]".
      iExists _. iFrame. iNext. iApply ("IH" with "Hle' Hle").
    - iIntros (v p2') "Hm".
      iDestruct ("Hle'" with "Hm") as (p1') "[Hle' Hm]".
      iDestruct ("Hle" with "Hm") as (p2'') "[Hle Hm]".
      iExists _. iFrame. iNext. iApply ("IH" with "Hle' Hle").
  Qed.

  Lemma iProto_le_end_inv_l p : END ⊑ p -∗ (p ≡ END).
  Proof.
    rewrite iProto_le_unfold.
    iIntros "H".
    destruct (iProto_case p).
    { done. }
    destruct H as (t&n&m&p'&Hp).
    iSpecialize ("H" $! n t m).
    iDestruct ("H" with "[]") as (m1') "[Heq _]".
    {  rewrite Hp. iApply iProto_elem_of_union_l. iApply iProto_elem_of_message. }
    by rewrite iProto_elem_of_end_inv_r iProto_message_end_equivI.
  Qed.

  Lemma iProto_le_send_inv i p1 m2 :
    p1 ⊑ (<![i]> m2) -∗ ∃ m1,
      (iProto_elem_of (<![i]> m1) p1) ∗
        ∀ v p2', iMsg_car m2 v (Next p2') -∗
               ∃ p1', ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1').
  Proof.
    iIntros "Hle".
    rewrite iProto_le_unfold.
    iDestruct ("Hle" with "[]") as "Hle".
    { iApply iProto_elem_of_message. }
    iDestruct "Hle" as (m1) "[H Hle]".
    iExists m1. iFrame.
  Qed.

  Lemma iProto_le_send_send_inv i m1 m2 v p2' :
    (<![i]> m1) ⊑ (<![i]> m2) -∗
    iMsg_car m2 v (Next p2') -∗ ∃ p1', ▷ (p1' ⊑ p2') ∗ iMsg_car m1 v (Next p1').
  Proof.
    iIntros "H Hm2". iDestruct (iProto_le_send_inv with "H") as (m1') "[Hm1 H]".
    iDestruct (iProto_elem_of_message_inv with "Hm1") as (_) "Hm1".
    iDestruct ("H" with "Hm2") as (p1') "[Hle Hm]".
    rewrite iMsg_equivI. iRewrite -("Hm1" $! v (Next p1')) in "Hm". auto with iFrame.
  Qed.

  Lemma iProto_le_recv_inv_r i p1 m2 :
    (p1 ⊑ <?[i]> m2) -∗ ∃ m1,
      (iProto_elem_of (<?[i]> m1) p1) ∗
      ∀ v p1', iMsg_car m1 v (Next p1') -∗
               ∃ p2', ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2').
  Proof.
    iIntros "Hle".
    rewrite iProto_le_unfold.
    iDestruct ("Hle" with "[]") as "Hle".
    { by iApply iProto_elem_of_message. }
    iDestruct "Hle" as (m1) "[H Hle]".
    iExists m1. iFrame.
  Qed.

  Lemma iProto_le_recv_recv_inv i m1 m2 v p1' :
    (<(Recv, i)> m1) ⊑ (<(Recv, i)> m2) -∗
    iMsg_car m1 v (Next p1') -∗ ∃ p2', ▷ (p1' ⊑ p2') ∗ iMsg_car m2 v (Next p2').
  Proof.
    iIntros "H Hm2". iDestruct (iProto_le_recv_inv_r with "H") as (m1') "[Hm1 H]".
    iApply "H". iDestruct (iProto_elem_of_message_inv with "Hm1") as (_) "Hm1".
    rewrite iMsg_equivI. by iRewrite -("Hm1" $! v (Next p1')).
  Qed.

  Lemma iProto_le_msg_inv_r j a p1 m2 :
    (p1 ⊑ <(a,j)> m2) -∗ ∃ m1, iProto_elem_of (<(a,j)> m1) p1.
  Proof.
    destruct a.
    - iIntros "Hle". iDestruct (iProto_le_send_inv with "Hle") as (m') "[H _]".
      iExists m'. iFrame.
    - iIntros "Hle". iDestruct (iProto_le_recv_inv_r with "Hle") as (m') "[H _]".
      iExists m'. iFrame.
  Qed.

  Lemma iProto_le_base a v P p1 p2 :
    ▷ (p1 ⊑ p2) -∗
    (<a> MSG v {{ P }}; p1) ⊑ (<a> MSG v {{ P }}; p2).
  Proof.
    rewrite iMsg_base_eq. iIntros "H". destruct a as [[]].
    - iApply iProto_le_send. iIntros (v' p') "(->&Hp&$)".
      iExists p1. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
    - iApply iProto_le_recv. iIntros (v' p') "(->&Hp&$)".
      iExists p2. iSplit; [|by auto]. iIntros "!>". by iRewrite -"Hp".
  Qed.

  Global Instance iProto_own_frag_ne γ s : NonExpansive (iProto_own_frag γ s).
  Proof. solve_proper. Qed.

  Lemma iProto_own_auth_agree γ ps i p :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p -∗ ▷ (ps !! i ≡ Some p).
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "H✓".
    rewrite gmap_view_both_validI.
    iDestruct "H✓" as "[_ [H1 H2]]".
    rewrite lookup_fmap.
    simpl.
    rewrite lookup_map_seq_0.
    destruct (ps !! i) eqn:Heqn; last first.
    { rewrite Heqn. rewrite !option_equivI. done. }
    rewrite Heqn.
    simpl. rewrite !option_equivI excl_equivI. by iNext.
  Qed.

  Lemma iProto_own_auth_agree_Some γ ps i p :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p -∗ ⌜is_Some (ps !! i)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "H✓".
    rewrite gmap_view_both_validI.
    iDestruct "H✓" as "[_ [H1 H2]]".
    rewrite lookup_fmap.
    simpl.
    rewrite lookup_map_seq_0.
    destruct (ps !! i) eqn:Heqn; last first.
    { rewrite Heqn. rewrite !option_equivI. done. }
    rewrite Heqn.
    simpl. rewrite !option_equivI excl_equivI. done.
  Qed.

  Lemma iProto_own_auth_update γ ps i p p' :
    iProto_own_auth γ ps -∗ iProto_own_frag γ i p ==∗
    iProto_own_auth γ (<[i := p']>ps) ∗ iProto_own_frag γ i p'.
  Proof.
    iIntros "H● H◯".
    iDestruct (iProto_own_auth_agree_Some with "H● H◯") as %HSome.
    iMod (own_update_2 with "H● H◯") as "[H1 H2]"; [|iModIntro].
    { eapply (gmap_view_replace _ _ _ (Excl' (Next p'))). done. }
    iFrame. rewrite -fmap_insert.
    rewrite /iProto_own_auth.
    rewrite insert_map_seq_0; [done|].
    by apply lookup_lt_is_Some_1.
  Qed.

  Lemma iProto_own_auth_alloc ps :
    ⊢ |==> ∃ γ, iProto_own_auth γ ps ∗ [∗ list] i ↦p ∈ ps, iProto_own γ i p.
  Proof.
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "Hauth".
    { apply gmap_view_auth_valid. }
    iExists γ.
    iInduction ps as [|p ps] "IH" using rev_ind.
    { iModIntro. iFrame. done. }
    iMod ("IH" with "Hauth") as "[Hauth Hfrags]".
    iFrame "Hfrags".
    iMod (own_update with "Hauth") as "[Hauth Hfrag]".
    { apply (gmap_view_alloc _ (length ps) (DfracOwn 1) (Excl' (Next p))); [|done|done].
      rewrite fmap_map_seq.
      rewrite lookup_map_seq_0.
      apply lookup_ge_None_2. rewrite length_fmap. done. }
    simpl.
    iModIntro.
    rewrite right_id_L.
    rewrite -fmap_insert. iFrame.
    rewrite /iProto_own_auth.
    rewrite map_seq_snoc. simpl. iFrame. iApply iProto_le_refl.
  Qed.

  Lemma valid_target_le ps i p1 p2 :
    valid_target ps -∗
    ps !! i ≡ Some p1 -∗
    p1 ⊑ p2 -∗
    valid_target (<[i := p2]>ps).
  Proof.
    iIntros "Htar Hps Hle".
    rename i into k.
    iAssert (⌜k < length ps⌝)%I as %Hlen.
    { rewrite option_equivI. destruct (ps !!k) eqn:Heqn; [|done].
      iPureIntro. by apply lookup_lt_is_Some_1. }
    iIntros (i j t m) "Hi".
    destruct (decide (j=k)) as [->|Hneq1].
    { by rewrite list_lookup_insert_eq.  }
    rewrite (list_lookup_insert_ne _ k j); [|done].
    destruct (decide (i=k)) as [->|Hneq2].
    { rewrite list_lookup_total_insert_eq; [|done].
      rewrite iProto_le_unfold.
      iDestruct ("Hle" with "Hi") as (m') "[Hi'' _]".
      iApply ("Htar" $! k).
      rewrite list_lookup_total_alt. iRewrite "Hps". simpl. done. }
    rewrite (list_lookup_total_insert_ne _ k i); [|done].
    by iApply "Htar".
  Qed.

  Lemma iProto_consistent_le ps i p1 p2 :
    iProto_consistent ps -∗
    ps !! i ≡ Some p1 -∗
    p1 ⊑ p2 -∗
    iProto_consistent (<[i := p2]>ps).
  Proof.
    iLöb as "IH" forall (ps i p1 p2).
    rename i into k.
    iIntros "Hps #Hk Hle".
    iAssert (⌜k < length ps⌝)%I as %Hlen.
    { rewrite option_equivI. destruct (ps !!k) eqn:Heqn; [|done].
      iPureIntro. by apply lookup_lt_is_Some_1. }
    rewrite !iProto_consistent_unfold.
    iDestruct "Hps" as "[Htar Hps]".
    iSplit.
    { iDestruct (valid_target_le with "Htar Hk Hle") as "$". }
    iIntros (i j m1 m2 Hneq) "Hi Hj".
    destruct (decide (k = i)) as [<-|Hneq1].
    - destruct (decide (k = j)) as [<-|Hneq2].
      + done.
      + rewrite list_lookup_total_insert_eq; [|done].
        rewrite list_lookup_total_insert_ne; [|done].
        rewrite iProto_le_unfold.
        iDestruct ("Hle" with "Hi") as (m') "[Hi Hle]".
        iIntros (v p) "Hm".
        iDestruct ("Hps" with "[//] [Hk Hi] Hj") as "Hps".
        { rewrite list_lookup_total_alt. iRewrite "Hk". simpl.
          done. }
        iDestruct ("Hle" with "Hm") as (p') "[Hle Hm]".
        iDestruct ("Hps" with "Hm") as (p'') "[Hm Hps]".
        iExists p''. iFrame.
        rewrite -!(list_insert_insert_ne _ k j); [|done..].
        iDestruct ("IH" $! _ k with "Hps [] Hle") as "Hps".
        { iNext.
          rewrite list_lookup_insert_eq; [done|].
          by rewrite length_insert. }
        rewrite !list_insert_insert_eq. done.
    - destruct (decide (k = j)) as [<-|Hneq2].
      + rewrite list_lookup_total_insert_ne; [|done].
        rewrite list_lookup_total_insert_eq; [|done].
        rewrite iProto_le_unfold.
        iDestruct ("Hle" with "Hj") as (m') "[Hj Hle]".
        iIntros (v p) "Hm".
        iDestruct ("Hps" with "[] Hi [Hk Hj]") as "Hps"; [done|..].
        { rewrite list_lookup_total_alt. iRewrite "Hk". simpl.
          done. }
        iDestruct ("Hps" with "Hm") as (p') "[Hm Hps]".
        iDestruct ("Hle" with "Hm") as (p'') "[Hle Hm]".
        iExists p''. iFrame.
        rewrite -!(list_insert_insert_ne _ k i); [|done..].
        iDestruct ("IH" $! _ k with "Hps [] Hle") as "Hps".
        { iNext. rewrite list_lookup_insert_eq; [done|by rewrite length_insert]. }
        rewrite !list_insert_insert_eq. done.
      + rewrite !list_lookup_total_insert_ne; [|done..].
        iDestruct ("Hps" with "[] Hi Hj") as "Hps"; [done|].
        iIntros (v p) "Hm".
        iDestruct ("Hps" with "Hm") as (p') "[Hm Hps]".
        iExists p'. iFrame. iNext.
        rewrite -(list_insert_insert_ne _ k j); [|done].
        rewrite -(list_insert_insert_ne _ k i); [|done].
        iApply ("IH" with "Hps [Hk] Hle").
        rewrite !list_lookup_insert_ne; done.
  Qed.

  Lemma iProto_le_payload_elim_l i m v P p :
    (P -∗ (<?[i]> MSG v; p) ⊑ (<?[i]> m)) ⊢
    (<?[i]> MSG v {{ P }}; p) ⊑ <?[i]> m.
  Proof.
    rewrite iMsg_base_eq. iIntros "H".
    iApply iProto_le_recv. iIntros (v' p') "(->&Hp&HP)".
    iApply (iProto_le_recv_recv_inv with "(H HP)"); simpl; auto.
  Qed.
  Lemma iProto_le_payload_elim_r i m v P p :
    (P -∗ (<(Send, i)> m) ⊑ (<(Send, i)> MSG v; p)) ⊢
    (<![i]> m) ⊑ (<![i]> MSG v {{ P }}; p).
  Proof.
    rewrite iMsg_base_eq. iIntros "H".
    iApply iProto_le_send. iIntros (v' p') "(->&Hp&HP)".
    iApply (iProto_le_send_send_inv with "(H HP)"); simpl; auto.
  Qed.
  Lemma iProto_le_payload_intro_l i v P p :
    P -∗ (<![i]> MSG v {{ P }}; p) ⊑ (<![i]> MSG v; p).
  Proof.
    rewrite iMsg_base_eq.
    iIntros "HP". iApply iProto_le_send. iIntros (v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iProto_le_refl|]. auto.
  Qed.
  Lemma iProto_le_payload_intro_r i v P p :
    P -∗ (<?[i]> MSG v; p) ⊑ (<?[i]> MSG v {{ P }}; p).
  Proof.
    rewrite iMsg_base_eq.
    iIntros "HP". iApply iProto_le_recv. iIntros (v' p') "(->&Hp&_) /=".
    iExists p'. iSplitR; [iApply iProto_le_refl|]. auto.
  Qed.
  Lemma iProto_le_exist_elim_l {A} i (m1 : A → iMsg Σ V) m2 :
    (∀ x, (<?[i]> m1 x) ⊑ (<?[i]> m2)) ⊢
    (<?[i] x> m1 x) ⊑ (<?[i]> m2).
  Proof.
    rewrite iMsg_exist_eq. iIntros "H".
    iApply iProto_le_recv. iIntros (v p1') "/=". iDestruct 1 as (x) "Hm".
    by iApply (iProto_le_recv_recv_inv with "H").
  Qed.
  Lemma iProto_le_exist_elim_r {A} i m1 (m2 : A → iMsg Σ V) :
    (∀ x, (<![i]> m1) ⊑ (<![i]> m2 x)) ⊢
    (<![i]> m1) ⊑ (<![i] x> m2 x).
  Proof.
    rewrite iMsg_exist_eq. iIntros "H".
    iApply iProto_le_send. iIntros (v p2'). iDestruct 1 as (x) "Hm".
    by iApply (iProto_le_send_send_inv with "H").
  Qed.
  Lemma iProto_le_exist_intro_l {A} i (m : A → iMsg Σ V) a :
    ⊢ (<![i] x> m x) ⊑ (<![i]> m a).
  Proof.
    rewrite iMsg_exist_eq. iApply iProto_le_send. iIntros (v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iProto_le_refl.
  Qed.
  Lemma iProto_le_exist_intro_r {A} i (m : A → iMsg Σ V) a :
    ⊢ (<?[i]> m a) ⊑ (<?[i] x> m x).
  Proof.
    rewrite iMsg_exist_eq. iApply iProto_le_recv. iIntros (v p') "Hm /=".
    iExists p'. iSplitR; last by auto. iApply iProto_le_refl.
  Qed.

  Lemma iProto_le_texist_elim_l {TT : tele} i (m1 : TT → iMsg Σ V) m2 :
    (∀ x, (<?[i]> m1 x) ⊑ (<?[i]> m2)) ⊢
    (<?[i].. x> m1 x) ⊑ (<?[i]> m2).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iProto_le_exist_elim_l; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.
  Lemma iProto_le_texist_elim_r {TT : tele} i m1 (m2 : TT → iMsg Σ V) :
    (∀ x, (<![i]> m1) ⊑ (<![i]> m2 x)) -∗
    (<![i]> m1) ⊑ (<![i].. x> m2 x).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply iProto_le_exist_elim_r; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.

  Lemma iProto_le_texist_intro_l {TT : tele} i (m : TT → iMsg Σ V) x :
    ⊢ (<![i].. x> m x) ⊑ (<![i]> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply iProto_le_refl. }
    iApply iProto_le_trans; [by iApply iProto_le_exist_intro_l|]. iApply IH.
  Qed.
  Lemma iProto_le_texist_intro_r {TT : tele} i (m : TT → iMsg Σ V) x :
    ⊢ (<?[i]> m x) ⊑ (<?[i].. x> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply iProto_le_refl. }
    iApply iProto_le_trans; [|by iApply iProto_le_exist_intro_r]. iApply IH.
  Qed.

  Lemma iProto_consistent_target ps m a i j :
    iProto_consistent ps -∗
    iProto_elem_of (<(a, j)> m) (ps !!! i) -∗
    ⌜is_Some (ps !! j)⌝.
  Proof.
    rewrite iProto_consistent_unfold. iDestruct 1 as "[Htar _]".
    iIntros "H". iApply ("Htar" $! i).
    rewrite list_lookup_total_alt. done.
  Qed.

  Lemma iProto_consistent_step ps m1 m2 i j v p1 :
    i ≠ j →
    iProto_consistent ps -∗
    iProto_elem_of (<(Send, j)> m1) (ps !!! i) -∗
    iProto_elem_of (<(Recv, i)> m2) (ps !!! j) -∗
    iMsg_car m1 v (Next p1) -∗
    ∃ p2, iMsg_car m2 v (Next p2) ∗
          ▷ iProto_consistent (<[i := p1]>(<[j := p2]>ps)).
  Proof.
    iIntros (Hneq) "Hprot #Hi #Hj Hm1".
    rewrite iProto_consistent_unfold /iProto_consistent_pre.
    iDestruct "Hprot" as "[_ Hprot]".
    iDestruct ("Hprot" $! i j with "[//] Hi Hj Hm1") as (p2) "[Hm2 Hprot]".
    iExists p2. iFrame.
  Qed.

  Lemma iProto_own_le γ s p1 p2 :
    iProto_own γ s p1 -∗ ▷ (p1 ⊑ p2) -∗ iProto_own γ s p2.
  Proof.
    iDestruct 1 as (p1') "[Hle H]". iIntros "Hle'".
    iExists p1'. iFrame "H". by iApply (iProto_le_trans with "Hle").
  Qed.

  Lemma iProto_own_excl γ i (p1 p2 : iProto Σ V) :
    iProto_own γ i p1 -∗ iProto_own γ i p2 -∗ False.
  Proof.
    rewrite /iProto_own.
    iDestruct 1 as (p1') "[_ Hp1]".
    iDestruct 1 as (p2') "[_ Hp2]".
    iDestruct (own_prot_excl with "Hp1 Hp2") as %[].
  Qed.

  Lemma iProto_ctx_agree γ n i p :
    iProto_ctx γ n -∗
    iProto_own γ i p -∗
    ⌜i < n⌝.
  Proof.
      iIntros "Hctx Hown".
      rewrite /iProto_ctx /iProto_own.
      iDestruct "Hctx" as (ps <-) "[Hauth Hps]".
      iDestruct "Hown" as (p') "[Hle Hown]".
      iDestruct (iProto_own_auth_agree_Some with "Hauth Hown") as %HSome.
      iPureIntro.
      by apply lookup_lt_is_Some_1.
  Qed.

  Lemma iProto_init ps :
    ▷ iProto_consistent ps -∗
    |==> ∃ γ, iProto_ctx γ (length ps) ∗ [∗ list] i ↦p ∈ ps, iProto_own γ i p.
  Proof.
    iIntros "Hconsistent".
    iMod iProto_own_auth_alloc as (γ) "[Hauth Hfrags]".
    iExists γ. by iFrame.
  Qed.

  Lemma iProto_step γ ps_dom i j m1 m2 p1 v :
    iProto_ctx γ ps_dom -∗
    iProto_own γ i (<(Send, j)> m1) -∗
    iProto_own γ j (<(Recv, i)> m2) -∗
    iMsg_car m1 v (Next p1) ==∗
    ▷ ∃ p2, iMsg_car m2 v (Next p2) ∗ iProto_ctx γ ps_dom ∗
            iProto_own γ i p1 ∗ iProto_own γ j p2.
  Proof.
    iIntros "Hctx Hi Hj Hm".
    iDestruct (iProto_ctx_agree with "Hctx Hi") as %Hi.
    iDestruct (iProto_ctx_agree with "Hctx Hj") as %Hij.
    iDestruct "Hi" as (pi) "[Hile Hi]".
    iDestruct "Hj" as (pj) "[Hjle Hj]".
    iDestruct "Hctx" as (ps Hdom) "[Hauth Hconsistent]".
    iDestruct (iProto_own_auth_agree with "Hauth Hi") as "#Hpi".
    iDestruct (iProto_own_auth_agree with "Hauth Hj") as "#Hpj".
    iDestruct (own_prot_idx with "Hi Hj") as %Hneq.
    iAssert (▷ (<[i:=<(Send, j)> m1]>ps !! j ≡ Some pj))%I as "Hpj'".
    { by rewrite list_lookup_insert_ne. }
    iDestruct (iProto_consistent_le with "Hconsistent Hpi Hile") as "Hconsistent".
    iDestruct (iProto_consistent_le with "Hconsistent Hpj' Hjle") as "Hconsistent".
    iDestruct (iProto_consistent_step _ _ _ i j with "Hconsistent [] [] [Hm //]") as
      (p2) "[Hm2 Hconsistent]"; [done|..].
    { rewrite list_lookup_insert_ne; [|done].
      rewrite (list_lookup_total_insert_ne _ j i); [|done].
      rewrite list_lookup_total_insert_eq; [|lia].
      by iApply iProto_elem_of_message. }
    { rewrite list_lookup_insert_ne; [|done].
      rewrite list_lookup_total_insert_eq; [|rewrite length_insert; lia].
      by iApply iProto_elem_of_message. }
    iMod (iProto_own_auth_update _ _ _ _ p2 with "Hauth Hj") as "[Hauth Hj]".
    iMod (iProto_own_auth_update _ _ _ _ p1 with "Hauth Hi") as "[Hauth Hi]".
    iIntros "!>!>". iExists p2. iFrame "Hm2".
    iSplitL "Hconsistent Hauth".
    { iExists (<[i:=p1]> (<[j:=p2]> ps)).
      iSplit.
      { iPureIntro. rewrite !length_insert. done. }
      iFrame. rewrite list_insert_insert_eq.
      rewrite list_insert_insert_ne; [|done]. rewrite list_insert_insert_eq.
      by rewrite list_insert_insert_ne; [|done]. }
    iSplitL "Hi"; iExists _; iFrame; iApply iProto_le_refl.
  Qed.

  Lemma iProto_target γ ps_dom i a j m :
    iProto_ctx γ ps_dom -∗
    iProto_own γ i (<(a, j)> m) -∗
    ▷ (⌜j < ps_dom⌝).
  Proof.
    iIntros "Hctx Hown".
    rewrite /iProto_ctx /iProto_own.
    iDestruct "Hctx" as (ps Hdom) "[Hauth Hps]".
    iDestruct "Hown" as (p') "[Hle Hown]".
    iDestruct (iProto_own_auth_agree with "Hauth Hown") as "#Hi".
    iDestruct (iProto_le_msg_inv_r with "Hle") as (m') "#Heq".
    iDestruct (iProto_consistent_target ps m' a i j with "Hps []") as "#H".
    { iNext. rewrite list_lookup_total_alt. iRewrite "Hi". done. }
    iNext. iDestruct "H" as %HSome.
    iPureIntro. subst. by apply lookup_lt_is_Some_1.
  Qed.

  Lemma iProto_lookup_le_weak p1 p2 a j m:
    iProto_elem_of (<(a,j)> m) p2 -∗
    p1 ⊑ p2 -∗
    ∃ m',
    iProto_elem_of (<(a,j)>m') p1.
  Proof.
    iIntros "Hp2 Hle".
    rewrite iProto_le_unfold.
    iDestruct ("Hle" with "Hp2") as (m') "[Hp1 Hle]".
    iExists _. iFrame.
  Qed.

  Lemma iProto_target_strong γ ps_dom i p a j m :
    iProto_ctx γ ps_dom -∗
    iProto_own γ i p -∗
    iProto_elem_of (<(a,j)> m) p -∗
    ▷ (⌜j < ps_dom⌝).
  Proof.
    iIntros "Hctx Hown #Hp".
    rewrite /iProto_ctx /iProto_own.
    iDestruct "Hctx" as (ps Hdom) "[Hauth Hps]".
    iDestruct "Hown" as (p') "[Hle Hown]".
    iDestruct (iProto_own_auth_agree with "Hauth Hown") as "#Hi".
    iNext.
    iDestruct (iProto_lookup_le_weak with "Hp Hle") as (m') "#Hp'".
    iDestruct (iProto_consistent_target ps m' a i j with "Hps []") as "#H".
    { rewrite list_lookup_total_alt. iRewrite "Hi". simpl. iApply "Hp'". }
    iDestruct "H" as %HSome.
    iPureIntro. subst. by apply lookup_lt_is_Some_1.
  Qed.

  (** The instances below make it possible to use the tactics [iIntros], *)
  (* [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [iProto_le] goals. *)
  Global Instance iProto_le_from_forall_l {A} i (m1 : A → iMsg Σ V) m2 name :
    AsIdentName m1 name →
    FromForall ((<?[i]> (iMsg_exist m1)) ⊑ (<?[i]> m2))
               (λ x, (<?[i]> m1 x) ⊑ (<?[i]> m2))%I name | 10.
  Proof. intros _. apply iProto_le_exist_elim_l. Qed.
  Global Instance iProto_le_from_forall_r {A} i m1 (m2 : A → iMsg Σ V) name :
    AsIdentName m2 name →
    FromForall ((<![i]> m1) ⊑ (<![i]> (iMsg_exist m2)))
               (λ x, (<![i]> m1) ⊑ (<![i]> m2 x))%I name | 11.
  Proof. intros _. apply iProto_le_exist_elim_r. Qed.

  Global Instance iProto_le_from_wand_l i m v P p :
    TCIf (TCEq P True%I) False TCTrue →
    FromWand ((<?[i]> MSG v {{ P }}; p) ⊑ (<?[i]> m)) P ((<?[i]> MSG v; p) ⊑ (<?[i]> m)) | 10.
  Proof. intros _. apply iProto_le_payload_elim_l. Qed.
  Global Instance iProto_le_from_wand_r i m v P p :
    FromWand ((<![i]> m) ⊑ (<![i]> MSG v {{ P }}; p)) P ((<![i]> m) ⊑ (<![i]> MSG v; p)) | 11.
  Proof. apply iProto_le_payload_elim_r. Qed.

  Global Instance iProto_le_from_exist_l {A} i (m : A → iMsg Σ V) p :
    FromExist ((<![i] x> m x) ⊑ p) (λ a, (<![i]> m a) ⊑ p)%I | 10.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iProto_le_trans with "[] H"). iApply iProto_le_exist_intro_l.
  Qed.
  Global Instance iProto_le_from_exist_r {A} i (m : A → iMsg Σ V) p :
    FromExist (p ⊑ <?[i] x> m x) (λ a, p ⊑ (<?[i]> m a))%I | 11.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (iProto_le_trans with "H"). iApply iProto_le_exist_intro_r.
  Qed.

  Global Instance iProto_le_from_sep_l i m v P p :
    FromSep ((<![i]> MSG v {{ P }}; p) ⊑ (<![i]> m)) P ((<![i]> MSG v; p) ⊑ (<![i]> m)) | 10.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iProto_le_trans with "[HP] H"). by iApply iProto_le_payload_intro_l.
  Qed.
  Global Instance iProto_le_from_sep_r i m v P p :
    FromSep ((<?[i]> m) ⊑ (<?[i]> MSG v {{ P }}; p)) P ((<?[i]> m) ⊑ (<?[i]> MSG v; p)) | 11.
  Proof.
    rewrite /FromSep. iIntros "[HP H]".
    iApply (iProto_le_trans with "H"). by iApply iProto_le_payload_intro_r.
  Qed.

  Global Instance iProto_le_frame_l i q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<![i]> MSG v {{ P }}; p) ⊑ (<![i]> m))
              ((<![i]> MSG v {{ Q }}; p) ⊑ (<![i]> m)) | 10.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iProto_le_trans with "[HR] H"). iApply iProto_le_payload_elim_r.
    iIntros "HQ". iApply iProto_le_payload_intro_l. iApply HP; iFrame.
  Qed.
  Global Instance iProto_le_frame_r i q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<?[i]> m) ⊑ (<?[i]> MSG v {{ P }}; p))
              ((<?[i]> m) ⊑ (<?[i]> MSG v {{ Q }}; p)) | 11.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (iProto_le_trans with "H"). iApply iProto_le_payload_elim_l.
    iIntros "HQ". iApply iProto_le_payload_intro_r. iApply HP; iFrame.
  Qed.

  Global Instance iProto_le_from_modal a v p1 p2 :
    FromModal True (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((<a> MSG v; p1) ⊑ (<a> MSG v; p2)) (p1 ⊑ p2).
  Proof. intros _. iApply iProto_le_base. Qed.

End proto.

Global Typeclasses Opaque iProto_ctx iProto_own.

Global Hint Extern 0 (environments.envs_entails _ (?x ⊑ ?y)) =>
  first [is_evar x; fail 1 | is_evar y; fail 1|iApply iProto_le_refl] : core.
