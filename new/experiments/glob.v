From iris.proofmode Require Import environments string_ident.
From New.proof Require Import proof_prelude.
From stdpp Require Import base.
Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 is_glob_identifier_char (x : char) : bool :=
  let n := Char.to_int x in
  let alpha_upper := Bool.and (Int.le n 90) (Int.le 65 n) in
  let alpha_lower := Bool.and (Int.le n 122) (Int.le 97 n) in
  let num := Bool.and (Int.le n 57) (Int.le 48 n) in
  if (Bool.or (Bool.or alpha_lower alpha_upper) num) then true
  else match (String.make 1 x) with
       | "_" => true | "'" => true | "*" => true | _ => false
       end.

Ltac2 is_glob_char (x : char) : bool := Int.equal 42 (Char.to_int x).

Ltac2 glob (handle_glob : string -> string -> string) (x : string) : string :=
  let word_start := Ref.ref 0 in
  let glob_pos : int option Ref.ref := Ref.ref None in

  let end_of_word i : string :=
    if (Int.lt (Ref.get word_start) i) then
      let gs := (String.sub x (Ref.get word_start) (Int.sub i (Ref.get word_start))) in
      match (Ref.get glob_pos) with
      | None => gs
      | Some p => (* and if it has a glob in it, then handle it. *)
          let gp := (Int.sub p (Ref.get word_start)) in
          let pref := (String.sub gs 0 gp) in
          let suff := (String.sub gs (Int.add gp 1) (Int.sub (String.length gs) (Int.add gp 1))) in
          handle_glob pref suff
      end
    else ""
  in

  let rec loop i :=
    if (Int.le (String.length x) i) then end_of_word i
    else (if is_glob_char (String.get x i) then (Ref.set glob_pos (Some i)) else ();
          if (is_glob_identifier_char (String.get x i)) then
            loop (Int.add i 1)
          else
            let s := end_of_word i in
            Ref.set word_start (Int.add i 1);
            Ref.set glob_pos None;
            String.app (String.app s (String.make 1 (String.get x i))) (loop (Int.add i 1)))
  in loop 0.

Ltac2 get_matching_hyps (check : string -> bool) : string list :=
  (* orelse (fun () => *)
            lazy_match! goal with
            | [ |- envs_entails (Envs _ ?es _) _ ] =>
                let rec loop es :=
                  match! es with
                  | Esnoc ?es (base.ident.INamed ?n) _ =>
                      let s := StringToIdent.coq_string_to_string n in
                      if check s then s :: (loop es)
                      else loop es
                  | _ => []
                  end in
                loop es
            | [ |- ?g ] =>
                Message.print (Message.of_constr g);
                Control.enter (fun () => Message.print (Message.of_constr (Control.goal ())));
                Control.backtrack_tactic_failure "get_matching_hyps: was not run with Iris context"
            end
    (* (fun _ => Control.throw (Tactic_failure (Some (Message.of_string "get_matching_hyps: oreslse failed")))). *)
.

Module String.
Ltac2 is_prefix pref s :=
  if Int.lt (String.length pref) (String.length s) then
    let pref' := (String.sub s 0 (String.length pref)) in
    String.equal pref pref'
  else false.

Ltac2 is_suffix suff s :=
  if Int.lt (String.length suff) (String.length s) then
    let suff' := (String.sub s (Int.sub (String.length s) (String.length suff)) (String.length suff)) in
    String.equal suff suff'
  else false.
End String.

Ltac2 handle_ipm_glob pref suff :=
  let minlen := Int.add (String.length pref) (String.length suff) in
  String.concat " "
    (get_matching_hyps
       (fun s => if (Int.ge (String.length s) minlen) then (* for overlapping [pref] and [suff] *)
                if String.is_prefix pref s then String.is_suffix suff s else false
              else false)).

Ltac2 glob_ipm (s : preterm) :=
  IdentToString.string_to_coq_string (glob handle_ipm_glob (StringToIdent.coq_string_to_string (Constr.pretype s))).

Section test.
Context `{PROP : bi}.

Notation " 'f' s" :=
  (ltac2:(let n := glob_ipm s in set (_glob_name:=$n); Message.print (Message.of_constr n)))
    (at level 0, only parsing).
(* ltac:(refine _glob_name)) (at level 0, only parsing). *)

Lemma test (P Q : PROP) :
  P -∗ P -∗ P -∗ P -∗ Q ∗ Q.
Proof.
  iIntros "H1 H2 P1 P2".
  (* FIXME: have not found a way to layer "glob" on top of exising Iris tactics.
     E.g. the `Tactic Notation` for `iSplitL` expects its argument to be a `constr`.
     When that constr is built up by embedding ltac2 as `ltac2:(glob_ipm
     whatever)`, that ltac2 actually gets run in a new proofview/goal just for
     constructing the constr. So, the goal is `?T` (to construct some constr,
     whose type is not even known).
     However, `glob_ipm` must be run against the actual IPM goal so it can see
     the named hypotheses.

     This implies that there's no way to use ltac to expand a glob in the constr
     arguments to existing Iris tactics.

     One solution: do glob expansion in something at the level of `envs_split_go`.
     Another possible solution: if tactics (like iSplitL) took e.g. ltac2
     strings as input, then computing the string ought to be run in the current
     proofview; the proofview changes when there are quotations/antiquotations.
   *)
  (* let p := f"H*" in *)
  ltac2:(glob_ipm preterm:("H*")).
  constr:(f"H*").
  iSplitL ltac2:(glob_ipm preterm:("H*")).
  constr:(f"H*").

  Time ltac2:(let n := glob_ipm "H*" in set (_glob_name:=$n));
  iSplitL _glob_name; clear _glob_name.

  iDestruct "H" as ltac2:(glob_ipm "H*").
  set (x:=ltac2:(glob_ipm "H*")).
  Ltac2 Eval glob_ipm "*2".
Abort.
End test.
