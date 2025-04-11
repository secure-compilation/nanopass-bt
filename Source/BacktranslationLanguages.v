Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Common.Tree.
Require Import Source.BacktranslationMisc.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq order.
From mathcomp Require ssrnat.
Require Import Lia.
From extructures Require Import fmap.

Import Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Fixpoint possible_step_from_root_br {A E : Type} (e : E) (tr : Tree.t A E) (br : Tree.b A E) : Prop := match br with                                                                     | Bnil => False                                                                 | Bcons e' tr' br' => e = e' /\ tr = tr' \/ possible_step_from_root_br e tr br'                                                                           end.

Definition possible_step_from_root {A E : Type} (e : E) (tr' tr : Tree.t A E) : Prop := match tr with                                                                                | node a br => possible_step_from_root_br e tr' br
                                                                                      end.

Definition unit_tree := Tree.t unit event.

Definition allowed_event (intf: Program.interface) (e: event): Prop :=
  match e with
  | ECall C1 P z C2 => C1 <> C2 /\ imported_procedure intf C1 C2 P /\ exported_procedure intf C2 P
  | ERet C1 z C2 => C1 <> C2
  end /\ cur_comp_of_event e \in domm intf /\ next_comp_of_event e \in domm intf.

Fixpoint wb_trace (st: seq (Component.id * Component.id)) (t: trace): Prop :=
  match t with
  | [] => True
  | ECall C1 _ _ C2 :: t' => wb_trace ((C1, C2) :: st) t'
  | ERet C1 _ C2 :: t' =>
    match st with
    | [] => False
    | (C2', C1') :: st' => (C1 == C1') /\ (C2 == C2') /\ wb_trace st' t'
    end
  end.

Definition valid_trace (intf: Program.interface) (t: trace) : Prop :=
  forall e, In e t -> allowed_event intf e.

Definition next_comp t :=
  match t with
  | [] => None
  | e :: t' => Some (cur_comp_of_event e)
  end.

Definition next_call_comp t :=
  match t with
  | ECall _ _ _ C2 :: t' => Some C2
  | _ => None
  end.

Fixpoint events_sequence_ok (C: Component.id) (t: trace) :=
  match t with
  | [] => True
  | e :: t' => cur_comp_of_event e = C /\
               events_sequence_ok (next_comp_of_event e) t'
  end.

Definition wf_trace (intf: Program.interface) (t: trace) :=
  wb_trace [] t /\ valid_trace intf t /\ next_comp t = Some Component.main /\ events_sequence_ok Component.main t.


Definition match_incoming e e' :=
  match e, e' with
  | ECall Ccur Pnext z Cnext, ECall Ccur' Pnext' z' Cnext' =>
      Cnext = Cnext' /\ Pnext = Pnext' /\ z = z'
  | ERet Ccur z Cnext, ERet Ccur' z' Cnext' =>
      Cnext = Cnext' /\ z = z'
  | _, _ => False
  end.

Inductive deterministic_tree {A: Type}: Tree.t A event -> Prop :=
| deterministic_cons : forall (a: A) (br: Tree.b A event),
    deterministic_branches br ->
    deterministic_tree (node a br)
with deterministic_branches {A: Type}: Tree.b A event -> Prop :=
| deterministic_empty:
  deterministic_branches (Bnil _ _)
| deterministic_branches_cons: forall e tr brs,
  deterministic_branches brs ->
  deterministic_tree tr ->
  do_not_appear_in e brs ->
  deterministic_branches (Bcons e tr brs)
  with do_not_appear_in {A: Type}: event -> Tree.b A event -> Prop :=
| do_not_appear_in_empty: forall e,
    do_not_appear_in e (Bnil _ _)
| do_not_appear_in_cons: forall e e' tr brs,
    do_not_appear_in e brs ->
    not (match_incoming e e') ->
    do_not_appear_in e (Bcons e' tr brs).

Fixpoint unique_current_tree {A: Type} (C: Component.id) (tr: Tree.t A event): bool :=
  match tr with
  | node _ br => unique_current_branches C br
  end
with unique_current_branches {A: Type} (C: Component.id) (br: Tree.b A event): bool :=
       match br with
       | Bnil => true
       | Bcons e tr br' =>
           (unique_current_tree C tr) &&
             (if cur_comp_of_event e == C then
                match br' with | Bnil => true | _ => false end
              else unique_current_branches C br')
       end.




Inductive Forall_branch_tr {A E: Type} (f: E -> Prop): Tree.t A E -> Prop :=
| fab_tr_case : forall (a: A) (br: Tree.b A E),
    Forall_branch_br f br ->
    Forall_branch_tr f (node a br)
with
  Forall_branch_br {A E: Type} (f: E -> Prop): Tree.b A E -> Prop :=
| fab_br_nil : Forall_branch_br f (Bnil A E)
| fab_br_bcons : forall (e: E) (tr: Tree.t A E) (br: Tree.b A E), f e -> Forall_branch_tr f tr -> Forall_branch_br f br -> Forall_branch_br f (Bcons e tr br).


Module UnitTree.
  Record prg := { prog_interface : Program.interface;
                  prog_trees : NMap unit_tree}.
  Definition genv := Program.interface.
  Definition state := (trace * NMap unit_tree)%type.

  Record wf (p : prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p);
      wfprog_interface_sound: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      unique_current: forall C tr, prog_trees p C = Some tr ->
                              unique_current_tree C tr;
      determinacy: forall C tr, prog_trees p C = Some tr -> deterministic_tree tr;
      wf_has_main: prog_interface p Component.main
    }.

  Variant initial (p : prg) : state -> Prop :=
    | initial_st: forall (tra : trace), wf_trace (prog_interface p) tra ->
                                   tra <> [] ->
                                        initial p (tra, prog_trees p)
  .

  Variant final (p : prg) : state -> Prop :=
    | final_nil: forall (trees : NMap unit_tree), final p ([], trees)
  .

  Variant step (p : prg) (ge : genv) : state -> trace -> state -> Prop :=
    | step_trace: forall (C1 C2 : Component.id) (tr1 tr2 tr'1 tr'2 : unit_tree)
                         (e : event) (tra : trace)
                         (trees : NMap unit_tree),
        forall (wf_e: well_formed_event (prog_interface p) e),
        forall (wf_et: events_sequence_ok C1 (e :: tra)),
        C1 = cur_comp_of_event e ->
        C2 = next_comp_of_event e ->
        forall (trees_cur: trees C1 = Some tr1)
          (possible_cur: possible_step_from_root e tr'1 tr1)
          (trees_next: trees C2 = Some tr2)
          (possible_next: possible_step_from_root e tr'2 tr2),
        forall (UNIQ1: unique_current_tree C1 tr1),
        forall (DET1: deterministic_tree tr1)
          (DET2: deterministic_tree tr2),
        step p ge (e :: tra, trees) [e] (tra, setm (setm trees C1 tr'1) C2 tr'2).

  Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
      initial_state := initial p;
      final_state := final p;
      globalenv := prog_interface p |}.
  
End UnitTree.

Definition numbered_tree := Tree.t nat event.

(* Definition get_loc_from_numbered_tree (tr : numbered_tree) := match tr with | node n _ => n end. *)

Module NumberedTree.
  Record prg := { prog_interface : Program.interface;
                  prog_trees : NMap numbered_tree}.
  Definition genv := Program.interface.
  Definition state := (trace * NMap numbered_tree * NMap nat)%type.

  Record wf (p : prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p);
      wfprog_interface_sound: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      unique_current: forall C tr, prog_trees p C = Some tr ->
                              unique_current_tree C tr;
      determinacy: forall C tr, prog_trees p C = Some tr -> deterministic_tree tr;
      unicity_loc: forall C tr, prog_trees p C = Some tr -> unique_numbering tr;
      (* wf_events: forall C tr, prog_trees p C = Some tr -> *)
      (*                    Forall_branch_tr (fun e => allowed_event (prog_interface p) e) tr; *)
      wf_has_main: prog_interface p Component.main
    }.

  Variant initial (p : prg) : state -> Prop :=
    | initial_st: forall (tra: trace),
        wf_trace (prog_interface p) tra ->
        tra <> [::] ->
        (forall C tr, prog_trees p C = Some tr -> loc tr = 0) ->
        initial p (tra, prog_trees p, mkfmapf (fun C => 0) (domm (prog_interface p)))
  .

  Variant final (p : prg) : state -> Prop :=
    | final_nil: forall (trees: NMap numbered_tree) (locs: NMap nat), final p ([], trees, locs)
  .

  Variant step (p : prg) (ge : genv) : state -> trace -> state -> Prop :=
    | step_trace: forall (C1 C2 : Component.id)
                         (e : event) (tra : trace)
                         (trees : NMap numbered_tree) (locs : NMap nat)
                         (tr1 tr'1 tr2 tr'2 : numbered_tree)
                         (n1 n2 : nat),
        forall (wf_e: well_formed_event (prog_interface p) e),
        forall (wf_et: events_sequence_ok C1 (e :: tra)),
        C1 = cur_comp_of_event e ->
        C2 = next_comp_of_event e ->
        forall (trees_cur: trees C1 = Some tr1)
          (possible_cur: possible_step_from_root e tr'1 tr1)
          (loc_cur: n1 = loc tr'1),
          (* (loc_cur': Some n1 = locs C1), *)
        forall (trees_next: trees C2 = Some tr2)
          (possible_next: possible_step_from_root e tr'2 tr2)
          (loc_next: n2 = loc tr'2),
          (* (loc_next': Some n2 = locs C2), *)
        forall (UNIQ1: unique_current_tree C1 tr1),
        forall (DET1: deterministic_tree tr1)
          (DET2: deterministic_tree tr2)
          (UNI1: unique_numbering tr1)
          (UNI2: unique_numbering tr2) ,
        step p ge
          (e :: tra, trees, locs)
          [e]
          (tra, setm (setm trees C1 tr'1) C2 tr'2, setm (setm locs C1 n1) C2 n2).

   Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.

End NumberedTree.

Definition stack_tree := Tree.t loc_stack event.
(* Definition get_loc_from_stack_tree (tr : stack_tree) := match tr with | node (n, _) _ => n end. *)

Module StackTree.

  Record prg := { prog_interface : Program.interface;
                  prog_trees : NMap stack_tree}.
  Definition genv := Program.interface.
  Definition state := (trace * NMap stack_tree * NMap nat * stack)%type.

  Record wf (p : prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p);
      wfprog_interface_sound: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_trees p);
      unique_current: forall C tr, prog_trees p C = Some tr ->
                              unique_current_tree C tr;
      determinacy: forall C tr, prog_trees p C = Some tr -> deterministic_tree tr;
      unicity_loc: forall C tr, prog_trees p C = Some tr -> unique_numbering tr;
      (* wf_events: forall C tr, prog_trees p C = Some tr -> *)
      (*                    Forall_branch_tr (fun e => allowed_event (prog_interface p) e) tr; *)
      wf_has_main: prog_interface p Component.main
    }.

  Variant initial (p : prg) : state -> Prop :=
    | initial_st: forall (tra: trace),
        tra <> [::] ->
        wf_trace (prog_interface p) tra ->
        (forall C tr, prog_trees p C = Some tr -> loc tr = 0) ->
        initial p (tra, prog_trees p, mkfmapf (fun C => 0) (domm (prog_interface p)), [])
  .

  Variant final (p : prg) : state -> Prop :=
    | final_nil: forall (trees: NMap stack_tree) (locs: NMap nat) (st: stack),
        final p ([], trees, locs, st)
  .

  Variant step (p : prg) (ge : genv) : state -> trace -> state -> Prop :=
    | step_call: forall (C1 C2 : Component.id) (P: Procedure.id) (z: Z)
                         (e : event)
                         (tra : trace)
                         (trees : NMap stack_tree) (locs : NMap nat)
                         (tr1 tr'1 tr2 tr'2 : stack_tree)
                         (st: stack)
                         (n1 n2 : nat),
        forall (wf_e: well_formed_event (prog_interface p) e),
        forall (wf_et: events_sequence_ok C1 (e :: tra)),
        e = ECall C1 P z C2 ->
        forall (trees_cur: trees C1 = Some tr1)
          (possible_cur: possible_step_from_root e tr'1 tr1)
          (loc_cur: n1 = loc tr'1),
          (* (loc_cur': Some n1 = locs C1), *)
        forall (trees_next: trees C2 = Some tr2)
          (possible_next: possible_step_from_root e tr'2 tr2)
          (loc_next: n2 = loc tr'2),
          (* (loc_next': Some n2 = locs C2), *)
        forall (UNIQ1: unique_current_tree C1 tr1),
        forall (DET1: deterministic_tree tr1)
          (DET2: deterministic_tree tr2)
          (UNI1: unique_numbering tr1)
          (UNI2: unique_numbering tr2) ,
        step p ge
          (e :: tra, trees, locs, st)
          [e]
          (tra, setm (setm trees C1 tr'1) C2 tr'2,
            setm (setm locs C1 n1) C2 n2, (C1, P, C2) :: st)
    | step_return: forall (C1 C2 : Component.id) (P: Procedure.id) (z: Z)
                         (e : event)
                         (tra : trace)
                         (trees : NMap stack_tree) (locs : NMap nat)
                         (tr1 tr'1 tr2 tr'2 : stack_tree)
                         (f: Component.id * Procedure.id * Component.id) (st: stack)
                         (n1 n2 : nat),
        forall (wf_e: well_formed_event (prog_interface p) e),
        forall (wf_et: events_sequence_ok C1 (e :: tra)),
        e = ERet C1 z C2 ->
        f = (C2, P, C1) ->
        forall (trees_cur: trees C1 = Some tr1)
          (possible_cur: possible_step_from_root e tr'1 tr1)
          (loc_cur: n1 = loc tr'1),
        forall (trees_next: trees C2 = Some tr2)
          (possible_next: possible_step_from_root e tr'2 tr2)
          (loc_next: n2 = loc tr'2),
        forall (UNIQ1: unique_current_tree C1 tr1),
        forall (DET1: deterministic_tree tr1)
          (DET2: deterministic_tree tr2)
          (UNI1: unique_numbering tr1)
          (UNI2: unique_numbering tr2),
        step p ge
          (e :: tra, trees, locs, (f :: st))
          [e]
          (tra, setm (setm trees C1 tr'1) C2 tr'2,
            setm (setm locs C1 n1) C2 n2, st).

   Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := prog_interface p |}.

End StackTree.


Definition outgoing_calls (C: Component.id) (es: list (nat * event * nat)):
  list (nat * (Component.id * Procedure.id * Z) * nat) :=
  pmap (fun '(n, e, n') => match e with
                      | ECall Ccur Pnext z Cnext =>
                          if C == Ccur then
                            Some (n, (Cnext, Pnext, z), n')
                          else
                            None
                      | _ => None
                      end) es.

Definition outgoing (C: Component.id) (es: list (nat * event * nat)):
  list (nat * sum (Component.id * Procedure.id * Z) Z * nat) :=
  pmap (fun '(n, e, n') => match e with
                      | ECall Ccur Pnext z Cnext =>
                          if C == Ccur then
                            Some (n, inl (Cnext, Pnext, z), n')
                          else
                            None
                      | ERet Ccur z Cnext =>
                          if C == Ccur then
                            Some (n, inr z, n')
                          else
                            None
                      end) es.

Definition outgoing_returns (C: Component.id) (es: list (nat * event * nat)):
  list (nat * Z * nat):=
  pmap (fun '(n, e, n') => match e with
                      | ERet Ccur z Cnext =>
                          if C == Ccur then
                            Some (n, z, n')
                          else
                            None
                      | _ => None
                      end) es.

Definition incoming_calls (C: Component.id) (P: Procedure.id)
  (es: list (nat * event * nat)): list (nat * Z * nat) :=
  pmap (fun '(n, e, n') => match e with
                      | ECall Ccur Pnext z Cnext =>
                          if (C == Cnext) && (P == Pnext) then
                            Some (n, z, n')
                          else
                            None
                      | _ => None
                      end) es.

Definition incoming_returns (C: Component.id) (es: list (nat * event * nat)):
  list (nat * Z * nat) :=
  pmap (fun '(n, e, n') => match e with
                      | ERet Ccur z Cnext =>
                          if C == Cnext then
                            Some (n, z, n')
                          else
                            None
                      | _ => None
                      end) es.
Module Flattened.

  Definition cur_proc (st: stack): Procedure.id :=
    match st with
    | nil => 0
    | (_, P, _) :: _ => P
    end.

  Record prg := { prog_interface: Program.interface;
                  prog_procedures: NMap (list (nat * event * nat));
    }.

  Record genv := { genv_interface: Program.interface;
                   genv_procedures: NMap (list (nat * event * nat));
    }.

  Definition state := (trace + (trace * NMap nat * stack))%type.

  Record wf (p : prg) :=
    { wfprog_interface_closed: closed_interface (prog_interface p);
      wfprog_interface_sound: sound_interface (prog_interface p);
      wfprog_defined_procedures: domm (prog_interface p) = domm (prog_procedures p);

      unique_outgoing: forall C es, prog_procedures p C = Some es ->
                                 unicity_in2 (outgoing C es);
      unique_incoming_calls: forall C P es, prog_procedures p C = Some es ->
                                 unicity_in (incoming_calls C P es);
      unique_incoming_returns: forall C es, prog_procedures p C = Some es ->
                                 unicity_in (incoming_returns C es);
      (* unique_current: forall C tr, prog_trees p C = Some tr -> *)
      (*                         unique_current_tree C tr; *)
      (* determinacy: forall C tr, prog_trees p C = Some tr -> deterministic_tree tr; *)
      (* unicity_loc: forall C tr, prog_trees p C = Some tr -> unique_numbering tr; *)
      (* wf_events: forall C tr, prog_trees p C = Some tr -> *)
      (*                    Forall_branch_tr (fun e => allowed_event (prog_interface p) e) tr; *)
      wf_has_main: prog_interface p Component.main
    }.

  Variant initial (p : prg) : state -> Prop :=
    | initial_st: forall (tra: trace),
        tra <> E0 ->
        wf_trace (prog_interface p) tra ->
        initial p (inl tra)
        (* initial p (tra, mkfmapf (fun C => 0) (domm (prog_interface p)), []) *)
  .

  Variant final (p : prg) : state -> Prop :=
    | final_nil': final p (inl [])
    | final_nil: forall (locs: NMap nat) (st: stack),
        final p (inr ([], locs, st))
  .

  Variant step (p : prg) (ge : genv) : state -> trace -> state -> Prop :=
    | step_initialize: forall tra,
        step p ge (inl tra) [::] (inr (tra, mkfmapf (fun C => 0) (domm (prog_interface p)), []))
    | step_call: forall (C1 C2 : Component.id) (P1 P2: Procedure.id) (z: Z)
                         (e : event)
                         (tra : trace)
                         (locs : NMap nat)
                         (cs1 cs2: seq (nat * event * nat))
                         (st: stack)
                         (n1 n2 n1' n2': nat),
        forall (wf_e: well_formed_event (prog_interface p) e),
        forall (wf_et: events_sequence_ok C1 (e :: tra)),
        e = ECall C1 P2 z C2 ->
        forall (curp: cur_proc st = P1),
        forall (procs_cur: ge.(genv_procedures) C1 = Some cs1),
        forall (procs_next: ge.(genv_procedures) C2 = Some cs2),
        forall (locs1: locs C1 = Some n1)
          (locs2: locs C2 = Some n2),
        forall (in_cs1: In (n1, e, n1') cs1),
        forall (in_cs2: In (n2, e, n2') cs2),
        step p ge
          (inr (e :: tra, locs, st))
          [e]
          (inr (tra, setm (setm locs C1 n1') C2 n2', (C1, P2, C2) :: st))
    | step_return: forall (C1 C2 : Component.id) (P1 P2: Procedure.id) (z: Z)
                         (e : event)
                         (tra : trace)
                         (trees : NMap stack_tree) (locs : NMap nat)
                         (cs1 cs2: seq (nat * event * nat))
                         (f: Component.id * Procedure.id * Component.id) (st: stack)
                         (n1 n2 n1' n2' : nat),
        forall (wf_e: well_formed_event (prog_interface p) e),
        forall (wf_et: events_sequence_ok C1 (e :: tra)),
        e = ERet C1 z C2 ->
        f = (C2, P1, C1) ->
        forall (curp: cur_proc st = P2),
        forall (procs_cur: ge.(genv_procedures) C1 = Some cs1),
        forall (procs_next: ge.(genv_procedures) C2 = Some cs2),
        forall (locs1: locs C1 = Some n1)
          (locs2: locs C2 = Some n2),
        forall (in_cs1: In (n1, e, n1') cs1),
        forall (in_cs2: In (n2, e, n2') cs2),
        step p ge
          (inr (e :: tra, locs, (f :: st)))
          [e]
          (inr (tra, setm (setm locs C1 n1') C2 n2', st)).

   Definition sem (p: prg): semantics :=
    {| Smallstep.step := step p;
       initial_state := initial p;
       final_state := final p;
       globalenv := {| genv_interface := prog_interface p;
                    genv_procedures := prog_procedures p; |};
    |}.

End Flattened.
