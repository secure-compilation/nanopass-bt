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
Require Import Source.BacktranslationCompilers.
Require Import Source.BacktranslationLanguages.
Require Import Source.BacktranslationExpressions.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import BacktranslationMisc.
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

Require Import Source.Extra.
Require Import BacktranslationSimulations.

Section Thm.

Variable p: UnitTree.prg.
Variable t: trace.

(* Here, we assume the trace is nonempty and well-formed.
   It is trivial to extend the result to empty traces. *)
Hypothesis wf_t: wf_trace (UnitTree.prog_interface p) t.
Hypothesis t_non_empty: t <> [::].

Hypothesis p_wf: UnitTree.wf p.
Theorem stack_tree_wf:
  StackTree.wf (compile_numbered_tree (compile_unit_tree p)).
Proof.
  destruct p_wf.
  constructor; try rewrite !domm_map; eauto.
  - intros C tr. rewrite !mapmE.
    simpl.
    specialize (unique_current C).
    destruct (UnitTree.prog_trees p C) eqn:H.
    2: { rewrite H. simpl. congruence. }
    specialize (unique_current _ Logic.eq_refl).
    rewrite H; simpl. intros G; inv G.
    eapply unique_current_numbered_to_stack_tree; eauto.
    unfold loc_tree_of_unit_tree.
    destruct (numbering_tree) eqn:X.
    symmetry in X.
    eapply numbering_tree_unique_current in X; eauto.
  - intros C tr. simpl. rewrite !mapmE.
    specialize (determinacy C).
    destruct (UnitTree.prog_trees p C) eqn:H.
    2: { rewrite H. simpl. congruence. }
    specialize (determinacy _ Logic.eq_refl).
    rewrite H; simpl. intros G; inv G.
    eapply deterministic_numbered_to_stack_tree.
    unfold loc_tree_of_unit_tree.
    destruct (numbering_tree) eqn:X.
    symmetry in X.
    eapply numbering_tree_determinacy in X; eauto.
  - intros C tr. simpl. rewrite !mapmE.
    destruct (UnitTree.prog_trees p C) eqn:H.
    2: { rewrite H. simpl. congruence. }
    rewrite H; simpl. intros G; inv G.
    eapply unique_numbering_numbered_to_stack_tree.
    unfold loc_tree_of_unit_tree.
    destruct (numbering_tree) eqn:X.
    symmetry in X.
    eapply numbering_tree_unicity in X; eauto.
Qed.

(* Hypothesis: the program [p] produces the trace [t] *)
Hypothesis p_does_t: exists s,
    Star (UnitTree.sem p) (t, UnitTree.prog_trees p) t s.

(* We assume that we are given the list of procedures that we
 have to produce for each compartment, and that this list satisfies
 some basic well-formedness properties.

Eventually, we will build this list from the traces to back-translate,
but this is not part of our formal development yet *)
Hypothesis procs: {fmap Component.id -> seq Procedure.id}.
Hypothesis domm_procs: domm procs = domm (UnitTree.prog_trees p).
Hypothesis domm_procs':
  forall (C C' : Component.id) (P : Procedure.id),
  imported_procedure (UnitTree.prog_interface p) C C' P ->
  exists Ps : seq Procedure.id, procs C' = Some Ps /\ P \in Ps.
Hypothesis domm_procs0:
  forall (C : nat_ordType) (Ps : seq Procedure.id),
  procs C = Some Ps -> 0 \in Ps.
Hypothesis main_procs:
  exists Ps : seq Procedure.id,
    procs Component.main = Some Ps /\ Procedure.main \in Ps.

Let p_bt := compile (compile_stack_tree
                       (compile_numbered_tree
                          (compile_unit_tree p))) procs.

Theorem fwd_sim_bt:
  forward_simulation (UnitTree.sem p) (CS.sem p_bt).
  unfold p_bt.
  eapply compose_forward_simulations with (L2 := NumberedTree.sem (compile_unit_tree p)).
  eapply sim_a_numbering.
  eapply compose_forward_simulations with (L2 := StackTree.sem (compile_numbered_tree (compile_unit_tree p))).
  eapply sim_b_stacking.
  eapply compose_forward_simulations with (L2 := Flattened.sem (compile_stack_tree (compile_numbered_tree (compile_unit_tree p)))).
  eapply sim_c_flattening. eapply stack_tree_wf.
  eapply sim_d_to_source. eapply wf_compile_stack_tree.
  eapply stack_tree_wf.
  rewrite /= !domm_map. eapply domm_procs.
  eapply domm_procs'.
  eapply domm_procs0.
  eapply main_procs.
Qed.

(* This is the final theorem (Theorem 3) *)
Corollary p_bt_does_t: exists s,
    Star (CS.sem p_bt) (CS.initial_machine_state p_bt) t s.
Proof.
  pose proof fwd_sim_bt as sim.
  inv sim.
  pose proof p_does_t as [s STAR].
  exploit fsim_match_initial_states; eauto.
  constructor; eauto.
  intros [i [? [INI MS]]].
  simpl in INI. inv INI.
  exploit simulation_star; eauto.
  intros [i' [s2' [? ?]]].
  eexists; eauto.
Qed.

End Thm.

Check p_bt_does_t.
Print Assumptions p_bt_does_t.
