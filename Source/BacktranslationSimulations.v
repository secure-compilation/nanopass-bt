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
Require Import Source.BacktranslationLanguages.
Require Import Source.BacktranslationCompilers.
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

Ltac fwd_sim M :=
  apply Forward_simulation with (order := Nat.lt) (match_states := M);
  constructor;
  [now apply lt_wf | | |].

Ltac inv H :=
  inversion H;
  clear H;
  subst.

Fixpoint comp_in_trace (tra: trace) (C: Component.id): bool :=
  match tra with
  | [] => false
  | e :: tra' => if (C == cur_comp_of_event e) || (C == next_comp_of_event e) then
                 true
               else
                 comp_in_trace tra' C
  end.

Fixpoint comp_in_trace_list (tras: list trace) (C: Component.id): bool :=
  match tras with
  | [] => false
  | tra :: tras' =>
      match comp_in_trace tra C with
      | false => comp_in_trace_list tras' C
      | true => true
      end
  end.

Inductive match_states_a_numbering (i: nat) : UnitTree.state -> NumberedTree.state -> Prop :=
| match_states_1:
  forall (tra: trace) (trees: NMap unit_tree) (trees': NMap numbered_tree) (locs: NMap nat),
  forall (TREES_COMPILED: forall (C: Component.id) (ut: unit_tree),
        trees C = Some ut ->
        exists n, trees' C = Some (numbering_tree ut n).2),
    match_states_a_numbering i (tra, trees) (tra, trees', locs)
.

(* Lemma get_tree_keep_numbering_tree: *)
(*   forall (ut ut': unit_tree) (tr: numbered_tree) (n0 sz: nat) (e: event), *)
(*     (sz, tr) = numbering_tree ut n0 -> *)
(*     get_child_after_label (eq_event_dec) e ut = Some ut' -> *)
(*     exists tr', get_child_after_label (eq_event_dec) e tr = Some tr'. *)
(* Proof. *)
(*   intro ut. *)
(*   induction ut using tree_ind with *)
(*     (P := fun ut => forall (ut': unit_tree) (tr: numbered_tree) *)
(*                            (n0 sz: nat) (e: event), *)
(*               (sz, tr) = numbering_tree ut n0 -> *)
(*               get_child_after_label eq_event_dec e ut = Some ut' -> *)
(*               exists tr': numbered_tree, *)
(*                 get_child_after_label eq_event_dec e tr = Some tr') *)
(*     (P0 := fun br => forall (ut': unit_tree) (brn: Tree.b nat event) *)
(*                             (n0 sz: nat) (e: event), *)
(*                (sz, brn) = numbering_branches br n0 -> *)
(*                get_tree_after_label_branch eq_event_dec e br = Some ut' -> *)
(*                exists tr' : numbered_tree, *)
(*                  get_tree_after_label_branch eq_event_dec e brn = Some tr'). *)
(*   + intros ut' tr n0 sz e Heq Hgc. *)
(*     inv Hgc ; inv Heq. *)
(*     destruct tr. *)
(*     destruct (numbering_branches b (S n0))eqn:EQ1. *)
(*     apply sym_eq in EQ1. *)
(*     destruct (IHut ut' b1 (S n0) n1 e EQ1 H0) as [tr' H]. *)
(*     exists tr'. *)
(*     unfold get_child_after_label. *)
(*     now inv H1. *)
(*   + intros ut' brn n0 sz e Heq Hgc. *)
(*     inv Hgc. *)
(*   + intros ut' brn n0 sz e0 Heq Hgc. *)
(*     inv Hgc. *)
(*     destruct (eq_event_dec e0 e) ; simpl in H0. *)
(*     * inv H0. *)
(*       inv Heq. *)
(*       destruct (numbering_tree ut' n0) eqn:EQ1. *)
(*       apply sym_eq in EQ1. *)
(*       destruct (numbering_branches b n) eqn:EQ2. *)
(*       exists t. *)
(*       inv H0. *)
(*       simpl. *)
(*       destruct (eq_event_dec e e) ; try reflexivity. *)
(*       now contradict n2. *)
(*     * inv Heq. *)
(*       destruct (numbering_tree ut n0) eqn:EQ1. *)
(*       destruct (numbering_branches b n1) eqn:EQ2. *)
(*       apply sym_eq in EQ2. *)
(*       destruct (IHut0 ut' b0 n1 n2 e0 EQ2 H0) as [tr' H]. *)
(*       exists tr'. *)
(*       inv H1. *)
(*       simpl. *)
(*       destruct (eq_event_dec e0 e) ; try contradiction. *)
(*       assumption. *)
(* Qed. *)

Lemma numbering_tree_keep_possible_label:
  forall (ut ut': unit_tree) (tr: numbered_tree) (n0 sz: nat) (e: event),
    (sz, tr) = numbering_tree ut n0 ->
    possible_step_from_root e ut' ut ->
    exists (n1 sz' : nat) (tr' : numbered_tree),
      (sz', tr') = numbering_tree ut' n1 /\ possible_step_from_root e tr' tr.
Proof.
  induction ut using tree_ind with
    (P := fun ut => forall (ut': unit_tree) (tr: numbered_tree) (n0 sz: nat) (e: event),
              (sz, tr) = numbering_tree ut n0 ->
              possible_step_from_root e ut' ut ->
              exists (n1 sz': nat) (tr': numbered_tree),
                (sz', tr') = numbering_tree ut' n1 /\ possible_step_from_root e tr' tr)
    (P0 := fun br => forall (ut': unit_tree) (brn: Tree.b nat event) (n0 sz: nat) (e: event),
               (sz, brn) = numbering_branches br n0 ->
               possible_step_from_root_br e ut' br ->
               exists (n1 sz' : nat) (tr': numbered_tree),
                 (sz', tr') = numbering_tree ut' n1 /\ possible_step_from_root_br e tr' brn).
  + intros ut' tr n0 sz e Heq Hps.
    inv Heq.
    destruct (numbering_branches b (S n0))eqn:EQ1.
    apply sym_eq in EQ1.
    simpl in Hps.
    destruct (IHut ut' b0 (S n0) n e EQ1 Hps) as [n1 H].
    exists n1.
    destruct H as [sz' H].
    exists sz'.
    destruct H as [tr' H].
    exists tr'.
    destruct H as [H1 H2].
    split ; try assumption.
    inv H0.
    now simpl.
  + intros ut' brn n0 sz e _ Habs.
    inv Habs.
  + intros ut' brn n0 sz e0 Heq Hps.
    inv Heq.
    destruct (numbering_tree ut n0)eqn:EQ1.
    apply sym_eq in EQ1.
    destruct (numbering_branches b n)eqn:EQ2.
    apply sym_eq in EQ2.
    inv Hps.
    destruct H as [H1 H2] ; rewrite H1 ; rewrite H2.
    * exists n0 ; exists n ; exists t.
      split ; try assumption.
      inv H0.
      simpl.
      left ; split ; reflexivity.
    * destruct (IHut0 ut' b0 n n1 e0 EQ2 H) as [n2 H1].
      destruct H1 as [sz' H1].
      destruct H1 as [tr' H1].
      destruct H1 as [H1 H2].
      exists n2 ; exists sz' ; exists tr'.
      split ; try assumption.
      inv H0.
      simpl.
      now right.
Qed.

Lemma sim_a_numbering (p: UnitTree.prg):
  forward_simulation (UnitTree.sem p) (NumberedTree.sem (compile_unit_tree p)).
Proof.
  fwd_sim match_states_a_numbering.
  + intros s1 Hinis1.
    inv Hinis1.
    exists 0.
    eexists ; split.
    * constructor. eauto. eauto.
      unfold compile_unit_tree. simpl.
      unfold loc_tree_of_unit_tree.
      intros C tr; rewrite mapmE.
      destruct (UnitTree.prog_trees p C) eqn:E; rewrite E; simpl;
        try congruence.
      destruct (numbering_tree) eqn:X.
      move=> [] <-.
      destruct u; simpl in *. destruct numbering_branches.
      inv X; auto.
    * econstructor.
      intros C ut Hunicity.
      exists 0.
      rewrite mapmE Hunicity //=.
  + intros i s1 s2 Hs1s2 Hfins1.
    inv Hfins1.
    inv Hs1s2.
    constructor.
  + intros s1 tra s1' Hsteps1 i s2 His1s2.
    inv Hsteps1; inversion His1s2.
    exists 0.    
    destruct (TREES_COMPILED (cur_comp_of_event e) tr1 trees_cur) as [n Hcur].
    destruct (TREES_COMPILED (next_comp_of_event e) tr2 trees_next) as [m Hnext].
    destruct (numbering_tree tr1 n)eqn:EQ1.
    apply sym_eq in EQ1.
    destruct (numbering_tree tr2 m)eqn:EQ2.
    apply sym_eq in EQ2.
    simpl in *.
    destruct (numbering_tree_keep_possible_label EQ1 possible_cur) as [m1 Hcurson].
    destruct Hcurson as [sz' Hcurson].
    destruct Hcurson as [tr' Hcurson].
    destruct Hcurson as [Hcurson1 Hcurson2].
    destruct (numbering_tree_keep_possible_label EQ2 possible_next) as [l Hnextson].
    destruct Hnextson as [sz'0 Hnextson].
    destruct Hnextson as [tr'0 Hnextson].
    destruct Hnextson as [Hnextson1 Hnexston2].
    eexists.
    split.
    * left.
      econstructor.
      { econstructor ; try eauto.
        + exact (numbering_tree_unique_current EQ1 UNIQ1).
        + exact (numbering_tree_determinacy EQ1 DET1).
        + exact (numbering_tree_determinacy EQ2 DET2).
        + exact (numbering_tree_unicity EQ1).
        + exact (numbering_tree_unicity EQ2).
      }
      - eapply star_refl.
      - reflexivity.
    * constructor.
      intros C ut.
      assert (tr' = (numbering_tree tr'1 m1).2).
      {inversion Hcurson1. reflexivity. }
      assert (tr'0 = (numbering_tree tr'2 l).2).
      {inversion Hnextson1. reflexivity. }
      subst.
      (* rewrite H7 ; rewrite H8. *)
      rewrite 4!setmE.
      case: (C == next_comp_of_event e); [move=> [] -> |].
      - now exists l.
      - case: (C == cur_comp_of_event e); [move=> [] -> |].
        ++ now exists m1.
        ++ intro Heq.
           exact (TREES_COMPILED C ut Heq).
Qed.

Definition proj_stack_on (C: Component.id) (s: stack): stack :=
  filter (fun '(C', p, C'') => (C == C') || (C == C'')) s.

Lemma get_loc_numbered_to_stack_tree:
  forall tr s,
    loc tr =
      loc (loc_sproc_tree_of_loc_tree_with_acc tr s).
Proof.
  move=> [] //=.
Qed.

Lemma unique_current_numbered_to_stack_tree:
  forall C tr s,
  unique_current_tree C tr ->
  unique_current_tree C (loc_sproc_tree_of_loc_tree_with_acc tr s).
Proof.
  intros C.
  induction tr using tree_ind with
    (P := fun tr => forall s,
              unique_current_tree C tr ->
              unique_current_tree C (loc_sproc_tree_of_loc_tree_with_acc tr s))
    (P0 := fun br => forall s,
              unique_current_branches C br ->
              unique_current_branches C (loc_sproc_branch_of_loc_branch_with_acc br s)).
  - rewrite //= /loc_sproc_tree_of_loc_tree_with_acc => s uni.
  - rewrite //= /loc_sproc_tree_of_loc_tree_with_acc => s uni.
  - rewrite //= /loc_sproc_tree_of_loc_tree_with_acc => s /andP [] uni1 uni2.
    apply /andP. split; auto.
    destruct (cur_comp_of_event e == C); auto.
    destruct b; auto.
Qed.

Lemma deterministic_numbered_to_stack_tree:
  forall tr s,
    deterministic_tree tr ->
    deterministic_tree (loc_sproc_tree_of_loc_tree_with_acc tr s).
Proof.
  induction tr using tree_ind with
    (P := fun tr => forall s,
            deterministic_tree tr ->
            deterministic_tree (loc_sproc_tree_of_loc_tree_with_acc tr s))
    (P0 := fun br => forall s,
               (deterministic_branches br ->
                deterministic_branches (loc_sproc_branch_of_loc_branch_with_acc br s)) /\
               (forall e,
                   do_not_appear_in e br ->
                   do_not_appear_in e (loc_sproc_branch_of_loc_branch_with_acc br s))).
  - rewrite /loc_sproc_tree_of_loc_tree_with_acc => s uni.
    destruct b; auto.
    + constructor. constructor.
    + specialize (IHtr s) as [IH1 IH2].
      inv uni.
      constructor. eapply (IH1 H0).
  - intros s; split; intros H; constructor.
  - move=> s; split.
    + intros H; inv H.
      constructor; eauto.
      eapply IHtr0; eauto.
      eapply IHtr0; eauto.
    + intros e0 H; inv H.
      constructor; eauto.
      eapply IHtr0; eauto.
Qed.

Lemma unique_numbering_numbered_to_stack_tree:
  forall tr s,
    unique_numbering tr ->
    unique_numbering (loc_sproc_tree_of_loc_tree_with_acc tr s).
Proof.
  intros tr s.
  assert (no_occ_tree:
           forall tr s n, no_occ_of_n_in_tree n tr ->
                     forall s', no_occ_of_n_in_tree (n, s')
                             (loc_sproc_tree_of_loc_tree_with_acc tr s)).
  { clear. intros tr.
    induction tr using tree_ind with
      (P := fun tr => forall s n, no_occ_of_n_in_tree n tr ->
                   forall s', no_occ_of_n_in_tree (n, s')
                           (loc_sproc_tree_of_loc_tree_with_acc tr s))
      (P0 := fun br => forall s n, no_occ_of_n_in_branches n br ->
                    forall s', no_occ_of_n_in_branches (n, s')
                           (loc_sproc_branch_of_loc_branch_with_acc br s)).
    - intros s n H s'.
      inv H; constructor; [simpl; congruence |].
      eapply IHtr; eauto.
    - intros s n H s'.
      inv H; constructor.
    - intros s n H s'.
      inv H.
      constructor.
      + eapply IHtr0; eauto.
      + simpl.
        fold (loc_sproc_tree_of_loc_tree_with_acc).
        destruct e; auto.
  }

  assert (no_occ_branch:
           forall br s n, no_occ_of_n_in_branches n br ->
                     forall s', no_occ_of_n_in_branches (n, s')
                             (loc_sproc_branch_of_loc_branch_with_acc br s)).
  { clear. intros br.
    induction br using branches_ind with
      (P := fun tr => forall s n, no_occ_of_n_in_tree n tr ->
                   forall s', no_occ_of_n_in_tree (n, s')
                           (loc_sproc_tree_of_loc_tree_with_acc tr s))
      (P0 := fun br => forall s n, no_occ_of_n_in_branches n br ->
                    forall s', no_occ_of_n_in_branches (n, s')
                           (loc_sproc_branch_of_loc_branch_with_acc br s)).
    - intros s n H s'.
      inv H; constructor; [simpl; congruence |].
      eapply IHbr; eauto.
    - intros s n H s'.
      inv H; constructor.
    - intros s n H s'.
      inv H.
      constructor.
      + eapply IHbr0; eauto.
      + simpl.
        fold (loc_sproc_tree_of_loc_tree_with_acc).
        destruct e; auto.
  }


  assert (unique_tree:
           forall tr s,
             (forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr) ->
             (forall n, no_occ_of_n_in_tree n (loc_sproc_tree_of_loc_tree_with_acc tr s) \/
                     unique_occ_of_n_in_tree n (loc_sproc_tree_of_loc_tree_with_acc tr s))).
  { clear -no_occ_tree no_occ_branch.
    intros tr s ? [n s'].
    specialize (H n) as [H | H]; [left; apply no_occ_tree; auto |].
    right.
    revert s n s' H.
    induction tr using tree_ind with
      (P := fun tr => forall s n s',
                unique_occ_of_n_in_tree n tr ->
                unique_occ_of_n_in_tree (n, s') (loc_sproc_tree_of_loc_tree_with_acc tr s))
      (P0 := fun br => forall s n s',
                 unique_occ_of_n_in_branches n br ->
                 unique_occ_of_n_in_branches (n, s') (loc_sproc_branch_of_loc_branch_with_acc br s)).
   - intros.
     inv H.
     + left; auto.
     + right. auto.
       (* inv H. *)
       apply IHtr; auto.
   - intros. inv H.
   - intros. inv H.
     + left; eauto.
     + right; eauto.
  }
  intros H. inv H.
  constructor. eauto.
Qed.

Lemma stack_tree_possible_step_call:
  forall (s: stack) (tr1: numbered_tree) (tr1': stack_tree) (tr2: numbered_tree)
    Ccur Cnext Pnext z,
    tr1' = loc_sproc_tree_of_loc_tree_with_acc tr1 s ->
    possible_step_from_root (ECall Ccur Pnext z Cnext) tr2 tr1 ->
    exists (tr2': stack_tree),
      tr2' = loc_sproc_tree_of_loc_tree_with_acc tr2 ((Ccur, Pnext, Cnext) :: s) /\
        possible_step_from_root (ECall Ccur Pnext z Cnext) tr2' tr1'.
Proof.
  move=> s [] n children tr1' tr2 Ccur Cnext Pnext z ->.
  rewrite /possible_step_from_root.
  elim: children => //=.
  move=> e tr children IH.
  case.
  - move=> [] <- ->.
    eexists (loc_sproc_tree_of_loc_tree_with_acc tr (_ :: s)).
    split; [| left; split]; auto.
  - move=> /IH [] _ [] -> G.
    eexists (loc_sproc_tree_of_loc_tree_with_acc tr2 (_ :: s)).
    split; [| right]; auto.
Qed.

Lemma stack_tree_possible_step_ret:
  forall (s: stack) (tr1: numbered_tree) (tr1': stack_tree) (tr2: numbered_tree)
    Ccur Cnext z,
    tr1' = loc_sproc_tree_of_loc_tree_with_acc tr1 s ->
    possible_step_from_root (ERet Ccur z Cnext) tr2 tr1 ->
    exists (tr2': stack_tree),
      tr2' = loc_sproc_tree_of_loc_tree_with_acc tr2 (behead s) /\
        possible_step_from_root (ERet Ccur z Cnext) tr2' tr1'.
Proof.
  move=> s [] n children tr1' tr2 Ccur Cnext z ->.
  rewrite /possible_step_from_root.
  elim: children => //=.
  move=> e tr children IH.
  case.
  - move=> [] <- ->.
    exists (loc_sproc_tree_of_loc_tree_with_acc tr (behead s)).
    split; [| left; split]; auto.
  - move=> /IH [] _ [] -> G.
    exists (loc_sproc_tree_of_loc_tree_with_acc tr2 (behead s)).
    split; [| right]; auto.
Qed.

Fixpoint wf_stack_trace (tra: trace) (st: stack): bool :=
  match tra with
  | [] => true
  | ECall Ccur P z Cnext :: tra' => wf_stack_trace tra' ((Ccur, P, Cnext) :: st)
  | ERet Ccur z Cnext :: tra' =>
      match st with
      | (Cnext', _, Ccur') :: st' =>
          (Ccur == Ccur') && (Cnext == Cnext') && wf_stack_trace tra' st'
      | _ => false
      end
  end.

Inductive match_states_b_stacking (i: nat) : NumberedTree.state -> StackTree.state -> Prop :=
| match_states_2:
  forall (tra : trace) (trees: NMap numbered_tree) (trees': NMap stack_tree) (locs : NMap nat) st,
  forall (TREES_COMPILED:
      forall C nt, trees C = Some nt ->
             trees' C = Some (loc_sproc_tree_of_loc_tree_with_acc nt (proj_stack_on C st))),
  forall (STACK: wf_stack_trace tra st),
    match_states_b_stacking i (tra, trees, locs) (tra, trees', locs, st)
.

Lemma wf_trace_wf_stack_trace: forall intf tra,
    wf_trace intf tra -> wf_stack_trace tra [::].
Proof.
  move=> intf tra [] wb_tra [] _ _. move: wb_tra.
  have: (([::]: seq (Component.id * Component.id)) = map (fun x => (x.1.1, x.2)) ([::]: stack)) => [//= |] EQ.
  rewrite EQ.
  move: EQ.
  elim: tra [::] [::] => //= e t IH.
  case: e => //=.
  - move=> Ccur P z Cnext l //= lo EQ.
    have EQ': ((Ccur, Cnext) :: lo = [seq (x.1.1, x.2) | x <- (Ccur, P, Cnext) :: l]).
    rewrite EQ; by [].
    move /(IH ((Ccur, P, Cnext) :: l) ((Ccur, Cnext) :: lo) EQ') => //=.
  - move=> Ccur z Cnext [] //=.
    move=> [] [] //= Cnext' Pnext Ccur' ? ? EQ [] ? [] ? /IH //= H.
    apply /andP; split; [apply /andP; split |].
    + by [].
    + by [].
    + eapply H; eauto.
Qed.

Lemma sim_b_stacking (p: NumberedTree.prg):
  forward_simulation (NumberedTree.sem p) (StackTree.sem (compile_numbered_tree p)).
Proof.
  fwd_sim match_states_b_stacking.
  - intros. inv H.
    exists 0.
    eexists; split; eauto.
    + constructor; eauto. unfold compile_numbered_tree. simpl.
      move=> C. move: (H2 C).
      rewrite /loc_sproc_tree_of_loc_tree //= mapmE.
      case: (NumberedTree.prog_trees p C) => //=.
      move=> [] a b /(_ _ Logic.eq_refl) -> //=.
      move=> ? [] <- //=.
    + constructor; eauto.
      intros. unfold compile_numbered_tree. simpl.
      rewrite mapmE H; simpl.
      by rewrite /proj_stack_on /loc_sproc_tree_of_loc_tree //=.
      eapply wf_trace_wf_stack_trace; eauto.
  - intros. inv H. inv H0. constructor; eauto.
  - intros ((tra1 & trees1) & locs1) t ((tra2 & trees2) & locs2).
    intros STEP; inv STEP.
    intros i (((tra1' & trees1') & locs1') & stack1') MS.
    inv MS.
    destruct e as [Ccur Pnext z Cnext | Ccur z Cnext].
    + eapply stack_tree_possible_step_call in possible_cur as [tr2' [? ?]]; eauto.
      eapply stack_tree_possible_step_call in possible_next as [tr2'' [? ?]]; eauto.
      exists 0. eexists; split.
      * left; eapply plus_one.
        econstructor; eauto.
        -- eapply unique_current_numbered_to_stack_tree; eauto.
        -- eapply deterministic_numbered_to_stack_tree; eauto.
        -- eapply deterministic_numbered_to_stack_tree; eauto.
        -- eapply unique_numbering_numbered_to_stack_tree; eauto.
        -- eapply unique_numbering_numbered_to_stack_tree; eauto.
      * subst.
        rewrite -!get_loc_numbered_to_stack_tree.
        econstructor.
        -- move=> C nt. rewrite !setmE.
           case: (C == Cnext)/eqP => [-> [] ->| C_Cnext] //=.
           rewrite /proj_stack_on //= eqxx orbT //=.
           move: C_Cnext.
           case: (C == Ccur)/eqP => [-> C_Cnext [] ->| C_Ccur] //=.
           move /eqP/negPf ->. apply TREES_COMPILED.
        -- eauto.
    + destruct stack1' as [| [[Cnext' Pcur] Ccur'] stack1']; [by [] |].
      move: STACK => /andP [] /andP [] /eqP ? /eqP ?; subst Ccur' Cnext'; move=> STACK.
      eapply stack_tree_possible_step_ret in possible_cur as [tr2' [? ?]]; eauto.
      eapply stack_tree_possible_step_ret in possible_next as [tr2'' [? ?]]; eauto.
      exists 0. eexists; split.
      * left; eapply plus_one.
        eapply StackTree.step_return; eauto.
        -- eapply unique_current_numbered_to_stack_tree; eauto.
        -- eapply deterministic_numbered_to_stack_tree; eauto.
        -- eapply deterministic_numbered_to_stack_tree; eauto.
        -- eapply unique_numbering_numbered_to_stack_tree; eauto.
        -- eapply unique_numbering_numbered_to_stack_tree; eauto.
      * subst.
        rewrite -!get_loc_numbered_to_stack_tree.
        econstructor; eauto.
        move=> C nt. rewrite !setmE.
        case: (C == Cnext)/eqP => [-> [] ->| C_Cnext] //=.
        rewrite /proj_stack_on //= eqxx //=.
        move: C_Cnext.
        case: (C == Ccur)/eqP => [-> C_Cnext [] ->| C_Ccur] //=.
        move: C_Cnext => /eqP/negPf -> //=.
        rewrite /proj_stack_on eqxx //= => -> //=.
        move=> C_Cnext /TREES_COMPILED ->.
        move: C_Cnext => /eqP/negPf. move: C_Ccur => /eqP/negPf.
        rewrite /proj_stack_on //= => -> -> //=.
Qed.

(* Definition all_in (p: Flattened.prg) (trees: NMap stack_tree) := *)
(*   forall C tr e tr' cs, trees C = Some tr -> *)
(*                    Flattened.prog_procedures p C = Some cs -> *)
(*                    possible_step_from_root e tr' tr -> *)
(*                    In (loc tr, e, loc tr') cs. *)

Inductive all_in_tree: seq (nat * event * nat) -> stack_tree -> Prop :=
  | all_in_node: forall cs br a,
      all_in_branches cs (loc a) br ->
      all_in_tree cs (node a br)
with all_in_branches: seq (nat * event * nat) -> nat -> b loc_stack event -> Prop :=
  | all_in_bnil: forall cs n,
      all_in_branches cs n (Bnil _ _)
  | all_in_bcons: forall cs n tr e br',
      all_in_tree cs tr ->
      all_in_branches cs n br' ->
      In (n, e, loc tr) cs ->
      all_in_branches cs n (Bcons e tr br').

Definition all_in (p: Flattened.prg) (trees: NMap stack_tree) :=
  forall C tr,
    trees C = Some tr ->
    exists cs, Flattened.prog_procedures p C = Some cs /\ all_in_tree cs tr.

Definition locs_ok (trees: NMap stack_tree) (locs: NMap nat) :=
  forall C tr,
    trees C = Some tr ->
    locs C = Some (loc tr).

Inductive match_states_c_flattening (p': Flattened.prg) (i: nat) : StackTree.state -> Flattened.state -> Prop :=
| match_states_ini:
  forall (tra : trace) (trees: NMap stack_tree),
  forall (ALL_IN: all_in p' trees)
    (LOCS_OK: locs_ok trees (mkfmapf (fun=> 0) (domm (Flattened.prog_interface p')))),
    match_states_c_flattening p' i (tra, trees, mkfmapf (fun=> 0) (domm (Flattened.prog_interface p')), [::]) (inl tra)
| match_states_3:
  forall (tra : trace) (trees: NMap stack_tree) (locs : NMap nat) st,
  forall (ALL_IN: all_in p' trees)
    (LOCS_OK: locs_ok trees locs),
    match_states_c_flattening p' i (tra, trees, locs, st) (inr (tra, locs, st))
.


Lemma x:
  forall tr tr' e cs,
  possible_step_from_root e tr' tr ->
  all_in_tree cs tr ->
  In (loc tr, e, loc tr') cs /\ all_in_tree cs tr'.
Proof.
  intros tr.
  induction tr using tree_ind with
    (P := fun tr => forall tr' e cs,
               possible_step_from_root e tr' tr ->
               all_in_tree cs tr ->
               In (loc tr, e, loc tr') cs /\ all_in_tree cs tr')
    (P0 := fun br => forall tr' n e cs,
               possible_step_from_root_br e tr' br ->
               all_in_branches cs n br ->
               In (n, e, loc tr') cs /\ all_in_tree cs tr').
  - intros.
    simpl in H.
    exploit IHtr; eauto. inv H0. eauto.
  - intros. simpl in *. by [].
  - intros. destruct H as [[] |]; subst.
    + inv H0; eauto.
    + eapply IHtr0; eauto. inv H0; eauto.
Qed.

Lemma all_in_tree_app:
  forall tr l l',
    all_in_tree l tr ->
    all_in_tree (l ++ l') tr.
Proof.
  induction tr using tree_ind with
    (P := fun tr => forall l l',
              all_in_tree l tr ->
              all_in_tree (l ++ l') tr)
    (P0 := fun br => forall l l' n,
               all_in_branches l n br ->
               all_in_branches (l ++ l') n br).
  - intros. constructor; inv H.
    eapply IHtr; eauto.
  - intros. constructor; inv H.
  - intros.
    constructor; inv H.
    + eapply IHtr; eauto.
    + eapply IHtr0; eauto.
    + eapply in_or_app; eauto.
Qed.

Lemma all_in_tree_app':
  forall tr l l',
    all_in_tree l' tr ->
    all_in_tree (l ++ l') tr.
Proof.
  induction tr using tree_ind with
    (P := fun tr => forall l l',
              all_in_tree l' tr ->
              all_in_tree (l ++ l') tr)
    (P0 := fun br => forall l l' n,
               all_in_branches l' n br ->
               all_in_branches (l ++ l') n br).
  - intros. constructor; inv H.
    eapply IHtr; eauto.
  - intros. constructor; inv H.
  - intros.
    constructor; inv H.
    + eapply IHtr; eauto.
    + eapply IHtr0; eauto.
    + eapply in_or_app; eauto.
Qed.

Lemma all_in_branches_app:
  forall br n l l',
    all_in_branches l' n br ->
    all_in_branches (l ++ l') n br.
Proof.
  induction br using branches_ind with
    (P := fun tr => forall l l',
              all_in_tree l' tr ->
              all_in_tree (l ++ l') tr)
    (P0 := fun br => forall n l l',
               all_in_branches l' n br ->
               all_in_branches (l ++ l') n br).
  - intros. constructor; inv H.
    eapply IHbr; eauto.
  - intros. constructor; inv H.
  - intros.
    constructor; inv H.
    + eapply IHbr; eauto.
    + eapply IHbr0; eauto.
    + eapply in_or_app; eauto.
Qed.

Lemma all_in_branches_app':
  forall br n l l',
    all_in_branches l n br ->
    all_in_branches (l ++ l') n br.
Proof.
  induction br using branches_ind with
    (P := fun tr => forall l l',
              all_in_tree l tr ->
              all_in_tree (l ++ l') tr)
    (P0 := fun br => forall n l l',
               all_in_branches l n br ->
               all_in_branches (l ++ l') n br).
  - intros. constructor; inv H.
    eapply IHbr; eauto.
  - intros. constructor; inv H.
  - intros.
    constructor; inv H.
    + eapply IHbr; eauto.
    + eapply IHbr0; eauto.
    + eapply in_or_app; eauto.
Qed.

Lemma sim_c_flattening (p: StackTree.prg) (wf_p: StackTree.wf p):
  forward_simulation (StackTree.sem p) (Flattened.sem (compile_stack_tree p)).
Proof.
  fwd_sim (match_states_c_flattening (compile_stack_tree p)).
  - intros. inv H.
    exists 0; eexists; split; constructor; eauto.
    + unfold all_in. clear -wf_p.
      { move=> C tr //=; rewrite mapmE => -> //=.
        eexists. split; eauto.
        induction tr using tree_ind with
          (P := fun tr => all_in_tree (BacktranslationCompilers.flatten tr).2 tr)
          (P0 := fun br => forall n,
                     all_in_branches
                          (BacktranslationCompilers.flatten_br n br)
                          n
                          br).
        - case: a => //=. - move=> n //=. constructor.
        - move=> n //=.
          destruct (BacktranslationCompilers.flatten tr) eqn:E; simpl in *.
          constructor.
          + clear -IHtr.
            replace ((n, e, n0) :: l ++ flatten_br n b)
              with ([(n, e, n0)] ++ l ++ flatten_br n b).
            eapply all_in_tree_app'; eauto.
            eapply all_in_tree_app; eauto.
            reflexivity.
          + clear -IHtr0. specialize (IHtr0 n).
            replace ((n, e, n0) :: l ++ flatten_br n b)
              with (([(n, e, n0)] ++ l) ++ flatten_br n b).
            eapply all_in_branches_app; eauto.
            reflexivity.
            (* replace ((n, e, n0) :: flatten_br n b) *)
            (*           with ([(n, e, n0)] ++ flatten_br n b) *)
            (*   by reflexivity. *)
            (* eapply all_in_branches_app; eauto. *)
          + assert (loc tr = n0).
            { unfold BacktranslationCompilers.flatten in E.
              destruct tr as [[] ?]; simpl in *.
              inv E. auto. }
            constructor. auto.
            (* replace ((n, e, n0) :: l ++ flatten_br n b) *)
            (*   with (([(n, e, n0)] ++ l) ++ flatten_br n b). *)
            (* eapply in_or_app. right. *)
            (* constructor. auto. *)
      }
    + unfold locs_ok.
      apply StackTree.wfprog_defined_procedures in wf_p.
      move=> C; move: (H2 C).
      rewrite mkfmapfE. simpl. rewrite wf_p.
      rewrite mem_domm.
      case: (StackTree.prog_trees p C) => //=.
      move=> [] a b /(_ _ Logic.eq_refl) a_1 ? [] <-.
      by rewrite a_1.
  - intros. inv H. inv H0; constructor; eauto.
    inv H0; econstructor; eauto.
  - intros (((tra1 & trees1) & locs1) & st1) tra
           (((tra1' & trees1') & locs1') & st1').
    intros STEP; inv STEP.
    + intros i s2 MS.
      assert (H: exists tra2 locs2 st2,
                 Star (Flattened.sem (compile_stack_tree p)) s2 [::] (inr (tra2, locs2, st2)) /\
                 match_states_c_flattening (compile_stack_tree p) i (ECall C1 P z C2 :: tra1', trees1, locs1, st1) (inr (tra2, locs2, st2))).
      { inv MS; [| eexists; eexists; eexists; split; econstructor; eauto].
        eexists; eexists; eexists; split.
        eapply star_one; eauto. constructor; eauto. simpl. simpl in LOCS_OK. econstructor; eauto. }
      clear MS.
      destruct H as [tra2 [locs2 [st2 [STAR0 MS]]]].
      inv MS.
      unfold all_in in ALL_IN.
      destruct (ALL_IN _ _ trees_cur) as [cs_cur [procs_cur all_in_cur]].
      destruct (ALL_IN _ _ trees_next) as [cs_next [procs_next all_in_next]].

      unfold locs_ok in LOCS_OK.
      specialize (LOCS_OK _ _ trees_cur) as loc_cur.
      specialize (LOCS_OK _ _ trees_next) as loc_next.

      pose proof (@x _ _ _ _ possible_cur all_in_cur) as [in_cur all_in_cur'].
      pose proof (@x _ _ _ _ possible_next all_in_next) as [in_next all_in_next'].
      exists 0. eexists; split; eauto.
      * left; eapply star_plus_trans.
        eauto.
        eapply plus_one.
        econstructor; eauto. traceEq.
      * econstructor.
        -- rewrite /all_in => C; rewrite !setmE.
           case: (C == C2) /eqP => [-> ? [] <- | _] //=.
           eexists; split; eauto.
           case: (C == C1) /eqP => [-> ? [] <- | _] //=.
           eexists; split; eauto.
           intros; eauto.
        -- rewrite /locs_ok => C; rewrite !setmE.
           case: (C == C2) => //= [? [] <- //=|].
           case: (C == C1) => //= [? [] <- //=|].
           eapply LOCS_OK.
    + intros i [| ((tra2 & locs2) & st2)] MS; try now inv MS.
      inv MS.
      unfold all_in in ALL_IN.
      destruct (ALL_IN _ _ trees_cur) as [cs_cur [procs_cur all_in_cur]].
      destruct (ALL_IN _ _ trees_next) as [cs_next [procs_next all_in_next]].

      unfold locs_ok in LOCS_OK.
      specialize (LOCS_OK _ _ trees_cur) as loc_cur.
      specialize (LOCS_OK _ _ trees_next) as loc_next.

      pose proof (@x _ _ _ _ possible_cur all_in_cur) as [in_cur all_in_cur'].
      pose proof (@x _ _ _ _ possible_next all_in_next) as [in_next all_in_next'].
      exists 0. eexists; split; eauto.
      * left; eapply plus_one.
        eapply Flattened.step_return; eauto.
      * econstructor.
        -- rewrite /all_in => C; rewrite !setmE.
           case: (C == C2) /eqP => [-> ? [] <- | _] //=.
           eexists; split; eauto.
           case: (C == C1) /eqP => [-> ? [] <- | _] //=.
           eexists; split; eauto.
           intros; eauto.
        -- rewrite /locs_ok => C; rewrite !setmE.
           case: (C == C2) => //= [? [] <- //=|].
           case: (C == C1) => //= [? [] <- //=|].
           eapply LOCS_OK.
Qed.

(* Axiom Kafter_call: cont. *)
Definition Kafter_call Ccur Pcur : cont :=
  Kassign1 (E_binop Add E_local (E_val (Int 2)))
    (Kseq
       (E_seq
          (E_assign (E_binop Add E_local (E_val (Int 1)))
             (E_val (Int 0))) (E_call Ccur Pcur (E_val (Int 0))))
    Kstop).

Inductive match_concrete_stacks: Component.id -> stack -> CS.stack -> Prop :=
| match_concrete_stacks_nil: forall C, match_concrete_stacks C [] []
| match_concrete_stacks_int: forall C s st old_arg,
    match_concrete_stacks C s st ->
    match_concrete_stacks C s (CS.Frame C old_arg Kstop :: st)
| match_concrete_stacks_ext: forall C C' s st old_arg P,
    C <> C' ->
    match_concrete_stacks C' s st ->
    match_concrete_stacks C
      ((C', P, C) :: s)
      (* (new_frame C' 0 old_arg Kstop :: st) *)
      (CS.Frame C' old_arg (Kafter_call C' 0) :: st)
.

Lemma unfold_stack: forall ge C1 P C2 st stack m z arg,
    match_concrete_stacks C1 ((C2, P, C1) :: st) stack ->
    exists stack' stack'' arg' arg'',
      stack' = CS.Frame C2 arg' (Kafter_call C2 0) :: stack''
      /\ match_concrete_stacks C2 st stack''
      /\ star CS.kstep ge [CState C1, stack, m, Kstop, E_val (Int z), arg] E0
             [CState C1, stack', m, Kstop, E_val (Int z), arg''].
Proof.
  move=> ge C1 P C2 st stack m z arg H.
  remember ((C2, P, C1) :: st) as st0.
  generalize dependent arg.
  induction H; intros.
  - inversion Heqst0.
  - specialize (IHmatch_concrete_stacks Heqst0) as
        [stack1 [stack2 [arg1 [arg2 [IH1 [IH2 IH3]]]]]].
    subst.
    eexists; eexists; eexists; eexists.
    simpl. split; last split.
    + eauto.
    + eauto.
    + take_step. eauto. eapply IH3.
  - inv Heqst0.
    eexists; eexists; eexists; eexists.
    simpl. split; last split.
    + eauto.
    + eauto.
    + eapply star_refl.
Qed.

Definition match_mem (locs: NMap nat) (mem: Memory.t) :=
  forall C n,
    locs C = Some n ->
    Memory.load mem (C, Block.local, 0%Z) = Some (Int (Z.of_nat n))
    /\ Memory.load mem (C, Block.local, 1%Z) = Some (Int 1%Z)
    /\ (exists v, Memory.load mem (C, Block.local, 2%Z) = Some v).

Definition cur_comp_of_trace (t: trace) :=
  match t with
  | nil => Component.main
  | e :: t => cur_comp_of_event e
  end.


Inductive match_states_d_to_source (p: Flattened.prg) (tp: program) (i: nat): Flattened.state -> CS.state -> Prop :=
| match_states4_init: forall s tra,
    CS.initial_state tp s ->
    tra <> [::] ->
    Component.main = cur_comp_of_trace tra ->
    match_states_d_to_source p tp i (inl tra) s
| match_states4_cons: forall t locs st C cst mem e v es,
    forall (MS_ST: match_concrete_stacks C st cst)
      (MS_MEM: match_mem locs mem)
      (ES: Flattened.genv_procedures (globalenv (Flattened.sem p)) C = Some es),
      (t <> [::] -> C = cur_comp_of_trace t) ->
      e = (switch_outgoing C es E_exit) ->
      forall (NOT_FINAL: t <> [::]),
      match_states_d_to_source p tp i (inr (t, locs, st)) (CS.State C cst mem Kstop e v)
| match_final: forall locs st C cst mem k e v,
  match_states_d_to_source p tp i (inr ([::], locs, st)) (CS.State C cst mem k e v)
.

Lemma switch_outgoing_calls_correct:
  forall p cs1 C1 C2 n1 n1' P2 cst k mem z v E,
    Memory.load mem (C1, Block.local, 0%Z) = Some (Int (Z.of_nat n1)) ->
    unicity_in2 (outgoing C1 cs1) ->
    In (n1, ECall C1 P2 z C2, n1') cs1 ->
    Star (CS.sem p) [CState C1, cst, mem, k,
        switch_outgoing C1 cs1 E, v]
      E0
      [CState C1, cst, mem, k, call_expr C1 C2 0 P2 n1' z, v].
Proof.
  move=> p cs1 C1 C2 n1 n1' P2 cst k mem z v E Hload unic Hin.
  assert (Hin': In (n1, inl (C2, P2, z), n1') (outgoing C1 cs1)).
  { clear -Hin. revert Hin.
    induction cs1; intros.
    - inv Hin.
    - destruct Hin.
      + subst. simpl; rewrite eqxx /=. now left.
      + destruct a as ((? & []) & ?).
        * simpl. case: ifP => /eqP ?; subst; simpl; try right; eauto.
        * simpl. case: ifP => /eqP ?; subst; simpl; try right; eauto.
  }
  clear Hin. rename Hin' into Hin.
  revert unic Hin. unfold switch_outgoing.
  generalize (outgoing C1 cs1).
  induction l; intros.
  - inv Hin.
  - destruct a as ((? & d) & ?); simpl in *.
    destruct d.
    2: {
      eapply switch_clause_spec with (n' := Z.of_nat n) in Hload; eauto.
      assert (n <> n1). {
        intros ?; subst n1.
        destruct Hin as [Hin | Hin]; try now inv Hin.
        specialize (unic n (inr z0) (inl (C2, P2, z)) n0 n1').
        exploit unic; eauto. left; eauto. right; eauto.
        intros []; congruence.
      }
      assert (n_n1: (Z.of_nat n1 =? Z.of_nat n)%Z = false).
      { clear -H. apply /Z.eqb_spec. intros N.
        apply H.
        replace n with (Z.to_nat (Z.of_nat n)).
        replace n1 with (Z.to_nat (Z.of_nat n1)).
        rewrite N; congruence.
        apply Nat2Z.id.
        apply Nat2Z.id. }
      rewrite n_n1 in Hload.
      eapply star_trans.
      eapply Hload. eapply IHl.
      eapply unicity_in2_smaller; eauto.
      destruct Hin; eauto.
      assert (n1 <> n). {
        intros ?; subst. inv H0. }
      congruence.
      traceEq.
    }
    destruct p0 as [[i i0] z0].
    eapply switch_clause_spec with (n' := Z.of_nat n) in Hload; eauto.
    destruct (Z.of_nat n1 =? Z.of_nat n)%Z eqn:?. simpl in *.
    + move: Heqb => /Z.eqb_spec n1_n.
      assert (n1 = n). {
        clear -n1_n.
        replace n with (Z.to_nat (Z.of_nat n)).
        replace n1 with (Z.to_nat (Z.of_nat n1)).
        rewrite n1_n. eauto.
        apply Nat2Z.id.
        apply Nat2Z.id. }
      subst.
      assert ((n, @inl _ Z (i, i0, z0), n0) = (n, inl (C2, P2, z), n1')).
      { destruct Hin as [? | Hin]; auto.
        clear -unic Hin.
        edestruct unic; eauto.
        left. eauto. right. eauto. subst. congruence. }
      assert (i = C2) by congruence.
      assert (i0 = P2) by congruence.
      assert (z0 = z) by congruence.
      assert (n0 = n1') by congruence. subst.
      eauto.
    + eapply star_trans.
      eapply Hload. eapply IHl.
      eapply unicity_in2_smaller; eauto.
      destruct Hin; eauto.
      assert (n1 <> n). {
        intros ?; subst.
        move: Heqb => /Z.eqb_spec. auto. }
        congruence.
      traceEq.
Qed.

Lemma switch_outgoing_returns_correct:
  forall p cs1 C1 C2 n1 n1' cst k mem z v E,
    Memory.load mem (C1, Block.local, 0%Z) = Some (Int (Z.of_nat n1)) ->
    unicity_in2 (outgoing C1 cs1) ->
    In (n1, ERet C1 z C2, n1') cs1 ->
    Star (CS.sem p) [CState C1, cst, mem, k,
        switch_outgoing C1 cs1 E, v]
      E0
      [CState C1, cst, mem, k, ret_expr n1' z, v].
Proof.
  move=> p cs1 C1 C2 n1 n1' cst k mem z v E Hload unic Hin.
  assert (Hin': In (n1, inr z, n1') (outgoing C1 cs1)).
  { clear -Hin. revert Hin.
    induction cs1; intros.
    - inv Hin.
    - destruct Hin.
      + subst. simpl; rewrite eqxx /=. now left.
      + destruct a as ((? & []) & ?).
        * simpl. case: ifP => /eqP ?; subst; simpl; try right; eauto.
        * simpl. case: ifP => /eqP ?; subst; simpl; try right; eauto.
  }
  clear Hin. rename Hin' into Hin.
  revert unic Hin. unfold switch_outgoing.
  generalize (outgoing C1 cs1).
  induction l; intros.
  - inv Hin.
  - destruct a as ((? & d) & ?); simpl in *.
    destruct d.
    {
      destruct p0 as [[? ?] ?].
      eapply switch_clause_spec with (n' := Z.of_nat n) in Hload; eauto.
      assert (n <> n1). {
        intros ?; subst n1.
        destruct Hin as [Hin | Hin]; try now inv Hin.
        specialize (unic n (inl (i, i0, z0)) (inr z) n0 n1').
        exploit unic; eauto. left; eauto. right; eauto.
        intros []; congruence.
      }
      assert (n_n1: (Z.of_nat n1 =? Z.of_nat n)%Z = false).
      { clear -H. apply /Z.eqb_spec. intros N.
        apply H.
        replace n with (Z.to_nat (Z.of_nat n)).
        replace n1 with (Z.to_nat (Z.of_nat n1)).
        rewrite N; congruence.
        apply Nat2Z.id.
        apply Nat2Z.id. }
      rewrite n_n1 in Hload.
      eapply star_trans.
      eapply Hload. eapply IHl.
      eapply unicity_in2_smaller; eauto.
      destruct Hin; eauto.
      assert (n1 <> n). {
        intros ?; subst. inv H0. }
      congruence.
      traceEq.
    }
    eapply switch_clause_spec with (n' := Z.of_nat n) in Hload; eauto.
    destruct (Z.of_nat n1 =? Z.of_nat n)%Z eqn:?. simpl in *.
    + move: Heqb => /Z.eqb_spec n1_n.
      assert (n1 = n). {
        clear -n1_n.
        replace n with (Z.to_nat (Z.of_nat n)).
        replace n1 with (Z.to_nat (Z.of_nat n1)).
        rewrite n1_n. eauto.
        apply Nat2Z.id.
        apply Nat2Z.id. }
      subst.
      assert ((n, @inr (Component.id * Procedure.id * Z) _ z0, n0) = (n, inr z, n1')).
      { destruct Hin as [? | Hin]; auto.
        clear -unic Hin.
        edestruct unic; eauto.
        left. eauto. right. eauto. subst. congruence. }
      assert (z0 = z) by congruence.
      assert (n0 = n1') by congruence. subst.
      eauto.
    + eapply star_trans.
      eapply Hload. eapply IHl.
      eapply unicity_in2_smaller; eauto.
      destruct Hin; eauto.
      assert (n1 <> n). {
        intros ?; subst.
        move: Heqb => /Z.eqb_spec. auto. }
        congruence.
      traceEq.
Qed.



Lemma switch_incoming_calls_correct: forall p cs2 C1 C2 n2 n2' P2 cst k mem z,
  Memory.load mem (C2, Block.local, 0%Z) = Some (Int (Z.of_nat n2)) ->
  unicity_in (incoming_calls C2 P2 cs2) ->
  In (n2, ECall C1 P2 z C2, n2') cs2 ->
  Star (CS.sem p) [CState C2, cst, mem, k,
      switch_incoming_calls C2 P2 cs2, Int z]
    E0
    [CState C2, cst, mem, k, update_loc n2', Int z].
Proof.
  move=> p cs2 C1 C2 n2 n2' P2 cst k mem z Hload unic Hin.
  assert (Hin': In (n2, z, n2') (incoming_calls C2 P2 cs2)).
  { clear -Hin. revert Hin.
    induction cs2; intros.
    - inv Hin.
    - destruct Hin.
      + subst. simpl; rewrite !eqxx /=. now left.
      + destruct a as ((? & []) & ?).
        * simpl. case: ifP => /eqP ?; subst; simpl; try right; eauto.
        * simpl. eauto. }
  clear Hin. rename Hin' into Hin.
  revert unic Hin. unfold switch_incoming_calls.
  generalize (incoming_calls C2 P2 cs2).
  induction l; intros.
  - inv Hin.
  - destruct a as ((? & ?) & ?); simpl in *.
    eapply switch2_clause_spec with (stk := cst) (e_then := update_loc n0) (n1' := Z.of_nat n) (z := z) (z' := z0) in Hload; eauto.
    (* rewrite Z.eqb_refl in Hload. *)
    destruct (Z.of_nat n2 =? Z.of_nat n)%Z eqn:?. simpl in *.
    + move: Heqb => /Z.eqb_spec n1_n.
      assert (n2 = n). {
        clear -n1_n.
        replace n with (Z.to_nat (Z.of_nat n)).
        replace n2 with (Z.to_nat (Z.of_nat n2)).
        rewrite n1_n. eauto.
        apply Nat2Z.id.
        apply Nat2Z.id. }
      subst n2.
      destruct (z =? z0)%Z eqn:?. simpl in *.
      * subst.
        move: Heqb => /Z.eqb_spec. intros ?; subst.
        assert ((n, z0, n0) = (n, z0, n2')).
        { destruct Hin as [? | Hin]; auto.
          clear -unic Hin.
          unfold unicity_in in unic.
          specialize (unic (n, z0) n0 n2').
          erewrite unic; eauto.
          left. eauto. right. eauto. }
        assert (n0 = n2') by congruence. subst.
        eauto.
      * eapply star_trans.
        eapply Hload. eapply IHl.
        eapply unicity_in_smaller; eauto.
        destruct Hin; eauto.
        assert ((n, z) <> (n, z0)). {
          intros ?; subst.
          move: Heqb => /Z.eqb_spec. congruence. }
        congruence.
        traceEq.
    + eapply star_trans.
      eapply Hload. eapply IHl.
      eapply unicity_in_smaller; eauto.
      clear Hload.
      destruct Hin; eauto.
      assert ((n, z0) <> (n2, z)). {
        intros ?; subst.
        move: Heqb => /Z.eqb_spec. congruence. }
      congruence.
      traceEq.
Qed.

Lemma switch_incoming_calls_correct': forall p cs2 C2 P2 cst k mem z,
  Memory.load mem (C2, Block.local, 0%Z) = Some (Int (-1)) ->
  Star (CS.sem p) [CState C2, cst, mem, k,
      switch_incoming_calls C2 P2 cs2, Int z]
    E0
    [CState C2, cst, mem, k, update_loc 0, Int z].
Proof.
  move=> p cs2 C2 P2 cst k mem z H.
  unfold switch_incoming_calls.
  generalize (incoming_calls C2 P2 cs2).
  induction l; intros.
  - simpl. eapply star_refl.
  - destruct a as ((? & ?) & ?); simpl in *.
    eapply switch2_clause_spec with (stk := cst) (e_then := update_loc n0) (n1' := Z.of_nat n) (z := z) (z' := z0) in H; eauto.
    assert (N: (-1 =? Z.of_nat n)%Z = false).
    { clear. apply /Z.eqb_spec. lia. }
    rewrite N in H. simpl in H. eapply star_trans. eauto. eauto. eauto.
Qed.

Lemma switch_incoming_returns_correct: forall p cs2 C1 C2 n2 n2' cst k mem z arg,
  Memory.load mem (C2, Block.local, 0%Z) = Some (Int (Z.of_nat n2)) ->
  Memory.load mem (C2, Block.local, 2%Z) = Some (Int z) ->
  unicity_in (incoming_returns C2 cs2) ->
  In (n2, ERet C1 z C2, n2') cs2 ->
  Star (CS.sem p) [CState C2, cst, mem, k,
      switch_incoming_return C2 cs2, Int arg]
    E0
    [CState C2, cst, mem, k, E_seq (update_loc n2')
      (E_assign (E_binop Add E_local (E_val (Int 1))) (E_val (Int 1))), Int arg].
Proof.
  move=> p cs2 C1 C2 n2 n2' cst k mem z arg Hload Hload' unic Hin.
  assert (Hin': In (n2, z, n2') (incoming_returns C2 cs2)).
  { clear -Hin. revert Hin.
    induction cs2; intros.
    - inv Hin.
    - destruct Hin.
      + subst. simpl; rewrite !eqxx /=. now left.
      + destruct a as ((? & []) & ?).
        * simpl. eauto.
        * simpl. case: ifP => /eqP ?; subst; simpl; try right; eauto. }
  clear Hin. rename Hin' into Hin.
  revert unic Hin. unfold switch_incoming_return.
  generalize (incoming_returns C2 cs2).
  induction l; intros.
  - inv Hin.
  - destruct a as ((? & ?) & ?); simpl in *.
    eapply switch2_clause_spec' with
      (stk := cst)
      (e_then := E_seq (update_loc n0)
                       (E_assign (E_binop Add E_local (E_val (Int 1))) (E_val (Int 1))))
      (n1' := Z.of_nat n)
      (z := z) (z' := z0) in Hload; eauto.
    (* rewrite Z.eqb_refl in Hload. *)
    destruct (Z.of_nat n2 =? Z.of_nat n)%Z eqn:?. simpl in *.
    + move: Heqb => /Z.eqb_spec n1_n.
      assert (n2 = n). {
        clear -n1_n.
        replace n with (Z.to_nat (Z.of_nat n)).
        replace n2 with (Z.to_nat (Z.of_nat n2)).
        rewrite n1_n. eauto.
        apply Nat2Z.id.
        apply Nat2Z.id. }
      subst n2.
      destruct (z =? z0)%Z eqn:?. simpl in *.
      * subst.
        move: Heqb => /Z.eqb_spec. intros ?; subst.
        assert ((n, z0, n0) = (n, z0, n2')).
        { destruct Hin as [? | Hin]; auto.
          clear -unic Hin.
          unfold unicity_in in unic.
          specialize (unic (n, z0) n0 n2').
          erewrite unic; eauto.
          left. eauto. right. eauto. }
        assert (n0 = n2') by congruence. subst.
        eauto.
      * eapply star_trans.
        eapply Hload. eapply IHl.
        eapply unicity_in_smaller; eauto.
        destruct Hin; eauto.
        assert ((n, z) <> (n, z0)). {
          intros ?; subst.
          move: Heqb => /Z.eqb_spec. congruence. }
        congruence.
        traceEq.
    + eapply star_trans.
      eapply Hload. eapply IHl.
      eapply unicity_in_smaller; eauto.
      clear Hload.
      destruct Hin; eauto.
      assert ((n, z0) <> (n2, z)). {
        intros ?; subst.
        move: Heqb => /Z.eqb_spec. congruence. }
      congruence.
    traceEq.
Qed.

Lemma sim_d_to_source (p: Flattened.prg) (wf_p: Flattened.wf p)
  (procs: {fmap Component.id -> seq Procedure.id})
  (procs_domm: domm procs = domm (Flattened.prog_procedures p))
  (procs_domm_intf: forall C C' P,
      imported_procedure (Flattened.prog_interface p) C C' P ->
      exists Ps, procs C' = Some Ps /\ P \in Ps)
  (procs_domm_intf': forall C Ps, procs C = Some Ps -> 0 \in Ps)
  (procs_has_main: exists Ps, procs Component.main = Some Ps /\ Procedure.main \in Ps):
  forward_simulation (Flattened.sem p) (CS.sem (compile p procs)).
Proof.
  fwd_sim (match_states_d_to_source p (compile p procs)).
  - intros. eexists; eexists; split.
    constructor. inv H. econstructor; eauto. constructor.
    destruct H1 as (A & B & C & D).
    destruct tra; simpl in *. eauto. inv C. eauto.
  - intros. inv H0. inv H. congruence. constructor.
  - intros [tra |((t1 & locs1) & st1)] t [tra' |((t1' & locs1') & st1')] STEP; try now inv STEP.
    { intros i [C cst mem k e v] MS.
      inv MS.
      unfold CS.initial_state, CS.initial_machine_state in H0.
      revert H0.
      destruct procs_has_main as [Ps_main [procsMain procsMainMain]].
      rewrite /prog_main /find_procedure mkfmapfE -procs_domm mem_domm procsMain //=.
      destruct (Flattened.prog_procedures p Component.main) eqn:p_main => //=.
      rewrite mkfmapfE procsMainMain //=. intros H; inv H.
      2: { revert p_main => /dommPn. rewrite -procs_domm => /dommPn. congruence. }
      assert (Hload:
          Memory.load (prepare_buffers (compile p procs)) (Component.main, Block.local, 0%Z) = Some (Int (-1))
        ).
      { rewrite /prepare_buffers /Memory.load /= mapmE mkfmapfE /= -procs_domm mem_domm procsMain //=.
        rewrite ComponentMemory.load_prealloc //=. }
      destruct (Memory.store_after_load (prepare_buffers (compile p procs))
              (Component.main, Block.local, 0%Z) (Int (-1)) (Int 0) ) as [mem MEM]; eauto.
      inv STEP.
      exists 0; eexists.
      split; [left|]; eauto.
      - econstructor. econstructor.
        do 7 (take_step); eauto.
        rewrite /prepare_buffers /Memory.load /= mapmE mkfmapfE /= -procs_domm mem_domm procsMain //=.
        rewrite ComponentMemory.load_prealloc //=.
        take_step; eauto. simpl.
        eapply star_trans.
        eapply switch_incoming_calls_correct'. eauto.
        take_step; eauto. simpl.
        take_step; eauto. simpl.
        take_step; eauto. simpl.
        take_step; eauto. simpl.
        take_step; eauto. simpl.
        eapply star_refl.
        traceEq.
        traceEq.
      - econstructor; eauto.
        econstructor. move=> C n //=; rewrite mkfmapfE.
        case: ifP => //= IN [] <-.
        split; erewrite Memory.load_after_store; eauto.
        case: ifP => //=.
        { rewrite /prepare_buffers /Memory.load /= mapmE mkfmapfE /= -(Flattened.wfprog_defined_procedures wf_p) IN //=.
          rewrite ComponentMemory.load_prealloc //=. case: ifP => //=.
          move=> /eqP -> /eqP //=. }
        split. case: ifP => //= /eqP; try congruence.
        { rewrite /prepare_buffers /Memory.load /= mapmE mkfmapfE /= -(Flattened.wfprog_defined_procedures wf_p) IN //=.
          rewrite ComponentMemory.load_prealloc //=. case: ifP => //=. }
        eexists.
        erewrite Memory.load_after_store; eauto.
        case: ifP => //=.
        { rewrite /prepare_buffers /Memory.load /= mapmE mkfmapfE /= -(Flattened.wfprog_defined_procedures wf_p) IN //=.
          rewrite ComponentMemory.load_prealloc //=. case: ifP => //=. }
    }
    inv STEP.
    + intros i [C cst mem k e v] MS.

      inv MS. simpl in *.
      exploit H1; try congruence. intros ?; subst C. clear H1.
      assert (es = cs1) as -> by congruence. clear ES.
      destruct (MS_MEM C1 n1 locs0) as (MEM1 & MEM2 & MEM3).
      eapply switch_outgoing_calls_correct
        with (p := compile p procs) (cst := cst) (k := Kstop) (v := v)
        in in_cs1 as STAR1; eauto.
      2: { eapply Flattened.unique_outgoing; eauto. }
      set G := (prepare_global_env (compile p procs)).
      assert (MEM1_t: exists v : value, Memory.load mem (C1, Block.local, 0%Z) = Some v) by eauto.
      assert (MEM2_t: exists v : value, Memory.load mem (C1, Block.local, 1%Z) = Some v) by eauto.

      assert (Cdiff: C1 <> C2).
      { move: wf_e => /andP [] /eqP //=. }
      assert (imp_P2: imported_procedure (genv_interface G) C1 C2 P2).
      { move: wf_e => /andP [] _ ?. now apply imported_procedure_iff. }

      assert (find_P2: find_procedure (genv_procedures G) C2 P2 = Some (code_of C2 P2 cs2)).
      { simpl. unfold find_procedure.
        rewrite mkfmapfE mem_domm procs_next //=.
        exploit procs_domm_intf; eauto. intros [Ps [-> ?]].
        rewrite mkfmapfE H //=. }

      pose proof (@call_expr_correct G C1 C2 0 P2 n1' z cst mem Kstop v _
                    MEM1_t MEM2_t Cdiff imp_P2 find_P2)
        as (mem' & PLUS & MEM1' & MEM2' & MEM3').
      clear MEM1_t MEM2_t.



      destruct (Memory.store_after_load mem'
                  (C2, Block.local, 0%Z)
                  (Int (Z.of_nat n2))
                  (Int (Z.of_nat n2')))
                 as [mem'' MEM''].
      { rewrite MEM3'; try congruence. eapply MS_MEM; eauto. }
      exists 0; eexists; split; [left|].
      * eapply star_plus_trans; [eapply STAR1 | |].
        eapply plus_star_trans; [eapply PLUS | |].
        unfold code_of.
        do 8 (take_step; eauto); simpl.
        { rewrite MEM3'; try congruence. eapply MS_MEM; eauto. }
        take_step; simpl; eauto.
        eapply star_trans.
        eapply switch_incoming_calls_correct
          with (p := compile p procs)
          in in_cs2 as STAR2; eauto.
        { rewrite MEM3'; try congruence. eapply MS_MEM; eauto. }
        { eapply Flattened.unique_incoming_calls; eauto. }
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        eapply star_refl.
        traceEq.
        traceEq.
        traceEq.
      * destruct t1'; [now apply match_final|].
        eapply match_states4_cons
          with (mem := mem'');
          eauto.
        -- eapply match_concrete_stacks_ext; auto.
        -- unfold match_mem.
           move=> C n; rewrite !setmE.
           case: ifP => /eqP.
           ++ move=> ? [] ?; subst.
              erewrite Memory.load_after_store; simpl; eauto.
              rewrite eqxx. split; auto.
              erewrite Memory.load_after_store; simpl; eauto.
              case: ifP => /eqP //= _.
              rewrite MEM3'; try congruence.
              split; auto. eapply MS_MEM; eauto.
              erewrite Memory.load_after_store; simpl; eauto.
              case: ifP => /eqP //= _.
              rewrite MEM3'; try congruence.
              eapply MS_MEM; eauto.
           ++ move=> C_C2.
              case: ifP => /eqP.
              ** move=> ? [] ?; subst; split.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 split; auto.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //= _.
                 rewrite MEM3'; try congruence.
                 eapply MS_MEM; eauto.
              ** intros C_C1 ?; split.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 rewrite MEM3'; try congruence. intros _.
                 eapply MS_MEM; eauto.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 rewrite MEM3'; try congruence. intros _.
                 split; auto. eapply MS_MEM; eauto.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //= _.
                 rewrite MEM3'; try congruence.
                 eapply MS_MEM; eauto.
        -- move: wf_et => [] _ []. intros. eauto.
        -- congruence.
    + intros i [C cst mem k e v] MS.

      inv MS. simpl in *.
      exploit H1; try congruence. intros ?; subst C. clear H1.
      assert (es = cs1) as -> by congruence. clear ES.
      destruct (MS_MEM C1 n1 locs0) as (MEM1 & MEM2 & MEM3).
      destruct (MS_MEM C2 n2 locs2) as (MEM1' & MEM2' & MEM3').
      eapply switch_outgoing_returns_correct
        with (p := compile p procs) (cst := cst) (k := Kstop) (v := v)
        in in_cs1 as STAR1; eauto.
      2: { eapply Flattened.unique_outgoing; eauto. }
      set G := (prepare_global_env (compile p procs)).
      assert (MEM1_t: exists v : value, Memory.load mem (C1, Block.local, 0%Z) = Some v) by eauto.
      assert (MEM2_t: exists v : value, Memory.load mem (C1, Block.local, 1%Z) = Some v) by eauto.

      assert (Cdiff: C1 <> C2).
      { move: wf_e => /eqP //=. }

      destruct (Memory.store_after_load mem
                  (C1, Block.local, 1%Z)
                  (Int 1)
                  (Int 1)) as [mem' MEM'].
      { eapply MS_MEM; eauto. }
      destruct (Memory.store_after_load mem'
                  (C1, Block.local, 0%Z)
                  (Int (Z.of_nat n1))
                  (Int (Z.of_nat n1'))) as [mem'' MEM''].
      { erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=. }
      destruct MEM3' as [oldret' MEM3'].
      destruct (Memory.store_after_load mem''
                  (C2, Block.local, 2%Z)
                  (oldret')
                  (Int z)) as [mem''' MEM'''].
      { erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=.
        erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=. }
      destruct (Memory.store_after_load mem'''
                  (C2, Block.local, 1%Z)
                  (Int 1)
                  (Int 0)) as [mem'''' MEM''''].
      { erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=.
        erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=.
        erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=. }

  destruct (Memory.store_after_load mem''''
              (C2, Block.local, 0%Z)
              (Int (Z.of_nat n2))
              (Int (Z.of_nat n2'))) as [mem''''' MEM'''''].
      { erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=.
        erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=.
        erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=.
        congruence.
        erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=. }
      destruct (Memory.store_after_load mem'''''
                  (C2, Block.local, 1%Z)
                  (Int 0)
                  (Int 1)) as [mem'''''' MEM''''''].
      { erewrite Memory.load_after_store; eauto.
        case: ifP => /eqP //=.
        erewrite Memory.load_after_store; eauto.
        rewrite eqxx //=. }

      pose proof (@unfold_stack G C1 P1 C2 st1' cst mem'' z v MS_ST)
                 as (stack' & stack'' & arg' & arg'' & stack'_eq & MS_ST' & STAR2).


      assert (find_P2: find_procedure (genv_procedures G) C2 0 =
                         Some (code_of C2 0 cs2)).
      { simpl. unfold find_procedure.
        rewrite mkfmapfE mem_domm procs_next //=.
        assert (exists Ps, procs C2 = Some Ps) as [Ps C2Ps].
        { clear -procs_next procs_domm.
          apply /dommP; rewrite procs_domm; apply /dommP; eauto. }

         exploit procs_domm_intf'; eauto. rewrite C2Ps mkfmapfE => -> //=. }

      exists 0; eexists; split; [left|].
      * eapply star_plus_trans; [eapply STAR1 | |].
        eapply plus_star_trans.
        eapply plus_one. econstructor.
        eapply star_trans.
        do 14 (take_step; eauto); simpl.
        subst stack'.
        eapply star_step. eapply CS.KS_ExternalReturn. auto.
        do 26 (take_step; eauto).
        erewrite Memory.load_after_store; eauto. rewrite eqxx; eauto.
        do 1 (take_step; eauto). simpl.

        eapply star_trans.
        eapply switch_incoming_returns_correct
          with (p := compile p procs)
               (mem := mem'''')
          in in_cs2 as STAR3; eauto.
        { erewrite Memory.load_after_store; simpl; eauto.
          case: ifP => /eqP //=.
          erewrite Memory.load_after_store; simpl; eauto.
          case: ifP => /eqP //=.
          erewrite Memory.load_after_store; simpl; eauto.
          case: ifP => /eqP //=; try congruence.
          erewrite Memory.load_after_store; simpl; eauto.
          case: ifP => /eqP //=; try congruence. }
        { erewrite Memory.load_after_store; simpl; eauto.
          case: ifP => /eqP //=.
          erewrite Memory.load_after_store; simpl; eauto.
          case: ifP => /eqP //=. }
        eapply Flattened.unique_incoming_returns; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        take_step; eauto.
        eapply star_refl.
        traceEq.
        traceEq.
        traceEq.
        traceEq.
        traceEq.
      * destruct t1'; [now apply match_final| ].
        eapply match_states4_cons
          with (mem := mem'''''');
          eauto.
        -- eapply match_concrete_stacks_int; auto.
        -- unfold match_mem.
           move=> C n; rewrite !setmE.
           case: ifP => /eqP.
           ++ move=> ? [] ?; subst.
              erewrite Memory.load_after_store; simpl; eauto.
              case: ifP => /eqP //=.
              erewrite Memory.load_after_store; simpl; eauto.
              rewrite eqxx. split; auto.
              erewrite Memory.load_after_store; simpl; eauto.
              rewrite eqxx. split; auto.
              erewrite Memory.load_after_store; simpl; eauto.
              case: ifP => /eqP //=.
              erewrite Memory.load_after_store; simpl; eauto.
              case: ifP => /eqP //=.
              erewrite Memory.load_after_store; simpl; eauto.
              case: ifP => /eqP //=.
              erewrite Memory.load_after_store; simpl; eauto.
              rewrite eqxx. eexists; eauto.
           ++ move=> C_C2.
              case: ifP => /eqP.
              ** move=> ? [] ?; subst; split.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 rewrite eqxx. split; eauto.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
              ** intros C_C1 ?; split.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 (* rewrite MEM3'; try congruence. intros _. *)
                 intros. eapply MS_MEM; eauto.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.

                 intros; split. exploit MS_MEM; eauto. intros [? [? [? ?]]]; eauto.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 erewrite Memory.load_after_store; simpl; eauto.
                 case: ifP => /eqP //=; try congruence.
                 intros. exploit MS_MEM; eauto. intros [_ [_ [? ?]]]; eauto.
        -- move: wf_et => [] _ [] ?. eauto.
        -- congruence.
           Unshelve.
           exact 0.
Qed.
