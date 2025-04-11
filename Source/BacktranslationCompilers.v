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

Lemma numbering_tree_unicity : forall (ut : unit_tree) (n0 sz : nat) (tr : numbered_tree), (sz, tr) = numbering_tree ut n0 -> unique_numbering tr.
Proof.
  intro ut.
  assert (forall n0 sz tr, (sz, tr) = numbering_tree ut n0 -> forall n1, (no_occ_of_n_in_tree n1 tr \/ unique_occ_of_n_in_tree n1 tr)
                             /\ (unique_occ_of_n_in_tree n1 tr -> n1 < sz /\ n1 >= n0)).
  { induction ut using tree_ind with
      (P := fun ut => forall n sz tr, (sz, tr) = numbering_tree ut n ->
                                      forall n1, (no_occ_of_n_in_tree n1 tr \/ unique_occ_of_n_in_tree n1 tr)
                                        /\ (unique_occ_of_n_in_tree n1 tr -> n1 < sz /\ n1 >= n))
      (P0 := (fun br => forall n sz br', (sz, br') = numbering_branches br n -> forall n1,
                    (no_occ_of_n_in_branches n1 br' \/ unique_occ_of_n_in_branches n1 br') /\
                      (unique_occ_of_n_in_branches n1 br' -> n1 < sz /\ n1 >= n))) ;
      intros n sz tr EQ n1.
    + simpl in EQ.
      destruct (numbering_branches b (S n)) eqn:EQ'.
      symmetry in EQ'.
      inv EQ.
      specialize (IHut (S n) n0 b0 EQ' n1) as H1.
      destruct H1.
      assert (n1 = n \/ n1 <> n). { lia. }
      split.
    - destruct H ; destruct H1.
      * right.
        rewrite <- H1.
        exact (first_occ_case n1 n1 b0 H Logic.eq_refl).
      * left.
        exact (never_here_case n1 n b0 H1 H).
      * specialize (H0 H).
        destruct H0.
        rewrite H1 in H2.
        lia.
      * right.
        exact (already_here_case n1 n b0 H1 H).
    - intro Hunq.
      inversion Hunq.
      * split; try auto.
        rewrite (numbering_branches_correct b (S n) n0 b0 EQ').
        subst. unfold loc in * . simpl in *.
        unfold Datatypes.id in *.
        lia.
        subst. unfold loc in * . simpl in *.
        unfold Datatypes.id in *. lia.
      * apply H0 in H6.
        subst. unfold loc in * . simpl in *.
        unfold Datatypes.id in *. lia.
      + inv EQ.
        split.
    - left ; constructor.
    - intro H ; inversion H.
      + inv EQ.
        destruct (numbering_tree ut n) eqn:E1 ; symmetry in E1.
        destruct (numbering_branches b n0) eqn:E2 ; symmetry in E2.
        destruct (IHut n n0 t E1 n1) as [Ht0 Ht1].
        destruct (IHut0 n0 n2 b0 E2 n1) as [Hb0 Hb1].
        inv H0.
        split.
    - destruct Ht0 ; destruct Hb0 ; try (right ; now constructor).
      * left. now constructor.
      * apply Ht1 in H.
        apply Hb1 in H0.
        destruct H.
        destruct H0.
        lia.
    - intro Hunq.
      inversion Hunq.
      * apply Ht1 in H4.
        destruct H4.
        split ; try auto.
        rewrite (numbering_branches_correct b n0 n2 b0 E2).
        lia.
      * apply Hb1 in H2.
        destruct H2.
        split ; try auto.
        rewrite (numbering_tree_correct ut n n0 t E1) in H5.
        lia.
  }
  intros n0 sz tr EQ.
  constructor.
  intro n.
  now destruct (H n0 sz tr EQ n).
Qed.

Lemma numbering_tree_determinacy : forall (ut: unit_tree) (n0 sz: nat) (tr: numbered_tree),
    (sz, tr) = numbering_tree ut n0 ->
    deterministic_tree ut ->
    deterministic_tree tr.
Proof.
  induction ut using tree_ind with
    (P := fun ut =>
            forall n0 sz tr,
              (sz, tr) = numbering_tree ut n0 ->
              deterministic_tree ut ->
              deterministic_tree tr)
    (P0 := fun ubr =>
             forall n0 sz br,
               (sz, br) = numbering_branches ubr n0 ->
               ((deterministic_branches ubr -> deterministic_branches br)
                /\ (forall e, do_not_appear_in e ubr -> do_not_appear_in e br))).
  - intros n0 sz tr Hfun Huni.
    inversion Hfun.
    destruct (numbering_branches b (S n0))eqn:EQ1.
    inv H0.
    constructor.
    apply sym_eq in EQ1.
    specialize (IHut (S n0) n b0 EQ1).
    destruct IHut as [IH1 IH2].
    inv Huni.
    exact (IH1 H0).
  - intros n0 sz br Hfun.
    split; intro H; inversion Hfun; constructor.
  - intros n0 sz br Hfun.
    split; inversion Hfun; destruct (numbering_tree ut n0) eqn:EQ1;
      apply sym_eq in EQ1;
      destruct (numbering_branches b n) eqn:EQ2;
      apply sym_eq in EQ2;
      inv H0.
    + intros Huni;
        inv Huni.
      { destruct (IHut0 n n1 b0 EQ2) as [IH1 IH2].
        constructor.
        - exact (IH1 H2).
        - now apply (IHut n0 n t EQ1).
        - eapply (IH2 e H4). }
    + intros e0 Huni; inv Huni.
      constructor; eauto.
      eapply IHut0; eauto.
Qed.

Lemma numbering_tree_unique_current:
  forall (C: Component.id) (ut: unit_tree) (n0 sz: nat) (tr: numbered_tree),
    (sz, tr) = numbering_tree ut n0 ->
    unique_current_tree C ut ->
    unique_current_tree C tr.
Proof.
  intros C.
  induction ut using tree_ind with
    (P := fun ut => forall n0 sz tr, (sz, tr) = numbering_tree ut n0 ->
                                     unique_current_tree C ut ->
                                     unique_current_tree C tr)
    (P0 := fun ubr => forall n0 sz br, (sz, br) = numbering_branches ubr n0 ->
                                       unique_current_branches C ubr ->
                                       unique_current_branches C br).
  - move=> n0 sz tr //= num_tr det.
    destruct (numbering_branches b (S n0)) eqn:eq1; inv num_tr.
    simpl; eapply IHut; eauto.
  - move=> n0 sz br //= num_br det.
    by inv num_br.
  - move=> n0 sz br //= num_br /andP [] det1 det2.
    destruct (numbering_tree ut n0) eqn:eq1; inv num_br.
    destruct (numbering_branches b n) eqn:eq2; inv H0.
    simpl. apply /andP; split.
    + eapply IHut; eauto.
    + destruct (cur_comp_of_event e == C).
      * destruct b; simpl in *; auto. inv eq2; auto.
      * eapply IHut0; eauto.
Qed.

Definition compile_unit_tree (p : UnitTree.prg): NumberedTree.prg :=
  {| NumberedTree.prog_interface := UnitTree.prog_interface p;
    NumberedTree.prog_trees := mapm loc_tree_of_unit_tree (UnitTree.prog_trees p)
  |}.

Program Fixpoint loc_sproc_tree_of_loc_tree_with_acc (tr: Tree.t nat event) (acc: stack):
  Tree.t loc_stack event :=
  match tr with
  | node l br => node (l, acc) (loc_sproc_branch_of_loc_branch_with_acc br acc)
  end
with loc_sproc_branch_of_loc_branch_with_acc (br: Tree.b nat event) (acc: stack):
  Tree.b loc_stack event :=
       match br with
       | Bnil => Bnil loc_stack event
       | Bcons e tr' br' =>
           let acc' := (match e with
                        | ECall Ccur P z Cnext => (Ccur, P, Cnext) :: acc
                        | ERet _ _ _ => behead acc
                        end) in
           Bcons e (loc_sproc_tree_of_loc_tree_with_acc tr' acc')
             (loc_sproc_branch_of_loc_branch_with_acc br' acc)
       end.

Definition loc_sproc_tree_of_loc_tree (tr: numbered_tree): stack_tree :=
  loc_sproc_tree_of_loc_tree_with_acc tr [].


Definition compile_numbered_tree (p : NumberedTree.prg): StackTree.prg :=
  {| StackTree.prog_interface := NumberedTree.prog_interface p;
    StackTree.prog_trees := mapm loc_sproc_tree_of_loc_tree (NumberedTree.prog_trees p)
  |}
.


Fixpoint flatten (tr: Tree.t loc_stack event): (nat * list (nat * event * nat)) :=
  match tr with
  | node (loc, _) br => (loc, flatten_br loc br)
  end
with flatten_br (loc: nat) (br: Tree.b loc_stack event): list (nat * event * nat) :=
       match br with
       | Bnil => []
       | Bcons e tr br' =>
           let (n, ls) := flatten tr in
           ((loc, e, n) :: ls) ++ (flatten_br loc br')
                               (* ls ++ (loc, e, n) :: (flatten_br loc br') *)
       end.

Definition compile_stack_tree (p: StackTree.prg): Flattened.prg :=
  {| Flattened.prog_interface  := StackTree.prog_interface p;
    Flattened.prog_procedures :=
      mapm (fun tr => snd (flatten tr)) (StackTree.prog_trees p);
  |}.

Lemma pmap_app: forall {A B: Type} (f: A -> option B) a a',
    pmap f (a ++ a') = pmap f a ++ pmap f a'.
Proof.
  intros A B f a.
  induction a.
  - intros. eauto.
  - intros. simpl. destruct (f a); simpl in *.
    rewrite IHa. eauto. eauto.
Qed.

Definition match_out e e' :=
  match e, e' with
  | ECall Ccur Pnext z Cnext, ECall Ccur' Pnext' z' Cnext' =>
      Ccur = Ccur' /\ Pnext = Pnext' /\ z = z' /\ Cnext = Cnext'
  | ERet Ccur z Cnext, ERet Ccur' z' Cnext' =>
      Ccur = Ccur' /\ z = z'
  | _, _ => False
  end.

Lemma flatten_unicity_cons:
  forall C k e n ls,
    (forall e' n', cur_comp_of_event e' = C ->
                   In (k, e', n') ls -> match_out e e' /\ n = n') ->
    unicity_in2 (outgoing C ls) ->
    unicity_in2 (outgoing C ((k, e, n) :: ls)).
Proof.
  intros C k e n ls NO_OCC UNI.
  destruct (C == cur_comp_of_event e) eqn:C_e.
  2: { unfold outgoing.
       simpl. case: e C_e {NO_OCC} => //=.
       intros ???? -> => //=.
       intros ??? -> => //=. }
  intros c b b' a a' IN IN'.
  replace (outgoing C ((k, e, n) :: ls)) with
    (outgoing C [(k, e, n)] ++ (outgoing C ls)) in *.
  2: { unfold outgoing. simpl.
       case: e C_e IN IN' {NO_OCC} => //=.
       intros ???? -> => //=.
       intros ??? -> => //=. }
  simpl in *.
  destruct e as [Ccur Pnext z Cnext | Ccur z Cnext]; simpl in *;
    rewrite C_e in IN, IN'; simpl in *.
  { destruct IN as [IN | IN]; destruct IN' as [IN' | IN'].
    - inv IN. inv IN'. auto.
    - inv IN.
      assert (exists e, In (c, e, a') ls /\ cur_comp_of_event e = C /\
                          match e with
                          | ECall _ Pnext z Cnext => b' = inl (Cnext, Pnext, z)
                          | ERet _ z _ => b' = inr z
                          end) as [e [IN [CC M]]].
      { clear -IN'. revert IN'.
        induction ls; intros.
        - inv IN'.
        - destruct a as [[? [|]] ?]; simpl in *.
          + revert IN'.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto.
          + revert IN'.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto. }
      (* + revert IN'. *)
      (*   case: ifP => /eqP. *)
      (*   * intros ?; subst. simpl. intros []; eauto. *)
      (*     inv H. eexists; left; eauto. *)
      (*     exploit IHls; eauto. intros [e ?]. *)
      (*     eexists; right; eauto. *)
      (*   * intros ?; subst. *)
      (*     intros. *)
      (*     exploit IHls; eauto. *)
      (*     intros [e ?]. *)
      (*     eexists; right; eauto. } *)
      exploit NO_OCC; eauto.
      intros G. destruct e; simpl in *.
      inv G. inv H. inv H1. inv H0. auto.
      inv G. inv H.
    - inv IN'.
      assert (exists e, In (c, e, a) ls /\ cur_comp_of_event e = C /\
                          match e with
                          | ECall _ Pnext z Cnext => b = inl (Cnext, Pnext, z)
                          | ERet _ z _ => b = inr z
                          end) as [e [IN' [CC M]]].
      { clear -IN. revert IN.
        induction ls; intros.
        - inv IN.
        - destruct a0 as [[? [|]] ?]; simpl in *.
          + revert IN.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto.
          + revert IN.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto. }
      exploit NO_OCC; eauto. intros G.
      destruct e; simpl in *.
      inv G. inv H. inv H1. inv H0. auto.
      inv G. inv H.
    - eauto. }
  { destruct IN as [IN | IN]; destruct IN' as [IN' | IN'].
    - inv IN. inv IN'. auto.
    - inv IN.
      assert (exists e, In (c, e, a') ls /\ cur_comp_of_event e = C /\
                          match e with
                          | ECall _ Pnext z Cnext => b' = inl (Cnext, Pnext, z)
                          | ERet _ z _ => b' = inr z
                          end) as [e [IN [CC M]]].
      { clear -IN'. revert IN'.
        induction ls; intros.
        - inv IN'.
        - destruct a as [[? [|]] ?]; simpl in *.
          + revert IN'.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto.
          + revert IN'.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto. }
      exploit NO_OCC; eauto. intros G.
      destruct e; simpl in *.
      inv G. inv H.
      inv G. inv H. auto.
    - inv IN'.
      assert (exists e, In (c, e, a) ls /\ cur_comp_of_event e = C /\
                          match e with
                          | ECall _ Pnext z Cnext => b = inl (Cnext, Pnext, z)
                          | ERet _ z _ => b = inr z
                          end) as [e [IN' [CC M]]].
      { clear -IN. revert IN.
        induction ls; intros.
        - inv IN.
        - destruct a0 as [[? [|]] ?]; simpl in *.
          + revert IN.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto.
          + revert IN.
            case: ifP => /eqP.
            * intros ?; subst. simpl. intros []; eauto.
              inv H; simpl.
              eexists; split; eauto. simpl; eauto.
              exploit IHls; eauto. intros [e [? ?]].
              eexists; split; eauto.
            * intros ?; subst.
              intros.
              exploit IHls; eauto.
              intros [e [? ?]].
              eexists; split; eauto. }
      exploit NO_OCC; eauto. intros G.
      destruct e; simpl in *.
      inv G. inv H.
      inv G. inv H. auto.
    - eauto. }
Qed.

Lemma flatten_unicity'':
  forall C (ls: seq (nat * event * nat)) br (loc: nat),
    (forall k e n', In (k.1, e, n') ls ->
                    k.1 <> loc /\ no_occ_of_n_in_branches k br) ->
    unicity_in2 (outgoing C ls) ->
    unicity_in2 (outgoing C (flatten_br loc br)) ->
    unicity_in2 (outgoing C
                   (ls ++ (flatten_br loc br))).
Proof.
  intros C ls.
  induction ls.
  - eauto.
  - intros.
    destruct a as [[k e] n].
    replace (((k, e, n) :: ls) ++ flatten_br loc br) with
      ((k, e, n) :: (ls ++ flatten_br loc br)) by reflexivity.
    simpl.
    destruct e as [Ccur Pnext z Cnext | Ccur z Cnext] eqn:eq_e.
    { case: ifP => //=.
      2: { intros N.
           eapply IHls; eauto.
           - intros.
             eapply H. right. eauto.
           - red. intros.
             eapply H0.
             -- simpl. rewrite N. eauto.
             -- simpl. rewrite N. eauto. }
      intros ?.
      replace ((k, inl (Cnext, Pnext, z), n) :: outgoing C (ls ++ flatten_br loc br))
        with ([(k, inl (Cnext, Pnext, z), n)] ++ outgoing C (ls ++ flatten_br loc br))
        by reflexivity.
      replace [:: (k, inl (Cnext, Pnext, z), n)]
        with (outgoing C [(k, ECall Ccur Pnext z Cnext, n)]).
      2: { simpl. rewrite i. reflexivity. }
      replace (outgoing C [:: (k, ECall Ccur Pnext z Cnext, n)] ++ outgoing C (ls ++ flatten_br loc br))
        with (outgoing C ((k, ECall Ccur Pnext z Cnext, n) :: (ls ++ flatten_br loc br))).
      2: { simpl. rewrite i. reflexivity. }
      eapply flatten_unicity_cons; eauto.
      + intros. eapply in_app_or in H3.
        destruct H3.
        * exploit H0.
          { simpl. rewrite i. simpl. now left. }
          { simpl. rewrite i. simpl. right.
            instantiate (2 :=
                           match e' with
                           | ECall Ccur Pnext z Cnext =>
                               inl (Cnext, Pnext, z)
                           | ERet Ccur z Cnext => inr z end).
            instantiate (1 := n').
            clear -H2 H3 i.
            induction ls.
            - eauto.
            - destruct a as [[] ]; simpl in *.
              destruct H3.
              + inv H. destruct e'. simpl in *. rewrite eqxx. simpl. now left.
                simpl. rewrite eqxx. simpl. now left.
              + destruct e'; simpl in *.
                destruct e; simpl in *.
                case: ifP => //=. eauto. eauto.
                case: ifP => //=. eauto. eauto.
                destruct e; simpl in *.
                case: ifP => //=. eauto. eauto.
                case: ifP => //=. eauto. eauto. }
          destruct e'. intros G; inv G.
          split; auto. inv H4; eauto. simpl in i.
          move: i => /eqP -> //=.
          intros []; congruence.
        * specialize (H (k, []) (ECall Ccur Pnext z Cnext) n).
          simpl in H. specialize (H (or_introl Logic.eq_refl)).
          destruct H as [H G].
          clear -G H H3. exfalso.
          revert loc k e' n' G H H3.
          { induction br using branches_ind with
              (P0 := fun br =>
                       forall loc k e' n',
                         no_occ_of_n_in_branches (k, [::]) br ->
                         k <> loc ->
                         In (k, e', n') (flatten_br loc br) ->
                         False)
              (P := fun tr =>
                      forall k e' n',
                        no_occ_of_n_in_tree (k, [::]) tr ->
                        In (k, e', n') (flatten tr).2 ->
                        False).
            - intros. destruct a; simpl in *.
              inv H. eapply IHbr; eauto.
            - intros. inv H1.
            - intros. inv H. simpl in *.
              destruct (flatten t) eqn:flatten_t. simpl in *.
              destruct H1.
              + inv H. congruence.
              + eapply in_app_or in H.
                destruct H.
                * eapply IHbr; eauto.
                * eapply IHbr0; eauto. }
      + eapply IHls; eauto.
        * intros.
          eapply H. right. eauto.
        * red. intros.
          eapply H0.
          -- simpl. rewrite i. simpl. eauto.
          -- simpl. rewrite i. simpl. eauto.
    }
    { case: ifP => //=.
      2: { intros N.
           eapply IHls; eauto.
           - intros.
             eapply H. right. eauto.
           - red. intros.
             eapply H0.
             -- simpl. rewrite N. eauto.
             -- simpl. rewrite N. eauto. }
      intros ?.
      replace ((k, inr z, n) :: outgoing C (ls ++ flatten_br loc br))
        with ([(k, inr z, n)] ++ outgoing C (ls ++ flatten_br loc br))
        by reflexivity.
      replace [:: (k, inr z, n)]
        with (outgoing C [(k, ERet Ccur z Cnext, n)]).
      2: { simpl. rewrite i. reflexivity. }
      replace (outgoing C [:: (k, ERet Ccur z Cnext, n)] ++ outgoing C (ls ++ flatten_br loc br))
        with (outgoing C ((k, ERet Ccur z Cnext, n) :: (ls ++ flatten_br loc br))).
      2: { simpl. rewrite i. reflexivity. }
      eapply flatten_unicity_cons; eauto.
      + intros. eapply in_app_or in H3.
        destruct H3.
        * exploit H0.
          { simpl. rewrite i. simpl. now left. }
          { simpl. rewrite i. simpl. right.
            instantiate (2 :=
                           match e' with
                           | ECall Ccur Pnext z Cnext =>
                               inl (Cnext, Pnext, z)
                           | ERet Ccur z _ => inr z end).
            instantiate (1 := n').
            clear -H2 H3 i.
            induction ls.
            - eauto.
            - destruct a as [[] ]; simpl in *.
              destruct H3.
              + inv H. destruct e'. simpl in *. rewrite eqxx. simpl. now left.
                simpl. rewrite eqxx. simpl. now left.
              + destruct e'; simpl in *.
                destruct e; simpl in *.
                case: ifP => //=. eauto. eauto.
                case: ifP => //=. eauto. eauto.
                destruct e; simpl in *.
                case: ifP => //=. eauto. eauto.
                case: ifP => //=. eauto. eauto. }
          destruct e'. intros []; congruence.
          intros G; inv G.
          split; auto. inv H4; eauto. simpl in i.
          move: i => /eqP -> //=.
        (* intros []; congruence. *)
        * specialize (H (k, []) (ERet Ccur z Cnext) n).
          simpl in H. specialize (H (or_introl Logic.eq_refl)).
          destruct H as [H G].
          clear -G H H3. exfalso.
          revert loc k e' n' G H H3.
          { induction br using branches_ind with
              (P0 := fun br =>
                       forall loc k e' n',
                         no_occ_of_n_in_branches (k, [::]) br ->
                         k <> loc ->
                         In (k, e', n') (flatten_br loc br) ->
                         False)
              (P := fun tr =>
                      forall k e' n',
                        no_occ_of_n_in_tree (k, [::]) tr ->
                        In (k, e', n') (flatten tr).2 ->
                        False).
            - intros. destruct a; simpl in *.
              inv H. eapply IHbr; eauto.
            - intros. inv H1.
            - intros. inv H. simpl in *.
              destruct (flatten t) eqn:flatten_t. simpl in *.
              destruct H1.
              + inv H. congruence.
              + eapply in_app_or in H.
                destruct H.
                * eapply IHbr; eauto.
                * eapply IHbr0; eauto. }
      + eapply IHls; eauto.
        * intros.
          eapply H. right. eauto.
        * red. intros.
          eapply H0.
          -- simpl. rewrite i. simpl. eauto.
          -- simpl. rewrite i. simpl. eauto. }
Qed.

Lemma flatten_no_occ_unicity tr n0 ls n e:
  flatten tr = (n0, ls) ->
  no_occ_of_n_in_tree n tr ->
  unicity_in2 (outgoing (cur_comp_of_event e) ls) ->
  unicity_in2 (outgoing (cur_comp_of_event e) ((n.1, e, n0) :: ls)).
Proof.
  intros ???.
  intros c b b' a a' IN IN'.
  replace (outgoing (cur_comp_of_event e) ((n.1, e, n0) :: ls))
    with ((outgoing (cur_comp_of_event e) [(n.1, e, n0)]) ++
            (outgoing (cur_comp_of_event e) ls)) in *.
  2: {
    unfold outgoing. rewrite -pmap_app. reflexivity.
  }
  (* replace (outgoing (cur_comp_of_event e) (ls ++ [:: (n.1, e, n0)])) *)
  (*   with ((outgoing (cur_comp_of_event e) ls) ++ (outgoing (cur_comp_of_event e) [:: (n.1, e, n0)])) in *. *)
  eapply in_app_or in IN.
  eapply in_app_or in IN'.
  destruct IN; destruct IN'.
  - move: H2 H3 => //=.
    clear H1.
    case: e => [???? | ???] //=. rewrite eqxx. firstorder; congruence.
    rewrite eqxx. firstorder; congruence.
  (* - eapply H1; eauto. *)
  - revert H1 H2 H3.
    case: e => //= [C P' z C' | C z C'].
    + rewrite eqxx /= => unic [] //= [] ? ? ? in1; subst c b n0.
      exfalso.
      assert (exists e, In (n.1, e, a') ls) as [e in2].
      { clear -in1.
        induction ls.
        - inv in1.
        - destruct a as [[? [|]] ?]; simpl in *.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
      }
      clear -H H0 in2.
      revert H H0 in2.
      revert ls n a a' e.
      induction tr using tree_ind with
        (P := fun tr =>
                forall ls n a a' e,
                  flatten tr = (a, ls) ->
                  (no_occ_of_n_in_tree n tr) ->
                  In (n.1, e, a') ls -> False)
        (P0 := fun br =>
                 forall ls n n' a e,
                   flatten_br n' br = ls ->
                   no_occ_of_n_in_branches n br ->
                   n.1 <> n' ->
                   (In (n.1, e, a) ls) ->
                   False).
      * intros. destruct a; simpl in *. inv H. inv H0.
        eapply IHtr; eauto.
      * intros; simpl in *; subst; inv H2.
      * intros; simpl in *.
        destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
        subst ls. inv H0.
        simpl in H2.
        destruct H2 as [H2 | H2].
        -- inv H2. congruence.
        -- apply in_app_or in H2.
           destruct H2 as [H2 | H2].
           ++ eapply IHtr; eauto.
           ++ eapply IHtr0; eauto.
    + rewrite eqxx /= => unic [] //= [] ? ? ? in1; subst c b n0.
      exfalso.
      assert (exists e, In (n.1, e, a') ls) as [e in2].
      { clear -in1.
        induction ls.
        - inv in1.
        - destruct a as [[? [|]] ?]; simpl in *.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
      }
      clear -H H0 in2.
      revert H H0 in2.
      revert ls n a a' e.
      induction tr using tree_ind with
        (P := fun tr =>
                forall ls n a a' e,
                  flatten tr = (a, ls) ->
                  (no_occ_of_n_in_tree n tr) ->
                  In (n.1, e, a') ls -> False)
        (P0 := fun br =>
                 forall ls n n' a e,
                   flatten_br n' br = ls ->
                   no_occ_of_n_in_branches n br ->
                   n.1 <> n' ->
                   (In (n.1, e, a) ls) ->
                   False).
      * intros. destruct a; simpl in *. inv H. inv H0.
        eapply IHtr; eauto.
      * intros; simpl in *; subst; inv H2.
      * intros; simpl in *.
        destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
        subst ls. inv H0.
        simpl in H2.
        destruct H2 as [H2 | H2].
        -- inv H2. congruence.
        -- apply in_app_or in H2.
           destruct H2 as [H2 | H2].
           ++ eapply IHtr; eauto.
           ++ eapply IHtr0; eauto.
  - revert H1 H2 H3.
    case: e => //= [C P' z C' | C z C'].
    + rewrite eqxx /= => unic in1 [] [] ? ? ?; subst c b' n0.
      exfalso.
      assert (exists e, In (n.1, e, a) ls) as [e in2].
      { clear -in1.
        induction ls.
        - inv in1.
        - destruct a0 as [[? [|]] ?]; simpl in *.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
      }
      clear -H H0 in2.
      revert H H0 in2.
      revert ls n a a' e.
      induction tr using tree_ind with
        (P := fun tr =>
                forall ls n a a' e,
                  flatten tr = (a', ls) ->
                  (no_occ_of_n_in_tree n tr) ->
                  In (n.1, e, a) ls -> False)
        (P0 := fun br =>
                 forall ls n n' a e,
                   flatten_br n' br = ls ->
                   no_occ_of_n_in_branches n br ->
                   n.1 <> n' ->
                   (In (n.1, e, a) ls) ->
                   False).
      * intros. destruct a; simpl in *. inv H. inv H0.
        eapply IHtr; eauto.
      * intros; simpl in *; subst; inv H2.
      * intros; simpl in *.
        destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
        subst ls. inv H0.
        simpl in H2.
        destruct H2 as [H2 | H2].
        -- inv H2. congruence.
        -- apply in_app_or in H2.
           destruct H2 as [H2 | H2].
           ++ eapply IHtr; eauto.
           ++ eapply IHtr0; eauto.
    + rewrite eqxx /= => unic in1 [] [] ? ? ?; subst c b' n0.
      exfalso.
      assert (exists e, In (n.1, e, a) ls) as [e in2].
      { clear -in1.
        induction ls.
        - inv in1.
        - destruct a0 as [[? [|]] ?]; simpl in *.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
          + revert in1. case: ifP => /eqP.
            intros ?; subst. simpl. intros []; eauto.
            inv H. eexists; left; eauto.
            exploit IHls; eauto. intros [? ?]; eauto.
            intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
      }
      clear -H H0 in2.
      revert H H0 in2.
      revert ls n a a' e.
      induction tr using tree_ind with
        (P := fun tr =>
                forall ls n a a' e,
                  flatten tr = (a', ls) ->
                  (no_occ_of_n_in_tree n tr) ->
                  In (n.1, e, a) ls -> False)
        (P0 := fun br =>
                 forall ls n n' a e,
                   flatten_br n' br = ls ->
                   no_occ_of_n_in_branches n br ->
                   n.1 <> n' ->
                   (In (n.1, e, a) ls) ->
                   False).
      * intros. destruct a; simpl in *. inv H. inv H0.
        eapply IHtr; eauto.
      * intros; simpl in *; subst; inv H2.
      * intros; simpl in *.
        destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
        subst ls. inv H0.
        simpl in H2.
        destruct H2 as [H2 | H2].
        -- inv H2. congruence.
        -- apply in_app_or in H2.
           destruct H2 as [H2 | H2].
           ++ eapply IHtr; eauto.
           ++ eapply IHtr0; eauto.
  - eapply H1; eauto.
Qed.

Lemma unicity_in2_unicity_in {A B C: Type} : forall (ls: seq (C * B * A)),
    unicity_in2 ls ->
    unicity_in ls.
Proof.
  intros. intros [c b] a a' IN1 IN2.
  eapply H; eauto.
Qed.

Lemma flatten_no_occ_unicity' P tr n0 ls n e:
  flatten tr = (n0, ls) ->
  no_occ_of_n_in_tree n tr ->
  unicity_in2 (incoming_calls (cur_comp_of_event e) P ls) ->
  unicity_in2 (incoming_calls (cur_comp_of_event e) P ((n.1, e, n0) :: ls)).
Proof.
  intros ???.
  intros c b b' a a' IN IN'.
  replace (incoming_calls (cur_comp_of_event e) P ((n.1, e, n0) :: ls))
    with ((incoming_calls (cur_comp_of_event e) P [(n.1, e, n0)]) ++
            (incoming_calls (cur_comp_of_event e) P ls)) in *.
  2: {
    unfold outgoing. rewrite -pmap_app. reflexivity.
  }
  (* replace (outgoing (cur_comp_of_event e) (ls ++ [:: (n.1, e, n0)])) *)
  (*   with ((outgoing (cur_comp_of_event e) ls) ++ (outgoing (cur_comp_of_event e) [:: (n.1, e, n0)])) in *. *)
  eapply in_app_or in IN.
  eapply in_app_or in IN'.
  destruct IN; destruct IN'.
  - move: H2 H3 => //=.
    clear H1.
    case: e => [Ccur Pnext z Cnext | ???] //=.
    case: ifP => /andP.
    + move=> [] /eqP Ceq /eqP Peq. simpl.
      intros []; eauto.
      * inv H1. intros []; inv H1. auto.
      * inv H1.
    + simpl. by [].
  (* - eapply H1; eauto. *)
  - revert H1 H2 H3.
    case: e => //= [C P' z C'].
    + move=> /= unic.
      case: ifP => /andP.
      * move=> [] /eqP Ceq /eqP Peq //=.
        intros []; eauto. inv H1; eauto.
        intros IN1.
        assert (exists e, In (n.1, e, a') ls) as [e in2].
        { clear -IN1.
          induction ls.
          - inv IN1.
          - destruct a as [[? [|]] ?]; simpl in *.
            + revert IN1. case: ifP => /eqP.
              intros ?; subst. simpl. intros []; eauto.
              inv H. eexists; left; eauto.
              exploit IHls; eauto. intros [? ?]; eauto.
              intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
            + exploit IHls; eauto. intros [? ?]. eauto. }
        clear -H H0 in2.
        { exfalso.
          revert H H0 in2.
          revert ls n a a' e.
          induction tr using tree_ind with
            (P := fun tr =>
                    forall ls n a a' e,
                      flatten tr = (a, ls) ->
                      (no_occ_of_n_in_tree n tr) ->
                      In (n.1, e, a') ls -> False)
            (P0 := fun br =>
                     forall ls n n' a e,
                       flatten_br n' br = ls ->
                       no_occ_of_n_in_branches n br ->
                       n.1 <> n' ->
                       (In (n.1, e, a) ls) ->
                       False).
          * intros. destruct a; simpl in *. inv H. inv H0.
            eapply IHtr; eauto.
          * intros; simpl in *; subst; inv H2.
          * intros; simpl in *.
            destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
            subst ls. inv H0.
            simpl in H2.
            destruct H2 as [H2 | H2].
            -- inv H2. congruence.
            -- apply in_app_or in H2.
               destruct H2 as [H2 | H2].
               ++ eapply IHtr; eauto.
               ++ eapply IHtr0; eauto. }
        contradiction.
      * by [].
  - revert H1 H2 H3.
    case: e => //= [C P' z C'].
    + move=> /= unic IN1.
      case: ifP => /andP.
      * move=> [] /eqP Ceq /eqP Peq //=.
        intros []; eauto.
        2: { inv H1; eauto. }
        inv H1.
        assert (exists e, In (n.1, e, a) ls) as [e in2].
        { clear -IN1.
          induction ls.
          - inv IN1.
          - destruct a0 as [[? [|]] ?]; simpl in *.
            + revert IN1. case: ifP => /eqP.
              intros ?; subst. simpl. intros []; eauto.
              inv H. eexists; left; eauto.
              exploit IHls; eauto. intros [? ?]; eauto.
              intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
            + exploit IHls; eauto. intros [? ?]. eauto. }
        clear -H H0 in2.
        { exfalso.
          revert H H0 in2.
          revert ls n a a' e.
          induction tr using tree_ind with
            (P := fun tr =>
                    forall ls n a a' e,
                      flatten tr = (a', ls) ->
                      (no_occ_of_n_in_tree n tr) ->
                      In (n.1, e, a) ls -> False)
            (P0 := fun br =>
                     forall ls n n' a e,
                       flatten_br n' br = ls ->
                       no_occ_of_n_in_branches n br ->
                       n.1 <> n' ->
                       (In (n.1, e, a) ls) ->
                       False).
          * intros. destruct a; simpl in *. inv H. inv H0.
            eapply IHtr; eauto.
          * intros; simpl in *; subst; inv H2.
          * intros; simpl in *.
            destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
            subst ls. inv H0.
            simpl in H2.
            destruct H2 as [H2 | H2].
            -- inv H2. congruence.
            -- apply in_app_or in H2.
               destruct H2 as [H2 | H2].
               ++ eapply IHtr; eauto.
               ++ eapply IHtr0; eauto. }
      * by [].
  - eapply H1; eauto.
Qed.

Lemma flatten_no_occ_unicity_incoming_calls C P tr n0 ls n e:
  flatten tr = (n0, ls) ->
  no_occ_of_n_in_tree n tr ->
  unicity_in (incoming_calls C P ls) ->
  unicity_in (incoming_calls C P ((n.1, e, n0) :: ls)).
Proof.
  intros ???.
  intros [c b] a a' IN IN'.
  replace (incoming_calls C P ((n.1, e, n0) :: ls))
    with ((incoming_calls C P [(n.1, e, n0)]) ++
            (incoming_calls C P ls)) in *.
  2: {
    unfold outgoing. rewrite -pmap_app. reflexivity.
  }
  (* replace (outgoing (cur_comp_of_event e) (ls ++ [:: (n.1, e, n0)])) *)
  (*   with ((outgoing (cur_comp_of_event e) ls) ++ (outgoing (cur_comp_of_event e) [:: (n.1, e, n0)])) in *. *)
  eapply in_app_or in IN.
  eapply in_app_or in IN'.
  destruct IN; destruct IN'.
  - move: H2 H3 => //=.
    clear H1.
    case: e => [Ccur Pnext z Cnext | ???] //=.
    case: ifP => /andP.
    + move=> [] /eqP Ceq /eqP Peq. simpl.
      intros []; eauto.
      * inv H1. intros []; inv H1. auto.
      * inv H1.
    + simpl. by [].
  (* - eapply H1; eauto. *)
  - revert H1 H2 H3.
    case: e => //= [Ccur P' z C'].
    + move=> /= unic.
      case: ifP => /andP.
      * move=> [] /eqP Ceq /eqP Peq //=.
        intros []; eauto. inv H1; eauto.
        intros IN1.
        assert (exists e, In (n.1, e, a') ls) as [e in2].
        { clear -IN1.
          induction ls.
          - inv IN1.
          - destruct a as [[? [|]] ?]; simpl in *.
            + revert IN1. case: ifP => /eqP.
              intros ?; subst. simpl. intros []; eauto.
              inv H. eexists; left; eauto.
              exploit IHls; eauto. intros [? ?]; eauto.
              intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
            + exploit IHls; eauto. intros [? ?]. eauto. }
        clear -H H0 in2.
        { exfalso.
          revert H H0 in2.
          revert ls n a a' e.
          induction tr using tree_ind with
            (P := fun tr =>
                    forall ls n a a' e,
                      flatten tr = (a, ls) ->
                      (no_occ_of_n_in_tree n tr) ->
                      In (n.1, e, a') ls -> False)
            (P0 := fun br =>
                     forall ls n n' a e,
                       flatten_br n' br = ls ->
                       no_occ_of_n_in_branches n br ->
                       n.1 <> n' ->
                       (In (n.1, e, a) ls) ->
                       False).
          * intros. destruct a; simpl in *. inv H. inv H0.
            eapply IHtr; eauto.
          * intros; simpl in *; subst; inv H2.
          * intros; simpl in *.
            destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
            subst ls. inv H0.
            simpl in H2.
            destruct H2 as [H2 | H2].
            -- inv H2. congruence.
            -- apply in_app_or in H2.
               destruct H2 as [H2 | H2].
               ++ eapply IHtr; eauto.
               ++ eapply IHtr0; eauto. }
        contradiction.
      * by [].
  - revert H1 H2 H3.
    case: e => //= [Ccur P' z C'].
    + move=> /= unic IN1.
      case: ifP => /andP.
      * move=> [] /eqP Ceq /eqP Peq //=.
        intros []; eauto.
        2: { inv H1; eauto. }
        inv H1.
        assert (exists e, In (n.1, e, a) ls) as [e in2].
        { clear -IN1.
          induction ls.
          - inv IN1.
          - destruct a0 as [[? [|]] ?]; simpl in *.
            + revert IN1. case: ifP => /eqP.
              intros ?; subst. simpl. intros []; eauto.
              inv H. eexists; left; eauto.
              exploit IHls; eauto. intros [? ?]; eauto.
              intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
            + exploit IHls; eauto. intros [? ?]. eauto. }
        clear -H H0 in2.
        { exfalso.
          revert H H0 in2.
          revert ls n a a' e.
          induction tr using tree_ind with
            (P := fun tr =>
                    forall ls n a a' e,
                      flatten tr = (a', ls) ->
                      (no_occ_of_n_in_tree n tr) ->
                      In (n.1, e, a) ls -> False)
            (P0 := fun br =>
                     forall ls n n' a e,
                       flatten_br n' br = ls ->
                       no_occ_of_n_in_branches n br ->
                       n.1 <> n' ->
                       (In (n.1, e, a) ls) ->
                       False).
          * intros. destruct a; simpl in *. inv H. inv H0.
            eapply IHtr; eauto.
          * intros; simpl in *; subst; inv H2.
          * intros; simpl in *.
            destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
            subst ls. inv H0.
            simpl in H2.
            destruct H2 as [H2 | H2].
            -- inv H2. congruence.
            -- apply in_app_or in H2.
               destruct H2 as [H2 | H2].
               ++ eapply IHtr; eauto.
               ++ eapply IHtr0; eauto. }
      * by [].
  - eapply H1; eauto.
Qed.

Lemma flatten_no_occ_unicity_incoming_returns C tr n0 ls n e:
  flatten tr = (n0, ls) ->
  no_occ_of_n_in_tree n tr ->
  unicity_in (incoming_returns C ls) ->
  unicity_in (incoming_returns C ((n.1, e, n0) :: ls)).
Proof.
  intros ???.
  intros [c b] a a' IN IN'.
  replace (incoming_returns C ((n.1, e, n0) :: ls))
    with ((incoming_returns C [(n.1, e, n0)]) ++
            (incoming_returns C ls)) in *.
  2: {
    unfold outgoing. rewrite -pmap_app. reflexivity.
  }
  (* replace (outgoing (cur_comp_of_event e) (ls ++ [:: (n.1, e, n0)])) *)
  (*   with ((outgoing (cur_comp_of_event e) ls) ++ (outgoing (cur_comp_of_event e) [:: (n.1, e, n0)])) in *. *)
  eapply in_app_or in IN.
  eapply in_app_or in IN'.
  destruct IN; destruct IN'.
  - move: H2 H3 => //=.
    clear H1.
    case: e => [Ccur Pnext z Cnext | ???] //=.
    case: ifP => /eqP ?; subst.
    + intros []; eauto.
      * inv H1. intros []; inv H1. auto.
      * inv H1.
    + simpl. by [].
  (* - eapply H1; eauto. *)
  - revert H1 H2 H3.
    case: e => //= [Ccur z C'].
    + move=> /= unic.
      case: ifP.
      * move=> /eqP Ceq //=.
        intros []; eauto. inv H1; eauto.
        intros IN1.
        assert (exists e, In (n.1, e, a') ls) as [e in2].
        { clear -IN1.
          induction ls.
          - inv IN1.
          - destruct a as [[? [|]] ?]; simpl in *.
            + exploit IHls; eauto. intros [? ?]. eauto.
            + revert IN1.
              case: ifP => /eqP.
              intros ?; subst. simpl. intros []; eauto.
              inv H. eexists; left; eauto.
              exploit IHls; eauto. intros [? ?]; eauto.
              intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto. }
        clear -H H0 in2.
        { exfalso.
          revert H H0 in2.
          revert ls n a a' e.
          induction tr using tree_ind with
            (P := fun tr =>
                    forall ls n a a' e,
                      flatten tr = (a, ls) ->
                      (no_occ_of_n_in_tree n tr) ->
                      In (n.1, e, a') ls -> False)
            (P0 := fun br =>
                     forall ls n n' a e,
                       flatten_br n' br = ls ->
                       no_occ_of_n_in_branches n br ->
                       n.1 <> n' ->
                       (In (n.1, e, a) ls) ->
                       False).
          * intros. destruct a; simpl in *. inv H. inv H0.
            eapply IHtr; eauto.
          * intros; simpl in *; subst; inv H2.
          * intros; simpl in *.
            destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
            subst ls. inv H0.
            simpl in H2.
            destruct H2 as [H2 | H2].
            -- inv H2. congruence.
            -- apply in_app_or in H2.
               destruct H2 as [H2 | H2].
               ++ eapply IHtr; eauto.
               ++ eapply IHtr0; eauto. }
        contradiction.
      * by [].
  - revert H1 H2 H3.
    case: e => //= [Ccur z C'].
    + move=> /= unic IN1.
      case: ifP.
      * move=> /eqP Ceq //=.
        intros []; eauto.
        2: { inv H1; eauto. }
        inv H1.
        assert (exists e, In (n.1, e, a) ls) as [e in2].
        { clear -IN1.
          induction ls.
          - inv IN1.
          - destruct a0 as [[? [|]] ?]; simpl in *.
            + exploit IHls; eauto. intros [? ?]. eauto.
            + revert IN1. case: ifP => /eqP.
              intros ?; subst. simpl. intros []; eauto.
              inv H. eexists; left; eauto.
              exploit IHls; eauto. intros [? ?]; eauto.
              intros ?. simpl. intros ?. exploit IHls; eauto. intros [? ?]; eauto.
              }
        clear -H H0 in2.
        { exfalso.
          revert H H0 in2.
          revert ls n a a' e.
          induction tr using tree_ind with
            (P := fun tr =>
                    forall ls n a a' e,
                      flatten tr = (a', ls) ->
                      (no_occ_of_n_in_tree n tr) ->
                      In (n.1, e, a) ls -> False)
            (P0 := fun br =>
                     forall ls n n' a e,
                       flatten_br n' br = ls ->
                       no_occ_of_n_in_branches n br ->
                       n.1 <> n' ->
                       (In (n.1, e, a) ls) ->
                       False).
          * intros. destruct a; simpl in *. inv H. inv H0.
            eapply IHtr; eauto.
          * intros; simpl in *; subst; inv H2.
          * intros; simpl in *.
            destruct (flatten tr) as [n0 ls0] eqn:flatten_tr.
            subst ls. inv H0.
            simpl in H2.
            destruct H2 as [H2 | H2].
            -- inv H2. congruence.
            -- apply in_app_or in H2.
               destruct H2 as [H2 | H2].
               ++ eapply IHtr; eauto.
               ++ eapply IHtr0; eauto. }
      * by [].
  - eapply H1; eauto.
Qed.

Lemma unicity_in_incoming_call_app C P:
  forall es loc b,
  unicity_in (incoming_calls C P (flatten_br loc b)) ->
  unicity_in (incoming_calls C P es) ->
  (forall (k : nat) (e : Z) (n' : nat),
       In (k, e, n') (incoming_calls C P es) ->
       k <> loc /\
       (forall n'' : nat,
        In (k, e, n'') (incoming_calls C P (flatten_br loc b)) -> n' = n'')) ->
  unicity_in (incoming_calls C P (es ++ flatten_br loc b)).
Proof.
  induction es; eauto.
  intros loc b uni1 uni2 HYP.
  destruct a as [[k e] n]. simpl.
  destruct e as [Ccur Pnext z Cnext |]; try eauto.

  assert (unicity_in (incoming_calls C P es)).
  { clear -uni2.
    revert uni2. simpl.
    case: ifP => //=.
    intros _. eapply unicity_in_smaller. }
  specialize (IHes _ _ uni1 H).
  assert (forall (k : nat) (e : Z) (n' : nat),
          In (k, e, n') (incoming_calls C P es) ->
          k <> loc /\
          (forall n'' : nat,
           In (k, e, n'') (incoming_calls C P (flatten_br loc b)) ->
           n' = n'')).
  { intros. eapply HYP. simpl.
    case: ifP. intros _. right; eauto.
    eauto. }
  specialize (IHes H0).
  case: ifP => //=; try eauto.
  move=> /andP [] /eqP ? /eqP ?; subst.
  simpl in uni2. rewrite !eqxx in uni2. simpl in uni2.
  simpl in HYP. rewrite !eqxx in HYP. simpl in HYP.
  intros [c b'] a a' IN IN'.
  destruct IN as [IN | IN]; destruct IN' as [IN' | IN'].
  - congruence.
  - inv IN.
    replace (incoming_calls Cnext Pnext (es ++ flatten_br loc b))
      with (incoming_calls Cnext Pnext es ++ incoming_calls Cnext Pnext (flatten_br loc b)) in IN'.
    2: { unfold incoming_calls; rewrite pmap_app; auto. }
    eapply in_app_or in IN'.
    destruct IN'.
    + eapply uni2. left; auto. right; eauto.
    + eapply HYP. left; auto. eauto.
  - inv IN'.
    replace (incoming_calls Cnext Pnext (es ++ flatten_br loc b))
      with (incoming_calls Cnext Pnext es ++ incoming_calls Cnext Pnext (flatten_br loc b)) in IN.
    2: { unfold incoming_calls; rewrite pmap_app; auto. }
    eapply in_app_or in IN.
    destruct IN.
    + eapply uni2. right; eauto. left; auto.
    + symmetry. eapply HYP. left; auto. eauto.
  - eapply IHes; eauto.
Qed.

Lemma unicity_in_incoming_return_app C:
  forall es loc b,
  unicity_in (incoming_returns C (flatten_br loc b)) ->
  unicity_in (incoming_returns C es) ->
  (forall (k : nat) (e : Z) (n' : nat),
       In (k, e, n') (incoming_returns C es) ->
       k <> loc /\
       (forall n'' : nat,
        In (k, e, n'') (incoming_returns C (flatten_br loc b)) -> n' = n'')) ->
  unicity_in (incoming_returns C (es ++ flatten_br loc b)).
Proof.
  induction es; eauto.
  intros loc b uni1 uni2 HYP.
  destruct a as [[k e] n]. simpl.
  destruct e as [Ccur Pnext z Cnext | Ccur z Cnext]; try eauto.

  assert (unicity_in (incoming_returns C es)).
  { clear -uni2.
    revert uni2. simpl.
    case: ifP => //=.
    intros _. eapply unicity_in_smaller. }
  specialize (IHes _ _ uni1 H).
  assert (forall (k : nat) (e : Z) (n' : nat),
          In (k, e, n') (incoming_returns C es) ->
          k <> loc /\
          (forall n'' : nat,
           In (k, e, n'') (incoming_returns C (flatten_br loc b)) ->
           n' = n'')).
  { intros. eapply HYP. simpl.
    case: ifP. intros _. right; eauto.
    eauto. }
  specialize (IHes H0).
  case: ifP => //=; try eauto.
  move=> /eqP ?; subst.
  simpl in uni2. rewrite !eqxx in uni2. simpl in uni2.
  simpl in HYP. rewrite !eqxx in HYP. simpl in HYP.
  intros [c b'] a a' IN IN'.
  destruct IN as [IN | IN]; destruct IN' as [IN' | IN'].
  - congruence.
  - inv IN.
    replace (incoming_returns Cnext (es ++ flatten_br loc b))
      with (incoming_returns Cnext es ++ incoming_returns Cnext (flatten_br loc b)) in IN'.
    2: { unfold incoming_returns; rewrite pmap_app; auto. }
    eapply in_app_or in IN'.
    destruct IN'.
    + eapply uni2. left; auto. right; eauto.
    + eapply HYP. left; auto. eauto.
  - inv IN'.
    replace (incoming_returns Cnext (es ++ flatten_br loc b))
      with (incoming_returns Cnext es ++ incoming_returns Cnext (flatten_br loc b)) in IN.
    2: { unfold incoming_returns; rewrite pmap_app; auto. }
    eapply in_app_or in IN.
    destruct IN.
    + eapply uni2. right; eauto. left; auto.
    + symmetry. eapply HYP. left; auto. eauto.
  - eapply IHes; eauto.
Qed.

Lemma wf_compile_stack_tree (p: StackTree.prg):
  StackTree.wf p ->
  Flattened.wf (compile_stack_tree p).
Proof.
  intros [].
  constructor; eauto.
  - simpl. rewrite wfprog_defined_procedures0.
    now rewrite domm_map.
  - simpl in *.
    move=> C; rewrite mapmE //=.
    move: (unique_current C) (determinacy C) (unicity_loc C).
    case: (StackTree.prog_trees p C) => //=.
    move=> tr /(_ _ Logic.eq_refl) unic.
    move=> /(_ _ Logic.eq_refl) det.
    move=> /(_ _ Logic.eq_refl) unin.
    inv unin. rename H into unin.
    move: unic det unin. clear.


    assert (forall tr loc es, (loc, es) = flatten tr ->
                              unique_current_tree C tr ->
                              deterministic_tree tr ->
                              (forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr) ->
                              unicity_in2 (outgoing C es)).

    { clear tr.
      induction tr using tree_ind with
        (P := fun tr => forall loc es, (loc, es) = flatten tr ->
                                       unique_current_tree C tr ->
                                       deterministic_tree tr ->
                                       (forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr) ->
                                       unicity_in2 (outgoing C es))
        (P0 := fun br => forall loc es, es = flatten_br loc br ->
                                        unique_current_branches C br ->
                                        deterministic_branches br ->
                                        no_occ_of_n_in_branches (loc, []) br ->
                                        (forall n, no_occ_of_n_in_branches n br \/ unique_occ_of_n_in_branches n br) ->
                                        unicity_in2 (outgoing C es)).
      - destruct a. simpl in *.
        intros loc es H; inv H.
        move=> unib det occ.
        inv det.
        eapply IHtr; eauto.
        { intros. exploit occ; eauto.
          intros [].
          + inv H. eauto.
          + inv H; eauto. simpl in H4; congruence.
        }
        intros. exploit occ; eauto.
        intros [].
        + inv H. left; eauto.
        + inv H; [left | right]; eauto.
      - intros; subst; simpl. by [].
      - intros loc es es_eq unibcons detbcons occ_loc occ; subst. simpl in unibcons. inv detbcons.
        move: unibcons => /andP [] unitr.
        destruct (flatten tr) as [loc' es] eqn:flatten_tr.
        assert (occ': forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr).
        { intros.
          exploit occ; eauto.
          intros [H | H]; inv H; eauto. }
        specialize (IHtr loc' es Logic.eq_refl unitr H3 occ'). clear occ'.
        case: ifP.
        + intros e_C.
          destruct b; try congruence.
          intros _. simpl. rewrite flatten_tr.
          replace (outgoing C ((loc, e, loc') :: es ++ [::])) with
            (outgoing C ((loc, e, loc') :: es)).
          2: { rewrite cats0. auto. }
          replace es with (flatten tr).2 in IHtr.
          2: { rewrite flatten_tr; eauto. }
          replace es with (flatten tr).2.
          2: { rewrite flatten_tr; eauto. }
          (* replace (outgoing C es) with (outgoing C (flatten tr).2) in IHtr. *)
          replace loc with (loc, []: stack).1 by reflexivity.
          move: e_C => /eqP ?. subst C.
          eapply flatten_no_occ_unicity; eauto. rewrite flatten_tr. eauto.
          inv occ_loc. eauto.
        + intros e_C unib.
          simpl. rewrite flatten_tr.
          replace ((outgoing C ((loc, e, loc') :: es ++ flatten_br loc b))) with
            (outgoing C (es ++ flatten_br loc b)).
          2: { destruct e; simpl in *.
               assert ((C == i) = false) as ->. apply /eqP. move: e_C => /eqP. auto. simpl. auto.
               assert ((C == i) = false) as ->. apply /eqP. move: e_C => /eqP. auto. simpl. auto. }
          assert (G: no_occ_of_n_in_branches (loc, [::]) b).
          { inv occ_loc; eauto. }
          assert (G': forall n, no_occ_of_n_in_branches n b \/ unique_occ_of_n_in_branches n b).
          { intros. exploit occ. intros [].
            - inv H; eauto.
            - inv H; eauto. }
          specialize (IHtr0 loc (flatten_br loc b) Logic.eq_refl unib H2 G G').
          eapply flatten_unicity''; eauto.
          intros [k s] e0 n'. simpl.
          clear -flatten_tr occ occ_loc.
          { intros H. split.
            - inv occ_loc. clear -H H5 flatten_tr.
              revert flatten_tr H H5.
              revert loc' es loc k e0 n'.
              induction tr using tree_ind with
                (P := fun tr => forall (loc' : nat) (es : seq (nat * event * nat))
                               (loc k : nat) (e0 : event) (n' : nat),
                          flatten tr = (loc', es) ->
                          In (k, e0, n') es ->
                          no_occ_of_n_in_tree (loc, [::]) tr ->
                          k <> loc)
                (P0 := fun br => forall es k e0 n n' loc,
                           n <> loc ->
                           flatten_br n br = es ->
                           In (k, e0, n') es -> no_occ_of_n_in_branches (loc, [::]) br ->
                           k <> loc).
              + intros. inv H1. simpl in H.
                destruct a; simpl in *. inv H.
                eapply IHtr. 3: eauto. 2: eauto. 2: eauto. eauto.
              + intros. simpl in H0. subst. by [].
              + intros es k e0 n n' loc n_loc.
                simpl. destruct (flatten tr) as [n0 ls] eqn:flatten_tr.
                intros ?; subst es. simpl.
                intros H.
                destruct H as [H | H].
                * inv H. eauto.
                * intros G. inv G.
                  eapply in_app_or in H as [H | H].
                  -- eapply IHtr; eauto.
                  -- eapply IHtr0; eauto.
            - specialize (occ (k, s)) as [occ | occ]; try now (inv occ; eauto).
              inv occ; eauto.
              exfalso.
              clear -H H5 flatten_tr.
              revert es loc' k e0 n' s flatten_tr H H5.
              induction tr using tree_ind with
                (P := fun tr => forall (es : seq (nat * event * nat)) (loc' k : nat) (e0 : event)
                               (n' : nat) (s : stack),
                          flatten tr = (loc', es) ->
                          In (k, e0, n') es ->
                          no_occ_of_n_in_tree (k, s) tr ->
                          False)
                (P0 := fun br => forall es k e0 loc n' s,
                           loc <> k ->
                           flatten_br loc br = es ->
                           In (k, e0, n') es ->
                           no_occ_of_n_in_branches (k, s) br ->
                           False).
              + intros. inv H1. simpl in H.
                destruct a; simpl in *. inv H.
                eapply IHtr. 3: eauto. 2: eauto. eauto. eauto.
              + intros. simpl in H. subst. by [].
              + intros es k e0 loc n' s loc_k.
                simpl. destruct (flatten tr) as [n0 ls] eqn:flatten_tr.
                intros ?; subst es. simpl.
                intros H.
                destruct H as [H | H].
                * inv H. congruence.
                * intros G. inv G.
                  eapply in_app_or in H as [H | H].
                  -- eapply IHtr; eauto.
                  -- eapply IHtr0; eauto.
          }
    }
    intros. destruct (flatten tr) eqn:?.
    inv H0. eapply H; eauto.
  - simpl in *.
    move=> C P; rewrite mapmE //=.
    move: (unique_current C) (determinacy C) (unicity_loc C).
    case: (StackTree.prog_trees p C) => //=.
    move=> tr /(_ _ Logic.eq_refl) unic.
    move=> /(_ _ Logic.eq_refl) det.
    move=> /(_ _ Logic.eq_refl) unin.
    inv unin. rename H into unin.
    move: unic det unin. clear.
    assert (forall tr loc es, (loc, es) = flatten tr ->
                         unique_current_tree C tr ->
                         deterministic_tree tr ->
                         (forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr) ->
                         unicity_in (incoming_calls C P es)).

    { clear tr.
      induction tr using tree_ind with
        (P := fun tr => forall loc es, (loc, es) = flatten tr ->
                                       unique_current_tree C tr ->
                                       deterministic_tree tr ->
                                       (forall n, no_occ_of_n_in_tree n tr \/
                                               unique_occ_of_n_in_tree n tr) ->
                                       unicity_in (incoming_calls C P es))
        (P0 := fun br => forall loc es, es = flatten_br loc br ->
                                        unique_current_branches C br ->
                                        deterministic_branches br ->
                                        no_occ_of_n_in_branches (loc, []) br ->
                                        (forall n, no_occ_of_n_in_branches n br \/
                                                unique_occ_of_n_in_branches n br) ->
                                        unicity_in (incoming_calls C P es)).
      - destruct a. simpl in *.
        intros loc es H; inv H.
        move=> unib det occ.
        inv det.
        eapply IHtr; eauto.
        { intros. exploit occ; eauto.
          intros [].
          + inv H. eauto.
          + inv H; eauto. simpl in H4; congruence.
        }
        intros. exploit occ; eauto.
        intros [].
        + inv H. left; eauto.
        + inv H; [left | right]; eauto.
      - intros; subst; simpl. by [].
      - intros loc es es_eq unibcons detbcons occ_loc occ; subst. simpl in unibcons. inv detbcons.
        move: unibcons => /andP [] unitr.
        destruct (flatten tr) as [loc' es] eqn:flatten_tr.
        assert (occ': forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr).
        { intros.
          exploit occ; eauto.
          intros [H | H]; inv H; eauto. }
        specialize (IHtr loc' es Logic.eq_refl unitr H3 occ'). clear occ'.
        case: ifP.
        + intros e_C.
          destruct b; try congruence.
          intros _. simpl. rewrite flatten_tr.
          replace (incoming_calls C P ((loc, e, loc') :: es ++ [::])) with
            (incoming_calls C P ((loc, e, loc') :: es)).
          2: { rewrite cats0. auto. }
          replace es with (flatten tr).2 in IHtr.
          2: { rewrite flatten_tr; eauto. }
          replace es with (flatten tr).2.
          2: { rewrite flatten_tr; eauto. }
          (* replace (outgoing C es) with (outgoing C (flatten tr).2) in IHtr. *)
          replace loc with (loc, []: stack).1 by reflexivity.
          move: e_C => /eqP ?. subst C.
          eapply flatten_no_occ_unicity_incoming_calls; eauto. rewrite flatten_tr. eauto.
          inv occ_loc. eauto.
        + intros ?. intros unibr.
          assert (G1: no_occ_of_n_in_branches (loc, [::]) b)
                   by now inversion occ_loc.
          assert (G2: (forall n : loc_stack,
           no_occ_of_n_in_branches n b \/ unique_occ_of_n_in_branches n b)).
          { intros. exploit occ. intros []; eauto.
            inv H; eauto.
            inv H; eauto. }
          assert (G3: (forall n : loc_stack,
           no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr)).
          { intros. exploit occ. intros []; eauto.
            inv H; eauto.
            inv H; eauto. }
          assert (G4: no_occ_of_n_in_tree (loc, [::]) tr).
          { intros. inv occ_loc; eauto. }
          specialize (IHtr0 _ _ Logic.eq_refl unibr H2 G1 G2).
          simpl. rewrite flatten_tr.
          assert (unicity_in (incoming_calls C P ((loc, e, loc') :: es))).
          { replace loc with (loc, []: stack).1 by reflexivity.
            eapply flatten_no_occ_unicity_incoming_calls; eauto. }
          assert (forall k e n',
                     In (k, e, n') (incoming_calls C P es) ->
                     k <> loc /\
                       (forall n'', In (k, e, n'') (incoming_calls C P (flatten_br loc b)) ->
                               n' = n'')).
          { intros k e0 n' IN. split.
            - revert flatten_tr G4 IN.
              clear.
              revert loc' es loc k e0 n'.
              induction tr using tree_ind with
                (P := fun tr => forall (loc' : nat) (es : seq (nat * event * nat))
                               (loc k : nat) e0 (n' : nat),
                          flatten tr = (loc', es) ->
                          no_occ_of_n_in_tree (loc, [::]) tr ->
                          In (k, e0, n') (incoming_calls C P es) ->
                          k <> loc)
                (P0 := fun br => forall es k e0 n n' loc,
                           n <> loc ->
                           flatten_br n br = es ->
                           In (k, e0, n') (incoming_calls C P es) ->
                           no_occ_of_n_in_branches (loc, [::]) br ->
                           k <> loc).
              + intros. inv H0. simpl in H.
                destruct a; simpl in *. inv H.
                eapply IHtr. 3: eauto. 2: eauto. 2: eauto. eauto.
              + intros. simpl in H0. subst. by [].
              + intros es k e0 n n' loc n_loc.
                simpl. destruct (flatten tr) as [n0 ls] eqn:flatten_tr.
                intros ?; subst es. simpl.
                intros H.
                destruct e; simpl in *.
                2: { intros G. inv G.

                     intros G. inv G.
                     replace (incoming_calls C P (ls ++ flatten_br n b))
                       with (incoming_calls C P ls ++ incoming_calls C P (flatten_br n b)) in H.
                     eapply in_app_or in H as [H | H].
                     -- eapply IHtr; eauto.
                     -- eapply IHtr0; eauto.
                     -- unfold incoming_calls. rewrite pmap_app. auto. }
                move: H.
                case: ifP. move => /andP [].
                move=> /eqP ? /eqP ?; subst. simpl.
                intros H.
                destruct H as [H | H].
                * inv H. eauto.
                * intros G. inv G.
                  replace (incoming_calls i1 i0 (ls ++ flatten_br n b))
                    with (incoming_calls i1 i0 ls ++ incoming_calls i1 i0 (flatten_br n b)) in H.
                  eapply in_app_or in H as [H | H].
                  -- eapply IHtr; eauto.
                  -- eapply IHtr0; eauto.
                  -- unfold incoming_calls. rewrite pmap_app. auto.
                * simpl. intros ? G H. inv H.
                  replace (incoming_calls C P (ls ++ flatten_br n b))
                    with (incoming_calls C P ls ++ incoming_calls C P (flatten_br n b)) in G.
                  eapply in_app_or in G as [G | G].
                  -- eapply IHtr; eauto.
                  -- eapply IHtr0; eauto.
                  -- unfold incoming_calls. rewrite pmap_app. auto.
            - intros n''. revert IN.
              revert k e0 n' n''.
              assert (forall k e0 n' ls,
                         In (k, e0, n') (incoming_calls C P ls) ->
                         exists e, In (k, e, n') ls).
              { clear. intros until ls.
                revert k e0 n'.
                induction ls.
                - simpl; eauto. by [].
                - simpl.
                  destruct a as [[? [|]]]; simpl.
                  2: { intros. exploit IHls; eauto. intros [? ?].
                       eexists;  right; eauto. }
                  case: ifP => //=.
                  2: { intros. exploit IHls; eauto. intros [? ?].
                       eexists;  right; eauto. }
                  move=> /andP [] /eqP ? /eqP ?; subst.
                  intros ??? [H | H].
                  + inv H. eexists; left; eauto.
                  + exploit IHls; eauto. intros [? ?].
                    eexists;  right; eauto. }
              intros k z n' n'' IN1 IN2.
              eapply H0 in IN1 as [e1 IN1].
              eapply H0 in IN2 as [e2 IN2].
              exfalso.
              clear -IN1 IN2 flatten_tr occ occ_loc.
              specialize (occ (k, [::])).
              destruct occ.
              + inv H. clear - flatten_tr H5 IN1.
                revert loc' es k e1 n' flatten_tr H5 IN1.
                induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                * intros. destruct a; simpl in *.
                  inv H0. inv H.
                  eapply IHtr; eauto.
                * intros. simpl in *. subst. by [].
                * intros. simpl in *.
                  destruct (flatten tr) eqn:flatten_tr.
                  subst.
                  inv H2. congruence.
                  apply in_app_or in H0.
                  destruct H0.
                  -- eapply IHtr; eauto. inv H1; eauto.
                  -- eapply IHtr0; eauto. inv H1; eauto.
              + inv H.
                * assert (k = loc).
                  { clear -IN2 H3.
                    revert k e2 n'' loc IN2 H3.
                    induction b using branches_ind with
                      (P0 := fun br => forall k e2 n'' loc,
                               In (k, e2, n'') (flatten_br loc br) ->
                               no_occ_of_n_in_branches (k, [::]) br ->
                               k = loc)
                      (P := fun tr => forall k e n'' es loc,
                                flatten tr = (loc, es) ->
                                In (k, e, n'') es ->
                                no_occ_of_n_in_tree (k, [::]) tr ->
                                False).
                    - intros. destruct a. simpl in *. inv H.
                      inv H1. simpl in *.
                      eapply H4.
                      eapply IHb. eauto. eauto.
                    - intros. inv H.
                    - intros. simpl in *.
                      destruct (flatten t) eqn:flatten_tr.
                      simpl in *.
                      destruct H.
                      + inv H. auto.
                      + apply in_app_or in H. destruct H as [H | H].
                        * exfalso. eapply IHb; eauto.
                          inv H0. eauto.
                        * eapply IHb0. eauto. inv H0. eauto.
                  }
                  subst.
                  inv occ_loc. clear -H5 H6.
                  revert loc H5 H6.
                  induction tr using tree_ind with
                    (P := fun tr => forall loc,
                              unique_occ_of_n_in_tree (loc, [::]) tr ->
                              no_occ_of_n_in_tree (loc, [::]) tr -> False)
                    (P0 := fun br => forall loc,
                               unique_occ_of_n_in_branches (loc, [::]) br ->
                               no_occ_of_n_in_branches (loc, [::]) br -> False).
                  -- intros. inv H. inv H0. eauto.
                     eapply IHtr. eauto. inv H0; eauto.
                  -- intros. inv H.
                  -- intros. inv H0.
                     inv H.
                     ++ eapply IHtr; eauto.
                     ++ eapply IHtr0; eauto.
                * clear - flatten_tr H5 IN1.
                  revert loc' es k e1 n' flatten_tr H5 IN1.
                  induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                  -- intros. destruct a; simpl in *.
                     inv H0. inv H.
                     eapply IHtr; eauto.
                  -- intros. simpl in *. subst. by [].
                  -- intros. simpl in *.
                     destruct (flatten tr) eqn:flatten_tr.
                     subst.
                     inv H2. congruence.
                     apply in_app_or in H0.
                     destruct H0.
                     ++ eapply IHtr; eauto. inv H1; eauto.
                     ++ eapply IHtr0; eauto. inv H1; eauto.
          }





          destruct e.
          2: { simpl. eapply unicity_in_incoming_call_app; eauto. }
          simpl. case: ifP => //=.
          2: { simpl. intros _. eapply unicity_in_incoming_call_app; eauto. }

          assert (G: unicity_in (incoming_calls C P (es ++ flatten_br loc b))).
          eapply unicity_in_incoming_call_app; eauto.

          move=> /andP [] /eqP ? /eqP ?; subst i1 i0.

          intros [c b'] a a' IN IN'.
          destruct IN as [IN | IN]; destruct IN' as [IN' | IN'].
          * congruence.
          * inv IN.
            replace (incoming_calls C P (es ++ flatten_br c b))
              with (incoming_calls C P es ++ incoming_calls C P (flatten_br c b)) in IN'.
            2: { unfold incoming_calls; rewrite pmap_app; auto. }
            eapply in_app_or in IN'.
            destruct IN'.
            -- eapply H; eauto.
               simpl. rewrite !eqxx /=. left; eauto.
               simpl. rewrite !eqxx /=. right; eauto.
            -- clear -H4 H1 G1.
               exfalso.
               assert (exists e, match_incoming (ECall i P b' C) e /\
                              In (c, e, a') (flatten_br c b))
                        as [e [MS IN]].
               { revert H1. generalize (flatten_br c b).
                 clear.
                 induction l.
                 - simpl. by [].
                 - destruct a as [[n0 e] n1].
                   simpl. destruct e; simpl in *.
                   2: { intros H. exploit IHl; eauto. intros [? [? ?]]; eauto. }
                   case: ifP => //=.
                   2: { simpl. intros H H'. exploit IHl; eauto. simpl. intros [? [? ?]]; eauto. }
                   move=> /andP [] /eqP ? /eqP ?; subst i1 i2.
                   intros H; destruct H as [H | H].
                   inv H. eexists; split; eauto. simpl. auto.
                   exploit IHl; eauto. intros [? [? ?]]; eauto. }
               clear -H4 MS IN G1.
               revert H4 MS IN G1.
               generalize (ECall i P b' C). intros e0 H.
               induction H.
               ++ eauto.
               ++ intros. simpl in IN.
                  destruct (flatten tr) as [n ls] eqn:?.
                  simpl in IN.
                  destruct IN.
                  ** inv H1. contradiction.
                  ** eapply in_app_or in H1.
                     destruct H1 as [H1 | H1].
                     --- inv G1. clear -Heqp H1 H7.
                         revert Heqp H7 H1.
                         revert n ls c e a'.
                  induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                  +++ intros. destruct a; simpl in *.
                      inv H0. inv H.
                      eapply IHtr; eauto.
                  +++ intros. simpl in *. subst. by [].
                  +++ intros. simpl in *.
                      destruct (flatten tr) eqn:flatten_tr.
                      subst.
                      inv H2. congruence.
                      apply in_app_or in H0.
                      destruct H0.
                      *** eapply IHtr; eauto. inv H1; eauto.
                      *** eapply IHtr0; eauto. inv H1; eauto.
                 --- eapply IHdo_not_appear_in; eauto.
                         inv G1; eauto.
          * inv IN'.
            replace (incoming_calls C P (es ++ flatten_br c b))
              with (incoming_calls C P es ++ incoming_calls C P (flatten_br c b)) in IN.
            2: { unfold incoming_calls; rewrite pmap_app; auto. }
            eapply in_app_or in IN.
            destruct IN.
            -- symmetry. eapply H; eauto.
               simpl. rewrite !eqxx /=. left; eauto.
               simpl. rewrite !eqxx /=. right; eauto.
            -- clear -H4 H1 G1.
               exfalso.
               assert (exists e, match_incoming (ECall i P b' C) e /\
                              In (c, e, a) (flatten_br c b))
                        as [e [MS IN]].
               { revert H1. generalize (flatten_br c b).
                 clear.
                 induction l.
                 - simpl. by [].
                 - destruct a0 as [[n0 e] n1].
                   simpl. destruct e; simpl in *.
                   2: { intros H. exploit IHl; eauto. intros [? [? ?]]; eauto. }
                   case: ifP => //=.
                   2: { simpl. intros H H'. exploit IHl; eauto. simpl. intros [? [? ?]]; eauto. }
                   move=> /andP [] /eqP ? /eqP ?; subst i1 i2.
                   intros H; destruct H as [H | H].
                   inv H. eexists; split; eauto. simpl. auto.
                   exploit IHl; eauto. intros [? [? ?]]; eauto. }
               clear -H4 MS IN G1.
               revert H4 MS IN G1.
               generalize (ECall i P b' C). intros e0 H.
               induction H.
               ++ eauto.
               ++ intros. simpl in IN.
                  destruct (flatten tr) as [n ls] eqn:?.
                  simpl in IN.
                  destruct IN.
                  ** inv H1. contradiction.
                  ** eapply in_app_or in H1.
                     destruct H1 as [H1 | H1].
                     --- inv G1. clear -Heqp H1 H7.
                         revert Heqp H7 H1.
                         revert n ls c e a.
                  induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                  +++ intros. destruct a; simpl in *.
                      inv H0. inv H.
                      eapply IHtr; eauto.
                  +++ intros. simpl in *. subst. by [].
                  +++ intros. simpl in *.
                      destruct (flatten tr) eqn:flatten_tr.
                      subst.
                      inv H2. congruence.
                      apply in_app_or in H0.
                      destruct H0.
                      *** eapply IHtr; eauto. inv H1; eauto.
                      *** eapply IHtr0; eauto. inv H1; eauto.
                 --- eapply IHdo_not_appear_in; eauto.
                         inv G1; eauto.
          * eapply G; eauto.
            }
    intros. destruct (flatten tr) eqn:?.
    inv H0. eapply H; eauto.
  - simpl in *.
    move=> C; rewrite mapmE //=.
    move: (unique_current C) (determinacy C) (unicity_loc C).
    case: (StackTree.prog_trees p C) => //=.
    move=> tr /(_ _ Logic.eq_refl) unic.
    move=> /(_ _ Logic.eq_refl) det.
    move=> /(_ _ Logic.eq_refl) unin.
    inv unin. rename H into unin.
    move: unic det unin. clear.
    assert (forall tr loc es, (loc, es) = flatten tr ->
                         unique_current_tree C tr ->
                         deterministic_tree tr ->
                         (forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr) ->
                         unicity_in (incoming_returns C es)).

    { clear tr.
      induction tr using tree_ind with
        (P := fun tr => forall loc es, (loc, es) = flatten tr ->
                                       unique_current_tree C tr ->
                                       deterministic_tree tr ->
                                       (forall n, no_occ_of_n_in_tree n tr \/
                                               unique_occ_of_n_in_tree n tr) ->
                                       unicity_in (incoming_returns C es))
        (P0 := fun br => forall loc es, es = flatten_br loc br ->
                                        unique_current_branches C br ->
                                        deterministic_branches br ->
                                        no_occ_of_n_in_branches (loc, []) br ->
                                        (forall n, no_occ_of_n_in_branches n br \/
                                                unique_occ_of_n_in_branches n br) ->
                                        unicity_in (incoming_returns C es)).
      - destruct a. simpl in *.
        intros loc es H; inv H.
        move=> unib det occ.
        inv det.
        eapply IHtr; eauto.
        { intros. exploit occ; eauto.
          intros [].
          + inv H. eauto.
          + inv H; eauto. simpl in H4; congruence.
        }
        intros. exploit occ; eauto.
        intros [].
        + inv H. left; eauto.
        + inv H; [left | right]; eauto.
      - intros; subst; simpl. by [].
      - intros loc es es_eq unibcons detbcons occ_loc occ; subst. simpl in unibcons. inv detbcons.
        move: unibcons => /andP [] unitr.
        destruct (flatten tr) as [loc' es] eqn:flatten_tr.
        assert (occ': forall n, no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr).
        { intros.
          exploit occ; eauto.
          intros [H | H]; inv H; eauto. }
        specialize (IHtr loc' es Logic.eq_refl unitr H3 occ'). clear occ'.
        case: ifP.
        + intros e_C.
          destruct b; try congruence.
          intros _. simpl. rewrite flatten_tr.
          replace (incoming_returns C ((loc, e, loc') :: es ++ [::])) with
            (incoming_returns C ((loc, e, loc') :: es)).
          2: { rewrite cats0. auto. }
          replace es with (flatten tr).2 in IHtr.
          2: { rewrite flatten_tr; eauto. }
          replace es with (flatten tr).2.
          2: { rewrite flatten_tr; eauto. }
          (* replace (outgoing C es) with (outgoing C (flatten tr).2) in IHtr. *)
          replace loc with (loc, []: stack).1 by reflexivity.
          move: e_C => /eqP ?. subst C.
          eapply flatten_no_occ_unicity_incoming_returns; eauto. rewrite flatten_tr. eauto.
          inv occ_loc. eauto.
        + intros ?. intros unibr.
          assert (G1: no_occ_of_n_in_branches (loc, [::]) b)
                   by now inversion occ_loc.
          assert (G2: (forall n : loc_stack,
           no_occ_of_n_in_branches n b \/ unique_occ_of_n_in_branches n b)).
          { intros. exploit occ. intros []; eauto.
            inv H; eauto.
            inv H; eauto. }
          assert (G3: (forall n : loc_stack,
           no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr)).
          { intros. exploit occ. intros []; eauto.
            inv H; eauto.
            inv H; eauto. }
          assert (G4: no_occ_of_n_in_tree (loc, [::]) tr).
          { intros. inv occ_loc; eauto. }
          specialize (IHtr0 _ _ Logic.eq_refl unibr H2 G1 G2).
          simpl. rewrite flatten_tr.
          assert (unicity_in (incoming_returns C ((loc, e, loc') :: es))).
          { replace loc with (loc, []: stack).1 by reflexivity.
            eapply flatten_no_occ_unicity_incoming_returns; eauto. }
          assert (forall k e n',
                     In (k, e, n') (incoming_returns C es) ->
                     k <> loc /\
                       (forall n'', In (k, e, n'') (incoming_returns C (flatten_br loc b)) ->
                               n' = n'')).
          { intros k e0 n' IN. split.
            - revert flatten_tr G4 IN.
              clear.
              revert loc' es loc k e0 n'.
              induction tr using tree_ind with
                (P := fun tr => forall (loc' : nat) (es : seq (nat * event * nat))
                               (loc k : nat) e0 (n' : nat),
                          flatten tr = (loc', es) ->
                          no_occ_of_n_in_tree (loc, [::]) tr ->
                          In (k, e0, n') (incoming_returns C es) ->
                          k <> loc)
                (P0 := fun br => forall es k e0 n n' loc,
                           n <> loc ->
                           flatten_br n br = es ->
                           In (k, e0, n') (incoming_returns C es) ->
                           no_occ_of_n_in_branches (loc, [::]) br ->
                           k <> loc).
              + intros. inv H0. simpl in H.
                destruct a; simpl in *. inv H.
                eapply IHtr. 3: eauto. 2: eauto. 2: eauto. eauto.
              + intros. simpl in H0. subst. by [].
              + intros es k e0 n n' loc n_loc.
                simpl. destruct (flatten tr) as [n0 ls] eqn:flatten_tr.
                intros ?; subst es. simpl.
                intros H.
                destruct e; simpl in *.
                { intros G. inv G.

                     intros G. inv G.
                     replace (incoming_returns C (ls ++ flatten_br n b))
                       with (incoming_returns C ls ++ incoming_returns C (flatten_br n b)) in H.
                     eapply in_app_or in H as [H | H].
                     -- eapply IHtr; eauto.
                     -- eapply IHtr0; eauto.
                     -- unfold incoming_returns. rewrite pmap_app. auto. }
                move: H.
                case: ifP. move => /eqP ?; subst i0. simpl.
                intros H.
                destruct H as [H | H].
                * inv H. eauto.
                * intros G. inv G.
                  replace (incoming_returns C (ls ++ flatten_br n b))
                    with (incoming_returns C ls ++ incoming_returns C (flatten_br n b)) in H.
                  eapply in_app_or in H as [H | H].
                  -- eapply IHtr; eauto.
                  -- eapply IHtr0; eauto.
                  -- unfold incoming_returns. rewrite pmap_app. auto.
                * simpl. intros ? G H. inv H.
                  replace (incoming_returns C (ls ++ flatten_br n b))
                    with (incoming_returns C ls ++ incoming_returns C (flatten_br n b)) in G.
                  eapply in_app_or in G as [G | G].
                  -- eapply IHtr; eauto.
                  -- eapply IHtr0; eauto.
                  -- unfold incoming_returns. rewrite pmap_app. auto.
            - intros n''. revert IN.
              revert k e0 n' n''.
              assert (forall k e0 n' ls,
                         In (k, e0, n') (incoming_returns C ls) ->
                         exists e, In (k, e, n') ls).
              { clear. intros until ls.
                revert k e0 n'.
                induction ls.
                - simpl; eauto. by [].
                - simpl.
                  destruct a as [[? [|]]]; simpl.
                  { intros. exploit IHls; eauto. intros [? ?].
                    eexists;  right; eauto. }
                  case: ifP => //=.
                  2: { intros. exploit IHls; eauto. intros [? ?].
                       eexists;  right; eauto. }
                  move=> /eqP ?; subst.
                  intros ??? [H | H].
                  + inv H. eexists; left; eauto.
                  + exploit IHls; eauto. intros [? ?].
                    eexists;  right; eauto. }
              intros k z n' n'' IN1 IN2.
              eapply H0 in IN1 as [e1 IN1].
              eapply H0 in IN2 as [e2 IN2].
              exfalso.
              clear -IN1 IN2 flatten_tr occ occ_loc.
              specialize (occ (k, [::])).
              destruct occ.
              + inv H. clear - flatten_tr H5 IN1.
                revert loc' es k e1 n' flatten_tr H5 IN1.
                induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                * intros. destruct a; simpl in *.
                  inv H0. inv H.
                  eapply IHtr; eauto.
                * intros. simpl in *. subst. by [].
                * intros. simpl in *.
                  destruct (flatten tr) eqn:flatten_tr.
                  subst.
                  inv H2. congruence.
                  apply in_app_or in H0.
                  destruct H0.
                  -- eapply IHtr; eauto. inv H1; eauto.
                  -- eapply IHtr0; eauto. inv H1; eauto.
              + inv H.
                * assert (k = loc).
                  { clear -IN2 H3.
                    revert k e2 n'' loc IN2 H3.
                    induction b using branches_ind with
                      (P0 := fun br => forall k e2 n'' loc,
                               In (k, e2, n'') (flatten_br loc br) ->
                               no_occ_of_n_in_branches (k, [::]) br ->
                               k = loc)
                      (P := fun tr => forall k e n'' es loc,
                                flatten tr = (loc, es) ->
                                In (k, e, n'') es ->
                                no_occ_of_n_in_tree (k, [::]) tr ->
                                False).
                    - intros. destruct a. simpl in *. inv H.
                      inv H1. simpl in *.
                      eapply H4.
                      eapply IHb. eauto. eauto.
                    - intros. inv H.
                    - intros. simpl in *.
                      destruct (flatten t) eqn:flatten_tr.
                      simpl in *.
                      destruct H.
                      + inv H. auto.
                      + apply in_app_or in H. destruct H as [H | H].
                        * exfalso. eapply IHb; eauto.
                          inv H0. eauto.
                        * eapply IHb0. eauto. inv H0. eauto.
                  }
                  subst.
                  inv occ_loc. clear -H5 H6.
                  revert loc H5 H6.
                  induction tr using tree_ind with
                    (P := fun tr => forall loc,
                              unique_occ_of_n_in_tree (loc, [::]) tr ->
                              no_occ_of_n_in_tree (loc, [::]) tr -> False)
                    (P0 := fun br => forall loc,
                               unique_occ_of_n_in_branches (loc, [::]) br ->
                               no_occ_of_n_in_branches (loc, [::]) br -> False).
                  -- intros. inv H. inv H0. eauto.
                     eapply IHtr. eauto. inv H0; eauto.
                  -- intros. inv H.
                  -- intros. inv H0.
                     inv H.
                     ++ eapply IHtr; eauto.
                     ++ eapply IHtr0; eauto.
                * clear - flatten_tr H5 IN1.
                  revert loc' es k e1 n' flatten_tr H5 IN1.
                  induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                  -- intros. destruct a; simpl in *.
                     inv H0. inv H.
                     eapply IHtr; eauto.
                  -- intros. simpl in *. subst. by [].
                  -- intros. simpl in *.
                     destruct (flatten tr) eqn:flatten_tr.
                     subst.
                     inv H2. congruence.
                     apply in_app_or in H0.
                     destruct H0.
                     ++ eapply IHtr; eauto. inv H1; eauto.
                     ++ eapply IHtr0; eauto. inv H1; eauto.
          }





          destruct e.
          simpl. eapply unicity_in_incoming_return_app; eauto.
          simpl. case: ifP => //=.
          2: { simpl. intros _. eapply unicity_in_incoming_return_app; eauto. }

          assert (G: unicity_in (incoming_returns C (es ++ flatten_br loc b))).
          eapply unicity_in_incoming_return_app; eauto.

          move=> /eqP ?; subst i0.
          (* move=> /andP [] /eqP ? /eqP ?; subst i1 i0. *)

          intros [c b'] a a' IN IN'.
          destruct IN as [IN | IN]; destruct IN' as [IN' | IN'].
          * congruence.
          * inv IN.
            replace (incoming_returns C (es ++ flatten_br c b))
              with (incoming_returns C es ++ incoming_returns C (flatten_br c b)) in IN'.
            2: { unfold incoming_returns; rewrite pmap_app; auto. }
            eapply in_app_or in IN'.
            destruct IN'.
            -- eapply H; eauto.
               simpl. rewrite !eqxx /=. left; eauto.
               simpl. rewrite !eqxx /=. right; eauto.
            -- clear -H4 H1 G1.
               exfalso.
               assert (exists e, match_incoming (ERet i b' C) e /\
                              In (c, e, a') (flatten_br c b))
                        as [e [MS IN]].
               { revert H1. generalize (flatten_br c b).
                 clear.
                 induction l.
                 - simpl. by [].
                 - destruct a as [[n0 e] n1].
                   simpl. destruct e; simpl in *.
                   intros H. exploit IHl; eauto. intros [? [? ?]]; eauto.
                   case: ifP => //=.
                   2: { simpl. intros H H'. exploit IHl; eauto. simpl. intros [? [? ?]]; eauto. }
                   move=> /eqP ?; subst i1.
                   intros H; destruct H as [H | H].
                   inv H. eexists; split; eauto. simpl. auto.
                   exploit IHl; eauto. intros [? [? ?]]; eauto. }
               clear -H4 MS IN G1.
               revert H4 MS IN G1.
               generalize (ERet i b' C). intros e0 H.
               induction H.
               ++ eauto.
               ++ intros. simpl in IN.
                  destruct (flatten tr) as [n ls] eqn:?.
                  simpl in IN.
                  destruct IN.
                  ** inv H1. contradiction.
                  ** eapply in_app_or in H1.
                     destruct H1 as [H1 | H1].
                     --- inv G1. clear -Heqp H1 H7.
                         revert Heqp H7 H1.
                         revert n ls c e a'.
                  induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                  +++ intros. destruct a; simpl in *.
                      inv H0. inv H.
                      eapply IHtr; eauto.
                  +++ intros. simpl in *. subst. by [].
                  +++ intros. simpl in *.
                      destruct (flatten tr) eqn:flatten_tr.
                      subst.
                      inv H2. congruence.
                      apply in_app_or in H0.
                      destruct H0.
                      *** eapply IHtr; eauto. inv H1; eauto.
                      *** eapply IHtr0; eauto. inv H1; eauto.
                 --- eapply IHdo_not_appear_in; eauto.
                         inv G1; eauto.
          * inv IN'.
            replace (incoming_returns C (es ++ flatten_br c b))
              with (incoming_returns C es ++ incoming_returns C (flatten_br c b)) in IN.
            2: { unfold incoming_returns; rewrite pmap_app; auto. }
            eapply in_app_or in IN.
            destruct IN.
            -- symmetry. eapply H; eauto.
               simpl. rewrite !eqxx /=. left; eauto.
               simpl. rewrite !eqxx /=. right; eauto.
            -- clear -H4 H1 G1.
               exfalso.
               assert (exists e, match_incoming (ERet i b' C) e /\
                              In (c, e, a) (flatten_br c b))
                        as [e [MS IN]].
               { revert H1. generalize (flatten_br c b).
                 clear.
                 induction l.
                 - simpl. by [].
                 - destruct a0 as [[n0 e] n1].
                   simpl. destruct e; simpl in *.
                   { intros H. exploit IHl; eauto. intros [? [? ?]]; eauto. }
                   case: ifP => //=.
                   2: { simpl. intros H H'. exploit IHl; eauto. simpl. intros [? [? ?]]; eauto. }
                   move=> /eqP ?; subst i1.
                   intros H; destruct H as [H | H].
                   inv H. eexists; split; eauto. simpl. auto.
                   exploit IHl; eauto. intros [? [? ?]]; eauto. }
               clear -H4 MS IN G1.
               revert H4 MS IN G1.
               generalize (ERet i b' C). intros e0 H.
               induction H.
               ++ eauto.
               ++ intros. simpl in IN.
                  destruct (flatten tr) as [n ls] eqn:?.
                  simpl in IN.
                  destruct IN.
                  ** inv H1. contradiction.
                  ** eapply in_app_or in H1.
                     destruct H1 as [H1 | H1].
                     --- inv G1. clear -Heqp H1 H7.
                         revert Heqp H7 H1.
                         revert n ls c e a.
                  induction tr using tree_ind with
                  (P := fun tr =>
                          forall (loc' : nat) (es : seq (nat * event * nat))
                            (k : nat) (e1 : event) (n' : nat),
                            flatten tr = (loc', es) ->
                            no_occ_of_n_in_tree (k, [::]) tr -> In (k, e1, n') es ->
                            False)
                  (P0 := fun br => forall loc' es k e1 n',
                             k <> loc' ->
                             flatten_br loc' br = es ->
                             no_occ_of_n_in_branches (k, [::]:stack) br ->
                             In (k, e1, n') es -> False).
                  +++ intros. destruct a; simpl in *.
                      inv H0. inv H.
                      eapply IHtr; eauto.
                  +++ intros. simpl in *. subst. by [].
                  +++ intros. simpl in *.
                      destruct (flatten tr) eqn:flatten_tr.
                      subst.
                      inv H2. congruence.
                      apply in_app_or in H0.
                      destruct H0.
                      *** eapply IHtr; eauto. inv H1; eauto.
                      *** eapply IHtr0; eauto. inv H1; eauto.
                 --- eapply IHdo_not_appear_in; eauto.
                         inv G1; eauto.
          * eapply G; eauto.
            }
    intros. destruct (flatten tr) eqn:?.
    inv H0. eapply H; eauto.
Qed.
