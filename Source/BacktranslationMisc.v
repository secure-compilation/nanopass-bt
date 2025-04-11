Require Import Tree.
Require Import List. Import ListNotations.
Require Import Lia.
Require Import Events.
Require Import Language.
Require Import Coq.ZArith.ZArith.
Require Import Values.

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
Require Import Coq.Logic.FunctionalExtensionality.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq order.
From mathcomp Require ssrnat.
Require Import Lia.
From extructures Require Import fmap.

Set Bullet Behavior "Strict Subproofs".

Ltac inv E := inversion E; subst; clear E.
Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

Fixpoint size {A B: Type} (t: Tree.t A B): nat :=
  match t with
  | node _ br => S (branches_size br)
  end
with branches_size {A B: Type} (br' : Tree.b A B): nat :=
       match br' with
       | Bnil => 0
       | Bcons _ t' q => size t' + branches_size q
       end.

Lemma size_tree_one : forall A B : Type, forall t : Tree.t A B, size t >= 1.
Proof.
  intros A B t.
  induction t.
  simpl.
  lia.
Qed.

Definition uniq_keys {A B: Type} (l: list (B * A)) :=
  forall n n' b a a',
    nth_error l n = Some (b, a) ->
    nth_error l n' = Some (b, a') ->
    n = n'.

Definition unicity_in {A B: Type} (l: list (B * A)) :=
  forall b a a',
    In (b, a) l ->
    In (b, a') l ->
    a = a'.

Lemma unicity_in_smaller:
  forall {A B: Type} (a: A * B ) l, unicity_in (a :: l) ->
                               unicity_in l.
Proof.
  unfold unicity_in.
  intros. eapply H; right; eauto.
Qed.

Definition unicity_in2 {A B C: Type} (l: list (C * B * A)) :=
  forall c b b' a a',
    In (c, b, a) l ->
    In (c, b', a') l ->
    b = b' /\ a = a'.

Lemma unicity_in2_smaller:
  forall {A B C: Type} (a: A * B * C) l, unicity_in2 (a :: l) ->
                                    unicity_in2 l.
Proof.
  unfold unicity_in2.
  intros. eapply H; right; eauto.
Qed.

Class HasLoc (A: Type) := {
    loc: A -> nat;
  }.

#[export] Instance HasLoc_Nat: HasLoc nat := {
    loc := id
  }.

#[export] Instance HasLoc_ProdLeft {X: Type}: HasLoc (nat * X) := {
    loc := fst
  }.


#[export] Instance HasLoc_ProdProdLeft {X Y: Type}: HasLoc (nat * X * Y) := {
    loc := fun t => fst (fst t)
  }.

#[export] Instance HasLoc_Tree {X E: Type} {HX: HasLoc X}: HasLoc (Tree.t X E) :=
  {
    loc := fun t => match t with node x _ => loc x end
  }.

Inductive unique_occ_of_n_in_tree {A E: Type} {NA: HasLoc A}: A -> Tree.t A E -> Prop :=
| first_occ_case: forall (n n': A) (br: Tree.b A E),
    no_occ_of_n_in_branches n br ->
    loc n = loc n' ->
    unique_occ_of_n_in_tree n (node n' br)
| already_here_case: forall (n m: A) (br: Tree.b A E),
    loc n <> loc m ->
    unique_occ_of_n_in_branches n br ->
    unique_occ_of_n_in_tree n (node m br)

with no_occ_of_n_in_branches {A E: Type} {NA: HasLoc A}: A -> Tree.b A E -> Prop :=
| bnil_case_no: forall (n: A),
    no_occ_of_n_in_branches n (Bnil A E)
| bcons_case_no: forall (n: A) (br: Tree.b A E) (e: E) (tr: Tree.t A E),
    no_occ_of_n_in_branches n br ->
    no_occ_of_n_in_tree n tr ->
    no_occ_of_n_in_branches n (Bcons e tr br)

with no_occ_of_n_in_tree {A E: Type} {NA: HasLoc A}: A -> Tree.t A E -> Prop :=
| never_here_case: forall (n m: A) (br: Tree.b A E),
    loc n <> loc m ->
    no_occ_of_n_in_branches n br ->
    no_occ_of_n_in_tree n (node m br)

with unique_occ_of_n_in_branches {A E: Type} {NA: HasLoc A}: A -> Tree.b A E -> Prop :=
| bcons_case_un_first_occ: forall (n: A) (tr: Tree.t A E) (e: E) (br: Tree.b A E),
    no_occ_of_n_in_branches n br ->
    unique_occ_of_n_in_tree n tr ->
    unique_occ_of_n_in_branches n (Bcons e tr br)
| bcons_case_un_already_here: forall (n: A) (tr: Tree.t A E) (e: E) (br: Tree.b A E),
    unique_occ_of_n_in_branches n br ->
    no_occ_of_n_in_tree n tr ->
    unique_occ_of_n_in_branches n (Bcons e tr br).

Scheme unique_occ_tree_ind := Induction for unique_occ_of_n_in_tree Sort Prop
    with no_occ_branches_ind := Induction for no_occ_of_n_in_branches Sort Prop
    with no_occ_tree_ind := Induction for no_occ_of_n_in_tree Sort Prop
    with unique_occ_branches_ind := Induction for unique_occ_of_n_in_branches Sort Prop.
Combined Scheme unique_ind from
  unique_occ_tree_ind, no_occ_branches_ind, no_occ_tree_ind, unique_occ_branches_ind.

Inductive unique_numbering {A E: Type} {NA: HasLoc A}: Tree.t A E -> Prop :=
| unique_numbering_cons: forall (tr: Tree.t A E),
    (forall (n: A), no_occ_of_n_in_tree n tr \/ unique_occ_of_n_in_tree n tr) ->
    unique_numbering tr.

Inductive path_in_tree {A E: Type}: list E -> Tree.t A E -> Prop :=
  | path_tr_node : forall (a: A) (br: Tree.b A E) (tra: list E),
      path_in_branch tra br ->
      path_in_tree tra (node a br)
with path_in_branch {A E: Type}: list E -> Tree.b A E -> Prop :=
  | path_br_nil : forall (br: Tree.b A E),
      path_in_branch nil br
| path_br_cons_keep : forall (tr: Tree.t A E) (lbl: E) (br: Tree.b A E) (tra: list E),
    path_in_branch tra br ->
    path_in_branch tra (Bcons lbl tr br)
| path_br_cons_intro : forall (tr: Tree.t A E) (lbl: E) (br: Tree.b A E) (tra: list E),
    path_in_tree tra tr ->
    path_in_branch (lbl :: tra) (Bcons lbl tr br).



Section WithEventType.

  Context {E: Type}.

  Program Fixpoint numbering_tree (ut: Tree.t unit E) (n0 : nat): nat * Tree.t nat E :=
    match ut with
    | node a c =>
        let '(n1, new_c) := numbering_branches c (S (n0)) in
        (n1, node n0 new_c)
    end
  with
  numbering_branches (br : Tree.b unit E) (n0 : nat): nat * Tree.b nat E :=
    match br with
    | Bnil => (n0, Bnil nat E)
    | Bcons e tr br' =>
        let '(n1, tr') := numbering_tree tr n0 in
        let '(n2, br'') := numbering_branches br' n1 in
        (n2, Bcons e tr' br'')
    end.

  Definition loc_tree_of_unit_tree (ut: Tree.t unit E): Tree.t nat E :=
    let '(_, tr) := numbering_tree ut 0 in tr.

Theorem numbering_tree_correct: forall (ut: Tree.t unit E) (n0 sz: nat) (tr: Tree.t nat E),
    (sz, tr) = numbering_tree ut n0 ->
    sz = size ut + n0.
Proof.
  intros ut.

  induction ut using tree_ind with (P := fun ut =>  forall n sz tr,
                                             (sz, tr) = numbering_tree ut n ->
                                             sz = size ut + n)
                                   (P0 := fun bt => forall n sz br,
                                              (sz, br) = numbering_branches bt n ->
                                              sz = branches_size bt + n).
  - intros n sz tr EQ.
    simpl in EQ.
    destruct (numbering_branches b (S n)) eqn:EQ'.
    symmetry in EQ'.
    apply IHut in EQ'. subst n0.
    simpl. inv EQ.
    lia.
  - intros n sz br EQ. inv EQ. auto.
  - intros n sz br EQ.
    simpl in EQ.
    destruct (numbering_tree ut n) eqn:EQ'.
    destruct (numbering_branches b _) eqn:EQ''.
    symmetry in EQ', EQ''. inv EQ.
    apply IHut0 in EQ''.
    apply IHut in EQ'. subst. simpl.
    lia.
Qed.

Lemma numbering_tree_sz_gt_n: forall (ut: Tree.t unit E) (n sz: nat) (tr: Tree.t nat E),
    (sz, tr) = numbering_tree ut n ->
    sz >= n.
Proof.
  intros.
  rewrite (numbering_tree_correct ut n sz tr H).
  lia.
Qed.

Lemma numbering_branches_correct: forall (br: Tree.b unit E) (n sz: nat) (br': Tree.b nat E),
    (sz, br') = numbering_branches br n ->
    sz = branches_size br + n.
Proof.
  intro br.
  induction br; intros n sz br' EQ.
  + simpl in *.
    inv EQ ; reflexivity.
  + simpl in *.
    destruct (numbering_tree t n) eqn: E1.
    symmetry in E1.
    apply (numbering_tree_correct t n n0 t0) in E1.
    destruct (numbering_branches br n0) eqn:E2.
    symmetry in E2.
    apply (IHbr n0 n1 b) in E2.
    rewrite E1 in E2.
    inv EQ.
    lia.
Qed.

Definition empty_unit_tree: Tree.t unit E :=
  node tt (Bnil unit E).


Definition stack: Set :=
  list (Definitions.Component.id * Definitions.Procedure.id * Definitions.Component.id).
Definition loc_stack: Set := (nat * stack).

End WithEventType.

