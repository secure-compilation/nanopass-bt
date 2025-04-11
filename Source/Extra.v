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

Ltac fwd_sim M :=
  apply Forward_simulation with (order := Nat.lt) (match_states := M);
  constructor;
  [now apply lt_wf | | |].

Ltac inv H :=
  inversion H;
  clear H;
  subst.

Lemma unzip1_pair_map {S T U: Type}:
  forall (P1: U -> S) (P2: U -> T) (uli : seq U),
    unzip1 [seq ((P1 u), (P2 u)) | u <- uli] =
      [seq ((P1 u)) | u <- uli].
Proof.
  move=> P1 P2 uli.
  elim: uli => //= u ls -> //=.
Qed.

Lemma sorted_impl_tail_sorted : forall (a : nat_ordType) (fsval : seq nat_ordType), path.sorted Ord.lt (a :: fsval) -> path.sorted Ord.lt fsval.
Proof.
  intros.
  inversion H.
  destruct fsval.
  + constructor.
  + unfold path.sorted.
    unfold path.path in H1.
    apply andb_prop in H1.
    destruct H1.
    assumption.
Qed.

Lemma in_unzip1 {T : Type} : forall (fmval : seq (nat_ordType * T)) (n : nat) (P : (nat_ordType * T -> bool)), n \in [seq u.1 | u <- [seq p | p <- fmval & P p]] -> In n (unzip1 fmval).
Proof.
  induction fmval ; intros.
  + simpl in H. inv H.
  + simpl in H.
    destruct (P a) eqn:EQ.
  - simpl in H.
    rewrite <- has_pred1 in H.
    simpl in H.
    apply orb_prop in H.
    destruct H.
    * left. move: H => /eqP //=.
    * right.
      rewrite has_pred1 in H.
      apply (IHfmval n P H).
  - right.
    apply (IHfmval n P H).
Qed.


Lemma iter_min_arg {T : Type} : forall (fmval : seq (nat_ordType * T)) (a0 a1 : nat), Ord.lt a0 a1 -> path.path Ord.lt a1 (unzip1 fmval) -> path.path Ord.lt a0 (unzip1 fmval).

Proof.
  intros.
  destruct fmval.
  + constructor.
  + simpl.
    inversion H0.
    apply andb_prop in H2.
    destruct H2 as [H1 H2].
    apply andb_true_intro.
    split; try assumption.
    apply (Ord.lt_trans H H1).
Qed.

Lemma min_arg_NMap {T : Type} : forall (fmval : seq (nat_ordType * T)) (a : nat_ordType * T), path.sorted Ord.lt (unzip1 (a :: fmval)) -> forall (n : nat), In n (unzip1 fmval) -> Ord.lt a.1 n.
Proof.
  induction fmval ; intros.
  + inv H0.
  + inversion H.
    apply andb_prop in H2.
    destruct H2 as [Hheadlt Htaillt].
    inversion H0.
  - subst.
    auto.
  - apply IHfmval ; try assumption.
    simpl.
    now apply (iter_min_arg Hheadlt).
Qed.

Lemma anti_refl_ord_lt : forall n : nat, ~ Ord.lt n n.

Proof.
  induction n.
  + intro.
    inv H.
  + assumption.
Qed.



Lemma need_it: forall (n: nat) (b: bool) (distr: NMap bool),
    n \in [seq u.1 | u <- [seq p | p <- distr & p.2 == b]] ->
          distr n = Some b.
Proof.
  clear. move=> n b distr.
  Locate "\in".
  rewrite -has_pred1 /pred1 //= => H.
  destruct distr as [fmval i].
  induction fmval.
  - inv H.
  -
    + simpl in H.
      destruct (a.2 == b) eqn:EQ.
      * rewrite EQ in H.
        simpl in H.
        apply orb_prop in H.
        destruct H.
        { unfold getm. simpl.
          rewrite ifT; auto;
            [move: EQ => /eqP -> //= | move: H => /eqP -> //=]. }
        { unfold getm. simpl.
          destruct (n == a.1) eqn:EQ'.
          - rewrite EQ';
              move: EQ => /eqP -> //=.
          - rewrite EQ'.
            apply sorted_impl_tail_sorted in i as i0.
            exact (IHfmval i0 H). }
      * rewrite EQ in H.
        apply sorted_impl_tail_sorted in i as i0.
        unfold getm. simpl.
        assert (FMap.FMap i0 n = Some b).
        { inversion i.
          { exact (IHfmval i0 H). } }
        destruct (n == a.1) eqn:EQ'.
        rewrite has_pred1 in H.
        apply in_unzip1 in H as H1.
        (* apply nat_eqb_impl_eq in i1. *)
        assert (Ord.lt a.1 n).
        { apply (min_arg_NMap i H1). }
        subst.
        contradict H2.
        move: EQ => /eqP EQ.
        move: EQ' => /eqP ->.
        apply anti_refl_ord_lt.
        rewrite EQ'.
        exact (IHfmval i0 H).
Qed.

Theorem eq_binnumspos_dec: forall (zp0 zp1: BinNums.positive),
    {zp0 = zp1} + {zp0 <> zp1}.
Proof.
  intros. decide equality.
Defined.

Theorem eq_binnumsZ_dec: forall (z0 z1: BinNums.Z),
    {z0 = z1} + {z0 <> z1}.
Proof. decide equality.
       eapply eq_binnumspos_dec.
       eapply eq_binnumspos_dec.
Defined.

Theorem eq_event_dec: forall (e1 e2: event),
    {e1 = e2} + {e1 <> e2}.
Proof.
  repeat decide equality.
Defined.

Lemma neg_symmetry {A : Type} : forall a b : A, a <> b -> b <> a.
Proof.
  intros a b Hab Hba.
  symmetry in Hba.
  contradiction.
Qed.
