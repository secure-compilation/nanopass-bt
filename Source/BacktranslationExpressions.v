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


Ltac take_step :=
  match goal with
  | |- @star _ _ _ _ _ ?t _ =>
      eapply (@star_step _ _ _ _ _ E0 _ t _ t); trivial; [econstructor|]
  end.

Fixpoint expr_of_expr_list (es: list expr): expr :=
  match es with
  | [] => E_exit
  | [e] => e
  | e :: es' => E_seq e (expr_of_expr_list es')
  end.

Definition switch_clause (matched_value: expr) (n: Z) (e_then e_else: expr) :=
  E_if (E_binop Eq matched_value (E_val (Int n)))
    e_then
    e_else.

Lemma switch_clause_spec prog C stk mem arg k:
  forall matched_value off n n' e_then e_else,
    matched_value = E_deref (E_binop Add E_local (E_val (Int off))) ->
    Memory.load mem (C, Block.local, off) = Some (Int n) ->
    if (n =? n') % Z then
        Star (CS.sem prog)
          [CState C, stk, mem, k, switch_clause matched_value n' e_then e_else, arg] E0
          [CState C, stk, mem, k, e_then, arg]
    else
      Star (CS.sem prog)
           [CState C, stk, mem, k, switch_clause matched_value n' e_then e_else, arg] E0
           [CState C, stk, mem, k, e_else, arg].
  Proof.
    move=> matched_value off n n' e_then e_else -> Hload.
    destruct (Z.eqb_spec n n') as [n_n'|n_n'].
    - subst n'.
      simpl in *.
      repeat take_step; trivial; try eassumption.
      repeat take_step; trivial; try eassumption.
      rewrite Z.eqb_refl -[_ != _]/(true) /=.
      repeat take_step; trivial; try eassumption.
      apply star_refl.
    - unfold switch_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite <- Z.eqb_neq in n_n'. rewrite n_n'. simpl.
        eapply CS.KS_If2. }
      apply star_refl.
  Qed.

Definition switch (matched_value: expr) (es: list (nat * expr)) (e_else: expr): expr :=
  fold_right (fun '(n, e) => switch_clause matched_value (Z.of_nat n) e) e_else es.

Definition switch2_clause (matched_value1 matched_value2: expr) (n1 n2: Z) (e_then e_else: expr) :=
  E_if (E_binop Mul (E_binop Eq matched_value1 (E_val (Int n1)))
                    (E_binop Eq matched_value2 (E_val (Int n2))))
    e_then
    e_else.

Lemma switch2_clause_spec prog C stk mem :
  forall matched_value1 matched_value2 off n1 n1' z z' e_then e_else k,
    matched_value1 = E_deref (E_binop Add E_local (E_val (Int off))) ->
    Memory.load mem (C, Block.local, off) = Some (Int n1) ->
    matched_value2 = E_arg ->
    if (n1 =? n1')%Z && (z =? z')%Z then
        Star (CS.sem prog)
          [CState C, stk, mem, k, switch2_clause matched_value1 matched_value2
                                        n1' z' e_then e_else, Int z] E0
          [CState C, stk, mem, k, e_then, Int z]
    else
      Star (CS.sem prog)
           [CState C, stk, mem, k, switch2_clause matched_value1 matched_value2
                                         n1' z' e_then e_else, Int z] E0
           [CState C, stk, mem, k, e_else, Int z].
  Proof.
    move=> matched_value1 matched_value2 off n1 n1' P P' e_then e_else k.
    move=> -> Hload ->.
    case n1_n1': (n1 =? n1')%Z; [case P_P': (P =? P')%Z|];
      move=> //=.
    - unfold switch2_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite n1_n1' P_P'. simpl. eapply CS.KS_If2. }
      apply star_refl.
    - unfold switch2_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite n1_n1' P_P'. simpl. eapply CS.KS_If2. }
      apply star_refl.
    - unfold switch2_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite n1_n1'. simpl. eapply CS.KS_If2. }
      apply star_refl.
  Qed.

Lemma switch2_clause_spec' prog C stk mem :
  forall matched_value1 matched_value2 off off' n1 n1' z z' arg e_then e_else k,
    matched_value1 = E_deref (E_binop Add E_local (E_val (Int off))) ->
    Memory.load mem (C, Block.local, off) = Some (Int n1) ->
    matched_value2 = E_deref (E_binop Add E_local (E_val (Int off'))) ->
    Memory.load mem (C, Block.local, off') = Some (Int z) ->
    if (n1 =? n1')%Z && (z =? z')%Z then
        Star (CS.sem prog)
          [CState C, stk, mem, k, switch2_clause matched_value1 matched_value2
                                        n1' z' e_then e_else, Int arg] E0
          [CState C, stk, mem, k, e_then, Int arg]
    else
      Star (CS.sem prog)
           [CState C, stk, mem, k, switch2_clause matched_value1 matched_value2
                                         n1' z' e_then e_else, Int arg] E0
           [CState C, stk, mem, k, e_else, Int arg].
  Proof.
    move=> matched_value1 matched_value2 off off' n1 n1' P P' arg e_then e_else k.
    move=> -> Hload -> Hload'.
    case n1_n1': (n1 =? n1')%Z; [case P_P': (P =? P')%Z|];
      move=> //=.
    - unfold switch2_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite n1_n1' P_P'. simpl. eapply CS.KS_If2. }
      apply star_refl.
    - unfold switch2_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite n1_n1' P_P'. simpl. eapply CS.KS_If2. }
      apply star_refl.
    - unfold switch2_clause.
      repeat take_step; trivial; try eassumption.
      eapply (@star_step _ _ _ _ _ E0 _ E0 _ E0); trivial; simpl.
      { rewrite n1_n1'. simpl. eapply CS.KS_If2. }
      apply star_refl.
  Qed.

Definition switch2 (matched_value1 matched_value2: expr)
  (es: list (nat * Z * expr)) (e_else: expr): expr :=
  fold_right (fun '(n, z, e) => switch2_clause matched_value1 matched_value2 (Z.of_nat n) z e) e_else es.

Definition loc_expr: expr := E_deref (E_binop Add E_local (E_val (Int 0))).
Definition is_call_expr: expr := E_deref (E_binop Add E_local (E_val (Int 1))).
Definition res_expr: expr := E_deref (E_binop Add E_local (E_val (Int 2))).


(* Definition handle_call_expr. *)

Definition update_loc (new_loc: nat) :=
 E_assign E_local (E_val (Int (Z.of_nat new_loc))).


Definition switch_incoming_calls
  (C: Component.id) (P: Procedure.id) (es: list (nat * event * nat)): expr :=
  let ls := incoming_calls C P es in
  let ls' := map (fun '(old_loc, z, new_loc) => (old_loc, z, update_loc new_loc)) ls in
  switch2
    (E_deref (E_binop Add E_local (E_val (Int 0)))) E_arg
    ls' (update_loc 0).

Definition switch_incoming_return
  (C: Component.id) (es: list (nat * event * nat)): expr :=
  let ls := incoming_returns C es in
  let ls' := map (fun '(old_loc, z, new_loc) =>
                    (old_loc, z, E_seq (update_loc new_loc)
               (E_assign (E_binop Add E_local (E_val (Int 1)))
                  (E_val (Int 1))))) ls in
  switch2
    (E_deref (E_binop Add E_local (E_val (Int 0))))
    (E_deref (E_binop Add E_local (E_val (Int 2))))
    ls' (E_val (Int 0)).

Section WithG.
Variable G: global_env.

(*
    // Call event
    is_call = 1;
    loc := new_loc;
    res = C2_P2(z6);
    is_call = 0;
    C1_P1(z);
    break;
 *)
Definition call_expr (Ccur Cnext: Component.id)
  (Pcur Pnext: Procedure.id)
  (new_loc: nat)
  (call_arg: Z): expr :=
  expr_of_expr_list
    [ E_assign (E_binop Add E_local (E_val (Int 1))) (E_val (Int 1));
      E_assign E_local (E_val (Int (Z.of_nat new_loc)));
      E_assign (E_binop Add E_local (E_val (Int 2)))
        (E_call Cnext Pnext (E_val (Int call_arg)));
      E_assign (E_binop Add E_local (E_val (Int 1))) (E_val (Int 0));
      E_call Ccur Pcur (E_val (Int 0))
    ].


Definition new_frame Ccur Pcur old_arg k :=
{| CS.f_component := Ccur;
   CS.f_arg := old_arg;
   CS.f_cont := Kassign1
                  (E_binop Add E_local (E_val (Int 2)))
                  (Kseq
                     (E_seq
                        (E_assign
                           (E_binop Add E_local
                              (E_val (Int 1)))
                           (E_val (Int 0)))
                        (E_call Ccur Pcur (E_val (Int 0))))
                     k) |}.

Lemma call_expr_correct: forall Ccur Cnext Pcur Pnext new_loc call_arg s m k old_arg e,
    (exists v, Memory.load m (Ccur, Block.local, 0%Z) = Some v) ->
    (exists v, Memory.load m (Ccur, Block.local, 1%Z) = Some v) ->
    Ccur <> Cnext ->
    imported_procedure (genv_interface G) Ccur Cnext Pnext ->
    find_procedure (genv_procedures G) Cnext Pnext = Some e ->
    exists m',
  plus CS.kstep G [CState Ccur, s, m, k,
      call_expr Ccur Cnext Pcur Pnext new_loc call_arg, old_arg]
    [ECall Ccur Pnext call_arg Cnext]
    [CState Cnext, new_frame Ccur Pcur old_arg k :: s, m', Kstop, e, Int call_arg]
  /\ Memory.load m' (Ccur, Block.local, 0%Z) = Some (Int (Z.of_nat new_loc))
  /\ Memory.load m' (Ccur, Block.local, 1%Z) = Some (Int 1%Z)
  /\ (forall ptr,
        ptr <> (Ccur, Block.local, 0%Z) ->
        ptr <> (Ccur, Block.local, 1%Z) ->
        Memory.load m' ptr = Memory.load m ptr).
Proof.
  move=> Ccur Cnext Pcur Pnext new_loc call_arg s m k old_arg e
          load1 load2 H1 H2 H3.
  destruct load2 as [v2 load2].
  exploit Memory.store_after_load; eauto.
  intros [m' H4].
  destruct load1 as [v1 load1].
  eapply Memory.load_after_store with (ptr' := (Ccur, Block.local, 0%Z))
    in H4 as load2'; eauto.
  case contra: eq_op load2';
    first (move: contra => //= /eqP; congruence).
  intros R; rewrite -R in load1.
  clear v2 load2.
  exploit Memory.store_after_load; eauto.
  intros [m'' H5].
  eexists.
  split; [| split; [| split]].
  - econstructor. constructor.
    do 17 (take_step; eauto).
    eapply star_step. eapply CS.KS_ExternalCall; eauto.
    eapply star_refl; eauto. reflexivity. reflexivity.
  - erewrite Memory.load_after_store; eauto. rewrite eqxx //=.
  - erewrite Memory.load_after_store; eauto.
    case: ifP => [/eqP [] //= | _].
    erewrite Memory.load_after_store; eauto. rewrite eqxx //=.
  - intros ptr.
    erewrite Memory.load_after_store; eauto.
    case: ifP => [/eqP //= | _].
    erewrite Memory.load_after_store; eauto.
    case: ifP => [/eqP //= | //=].
Qed.

(*
    // return event
    is_call = 1;
    loc = new_loc;
    return z7;
 *)
Definition ret_expr (new_loc: nat) (ret_val: Z): expr :=
  expr_of_expr_list
    [ E_assign (E_binop Add E_local (E_val (Int 1))) (E_val (Int 1));
      E_assign E_local (E_val (Int (Z.of_nat new_loc)));
      E_val (Int ret_val)
    ].

Lemma ret_expr_correct: forall Ccur f s m old_arg new_loc ret_val,
    (exists v, Memory.load m (Ccur, Block.local, 0%Z) = Some v) ->
    (exists v, Memory.load m (Ccur, Block.local, 1%Z) = Some v) ->
    Ccur <> f.(CS.f_component) ->
    exists m',
  star CS.kstep G [CState Ccur, f :: s, m, Kstop, ret_expr new_loc ret_val, old_arg]
             [ERet Ccur ret_val f.(CS.f_component)]
             [CState f.(CS.f_component), s, m', f.(CS.f_cont), E_val (Int ret_val), f.(CS.f_arg)].
Proof.
  move=> Ccur f s m old_arg new_loc ret_val load1 load2 H1.
  destruct load2 as [v2 load2].
  exploit Memory.store_after_load; eauto.
  intros [m' H2].
  destruct load1 as [v1 load1].
  eapply Memory.load_after_store with (ptr' := (Ccur, Block.local, 0%Z))
    in H2 as load1'; eauto.
  case contra: eq_op load1';
    first (move: contra => //= /eqP; congruence).
  intros R; rewrite -R in load1.
  clear v2 load2.
  exploit Memory.store_after_load; eauto.
  intros [m'' H3].
  destruct f as [Cnext arg k].
  eexists.
  do 15 (take_step; eauto).
  eapply star_step. eapply CS.KS_ExternalReturn; eauto. eapply star_refl.
  reflexivity.
Qed.

Definition switch_outgoing
  (C: Component.id) (es: list (nat * event * nat)) (e_else: expr): expr :=
  let ls := outgoing C es in
  let ls' := map (fun '(old_loc, d, new_loc) =>
                    match d with
                    | inl (Cnext, Pnext, z) => (old_loc, call_expr C Cnext 0 Pnext new_loc z)
                    | inr z => (old_loc, ret_expr new_loc z)
                    end) ls in
  switch (E_deref (E_binop Add E_local (E_val (Int 0)))) ls' e_else.


End WithG.

Definition code_of (C: Component.id) (P: Procedure.id) (es: list (nat * event * nat)): expr :=
  E_seq (E_if is_call_expr
              (switch_incoming_calls C P es)
              (switch_incoming_return C es))
        (switch_outgoing C es E_exit).

Section Build.

  Variable p: Flattened.prg.
  Hypothesis wf_p: Flattened.wf p.

  Let comps := domm (Flattened.prog_procedures p).
  Variable procs: {fmap Component.id -> seq Procedure.id}.
  Hypothesis domm_procs: domm procs = comps.

  Definition compile: program :=
    {| prog_interface := Flattened.prog_interface p;
       prog_procedures :=
        mkfmapf
          (fun C =>
             match Flattened.prog_procedures p C with
             | Some cs =>
                 match procs C with
                 | Some Ps =>
                     mkfmapf (fun P => code_of C P cs) Ps
                 | None => emptym
                 end
             | None => emptym
             end) comps;
       prog_buffers := mkfmapf (fun C => if C == Component.main then
                                        inr [Int (-1); Int 1; Int 0]
                                      else inr [Int 0; Int 1; Int 0]) comps
      |}.

End Build.
