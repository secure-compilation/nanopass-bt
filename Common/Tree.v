Require Import List.
Require Import Program.
Require Import Classical. Require Import Lia.
Import ListNotations.

From Coq Require Import ssreflect ssrfun ssrbool.

Section Tree.

  Set Implicit Arguments.
  Inductive t (A E: Type): Type :=
  | node : A -> (* content of the node *)
           b A E -> (* children *)
           t A E
  with b (A E: Type) : Type :=
  | Bnil : b A E
  | Bcons : E -> (* label *)
            t A E -> (* tree corresponding to that label *)
            b A E -> (* rest of the children *)
            b A E
  .
  Unset Implicit Arguments.


  Scheme tree_ind :=
    Induction for t Sort Prop
  with branches_ind :=
    Induction for b Sort Prop.
  Combined Scheme tree_branches_ind from tree_ind, branches_ind.

  (* Print List.In. *)
  Fixpoint el_in_tree {A E: Type} (x : A) (tr : t A E): Prop :=
    match tr with
    | node a br => (x = a) \/ (el_in_branches x br)
    end
    with
      el_in_branches {A E : Type} (x : A) (br : b A E) :=
      match br with
      | Bnil _ _ => False
      | Bcons _ tr br' => el_in_tree x tr \/ el_in_branches x br'
      end.

  Fixpoint in_branches {A E : Type} (tr : t A E) (br : b A E): Prop :=
    match br with
    | Bnil _ _ => False
    | Bcons _ tr' br' => tr = tr' \/ in_branches tr br'
    end.

  (* Section TreeInduction. *)
  (*   Context (A E : Type). *)
  (*   Variable P : t A E -> Prop. *)
  (*   (* Hypothesis leaf_case : forall (x: A), P (node x (Bnil A B)). *) *)
  (*   (* not needed, for in the Bnil case, the prerequisite is always true *) *)
  (*   Hypothesis node_case : forall (x: A) (chld : b A E), (forall tr_c : t A E, in_branches tr_c chld -> P tr_c) -> P (node x chld). *)

  (*   Fixpoint tree_ind (tr : t A E) : P tr. *)
  (*   Proof. *)
  (*     refine (match tr with *)
  (*             | node a chld => node_case a chld ((fix branches_ind (chld : b A E) : forall tr_c, in_branches tr_c chld -> P tr_c := *)
  (*                                                   match chld with *)
  (*                                                   | Bnil _ _  => _ *)
  (*                                                   | Bcons lbl tr' br' => _ *)
  (*                                                                            end *)
  (*                                                ) chld) *)
  (*             end). *)
  (*     + intros tr_c Habs. *)
  (*       inversion Habs. *)
  (*     + intros tr_c Hcons. *)
  (*       inversion Hcons. *)
  (*       - pose proof (tree_ind tr') as H1. *)
  (*         now rewrite H. *)
  (*       - pose proof (branches_ind br') as H2. *)
  (*         exact (H2 tr_c H). *)
  (*   Qed. *)
  (* End TreeInduction. *)

  Fixpoint max_list (n : nat) (l : list nat) :=
    match l with
    | [] => n
    | n' :: ls => max_list (max n n') ls
    end.

  (* Fixpoint max_branch {A B : Type} (tr : t A B) := *)
  (*   match tr with *)
  (*   | leaf _ _ => 0 *)
  (*   | node _ ls => *)
  (*     let ls' := List.map max_branch ls in *)
  (*     max_list (List.length ls) ls' *)
  (*   end. *)

  (* Fixpoint depth {A : Type} (tr : t A) := *)
  (*   match tr with *)
  (*   | leaf _ => 0 *)
  (*   | node _ ls => *)
  (*     let ls' := List.map depth ls in *)
  (*     1 + max_list 0 ls' *)
  (*   end. *)

  (* Definition content_of {A: Type} (tr: t A): option A := *)
  (*   match tr with *)
  (*   | leaf _ => None *)
  (*   | node a _ => Some a *)
  (*   end. *)

End Tree.

(* Fixpoint showtree {A : Type} `{Show A} (tr : t A) : string := *)
(*   let fix showlist (ls : list (t A)) : string := *)
(*       match ls with *)
(*       | [] => ""%string *)
(*       | [tr'] => showtree tr' *)
(*       | tr' :: ls' => (showtree tr' ++ ", " ++ showlist ls')%string *)
(*       end in *)
(*   match tr with *)
(*   | leaf _ => "Leaf" *)
(*   | node a ls => *)
(*     "Node (" ++ show a ++ " -> " ++ "[" ++ showlist ls ++ "]" ++ ")" *)
(*   end. *)

(* Instance ShowTree {A : Type} `{Show A} : Show (@t A) := *)
(*   { *)
(*   show tr := showtree tr *)
(*   }. *)

(* Fixpoint gentree {A : Type} `{Gen A} (depth : nat) (branch : nat) : G (t A) := *)
(*   let fix genlist (depth : nat) (branch : nat) (curr : nat) : G (list (t A)) := *)
(*       match depth with *)
(*       | 0 => ret [] *)
(*       | S depth' => *)
(*         match curr with *)
(*         | 0 => ret [] *)
(*         | S curr' => *)
(*           freq [(1, ret []); *)
(*                (depth, tr <- gentree depth' branch;; *)
(*                    ls <- genlist depth' branch curr';; *)
(*                    ret (tr :: ls)) *)
(*                ] *)
(*         end *)
(*       end in *)
(*   a <- arbitrary;; *)
(*   ls <- genlist depth branch branch;; *)
(*   ret (node a ls) *)
(* . *)

(* Fixpoint shrinktree {A : Type} `{Shrink A} (tr : t A) : list (t A) := *)
(*   let fix shrinklist (shr : t A -> list (t A)) (l : list (t A)) : list (list (t A)) := *)
(*       match l with *)
(*       | [] => [] *)
(*       | x :: xs => (xs :: List.map (fun xs' => x :: xs') (shrinkListAux shr xs)) ++ List.map (fun x' => x' :: xs) (shr x) *)
(*       end in *)
(*   match tr with *)
(*   | leaf _ => [leaf _] *)
(*   | node a ls => node a [] :: List.map (node a) (shrinkListAux (fun tr => [tr]) ls) *)
(*   end. *)

(* Instance GenTree {A : Type} `{Arbitrary A} : Gen (@t A) := *)
(*   { *)
(*   arbitrary := sized (fun n => sized (gentree n)) *)
(*   }. *)

(* Section Path. *)

(*   Definition path := list nat. *)

(*   Definition traverse_node {A : Type} (n : nat) (ls : list (t A)) : option (t A) := *)
(*     List.nth_error ls n. *)

(*   Fixpoint traverse_path {A : Type} (p : path) (tr : t A) : option (t A) := *)
(*     match p with *)
(*     | [] => Some tr *)
(*     | n :: p' => *)
(*       match tr with *)
(*       | leaf _ => None *)
(*       | node _ ls => match traverse_node n ls with *)
(*                     | None => None *)
(*                     | Some tr' => traverse_path p' tr' *)
(*                     end *)
(*       end *)
(*     end. *)

(*   Fixpoint path_eq (p1 p2 : path) := *)
(*     match p1, p2 with *)
(*     | [], [] => true *)
(*     | n1 :: p1', n2 :: p2' => andb (Nat.eqb n1 n2) (path_eq p1' p2') *)
(*     | _, _ => false *)
(*     end. *)

(* End Path. *)

(* Section Numbering. *)
(*   (* In this section we define a numbering on the nodes of a tree. *)
(*      In particular, each node must have a different number. *) *)

(*   Fixpoint give_num_tree {A : Type} (tr : t A) (n : nat) : t (A * nat) * nat := *)
(*     let fix give_num_list (ls : list (t A)) (n : nat) : list (t (A * nat)) * nat := *)
(*         match ls with *)
(*         | [] => ([], n) *)
(*         | tr :: ls' => *)
(*           let (tr', n') := give_num_tree tr n in *)
(*           let (ls'', n'') := give_num_list ls' n' in *)
(*           (tr' :: ls'', n'') *)
(*         end in *)
(*     match tr with *)
(*     | leaf _ => (leaf _, n) *)
(*     | node a ls => *)
(*       let (ls', n') := give_num_list ls (S n) in *)
(*       (node (a, n) ls', n') *)
(*     end. *)

(*   Fixpoint give_num_list {A: Type} (trs: seq (t A)) (n: nat): seq (t (A * nat)) * nat := *)
(*     match trs with *)
(*     | [] => ([], n) *)
(*     | tr :: ls' => *)
(*       let (tr', n') := give_num_tree tr n in *)
(*       let (ls'', n'') := give_num_list ls' n' in *)
(*       (tr' :: ls'', n'') *)
(*     end. *)

(*   Lemma give_num_tree_list {A: Type}: forall (tr: t A) n, *)
(*       give_num_tree tr n = match tr with *)
(*                            | leaf _ => (leaf _, n) *)
(*                            | node a ls => *)
(*                              let (ls', n') := give_num_list ls (S n) in *)
(*                              (node (a, n) ls', n') *)
(*                            end. *)
(*   Proof. *)
(*     induction tr using tree_ind' with (Q := fun trs => forall n, give_num_list trs n = *)
(*                                                          let fix give_num_list (ls : list (t A)) (n : nat) : list (t (A * nat)) * nat := *)
(*                                                              match ls with *)
(*                                                              | [] => ([], n) *)
(*                                                              | tr :: ls' => *)
(*                                                                let (tr', n') := give_num_tree tr n in *)
(*                                                                let (ls'', n'') := give_num_list ls' n' in *)
(*                                                                (tr' :: ls'', n'') *)
(*                                                              end in give_num_list trs n). *)
(*     - eauto. *)
(*     - eauto. *)
(*     - simpl. intros n. rewrite (IHtr (S n)). simpl. eauto. *)
(*     - move=> n. simpl. *)
(*       rewrite IHtr; simpl; eauto. *)
(*       destruct (match tr with *)
(*                 | leaf _ => (leaf (A * nat), n) *)
(*                 | node a ls0 => let (ls', n') := give_num_list ls0 (S n) in (node (a, n) ls', n') *)
(*                 end) as [tr' n']. *)
(*       rewrite IHtr0; simpl; eauto. *)
(*   Qed. *)

(*   Lemma give_num_tree_destruct {A: Type}: forall (tr: t A) (n: nat), *)
(*       exists tr' n', *)
(*         give_num_tree tr n = (tr', n'). *)
(*   Proof. *)
(*     move=> tr. *)
(*     induction tr using tree_ind. *)
(*     - move=> n. *)
(*       eexists; eexists; reflexivity. *)
(*     - move=> n. *)
(*       (* set tr := (node x ls). *) *)
(*       destruct ls as [| tr' ls']. *)
(*       + simpl. eexists; eexists; eauto. *)
(*       + assert (Hin: In tr' (tr' :: ls')) by now left. *)
(*         specialize (H tr' Hin (S n)) as [tr0 [n0 H]]. *)
(*         simpl; rewrite H. *)
(*         destruct ((fix give_num_list (ls : seq (t A)) (n1 : nat) {struct ls} : *)
(*                      seq (t (A * nat)) * nat := *)
(*                      match ls with *)
(*                      | [::] => ([::], n1) *)
(*                      | tr :: ls'0 => *)
(*                        let (tr'1, n'0) := give_num_tree tr n1 in *)
(*                        let (ls'', n'') := give_num_list ls'0 n'0 in (tr'1 :: ls'', n'') *)
(*                      end) ls' n0). *)
(*         eexists; eexists; eauto. *)
(*   Qed. *)

(*   Definition give_num {A : Type} (tr : t A) := *)
(*     fst (give_num_tree tr 0). *)

(*   Definition give_nums {A: Type} (trs: seq (t A)) := *)
(*     fst (give_num_list trs 0). *)

(*   Instance showUnit : Show unit := *)
(*     { show _ := "tt"%string }. *)

(*   Definition give_num_unique_test := *)
(*     forAllShrink arbitrary shrinktree (fun tr : t nat => *)
(*     forAll arbitrary                  (fun p : path => *)
(*     forAll arbitrary                  (fun p' : path => *)
(*     let tr_num := give_num tr in *)
(*     match traverse_path p tr_num, traverse_path p' tr_num with *)
(*     | Some (node (_, n) ls), Some (node (_, n') ls') => *)
(*       if Nat.eqb n n' then path_eq p p' else eqb (path_eq p p') false *)
(*     | _, _ => true *)
(*     end))). *)


(* End Numbering. *)

(* Section Map. *)
(*   Context {A B : Type}. *)
(*   Variable f : A -> B. *)

(*   Fixpoint map (tr : t A) : t B := *)
(*     match tr with *)
(*     | leaf _ => leaf _ *)
(*     | node a ls => node (f a) (List.map map ls) *)
(*     end. *)

(* End Map. *)

(* Section MapGeneral. *)
(*   Context {A B : Type}. *)
(*   Variable f : A -> list (t A) -> B. *)

(*   Fixpoint map_gen (tr : t A) : t B := *)
(*     match tr with *)
(*     | leaf _ => leaf _ *)
(*     | node a ls => node (f a ls) (List.map map_gen ls) *)
(*     end. *)

(* End MapGeneral. *)

(* Section Filter. *)
(*   Context {A : Type}. *)
(*   Variable f : A -> bool. *)

(*   Let ftr : t A -> bool := *)
(*     fun (tr : t A) => *)
(*       match tr with *)
(*       | leaf _ => true *)
(*       | node a _ => f a *)
(*       end. *)

(*   Fixpoint filter (tr : t A) : list (t A) := *)
(*     match tr with *)
(*     | leaf _ => [leaf _] *)
(*     | node a ls => *)
(*       if f a then *)
(*         [node a (List.filter ftr ls)] *)
(*       else *)
(*         List.filter ftr ls *)
(*     end. *)

(* End Filter. *)

(* Section Foldr. *)
(*   Context {A B : Type}. *)
(*   Variable f : B -> A -> A. *)
(*   Variable g : A -> A -> A. *)
(*   Variable a0 : A. *)

(*   Fixpoint foldr (tr : t B) : A := *)
(*     match tr with *)
(*     | leaf _ => a0 *)
(*     | node b ls => *)
(*       let ls' := List.map foldr ls in *)
(*       let a := List.fold_right g a0 ls' in *)
(*       f b a *)
(*     end. *)

(* End Foldr. *)

(* Section TreeToList. *)
(*   Context {A: Type}. *)

(* Fixpoint tree_to_list (tr: t A): list A := *)
(*   match tr with *)
(*   | leaf _ => [] *)
(*   | node x ls => let ls' := List.map tree_to_list ls in *)
(*                 x :: List.concat ls' *)
(*   end. *)

(* Definition tree_to_list' (tr: t A): list A := *)
(*   tree_rect *)
(*     A *)
(*     (fun tr => list A) *)
(*     (fun trs => list A) *)
(*     (nil) *)
(*     (nil) *)
(*     (fun a ls ls' => a :: ls') *)
(*     (fun tr ls ls' ls'' => ls' ++ ls'') *)
(*     tr *)
(* . *)

(* Lemma tree_to_list_equiv: forall tr, tree_to_list tr = tree_to_list' tr. *)
(* Proof. *)
(*   induction tr using tree_ind' with (Q := fun ls => List.map tree_to_list ls = List.map tree_to_list' ls). *)
(*   - eauto. *)
(*   - eauto. *)
(*   - simpl. rewrite IHtr. rewrite <- List.flat_map_concat_map. *)
(*     now unfold flat_map. *)
(*   - simpl. rewrite IHtr. rewrite IHtr0. eauto. *)
(* Qed. *)

(* End TreeToList. *)


(* Section ListInTree. *)
(*   Context {A: Type}. *)

(*   Inductive list_in : list A -> t A -> Prop := *)
(*   | list_in_nil: forall tr, list_in [] tr *)
(*   | list_in_cons: forall (a: A) (l: list A) (ls: list (t A)), *)
(*       List.Exists (list_in l) ls -> *)
(*       list_in (a :: l) (node a ls) *)
(*   . *)
(* End ListInTree. *)

(* Section All. *)

(*   Context {A: Type}. *)
(*   Fixpoint all (a: pred A) (tr: t A): bool := *)
(*     match tr with *)
(*     | leaf _ => true *)
(*     | node x ls => *)
(*       a x && seq.all (all a) ls *)
(*     end. *)

(*   Inductive Forall (a: A -> Prop): t A -> Prop := *)
(*   | Forall_leaf: Forall a (leaf _) *)
(*   | Forall_node: forall x ls, *)
(*       a x -> *)
(*       List.Forall (Forall a) ls -> *)
(*       Forall a (node x ls). *)

(*   Definition all_list (a: A -> Prop) (trs: list (t A)): Prop := *)
(*     List.Forall (Forall a) trs. *)

(*   Lemma forall_list_forall (a: A -> Prop): *)
(*     forall tr, *)
(*       Forall a tr -> List.Forall a (tree_to_list tr). *)
(*   Proof. *)
(*     intros tr. *)
(*     (* rewrite tree_to_list_equiv. *) *)
(*     induction tr using tree_ind' with (Q := fun (trs: list (t A)) => List.Forall (Forall a) trs -> *)
(*                                                                   List.Forall a (List.concat (List.map tree_to_list trs))). *)
(*     - move=> H. simpl. eauto. *)
(*     - simpl. econstructor. *)
(*     - move=> H. *)
(*       simpl. inversion H; subst; clear H. *)
(*       specialize (IHtr H3). *)
(*       econstructor. eauto. eauto. *)
(*     - intros H. *)
(*       inversion H; subst; clear H. *)
(*       specialize (IHtr H2). *)
(*       specialize (IHtr0 H3). *)
(*       simpl. eapply List.Forall_app. *)
(*       split; eauto. *)
(*   Qed. *)

(* End All. *)



(* Definition trees_max_branch (branch : nat) := *)
(*   forAll arbitrary (fun depth => *)
(*   forAll (gentree depth branch) (fun tr => *)
(*   PeanoNat.Nat.leb (max_branch tr) branch)). *)
(* (*! QuickChick (trees_max_branch 6). *) *)


(* (* Lemma k_plus_2_ok : forall k, 1 < k + 2. *) *)
(* (* Proof. *) *)
(* (*   intros. lia. *) *)
(* (* Qed. *) *)

(* (* Definition get_ok0 := *) *)
(* (*   forAllShrink (gentree 7 2) shrinktree (fun tr => *) *)
(* (*   forAll arbitrary (fun n => whenFail (show ((give_id 3 tr), get 3 (k_plus_2_ok 1) n (give_id 3 tr))) *) *)
(* (*   match get 3 (k_plus_2_ok 01) n (give_id 3 tr) with *) *)
(* (*   | Some (node (i, _) _) => Nat.eqb i n *) *)
(* (*   | None => true *) *)
(* (*   end)). *) *)
(* (* QuickChick get_ok0. *) *)

(* (* Definition get_ok := *) *)
(* (*   forAll arbitrary (fun k => *) *)
(* (*   forAllShrink (sized (fun n => gentree n k)) shrinktree (fun tr => *) *)
(* (*   forAll arbitrary (fun n => collect (depth tr) ( *) *)
(* (*   match get (k + 2) (k_plus_2_ok k) n (give_id (k + 2) tr) with *) *)
(* (*   | Some (node (i, _) _) => Nat.eqb i n *) *)
(* (*   | None => true *) *)
(* (*   end)))). *) *)
(* (* QuickChick get_ok. *) *)

(* Fixpoint tree_of_list {A : Type} (ls : list A) : t A := *)
(*   match ls with *)
(*   | [] => leaf _ *)
(*   | [a] => (node a []) *)
(*   | a :: ls' => node a [tree_of_list ls'] *)
(*   end. *)

(* Fixpoint list_of_tree {A : Type} (tr : @t A) : list A := *)
(*   match tr with *)
(*   | leaf _ => [] *)
(*   | node a ls => *)
(*     match ls with *)
(*     | [] => [a] *)
(*     | tr' :: _ => a :: (list_of_tree tr') *)
(*     end *)
(*   end. *)

(* Fixpoint add_trace {A: eqType} (tr: @t A) (ls: list A) : option (t A) := *)
(*   let fix add_trace_list ls xs := *)
(*       match ls with *)
(*       | nil => *)
(*         [tree_of_list xs] *)
(*       | tr :: ls' => *)
(*         match add_trace tr xs with *)
(*         | Some tr' => tr' :: ls' *)
(*         | None => tr :: (add_trace_list ls' xs) *)
(*         end *)
(*       end *)
(*   in *)
(*   match tr, ls with *)
(*   | leaf _, ls => Some (tree_of_list ls) *)
(*   | node x ls, [] => Some tr *)
(*   | node x ls, x' :: xs => *)
(*     if x == x' then *)
(*       Some (node x (add_trace_list ls xs)) *)
(*     else *)
(*       None *)
(*   end. *)

(* Fixpoint list_in_tree {A: eqType} (tr: t A) (xs: list A) : bool := *)
(*   let fix list_in_tree_list ls (tr : list A) := *)
(*       match tr with *)
(*       | nil => true *)
(*       | _ => *)
(*         match ls with *)
(*         | nil => false *)
(*         | tr' :: ls' => *)
(*           if list_in_tree tr' tr then true *)
(*           else list_in_tree_list ls' tr *)
(*         end *)
(*       end *)
(*   in *)
(*   match tr, xs with *)
(*   | leaf _, [] => true *)
(*   | leaf _, _ :: _ => false *)
(*   | node x ls, [] => true *)
(*   | node x ls, x' :: xs' => (x == x') && list_in_tree_list ls xs' *)
(*   end. *)

(* Hypothesis trace_in_tree_add_trace : forall (A : eqType) (tr: t A) (ls: list A), *)
(*     match add_trace tr ls with *)
(*     | Some tr' => list_in_tree tr' ls *)
(*     | None => false *)
(*     end. *)

(* Definition trace_in_tree_add_trace' := *)
(*   forAll arbitrary (fun k => *)
(*   forAllShrink (sized (fun n => gentree n k)) shrinktree (fun tr => *)
(*   forAll arbitrary (fun ls : list nat => ( *)
(*   match @add_trace ssrnat.nat_eqType tr ls with *)
(*   | Some tr' => list_in_tree tr' ls *)
(*   | None => true *)
(*   end)))). *)
(* (*! QuickChick trace_in_tree_add_trace'. *) *)

(* Section LiftRel. *)
(*   Context {A: Type}. *)
(*   Context (R: A -> A -> Prop). *)

(*   Fixpoint lift_rel (tr1 tr2: t A): Prop := *)
(*     let *)
(*       fix lift_rel_list (ls1 ls2: seq (t A)): Prop := *)
(*       match ls1, ls2 with *)
(*       | [], [] => True *)
(*       | tr1 :: ls1', tr2 :: ls2' => *)
(*         lift_rel tr1 tr2 /\ *)
(*         lift_rel_list ls1' ls2' *)
(*       | _, _ => False *)
(*       end in *)
(*     match tr1, tr2 with *)
(*     | leaf _, leaf _ => True *)
(*     | node a1 ls1, node a2 ls2 => *)
(*       R a1 a2 /\ *)
(*       lift_rel_list ls1 ls2 *)
(*     | _, _ => False *)
(*     end. *)

(*   Fixpoint lift_rel_list (ls1 ls2: seq (t A)): Prop := *)
(*     match ls1, ls2 with *)
(*     | [], [] => True *)
(*     | tr1 :: ls1', tr2 :: ls2' => *)
(*       lift_rel tr1 tr2 /\ *)
(*       lift_rel_list ls1' ls2' *)
(*     | _, _ => False *)
(*     end. *)

(*   Lemma lift_rel_rewrite (tr1 tr2: t A): *)
(*     lift_rel tr1 tr2 = match tr1, tr2 with *)
(*                        | leaf _, leaf _ => True *)
(*                        | node a1 ls1, node a2 ls2 => *)
(*                          R a1 a2 /\ *)
(*                          lift_rel_list ls1 ls2 *)
(*                        | _, _ => False *)
(*                        end. *)
(*   Proof. *)
(*     unfold lift_rel. *)
(*     destruct tr1, tr2; eauto. *)
(*   Qed. *)

(*   Definition lift_option (oa1 oa2: option A): Prop := *)
(*     match oa1, oa2 with *)
(*     | None, None => True *)
(*     | Some a1, Some a2 => R a1 a2 *)
(*     | _, _ => False *)
(*     end. *)

(* End LiftRel. *)


(* Section Unique. *)

(*   Context {A: Type}. *)
(*   Context (R: A -> A -> Prop). *)

(*   (* Definition unique_list (ls: seq (t A)) := *) *)
(*   (*   forall (t1 t2: t A), *) *)
(*   (*     In t1 ls -> *) *)
(*   (*     In t2 ls -> *) *)
(*   (*     lift_option R (content_of t1) (content_of t2) -> *) *)
(*   (*     lift_rel R t1 t2. *) *)

(*   (* Inductive determinate_tree: t A -> Prop := *) *)
(*   (* | determinate_leaf: determinate_tree (leaf _) *) *)
(*   (* | determinate_node: forall a ls, *) *)
(*   (*     unique_list ls -> *) *)
(*   (*     (forall tr, In tr ls -> determinate_tree tr) -> *) *)
(*   (*       determinate_tree (node a ls) *) *)
(*   (* . *) *)

(*   (* Definition determinate_tree_list (ls: seq (t A)): Prop := *) *)
(*   (*   unique_list ls /\ forall tr, In tr ls -> determinate_tree tr. *) *)


(*   Definition unique_tree_list (ls: seq (t A)) := *)
(*     forall p p' a1 ls1 a2 ls2, *)
(*       List.nth_error ls p = Some (node a1 ls1) -> *)
(*       List.nth_error ls p' = Some (node a2 ls2) -> *)
(*       R a1 a2 -> *)
(*       p = p'. *)

(*   Inductive determinate_tree: t A -> Prop := *)
(*   | determinate_leaf: determinate_tree (leaf _) *)
(*   | determinate_node: forall a ls, *)
(*       unique_tree_list ls -> *)
(*       (forall tr, In tr ls -> determinate_tree tr) -> *)
(*       determinate_tree (node a ls) *)
(*   . *)

(*   Definition determinate_tree_list (ls: seq (t A)): Prop := *)
(*     unique_tree_list ls /\ forall tr, In tr ls -> determinate_tree tr. *)
(* End Unique. *)
