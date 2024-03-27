(** * Meldable Heaps *)
From clutch.ert_logic Require Import ert_weakestpre lifting ectx_lifting primitive_laws expected_time_credits cost_models problang_wp proofmode ert_rules.
From clutch.ert_logic Require Import min_heap_spec.
From clutch.lib Require Import utils.
From iris.proofmode Require Export tactics.
From Coq Require Export Reals Psatz.
From stdpp Require Import sorting.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Set Default Proof Using "Type*".
Require Import Lra.


Section program.

End program.


Section heaps.

  (** Binary trees *)
  Context (A : Type).

  Inductive BinaryTree : Type :=
    | Nil
    | Node (v : A) (l : BinaryTree) (r : BinaryTree).


  Fixpoint tree_size (t : BinaryTree) : nat
    := match t with
        | Nil => 0%nat
        | (Node _ l r) => 1 + (tree_size l) + (tree_size r)
       end.

  Fixpoint tree_to_list (t : BinaryTree) : list A
    := match t with
        | Nil => []
        | (Node x l r) => [x] ++ (tree_to_list l) ++ (tree_to_list r)
       end.


  (** Injections of Binary trees to val *)
  Fixpoint inject_binarytree `{!Inject A val} (b : BinaryTree) : val
    := match b with
        | Nil => NONEV
        | Node x l r => SOMEV (PairV (inject x) (PairV (inject_binarytree l) (inject_binarytree r)))
       end.

  Global Program Instance Inject_binarytree `{!Inject A val} : Inject BinaryTree val :=
    {| inject := inject_binarytree |}.
  Next Obligation. Admitted.


  Fixpoint is_binarytree `{!Inject A val} (b : BinaryTree) (v : val) :=
      match b with
      | Nil => v = NONEV
      | Node x l r => ∃ vl vr, v = SOMEV ((inject x), (vl, vr)) ∧ is_binarytree l vl /\ is_binarytree r vr
    end.

  Lemma is_binarytree_inject `{!Inject A val} b v :
      is_binarytree b v ↔ v = (inject b).
  Proof. Admitted.
  (*
      revert v.
      induction xs as [|x xs IH]; [done|]. split.
      - destruct 1 as (? & -> & ?). simpl.
        do 2 f_equal. by apply IH.
      - intros ->. eexists. split; [done|]. by apply IH.
    Qed.
   *)

  (** Heaps: Heap-ordered binary trees *)

  Context (R : relation A).
  Context (HTo : TotalOrder R).

  Definition HeapOrdered (v : A) (next : BinaryTree) : Prop
    := match next with
        | Nil => True
        | (Node v' _ _) => R v v'
       end.

  Inductive IsHeap : BinaryTree -> Prop :=
      | Heap_nil : IsHeap Nil
      | Heap_node (v : A) (l r : BinaryTree) :
          IsHeap l -> IsHeap r -> HeapOrdered v l -> HeapOrdered v r -> IsHeap (Node v l r).

End heaps.


Section program.
  Context `{A : Type}.
  Context `{!ert_clutchGS Σ CostTick}.
  Context `[!Inject A val].



  Definition is_meld_heap_val (cmp : comparator A CostTick) (L : list A) (v : val) : iProp Σ
    := ∃ (b : BinaryTree A),
            ⌜v = (inject b) ⌝ ∗           (* v is an injection of a binary tree b *)
            ⌜IsHeap A (cmp_rel cmp) b ⌝ ∗ (* ... where b is a heap with respect to cmp *)
            ⌜L = tree_to_list A b ⌝       (* ... and b's elements are L *).

  Definition is_meld_heap_ref (cmp : comparator A CostTick) (L : list A) (v : val) : iProp Σ
    := ∃ (l : loc) (v' : val),
            ⌜ v = #l ⌝ ∗                  (* v is a location *)
            l ↦ v' ∗                       (* ... which points to a value *)
            is_meld_heap_val cmp L v'       (* ... which is a meld heap *).



  Definition meld_heap_new : val := (λ: "_", ref NONEV)%V.

  (* Takes two values (not references!) and melds them *)
  Definition meld_heap_meld (c : comparator A CostTick) : val
    :=  (rec: "meld" "h1" "h2" :=
          if: ("h1" = NONEV) then "h2" else
          if: ("h2" = NONEV) then "h1" else

          let: "h'" := if: (c (Fst "h1") (Fst "h2")) then ("h1", "h2") else ("h2", "h1") in
          let: "h_min" := (Fst "h'") in
          let: "h_max" := (Snd "h'") in
          (* Now (Fst h_min) <= (Fst h_max), so h_max should get melded into a child of h_min *)

          if: (rand #1 = #0)
            then (* Meld into the left branch of h_min *)
              let: "melded" := ("meld" (Fst (Snd "h_min")) "h_max") in
              (Fst "h_min", ("melded", (Snd (Snd "h_max"))))
            else
              let: "melded" := ("meld" (Snd (Snd "h_min")) "h_max") in
              (Fst "h_min", (Fst (Snd "h_max"), "melded")))%V.


  Definition meld_heap_insert (c : comparator A CostTick) : val
    := (λ: "ref_h" "v",
          "ref_h" <- (meld_heap_meld c (!"ref_h") (SOME ("v", (NONEV, NONEV)))) ;;
          "ref_h")%V.

  Definition meld_heap_remove (c : comparator A CostTick) : val
    := (λ: "ref_h",
          if: (!"ref_h" = NONEV) then #() else
          ("ref_h" <- (meld_heap_meld c (Fst (Snd !"ref_h")) (Snd (Snd !"ref_h")) ;;
          #() (* ??? *) )))%V.


  (** Time credit accounting *)

  (* Coq uses a fake version of log, which will be nice for handling edge cases in our derivation *)
  Lemma ln_0 : (ln 0%R = 0%R).
  Proof. compute. destruct (Rlt_dec R0 R0); auto. exfalso. lra. Qed.

  Definition tc_meld (k : R) (n : nat)  := (2 * k * (1 + Rlog 2 n))%R.

  Lemma tc_meld_1 (k : R) : (tc_meld k 1 = 2 * k)%R.
  Proof. rewrite /tc_meld /Rlog ln_1. lra. Qed.

  (* Inductive bound for tc_meld *)
  (* We will only apply advanced composition in the case that both a and b have size at at least 1 *)
  Lemma tc_meld_ind (k : R) (a b : nat) :
      (0 < a) -> (0 < b) -> (0 < k)%R -> (tc_meld k (1 + a + b) >= k + (tc_meld k a + tc_meld k b) / 2)%R.
  Proof.
    intros Ha Hb Hk.
    apply Rle_ge.
    rewrite /tc_meld.

    (* Divide by k and cancel the 2 factors *)
    apply (Rmult_le_reg_r (/ k)%R); first by apply Rinv_0_lt_compat.
    rewrite Rmult_plus_distr_r.
    rewrite Rinv_r; last lra.
    rewrite Rdiv_def.
    rewrite Rmult_assoc.
    rewrite -Rinv_mult.
    rewrite Rmult_comm.
    rewrite Rmult_plus_distr_l.
    replace  (/ (2 * k) * (2 * k * (1 + Rlog 2 a)))%R with (1 + Rlog 2 a)%R; last first.
    { rewrite -Rmult_assoc. rewrite Rinv_l; lra. }
    replace  (/ (2 * k) * (2 * k * (1 + Rlog 2 b)))%R with (1 + Rlog 2 b)%R; last first.
    { rewrite -Rmult_assoc. rewrite Rinv_l; lra. }
    replace (2 * k * (1 + Rlog 2 (1 + a + b)%nat) * / k)%R with (2 * (1 + Rlog 2 (1 + a + b)%nat))%R; last first.
    { rewrite (Rmult_comm _ (/ _)%R) -Rmult_assoc (Rmult_comm _ k) -Rmult_assoc.
      rewrite Rinv_l; lra. }

    (* Cancel out some 1's *)
    rewrite Rmult_plus_distr_l Rmult_1_r.
    do 3 rewrite -Rplus_assoc.
    replace (1 + 1)%R with 2%R by lra.
    repeat rewrite Rplus_assoc.
    repeat apply Rplus_le_compat_l.
    rewrite Rplus_comm.

    (* Replace 1 with a logarithm *)
    replace 1%R with (INR 1) by done.
    rewrite -(Rlog_pow 2); try lra.

    (* Turn Rlog into ln so that we can add them *)
    rewrite /Rlog.
    assert (Hln2 : (0 < ln 2)%R).
    { eapply Rlt_trans; [| eapply ln_lt_2]. lra. }
    apply (Rmult_le_reg_r (ln 2)); [done|].
    repeat rewrite (Rmult_plus_distr_r _ _ (ln 2)).
    repeat rewrite (Rmult_assoc _ _ (ln 2)).
    repeat (rewrite Rinv_l; last lra).
    repeat rewrite Rmult_1_r.


    (* Simplify the logarithms; apply monotonicity *)
    rewrite -ln_mult; [| lra | by apply lt_0_INR].
    rewrite -ln_mult; [ | | by apply lt_0_INR]; last first.
    { apply Rmult_lt_0_compat; [lra | by apply lt_0_INR]. }
    rewrite -ln_Rpower.
    apply Rcomplements.ln_le.
    { apply Rmult_lt_0_compat; last by apply lt_0_INR.
      apply Rmult_lt_0_compat; last by apply lt_0_INR.
      lra.
    }

    (* Turn the exponent into a product *)
    replace 2%R with (1%R + 1%R)%R by lra.
    rewrite Rpower_plus.
    rewrite Rpower_1; last (apply lt_0_INR; lia).
    replace (1%R + 1%R)%R with 2%R by lra.
    rewrite pow_1.


    (* Expand the binomial, bound using some of the terms *)
    repeat rewrite plus_INR.
    eapply (Rle_trans _ (a * b + b * a)%R); try lra.
    repeat rewrite Rmult_plus_distr_r.
    repeat rewrite Rmult_plus_distr_l.
    repeat rewrite INR_1.
    assert (0 < a)%R; [by apply lt_0_INR|].
    assert (0 < b)%R; [by apply lt_0_INR|].
    repeat rewrite Rmult_1_r.
    repeat rewrite Rmult_1_l.

    rewrite Rplus_assoc.
    rewrite -{1}(Rplus_0_l ((_ * _) + (_ * _))%R).
    apply Rle_plus_plus; first lra.

    rewrite Rplus_assoc.
    rewrite -{1}(Rplus_0_l ((_ * _) + (_ * _))%R).
    apply Rle_plus_plus.
    { apply Rplus_le_le_0_compat; try lra. apply Rmult_le_pos; try lra. }

    apply Rplus_le_compat_l.

    rewrite Rplus_assoc.
    rewrite -{1}(Rplus_0_l ((_ * _))%R).
    apply Rle_plus_plus; first lra.

    rewrite -{1}(Rplus_0_r ((_ * _))%R).
    apply Rplus_le_compat_l.

    apply Rmult_le_pos; try lra.

  Qed.



  Lemma spec_meld_heap_new cmp : {{{ True }}} meld_heap_new #() {{{ v, RET v; (is_meld_heap_ref cmp) [] v }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /meld_heap_new.
    wp_pures.
    wp_alloc.
    iApply "HΦ".
    rewrite /is_meld_heap_ref.
    iExists _, _; iFrame.
    rewrite /is_meld_heap_val.
    iPureIntro.
    split; auto.
    exists (Nil A).
    simpl.
    do 2 (split; auto).
    constructor.
  Qed.


  Lemma spec_meld_heap_meld cmp h1 h2 (L1 L2 : list A) :
      {{{ (is_meld_heap_val cmp L1 h1) ∗
          (is_meld_heap_val cmp L2 h2) ∗
          ⧖ ((cmp_cost cmp) + tc_meld (cmp_cost cmp) (length L1) + tc_meld (cmp_cost cmp) (length L2))
      }}}
        (meld_heap_meld cmp h1 h2)%E
      {{{ v, RET v;
          ∃ L, is_meld_heap_val cmp L v ∗ ⌜L ≡ₚ L1 ++ L2 ⌝
      }}}.
  Proof.
    iLöb as "IH" forall (h1 h2 L1 L2).
    iIntros (Φ) "((%b1 & -> & %Hb1 & ->) & (%b2 & -> & %Hb2 & ->) & H⧖) HΦ".
    rewrite {2}/meld_heap_meld.
    wp_pure.
    remember (rec: "meld" "h1" "h2" := _)%V as Vrec.
    wp_pures.
    case_bool_decide.
    { wp_pures.
      iModIntro; iApply "HΦ".
      iExists (tree_to_list A b2).
      iPureIntro.
      split.
      - eexists b2. auto.
      - by replace (tree_to_list A b1) with ([] : list A) by admit.
    }
    wp_pures.
    case_bool_decide.
    { wp_pures.
      iModIntro; iApply "HΦ".
      iExists (tree_to_list A b1).
      iPureIntro.
      split.
      - eexists b1. auto.
      - replace (tree_to_list A b2) with ([] : list A) by admit.
        by rewrite app_nil_r.
    }
    wp_pures.
    wp_bind (cmp _ _).
    wp_pures.

    (* need to destruct the binary tree *)
    wp_pures.

    Fail wp_apply ((@wp_cmp A CostTick cmp Σ ert_clutchGS0 _ _ _ _ ) with "[]").
  Admitted.


End program.


Section interface.


  Context `{A : Type}.
  Context `[!Inject A val].

  (* How to properly quantify over Σ? *)
  Program Definition meld_heap_spec cmp : (@min_heap A CostTick cmp)
    := {| heap_new := meld_heap_new ;
          heap_insert := meld_heap_insert cmp ;
          heap_remove := meld_heap_remove cmp ;
       |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

End interface.
