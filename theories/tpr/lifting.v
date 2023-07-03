From iris.proofmode Require Import tactics.
From clutch.tpr Require Export weakestpre.
Set Default Proof Using "Type".

Section lifting.
Context `{spec A B Σ} `{!tprwpG Λ Σ}.

(** * RWP *)
Lemma rwp_lift_step_fupd_coupl E Φ e1 :
  to_val e1 = None →
  (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗
      rwp_coupl e1 σ1 a1 (λ '(e2, σ2) a2,
        |={∅,E}=> state_interp σ2 ∗ spec_interp a2 ∗ RWP e2 @ E ⟨⟨ Φ ⟩⟩))
  ⊢ RWP e1 @ E ⟨⟨ Φ ⟩⟩.
Proof. by rewrite rwp_unfold /rwp_pre=>->. Qed.

Lemma rwp_lift_step_fupd E Φ e1 :
  to_val e1 = None →
  (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗
      ⌜reducible e1 σ1⌝ ∗
      ∀ e2 σ2,
        ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ |={∅,E}=>
        state_interp σ2 ∗ spec_interp a1 ∗ RWP e2 @ E ⟨⟨ Φ ⟩⟩)
  ⊢ RWP e1 @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (?) "H".
  iApply rwp_lift_step_fupd_coupl; [done|].
  iIntros (σ1 a1) "[Hσ1 Ha1]".
  iMod ("H" with "[$]") as "[%Hred H]".
  iModIntro.
  iApply rwp_coupl_prim_step_l.
  iExists _.
  iSplit; [done|].
  iSplit.
  { iPureIntro. eapply Rcoupl_pos_R, Rcoupl_trivial.
    - apply prim_step_mass. eauto.
    - apply dret_mass. }
  iIntros ([e2 σ2] (_ & Hstep & _)).
  iMod ("H" with "[//]") as "H".
  by iIntros "!>".
Qed.

Lemma rwp_lift_pure_step `{!Inhabited (state Λ)} E Φ e1 :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
  (∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → RWP e2 @ E ⟨⟨ Φ ⟩⟩)
  ⊢ RWP e1 @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hsafe Hstep) "H". iApply rwp_lift_step_fupd.
  { specialize (Hsafe inhabitant). eauto using reducible_not_val. }
  iIntros (σ1 a1) "Hσ".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; [done|].
  iIntros (e2 σ2 Hprim).
  destruct (Hstep _ _ _ Hprim).
  iModIntro.
  iMod "Hclose" as "_".
  iModIntro.
  iDestruct ("H" with "[//]") as "H".
  iFrame.
Qed.

Lemma rwp_lift_atomic_step {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 a1, state_interp σ1 ∗ spec_interp a1 ={E}=∗
    ⌜reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗ spec_interp a1 ∗
      from_option Φ False (to_val e2))
  ⊢ RWP e1 @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (?) "H".
  iApply (rwp_lift_step_fupd E _ e1)=>//; iIntros (σ1 a1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iMod "Hclose" as "_". iDestruct "H" as "($ & $ & HQ)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply rwp_value; [|done]. by apply of_to_val.
Qed.

Lemma rwp_lift_pure_det_step `{!Inhabited (state Λ)} {E Φ} e1 e2 :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  RWP e2 @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e1 @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (? Hpuredet) "H". iApply (rwp_lift_pure_step E); try done.
  { naive_solver. }
  by iIntros (?? (?&->)%Hpuredet).
Qed.

Lemma rwp_pure_step `{!Inhabited (state Λ)} E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  RWP e2 @ E ⟨⟨ Φ ⟩⟩ ⊢ RWP e1 @ E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply rwp_lift_pure_det_step.
  - intros σ. specialize (Hsafe σ). eauto using reducible_not_val.
  - intros σ1 e2' σ2 Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - by iApply "IH".
Qed.

(** * SWP  *)
Lemma rswp_lift_step_fupd k E Φ e1 :
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    |={∅}▷=>^k ⌜reducible e1 σ1⌝ ∗
     ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0%R⌝ ={∅,E}=∗
      state_interp σ2  ∗
      RWP e2 @ E ⟨⟨ Φ ⟩⟩)
  ⊢ RSWP e1 at k @ E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_unfold /rswp_def /rswp_step.
  iIntros "H" (σ1 ?) "(Hσ & Ha)".
  iMod ("H" with "Hσ") as "H". iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros "(% & H)".
  iSplit; [done|].
  iExists _.
  iSplit.
  { iPureIntro. eapply Rcoupl_pos_R, Rcoupl_trivial.
    - apply prim_step_mass. eauto.
    - apply dret_mass. }
  iIntros (?? (?&?&?)).
  iMod ("H" with "[//]") as "[$ H]".
  by iFrame.
Qed.

End lifting.
