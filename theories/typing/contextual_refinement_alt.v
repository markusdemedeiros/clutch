From Coq Require Import Reals.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From clutch.common Require Import language ectx_language.
From clutch.prob_lang Require Import lang notation metatheory.
From clutch.typing Require Import types contextual_refinement.
From clutch.prob Require Import distribution.

(** Alternative formulation of contextual refinement without restricting to
    contexts of the ground type but only observing termination through their
    masses. *)
Definition ctx_refines_alt (Γ : stringmap type)
    (e e' : expr) (τ : type) : Prop := ∀ K σ₀ τ',
  typed_ctx K Γ τ ∅ τ' →
  (SeriesC (lim_exec (fill_ctx K e, σ₀)) <= SeriesC (lim_exec (fill_ctx K e', σ₀)))%R.

Notation SeqV e1 e2 := (LamV BAnon e2%E e1%E).

Lemma prim_step_true_no_final e σ n :
  to_val e = None →
  step_or_final ((SeqV e #true)%E, σ) ≫= exec n =
    (prim_step e σ) ≫= (λ '(e', σ'), exec n ((SeqV e' #true)%E, σ')).
Proof.
  intros He.
  rewrite 1!step_or_final_no_final /=; [|eauto].
  replace (SeqV e #true)%E with (fill [(AppRCtx (LamV <> #true)%E)] e); [|done].
  rewrite fill_dmap //=.
  rewrite /dmap.
  rewrite -dbind_assoc -/exec.
  eapply dbind_eq; [|done].
  intros [e' σ'] Hs.
  rewrite dret_id_left //.
Qed.

Lemma prim_step_true_val e σ n v :
  to_val e = Some v →
  step_or_final ((SeqV e #true)%E, σ) ≫= exec n =
    exec n ((of_val #true)%E, σ).
Proof.
  intros He.
  rewrite 1!step_or_final_no_final /=; [|eauto].
  apply of_to_val in He. rewrite -He.
  rewrite head_prim_step_eq; last first.
  { eexists (_, _).
    eapply head_step_support_equiv_rel.
    by econstructor. }
  erewrite det_head_step_singleton; [|by econstructor]; simpl.
  rewrite dret_id_left -/exec //.
Qed.

Lemma exec_SeriesC_SeqV_true e σ n :
  exec (S n) (SeqV e #true, σ) #true = SeriesC (exec n (e, σ)).
Proof.
  move: e σ; induction n; intros e σ.
  - rewrite exec_Sn.
    destruct (to_val e) eqn:Heq.
    + setoid_rewrite prim_step_true_val; eauto; simpl.
      rewrite Heq dret_mass dret_1_1; auto.
    + setoid_rewrite prim_step_true_no_final; eauto; simpl.
      rewrite Heq.
      rewrite SeriesC_0; auto.
      rewrite /pmf/=/dbind_pmf.
      setoid_rewrite SeriesC_0; auto.
      intros (? & ?).
      rewrite Rmult_0_r; auto.
  - setoid_rewrite exec_Sn.
    destruct (to_val e) eqn:Heq.
    + rewrite (prim_step_true_val _ _ _ v); auto.
      rewrite {1}/step_or_final/= Heq.
      assert (SeriesC (exec n (e, σ)) = SeriesC (dret (e, σ) ≫= exec n)) as Haux.
      { apply SeriesC_ext; intro. rewrite dret_id_left. auto. }
      rewrite -Haux.
      rewrite exec_unfold /= Heq.
      rewrite dret_mass.
      rewrite dret_1_1; auto.
    + rewrite prim_step_true_no_final; auto.
      rewrite step_or_final_no_final; auto.
      rewrite /pmf/=/dbind_pmf.
      rewrite distr_double_swap.
      apply SeriesC_ext; intro.
      rewrite SeriesC_scal_l.
      rewrite (Rmult_eq_compat_l (prim_step e σ n0)
                 ((let '(e', σ') := n0 in prim_step (SeqV e' #true) σ' ≫= exec n) #true)
                 (SeriesC (exec n n0))); auto.
      destruct n0. rewrite -IHn.
      rewrite exec_Sn.
      rewrite step_or_final_no_final //; auto. 
Qed.

Lemma lim_exec_SeriesC_SeqV_true e σ :
  SeriesC (lim_exec (e, σ)) = (lim_exec (SeqV e #true, σ)) #true.
Proof.
  rewrite lim_exec_unfold.
  erewrite SeriesC_ext; [|intro; apply lim_exec_unfold].
  simpl.
  rewrite (MCT_seriesC _ (λ n, SeriesC (exec n (e,σ)))
             (Sup_seq (λ n0 : nat, SeriesC (λ n : val, exec n0 (e, σ) n)))) .
  - rewrite (mon_sup_succ (λ n : nat, exec n ((SeqV e #true)%E, σ) #true)).
    + f_equal. apply Sup_seq_ext; intro n.
      rewrite (exec_SeriesC_SeqV_true e σ n); auto.
    + intro; apply exec_mono.
  - intros; auto.
  - intros. apply: (exec_mono (_,_)).
  - intros; exists 1; intros; auto.
  - intros. apply SeriesC_correct; auto.
  - rewrite (Rbar_le_sandwich 0 1); auto.
    + apply Sup_seq_correct.
    + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
    + apply upper_bound_ge_sup; intro; simpl; auto.
Qed.

Lemma ctx_refines_impl_alt Γ e1 e2 τ :
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) → ctx_refines_alt Γ e1 e2 τ.
Proof.
  intros H K σ0 τ' Hty.
  pose (K' := (CTX_AppR (LamV BAnon #true)%E):: K).
  cut (∀ e, lim_exec (SeqV e #true, σ0) #true = SeriesC (lim_exec (e, σ0))).
  - intros Heq. rewrite -2!Heq.
    eapply (H K' σ0 true).
    repeat econstructor; eauto.
  - intros e.
    rewrite lim_exec_SeriesC_SeqV_true //.
Qed.
