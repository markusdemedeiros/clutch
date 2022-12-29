(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Logical relation is sound w.r.t. the contextual refinement. *)
From iris.proofmode Require Import proofmode.
From self.logrel Require Export model adequacy.
From self.typing Require Export contextual_refinement.

(* Observable types are, at the moment, exactly the unboxed types
   which support direct equality tests. *)
(* Definition ObsType : type → Prop := λ τ, EqType τ ∧ UnboxedType τ. *)

(* Lemma logrel_adequate Σ `{relocPreG Σ} *)
(*    e e' τ (σ : state) : *)
(*   (∀ `{relocG Σ} Δ, ⊢ {⊤;Δ;∅} ⊨ e ≤log≤ e' : τ) → *)
(*   adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h) *)
(*     ∧ (EqType τ → v = v')). *)
(* Proof. *)
(*   intros Hlog. *)
(*   set (A := λ (HΣ : relocG Σ), interp τ []). *)
(*   eapply (refines_adequate Σ A); last first. *)
(*   - intros HΣ. specialize (Hlog HΣ []). *)
(*     revert Hlog. unfold A, bin_log_related. *)
(*     rewrite !fmap_empty. intros Hvs. *)
(*     iPoseProof Hvs as "H". iSpecialize ("H" $! ∅ with "[]"). *)
(*     { iApply env_ltyped2_empty. } *)
(*     by rewrite !fmap_empty !subst_map_empty. *)
(*   - intros HΣ v v'. unfold A. iIntros "Hvv". *)
(*     iIntros (Hτ). by iApply (eq_type_sound with "Hvv"). *)
(* Qed. *)

(* Theorem logrel_typesafety Σ `{relocPreG Σ} e e' τ thp σ σ' : *)
(*   (∀ `{relocG Σ} Δ, ⊢ {⊤;Δ;∅} ⊨ e ≤log≤ e : τ) → *)
(*   rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → *)
(*   not_stuck e' σ'. *)
(* Proof. *)
(*   intros Hlog ??. *)
(*   cut (adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e], σ) (of_val v' :: thp', h) ∧ (EqType τ → v = v'))); first (intros [_ ?]; eauto). *)
(*   eapply logrel_adequate; eauto. *)
(* Qed. *)

(* Theorem F_mu_ref_conc_typesfety e e' τ σ thp σ' : *)
(*   ∅ ⊢ₜ e : τ → *)
(*   rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → *)
(*   is_Some (to_val e') ∨ reducible e' σ'. *)
(* Proof. *)
(*   intros. *)
(*   eapply (logrel_typesafety relocΣ); eauto. *)
(*   intros. by apply fundamental. *)
(* Qed. *)

(* Lemma logrel_simul Σ `{relocPreG Σ} *)
(*   e e' τ v thp hp σ : *)
(*   (∀ `{relocG Σ} Δ, ⊢ {⊤;Δ;∅} ⊨ e ≤log≤ e' : τ) → *)
(*   rtc erased_step ([e], σ) (of_val v :: thp, hp) → *)
(*   (∃ thp' hp' v', rtc erased_step ([e'], σ) (of_val v' :: thp', hp') ∧ (ObsType τ → v = v')). *)
(* Proof. *)
(*   intros Hlog Hsteps. *)
(*   cut (adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h) ∧ (EqType τ → v = v'))). *)
(*   { unfold ObsType. destruct 1; naive_solver. } *)
(*   eapply logrel_adequate; eauto. *)
(* Qed. *)

Lemma refines_sound_open Σ `{!prelogrelGpreS Σ} Γ e e' τ :
  (∀ `{prelogrelGS Σ} Δ, ⊢ {⊤;Δ;Γ} ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog K σ₀ b Htyped.
  cut (∀ n, ((exec_val n (fill_ctx K e, σ₀)) #b <=
             (lim_exec_val (fill_ctx K e', σ₀)) #b)%R).
  { intros Hn. by eapply lim_exec_val_continous. }
  intros n.
  eapply refRcoupl_eq_elim.
  eapply (refines_coupling Σ (λ _, lrel_bool)); last first.
  - iIntros (?).
    iPoseProof (bin_log_related_under_typed_ctx with "[]") as "H"; [done| |].
    { iIntros "!>" (?). iApply Hlog. }
    iSpecialize ("H" $! [] ∅ with "[]").
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    rewrite /interp 2!fmap_empty 2!subst_map_empty /=.
    done.
  - by iIntros (???) "[%b' [-> ->]]".
Qed.

Lemma refines_sound Σ `{Hpre : !prelogrelGpreS Σ} (e e': expr) τ :
  (∀ `{prelogrelGS Σ} Δ, ⊢ REL e << e' : (interp τ Δ)) →
  ∅ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog. eapply (refines_sound_open Σ).
  iIntros (? Δ vs).
  rewrite fmap_empty env_ltyped2_empty_inv.
  iIntros (->).
  rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.
