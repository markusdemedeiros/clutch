From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From stdpp Require Import fin_maps fin_map_dom.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import con_language con_ectx_language sch_erasable.
From clutch.con_prob_lang Require Import notation lang metatheory.
From clutch.prob Require Import couplings couplings_app mdp.

Set Default Proof Using "Type*".
Local Open Scope R.

Section erasure_helpers.

  Variable (m : nat).
  Context {sch_int_σ: Type}.
  Context `{TapeOblivious sch_int_σ sch}.
  Context {ζ : sch_int_σ}.
  Hypothesis IH :
    ∀ (es1 : list expr) (σ1 : state) α N zs,
    tapes σ1 !! α = Some (N; zs) →
    Rcoupl
      (dmap (λ x, x.1) (sch_pexec sch m (ζ, (es1, σ1))))
      (dmap (λ x, x.1) (dunifP N ≫= (λ z, sch_pexec sch m (ζ, (es1, state_upd_tapes <[α:= (N; zs ++ [z])]> σ1))))) eq.

  (* Local Lemma ind_case_det e σ α N zs K : *)
  (*   tapes σ !! α = Some (N; zs) → *)
  (*   is_det_head_step e σ = true → *)
  (*   Rcoupl *)
  (*     (dmap (fill_lift K) (head_step e σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)) *)
  (*     (dunifP N ≫= (λ z, dmap *)
  (*                          (fill_lift K) *)
  (*                          (head_step e (state_upd_tapes <[α:= (N; zs ++ [z]) ]> σ)) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))) *)
  (*      (=). *)
  (* Proof using m IH. *)
  (*   intros Hα (e2 & (σ2 & Hdet))%is_det_head_step_true%det_step_pred_ex_rel. *)
  (*   erewrite 1!det_head_step_singleton; [|done..]. *)
  (*   setoid_rewrite (det_head_step_singleton ); eauto; last first. *)
  (*   - eapply det_head_step_upd_tapes; eauto. *)
  (*   - erewrite det_step_eq_tapes in Hα; [|done]. *)
  (*     rewrite !dmap_dret. *)
  (*     setoid_rewrite (dmap_dret (fill_lift K)). *)
  (*     rewrite !dret_id_left. *)
  (*     erewrite (distr_ext (dunifP _ ≫= _) _); last first. *)
  (*     { intros. apply dbind_pmf_ext; [|done..]. intros. *)
  (*       rewrite dret_id_left. done. } *)
  (*     rewrite -dmap_dbind. apply IH. done. *)
  (* Qed. *)

  (* Local Lemma ind_case_dzero e σ α N zs K : *)
  (*   tapes σ !! α = Some (N; zs) → *)
  (*   head_step e σ = dzero → *)
  (*   Rcoupl *)
  (*     (dmap (fill_lift K) (head_step e σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)) *)
  (*     (dunifP N ≫= (λ z, *)
  (*                     dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=(N; zs ++ [z])]> σ)) ≫= *)
  (*                       λ ρ, dmap (λ x, x.1) (pexec m ρ))) eq. *)
  (* Proof using m IH. *)
  (*   intros Hα Hz. *)
  (*   rewrite Hz. *)
  (*   setoid_rewrite head_step_dzero_upd_tapes; [|by eapply elem_of_dom_2|done]. *)
  (*   rewrite dmap_dzero dbind_dzero dzero_dbind. *)
  (*   apply Rcoupl_dzero_dzero. *)
  (* Qed. *)

  (* Local Lemma ind_case_alloc σ α N ns (z : Z) K : *)
  (*   tapes σ !! α = Some (N; ns) → *)
  (*   Rcoupl *)
  (*     (dmap (fill_lift K) (head_step (alloc #z) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)) *)
  (*     (dunifP N ≫= *)
  (*        (λ n, dmap (fill_lift K) (head_step (alloc #z) (state_upd_tapes <[α:= (N; ns ++ [n])]> σ)) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))) *)
  (*     eq. *)
  (* Proof using m IH. *)
  (*   intros Hα. *)
  (*   rewrite dmap_dret dret_id_left -/exec. *)
  (*   setoid_rewrite (dmap_dret (fill_lift K)). *)
  (*   erewrite (distr_ext (dunifP N ≫= _)); last first. *)
  (*   { intros. apply dbind_pmf_ext; [|done..]. *)
  (*     intros. rewrite dret_id_left. done. } *)
  (*   rewrite -dmap_dbind. *)
  (*   (* TODO: fix slightly ugly hack ... *) *)
  (*   revert IH; intro IHm. *)
  (*   apply lookup_total_correct in Hα as Hαtot. *)
  (*   pose proof (elem_fresh_ne _ _ _ Hα) as Hne. *)
  (*   erewrite dbind_ext_right; last first. *)
  (*   { intros n. *)
  (*     rewrite -(fresh_loc_upd_some _ _ (N; ns)); [|done]. *)
  (*     rewrite (fresh_loc_upd_swap σ α (N; ns) (_; [])) //. } *)
  (*   apply IHm. *)
  (*   by apply fresh_loc_lookup. *)
  (* Qed. *)

  (* Local Lemma ind_case_rand_some σ α α' K N M (z : Z) n ns ns' : *)
  (*   N = Z.to_nat z → *)
  (*   tapes σ !! α = Some (M; ns') → *)
  (*   tapes σ !! α' = Some (N; n :: ns) → *)
  (*   Rcoupl *)
  (*     (dmap (fill_lift K) (head_step (rand(#lbl:α') #z) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)) *)
  (*     (dunifP M ≫= *)
  (*        (λ n, dmap (fill_lift K) *)
  (*                (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α:= (M; ns' ++ [n])]> σ)) *)
  (*                ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))) *)
  (*     (=). *)
  (* Proof using m IH. *)
  (*   intros Hz Hα Hα'. *)
  (*   apply lookup_total_correct in Hα as Hαtot. *)
  (*   apply lookup_total_correct in Hα' as Hα'tot. *)
  (*   destruct (decide (α = α')) as [-> | Hαneql]. *)
  (*   - simplify_eq. rewrite /head_step Hα. *)
  (*     setoid_rewrite lookup_insert. *)
  (*     rewrite bool_decide_eq_true_2 //. *)
  (*     rewrite dmap_dret dret_id_left -/exec. *)
  (*     erewrite dbind_ext_right; last first. *)
  (*     { intros. *)
  (*       rewrite -app_comm_cons. *)
  (*       rewrite upd_tape_twice dmap_dret dret_id_left -/exec //. } *)
  (*     assert (Haux : ∀ n, *)
  (*                state_upd_tapes <[α':=(Z.to_nat z; ns ++ [n])]> σ = *)
  (*                state_upd_tapes <[α':=(Z.to_nat z; ns ++ [n])]> (state_upd_tapes <[α':=(Z.to_nat z; ns)]> σ)). *)
  (*     { intros. rewrite /state_upd_tapes. f_equal. rewrite insert_insert //. } *)
  (*     erewrite dbind_ext_right; [| intros; rewrite Haux; done]. *)
  (*     rewrite -dmap_dbind. *)
  (*     apply IH. *)
  (*     apply lookup_insert. *)
  (*   - rewrite /head_step Hα'. *)
  (*     rewrite bool_decide_eq_true_2 //. *)
  (*     setoid_rewrite lookup_insert_ne; [|done]. *)
  (*     rewrite Hα' bool_decide_eq_true_2 //. *)
  (*     rewrite !dmap_dret !dret_id_left -/exec. *)
  (*     erewrite dbind_ext_right; last first. *)
  (*     { intros. *)
  (*       rewrite upd_diff_tape_comm; [|done]. *)
  (*       rewrite dmap_dret dret_id_left -/exec //. } *)
  (*     rewrite -dmap_dbind. *)
  (*     eapply IH. *)
  (*     rewrite lookup_insert_ne //. *)
  (* Qed. *)

  (* Local Lemma ind_case_rand_empty σ α α' K (N M : nat) z ns : *)
  (*   M = Z.to_nat z → *)
  (*   tapes σ !! α = Some (N; ns) → *)
  (*   tapes σ !! α' = Some (M; []) → *)
  (*   Rcoupl *)
  (*     (dmap (fill_lift K) (head_step (rand(#lbl:α') #z) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)) *)
  (*     (dunifP N ≫= *)
  (*        (λ n, dmap (fill_lift K) *)
  (*                (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α := (N; ns ++ [n])]> σ)) *)
  (*                ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))) *)
  (*     eq. *)
  (* Proof using m IH. *)
  (*   intros Hz Hα Hα'. *)
  (*   destruct (decide (α = α')) as [-> | Hαneql]. *)
  (*   + simplify_eq.  rewrite /head_step Hα. *)
  (*     rewrite bool_decide_eq_true_2 //. *)
  (*     rewrite {1 2}/dmap. *)
  (*     rewrite -!dbind_assoc -/exec. *)
  (*     eapply (Rcoupl_dbind _ _ _ _ (=)); [ |apply Rcoupl_eq]. *)
  (*     intros ? b ->. *)
  (*     do 2 rewrite dret_id_left. *)
  (*     rewrite lookup_insert. *)
  (*     rewrite bool_decide_eq_true_2 //. *)
  (*     rewrite dmap_dret dret_id_left -/exec. *)
  (*     rewrite upd_tape_twice. *)
  (*     rewrite /state_upd_tapes insert_id //. *)
  (*     destruct σ; simpl. *)
  (*     apply Rcoupl_eq. *)
  (*   + rewrite /head_step /=. *)
  (*     setoid_rewrite lookup_insert_ne; [|done]. *)
  (*     rewrite Hα'. *)
  (*     rewrite bool_decide_eq_true_2 //. *)
  (*     rewrite {1 2}/dmap. *)
  (*     erewrite (dbind_ext_right (dunifP N)); last first. *)
  (*     { intro. *)
  (*       rewrite {1 2}/dmap. *)
  (*       do 2 rewrite -dbind_assoc -/exec. *)
  (*       done. } *)
  (*     rewrite -!dbind_assoc -/exec. *)
  (*     rewrite dbind_comm. *)
  (*     eapply Rcoupl_dbind; [|apply Rcoupl_eq]. *)
  (*     intros; simplify_eq. *)
  (*     do 2 rewrite dret_id_left /=. *)
  (*     erewrite (distr_ext (dunifP N≫=_)); last first. *)
  (*     { intros. apply dbind_pmf_ext; [|done..]. *)
  (*       intros. rewrite !dret_id_left. done. *)
  (*     } *)
  (*     rewrite dbind_assoc. *)
  (*     by apply IH. *)
  (* Qed. *)

  (* Local Lemma ind_case_rand_some_neq σ α α' K N M ns ns' z : *)
  (*   N ≠ Z.to_nat z → *)
  (*   tapes σ !! α = Some (M; ns') → *)
  (*   tapes σ !! α' = Some (N; ns) → *)
  (*   Rcoupl *)
  (*     (dmap (fill_lift K) (head_step (rand(#lbl:α') #z) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)) *)
  (*     (dunifP M ≫= *)
  (*        (λ n, dmap (fill_lift K) *)
  (*                (head_step (rand(#lbl:α') #z) (state_upd_tapes <[α:= (M; ns' ++ [n]) : tape]> σ)) *)
  (*                ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))) *)
  (*     (=). *)
  (* Proof using m IH. *)
  (*   intros Hz Hα Hα'. *)
  (*   rewrite /head_step Hα'. *)
  (*   rewrite bool_decide_eq_false_2 //. *)
  (*   destruct (decide (α = α')) as [-> | Heq]. *)
  (*   - simplify_eq. *)
  (*     setoid_rewrite lookup_insert. *)
  (*     rewrite bool_decide_eq_false_2 //. *)
  (*     rewrite /dmap /=. *)
  (*     rewrite -!dbind_assoc -/exec. *)
  (*     erewrite (dbind_ext_right (dunifP M)); last first. *)
  (*     { intros. rewrite -!dbind_assoc -/exec //. } *)
  (*     rewrite dbind_comm. *)
  (*     eapply Rcoupl_dbind; [|apply Rcoupl_eq]. *)
  (*     intros; simplify_eq. *)
  (*     rewrite 2!dret_id_left. *)
  (*     erewrite (distr_ext (dunifP M ≫=_ )); last first. *)
  (*     { intros. apply dbind_pmf_ext; [|done..]. *)
  (*       intros. rewrite !dret_id_left; done. *)
  (*     } *)
  (*     rewrite -dmap_dbind. *)
  (*     by apply IH. *)
  (*   - setoid_rewrite lookup_insert_ne; [|done]. *)
  (*     rewrite Hα' bool_decide_eq_false_2 //. *)
  (*     rewrite /dmap. *)
  (*     rewrite -!dbind_assoc -/exec. *)
  (*     erewrite (dbind_ext_right (dunifP M)); last first. *)
  (*     { intros. rewrite -!dbind_assoc -/exec //. } *)
  (*     rewrite dbind_comm. *)
  (*     eapply Rcoupl_dbind; [|apply Rcoupl_eq]. *)
  (*     intros; simplify_eq. *)
  (*     rewrite 2!dret_id_left. *)
  (*     erewrite (distr_ext (dunifP M ≫=_ )); last first. *)
  (*     { intros. apply dbind_pmf_ext; [|done..]. *)
  (*       intros. rewrite !dret_id_left; done. *)
  (*     } *)
  (*     rewrite -dmap_dbind. *)
  (*     by apply IH. *)
  (* Qed. *)

  (* Local Lemma ind_case_rand σ α K (M N : nat) z ns : *)
  (*   N = Z.to_nat z → *)
  (*   tapes σ !! α = Some (M; ns) → *)
  (*   Rcoupl *)
  (*     (dmap (fill_lift K) (head_step (rand #z) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)) *)
  (*     (dunifP M ≫= *)
  (*        (λ n, *)
  (*          dmap (fill_lift K) *)
  (*            (head_step (rand #z) (state_upd_tapes <[α := (M; ns ++ [n]) : tape]> σ)) *)
  (*            ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))) *)
  (*     eq. *)
  (* Proof using m IH. *)
  (*   intros Hz Hα. *)
  (*   rewrite /head_step. *)
  (*   rewrite {1 2}/dmap. *)
  (*   erewrite (dbind_ext_right (dunifP M)); last first. *)
  (*   { intro. *)
  (*     rewrite {1 2}/dmap. *)
  (*     do 2 rewrite -dbind_assoc //. } *)
  (*   rewrite -/exec /=. *)
  (*   rewrite -!dbind_assoc -/exec. *)
  (*   erewrite (dbind_ext_right (dunifP M)); last first. *)
  (*   { intros n. rewrite -!dbind_assoc. done. } *)
  (*   rewrite dbind_comm. *)
  (*   eapply Rcoupl_dbind; [|apply Rcoupl_eq]. *)
  (*   intros; simplify_eq. *)
  (*   do 2 rewrite dret_id_left. *)
  (*   erewrite (distr_ext (dunifP M ≫=_ )); last first. *)
  (*   { intros. apply dbind_pmf_ext; [|done..]. *)
  (*     intros. rewrite !dret_id_left; done. *)
  (*   } *)
  (*   rewrite -dmap_dbind. *)
  (*   apply IH; auto. *)
  (* Qed. *)

End erasure_helpers.


Lemma prim_coupl_upd_tapes_dom `{Countable sch_int_σ} m (es1: list expr) σ1 α N ns ζ (sch: scheduler (con_lang_mdp con_prob_lang) sch_int_σ):
  σ1.(tapes) !! α = Some (N; ns) →
  Rcoupl
    (dmap (λ x, x.2.1) (sch_pexec sch m (ζ, (es1, σ1))))
    (dunifP N ≫=
       (λ n, dmap (λ x, x.2.1) (sch_pexec sch m (ζ, (es1, state_upd_tapes <[α := (N; ns ++ [n])]> σ1)))))
    (=).
Proof.
Admitted.
(*   rewrite -dmap_dbind. *)
(*   revert e1 σ1 α N ns; induction m; intros e1 σ1 α N ns Hα. *)
(*   - rewrite /pexec /=. *)
(*     rewrite dmap_dret. *)
(*     rewrite dmap_dbind. *)
(*     erewrite (distr_ext (dunifP N≫=_)); last first. *)
(*     { intros. apply dbind_pmf_ext; [|done..]. *)
(*       intros. rewrite dmap_dret. done. *)
(*     } *)
(*     rewrite (dret_const (dunifP N)); [apply Rcoupl_eq | apply dunif_mass; lia]. *)
(*   - rewrite pexec_Sn /step_or_final /=. *)
(*     destruct (to_val e1) eqn:He1. *)
(*     + rewrite dret_id_left. *)
(*       rewrite -/(pexec m (e1, σ1)). *)
(*       rewrite pexec_is_final; last by rewrite /is_final. *)
(*       rewrite dmap_dret. simpl. *)
(*       rewrite dmap_dbind. *)
(*       erewrite (distr_ext (dunifP N ≫=_)); last first. *)
(*       { intros. apply dbind_pmf_ext; [|done..]. *)
(*         intros. rewrite pexec_is_final; last by rewrite /is_final. *)
(*         rewrite dmap_dret. simpl. done. *)
(*       } *)
(*       rewrite dret_const; [|solve_distr_mass]. *)
(*       apply Rcoupl_eq. *)
(*     + rewrite !dmap_dbind. *)
(*       erewrite (distr_ext (dunifP N ≫= _)); last first. *)
(*       { intros. apply dbind_pmf_ext; [|done..]. *)
(*         intros. setoid_rewrite pexec_Sn. *)
(*         rewrite /step_or_final/=He1/prim_step/=. *)
(*         rewrite dmap_dbind. *)
(*         done. *)
(*       } *)
(*       rewrite /prim_step/=. *)
(*       destruct (decomp e1) as [K ered] eqn:Hdecomp_e1. *)
(*       rewrite Hdecomp_e1. *)
(*       destruct (det_or_prob_or_dzero ered σ1) as [ HD | [HP | HZ]]. *)
(*       * eapply ind_case_det; [done|done|by apply is_det_head_step_true]. *)
(*       * inversion HP; simplify_eq. *)
(*         -- by eapply ind_case_alloc. *)
(*         -- by eapply ind_case_rand_some. *)
(*         -- by eapply ind_case_rand_empty. *)
(*         -- by eapply ind_case_rand_some_neq. *)
(*         -- by eapply ind_case_rand. *)
(*       * by eapply ind_case_dzero. *)
(* Qed. *)

Lemma pexec_coupl_step_pexec `{Countable sch_int_σ} m es1 σ1 α bs ζ (sch: scheduler (con_lang_mdp con_prob_lang) sch_int_σ) :
  σ1.(tapes) !! α = Some bs →
   Rcoupl
    (dmap (λ ρ, ρ.2.1) (sch_pexec sch m (ζ, (es1, σ1))))
    (dmap (λ ρ, ρ.2.1) (state_step σ1 α ≫= (λ σ2, sch_pexec sch m (ζ, (es1, σ2)))))
    eq.
Proof.
  intros.
  destruct bs.
  eapply Rcoupl_eq_trans; first eapply prim_coupl_upd_tapes_dom; try done.
  rewrite <-dmap_dbind.
  apply Rcoupl_dmap.
  erewrite state_step_unfold; last done.
  rewrite /dmap.
  rewrite -dbind_assoc.
  eapply Rcoupl_dbind; last apply Rcoupl_eq.
  intros ??->.
  rewrite dret_id_left.
  eapply Rcoupl_mono; first apply Rcoupl_eq.
  intros. naive_solver.
Qed.

Lemma prim_coupl_step_prim `{Hcountable:Countable sch_int_σ} m es1 σ1 α bs ζ (sch: scheduler (con_lang_mdp con_prob_lang) sch_int_σ) :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (sch_exec sch m (ζ, (es1, σ1)))
    (state_step σ1 α ≫= (λ σ2, sch_exec sch m (ζ, (es1, σ2))))
    eq.
Proof.
  intros Hα.
  epose proof pexec_coupl_step_pexec _ _ _ _ _ _ _ Hα as H.
  setoid_rewrite sch_exec_pexec_relate.
  simpl.
  set (g:= λ es2: list expr, match option_bind _ _ to_val ((es2!!(0%nat)): option expr) with | Some b => dret b | None => dzero end).
  erewrite (distr_ext _ (dmap (λ ρ, ρ.2.1) (sch_pexec sch m (ζ, (es1, σ1))) ≫= g )); last first.
  { intros. rewrite /dmap.
    rewrite -dbind_assoc. simpl.
    apply dbind_pmf_ext; try done.
    intros [? []]. rewrite dret_id_left.
    rewrite /con_lang_mdp_to_final. intros.
    simpl. rewrite /option_bind. done.
  }
  erewrite (distr_ext (state_step _ _ ≫= _) _).
  - eapply Rcoupl_dbind; last exact.
    intros. subst. apply Rcoupl_eq.
  - intros. rewrite /dmap.
    rewrite -!dbind_assoc. simpl.
    apply dbind_pmf_ext; [|done|done].
    intros. apply dbind_pmf_ext; try done.
    intros [?[]]?.
    rewrite dret_id_left. simpl.
    rewrite /option_bind. done.
Qed.

Lemma state_step_sch_erasable `{Hcountable:Countable sch_int_σ} σ1 α bs (sch: scheduler (con_lang_mdp con_prob_lang) sch_int_σ):
  σ1.(tapes) !! α = Some bs →
  sch_erasable sch (state_step σ1 α) σ1.
Proof.
  intros. rewrite /sch_erasable.
  intros.
  symmetry.
  apply Rcoupl_eq_elim.
  by eapply prim_coupl_step_prim.
Qed.

(* Lemma iterM_state_step_erasable σ1 α bs n: *)
(*   σ1.(tapes) !! α = Some bs → *)
(*   erasable (iterM n (λ σ, state_step σ α) σ1) σ1. *)
(* Proof. *)
(*   revert σ1 bs. *)
(*   induction n; intros σ1 bs H. *)
(*   - simpl. apply dret_erasable. *)
(*   - simpl. apply erasable_dbind; first by eapply state_step_erasable. *)
(*     intros ? H0.  *)
(*     destruct bs.  *)
(*     erewrite state_step_unfold in H0; last done. *)
(*     rewrite dmap_pos in H0. destruct H0 as (?&->&K). *)
(*     eapply IHn. simpl. apply lookup_insert. *)
(* Qed. *)

(* Lemma limprim_coupl_step_limprim_aux e1 σ1 α bs v: *)
(*   σ1.(tapes) !! α = Some bs → *)
(*   (lim_exec (e1, σ1)) v = *)
(*   (state_step σ1 α ≫= (λ σ2, lim_exec (e1, σ2))) v. *)
(* Proof. *)
(*   intro Hsome. *)
(*    rewrite lim_exec_unfold/=. *)
(*    rewrite {2}/pmf/=/dbind_pmf. *)
(*    setoid_rewrite lim_exec_unfold. *)
(*    simpl in *. *)
(*    assert *)
(*      (SeriesC (λ a: state, state_step σ1 α a * Sup_seq (λ n : nat, exec n (e1, a) v)) = *)
(*      SeriesC (λ a: state, Sup_seq (λ n : nat, state_step σ1 α a * exec n (e1, a) v))) as Haux. *)
(*    { apply SeriesC_ext; intro v'. *)
(*      apply eq_rbar_finite. *)
(*      rewrite rmult_finite. *)
(*      rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, exec n (e1, v') v))); auto. *)
(*      - rewrite <- (Sup_seq_scal_l (state_step σ1 α v') (λ n : nat, exec n (e1, v') v)); auto. *)
(*      - apply (Rbar_le_sandwich 0 1). *)
(*        + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto. *)
(*        + apply upper_bound_ge_sup; intro; simpl; auto. *)
(*    } *)
(*    rewrite Haux. *)
(*    rewrite (MCT_seriesC _ (λ n, exec n (e1,σ1) v) (lim_exec (e1,σ1) v)); auto. *)
(*    - real_solver. *)
(*    - intros. apply Rmult_le_compat; auto; [done|apply exec_mono]. *)
(*    - intro. exists (state_step σ1 α a)=>?. real_solver. *)
(*    - intro n. *)
(*      rewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim n e1 σ1 α bs Hsome)); auto. *)
(*      rewrite {3}/pmf/=/dbind_pmf. *)
(*      apply SeriesC_correct; auto. *)
(*      apply (ex_seriesC_le _ (state_step σ1 α)); auto. *)
(*      real_solver. *)
(*    - rewrite lim_exec_unfold. *)
(*      rewrite rbar_finite_real_eq; [apply Sup_seq_correct |]. *)
(*      rewrite mon_sup_succ. *)
(*      + apply (Rbar_le_sandwich 0 1); auto. *)
(*        * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto. *)
(*        * apply upper_bound_ge_sup; intro; simpl; auto. *)
(*      + intros. eapply exec_mono. *)
(* Qed. *)

(* Lemma limprim_coupl_step_limprim e1 σ1 α bs : *)
(*   σ1.(tapes) !! α = Some bs → *)
(*   Rcoupl *)
(*     (lim_exec (e1, σ1)) *)
(*     (state_step σ1 α ≫= (λ σ2, lim_exec (e1, σ2))) *)
(*     eq. *)
(* Proof. *)
(*   intro Hsome. *)
(*   erewrite (distr_ext (lim_exec (e1, σ1))); last first. *)
(*   - intro a. *)
(*     apply (limprim_coupl_step_limprim_aux _ _ _ _ _ Hsome). *)
(*   - apply Rcoupl_eq. *)
(* Qed. *)

(* Lemma lim_exec_eq_erasure αs e σ : *)
(*   αs ⊆ get_active σ → *)
(*   lim_exec (e, σ) = foldlM state_step σ αs ≫= (λ σ', lim_exec (e, σ')). *)
(* Proof. *)
(*   induction αs as [|α αs IH] in σ |-*. *)
(*   { rewrite /= dret_id_left //. } *)
(*   intros Hα. *)
(*   eapply Rcoupl_eq_elim. *)
(*   assert (lim_exec (e, σ) = state_step σ α ≫= (λ σ2, lim_exec (e, σ2))) as ->. *)
(*   { apply distr_ext => v. *)
(*     assert (α ∈ get_active σ) as Hel; [apply Hα; left|]. *)
(*     rewrite /get_active in Hel. *)
(*     apply elem_of_elements, elem_of_dom in Hel as [? ?]. *)
(*     by eapply limprim_coupl_step_limprim_aux. } *)
(*   rewrite foldlM_cons -dbind_assoc. *)
(*   eapply Rcoupl_dbind; [|eapply Rcoupl_pos_R, Rcoupl_eq]. *)
(*   intros ?? (-> & Hs%state_step_support_equiv_rel & _). *)
(*   inversion_clear Hs. *)
(*   rewrite IH; [eapply Rcoupl_eq|]. *)
(*   intros α' ?. rewrite /get_active /=. *)
(*   apply elem_of_elements. *)
(*   apply elem_of_dom. *)
(*   destruct (decide (α = α')); subst. *)
(*   + eexists. rewrite lookup_insert //. *)
(*   + rewrite lookup_insert_ne //. *)
(*     apply elem_of_dom. eapply elem_of_elements, Hα. by right. *)
(* Qed. *)