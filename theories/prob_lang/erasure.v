From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Import fin_maps fin_map_dom.
From self.prelude Require Import stdpp_ext.
From self.program_logic Require Export exec.
From self.prob_lang Require Import notation lang metatheory.
From self.prob Require Export couplings distribution.

Set Default Proof Using "Type*".
Local Open Scope R.

Section erasure_helpers.

  Variable (m : nat).
  Hypothesis IH :
    ∀ (e1 : expr) (σ1 : state) α n zs,
    tapes σ1 !! α = Some (n, zs) →
    Rcoupl (exec_val m (e1, σ1))
      (dbind (λ z, exec_val m (e1, state_upd_tapes <[α:= (n, zs ++ [Z.of_nat z])]> σ1)) (unif_distr n)) eq.

  Local Lemma ind_case_det e σ α n zs K :
    tapes σ !! α = Some (n, zs) →
    is_det_head_step e σ = true →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= exec_val m)
      (unif_distr n ≫= (λ z : nat, dmap (fill_lift K)
                                   (head_step e (state_upd_tapes <[α:= (n, zs ++ [Z.of_nat z]) ]> σ)) ≫= exec_val m))
       eq.
  Proof using m IH.
    intros Hα (e2 & (σ2 & Hdet))%is_det_head_step_true%det_step_pred_ex_rel.
    (* erewrite det_step_eq_tapes in Hα; [|done]. *)
    erewrite 1!det_head_step_singleton; [|done..].
    setoid_rewrite (det_head_step_singleton ); eauto; last first.
    - eapply det_head_step_upd_tapes; eauto.
    - erewrite det_step_eq_tapes in Hα; [|done].
      rewrite !dmap_dret.
      setoid_rewrite (dmap_dret (fill_lift K)).
      rewrite !dret_id_left.
      setoid_rewrite (dret_id_left (exec_val m)).
      eapply IH; eauto.
  Qed.

  Local Lemma ind_case_dzero e σ α n zs K :
    tapes σ !! α = Some (n, zs) →
    is_det_head_step e σ = false →
    ¬ det_head_step_pred e σ →
    (∀ σ', σ.(heap) = σ'.(heap) → head_step e σ' = dzero) →
    Rcoupl
      (dmap (fill_lift K) (head_step e σ) ≫= exec_val m)
      (unif_distr n ≫= (λ z,
         dmap (fill_lift K) (head_step e (state_upd_tapes <[α:=(n, zs ++ [Z.of_nat z])]> σ)) ≫= exec_val m)) eq.
  Proof using m IH.
    intros Hα Hdet Hndet HZ.
    rewrite !HZ //.
    rewrite dmap_dzero dbind_dzero.
    exists dzero; split.
    - split.
      + rewrite /lmarg dmap_dzero; auto.
      + rewrite /rmarg dmap_dzero.
        apply distr_ext=> ?.
        rewrite {1}/pmf/dzero.
        erewrite dbind_ext_right; last first.
        { intro.
          rewrite HZ; [ | auto].
          rewrite dmap_dzero.
          rewrite dbind_dzero.
          auto.
        }
        rewrite /pmf/=/dbind_pmf.
        symmetry; apply SeriesC_0.
        intro.
        rewrite /pmf /dzero; lra.
    - intros []. rewrite /pmf /=. lra.
  Qed.


  Local Lemma ind_case_alloc σ α n zs n0 K :
    tapes σ !! α = Some (n, zs) →
    prob_head_step_pred (alloc n0) σ →
    ¬ det_head_step_pred (alloc n0) σ →
    is_det_head_step (alloc n0) σ = false →
    Rcoupl
      (dmap (fill_lift K) (head_step (alloc n0) σ) ≫= exec_val m)
      (unif_distr n ≫=
         (λ z : nat, dmap (fill_lift K) (head_step (alloc n0) (state_upd_tapes <[α:= (n, zs ++ [Z.of_nat z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα HP Hndet Hdet.
    rewrite head_step_alloc_unfold.
    rewrite dmap_dret dret_id_left.
    rewrite -/exec_val.
    setoid_rewrite (dmap_dret (fill_lift K)).
    setoid_rewrite (dret_id_left (exec_val m)).
    (* TODO: fix slightly ugly hack :P *)
    revert IH; intro IHm.
    specialize (IHm (fill K (#lbl:(fresh_loc (tapes σ)))) (state_upd_tapes <[fresh_loc (tapes σ):=(n0, [])]> σ) α n zs).
    apply lookup_total_correct in Hα as Hαtot.
    pose proof (elem_fresh_ne _ _ _ Hα) as Hne.
    assert (α ≠ fresh_loc (tapes σ)) as Hne' by auto ; clear Hne.
    (* rewrite -(upd_diff_tape_tot σ _ _ _ Hne') in IHm. *)
    specialize (IHm (fresh_loc_lookup σ α (n,zs) (n0,[]) Hα)).
    (*rewrite Hαtot in IHm.*)
    rewrite /add_int_to_tape in IHm.
    (* setoid_rewrite Hαtot. *)
    (* This is a bit slow *)
    setoid_rewrite <- fresh_loc_upd_some; eauto.
    assert (∀ z e, exec_val m (e, state_upd_tapes <[fresh_loc (tapes σ):=(n0, [])]> (state_upd_tapes <[α:=(n, zs ++ [z])]> σ)) =
                     exec_val m (e, state_upd_tapes <[α:=(n, zs ++ [z])]> (state_upd_tapes <[fresh_loc (tapes σ):=(n0, [])]> σ))) as H.
    { intros x. by erewrite (fresh_loc_upd_swap σ α _ (n0,[]) (n, _)). }
    setoid_rewrite H.
    apply IHm.
  Qed.

  Local Lemma ind_case_flip_some σ α α' K z n zs n' zs' :
    tapes σ !! α = Some (n, zs) →
    tapes σ !! α' = Some (n', z :: zs') →
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= exec_val m)
      (unif_distr n ≫=
         (λ z : nat, dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α:= (n, zs ++ [Z.of_nat z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα Hα'.
    apply lookup_total_correct in Hα as Hαtot.
    apply lookup_total_correct in Hα' as Hα'tot.
    destruct (decide (α = α')) as [-> | Hαneql].
    - simplify_eq.
      rewrite (head_step_flip_nonempty_unfold _ _ n z zs') //.
      rewrite /add_int_to_tape.
      rewrite dmap_dret dret_id_left.
      (* Can I stop Coq from unfolding the fixpoint? *)
      rewrite -/exec_val.
      simpl fill_lift.
      specialize (IH (fill K #z) (state_upd_tapes <[α':=(n, zs')]> σ) α' n zs').
      setoid_rewrite (head_step_flip_nonempty_unfold _ _ n z); last first.
      { simpl. rewrite lookup_insert.
        rewrite app_comm_cons; auto. }
      (* Why is append unfolded? *)
      rewrite -/app.
      erewrite dbind_ext_right; last first.
      { intro; rewrite upd_tape_twice dmap_dret dret_id_left.
        done.}
      simpl.
      (* There must be a better way *)
      assert
        (forall z0, state_upd_tapes <[α':=(n, zs' ++ [z0])]> σ =
                 state_upd_tapes <[α':=(n, zs' ++ [z0])]> (state_upd_tapes <[α':=(n, zs')]> σ)) as Haux.
      {
        intro z0.
        rewrite /state_upd_tapes. f_equal.
        rewrite insert_insert; auto.
      }
      erewrite dbind_ext_right; [ | intro; rewrite Haux; done].
      apply IH.
      apply lookup_insert.
    - rewrite (head_step_flip_nonempty_unfold _ _ n' z zs') //.
      setoid_rewrite (head_step_flip_nonempty_unfold _ _ n' z zs'); last first.
      { rewrite lookup_insert_ne; auto. }
      rewrite !dmap_dret !dret_id_left.
      assert (tapes (state_upd_tapes <[α':=(n', zs')]> σ) !! α = Some (n, zs)) as Hα''.
      { rewrite lookup_insert_ne //. }
      pose proof (IH (fill K #z) (state_upd_tapes <[α':=(n', zs')]> σ) α n zs Hα'') as IHm2.
      erewrite dbind_ext_right; last first.
      {
        intro.
        rewrite upd_diff_tape_comm; [ | auto].
        rewrite dmap_dret dret_id_left; done.
      }
      apply IHm2.
  Qed.

  Local Lemma ind_case_flip_empty σ α α' K n n' zs :
    tapes σ !! α = Some (n, zs) →
    (tapes σ !! α' = Some (n', [])) →
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= exec_val m)
      (unif_distr n ≫=
         (λ z : nat, dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α := (n, zs ++ [Z.of_nat z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα Hα'.
    destruct (decide (α = α')) as [-> | Hαneql].
    + simplify_eq.
      rewrite (head_step_flip_empty_unfold _ α' n) //.
      setoid_rewrite (head_step_flip_nonempty_unfold _ α' n); last first.
      { rewrite lookup_insert; auto. }
      rewrite {1 2}/dmap.
      rewrite -!dbind_assoc.
      eapply (Rcoupl_dbind _ _ _ _ (=)); [ | apply Rcoupl_eq].
      intros ? b ->.
      do 2 rewrite dret_id_left; simpl.
      setoid_rewrite dmap_dret.
      setoid_rewrite dret_id_left.
      simpl.
      rewrite insert_insert.
      rewrite insert_id; auto.
      (* It is a bit hacky that I need to do this before Rcoupl_eq *)
      rewrite -/exec_val.
      destruct σ; simpl.
      apply Rcoupl_eq.
    + rewrite (head_step_flip_empty_unfold _ α' n') //.
      setoid_rewrite (head_step_flip_empty_unfold _ α' n'); last first.
      { rewrite lookup_insert_ne; auto. }
      rewrite {1 2}/dmap.
      erewrite (dbind_ext_right (unif_distr n)); last first.
      { intro.
        rewrite {1 2}/dmap.
        do 2 rewrite -dbind_assoc.
        auto.
      }
      rewrite -!dbind_assoc.
      rewrite -/exec_val.
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros; simplify_eq.
      do 2 rewrite dret_id_left.
      erewrite dbind_ext_right; last first.
      { intro; do 2 rewrite dret_id_left; auto. }
      apply IH; auto.
  Qed.


  Local Lemma ind_case_flip_none σ α α' K n zs :
    tapes σ !! α = Some (n, zs) →
    tapes σ !! α' = None →
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #lbl:α') σ) ≫= exec_val m)
      (unif_distr n ≫=
         (λ z : nat, dmap (fill_lift K) (head_step (flip #lbl:α') (state_upd_tapes <[α := (n, zs ++ [Z.of_nat z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα Hα'.
    destruct (decide (α = α')) as [-> | Hαneql]; [simplify_map_eq|].
    rewrite head_step_flip_unalloc_unfold //.
    setoid_rewrite head_step_flip_unalloc_unfold; last first.
    { rewrite lookup_insert_ne; auto. }
    rewrite /fair_conv_comb.
    rewrite -!dbind_assoc.
    erewrite (dbind_ext_right (unif_distr n)); last first.
    { intro.
      rewrite /dmap.
      do 2 rewrite -dbind_assoc.
      auto.
    }
    rewrite dbind_comm.
    eapply Rcoupl_dbind; [|apply Rcoupl_eq].
    intros; simplify_eq.
    destruct b; simpl; rewrite dret_id_left.
    - simpl.
      rewrite dret_id_left.
      erewrite (dbind_ext_right (unif_distr n)); last first.
      { intros.
        do 2 rewrite dret_id_left.
        simpl; auto.
       }
       apply IH; auto.
    - simpl.
      rewrite dret_id_left.
      erewrite (dbind_ext_right (unif_distr n)); last first.
      { intros.
        do 2 rewrite dret_id_left.
        simpl; auto.
       }
       apply IH; auto.
  Qed.


 
  Local Lemma ind_case_flip_no_tapes (σ : state) (α : loc) K n zs :
    tapes σ !! α = Some (n, zs) →
    Rcoupl
      (dmap (fill_lift K) (head_step (flip #()) σ) ≫= exec_val m)
      (unif_distr n ≫=
         (λ z : nat, dmap (fill_lift K)
            (head_step (flip #())
               (state_upd_tapes <[α:= (n, zs ++ [Z.of_nat z])]> σ)) ≫= exec_val m))
      eq.
  Proof using m IH.
    intros Hα.
    rewrite !head_step_flip_no_tape_unfold.
    rewrite -!dbind_assoc -/exec_val.
    erewrite (dbind_ext_right (unif_distr n)); last first.
    {
      intro.
      rewrite /dmap.
      rewrite !head_step_flip_no_tape_unfold.
      rewrite /fair_conv_comb.
      do 2 rewrite -dbind_assoc; auto.
    }
    rewrite dbind_comm.
    eapply Rcoupl_dbind; [|apply Rcoupl_eq].
    intros ? [] ->.
    - simpl.
      rewrite !dret_id_left.
      erewrite dbind_ext_right; last first.
      {
        intro.
        rewrite !dret_id_left; simpl; auto.
      }
      apply IH; auto.
    - simpl.
      rewrite !dret_id_left.
      erewrite dbind_ext_right; last first.
      {
        intro.
        rewrite !dret_id_left; simpl; auto.
      }
      apply IH; auto.
  Qed.


End erasure_helpers.

Lemma prim_coupl_upd_tapes_dom m e1 σ1 α n zs :
  σ1.(tapes) !! α = Some (n, zs) →
  Rcoupl
    (exec_val m (e1, σ1))
    (dbind (λ z, (exec_val m (e1, (state_upd_tapes <[α := (n, zs ++ [Z.of_nat z])]> σ1)))) (unif_distr n))
    eq.
Proof.
  revert e1 σ1 α n zs; induction m; intros e1 σ1 α n zs Hα.
  - rewrite /exec_val/=.
    destruct (to_val e1) eqn:He1.
    + rewrite (dret_const (unif_distr n) v); [apply Rcoupl_eq | apply SeriesC_unif_distr ].
    + exists dzero. repeat split_and!.
      * rewrite /lmarg dmap_dzero //.
      * apply distr_ext=>?.
        rewrite rmarg_pmf.
        rewrite /pmf/=/dbind_pmf.
        rewrite SeriesC_0 //.
        symmetry.
        apply SeriesC_0.
        rewrite /pmf/=.
        intro; lra.
      * intros ?. rewrite /pmf /=. lra.
  - simpl. destruct (to_val e1) eqn:He1.
    + specialize (IHm e1 σ1 α n zs Hα).
      destruct m; simpl in *; by rewrite He1 in IHm.
    + rewrite /prim_step /=.
      destruct (decomp e1) as [K ered] eqn:decomp_e1.
      rewrite decomp_e1.
      destruct (is_det_head_step ered σ1) eqn:Hdet.
      * by eapply ind_case_det.
      * assert (¬ det_head_step_pred ered σ1) as Hndet.
        { intros ?%is_det_head_step_true. rewrite H // in Hdet. }
        destruct (det_or_prob_or_dzero ered σ1) as [ HD | [HP | HZ]].
        { by destruct Hndet. }
        { inversion HP; simplify_eq.
          - by eapply ind_case_alloc.
          - by eapply ind_case_flip_some.
          - destruct H; [by eapply ind_case_flip_empty | by eapply ind_case_flip_none].
          - by eapply ind_case_flip_no_tapes. }
        { by eapply ind_case_dzero. }
Qed.

Lemma prim_coupl_step_prim m e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (exec_val m (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, exec_val m (e1, σ2)))
    eq.
Proof.
  intros Hα.
  rewrite state_step_fair_conv_comb; last first.
  { apply elem_of_dom. eauto. }
  rewrite fair_conv_comb_dbind.
  do 2 rewrite dret_id_left.
  by eapply prim_coupl_upd_tapes_dom.
Qed.



Lemma limprim_coupl_step_limprim_aux e1 σ1 α bs v:
  σ1.(tapes) !! α = Some bs →
  (lim_exec_val (e1, σ1)) v =
  (state_step σ1 α ≫= (λ σ2, lim_exec_val (e1, σ2))) v.
Proof.
  intro Hsome.
   rewrite lim_exec_val_rw/=.
   rewrite {2}/pmf/=/dbind_pmf.
   setoid_rewrite lim_exec_val_rw.
   simpl in *.
   assert
     (SeriesC (λ a: state, state_step σ1 α a * Sup_seq (λ n : nat, exec_val n (e1, a) v)) =
     SeriesC (λ a: state, Sup_seq (λ n : nat, state_step σ1 α a * exec_val n (e1, a) v))) as Haux.
   { apply SeriesC_ext; intro v'.
     apply eq_rbar_finite.
     rewrite rmult_finite.
     rewrite (rbar_finite_real_eq (Sup_seq (λ n : nat, exec_val n (e1, v') v))); auto.
     - rewrite <- (Sup_seq_scal_l (state_step σ1 α v') (λ n : nat, exec_val n (e1, v') v)); auto.
     - apply (Rbar_le_sandwich 0 1).
       + apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       + apply upper_bound_ge_sup; intro; simpl; auto.
   }
   rewrite Haux.
   rewrite (MCT_seriesC _ (λ n, exec_val n (e1,σ1) v) (lim_exec_val (e1,σ1) v)); auto.
   - intros; apply Rmult_le_pos; auto.
   - intros.
     apply Rmult_le_compat; auto; [apply Rle_refl | apply exec_val_mon]; auto.
   - intro.
     exists (state_step σ1 α a); intro.
     rewrite <- Rmult_1_r.
     apply Rmult_le_compat_l; auto.
   - intro n.
     rewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim n e1 σ1 α bs Hsome)); auto.
     rewrite {3}/pmf/=/dbind_pmf.
     apply SeriesC_correct; auto.
     apply (ex_seriesC_le _ (state_step σ1 α)); auto.
     intro; split; auto.
     + apply Rmult_le_pos; auto.
     + rewrite <- Rmult_1_r.
       apply Rmult_le_compat_l; auto.
   - rewrite lim_exec_val_rw.
     rewrite rbar_finite_real_eq; [ apply Sup_seq_correct | ].
     rewrite mon_sup_succ.
     + apply (Rbar_le_sandwich 0 1); auto.
       * apply (Sup_seq_minor_le _ _ 0%nat); simpl; auto.
       * apply upper_bound_ge_sup; intro; simpl; auto.
     + intro; apply exec_val_mon.
Qed.

Lemma limprim_coupl_step_limprim e1 σ1 α bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl
    (lim_exec_val (e1, σ1))
    (state_step σ1 α ≫= (λ σ2, lim_exec_val (e1, σ2)))
    eq.
Proof.
  intro Hsome.
  erewrite (distr_ext (lim_exec_val (e1, σ1))); last first.
  - intro a.
    apply (limprim_coupl_step_limprim_aux _ _ _ _ _ Hsome).
  - apply Rcoupl_eq.
Qed.

Lemma refRcoupl_erasure e1 σ1 e1' σ1' α α' R Φ m bs bs':
  σ1.(tapes) !! α = Some bs →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (state_step σ1 α) (state_step σ1' α') R →
  (∀ σ2 σ2', R σ2 σ2' →
             refRcoupl (exec_val m (e1, σ2))
               (lim_exec_val (e1', σ2')) Φ ) →
  refRcoupl (exec_val m (e1, σ1))
    (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros Hα Hα' HR Hcont.
  eapply refRcoupl_eq_refRcoupl_unfoldl ;
    [eapply prim_coupl_step_prim; eauto |].
  eapply refRcoupl_eq_refRcoupl_unfoldr;
    [| eapply Rcoupl_eq_sym, limprim_coupl_step_limprim; eauto].
  apply (refRcoupl_dbind _ _ _ _ R); auto.
  by eapply Rcoupl_refRcoupl.
Qed.

Lemma refRcoupl_erasure_r (e1 : expr) σ1 e1' σ1' α' R Φ m bs':
  to_val e1 = None →
  σ1'.(tapes) !! α' = Some bs' →
  Rcoupl (prim_step e1 σ1) (state_step σ1' α') R →
  (∀ e2 σ2 σ2', R (e2, σ2) σ2' → refRcoupl (exec_val m (e2, σ2)) (lim_exec_val (e1', σ2')) Φ ) →
  refRcoupl (exec_val (S m) (e1, σ1)) (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros He1 Hα' HR Hcont.
  rewrite exec_val_Sn_not_val //.
  eapply (refRcoupl_eq_refRcoupl_unfoldr _ (state_step σ1' α' ≫= (λ σ2', lim_exec_val (e1', σ2')))).
  - eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros [] ??. by apply Hcont.
  - apply Rcoupl_eq_sym. by eapply limprim_coupl_step_limprim.
Qed.

Lemma refRcoupl_erasure_l (e1 e1' : expr) σ1 σ1' α R Φ m bs :
  σ1.(tapes) !! α = Some bs →
  Rcoupl (state_step σ1 α) (prim_step e1' σ1') R →
  (∀ σ2 e2' σ2', R σ2 (e2', σ2') → refRcoupl (exec_val m (e1, σ2)) (lim_exec_val (e2', σ2')) Φ ) →
  refRcoupl (exec_val m (e1, σ1)) (lim_exec_val (e1', σ1')) Φ.
Proof.
  intros Hα HR Hcont.
  assert (to_val e1' = None).
  { apply Rcoupl_pos_R, Rcoupl_inhabited_l in HR as (?&?&?&?&?); [eauto using val_stuck|].
    rewrite state_step_mass; [lra|]. apply elem_of_dom. eauto. }
  eapply (refRcoupl_eq_refRcoupl_unfoldl _ (state_step σ1 α ≫= (λ σ2, exec_val m (e1, σ2)))).
  - by eapply prim_coupl_step_prim.
  - rewrite lim_exec_val_prim_step.
    rewrite prim_step_or_val_no_val //.
    eapply refRcoupl_dbind; [|by apply Rcoupl_refRcoupl].
    intros ? [] ?. by apply Hcont.
Qed.
