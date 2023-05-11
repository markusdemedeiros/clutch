(** If we assume that we can freely pick presampling tapes to read from when *)
(*     resolving probabilistic choices, we can show refinements/equivalences that *)
(*     do not hold. *)
From clutch Require Export clutch lib.flip lib.conversion.
Set Default Proof Using "Type*".

(** An (unsound) rule that allows us to pick an arbitrary presampling tape when
    resolving the [flip] on the left. *)
Definition refines_tape_unsound `{!clutchRGS Σ} :=
  ∀ K E A α b bs e',
    α ↪B (b :: bs) ∗
    (α ↪B bs -∗ REL fill K (of_val #b) << e' @ E : A)
    ⊢ REL fill K flip << e' @ E : A.


Section counterexample.
  Context `{!clutchRGS Σ}.

  (** [flip_ors] returns [true] with probability 3/4, false with 1/4 *)
  Definition flip_ors : expr :=
    let: "x" := flip in
    let: "y" := flip in
    "x" || "y".

  (** If we assume [refines_tape_unsound], we can show that [flip] refines 
      [flip_ors] which obviously cannot be true. *)
  Lemma counterexample α1 α2 :
    refines_tape_unsound →
    α1 ↪B [] ∗ α2 ↪B []
    ⊢ REL flip << flip_ors  : lrel_bool.
  Proof.
    iIntros (Hrule) "[Hα1 Hα2]". rewrite /flip_ors.
    rel_apply (refines_couple_tape_flip _ _ α1); [done|iFrame].
    iIntros (b1) "Hα1 /=".
    rel_pures_r.
    rel_apply (refines_couple_tape_flip _ _ α2); [done|iFrame].
    iIntros (b2) "Hα2 /=".
    rel_pures_r.
    destruct b1; rel_pures_r.
    - rel_apply (Hrule _ _ _ α1).
      iFrame. iIntros "Hα1". rel_values.
    - rel_apply (Hrule _ _ _ α2).
      iFrame. iIntros "Hα2". rel_values.
  Qed.

End counterexample.

Definition flip' : expr :=
  let: "α1" := allocB in
  let: "α2" := allocB in
  flip.

Lemma counterexample_ctx :
  (∀ `{clutchRGS Σ}, refines_tape_unsound) →
  ∅ ⊨ flip' ≤ctx≤ flip_ors : TBool.
Proof.
  intros Hrule.
  eapply (refines_sound clutchRΣ).
  iIntros (??). rewrite /flip'.
  rel_allocBtape_l α1 as "Hα1".
  rel_allocBtape_l α2 as "Hα2".
  rel_pures_l. rewrite -/flip.
  by iApply (counterexample with "[$]").
Qed.

(* just rewriting with [dret_id_left] unfolds [exec_val] even though its
   opaque.... *)
Local Ltac rem_dret_left :=
  match goal with
  | |- context[dbind (exec_val ?n) (dret ?ρ)] =>
      replace (dbind _ (dret _)) with (exec_val n ρ)
  end; [|rewrite dret_id_left //].

Local Opaque exec_val.

Lemma exec_val_flip' σ :
  exec_val 11 (flip', σ) = fair_conv_comb (dret #true) (dret #false).
Proof.
  rewrite /flip'.

  rewrite exec_val_Sn_not_val //=.
  reshape_prim_step allocB.
  rewrite dmap_dret /=.
  rem_dret_left.

  rewrite exec_val_Sn_not_val //=.
  reshape_prim_step (λ: _, _)%E.
  rewrite dmap_dret /=.
  rem_dret_left.

  rewrite exec_val_Sn_not_val //=.
  rewrite head_prim_step_eq /=; [|eauto with head_step].
  rem_dret_left.

  rewrite exec_val_Sn_not_val //=.
  reshape_prim_step allocB.
  rewrite dmap_dret /=.
  rem_dret_left.
  set (σ' := {| heap := _; tapes := _ |}).

  rewrite exec_val_Sn_not_val //=.
  reshape_prim_step (λ: _, _)%E.
  rewrite dmap_dret /=.
  rem_dret_left.

  rewrite exec_val_Sn_not_val //=.
  rewrite head_prim_step_eq /=; [|eauto with head_step].
  rem_dret_left.

  rewrite -/flip.
  apply exec_val_flip.
Qed.

Lemma exec_val_flip'_obs σ (b : bool) :
  exec_val 11 (flip', σ) #b = 0.5%R.
Proof.
  rewrite exec_val_flip'.
  rewrite fair_conv_comb_pmf.
  destruct b.
  - rewrite dret_1_1 // dret_0 //. lra.
  - rewrite dret_0 // dret_1_1 //. lra.
Qed.

Tactic Notation "reshape_prim_step'" open_constr(efoc) :=
  lazymatch goal with
  | |- context[prim_step ?e _] =>
      reshape_expr e
        ltac:(fun K e' =>
                unify e' efoc;
                rewrite (fill_prim_step_dbind K e') //)
  end.

Local Lemma bias_leq :
 (0 <= 0.75 <= 1)%R.
Proof. lra. Qed.

Lemma exec_is_val e σ n :
  is_Some (to_val e) →
  exec n (e, σ) = dret (e, σ).
Proof.
  induction n. 
  { rewrite exec_O //. }
  intros Hv.
  rewrite exec_Sn.
  rewrite prim_step_or_val_is_val //.
  rewrite dret_id_left.
  rewrite -IHn //.
Qed. 
  
Lemma exec_val_exec n m (ρ : cfg) :
  exec_val (n + m) ρ = dbind (λ ρ', exec_val m ρ') (exec n ρ). 
Proof.
  revert ρ. 
  induction n.
  { intros. rewrite exec_O /= dret_id_left //. }
  intros [e σ]=>/=.
  destruct (to_val e) eqn:Heq.
  - erewrite exec_val_is_val; [|done]. 
    rewrite exec_Sn.
    rewrite prim_step_or_val_is_val //.
    replace (dbind (exec n) (dret (e, σ)))
      with (exec n (e, σ)); [|rewrite dret_id_left //].
    rewrite exec_is_val //.
    rewrite dret_id_left.
    by erewrite exec_val_is_val.
  - rewrite exec_val_Sn_not_val //=.
    rewrite exec_Sn.
    rewrite prim_step_or_val_no_val //=.
    rewrite -dbind_assoc. 
    apply dbind_eq; [|auto].
    intros ρ.
    intros Hs. rewrite IHn //.
Qed. 

Lemma exec_plus_bind K `{!LanguageCtx K} n m (e : expr) σ :
  exec (n + m) (K e, σ) = dbind (λ '(e', σ'), exec m (K e', σ')) (exec n (e, σ)).
Proof.
  revert e σ.
      
Admitted. 

Lemma exec_val_flip_ors σ :
  exec_val 14 (flip_ors, σ) = biased_conv_comb 0.75%R bias_leq (dret #true) (dret #false).
Proof.
  rewrite /flip_ors.
  rewrite (exec_val_exec 12 2) /=.
  
  rewrite exec_Sn.
  rewrite prim_step_or_val_no_val //=.
  reshape_prim_step' flip.
  

Admitted.

Lemma exec_val_flip_ors_obs σ  :
  exec_val 14 (flip_ors, σ) #false = 0.25%R.
Proof.
  rewrite exec_val_flip_ors.
  rewrite biased_conv_comb_pmf.
  rewrite dret_0 // dret_1_1 //. lra.
Qed.

Lemma counterexample_False :
  (∀ `{clutchRGS Σ}, refines_tape_unsound) → False.
Proof.
  intros Hctx%counterexample_ctx.
  set (σ0 := {| heap := ∅; tapes := ∅ |}).
  specialize (Hctx [] σ0 false (TPCTX_nil ∅ _)).
  simpl in *.
  assert (lim_exec_val (flip', σ0) #false = 0.5)%R as Hflip.
  { rewrite (lim_exec_positive_ast 11); [apply exec_val_flip'_obs|].
    rewrite exec_val_flip'.
    (* TODO: extract this as a general lemma about [fair_conv_comb]*)
    rewrite /fair_conv_comb.
    rewrite /pmf /= /dbind_pmf.
    rewrite distr_double_swap.
    setoid_rewrite SeriesC_scal_l.
    setoid_rewrite (SeriesC_ext _ (λ b, fair_coin b)) ; last first.
    { intros []; rewrite dret_mass; lra. }
    rewrite SeriesC_finite_mass/=. lra. }
  assert (lim_exec_val (flip_ors, σ0) #false = 0.25)%R as Hflip_ors.
  { rewrite (lim_exec_positive_ast 14); [apply exec_val_flip_ors_obs|].
    rewrite exec_val_flip_ors.
    rewrite /biased_conv_comb /pmf /= /dbind_pmf.
    rewrite distr_double_swap.
    setoid_rewrite SeriesC_scal_l.
    setoid_rewrite (SeriesC_ext _ (λ b, biased_coin 0.75 bias_leq b)) ; last first.
    { intros []; rewrite dret_mass; lra. }
    rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = true) then 0.75 else 0) +
                                  if bool_decide (b = false) then 0.25 else 0))%R.
    2: { intros []; rewrite /= {1}/pmf /=;  lra. }
    erewrite SeriesC_plus; [|eapply ex_seriesC_singleton.. ].
    rewrite 2!SeriesC_singleton /=. lra. }
  rewrite Hflip Hflip_ors in Hctx.
  lra.
Qed.
