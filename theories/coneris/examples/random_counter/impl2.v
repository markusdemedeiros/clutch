From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris hocap random_counter.
From clutch Require Import uniform_list.

Set Default Proof Using "Type*".

Local Definition expander (l:list nat):=
  l ≫= (λ x, [Nat.div2 x; Nat.b2n (Nat.odd x)]).

Class hocap_tapesGS' (Σ : gFunctors) := Hocap_tapesGS' {
  hocap_tapesGS_inG' :: ghost_mapG Σ loc (bool* list nat)
                                         }.
Definition hocap_tapesΣ' := ghost_mapΣ loc (bool *list nat).

Notation "α ◯↪N ( b , ns ) @ γ":= (α ↪[ γ ] (b, ns))%I
                                    (at level 20) : bi_scope.

Notation "● m @ γ" := (ghost_map_auth γ 1 m) (at level 20) : bi_scope.

Section tapes_lemmas.
  Context `{!conerisGS Σ, !hocap_tapesGS' Σ}.

  Lemma hocap_tapes_alloc' m:
    ⊢ |==>∃ γ, (● m @ γ) ∗ [∗ map] k↦v ∈ m, (k ◯↪N (v.1, v.2) @ γ).
  Proof.
    iMod ghost_map_alloc as (γ) "[??]".
    iFrame. iModIntro.
    iApply big_sepM_mono; last done.
    by iIntros (?[??]).
  Qed.

  Lemma hocap_tapes_agree' m b γ k ns:
    (● m @ γ) -∗ (k ◯↪N (b, ns) @ γ) -∗ ⌜ m!!k = Some (b, ns) ⌝.
  Proof.
    iIntros "H1 H2".
    by iCombine "H1 H2" gives "%".
  Qed.

  Lemma hocap_tapes_new' γ m k ns b:
    m!!k=None -> ⊢ (● m @ γ) ==∗ (● (<[k:=(b, ns)]>m) @ γ) ∗ (k ◯↪N (b, ns) @ γ).
  Proof.
    iIntros (Hlookup) "H".
    by iApply ghost_map_insert.
  Qed.

  Lemma hocap_tapes_presample' b γ m k ns n:
    (● m @ γ) -∗ (k ◯↪N (b, ns) @ γ) ==∗ (● (<[k:=(b, ns++[n])]>m) @ γ) ∗ (k ◯↪N (b, ns++[n]) @ γ).
  Proof.
    iIntros "H1 H2".
    iApply (ghost_map_update with "[$][$]").
  Qed.

  Lemma hocap_tapes_pop1' γ m k ns:
    (● m @ γ) -∗ (k ◯↪N (true, ns) @ γ) ==∗ (● (<[k:=(false, ns)]>m) @ γ) ∗ (k ◯↪N (false, ns) @ γ).
  Proof.
    iIntros "H1 H2".
    iApply (ghost_map_update with "[$][$]").
  Qed.
  
  Lemma hocap_tapes_pop2' γ m k ns n:
    (● m @ γ) -∗ (k ◯↪N (false, n::ns) @ γ) ==∗ (● (<[k:=(true, ns)]>m) @ γ) ∗ (k ◯↪N (true, ns) @ γ).
  Proof.
    iIntros "H1 H2".
    iApply (ghost_map_update with "[$][$]").
  Qed.

  Lemma hocap_tapes_notin' α N ns m (f:(bool*list nat)-> nat) g:
    α ↪N (N; ns) -∗ ([∗ map] α0↦t ∈ m, α0 ↪N (f t; g t)) -∗ ⌜m!!α=None ⌝.
  Proof.
    destruct (m!!α) eqn:Heqn; last by iIntros.
    iIntros "Hα Hmap".
    iDestruct (big_sepM_lookup with "[$]") as "?"; first done.
    iExFalso.
    iApply (tapeN_tapeN_contradict with "[$][$]").
  Qed.

End tapes_lemmas.

Section impl2.

  Definition new_counter2 : val:= λ: "_", ref #0.
  Definition incr_counter2 : val := λ: "l", let: "n" := rand #1 in
                                            let: "n'" := rand #1 in
                                            let: "x" := #2 * "n" + "n'" in
                                            (FAA "l" "x", "x").
  Definition allocate_tape2 : val := λ: "_", AllocTape #1.
  Definition incr_counter_tape2 :val := λ: "l" "α", let: "n" := rand("α") #1 in
                                                    let: "n'" := rand("α") #1 in
                                                    let: "x" := #2 * "n" + "n'" in
                                                    (FAA "l" "x", "x").
  Definition read_counter2 : val := λ: "l", !"l".
  Class counterG2 Σ := CounterG2 { counterG2_error::hocap_errorGS Σ;
                                   counterG2_tapes:: hocap_tapesGS' Σ;
                                   counterG2_frac_authR:: inG Σ (frac_authR natR) }.
  
  Context `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS' Σ, !inG Σ (frac_authR natR)}.
  
  
  Definition counter_inv_pred2 (c:val) γ1 γ2 γ3:=
    (∃ (ε:R) (m:gmap loc (bool*list nat)) (l:loc) (z:nat),
        ↯ ε ∗ ●↯ ε @ γ1 ∗
        ([∗ map] α ↦ t ∈ m, α ↪N ( 1%nat ; if t.1:bool then expander t.2 else drop 1%nat (expander t.2)) )
        ∗ ●m@γ2 ∗  
        ⌜c=#l⌝ ∗ l ↦ #z ∗ own γ3 (●F z)
    )%I.

  Lemma new_counter_spec2 E ε N:
    {{{ ↯ ε }}}
      new_counter2 #() @ E
      {{{ (c:val), RET c;
          ∃ γ1 γ2 γ3, inv N (counter_inv_pred2 c γ1 γ2 γ3) ∗
                      ◯↯ε @ γ1 ∗ own γ3 (◯F 0%nat)
      }}}.
  Proof.
    rewrite /new_counter2.
    iIntros (Φ) "Hε HΦ".
    wp_pures.
    wp_alloc l as "Hl".
    iDestruct (ec_valid with "[$]") as "%".
    unshelve iMod (hocap_error_alloc (mknonnegreal ε _)) as "[%γ1 [H1 H2]]".
    { lra. }
    simpl.
    iMod (hocap_tapes_alloc' (∅:gmap _ _)) as "[%γ2 [H3 H4]]".
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as "[%γ3[H5 H6]]".
    { by apply frac_auth_valid. }
    replace (#0) with (#0%nat) by done.
    iMod (inv_alloc N _ (counter_inv_pred2 (#l) γ1 γ2 γ3) with "[$Hε $Hl $H1 $H3 $H5]") as "#Hinv".
    { iSplit; last done. by iApply big_sepM_empty. }
    iApply "HΦ".
    iExists _, _, _. by iFrame.
  Qed.


  (** This lemma is not possible as only one view shift*)
  Lemma incr_counter_spec2 E N c γ1 γ2 γ3 (ε2:R -> nat -> R) (P: iProp Σ) (T: nat -> iProp Σ) (Q: nat->nat->iProp Σ):
    ↑N ⊆ E->
    (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R->
    (∀ (ε:R), 0<=ε -> ((ε2 ε 0%nat) + (ε2 ε 1%nat)+ (ε2 ε 2%nat)+ (ε2 ε 3%nat))/4 <= ε)%R →
    {{{ inv N (counter_inv_pred2 c γ1 γ2 γ3) ∗
        □(∀ (ε:R) (n : nat), P ∗ ●↯ ε @ γ1 ={E∖↑N}=∗ (⌜(1<=ε2 ε n)%R⌝∨●↯ (ε2 ε n) @ γ1 ∗ T n) ) ∗
        □ (∀ (n z:nat), T n ∗ own γ3 (●F z) ={E∖↑N}=∗
                          own γ3 (●F(z+n)%nat)∗ Q z n) ∗
        P
    }}}
      incr_counter2 c @ E
      {{{ (n:nat) (z:nat), RET (#z, #n); Q z n }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP) HΦ".
    rewrite /incr_counter2.
    wp_pures.
    wp_bind (rand _)%E.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    (** cant do two view shifts! *)
  Abort.

  Lemma allocate_tape_spec2 N E c γ1 γ2 γ3:
    ↑N ⊆ E->
    {{{ inv N (counter_inv_pred2 c γ1 γ2 γ3) }}}
      allocate_tape2 #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ α ◯↪N (true,  []) @ γ2
      }}}.
  Proof.
    iIntros (Hsubset Φ) "#Hinv HΦ".
    rewrite /allocate_tape2.
    wp_pures.
    wp_alloctape α as "Hα".
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_notin' with "[$][$]") as "%".
    iMod (hocap_tapes_new' _ _ _ _ true with "[$]") as "[H4 H7]"; first done.
    replace ([]) with (expander []) by done.
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Hα]") as "_".
    { iNext. iSplitL; last done.
      rewrite big_sepM_insert; [iFrame|done].
    }
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma incr_counter_tape_spec_some2 N E c γ1 γ2 γ3 (P: iProp Σ) (Q:nat->iProp Σ) (α:loc) (n:nat) ns:
    ↑N⊆E ->
    {{{ inv N (counter_inv_pred2 c γ1 γ2 γ3) ∗
        □ (∀ (z:nat), P ∗ own γ3 (●F z) ={E∖↑N}=∗
                          own γ3 (●F(z+n)%nat)∗ Q z) ∗
        P ∗ α ◯↪N (true, n::ns) @ γ2
    }}}
      incr_counter_tape2 c #lbl:α @ E
      {{{ (z:nat), RET (#z, #n); Q z ∗ α ◯↪N (true, ns) @ γ2}}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & #Hvs & HP & Hα) HΦ".
    rewrite /incr_counter_tape2.
    wp_pures.
    wp_bind (rand(_) _)%E.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_agree' with "[$][$]") as "%".
    erewrite <-(insert_delete m) at 1; last done.
    rewrite big_sepM_insert; last apply lookup_delete.
    simpl.
    iDestruct "H3" as "[Htape H3]".
    wp_apply (wp_rand_tape with "[$]").
    iIntros "[Htape %H1]".
    iMod (hocap_tapes_pop1' with "[$][$]") as "[H4 Hα]".
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Htape]") as "_".
    { iSplitL; last done.
      erewrite <-(insert_delete m) at 2; last done.
      iNext.
      rewrite insert_insert.
      rewrite big_sepM_insert; last apply lookup_delete. iFrame.
    }
    iModIntro.
    wp_pures.
    clear -Hsubset H1.
    wp_bind (rand(_) _)%E.
    iInv N as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    iDestruct (hocap_tapes_agree' with "[$][$]") as "%".
    erewrite <-(insert_delete m) at 1; last done.
    rewrite big_sepM_insert; last apply lookup_delete.
    simpl.
    iDestruct "H3" as "[Htape H3]".
    wp_apply (wp_rand_tape with "[$]").
    iIntros "[Htape %H2]".
    iMod (hocap_tapes_pop2' with "[$][$]") as "[H4 Hα]".
    iMod ("Hclose" with "[$H1 $H2 H3 $H4 $H5 $H6 Htape]") as "_".
    { iSplitL; last done.
      erewrite <-(insert_delete m) at 2; last done.
      iNext.
      rewrite insert_insert.
      rewrite big_sepM_insert; last apply lookup_delete. iFrame.
    }
    iModIntro.
    wp_pures.
    clear -Hsubset H1 H2.
    wp_bind (FAA _ _).
    iInv N as ">(%ε & %m & % & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_faa.
    iMod ("Hvs" with "[$]") as "[H6 HQ]".
    replace (#(z+n)) with (#(z+n)%nat); last first.
    { by rewrite Nat2Z.inj_add. }
    replace 2%Z with (Z.of_nat 2%nat) by done.
    rewrite -Nat2Z.inj_mul -Nat2Z.inj_add -Nat.div2_odd -Nat2Z.inj_add. 
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 H5 $H6]") as "_"; first by iFrame.
    iModIntro. wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma counter_presample_spec2 NS  E ns α
     (ε2 : R -> nat -> R)
    (P : iProp Σ) T γ1 γ2 γ3 c:
    ↑NS ⊆ E ->
    (∀ ε n, 0<= ε -> 0<=ε2 ε n)%R ->
    (∀ (ε:R), 0<= ε ->SeriesC (λ n, if (bool_decide (n≤3%nat)) then 1 / (S 3%nat) * ε2 ε n else 0%R)%R <= ε)%R->
    inv NS (counter_inv_pred2 c γ1 γ2 γ3) -∗
    (□∀ (ε:R) n, (P ∗ ●↯ ε@ γ1) ={E∖↑NS}=∗
        (⌜(1<=ε2 ε n)%R⌝ ∨(●↯ (ε2 ε n) @ γ1 ∗ T (n))))
        -∗
    P -∗ α ◯↪N (true, ns) @ γ2 -∗
        wp_update E (∃ n, T (n) ∗ α◯↪N (true, ns++[n]) @ γ2).
  Proof.
    iIntros (Hsubset Hpos Hineq) "#Hinv #Hvs HP Hfrag".
    iApply wp_update_state_step_coupl.
    iIntros (σ ε) "((Hheap&Htapes)&Hε)".
    iMod (inv_acc with "Hinv") as "[>(% & % & % & % & H1 & H2 & H3 & H4 & -> & H5 & H6) Hclose]"; [done|].
    iDestruct (hocap_tapes_agree' with "[$][$]") as "%".
    erewrite <-(insert_delete m) at 1; last done.
    rewrite big_sepM_insert; last apply lookup_delete.
    simpl.
    iDestruct "H3" as "[Htape H3]".
    iDestruct (tapeN_lookup with "[$][$]") as "(%&%&%H1)".
    iDestruct (ec_supply_bound with "[$][$]") as "%".
    iMod (ec_supply_decrease with "[$][$]") as (ε1' ε_rem -> Hε1') "Hε_supply". subst.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iApply (state_step_coupl_iterM_state_adv_comp_con_prob_lang 2%nat); first done.
    pose (f (l:list (fin 2)) := (match l with
                                       | x::[x'] => 2*fin_to_nat x + fin_to_nat x'
                                       | _ => 0
                                       end)).
    unshelve iExists
      (λ l, mknonnegreal (ε2 ε1' (f l) ) _).
    { apply Hpos; simpl. auto. }
    simpl.
    iSplit.
    { iPureIntro.
      etrans; last apply Hineq; last auto.
      pose (k:=(λ n, 1 / ((1 + 1) * ((1 + 1) * 1)) * ε2 ε1' (f n))%R).
      erewrite (SeriesC_ext _ (λ x, if bool_decide (x ∈ enum_uniform_list 1%nat 2%nat)
                                    then k x else 0%R))%R; last first.
      - intros. case_bool_decide as K.
        + rewrite elem_of_enum_uniform_list in K. by rewrite K /k.
        + rewrite elem_of_enum_uniform_list in K.
          case_match eqn:K'; [by rewrite Nat.eqb_eq in K'|done].
      - rewrite SeriesC_list; last apply NoDup_enum_uniform_list.
        rewrite /k /=. rewrite SeriesC_nat_bounded'/=. lra.
    }
    iIntros (sample ?).
    destruct (Rlt_decision (nonneg ε_rem + (ε2 ε1' (f sample)))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply state_step_coupl_ret_err_ge_1.
      simpl. simpl in *. lra.
    }
    iApply state_step_coupl_ret.
    unshelve iMod (ec_supply_increase _ (mknonnegreal (ε2 ε1' (f sample)) _) with "Hε_supply") as "[Hε_supply Hε]".
    { apply Hpos. apply cond_nonneg. }
    { simpl. done. }
    assert (Nat.div2 (f sample)<2)%nat as K1.
    { rewrite Nat.div2_div. apply Nat.Div0.div_lt_upper_bound. rewrite /f.
      simpl. repeat case_match; try lia. pose proof fin_to_nat_lt t. pose proof fin_to_nat_lt t0. lia.
    }
    rewrite -H1.
    iMod (tapeN_update_append _ _ _ _ (nat_to_fin K1) with "[$][$]") as "[Htapes Htape]".
    assert (Nat.b2n (Nat.odd (f sample))<2)%nat as K2.
    { edestruct (Nat.odd _); simpl; lia.  }
    rewrite -(list_fmap_singleton (fin_to_nat)) -fmap_app.
    iMod (tapeN_update_append _ _ _ _ (nat_to_fin K2) with "[$][$]") as "[Htapes Htape]".
    iMod (hocap_tapes_presample' _ _ _ _ _ (f sample) with "[$][$]") as "[H4 Hfrag]".
    iMod "Hclose'" as "_".
    iMod ("Hvs" with "[$]") as "[%|[H2 HT]]".
    { iExFalso. iApply (ec_contradict with "[$]"). exact. }
    rewrite insert_insert.
    rewrite fmap_app -!app_assoc /=.
    assert (([nat_to_fin K1;nat_to_fin K2]) = sample) as K.
    { destruct sample as [|x xs]; first done.
      destruct xs as [|x' xs]; first done.
      destruct xs as [|]; last done.
      pose proof fin_to_nat_lt x. pose proof fin_to_nat_lt x'.
      repeat f_equal; apply fin_to_nat_inj; rewrite fin_to_nat_to_fin. 
      - rewrite /f. rewrite Nat.div2_div.
        rewrite Nat.mul_comm Nat.div_add_l; last lia. rewrite Nat.div_small; lia.
      - rewrite /f. rewrite Nat.add_comm Nat.odd_add_even.
        + destruct (fin_to_nat x') as [|[|]]; simpl; lia.
        + by econstructor. 
    }
    iMod ("Hclose" with "[$Hε $H2 Htape H3 $H4 $H5 $H6]") as "_".
    { iNext. iSplit; last done.
      rewrite big_sepM_insert_delete; iFrame.
      simpl. rewrite !fin_to_nat_to_fin.
      rewrite /expander bind_app -/(expander ns). simpl. by rewrite H1. 
    }
    iApply fupd_mask_intro_subseteq; first set_solver.
    rewrite K.
    iFrame. 
  Qed.

  Lemma read_counter_spec2 N E c γ1 γ2 γ3 P Q:
    ↑N ⊆ E ->
    {{{  inv N (counter_inv_pred2 c γ1 γ2 γ3) ∗
        □ (∀ (z:nat), P ∗ own γ3 (●F z) ={E∖↑N}=∗
                    own γ3 (●F z)∗ Q z)
         ∗ P
    }}}
      read_counter2 c @ E
      {{{ (n':nat), RET #n'; Q n'
      }}}.
  Proof.
    iIntros (Hsubset Φ) "(#Hinv & #Hvs & HP) HΦ".
    rewrite /read_counter2.
    wp_pure.
    iInv N as ">(%ε & %m & %l & %z & H1 & H2 & H3 & H4 & -> & H5 & H6)" "Hclose".
    wp_load.
    iMod ("Hvs" with "[$]") as "[H6 HQ]".
    iMod ("Hclose" with "[$H1 $H2 $H3 $H4 $H5 $H6]"); first done.
    iApply ("HΦ" with "[$]").
  Qed.
  
End impl2.

Program Definition random_counter2 `{!conerisGS Σ}: random_counter :=
  {| new_counter := new_counter2;
    allocate_tape:= allocate_tape2;
    incr_counter_tape := incr_counter_tape2;
    read_counter:=read_counter2;
    counterG := counterG2;
    error_name := gname;
    tape_name := gname;
    counter_name :=gname;
    is_counter _ N c γ1 γ2 γ3 := inv N (counter_inv_pred2 c γ1 γ2 γ3);
    counter_error_auth _ γ x := ●↯ x @ γ;
    counter_error_frag _ γ x := ◯↯ x @ γ;
    counter_tapes_auth _ γ m := (●((λ ns, (true, ns))<$>m)@γ)%I;
    counter_tapes_frag _ γ α ns := (α◯↪N (true, ns) @ γ)%I;
    counter_content_auth _ γ z := own γ (●F z);
    counter_content_frag _ γ f z := own γ (◯F{f} z);
    new_counter_spec _ := new_counter_spec2;
    allocate_tape_spec _ :=allocate_tape_spec2;
    incr_counter_tape_spec_some _ :=incr_counter_tape_spec_some2;
    counter_presample_spec _ :=counter_presample_spec2;
    read_counter_spec _ :=read_counter_spec2
  |}.
Next Obligation.
  simpl.
  iIntros (??????) "(%&<-&H1)(%&<-&H2)".
  iCombine "H1 H2" gives "%H". by rewrite excl_auth.excl_auth_auth_op_valid in H.
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "(%&<-&H1)(%&<-&H2)".
  iCombine "H1 H2" gives "%H". by rewrite excl_auth.excl_auth_frag_op_valid in H.
Qed.
Next Obligation.
  simpl.
  iIntros (?????) "H".
  iApply (hocap_error_auth_pos with "[$]").
Qed.
Next Obligation.
  simpl.
  iIntros (?????) "H".
  iApply (hocap_error_frag_pos with "[$]").
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "H1 H2".
  iApply (hocap_error_agree with "[$][$]").
Qed.
Next Obligation.
  simpl. iIntros (???????) "??".
  iApply (hocap_error_update with "[$][$]").
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "H1 H2".
  by iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "[%H _]".
Qed.
Next Obligation.
  simpl.
  iIntros (???????) "H1 H2".
  iDestruct (ghost_map_elem_frac_ne with "[$][$]") as "%"; last done.
  rewrite dfrac_op_own dfrac_valid_own. by intro.
Qed.
Next Obligation.
  simpl.
  iIntros.
  iDestruct (hocap_tapes_agree' with "[$][$]") as "%H".
  rewrite lookup_fmap_Some in H. destruct H as (?&?&?).
  by simplify_eq.
Qed.
Next Obligation.
  iIntros.
  iDestruct (hocap_tapes_presample' with "[$][$]") as ">[? $]".
  by rewrite fmap_insert.
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "H1 H2".
  iCombine "H1 H2" gives "%H". by rewrite auth_auth_op_valid in H.
Qed.
Next Obligation.
  simpl. iIntros (???? z z' ?) "H1 H2".
  iCombine "H1 H2" gives "%H".
  apply frac_auth_included_total in H. iPureIntro.
  by apply nat_included.
Qed.
Next Obligation.
  simpl.
  iIntros (????????).
  rewrite frac_auth_frag_op. by rewrite own_op.
Qed.
Next Obligation.
  simpl. iIntros (??????) "H1 H2".
  iCombine "H1 H2" gives "%H".
  iPureIntro.
  by apply frac_auth_agree_L in H.
Qed.
Next Obligation.
  simpl. iIntros (????????) "H1 H2".
  iMod (own_update_2 _ _ _ (_ ⋅ _) with "[$][$]") as "[$$]"; last done.
  apply frac_auth_update.
  apply nat_local_update. lia.
Qed.
  
