From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable.
From self.prelude Require Export base Coquelicot_ext Reals_ext.
From self.prob Require Export countable_sum double distribution.

Arguments MkDistr {_ _ _}.
Arguments pmf {_ _ _ _}.
Arguments pmf_pos {_ _ _}.
Arguments pmf_ex_seriesC {_ _ _}.
Arguments pmf_SeriesC {_ _ _}.

#[global] Hint Resolve pmf_pos pmf_ex_seriesC pmf_SeriesC : core.
Notation Decidable P := (∀ x, Decision (P x)).

Open Scope R.

Section couplings.
  Context `{Countable A, Countable B, Countable A', Countable B'}.
  Context (μ1 : distr A) (μ2 : distr B) (R : A -> B -> Prop) (S : A' → B' → Prop). 

  Definition lmarg (μ : distr (A * B)) : distr A :=
    dmap (fun p =>  fst p) μ.

  Definition rmarg (μ : distr (A * B)) : distr B :=
    dmap (fun p =>  snd p) μ.

  Lemma lmarg_pmf (μ : distr (A * B)) :
    forall (a : A), (lmarg μ) a = SeriesC (λ (b : B), μ (a, b)).
  Proof.
    intro a.
    simpl.
    rewrite /dbind_pmf.
    rewrite (SeriesC_double_prod_rl (λ a0 : A * B, μ a0 * dret a0.1 a)).
    apply SeriesC_ext; intro b.
    rewrite /= /dret_pmf /=.
    assert (SeriesC (λ a0 : A, μ (a0, b) * (if bool_decide (a = a0) then 1 else 0)) =
           SeriesC (λ a0 : A, (if bool_decide (a = a0) then μ (a, b) else 0))).
    { apply SeriesC_ext; intro a0.
      case_bool_decide; try lra.
      rewrite H3; lra.
    }
    rewrite H3 SeriesC_singleton'; auto.
  Qed.


  Lemma rmarg_pmf (μ : distr (A * B)) :
    forall (b : B), (rmarg μ) b = SeriesC (λ (a : A), μ (a, b)).
  Proof.
    intro b.
    simpl.
    rewrite /dbind_pmf.
    rewrite (SeriesC_double_prod_lr (λ a : A * B, μ a * dret a.2 b)).
    apply SeriesC_ext; intro a.
    rewrite /= /dret_pmf /=.
    assert (SeriesC (λ b0 : B, μ (a, b0) * (if bool_decide (b = b0) then 1 else 0)) =
              SeriesC (λ b0 : B, if bool_decide (b = b0) then μ (a, b) else 0)).
    { apply SeriesC_ext; intro b0.
      case_bool_decide; try lra.
      rewrite H3; lra.
    }
    rewrite H3 SeriesC_singleton'; auto.
  Qed.

(* There are multiple options we could try here. We have the usual
   existential definition, but we can also define it universally via
   Strassens theorem,

  Definition coupl μ1 μ2 R :=
    forall (P1 : A -> Bool) (P2 : B -> Bool),
           (forall a b, P1(a)=true /\ R(A,B) -> P2(a)= true),
                   prob μ1 P1 <= prob μ2 P2
 *)


  Definition isCoupl (μ : distr (A * B)) : Prop :=
    lmarg μ = μ1 /\ rmarg μ = μ2.

  Definition coupl :=
    ∃ (μ : distr (A * B)), isCoupl μ.

  Definition isRcoupl (μ : distr (A * B)) : Prop :=
    isCoupl μ ∧ (forall (p : A * B), (μ p > 0) -> R (fst p) (snd p)).

  Definition Rcoupl :=
    ∃ (μ : distr (A * B)), isRcoupl μ.


  Lemma isRcoupl_isCoupl μ : isRcoupl μ -> isCoupl μ.
  Proof.
    intro C; destruct C; auto.
  Qed.

  Lemma isCoupl_mass_l μ : isCoupl μ -> SeriesC μ = SeriesC μ1.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite <- Hμl.
    rewrite /lmarg.
    rewrite <- dmap_mass.
    auto.
  Qed.

  Lemma isCoupl_mass_r μ : isCoupl μ -> SeriesC μ = SeriesC μ2.
  Proof.
    intro Hμ.
    destruct Hμ as (Hμl & Hμr).
    rewrite <- Hμr.
    rewrite /rmarg.
    rewrite <- dmap_mass.
    auto.
  Qed.

  Lemma isCoupl_mass_eq μ : isCoupl μ -> SeriesC μ1 = SeriesC μ2.
  Proof.
    intro Hμ.
    rewrite <- (isCoupl_mass_l μ); auto.
    rewrite <- (isCoupl_mass_r μ); auto.
  Qed.



End couplings.

Section couplings_theory.
  Context `{Countable A, Countable B, Countable A', Countable B'}.

  Proposition is_coupl_ret :
    forall (a : A) (b : B), isCoupl (dret a) (dret b) (dret (a, b)).
  Proof.
    intros a b.
    split.
    - rewrite /lmarg.
      rewrite dmap_dret.
      auto.
    - rewrite /rmarg.
      rewrite dmap_dret.
      auto.
   Qed.
    
  Proposition coupl_ret :
    forall (a : A) (b : B), coupl (dret a) (dret b).
  Proof.
    intros a b.
    exists (dret (a, b)).
    apply is_coupl_ret.
  Qed.

  Proposition isRcoupl_ret : 
    forall (a : A) (b : B) (R : A → B → Prop), R a b -> isRcoupl (dret a) (dret b) R (dret (a, b)).
  Proof.
    intros a b R HR.
    split.
    + apply is_coupl_ret.
    + intro p.
      simpl.
      rewrite /dret_pmf.
      case_eq (bool_decide (p = (a, b))); intros Heq Hineq; try lra.
      pose proof (bool_decide_eq_true_1 (p = (a, b))) Heq as Heq'.
      rewrite Heq'.
      auto.
  Qed.

  Proposition Rcoupl_ret :
    forall (a : A) (b : B) (R : A → B → Prop) , R a b -> Rcoupl (dret a) (dret b) R.
  Proof.
    intros a b R HR.
    exists (dret (a, b)).
    apply isRcoupl_ret.
    auto.
  Qed.

  Proposition coupl_sym (μ1 : distr A) (μ2 : distr B) :
    coupl μ1 μ2 -> coupl μ2 μ1.
  Proof.
    intros (μ & HμL & HμR).
    exists (dmap (λ '(a, b), (b, a)) μ); split; apply distr_ext.
    + intro b.
      rewrite <- HμR.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro a.
      simpl.
      rewrite /dbind_pmf /=.
      rewrite /dret_pmf /=.
      assert (forall a0 : A * B, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                                     = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; try lra.
        + rewrite H4; lra.
        + inversion H3. rewrite H6 H7 in H4; done.
        + inversion H4. rewrite H6 H7 in H3; done.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
    + intro a.
      rewrite <- HμL.
      rewrite lmarg_pmf rmarg_pmf.
      apply SeriesC_ext; intro b.
      simpl.
      rewrite /dbind_pmf /=.
      rewrite /dret_pmf /=.
      assert (forall a0 : A * B, μ a0 * (if bool_decide ((b, a) = (let '(a1, b0) := a0 in (b0, a1))) then 1 else 0)
                                     = if bool_decide ((a, b) = a0 ) then μ (a, b) else 0) as Heq1.
      { intros (a' & b').
        case_bool_decide; case_bool_decide; try lra.
        + rewrite H4; lra.
        + inversion H3. rewrite H6 H7 in H4; done.
        + inversion H4. rewrite H6 H7 in H3; done.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      apply SeriesC_singleton'.
  Qed. 




  Proposition coupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B),
      (∀ a b, coupl (f a) (g b)) → coupl μ1 μ2 → coupl (dbind f μ1) (dbind g μ2).
  Proof.
    intros f g μ1 μ2 Hfg (μ & Hμ).
    rewrite /coupl in Hfg.
    assert (∀ (p : A * B), ∃ μ : distr (A' * B'), isCoupl (f p.1) (g p.2) μ) as Hfg'; auto.
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as Ch.

    rewrite /coupl.
    destruct Ch as (Ch & HCh).
    exists (dbind Ch μ); split.
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      assert (∀ b, SeriesC (λ a : B', μ b * Ch b (a', a)) = μ b * SeriesC (λ a : B', Ch b (a', a))) as Heq1.
      {
        intro b; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ b' : B', Ch p (a', b')) = μ p * f p.1 a') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChL.
        rewrite lmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_lr.
      assert (∀ a : A, SeriesC (λ b : B, μ (a, b) * f (a, b).1 a')
               = SeriesC (λ b : B, μ (a, b) ) * f a a') as Heq3.
      {
        intro a; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ a, SeriesC (λ b : B, μ (a, b)) = μ1 a) as Heq4.
      {
        intro a.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite <- Hμ1;
        rewrite lmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro a.
      rewrite (Heq4 a); auto.
(* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf.
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      assert (∀ p, SeriesC (λ a : A', μ p * Ch p (a, b')) = μ p * SeriesC (λ a : A', Ch p (a, b'))) as Heq1.
      {
        intro p; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ a' : A', Ch p (a', b')) = μ p * g p.2 b') as Heq2.
      { intros (a & b).
        specialize (HCh (a, b)) as (HChL & HChR).
        rewrite <- HChR.
        rewrite rmarg_pmf.
        auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_rl.
      assert (∀ b : B, SeriesC (λ a : A, μ (a, b) * g (a, b).2 b')
               = SeriesC (λ a : A, μ (a, b) ) * g b b') as Heq3.
      {
        intro b; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ b, SeriesC (λ a : A, μ (a, b)) = μ2 b) as Heq4.
      {
        intro b.
        destruct Hμ as (Hμ1 & Hμ2).
        rewrite <- Hμ2;
        rewrite rmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro b.
      rewrite (Heq4 b); auto.
  Qed.


  Proposition Rcoupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop),
      (∀ a b, R a b → Rcoupl (f a) (g b) S) → Rcoupl μ1 μ2 R → Rcoupl (dbind f μ1) (dbind g μ2) S.
  Proof.
    intros f g μ1 μ2 R S Hfg (μ & HμC & HμS).
    rewrite /Rcoupl /isRcoupl in Hfg.
    assert (∀ (p : A * B), ∃ μ' : distr (A' * B'), R p.1 p.2 → (isCoupl (f p.1) (g p.2) μ' ∧
                                                     (∀ q : A' * B', μ' q > 0 → S q.1 q.2))) as Hfg'; auto.
    {
      intro p.
      specialize (HμS p).
      specialize (Hfg p.1 p.2).
      pose proof (ExcludedMiddle (R p.1 p.2)) as H3; destruct H3 as [HR | HnR].
      + specialize (Hfg HR).
        destruct Hfg as (μ' & Hμ'1 & Hμ'2).
        exists μ'; auto.
      + exists dzero; intro ; done.
    }
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as (Ch & HCh).
    rewrite /Rcoupl /isRcoupl.
    exists (dbind Ch μ); split; try split.
    + apply distr_ext; intro a'.
      rewrite lmarg_pmf.
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(b, a), μ a * Ch a (a', b))).
      assert (∀ b, SeriesC (λ a : B', μ b * Ch b (a', a)) = μ b * SeriesC (λ a : B', Ch b (a', a))) as Heq1.
      {
        intro b; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ b' : B', Ch p (a', b')) = μ p * f p.1 a') as Heq2.
      { intros (a & b).
        pose proof (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        + pose proof (pmf_pos μ (a, b)); lra.
        + rewrite Heqz; lra.
        + specialize (HCh (a, b) (HμS (a, b) Hgt)) as ((HChL & HChR) & HChS).
          rewrite <- HChL.
          rewrite lmarg_pmf.
          auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_lr.
      assert (∀ a : A, SeriesC (λ b : B, μ (a, b) * f (a, b).1 a')
               = SeriesC (λ b : B, μ (a, b) ) * f a a') as Heq3.
      {
        intro a; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ a, SeriesC (λ b : B, μ (a, b)) = μ1 a) as Heq4.
      {
        intro a.
        destruct HμC as (Hμ1 & Hμ2).
        rewrite <- Hμ1;
        rewrite lmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro a.
      rewrite (Heq4 a); auto.
(* The second half is esentially the same as the first, can it be proven somehow by symmetry? *)
    + apply distr_ext; intro b'.
      rewrite rmarg_pmf.
      simpl.
      unfold dbind_pmf.
      rewrite (SeriesC_double_swap (λ '(a, a0), μ a0 * Ch a0 (a, b'))).
      assert (∀ p, SeriesC (λ a : A', μ p * Ch p (a, b')) = μ p * SeriesC (λ a : A', Ch p (a, b'))) as Heq1.
      {
        intro p; apply SeriesC_scal_l.
      }
      rewrite (SeriesC_ext _ _ Heq1).
      assert (∀ p , μ p * SeriesC (λ a' : A', Ch p (a', b')) = μ p * g p.2 b') as Heq2.
      { intros (a & b).
        pose proof (Rtotal_order (μ (a, b)) 0) as [Hlt | [Heqz | Hgt]].
        + pose proof (pmf_pos μ (a, b)); lra.
        + rewrite Heqz; lra.
        + specialize (HCh (a, b) (HμS (a, b) Hgt)) as ((HChL & HChR) & HChS).
          rewrite <- HChR.
          rewrite rmarg_pmf.
          auto.
      }
      rewrite (SeriesC_ext _ _ Heq2).
      rewrite SeriesC_double_prod_rl.
      assert (∀ b : B, SeriesC (λ a : A, μ (a, b) * g (a, b).2 b')
               = SeriesC (λ a : A, μ (a, b) ) * g b b') as Heq3.
      {
        intro b; simpl; apply SeriesC_scal_r.
      }
      rewrite (SeriesC_ext _ _ Heq3).
      assert (∀ b, SeriesC (λ a : A, μ (a, b)) = μ2 b) as Heq4.
      {
        intro b.
        destruct HμC as (Hμ1 & Hμ2).
        rewrite <- Hμ2;
        rewrite rmarg_pmf; auto.
      }
      apply SeriesC_ext.
      intro b.
      rewrite (Heq4 b); auto.
    + intro p.
      destruct p as (a' & b').
      intro H3; simpl.
      pose proof (dbind_pos_support Ch μ (a', b')) as (H4 & H5).
      specialize (H4 H3) as ((a0, b0) & H7 & H8).
      specialize (HμS (a0, b0) H8).
      specialize (HCh (a0, b0) HμS).
      destruct HCh as (HCh1 & HCh2).
      specialize (HCh2 (a', b') H7).
      done.
  Qed.



(* Old proof attempts below, can probably be deleted

  Proposition Rcoupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (μ : distr (A * B))
      (Ch : A * B → distr (A' * B')),
          (∀ a b, isCoupl (f a) (g b) (Ch (a , b)) ) → isCoupl μ1 μ2 μ →
        isCoupl (dbind f μ1) (dbind g μ2) (dbind Ch μ).
  Proof.
    intros f g μ1 μ2 μ Ch HCh Hμ.
    rewrite /isCoupl.
    rewrite /isCoupl in HCh.
    pose proof (Choice A B (λ a b, lmarg (Ch (a, b)) = f a ∧ rmarg (Ch (a, b)) = g b)).


    intros f g μ1 μ2 μ Ch HCh Hμ; split.
    + (* Here we want to instantiate HCh, but A, B may be empty *)
      apply distr_ext.
      pose proof (ExcludedMiddle (∀ b, μ2 b = 0)) as ExM; destruct ExM as [ExM1 | ExM2].
      ++ assert (μ2 = dzero) as Hμ2Z.
         {apply distr_ext; auto.}
         assert (μ = dzero) as HμZ.
         {
           pose proof (isCoupl_mass_r _ _ _ Hμ).
           rewrite Hμ2Z in H3.
           rewrite /= /dzero (SeriesC_0 (λ _ : B, 0)) in H3; auto.
           apply SeriesC_zero_dzero; auto.
         }
         assert (SeriesC μ1 = 0) as HμZ'.
         {
           rewrite (isCoupl_mass_eq μ1 μ2 μ); auto.
         }

          (∀ p, μ p = 0).
         {
           destruct Hμ as (Hμm1 & Hμm2).
           rewrite /rmarg in Hμm2.
           rewrite /dmap in Hμm2.
           rewrite <- Hμm2 in ExM1.
           intro p.
           destruct p as (a & b).
           pose proof (ExM1 b) as ExM1b.
           apply (distr_ext (μ ≫= (λ a : A * B, dret a.2)) μ2) in Hμm2.
           rewrite /dbind in Hμm2.


         }


  Proposition coupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B),
      (∀ a b, coupl (f a) (g b)) → coupl μ1 μ2 → coupl (dbind f μ1) (dbind g μ2).
  Proof.
    intros f g μ1 μ2 Hfg (μ & Hμ).
    rewrite /coupl in Hfg.
    assert (∀ (p : A * B), ∃ μ : distr (A' * B'), isCoupl (f p.1) (g p.2) μ) as Hfg'; auto.
    pose proof (Choice (A * B) (distr (A' * B')) _ Hfg') as Ch.

 Proposition Rcoupl_bind :
    forall (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (S : A' → B' → Prop),
      (exists (H : A * B → distr (A' * B')),
          (∀ a b, isCoupl (f a) (g b) (λ x y, (R a b → S x y)) (H (a , b)) )) → coupl μ1 μ2 R →
        coupl (dbind f μ1) (dbind g μ2) S.
  Proof.
    intros f g μ1 μ2 R S HCh Hμ.
    destruct HCh as [ Ch HCh ].
    destruct Hμ as [wit1 ( wit1m1 &  wit1m2 & wit1supp ) ].
    exists(dbind Ch wit1).
    split; try split.
    3: {
     intro p.
     destruct p as (a' & b').
     pose proof (Rtotal_order 0 (dbind Ch wit1 (a', b')) ) as tri.
     destruct tri.
     + right; simpl.
       assert (exists a b, wit1 (a, b) > 0 /\ (Ch (a, b)) (a' , b') > 0) as Hab.
       ++ admit.
       ++ destruct Hab as (a & b & Hab1 & Hab2).
          specialize (HCh a b).
          destruct HCh as (HCh1 & HCh2 & HCh3).
          specialize (HCh3 (a' , b')).
          destruct HCh3; try lra.
          specialize (wit1supp (a, b)).
          destruct wit1supp; try lra.
          auto.

     + destruct H3; auto.
       left.
       pose proof (pmf_pos (dbind Ch wit1) (a', b')).
       lra.

    }.
    + intro a'.
      rewrite /lmarg.
      rewrite /dmap.
      simpl.
      rewrite /dbind_pmf.
      simpl.
      rewrite /dbind_pmf.
      assert (SeriesC (λ a : A' * B', SeriesC (λ a0 : A * B, wit1 a0 * Ch a0 a) * dret_pmf a.1 a')
             = SeriesC (λ a : A' * B', SeriesC (λ a0 : A * B, wit1 a0 * Ch a0 a * dret_pmf a.1 a'))) as Heq1.
      { apply SeriesC_ext. intro p. symmetry.
        apply SeriesC_scal_r.}
     rewrite Heq1.
      assert (SeriesC (λ a : A' * B', SeriesC (λ a0 : A * B, wit1 a0 * Ch a0 a * dret_pmf a.1 a'))
             = SeriesC (λ a0 : A * B, SeriesC (λ a : A' * B', wit1 a0 * Ch a0 a * dret_pmf a.1 a'))) as Heq2.
      { apply (SeriesC_double_swap (λ p, wit1 p.2 * Ch p.2 p.1 * dret_pmf p.1.1 a' )).}
      rewrite Heq2.
      assert (SeriesC (λ a : A, μ1 a * f a a') = SeriesC (λ p : A*B, μ1 p.1 * f p.1 a')) as Heq3.
      { rewrite (SeriesC_double_prod (λ p : A * B, μ1 p.1 * f p.1 a')) .
        apply SeriesC_ext.
        intro a.
        simpl.
       Search Inhabited.
       Search Empty.
      }
   Admitted.
*)