From clutch.prelude Require Import base.
From clutch.program_logic Require Import weakestpre.
From clutch.prob_lang Require Import notation lang.
From clutch.rel_logic Require Import model spec_ra.
From clutch.typing Require Import types.
From clutch.examples.crypto Require Import mc_val_instances.
From clutch Require Import clutch.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import solvable.cyclic choice eqtype finset fintype seq
  ssrbool ssreflect zmodp.
From mathcomp Require ssralg.
Import fingroup.
Set Warnings "notation-overridden,ambiguous-paths".
Set Bullet Behavior "Strict Subproofs".

From deriving Require Import deriving.
From deriving Require Import instances.

Local Open Scope group_scope.
Import fingroup.fingroup.
Local Notation "'cval'" := (prob_lang.val).

Class val_group :=
  Val_group { vgG :> finGroupType
            ; vgval :> vgG → cval
            ; vgval_inj : Inj eq eq vgval }.

(* Both of the below seem necessary since there is a subtle difference in the
   domain type DOM, despite DOM being to {x : val | P x} in both cases. *)
#[nonuniform] Coercion vgval_as {vg : val_group}
  (x : FinGroup.arg_sort (FinGroup.base vgG)) : cval := vgval x.
#[nonuniform] Coercion vgval_s {vg : val_group}
  (x : FinGroup.sort (FinGroup.base vgG)) : cval := vgval x.

Class clutch_group_struct :=
  Clutch_group_struct
    { vunit : cval
    ; vinv : cval
    ; vmult : cval
    (* ; vexp : val *)
    ; int_of_vg : cval
    ; vg_of_int : cval
    ; τG : type
    ; vunit_typed : val_typed vunit τG
    ; vmult_typed : val_typed vmult (τG → τG → τG)%ty
    (* ; vexp_typed : val_typed vexp (τG → TInt → τG)%ty *)
    ; int_of_vg_typed : val_typed int_of_vg (τG → TInt)%ty
    ; vg_of_int_typed : val_typed vg_of_int (TInt → () + τG)%ty
    }.

Definition vexp `{!clutch_group_struct} : cval := λ:"a", rec: "vexp" "n" :=
    if: "n" ≤ #0 then vunit else let: "x" := "vexp" ("n" - #1) in vmult "a" "x".

Definition lrel_G `{clutchRGS Σ} {vg : val_group} : lrel Σ
  := LRel (λ w1 w2, ∃ a : vgG, ⌜ w1 = a ∧ w2 = a ⌝)%I.

(* Could push `{clutchRGS Σ} down to the Iris propositions, or move the
   syntactic typing info into the clutch_group_struct. *)
Class clutch_group `{clutchRGS Σ} {vg : val_group} {cg : clutch_group_struct} :=
  Clutch_group
    {
      (* We want to prove statements such as
         ∀ (x : vg), ⊢ REL x << x : T

         ∀ (x : vg), ⊢ₜ x : τG

         ∀ (v1 v2 : val), T v1 v2 → P v1 ∧ P v2

         ⊢ᵥ vmult : τG → τG → τG

         ⊢ REL vmult << vmult : T → T → T

         Can we prove that
         ⊢ A -∗ B
         → ⊢ REL vmult << vmult : A → A → A
         → ⊢ REL vmult << vmult : B → B → B

       *)
    (*   TT : lrel Σ *)
    (* ; TT_interp v1 v2 : ⊢ TT v1 v2 -∗ interp.interp τG [] v1 v2 *)
    (* ; TT_refl (x : vg) : ⊢ TT x x *)

    (* These two might not be needed if we only deal with fully applied
    expressions, since we can use is_mult / is_exp in those cases instead. *)
    (* ; vmult_lrel_G : ⊢ (lrel_G → lrel_G → lrel_G)%lrel vmult vmult *)
    (* ; vexp_lrel_G : ⊢ (lrel_G → interp.interp TInt [] → lrel_G)%lrel vexp vexp *)

      int_of_vg_lrel_G : ⊢ (lrel_G → interp.interp TInt [])%lrel int_of_vg int_of_vg
    ; vg_of_int_lrel_G : ⊢ (interp.interp TInt [] → (() + lrel_G))%lrel vg_of_int vg_of_int

    (* could add an assumption like
       lrel_G v1 v2 <-> (P v1 /\ P v2 /\ interp τG [] v1 v2)
     *)

    (* ; vg_log_rel' v1 v2 : (⊢ (TT v1 v2) -∗ ⌜ P v1 /\ P v2 ⌝)%I *)
    ; τG_closed : forall Δ, interp.interp τG Δ = interp.interp τG []
    ; vall_typed : (∀ (x : vgG), ⊢ᵥ x : τG)%ty
    (* this won't hold, the syntactic type says nothing about P. *)
    (* ; vg_log_rel v1 v2 : (⊢ (interp.interp τG [] v1 v2) -∗ ⌜ P v1 /\ P v2 ⌝)%I *)
    ; is_unit : vunit = 1
    ; is_inv (x : vgG) : {{{ True }}} vinv x {{{ v, RET (v : cval); ⌜v = x^-1⌝ }}}
    ; is_spec_inv (x : vgG) K :
      refines_right K (vinv x) ={⊤}=∗ refines_right K (x^-1)
    ; is_mult (x y : vgG) : {{{ True }}} vmult x y {{{ v, RET (v : cval); ⌜v = (x * y)%g⌝ }}}
    ; is_spec_mult (x y : vgG) K :
      refines_right K (vmult x y) ={⊤}=∗ refines_right K (x * y)%g
    (* ; is_exp (b : vg) (x : nat) : {{{ True }}} vexp b #x {{{ v, RET (v : val); ⌜v = b ^+ x⌝ }}} *)
    (* ; is_spec_exp (b : vg) (x : nat) K : *)
    (*   refines_right K (vexp b #x) ={⊤}=∗ refines_right K (b ^+ x) *)
    }.

#[export] Hint Extern 0 (val_typed vunit τG) => apply vunit_typed : core.
#[export] Hint Extern 0 (val_typed _ τG) => apply vall_typed : core.
#[export] Hint Extern 0 (val_typed vmult _) => apply vmult_typed : core.
Definition vexp_typed `{!clutch_group_struct} : val_typed vexp (τG → TInt → τG)%ty.
Proof. unfold vexp ; tychk => //. Qed.
#[export] Hint Extern 0 (val_typed vexp _) => apply vexp_typed : core.
#[export] Hint Extern 0 (val_typed int_of_vg _) => apply int_of_vg_typed : core.
#[export] Hint Extern 0 (val_typed vg_of_int _) => apply vg_of_int_typed : core.

Definition vg_of_cg := λ {Σ HΣ} vg cg (G : @clutch_group Σ HΣ vg cg), vg.
Coercion vg_of_cg : clutch_group >-> val_group.

(* vg is generated by g. We further include the assumption that vg is
   nontrivial, i.e. of size at least 2, since this allows us to work with
   mathcomp's 'Z_p type of integers modulo p (taking p := #[g]). *)
Class clutch_group_generator {vg : val_group} :=
  Clutch_group_generator
    { g : vgG
    ; n'' : nat
    ; g_nontriv : #[g] = S (S n'')
    ; g_generator : generator [set: vgG] g
    }.

Set Default Proof Using "Type*".

Section facts.

Context `{!clutchRGS Σ}.

Context {vg : val_group}.
Context {cg : clutch_group_struct}.
Context {G : clutch_group (vg:=vg) (cg:=cg)}.
Context {cgg : @clutch_group_generator vg}.


(* Fact mult_typed : ∀ Γ, Γ ⊢ₜ vmult : (τG → τG → τG)%ty. *)
(* Proof. intros. constructor. apply vmult_typed. Qed. *)

Lemma refines_mult_l E K A (a b : vgG) t :
  (refines E (ectxi_language.fill K (Val (a * b)%g)) t A)
    ⊢ refines E (ectxi_language.fill K (vmult a b)) t A.
Proof.
  iIntros "H".
  rel_apply_l refines_wp_l.
  iApply (is_mult a b) => //.
  iModIntro ; iIntros (v) "->" => //.
Qed.

Lemma refines_mult_r E K A (a b : vgG) t :
  (refines E t (ectxi_language.fill K (Val (a * b)%g)) A)
    ⊢ refines E t (ectxi_language.fill K (vmult a b)) A.
Proof.
  iIntros "H".
  rel_apply_r refines_steps_r => //.
  iIntros (?).
  iApply is_spec_mult.
Qed.

Fact is_exp (b : vgG) (x : nat) :
  {{{ True }}} vexp b #x {{{ v, RET (v : cval); ⌜v = (b ^+ x)%g⌝ }}}.
Proof.
  unfold vexp. iIntros (? _) "hlog".
  wp_pure. wp_pure.
  iInduction x as [|x] "IH" forall (Φ).
  - wp_pures.
    rewrite is_unit.
    iApply ("hlog").
    by rewrite expg0.
  - do 4 wp_pure.
    wp_bind ((rec: _ _ := _)%V _).
    replace (S x - 1)%Z with (Z.of_nat x) by lia.
    iApply "IH".
    iIntros. wp_pures.
    iApply is_mult => //.
    iModIntro. iIntros. subst.
    iApply "hlog".
    by rewrite expgS.
Qed.

Fact is_spec_exp (b : vgG) (x : nat) K :
  refines_right K (vexp b #x) ={⊤}=∗ refines_right K (b ^+ x)%g.
Proof.
  unfold vexp. iIntros "hlog".
  tp_pure. tp_pure.
  iInduction x as [|x] "IH" forall (K).
  - tp_pures. rewrite is_unit.
    iApply ("hlog").
  - do 4 tp_pure.
    tp_bind ((rec: _ _ := _)%V _).
    replace (S x - 1)%Z with (Z.of_nat x) by lia.
    rewrite refines_right_bind.
    iSpecialize ("IH" with "hlog").
    iMod "IH" as "IH".
    rewrite -refines_right_bind => /=.
    tp_pures.
    rewrite is_spec_mult.
    by rewrite expgS.
Qed.

Lemma refines_exp_l E K A (b : vgG) (p : nat) t :
  (refines E (ectxi_language.fill K (Val (b ^+ p)%g)) t A)
    ⊢ refines E (ectxi_language.fill K (vexp b #p)) t A.
Proof.
  iIntros "H".
  rel_apply_l refines_wp_l.
  iApply (is_exp b p) => //.
  iModIntro ; iIntros (v) "->" => //.
Qed.

Lemma refines_exp_r E K A (b : vgG) (p : nat) t :
  (refines E t (ectxi_language.fill K (Val (b ^+ p)%g)) A)
    ⊢ refines E t (ectxi_language.fill K (vexp b #p)) A.
Proof.
  iIntros "H".
  rel_apply_r refines_steps_r => //.
  iIntros (?).
  iApply (is_spec_exp b).
Qed.

Lemma log_g
  : ∀ v : vgG, ∃ k : fin (S (S n'')), (v = g^+k)%g.
Proof using.
  pose proof g_nontriv.
  pose proof g_generator.
  unfold generator in *.
  intros v ; destruct (@cyclePmin vgG g v).
  2: {
    assert (hx : x < #[g]%g) by by apply /ssrnat.leP.
    rewrite g_nontriv in hx.
    exists (nat_to_fin hx).
    symmetry. rewrite e. f_equal.
    rewrite fin_to_nat_to_fin.
    reflexivity.
  }
  assert ([set: vgG] = cycle g)%g as <-.
  2: apply in_setT.
  by destruct (@eqtype.eqP _ [set: vgG] (cycle g)).
Qed.


End facts.

(* fast tactics to simplify multiplications *)
Tactic Notation "rel_mult_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ ?e _ _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          rel_apply_l (refines_mult_l _ _ _ a b _) => //
      | _ => fail "rel_mult_l: no vmult / v1 / v2 found"
      end
  | _ => fail "rel_mult_l: not proving a refinement"
  end.

Tactic Notation "rel_mult_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ _ ?e _) =>
      match e with
      | context[App (App (Val vmult) (Val ?a)) (Val ?b)] =>
          rel_apply_r (refines_mult_r _ _ _ a b _) => //
      | _ => fail "rel_mult_r: no vmult / v1 / v2 found"
      end
  | _ => fail "rel_mult_r: not proving a refinement"
  end.

(* fast tactics to simplify exponentials *)
Tactic Notation "rel_exp_l" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ ?e _ _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          rel_apply_l (refines_exp_l _ _ _ b p _) => //
      | _ => fail "rel_exp_l: no vexp / base / exponent found"
      end
  | _ => fail "rel_exp_l: not proving a refinement"
  end.

Tactic Notation "rel_exp_r" :=
  lazymatch goal with
  | |- environments.envs_entails _ (refines _ _ ?e _) =>
      match e with
      | context[App (App (Val vexp) (Val ?b)) (Val #(LitInt (Z.of_nat ?p)))] =>
          rel_apply_r (refines_exp_r _ _ _ b p _) => //
      | _ => fail "rel_exp_r: no vexp / base / exponent found"
      end
  | _ => fail "rel_exp_r: not proving a refinement"
  end.