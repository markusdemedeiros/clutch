(* ElGamal encryption has one-time secrecy against chosen plaintext attack, in
   the real/random paradigm. Following Rosulek's "The Joy of Crypto". *)
From clutch Require Import clutch.
From clutch.examples.crypto Require Import valgroup more_tactics.
From clutch.examples.crypto Require ElGamal_bijection.

From mathcomp Require ssrnat.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import zmodp finset ssrbool fingroup.fingroup solvable.cyclic.
Set Warnings "notation-overridden,ambiguous-paths".

Set Default Proof Using "Type*".

Section ElGamal.

Ltac rel_red :=
  iStartProof ;
  repeat (iredsr ; try first [rel_exp_r | rel_mult_r | rel_inv_r]) ;
  repeat (iredsl ; try first [rel_exp_l | rel_mult_l | rel_inv_l]).

Context `{!clutchRGS Σ}.

Context {vg : val_group}.           (* A group on a subset of values. *)
Context {cg : clutch_group_struct}. (* Implementations of the vg group operations *)
Context {G : clutch_group (vg:=vg) (cg:=cg)}. (* ...satisfying the group laws. *)
Context {cgg : @clutch_group_generator vg}.   (* G is generated by g. *)
Context {Δ : listO (lrelC Σ)}.

#[local] Notation T := (interp τG Δ).
#[local] Notation n := (S n'').

#[local] Definition rnd t := (rand #n from t)%E.

Import valgroup_notation valgroup_tactics.

(* ElGamal public key encryption *)
Definition keygen : expr :=
  λ:<>, let: "sk" := rnd #() in
    let: "pk" := g^"sk" in
    ("pk", "sk").

Definition enc : expr :=
  λ: "pk", λ: "msg",
    let: "b" := rnd #() in
    let: "B" := g^"b" in
    ("B", "msg" · ("pk"^"b")).

Definition dec : expr :=
  λ:"sk" "BX",
    let, ("B", "X") := "BX" in
    "X" · ("B"^-"sk").

(* The syntactic and semantic type of the Diffie-Hellman game(s). *)
Definition τ_DH := (() → (τG * τG * τG))%ty.
Definition T_DH := Eval cbn in (interp τ_DH Δ).

(* The syntactic and semantic type of the ElGamal game(s). *)
Definition τ_EG := ((() → τG) * (TInt → () + τG * τG))%ty.
Definition T_EG := Eval cbn in (interp τ_EG Δ).

(* The Decisional Diffie Hellman assumption says the following two programs are
   PPT(n) indistinguishable. *)
Definition DH_real : expr :=
  λ:<>,
    let: "a" := rnd #() in let: "b" := rnd #() in
    (g^"a", g^"b", g^("a"*"b")).

Definition DH_rnd : expr :=
  λ:<>,
    let: "a" := rnd #() in let: "b" := rnd #() in let: "c" := rnd #() in
    (g^"a", g^"b", g^"c").

(* Public key OTS-CPA$ security (one-time secrecy chosen plaintext attack -
   real/random) is defined as the indistinguishability of pk_ots_rnd_real and
   pk_ots_rnd_rnd. *)
(* In the random game, rather than encrypting the message, "query" returns a
   random ciphertext, i.e. two random group elements (B,X). *)
Definition pk_ots_rnd_rnd : expr :=
  let, ("pk", "sk") := keygen #() in
  let: "count" := ref #0 in
  let: "getpk" := λ:<>, "pk" in
  let: "query" := λ:"msg",
      let:m "msg" := vg_of_int "msg" in
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      let: "b" := rnd #() in let: "x" := rnd #() in
      let: "B" := g^"b"   in let: "X" := g^"x"   in
      ("B", "X") in
  ("getpk", "query").

(* The real game instead encrypts the message in "query". Below, we transform
   pk_ots_rnd_real into C[DH_real] and C[DH_rnd] into pk_ots_rnd_rnd. *)
Definition pk_ots_rnd_real : expr :=
  let, ("pk", "sk") := keygen #() in
  let: "count" := ref #0 in
  let: "getpk" := λ:<>, "pk" in
  let: "query" := λ:"msg",
      let:m "msg" := vg_of_int "msg" in
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      enc "pk" "msg" in
  ("getpk", "query").

(* Unfold definitions and label the flips. We need to label the flip in
   "query" since it occurs in a closure, and we want to relate it to an
   eager sampling in the set-up phase in order to make DH_real appear as a
   sub-expression. *)
Definition pk_ots_rnd_real_lbl : expr :=
  let: "β" := alloc #n in
  let: "sk" := rnd #() in
  let: "pk" := g^"sk" in
  let: "count" := ref #0 in
  let: "getpk" := λ:<>, "pk" in
  let: "query" := λ:"msg",
      let:m "msg" := vg_of_int "msg" in
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "B" := g^"b" in
      ("B", "msg" · "pk"^"b") in
  ("getpk", "query").

(* Pull out DH_real. This requires moving the sampling of "b" from "query" to
   the initialisation. Only equivalent because "query" gets called only once:
   only one message is encrypted, so only one nonce "b" is required, and we can
   pre-sample it in the setup. *)

Definition eC : expr :=
  (λ: "DH_real_or_rnd",
       let, ("A", "B", "C") := "DH_real_or_rnd" #() in
       let: "count" := ref #0 in
       let: "getpk" := λ: <>, "A" in
       let: "query" := λ: "msg",
           let:m "msg" := vg_of_int "msg" in
           assert (!"count" = #0) ;;;
           "count" <- #1 ;;
           ("B", "msg" · "C") in
       ("getpk", "query")).

Definition pk_ots_rnd_1 : expr := eC DH_real.

(* Isolate DH_rnd. *)
Definition pk_ots_rnd_2 : expr := eC DH_rnd.

Definition C : list ectx_item := [AppRCtx eC].
Definition C' : list ctx_item := [CTX_AppR eC].

(* Inline DH_rnd and push the two random samplings not required for the key
   generation (and thus getpk) back down (using tapes β and γ). *)
Definition pk_ots_rnd_4 : expr :=
  let: "β" := alloc #n in
  let: "γ" := alloc #n in
  let: "a" := rnd #() in
  let: "A" := g^"a" in
  let: "count" := ref #0 in
  let: "getpk" := λ:<>, "A" in
  let: "query" := λ:"msg",
      let:m "msg" := vg_of_int "msg" in
      assert (!"count" = #0) ;;;
      "count" <- #1 ;;
      let: "b" := rnd "β" in
      let: "c" := rnd "γ" in
      let: "B" := g^"b" in
      let: "C" := g^"c" in
      ("B", "msg" · "C") in
  ("getpk", "query").

(* Finally, we connect pk_ots_rnd_4 to pk_ots_rnd_rnd. For this last step, we
   want to show that multiplying the message with a random group element really
   looks random, i.e. that msg⋅C = msg⋅g^c looks random, just like X = g^x. *)
(* We prove this by showing that multiplying by msg induces a bijection f on the
   set fin (S n) we sampled x from: Since msg = g^k for some unique k, msg has
   inverse g^(-k), i.e. we define f(c) := k+c (the inverse is obviously given
   by (λ c, c-k)). Let msg⋅g^c = g^k⋅g^c = g^(k+c). Let x = f(c) be sampled along
   the bijection f. Then g^x = g^f(c) = g^(c+k), as required. *)
(* Since we need to know the value of msg, we cannot combine this game-hop with
   the previous one: in pk_ots_rnd_2, c is sampled before msg is known. *)

Definition pkN := nroot.@"pks".

Local Tactic Notation "inv_prove" :=
  iSplitL ; [ by (repeat (iExists _) ; (by iFrame) || (iLeft ; by iFrame) || (iRight ; by iFrame)) |].

Local Tactic Notation "inv_mk" constr(Pinv) constr(h) :=
  iApply (refines_na_alloc Pinv pkN) ; inv_prove ; iIntros h.

Local Tactic Notation "inv_cl" constr(h) :=
  iApply (refines_na_close with h) ; inv_prove.

Fact refines_get_pk sk : ⊢ (() → T)%lrel (λ: <>, (g ^+ sk)%g)%V (λ: <>, (g ^+ sk)%g)%V.
Proof. iModIntro ; iIntros ; rel_pures ; rel_vals. Qed.

Lemma pk_ots_rnd_real_real_lbl : ⊢ refines top pk_ots_rnd_real pk_ots_rnd_real_lbl T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk (βₛ ↪ₛ (n;[]) ∗ (count ↦ #0 ∗ countₛ ↦ₛ #0) ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1) )%I "#Hinv"...
  rel_vals ; [iApply refines_get_pk|]. iIntros "!>" (??) "[%v[->->]]"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_&%_'&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]"); [done|].
  iIntros "[>[(β&c&c')|(c&c')] Hclose]"...
  2: inv_cl "[- $Hclose]" ; rel_vals.
  rel_couple_UT "β"...
  inv_cl "[- $Hclose]"... rel_vals.
Qed.

Lemma pk_ots_rnd_real_lbl_real : ⊢ refines top pk_ots_rnd_real_lbl pk_ots_rnd_real T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk (β ↪ (n;[]) ∗ (count ↦ #0 ∗ countₛ ↦ₛ #0) ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1) )%I "#Hinv"...
  rel_vals ; [iApply refines_get_pk|]. iIntros "!>" (??) "[%v[->->]]"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_&%_'&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]"); [done|].
  iIntros "[>[(β&c&c')|(c&c')] Hclose]"...
  2: inv_cl "[- $Hclose]" ; rel_vals.
  rel_couple_TU "β"...
  inv_cl "[- $Hclose]" ; rel_vals.
Qed.

Lemma pk_ots_rnd_real_lbl_1 : ⊢ refines top pk_ots_rnd_real_lbl pk_ots_rnd_1 T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU. ireds.
  rel_couple_TU "β"...
  rewrite -Nat2Z.inj_mul...
  inv_mk ((β ↪ (n;[b]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; [iApply refines_get_pk|]. iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>[(β&cnt&cnt')|(c&c')] Hclose]"...
  2: by (inv_cl "[- $Hclose]" ; rel_vals).
  inv_cl "[- $Hclose]"...
  rewrite -expgM -ssrnat.multE. rel_vals.
Qed.

Lemma pk_ots_rnd_1_real_lbl : ⊢ refines top pk_ots_rnd_1 pk_ots_rnd_real_lbl T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU. ireds.
  rel_couple_UT "βₛ"...
  rewrite -Nat2Z.inj_mul...
  inv_mk ((βₛ ↪ₛ (n;[b]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; [iApply refines_get_pk|]. iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]"); [done|].
  iIntros "[>[(β&cnt&cnt')|(c&c')] Hclose]"...
  2: by (inv_cl "[- $Hclose]" ; rel_vals).
  inv_cl "[- $Hclose]"...
  rewrite -expgM -ssrnat.multE. rel_vals.
Qed.

(* This assumption is too strong in this generality, since it does not mention
   PPT indistinguishability and assumes a logical instead of contextual
   refinement. *)
Definition DDH_ref := ⊢ refines top DH_real DH_rnd T_DH.
(* If we do make this assumption though, we may prove the following refinement. *)
Lemma pk_ots_rnd_1_2 (DDH : DDH_ref) : ⊢ refines top pk_ots_rnd_1 pk_ots_rnd_2 T_EG.
Proof with rel_red.
  rewrite /pk_ots_rnd_1 /pk_ots_rnd_2.
  rel_bind_l DH_real. rel_bind_r DH_rnd.
  rel_apply refines_app. 2: iApply DDH.
  replace (T_DH → T_EG)%lrel with (interp (τ_DH → τ_EG)%ty Δ) by auto.
  iApply refines_typed. unfold eC. tychk => //.
Qed.

Lemma pk_ots_rnd_2_4 : ⊢ refines top pk_ots_rnd_2 pk_ots_rnd_4 T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  rel_couple_UT "βₛ"...
  rel_couple_UT "γₛ"...
  inv_mk ((βₛ ↪ₛ (n;[b]) ∗ γₛ ↪ₛ (n;[c]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; [iApply refines_get_pk|] ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind ;
    [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]") => //.
  iIntros "[>[(β'&γ'&cnt&cnt')|(cnt&cnt')] Hclose]"...
  all: inv_cl "[- $Hclose]" ; rel_vals.
Qed.

Lemma pk_ots_rnd_4_2 : ⊢ refines top pk_ots_rnd_4 pk_ots_rnd_2 T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU. iredsr.
  rel_couple_TU "β". iredsr.
  rel_couple_TU "γ"...
  inv_mk ((β ↪ (n;[b]) ∗ γ ↪ (n;[c]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; [iApply refines_get_pk|] ; iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind
  ; [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[$Hinv]") => //.
  iIntros "[>[(β'&γ'&cnt&cnt')|(cnt&cnt')] Hclose]"...
  all: inv_cl "[- $Hclose]" ; rel_vals.
Qed.

Lemma pk_ots_rnd_4_rnd : ⊢ refines top pk_ots_rnd_4 pk_ots_rnd_rnd T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk ((β ↪ (n;[]) ∗ γ ↪ (n;[]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv".
  rel_vals ; [iApply refines_get_pk|]. iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind
  ; [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]") => //.
  iIntros "[>[(β&γ&cnt&cnt')|(cnt&cnt')] Hclose]"...
  2: by (inv_cl "[-$Hclose]" ; rel_vals).
  rel_couple_TU "β"...
  (* Rewrite msg into g^k_msg for some k_msg. *)
  destruct (log_g vmsg) as [k_msg ->].
  (* Sample c on the left, and ((k_msg + c) mod (S n)) on the right. *)
  pose (k_msg_plus := ElGamal_bijection.f n'' k_msg).
  unshelve rel_couple_TU "γ" k_msg_plus...
  inv_cl "[- $Hclose]"...
  rewrite -expgD -ssrnat.plusE.
  assert ((g ^+ (k_msg + x)) = (g ^+ k_msg_plus x))%g as heq.
  { clear. rewrite fin_to_nat_to_fin /= -ssrnat.plusE /Zp_trunc /=.
    pose proof (e := eq_sym (expg_mod_order g (k_msg+x))).
    rewrite g_nontriv in e. exact e.
  }
  rewrite -heq. rel_vals.
Qed.

Lemma pk_ots_rnd_rnd_4 : ⊢ refines top pk_ots_rnd_rnd pk_ots_rnd_4 T_EG.
Proof with rel_red.
  rel_red. rel_couple_UU...
  inv_mk ((βₛ ↪ₛ (n;[]) ∗ γₛ ↪ₛ (n;[]) ∗ count ↦ #0 ∗ countₛ ↦ₛ #0)
          ∨ (count ↦ #1 ∗ countₛ ↦ₛ #1))%I "#Hinv"...
  rel_vals ; [iApply refines_get_pk|]. iIntros "!>" (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind
  ; [iApply vg_of_int_lrel_G ; iExists _ ; eauto|].
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  iApply (refines_na_inv with "[-$Hinv]") => //.
  iIntros "[>[(βₛ&γₛ&count&countₛ)|(count&countₛ)] Hclose]"...
  2: by (inv_cl "[-$Hclose]" ; rel_vals).
  rel_couple_UT "βₛ"...
  (* Rewrite msg into g^k_msg for some k_msg. *)
  destruct (log_g vmsg) as [k_msg ->].
  (* Sample x on the left, and ((-x + k_msg) mod (S n)) on the right. *)
  pose (minus_k_msg_plus := ElGamal_bijection.g n'' k_msg).
  unshelve rel_couple_UT "γₛ" minus_k_msg_plus...
  inv_cl "[- $Hclose]"...
  rewrite -expgD -ssrnat.plusE.
  assert ((g ^+ x) = (g ^+ (k_msg + minus_k_msg_plus x)))%g as heq.
  { clear. rewrite fin_to_nat_to_fin /= /Zp_trunc /=.
    epose proof (e := (expg_mod_order g)).
    rewrite g_nontriv in e.
    rewrite -[in LHS]e -{}[in RHS]e.
    f_equal.
    rewrite div.modnDmr ssrnat.addnC -ssrnat.addnA div.modnDml.
    rewrite [ssrnat.addn x _]ssrnat.addnC ssrnat.addnA.
    rewrite ssrnat.subnK.
    - rewrite div.modnDl. reflexivity.
    - apply /ssrnat.leP. move : (fin_to_nat_lt k_msg). lia.
  }
  rewrite -heq. rel_vals.
Qed.

(* Decryption is left inverse to encryption. We only consider valid messages,
   i.e. integers that decode to a group element (in practice, this means that
   the integer has to be smaller than the group order). *)
Lemma ElGamal_correct :
  ⊢ refines top
      (let, ("pk", "sk") := keygen #() in
       λ:"msg",
         let:m "msg" := vg_of_int "msg" in
         let: "c" := enc "pk" "msg" in
         let: "vmsg" := dec "sk" "c" in
         SOME ("vmsg"))
      (λ:"msg",
         let:m "vmsg" := vg_of_int "msg" in
         SOME ("vmsg"))
      (lrel_int → () + lrel_G).
Proof with rel_red.
  rel_red. rel_randU_l...
  rel_arrow_val ; iIntros (??) "#(%msg&->&->)"...
  rel_bind_l (vg_of_int _) ; rel_bind_r (vg_of_int _) ; rel_apply refines_bind.
  1: iApply vg_of_int_lrel_G ; iExists _ ; eauto.
  iIntros (??) "#(%_1&%_2&[(->&->&->&->)|(->&->&%vmsg&->&->)])"... 1: rel_vals.
  rel_randU_l...
  rewrite -?expgM -ssrnat.multE -mulgA Nat.mul_comm mulgV mulg1.
  rel_vals.
Qed.

End ElGamal.

Section Ctx.

Context {vg : val_group}.
Context {cg : clutch_group_struct}.
Context {G : forall `{!clutchRGS Σ}, clutch_group (vg:=vg) (cg:=cg)}.
Context {cgg : @clutch_group_generator vg}.

Lemma ctx_pk_ots_rnd_real_real_lbl :
  ∅ ⊨ pk_ots_rnd_real =ctx= pk_ots_rnd_real_lbl : τ_EG.
Proof.
  split ; apply (refines_sound clutchRΣ) ; intros.
  - apply: pk_ots_rnd_real_real_lbl.
  - apply: pk_ots_rnd_real_lbl_real.
Qed.

Lemma ctx_pk_ots_rnd_real_lbl_1 :
  ∅ ⊨ pk_ots_rnd_real_lbl =ctx= (fill C DH_real) : τ_EG.
Proof.
  split ; apply (refines_sound clutchRΣ) ; intros.
  - apply: pk_ots_rnd_real_lbl_1.
  - apply: pk_ots_rnd_1_real_lbl.
Qed.

Lemma ctx_pk_ots_rnd_2_4 :
  ∅ ⊨ (fill C DH_rnd) =ctx= pk_ots_rnd_4 : τ_EG.
Proof.
  split ; apply (refines_sound clutchRΣ) ; intros.
  - apply: pk_ots_rnd_2_4.
  - apply: pk_ots_rnd_4_2.
Qed.

Lemma ctx_pk_ots_rnd_4_rnd :
  ∅ ⊨ pk_ots_rnd_4 =ctx= pk_ots_rnd_rnd : τ_EG.
Proof.
  split ; apply (refines_sound clutchRΣ) ; intros.
  - apply: pk_ots_rnd_4_rnd.
  - apply: pk_ots_rnd_rnd_4.
Qed.

Global Instance ctx_equiv_transitive Γ τ :
  Transitive (fun e1 e2 => ctx_equiv Γ e1 e2 τ).
Proof.
  intros e1 e2 e3 [Hctx11 Hctx12] [Hctx21 Hctx22].
  split ; eapply ctx_refines_transitive ;eauto.
Qed.

Lemma pk_ots_rnd_real_ddh_real :
  ∅ ⊨ pk_ots_rnd_real =ctx= (fill C DH_real) : τ_EG.
Proof.
  eapply ctx_equiv_transitive.
  - apply: ctx_pk_ots_rnd_real_real_lbl.
  - apply: ctx_pk_ots_rnd_real_lbl_1.
Qed.

Lemma pk_ots_rnd_rnd_ddh_rnd :
  ∅ ⊨ (fill C DH_rnd) =ctx= pk_ots_rnd_rnd : τ_EG.
Proof.
  eapply ctx_equiv_transitive.
  - apply: ctx_pk_ots_rnd_2_4.
  - apply: ctx_pk_ots_rnd_4_rnd.
Qed.

Lemma pk_ots_rnd_ddh_C :
  (∅ ⊨ DH_real =ctx= DH_rnd : τ_DH) →
  (∅ ⊨ (fill C DH_real) =ctx= (fill C DH_rnd) : τ_EG).
Proof.
  replace (fill C _) with (fill_ctx C' DH_real) ; auto ;
    replace (fill C _) with (fill_ctx C' DH_rnd) => //.
  intros DDH.
  split.
  - eapply ctx_refines_congruence.
    2: apply DDH.
    unfold C', eC. tychk => //.
  - eapply ctx_refines_congruence.
    2: apply DDH.
    unfold C', eC. tychk => //.
Qed.

Lemma pk_ots_rnd_ddh (DDH : ∅ ⊨ DH_real =ctx= DH_rnd : τ_DH) :
  (∅ ⊨ pk_ots_rnd_real =ctx= pk_ots_rnd_rnd : τ_EG).
Proof.
  eapply ctx_equiv_transitive.
  - apply: pk_ots_rnd_real_ddh_real.
  - eapply ctx_equiv_transitive.
    + apply: pk_ots_rnd_ddh_C => //.
    + apply: pk_ots_rnd_rnd_ddh_rnd.
Qed.

(*
Definition DDH :=
            ∅ ⊨_{#|g|} DH_rnd =ctx= DH_real : τ_EG.

            ∅ ⊨_ε({#|g|}) DH_rnd =ctx= DH_real : τ_EG.

            ∅ ⊨_{#|g|} C [DH_rnd] =ctx= C [DH_real] : τ_EG.

Fact PPT_C : @PPT #|g| C.

Theorem Ctx_PPT_congr : PPT n C →
            ∅ ⊨_n e1 =ctx= e2 : τ_EG →
            ∅ ⊨_n C [e1] =ctx= C [e2] : τ_EG.
*)

End Ctx.