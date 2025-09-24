From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt.
Import Rdefinitions.RbaseSymbolsImpl.
Import Hierarchy.
Import SF_seq.
Import Reals.
Import mathcomp.ssreflect.seq.
Import Coq.micromega.Lra.

From Coquelicot Require Import AutoDerive Compactness Complex Continuity Derive.
From Coquelicot Require Import Derive_2d Equiv ElemFct Hierarchy Lim_seq.
From Coquelicot Require Import Lub Markov PSeries Rbar Rcomplements.
From Coquelicot Require Import RInt RInt_gen RInt_analysis Seq_fct Series SF_seq.

From clutch.prob Require Import distribution couplings couplings_app mdp. (* Importing this just for the transitive deps idk *)

(* Fubini's theorem *)
Set Default Proof Using "Type*".

Context `{V : NormedModule R_AbsRing}.


(* Reduction of Fubini's theorem to the one we could prove *)


Check prod_ball.

Definition Continuity2 (f : (R * R) -> R) (x y : R) : Prop :=
  filterlim f (locally (x, y)) (locally (f (x, y))).

Definition Discontinuities2 (f : R * R -> R) : R * R -> Prop :=
  fun '(x, y) => ¬ Continuity2 f x y.

(* A set is negligible if it can be covered by countably many balls of arbitrarily small total volume. *)
Definition Negligible (S : R * R -> Prop) : Prop :=
  ∀ (ε : posreal), ∃ (c : nat -> R * R) (r : nat -> nonnegreal),
    (Series (fun n => r n * r n) < ε) /\
    (∀ x, S x -> ∃ n, ball (c n) (r n) x).

Theorem Negligible_Empty : Negligible (fun _ => False).
Proof.
  intro ε.
  exists (fun _ => (0, 0)), (fun _ => mknonnegreal 0 (Rle_refl 0)); constructor.
  { simpl. rewrite Series_0; [apply cond_pos | ]. intros ?; lra. }
  intros ? [].
Qed.

(* Sets *)

Definition Icc (a b : R) : R -> Prop :=
  fun t => Rmin a b <= t <= Rmax a b.

Definition Ici (a : R) : R -> Prop :=
  fun t => a <= t.

Definition Iic (b : R) : R -> Prop :=
  fun t => t <= b.

Definition Iii : R -> Prop :=
  fun t => True.

Definition RII (X Y : R -> Prop) : R * R -> Prop :=
  fun '(tx, ty) => X tx /\ Y ty.

Definition On {T} (S U : T -> Prop) : Prop :=
  ∀ t, S t -> U t.

Definition Int {T} (S U : T -> Prop) : T -> Prop :=
  fun t => S t /\ U t.

Definition Bounded (f : R * R -> R) (M : R) : R * R -> Prop :=
  fun t => Rabs (f t) <= M.

(*
Definition BoundedOnRectangle (xa xb ya yb : R) (f : R * R -> R) (M : R) : Prop :=
  ∀ t, OnRectangle xa xb ya yb (fun t => Rabs (f t) <= M) t.

Definition NegligibleDiscontinuitiesOnRectangle (xa xb ya yb : R) (f : R * R -> R) : Prop :=
  Negligible (fun '(tx, ty) => Rmin xa xb <= tx <= Rmax xa xb /\
                             Rmin ya yb <= ty <= Rmax ya yb /\
                             Discontinuities2 f (tx, ty)).
*)

(* f, partially applied, and set to zero outside an interval.
The integral of this is equal to the integral of f(x, ⋅) on the interval. *)
Definition FubiniIx (f : R * R -> R) (x : R) (xa xb : R) : R -> R :=
  if bool_decide (Rmin xa xb <= x <= Rmax xa xb)
    then fun y => f (x, y)
    else fun y => 0.

Theorem FubiniIx_eval {f : R * R -> R} {xa xb x y : R}
  (Hx : Rmin xa xb < x < Rmax xa xb) :
  FubiniIx f x xa xb y = f (x, y).
Proof. Admitted.

Definition FubiniIy (f : R * R -> R) (y : R) (ya yb : R) : R -> R :=
  if bool_decide (Rmin ya yb <= y <= Rmax ya yb)
    then fun x => f (x, y)
    else fun x => 0.

Theorem FubiniIy_eval {f : R * R -> R} {ya yb x y : R}
  (Hx : Rmin ya yb < y < Rmax ya yb) :
  FubiniIy f y ya yb x = f (x, y).
Proof. Admitted.

(* Fix x, integrate over y *)
Theorem FubiniCoreIntegrableX {f : R * R → R} {xa xb ya yb M x : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  Riemann_integrable (FubiniIx f x xa xb) ya yb.
Proof. Admitted.

(* Fix y, integrate over x *)
Theorem FubiniCoreIntegrableY {f : R * R → R} {xa xb ya yb M y : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  Riemann_integrable (FubiniIy f y ya yb) xa xb.
Proof. Admitted.

Definition FubiniCoreIntegralX {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :=
  fun x => RiemannInt (@FubiniCoreIntegrableX f xa xb ya yb M x HB HC).

Definition FubiniCoreIntegralY {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :=
  fun y => RiemannInt (@FubiniCoreIntegrableY f xa xb ya yb M y HB HC).

Definition FubiniCoreX {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  Riemann_integrable (FubiniCoreIntegralY HB HC) ya yb.
Proof. Admitted.

Definition FubiniCoreY {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  Riemann_integrable (FubiniCoreIntegralX HB HC) xa xb.
Proof. Admitted.

Theorem FubiniCore {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  RiemannInt (@FubiniCoreX f xa xb ya yb M HB HC) = RiemannInt (@FubiniCoreY f xa xb ya yb M HB HC).
Proof. Admitted.

(* Coquelicot version of Fubini, which reduces to the Stdlib (core) version *)
Theorem Fubini {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  RInt (fun x => RInt (fun y => f (x, y)) ya yb) xa xb = RInt (fun y => RInt (fun x => f (x, y)) xa xb) ya yb.
Proof.
  rewrite (RInt_ext (λ x : R, RInt (λ y : R, f (x, y)) ya yb) (FubiniCoreIntegralX HB HC) xa xb); last first.
  { intros x Hx.
    rewrite /FubiniCoreIntegralX -RInt_Reals.
    apply RInt_ext.
    intros y Hy.
    by rewrite (FubiniIx_eval Hx).
  }
  rewrite (RInt_ext (λ y : R, RInt (λ x : R, f (x, y)) xa xb) (FubiniCoreIntegralY HB HC) ya yb); last first.
  { intros y Hy.
    rewrite /FubiniCoreIntegralY -RInt_Reals.
    apply RInt_ext.
    intros x Hx.
    by rewrite (FubiniIy_eval Hy).
  }
  replace (RInt (FubiniCoreIntegralX HB HC) xa xb)
    with (RiemannInt (@FubiniCoreY f xa xb ya yb M HB HC))
    by (by rewrite -RInt_Reals).
  by rewrite -FubiniCore -RInt_Reals.
Qed.

Theorem exRInt_FubiniX {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  ex_RInt (fun x => RInt (fun y => f (x, y)) ya yb) xa xb.
Proof.
  eapply ex_RInt_ext; last (eapply ex_RInt_Reals_1; apply (FubiniCoreY HB HC)).
  intros x Hx.
  rewrite /FubiniCoreIntegralX -RInt_Reals.
  apply RInt_ext.
  intros y Hy.
  by rewrite (FubiniIx_eval Hx).
Qed.

Theorem exRInt_FubiniY {f : R * R → R} {xa xb ya yb M : R}
  (HB : On (RII (Icc xa xb) (Icc ya yb)) (Bounded f M))
  (HC : Negligible (Int (RII (Icc xa xb) (Icc ya yb)) (Discontinuities2 f))) :
  ex_RInt (fun y => RInt (fun x => f (x, y)) xa xb) ya yb.
Proof.
  eapply ex_RInt_ext; last (eapply ex_RInt_Reals_1; apply (FubiniCoreX HB HC)).
  intros y Hy.
  rewrite /FubiniCoreIntegralY -RInt_Reals.
  apply RInt_ext.
  intros x Hx.
  by rewrite (FubiniIy_eval Hy).
Qed.


(* Fubini's theorem with indefinite integrals

Uses the set naming convention for the two integrals.

There are 16 different combinations we might want, because each of xa xb ya and yb could be infinite.

Of course there is a lot of redundancy. *)

(* Endpoints: Each endpoint is either finite or infinite.
   Integrals over two finite endpoints are allowed to be in the wrong order.
   However, integrals with one finite and one infinite endpoint are assumed to be the right way around.
   ie. (F 5, I) is always the integral from 5 to infinity, not the (backwards) integral from 5 to -infinity.
 *)

Inductive EP := | F (r : R) | I.

Definition EPi (a b : EP) : R -> Prop :=
  match a, b with
  | F a, F b => Icc a b
  | F a, I => Ici a
  | I, F b => Iic b
  | I, I => Iii
  end.

Definition EPr (xa xb ya yb : EP) : R * R -> Prop :=
  RII (EPi xa xb) (EPi ya yb).

(* Lower filter for an endpoint *)
Definition EPfl (a : EP) : (R -> Prop) -> Prop  :=
  match a with | F i => at_point i | I => Rbar_locally m_infty end.

(* Upper filter for an endpoint *)
Definition EPfu (b : EP) : (R -> Prop) -> Prop  :=
  match b with | F i => at_point i | I => Rbar_locally p_infty end.

Definition Swap2 (f : R * R -> R) : R * R -> R := fun '(x, y) => f (y, x).

(* Bound exchanges. Doesn't exchange the bounds in general but does echange their finite-ness/infinite-ness. *)

Definition exL (a b : EP) : EP :=
  match a, b with
  | F x, F _ => F x
  | F _, I => I
  | I, F y => F (-y)
  | I, I => I
  end.

Definition exU (a b : EP) : EP :=
  match a, b with
  | F _, F y => F y
  | F x, I => F (-x)
  | I, F _ => I
  | I, I => I
  end.

Definition exF (a b : EP) (r : R) : R :=
  match a, b with
  | F _, F _ => r
  | F _, I => -r
  | I, F _ => -r
  | I, I => r
  end.

(* Correctness of the integral exchange *)
Theorem Exch (f : R -> R) (a b : EP) :
  RInt_gen f (EPfl a) (EPfu b) = RInt_gen (fun x => f (exF a b x)) (EPfl (exL a b)) (EPfu (exU a b)).
Proof.
  destruct a; destruct b; rewrite /exL/exU//=.
  (* Change of variables x -> -x, then add a negative sign to change the order. *)
  { admit. }
  { admit. }
Admitted.

Definition ExchX (f : R * R -> R) (xa xb : EP) : R * R -> R :=
  fun '(x, y) => f (exF xa xb x, y).

Definition ExchY (f : R * R -> R) (ya yb : EP) : R * R -> R :=
  fun '(x, y) => f (x, exF ya yb y).

(* Define this as a Prop so I can do reductions on it *)
Definition FubiniGen (f : R * R -> R) (xa xb ya yb : EP) : Prop :=
  RInt_gen (fun x => RInt_gen (fun y => f (x, y)) (EPfl ya) (EPfu yb)) (EPfl xa) (EPfu xb) =
  RInt_gen (fun y => RInt_gen (fun x => f (x, y)) (EPfl xa) (EPfu xb)) (EPfl ya) (EPfu yb).

Definition FubiniGenBound (f : R * R -> R) (xa xb ya yb : EP) (M : R) : Prop :=
  On (EPr xa xb ya yb) (Bounded f M).

Theorem RevXBound {f : R * R → R} {xa xb ya yb : EP} {M} :
  FubiniGenBound f xa xb ya yb M ->
  FubiniGenBound (ExchX f xa xb) (exL xa xb) (exU xa xb) ya yb M.
Proof.
  destruct xa; destruct xb; rewrite /FubiniGenBound/ExchX//=.
  { rewrite /On/EPr/Bounded//=.
    intros H [x y] Hin.
    apply H.
    apply Hin.
  }
  { rewrite /On/EPr/Bounded/RII//=.
    intros H [x y] [HinX HinY].
    apply H; intuition.
    revert HinX; rewrite /Iic/Ici//=; nra.
  }
  { rewrite /On/EPr/Bounded/RII//=.
    intros H [x y] [HinX HinY].
    apply H; intuition.
    revert HinX; rewrite /Iic/Ici//=; nra.
  }
  { rewrite /On/EPr/Bounded//=.
    intros H [x y] Hin.
    apply H.
    apply Hin.
  }
Qed.

Theorem RevYBound {f : R * R → R} {xa xb ya yb : EP} {M} :
  FubiniGenBound f xa xb ya yb M ->
  FubiniGenBound (ExchY f ya yb) xa xb (exL ya yb) (exU ya yb) M.
Proof.
  destruct ya; destruct yb; rewrite /FubiniGenBound/ExchY//=.
  { rewrite /On/EPr/Bounded//=.
    intros H [x y] Hin.
    apply H.
    apply Hin.
  }
  { rewrite /On/EPr/Bounded/RII//=.
    intros H [x y] [HinX HinY].
    apply H; intuition.
    revert HinY; rewrite /Iic/Ici//=; nra.
  }
  { rewrite /On/EPr/Bounded/RII//=.
    intros H [x y] [HinX HinY].
    apply H; intuition.
    revert HinY; rewrite /Iic/Ici//=; nra.
  }
  { rewrite /On/EPr/Bounded//=.
    intros H [x y] Hin.
    apply H.
    apply Hin.
  }
Qed.

Theorem Swap2Bound {f : R * R → R} {xa xb ya yb : EP} {M : R} :
  FubiniGenBound f xa xb ya yb M ->
  FubiniGenBound (Swap2 f) ya yb xa xb M.
Proof.
  rewrite /FubiniGenBound/Swap2/Bounded/On//=.
  intros HB [x y] HS.
  apply HB.
  revert HS.
  rewrite /EPr//=.
  intuition.
Qed.

Theorem SplitXLBound {f : R * R → R} {ya yb : EP} {M} :
  FubiniGenBound f I I ya yb M -> FubiniGenBound f I (F 0) ya yb M.
Proof.
  rewrite /FubiniGenBound/Bounded/On/EPr/RII//=.
  intros HB [x y] HS.
  apply HB.
  by intuition.
Qed.

Theorem SplitXRBound {f : R * R → R} {ya yb : EP} {M} :
  FubiniGenBound f I I ya yb M -> FubiniGenBound f (F 0) I ya yb M.
Proof.
  rewrite /FubiniGenBound/Bounded/On/EPr/RII//=.
  intros HB [x y] HS.
  apply HB.
  by intuition.
Qed.

Definition FubiniGenInt (f : R * R -> R) (xa xb ya yb : EP) : Prop :=
  Negligible (Int (EPr xa xb ya yb) (Discontinuities2 f)).

Theorem Swap2Int {f : R * R → R} {xa xb ya yb : EP} :
  FubiniGenInt f xa xb ya yb ->
  FubiniGenInt (Swap2 f) ya yb xa xb.
Proof. Admitted.

Theorem RevXInt {f : R * R → R} {xa xb ya yb : EP} :
  FubiniGenInt f xa xb ya yb ->
  FubiniGenInt (ExchX f xa xb) (exL xa xb) (exU xa xb) ya yb.
Proof. Admitted.

Theorem RevYInt {f : R * R → R} {xa xb ya yb : EP} :
  FubiniGenInt f xa xb ya yb ->
  FubiniGenInt (ExchY f ya yb) xa xb (exL ya yb) (exU ya yb).
Proof. Admitted.

Theorem SplitXLInt {f : R * R → R} {ya yb : EP} :
  FubiniGenInt f I I ya yb -> FubiniGenInt f I (F 0) ya yb.
Proof. Admitted.

Theorem SplitXRInt {f : R * R → R} {ya yb : EP} :
  FubiniGenInt f I I ya yb -> FubiniGenInt f (F 0) I ya yb.
Proof. Admitted.

(* First reduct: The definite-definite case. *)
Theorem FubiniGenIccIcc {f : R * R → R} {xa xb ya yb : R} {M : R}
  (HB : FubiniGenBound f (F xa) (F xb) (F ya) (F yb) M)
  (HC : FubiniGenInt f (F xa) (F xb) (F ya) (F yb)) :
  FubiniGen f (F xa) (F xb) (F ya) (F yb).
Proof.
  (* Simplify the integrals and apply Fubini from above *)
  rewrite /FubiniGen//=.
  rewrite RInt_gen_at_point; last first.
  { admit. }
  rewrite RInt_gen_at_point; last first.
  { admit. }
  replace (λ x, RInt_gen (λ y, f (x, y)) (at_point ya) (at_point yb))
     with (λ x, RInt (λ y, f (x, y)) ya yb); last first.
  { apply functional_extensionality; intro x.
    rewrite RInt_gen_at_point; first done.
    admit. }
  replace (λ y, RInt_gen (λ x, f (x, y)) (at_point xa) (at_point xb))
     with (λ y, RInt (λ x, f (x, y)) xa xb); last first.
  { apply functional_extensionality; intro y.
    rewrite RInt_gen_at_point; first done.
    admit. }
  by apply (Fubini HB HC).
Admitted.

(* Fubini's theorem for indefinite/definite integral. TODO: This is the main proof. *)
Theorem FubiniGenIciIcc {f : R * R → R} {xa ya yb : R} {M : R}
  (HB : FubiniGenBound f (F xa) I (F ya) (F yb) M)
  (HC : FubiniGenInt f (F xa) I (F ya) (F yb)) :
  FubiniGen f (F xa) I (F ya) (F yb).
Proof. Admitted.

(* TODO: Does this reduce to the prior case? *)
Theorem FubiniGenIciIci {f : R * R → R} {xa ya : R} {M : R}
  (HB : FubiniGenBound f (F xa) I (F ya) I M)
  (HC : FubiniGenInt f (F xa) I (F ya) I) :
  FubiniGen f (F xa) I (F ya) I.
Proof. Admitted.


(* Reduce indefinite/indefinite Fubini's theorem to the Ici case by Chasales theorem.
   Do I need an extra assumption or am I able to make use of the prior Fubini theorems? *)
Theorem FubiniGenIii {f : R * R → R} {ya yb : EP}
  (HFL : FubiniGen f I (F 0) ya yb) (HFU : FubiniGen f (F 0) I ya yb) :
  FubiniGen f I I ya yb.
Proof.
  rewrite /FubiniGen; rewrite /FubiniGen in HFL HFU.
  (* Split up the integrals, commute by HFU/HFL, and recombine. *)
Admitted.

(* Reduction: Symmetry of Eq. Cuts the number of proof obligations in half. *)
Theorem FubiniGenSwap2 {f : R * R → R} {xa xb ya yb : EP} :
  FubiniGen (Swap2 f) ya yb xa xb -> FubiniGen f xa xb ya yb.
Proof. unfold FubiniGen. by move=>->. Qed.

Theorem FubiniGenRevX  {f : R * R → R} {xa xb ya yb : EP} :
  FubiniGen (ExchX f xa xb) (exL xa xb) (exU xa xb) ya yb ->
  FubiniGen f xa xb ya yb.
Proof.
  (* Rewrite using the correctness of Exch *)
Admitted.

Theorem FubiniGenRevY {f : R * R → R} {xa xb ya yb : EP} :
  FubiniGen (ExchY f ya yb) xa xb (exL ya yb) (exU ya yb) ->
  FubiniGen f xa xb ya yb.
Proof.
  (* Rewrite using the correctness of Exch *)
Admitted.

(* The general theorem *)
Theorem FubiniGenHolds {f : R * R → R} {xa xb ya yb : EP} {M : R}
  (HB : FubiniGenBound f xa xb ya yb M) (HC : FubiniGenInt f xa xb ya yb ) :
  FubiniGen f xa xb ya yb.
Proof.
  destruct xa, xb, ya, yb.
  - (* Icc Icc *)
    exact (FubiniGenIccIcc HB HC).
  - (* Icc Ici *)
    apply FubiniGenSwap2; apply Swap2Bound in HB; apply Swap2Int in HC.
    exact (FubiniGenIciIcc HB HC).
  - (* Icc Iic *)
    apply FubiniGenSwap2; apply Swap2Bound in HB; apply Swap2Int in HC.
    apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
    exact (FubiniGenIciIcc HB HC).
  - (* Icc Iii *)
    apply FubiniGenSwap2; apply Swap2Bound in HB; apply Swap2Int in HC.
    apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                        | apply SplitXRBound in HB; apply SplitXRInt in HC].
    + apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
      exact (FubiniGenIciIcc HB HC).
    + exact (FubiniGenIciIcc HB HC).
  - (* Ici Icc *)
    exact (FubiniGenIciIcc HB HC).
  - (* Ici Ici *)
    exact (FubiniGenIciIci HB HC).
  - (* Ici Iic *)
    apply FubiniGenRevY; apply RevYBound in HB; apply RevYInt in HC.
    exact (FubiniGenIciIci HB HC).
  - (* Ici Iii *)
    apply FubiniGenSwap2; apply Swap2Bound in HB; apply Swap2Int in HC.
    apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                        | apply SplitXRBound in HB; apply SplitXRInt in HC].
    + apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
      exact (FubiniGenIciIci HB HC).
    + exact (FubiniGenIciIci HB HC).
  - (* Iic Icc *)
    apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
    exact (FubiniGenIciIcc HB HC).
  - (* Iic Ici *)
    apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
    exact (FubiniGenIciIci HB HC).
  - (* Iic Iic *)
    apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
    apply FubiniGenRevY; apply RevYBound in HB; apply RevYInt in HC.
    exact (FubiniGenIciIci HB HC).
  - (* Iic Iii *)
    apply FubiniGenSwap2; apply Swap2Bound in HB; apply Swap2Int in HC.
    apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                        | apply SplitXRBound in HB; apply SplitXRInt in HC].
    + apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
      apply FubiniGenRevY; apply RevYBound in HB; apply RevYInt in HC.
      exact (FubiniGenIciIci HB HC).
    + apply FubiniGenRevY; apply RevYBound in HB; apply RevYInt in HC.
      exact (FubiniGenIciIci HB HC).
  - (* Iii Icc *)
    apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                        | apply SplitXRBound in HB; apply SplitXRInt in HC].
    + apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
      exact (FubiniGenIciIcc HB HC).
    + exact (FubiniGenIciIcc HB HC).
  - (* Iii Ici *)
    apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                        | apply SplitXRBound in HB; apply SplitXRInt in HC].
    + apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
      exact (FubiniGenIciIci HB HC).
    + exact (FubiniGenIciIci HB HC).
  - (* Iii Iic *)
    apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                        | apply SplitXRBound in HB; apply SplitXRInt in HC].
    + apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
      apply FubiniGenRevY; apply RevYBound in HB; apply RevYInt in HC.
      exact (FubiniGenIciIci HB HC).
    + apply FubiniGenRevY; apply RevYBound in HB; apply RevYInt in HC.
      exact (FubiniGenIciIci HB HC).
  - (* Iii Iii *)
    apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                        | apply SplitXRBound in HB; apply SplitXRInt in HC].
    + apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
      apply FubiniGenSwap2; apply Swap2Bound in HB; apply Swap2Int in HC.
      apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                          | apply SplitXRBound in HB; apply SplitXRInt in HC].
      * apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
        exact (FubiniGenIciIci HB HC).
      * exact (FubiniGenIciIci HB HC).
    + apply FubiniGenSwap2; apply Swap2Bound in HB; apply Swap2Int in HC.
      apply FubiniGenIii; [apply SplitXLBound in HB; apply SplitXLInt in HC
                          | apply SplitXRBound in HB; apply SplitXRInt in HC].
      * apply FubiniGenRevX; apply RevXBound in HB; apply RevXInt in HC.
        exact (FubiniGenIciIci HB HC).
      * exact (FubiniGenIciIci HB HC).
Qed.




  (*



(* Improper-Proper Fubini's theorem *)


Search Rbar "locally".

Check RInt_gen (fun x => RInt (fun y => f (x, y)) ya yb) (locally xa) (Rbar_locally .

(*
First off: Should do Chasales to split it into the positive and negative parts with
  RInt_gen_Chasles. *)



Search RInt_gen.

Print RInt_gen.
Print is_RInt_gen.



Search RInt.
Search is_RInt.
Check filterlim_RInt.

Check filterlim.

(* Check proof of RInt_PSeries:  *)



Search filterlimi.


Check filterlimi.
Check RInt_gen_at_point. (* RInt_gen to RInt *)

(* Fubini's theorem with definite-indefinite integral *)
(* Fubini's theorem with indefinite-indefinite integral *)
*)



(* Indefinite integral equals series *)






(* WIP: Proving the admitted theorems:






Check filterlim.
Check Riemann_fine.
Locate RInt_val.
Locate is_RInt.
Locate RiemannInt.RiemannInt. (* Stdlib integral *)
Check RInt_Reals. (* Coquelicot version equals Stdlib version for all stdlib-integrable functions *)
Check ex_RInt_Reals_0. (* Equivalence of integrability *)
Check ex_RInt_Reals_1. (* Equivalence of integrability *)

(* Do we have a supremum operator? Instead of using the Coquelicot version to define lower and upper integrals,
   it might be easier to define it using the stdlib (since they quantify over step functions whereas
   Coquelicot uses a specific one) *)

Locate RiemannInt.
Print seq.
Search filter_le locally.
Search is_RInt.
Check Riemann_fine.
Locate SF_sup_fun.





(* The constant step function
  exists ({| fe := fct_cte M; pre := StepFun_P4 a b M |}); constructor.
 *)


Definition LowerStepFun (a b : R) (f : R -> R) (ϕ : StepFun a b) : Prop :=
  forall t : R,  Rmin a b <= t <= Rmax a b -> ϕ t <= f t.

Definition UpperStepFun (a b : R) (f : R -> R) (ϕ : StepFun a b) : Prop :=
  forall t : R,  Rmin a b <= t <= Rmax a b -> f t <= ϕ t.


Definition IsLowerIntegral (a b : R) (f : R -> R) (r : R) : Prop :=
  exists ϕ : StepFun a b, LowerStepFun a b f ϕ /\ RiemannInt_SF ϕ = r.

Definition IsUpperIntegral (a b : R) (f : R -> R) (r : R) : Prop :=
  exists ϕ : StepFun a b, UpperStepFun a b f ϕ /\ RiemannInt_SF ϕ = r.

Theorem IsLowerIntegral_IsUpperIntegral_fwd_le (a b : R) (f : R -> R) (rl ru : R) :
  a <= b -> IsLowerIntegral a b f rl -> IsUpperIntegral a b f ru -> rl <= ru.
Proof.
  intros Hab [ϕl [Hl HlInt]] [ϕu [Hu HuInt]].
  rewrite -HlInt -HuInt.
  apply (StepFun_P37 _ _ Hab).
  intros x Hx.
  have Hab' : Rmin a b <= x <= Rmax a b by rewrite (Rmin_left _ _ Hab) (Rmax_right _ _ Hab); nra.
  etransitivity.
  { apply (Hl _ Hab'). }
  { apply (Hu _ Hab'). }
Qed.

(* There is a finite upper bound on the lower integrals when f is bounded *)
Theorem IsLowerIntegral_UpperBound_fwd {a b : R} (Hab : a <= b) {f : R -> R} {M : R} (H : BoundedByOn a b f M) :
  ∀ r, IsLowerIntegral a b f r → r <= M * (b-a).
Proof.
  intros r [ϕ [Hlsf Hsfint]].
  rewrite -Hsfint -(StepFun_P18 a b M).
  apply (StepFun_P37 _ _ Hab); intros x Hx.
  rewrite /fct_cte//=.
  have Hab' : Rmin a b <= x <= Rmax a b by rewrite (Rmin_left _ _ Hab) (Rmax_right _ _ Hab); nra.
  etransitivity; first apply (Hlsf _ Hab').
  etransitivity; first apply RRle_abs.
  apply (H x Hab').
Qed.

(*
Theorem IsLowerIntegral_UpperBound_neg {a b : R} (Hab : b <= a) {f : R -> R} {M : R} (H : BoundedByOn a b f M) :
  ∀ r, IsLowerIntegral a b f r → r <= M * (b-a). (* Might be wrong *)
Proof.
  intros r [ϕ [Hlsf Hsfint]].
  rewrite StepFun_P39 in Hsfint.
  (* Check StepFun_P6. *)
Admitted.
*)


(* There's definitely some way to prove something like this *)
Theorem IsLowerIntegral_UpperBound {a b : R} {f : R -> R} {M : R} (H : BoundedByOn a b f M) :
  ∀ r, IsLowerIntegral a b f r → r <= Rabs M * Rabs (b-a).
Proof. Admitted.

(* There's definitely some way to prove something like this *)
Theorem IsLowerIntegral_LowerBound {a b : R} {f : R -> R} {M : R} (H : BoundedByOn a b f M) :
  IsLowerIntegral a b f (- Rabs M * Rabs (b-a)).
Proof. Admitted.


Theorem IsLowerIntegral_Lub_finite {a b : R} {f : R -> R} {M : R} (H : BoundedByOn a b f M) :
  is_finite (Lub_Rbar (IsLowerIntegral a b f)).
Proof.
  eapply Coquelicot_ext.is_finite_bounded.
Admitted.

Theorem IsUpperIntegral_Glb_finite {a b : R} {f : R -> R} {M : R} (H : BoundedByOn a b f M) :
  is_finite (Glb_Rbar (IsUpperIntegral a b f)).
Proof.
  eapply Coquelicot_ext.is_finite_bounded.
Admitted.


Definition LowerIntegral (a b : R) (f : R -> R) : R :=
  real (Lub_Rbar (IsLowerIntegral a b f)).

Definition UpperIntegral (a b : R) (f : R -> R) : R :=
  real (Glb_Rbar (IsUpperIntegral a b f)).

Theorem Integrable_of_Upper_Lower {a b : R} {f : R -> R} {M : R}
    (H : BoundedByOn a b f M) (Hab : a <= b) (r : R)
    (HL : LowerIntegral a b f = r) (HR : UpperIntegral a b f = r) :
  Riemann_integrable f a b.
Proof.
  intro ε.
  (* Get two step functions that are both within ε/2 of r
     phi is their mean
     psi is their difference

     This must be done in term mode because it will be unfolded in the next step.
   *)
Admitted.

Theorem Integral_of_Upper_Lower {a b : R} {f : R -> R} {M : R}
    (H : BoundedByOn a b f M) (Hab : a <= b) (r : R) (HL : LowerIntegral a b f = r)
    (HR : UpperIntegral a b f = r) :
  RiemannInt (Integrable_of_Upper_Lower H Hab r HL HR) = r.
Proof.
  unfold RiemannInt.
  case (RiemannInt_exists (Integrable_of_Upper_Lower H Hab r HL HR) RinvN RinvN_cv).
  intros x Hcvg.
  eapply (UL_sequence _ _ _ Hcvg); clear Hcvg x.
  intros ε Hε.
  unfold phi_sequence.
Admitted.


(* NB. there are at least two different definitions for the LUB depending on the domain of the function.
Check Lub_Rbar.
Check Rbar_lub.
Check Rbar_glb_le_lub.
*)



(* Next up: Define the double lower sums, double upper sums, double integrals, and I.

  It's okay if these double integrals are unable to link with Coquelicot because they will only be used
  in the process of proving Fubini. *)


Structure DoubleStepFun (a_x b_x a_y b_y : R) := {
  stepX : StepFun a_x b_x;
  stepY : StepFun a_y b_y
}.

(* The double step function is the sum of the x and y step functions *)
Definition DoubleStepFun_eval {a_x b_x a_y b_y : R} (D : DoubleStepFun a_x b_x a_y b_y) (x y : R) : R :=
  stepX _ _ _ _ D x + stepY _ _ _ _ D y.

(* Lower sum *)

(* Double integral: Supremum of lower sums of all double step functions. *)
Print RiemannInt_SF.
Check subdivision_val.
Check subdivision.
Check (seq.seq R).








(*
Theorem IsLowerIntegralBound {a b : R} {f : R -> R} {M : R}
  (H : BoundedByOn a b f M) : bound (IsLowerIntegral a b f).
Proof.
  exists (M * (Rmax a b - Rmin a b)). intro r.
  unfold IsLowerIntegral.
  intros [ϕ [LSF Heq]]; rewrite <-Heq.
  have Hab : a <= b by admit.
  etransitivity.
  { apply (StepFun_P37 _ (UpperStepFun_trivial H) Hab).
    intros x Haxb.
    unfold UpperStepFun_trivial; simpl.
    unfold fct_cte.
    unfold BoundedByOn in H.
    unfold LowerStepFun in LSF.
    have HMX : Rmin a b <= x <= Rmax a b by admit.
    etransitivity.
    { apply LSF. apply HMX. }
    etransitivity.
    { apply RRle_abs. }
    { apply H. apply HMX. }
  }
  unfold UpperStepFun_trivial.
  rewrite StepFun_P18.
  (* true *)
Admitted.


Theorem IsLowerIntegralExists {a b : R} {f : R -> R} {M : R}
    (H : BoundedByOn a b f M) : ∃ x : R, IsLowerIntegral a b f x.
Proof.
  exists (-M * (Rmax a b - Rmin a b)).
  exists {| fe := fct_cte (-M); pre := StepFun_P4 a b _ |}.
  split.
  { intros t Hat.
    rewrite /fct_cte//=.
    (* By apply H *)
    admit. }
  { rewrite StepFun_P18.
    admit. }
Admitted.


Locate is_lub.
Search "sup".
Locate Lub.Rbar_is_lub.

Definition UpperIntegral (a b : R) (f : R -> R) : R. Admitted.

*)

(* is_RInt_SF *)


(*
Definition Riemann_integrable (f:R -> R) (a b:R) : Type :=
  forall eps:posreal,
    { phi:StepFun a b &
      { psi:StepFun a b |
        (forall t:R,
          Rmin a b <= t <= Rmax a b -> Rabs (f t - phi t) <= psi t) /\
        Rabs (RiemannInt_SF psi) < eps } }.

Definition phi_sequence (un:nat -> posreal) (f:R -> R)
  (a b:R) (pr:Riemann_integrable f a b) (n:nat) :=
  projT1 (pr (un n)).

Lemma RiemannInt_exists :
  forall (f:R -> R) (a b:R) (pr:Riemann_integrable f a b)
    (un:nat -> posreal),
    Un_cv un 0 ->
    { l:R | Un_cv (fun N:nat => RiemannInt_SF (phi_sequence un pr N)) l }.

Definition RiemannInt (f:R -> R) (a b:R) (pr:Riemann_integrable f a b) : R :=
  let (a,_) := RiemannInt_exists pr RinvN RinvN_cv in a.
*)

(*

Definition UpperStepFun_trivial {a b : R} {f : R -> R} {M : R}
  (H : BoundedByOn a b f M) : StepFun a b := {| fe := fct_cte M; pre := StepFun_P4 a b M |}.
(* Example: Constructing a stdlib step function by hand *)
Definition StepSquare (a b v x : R) : R :=
  if bool_decide (x < Rmin a b) then 0 else
  if bool_decide (Rmax a b < x) then 0 else
  v.

Definition UpperStepFun_trivial ...
refine (mkStepFun (fe := StepSquare a b M) _).
Proof.
  exists [:: Rmin a b; Rmax a b].
  exists [:: M].
  constructor. { apply sorted_compat. simpl; split; auto. apply  Rminmax.}
  constructor. { simpl. reflexivity. }
  constructor. { simpl. reflexivity. }
  constructor. { simpl. reflexivity. }
  simpl.
  intros i Hi.
  destruct i as [|[|]].
  all: unfold constant_D_eq; unfold open_interval; simpl; intros x Hx; unfold StepSquare; simpl.
  all: repeat (case_bool_decide; try lra).
Defined.
*)
*)
