/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex estimating-sequence recurrences on real inner-product spaces.

Sampled owner-style declarations in this domain:
* `strongConvexEstimatingFunction` in `Lemma_2_8`, the chapter owner recurrence whose centered
  quadratic coefficients are identified here;
* `AffineMap.lineMap` in mathlib, the canonical affine-combination owner for updating one function
  stage from the previous stage and the regularized lower model;
* `firstOrderTaylorModelAt` in `Definition_1_4_17`, the canonical owner of the affine lower model
  `x ↦ f(y_k) + ⟪∇ f(y_k), x - y_k⟫`;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the canonical centered quadratic
  owner `x ↦ f x + (δ / 2) ‖x - x₀‖²`.

Best owner abstraction:
* source-facing: `estimatingSequenceCurvature`, `estimatingSequenceCenter`,
  `estimatingSequenceValue`, and the centered quadratic theorem of Lemma 2.9 for
  `strongConvexEstimatingFunction`;
* core/canonical: `strongConvexEstimatingFunction`, `quadraticallyRegularizedObjective`,
  `firstOrderTaylorModelAt`, and `lineMap`;
* bridge/view: the private recurrence-level centered formula used to derive the owner theorem.

Primitive data:
* the initial centered data `(φ₀*, γ₀, v₀)`;
* the recurrence inputs `α`, `y`, and `∇ f (y_k)`;
* the owner estimating-sequence recurrence `strongConvexEstimatingFunction`.

Derived API:
* the recursive coefficient sequences `estimatingSequenceCurvature`,
  `estimatingSequenceCenter`, and `estimatingSequenceValue`;
* the source-domain hypothesis that each successor curvature `γ_{k+1}` is nonzero, used only by
  centered-quadratic proofs rather than by the recursive data themselves;
* the centered quadratic identity for the owner recurrence from `Lemma_2_8`.

This file is `source-facing`: it keeps the textbook recursive coefficients `γ_k`, `v_k`,
and `φ_k^*`. Its owner ambient space is the intrinsic complete real inner-product space already
used by `Lemma_2_8`, not the coordinate presentation `EuclideanSpace ℝ (Fin n)`. -/

/-- The curvature sequence `γ_k` in the centered quadratic form of Lemma 2.9. -/
def estimatingSequenceCurvature
    (μ γ0 : ℝ)
    (α : ℕ → ℝ) :
    ℕ → ℝ
  | 0 => γ0
  | k + 1 =>
      (1 - α k) * estimatingSequenceCurvature μ γ0 α k + α k * μ

/-- The curvature sequence starts from the initial curvature `γ₀`. -/
@[simp] theorem estimatingSequenceCurvature_zero
    (μ γ0 : ℝ)
    (α : ℕ → ℝ) :
    estimatingSequenceCurvature μ γ0 α 0 = γ0 := rfl

/-- The center sequence `v_k` in the centered quadratic form of Lemma 2.9. The recurrence itself
is defined for every coefficient sequence; the later centered-quadratic proofs assume the
successor curvatures are nonzero when dividing by `γ_{k+1}`. -/
def estimatingSequenceCenter
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ γ0 : ℝ)
    (v0 : E) :
    ℕ → E
  | 0 => v0
  | k + 1 =>
      let gammaCurr := estimatingSequenceCurvature μ γ0 α k
      let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
      let yk := y k
      let gk := ∇ f yk
      (1 / gammaNext) •
        (((1 - α k) * gammaCurr) • estimatingSequenceCenter f α y μ γ0 v0 k +
          (α k * μ) • yk -
          α k • gk)

/-- The center sequence starts from the initial center `v₀`. -/
@[simp] theorem estimatingSequenceCenter_zero
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ γ0 : ℝ)
    (v0 : E) :
    estimatingSequenceCenter f α y μ γ0 v0 0 = v0 := rfl

/-- The scalar sequence `φ_k^*` in the centered quadratic form of Lemma 2.9. The recurrence itself
is defined for every coefficient sequence; the later centered-quadratic proofs assume the
successor curvatures are nonzero when dividing by `γ_{k+1}`. -/
def estimatingSequenceValue
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ φ0Star γ0 : ℝ)
    (v0 : E) :
    ℕ → ℝ
  | 0 => φ0Star
  | k + 1 =>
      let gammaCurr := estimatingSequenceCurvature μ γ0 α k
      let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
      let vCurr := estimatingSequenceCenter f α y μ γ0 v0 k
      let yk := y k
      let gk := ∇ f yk
      (1 - α k) * estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
        α k * f yk -
        (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
        (α k * (1 - α k) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk))

/-- The scalar sequence starts from the initial value `φ₀*`. -/
@[simp] theorem estimatingSequenceValue_zero
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ φ0Star γ0 : ℝ)
    (v0 : E) :
    estimatingSequenceValue f α y μ φ0Star γ0 v0 0 = φ0Star := rfl

/-- The curvature sequence satisfies its defining successor recursion. -/
-- Proof sketch: unfold `estimatingSequenceCurvature` at index `k + 1`.
theorem estimatingSequenceCurvature_succ
    (μ γ0 : ℝ)
    (α : ℕ → ℝ)
    (k : ℕ) :
    estimatingSequenceCurvature μ γ0 α (k + 1) =
      (1 - α k) * estimatingSequenceCurvature μ γ0 α k + α k * μ := rfl

/-- The center sequence satisfies its defining successor recursion. -/
-- Proof sketch: unfold `estimatingSequenceCenter` at index `k + 1`.
theorem estimatingSequenceCenter_succ
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ γ0 : ℝ)
    (v0 : E)
    (k : ℕ) :
    estimatingSequenceCenter f α y μ γ0 v0 (k + 1) =
      let gammaCurr := estimatingSequenceCurvature μ γ0 α k
      let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
      let yk := y k
      let gk := ∇ f yk
      (1 / gammaNext) •
        (((1 - α k) * gammaCurr) • estimatingSequenceCenter f α y μ γ0 v0 k +
          (α k * μ) • yk -
          α k • gk) := rfl

/-- The scalar sequence satisfies its defining successor recursion. -/
-- Proof sketch: unfold `estimatingSequenceValue` at index `k + 1`.
theorem estimatingSequenceValue_succ
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ φ0Star γ0 : ℝ)
    (v0 : E)
    (k : ℕ) :
    estimatingSequenceValue f α y μ φ0Star γ0 v0 (k + 1) =
      let gammaCurr := estimatingSequenceCurvature μ γ0 α k
      let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
      let vCurr := estimatingSequenceCenter f α y μ γ0 v0 k
      let yk := y k
      let gk := ∇ f yk
      (1 - α k) * estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
        α k * f yk -
        (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
        (α k * (1 - α k) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) := rfl

/- Recenter a centered quadratic about an intermediate basepoint. This algebraic bridge is the
shared quadratic-expansion owner used by the chapter's centered-quadratic recurrence proofs. -/
-- Proof sketch: write `x - c = (x - y) + (y - c)` and expand the square with
-- `norm_add_sq_real`.
omit [CompleteSpace E] in
theorem centered_quadratic_expand_about_point
    (γ : ℝ)
    (x y c : E) :
    (γ / 2) * ‖x - c‖ ^ (2 : ℕ) =
      (γ / 2) * ‖y - c‖ ^ (2 : ℕ) +
        γ * inner ℝ (x - y) (y - c) +
        (γ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  -- Recenter the quadratic at `y`, which is the source proof's evaluation point.
  have hdecomp : x - c = (x - y) + (y - c) := by
    abel
  rw [hdecomp, norm_add_sq_real]
  ring

/-- Helper for Lemma 2.9: rewrite the center update relative to the basepoint `y k`. -/
-- Proof sketch: subtract `y k` from the explicit recursion for `v_{k+1}` and use the curvature
-- recursion to absorb the `y k` coefficient.
private theorem estimatingSequenceCenter_succ_sub_eq
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ γ0 : ℝ)
    (v0 : E)
    (hγ : ∀ k, estimatingSequenceCurvature μ γ0 α (k + 1) ≠ 0)
    (k : ℕ) :
    estimatingSequenceCenter f α y μ γ0 v0 (k + 1) - y k =
      (1 / estimatingSequenceCurvature μ γ0 α (k + 1)) •
        (((1 - α k) * estimatingSequenceCurvature μ γ0 α k) •
            (estimatingSequenceCenter f α y μ γ0 v0 k - y k) -
          α k • ∇ f (y k)) := by
  -- Cancel the copied basepoint term by rewriting `y k` through the nonzero next curvature.
  let gammaCurr := estimatingSequenceCurvature μ γ0 α k
  let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
  let vCurr := estimatingSequenceCenter f α y μ γ0 v0 k
  let yk := y k
  let gk := ∇ f yk
  have hgammaNext_ne : gammaNext ≠ 0 := by simpa [gammaNext] using hγ k
  have hyk : (1 / gammaNext) • (gammaNext • yk) = yk := by
    rw [smul_smul, one_div, inv_mul_cancel₀ hgammaNext_ne, one_smul]
  calc
    estimatingSequenceCenter f α y μ γ0 v0 (k + 1) - y k
        = (1 / gammaNext) •
            (((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk) - yk := by
              simp [estimatingSequenceCenter_succ, gammaCurr, gammaNext, vCurr, yk, gk]
    _ = (1 / gammaNext) •
          (((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk) -
            (1 / gammaNext) • (gammaNext • yk) := by rw [hyk]
    _ = (1 / gammaNext) •
          ((((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk) - gammaNext • yk) := by
            conv_rhs => rw [smul_sub]
    _ = (1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk) := by
      congr 1
      change
        ((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk -
            (((1 - α k) * gammaCurr + α k * μ) • yk) =
          ((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk
      calc
        ((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk -
            (((1 - α k) * gammaCurr + α k * μ) • yk)
            =
            ((1 - α k) * gammaCurr) • vCurr +
              ((α k * μ) • yk - (((1 - α k) * gammaCurr + α k * μ) • yk)) -
              α k • gk := by
                abel
        _ =
            ((1 - α k) * gammaCurr) • vCurr +
              (-(((1 - α k) * gammaCurr) • yk)) -
              α k • gk := by
                rw [add_smul]
                abel
        _ = ((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk := by
          rw [smul_sub]
          abel

/-- Helper for Lemma 2.9: the updated center gives the required linear term after expanding the
centered quadratic about `y k`. -/
-- Proof sketch: negate the previous center-difference formula, move the scalar inside the inner
-- product, and cancel the reciprocal with the nonzero next curvature.
private theorem estimatingSequenceCenter_succ_cross_term_eq
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ γ0 : ℝ)
    (v0 : E)
    (hγ : ∀ k, estimatingSequenceCurvature μ γ0 α (k + 1) ≠ 0)
    (k : ℕ)
    (x : E) :
    estimatingSequenceCurvature μ γ0 α (k + 1) *
        inner ℝ (x - y k) (y k - estimatingSequenceCenter f α y μ γ0 v0 (k + 1)) =
      (1 - α k) * estimatingSequenceCurvature μ γ0 α k *
        inner ℝ (x - y k) (y k - estimatingSequenceCenter f α y μ γ0 v0 k) +
        α k * inner ℝ (∇ f (y k)) (x - y k) := by
  -- Route correction: the linear term is matched algebraically from the explicit center update,
  -- not by differentiating the recurrence.
  let gammaCurr := estimatingSequenceCurvature μ γ0 α k
  let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
  let vCurr := estimatingSequenceCenter f α y μ γ0 v0 k
  let vNext := estimatingSequenceCenter f α y μ γ0 v0 (k + 1)
  let yk := y k
  let gk := ∇ f yk
  have hgammaNext_ne : gammaNext ≠ 0 := by simpa [gammaNext] using hγ k
  have hsub :
      yk - vNext =
        (1 / gammaNext) • (((1 - α k) * gammaCurr) • (yk - vCurr) + α k • gk) := by
    calc
      yk - vNext = -(vNext - yk) := by abel
      _ = -((1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)) := by
            rw [estimatingSequenceCenter_succ_sub_eq f α y μ γ0 v0 hγ k]
      _ = (1 / gammaNext) • (((1 - α k) * gammaCurr) • (yk - vCurr) + α k • gk) := by
            simp [sub_eq_add_neg, add_comm]
  calc
    gammaNext * inner ℝ (x - yk) (yk - vNext)
        = gammaNext *
            inner ℝ (x - yk)
              ((1 / gammaNext) • (((1 - α k) * gammaCurr) • (yk - vCurr) + α k • gk)) := by
                rw [hsub]
    _ =
        (1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
          α k * inner ℝ gk (x - yk) := by
            rw [real_inner_smul_right, inner_add_right, real_inner_smul_right,
              real_inner_smul_right, real_inner_comm (x - yk) gk]
            field_simp [hgammaNext_ne]

/-- Helper for Lemma 2.9: the new center's squared distance to `y k` matches the scalar recursion
for `φ_{k+1}^*`. -/
-- Proof sketch: substitute the center-difference formula, scale out the nonzero next curvature, and
-- expand the remaining norm square with `norm_sub_sq_real`.
private theorem estimatingSequenceCenter_succ_norm_sq_eq
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ γ0 : ℝ)
    (v0 : E)
    (hγ : ∀ k, estimatingSequenceCurvature μ γ0 α (k + 1) ≠ 0)
    (k : ℕ) :
    (estimatingSequenceCurvature μ γ0 α (k + 1) / 2) *
        ‖estimatingSequenceCenter f α y μ γ0 v0 (k + 1) - y k‖ ^ (2 : ℕ) =
      (((1 - α k) ^ (2 : ℕ) * estimatingSequenceCurvature μ γ0 α k ^ (2 : ℕ)) /
          (2 * estimatingSequenceCurvature μ γ0 α (k + 1))) *
        ‖estimatingSequenceCenter f α y μ γ0 v0 k - y k‖ ^ (2 : ℕ) -
        (α k * (1 - α k) * estimatingSequenceCurvature μ γ0 α k /
            estimatingSequenceCurvature μ γ0 α (k + 1)) *
          inner ℝ (∇ f (y k)) (estimatingSequenceCenter f α y μ γ0 v0 k - y k) +
        (α k ^ (2 : ℕ) / (2 * estimatingSequenceCurvature μ γ0 α (k + 1))) *
          ‖∇ f (y k)‖ ^ (2 : ℕ) := by
  let gammaCurr := estimatingSequenceCurvature μ γ0 α k
  let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
  let vCurr := estimatingSequenceCenter f α y μ γ0 v0 k
  let yk := y k
  let gk := ∇ f yk
  have hgammaNext_ne : gammaNext ≠ 0 := by simpa [gammaNext] using hγ k
  have hscaled :
      (gammaNext / 2) *
          ‖(1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)‖ ^ (2 : ℕ) =
        (1 / (2 * gammaNext)) *
          ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) := by
    -- The nonzero next curvature converts the scaled norm square into the expected scalar factor.
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp [hgammaNext_ne]
  have hexpand :
      ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) =
        ((1 - α k) * gammaCurr) ^ (2 : ℕ) * ‖vCurr - yk‖ ^ (2 : ℕ) -
          2 * ((1 - α k) * gammaCurr) * α k * inner ℝ (vCurr - yk) gk +
          α k ^ (2 : ℕ) * ‖gk‖ ^ (2 : ℕ) := by
    -- This is exactly the textbook expansion of equation `(2.2.9)`.
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  calc
    (estimatingSequenceCurvature μ γ0 α (k + 1) / 2) *
        ‖estimatingSequenceCenter f α y μ γ0 v0 (k + 1) - y k‖ ^ (2 : ℕ)
        =
        (gammaNext / 2) *
          ‖(1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)‖ ^ (2 : ℕ) := by
            simpa [gammaNext, gammaCurr, vCurr, yk, gk] using
              congrArg
                (fun z : E ↦ (estimatingSequenceCurvature μ γ0 α (k + 1) / 2) * ‖z‖ ^ (2 : ℕ))
                (estimatingSequenceCenter_succ_sub_eq f α y μ γ0 v0 hγ k)
    _ = (1 / (2 * gammaNext)) *
          ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) := hscaled
    _ =
        (1 / (2 * gammaNext)) *
          (((1 - α k) * gammaCurr) ^ (2 : ℕ) * ‖vCurr - yk‖ ^ (2 : ℕ) -
            2 * ((1 - α k) * gammaCurr) * α k * inner ℝ (vCurr - yk) gk +
            α k ^ (2 : ℕ) * ‖gk‖ ^ (2 : ℕ)) := by rw [hexpand]
    _ =
        (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
          ‖vCurr - yk‖ ^ (2 : ℕ) -
          (α k * (1 - α k) * gammaCurr / gammaNext) * inner ℝ gk (vCurr - yk) +
          (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) := by
            rw [real_inner_comm (vCurr - yk) gk]
            ring

-- Internal bridge: any recurrence with the same owner zero/successor data has the same centered
-- quadratic coefficients.
-- Proof sketch: argue by induction on `k`. The base case unfolds the initial quadratic
-- `quadraticallyRegularizedObjective (fun _ ↦ φ0Star) γ0 v0`. For the induction step, rewrite
-- the owner recurrence with `lineMap_apply_module`, then unfold
-- `quadraticallyRegularizedObjective` and `firstOrderTaylorModelAt`, substitute the centered
-- quadratic formula for `φₖ`, and identify the new centered coefficients with the recursive
-- formulas defining `estimatingSequenceValue`, `estimatingSequenceCurvature`, and
-- `estimatingSequenceCenter`.
private theorem estimatingSequence_eq_canonicalQuadratic_of_recurrence
    (f : E → ℝ)
    (φ : ℕ → E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ φ0Star γ0 : ℝ)
    (v0 : E)
    (hφ0 :
      φ 0 = quadraticallyRegularizedObjective (fun _ ↦ φ0Star) γ0 v0)
    (hrec : ∀ k,
      φ (k + 1) =
        lineMap
          (φ k)
          (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k))
          (α k))
    (hγ : ∀ k, estimatingSequenceCurvature μ γ0 α (k + 1) ≠ 0)
    (k : ℕ) :
    φ k =
      quadraticallyRegularizedObjective
        (fun _ ↦ estimatingSequenceValue f α y μ φ0Star γ0 v0 k)
        (estimatingSequenceCurvature μ γ0 α k)
        (estimatingSequenceCenter f α y μ γ0 v0 k) := by
  ext x
  induction k generalizing x with
  | zero =>
      -- The initial stage is exactly the given centered quadratic.
      simpa [quadraticallyRegularizedObjective_apply] using
        congrArg (fun ψ : E → ℝ ↦ ψ x) hφ0
  | succ k hk =>
      -- Route correction: match the source proof by expanding about `y k` and completing the
      -- square algebraically, rather than introducing derivative-based obligations.
      let gammaCurr := estimatingSequenceCurvature μ γ0 α k
      let gammaNext := estimatingSequenceCurvature μ γ0 α (k + 1)
      let vCurr := estimatingSequenceCenter f α y μ γ0 v0 k
      let vNext := estimatingSequenceCenter f α y μ γ0 v0 (k + 1)
      let yk := y k
      let gk := ∇ f yk
      have hrecx :
          φ (k + 1) x =
            (1 - α k) *
                (estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
                  (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
              α k *
                (f yk + inner ℝ gk (x - yk) + (μ / 2) * ‖x - yk‖ ^ (2 : ℕ)) := by
        -- Evaluate the function-space recurrence at `x` and insert the induction hypothesis.
        simpa [lineMap_apply_module, quadraticallyRegularizedObjective_apply,
          firstOrderTaylorModelAt_apply, gammaCurr, yk, gk, hk x] using
          congrArg (fun ψ : E → ℝ ↦ ψ x) (hrec k)
      have hgammaNext_ne : gammaNext ≠ 0 := by
        simpa [gammaNext] using hγ k
      have hcurv :
          gammaNext = (1 - α k) * gammaCurr + α k * μ := by
        simpa [gammaCurr, gammaNext] using estimatingSequenceCurvature_succ μ γ0 α k
      have hvalue :
          estimatingSequenceValue f α y μ φ0Star γ0 v0 (k + 1) =
            (1 - α k) * estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
              α k * f yk -
              (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
              (α k * (1 - α k) * gammaCurr / gammaNext) *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) := by
        simpa [gammaCurr, gammaNext, vCurr, yk, gk] using
          estimatingSequenceValue_succ f α y μ φ0Star γ0 v0 k
      have hcross :
          gammaNext * inner ℝ (x - yk) (yk - vNext) =
            (1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
              α k * inner ℝ gk (x - yk) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk] using
          estimatingSequenceCenter_succ_cross_term_eq f α y μ γ0 v0 hγ k x
      have hnorm :
          (gammaNext / 2) * ‖yk - vNext‖ ^ (2 : ℕ) =
            (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
              ‖vCurr - yk‖ ^ (2 : ℕ) -
              (α k * (1 - α k) * gammaCurr / gammaNext) * inner ℝ gk (vCurr - yk) +
              (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk, norm_sub_rev] using
          estimatingSequenceCenter_succ_norm_sq_eq f α y μ γ0 v0 hγ k
      -- Expand the previous and next centered quadratics about the common basepoint `y k`.
      rw [hrecx, quadraticallyRegularizedObjective_apply, hvalue,
        centered_quadratic_expand_about_point gammaCurr x yk vCurr,
        centered_quadratic_expand_about_point gammaNext x yk vNext, hcross, hnorm]
      -- The remaining goal is scalar coefficient matching using the recursive formulas.
      let commonForm :=
        (1 - α k) * estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
          α k * f yk +
          (1 - α k) * (gammaCurr / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) +
          ((1 - α k) * gammaCurr) * inner ℝ (x - yk) (yk - vCurr) +
          ((1 - α k) * (gammaCurr / 2) + α k * (μ / 2)) * ‖x - yk‖ ^ (2 : ℕ) +
          α k * inner ℝ gk (x - yk)
      have hconstCoeff :
          α k * (1 - α k) * gammaCurr / gammaNext * (μ / 2) +
            (1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext) =
            (1 - α k) * (gammaCurr / 2) := by
        field_simp [hgammaNext_ne]
        rw [hcurv]
        ring
      have hxCoeff :
          gammaNext / 2 = (1 - α k) * (gammaCurr / 2) + α k * (μ / 2) := by
        nlinarith [hcurv]
      have hleft :
          (1 - α k) *
              (estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
                (gammaCurr / 2 * ‖yk - vCurr‖ ^ (2 : ℕ) +
                  gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  gammaCurr / 2 * ‖x - yk‖ ^ (2 : ℕ))) +
            α k * (f yk + inner ℝ gk (x - yk) + μ / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm := by
        simp [commonForm]
        ring
      have hright :
          (1 - α k) * estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
              α k * f yk -
              α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
              α k * (1 - α k) * gammaCurr / gammaNext *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
            ((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext) *
                  ‖vCurr - yk‖ ^ (2 : ℕ) -
                α k * (1 - α k) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
              ((1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                α k * inner ℝ gk (x - yk)) +
              gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm := by
        calc
          (1 - α k) * estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
                α k * f yk -
                α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
                α k * (1 - α k) * gammaCurr / gammaNext *
                  ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
              ((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext) *
                    ‖vCurr - yk‖ ^ (2 : ℕ) -
                  α k * (1 - α k) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                  α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
                ((1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  α k * inner ℝ gk (x - yk)) +
                gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ))
              =
              (1 - α k) * estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
                α k * f yk +
                (α k * (1 - α k) * gammaCurr / gammaNext * (μ / 2) +
                    (1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                  ‖yk - vCurr‖ ^ (2 : ℕ) +
                ((1 - α k) * gammaCurr) * inner ℝ (x - yk) (yk - vCurr) +
                (gammaNext / 2) * ‖x - yk‖ ^ (2 : ℕ) +
                α k * inner ℝ gk (x - yk) := by
                  simp [norm_sub_rev]
                  ring
          _ = commonForm := by
            rw [hconstCoeff, hxCoeff]
      simpa [quadraticallyRegularizedObjective_apply] using hleft.trans hright.symm

/-- Lemma 2.9: if each successor curvature `γ_{k+1}` is nonzero, then the strong-convex
estimating sequence from `Lemma_2_8` stays in centered quadratic form. Starting from the centered
quadratic model
`quadraticallyRegularizedObjective (fun _ ↦ φ0Star) γ0 v0`, every stage of
`strongConvexEstimatingFunction μ f ... y α` is exactly the owner quadratic
`quadraticallyRegularizedObjective (fun _ ↦ φ_k^*) γ_k v_k`, where `φ_k^*`, `γ_k`, and `v_k`
are `estimatingSequenceValue`, `estimatingSequenceCurvature`, and
`estimatingSequenceCenter`. -/
theorem estimatingSequence_eq_canonicalQuadratic
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ φ0Star γ0 : ℝ)
    (v0 : E)
    (hγ : ∀ k, estimatingSequenceCurvature μ γ0 α (k + 1) ≠ 0)
    (k : ℕ) :
    strongConvexEstimatingFunction μ f
        (quadraticallyRegularizedObjective (fun _ ↦ φ0Star) γ0 v0)
        y α k =
      quadraticallyRegularizedObjective
        (fun _ ↦ estimatingSequenceValue f α y μ φ0Star γ0 v0 k)
        (estimatingSequenceCurvature μ γ0 α k)
        (estimatingSequenceCenter f α y μ γ0 v0 k) := by
  simpa using
    estimatingSequence_eq_canonicalQuadratic_of_recurrence
      f
      (strongConvexEstimatingFunction μ f
        (quadraticallyRegularizedObjective (fun _ ↦ φ0Star) γ0 v0)
        y α)
      α
      y
      μ
      φ0Star
      γ0
      v0
      rfl
      (strongConvexEstimatingFunction_succ μ f
        (quadraticallyRegularizedObjective (fun _ ↦ φ0Star) γ0 v0)
        y α)
      hγ
      k

/-- Companion evaluation formula for Lemma 2.9: the owner equality unfolds to the displayed
centered quadratic expression at each point `x`. -/
theorem estimatingSequence_eq_canonicalQuadratic_apply
    (f : E → ℝ)
    (α : ℕ → ℝ)
    (y : ℕ → E)
    (μ φ0Star γ0 : ℝ)
    (v0 : E)
    (hγ : ∀ k, estimatingSequenceCurvature μ γ0 α (k + 1) ≠ 0)
    (k : ℕ) (x : E) :
    strongConvexEstimatingFunction μ f
        (quadraticallyRegularizedObjective (fun _ ↦ φ0Star) γ0 v0)
        y α k x =
      estimatingSequenceValue f α y μ φ0Star γ0 v0 k +
        (estimatingSequenceCurvature μ γ0 α k / 2) *
          ‖x - estimatingSequenceCenter f α y μ γ0 v0 k‖ ^ (2 : ℕ) := by
  simpa [quadraticallyRegularizedObjective_apply] using
    congrFun
      (estimatingSequence_eq_canonicalQuadratic f α y μ φ0Star γ0 v0 hγ k)
      x

end
