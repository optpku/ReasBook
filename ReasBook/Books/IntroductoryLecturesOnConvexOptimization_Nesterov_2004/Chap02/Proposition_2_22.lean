/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_9

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap
open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: simple-set estimating-sequence recurrences for projected-gradient lower models.

Sampled owner declarations in this domain:
* `gradientMapping` and `reducedGradient` from `Definition_2_35_1`, which own the projected-step
  point and reduced gradient;
* `quadraticallyRegularizedObjective` from `Definition_1_4_17.lean`, which owns the centered
  quadratic regularization added to each lower model;
* `lineMap` from `AffineMap`, which owns the affine-combination update of one stage from the
  previous stage and the new lower model;
* `estimatingSequenceCurvature` and `estimatingSequenceCenter` from `Lemma_2_9`, which already
  own the universal curvature and Euclidean center recurrences for this centered-quadratic
  pattern;
* `centered_quadratic_expand_about_point` from `Lemma_2_9`, the chapter owner for the algebraic
  recentering identity used when completing the square.

Best owner abstraction:
* source-facing: `simpleSetEstimatingModel`, `simpleSetEstimatingFunction`,
  `simpleSetEstimatingCenter`, and `simpleSetEstimatingValue`;
* core/canonical: `gradientMapping`, `reducedGradient`, `quadraticallyRegularizedObjective`,
  `lineMap`, and `estimatingSequenceCurvature`;
* bridge/view: the model evaluation formula, the zero/successor equations, and the canonical
  quadratic identity.

Primitive data:
* the feasible set `Q` with its nonempty / closed / convex structure;
* the projected-gradient stage data derived from `gradientMapping` and `reducedGradient`;
* the source-facing recursive objects `simpleSetEstimatingFunction`,
  `simpleSetEstimatingCenter`, and `simpleSetEstimatingValue`.

Derived API:
* the displayed formula for the stagewise lower model;
* function-level zero/successor equations for the recursive functions;
* the source-domain hypothesis that each successor curvature `γ_{k+1}` is nonzero, used only in
  the cancellation lemmas and canonical quadratic theorem;
* the canonical quadratic identity of Proposition 2.22.

Accordingly, this file keeps the source-facing simple-set objects, but reuses the owner
curvature recurrence from `Lemma_2_9` and the owner affine/quadratic combinators instead of
duplicating them as parallel local formulas. -/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ)

local notation "xProj" =>
  fun k : ℕ ↦ x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y k)

local notation "gProj" =>
  fun k : ℕ ↦ g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y k)

local notation "gamma" => estimatingSequenceCurvature μ gamma0 α

/-- The lower quadratic model built directly from the projected-gradient point
`x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y_k)` and reduced gradient
`g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y_k)` at stage `k`. -/
def simpleSetEstimatingModel
    (k : ℕ) :
    E → ℝ :=
  let yk := y k
  let xQk := xProj k
  let gQk := gProj k
  quadraticallyRegularizedObjective
    (fun x ↦
      f xQk +
        (1 / (2 * L)) * ‖gQk‖ ^ (2 : ℕ) +
        inner ℝ gQk (x - yk))
    μ
    yk

/-- Evaluating the simple-set lower model recovers the displayed quadratic formula. -/
@[simp] theorem simpleSetEstimatingModel_apply
    (k : ℕ) (x : E) :
    simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x =
      let yk := y k
      let xQk := xProj k
      let gQk := gProj k
      f xQk +
        (1 / (2 * L)) * ‖gQk‖ ^ (2 : ℕ) +
        inner ℝ gQk (x - yk) +
        (μ / 2) * ‖x - yk‖ ^ (2 : ℕ) := rfl

/-- The recursively defined estimating-sequence functions for the simple-set method. -/
def simpleSetEstimatingFunction
    :
    ℕ → E → ℝ
  | 0 => quadraticallyRegularizedObjective (fun _ ↦ f x0) gamma0 x0
  | k + 1 =>
      lineMap
        (simpleSetEstimatingFunction k)
        (simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k)
        (α k)

/-- The center sequence `v_k` in the canonical quadratic representation. The recurrence itself is
defined for every coefficient sequence; the later centered-quadratic proofs assume the successor
curvatures are nonzero when dividing by `γ_{k+1}`. -/
def simpleSetEstimatingCenter
    :
    ℕ → E
  | 0 => x0
  | k + 1 =>
      let gammaCurr := gamma k
      let gammaNext := gamma (k + 1)
      let yk := y k
      let gQk := gProj k
      (1 / gammaNext) •
        (((1 - α k) * gammaCurr) •
            simpleSetEstimatingCenter k +
          (α k * μ) • yk -
          α k • gQk)

/-- The scalar term `φ_k^*` in the canonical quadratic representation. The recurrence itself is
defined for every coefficient sequence; the later centered-quadratic proofs assume the successor
curvatures are nonzero when dividing by `γ_{k+1}`. -/
def simpleSetEstimatingValue
    :
    ℕ → ℝ
  | 0 => f x0
  | k + 1 =>
      let gammaNext := gamma (k + 1)
      let gammaCurr := gamma k
      let yk := y k
      let vCurr := simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      let gCurr := gProj k
      let xQCurr := xProj k
      (1 - α k) * simpleSetEstimatingValue k +
        α k * f xQCurr +
        (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gCurr‖ ^ (2 : ℕ) +
        (α k * (1 - α k) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gCurr (vCurr - yk))

local notation "phi" =>
  simpleSetEstimatingFunction Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α

/-- The estimating-sequence functions start from the initial quadratic model at `x0`. -/
-- Proof sketch: unfold `simpleSetEstimatingFunction` at index `0`.
@[simp] theorem simpleSetEstimatingFunction_zero
    :
    phi 0 =
      quadraticallyRegularizedObjective (fun _ ↦ f x0) gamma0 x0 := rfl

/-- Evaluating the initial simple-set estimating function recovers the displayed quadratic
formula. -/
@[simp] theorem simpleSetEstimatingFunction_zero_apply
    (x : E) :
    phi 0 x =
      f x0 + (gamma0 / 2) * ‖x - x0‖ ^ (2 : ℕ) := rfl

/-- The estimating-sequence functions satisfy their defining affine update with the simple-set
lower model. -/
-- Proof sketch: unfold `simpleSetEstimatingFunction` at index `k + 1`.
theorem simpleSetEstimatingFunction_succ
    (k : ℕ) :
    phi (k + 1) =
      lineMap
        (phi k)
        (simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k)
        (α k) := rfl

/-- Evaluating the successor stage recovers the textbook affine update formula. -/
@[simp] theorem simpleSetEstimatingFunction_succ_apply
    (k : ℕ) (x : E) :
    phi (k + 1) x =
      (1 - α k) * phi k x +
        α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
  simpa [lineMap_apply_module] using
    congrFun
      (simpleSetEstimatingFunction_succ
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k)
      x

/-- The center sequence starts from the initial point `x0`. -/
-- Proof sketch: unfold `simpleSetEstimatingCenter` at index `0`.
theorem simpleSetEstimatingCenter_zero
    :
    simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α 0 = x0 := rfl

/-- The center sequence satisfies its defining recursion. -/
-- Proof sketch: unfold `simpleSetEstimatingCenter` at index `k + 1`.
theorem simpleSetEstimatingCenter_succ
    (k : ℕ) :
    simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) =
      let gammaCurr := gamma k
      let gammaNext := gamma (k + 1)
      let yk := y k
      let gQk := gProj k
      (1 / gammaNext) •
        (((1 - α k) * gammaCurr) •
            simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k +
          (α k * μ) • yk -
          α k • gQk) := rfl

/-- The scalar term `φ_k^*` starts from the initial value `f(x0)`. -/
-- Proof sketch: unfold `simpleSetEstimatingValue` at index `0`.
theorem simpleSetEstimatingValue_zero
    :
    simpleSetEstimatingValue
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α 0 = f x0 := rfl

/-- The scalar term `φ_k^*` satisfies its defining recursive update. -/
-- Proof sketch: unfold `simpleSetEstimatingValue` at index `k + 1`.
theorem simpleSetEstimatingValue_succ
    (k : ℕ) :
    simpleSetEstimatingValue
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) =
      let gammaNext := gamma (k + 1)
      let gammaCurr := gamma k
      let yk := y k
      let vCurr :=
        simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      let gCurr := gProj k
      let xQCurr := xProj k
      (1 - α k) *
          simpleSetEstimatingValue
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k +
        α k * f xQCurr +
        (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gCurr‖ ^ (2 : ℕ) +
        (α k * (1 - α k) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gCurr (vCurr - yk)) := rfl

/- Helper for Proposition 2.22: rewrite the center update relative to the basepoint `y k`. -/
-- Proof sketch: subtract `y k` from the explicit recursion for `v_{k+1}` and use the curvature
-- recursion to absorb the `y k` coefficient.
private theorem simpleSetEstimatingCenter_succ_sub_eq
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) :
    simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) - y k =
      (1 / gamma (k + 1)) •
        (((1 - α k) * gamma k) •
            (simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k - y k) -
          α k • gProj k) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let gammaCurr : ℝ := gamma k
  let gammaNext : ℝ := gamma (k + 1)
  let vCurr : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
  let yk : E := y k
  let gk : E := gProj k
  have hgammaNext_ne : gammaNext ≠ 0 := by
    simpa [gammaNext] using hγ k
  have hyk : (1 / gammaNext) • (gammaNext • yk) = yk := by
    rw [smul_smul, one_div, inv_mul_cancel₀ hgammaNext_ne, one_smul]
  calc
    center (k + 1) - y k
        = (1 / gammaNext) •
            (((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk) - yk := by
              simpa [center, gammaCurr, gammaNext, vCurr, yk, gk] using
                congrArg (fun z : E ↦ z - y k)
                  (simpleSetEstimatingCenter_succ
                    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k)
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

/-- Helper for Proposition 2.22: the updated center gives the required linear term after
expanding the centered quadratic about `y k`. -/
-- Proof sketch: negate the previous center-difference formula, move the scalar inside the inner
-- product, and cancel the reciprocal with the nonzero next curvature.
private theorem simpleSetEstimatingCenter_succ_cross_term_eq
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ)
    (x : E) :
    gamma (k + 1) *
        inner ℝ
          (x - y k)
          (y k -
            simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1)) =
      (1 - α k) * gamma k *
          inner ℝ
            (x - y k)
            (y k -
              simpleSetEstimatingCenter
                Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k) +
        α k * inner ℝ (gProj k) (x - y k) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let gammaCurr : ℝ := gamma k
  let gammaNext : ℝ := gamma (k + 1)
  let vCurr : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
  let vNext : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1)
  let yk : E := y k
  let gk : E := gProj k
  have hgammaNext_ne : gammaNext ≠ 0 := by
    simpa [gammaNext] using hγ k
  have hsub :
      yk - vNext =
        (1 / gammaNext) • (((1 - α k) * gammaCurr) • (yk - vCurr) + α k • gk) := by
    calc
      yk - vNext = -(vNext - yk) := by abel
      _ = -((1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)) := by
            rw [simpleSetEstimatingCenter_succ_sub_eq
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k]
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

/-- Helper for Proposition 2.22: the new center's squared distance to `y k` matches the scalar
recursion for `φ_{k+1}^*`. -/
-- Proof sketch: substitute the center-difference formula, scale out the nonzero next curvature,
-- and expand the remaining norm square with `norm_sub_sq_real`.
private theorem simpleSetEstimatingCenter_succ_norm_sq_eq
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) :
    (gamma (k + 1) / 2) *
        ‖simpleSetEstimatingCenter
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) - y k‖ ^ (2 : ℕ) =
      (((1 - α k) ^ (2 : ℕ) * gamma k ^ (2 : ℕ)) / (2 * gamma (k + 1))) *
        ‖simpleSetEstimatingCenter
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k - y k‖ ^ (2 : ℕ) -
        (α k * (1 - α k) * gamma k / gamma (k + 1)) *
          inner ℝ
            (gProj k)
            (simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k - y k) +
        (α k ^ (2 : ℕ) / (2 * gamma (k + 1))) *
          ‖gProj k‖ ^ (2 : ℕ) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let gammaCurr : ℝ := gamma k
  let gammaNext : ℝ := gamma (k + 1)
  let vCurr : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
  let yk : E := y k
  let gk : E := gProj k
  have hgammaNext_ne : gammaNext ≠ 0 := by
    simpa [gammaNext] using hγ k
  have hscaled :
      (gammaNext / 2) *
          ‖(1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)‖ ^ (2 : ℕ) =
        (1 / (2 * gammaNext)) *
          ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp [hgammaNext_ne]
  have hexpand :
      ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) =
        ((1 - α k) * gammaCurr) ^ (2 : ℕ) * ‖vCurr - yk‖ ^ (2 : ℕ) -
          2 * ((1 - α k) * gammaCurr) * α k * inner ℝ (vCurr - yk) gk +
          α k ^ (2 : ℕ) * ‖gk‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  calc
    (gamma (k + 1) / 2) * ‖center (k + 1) - y k‖ ^ (2 : ℕ)
        =
        (gammaNext / 2) *
          ‖(1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)‖ ^ (2 : ℕ) := by
            simpa [gammaNext, gammaCurr, vCurr, yk, gk] using
              congrArg
                (fun z : E ↦ (gamma (k + 1) / 2) * ‖z‖ ^ (2 : ℕ))
                (simpleSetEstimatingCenter_succ_sub_eq
                  Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k)
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

/-- Proposition 2.22: if each successor curvature `γ_{k+1}` is nonzero, the recursively defined
estimating sequence over a simple set is exactly the centered quadratic
`quadraticallyRegularizedObjective (fun _ ↦ φ_k^*) γ_k v_k`, where `φ_k^*` and `v_k` are the
source-facing recursive sequences `simpleSetEstimatingValue` and `simpleSetEstimatingCenter`,
while `γ_k` is the owner curvature sequence `estimatingSequenceCurvature` from `Lemma_2_9`. -/
-- Proof sketch: prove the formula by induction on `k`. The base case is the initial quadratic
-- model centered at `x0`. For the inductive step, expand the recursion for
-- `simpleSetEstimatingFunction`, substitute the induction hypothesis, expand the projected lower
-- quadratic model, and complete the square in `x` to identify the new constant term, center, and
-- curvature with the recursive formulas defining `simpleSetEstimatingValue`,
-- `simpleSetEstimatingCenter`, and `estimatingSequenceCurvature`.
theorem simpleSetEstimatingFunction_eq_canonicalQuadratic
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) :
    phi k =
      quadraticallyRegularizedObjective
        (fun _ ↦
          simpleSetEstimatingValue
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k)
        (gamma k)
        (simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let value := simpleSetEstimatingValue
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  ext x
  induction k generalizing x with
  | zero =>
      simp [quadraticallyRegularizedObjective_apply, simpleSetEstimatingValue_zero,
        simpleSetEstimatingCenter_zero]
  | succ k hk =>
      let gammaCurr : ℝ := gamma k
      let gammaNext : ℝ := gamma (k + 1)
      let vCurr : E :=
        simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      let vNext : E :=
        simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1)
      let yk : E := y k
      let gk : E := gProj k
      let xQk : E := xProj k
      have hrecx :
          phi (k + 1) x =
            (1 - α k) * (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
              α k *
                (f xQk + (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                  inner ℝ gk (x - yk) + (μ / 2) * ‖x - yk‖ ^ (2 : ℕ)) := by
        calc
          phi (k + 1) x =
              (1 - α k) * phi k x +
                α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
                  exact
                    simpleSetEstimatingFunction_succ_apply
                      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k x
          _ =
              (1 - α k) *
                  quadraticallyRegularizedObjective
                    (fun _ : E ↦ value k)
                    (gamma k)
                    (center k) x +
                α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
                  rw [hk x]
          _ =
              (1 - α k) * (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
                α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
                  simp [quadraticallyRegularizedObjective_apply, center, gammaCurr, vCurr]
          _ =
              (1 - α k) * (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
                α k *
                  (f xQk + (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                    inner ℝ gk (x - yk) + (μ / 2) * ‖x - yk‖ ^ (2 : ℕ)) := by
                  rw [simpleSetEstimatingModel_apply]
      have hgammaNext_ne : gammaNext ≠ 0 := by
        simpa [gammaNext] using hγ k
      have hcurv :
          gammaNext = (1 - α k) * gammaCurr + α k * μ := by
        simpa [gammaCurr, gammaNext] using estimatingSequenceCurvature_succ μ gamma0 α k
      have hvalue :
          value (k + 1) =
            (1 - α k) * value k +
              α k * f xQk +
              (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
              (α k * (1 - α k) * gammaCurr / gammaNext) *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) := by
        simpa [gammaCurr, gammaNext, vCurr, yk, gk, xQk] using
          simpleSetEstimatingValue_succ
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      have hcross :
          gammaNext * inner ℝ (x - yk) (yk - vNext) =
            (1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
              α k * inner ℝ gk (x - yk) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk] using
          simpleSetEstimatingCenter_succ_cross_term_eq
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k x
      have hnorm :
          (gammaNext / 2) * ‖yk - vNext‖ ^ (2 : ℕ) =
            (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
              ‖vCurr - yk‖ ^ (2 : ℕ) -
              (α k * (1 - α k) * gammaCurr / gammaNext) * inner ℝ gk (vCurr - yk) +
              (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk, norm_sub_rev] using
          simpleSetEstimatingCenter_succ_norm_sq_eq
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k
      change
        phi (k + 1) x =
          value (k + 1) + (gammaNext / 2) * ‖(x - vNext : E)‖ ^ (2 : ℕ)
      rw [hrecx, hvalue,
        centered_quadratic_expand_about_point gammaCurr x yk vCurr,
        centered_quadratic_expand_about_point gammaNext x yk vNext, hcross, hnorm]
      let commonForm :=
        (1 - α k) * value k +
          α k * f xQk +
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
              (value k +
                (gammaCurr / 2 * ‖yk - vCurr‖ ^ (2 : ℕ) +
                  gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  gammaCurr / 2 * ‖x - yk‖ ^ (2 : ℕ))) +
            α k *
              (f xQk + 1 / (2 * L) * ‖gk‖ ^ (2 : ℕ) +
                inner ℝ gk (x - yk) + μ / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm + α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
        simp [commonForm]
        ring
      have hright :
          (1 - α k) * value k +
              α k * f xQk +
              (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
              α k * (1 - α k) * gammaCurr / gammaNext *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
            (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                  ‖vCurr - yk‖ ^ (2 : ℕ) -
                α k * (1 - α k) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
              ((1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                α k * inner ℝ gk (x - yk)) +
              gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm + α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
        calc
          (1 - α k) * value k +
                α k * f xQk +
                (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
                α k * (1 - α k) * gammaCurr / gammaNext *
                  ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
              (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                    ‖vCurr - yk‖ ^ (2 : ℕ) -
                  α k * (1 - α k) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                  α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
                ((1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  α k * inner ℝ gk (x - yk)) +
                gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ))
              =
              (1 - α k) * value k +
                α k * f xQk +
                α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                (α k * (1 - α k) * gammaCurr / gammaNext * (μ / 2) +
                    (1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                  ‖yk - vCurr‖ ^ (2 : ℕ) +
                ((1 - α k) * gammaCurr) * inner ℝ (x - yk) (yk - vCurr) +
                (gammaNext / 2) * ‖x - yk‖ ^ (2 : ℕ) +
                α k * inner ℝ gk (x - yk) := by
                  simp [norm_sub_rev]
                  ring
          _ = commonForm + α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
            rw [hconstCoeff, hxCoeff]
            simp [commonForm]
            ring
      simpa [quadraticallyRegularizedObjective_apply, gammaCurr, gammaNext, vCurr, vNext, yk, gk,
        xQk] using hleft.trans hright.symm

/-- Companion evaluation formula for Proposition 2.22: the owner equality unfolds to the
displayed centered quadratic expression at each point `x`. -/
theorem simpleSetEstimatingFunction_eq_canonicalQuadratic_apply
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) (x : E) :
    phi k x =
      simpleSetEstimatingValue
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k +
        (gamma k / 2) *
          ‖x -
              simpleSetEstimatingCenter
                Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k‖ ^ (2 : ℕ) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let value := simpleSetEstimatingValue
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  calc
    phi k x =
        quadraticallyRegularizedObjective
          (fun _ ↦ value k)
          (gamma k)
          (center k) x :=
      congrFun
        (simpleSetEstimatingFunction_eq_canonicalQuadratic
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k)
        x
    _ = value k + (gamma k / 2) * ‖x - center k‖ ^ (2 : ℕ) := by
      simp [quadraticallyRegularizedObjective_apply]

end

end
