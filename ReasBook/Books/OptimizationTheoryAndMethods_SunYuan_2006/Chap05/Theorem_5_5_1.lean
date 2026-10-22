/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_1_5
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped MatrixOrder

noncomputable section

-- Source/core/bridge triage for this file:
-- * source-facing: the one-step quadratic Newton-like contraction statements and their explicit
--   step and search-direction owners.
-- * core/canonical: `quadraticObjective` from Chapter 4 and the Euclidean matrix action
--   `Matrix.toEuclideanLin`, together with Chapter 2 `lineSearchObjective` /
--   `IsExactLineSearchStepOnNonnegativeRay`.
-- * bridge/view: `quadraticNewtonLikePoint` as the source-facing step formula for the canonical
--   Chapter 2 line-search ray.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The explicit Newton-like trial point
`xk - α • Matrix.toEuclideanLin Hk gk` used in the exact line search. -/
abbrev quadraticNewtonLikePoint (Hk : MatrixN) (xk gk : Point) (α : ℝ) : Point :=
  xk - α • Matrix.toEuclideanLin Hk gk

/-- The Newton-like search direction `-Matrix.toEuclideanLin Hk gk`. -/
abbrev quadraticNewtonLikeDirection (Hk : MatrixN) (gk : Point) : Point :=
  -Matrix.toEuclideanLin Hk gk

/-- The Chapter 2 exact-line-search predicate along the Newton-like direction on the
nonnegative ray from `xk`. -/
abbrev IsQuadraticNewtonLikeExactLineSearchStep
    (f : Point → ℝ) (Hk : MatrixN) (xk gk : Point) (α : ℝ) : Prop :=
  IsExactLineSearchStepOnNonnegativeRay f xk (quadraticNewtonLikeDirection Hk gk) α

/-- The explicit Newton-like trial point is the Chapter 2 line-search ray from `xk` in the
direction `quadraticNewtonLikeDirection Hk gk`. -/
@[simp] theorem quadraticNewtonLikePoint_eq_add_smul_direction
    (Hk : MatrixN) (xk gk : Point) (α : ℝ) :
    quadraticNewtonLikePoint Hk xk gk α =
      xk + α • quadraticNewtonLikeDirection Hk gk := by
  simp [quadraticNewtonLikePoint, quadraticNewtonLikeDirection, sub_eq_add_neg]

/-- Evaluating the Chapter 2 `lineSearchObjective` along the Newton-like direction recovers the
source-facing point formula `quadraticNewtonLikePoint Hk xk gk α`. -/
@[simp] theorem lineSearchObjective_quadraticObjective_quadraticNewtonLikeDirection_apply
    (G Hk : MatrixN) (b xk gk : Point) (c α : ℝ) :
    lineSearchObjective (quadraticObjective G b c) xk
        (quadraticNewtonLikeDirection Hk gk) α =
      quadraticObjective G b c (quadraticNewtonLikePoint Hk xk gk α) := by
  simp [lineSearchObjective, quadraticNewtonLikePoint_eq_add_smul_direction]

/-- The objective gap `quadraticObjective G b c x - quadraticObjective G b c xStar`. -/
def quadraticSuboptimality
    (G : MatrixN) (b : Point) (c : ℝ) (xStar x : Point) : ℝ :=
  quadraticObjective G b c x - quadraticObjective G b c xStar

/-- The quadratic energy `E x = (1 / 2) * (x - xStar)ᵀ G (x - xStar)` from `(5.5.6)`. -/
def quadraticEnergy (G : MatrixN) (xStar x : Point) : ℝ :=
  (1 / 2 : ℝ) * dotProduct (x - xStar) (Matrix.toEuclideanLin G (x - xStar))

/-- The Kantorovich contraction factor `((lambda1 - lambdaN)^2) / ((lambda1 + lambdaN)^2)`. -/
def kantorovichContractionFactor (lambda1 lambdaN : ℝ) : ℝ :=
  (lambda1 - lambdaN) ^ (2 : ℕ) / (lambda1 + lambdaN) ^ (2 : ℕ)

/-- Helper for Chapter05 Theorem 5.5.1: at a minimizer of the quadratic objective, the
suboptimality gap is exactly the centered quadratic energy. -/
theorem quadraticSuboptimality_eq_quadraticEnergy_of_minimizer
    {G : MatrixN} {b xStar x : Point} {c : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef) :
    quadraticSuboptimality G b c xStar x = quadraticEnergy G xStar x := by
  have hGsymm : G.IsSymm := posDef_isSymm hGpos
  have hDiff : DifferentiableAt ℝ (quadraticObjective G b c) xStar :=
    (hasGradientAt_quadraticObjective G b c hGsymm xStar).differentiableAt
  -- First-order optimality at the minimizer kills the linear term in the quadratic expansion.
  have hGradZero : gradient (quadraticObjective G b c) xStar = 0 := by
    exact gradient_eq_zero_of_isLocalMinOn
      Set.univ (quadraticObjective G b c) xStar isOpen_univ (by simp) hDiff hMin.localize
  -- Expand around `xStar`; the remaining quadratic remainder is exactly the energy.
  have hExpand :
      quadraticObjective G b c x =
        quadraticObjective G b c xStar +
          dotProduct ((gradient (quadraticObjective G b c) xStar : Point)) (x - xStar) +
            (1 / 2 : ℝ) * dotProduct (x - xStar) (Matrix.toEuclideanLin G (x - xStar)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Matrix.toEuclideanLin_apply] using
      quadraticObjective_eq_at_reference_add_gradient_displacement G b c hGsymm xStar (x - xStar)
  unfold quadraticSuboptimality quadraticEnergy
  rw [hExpand]
  simp [hGradZero, add_assoc, add_left_comm, add_comm]

/-- Helper for Chapter05 Theorem 5.5.1: at a quadratic minimizer, the gradient at `x`
is the Hessian applied to the displacement `x - xStar`. -/
theorem quadraticGradient_eq_displacement_of_minimizer
    {G : MatrixN} {b xStar x g : Point} {c : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) g x) :
    g = Matrix.toEuclideanLin G (x - xStar) := by
  have hGsymm : G.IsSymm := posDef_isSymm hGpos
  have hDiff : DifferentiableAt ℝ (quadraticObjective G b c) xStar :=
    (hasGradientAt_quadraticObjective G b c hGsymm xStar).differentiableAt
  -- First-order optimality makes the gradient vanish at the minimizer.
  have hGradZero : gradient (quadraticObjective G b c) xStar = 0 := by
    exact gradient_eq_zero_of_isLocalMinOn
      Set.univ (quadraticObjective G b c) xStar isOpen_univ (by simp) hDiff hMin.localize
  have hAtStar :
      Matrix.toEuclideanLin G xStar + b = 0 := by
    simpa [gradient_quadraticObjective G b c hGsymm xStar] using hGradZero
  have hb :
      b = -Matrix.toEuclideanLin G xStar := by
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hAtStar)
  -- Rewrite the current gradient by subtracting the vanishing minimizer gradient.
  calc
    g = gradient (quadraticObjective G b c) x := hGrad.gradient.symm
    _ = Matrix.toEuclideanLin G x + b := by
      rw [gradient_quadraticObjective G b c hGsymm x]
    _ = Matrix.toEuclideanLin G x - Matrix.toEuclideanLin G xStar := by
      rw [hb]
      abel
    _ = Matrix.toEuclideanLin G (x - xStar) := by
      simp [sub_eq_add_neg]

/-- Helper for Chapter05 Theorem 5.5.1: at a minimizer of the quadratic objective, the current
suboptimality gap equals `(1 / 2) * gkᵀ G⁻¹ gk` for the gradient `gk` at `xk`. -/
theorem quadraticSuboptimality_eq_half_gradientInverseQuadratic
    {G : MatrixN} {b xStar xk gk : Point} {c : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk) :
    quadraticSuboptimality G b c xStar xk =
      (1 / 2 : ℝ) * dotProduct gk (Matrix.toEuclideanLin G⁻¹ gk) := by
  let _ := hGpos.isUnit.invertible
  have hGsymm : G.IsSymm := posDef_isSymm hGpos
  have hDiff :
      DifferentiableAt ℝ (quadraticObjective G b c) xStar :=
    (hasGradientAt_quadraticObjective G b c hGsymm xStar).differentiableAt
  have hGradZero : gradient (quadraticObjective G b c) xStar = 0 := by
    exact gradient_eq_zero_of_isLocalMinOn
      Set.univ (quadraticObjective G b c) xStar isOpen_univ (by simp) hDiff hMin.localize
  have hAtStar :
      Matrix.toEuclideanLin G xStar + b = 0 := by
    simpa [gradient_quadraticObjective G b c hGsymm xStar] using hGradZero
  have hb :
      b = -Matrix.toEuclideanLin G xStar := by
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hAtStar)
  have hgk_eq :
      gk = Matrix.toEuclideanLin G (xk - xStar) :=
    quadraticGradient_eq_displacement_of_minimizer hMin hGpos hGrad
  have hdisp :
      xk - xStar = Matrix.toEuclideanLin G⁻¹ gk := by
    -- Apply `G⁻¹` to the gradient identity to recover the displacement from the minimizer.
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] using congrArg (Matrix.toEuclideanLin G⁻¹) hgk_eq |>.symm
  have hpush :
      Matrix.toEuclideanLin G (Matrix.toEuclideanLin G⁻¹ gk) = gk := by
    -- The Hessian action cancels its inverse on the gradient vector.
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec]
  -- Replace the centered displacement-energy form by the gradient/inverse-gradient form.
  calc
    quadraticSuboptimality G b c xStar xk = quadraticEnergy G xStar xk :=
      quadraticSuboptimality_eq_quadraticEnergy_of_minimizer hMin hGpos
    _ = (1 / 2 : ℝ) * dotProduct (xk - xStar) (Matrix.toEuclideanLin G (xk - xStar)) := rfl
    _ = (1 / 2 : ℝ) * dotProduct (Matrix.toEuclideanLin G⁻¹ gk)
          (Matrix.toEuclideanLin G (Matrix.toEuclideanLin G⁻¹ gk)) := by
      rw [hdisp]
    _ = (1 / 2 : ℝ) * dotProduct (Matrix.toEuclideanLin G⁻¹ gk) gk := by
      rw [hpush]
    _ = (1 / 2 : ℝ) * dotProduct gk (Matrix.toEuclideanLin G⁻¹ gk) := by
      rw [dotProduct_comm]

/-- Helper for Chapter05 Theorem 5.5.1: along the Newton-like ray
`α ↦ xk - α • Matrix.toEuclideanLin Hk gk`, the quadratic suboptimality is the source scalar
quadratic model in `α`. -/
theorem quadraticNewtonLikeSuboptimality_along_ray
    {G Hk : MatrixN} {b xStar xk gk : Point} {c α : ℝ}
    (hGpos : G.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk) :
    quadraticSuboptimality G b c xStar (quadraticNewtonLikePoint Hk xk gk α) =
      quadraticSuboptimality G b c xStar xk -
        α * dotProduct gk (Matrix.toEuclideanLin Hk gk) +
          (α ^ 2 / 2 : ℝ) *
            dotProduct (Matrix.toEuclideanLin Hk gk)
              (Matrix.toEuclideanLin G (Matrix.toEuclideanLin Hk gk)) := by
  let u : Point := Matrix.toEuclideanLin Hk gk
  have hGsymm : G.IsSymm := posDef_isSymm hGpos
  have hExpand :=
    quadraticObjective_eq_at_reference_add_gradient_displacement G b c hGsymm xk (-α • u)
  have hRayExpand :
      quadraticObjective G b c (quadraticNewtonLikePoint Hk xk gk α) =
        quadraticObjective G b c xk +
          dotProduct gk (-α • u) +
          (1 / 2 : ℝ) * dotProduct (-α • u) (G.mulVec (-α • u)) := by
    -- Expand at `xk`; the Newton-like point is exactly the displacement `-α • u`.
    simpa [quadraticNewtonLikePoint, u, sub_eq_add_neg, add_assoc, hGrad.gradient] using hExpand
  have hLinear :
      dotProduct gk (-α • u) = -α * dotProduct gk u := by
    rw [dotProduct_smul]
    ring
  have hQuadratic :
      (1 / 2 : ℝ) * dotProduct (-α • u) (G.mulVec (-α • u)) =
        (α ^ 2 / 2 : ℝ) * dotProduct u (Matrix.toEuclideanLin G u) := by
    have hMulVecScale : G.mulVec (-α • u) = -α • G.mulVec u := by
      simpa using (Matrix.mulVec_smul G (-α) u.ofLp)
    -- The quadratic remainder scales by `(-α)^2 = α^2` along the ray.
    calc
      (1 / 2 : ℝ) * dotProduct (-α • u) (G.mulVec (-α • u))
          = (1 / 2 : ℝ) * dotProduct (-α • u) (-α • Matrix.toEuclideanLin G u) := by
              rw [hMulVecScale]
              rfl
      _ = (1 / 2 : ℝ) * (((-α) * (-α)) * dotProduct u (Matrix.toEuclideanLin G u)) := by
            simp [smul_dotProduct, dotProduct_smul, mul_assoc]
      _ = (α ^ 2 / 2 : ℝ) * dotProduct u (Matrix.toEuclideanLin G u) := by
            ring
  -- Subtract the minimizer value and normalize the scalar coefficients.
  calc
    quadraticSuboptimality G b c xStar (quadraticNewtonLikePoint Hk xk gk α)
        = quadraticObjective G b c xk + dotProduct gk (-α • u) +
            (1 / 2 : ℝ) * dotProduct (-α • u) (G.mulVec (-α • u)) -
            quadraticObjective G b c xStar := by
              simpa [quadraticSuboptimality, sub_eq_add_neg] using hRayExpand
    _ = quadraticSuboptimality G b c xStar xk + dotProduct gk (-α • u) +
          (1 / 2 : ℝ) * dotProduct (-α • u) (G.mulVec (-α • u)) := by
            unfold quadraticSuboptimality
            ring
    _ = quadraticSuboptimality G b c xStar xk + (-α) * dotProduct gk u +
          (1 / 2 : ℝ) * dotProduct (-α • u) (G.mulVec (-α • u)) := by
            rw [hLinear]
    _ = quadraticSuboptimality G b c xStar xk - α * dotProduct gk u +
          (1 / 2 : ℝ) * dotProduct (-α • u) (G.mulVec (-α • u)) := by
            ring
    _ = quadraticSuboptimality G b c xStar xk - α * dotProduct gk u +
          (α ^ 2 / 2 : ℝ) * dotProduct u (Matrix.toEuclideanLin G u) := by
            rw [hQuadratic]
    _ = quadraticSuboptimality G b c xStar xk -
          α * dotProduct gk (Matrix.toEuclideanLin Hk gk) +
          (α ^ 2 / 2 : ℝ) *
            dotProduct (Matrix.toEuclideanLin Hk gk)
              (Matrix.toEuclideanLin G (Matrix.toEuclideanLin Hk gk)) := by
            simp [u]

/-- Helper for Chapter05 Theorem 5.5.1: substituting the stationary trial step
`alphaTrial = a / cRay` into the quadratic Newton-like ray model yields the reduced scalar gap
`gap_k - a^2 / (2 * cRay)`. -/
theorem quadraticNewtonLikeSuboptimality_trial_eq_gap_sub_square
    {G Hk : MatrixN} {b xStar xk gk : Point} {c a cRay : ℝ}
    (hGpos : G.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk)
    (ha : a = dotProduct gk (Matrix.toEuclideanLin Hk gk))
    (hcRay :
      cRay = dotProduct (Matrix.toEuclideanLin Hk gk)
        (Matrix.toEuclideanLin G (Matrix.toEuclideanLin Hk gk)))
    (hcRay_pos : 0 < cRay) :
    quadraticSuboptimality G b c xStar (quadraticNewtonLikePoint Hk xk gk (a / cRay)) =
      quadraticSuboptimality G b c xStar xk - a ^ (2 : ℕ) / (2 * cRay) := by
  -- Evaluate the source quadratic ray at the stationary trial step `a / cRay`.
  rw [quadraticNewtonLikeSuboptimality_along_ray (G := G) (Hk := Hk) (b := b)
    (xStar := xStar) (xk := xk) (gk := gk) (c := c) (α := a / cRay) hGpos hGrad]
  rw [ha, hcRay]
  have hcRay_ne : cRay ≠ 0 := ne_of_gt hcRay_pos
  -- The scalar quadratic collapses to the reduced value after clearing the denominator.
  field_simp [hcRay_ne]
  ring_nf

/-- Helper for Chapter05 Theorem 5.5.1: once the current gap is identified with
`(1 / 2) * dGap` and the accepted step is bounded by the reduced trial value
`gap_k - a^2 / (2 * cRay)`, the gap contracts by the reduced Rayleigh factor
`1 - a^2 / (dGap * cRay)`. -/
theorem quadraticSuboptimality_le_reducedRayleighFactor_of_gapData
    {G : MatrixN} {b xStar xk xk1 : Point} {c a cRay dGap : ℝ}
    (hGapEq :
      quadraticSuboptimality G b c xStar xk = (1 / 2 : ℝ) * dGap)
    (hTrialBound :
      quadraticSuboptimality G b c xStar xk1 ≤
        quadraticSuboptimality G b c xStar xk - a ^ (2 : ℕ) / (2 * cRay))
    (hcRay_pos : 0 < cRay)
    (hGapDen_pos : 0 < dGap) :
    quadraticSuboptimality G b c xStar xk1 ≤
      (1 - a ^ (2 : ℕ) / (dGap * cRay)) *
        quadraticSuboptimality G b c xStar xk := by
  have hcRay_ne : cRay ≠ 0 := ne_of_gt hcRay_pos
  have hGapDen_ne : dGap ≠ 0 := ne_of_gt hGapDen_pos
  rw [hGapEq] at hTrialBound ⊢
  have hFactor :
      (1 - a ^ (2 : ℕ) / (dGap * cRay)) * ((1 / 2 : ℝ) * dGap) =
        (1 / 2 : ℝ) * dGap - a ^ (2 : ℕ) / (2 * cRay) := by
    -- Clear the positive denominators to match the reduced trial-gap expression.
    field_simp [hcRay_ne, hGapDen_ne]
  rw [hFactor]
  exact hTrialBound

/-- Helper for Chapter05 Theorem 5.5.1: the square-root conjugate
`CFC.sqrt Hk * G * CFC.sqrt Hk` is positive definite. -/
theorem sqrtConjugateRepresentative_posDef
    {G Hk : MatrixN} (hGpos : G.PosDef) (hHkpos : Hk.PosDef) :
    (CFC.sqrt Hk * G * CFC.sqrt Hk).PosDef := by
  have hSunit : IsUnit (CFC.sqrt Hk) := by
    -- The positive-definite square root stays invertible because `Hk` itself is invertible.
    exact (CFC.isUnit_sqrt_iff Hk hHkpos.posSemidef.nonneg).2 hHkpos.isUnit
  have hStrans : (CFC.sqrt Hk).transpose = CFC.sqrt Hk := by
    -- Over `ℝ`, the square root of a nonnegative matrix is self-adjoint, hence symmetric.
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg Hk).star_eq
  -- Conjugating the positive-definite matrix `G` by the invertible square root preserves
  -- positive definiteness.
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hStrans] using
    hGpos.conjTranspose_mul_mul_same
      (B := CFC.sqrt Hk)
      (mulVec_injective_of_isUnit hSunit)

/-- Helper for Chapter05 Theorem 5.5.1: pointwise real-spectrum membership is preserved between
`Hk * G` and its square-root conjugate `CFC.sqrt Hk * G * CFC.sqrt Hk`. -/
theorem sqrtConjugateSpectrumMem_iff
    {G Hk : MatrixN} (hHkpos : Hk.PosDef) (μ : ℝ) :
    let S : MatrixN := CFC.sqrt Hk
    let T : MatrixN := S * G * S
    μ ∈ spectrum ℝ T ↔ μ ∈ spectrum ℝ (Hk * G) := by
  dsimp
  have hSunit : IsUnit (CFC.sqrt Hk) := by
    -- The square root inherits invertibility from the positive-definite matrix `Hk`.
    exact (CFC.isUnit_sqrt_iff Hk hHkpos.posSemidef.nonneg).2 hHkpos.isUnit
  let u : MatrixNˣ := hSunit.unit
  have hu : (↑u : MatrixN) = CFC.sqrt Hk := hSunit.unit_spec
  have hSq : ((↑u : MatrixN) ^ (2 : ℕ)) = Hk := by
    -- The square root squares back to `Hk`.
    simpa [hu, pow_two] using CFC.sq_sqrt Hk hHkpos.posSemidef.nonneg
  have hSpec :
      spectrum ℝ ((CFC.sqrt Hk) * G * (CFC.sqrt Hk)) = spectrum ℝ (Hk * G) := by
    -- View `sqrt(Hk) * G * sqrt(Hk)` as the unit conjugate of `Hk * G`.
    calc
      spectrum ℝ ((CFC.sqrt Hk) * G * (CFC.sqrt Hk))
          = spectrum ℝ ((↑u⁻¹ : MatrixN) * (Hk * G) * (↑u : MatrixN)) := by
              congr 1
              calc
                (CFC.sqrt Hk) * G * (CFC.sqrt Hk)
                    = (↑u : MatrixN) * G * (↑u : MatrixN) := by rw [hu]
                _ = (↑u⁻¹ : MatrixN) * ((((↑u : MatrixN) ^ (2 : ℕ)) * G)) * (↑u : MatrixN) := by
                      calc
                        (↑u : MatrixN) * G * (↑u : MatrixN)
                            = (1 : MatrixN) * ((↑u : MatrixN) * G) * (↑u : MatrixN) := by simp
                        _ = ((↑u⁻¹ : MatrixN) * (↑u : MatrixN)) * ((↑u : MatrixN) * G) *
                              (↑u : MatrixN) := by simp
                        _ = (↑u⁻¹ : MatrixN) * ((↑u : MatrixN) * ((↑u : MatrixN) * G)) *
                              (↑u : MatrixN) := by simp [mul_assoc]
                        _ = (↑u⁻¹ : MatrixN) * ((((↑u : MatrixN) * (↑u : MatrixN)) * G)) *
                              (↑u : MatrixN) := by simp [mul_assoc]
                        _ = (↑u⁻¹ : MatrixN) * ((((↑u : MatrixN) ^ (2 : ℕ)) * G)) *
                              (↑u : MatrixN) := by simp [pow_two]
                _ = (↑u⁻¹ : MatrixN) * (Hk * G) * (↑u : MatrixN) := by rw [hSq]
      _ = spectrum ℝ (Hk * G) := by
            simpa using
              (spectrum.units_conjugate' (R := ℝ) (a := Hk * G) (u := u))
  simpa [hSpec]

/-- Helper for Chapter05 Theorem 5.5.1: the centered energy `quadraticEnergy G xStar x`
becomes the centered quadratic objective of `T = sqrt(Hk) * G * sqrt(Hk)` after transport by
`sqrt(Hk)⁻¹`. -/
theorem quadraticEnergy_eq_sqrtConjugateCenteredObjective
    {G Hk : MatrixN} {xStar x : Point}
    (hGpos : G.PosDef) (hHkpos : Hk.PosDef) :
    let S : MatrixN := CFC.sqrt Hk
    let T : MatrixN := S * G * S
    let y : Point := Matrix.toEuclideanLin S⁻¹ (x - xStar)
    quadraticEnergy G xStar x = quadraticObjective T 0 0 y := by
  dsimp
  have hSunit : IsUnit (CFC.sqrt Hk) := by
    -- The positive square root stays invertible because `Hk` is positive definite.
    exact (CFC.isUnit_sqrt_iff Hk hHkpos.posSemidef.nonneg).2 hHkpos.isUnit
  let _ := hSunit.invertible
  have hSsymm : (CFC.sqrt Hk).transpose = CFC.sqrt Hk := by
    -- Over `ℝ`, the positive square root is symmetric.
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg Hk).star_eq
  let y : Point := Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (x - xStar)
  have hRecover :
      Matrix.toEuclideanLin (CFC.sqrt Hk) y = x - xStar := by
    -- Apply `sqrt(Hk)` back to the transported state and cancel the inverse.
    simpa [y, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hCore :
      dotProduct (x - xStar) (Matrix.toEuclideanLin G (x - xStar)) =
        y.ofLp ⬝ᵥ (((CFC.sqrt Hk) * G * CFC.sqrt Hk) *ᵥ y.ofLp) := by
    -- Move the outer `sqrt(Hk)` factor across the dot product to obtain the conjugated matrix.
    rw [← hRecover]
    calc
      dotProduct (Matrix.toEuclideanLin (CFC.sqrt Hk) y)
          (Matrix.toEuclideanLin G (Matrix.toEuclideanLin (CFC.sqrt Hk) y))
        = ((CFC.sqrt Hk) *ᵥ y.ofLp) ⬝ᵥ (G *ᵥ ((CFC.sqrt Hk) *ᵥ y.ofLp)) := by
            simp [y, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
      _ = (((CFC.sqrt Hk) *ᵥ y.ofLp) ᵥ* G) ⬝ᵥ ((CFC.sqrt Hk) *ᵥ y.ofLp) := by
            rw [Matrix.dotProduct_mulVec]
      _ = (y.ofLp ᵥ* ((CFC.sqrt Hk).transpose * G)) ⬝ᵥ ((CFC.sqrt Hk) *ᵥ y.ofLp) := by
            rw [Matrix.vecMul_mulVec]
      _ = y.ofLp ⬝ᵥ ((((CFC.sqrt Hk).transpose * G) * CFC.sqrt Hk) *ᵥ y.ofLp) := by
            rw [← Matrix.dotProduct_mulVec]
            simp [Matrix.mulVec_mulVec, mul_assoc]
      _ = y.ofLp ⬝ᵥ (((CFC.sqrt Hk) * G * CFC.sqrt Hk) *ᵥ y.ofLp) := by
            rw [hSsymm]
  -- Rewrite the centered energy in the conjugated quadratic form.
  calc
    quadraticEnergy G xStar x
      = (1 / 2 : ℝ) * dotProduct (x - xStar) (Matrix.toEuclideanLin G (x - xStar)) := rfl
    _ = (1 / 2 : ℝ) * (y.ofLp ⬝ᵥ (((CFC.sqrt Hk) * G * CFC.sqrt Hk) *ᵥ y.ofLp)) := by
          rw [hCore]
    _ = quadraticObjective ((CFC.sqrt Hk) * G * CFC.sqrt Hk) 0 0 y := by
          simp [quadraticObjective, Matrix.toEuclideanLin_apply, mul_assoc]

/-- Helper for Chapter05 Theorem 5.5.1: transporting the Newton-like step by `sqrt(Hk)⁻¹`
identifies it with a steepest-descent step for the centered quadratic with Hessian
`sqrt(Hk) * G * sqrt(Hk)`. -/
theorem quadraticNewtonLikePoint_eq_sqrtConjugateSteepestDescentStep
    {G Hk : MatrixN} {b xStar xk gk : Point} {c α : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef)
    (hHkpos : Hk.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk) :
    let S : MatrixN := CFC.sqrt Hk
    let T : MatrixN := S * G * S
    let yk : Point := Matrix.toEuclideanLin S⁻¹ (xk - xStar)
    Matrix.toEuclideanLin S⁻¹ (quadraticNewtonLikePoint Hk xk gk α - xStar) =
      steepestDescentStep (quadraticObjective T 0 0) yk α := by
  dsimp
  have hSunit : IsUnit (CFC.sqrt Hk) := by
    -- The square root is invertible because `Hk` is positive definite.
    exact (CFC.isUnit_sqrt_iff Hk hHkpos.posSemidef.nonneg).2 hHkpos.isUnit
  let _ := hSunit.invertible
  have hgk_eq :
      gk = Matrix.toEuclideanLin G (xk - xStar) :=
    quadraticGradient_eq_displacement_of_minimizer hMin hGpos hGrad
  have hTsymm : ((CFC.sqrt Hk) * G * CFC.sqrt Hk).IsSymm := by
    exact posDef_isSymm (sqrtConjugateRepresentative_posDef hGpos hHkpos)
  have hGradT :
      gradient (quadraticObjective ((CFC.sqrt Hk) * G * CFC.sqrt Hk) 0 0)
        (Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (xk - xStar)) =
        Matrix.toEuclideanLin (CFC.sqrt Hk) gk := by
    -- Compute the centered quadratic gradient at the transported state.
    rw [gradient_quadraticObjective ((CFC.sqrt Hk) * G * CFC.sqrt Hk) 0 0 hTsymm]
    simp [Matrix.toEuclideanLin_apply, hgk_eq, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hMul :
      Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (Matrix.toEuclideanLin Hk gk) =
        Matrix.toEuclideanLin (CFC.sqrt Hk) gk := by
    -- Cancel one `sqrt(Hk)` factor from `Hk = sqrt(Hk) * sqrt(Hk)`.
    have hSq : CFC.sqrt Hk * CFC.sqrt Hk = Hk := by
      simpa [pow_two] using CFC.sq_sqrt Hk hHkpos.posSemidef.nonneg
    calc
      Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (Matrix.toEuclideanLin Hk gk)
        = Matrix.toEuclideanLin (((CFC.sqrt Hk)⁻¹) * Hk) gk := by
            simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
      _ = Matrix.toEuclideanLin (CFC.sqrt Hk) gk := by
            have hMatrix : (CFC.sqrt Hk)⁻¹ * Hk = CFC.sqrt Hk := by
              calc
                (CFC.sqrt Hk)⁻¹ * Hk = (CFC.sqrt Hk)⁻¹ * (CFC.sqrt Hk * CFC.sqrt Hk) := by
                  rw [hSq]
                _ = CFC.sqrt Hk := by
                  rw [← mul_assoc, Matrix.inv_mul_of_invertible, one_mul]
            rw [hMatrix]
  -- Push `sqrt(Hk)⁻¹` through the Newton-like update and then rewrite the centered gradient.
  calc
    Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (quadraticNewtonLikePoint Hk xk gk α - xStar)
      = Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹
          ((xk - xStar) - α • Matrix.toEuclideanLin Hk gk) := by
            simp [quadraticNewtonLikePoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (xk - xStar) -
          α • Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (Matrix.toEuclideanLin Hk gk) := by
            rw [LinearMap.map_sub, LinearMap.map_smul]
    _ = Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (xk - xStar) -
          α • Matrix.toEuclideanLin (CFC.sqrt Hk) gk := by
            rw [hMul]
    _ = steepestDescentStep
          (quadraticObjective ((CFC.sqrt Hk) * G * CFC.sqrt Hk) 0 0)
          (Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (xk - xStar)) α := by
            rw [steepestDescentStep_eq, hGradT]

/-- Helper for Chapter05 Theorem 5.5.1: exact line search on the Newton-like ray transports to
exact line search on the centered steepest-descent ray after conjugation by `sqrt(Hk)⁻¹`. -/
theorem quadraticNewtonLikeExactLineSearch_transport
    {G Hk : MatrixN} {b xStar xk gk : Point} {c α : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef)
    (hHkpos : Hk.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk)
    (hExactLineSearch :
      IsQuadraticNewtonLikeExactLineSearchStep (quadraticObjective G b c) Hk xk gk α) :
    let S : MatrixN := CFC.sqrt Hk
    let T : MatrixN := S * G * S
    let yk : Point := Matrix.toEuclideanLin S⁻¹ (xk - xStar)
    IsExactLineSearchStepOnNonnegativeRay
      (quadraticObjective T 0 0)
      yk
      (steepestDescentDirection (quadraticObjective T 0 0) yk)
      α := by
  dsimp
  have hPointTransport (β : ℝ) :
      quadraticSuboptimality G b c xStar (quadraticNewtonLikePoint Hk xk gk β) =
        quadraticObjective ((CFC.sqrt Hk) * G * CFC.sqrt Hk) 0 0
          (steepestDescentStep
            (quadraticObjective ((CFC.sqrt Hk) * G * CFC.sqrt Hk) 0 0)
            (Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ (xk - xStar)) β) := by
    -- Rewrite the source gap through the transported centered energy and the transported step.
    rw [quadraticSuboptimality_eq_quadraticEnergy_of_minimizer hMin hGpos]
    rw [quadraticEnergy_eq_sqrtConjugateCenteredObjective
      (G := G) (Hk := Hk) (xStar := xStar)
      (x := quadraticNewtonLikePoint Hk xk gk β) hGpos hHkpos]
    rw [quadraticNewtonLikePoint_eq_sqrtConjugateSteepestDescentStep
      (G := G) (Hk := Hk) (b := b) (xStar := xStar) (xk := xk) (gk := gk) (c := c)
      (α := β) hMin hGpos hHkpos hGrad]
  refine (isExactLineSearchStepOnNonnegativeRay_iff _ _ _ _).2 ?_
  refine ⟨hExactLineSearch.nonneg, ?_⟩
  intro β hβ
  have hOpt :=
    sub_le_sub_right (hExactLineSearch.optimal hβ) (quadraticObjective G b c xStar)
  -- Subtract the minimizer value and rewrite both sides in the centered coordinates.
  have hGapOpt :
      quadraticSuboptimality G b c xStar (quadraticNewtonLikePoint Hk xk gk α) ≤
        quadraticSuboptimality G b c xStar (quadraticNewtonLikePoint Hk xk gk β) := by
    simpa [quadraticSuboptimality] using hOpt
  rw [hPointTransport α, hPointTransport β] at hGapOpt
  simpa [lineSearchObjective, steepestDescentStep] using hGapOpt

/-- Helper for Chapter05 Theorem 5.5.1: the inverse denominator `gkᵀ G⁻¹ gk` becomes
`zᵀ T⁻¹ z` in the square-root conjugate coordinates. -/
theorem sqrtConjugateInverseDenominator_eq
    {G Hk : MatrixN} {gk : Point} (hGpos : G.PosDef) (hHkpos : Hk.PosDef) :
    let S : MatrixN := CFC.sqrt Hk
    let T : MatrixN := S * G * S
    let z : Fin n → ℝ := (Matrix.toEuclideanLin S gk).ofLp
    dotProduct gk (Matrix.toEuclideanLin G⁻¹ gk) = z ⬝ᵥ (T⁻¹ *ᵥ z) := by
  dsimp
  have hSunit : IsUnit (CFC.sqrt Hk) := by
    -- The positive square root is invertible because `Hk` is positive definite.
    exact (CFC.isUnit_sqrt_iff Hk hHkpos.posSemidef.nonneg).2 hHkpos.isUnit
  let _ := hSunit.invertible
  have hSsymm : (CFC.sqrt Hk).transpose = CFC.sqrt Hk := by
    -- Over `ℝ`, the positive square root is symmetric.
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg Hk).star_eq
  have hSinvSymm : ((CFC.sqrt Hk)⁻¹).transpose = (CFC.sqrt Hk)⁻¹ := by
    -- Symmetry is preserved by inversion.
    simpa [hSsymm] using
      (Matrix.transpose_nonsing_inv (A := CFC.sqrt Hk))
  have hInv :
      ((CFC.sqrt Hk) * G * (CFC.sqrt Hk))⁻¹ =
        (CFC.sqrt Hk)⁻¹ * G⁻¹ * (CFC.sqrt Hk)⁻¹ := by
    -- The inverse of the conjugated matrix is the conjugate of the inverse.
    rw [mul_assoc, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  let zVec : Point := Matrix.toEuclideanLin (CFC.sqrt Hk) gk
  have hRecover :
      Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ zVec = gk := by
    -- Applying the inverse square root to `z` recovers the original gradient vector.
    simpa [zVec, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hCore :
      dotProduct gk (Matrix.toEuclideanLin G⁻¹ gk) =
        zVec.ofLp ⬝ᵥ ((((CFC.sqrt Hk) * G * (CFC.sqrt Hk))⁻¹) *ᵥ zVec.ofLp) := by
    -- Transport the inverse quadratic form through the inverse square root.
    rw [← hRecover, hInv]
    calc
      dotProduct (Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ zVec)
          (Matrix.toEuclideanLin G⁻¹ (Matrix.toEuclideanLin (CFC.sqrt Hk)⁻¹ zVec))
        = ((CFC.sqrt Hk)⁻¹ *ᵥ zVec.ofLp) ⬝ᵥ (G⁻¹ *ᵥ (((CFC.sqrt Hk)⁻¹) *ᵥ zVec.ofLp)) := by
            simp [zVec, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
      _ = ((((CFC.sqrt Hk)⁻¹) *ᵥ zVec.ofLp) ᵥ* G⁻¹) ⬝ᵥ (((CFC.sqrt Hk)⁻¹) *ᵥ zVec.ofLp) := by
            rw [Matrix.dotProduct_mulVec]
      _ = (zVec.ofLp ᵥ* (((CFC.sqrt Hk)⁻¹).transpose * G⁻¹)) ⬝ᵥ
            (((CFC.sqrt Hk)⁻¹) *ᵥ zVec.ofLp) := by
              rw [Matrix.vecMul_mulVec]
      _ = zVec.ofLp ⬝ᵥ (((((CFC.sqrt Hk)⁻¹).transpose * G⁻¹) * (CFC.sqrt Hk)⁻¹) *ᵥ zVec.ofLp) := by
            rw [← Matrix.dotProduct_mulVec]
            simp [Matrix.mulVec_mulVec, mul_assoc]
      _ = zVec.ofLp ⬝ᵥ ((((CFC.sqrt Hk)⁻¹ * G⁻¹ * (CFC.sqrt Hk)⁻¹) *ᵥ zVec.ofLp)) := by
            rw [hSinvSymm]
  simpa [zVec] using hCore

/-- Helper for Chapter05 Theorem 5.5.1: the centered quadratic is constant along the stationary
ray from `0`, so the step length `0` is an exact line-search step. -/
theorem centeredQuadraticObjective_zero_exactLineSearch
    {G : MatrixN} (hGpos : G.PosDef) :
    IsExactLineSearchStepOnNonnegativeRay
      (quadraticObjective G 0 0)
      0
      (steepestDescentDirection (quadraticObjective G 0 0) 0)
      0 := by
  have hGsymm : G.IsSymm := posDef_isSymm hGpos
  refine (isExactLineSearchStepOnNonnegativeRay_iff _ _ _ _).2 ?_
  refine ⟨le_rfl, ?_⟩
  intro β hβ
  -- The gradient vanishes at the centered minimizer, so every point on the ray is the same point.
  simp [lineSearchObjective, steepestDescentDirection,
    gradient_quadraticObjective G 0 0 hGsymm (0 : Point)]

/-- Helper for Chapter05 Theorem 5.5.1: the canonical closed-form step size for the centered
quadratic uses the Chapter03 nonstationary exact-step formula and falls back to `0` at a
stationary iterate. -/
noncomputable def centeredQuadraticClosedFormStepSize
    {T : MatrixN} (hTpos : T.PosDef) (y : Point) : ℝ :=
  if hy : y = 0 then
    0
  else
    dotProduct (T.mulVec y) (T.mulVec y) /
      dotProduct (T.mulVec y) (T.mulVec (T.mulVec y))

/-- Helper for Chapter05 Theorem 5.5.1: starting from `y0`, the canonical centered continuation
updates each iterate by one steepest-descent step with the closed-form step-size rule. -/
noncomputable def centeredQuadraticClosedFormIterates
    {T : MatrixN} (hTpos : T.PosDef) (y0 : Point) : ℕ → Point
  | 0 => y0
  | k + 1 =>
      steepestDescentStep
        (quadraticObjective T 0 0)
        (centeredQuadraticClosedFormIterates hTpos y0 k)
        (centeredQuadraticClosedFormStepSize hTpos
          (centeredQuadraticClosedFormIterates hTpos y0 k))

/-- Helper for Chapter05 Theorem 5.5.1: the canonical centered continuation records at each
iterate the closed-form exact-line-search step size used by
`centeredQuadraticClosedFormIterates`. -/
noncomputable def centeredQuadraticClosedFormSteps
    {T : MatrixN} (hTpos : T.PosDef) (y0 : Point) (k : ℕ) : ℝ :=
  centeredQuadraticClosedFormStepSize hTpos (centeredQuadraticClosedFormIterates hTpos y0 k)

/-- Helper for Chapter05 Theorem 5.5.1: the canonical centered continuation is a full
exact-line-search steepest-descent sequence for `quadraticObjective T 0 0`. -/
theorem centeredQuadraticClosedFormSequence
    {T : MatrixN} (hTpos : T.PosDef) (y0 : Point) :
    IsSteepestDescentSequence
      (quadraticObjective T 0 0)
      (centeredQuadraticClosedFormIterates hTpos y0)
      (centeredQuadraticClosedFormSteps hTpos y0) := by
  intro k
  by_cases hk : centeredQuadraticClosedFormIterates hTpos y0 k = 0
  · -- At a stationary iterate, the canonical rule uses the zero exact line-search step.
    refine ⟨?_, rfl⟩
    simpa [centeredQuadraticClosedFormSteps, centeredQuadraticClosedFormStepSize, hk] using
      centeredQuadraticObjective_zero_exactLineSearch (G := T) hTpos
  · -- Otherwise the canonical rule uses the closed-form exact step from Chapter 3.
    refine ⟨?_, rfl⟩
    simpa [centeredQuadraticClosedFormSteps, centeredQuadraticClosedFormStepSize, hk] using
      centeredQuadraticObjective_closedForm_exactLineSearch (G := T) hTpos hk

/-- Helper for Chapter05 Theorem 5.5.1: any accepted exact steepest-descent step from `yk` is
no worse than the canonical closed-form first step, because both steps minimize the same
one-dimensional line-search objective on the nonnegative ray. -/
theorem centeredQuadraticFirstStep_le_closedFormFirstStep
    {T : MatrixN} {yk yk1 : Point} {αk : ℝ}
    (hTpos : T.PosDef)
    (hStep :
      yk1 = steepestDescentStep (quadraticObjective T 0 0) yk αk)
    (hExactT :
      IsExactLineSearchStepOnNonnegativeRay
        (quadraticObjective T 0 0)
        yk
        (steepestDescentDirection (quadraticObjective T 0 0) yk)
        αk) :
    quadraticObjective T 0 0 yk1 ≤
      quadraticObjective T 0 0 (centeredQuadraticClosedFormIterates hTpos yk 1) := by
  let xcf := centeredQuadraticClosedFormIterates hTpos yk
  let αcf := centeredQuadraticClosedFormSteps hTpos yk 0
  have hSeq :
      IsSteepestDescentSequence
        (quadraticObjective T 0 0)
        xcf
        (centeredQuadraticClosedFormSteps hTpos yk) := by
    simpa [xcf] using centeredQuadraticClosedFormSequence (T := T) hTpos yk
  have hCfNonneg : 0 ≤ αcf := by
    -- The canonical first-step size is feasible because it comes from an exact line search.
    exact (hSeq.exactLineSearch 0).nonneg
  have hOpt :
      lineSearchObjective
          (quadraticObjective T 0 0)
          yk
          (steepestDescentDirection (quadraticObjective T 0 0) yk)
          αk ≤
        lineSearchObjective
          (quadraticObjective T 0 0)
          yk
          (steepestDescentDirection (quadraticObjective T 0 0) yk)
          αcf := hExactT.optimal hCfNonneg
  have hUpdate :
      xcf 1 = steepestDescentStep (quadraticObjective T 0 0) yk αcf := by
    -- The canonical sequence update identifies its first iterate with the closed-form step.
    simp [xcf, αcf, centeredQuadraticClosedFormSteps, centeredQuadraticClosedFormIterates]
  -- Compare the actual accepted step against the canonical first iterate at the objective level.
  calc
    quadraticObjective T 0 0 yk1
      = quadraticObjective T 0 0
          (steepestDescentStep (quadraticObjective T 0 0) yk αk) := by
            rw [hStep]
    _ ≤ quadraticObjective T 0 0
          (steepestDescentStep (quadraticObjective T 0 0) yk αcf) := by
            simpa [lineSearchObjective, steepestDescentStep] using hOpt
    _ = quadraticObjective T 0 0 (xcf 1) := by
          rw [hUpdate]

/-- Helper for Chapter05 Theorem 5.5.1: the centered quadratic objective is strictly positive
away from the minimizer `0`. -/
theorem centeredQuadraticObjective_pos_of_ne_zero
    {T : MatrixN} (hTpos : T.PosDef) {y : Point} (hy : y ≠ 0) :
    0 < quadraticObjective T 0 0 y := by
  have hyLp : y.ofLp ≠ 0 := by
    simpa using hy
  have hQuad : 0 < dotProduct y (Matrix.toEuclideanLin T y) := by
    -- Positive definiteness makes the centered quadratic form strictly positive on nonzero
    -- vectors.
    simpa [Matrix.toEuclideanLin_apply] using hTpos.dotProduct_mulVec_pos (x := y.ofLp) hyLp
  have hHalfQuad : 0 < (1 / 2 : ℝ) * dotProduct y (Matrix.toEuclideanLin T y) := by
    nlinarith
  rw [quadraticObjective_apply]
  -- The centered objective is exactly one half of the positive quadratic form.
  simpa using hHalfQuad

/-- Helper for Chapter05 Theorem 5.5.1: one centered exact-line-search steepest-descent step
contracts the centered quadratic objective by the Kantorovich factor from Chapter 3. -/
theorem centeredQuadraticOneStepContraction_of_exactLineSearch
    {T : MatrixN} {yk yk1 : Point} {αk lambda1 lambdaN : ℝ}
    (hTpos : T.PosDef)
    (hStep :
      yk1 = steepestDescentStep (quadraticObjective T 0 0) yk αk)
    (hExactT :
      IsExactLineSearchStepOnNonnegativeRay
        (quadraticObjective T 0 0)
        yk
        (steepestDescentDirection (quadraticObjective T 0 0) yk)
        αk)
    (hyk : yk ≠ 0)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues T hTpos)) lambda1)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues T hTpos)) lambdaN)
    (hlambdaN_pos : 0 < lambdaN) :
    quadraticObjective T 0 0 yk1 ≤
      kantorovichContractionFactor lambda1 lambdaN * quadraticObjective T 0 0 yk := by
  let xcf := centeredQuadraticClosedFormIterates hTpos yk
  let αcf := centeredQuadraticClosedFormSteps hTpos yk
  have hSeq :
      IsSteepestDescentSequence
        (quadraticObjective T 0 0)
        xcf
        αcf := by
    simpa [xcf, αcf] using centeredQuadraticClosedFormSequence (T := T) hTpos yk
  have hCompare :
      quadraticObjective T 0 0 yk1 ≤ quadraticObjective T 0 0 (xcf 1) := by
    -- Compare the user-supplied exact step to the canonical closed-form first iterate.
    simpa [xcf] using
      centeredQuadraticFirstStep_le_closedFormFirstStep
        (T := T) hTpos hStep hExactT
  have hRatio :
      (quadraticObjective T 0 0 (xcf (0 + 1)) - quadraticObjective T 0 0 0) /
          (quadraticObjective T 0 0 (xcf 0) - quadraticObjective T 0 0 0) ≤
        (((lambda1 - lambdaN) / (lambda1 + lambdaN)) ^ (2 : ℕ)) := by
    -- Route correction: use the canonical closed-form sequence to access the importable
    -- Chapter03 ratio theorem at `k = 0`.
    simpa [xcf] using
      steepestDescentQuadraticObjectiveContraction
        (G := T)
        (lambdaMax := lambda1)
        (lambdaMin := lambdaN)
        hTpos
        hLambdaMax
        hLambdaMin
        hSeq
        0
        hyk
  have hyk_pos : 0 < quadraticObjective T 0 0 yk :=
    centeredQuadraticObjective_pos_of_ne_zero (T := T) hTpos hyk
  have hAbs :
      quadraticObjective T 0 0 (xcf 1) ≤
        (((lambda1 - lambdaN) / (lambda1 + lambdaN)) ^ (2 : ℕ)) *
          quadraticObjective T 0 0 yk := by
    have hXcfZero : xcf 0 = yk := by
      simp [xcf, centeredQuadraticClosedFormIterates]
    have hDenPos :
        0 < quadraticObjective T 0 0 (xcf 0) - quadraticObjective T 0 0 0 := by
      rw [hXcfZero]
      simpa [quadraticObjective_apply] using hyk_pos
    have hMul :=
      (div_le_iff₀ hDenPos).1 hRatio
    -- Clear the centered `f 0 = 0` terms after multiplying out the ratio inequality.
    rw [hXcfZero] at hMul
    simpa [quadraticObjective_apply] using hMul
  have hLambdaOrder : lambdaN ≤ lambda1 := hLambdaMin.2 hLambdaMax.1
  have hLambdaSum_pos : 0 < lambda1 + lambdaN := by
    nlinarith
  have hFactor :
      (((lambda1 - lambdaN) / (lambda1 + lambdaN)) ^ (2 : ℕ)) =
        kantorovichContractionFactor lambda1 lambdaN := by
    have hLambdaSum_ne : lambda1 + lambdaN ≠ 0 := ne_of_gt hLambdaSum_pos
    unfold kantorovichContractionFactor
    field_simp [hLambdaSum_ne]
  -- Combine the optimality comparison with the Chapter 3 contraction for the canonical step.
  calc
    quadraticObjective T 0 0 yk1 ≤ quadraticObjective T 0 0 (xcf 1) := hCompare
    _ ≤ (((lambda1 - lambdaN) / (lambda1 + lambdaN)) ^ (2 : ℕ)) *
          quadraticObjective T 0 0 yk := hAbs
    _ = kantorovichContractionFactor lambda1 lambdaN * quadraticObjective T 0 0 yk := by
          rw [hFactor]

/-- Helper for Chapter05 Theorem 5.5.1: the numerator `gkᵀ Hk gk` is the Euclidean square
`zᵀ z` for `z = sqrt(Hk) gk`. -/
theorem sqrtConjugateNumerator_eq
    {Hk : MatrixN} {gk : Point} (hHkpos : Hk.PosDef) :
    let S : MatrixN := CFC.sqrt Hk
    let z : Fin n → ℝ := (Matrix.toEuclideanLin S gk).ofLp
    dotProduct gk (Matrix.toEuclideanLin Hk gk) = z ⬝ᵥ z := by
  dsimp
  have hSsymm : (CFC.sqrt Hk).transpose = CFC.sqrt Hk := by
    -- Over `ℝ`, the positive square root is symmetric.
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg Hk).star_eq
  have hSq : CFC.sqrt Hk * CFC.sqrt Hk = Hk := by
    -- Expand `Hk` as the square of its positive square root.
    simpa [pow_two] using CFC.sq_sqrt Hk hHkpos.posSemidef.nonneg
  -- Move one `sqrt(Hk)` factor across the dot product and rewrite the remaining vector as `z`.
  calc
    dotProduct gk (Matrix.toEuclideanLin Hk gk)
        = dotProduct gk (Hk *ᵥ gk.ofLp) := by rfl
    _ = dotProduct gk (((CFC.sqrt Hk * CFC.sqrt Hk) *ᵥ gk.ofLp)) := by rw [hSq]
    _ = dotProduct gk ((CFC.sqrt Hk) *ᵥ ((CFC.sqrt Hk) *ᵥ gk.ofLp)) := by
          rw [Matrix.mulVec_mulVec]
    _ = ((CFC.sqrt Hk) *ᵥ gk.ofLp) ⬝ᵥ ((CFC.sqrt Hk) *ᵥ gk.ofLp) := by
          simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, hSsymm] using
            (Matrix.dotProduct_transpose_mulVec (A := CFC.sqrt Hk)
              (x := gk.ofLp) (y := (CFC.sqrt Hk) *ᵥ gk.ofLp))
    _ = ((Matrix.toEuclideanLin (CFC.sqrt Hk) gk).ofLp) ⬝ᵥ
          ((Matrix.toEuclideanLin (CFC.sqrt Hk) gk).ofLp) := by
          simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Chapter05 Theorem 5.5.1: the forward denominator
`(Hk gk)ᵀ G (Hk gk)` becomes `zᵀ T z` in the square-root conjugate coordinates. -/
theorem sqrtConjugateForwardDenominator_eq
    {G Hk : MatrixN} {gk : Point} (hHkpos : Hk.PosDef) :
    let S : MatrixN := CFC.sqrt Hk
    let T : MatrixN := S * G * S
    let z : Fin n → ℝ := (Matrix.toEuclideanLin S gk).ofLp
    dotProduct (Matrix.toEuclideanLin Hk gk)
      (Matrix.toEuclideanLin G (Matrix.toEuclideanLin Hk gk)) = z ⬝ᵥ (T *ᵥ z) := by
  dsimp
  have hSsymm : (CFC.sqrt Hk).transpose = CFC.sqrt Hk := by
    -- Over `ℝ`, the positive square root is symmetric.
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg Hk).star_eq
  have hSq : CFC.sqrt Hk * CFC.sqrt Hk = Hk := by
    -- Expand `Hk` as the square of its positive square root.
    simpa [pow_two] using CFC.sq_sqrt Hk hHkpos.posSemidef.nonneg
  let z0 : Fin n → ℝ := (Matrix.toEuclideanLin (CFC.sqrt Hk) gk).ofLp
  have hHkgk :
      Matrix.toEuclideanLin Hk gk = Matrix.toEuclideanLin (CFC.sqrt Hk) (Matrix.toEuclideanLin (CFC.sqrt Hk) gk) := by
    -- Rewrite the Newton-like image through two consecutive square-root actions.
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, hSq, Matrix.mulVec_mulVec]
  -- Move one `sqrt(Hk)` factor across the dot product to obtain the `zᵀ T z` form.
  calc
    dotProduct (Matrix.toEuclideanLin Hk gk)
        (Matrix.toEuclideanLin G (Matrix.toEuclideanLin Hk gk))
      = dotProduct
          (Matrix.toEuclideanLin (CFC.sqrt Hk) (Matrix.toEuclideanLin (CFC.sqrt Hk) gk))
          (Matrix.toEuclideanLin G
            (Matrix.toEuclideanLin (CFC.sqrt Hk) (Matrix.toEuclideanLin (CFC.sqrt Hk) gk))) := by
            rw [hHkgk]
    _ = z0 ⬝ᵥ (((CFC.sqrt Hk).transpose * G * CFC.sqrt Hk) *ᵥ z0) := by
          -- Normalize the bilinear form through row-vector association before flattening `T`.
          calc
            dotProduct
                (Matrix.toEuclideanLin (CFC.sqrt Hk) (Matrix.toEuclideanLin (CFC.sqrt Hk) gk))
                (Matrix.toEuclideanLin G
                  (Matrix.toEuclideanLin (CFC.sqrt Hk) (Matrix.toEuclideanLin (CFC.sqrt Hk) gk)))
              = ((CFC.sqrt Hk) *ᵥ z0) ⬝ᵥ (G *ᵥ ((CFC.sqrt Hk) *ᵥ z0)) := by
                  simp [z0, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
            _ = (((CFC.sqrt Hk) *ᵥ z0) ᵥ* G) ⬝ᵥ ((CFC.sqrt Hk) *ᵥ z0) := by
                  rw [Matrix.dotProduct_mulVec]
            _ = (z0 ᵥ* ((CFC.sqrt Hk).transpose * G)) ⬝ᵥ ((CFC.sqrt Hk) *ᵥ z0) := by
                  rw [Matrix.vecMul_mulVec]
            _ = z0 ⬝ᵥ (((CFC.sqrt Hk).transpose * G * CFC.sqrt Hk) *ᵥ z0) := by
                  rw [← Matrix.dotProduct_mulVec]
                  simp [Matrix.mulVec_mulVec, mul_assoc]
    _ = z0 ⬝ᵥ (((CFC.sqrt Hk) * G * CFC.sqrt Hk) *ᵥ z0) := by
          rw [hSsymm]

/-- Helper for Chapter05 Theorem 5.5.1: the spectral endpoint hypotheses on `Hk * G` produce the
extremal endpoint data required by Chapter03 `kantorovichInequality` for
`T = CFC.sqrt Hk * G * CFC.sqrt Hk`. -/
theorem sqrtConjugateEndpointWitnesses_of_productSpectrumBounds
    {G Hk : MatrixN} (hHkpos : Hk.PosDef)
    {lambda1 lambdaN : ℝ}
    (hTpos : (CFC.sqrt Hk * G * CFC.sqrt Hk).PosDef)
    (hlambda1 : lambda1 ∈ spectrum ℝ (Hk * G))
    (hlambdaN : lambdaN ∈ spectrum ℝ (Hk * G))
    (hSpectrum : spectrum ℝ (Hk * G) ⊆ Set.Icc lambdaN lambda1) :
    IsGreatest
        (Set.range (posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos))
        lambda1 ∧
      IsLeast
        (Set.range (posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos))
        lambdaN := by
  have hLambda1T :
      lambda1 ∈ spectrum ℝ (CFC.sqrt Hk * G * CFC.sqrt Hk) :=
    (sqrtConjugateSpectrumMem_iff (G := G) (Hk := Hk) hHkpos lambda1).2 hlambda1
  have hLambdaNT :
      lambdaN ∈ spectrum ℝ (CFC.sqrt Hk * G * CFC.sqrt Hk) :=
    (sqrtConjugateSpectrumMem_iff (G := G) (Hk := Hk) hHkpos lambdaN).2 hlambdaN
  have hRange1 :
      lambda1 ∈ Set.range (posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos) := by
    simpa [posDefEigenvalues_def, hTpos.isHermitian.spectrum_real_eq_range_eigenvalues] using
      hLambda1T
  have hRangeN :
      lambdaN ∈ Set.range (posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos) := by
    simpa [posDefEigenvalues_def, hTpos.isHermitian.spectrum_real_eq_range_eigenvalues] using
      hLambdaNT
  have hUpper :
      ∀ i,
        posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i ≤ lambda1 := by
    intro i
    have hiSpecT :
        posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i ∈
          spectrum ℝ (CFC.sqrt Hk * G * CFC.sqrt Hk) := by
      simpa [posDefEigenvalues_def] using
        hTpos.isHermitian.eigenvalues_mem_spectrum_real i
    have hiSpecProduct :
        posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i ∈
          spectrum ℝ (Hk * G) :=
      (sqrtConjugateSpectrumMem_iff (G := G) (Hk := Hk) hHkpos
        (posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i)).1 hiSpecT
    exact (hSpectrum hiSpecProduct).2
  have hLower :
      ∀ i,
        lambdaN ≤ posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i := by
    intro i
    have hiSpecT :
        posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i ∈
          spectrum ℝ (CFC.sqrt Hk * G * CFC.sqrt Hk) := by
      simpa [posDefEigenvalues_def] using
        hTpos.isHermitian.eigenvalues_mem_spectrum_real i
    have hiSpecProduct :
        posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i ∈
          spectrum ℝ (Hk * G) :=
      (sqrtConjugateSpectrumMem_iff (G := G) (Hk := Hk) hHkpos
        (posDefEigenvalues (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos i)).1 hiSpecT
    exact (hSpectrum hiSpecProduct).1
  constructor
  · rcases hRange1 with ⟨i, hi⟩
    exact (isGreatest_posDefEigenvalues_iff
      (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos lambda1).2 ⟨⟨i, hi⟩, hUpper⟩
  · rcases hRangeN with ⟨i, hi⟩
    exact (isLeast_posDefEigenvalues_iff
      (CFC.sqrt Hk * G * CFC.sqrt Hk) hTpos lambdaN).2 ⟨⟨i, hi⟩, hLower⟩

/-- Chapter05 Theorem 5.5.1 (1): if `xStar` is a minimizer of the positive-definite quadratic
objective `quadraticObjective G b c`, `Hk` is positive definite, `gk` is the gradient at `xk`,
`xk1 = xk - αk • Matrix.toEuclideanLin Hk gk` is the exact-line-search Newton-like step on the
nonnegative ray in direction `quadraticNewtonLikeDirection Hk gk`, and `λ₁`, `λₙ` are
respectively the largest and smallest eigenvalues of `Hk * G`, then the single-step objective gap
contracts by `kantorovichContractionFactor lambda1 lambdaN`. -/
theorem quadraticNewtonLikeSuboptimality_le_kantorovichContractionFactor
    {G Hk : MatrixN} {b xStar xk xk1 gk : Point} {c αk lambda1 lambdaN : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef)
    (hHkpos : Hk.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk)
    (hStep : xk1 = quadraticNewtonLikePoint Hk xk gk αk)
    (hExactLineSearch :
      IsQuadraticNewtonLikeExactLineSearchStep (quadraticObjective G b c) Hk xk gk αk)
    (hlambda1 : lambda1 ∈ spectrum ℝ (Hk * G))
    (hlambdaN : lambdaN ∈ spectrum ℝ (Hk * G))
    (hSpectrum : spectrum ℝ (Hk * G) ⊆ Set.Icc lambdaN lambda1)
    (hlambdaN_pos : 0 < lambdaN) :
    quadraticSuboptimality G b c xStar xk1 ≤
      kantorovichContractionFactor lambda1 lambdaN *
        quadraticSuboptimality G b c xStar xk := by
  let _ := hGpos.isUnit.invertible
  have hGapEq :
      quadraticSuboptimality G b c xStar xk =
        (1 / 2 : ℝ) * dotProduct gk (Matrix.toEuclideanLin G⁻¹ gk) :=
    quadraticSuboptimality_eq_half_gradientInverseQuadratic hMin hGpos hGrad
  by_cases hgk0 : gk = 0
  · have hxk1 : xk1 = xk := by
      -- A zero gradient makes the Newton-like point coincide with the current iterate.
      simpa [hStep, quadraticNewtonLikePoint, hgk0]
    have hGap0 : quadraticSuboptimality G b c xStar xk = 0 := by
      rw [hGapEq]
      simp [hgk0]
    simpa [hxk1, hGap0, kantorovichContractionFactor]
  · let u : Point := Matrix.toEuclideanLin Hk gk
    let S : MatrixN := CFC.sqrt Hk
    let T : MatrixN := S * G * S
    let yk : Point := Matrix.toEuclideanLin S⁻¹ (xk - xStar)
    let yk1 : Point := Matrix.toEuclideanLin S⁻¹ (xk1 - xStar)
    have hSunit : IsUnit S := by
      -- The positive square root is invertible because `Hk` is positive definite.
      simpa [S] using
        (CFC.isUnit_sqrt_iff Hk hHkpos.posSemidef.nonneg).2 hHkpos.isUnit
    let _ := hSunit.invertible
    have hTpos : T.PosDef := by
      -- Positive definiteness is preserved by the square-root conjugation.
      simpa [S, T] using sqrtConjugateRepresentative_posDef (G := G) (Hk := Hk) hGpos hHkpos
    have hEndpoints :
        IsGreatest (Set.range (posDefEigenvalues T hTpos)) lambda1 ∧
          IsLeast (Set.range (posDefEigenvalues T hTpos)) lambdaN := by
      -- Transport the spectrum interval on `Hk * G` to the centered representative `T`.
      simpa [S, T] using
        sqrtConjugateEndpointWitnesses_of_productSpectrumBounds
          (G := G) (Hk := Hk) hHkpos hTpos hlambda1 hlambdaN hSpectrum
    have hxk_ne : xk - xStar ≠ 0 := by
      -- A nonzero gradient forces a nonzero displacement from the minimizer.
      intro hZero
      apply hgk0
      simpa [quadraticGradient_eq_displacement_of_minimizer hMin hGpos hGrad, hZero]
    have hyk_ne : yk ≠ 0 := by
      -- Transporting by the invertible square root preserves nonzeroness.
      intro hZero
      have hRecover := congrArg (Matrix.toEuclideanLin S) hZero
      apply hxk_ne
      simpa [S, yk, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
        Matrix.mul_inv_of_invertible, Matrix.one_mulVec] using hRecover
    have hStepT :
        yk1 = steepestDescentStep (quadraticObjective T 0 0) yk αk := by
      -- The source Newton-like update is exactly the centered steepest-descent step.
      change Matrix.toEuclideanLin S⁻¹ (xk1 - xStar) =
        steepestDescentStep (quadraticObjective T 0 0) yk αk
      rw [hStep]
      simpa [S, T, yk] using
        quadraticNewtonLikePoint_eq_sqrtConjugateSteepestDescentStep
          (G := G) (Hk := Hk) (b := b) (xStar := xStar) (xk := xk) (gk := gk) (c := c)
          (α := αk) hMin hGpos hHkpos hGrad
    have hExactT :
        IsExactLineSearchStepOnNonnegativeRay
          (quadraticObjective T 0 0)
          yk
          (steepestDescentDirection (quadraticObjective T 0 0) yk)
          αk := by
      -- The exact line-search predicate is invariant under the centered transport.
      simpa [S, T, yk] using
        quadraticNewtonLikeExactLineSearch_transport
          (G := G) (Hk := Hk) (b := b) (xStar := xStar) (xk := xk) (gk := gk) (c := c)
          (α := αk) hMin hGpos hHkpos hGrad hExactLineSearch
    have hGapXk :
        quadraticSuboptimality G b c xStar xk = quadraticObjective T 0 0 yk := by
      -- Rewrite the current source gap as the centered quadratic objective.
      rw [quadraticSuboptimality_eq_quadraticEnergy_of_minimizer hMin hGpos]
      simpa [S, T, yk] using
        quadraticEnergy_eq_sqrtConjugateCenteredObjective
          (G := G) (Hk := Hk) (xStar := xStar) (x := xk) hGpos hHkpos
    have hGapXk1 :
        quadraticSuboptimality G b c xStar xk1 = quadraticObjective T 0 0 yk1 := by
      -- The accepted next gap has the same centered representation.
      rw [quadraticSuboptimality_eq_quadraticEnergy_of_minimizer hMin hGpos]
      simpa [S, T, yk1] using
        quadraticEnergy_eq_sqrtConjugateCenteredObjective
          (G := G) (Hk := Hk) (xStar := xStar) (x := xk1) hGpos hHkpos
    have hCentered :
        quadraticObjective T 0 0 yk1 ≤
          kantorovichContractionFactor lambda1 lambdaN *
            quadraticObjective T 0 0 yk := by
      -- Route correction: apply the importable Chapter 3 one-step contraction theorem in the
      -- centered `T`-world instead of the unavailable quotient theorem.
      exact centeredQuadraticOneStepContraction_of_exactLineSearch
        (T := T) hTpos hStepT hExactT hyk_ne hEndpoints.1 hEndpoints.2 hlambdaN_pos
    rw [hGapXk1, hGapXk]
    exact hCentered

/-- Companion ratio form of
`quadraticNewtonLikeSuboptimality_le_kantorovichContractionFactor` when the denominator is
strictly positive. -/
theorem quadraticNewtonLikeSuboptimalityRatio_le_kantorovichContractionFactor
    {G Hk : MatrixN} {b xStar xk xk1 gk : Point} {c αk lambda1 lambdaN : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef)
    (hHkpos : Hk.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk)
    (hStep : xk1 = quadraticNewtonLikePoint Hk xk gk αk)
    (hExactLineSearch :
      IsQuadraticNewtonLikeExactLineSearchStep (quadraticObjective G b c) Hk xk gk αk)
    (hSuboptimality : 0 < quadraticSuboptimality G b c xStar xk)
    (hlambda1 : lambda1 ∈ spectrum ℝ (Hk * G))
    (hlambdaN : lambdaN ∈ spectrum ℝ (Hk * G))
    (hSpectrum : spectrum ℝ (Hk * G) ⊆ Set.Icc lambdaN lambda1)
    (hlambdaN_pos : 0 < lambdaN) :
    quadraticSuboptimality G b c xStar xk1 / quadraticSuboptimality G b c xStar xk ≤
      kantorovichContractionFactor lambda1 lambdaN := by
  -- Divide the one-step gap contraction by the positive current gap.
  refine (div_le_iff₀ hSuboptimality).2 ?_
  simpa [mul_comm] using quadraticNewtonLikeSuboptimality_le_kantorovichContractionFactor
    hMin hGpos hHkpos hGrad hStep hExactLineSearch hlambda1 hlambdaN hSpectrum hlambdaN_pos

/-- Chapter05 Theorem 5.5.1 (2): under the same positive-definite quadratic Newton-like step
hypotheses as in `quadraticNewtonLikeSuboptimality_le_kantorovichContractionFactor`, the
quadratic energy `quadraticEnergy G xStar x` satisfies the same one-step contraction bound. -/
theorem quadraticNewtonLikeEnergy_le_kantorovichContractionFactor
    {G Hk : MatrixN} {b xStar xk xk1 gk : Point} {c αk lambda1 lambdaN : ℝ}
    (hMin : IsMinOn (quadraticObjective G b c) Set.univ xStar)
    (hGpos : G.PosDef)
    (hHkpos : Hk.PosDef)
    (hGrad : HasGradientAt (quadraticObjective G b c) gk xk)
    (hStep : xk1 = quadraticNewtonLikePoint Hk xk gk αk)
    (hExactLineSearch :
      IsQuadraticNewtonLikeExactLineSearchStep (quadraticObjective G b c) Hk xk gk αk)
    (hlambda1 : lambda1 ∈ spectrum ℝ (Hk * G))
    (hlambdaN : lambdaN ∈ spectrum ℝ (Hk * G))
    (hSpectrum : spectrum ℝ (Hk * G) ⊆ Set.Icc lambdaN lambda1)
    (hlambdaN_pos : 0 < lambdaN) :
    quadraticEnergy G xStar xk1 ≤
      kantorovichContractionFactor lambda1 lambdaN * quadraticEnergy G xStar xk := by
  -- Rewrite both energies as objective gaps at the minimizer and reuse the main contraction.
  rw [← quadraticSuboptimality_eq_quadraticEnergy_of_minimizer hMin hGpos (x := xk1)]
  rw [← quadraticSuboptimality_eq_quadraticEnergy_of_minimizer hMin hGpos (x := xk)]
  exact quadraticNewtonLikeSuboptimality_le_kantorovichContractionFactor
    hMin hGpos hHkpos hGrad hStep hExactLineSearch hlambda1 hlambdaN hSpectrum hlambdaN_pos

end
