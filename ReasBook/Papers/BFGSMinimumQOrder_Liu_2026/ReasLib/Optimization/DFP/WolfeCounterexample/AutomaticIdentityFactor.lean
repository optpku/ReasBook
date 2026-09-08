module

public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedIdentityInitialization
public import ReasLib.Analysis.InnerProductSpace.FiniteDimensionalOperatorLowerBound
public import ReasLib.Analysis.InnerProductSpace.SquareRoot
public import ReasLib.LinearAlgebra.Matrix.PosDef.Operator
import Mathlib.Tactic

/-!
# Automatic identity factorization

This module removes the factorization hypotheses from the operator-level
identity-initialization theorem.  The initial positive-definite matrix is
realized as a positive operator, its positive square root supplies the change
of coordinates, and positivity plus invertibility supplies an explicit strict
Loewner lower bound.  The upper bound is the operator norm plus one; the extra
one keeps positivity of the displayed bound without any nonempty-index side
condition.

The result remains operator-valued.  It intentionally does not assert a
matrix-valued `InverseIteration` conversion.
-/

public section

noncomputable section

universe u

open Filter
open scoped InnerProduct MatrixOrder Topology

namespace DFP.WolfeCounterexample

/- The following helper is the representation-independent part of the package:
   it exposes the factor and all quantitative maps before the certificate is
   assembled. -/

/-!
The factor helper is stated for an arbitrary positive-definite initial matrix;
the strong-Wolfe trajectory is only needed by the downstream assembly theorem.
-/

/-- Helper for TASK-14: a positive-definite initial inverse Hessian determines
an invertible self-adjoint factor and explicit lower and upper Loewner bounds
for its pullback and pushforward identity operators. -/
theorem factorAndBounds_of_initialPosDef
    {n : ℕ} {H₀ : Matrix (Fin n) (Fin n) ℝ}
    (hH₀ : H₀.PosDef) :
    ∃ (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (a b q : ℝ),
      0 < a ∧ 0 < b ∧ 0 < q ∧
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) H₀ =
        L.toContinuousLinearMap.pushforward 1 ∧
      a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
        L.toContinuousLinearMap.pullback 1 ∧
      L.toContinuousLinearMap.pullback 1 ≤
        b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∧
      q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
        L.toContinuousLinearMap.pushforward 1 := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) H₀
  have hApositive : A.IsPositive := by
    dsimp only [A]
    exact Matrix.isPositive_toEuclideanCLM_iff.mpr hH₀.posSemidef
  have hAunit : IsUnit A := by
    dsimp only [A]
    exact (isUnit_map_iff
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) H₀).mpr hH₀.isUnit
  obtain ⟨a, ha, hAlower⟩ :=
    ContinuousLinearMap.exists_loewner_lowerBound_of_isPositive_isUnit
      hApositive hAunit
  have hAupper : A ≤ ‖A‖ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearMap.isPositive_le_norm_smul_one hApositive
  have hNormDiff :
      (‖A‖ + 1) • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) -
          ‖A‖ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) =
        (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    module
  have hNormLe : ‖A‖ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) ≤
      (‖A‖ + 1) • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) := by
    rw [ContinuousLinearMap.le_def, hNormDiff]
    exact ContinuousLinearMap.isPositive_one
  have hAupper' : A ≤ (‖A‖ + 1) • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) := by
    exact hAupper.trans hNormLe
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    hH₀.sqrtEquiv
  have hLself : IsSelfAdjoint L.toContinuousLinearMap := by
    dsimp only [L]
    exact hH₀.sqrtEquiv_isSelfAdjoint
  have hfactor : A = L.toContinuousLinearMap.pushforward 1 := by
    dsimp only [A, L]
    exact hH₀.sqrtEquiv_pushforward_one
  have hpull : L.toContinuousLinearMap.pullback 1 = A := by
    rw [ContinuousLinearMap.pullback_one_eq_pushforward_one
      L.toContinuousLinearMap hLself]
    exact hfactor.symm
  have hb : 0 < ‖A‖ + 1 := by positivity
  refine ⟨L, a, ‖A‖ + 1, a, ha, hb, ha, hfactor, ?_, ?_, ?_⟩
  · rw [hpull]
    exact hAlower
  · rw [hpull]
    exact hAupper'
  · rw [← hfactor]
    exact hAlower

/-- TASK-14: Every parameterized strong-Wolfe counterexample with a
positive-definite initial inverse Hessian admits an automatically normalized
identity-initialized strong-Wolfe operator certificate.  The existential
output displays the factor and the positive distortion constants
`a = q` and `b = ‖A‖ + 1` together with every map inequality consumed by
`identityInitializedStrongWolfe_of_factorized`. -/
theorem exists_identityInitializedStrongWolfe_of_initialPosDef
    {n : ℕ} (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (a b q : ℝ),
      0 < a ∧ 0 < b ∧ 0 < q ∧
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (c.iteration.inverseHessian 0) =
        L.toContinuousLinearMap.pushforward 1 ∧
      a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
        L.toContinuousLinearMap.pullback 1 ∧
      L.toContinuousLinearMap.pullback 1 ≤
        b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∧
      q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
        L.toContinuousLinearMap.pushforward 1 ∧
      Nonempty (IdentityInitializedStrongWolfeOperatorCertificate (Fin n)
        ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂) := by
  obtain ⟨L, a, b, q, ha, hb, hq, hfactor, hlower, hupper, hgradient⟩ :=
    factorAndBounds_of_initialPosDef c.initialInverseHessianPosDef
  have hm : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hM : (0 : ℝ) ≤ 3 / 2 := by norm_num
  have hc₁_lt_c₂ : c₁ < c₂ :=
    lt_of_lt_of_le hc₁_lt_two_thirds hc₂_ge_two_thirds
  have hcertificate := identityInitializedStrongWolfe_of_factorized
    c L hfactor hm hM hc₁_pos hc₁_lt_c₂ hc₂_lt_one hlower hupper hq hgradient
  exact ⟨L, a, b, q, ha, hb, hq, hfactor, hlower, hupper, hgradient, hcertificate⟩

end DFP.WolfeCounterexample
