/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_3.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_11.StrictComplementarity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

noncomputable section

open scoped BigOperators

namespace Remark922

/-- Helper for Remark 9.22: the least-squares functional `(9.2)` from Example
9.1. -/
@[expose] def lsFunctional (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦ ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2

/-- Helper for Remark 9.22: the defining formula for `lsFunctional`. -/
theorem lsFunctional_def (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (α : ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    lsFunctional n K d α f =
      ‖Matrix.toEuclideanLin K f - d‖ ^ 2 / 2 + (α / 2) * ‖f‖ ^ 2 := rfl

/-- Helper for Remark 9.22: the shifted Poisson-likelihood functional `(9.5)`
from Example 9.1. -/
@[expose] def likelihoodFunctional (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦
    (∑ i : Fin n, Matrix.toEuclideanLin K f i + σ2) -
      ∑ i : Fin n, (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2) +
        (α / 2) * ‖f‖ ^ 2

/-- Helper for Remark 9.22: the defining formula for `likelihoodFunctional`. -/
theorem likelihoodFunctional_def (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    likelihoodFunctional n K d σ2 α f =
      (∑ i : Fin n, Matrix.toEuclideanLin K f i + σ2) -
        ∑ i : Fin n, (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2) +
          (α / 2) * ‖f‖ ^ 2 := rfl

/-- Helper for Remark 9.22: the quadratic functional
`f ↦ c + ⟪b, f⟫ + (1 / 2) ⟪A f, f⟫`. -/
@[expose] def quadraticFunctional (c : ℝ) (b : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦
    c + inner ℝ b f +
      (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A f) f

/-- Helper for Remark 9.22: the defining formula for `quadraticFunctional`. -/
theorem quadraticFunctional_def (c : ℝ) (b : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    quadraticFunctional c b A f =
      c + inner ℝ b f +
        (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A f) f := rfl

/-- Helper for Remark 9.22: a functional is quadratic when it has a symmetric
matrix representation. -/
def IsQuadraticFunctional (J : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ c b A, A.IsSymm ∧ J = quadraticFunctional c b A

/-- Helper for Remark 9.22: explicit expansion of `IsQuadraticFunctional`. -/
theorem isQuadraticFunctional_iff (J : EuclideanSpace ℝ (Fin n) → ℝ) :
    IsQuadraticFunctional J ↔
      ∃ c b A, A.IsSymm ∧ J = quadraticFunctional c b A := Iff.rfl

/-- Helper for Remark 9.22: the active coordinates of the orthant constraint
are exactly the vanishing coordinates of `f`. -/
@[expose] def activeCoordinates {n : ℕ} (f : EuclideanSpace ℝ (Fin n)) : Set (Fin n) :=
  {i | f i = 0}

/-- Helper for Remark 9.22: membership in `activeCoordinates f` is equivalent to
the vanishing of the corresponding coordinate. -/
theorem mem_activeCoordinates {n : ℕ} (f : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    i ∈ activeCoordinates f ↔ f i = 0 := Iff.rfl

/-- Helper for Remark 9.22: degeneracy is equivalent to an active coordinate
whose gradient component vanishes. -/
theorem not_strictComplementarity_iff_exists_mem_active_and_gradient_eq_zero
    {n : ℕ}
    {J : EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (hcrit : NonnegativeOrthant.IsCriticalPoint J f) :
    ¬ NonnegativeOrthant.StrictComplementarity J f ↔
      ∃ i : Fin n, i ∈ activeCoordinates f ∧ gradient J f i = 0 := by
  classical
  rw [NonnegativeOrthant.strictComplementarity_iff]
  constructor
  · intro hnot
    push Not at hnot
    rcases hnot with ⟨i, hfi, hgrad_nonpos⟩
    have hgrad : gradient J f i = 0 := le_antisymm hgrad_nonpos (hcrit.gradientNonneg i)
    exact ⟨i, (mem_activeCoordinates f i).2 hfi, hgrad⟩
  · rintro ⟨i, hi, hgrad⟩ hsc
    have hfi : f i = 0 := (mem_activeCoordinates f i).1 hi
    have hpos : 0 < gradient J f i := hsc i hfi
    simp [hgrad] at hpos

/-- The least-squares functional `(9.2)` from Example 9.1 is a quadratic
functional with constant term `‖d‖ ^ 2 / 2`, linear term `-Kᵀ d`, and matrix
part `Kᵀ K + α I`. This is the reusable quadratic owner behind the one-step
Newton observation in Remark 9.22. -/
theorem lsFunctional_eq_quadraticFunctional (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    lsFunctional n K d α =
      quadraticFunctional
        (‖d‖ ^ 2 / 2)
        (-Matrix.toEuclideanLin K.transpose d)
        (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  funext f
  -- Move the transpose action across the inner product so the mixed term depends on `Kᵀ d`.
  have hKAdj : LinearMap.adjoint (K.toEuclideanLin) = (K.transpose).toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
  have hCross :
      inner ℝ (Matrix.toEuclideanLin K f) d =
        inner ℝ (Matrix.toEuclideanLin K.transpose d) f := by
    calc
      inner ℝ (Matrix.toEuclideanLin K f) d
          = inner ℝ f (LinearMap.adjoint (K.toEuclideanLin) d) := by
              simpa using
                (LinearMap.adjoint_inner_right
                  (A := K.toEuclideanLin) (x := f) (y := d)).symm
      _ = inner ℝ f ((K.transpose).toEuclideanLin d) := by
            rw [hKAdj]
      _ = inner ℝ (Matrix.toEuclideanLin K.transpose d) f := by
            rw [real_inner_comm]
  have hCross' :
      inner ℝ d (Matrix.toEuclideanLin K f) =
        inner ℝ (Matrix.toEuclideanLin K.transpose d) f := by
    rw [real_inner_comm]
    exact hCross
  have hQuadratic :
      inner ℝ (Matrix.toEuclideanLin K f) (Matrix.toEuclideanLin K f) =
        inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f := by
    calc
      inner ℝ (Matrix.toEuclideanLin K f) (Matrix.toEuclideanLin K f)
          = inner ℝ f (LinearMap.adjoint (K.toEuclideanLin) (Matrix.toEuclideanLin K f)) := by
              simpa using
                (LinearMap.adjoint_inner_right
                  (A := K.toEuclideanLin) (x := f) (y := Matrix.toEuclideanLin K f)).symm
      _ = inner ℝ f (Matrix.toEuclideanLin K.transpose (Matrix.toEuclideanLin K f)) := by
            rw [hKAdj]
      _ = inner ℝ f (Matrix.toEuclideanLin (K.transpose * K) f) := by
            simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
      _ = inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f := by
            rw [real_inner_comm]
  have hMatrixPart :
      inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f + α * inner ℝ f f =
        inner ℝ
          (Matrix.toEuclideanLin
            (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
    -- Assemble the Gramian part and the Tikhonov shift into one matrix action.
    have hAddApply :
        Matrix.toEuclideanLin
            (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f =
          Matrix.toEuclideanLin (K.transpose * K) f + α • f := by
      simp [Matrix.toLpLin_apply]
    calc
      inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f + α * inner ℝ f f
          = inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f + inner ℝ (α • f) f := by
              rw [real_inner_smul_left]
      _ = inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f + α • f) f := by
            rw [inner_add_left]
      _ =
          inner ℝ
            (Matrix.toEuclideanLin
              (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
            rw [← hAddApply]
  -- Expand the residual norm, rewrite the mixed and quadratic terms, and regroup.
  rw [lsFunctional_def, quadraticFunctional_def, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, inner_sub_right, hCross, hCross', hQuadratic]
  calc
    (inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f -
          inner ℝ (Matrix.toEuclideanLin K.transpose d) f -
            (inner ℝ (Matrix.toEuclideanLin K.transpose d) f - inner ℝ d d)) /
        2 +
        (α / 2) * ‖f‖ ^ 2
        =
      ‖d‖ ^ 2 / 2 - inner ℝ (Matrix.toEuclideanLin K.transpose d) f +
        (1 / 2 : ℝ) *
          (inner ℝ (Matrix.toEuclideanLin (K.transpose * K) f) f + α * inner ℝ f f) := by
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
            ring
    _ =
      ‖d‖ ^ 2 / 2 - inner ℝ (Matrix.toEuclideanLin K.transpose d) f +
        (1 / 2 : ℝ) *
          inner ℝ
            (Matrix.toEuclideanLin
              (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
            rw [hMatrixPart]
    _ =
      ‖d‖ ^ 2 / 2 + inner ℝ (-Matrix.toEuclideanLin K.transpose d) f +
        (1 / 2 : ℝ) *
          inner ℝ
            (Matrix.toEuclideanLin
              (K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ)) f) f := by
            rw [sub_eq_add_neg, ← inner_neg_left]

/-- The least-squares functional `(9.2)` is quadratic in the sense of
`Remark922.IsQuadraticFunctional`. -/
theorem lsFunctional_isQuadraticFunctional (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    IsQuadraticFunctional (lsFunctional n K d α) := by
  -- Package the normalized least-squares expression with the symmetric Gramian-plus-shift matrix.
  rw [isQuadraticFunctional_iff]
  refine ⟨‖d‖ ^ 2 / 2, -Matrix.toEuclideanLin K.transpose d,
    K.transpose * K + α • (1 : Matrix (Fin n) (Fin n) ℝ), ?_, ?_⟩
  · exact
      (Matrix.isSymm_transpose_mul_self K).add
        ((Matrix.isSymm_one : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm).smul α)
  · exact lsFunctional_eq_quadraticFunctional n K d α

end Remark922

/-- Remark 9.22. The least-squares functional `(9.2)` from Example 9.1 is
quadratic. -/
theorem example91LsFunctional_isQuadraticFunctional (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    Remark922.IsQuadraticFunctional (Remark922.lsFunctional n K d α) :=
  Remark922.lsFunctional_isQuadraticFunctional n K d α

/- Remark 9.22.

The source remark compares runs for the least-squares objective `(9.2)` and the
shifted Poisson-likelihood objective `(9.5)`, interprets histograms of active
gradient components through Definition 9.12, observes a two-to-one GPRN
iteration-count gap in favor of least squares, notes the one-step Newton effect
for the quadratic least-squares objective after active-set identification, and
compares GPRN against plain gradient projection.

The current repository snapshot does not yet provide checked owners for the
figure data, histogram objects, or concrete GPRN run sequences. This file
therefore keeps the missing empirical layers as explicit blocked clause
surfaces, while exposing the source-faithful reusable owners that are already
available: the two objectives, the active-coordinate form of degeneracy from
Definition 9.12, the quadraticity of `(9.2)`, and the projected-gradient
iterate owner used in the final comparison.
-/

/- Remark 9.22. Backend owner for the least-squares functional `(9.2)`. -/
#check Remark922.lsFunctional

/- Backend owner for the shifted Poisson-likelihood functional `(9.5)`. -/
#check Remark922.likelihoodFunctional

/- Remark 9.22. The active-coordinate form of Definition 9.12 that underlies
the histogram interpretation of degeneracy. -/
#check Remark922.not_strictComplementarity_iff_exists_mem_active_and_gradient_eq_zero

/- Remark 9.22.
The source compares Figures 9.5 and 9.6 by reporting that the GPRN run for the
shifted Poisson-likelihood objective `(9.5)` used twice as many outer
iterations as the GPRN run for the least-squares objective `(9.2)`. The exact
figure/run owner is still absent, so this remains an explicit local surface. -/
#check
  ∀ (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (σ2 α : ℝ)
    (gprnOuterIterationCount : (EuclideanSpace ℝ (Fin n) → ℝ) → ℕ),
      gprnOuterIterationCount (Remark922.likelihoodFunctional n K d σ2 α) =
        2 * gprnOuterIterationCount (Remark922.lsFunctional n K d α)

/- Remark 9.22.
The least-squares objective `(9.2)` is quadratic, so any later checked rule
saying that quadratic objectives converge in one reduced-Newton step after the
optimal active set has been identified applies immediately to
`Remark922.lsFunctional`. The reduced-Hessian-based reduced-Newton stage owner
is now available through `GPRN`, but the specific one-step convergence theorem
for the Chapter 9 reduced-Newton stage is still absent, so this remains an
explicit blocked source-facing surface. -/
#check
  ∀ (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (α : ℝ)
    (hasOneStepNewtonStageAfterActiveSetIdentification :
      (EuclideanSpace ℝ (Fin n) → ℝ) → Prop),
      hasOneStepNewtonStageAfterActiveSetIdentification
        (Remark922.lsFunctional n K d α)

/- Remark 9.22.
The comparison with Figure 9.4 says that GPRN converges much more rapidly than
plain gradient projection on the shifted Poisson-likelihood test problem. The
projected-gradient and GPRN iterate owners are now available, but the
figure-derived comparison metric is not, so the comparison is kept as an
explicit source-facing surface. -/
#check
  ∀ (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (σ2 α : ℝ) (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (σGP σGPRN τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n))
    (convergesMoreRapidly :
      (ℕ → EuclideanSpace ℝ (Fin n)) →
        (ℕ → EuclideanSpace ℝ (Fin n)) → Prop),
      convergesMoreRapidly
        (GPRN.iterates
          P
          (Remark922.likelihoodFunctional n K d σ2 α)
          σGPRN
          τ
          f0
          s)
        (GradientProjection.iterates
          P
          (Remark922.likelihoodFunctional n K d σ2 α)
          σGP
          f0)
