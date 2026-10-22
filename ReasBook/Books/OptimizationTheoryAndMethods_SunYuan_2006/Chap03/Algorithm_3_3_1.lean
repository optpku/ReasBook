/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_3_2

open scoped Gradient

noncomputable section

-- Domain sampling:
-- * `IsExactLineSearchStepOnNonnegativeRay` is the Chapter 2 owner for source-facing exact
--   line-search data on the nonnegative ray.
-- * `HasGradientAt`, `HasFDerivAt (∇ f)`, `fderiv ℝ (∇ f)`, `Matrix.PosDef`, and
--   `Matrix.toEuclideanCLM` are the canonical Chapter 3 owners for Newton-type gradient,
--   Hessian, and positivity data. The run structure keeps the source-facing Hessian matrix
--   data `G k`, while the namespace API below bridges `G k` to the canonical operator
--   `fderiv ℝ (∇ f) (A k)`.
-- * `ModifiedCholeskyFactorization` from Algorithm 3.3.2 is the chapter owner for the
--   Gill-Murray correction data. Its primitive data are the Hessian matrix `G`, symmetry,
--   the safeguard parameter `δ`, and `0 < δ`; its derived API is `.e`, `correctionMatrix`,
--   `correctedMatrix`, `shiftUpperBound1`, `shiftUpperBound2`, `permutedCorrectedMatrix`, and
--   `factorization`.
-- * The source-facing owner in this file is `ModifiedNewtonMethod`; its primitive data are the
--   iterate, direction, step-size, explicit gradient, safeguard-shift, and the stagewise
--   `ModifiedCholeskyFactorization` owner. The source-facing Hessian `G k`, parameter `δ k`,
--   correction `Eₖ`, corrected matrix `Ḡₖ`, and safeguard bounds are derived views.

variable {n : ℕ}

/-- Chapter03 Algorithm 3.3.1: the modified Newton method starts from an initial point
`x0 : ℝ^n` for an objective `f`, records indexed iterates `x k`, explicit gradients `g k`,
search directions `d k`, step sizes `α k`, and the stagewise Gill-Murray
modified-Cholesky owners used at each Hessian. Lean records that `g k` is the gradient of `f`
at `x k`; the associated `ModifiedCholeskyFactorization` at step `k` carries the symmetric
Hessian matrix `G k`, the safeguard parameter `δ k`, the nonnegative diagonal correction `E_k`,
the corrected matrix `Ḡ_k = G_k + E_k`, and the pivot-order factorization of `Ḡ_k`; the
safeguard shift is `0` when that correction vanishes and otherwise equals `min (b₁, b₂)`;
`Ḡ_k` is positive definite; the corrected linear system `Ḡ_k d_k = -g_k` is solved; `α k`
is an exact line-search step on the ray `a ↦ f (x k + a • d k)`; and the next iterate
satisfies `x (k + 1) = x k + α k • d k`. -/
structure ModifiedNewtonMethod (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) where
  x0 : EuclideanSpace ℝ (Fin n)
  x : ℕ → EuclideanSpace ℝ (Fin n)
  g : ℕ → EuclideanSpace ℝ (Fin n)
  modifiedCholesky : ℕ → ModifiedCholeskyFactorization n
  ν : ℕ → ℝ
  d : ℕ → EuclideanSpace ℝ (Fin n)
  α : ℕ → ℝ
  x_zero : x 0 = x0
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  hessian :
    ∀ k : ℕ,
      HasFDerivAt (∇ f)
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
              EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          ((modifiedCholesky k).G))
        (x k)
  shift_eq_zero_of_correction_eq_zero :
    ∀ k : ℕ,
      (modifiedCholesky k).correctionMatrix = 0 → ν k = 0
  shift_eq_min_of_correction_ne_zero :
    ∀ k : ℕ,
      (modifiedCholesky k).correctionMatrix ≠ 0 →
        ν k = min
          (modifiedCholesky k).shiftUpperBound1
          (modifiedCholesky k).shiftUpperBound2
  shift_eq_zero_of_posDef : ∀ k : ℕ, ((modifiedCholesky k).G).PosDef → ν k = 0
  shift_pos_of_not_posDef : ∀ k : ℕ, ¬ ((modifiedCholesky k).G).PosDef → 0 < ν k
  corrected_posDef : ∀ k : ℕ, ((modifiedCholesky k).correctedMatrix).PosDef
  linearSystem :
    ∀ k : ℕ,
      ((modifiedCholesky k).correctedMatrix).mulVec (d k) = -g k
  exactLineSearch : ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  update : ∀ k : ℕ, x (k + 1) = x k + α k • d k

/-- A modified Newton method can be used as its indexed iterate map `k ↦ x k`. -/
instance {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    CoeFun (ModifiedNewtonMethod n f) (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n)) where
  coe A := A.x

namespace ModifiedNewtonMethod

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- Evaluating a modified Newton method as a function returns its iterate sequence. -/
@[simp] theorem coe_apply (A : ModifiedNewtonMethod n f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The explicit Hessian matrix `G_k` recorded at step `k`. -/
abbrev G (A : ModifiedNewtonMethod n f) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (A.modifiedCholesky k).G

/-- The safeguard parameter `δ_k` attached to the step-`k` modified Cholesky factorization. -/
abbrev δ (A : ModifiedNewtonMethod n f) (k : ℕ) : ℝ :=
  (A.modifiedCholesky k).δ

/-- The diagonal correction matrix `E_k` attached to the step-`k` modified Cholesky
factorization. -/
abbrev correctionMatrix (A : ModifiedNewtonMethod n f) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (A.modifiedCholesky k).correctionMatrix

/-- The corrected Hessian matrix `Ḡ_k = G_k + E_k` attached to step `k`. -/
abbrev correctedMatrix (A : ModifiedNewtonMethod n f) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (A.modifiedCholesky k).correctedMatrix

/-- The rowwise Gershgorin safeguard bound `b₁` attached to step `k`. -/
abbrev shiftUpperBound1 (A : ModifiedNewtonMethod n f) (k : ℕ) : ℝ :=
  (A.modifiedCholesky k).shiftUpperBound1

/-- The diagonal-correction safeguard bound `b₂` attached to step `k`. -/
abbrev shiftUpperBound2 (A : ModifiedNewtonMethod n f) (k : ℕ) : ℝ :=
  (A.modifiedCholesky k).shiftUpperBound2

/-- The explicit gradient data agrees with the canonical gradient of `f` at every iterate. -/
theorem gradient_eq (A : ModifiedNewtonMethod n f) (k : ℕ) :
    ∇ f (A k) = A.g k :=
  (A.hasGradientAt k).gradient

/-- The explicit Hessian data agrees with the Hessian of `f` at every iterate. -/
theorem hessianAt (A : ModifiedNewtonMethod n f) (k : ℕ) :
    HasFDerivAt (∇ f)
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (A.G k))
      (A k) :=
  A.hessian k

/-- Converting the explicit Hessian matrix `G_k` through `Matrix.toEuclideanCLM` recovers the
canonical Hessian operator `fderiv ℝ (∇ f) (A k)`. -/
theorem toEuclideanCLM_G (A : ModifiedNewtonMethod n f) (k : ℕ) :
    (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (A.G k) =
      fderiv ℝ (∇ f) (A k) := by
  symm
  simpa using (A.hessianAt k).fderiv

/-- The explicit Hessian matrix `G_k` is the Euclidean matrix representative of the canonical
Hessian operator `fderiv ℝ (∇ f) (A k)`. -/
theorem G_eq_symm_fderiv_gradient (A : ModifiedNewtonMethod n f) (k : ℕ) :
    A.G k =
      (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (fderiv ℝ (∇ f) (A k)) :=
by
  have h := congrArg
    ((Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm)
    (A.toEuclideanCLM_G k)
  simpa using h

/-- The corrected linear system can be read directly against the canonical gradient
`∇ f (A k)`. -/
theorem linearSystem_eq_neg_gradient (A : ModifiedNewtonMethod n f) (k : ℕ) :
    (A.correctedMatrix k).mulVec (A.d k) = -∇ f (A k) := by
  simpa [A.gradient_eq k] using A.linearSystem k

/-- The safeguard shift `ν_k` is `0` exactly when the correction vanishes and otherwise equals
`min (b₁, b₂)`. -/
theorem shift_eq_if_correctionMatrix
    (A : ModifiedNewtonMethod n f) (k : ℕ) :
    A.ν k = if A.correctionMatrix k = 0 then 0 else
      min (A.shiftUpperBound1 k) (A.shiftUpperBound2 k) := by
  by_cases hE : A.correctionMatrix k = 0
  · rw [if_pos hE]
    exact A.shift_eq_zero_of_correction_eq_zero k hE
  · rw [if_neg hE]
    exact A.shift_eq_min_of_correction_ne_zero k hE

/-- At every step, the modified Newton run records the Hessian, the positive-definite corrected
matrix, the corrected linear system, exact line search, and the iterate update. -/
theorem step (A : ModifiedNewtonMethod n f) (k : ℕ) :
    HasFDerivAt (∇ f)
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (A.G k))
      (A k) ∧
      (A.correctedMatrix k).PosDef ∧
      (A.correctedMatrix k).mulVec (A.d k) = -A.g k ∧
      IsExactLineSearchStepOnNonnegativeRay f (A k) (A.d k) (A.α k) ∧
      A (k + 1) = A k + A.α k • A.d k :=
  ⟨A.hessianAt k, A.corrected_posDef k, A.linearSystem k, A.exactLineSearch k, A.update k⟩

/-- The update rule identifies `x (k + 1)` with the line-search step `x k + α k • d k`. -/
theorem nextIterate_eq_add_direction (A : ModifiedNewtonMethod n f) (k : ℕ) :
    A (k + 1) = A k + A.α k • A.d k :=
  A.update k

end ModifiedNewtonMethod
