/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-
Algorithm 5.0.2 lies in the finite-dimensional linear-system / Cholesky-factorization domain.

Sampled owner-style declarations:
* `Matrix.mulVec_mulVec`, the canonical owner for composing matrix-vector actions;
* `Matrix.invertibleTranspose`, the canonical bridge giving an inverse for `Lᵀ` from one for `L`;
* `mul_invOf_self`, the canonical cancellation theorem for an invertible matrix.

Best owner abstraction:
* source-facing: the two-step Cholesky solve for a factorization `A = L Lᵀ`;
* core/canonical: inverse matrices acting on vectors via `mulVec`;
* bridge/view: the theorem below identifying the source-facing solve with the canonical inverse
  expression.

Primitive data:
* a square matrix `L`,
* a right-hand side `b`,
* a factorization `A = L Lᵀ`,
* an explicit witness `hL : Invertible L`.

Derived API:
* the canonical solve vector `⅟(Lᵀ) *ᵥ (⅟L *ᵥ b)`,
* the solve identity `A *ᵥ (⅟(Lᵀ) *ᵥ (⅟L *ᵥ b)) = b`.

The previous file introduced local wrappers `choleskyForwardSolve` and `choleskySolve` around the
canonical inverse-`mulVec` expressions and then proved the final identity through those wrappers.
This refinement deletes that duplicate API and states the algorithm directly on the `Matrix`
owner surface. -/

/-- Algorithm 5.0.2: once an invertible Cholesky factorization `A = L Lᵀ` is fixed, the canonical
two-step solve
`y = ⅟L *ᵥ b`, `x = ⅟(Lᵀ) *ᵥ y`
produces a vector `x` satisfying `Ax = b`. The positive-definite and triangular hypotheses are
the usual existence conditions for such a factorization, but the solve identity itself only uses
the displayed factorization and invertibility of `L`. -/
set_option maxHeartbeats 800000
theorem choleskySolve_solves_system
    (A L : Matrix ι ι R) (b : ι → R) (hfactor : A = L * Lᵀ) (hL : Invertible L) :
    A *ᵥ (⅟(Lᵀ) *ᵥ (⅟L *ᵥ b)) = b := by
  letI : Invertible L := hL
  letI : Invertible Lᵀ := L.invertibleTranspose
  simpa [hfactor] using
    (by
      rw [mulVec_mulVec, mulVec_mulVec]
      simp : (L * Lᵀ) *ᵥ (⅟(Lᵀ) *ᵥ (⅟L *ᵥ b)) = b)
