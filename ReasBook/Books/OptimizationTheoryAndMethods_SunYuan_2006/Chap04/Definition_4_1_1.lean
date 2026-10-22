/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Domain sampling for this item:
-- * source-facing owner: `Matrix.IsConjugateFamily`
-- * core/canonical owners: `LinearMap.BilinForm.iIsOrtho`, `Matrix.toBilin'`
-- * downstream positive-definite consequence: `LinearMap.BilinForm.linearIndependent_of_iIsOrtho`

namespace Matrix

variable {m n : ℕ}

/-- Chapter04 Definition 4.1.1 (1): for a symmetric positive definite real matrix `G`, a family
`d : Fin m → Fin n → ℝ` is `G`-conjugate when every `d i` is nonzero and `d iᵀ G d j = 0` for
all `i ≠ j`. -/
class IsConjugateFamily (G : Matrix (Fin n) (Fin n) ℝ) (d : Fin m → Fin n → ℝ) : Prop where
  nonzero : ∀ i, d i ≠ 0
  iIsOrtho : G.toBilin'.iIsOrtho d

/-- Unfolding formula for `Matrix.IsConjugateFamily`. -/
theorem isConjugateFamily_iff {G : Matrix (Fin n) (Fin n) ℝ} {d : Fin m → Fin n → ℝ} :
    G.IsConjugateFamily d ↔
      (∀ i, d i ≠ 0) ∧ ∀ i j, i ≠ j → dotProduct (d i) (G *ᵥ d j) = 0 := by
  constructor
  · intro hd
    refine ⟨hd.nonzero, ?_⟩
    -- Rewrite the abstract bilinear-form orthogonality field into the textbook matrix identity.
    intro i j hij
    have hijOrtho := (LinearMap.BilinForm.iIsOrtho_def.mp hd.iIsOrtho) i j hij
    simpa only [Matrix.toBilin'_apply'] using hijOrtho
  · rintro ⟨hNonzero, hOrtho⟩
    refine ⟨hNonzero, ?_⟩
    -- Package the textbook pairwise vanishing condition back into `iIsOrtho`.
    exact LinearMap.BilinForm.iIsOrtho_def.mpr fun i j hij ↦ by
      simpa only [Matrix.toBilin'_apply'] using hOrtho i j hij

/-- Helper for Chapter04 Definition 4.1.1: a positive definite matrix gives each conjugate
direction a nonzero self-pairing under `G.toBilin'`. -/
lemma conjugateSelf_not_isOrtho_of_posDef {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) {d : Fin m → Fin n → ℝ} (hd : G.IsConjugateFamily d) :
    ∀ i, ¬ G.toBilin'.IsOrtho (d i) (d i) := by
  intro i hSelfOrtho
  -- Positive definiteness yields strict positivity of the quadratic value on each nonzero vector.
  have hPos : 0 < dotProduct (d i) (G *ᵥ d i) := by
    simpa using hG.dotProduct_mulVec_pos (hd.nonzero i)
  -- Orthogonality to itself would force that same quantity to vanish.
  have hZero : dotProduct (d i) (G *ᵥ d i) = 0 := by
    simpa [LinearMap.BilinForm.isOrtho_def, Matrix.toBilin'_apply'] using hSelfOrtho
  exact (ne_of_gt hPos) hZero

/-- Chapter04 Definition 4.1.1 (2): a `G`-conjugate family for a positive definite real matrix is
linearly independent. -/
theorem linearIndependent_of_isConjugateFamily {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) {d : Fin m → Fin n → ℝ} (hd : G.IsConjugateFamily d) :
    LinearIndependent ℝ d := by
  -- Reuse the standard linear-independence criterion for pairwise orthogonal families.
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho hd.iIsOrtho ?_
  -- Positive definiteness supplies the required nonvanishing self-pairings.
  exact conjugateSelf_not_isOrtho_of_posDef hG hd

/-- Chapter04 Definition 4.1.1 (3): when `G = 1`, `G`-conjugacy reduces to ordinary pairwise
orthogonality of the same nonzero vectors. -/
theorem isConjugateFamily_one_iff {d : Fin m → Fin n → ℝ} :
    (1 : Matrix (Fin n) (Fin n) ℝ).IsConjugateFamily d ↔
      (∀ i, d i ≠ 0) ∧ ∀ i j, i ≠ j → dotProduct (d i) (d j) = 0 := by
  -- The identity matrix acts trivially, so the general characterization simplifies immediately.
  simpa only [Matrix.one_mulVec] using
    (isConjugateFamily_iff (G := (1 : Matrix (Fin n) (Fin n) ℝ)) (d := d))

end Matrix
