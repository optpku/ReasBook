/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Normed.Lp.PiLp

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (toLp)

noncomputable section

universe u v

variable {ι : Type u} [Fintype ι] {E : ι → Type v}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace ℝ (E i)]

/-- Definition 1.37: the composite weighted `l_2` formula on the finite product
`∏ i, E i`, modeling a finite block product, is the
canonical `PiLp` `L²` norm of the componentwise rescaled family. Written out in coordinates, this
is the textbook weighted `l_2` norm with strictly positive weights. -/
def compositeWeightedL2Norm (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) : ℝ :=
  ‖WithLp.toLp (2 : ENNReal) (fun i ↦ Real.sqrt (ω i : ℝ) • u i)‖

/-- The componentwise rescaling bridge from the source-facing weighted product to the canonical
`PiLp (2 : ENNReal)` owner. -/
def compositeWeightedL2LinearEquivToPiLp (ω : ι → Set.Ioi (0 : ℝ)) :
    (∀ i, E i) ≃ₗ[ℝ] PiLp (2 : ENNReal) E where
  toFun u := toLp (2 : ENNReal) (fun i ↦ Real.sqrt (ω i : ℝ) • u i)
  invFun x i := (Real.sqrt (ω i : ℝ))⁻¹ • x i
  left_inv u := by
    ext i
    have hs : Real.sqrt (ω i : ℝ) ≠ 0 := (Real.sqrt_pos.2 (ω i).2).ne'
    simp [hs]
  right_inv x := by
    ext i
    have hs : Real.sqrt (ω i : ℝ) ≠ 0 := (Real.sqrt_pos.2 (ω i).2).ne'
    simp [hs]
  map_add' u w := by
    ext i
    simp [smul_add]
  map_smul' c u := by
    ext i
    simp [smul_smul, mul_comm]

/-- The weighted rescaling bridge has norm equal to the textbook weighted `l_2` formula from
Definition 1.37. -/
theorem norm_compositeWeightedL2LinearEquivToPiLp_eq
    (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) :
    ‖compositeWeightedL2LinearEquivToPiLp ω u‖ = compositeWeightedL2Norm ω u :=
  rfl

omit [Fintype ι] in
/-- Helper for Definition 1.37: rescaling one component by `Real.sqrt (ω i : ℝ)` turns its squared
norm into the weighted squared norm contribution `(ω i : ℝ) * ‖u i‖ ^ 2`. -/
lemma rescaledComponentNormSq
    (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) (i : ι) :
    ‖Real.sqrt (ω i : ℝ) • u i‖ ^ (2 : ℕ) = (ω i : ℝ) * ‖u i‖ ^ (2 : ℕ) := by
  -- Rewrite the norm of the scalar multiple into a scalar square times the component square.
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (le_of_lt (ω i).2)]

-- Proof sketch: apply `PiLp.norm_eq_of_L2` to the rescaled family
-- `fun i ↦ √ωᵢ • uᵢ`, then simplify `‖√ωᵢ • uᵢ‖² = ωᵢ ‖uᵢ‖²` using positivity of `ω i`.
/-- The composite weighted `l_2` norm is the textbook square-root-of-weighted-sum formula. -/
theorem compositeWeightedL2Norm_def (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) :
    compositeWeightedL2Norm ω u = √(∑ i, (ω i : ℝ) * ‖u i‖ ^ (2 : ℕ)) := by
  -- Expand the owner-side `PiLp` norm into the finite `L²` coordinate formula.
  rw [compositeWeightedL2Norm, PiLp.norm_eq_of_L2]
  -- Replace each rescaled coordinate by its weighted squared contribution.
  congr 1
  exact Finset.sum_congr rfl fun i _ => rescaledComponentNormSq ω u i

/-- Pulling a `PiLp (2 : ENNReal)` point back through the weighted rescaling bridge recovers the
source weighted norm. -/
theorem compositeWeightedL2Norm_linearEquivToPiLp_symm_eq
    (ω : ι → Set.Ioi (0 : ℝ)) (x : PiLp (2 : ENNReal) E) :
    compositeWeightedL2Norm ω ((compositeWeightedL2LinearEquivToPiLp ω).symm x) = ‖x‖ := by
  simpa using
    norm_compositeWeightedL2LinearEquivToPiLp_eq ω
      ((compositeWeightedL2LinearEquivToPiLp ω).symm x) |>.symm

-- Proof sketch: square the defining formula, use the positivity hypothesis on `ω` together with
-- nonnegativity of `‖u i‖ ^ 2`, and conclude from vanishing of the weighted sum that every
-- component norm is zero.
/-- With strictly positive weights, the composite weighted `l_2`-norm vanishes exactly on the zero
family. -/
theorem compositeWeightedL2Norm_eq_zero_iff (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) :
    compositeWeightedL2Norm ω u = 0 ↔ u = 0 := by
  -- Route correction: transport the vanishing question to the `PiLp` owner norm instead of
  -- reopening the weighted-sum positivity argument.
  rw [← norm_compositeWeightedL2LinearEquivToPiLp_eq (ω := ω) (u := u), norm_eq_zero]
  -- The rescaling bridge is a linear equivalence, so only the zero family maps to zero.
  exact (compositeWeightedL2LinearEquivToPiLp ω).map_eq_zero_iff

end
