/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open WithLp

universe u

namespace ERealFunction

noncomputable section

section Autoconjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Evaluating the autoconjugacy identity at `(u, x)` rewrites the conjugate value
`F∗ (u, x)` as the swapped original value `F (x, u)`. -/
theorem conjugate_swap_eq_of_autoconjugate
    {F : H × H → EReal} (hauto : autoconjugate F) (x u : H) :
    F∗ (u, x) = F (x, u) := by
  simpa [autoconjugate, transpose_apply] using congrFun hauto (u, x)

-- Proof sketch: apply the Fenchel--Young inequality to `F` at the points `(x, u)` and `(u, x)`,
-- then use the autoconjugacy identity `F∗ = Fᵀ` to rewrite `conjugate F (u, x)` as `F (x, u)`.
-- The resulting inequality
-- is `2 ⟪x, u⟫ ≤ 2 F (x, u)`, hence `⟪x, u⟫ ≤ F (x, u)`.
/-- Proposition 13.36 (1): a proper autoconjugate function on `H × H` dominates the canonical
pairing `⟪x, u⟫` pointwise. -/
theorem pairing_le_autoconjugate
    {F : H × H → EReal} (hproper : IsProper F)
    (hauto : autoconjugate F) (x u : H) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F (x, u) := by
  by_cases htop : F (x, u) = ⊤
  · simp [htop]
  have hbot := hproper.1 (x, u)
  have hfy := fenchel_young_inequality hproper (x, u) (u, x)
  rw [conjugate_swap_eq_of_autoconjugate hauto x u] at hfy
  rw [show ⟪(x, u), (u, x)⟫_ℝ = ⟪x, u⟫_ℝ + ⟪x, u⟫_ℝ by
    change ⟪x, u⟫_ℝ + ⟪u, x⟫_ℝ = ⟪x, u⟫_ℝ + ⟪x, u⟫_ℝ
    rw [real_inner_comm]] at hfy
  rw [← EReal.coe_toReal htop hbot] at hfy
  have hreal : ⟪x, u⟫_ℝ + ⟪x, u⟫_ℝ ≤ (F (x, u)).toReal + (F (x, u)).toReal := by
    exact_mod_cast hfy
  have htwo : 2 * ⟪x, u⟫_ℝ ≤ 2 * (F (x, u)).toReal := by
    simpa [two_mul] using hreal
  have hle : ⟪x, u⟫_ℝ ≤ (F (x, u)).toReal := by
    exact le_of_mul_le_mul_left htwo (show (0 : ℝ) < 2 by norm_num)
  rw [← EReal.coe_toReal htop hbot]
  exact_mod_cast hle

-- Proof sketch: evaluate the autoconjugacy identity at `(x, u)` to rewrite `F∗ (x, u)` as the
-- swapped original value `F (u, x)`, then apply Proposition 13.36 (1) to `(u, x)`.
/-- Proposition 13.36 (2): the Fenchel conjugate of a proper autoconjugate function on `H × H`
dominates the canonical pairing pointwise. -/
theorem pairing_le_conjugate_of_autoconjugate
    {F : H × H → EReal} (hproper : IsProper F)
    (hauto : autoconjugate F) (x u : H) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F∗ (x, u) := by
  rw [conjugate_swap_eq_of_autoconjugate hauto u x]
  simpa [real_inner_comm] using pairing_le_autoconjugate hproper hauto u x

end Autoconjugation

end

end ERealFunction
