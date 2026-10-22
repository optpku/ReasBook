/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open WithLp

universe u v

namespace ERealFunction

noncomputable section

section Transpose

variable {H : Type u}

/-- The transpose of a function on `H × H` swaps the two variables. -/
abbrev transpose {α : Type v} (F : H × H → α) : H × H → α :=
  F ∘ Prod.swap

scoped postfix:max "ᵀ" => ERealFunction.transpose

-- Proof sketch: unfold `transpose` and evaluate the composition with `Prod.swap`.
/-- Evaluating the transpose exchanges the two coordinates. -/
@[simp] theorem transpose_apply {α : Type v} (F : H × H → α) (u x : H) :
    Fᵀ (u, x) = F (x, u) :=
  rfl

end Transpose

section Autoconjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: unfold the product-space `conjugate` from Definition 13.1 and rewrite the
-- product inner product as the sum of the two component inner products.
/-- Evaluating the Fenchel conjugate on the Hilbert product `H × H` splits the canonical pairing
into the two component inner products. -/
theorem conjugate_apply_pair (F : H × H → EReal) (u x : H) :
    F∗ (u, x) =
      ⨆ p : H × H, (((⟪u, p.1⟫_ℝ + ⟪x, p.2⟫_ℝ : ℝ) : EReal) - F p) := by
  change (⨆ p : H × H, (((⟪p.1, u⟫_ℝ + ⟪p.2, x⟫_ℝ : ℝ) : EReal) - F p)) = _
  congr with p
  congr 1
  rw [real_inner_comm p.1 u, real_inner_comm p.2 x]

/-- Definition 13.34: an extended-real-valued function on `H × H` is autoconjugate when its
Fenchel conjugate for the canonical pairing on the Hilbert product equals its transpose. -/
def autoconjugate (F : H × H → EReal) : Prop :=
  F∗ = Fᵀ

end Autoconjugation

end

end ERealFunction
