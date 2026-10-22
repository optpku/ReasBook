/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34

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

-- Proof sketch: expand both sides with `conjugate_apply_pair`, rewrite the transpose by
-- `transpose_apply`, and reindex the supremum on the right by the coordinate swap `Prod.swap`.
/-- Proposition 13.35: on `H × H`, Fenchel conjugation commutes with transpose `ᵀ`. -/
theorem transpose_conjugate (F : H × H → EReal) :
    (F∗)ᵀ = (Fᵀ)∗ := by
  ext ⟨u, x⟩
  simp only [transpose_apply, conjugate_apply_pair]
  exact (Equiv.prodComm H H).iSup_congr fun p ↦ by
    rcases p with ⟨a, b⟩
    simp [add_comm]

end Autoconjugation

end

end ERealFunction
