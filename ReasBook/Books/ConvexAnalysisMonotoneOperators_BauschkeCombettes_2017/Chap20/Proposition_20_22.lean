/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_21
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: swap the coordinates of the graph. This transports monotonicity to `A⁻¹`,
-- and graph inclusion between monotone extensions is preserved by taking inverses, so maximality
-- transfers as well.
/-- Proposition 20.22 (1): the inverse of a maximally monotone set-valued operator is maximally
monotone. -/
theorem Maximal.inverse {A : SetValuedOperator H H}
    (hA : Maximal IsMonotone A) :
    Maximal IsMonotone A⁻¹ := sorry

-- Proof sketch: view `x ↦ {u} + γ • A (x + z)` as the image of `A.graph` under the affine
-- automorphism `(x, a) ↦ (x - z, u + γ • a)` of `H × H`. Positive scaling and translations
-- preserve monotonicity, and the bijective transport of graph inclusion preserves maximality.
/-- Proposition 20.22 (2): for `z, u : H` and `γ ∈ ℝ_{++}`, the affine perturbation
`x ↦ {u} + γ • A (x + z)` of a maximally monotone operator is maximally monotone. -/
theorem Maximal.output_translation_smul_input_translation
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (z u : H) (γ : Set.Ioi (0 : ℝ)) :
    Maximal IsMonotone (((fun _ : H ↦ u).toSetValuedOperator) + (γ : ℝ) • A.translate (-z)) :=
  sorry

end SetValuedOperator
