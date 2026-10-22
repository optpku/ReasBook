/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise SetValuedOperator

universe u v

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: rewrite membership in `A⁻¹` with `SetValuedOperator.mem_inverse_iff`. The
-- monotonicity inequality for `A⁻¹` is then exactly the monotonicity inequality for `A`
-- with the graph coordinates exchanged.
/-- Proposition 20.10 (1): the inverse of a monotone set-valued operator on a real Hilbert space
is monotone. -/
theorem IsMonotone.inverse {A : SetValuedOperator H H} (hA : A.IsMonotone) :
    A⁻¹.IsMonotone := sorry

-- Proof sketch: unpack membership in the scaled operator `γ • A`. The witnesses are scaled by
-- the nonnegative scalar `(γ : ℝ)`, so the monotonicity pairing is the original pairing for `A`
-- multiplied by `(γ : ℝ)`.
/-- Proposition 20.10 (2): every nonnegative scalar multiple of a monotone set-valued operator on
a real Hilbert space is monotone. -/
theorem IsMonotone.smul {A : SetValuedOperator H H} (hA : A.IsMonotone) (γ : NNReal) :
    (γ • A).IsMonotone := sorry

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: write elements of the sum operator as `uA + L.adjoint uB` and
-- `vA + L.adjoint vB`, with `uA ∈ A x`, `vA ∈ A y`, `uB ∈ B (L x)`, and `vB ∈ B (L y)`. Expand
-- the monotonicity pairing and use the adjoint identity
-- `⟪x - y, L.adjoint (uB - vB)⟫_ℝ = ⟪L x - L y, uB - vB⟫_ℝ` together with monotonicity of `A`
-- and `B`.
/-- Proposition 20.10 (3): if `A` and `B` are monotone set-valued operators on real Hilbert
spaces and `L : H →L[ℝ] K` is bounded linear, then `A + L^* ∘ B ∘ L`, realized as
`A + L.adjointImage B`, is monotone. -/
theorem IsMonotone.add_adjointImage
    [CompleteSpace H] [CompleteSpace K]
    {A : SetValuedOperator H H} (hA : A.IsMonotone)
    (L : H →L[ℝ] K) {B : SetValuedOperator K K} (hB : B.IsMonotone) :
    (A + L.adjointImage B).IsMonotone := sorry

end SetValuedOperator
