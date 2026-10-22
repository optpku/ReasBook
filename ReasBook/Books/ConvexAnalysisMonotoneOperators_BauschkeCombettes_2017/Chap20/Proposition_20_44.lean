/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_42

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

/-
Source/core/bridge triage:
- `source-facing`: Proposition 20.44 records the textbook properties of the partial inverse.
- `core/canonical`: the owner abstractions are `partialInverse`, `partialInverseTransform`,
  `SetValuedOperator.graph`, `SetValuedOperator.IsMonotone`, and `Maximal IsMonotone`.
- `bridge/view`: the proposition transports graph membership, monotonicity, and maximality across
  the involutive graph transform `partialInverseTransform`.
-/

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: unfold the partial inverse on `V` and on `Vᗮ`, rewrite graph membership through
-- the same transformed pair, and swap the graph coordinates to identify the result with the
-- inverse graph.
/-- Proposition 20.44 (1): clause (i). The partial inverse with respect to `V` is the inverse of
the partial inverse with respect to `Vᗮ`. -/
theorem partialInverse_eq_inverse_partialInverse_orthogonal
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎ = A₍Vᗮ₎⁻¹ := sorry

-- Proof sketch: rewrite `gra ((A⁻¹)₍Vᗮ₎)` from the definition of the partial inverse and use
-- `SetValuedOperator.mem_inverse_iff` to exchange the graph coordinates of `A`.
/-- Proposition 20.44 (2): clause (i). The partial inverse with respect to `V` is also the
partial inverse of the inverse operator with respect to `Vᗮ`. -/
theorem partialInverse_eq_partialInverse_inverse_orthogonal
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎ = (A⁻¹)₍Vᗮ₎ := sorry

/- Proposition 20.44 (3): clause (ii). Spingarn's transform is an involution; this is exactly
the owner theorem `partialInverseTransform_involutive` from Definition 20.42. -/
recall partialInverseTransform_involutive

/- Proposition 20.44 (4): clause (ii). The graph-image formula for the partial inverse is
exactly the owner theorem `graph_partialInverse_eq` from Definition 20.42. -/
recall graph_partialInverse_eq

-- Proof sketch: use the previous graph-image formula for `A₍V₎` and the
-- involutivity of `partialInverseTransform V` to apply the same transform once more and recover
-- `A.graph`.
/-- Proposition 20.44 (5): clause (ii). Applying Spingarn's transform to the graph of the partial
inverse recovers the original graph. -/
theorem graph_eq_image_partialInverseTransform_partialInverse
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A.graph = partialInverseTransform V '' (A₍V₎).graph := sorry

-- Proof sketch: expand both transformed coordinates, use orthogonality of the `V`- and
-- `Vᗮ`-components, and then combine the two projection contributions with
-- `P_V + P_{Vᗮ} = Id`.
/-- Proposition 20.44 (6): clause (iii). Spingarn's transform preserves the monotonicity pairing
between differences of graph points. -/
theorem inner_partialInverseTransform_sub_eq
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] (x₁ u₁ x₂ u₂ : H) :
    ⟪(partialInverseTransform V (x₁, u₁)).1 - (partialInverseTransform V (x₂, u₂)).1,
      (partialInverseTransform V (x₁, u₁)).2 - (partialInverseTransform V (x₂, u₂)).2⟫_ℝ =
      ⟪x₁ - x₂, u₁ - u₂⟫_ℝ := sorry

-- Proof sketch: translate graph points of `A` to graph points of `A₍V₎` via the
-- graph-image formula, then apply the pairing-preservation identity from the previous clause in
-- both directions.
/-- Proposition 20.44 (7): clause (iv). The partial inverse is monotone exactly when the original
operator is monotone. -/
theorem partialInverse_isMonotone_iff
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    A₍V₎.IsMonotone ↔ A.IsMonotone := sorry

-- Proof sketch: combine the involutive graph transform with the characterization of maximal
-- monotonicity as maximality among monotone graph extensions, so graph inclusion is transported
-- back and forth by the involution.
/-- Proposition 20.44 (8): clause (v). The partial inverse is maximally monotone exactly when the
original operator is maximally monotone. -/
theorem partialInverse_isMaximallyMonotone_iff
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] :
    Maximal IsMonotone A₍V₎ ↔ Maximal IsMonotone A := sorry

-- Proof sketch: unfold `SetValuedOperator.zeros`, rewrite `0 ∈ A₍V₎ x` as `(x, 0) ∈ (A₍V₎).graph`,
-- use the graph-image description, and compute `partialInverseTransform V (x, 0)`.
/-- Proposition 20.44 (9): clause (vi). A point is a zero of the partial inverse exactly when its
`V`- and `Vᗮ`-projections form a graph point of the original operator. -/
theorem mem_zeros_partialInverse_iff_projection_mem_graph
    (A : SetValuedOperator H H) (V : Submodule ℝ H) [V.HasOrthogonalProjection] (x : H) :
    x ∈ A₍V₎.zeros ↔ (V.starProjection x, Vᗮ.starProjection x) ∈ A.graph := sorry

end SetValuedOperator
