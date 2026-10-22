/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section AttouchBrezisTheorem

-- Proof sketch: compute the sum `f + g` explicitly as the indicator of `{0} × ℝ₊`, whose
-- conjugate is the indicator of `ℝ × ℝ₋`. Compute the separate conjugates and identify their
-- infimal convolution with the indicator of `ℝ × ℝ_{--}`. Finally, check that
-- `cone (dom f - dom g) = ℝ₊ × ℝ`, which is closed but not symmetric under negation, so it cannot
-- be a linear subspace.
/-- Remark 15.4 (1): on the explicit `ℝ²` example, the conjugate-of-a-sum formula from Theorem
15.3 fails even though `cone (dom f - dom g)` is a closed cone; the missing hypothesis is that
this cone be a closed linear subspace. -/
theorem attouchBrezis_counterexample_closedCone_not_closedLinearSubspace :
    let E := EuclideanSpace ℝ (Fin 2)
    let Q : Set E := {x | 0 ≤ x 0 ∧ 0 ≤ x 1}
    let L : Set E := {x | x 0 = 0}
    let f : E → EReal := fun x ↦
      if x ∈ Q then
        (((-Real.sqrt (x 0 * x 1) : ℝ) : EReal))
      else
        ⊤
    let g : E → EReal := (ι[L]).asEReal
    let Rnonpos : Set E := {x | x 1 ≤ 0}
    let Rneg : Set E := {x | x 1 < 0}
    ((f + g)∗ = (ι[Rnonpos]).asEReal ∧
      infimalConvolution f∗ g∗ = (ι[Rneg]).asEReal) ∧
      (IsClosed (cone (dom f - dom g)) ∧
        ¬ ∃ V : Submodule ℝ E, cone (dom f - dom g) = (V : Set E)) := sorry

-- Proof sketch: use the canonical indicator owners for the closed subspaces `U` and `V`.
-- Example 13.3 identifies their conjugates with the indicators of `Uᗮ` and `Vᗮ`, and the
-- biconjugate formula for closed subspaces rewrites the conjugate of the sum as the indicator of
-- `closure (Uᗮ + Vᗮ)`. Corollary 15.35 transfers the nonclosedness of `U + V` to the
-- nonclosedness of `Uᗮ + Vᗮ`, so the two sides of Theorem 15.3 are genuinely different. Meanwhile
-- `effectiveDomain f - effectiveDomain g = U - V` is a linear subspace, hence the origin belongs
-- to its relative interior.
/-- Remark 15.4 (2): for closed linear subspaces `U` and `V`, equivalently for indicators
`ι[U], ι[V] ∈ Γ₀(H)`, with nonclosed sum, replacing strong relative interior by relative
interior is not enough in Theorem 15.3. -/
theorem attouchBrezis_counterexample_relativeInterior_not_enough
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU_closed : IsClosed (U : Set H)) (hV_closed : IsClosed (V : Set H))
    (hUV_not_closed : ¬ IsClosed ((U ⊔ V : Submodule ℝ H) : Set H)) :
    let f : H → Set.Ioi (⊥ : EReal) := ι[(U : Set H)]
    let g : H → Set.Ioi (⊥ : EReal) := ι[(V : Set H)]
    let W : Submodule ℝ H := Uᗮ ⊔ Vᗮ
    (((f.asEReal + g.asEReal)∗ = (ι[closure (W : Set H)]).asEReal ∧
      infimalConvolution f.asEReal∗ g.asEReal∗ = (ι[(W : Set H)]).asEReal ∧
      ¬ IsClosed (W : Set H)) ∧
      ((f.asEReal + g.asEReal)∗ ≠ infimalConvolution f.asEReal∗ g.asEReal∗) ∧
      ((0 : H) ∈ ri (effectiveDomain f - effectiveDomain g) ∧
        ¬ IsClosed (effectiveDomain f - effectiveDomain g))) := sorry

-- Proof sketch: Example 9.22 says that a discontinuous linear functional admits no continuous
-- affine minorant, so Proposition 13.12(ii) makes its conjugate identically `⊤`. The indicator
-- `ι[{0}]` has conjugate `0`, and adding that indicator to `f` cuts the function down to `{0}`,
-- so the conjugate of the sum is identically `0`. Since the linear functional is finite
-- everywhere, its domain minus `{0}` is all of `H`.
/-- Remark 15.4 (3): lower semicontinuity is necessary in Theorem 15.3; for a discontinuous linear
functional `f` and `g = ι_{ {0} }`, the conjugate of `f + g` is `0` whereas the infimal
convolution of the separate conjugates is `+∞`, even though `dom f - dom g = H`. -/
theorem attouchBrezis_counterexample_without_lowerSemicontinuity
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ℓ : H →ₗ[ℝ] ℝ) (hℓ : ¬ Continuous ℓ) :
    let f : H → EReal := (ℓ : H → ℝ).toEReal.asEReal
    let g : H → EReal := (ι[({(0 : H)} : Set H)]).asEReal
    (((f + g)∗ = (0 : H → EReal)) ∧
      infimalConvolution f∗ g∗ = (⊤ : H → EReal)) ∧
      (dom f - dom g) = (Set.univ : Set H) := sorry

end AttouchBrezisTheorem

end ERealFunction
