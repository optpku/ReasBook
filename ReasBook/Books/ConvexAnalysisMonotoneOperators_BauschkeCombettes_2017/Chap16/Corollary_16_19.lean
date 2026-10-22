/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_17

open Set Filter
open scoped InnerProductSpace

universe u

namespace ERealFunction

section Corollary_16_19

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (h : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn h (effectiveDomain h))
variable (D : Set H) (hD_nonempty : D.Nonempty) (hD_open : IsOpen D) (hD_convex : Convex ℝ D)
variable (hD_cont : D ⊆ {x : H | ContinuousAtOnEffectiveDomain h x})

-- Proof sketch: pick a continuity point `y ∈ D`, use continuity to identify
-- `(h.asEReal + (ι[D]).asEReal)∗∗ y` with `h y`, and then apply the finite-point
-- biconjugation theorem to obtain properness of the biconjugate.
/-- The biconjugate of `h + ι_D` is proper once `D` is a nonempty open convex subset of the
effective-domain continuity set of `h`. -/
theorem isProper_biconjugate_add_indicator_of_open_convex_subset_continuity
    : IsProper (((h + ι[D]).asEReal)∗∗) := sorry

-- Proof sketch: combine properness of `(h + ι[D])∗∗` with the general
-- fact that every Fenchel conjugate belongs to `Γ(H)`, then apply this to the conjugate
-- `conjugate (h + ι[D])`.
/-- The biconjugate of `h + ι_D` belongs to the convex lower-semicontinuous class `Γ(H)`. -/
theorem biconjugate_add_indicator_mem_gamma_of_open_convex_subset_continuity
    : ((h + ι[D]).asEReal)∗∗ ∈ gamma H := sorry

-- Proof sketch: continuity points in `D` are subdifferentiability points for `h + ι[D]`, so the
-- biconjugate agrees with `h` there and has a nonempty affine-minorant set. Proposition
-- 13.46 then yields the domain inclusion into `closure D`.
/-- The effective domain of the biconjugate of `h + ι_D` is contained in `closure D`. -/
theorem dom_biconjugate_add_indicator_subset_closure_of_open_convex_subset_continuity
    : dom (((h + ι[D]).asEReal)∗∗) ⊆ closure D := sorry

-- Proof sketch: every point of `D` is a continuity point of `h + ι[D]`, hence a
-- subdifferentiability point. Proposition 16.5 identifies the biconjugate with the original
-- function at such points, and `h + ι[D]` agrees there with `h`.
/-- On `D`, the biconjugate of `h + ι_D` agrees with `h`. -/
theorem biconjugate_add_indicator_eqOn_domain_of_open_convex_subset_continuity
    : EqOn (((h + ι[D]).asEReal)∗∗) h.asEReal D := sorry

-- Proof sketch: apply Corollary 16.19 to the canonical constrained function `h + ι[D]`, then
-- identify the resulting `Γ₀(H)` extension with the Chapter 9 boundary-liminf extension owner.
/-- The canonical constrained biconjugate from Corollary 16.19 is exactly the Chapter 9
boundary-liminf extension of `h + ι_D`. -/
theorem biconjugate_add_indicator_eq_boundaryLiminfExtensionEReal_of_open_convex_subset_continuity
    : ((h + ι[D]).asEReal)∗∗ = boundaryLiminfExtensionEReal (h + ι[D]) := sorry

-- Proof sketch: first show that `(h + ι[D])∗∗` itself has the three
-- required properties: it belongs to `Γ(H)` and is proper, its domain lies in `closure D`, and it
-- agrees with `h` on `D`. Then compare any other `Γ₀(H)` extension `f` with the same support and
-- trace, and use the boundary-limit formula along segments from `D` to force pointwise equality.
/-- Corollary 16.19: if `h` is convex and `D` is a nonempty open convex subset of the
effective-domain continuity set of `h`, then every `Γ₀(H)` function whose effective domain is
contained in `closure D` and which agrees with `h` on `D` coincides with `(h + ι_D)^{**}`. -/
theorem eq_biconjugate_add_indicator_of_mem_gammaZero_subset_closure_eqOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : effectiveDomain f ⊆ closure D) (hEq : EqOn f h D) :
    f.asEReal = ((h + ι[D]).asEReal)∗∗ := sorry

-- Proof sketch: once the domain inclusion is known, points outside `closure D` lie outside the
-- domain of the biconjugate and therefore take the value `+∞`.
/-- Outside `closure D`, the biconjugate of `h + ι_D` takes the value `+∞`. -/
theorem biconjugate_add_indicator_eq_top_of_not_mem_closure
    {x : H} (hx : x ∉ closure D) :
    ((h + ι[D]).asEReal)∗∗ x = ⊤ := sorry

-- Proof sketch: if `x ∈ closure D` and `y ∈ D`, Proposition 3.44 keeps the punctured segment
-- `]x,y]` inside `D`, where the biconjugate agrees with `h`. Apply Proposition 9.14 to the
-- `Γ₀(H)` extension `((h + ι[D]).asEReal)∗∗` to identify its value at `x`
-- with the
-- right limit along that segment.
/-- At points of `closure D`, the biconjugate of `h + ι_D` is the right-limit of the values of
`h` along any segment from `x` to a point `y ∈ D`. -/
theorem tendsto_add_indicator_lineMap_to_biconjugate_of_mem_closure
    {x y : H} (hx : x ∈ closure D) (hy : y ∈ D) :
    Tendsto (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((h + ι[D]).asEReal)∗∗ x)) := sorry

end Corollary_16_19

end ERealFunction
