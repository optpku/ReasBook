/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialBasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: choose a point `y` in the effective domain. If `u ∈ subdifferential f x`, then
-- the defining inequality with that `y` forces `(f x : EReal) < ⊤`.
/-- Proposition 16.4 (1): if `f` has a nonempty effective domain, then every point at which the
subdifferential is nonempty lies in the effective domain. For `]-∞,+∞]`-valued functions, this is
the remaining properness content after excluding `-∞` by the codomain. -/
theorem subdifferential_domain_subset_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) :
    SetValuedOperator.dom (∂ f) ⊆ effectiveDomain f := sorry

/-- Pointwise form of Proposition 16.4 (1): subdifferentiability forces effective-domain
membership. -/
theorem SubdifferentiableAt.mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) {x : H}
    (hx : SubdifferentiableAt f x) :
    x ∈ effectiveDomain f := sorry

-- Proof sketch: rewrite `u ∈ subdifferential f x` using the defining affine-minorant inequality,
-- then move the finite value `(f x : EReal)` to the right-hand side for each `y ∈ effectiveDomain
-- f`.
/-- Proposition 16.4 (2): at a point of the effective domain, the subdifferential is the
intersection of the affine half-spaces cut out by the subgradient inequalities over the effective
domain. -/
theorem subdifferential_eq_iInter_affine_halfspaces
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (hx : x ∈ effectiveDomain f) :
    (∂ f) x =
      ⋂ y ∈ effectiveDomain f,
        {u : H | ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal} := sorry

-- Proof sketch: if `x ∈ effectiveDomain f`, use the half-space description from clause (2). Each
-- defining set is closed, and arbitrary intersections of closed sets are closed. If
-- `x ∉ effectiveDomain f`, then `(∂ f) x` is either `∅` or `Set.univ`, hence closed.
/-- Proposition 16.4 (3): the subdifferential is closed at every point. -/
theorem isClosed_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    IsClosed ((∂ f) x) := sorry

-- Proof sketch: if `x ∈ effectiveDomain f`, use the half-space description from clause (2). Each
-- defining set is convex, and arbitrary intersections of convex sets are convex. If
-- `x ∉ effectiveDomain f`, then `(∂ f) x` is either `∅` or `Set.univ`, hence convex.
/-- Proposition 16.4 (4): the subdifferential is convex at every point. -/
theorem convex_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    Convex ℝ ((∂ f) x) := sorry

-- Proof sketch: pick `u ∈ subdifferential f x`; the subgradient inequality gives
-- `f x ≤ f y - ⟪y - x, u⟫`, and continuity of the affine term transfers this to the liminf
-- characterization of lower semicontinuity at `x`.
/-- Proposition 16.4 (5): if the subdifferential of `f` at `x` is nonempty, then `f` is
lower semicontinuous at `x`. -/
theorem SubdifferentiableAt.lowerSemicontinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hxsub : SubdifferentiableAt f x) :
    LowerSemicontinuousAt f.asEReal x := sorry

-- Proof sketch: first obtain ordinary lower semicontinuity at `x` from clause (5). Then view the
-- same subgradient inequality on `WeakSpace ℝ H`; the affine functional remains weakly continuous,
-- so the same liminf argument yields weak lower semicontinuity.
/-- Proposition 16.4 (6): if the subdifferential of `f` at `x` is nonempty, then `f` is
weakly lower semicontinuous at `x`. -/
theorem SubdifferentiableAt.weaklyLowerSemicontinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hxsub : SubdifferentiableAt f x) :
    WeaklyLowerSemicontinuousAt f.asEReal x := sorry

end SubdifferentialBasicProperties

end ERealFunction
