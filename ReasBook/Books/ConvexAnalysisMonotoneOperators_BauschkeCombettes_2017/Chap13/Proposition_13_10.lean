/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section Conjugation

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: evaluate the conjugate at `0`, so the inner-product term vanishes and the supremum
-- of `x ↦ -f x` becomes the negative of the infimum of `f`.
/-- Proposition 13.10 (1): clause (i). The conjugate at the origin is the negative infimum of the
values of `f`. -/
theorem conjugate_zero_eq_neg_iInf
    (f : H → EReal) :
    f∗ 0 = - (⨅ x : H, f x) := sorry

-- Proof sketch: if `conjugate f` attains `-∞`, then every affine defect `⟪x,u⟫ - f x` is `-∞`,
-- forcing `f x = +∞` for all `x`; conversely, if `f ≡ +∞`, then every conjugate value is `-∞`.
/-- Proposition 13.10 (2): clause (ii). The conjugate attains `-∞` exactly when `f` is
identically `+∞`. -/
theorem bot_mem_range_conjugate_iff_eq_top
    (f : H → EReal) :
    (⊥ : EReal) ∈ Set.range f∗ ↔ f = ⊤ := sorry

-- Proof sketch: unfold the definition of the conjugate when `f ≡ +∞`; conversely, if
-- `conjugate f ≡ -∞`, then evaluating at `0` and using part (i) forces `inf f(H) = +∞`.
/-- Proposition 13.10 (3): clause (ii). The function `f` is identically `+∞` exactly when its
conjugate is identically `-∞`. -/
theorem conjugate_eq_bot_iff_eq_top
    (f : H → EReal) :
    f∗ = ⊥ ↔ f = ⊤ := sorry

-- Proof sketch: properness of `conjugate f` excludes `conjugate f ≡ -∞`, so part (ii) gives that
-- `f` is not identically `+∞`; combine this with part (i) to rule out `f = -∞` anywhere and obtain
-- nonempty domain.
/-- Proposition 13.10 (4): clause (iii). Properness of the conjugate forces properness of the
original function. -/
theorem is_proper_of_conjugate_is_proper
    {f : H → EReal} (hproper : IsProper f∗) :
    IsProper f := sorry

-- Proof sketch: outside `dom f`, the value `f x` is `+∞`, so the affine defect
-- `⟪x,u⟫ - f x` equals `-∞` and does not change the supremum defining `conjugate f`.
/-- Proposition 13.10 (5): clause (iv). The conjugate may be computed by taking the supremum only
over the effective domain of `f`. -/
theorem conjugate_eq_sSup_image_dom
    (f : H → EReal) (u : H) :
    f∗ u =
      sSup ((fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) '' dom f) := sorry

-- Proof sketch: rewrite epigraph membership as `f x ≤ ξ`; for fixed `x`, the quantity
-- `⟪x,u⟫ - ξ` is maximized by choosing `ξ = f x`, so the supremum over `epigraph f` agrees with
-- the supremum over `dom f`.
/-- Proposition 13.10 (6): clause (iv). The conjugate is also the supremum of the affine
functional `(x, ξ) ↦ ⟪x, u⟫ - ξ` over the epigraph of `f`. -/
theorem conjugate_eq_sSup_image_epigraph
    (f : H → EReal) (u : H) :
    f∗ u =
      sSup ((fun p : H × ℝ ↦ ((⟪p.1, u⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph f) := sorry

-- Proof sketch: expand the conjugate of the epigraph indicator on `H × ℝ`; evaluating it at
-- `(u, -1)` gives the same supremum over `epigraph f` as in part (iv).
/-- Proposition 13.10 (7): clause (v). The conjugate of `f` is the conjugate of the epigraph
indicator `ι[epigraph f]`, evaluated along the slice `u ↦ (u, -1)` in the Hilbert product
space `H × ℝ`. -/
theorem conjugate_eq_conjugate_indicator_epigraph
    (f : H → EReal) :
    f∗ =
      fun u ↦ ((ι[epigraph f]).asEReal)∗ (u, -1) := sorry

-- Proof sketch: identify the conjugate of the epigraph indicator with the support function of the
-- epigraph, then specialize to the slice `(u, -1)`.
/-- Proposition 13.10 (8): clause (v). The conjugate of `f` is the support function of the
epigraph, evaluated at `(u, -1)` in the Hilbert product space `H × ℝ`. -/
theorem conjugate_eq_support_function_epigraph
    (f : H → EReal) :
    f∗ =
      fun u ↦ σ[epigraph f] (u, -1) := sorry

-- Proof sketch: if `f` never attains `-∞`, then points of `graph f` encode exactly the values of
-- `f` that can occur with real ordinate; expanding the graph-indicator conjugate at `(u, -1)`
-- reproduces the same supremum as the definition of `conjugate f`.
/-- Proposition 13.10 (9): clause (vi). If `f` never attains `-∞`, then the conjugate is the
conjugate of the graph indicator `ι[graph f]`, evaluated along `u ↦ (u, -1)` in the Hilbert
product space `H × ℝ`. -/
theorem conjugate_eq_conjugate_indicator_graph
    {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    f∗ =
      fun u ↦ ((ι[graph f]).asEReal)∗ (u, -1) := sorry

-- Proof sketch: if `f` never attains `-∞`, then the graph-indicator conjugate agrees with the
-- support function of `graph f`; then restrict this support function to the slice `(u, -1)`.
/-- Proposition 13.10 (10): clause (vi). If `f` never attains `-∞`, then the conjugate is the
support function of the graph, evaluated at `(u, -1)` in the Hilbert product space `H × ℝ`. -/
theorem conjugate_eq_support_function_graph
    {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    f∗ =
      fun u ↦ σ[graph f] (u, -1) := sorry

end Conjugation

end

end ERealFunction
