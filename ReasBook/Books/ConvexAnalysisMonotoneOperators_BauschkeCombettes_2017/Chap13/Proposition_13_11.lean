/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10

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

-- Proof sketch: for `μ > 0`, scale the support function and apply Proposition 13.10 (8); for
-- `μ = 0`, only the horizontal component remains, so the support function reduces to that of
-- `dom f`; for `μ < 0`, the upward vertical rays in the epigraph make the support value equal to
-- `+∞`, and nonempty domain rules out the empty-epigraph pathology.
/-- Proposition 13.11: if `dom f` is nonempty, then the support function of the epigraph of `f`,
evaluated at `(u, -μ)` in the Hilbert product space `H × ℝ`, equals `μ f*(u / μ)` for `μ > 0`,
equals the support function of `dom f` for `μ = 0`, and equals `+∞` for `μ < 0`. -/
theorem supportFunction_epigraph_eq
    {f : H → EReal} (hdom : (dom f).Nonempty) (u : H) (μ : ℝ) :
    σ[epigraph f] (u, -μ) =
      if 0 < μ then (μ : EReal) * f∗ (μ⁻¹ • u)
      else if μ = 0 then σ[dom f] u
      else ⊤ := sorry

/-- Proposition 13.11, positive branch: for `μ > 0`, the support function of the epigraph at
`(u, -μ)` is `μ f*(u / μ)`. -/
theorem supportFunction_epigraph_eq_mul_conjugate_of_pos
    {f : H → EReal} (u : H) {μ : ℝ} (hμ : 0 < μ) :
    σ[epigraph f] (u, -μ) = (μ : EReal) * f∗ (μ⁻¹ • u) := sorry

/-- Proposition 13.11, zero branch: on the horizontal slice, the support function of the epigraph
reduces to the support function of the effective domain. -/
theorem supportFunction_epigraph_eq_supportFunction_dom_zero
    {f : H → EReal} (u : H) :
    σ[epigraph f] (u, 0) = σ[dom f] u := sorry

/-- Proposition 13.11, negative branch: for `μ < 0`, the upward rays in the epigraph force the
support value at `(u, -μ)` to be `+∞`. -/
theorem supportFunction_epigraph_eq_top_of_neg
    {f : H → EReal} (hdom : (dom f).Nonempty) (u : H) {μ : ℝ} (hμ : μ < 0) :
    σ[epigraph f] (u, -μ) = ⊤ := by
  have hnot_pos : ¬ 0 < μ := by
    exact not_lt_of_ge hμ.le
  have hne : μ ≠ 0 := ne_of_lt hμ
  simpa [hnot_pos, hne] using supportFunction_epigraph_eq hdom u μ

end Conjugation

end

end ERealFunction
