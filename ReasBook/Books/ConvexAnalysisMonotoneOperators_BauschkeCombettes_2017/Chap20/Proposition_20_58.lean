/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_56

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.58 gives the Fitzpatrick lower bound and the corresponding
  contact-set description of a maximally monotone operator.
- `core/canonical`: the owner abstractions are `Maximal IsMonotone A`, the graph owner `A.graph`,
  and the Fitzpatrick function owner `F[A]`.
- `bridge/view`: the pointwise graph-membership criterion below is the atomic bridge from maximal
  monotonicity to the Fitzpatrick contact set; the displayed graph equality is derived from it. -/

-- Proof sketch: if `(x, u) ∈ gra A`, Proposition 20.56 (1) gives equality
-- `F_A(x, u) = ⟪x, u⟫`. If `(x, u) ∉ gra A`, maximal monotonicity implies that
-- `insert (x, u) (gra A)` is not monotone, and Proposition 20.56 (4) then rules
-- out the inequality `F_A(x, u) ≤ ⟪x, u⟫`, so necessarily `⟪x, u⟫ ≤ F_A(x, u)`.
/-- Proposition 20.58 (1): the Fitzpatrick function of a maximally monotone
operator dominates the pairing everywhere. -/
theorem Maximal.inner_le_fitzpatrickFunction
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F[A] (x, u) := by
  by_cases hxu : (x, u) ∈ A.graph
  · rw [fitzpatrickFunction_eq_inner_of_mem_graph A hA.1 hxu]
  · by_contra hinner_le
    have hfitz_le_inner : F[A] (x, u) ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
      le_of_lt (lt_of_not_ge hinner_le)
    have hinsert :
        SetRel.IsMonotone (Set.insert (x, u) (gra A)) :=
      (fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone A hA.1 x u).1 hfitz_le_inner
    have hmonorel : ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := by
      intro y v hv
      have hx : (x, u) ∈ Set.insert (x, u) (gra A) := Or.inl rfl
      have hy : (y, v) ∈ Set.insert (x, u) (gra A) := by
        exact Or.inr (by simpa [SetValuedOperator.mem_graph] using hv)
      exact hinsert hx hy
    exact hxu ((Maximal.mem_iff hA x u).2 hmonorel)

/-- A point belongs to the graph of a maximally monotone operator exactly when its Fitzpatrick
value is the pairing. -/
theorem Maximal.mem_graph_iff_fitzpatrickFunction_eq_inner
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    (x, u) ∈ A.graph ↔ F[A] (x, u) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  constructor
  · exact fitzpatrickFunction_eq_inner_of_mem_graph A hA.1
  · intro hcontact
    have hfitz_le_inner : F[A] (x, u) ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) := hcontact.le
    have hinsert :
        SetRel.IsMonotone (Set.insert (x, u) (gra A)) :=
      (fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone A hA.1 x u).1 hfitz_le_inner
    exact (Maximal.mem_iff hA x u).2 fun {y v} hv ↦
      let hx : (x, u) ∈ Set.insert (x, u) (gra A) := Or.inl rfl
      let hy : (y, v) ∈ Set.insert (x, u) (gra A) :=
        Or.inr (by simpa [SetValuedOperator.mem_graph] using hv)
      hinsert hx hy

-- Proof sketch: combine part (1) with Proposition 20.56 (1). At graph points,
-- Proposition 20.56 (1) gives equality with the pairing; conversely, if
-- `F_A(x, u) = ⟪x, u⟫`, then part (1) yields `F_A(x, u) ≤ ⟪x, u⟫`, so
-- Proposition 20.56 (4) shows that adjoining `(x, u)` preserves monotonicity.
-- Maximal monotonicity then forces `(x, u) ∈ gra A`.
/-- Proposition 20.58 (2): the graph of a maximally monotone operator is exactly
the set of points where its Fitzpatrick function coincides with the pairing. -/
theorem Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A.graph = {p | F[A] p = ((⟪p.1, p.2⟫_ℝ : ℝ) : EReal)} := by
  ext p
  exact Maximal.mem_graph_iff_fitzpatrickFunction_eq_inner hA p.1 p.2

end SetValuedOperator
