/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

/- Source/core/bridge triage:
- `source-facing`: Definition 20.20 names maximal monotonicity of a set-valued operator.
- `core/canonical`: the owner abstraction is order-theoretic maximality among monotone extensions,
  namely `Maximal SetValuedOperator.IsMonotone A`.
- `bridge/view`: the familiar Minty-style graph-membership criterion is a characterization theorem,
  not the owner definition. -/

/- Definition 20.20: a set-valued operator is maximally monotone exactly when it is maximal, for
the canonical pointwise order on set-valued operators, among monotone extensions; this is the
specialization `Maximal SetValuedOperator.IsMonotone A` of the order-theoretic owner `Maximal`. -/
recall Maximal

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The order-theoretic owner `Maximal IsMonotone A` is equivalent to the textbook criterion that
`(x, u)` lies in `gra A` exactly when it is monotonically related to every graph point of `A`. -/
theorem Maximal.mem_iff
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x u : H) :
    u ∈ A x ↔ ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := by
  constructor
  · intro hxu y v hv
    exact (isMonotone_iff A).1 hA.1 hxu hv
  · intro hxu
    classical
    let B : SetValuedOperator H H :=
      fun y ↦ if h : y = x then Set.insert u (A x) else A y
    have hAB : A ≤ B := by
      intro y v hv
      by_cases hy : y = x
      · subst y
        simpa [B] using (Or.inr hv : v = u ∨ v ∈ A x)
      · simp [B, hy, hv]
    have hBmono : B.IsMonotone := by
      rw [isMonotone_iff]
      intro y v z w hv hw
      by_cases hy : y = x
      · subst y
        by_cases hz : z = x
        · subst z
          simp
        · have hv' : v = u ∨ v ∈ A x := by
            simpa [B] using hv
          have hw' : w ∈ A z := by
            simpa [B, hz] using hw
          rcases hv' with rfl | hvA
          · simpa using hxu hw'
          · exact (isMonotone_iff A).1 hA.1 hvA hw'
      · by_cases hz : z = x
        · subst z
          have hv' : v ∈ A y := by
            simpa [B, hy] using hv
          have hw' : w = u ∨ w ∈ A x := by
            simpa [B] using hw
          rcases hw' with rfl | hwA
          · have hxy : 0 ≤ ⟪x - y, w - v⟫_ℝ := hxu hv'
            have hswap : ⟪x - y, w - v⟫_ℝ = ⟪y - x, v - w⟫_ℝ := by
              have hxy' : x - y = -(y - x) := by
                abel_nf
              have hwv' : w - v = -(v - w) := by
                abel_nf
              calc
                ⟪x - y, w - v⟫_ℝ = ⟪-(y - x), -(v - w)⟫_ℝ := by
                  rw [hxy', hwv']
                _ = ⟪y - x, v - w⟫_ℝ := by
                  rw [inner_neg_left, inner_neg_right]
                  simp
            rw [← hswap]
            exact hxy
          · exact (isMonotone_iff A).1 hA.1 hv' hwA
        · have hv' : v ∈ A y := by
            simpa [B, hy] using hv
          have hw' : w ∈ A z := by
            simpa [B, hz] using hw
          exact (isMonotone_iff A).1 hA.1 hv' hw'
    have huB : u ∈ B x := by
      dsimp [B]
      split_ifs with hx
      · exact Or.inl rfl
      · contradiction
    exact (hA.2 hBmono hAB x) huB

/-- A set-valued operator is maximal among monotone extensions exactly when graph membership is
equivalent to the textbook monotonicity relation against every graph point. -/
theorem maximal_iff_mem_iff (A : SetValuedOperator H H) :
    Maximal IsMonotone A ↔
      ∀ x u : H, u ∈ A x ↔ ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := by
  constructor
  · intro hA x u
    exact SetValuedOperator.Maximal.mem_iff hA x u
  · intro hA
    have hmem : ∀ x u : H,
        u ∈ A x ↔ ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := @hA
    constructor
    · rw [isMonotone_iff]
      intro x u y v hxu hyv
      exact (hmem x u).1 hxu hyv
    · intro B hB hAB x u huB
      exact (hmem x u).2 fun {y v} hvA ↦
        (isMonotone_iff B).1 hB huB (hAB y hvA)

/-- Every maximally monotone operator is monotone. -/
theorem Maximal.isMonotone
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A.IsMonotone :=
  hA.1

end SetValuedOperator
