/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Example_7_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Theorem_7_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: apply Theorem 7.18 to rewrite `Cᵒ⊙ᵒ⊙` as
-- `closure (convexHull ℝ (C ∪ {0}))`; for a closed convex set containing `0`, this closure and
-- convex hull reduce to `C`.
/-- Corollary 7.19 (1): textbook clause (1), forward direction. A closed convex set containing the
origin is equal to its bipolar polar set. -/
theorem polarSet_polarSet_eq_of_isClosed_of_convex_of_zero_mem (C : Set 𝓗)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_zero : (0 : 𝓗) ∈ C) :
    Cᵒ⊙ᵒ⊙ = C := by
  -- Rewrite the bipolar by Theorem 7.18, then collapse the closed convex hull back to `C`.
  rw [polarSet_polarSet_eq_closure_convexHull_union_singleton_zero]
  apply Subset.antisymm
  · -- Closedness finishes once the convex hull is already inside `C`.
    refine closure_minimal ?_ hC_closed
    refine convexHull_min ?_ hC_convex
    rintro x (hx | hx)
    · exact hx
    · have hx0 : x = 0 := by simpa using hx
      simpa [hx0] using hC_zero
  · -- Every point of `C` already belongs to the generating set of the hull.
    intro x hx
    exact subset_closure (subset_convexHull ℝ (C ∪ ({0} : Set 𝓗)) (Or.inl hx))

-- Proof sketch: rewrite `C` as `Cᵒ⊙ᵒ⊙`, then apply Theorem 7.18 to identify it with
-- `closure (convexHull ℝ (C ∪ {0}))`, which is closed.
/-- Corollary 7.19 (2): textbook clause (1), converse closedness direction. If a set is equal to
its bipolar polar set, then it is closed. -/
theorem isClosed_of_polarSet_polarSet_eq {C : Set 𝓗} (hC : Cᵒ⊙ᵒ⊙ = C) :
    IsClosed C := by
  -- Theorem 7.18 identifies the bipolar with a closure, hence with a closed set.
  have hclosed : IsClosed (Cᵒ⊙ᵒ⊙ : Set 𝓗) := by
    rw [polarSet_polarSet_eq_closure_convexHull_union_singleton_zero]
    exact isClosed_closure
  simpa [hC] using hclosed

-- Proof sketch: rewrite `C` as `Cᵒ⊙ᵒ⊙`, then apply Theorem 7.18 to identify it with
-- `closure (convexHull ℝ (C ∪ {0}))`, which is convex.
/-- Corollary 7.19 (3): textbook clause (1), converse convexity direction. If a set is equal to
its bipolar polar set, then it is convex. -/
theorem convex_of_polarSet_polarSet_eq {C : Set 𝓗} (hC : Cᵒ⊙ᵒ⊙ = C) :
    Convex ℝ C := by
  -- Theorem 7.18 identifies the bipolar with the closure of a convex hull, which remains convex.
  have hconvex : Convex ℝ (Cᵒ⊙ᵒ⊙ : Set 𝓗) := by
    rw [polarSet_polarSet_eq_closure_convexHull_union_singleton_zero]
    simpa using (convex_convexHull ℝ (C ∪ ({0} : Set 𝓗))).closure
  simpa [hC] using hconvex

-- Proof sketch: rewrite `C` as `Cᵒ⊙ᵒ⊙`, then use Theorem 7.18; the set
-- `closure (convexHull ℝ (C ∪ {0}))` contains `0`.
/-- Corollary 7.19 (4): textbook clause (1), converse origin direction. If a set is equal to its
bipolar polar set, then it contains the origin. -/
theorem zero_mem_of_polarSet_polarSet_eq {C : Set 𝓗} (hC : Cᵒ⊙ᵒ⊙ = C) :
    (0 : 𝓗) ∈ C := by
  -- The origin is one of the generators of `closure (convexHull ℝ (C ∪ {0}))`.
  have hzero : (0 : 𝓗) ∈ Cᵒ⊙ᵒ⊙ := by
    rw [polarSet_polarSet_eq_closure_convexHull_union_singleton_zero]
    exact subset_closure (subset_convexHull ℝ (C ∪ ({0} : Set 𝓗)) (Or.inr (by simp)))
  simpa [hC] using hzero

/-- Helper for Corollary 7.19: a nonempty closed cone contains the origin because positive scalar
multiples of one of its points converge to `0`. -/
lemma zero_mem_of_nonempty_of_isClosed_of_isCone {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_cone : IsCone C) :
    (0 : 𝓗) ∈ C := by
  -- Rewrite the cone hypothesis into the positive-scalar image characterization.
  rw [isCone_iff] at hC_cone
  rcases hC_nonempty with ⟨x, hx⟩
  have htendsto :
      Filter.Tendsto (fun n : ℕ ↦ ((1 : ℝ) / n) • x) Filter.atTop (nhds (0 : 𝓗)) := by
    -- The scalar factor tends to `0`, so the rescaled sequence tends to the origin.
    have hscalar :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    have hconst : Filter.Tendsto (fun _ : ℕ ↦ x) Filter.atTop (nhds x) :=
      tendsto_const_nhds
    simpa using hscalar.smul hconst
  have hmem : ∀ᶠ n : ℕ in Filter.atTop, ((1 : ℝ) / n) • x ∈ C := by
    -- For all large enough `n`, the scalar `1 / n` is positive, so the cone contains the scaled
    -- point.
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_pos_nat
    have hscalar_pos : 0 < (1 : ℝ) / n := one_div_pos.mpr hn_pos
    have hsmul : ((1 : ℝ) / n) • x ∈ (Ioi (0 : ℝ) : Set ℝ) • C := by
      exact Set.mem_smul.mpr ⟨(1 : ℝ) / n, hscalar_pos, x, hx, rfl⟩
    exact hC_cone.symm ▸ hsmul
  exact hC_closed.mem_of_tendsto htendsto hmem

-- Proof sketch: by Example 7.15, a cone has the same polar set and polar cone; then apply the
-- previous forward bipolar statement to the closed convex set `C`.
/-- Corollary 7.19 (5): textbook clause (2), forward direction. A nonempty closed convex cone is
equal to its double polar cone. -/
theorem polarCone_polarCone_eq_of_nonempty_of_isClosed_of_convex_of_isCone (C : Set 𝓗)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_cone : IsCone C) :
    Cᵒ⊖ᵒ⊖ = C := by
  -- Route correction: first turn clause (i) into a statement about `C` itself, then rewrite both
  -- polar operators into polar cones using the cone structure on `C` and on `Cᵒ⊖`.
  have hC_zero : (0 : 𝓗) ∈ C :=
    zero_mem_of_nonempty_of_isClosed_of_isCone hC_nonempty hC_closed hC_cone
  have hpolarSet : Cᵒ⊙ᵒ⊙ = C :=
    polarSet_polarSet_eq_of_isClosed_of_convex_of_zero_mem C hC_closed hC_convex hC_zero
  have hpolarSet_eq : Cᵒ⊙ = Cᵒ⊖ :=
    polarSet_eq_polarCone_of_isCone hC_cone
  have hpolarCone_cone : IsCone (Cᵒ⊖ : Set 𝓗) := by
    -- Proposition 6.24 identifies every negative polar cone as a cone.
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_isCone C
  have houter_eq : (Cᵒ⊖ : Set 𝓗)ᵒ⊙ = (Cᵒ⊖ : Set 𝓗)ᵒ⊖ :=
    polarSet_eq_polarCone_of_isCone hpolarCone_cone
  calc
    Cᵒ⊖ᵒ⊖ = (Cᵒ⊖ : Set 𝓗)ᵒ⊙ := by
      simpa using houter_eq.symm
    _ = Cᵒ⊙ᵒ⊙ := by
      rw [← hpolarSet_eq]
    _ = C := hpolarSet

-- Proof sketch: `Cᵒ⊖` is always nonempty by Proposition 6.24, so the same holds for
-- `Cᵒ⊖ᵒ⊖`; transport this property across the assumed equality with `C`.
/-- Corollary 7.19 (6): textbook clause (2), converse nonemptiness direction. If a set is equal to
its double polar cone, then it is nonempty. -/
theorem nonempty_of_polarCone_polarCone_eq {C : Set 𝓗} (hC : Cᵒ⊖ᵒ⊖ = C) :
    C.Nonempty := by
  -- Rewrite the outer polar cone as a Chapter 6 negative polar cone and use its nonemptiness.
  have hnonempty : (Cᵒ⊖ᵒ⊖ : Set 𝓗).Nonempty := by
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_nonempty (Cᵒ⊖ : Set 𝓗)
  simpa [hC] using hnonempty

-- Proof sketch: `Cᵒ⊖` is always closed by Proposition 6.24, so its double polar cone is closed as
-- well; transport closedness across the assumed equality with `C`.
/-- Corollary 7.19 (7): textbook clause (2), converse closedness direction. If a set is equal to
its double polar cone, then it is closed. -/
theorem isClosed_of_polarCone_polarCone_eq {C : Set 𝓗} (hC : Cᵒ⊖ᵒ⊖ = C) :
    IsClosed C := by
  -- The double polar cone is a negative polar cone, and those are closed by Proposition 6.24.
  have hclosed : IsClosed (Cᵒ⊖ᵒ⊖ : Set 𝓗) := by
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_isClosed (Cᵒ⊖ : Set 𝓗)
  simpa [hC] using hclosed

-- Proof sketch: `Cᵒ⊖` is always convex by Proposition 6.24, so its double polar cone is convex as
-- well; transport convexity across the assumed equality with `C`.
/-- Corollary 7.19 (8): textbook clause (2), converse convexity direction. If a set is equal to
its double polar cone, then it is convex. -/
theorem convex_of_polarCone_polarCone_eq {C : Set 𝓗} (hC : Cᵒ⊖ᵒ⊖ = C) :
    Convex ℝ C := by
  -- The same rewrite turns the double polar cone into a convex negative polar cone.
  have hconvex : Convex ℝ (Cᵒ⊖ᵒ⊖ : Set 𝓗) := by
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_convex (Cᵒ⊖ : Set 𝓗)
  simpa [hC] using hconvex

-- Proof sketch: `Cᵒ⊖` is always a cone by Proposition 6.24, so its double polar cone is a cone as
-- well; transport this property across the assumed equality with `C`.
/-- Corollary 7.19 (9): textbook clause (2), converse conical direction. If a set is equal to its
double polar cone, then it is a cone. -/
theorem isCone_of_polarCone_polarCone_eq {C : Set 𝓗} (hC : Cᵒ⊖ᵒ⊖ = C) :
    IsCone C := by
  -- The same rewrite turns the double polar cone into a cone-valued negative polar cone.
  have hcone : IsCone (Cᵒ⊖ᵒ⊖ : Set 𝓗) := by
    rw [Set.polarCone_eq_innerDual_neg]
    simpa [Set.negativePolar] using Set.negativePolar_isCone (Cᵒ⊖ : Set 𝓗)
  simpa [hC] using hcone

-- Proof sketch: use the Hilbert-space identity `Kᗮᗮ = K.topologicalClosure` for submodules, and
-- then rewrite `K.topologicalClosure = K` by `IsClosed.submodule_topologicalClosure_eq`.
/-- Corollary 7.19 (10): textbook clause (3). A linear subspace of a real Hilbert space is closed
if and only if it is equal to its double orthogonal complement. -/
theorem isClosed_iff_orthogonal_orthogonal_eq (K : Submodule ℝ 𝓗) :
    IsClosed (K : Set 𝓗) ↔ Kᗮᗮ = K := by
  constructor
  · intro hK_closed
    -- The orthogonal-closure theorem identifies `Kᗮᗮ` with the closure of `K`.
    calc
      Kᗮᗮ = K.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure K
      _ = K := hK_closed.submodule_topologicalClosure_eq
  · intro hK
    -- Conversely, the equality with `Kᗮᗮ` identifies `K` with its closed topological closure.
    have hclosure : K.topologicalClosure = K := by
      calc
        K.topologicalClosure = Kᗮᗮ := by
          symm
          exact Submodule.orthogonal_orthogonal_eq_closure K
        _ = K := hK
    simpa [hclosure] using Submodule.isClosed_topologicalClosure K

end

end Set
