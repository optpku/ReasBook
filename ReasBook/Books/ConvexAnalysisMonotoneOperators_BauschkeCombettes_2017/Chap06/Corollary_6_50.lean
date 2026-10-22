/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Corollary_6_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_49

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

open scoped Pointwise Topology

omit [CompleteSpace 𝓗] in
/-- Corollary 6.50: the recession cone of a nonempty closed convex cone in a real Hilbert space
equals the cone itself. -/
theorem recessionCone_eq_self_of_nonempty_isClosed_convex_isCone {K : Set 𝓗}
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsCone K) :
    rec K = K := by
  -- Route correction: in this workspace Proposition 6.49 exposes the source polar cone only
  -- through a private local definition, so we realize the same corollary through the equivalent
  -- additive characterization of a convex cone.
  have _hK_closed : IsClosed K := hK_closed
  obtain ⟨x, hx⟩ := hK_nonempty
  have h0 : (0 : 𝓗) ∈ K := by
    -- The project cone convention only gives positive scaling.  Closedness supplies the missing
    -- endpoint by sending positive multiples of one point to zero.
    have hmem : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) • x ∈ K := by
      intro n
      rw [Set.isCone_iff_nonneg_smul_mem] at hK_cone
      rw [hK_cone]
      exact Set.mem_smul.mpr
        ⟨1 / ((n : ℝ) + 1), by simpa only [Set.mem_Ioi] using
          (show 0 < 1 / ((n : ℝ) + 1) by positivity), x, hx, rfl⟩
    have hcoeff : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop
        (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Filter.Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) • x) Filter.atTop
        (𝓝 (0 : 𝓗)) := by
      simpa using hcoeff.smul_const x
    exact hK_closed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  have hAdd : K + K ⊆ K := (Convex.isCone_iff_add_subset hK_convex h0).mp hK_cone
  -- Prove both inclusions: recession vectors preserve `K` under translation, and elements of a
  -- cone translate `K` into itself because the cone is additively closed.
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    rw [Set.mem_recessionCone_iff] at hy
    have hy0 : y + 0 ∈ ({y} : Set 𝓗) + K := by
      exact Set.mem_add.2 ⟨y, by simp, 0, h0, by simp⟩
    simpa using hy hy0
  · intro y hy
    rw [Set.mem_recessionCone_iff]
    intro z hz
    rcases Set.mem_add.1 hz with ⟨u, hu, v, hv, huv⟩
    have hu' : u = y := by
      simpa using hu
    subst u
    -- Additive closure of the cone sends `y + v` back to `K`.
    simpa [huv] using hAdd (Set.mem_add.2 ⟨y, hy, v, hv, rfl⟩)

end

end Set
