/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.DualPairing.Monotone
public import Mathlib.Order.Zorn

/-!
# Maximal monotone extensions
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- Every monotone subset of a dual-pairing product is contained in a maximal
monotone subset. -/
theorem exists_maximal_monotone_superset (P : DualPairing X Xstar)
    {S : Set (X × Xstar)} (hS : P.IsMonotone S) :
    ∃ G, S ⊆ G ∧ Maximal P.IsMonotone G := by
  let family : Set (Set (X × Xstar)) := {T | P.IsMonotone T}
  have hUnion : ∀ c ⊆ family, IsChain (· ⊆ ·) c → c.Nonempty →
      P.IsMonotone (⋃₀ c) := by
    intro c hc hchain hne
    apply (P.isMonotone_iff_subset_polar (⋃₀ c)).2
    intro z hz
    rw [P.mem_monotonePolar]
    intro w hw
    rcases Set.mem_sUnion.mp hz with ⟨T, hT, hzT⟩
    rcases Set.mem_sUnion.mp hw with ⟨U, hU, hwU⟩
    rcases hchain.total hT hU with hTU | hUT
    · have hUmono : P.IsMonotone U := hc hU
      have hzpolar := (P.isMonotone_iff_subset_polar U).1 hUmono (hTU hzT)
      rw [P.mem_monotonePolar] at hzpolar
      exact hzpolar w hwU
    · have hTmono : P.IsMonotone T := hc hT
      have hzpolar := (P.isMonotone_iff_subset_polar T).1 hTmono hzT
      rw [P.mem_monotonePolar] at hzpolar
      exact hzpolar w (hUT hwU)
  obtain ⟨G, hSG, hG⟩ := zorn_subset_nonempty family
      (by
        intro c hc hchain hne
        exact ⟨⋃₀ c, hUnion c hc hchain hne,
          fun T hT z hz ↦ Set.mem_sUnion.mpr ⟨T, hT, hz⟩⟩)
      S (show S ∈ family from hS)
  exact ⟨G, hSG, hG⟩

end DualPairing
