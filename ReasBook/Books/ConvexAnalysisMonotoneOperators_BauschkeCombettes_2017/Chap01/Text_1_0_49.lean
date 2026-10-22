/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

namespace EReal

/-- The family of real open intervals together with the lower and upper infinite rays in `EReal`.
-/
abbrev realIntervalRayBasis : Set (Set EReal) :=
  {s | (∃ a b : ℝ, s = Ioo (a : EReal) (b : EReal)) ∨
      (∃ ξ : ℝ, s = Iio (ξ : EReal)) ∨
      ∃ ξ : ℝ, s = Ioi (ξ : EReal)}

/-- Text 1.0.49: the canonical topology on the extended real line `EReal` has as a basis the
family of all embedded real open intervals `(a, b)` together with the lower rays `[-∞, ξ)` and
the upper rays `(ξ, +∞]`, represented in Lean by `Ioo (a : EReal) (b : EReal)`, `Iio (ξ : EReal)`,
and `Ioi (ξ : EReal)`. -/
-- Proof sketch: use that `EReal` carries the order topology and identify the textbook basis as
-- the standard basis by open intervals at finite points together with the one-sided ray bases at
-- `⊥` and `⊤`.
theorem realIntervalRayBasis_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis realIntervalRayBasis := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨a, b, rfl⟩
      exact isOpen_Ioo
    · rcases hs with hs | hs
      · rcases hs with ⟨ξ, rfl⟩
        exact isOpen_Iio
      · rcases hs with ⟨ξ, rfl⟩
        exact isOpen_Ioi
  · intro x u hx hu
    by_cases hbot : x = ⊥
    · subst hbot
      rcases mem_nhds_bot_iff.mp (IsOpen.mem_nhds hu hx) with ⟨ξ, hξ⟩
      exact ⟨Iio (ξ : EReal), Or.inr <| Or.inl ⟨ξ, rfl⟩, bot_lt_coe ξ, hξ⟩
    by_cases htop : x = ⊤
    · subst htop
      rcases mem_nhds_top_iff.mp (IsOpen.mem_nhds hu hx) with ⟨ξ, hξ⟩
      exact ⟨Ioi (ξ : EReal), Or.inr <| Or.inr ⟨ξ, rfl⟩, coe_lt_top ξ, hξ⟩
    lift x to ℝ using ⟨htop, hbot⟩
    have hpre : Real.toEReal ⁻¹' u ∈ 𝓝 x := by
      simpa [nhds_coe] using (IsOpen.mem_nhds hu hx)
    rcases mem_nhds_iff_exists_Ioo_subset.mp hpre with ⟨a, b, hxab, hab⟩
    refine ⟨Ioo (a : EReal) (b : EReal), Or.inl ⟨a, b, rfl⟩, ?_, ?_⟩
    · simpa using hxab
    · simpa [image_coe_Ioo] using image_subset_iff.mpr hab

end EReal
