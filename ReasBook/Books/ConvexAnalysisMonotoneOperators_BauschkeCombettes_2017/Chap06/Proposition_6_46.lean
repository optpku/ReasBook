/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_45

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

-- Proof sketch: every vector orthogonal to the direction of `affineSpan ℝ C` annihilates each
-- difference `y - x` with `y ∈ C`, hence belongs to `N[C] x`. If `N[C] x = {0}`, then the
-- orthogonal complement of `(affineSpan ℝ C).direction` is trivial, so the direction is `⊤`.
-- Therefore `affineSpan ℝ C = ⊤`, which makes `interior C` nonempty in finite dimension; then `x`
-- lies in the interior.
/-- Helper for Proposition 6.46: in finite dimension, a convex set has trivial normal cone at
`x ∈ C` only when `x` is an interior point. -/
theorem mem_interior_of_normalCone_eq_singleton_zero_of_convex_of_finiteDimensional
    {C : Set 𝓗} {x : 𝓗} (hC_convex : Convex ℝ C) (hx : x ∈ C)
    (hN : N[C] x = ({0} : Set 𝓗)) :
    x ∈ interior C := by
  let A : AffineSubspace ℝ 𝓗 := affineSpan ℝ C
  have hxA : x ∈ (A : Set 𝓗) := subset_affineSpan ℝ C hx
  have horth_subset : (((A.directionᗮ : Submodule ℝ 𝓗) : Set 𝓗)) ⊆ N[C] x := by
    intro u hu
    rw [normalCone_of_mem hx]
    change innerSupremumOn (C - ({x} : Set 𝓗)) u ≤ 0
    have :
        innerSupremumOn (C - ({x} : Set 𝓗)) u ≤ innerInfimumOn ({0} : Set 𝓗) u :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({x} : Set 𝓗)) ({0} : Set 𝓗) u).2
        (fun v hv z hz ↦ by
          have hz' : z = 0 := by simpa using hz
          subst hz'
          rcases hv with ⟨y, hy, w, hw, hv⟩
          have hw' : w = x := by simpa using hw
          have hyA : y ∈ (A : Set 𝓗) := subset_affineSpan ℝ C hy
          have hdir : y - x ∈ A.direction := by
            rw [show y - x = y -ᵥ x by rfl]
            exact A.vsub_mem_direction hyA hxA
          have hle : ⟪y - x, u⟫_ℝ ≤ 0 :=
            le_of_eq <| Submodule.inner_right_of_mem_orthogonal hdir hu
          have hv' : v = y - x := by
            simpa [hw'] using hv.symm
          simpa [hv'] using hle)
    simpa using this
  have horth_eq_bot : A.directionᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u ∈ ({0} : Set 𝓗) := by
      rw [← hN]
      exact horth_subset hu
    simpa using this
  letI : A.direction.HasOrthogonalProjection := by infer_instance
  have hdir_top : A.direction = ⊤ := Submodule.orthogonal_eq_bot_iff.mp horth_eq_bot
  have hA_top : A = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x, hxA⟩).1 hdir_top
  have hC_int_nonempty : (interior C).Nonempty :=
    (hC_convex.interior_nonempty_iff_affineSpan_eq_top).2 (by simpa [A] using hA_top)
  exact (mem_interior_iff_normalCone_eq_singleton_zero_of_convex hC_convex hC_int_nonempty hx).2 hN

-- Proof sketch: if `x ∈ interior C`, then `interior C` is nonempty and Proposition 6.45 gives the
-- trivial-normal-cone characterization `(i) → (iii)`. Conversely, the finite-dimensional helper
-- proves `(iii) → (i)`, and Proposition 6.44 identifies `(ii)` with `(iii)`.
/-- Proposition 6.46: for a convex subset `C` of a finite-dimensional real Hilbert space and a
point `x ∈ C`, the following are equivalent: `x ∈ interior C`, the tangent cone `T[C] x` is the
whole space, and the normal cone `N[C] x` is trivial. -/
theorem
    mem_interior_tfae_tangentCone_eq_univ_normalCone_eq_singleton_zero_of_convex_finiteDimensional
    {C : Set 𝓗} {x : 𝓗} (hC_convex : Convex ℝ C) (hx : x ∈ C) :
    List.TFAE
      [ x ∈ interior C,
        T[C] x = (univ : Set 𝓗),
        N[C] x = ({0} : Set 𝓗) ] := by
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hx_int
      exact
        (mem_interior_iff_normalCone_eq_singleton_zero_of_convex hC_convex ⟨x, hx_int⟩ hx).1
          hx_int
    · exact mem_interior_of_normalCone_eq_singleton_zero_of_convex_of_finiteDimensional
        hC_convex hx
  tfae_have 2 ↔ 3 := tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem hC_convex hx
  tfae_finish

end

end Set
