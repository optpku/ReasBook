/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} {x : E}

-- Proof sketch: apply Proposition 6.17 to the translated convex set `C - {x}`. Translation by
-- `-x` identifies `x ∈ interior C` with `0 ∈ interior (C - {x})`, and `tangentCone_of_mem hx`
-- identifies the tangent cone with `closure (cone (C - {x}))`.
/-- Proposition 6.45 (i) ↔ (ii): for a convex subset `C` of a real normed space with
nonempty interior and a point `x ∈ C`, the point `x` lies in `interior C` if and only if the
tangent cone `T[C] x` is the whole space. -/
theorem mem_interior_iff_tangentCone_eq_univ_of_convex
    (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty)
    (hx : x ∈ C) :
    x ∈ interior C ↔ T[C] x = (univ : Set E) := by
  let D : Set E := C - ({x} : Set E)
  have hD_convex : Convex ℝ D := by
    dsimp [D]
    simpa [sub_eq_add_neg] using hC_convex.add (convex_singleton (-x))
  have hD_interior : interior D = (fun y ↦ y - x) '' interior C := by
    dsimp [D]
    rw [show C - ({x} : Set E) = (fun y ↦ y - x) '' C by
      ext y
      simp]
    simpa [sub_eq_add_neg] using ((Homeomorph.addRight (-x)).image_interior C).symm
  have hD_int_nonempty : (interior D).Nonempty := by
    rw [hD_interior]
    exact hC_int_nonempty.image (fun y ↦ y - x)
  have h03 : 0 ∈ interior D ↔ closure (cone D) = (univ : Set E) := by
    let l : List Prop :=
      [0 ∈ interior D, cone (interior D) = univ, cone D = univ,
        closure (cone D) = (univ : Set E)]
    have hl : l.TFAE :=
      zero_mem_interior_tfae_cone_interior_cone_closure_eq_univ hD_convex hD_int_nonempty
    simpa [l] using (List.TFAE.out hl 0 3)
  have hx0 : x ∈ interior C ↔ 0 ∈ interior D := by
    rw [hD_interior]
    constructor
    · intro hx_int
      exact ⟨x, hx_int, sub_self x⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := sub_eq_zero.mp hyx
      simpa [this] using hy
  rw [tangentCone_of_mem hx]
  exact hx0.trans h03

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗} {x : 𝓗}

-- Proof sketch: rewrite the tangent-cone clause using
-- `mem_interior_iff_tangentCone_eq_univ_of_convex`, then invoke Proposition 6.44 (3).
/-- Proposition 6.45 (i) ↔ (iii): for a convex subset `C` of a real Hilbert space with nonempty
interior and a point `x ∈ C`, the point `x` lies in `interior C` if and only if the normal cone
`N[C] x` is trivial. -/
theorem mem_interior_iff_normalCone_eq_singleton_zero_of_convex
    (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty)
    (hx : x ∈ C) :
    x ∈ interior C ↔ N[C] x = ({0} : Set 𝓗) := by
  rw [mem_interior_iff_tangentCone_eq_univ_of_convex hC_convex hC_int_nonempty hx]
  -- Use the already-proved tangent/normal equivalence at the same set and base point.
  exact
    tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem
      (C := C) (x := x) hC_convex hx

-- Proof sketch: the three source clauses are linked by the tangent/interior equivalence above and
-- the canonical tangent/normal equivalence from Proposition 6.44 (3).
/-- Proposition 6.45: for a convex subset `C` of a real Hilbert space with nonempty interior and a
point `x ∈ C`, the following are equivalent: `x ∈ interior C`, the tangent cone `T[C] x` is the
whole space, and the normal cone `N[C] x` is trivial. -/
theorem mem_interior_tfae_tangentCone_eq_univ_normalCone_eq_singleton_zero_of_convex
    (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty)
    (hx : x ∈ C) :
    List.TFAE
      [ x ∈ interior C,
        T[C] x = (univ : Set 𝓗),
        N[C] x = ({0} : Set 𝓗) ] := by
  tfae_have 1 ↔ 2 := mem_interior_iff_tangentCone_eq_univ_of_convex hC_convex hC_int_nonempty hx
  -- Reuse Proposition 6.44 (3) with explicit parameters to match the current TFAE clauses.
  tfae_have 2 ↔ 3 :=
    tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem
      (C := C) (x := x) hC_convex hx
  tfae_finish

end

end Set
