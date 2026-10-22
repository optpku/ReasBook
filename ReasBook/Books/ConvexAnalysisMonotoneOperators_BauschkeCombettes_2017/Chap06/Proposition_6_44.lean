/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.44: at a point of the set, the normal cone is the polar cone of the
translate `C - {x}`. -/
theorem normalCone_eq_polarCone_translate_of_mem {C : Set 𝓗} {x : 𝓗} (hx : x ∈ C) :
    N[C] x = (C - ({x} : Set 𝓗))ᵒ⊖ := by
  ext u
  -- Rewrite the normal cone and the polar cone into the same support-function inequality.
  rw [normalCone_of_mem hx, mem_polarCone_iff]
  simp [innerSupremumOn_eq_sSup_image]

/-- Helper for Proposition 6.44: taking the polar cone is unchanged by passing to the closure of
the conical hull. -/
theorem polarCone_closure_cone_eq_polarCone (D : Set 𝓗) :
    (closure (cone D))ᵒ⊖ = Dᵒ⊖ := by
  -- Route correction: rewrite both source-facing polar cones as Proposition 6.24 negative polars,
  -- then use invariance under `closure` and `cone`.
  calc
    (closure (cone D))ᵒ⊖ = Set.negativePolar (closure (cone D)) := by
      simpa [Set.negativePolar] using Set.polarCone_eq_innerDual_neg (closure (cone D))
    _ = Set.negativePolar (cone D) := Set.negativePolar_closure_eq (cone D)
    _ = Set.negativePolar D := Set.negativePolar_cone_eq D
    _ = Dᵒ⊖ := by
      simpa [Set.negativePolar] using (Set.polarCone_eq_innerDual_neg D).symm

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.44: the polar cone of the whole space is the singleton `{0}`. -/
theorem polarCone_univ_eq_singleton_zero :
    ((univ : Set 𝓗)ᵒ⊖) = ({0} : Set 𝓗) := by
  ext u
  constructor
  · intro hu
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hu
    -- Test the defining inequality at `u` itself to force vanishing of the norm square.
    have huu : ⟪u, u⟫_ℝ ≤ 0 := hu u (by simp)
    have hnonneg : 0 ≤ ⟪u, u⟫_ℝ := by
      exact real_inner_self_nonneg (x := u)
    have hzero : ⟪u, u⟫_ℝ = 0 := le_antisymm huu hnonneg
    simpa using inner_self_eq_zero.mp hzero
  · rintro rfl
    -- The origin has zero inner product with every vector, so it lies in every polar cone.
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    intro y hy
    simp

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.44: the polar cone of `{0}` is the whole space. -/
theorem polarCone_singleton_zero_eq_univ :
    (({0} : Set 𝓗)ᵒ⊖) = (univ : Set 𝓗) := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    -- The only point in `{0}` contributes the trivial inequality `0 ≤ 0`.
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    intro y hy
    simp [Set.mem_singleton_iff.mp hy]

-- Proof sketch: rewrite `T[C] x` by `tangentCone_of_mem hx` and `N[C] x` by `normalCone_of_mem hx`.
-- Proposition 6.24 identifies the negative polar cone of `closure (cone (C - {x}))` with that of
-- `C - {x}`, giving the equality.
/-- Proposition 6.44 (1): at a point of a set, the polar cone of the tangent cone equals the
normal cone. -/
theorem polarCone_tangentCone_eq_normalCone_of_mem {C : Set 𝓗} {x : 𝓗}
    (hC_convex : Convex ℝ C) (hx : x ∈ C) :
    (T[C] x)ᵒ⊖ = N[C] x := by
  let _ := hC_convex
  -- Rewrite both cones through the translated set `C - {x}`.
  calc
    (T[C] x)ᵒ⊖ = (closure (cone (C - ({x} : Set 𝓗))))ᵒ⊖ := by
      rw [tangentCone_of_mem hx]
    _ = (C - ({x} : Set 𝓗))ᵒ⊖ := polarCone_closure_cone_eq_polarCone (C - ({x} : Set 𝓗))
    _ = N[C] x := (normalCone_eq_polarCone_translate_of_mem hx).symm

-- Proof sketch: by Proposition 6.44 (1), `N[C] x` is the polar cone of `T[C] x`. The tangent cone
-- is a nonempty closed convex cone, so Corollary 6.34 applies to identify its double polar with
-- itself.
/-- Proposition 6.44 (2): at a point of a set, the polar cone of the normal cone equals the
tangent cone. -/
theorem polarCone_normalCone_eq_tangentCone_of_mem {C : Set 𝓗} {x : 𝓗}
    (hC_convex : Convex ℝ C) (hx : x ∈ C) :
    (N[C] x)ᵒ⊖ = T[C] x := by
  let D : Set 𝓗 := C - ({x} : Set 𝓗)
  have hD_nonempty : D.Nonempty := by
    -- The translated set contains `x - x = 0`.
    refine ⟨0, ?_⟩
    dsimp [D]
    exact ⟨x, hx, x, by simp, by simp⟩
  have hD_convex : Convex ℝ D := by
    -- Translation preserves convexity.
    dsimp [D]
    simpa [sub_eq_add_neg] using hC_convex.add (convex_singleton (-x))
  -- Apply the bipolar theorem to the translated set.
  calc
    (N[C] x)ᵒ⊖ = (Dᵒ⊖)ᵒ⊖ := by
      rw [normalCone_eq_polarCone_translate_of_mem hx]
    _ = closure (cone D) :=
      Set.polarCone_polarCone_eq_closure_cone_of_nonempty_convex hD_nonempty hD_convex
    _ = T[C] x := by
      simpa [D] using (tangentCone_of_mem (C := C) (x := x) hx).symm

-- Proof sketch: Proposition 6.44 (1) identifies `N[C] x` with the polar cone of `T[C] x`, so
-- `T[C] x = univ` forces `N[C] x = {0}` because the polar cone of `univ` is `{0}`. Conversely,
-- Proposition 6.44 (2) identifies `T[C] x` with the polar cone of `N[C] x`, and the polar cone of
-- `{0}` is `univ`.
/-- Proposition 6.44 (3): at a point of a set, the tangent cone is the whole space if and only if
the normal cone is trivial. -/
theorem tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem {C : Set 𝓗} {x : 𝓗}
    (hC_convex : Convex ℝ C) (hx : x ∈ C) :
    T[C] x = (univ : Set 𝓗) ↔ N[C] x = ({0} : Set 𝓗) := by
  constructor
  · intro hT
    -- Convert `N[C] x` to the polar of `T[C] x`, then evaluate the endpoint polar explicitly.
    calc
      N[C] x = (T[C] x)ᵒ⊖ :=
        (polarCone_tangentCone_eq_normalCone_of_mem hC_convex hx).symm
      _ = ((univ : Set 𝓗))ᵒ⊖ := by rw [hT]
      _ = ({0} : Set 𝓗) := polarCone_univ_eq_singleton_zero
  · intro hN
    -- Use the reverse duality from part (2) and the polar of `{0}`.
    calc
      T[C] x = (N[C] x)ᵒ⊖ :=
        (polarCone_normalCone_eq_tangentCone_of_mem hC_convex hx).symm
      _ = (({0} : Set 𝓗))ᵒ⊖ := by rw [hN]
      _ = (univ : Set 𝓗) := polarCone_singleton_zero_eq_univ

end

end Set
