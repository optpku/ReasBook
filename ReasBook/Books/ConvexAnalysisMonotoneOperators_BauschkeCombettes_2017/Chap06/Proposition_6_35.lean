/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.35: a project cone is stable under positive scalar multiplication. -/
private lemma smul_mem_of_isCone {C : Set 𝓗} (hC_cone : IsCone C) {x : 𝓗} (hx : x ∈ C)
    {a : ℝ} (ha : 0 < a) :
    a • x ∈ C := by
  -- Rewrite the cone hypothesis as the positive-scalar image description and use the witness
  -- `(a, x)` for the target multiple.
  rw [isCone_iff] at hC_cone
  have hax : a • x ∈ (Set.Ioi (0 : ℝ)) • C := by
    exact Set.mem_smul.mpr ⟨a, ha, x, hx, rfl⟩
  rw [hC_cone]
  exact hax

/-- Helper for Proposition 6.35: if `a + ε b ≤ 0` for every positive `ε`, then already `a ≤ 0`.
-/
private lemma le_zero_of_forall_pos_add_mul_le_zero (a b : ℝ)
    (h : ∀ ε > 0, a + ε * b ≤ 0) :
    a ≤ 0 := by
  by_contra ha_nonpos
  have ha : 0 < a := by
    linarith
  by_cases hb : 0 ≤ b
  · -- If `b` is nonnegative, evaluating at `ε = 1` already contradicts `a > 0`.
    have hab : a + 1 * b ≤ 0 := h 1 (by norm_num)
    linarith
  · -- If `b` is negative, choose a small positive `ε` so that the sum stays positive.
    have hb_lt : b < 0 := by
      linarith
    let ε : ℝ := a / (-2 * b)
    have hden : 0 < -2 * b := by
      nlinarith
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos ha hden
    have hε_le : a + ε * b ≤ 0 := h ε hε
    have hb_ne : b ≠ 0 := by
      linarith
    have hhalf : a + ε * b = a / 2 := by
      dsimp [ε]
      field_simp [hb_ne]
      ring
    linarith

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.35: the polar cone of a sum of nonempty cones is contained in the
intersection of the two polar cones. -/
private lemma polarCone_add_subset_inter {K₁ K₂ : Set 𝓗}
    (hK₁_cone : IsCone K₁) (hK₁_nonempty : K₁.Nonempty)
    (hK₂_cone : IsCone K₂) (hK₂_nonempty : K₂.Nonempty) :
    (K₁ + K₂)ᵒ⊖ ⊆ K₁ᵒ⊖ ∩ K₂ᵒ⊖ := by
  intro u hu
  rcases hK₁_nonempty with ⟨y₁, hy₁⟩
  rcases hK₂_nonempty with ⟨y₂, hy₂⟩
  rw [Set.mem_inter_iff, Set.mem_polarCone_iff_forall_inner_nonpos,
    Set.mem_polarCone_iff_forall_inner_nonpos]
  constructor
  · intro x₁ hx₁
    -- Test on `x₁ + ε • y₂` and send `ε` to zero to isolate the `x₁` term.
    have htest : ∀ ε > 0, ⟪x₁, u⟫_ℝ + ε * ⟪y₂, u⟫_ℝ ≤ 0 := by
      intro ε hε
      have hy₂ε : ε • y₂ ∈ K₂ := smul_mem_of_isCone hK₂_cone hy₂ hε
      have hsum : x₁ + ε • y₂ ∈ K₁ + K₂ := by
        exact Set.mem_add.2 ⟨x₁, hx₁, ε • y₂, hy₂ε, rfl⟩
      have hinner : ⟪x₁ + ε • y₂, u⟫_ℝ ≤ 0 :=
        (Set.mem_polarCone_iff_forall_inner_nonpos.1 hu) (x₁ + ε • y₂) hsum
      simpa [inner_add_left, real_inner_smul_left] using hinner
    exact le_zero_of_forall_pos_add_mul_le_zero _ _ htest
  · intro x₂ hx₂
    -- Repeat the same argument with a fixed point from `K₁`.
    have htest : ∀ ε > 0, ⟪x₂, u⟫_ℝ + ε * ⟪y₁, u⟫_ℝ ≤ 0 := by
      intro ε hε
      have hy₁ε : ε • y₁ ∈ K₁ := smul_mem_of_isCone hK₁_cone hy₁ hε
      have hsum : ε • y₁ + x₂ ∈ K₁ + K₂ := by
        exact Set.mem_add.2 ⟨ε • y₁, hy₁ε, x₂, hx₂, rfl⟩
      have hinner : ⟪ε • y₁ + x₂, u⟫_ℝ ≤ 0 :=
        (Set.mem_polarCone_iff_forall_inner_nonpos.1 hu) (ε • y₁ + x₂) hsum
      simpa [inner_add_left, real_inner_smul_left, add_comm] using hinner
    exact le_zero_of_forall_pos_add_mul_le_zero _ _ htest

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.35: the intersection of two polar cones lies in the polar cone of
their pointwise sum. -/
private lemma inter_subset_polarCone_add {K₁ K₂ : Set 𝓗} :
    K₁ᵒ⊖ ∩ K₂ᵒ⊖ ⊆ (K₁ + K₂)ᵒ⊖ := by
  intro u hu
  rw [Set.mem_inter_iff, Set.mem_polarCone_iff_forall_inner_nonpos,
    Set.mem_polarCone_iff_forall_inner_nonpos] at hu
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro z hz
  rcases Set.mem_add.1 hz with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  -- Expand the inner product across the sum and combine the two nonpositivity bounds.
  have hx₁_nonpos : ⟪x₁, u⟫_ℝ ≤ 0 := hu.1 x₁ hx₁
  have hx₂_nonpos : ⟪x₂, u⟫_ℝ ≤ 0 := hu.2 x₂ hx₂
  simpa [inner_add_left] using add_nonpos hx₁_nonpos hx₂_nonpos

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.35: for nonempty cones, polarizing a pointwise sum produces the
intersection of the two polar cones. -/
private lemma polarCone_add_eq_inter {K₁ K₂ : Set 𝓗}
    (hK₁_cone : IsCone K₁) (hK₁_nonempty : K₁.Nonempty)
    (hK₂_cone : IsCone K₂) (hK₂_nonempty : K₂.Nonempty) :
    (K₁ + K₂)ᵒ⊖ = K₁ᵒ⊖ ∩ K₂ᵒ⊖ := by
  -- Package the textbook argument as the two natural set inclusions.
  refine Set.Subset.antisymm ?_ ?_
  · exact polarCone_add_subset_inter hK₁_cone hK₁_nonempty hK₂_cone hK₂_nonempty
  · exact inter_subset_polarCone_add

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.35: the polar cone of any set contains the origin. -/
private lemma polarCone_nonempty (C : Set 𝓗) :
    (Cᵒ⊖ : Set 𝓗).Nonempty := by
  refine ⟨0, ?_⟩
  -- The zero vector satisfies every defining inner-product inequality.
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro x hx
  simp

/-- Helper for Proposition 6.35: polar cones are convex. -/
private lemma polarCone_convex (C : Set 𝓗) :
    Convex ℝ (Cᵒ⊖ : Set 𝓗) := by
  -- Proposition 6.24 already gives convexity for the negative polar, and the two notions agree.
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_convex C

/-- Helper for Proposition 6.35: polar cones are cones. -/
private lemma polarCone_isCone (C : Set 𝓗) :
    IsCone (Cᵒ⊖ : Set 𝓗) := by
  -- Proposition 6.24 already gives the cone law for the negative polar, and the two notions
  -- agree.
  rw [Set.polarCone_eq_innerDual_neg]
  simpa [Set.negativePolar] using Set.negativePolar_isCone C

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 6.35: taking the closure of the cone hull does not enlarge a convex
cone. -/
private lemma closure_cone_eq_closure_of_convex_cone {C : Set 𝓗}
    (hC_convex : Convex ℝ C) (hC_cone : IsCone C) :
    closure (cone C) = closure C := by
  have hcone_eq : cone C = C := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      -- Route cone-hull membership through `Convex.toCone`, then use the given cone law on `C`.
      have hx_toCone : x ∈ (hC_convex.toCone C : Set 𝓗) := by
        exact (ConvexCone.hull_min (R := ℝ) (s := C) (C := hC_convex.toCone C)
          hC_convex.subset_toCone) (by simpa [Set.cone_def] using hx)
      rcases (Convex.mem_toCone hC_convex).1 hx_toCone with ⟨a, ha, y, hy, rfl⟩
      exact smul_mem_of_isCone hC_cone hy ha
    · intro x hx
      -- The cone hull always contains the original set.
      simpa [Set.cone_def] using (ConvexCone.subset_hull (R := ℝ) (s := C) hx)
  -- Once the cone hull is literally `C`, their closures coincide.
  rw [hcone_eq]

-- Proof sketch: Proposition 6.27 applied to the nonempty cones `K₁ᵒ⊖` and `K₂ᵒ⊖` gives
-- `(K₁ᵒ⊖ + K₂ᵒ⊖)ᵒ⊖ = (K₁ᵒ⊖)ᵒ⊖ ∩ (K₂ᵒ⊖)ᵒ⊖`. Proposition 6.33 identifies each double polar with
-- `closure (cone Kᵢ)`, and since each `Kᵢ` is a cone this is `closure Kᵢ`. Taking polars gives
-- the closure of the sum of the two polar cones.
/-- Proposition 6.35: if `K₁` and `K₂` are nonempty convex cones in a real Hilbert space, then
the polar cone of `closure K₁ ∩ closure K₂` is the closure of the sum of the polar cones of
`K₁` and `K₂`. This is the formula obtained by polarizing the identity in the proof; the raw sum
need not be closed in an infinite-dimensional Hilbert space. -/
theorem polarCone_inter_closure_eq_closure_add_polarCone {K₁ K₂ : Set 𝓗}
    (hK₁_nonempty : K₁.Nonempty) (hK₁_convex : Convex ℝ K₁) (hK₁_cone : IsCone K₁)
    (hK₂_nonempty : K₂.Nonempty) (hK₂_convex : Convex ℝ K₂) (hK₂_cone : IsCone K₂) :
    (closure K₁ ∩ closure K₂)ᵒ⊖ = closure (K₁ᵒ⊖ + K₂ᵒ⊖) := by
  -- Route correction: the repaired statement keeps the closure on the sum of polar cones, so the
  -- textbook proof goes through by applying Proposition 6.33 a second time to that sum.
  let S : Set 𝓗 := K₁ᵒ⊖ + K₂ᵒ⊖
  have hS_nonempty : S.Nonempty := by
    rcases polarCone_nonempty K₁ with ⟨u₁, hu₁⟩
    rcases polarCone_nonempty K₂ with ⟨u₂, hu₂⟩
    refine ⟨u₁ + u₂, ?_⟩
    exact Set.mem_add.2 ⟨u₁, hu₁, u₂, hu₂, rfl⟩
  have hS_convex : Convex ℝ S := by
    -- Pointwise sums of convex sets are convex, so the same holds for the two polar cones.
    simpa [S] using (polarCone_convex K₁).add (polarCone_convex K₂)
  have hS_cone : IsCone S := by
    -- Unpack the pointwise sum and rescale each summand using the cone laws of the polar cones.
    rw [isCone_iff]
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
    · intro x hx
      rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
      rcases Set.mem_add.1 hy with ⟨y₁, hy₁, y₂, hy₂, rfl⟩
      refine Set.mem_add.2 ⟨a • y₁, smul_mem_of_isCone (polarCone_isCone K₁) hy₁ ha,
        a • y₂, smul_mem_of_isCone (polarCone_isCone K₂) hy₂ ha, ?_⟩
      rw [smul_add]
  have hpolar_sum : Sᵒ⊖ = closure K₁ ∩ closure K₂ := by
    -- First polarize the sum using Proposition 6.27, then identify each double polar by
    -- Proposition 6.33 and simplify the cone hulls away.
    calc
      Sᵒ⊖ = (K₁ᵒ⊖)ᵒ⊖ ∩ (K₂ᵒ⊖)ᵒ⊖ := by
        simpa [S] using
          polarCone_add_eq_inter (K₁ := K₁ᵒ⊖) (K₂ := K₂ᵒ⊖)
            (polarCone_isCone K₁) (polarCone_nonempty K₁)
            (polarCone_isCone K₂) (polarCone_nonempty K₂)
      _ = closure (cone K₁) ∩ closure (cone K₂) := by
        rw [Set.polarCone_polarCone_eq_closure_cone_of_nonempty_convex hK₁_nonempty hK₁_convex,
          Set.polarCone_polarCone_eq_closure_cone_of_nonempty_convex hK₂_nonempty hK₂_convex]
      _ = closure K₁ ∩ closure K₂ := by
        rw [closure_cone_eq_closure_of_convex_cone hK₁_convex hK₁_cone,
          closure_cone_eq_closure_of_convex_cone hK₂_convex hK₂_cone]
  -- Apply Proposition 6.33 once more to `S` and rewrite using the computed formula for `Sᵒ⊖`.
  calc
    (closure K₁ ∩ closure K₂)ᵒ⊖ = (Sᵒ⊖)ᵒ⊖ := by rw [hpolar_sum]
    _ = closure (cone S) := by
      exact Set.polarCone_polarCone_eq_closure_cone_of_nonempty_convex hS_nonempty hS_convex
    _ = closure S := by
      exact closure_cone_eq_closure_of_convex_cone hS_convex hS_cone
    _ = closure (K₁ᵒ⊖ + K₂ᵒ⊖) := by
      rfl

end

end Set
