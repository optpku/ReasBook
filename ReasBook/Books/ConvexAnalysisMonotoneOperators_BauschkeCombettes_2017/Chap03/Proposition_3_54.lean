/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Example_3_41
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

noncomputable section

/- Helper for Proposition 3.54: an infinite-dimensional Hilbert space contains closed linear
subspaces with nonclosed sum. -/
private lemma exists_closed_subspaces_with_nonclosed_sup
    (hinfdim : ¬ FiniteDimensional ℝ 𝓗) :
    ∃ C D : Submodule ℝ 𝓗,
      IsClosed (C : Set 𝓗) ∧ IsClosed (D : Set 𝓗) ∧
      Disjoint C D ∧ ¬ IsClosed (((C ⊔ D : Submodule ℝ 𝓗) : Set 𝓗)) := by
  -- Isolate the infinite-dimensional input by instantiating Example 3.41 with a concrete angle
  -- sequence whose squared sines are summable.
  obtain ⟨e, he⟩ := exists_orthonormal_sequence_of_not_finiteDimensional hinfdim
  let θ : ℕ → ℝ := fun n ↦ ((1 : ℝ) / 2) ^ (n + 1)
  have hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
    intro n
    constructor
    · dsimp [θ]
      positivity
    · have hθ_le_one : θ n ≤ 1 := by
        dsimp [θ]
        exact pow_le_one₀ (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ 1)
      linarith [Real.pi_gt_three, hθ_le_one]
  have hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2) := by
    have hθ_summable : Summable θ := by
      have hgeom :
          Summable (fun n : ℕ ↦ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n)) :=
        Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      convert hgeom using 1
      ext n
      simp [θ, pow_succ, mul_comm]
    refine Summable.of_nonneg_of_le (fun n ↦ sq_nonneg _) ?_ hθ_summable
    intro n
    have hθ_nonneg : 0 ≤ θ n := (hθ n).1.le
    have hθ_le_one : θ n ≤ 1 := by
      dsimp [θ]
      exact pow_le_one₀ (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ 1)
    calc
      Real.sin (θ n) ^ 2 ≤ θ n ^ 2 := Real.sin_sq_le_sq
      _ ≤ θ n := by nlinarith
  refine ⟨even_indexed_closed_span e, rotated_even_odd_closed_span e θ, ?_, ?_, ?_, ?_⟩
  · exact isClosed_even_indexed_closed_span e
  · exact isClosed_rotated_even_odd_closed_span e θ
  · exact disjoint_even_indexed_closed_span_rotated_even_odd_closed_span e θ he hθ
  · exact not_isClosed_sup_even_indexed_closed_span_rotated_even_odd_closed_span
      e θ he hθ hθ_square_summable

/- Helper for Proposition 3.54: membership in `C ⊔ Sᗮ` is equivalent to the projection onto the
closed sum `S = closure (C ⊔ D)` lying in `C`. -/
private lemma mem_left_counterexample_iff_starProjection_mem_base
    (C D : Submodule ℝ 𝓗) (x : 𝓗) :
    let S : Submodule ℝ 𝓗 := (C ⊔ D).topologicalClosure
    x ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) ↔ S.starProjection x ∈ C := by
  -- The decomposition `x = proj_S x + (x - proj_S x)` separates the `S` and `Sᗮ` directions.
  dsimp
  have hC_le : C ≤ (C ⊔ D).topologicalClosure :=
    le_trans le_sup_left (Submodule.le_topologicalClosure _)
  constructor
  · intro hx
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨c, hc, w, hw, rfl⟩
    have hproj : ((C ⊔ D).topologicalClosure).starProjection (c + w) = c := by
      exact ((C ⊔ D).topologicalClosure).eq_starProjection_of_mem_orthogonal (hC_le hc)
        (by simpa [Submodule.orthogonal_closure] using hw)
    simpa [hproj] using hc
  · intro hx
    rw [Submodule.mem_sup]
    refine ⟨((C ⊔ D).topologicalClosure).starProjection x, hx,
      x - ((C ⊔ D).topologicalClosure).starProjection x,
      ((C ⊔ D).topologicalClosure).sub_starProjection_mem_orthogonal x, by abel_nf⟩

/- Helper for Proposition 3.54: if a linear functional is bounded above on the whole line
`ℝ • a`, then it vanishes on that direction. -/
private lemma inner_eq_zero_of_line_upper_bound {a c : ℝ}
    (hbound : ∀ t : ℝ, t * a ≤ c) : a = 0 := by
  -- A nonzero slope would let us choose a scalar that violates the uniform upper bound.
  by_contra ha
  have hne : a ≠ 0 := ha
  have hsign : 0 < a ∨ a < 0 := lt_or_gt_of_ne hne.symm
  rcases hsign with hpos | hneg
  · have h := hbound (c / a + 1)
    have hcalc : (c / a + 1) * a = c + a := by
      field_simp [hne]
    rw [hcalc] at h
    linarith
  · have h := hbound (c / a - 1)
    have hcalc : (c / a - 1) * a = c - a := by
      field_simp [hne]
    rw [hcalc] at h
    linarith

-- Proof sketch: choose closed linear subspaces `C` and `D` with nonclosed sum `C + D`, then pick
-- `z ∈ closure (C + D) \ (C + D)` and define `U := C + (C + D)ᗮ` and `V := z + D`. These affine
-- subspaces are closed and disjoint, while `U - V` is dense in `𝓗`, forcing every separating
-- normal vector to vanish.
/-- Proposition 3.54: an infinite-dimensional real Hilbert space contains disjoint closed affine
subspaces that are not separated. -/
theorem exists_disjoint_closed_affineSubspaces_not_separated
    (hinfdim : ¬ FiniteDimensional ℝ 𝓗) :
    ∃ U V : AffineSubspace ℝ 𝓗,
      IsClosed (U : Set 𝓗) ∧ IsClosed (V : Set 𝓗) ∧
      Disjoint (U : Set 𝓗) (V : Set 𝓗) ∧ ¬ AreSeparated (U : Set 𝓗) (V : Set 𝓗) := by
  -- Route correction: work from a nonclosed linear sum, then separate the closure direction `S`
  -- from its orthogonal complement instead of chasing a direct density computation for `U - V`.
  obtain ⟨C, D, hC_closed, hD_closed, hCD_disjoint, hCD_nonclosed⟩ :=
    exists_closed_subspaces_with_nonclosed_sup hinfdim
  let S : Submodule ℝ 𝓗 := (C ⊔ D).topologicalClosure
  have hS_closed : IsClosed (S : Set 𝓗) := by
    simp [S]
  have hC_le_S : C ≤ S := le_trans le_sup_left (Submodule.le_topologicalClosure _)
  have hD_le_S : D ≤ S := le_trans le_sup_right (Submodule.le_topologicalClosure _)
  obtain ⟨z, hzS, hz_not_mem⟩ : ∃ z : 𝓗, z ∈ S ∧ z ∉ C ⊔ D := by
    -- If every point of the closure belonged to `C ⊔ D`, that sum would already be closed.
    by_contra hz_fail
    have hS_le : S ≤ C ⊔ D := by
      intro x hx
      by_contra hx_not
      exact hz_fail ⟨x, hx, hx_not⟩
    have hS_eq : S = C ⊔ D := le_antisymm hS_le (Submodule.le_topologicalClosure _)
    exact hCD_nonclosed (by simpa [S, hS_eq] using Submodule.isClosed_topologicalClosure (C ⊔ D))
  let U : AffineSubspace ℝ 𝓗 := (C ⊔ Sᗮ).toAffineSubspace
  let V : AffineSubspace ℝ 𝓗 := z +ᵥ D.toAffineSubspace
  refine ⟨U, V, ?_, ?_, ?_, ?_⟩
  · -- The left affine subspace is the preimage of the closed set `C` under the continuous
    -- projection onto `S`.
    have hclosed_subspace : IsClosed ((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗) := by
      convert hC_closed.preimage S.starProjection.continuous using 1
      ext x
      simpa [Set.mem_preimage, S] using
        (mem_left_counterexample_iff_starProjection_mem_base C D x)
    simpa [U] using hclosed_subspace
  · -- The right affine subspace is a translate of the closed linear subspace `D`.
    simpa [V, AffineSubspace.coe_pointwise_vadd] using
      (by simpa [vadd_eq_add] using hD_closed.left_addCoset z :
        IsClosed (z +ᵥ (D : Set 𝓗)))
  · -- Any common point would place `z` back in `C ⊔ D`, contradicting the choice of `z`.
    rw [Set.disjoint_left]
    intro x hxU hxV
    have hxU' : x ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := by
      change x ∈ ((C ⊔ Sᗮ : Submodule ℝ 𝓗).toAffineSubspace : AffineSubspace ℝ 𝓗) at hxU
      simpa using hxU
    rcases
      (show ∃ d ∈ D, z + d = x from by
        simpa [V, AffineSubspace.coe_pointwise_vadd, Set.mem_vadd_set, vadd_eq_add] using hxV) with
      ⟨d, hd, rfl⟩
    have hxS : z + d ∈ S := S.add_mem hzS (hD_le_S hd)
    have hxC : z + d ∈ C := by
      have hprojC : S.starProjection (z + d) ∈ C :=
        (mem_left_counterexample_iff_starProjection_mem_base C D (z + d)).1 hxU'
      simpa [Submodule.starProjection_eq_self_iff.mpr hxS] using hprojC
    have hz_mem : z ∈ C ⊔ D := by
      rw [Submodule.mem_sup]
      refine ⟨z + d, hxC, -d, D.neg_mem hd, by abel_nf⟩
    exact hz_not_mem hz_mem
  · intro hsep
    rcases (areSeparated_iff_exists_nonzero (U : Set 𝓗) (V : Set 𝓗)).mp hsep with ⟨u, hu_ne, hu_sep⟩
    have hu_sep_left :
        innerSupremumOn (((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗)) u ≤ innerInfimumOn (V : Set 𝓗) u := by
      simpa [U] using hu_sep
    have hzV : z ∈ (V : Set 𝓗) := by
      change z ∈ z +ᵥ (D : Set 𝓗)
      exact ⟨0, D.zero_mem, by simp [vadd_eq_add]⟩
    have hzero_on_orthogonal : ∀ w ∈ Sᗮ, ⟪w, u⟫_ℝ = 0 := by
      -- Bounding the separator on the full line through an orthogonal direction forces that
      -- direction to be annihilated.
      intro w hw
      apply inner_eq_zero_of_line_upper_bound
      intro t
      have hw_mem : w ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := Submodule.mem_sup_right hw
      have ht_mem : t • w ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := (C ⊔ Sᗮ).smul_mem t hw_mem
      have ht_le : (⟪t • w, u⟫_ℝ : EReal) ≤ (⟪z, u⟫_ℝ : EReal) := by
        have hx_le : (⟪t • w, u⟫_ℝ : EReal) ≤
            innerSupremumOn (((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗)) u := by
          rw [innerSupremumOn_eq_sSup_image]
          exact (isLUB_sSup _).1 ⟨t • w, ht_mem, rfl⟩
        have hy_ge : innerInfimumOn (V : Set 𝓗) u ≤ (⟪z, u⟫_ℝ : EReal) := by
          rw [innerInfimumOn_eq_sInf_image]
          exact (isGLB_sInf _).1 ⟨z, hzV, rfl⟩
        exact le_trans (le_trans hx_le hu_sep_left) hy_ge
      have ht_le_real : ⟪t • w, u⟫_ℝ ≤ ⟪z, u⟫_ℝ := by
        exact_mod_cast ht_le
      simpa [inner_smul_left] using ht_le_real
    have hsubset_nonpos :
        ((C ⊔ D : Submodule ℝ 𝓗) : Set 𝓗) ⊆ {s : 𝓗 | ⟪s - z, u⟫_ℝ ≤ 0} := by
      -- Evaluating the separator on `c ∈ C ⊆ U` and `z - d ∈ V` yields the key inequality on
      -- every point `c + d` of the algebraic sum.
      intro s hs
      change s ∈ (C ⊔ D : Submodule ℝ 𝓗) at hs
      rw [Submodule.mem_sup] at hs
      rcases hs with ⟨c, hc, d, hd, rfl⟩
      have hzdV : z - d ∈ (V : Set 𝓗) := by
        simpa [V, AffineSubspace.coe_pointwise_vadd, Set.mem_vadd_set, vadd_eq_add] using
          (show ∃ w ∈ D, z + w = z - d from ⟨-d, D.neg_mem hd, by abel_nf⟩)
      have hc_mem : c ∈ (C ⊔ Sᗮ : Submodule ℝ 𝓗) := Submodule.mem_sup_left hc
      have hcd_le : ⟪c, u⟫_ℝ ≤ ⟪z - d, u⟫_ℝ := by
        have hx_le : (⟪c, u⟫_ℝ : EReal) ≤
            innerSupremumOn (((C ⊔ Sᗮ : Submodule ℝ 𝓗) : Set 𝓗)) u := by
          rw [innerSupremumOn_eq_sSup_image]
          exact (isLUB_sSup _).1 ⟨c, hc_mem, rfl⟩
        have hy_ge : innerInfimumOn (V : Set 𝓗) u ≤ (⟪z - d, u⟫_ℝ : EReal) := by
          rw [innerInfimumOn_eq_sInf_image]
          exact (isGLB_sInf _).1 ⟨z - d, hzdV, rfl⟩
        exact_mod_cast le_trans (le_trans hx_le hu_sep_left) hy_ge
      have hcalc : ⟪c + d - z, u⟫_ℝ = ⟪c, u⟫_ℝ - ⟪z - d, u⟫_ℝ := by
        calc
          ⟪c + d - z, u⟫_ℝ = ⟪c - (z - d), u⟫_ℝ := by
            congr 1
            abel_nf
          _ = ⟪c, u⟫_ℝ - ⟪z - d, u⟫_ℝ := by
            rw [inner_sub_left]
      change ⟪c + d - z, u⟫_ℝ ≤ 0
      rw [hcalc]
      exact sub_nonpos.mpr hcd_le
    have hclosed_nonpos : IsClosed {s : 𝓗 | ⟪s - z, u⟫_ℝ ≤ 0} := by
      exact isClosed_le ((continuous_id.sub continuous_const).inner continuous_const) continuous_const
    have hnonpos_on_S : ∀ s ∈ S, ⟪s - z, u⟫_ℝ ≤ 0 := by
      -- Closedness propagates the inequality from the dense algebraic sum to the whole closure `S`.
      intro s hs
      have hclosure_subset :
          closure (((C ⊔ D : Submodule ℝ 𝓗) : Set 𝓗)) ⊆ {s : 𝓗 | ⟪s - z, u⟫_ℝ ≤ 0} :=
        closure_minimal hsubset_nonpos hclosed_nonpos
      exact hclosure_subset (by simpa [S] using hs)
    have hzero_on_S_shift : ∀ s ∈ S, ⟪s - z, u⟫_ℝ = 0 := by
      -- Apply the same nonpositivity estimate to the reflected point `2z - s ∈ S` to obtain the
      -- opposite inequality and hence equality.
      intro s hs
      have hs_nonpos : ⟪s - z, u⟫_ℝ ≤ 0 := hnonpos_on_S s hs
      have hsym_mem : (2 : ℝ) • z - s ∈ S := S.sub_mem (S.smul_mem 2 hzS) hs
      have hsym_nonpos : ⟪((2 : ℝ) • z - s) - z, u⟫_ℝ ≤ 0 := hnonpos_on_S ((2 : ℝ) • z - s) hsym_mem
      have hcalc : ⟪((2 : ℝ) • z - s) - z, u⟫_ℝ = -⟪s - z, u⟫_ℝ := by
        calc
          ⟪((2 : ℝ) • z - s) - z, u⟫_ℝ = ⟪z - s, u⟫_ℝ := by
            congr 1
            simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = -⟪s - z, u⟫_ℝ := by
            rw [show z - s = -(s - z) by abel_nf, inner_neg_left]
      have hs_nonneg : 0 ≤ ⟪s - z, u⟫_ℝ := by
        rw [hcalc] at hsym_nonpos
        linarith
      linarith
    have hz_inner_zero : ⟪z, u⟫_ℝ = 0 := by
      have h0 := hzero_on_S_shift 0 S.zero_mem
      simpa using h0
    have hu_mem_orth : u ∈ Sᗮ := by
      -- Vanishing on all of `S` means the separator lies in `Sᗮ`.
      rw [Submodule.mem_orthogonal']
      intro s hs
      have hs_zero : ⟪s - z, u⟫_ℝ = 0 := hzero_on_S_shift s hs
      have hs_right : ⟪s, u⟫_ℝ = 0 := by
        rw [inner_sub_left] at hs_zero
        linarith
      simpa [real_inner_comm] using hs_right
    have hu_mem_orthorth : u ∈ Sᗮᗮ := by
      -- The orthogonal directions are also annihilated, so `u` lies in the double orthogonal.
      rw [Submodule.mem_orthogonal']
      intro w hw
      have hw_zero : ⟪w, u⟫_ℝ = 0 := hzero_on_orthogonal w hw
      simpa [real_inner_comm] using hw_zero
    have hu_mem_S : u ∈ S := by
      simpa [Submodule.orthogonal_orthogonal_eq_closure, hS_closed.submodule_topologicalClosure_eq]
        using hu_mem_orthorth
    have hu_mem_bot : u ∈ (⊥ : Submodule ℝ 𝓗) := by
      have : u ∈ S ⊓ Sᗮ := ⟨hu_mem_S, hu_mem_orth⟩
      simpa [S.inf_orthogonal_eq_bot] using this
    exact hu_ne (by simpa using hu_mem_bot)
