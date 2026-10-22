/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Pointwise

universe u

namespace Proposition612Absorbent

namespace Set

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The core of a set consists of the points whose translates of the set around the origin are
absorbent. -/
def core (C : Set E) : Set E :=
  {x | Absorbent ℝ ((fun y : E ↦ x + y) ⁻¹' C)}

-- Proof sketch: unfold `Set.core` and `Absorbent`; then rewrite absorption of the translated set
-- in terms of small positive scalar multiples of an arbitrary direction.
/-- A point lies in the core exactly when every direction can be followed for a short positive
distance while staying in the set. -/
theorem mem_core_iff {C : Set E} {x : E} :
    x ∈ core C ↔
      ∀ y : E, ∃ ε > (0 : ℝ), ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) ε → x + t • y ∈ C := by
  let S : Set E := ((fun y : E ↦ x + y) ⁻¹' C)
  constructor
  · intro hx y
    -- Turn absorbency into a punctured neighborhood statement in the chosen direction.
    have hx' : Absorbent ℝ S := hx
    have h0S : (0 : E) ∈ S := hx'.zero_mem
    have hy :
        {c : ℝ | c • y ∈ S} ∈ 𝓝[≠] (0 : ℝ) := by
      simpa [S] using hx'.eventually_nhdsNE_zero y
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hy with ⟨U, hU_nhds, hU_subset⟩
    rcases Metric.mem_nhds_iff.mp hU_nhds with ⟨r, hr, hrU⟩
    refine ⟨r / 2, by positivity, ?_⟩
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · -- The translated set contains `0`, so the segment criterion also covers the endpoint.
      simpa [S] using h0S
    · -- A nonzero scalar in the half-radius interval belongs to the punctured ball extracted above.
      have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have ht_ball : t ∈ Metric.ball (0 : ℝ) r := by
        rw [Metric.mem_ball, Real.dist_eq]
        have : t < r := by nlinarith [ht.2, hr]
        simpa [abs_of_nonneg ht.1] using this
      have ht_mem : t ∈ U ∩ ({0} : Set ℝ)ᶜ := ⟨hrU ht_ball, ht0⟩
      have : t • y ∈ S := hU_subset ht_mem
      simpa [S] using this
  · intro hx
    -- Build a punctured neighborhood criterion using forward segments
    -- in the directions `y` and `-y`.
    refine (absorbent_iff_eventually_nhdsNE_zero).2 ?_
    intro y
    rcases hx y with ⟨ε₁, hε₁, hseg₁⟩
    rcases hx (-y) with ⟨ε₂, hε₂, hseg₂⟩
    let ε : ℝ := min ε₁ ε₂
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    have hBall :
        Metric.ball (0 : ℝ) ε ∩ ({0} : Set ℝ)ᶜ ∈ 𝓝[≠] (0 : ℝ) := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
      refine ⟨Metric.ball (0 : ℝ) ε, Metric.ball_mem_nhds (0 : ℝ) hε, ?_⟩
      simp
    exact Filter.mem_of_superset hBall (fun c hc => by
      rcases hc with ⟨hc_ball, hc_ne⟩
      have hc_abs : |c| < ε := by
        simpa [Metric.mem_ball, Real.dist_eq, ε] using hc_ball
      by_cases hc_pos : 0 < c
      · -- Positive scalars use the segment in the original direction.
        have hc_mem : c ∈ Set.Icc (0 : ℝ) ε₁ := by
          constructor
          · exact le_of_lt hc_pos
          · have : c < ε := by
              simpa [abs_of_nonneg (le_of_lt hc_pos)] using hc_abs
            exact this.le.trans (min_le_left _ _)
        simpa [S] using hseg₁ c hc_mem
      · -- Negative scalars are rewritten as positive motion in the opposite direction.
        have hc_neg : c < 0 := lt_of_le_of_ne (not_lt.mp hc_pos) hc_ne
        have hnegc_mem : -c ∈ Set.Icc (0 : ℝ) ε₂ := by
          constructor
          · linarith
          · have : -c < ε := by
              simpa [abs_of_neg hc_neg] using hc_abs
            exact this.le.trans (min_le_right _ _)
        have : x + (-c) • (-y) ∈ C := hseg₂ (-c) hnegc_mem
        simpa [S, smul_neg] using this
      )

end

end Set

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Helper for Proposition 6.12: translating a core point to the origin preserves the core
criterion. -/
private lemma zero_mem_core_translate_preimage_iff {C : Set E} {x : E} :
    (0 : E) ∈ Set.core ((fun y : E ↦ x + y) ⁻¹' C) ↔ x ∈ Set.core C := by
  -- The segment characterization is translation-invariant after evaluating at the origin.
  rw [Set.mem_core_iff, Set.mem_core_iff]
  constructor <;> intro hx y
  · rcases hx y with ⟨ε, hε, hseg⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    simpa using hseg t ht
  · rcases hx y with ⟨ε, hε, hseg⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    simpa using hseg t ht

/-- Helper for Proposition 6.12: for a convex set with nonempty interior, core membership of the
origin forces the origin into the interior. -/
private lemma zero_mem_interior_of_zero_mem_core_of_convex_of_nonempty_interior
    {S : Set E} (hS_convex : Convex ℝ S) (hS_int : (interior S).Nonempty)
    (h0 : (0 : E) ∈ Set.core S) : (0 : E) ∈ interior S := by
  rcases hS_int with ⟨z, hz⟩
  -- Follow the core in the opposite direction and average with the given interior point.
  rcases (Set.mem_core_iff.mp h0) (-z) with ⟨ε, hε, hseg⟩
  have hneg : -ε • z ∈ S := by
    simpa [smul_neg] using hseg ε ⟨le_of_lt hε, le_rfl⟩
  have ha : 0 ≤ 1 / (1 + ε) := by positivity
  have hb : 0 < ε / (1 + ε) := by positivity
  have hab : 1 / (1 + ε) + ε / (1 + ε) = (1 : ℝ) := by
    field_simp [hε.ne']
  have hcombo :
      (1 / (1 + ε)) • (-ε • z) + (ε / (1 + ε)) • z ∈ interior S :=
    hS_convex.combo_self_interior_mem_interior hneg hz ha hb hab
  have hzero :
      (1 / (1 + ε)) • (-ε • z) + (ε / (1 + ε)) • z = (0 : E) := by
    rw [smul_smul, ← add_smul]
    have hscalar : (1 / (1 + ε)) * (-ε) + (ε / (1 + ε)) = (0 : ℝ) := by
      field_simp [hε.ne']
      ring
    rw [hscalar, zero_smul]
  exact hzero ▸ hcombo

/-- Helper for Proposition 6.12: a closed set whose origin lies in the core has nonempty interior.
-/
private lemma interior_nonempty_of_zero_mem_core_of_isClosed
    {S : Set E} (hS_closed : IsClosed S) (h0 : (0 : E) ∈ Set.core S) : (interior S).Nonempty := by
  have h0S : (0 : E) ∈ S := by
    rw [Set.core] at h0
    simpa using (h0.zero_mem : (0 : E) ∈ ((fun y : E ↦ (0 : E) + y) ⁻¹' S))
  -- Core membership lets every point land in a suitable positive dilation of `S`.
  have hUnion : (⋃ n : ℕ, (((n + 1 : ℕ) : ℝ) • S)) = Set.univ := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      rcases (Set.mem_core_iff.mp h0) y with ⟨ε, hε, hseg⟩
      rcases exists_nat_one_div_lt hε with ⟨n, hn⟩
      have ht : (1 / (((n + 1 : ℕ) : ℝ))) ∈ Set.Icc (0 : ℝ) ε := by
        constructor
        · positivity
        · have : (1 / ((n : ℝ) + 1)) < ε := by
            simpa [Nat.cast_add, Nat.cast_one] using hn
          simpa [Nat.cast_add, Nat.cast_one] using this.le
      have hyS : (1 / (((n + 1 : ℕ) : ℝ))) • y ∈ S := by
        simpa using hseg (1 / (((n + 1 : ℕ) : ℝ))) ht
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      refine ⟨(1 / (((n + 1 : ℕ) : ℝ))) • y, hyS, ?_⟩
      have hn_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      calc
        (((n + 1 : ℕ) : ℝ)) • ((1 / (((n + 1 : ℕ) : ℝ))) • y)
            = ((((n + 1 : ℕ) : ℝ)) * (1 / (((n + 1 : ℕ) : ℝ)))) • y := by
                rw [smul_smul]
        _ = y := by
          rw [one_div, mul_inv_cancel₀ hn_ne, one_smul]
  have hclosed_scaled : ∀ n : ℕ, IsClosed ((((n + 1 : ℕ) : ℝ) • S)) := fun n ↦
    hS_closed.smul₀ (((n + 1 : ℕ) : ℝ))
  -- Baire's theorem supplies one scaled copy with nonempty interior.
  rcases nonempty_interior_of_iUnion_of_closed hclosed_scaled hUnion with ⟨n, hscaled_int⟩
  rcases hscaled_int with ⟨x, hx⟩
  have hn_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hx' : x ∈ (((n + 1 : ℕ) : ℝ) • interior S) := by
    rwa [interior_smul₀ hn_ne] at hx
  rcases hx' with ⟨y, hy, rfl⟩
  exact ⟨y, hy⟩

/-- Helper for Proposition 6.12: in finite dimension, a convex set whose origin lies in the core
has nonempty interior. -/
private lemma interior_nonempty_of_zero_mem_core_of_convex_of_finiteDimensional
    {S : Set E} [FiniteDimensional ℝ E] (hS_convex : Convex ℝ S) (h0 : (0 : E) ∈ Set.core S) :
    (interior S).Nonempty := by
  have h0S : (0 : E) ∈ S := by
    rw [Set.core] at h0
    simpa using (h0.zero_mem : (0 : E) ∈ ((fun y : E ↦ (0 : E) + y) ⁻¹' S))
  have hspan_top : Submodule.span ℝ S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    -- Every direction has a nontrivial positive multiple inside `S`, hence lies in the span.
    rcases (Set.mem_core_iff.mp h0) y with ⟨ε, hε, hseg⟩
    have hεy : ε • y ∈ Submodule.span ℝ S := by
      exact Submodule.subset_span (by simpa using hseg ε ⟨le_of_lt hε, le_rfl⟩)
    exact ((Submodule.span ℝ S).smul_mem_iff hε.ne').1 hεy
  have hvector_eq :
      vectorSpan ℝ S = Submodule.span ℝ S := by
    simpa [vsub_eq_sub] using
      (vectorSpan_eq_span_vsub_set_right (k := ℝ) (s := S) (p := (0 : E)) h0S)
  have hAffineTop : affineSpan ℝ S = ⊤ := by
    refine (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
      (k := ℝ) (V := E) (P := E) ⟨0, h0S⟩).2 ?_
    rw [hvector_eq, hspan_top]
  exact (hS_convex.interior_nonempty_iff_affineSpan_eq_top).2 hAffineTop

-- Proof sketch: `interior C ⊆ core C` follows from neighborhood absorbency at each interior point.
-- For the reverse inclusion, argue by cases on the three textbook hypotheses: nonempty interior is
-- the direct convexity case; closedness reduces to that case via Baire-category nonemptiness of
-- the interior; finite dimensionality supplies a small ball inside a convex hull of basis
-- directions.
/-- Proposition 6.12: for a convex set in a complete real normed space, the interior coincides with
its core whenever (i) the interior is nonempty, or (ii) the set is closed, or (iii) the ambient
space is finite-dimensional. -/
theorem interior_eq_core_of_convex {C : Set E} (hC : Convex ℝ C)
    (h : (interior C).Nonempty ∨ IsClosed C ∨ FiniteDimensional ℝ E) :
    interior C = Set.core C := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    -- Translate the interior neighborhood at `x` back to a neighborhood of the origin.
    rw [Set.core]
    have hpre :
        (0 : E) ∈ interior ((fun y : E ↦ x + y) ⁻¹' C) := by
      have hx' : (0 : E) ∈ (Homeomorph.addLeft x) ⁻¹' interior C := by
        simpa using hx
      rwa [(Homeomorph.addLeft x).preimage_interior C] at hx'
    exact absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp hpre)
  · intro x hx
    let S : Set E := ((fun y : E ↦ x + y) ⁻¹' C)
    have h0_core : (0 : E) ∈ Set.core S := by
      simpa [S] using (zero_mem_core_translate_preimage_iff (C := C) (x := x)).2 hx
    have hS_convex : Convex ℝ S := by
      simpa [S, add_comm] using hC.translate_preimage_right x
    have h0_int : (0 : E) ∈ interior S := by
      rcases h with hC_int | hC_closed_or_finite
      · -- Branch (i): transport the given nonempty interior through the translation.
        have hS_int : (interior S).Nonempty := by
          rcases hC_int with ⟨z, hz⟩
          refine ⟨z - x, ?_⟩
          have hz' : z - x ∈ (Homeomorph.addLeft x) ⁻¹' interior C := by
            simpa [sub_eq_add_neg, add_assoc] using hz
          have hz'' : z - x ∈ interior ((Homeomorph.addLeft x) ⁻¹' C) := by
            rwa [(Homeomorph.addLeft x).preimage_interior C] at hz'
          simpa [S] using hz''
        exact zero_mem_interior_of_zero_mem_core_of_convex_of_nonempty_interior
          hS_convex hS_int h0_core
      · rcases hC_closed_or_finite with hC_closed | hC_finite
        · -- Branch (ii): closedness gives nonempty interior by Baire, then branch (i) closes.
          have hS_closed : IsClosed S := by
            simpa [S] using hC_closed.preimage (continuous_const_add x)
          have hS_int : (interior S).Nonempty :=
            interior_nonempty_of_zero_mem_core_of_isClosed hS_closed h0_core
          exact zero_mem_interior_of_zero_mem_core_of_convex_of_nonempty_interior
            hS_convex hS_int h0_core
        · -- Branch (iii): finite dimensionality gives full affine span, hence nonempty interior.
          letI : FiniteDimensional ℝ E := hC_finite
          have hS_int : (interior S).Nonempty :=
            interior_nonempty_of_zero_mem_core_of_convex_of_finiteDimensional hS_convex h0_core
          exact zero_mem_interior_of_zero_mem_core_of_convex_of_nonempty_interior
            hS_convex hS_int h0_core
    -- Push the interior membership of the translated set back to the original point.
    have hx_image : x ∈ (Homeomorph.addLeft x) '' interior S := ⟨0, h0_int, by simp⟩
    have himageS : (Homeomorph.addLeft x) '' S = C := by
      simpa [S] using image_preimage_eq C (Homeomorph.addLeft x).surjective
    have himageInt : (Homeomorph.addLeft x) '' interior S = interior C := by
      rw [(Homeomorph.addLeft x).image_interior, himageS]
    rw [← himageInt]
    exact hx_image

end

end Proposition612Absorbent
