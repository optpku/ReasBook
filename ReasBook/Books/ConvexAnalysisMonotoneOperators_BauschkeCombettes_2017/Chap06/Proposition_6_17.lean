/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace Set

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Proposition 6.17: if the origin belongs to the cone of a convex set, then it
already belongs to the set. -/
lemma zero_mem_of_zero_mem_cone_of_convex {D : Set E} (hD_convex : Convex ℝ D)
    (h0_cone : (0 : E) ∈ cone D) :
    (0 : E) ∈ D := by
  -- Unpack the cone witness and use positivity of the scalar to cancel the dilation.
  rcases (mem_cone_iff_exists_pos_smul_mem hD_convex).1 h0_cone with ⟨a, ha, haD⟩
  rcases haD with ⟨y, hy, hay⟩
  have hy_zero : y = 0 := by
    apply smul_right_injective E ha.ne'
    simp [hay]
  simpa [hy_zero] using hy

/-- Helper for Proposition 6.17: an interior neighborhood of the origin generates the whole space
through the cone of the interior. -/
lemma cone_interior_eq_univ_of_zero_mem_interior {C : Set E} (hC_convex : Convex ℝ C)
    (h0_int : (0 : E) ∈ interior C) :
    cone (interior C) = (univ : Set E) := by
  have hC_int_convex : Convex ℝ (interior C) := hC_convex.interior
  -- Scale any ambient vector into a small ball around the origin contained in `interior C`.
  have hmem : interior C ∈ nhds (0 : E) := isOpen_interior.mem_nhds h0_int
  rcases Metric.mem_nhds_iff.mp hmem with ⟨ε, hε, hball⟩
  ext y
  constructor
  · intro _
    simp
  · intro _
    let t : ℝ := ε / (1 + ‖y‖)
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hty_norm : ‖t • y‖ < ε := by
      have hden : 0 < 1 + ‖y‖ := by positivity
      have hy_lt : ‖y‖ < 1 + ‖y‖ := by
        nlinarith [norm_nonneg y]
      have hfrac_lt : ‖y‖ / (1 + ‖y‖) < (1 : ℝ) := by
        exact (div_lt_iff₀ hden).2 <| by simpa using hy_lt
      have hlt' : ε / (1 + ‖y‖) * ‖y‖ < ε := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          mul_lt_mul_of_pos_left hfrac_lt hε
      have hlt : t * ‖y‖ < ε := by
        simpa [t] using hlt'
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht] using hlt
    have hty_mem : t • y ∈ interior C := hball <| by
      simpa [Metric.mem_ball, dist_eq_norm] using hty_norm
    exact (mem_cone_iff_exists_pos_smul_mem hC_int_convex).2
      ⟨1 / t, by positivity, ⟨t • y, hty_mem, by
        simpa [one_div, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]⟩⟩

/-- Helper for Proposition 6.17: if the cone of the interior is all of the ambient space, then the
origin is an interior point. -/
lemma zero_mem_interior_of_cone_interior_eq_univ {C : Set E} (hC_convex : Convex ℝ C)
    (hC_int_nonempty : (interior C).Nonempty) (hcone : cone (interior C) = (univ : Set E)) :
    (0 : E) ∈ interior C := by
  have hC_int_convex : Convex ℝ (interior C) := hC_convex.interior
  rcases hC_int_nonempty with ⟨z, hz⟩
  have hnegz : -z ∈ cone (interior C) := by
    simpa [hcone]
  -- Represent `-z` by a positive dilate of an interior point and average back to the origin.
  rcases (mem_cone_iff_exists_pos_smul_mem hC_int_convex).1 hnegz with ⟨c, hc, hc_mem⟩
  rcases hc_mem with ⟨y, hy, hcy⟩
  have ha : 0 ≤ c / (c + 1) := by positivity
  have hb : 0 < 1 / (c + 1) := by positivity
  have hab : c / (c + 1) + 1 / (c + 1) = (1 : ℝ) := by
    field_simp [hc.ne']
  have hcombo :
      (c / (c + 1)) • y + (1 / (c + 1)) • z ∈ interior C := by
    -- Keep one point interior and take a convex combination with the second point from `C`.
    exact hC_convex.combo_self_interior_mem_interior (interior_subset hy) hz ha hb hab
  have hzero :
      (c / (c + 1)) • y + (1 / (c + 1)) • z = (0 : E) := by
    have hsum : c • y + z = (0 : E) := by
      simpa [hcy]
    calc
      (c / (c + 1)) • y + (1 / (c + 1)) • z
          = (1 / (c + 1)) • (c • y) + (1 / (c + 1)) • z := by
              rw [div_eq_mul_inv, one_div, smul_smul, mul_comm c ((c + 1)⁻¹)]
      _ = (1 / (c + 1)) • (c • y + z) := by rw [smul_add]
      _ = (1 / (c + 1)) • (0 : E) := by rw [hsum]
      _ = (0 : E) := by rw [smul_zero]
  exact hzero ▸ hcombo

/-- Helper for Proposition 6.17: a dense cone over a convex set with nonempty interior already
forces the cone of the interior to be the whole space. -/
lemma cone_interior_eq_univ_of_closure_cone_eq_univ {C : Set E} (hC_convex : Convex ℝ C)
    (hC_int_nonempty : (interior C).Nonempty) (hclosure : closure (cone C) = (univ : Set E)) :
    cone (interior C) = (univ : Set E) := by
  have hcone_convex : Convex ℝ (cone C) := by
    simpa [Set.cone_def] using (ConvexCone.hull ℝ C).convex
  have hcone_int_nonempty : (interior (cone C)).Nonempty := by
    -- The original interior sits inside the cone, so the cone also has nonempty interior.
    exact hC_int_nonempty.mono fun x hx ↦
      interior_mono (fun y hy ↦ ConvexCone.subset_hull hy) hx
  have hcone_int :
      interior (closure (cone C)) = interior (cone C) :=
    interior_closure_eq_interior_of_convex_nonempty_interior hcone_convex hcone_int_nonempty
  have hcone_int_univ : interior (cone C) = (univ : Set E) := by
    calc
      interior (cone C) = interior (closure (cone C)) := hcone_int.symm
      _ = (univ : Set E) := by rw [hclosure]; simp
  have h0_cone_int : (0 : E) ∈ interior (cone C) := by
    simpa [hcone_int_univ]
  have h0C : (0 : E) ∈ C :=
    zero_mem_of_zero_mem_cone_of_convex hC_convex (interior_subset h0_cone_int)
  -- Proposition 6.16 now identifies the interior of the cone with the cone of the interior.
  calc
    cone (interior C) = interior (cone C) :=
      (interior_cone_eq_cone_interior hC_convex h0C hC_int_nonempty).symm
    _ = (univ : Set E) := hcone_int_univ

-- Proof sketch: if `0 ∈ interior C`, then an open neighborhood of `0` contained in `C` scales to
-- cover the whole space, so `cone (interior C) = univ`; the implications `(ii) → (iii) → (iv)`
-- are immediate from monotonicity of `cone` and closure. For `(iv) → (ii)`, use Proposition 6.16
-- together with convexity of `cone C` and invariance of interior under closure for convex sets with
-- nonempty interior. For `(ii) → (i)`, membership `0 ∈ cone (interior C)` gives a positive scalar
-- multiple of some point of `interior C` equal to `0`, hence `0` itself lies in `interior C`.
/-- Proposition 6.17: for a convex subset `C` of a real normed space with nonempty interior, the
following are equivalent: (i) `0 ∈ interior C`; (ii) `cone (interior C) = univ`; (iii)
`cone C = univ`; and (iv) `closure (cone C) = univ`. -/
theorem zero_mem_interior_tfae_cone_interior_cone_closure_eq_univ {C : Set E}
    (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty) :
    List.TFAE
      [ 0 ∈ interior C,
        cone (interior C) = univ,
        cone C = univ,
        closure (cone C) = univ ] := by
  -- Route correction: keep the textbook cycle `1 → 2 → 3 → 4 → 2`, and only derive `0 ∈ C`
  -- inside the reverse implication where Proposition 6.16 needs it.
  tfae_have 1 → 2 := by
    intro h0_int
    -- The interior neighborhood of the origin absorbs every direction.
    exact cone_interior_eq_univ_of_zero_mem_interior hC_convex h0_int
  tfae_have 2 → 3 := by
    intro hcone_int
    -- The cone of `interior C` sits inside the cone of `C`, so `univ` does as well.
    have hsubset : cone (interior C) ⊆ cone C := by
      exact ConvexCone.hull_min fun x hx ↦ ConvexCone.subset_hull (interior_subset hx)
    ext x
    constructor
    · intro _
      simp
    · intro _
      exact hsubset <| by simpa [hcone_int]
  tfae_have 3 → 4 := by
    intro hcone
    -- Closing the cone cannot shrink `univ`.
    ext x
    constructor
    · intro _
      simp
    · intro _
      exact subset_closure <| by simpa [hcone]
  tfae_have 4 → 2 := by
    intro hclosure
    -- Dense convex cones with nonempty interior have full interior, and Proposition 6.16 closes.
    exact cone_interior_eq_univ_of_closure_cone_eq_univ hC_convex hC_int_nonempty hclosure
  tfae_have 2 → 1 := by
    intro hcone
    -- Evaluate the cone equality at the origin and average back into the interior.
    exact zero_mem_interior_of_cone_interior_eq_univ hC_convex hC_int_nonempty hcone
  tfae_finish

end

end Set
