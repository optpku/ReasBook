/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_definition_6_1_extra_1
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.ENNReal.Real
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

-- This source-facing file keeps the Section 6.2 coefficient-space corner/intersection-cut owners
-- local, while reusing the existing Chapter 6 mixed-integer lattice owner and the Chapter 3
-- owner `is_valid_inequality` through a companion bridge.

noncomputable section

section Theorem65

variable {n p k : ℕ}

namespace IntersectionCut

/-- The point in `ℝ^n` obtained from the apex `xbar` by moving along the corner rays with
coefficients `λ`. -/
def corner_point
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (coeffs : Fin k → ℝ) : Fin n → ℝ :=
  xbar + ∑ j : Fin k, coeffs j • rays j

/-- `corner_point xbar rays λ` is the apex plus the ray combination with coefficients `λ`. -/
theorem corner_point_def
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (coeffs : Fin k → ℝ) :
    corner_point xbar rays coeffs = xbar + ∑ j : Fin k, coeffs j • rays j := rfl

/-- The corner polyhedron determined by apex `xbar` and rays `rays`, encoded in the
nonnegative ray-coordinate space. -/
def corner_polyhedron
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Set (Fin k → ℝ) :=
  {coeffs |
    (∀ j : Fin k, 0 ≤ coeffs j) ∧
      corner_point xbar rays coeffs ∈ mixed_integer_prefix_lattice hpn}

/-- Membership in `corner_polyhedron hpn xbar rays` means nonnegative ray coefficients whose
associated point lies in `ℤ^p × ℝ^(n - p)`. -/
theorem mem_corner_polyhedron_iff
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (coeffs : Fin k → ℝ) :
    coeffs ∈ corner_polyhedron hpn xbar rays ↔
      (∀ j : Fin k, 0 ≤ coeffs j) ∧
        corner_point xbar rays coeffs ∈ mixed_integer_prefix_lattice hpn := Iff.rfl

/-- The ambient-point realization `P(B)` of the corner polyhedron, obtained by mapping feasible
ray coefficients to their corresponding points in `ℝ^n`. -/
def ambient_corner_polyhedron
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  corner_point xbar rays '' corner_polyhedron hpn xbar rays

end IntersectionCut

namespace CornerPolyhedronNotation

/- Source-facing ambient notation: `P(hpn, xbar, rays)` is the ambient realization `P(B)` of the
corner polyhedron determined by the mixed-integer prefix block `hpn`, apex `xbar`, and rays
`rays`. -/
scoped notation:max "P(" hpn ", " xbar ", " rays ")" =>
  IntersectionCut.ambient_corner_polyhedron hpn xbar rays

end CornerPolyhedronNotation

open scoped CornerPolyhedronNotation

namespace IntersectionCut

/-- Membership in `P(hpn, xbar, rays)` means that the ambient point is
represented by some coefficient vector of the corner polyhedron. -/
theorem mem_ambient_corner_polyhedron_iff
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (x : Fin n → ℝ) :
    x ∈ P(hpn, xbar, rays) ↔
      ∃ coeffs : Fin k → ℝ,
        coeffs ∈ corner_polyhedron hpn xbar rays ∧
          corner_point xbar rays coeffs = x := Iff.rfl

/-- The admissible nonnegative real parameters `t` for which the point `xbar + t • rays j`
remains in `C`. -/
def ray_admissible_parameters
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) : Set ℝ :=
  {t | 0 ≤ t ∧ xbar + t • rays j ∈ C}

/-- Membership in `ray_admissible_parameters C xbar rays j` is exactly the conjunction
`0 ≤ t` and `xbar + t • rays j ∈ C`. -/
theorem mem_ray_admissible_parameters_iff
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k)
    (t : ℝ) :
    t ∈ ray_admissible_parameters C xbar rays j ↔
      0 ≤ t ∧ xbar + t • rays j ∈ C := Iff.rfl

/-- The ray-intersection parameter `αⱼ` of `C` along the `j`th ray from `xbar`, allowing the
value `∞` exactly when the admissible real ray lengths are unbounded above. -/
def ray_intersection_parameter
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) : ENNReal :=
  sSup (ENNReal.ofReal '' ray_admissible_parameters C xbar rays j)

/-- `ray_intersection_parameter C xbar rays j` is the supremum of the admissible nonnegative
real ray lengths along `rays j`, viewed in `ℝ≥0∞`. -/
theorem ray_intersection_parameter_def
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) :
    ray_intersection_parameter C xbar rays j =
      sSup (ENNReal.ofReal '' ray_admissible_parameters C xbar rays j) :=
  rfl

/-- The coefficient of the intersection cut attached to `C`, namely `1 / αⱼ` with the convention
that the coefficient is `0` when `αⱼ = ∞`. -/
def intersection_cut_coeff
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) : ℝ :=
  ((ray_intersection_parameter C xbar rays j).toReal)⁻¹

/-- The intersection-cut coefficient is the reciprocal of the corresponding ray-intersection
parameter after converting from `ℝ≥0∞` to `ℝ`. -/
theorem intersection_cut_coeff_eq_inv_ray_intersection_parameter
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) :
    intersection_cut_coeff C xbar rays j =
      ((ray_intersection_parameter C xbar rays j).toReal)⁻¹ := rfl

/-- If `C₁ ⊆ C₂`, then the ray-intersection parameters are monotone along every chosen ray. -/
theorem ray_intersection_parameter_mono_of_subset
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    {C1 C2 : Set (Fin n → ℝ)}
    (hsubset : C1 ⊆ C2)
    (j : Fin k) :
    ray_intersection_parameter C1 xbar rays j ≤
      ray_intersection_parameter C2 xbar rays j := by
  -- The admissible-parameter set only grows under set inclusion, so its supremum grows as well.
  rw [ray_intersection_parameter_def, ray_intersection_parameter_def]
  refine sSup_le ?_
  rintro _ ⟨t, ht, rfl⟩
  exact le_sSup ⟨t, ⟨ht.1, hsubset ht.2⟩, rfl⟩

/-- If `xbar ∈ interior C`, then each ray-intersection parameter is positive (possibly `∞`) along
the chosen ray family. -/
theorem ray_intersection_parameter_pos_of_mem_interior
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    {C : Set (Fin n → ℝ)}
    (hxbar : xbar ∈ interior C)
    (j : Fin k) :
    0 < ray_intersection_parameter C xbar rays j := by
  -- Openness of `interior C` gives a small positive ray segment that stays in `C`.
  rw [ray_intersection_parameter_def]
  have hpreimage :
      {t : ℝ | xbar + t • rays j ∈ interior C} ∈ nhds (0 : ℝ) := by
    have hcont : Continuous fun t : ℝ ↦ xbar + t • rays j := by
      continuity
    simpa using
      hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hxbar)
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hεpos, hball⟩
  have hεmem : xbar + (ε / 2) • rays j ∈ interior C := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hεpos)]
    linarith
  have hhalf_mem : ε / 2 ∈ ray_admissible_parameters C xbar rays j := by
    exact ⟨(half_pos hεpos).le, interior_subset hεmem⟩
  have hhalf_pos : (0 : ENNReal) < ENNReal.ofReal (ε / 2) := by
    exact ENNReal.ofReal_pos.mpr (half_pos hεpos)
  exact lt_of_lt_of_le hhalf_pos (le_sSup ⟨ε / 2, hhalf_mem, rfl⟩)

/-- Helper for Theorem 6.5: a strict lower bound below
`ray_intersection_parameter C xbar rays j` can be realized by an admissible real ray parameter
strictly above that bound. -/
lemma existsAdmissibleRayParameterAbove
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k)
    {s : ℝ}
    (hs_nonneg : 0 ≤ s)
    (hs :
      ENNReal.ofReal s < ray_intersection_parameter C xbar rays j) :
    ∃ t : ℝ, s < t ∧ 0 ≤ t ∧ xbar + t • rays j ∈ C := by
  -- Unpack the supremum definition to get an admissible parameter whose ENNReal image is above
  -- `s`, then convert that strict ENNReal inequality back to a real inequality.
  rw [ray_intersection_parameter_def] at hs
  rcases lt_sSup_iff.mp hs with ⟨u, ⟨t, ht, rfl⟩, hu⟩
  refine ⟨t, ?_, ht.1, ht.2⟩
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs_nonneg).mp hu

/-- If `C₁ ⊆ C₂` and `xbar ∈ interior C₁`, then the intersection-cut coefficients decrease from
`C₁` to `C₂` along every chosen ray. -/
theorem intersection_cut_coeff_antitone_of_subset
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    {C1 C2 : Set (Fin n → ℝ)}
    (hx1 : xbar ∈ interior C1)
    (hsubset : C1 ⊆ C2)
    (j : Fin k) :
    intersection_cut_coeff C2 xbar rays j ≤
      intersection_cut_coeff C1 xbar rays j := by
  -- The larger set has a larger ray parameter, and reciprocals reverse that order.
  let α1 := ray_intersection_parameter C1 xbar rays j
  let α2 := ray_intersection_parameter C2 xbar rays j
  have hαmono : α1 ≤ α2 := ray_intersection_parameter_mono_of_subset xbar rays hsubset j
  have hα1pos : 0 < α1 := by
    simpa [α1] using ray_intersection_parameter_pos_of_mem_interior xbar rays hx1 j
  rw [intersection_cut_coeff_eq_inv_ray_intersection_parameter,
    intersection_cut_coeff_eq_inv_ray_intersection_parameter]
  by_cases hα2top : α2 = ⊤
  · -- When the larger-set parameter is infinite, its reciprocal coefficient is `0`.
    simp [α2, hα2top, inv_nonneg, ENNReal.toReal_nonneg]
  · have hα1top : α1 ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hαmono (lt_top_iff_ne_top.mpr hα2top))
    have hα1toReal_pos : 0 < α1.toReal := by
      exact ENNReal.toReal_pos_iff.mpr ⟨hα1pos, lt_top_iff_ne_top.mpr hα1top⟩
    have hα2pos : 0 < α2 := lt_of_lt_of_le hα1pos hαmono
    have hα2toReal_pos : 0 < α2.toReal := by
      exact ENNReal.toReal_pos_iff.mpr ⟨hα2pos, lt_top_iff_ne_top.mpr hα2top⟩
    rw [inv_le_inv₀ hα2toReal_pos hα1toReal_pos]
    exact ENNReal.toReal_mono hα2top hαmono

/-- Helper for Theorem 6.5: a strict cut violation yields admissible ray points whose reciprocal
weights still sum to less than `1`. -/
lemma existsAdmissibleParametersWithStrictWeightSum
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (coeffs : Fin k → ℝ)
    (hxbar_mem : xbar ∈ interior C)
    (hcoeffs_nonneg : ∀ j : Fin k, 0 ≤ coeffs j)
    (hcut_lt : intersection_cut_coeff C xbar rays ⬝ᵥ coeffs < 1) :
    ∃ t : Fin k → ℝ,
      (∀ j : Fin k, 0 < t j ∧ xbar + t j • rays j ∈ C) ∧
        ∑ j : Fin k, coeffs j / t j < 1 := by
  classical
  let cutSum : ℝ := intersection_cut_coeff C xbar rays ⬝ᵥ coeffs
  let η : ℝ := (1 - cutSum) / (2 * ((k : ℝ) + 1))
  let β : Fin k → ℝ := fun j ↦ coeffs j * intersection_cut_coeff C xbar rays j + η
  let s : Fin k → ℝ := fun j ↦ coeffs j / β j
  have hcutSum_lt_one : cutSum < 1 := by
    simpa [cutSum] using hcut_lt
  have hη_pos : 0 < η := by
    -- The strict cut slack provides a uniform positive margin to enlarge every denominator.
    have hslack_pos : 0 < 1 - cutSum := by
      linarith
    have hden_pos : 0 < 2 * ((k : ℝ) + 1) := by
      positivity
    exact div_pos hslack_pos hden_pos
  have hcoeff_nonneg_cut : ∀ j : Fin k, 0 ≤ coeffs j * intersection_cut_coeff C xbar rays j := by
    intro j
    have hcut_nonneg : 0 ≤ intersection_cut_coeff C xbar rays j := by
      rw [intersection_cut_coeff_eq_inv_ray_intersection_parameter]
      exact inv_nonneg.mpr ENNReal.toReal_nonneg
    exact mul_nonneg (hcoeffs_nonneg j) hcut_nonneg
  have hβ_pos : ∀ j : Fin k, 0 < β j := by
    intro j
    dsimp [β]
    linarith [hcoeff_nonneg_cut j, hη_pos]
  have hs_nonneg : ∀ j : Fin k, 0 ≤ s j := by
    intro j
    dsimp [s]
    exact div_nonneg (hcoeffs_nonneg j) (hβ_pos j).le
  have hs_lt_parameter :
      ∀ j : Fin k, ENNReal.ofReal (s j) < ray_intersection_parameter C xbar rays j := by
    intro j
    let α : ENNReal := ray_intersection_parameter C xbar rays j
    by_cases hα_top : α = ⊤
    · -- Infinite ray-intersection parameters dominate every finite real bound.
      have hlt_top : ENNReal.ofReal (s j) < ⊤ := by
        exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
      simpa [α, hα_top] using hlt_top
    · -- In the finite case, the enlarged denominator makes `s j` strictly smaller than `α`.
      have hα_pos : 0 < α := by
        simpa [α] using ray_intersection_parameter_pos_of_mem_interior xbar rays hxbar_mem j
      have hα_toReal_pos : 0 < α.toReal := by
        exact ENNReal.toReal_pos_iff.mpr ⟨hα_pos, lt_top_iff_ne_top.mpr hα_top⟩
      have hβ_gt_cut :
          coeffs j * intersection_cut_coeff C xbar rays j < β j := by
        dsimp [β]
        exact lt_add_of_pos_right _ hη_pos
      have hdiv_lt : coeffs j / α.toReal < β j := by
        simpa [α, intersection_cut_coeff_eq_inv_ray_intersection_parameter, div_eq_mul_inv,
          mul_comm, mul_left_comm, mul_assoc] using hβ_gt_cut
      have hcoeff_lt : coeffs j < β j * α.toReal := by
        exact (div_lt_iff₀ hα_toReal_pos).mp hdiv_lt
      have hs_lt_toReal : s j < α.toReal := by
        exact (div_lt_iff₀ (hβ_pos j)).mpr <| by
          simpa [s, α, mul_comm, mul_left_comm, mul_assoc] using hcoeff_lt
      exact (ENNReal.ofReal_lt_iff_lt_toReal (hs_nonneg j) hα_top).mpr hs_lt_toReal
  have hexists :
      ∀ j : Fin k, ∃ t : ℝ, s j < t ∧ 0 ≤ t ∧ xbar + t • rays j ∈ C := by
    intro j
    exact existsAdmissibleRayParameterAbove C xbar rays j (hs_nonneg j) (hs_lt_parameter j)
  choose t ht_gt ht_nonneg ht_mem using hexists
  have hterm_lt : ∀ j : Fin k, coeffs j / t j < β j := by
    intro j
    have ht_pos : 0 < t j := lt_of_le_of_lt (hs_nonneg j) (ht_gt j)
    have hcoeff_lt : coeffs j < t j * β j := by
      exact (div_lt_iff₀ (hβ_pos j)).mp (ht_gt j)
    exact (div_lt_iff₀ ht_pos).mpr <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcoeff_lt
  have hsum_le_beta : ∑ j : Fin k, coeffs j / t j ≤ ∑ j : Fin k, β j := by
    exact Finset.sum_le_sum fun j _ ↦ (hterm_lt j).le
  have hbeta_sum_eq : ∑ j : Fin k, β j = cutSum + ∑ _j : Fin k, η := by
    -- Expand the augmented denominators once, separating the original cut value from the slack.
    simp [β, cutSum, dotProduct, mul_comm, add_comm, Finset.sum_add_distrib]
  have heta_sum_le : ∑ _j : Fin k, η ≤ (1 - cutSum) / 2 := by
    have hmul_le : (k : ℝ) * η ≤ ((k : ℝ) + 1) * η := by
      nlinarith [show (0 : ℝ) ≤ η by exact le_of_lt hη_pos]
    calc
      ∑ _j : Fin k, η = (k : ℝ) * η := by
        simp
      _ ≤ ((k : ℝ) + 1) * η := hmul_le
      _ = (1 - cutSum) / 2 := by
        have hk1_ne : ((k : ℝ) + 1) ≠ 0 := by
          positivity
        calc
          ((k : ℝ) + 1) * η = ((k : ℝ) + 1) * ((1 - cutSum) / (2 * ((k : ℝ) + 1))) := by
            rfl
          _ = (1 - cutSum) / 2 := by
            field_simp [hk1_ne]
  have hbeta_sum_lt_one : ∑ j : Fin k, β j < 1 := by
    rw [hbeta_sum_eq]
    nlinarith [heta_sum_le, hcutSum_lt_one]
  refine ⟨t, ?_, ?_⟩
  · intro j
    -- Each chosen admissible parameter is strictly positive because it lies above the nonnegative
    -- lower bound `s j`.
    refine ⟨lt_of_le_of_lt (hs_nonneg j) (ht_gt j), ht_mem j⟩
  · exact lt_of_le_of_lt hsum_le_beta hbeta_sum_lt_one

/-- Helper for Theorem 6.5: `corner_point xbar rays coeffs` admits the stable affine normal form
used in the convexity argument once the admissible ray lengths `t` are fixed. -/
lemma cornerPoint_eq_weightedAdmissibleCombination
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (coeffs t : Fin k → ℝ)
    (ht_ne : ∀ j : Fin k, t j ≠ 0) :
    corner_point xbar rays coeffs =
      (1 - ∑ j : Fin k, coeffs j / t j) • xbar +
        ∑ j : Fin k, (coeffs j / t j) • (xbar + t j • rays j) := by
  ext i
  have hsum_xbar :
      ∑ j : Fin k, (coeffs j / t j) * xbar i = (∑ j : Fin k, coeffs j / t j) * xbar i := by
    simpa using
      (Finset.sum_mul Finset.univ (fun j : Fin k ↦ coeffs j / t j) (xbar i)).symm
  have hsum_rays :
      ∑ j : Fin k, (coeffs j / t j) * (t j * rays j i) = ∑ j : Fin k, coeffs j * rays j i := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    field_simp [ht_ne j]
  have hsum_expand :
      ∑ j : Fin k, (coeffs j / t j) * (xbar i + t j * rays j i) =
        ∑ j : Fin k, ((coeffs j / t j) * xbar i + (coeffs j / t j) * (t j * rays j i)) := by
    simp only [mul_add]
  calc
    corner_point xbar rays coeffs i = xbar i + ∑ j : Fin k, coeffs j * rays j i := by
      simp [corner_point_def]
    _ = (1 - ∑ j : Fin k, coeffs j / t j) * xbar i +
        ((∑ j : Fin k, coeffs j / t j) * xbar i + ∑ j : Fin k, coeffs j * rays j i) := by
          ring
    _ = (1 - ∑ j : Fin k, coeffs j / t j) * xbar i +
        (∑ j : Fin k, (coeffs j / t j) * xbar i +
          ∑ j : Fin k, (coeffs j / t j) * (t j * rays j i)) := by
          rw [hsum_xbar, hsum_rays]
    _ = (1 - ∑ j : Fin k, coeffs j / t j) * xbar i +
        ∑ j : Fin k, ((coeffs j / t j) * xbar i + (coeffs j / t j) * (t j * rays j i)) := by
          rw [← Finset.sum_add_distrib]
    _ = (1 - ∑ j : Fin k, coeffs j / t j) * xbar i +
        ∑ j : Fin k, (coeffs j / t j) * (xbar i + t j * rays j i) := by
          exact congrArg (fun y : ℝ ↦ (1 - ∑ j : Fin k, coeffs j / t j) * xbar i + y)
            hsum_expand.symm
    _ = ((1 - ∑ j : Fin k, coeffs j / t j) • xbar +
        ∑ j : Fin k, (coeffs j / t j) • (xbar + t j • rays j)) i := by
          simpa using congrArg
            (fun y : ℝ ↦ (1 - ∑ j : Fin k, coeffs j / t j) * xbar i + y) hsum_expand

/-- Helper for Theorem 6.5: a convex combination of points of `C` with one strictly positive
weight on the interior anchor `xbar` remains in `interior C`. -/
lemma weightedCombination_memInterior_of_sum_lt_one
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    (μ : Fin k → ℝ)
    (z : Fin k → Fin n → ℝ)
    (hμ_nonneg : ∀ j : Fin k, 0 ≤ μ j)
    (hμ_sum_lt_one : ∑ j : Fin k, μ j < 1)
    (hz_mem : ∀ j : Fin k, z j ∈ C) :
    (1 - ∑ j : Fin k, μ j) • xbar + ∑ j : Fin k, μ j • z j ∈ interior C := by
  let σ : ℝ := ∑ j : Fin k, μ j
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ]
    exact Finset.sum_nonneg fun j _ ↦ hμ_nonneg j
  by_cases hσ_zero : σ = 0
  · -- When the external weights vanish, the affine combination is just the interior point `xbar`.
    have hμ_zero_fun : μ = 0 := by
      exact (Fintype.sum_eq_zero_iff_of_nonneg hμ_nonneg).mp hσ_zero
    have hμ_zero : ∀ j : Fin k, μ j = 0 := by
      intro j
      simpa using congr_fun hμ_zero_fun j
    have hsum_zero : ∑ j : Fin k, μ j • z j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      simp [hμ_zero j]
    have hcollapse :
        (1 - ∑ j : Fin k, μ j) • xbar + ∑ j : Fin k, μ j • z j = xbar := by
      simp [σ, hσ_zero, hsum_zero]
    rw [hcollapse]
    exact hxbar_mem
  · -- Otherwise, normalize the outer finite sum to a point of `C` and combine it with `xbar`.
    have hσ_ne : 0 ≠ σ := by
      simpa [eq_comm] using hσ_zero
    have hσ_pos : 0 < σ := lt_of_le_of_ne hσ_nonneg hσ_ne
    have hcenter_mem : (Finset.univ : Finset (Fin k)).centerMass μ z ∈ C := by
      simpa [σ] using
        hC_convex.centerMass_mem
          (fun j _ ↦ hμ_nonneg j)
          (by simpa [σ] using hσ_pos)
          (fun j _ ↦ hz_mem j)
    have hrewrite :
        (1 - ∑ j : Fin k, μ j) • xbar + ∑ j : Fin k, μ j • z j =
          (1 - σ) • xbar + σ • (Finset.univ : Finset (Fin k)).centerMass μ z := by
      rw [Finset.centerMass]
      simp [σ, hσ_pos.ne']
    rw [hrewrite]
    refine hC_convex.combo_interior_self_mem_interior hxbar_mem hcenter_mem ?_ hσ_nonneg ?_
    · simpa [σ] using sub_pos.mpr hμ_sum_lt_one
    · ring

/-- Theorem 6.5. Let `C ⊆ ℝ^n` be a closed convex set whose interior contains `xbar` but no point
in `ℤ^p × ℝ^(n - p)`. Then the intersection cut defined by `C`, expressed by the reciprocals of
the ray-intersection parameters of the rays of the corner polyhedron, is a valid inequality for
that corner polyhedron. -/
theorem intersection_cut_valid_for_corner_polyhedron
    (hpn : p ≤ n)
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    (hC_lattice_free : Disjoint (interior C) (mixed_integer_prefix_lattice hpn)) :
    ∀ ⦃coeffs : Fin k → ℝ⦄,
      coeffs ∈ corner_polyhedron hpn xbar rays →
        1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ coeffs := by
  let _ := hC_closed
  intro coeffs hcoeffs_mem
  rcases (mem_corner_polyhedron_iff hpn xbar rays coeffs).mp hcoeffs_mem with
    ⟨hcoeffs_nonneg, hcorner_mem⟩
  by_contra hcut_valid
  have hcut_lt : intersection_cut_coeff C xbar rays ⬝ᵥ coeffs < 1 := by
    exact lt_of_not_ge hcut_valid
  rcases existsAdmissibleParametersWithStrictWeightSum
      C xbar rays coeffs hxbar_mem hcoeffs_nonneg hcut_lt with
    ⟨t, ht, hweight_sum_lt_one⟩
  have ht_pos : ∀ j : Fin k, 0 < t j := fun j ↦ (ht j).1
  have ht_mem : ∀ j : Fin k, xbar + t j • rays j ∈ C := fun j ↦ (ht j).2
  have hcorner_interior : corner_point xbar rays coeffs ∈ interior C := by
    -- Route correction: replace the abandoned induction by one global admissible-weight witness
    -- and a stable affine normal form for `corner_point`.
    rw [cornerPoint_eq_weightedAdmissibleCombination xbar rays coeffs t
      (fun j ↦ ne_of_gt (ht_pos j))]
    refine weightedCombination_memInterior_of_sum_lt_one
      C xbar hC_convex hxbar_mem
      (fun j : Fin k ↦ coeffs j / t j)
      (fun j : Fin k ↦ xbar + t j • rays j) ?_ hweight_sum_lt_one ht_mem
    -- The normalized weights are nonnegative because both the coefficients and the chosen
    -- admissible parameters are nonnegative.
    intro j
    exact div_nonneg (hcoeffs_nonneg j) (ht_pos j).le
  -- The violated cut would place a mixed-integer corner point inside `interior C`, contradicting
  -- the lattice-freeness assumption.
  exact (Set.disjoint_left.mp hC_lattice_free) hcorner_interior hcorner_mem

/-- Companion bridge: Theorem 6.5 in the canonical Chapter 3 owner `is_valid_inequality`. -/
theorem intersection_cut_valid_for_corner_polyhedron_is_valid_inequality
    (hpn : p ≤ n)
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    (hC_lattice_free : Disjoint (interior C) (mixed_integer_prefix_lattice hpn)) :
    is_valid_inequality
      (corner_polyhedron hpn xbar rays)
      (-intersection_cut_coeff C xbar rays)
      (-1) := by
  exact valid_ge_inequality_iff_is_valid_inequality_neg.mp
    (intersection_cut_valid_for_corner_polyhedron
      hpn C xbar rays hC_closed hC_convex hxbar_mem hC_lattice_free)

end IntersectionCut

end Theorem65
