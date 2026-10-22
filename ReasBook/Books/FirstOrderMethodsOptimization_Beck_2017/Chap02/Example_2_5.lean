/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E]

/-- The distance-based potential `x ↦ (‖x‖² - d_C(x)²) / 2` associated to a set in a real inner
product space. -/
noncomputable def euclidean_distance_potential (C : Set E) : E → ℝ :=
  fun x ↦ (‖x‖ ^ 2 - infDist x C ^ 2) / 2

@[simp] theorem euclidean_distance_potential_apply (C : Set E) (x : E) :
    euclidean_distance_potential C x = (‖x‖ ^ 2 - infDist x C ^ 2) / 2 :=
  rfl

@[simp] theorem euclidean_distance_potential_empty :
    euclidean_distance_potential (∅ : Set E) = fun x : E ↦ ‖x‖ ^ 2 / 2 := by
  funext x
  simp [euclidean_distance_potential]

end

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Example 2.5: rewrite each affine witness as a transformed squared distance. -/
lemma affineValue_eq_half_norm_sq_sub_sqDist (x y : E) :
    inner ℝ y x - (‖y‖ ^ 2) / 2 = (‖x‖ ^ 2 - dist x y ^ 2) / 2 := by
  -- Expand the squared distance with the real polarization identity and simplify the affine term.
  rw [dist_eq_norm, norm_sub_sq_real, real_inner_comm]
  ring

/-- Helper for Example 2.5: every affine witness is bounded above by the distance potential. -/
lemma affineValue_le_potential (C : Set E) (x y : E) (hy : y ∈ C) :
    inner ℝ y x - (‖y‖ ^ 2) / 2 ≤ euclidean_distance_potential C x := by
  -- Compare the witness distance with the minimal distance defining `infDist`.
  rw [euclidean_distance_potential_apply, affineValue_eq_half_norm_sq_sub_sqDist]
  have hd : infDist x C ≤ dist x y := Metric.infDist_le_dist_of_mem hy
  have hdn : 0 ≤ infDist x C := Metric.infDist_nonneg
  have hyn : 0 ≤ dist x y := dist_nonneg
  nlinarith

/-- Helper for Example 2.5: the affine witness respects convex combinations in the `x` variable. -/
lemma affineValue_combo (u x z : E) (a b : ℝ) (hab : a + b = 1) :
    inner ℝ u (a • x + b • z) - (‖u‖ ^ 2) / 2 =
      a * (inner ℝ u x - (‖u‖ ^ 2) / 2) + b * (inner ℝ u z - (‖u‖ ^ 2) / 2) := by
  -- Expand the inner product across the convex combination and collapse the constant term with
  -- `a + b = 1`.
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  nlinarith

/-- Helper for Example 2.5: the half squared norm is convex on the whole space. -/
lemma half_norm_sq_convexOn_univ :
    ConvexOn ℝ Set.univ (fun x : E ↦ (‖x‖ ^ 2) / 2) := by
  -- First prove convexity of the squared norm from convexity of the norm.
  have hnorm : ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖) := convexOn_univ_norm
  have hsq : ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ 2) :=
    hnorm.pow (fun x _ ↦ norm_nonneg x) 2
  -- Then scale by the nonnegative constant `1 / 2`.
  simpa [one_div, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hsq.smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)

-- Proof sketch: expand `Metric.infDist` as the infimum of the distance function, use the identity
-- `‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ y x + ‖y‖ ^ 2`, and rewrite a constant minus an infimum
-- as the corresponding supremum.
/-- The distance-based potential agrees with the supremum of the affine functions
`x ↦ inner ℝ y x - ‖y‖² / 2` indexed by `y ∈ C`. -/
theorem euclidean_distance_potential_eq_sSup_affine (C : Set E) (hC : C.Nonempty) :
    euclidean_distance_potential C =
      fun x ↦ sSup ((fun y : E ↦ inner ℝ y x - (‖y‖ ^ 2) / 2) '' C) := by
  funext x
  let S : Set ℝ := (fun y : E ↦ inner ℝ y x - (‖y‖ ^ 2) / 2) '' C
  let pot : ℝ := euclidean_distance_potential C x
  have hS_nonempty : S.Nonempty := by
    rcases hC with ⟨y, hy⟩
    exact ⟨_, ⟨y, hy, rfl⟩⟩
  have hS_upper : ∀ z ∈ S, z ≤ pot := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    dsimp [pot]
    exact affineValue_le_potential C x y hy
  have hS_bdd : BddAbove S := ⟨pot, hS_upper⟩
  refine le_antisymm ?_ (csSup_le hS_nonempty hS_upper)
  -- Approximate `infDist x C` from above by an actual witness distance to reach the supremum.
  by_contra hpot
  let ε : ℝ := pot - sSup S
  let d : ℝ := infDist x C
  let δ : ℝ := min 1 (ε / (2 * (d + 1)))
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact sub_pos.mpr (lt_of_not_ge hpot)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    exact Metric.infDist_nonneg
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min zero_lt_one ?_
    have hd1 : 0 < d + 1 := by
      nlinarith
    have hden : 0 < 2 * (d + 1) := by
      nlinarith
    exact div_pos hεpos hden
  have hδle_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδle : δ ≤ ε / (2 * (d + 1)) := by
    dsimp [δ]
    exact min_le_right _ _
  have hdlt : d < d + δ := by
    nlinarith
  rcases (Metric.infDist_lt_iff (x := x) (s := C) (r := d + δ) hC).mp (by simpa [d] using hdlt) with
    ⟨y, hyC, hyr⟩
  have hδmul : 2 * (d + 1) * δ ≤ ε := by
    have hden : 0 < 2 * (d + 1) := by
      nlinarith
    have hmul : δ * (2 * (d + 1)) ≤ ε := (le_div_iff₀ hden).mp hδle
    nlinarith
  have hδbound : d * δ + δ ^ 2 / 2 < ε := by
    nlinarith
  have hy_lt : sSup S < inner ℝ y x - (‖y‖ ^ 2) / 2 := by
    have hyr' : dist x y < d + δ := by
      simpa [d] using hyr
    have hy_nonneg : 0 ≤ dist x y := dist_nonneg
    calc
      sSup S = pot - ε := by
        dsimp [ε]
        ring
      _ = (‖x‖ ^ 2 - d ^ 2) / 2 - ε := by
        dsimp [pot, d]
      _ < (‖x‖ ^ 2 - dist x y ^ 2) / 2 := by
        nlinarith
      _ = inner ℝ y x - (‖y‖ ^ 2) / 2 := by
        rw [affineValue_eq_half_norm_sq_sub_sqDist]
  exact (not_lt_of_ge (le_csSup hS_bdd ⟨y, hyC, rfl⟩)) hy_lt

@[simp] theorem euclidean_distance_potential_eq_sSup_affine_apply
    (C : Set E) (hC : C.Nonempty) (x : E) :
    euclidean_distance_potential C x =
      sSup ((fun y : E ↦ inner ℝ y x - (‖y‖ ^ 2) / 2) '' C) := by
  simpa using congrArg (fun f : E → ℝ ↦ f x) (euclidean_distance_potential_eq_sSup_affine C hC)

-- Proof sketch: if `C = ∅`, then `Metric.infDist x C = 0`, so the function is `x ↦ ‖x‖² / 2`,
-- which is convex. Otherwise rewrite with `euclidean_distance_potential_eq_sSup_affine`; each term
-- `x ↦ inner ℝ y x - ‖y‖² / 2` is affine, hence convex, and a pointwise supremum of such affine
-- functions is convex.
/-- Example 2.5: for a subset `C` of a real inner product space, the function
`x ↦ (‖x‖² - d_C(x)²) / 2` is convex. -/
theorem euclidean_distance_potential_convex (C : Set E) :
    ConvexOn ℝ Set.univ (euclidean_distance_potential C) := by
  classical
  by_cases hC : C.Nonempty
  · refine ⟨convex_univ, ?_⟩
    intro x _ z _ a b ha hb hab
    let Sx : Set ℝ := (fun u : E ↦ inner ℝ u x - (‖u‖ ^ 2) / 2) '' C
    let Sz : Set ℝ := (fun u : E ↦ inner ℝ u z - (‖u‖ ^ 2) / 2) '' C
    let Smix : Set ℝ := (fun u : E ↦ inner ℝ u (a • x + b • z) - (‖u‖ ^ 2) / 2) '' C
    have hSx_bdd : BddAbove Sx := by
      refine ⟨euclidean_distance_potential C x, ?_⟩
      intro r hr
      rcases hr with ⟨u, huC, rfl⟩
      exact affineValue_le_potential C x u huC
    have hSz_bdd : BddAbove Sz := by
      refine ⟨euclidean_distance_potential C z, ?_⟩
      intro r hr
      rcases hr with ⟨u, huC, rfl⟩
      exact affineValue_le_potential C z u huC
    have hSmix_nonempty : Smix.Nonempty := by
      rcases hC with ⟨u, huC⟩
      exact ⟨_, ⟨u, huC, rfl⟩⟩
    -- Rewrite all three evaluations by the affine-supremum formula and bound witnesses one by one.
    rw [euclidean_distance_potential_eq_sSup_affine_apply C hC,
      euclidean_distance_potential_eq_sSup_affine_apply C hC,
      euclidean_distance_potential_eq_sSup_affine_apply C hC]
    change sSup Smix ≤ a * sSup Sx + b * sSup Sz
    refine csSup_le hSmix_nonempty ?_
    intro r hr
    rcases hr with ⟨u, huC, rfl⟩
    change inner ℝ u (a • x + b • z) - (‖u‖ ^ 2) / 2 ≤ a * sSup Sx + b * sSup Sz
    rw [affineValue_combo u x z a b hab]
    have hx_le : inner ℝ u x - (‖u‖ ^ 2) / 2 ≤ sSup Sx :=
      le_csSup hSx_bdd ⟨u, huC, rfl⟩
    have hz_le : inner ℝ u z - (‖u‖ ^ 2) / 2 ≤ sSup Sz :=
      le_csSup hSz_bdd ⟨u, huC, rfl⟩
    nlinarith
  · have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    -- The empty-set potential is the half squared norm, whose convexity was isolated above.
    simpa [hEmpty] using (half_norm_sq_convexOn_univ (E := E))

end
