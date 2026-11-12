/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_lemma_5_4.MixedCut
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_2.ch5_sec5_1_2_theorem_5_10

open scoped Matrix

-- Semantic recall note: this item reuses the earlier mixed-cut foundation owner from
-- `ch5_sec5_1_1_lemma_5_4.MixedCut`, together with the Chapter 5 mixed split-hull owner
-- `mixed_split_hull` and the canonical mixed-polyhedron owner `real_mixed_polyhedron`; the
-- matrix presentation remains only as a bridge theorem.

section Lemma54

variable {m nI nC : ℕ}

/-- In the matrix presentation `P = {(x, y) | A x + G y ≤ b}`, the canonical mixed split hull
`mixed_split_hull P π π₀` for `P = real_mixed_polyhedron A G b` unfolds to the two matrix-defined
split branches. -/
theorem mixed_split_hull_real_mixed_polyhedron_def
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (π0 : ℤ) :
    mixed_split_hull (real_mixed_polyhedron A G b) π π0 =
      convexHull ℝ
        ({xy : MixedRealPoint nI nC |
            A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧
              split_dot π xy.1 ≤ (π0 : ℝ)} ∪
          {xy : MixedRealPoint nI nC |
            A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧
              (π0 : ℝ) + 1 ≤ split_dot π xy.1}) := by
  rw [mixed_split_hull]
  congr 1
  ext xy
  simp [split_dot, mem_real_mixed_polyhedron_iff]

/-- Helper for Lemma 5.4: the positive-minus-negative row-multiplier slack equals the scalar
gap `u b - π x` on a mixed point. -/
lemma mixedRowSlackGap_eq_rhsGap
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A = fun i : Fin nI ↦ (π i : ℝ))
    (hG : u ᵥ* G = 0)
    (xy : MixedRealPoint nI nC) :
    (row_multiplier_pos u ⬝ᵥ (b - (A *ᵥ xy.1 + G *ᵥ xy.2))) -
        (row_multiplier_neg u ⬝ᵥ (b - (A *ᵥ xy.1 + G *ᵥ xy.2))) =
      u ⬝ᵥ b - split_dot π xy.1 := by
  have hdecomp : row_multiplier_pos u - row_multiplier_neg u = u := by
    ext i
    by_cases hi : 0 ≤ u i
    · -- On nonnegative coordinates, the positive part is `u i` and the negative part vanishes.
      have hneg : -u i ≤ 0 := by
        linarith
      simp [row_multiplier_pos, row_multiplier_neg, hi, hneg]
    · -- On negative coordinates, the positive part vanishes and the negative part is `-u i`.
      have hi' : u i < 0 := lt_of_not_ge hi
      have hneg : 0 ≤ -u i := by linarith
      simp [row_multiplier_pos, row_multiplier_neg, hi'.le, hneg]
  have hAu : u ⬝ᵥ (A *ᵥ xy.1) = split_dot π xy.1 := by
    -- Rewrite the matrix action `u A` into the split coefficients `π`.
    rw [Matrix.dotProduct_mulVec, hπ, split_dot]
  have hGu : u ⬝ᵥ (G *ᵥ xy.2) = 0 := by
    -- The continuous block contributes nothing because `u A_C = 0`.
    simp [Matrix.dotProduct_mulVec, hG]
  calc
    (row_multiplier_pos u ⬝ᵥ (b - (A *ᵥ xy.1 + G *ᵥ xy.2))) -
        (row_multiplier_neg u ⬝ᵥ (b - (A *ᵥ xy.1 + G *ᵥ xy.2)))
        = (row_multiplier_pos u - row_multiplier_neg u) ⬝ᵥ
            (b - (A *ᵥ xy.1 + G *ᵥ xy.2)) := by
              rw [sub_dotProduct]
    _ = u ⬝ᵥ (b - (A *ᵥ xy.1 + G *ᵥ xy.2)) := by
          rw [hdecomp]
    _ = u ⬝ᵥ b - u ⬝ᵥ (A *ᵥ xy.1 + G *ᵥ xy.2) := by
          rw [dotProduct_sub]
    _ = u ⬝ᵥ b - (u ⬝ᵥ (A *ᵥ xy.1) + u ⬝ᵥ (G *ᵥ xy.2)) := by
          rw [dotProduct_add]
    _ = u ⬝ᵥ b - split_dot π xy.1 := by
          rw [hAu, hGu]
          ring

/-- Helper for Lemma 5.4: the mixed Gomory fractional cut is valid on the lower split branch. -/
lemma mixedGomoryCut_validOnLowerBranch
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A = fun i : Fin nI ↦ (π i : ℝ))
    (hG : u ᵥ* G = 0)
    (hub_nonint : ¬ ∃ z : ℤ, u ⬝ᵥ b = (z : ℝ))
    (xy : MixedRealPoint nI nC)
    (hslack : A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b)
    (hlower : split_dot π xy.1 ≤ Int.floor (u ⬝ᵥ b)) :
    1 ≤ mixed_gomory_fractional_cut_value A G b u xy := by
  let r : Fin m → ℝ := b - (A *ᵥ xy.1 + G *ᵥ xy.2)
  let s1 : ℝ := row_multiplier_pos u ⬝ᵥ r
  let s2 : ℝ := row_multiplier_neg u ⬝ᵥ r
  have hub_not_mem : u ⬝ᵥ b ∉ Set.range (Int.cast : ℤ → ℝ) := by
    simpa [Set.mem_range, eq_comm] using hub_nonint
  have hf_ne : Int.fract (u ⬝ᵥ b) ≠ 0 := by
    exact (Int.fract_ne_zero_iff).2 hub_not_mem
  have hf_pos : 0 < Int.fract (u ⬝ᵥ b) := by
    exact lt_of_le_of_ne' (Int.fract_nonneg _) hf_ne
  have hf_lt_one : Int.fract (u ⬝ᵥ b) < 1 := Int.fract_lt_one _
  have hr_nonneg : 0 ≤ r := by
    intro i
    dsimp [r]
    exact sub_nonneg.mpr (hslack i)
  have hs2_nonneg : 0 ≤ s2 := by
    -- Every term in the negative-part slack sum is nonnegative.
    dsimp [s2]
    exact dotProduct_nonneg_of_nonneg
      (by
        intro i
        simp [row_multiplier_neg])
      hr_nonneg
  have hgap_eq : s1 - s2 = u ⬝ᵥ b - split_dot π xy.1 := by
    simpa [r, s1, s2] using mixedRowSlackGap_eq_rhsGap A G b u π hπ hG xy
  have hgap : Int.fract (u ⬝ᵥ b) ≤ s1 - s2 := by
    -- The lower-branch inequality gives the source-proof gap `ub - πx ≥ fract(ub)`.
    rw [hgap_eq]
    rw [← Int.self_sub_floor (u ⬝ᵥ b)]
    linarith
  -- The generic one-dimensional inequality now closes the branch case.
  simpa [mixed_gomory_fractional_cut_value_eq, r, s1, s2] using
    one_le_fractionalCutExpr_of_lowerGap hf_pos hf_lt_one hs2_nonneg hgap

/-- Helper for Lemma 5.4: the mixed Gomory fractional cut is valid on the upper split branch. -/
lemma mixedGomoryCut_validOnUpperBranch
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A = fun i : Fin nI ↦ (π i : ℝ))
    (hG : u ᵥ* G = 0)
    (hub_nonint : ¬ ∃ z : ℤ, u ⬝ᵥ b = (z : ℝ))
    (xy : MixedRealPoint nI nC)
    (hslack : A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b)
    (hupper : (Int.floor (u ⬝ᵥ b) : ℝ) + 1 ≤ split_dot π xy.1) :
    1 ≤ mixed_gomory_fractional_cut_value A G b u xy := by
  let r : Fin m → ℝ := b - (A *ᵥ xy.1 + G *ᵥ xy.2)
  let s1 : ℝ := row_multiplier_pos u ⬝ᵥ r
  let s2 : ℝ := row_multiplier_neg u ⬝ᵥ r
  have hub_not_mem : u ⬝ᵥ b ∉ Set.range (Int.cast : ℤ → ℝ) := by
    simpa [Set.mem_range, eq_comm] using hub_nonint
  have hf_ne : Int.fract (u ⬝ᵥ b) ≠ 0 := by
    exact (Int.fract_ne_zero_iff).2 hub_not_mem
  have hf_pos : 0 < Int.fract (u ⬝ᵥ b) := by
    exact lt_of_le_of_ne' (Int.fract_nonneg _) hf_ne
  have hf_lt_one : Int.fract (u ⬝ᵥ b) < 1 := Int.fract_lt_one _
  have hr_nonneg : 0 ≤ r := by
    intro i
    dsimp [r]
    exact sub_nonneg.mpr (hslack i)
  have hs1_nonneg : 0 ≤ s1 := by
    -- Every term in the positive-part slack sum is nonnegative.
    dsimp [s1]
    exact dotProduct_nonneg_of_nonneg
      (by
        intro i
        simp [row_multiplier_pos])
      hr_nonneg
  have hgap_eq : s1 - s2 = u ⬝ᵥ b - split_dot π xy.1 := by
    simpa [r, s1, s2] using mixedRowSlackGap_eq_rhsGap A G b u π hπ hG xy
  have hgap : 1 - Int.fract (u ⬝ᵥ b) ≤ s2 - s1 := by
    have hfract :
        1 - Int.fract (u ⬝ᵥ b) = (Int.floor (u ⬝ᵥ b) : ℝ) + 1 - u ⬝ᵥ b := by
      calc
        1 - Int.fract (u ⬝ᵥ b)
            = 1 - (u ⬝ᵥ b - (Int.floor (u ⬝ᵥ b) : ℝ)) := by
                rw [Int.self_sub_floor]
        _ = (Int.floor (u ⬝ᵥ b) : ℝ) + 1 - u ⬝ᵥ b := by ring
    -- The upper-branch inequality gives the symmetric source-proof gap `πx - ub ≥ 1 - fract(ub)`.
    rw [hfract]
    have hgap_eq' : s2 - s1 = split_dot π xy.1 - u ⬝ᵥ b := by
      linarith [hgap_eq]
    rw [hgap_eq']
    linarith
  -- The symmetric one-dimensional inequality closes the upper branch.
  simpa [mixed_gomory_fractional_cut_value_eq, r, s1, s2] using
    one_le_fractionalCutExpr_of_upperGap hf_pos hf_lt_one hs1_nonneg hgap

/-- Helper for Lemma 5.4: the mixed fractional-cut value is affine on convex combinations of
mixed points. -/
lemma mixedGomoryCutValue_convexCombination
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (α β : ℝ)
    (hαβ : α + β = 1)
    (x y : MixedRealPoint nI nC) :
    mixed_gomory_fractional_cut_value A G b u (α • x + β • y) =
      α * mixed_gomory_fractional_cut_value A G b u x +
        β * mixed_gomory_fractional_cut_value A G b u y := by
  have hslack :
      b - (A *ᵥ (α • x.1 + β • y.1) + G *ᵥ (α • x.2 + β • y.2)) =
        α • (b - (A *ᵥ x.1 + G *ᵥ x.2)) + β • (b - (A *ᵥ y.1 + G *ᵥ y.2)) := by
    ext i
    -- The residual vector is affine because the coefficients satisfy `α + β = 1`.
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hβ : β = 1 - α := by
      linarith
    rw [hβ]
    ring
  -- Expand the cut formula and push the affine slack decomposition through the dot products.
  have hcut_combo :
      mixed_gomory_fractional_cut_value A G b u (α • x + β • y) =
        row_multiplier_pos u ⬝ᵥ
            (b - (A *ᵥ (α • x.1 + β • y.1) + G *ᵥ (α • x.2 + β • y.2))) /
          Int.fract (u ⬝ᵥ b) +
          row_multiplier_neg u ⬝ᵥ
            (b - (A *ᵥ (α • x.1 + β • y.1) + G *ᵥ (α • x.2 + β • y.2))) /
            (1 - Int.fract (u ⬝ᵥ b)) := by
    simpa using mixed_gomory_fractional_cut_value_eq A G b u (α • x + β • y)
  rw [hcut_combo, mixed_gomory_fractional_cut_value_eq, mixed_gomory_fractional_cut_value_eq]
  rw [hslack, dotProduct_add, dotProduct_smul, dotProduct_smul]
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
  simp [smul_eq_mul]
  ring

/-- Helper for Lemma 5.4: the mixed Gomory fractional-cut halfspace is convex. -/
lemma mixedGomoryCutHalfspace_convex
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ) :
    Convex ℝ {xy : MixedRealPoint nI nC | 1 ≤ mixed_gomory_fractional_cut_value A G b u xy} := by
  intro x hx y hy α β hα_nonneg hβ_nonneg hαβ
  have hx' : 1 ≤ mixed_gomory_fractional_cut_value A G b u x := by
    simpa using hx
  have hy' : 1 ≤ mixed_gomory_fractional_cut_value A G b u y := by
    simpa using hy
  -- Affinity of the cut value turns convexity into a one-line linear inequality.
  change 1 ≤ mixed_gomory_fractional_cut_value A G b u (α • x + β • y)
  rw [mixedGomoryCutValue_convexCombination A G b u α β hαβ x y]
  nlinarith

/-- Lemma 5.4. In the mixed-space representation `P = { (x, y) | A x + G y ≤ b }`, assume
`π = u A_I` is represented by the integral row `π`, the continuous block is annihilated by
`u A_C = 0`, and `u b ∉ ℤ`. Then the fractional split-cut inequality (5.6) is valid for the split
set `P^(π, π₀)` with `π₀ = ⌊u b⌋`. -/
theorem mixed_gomory_fractional_cut_valid_on_split_hull
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A = fun i : Fin nI ↦ (π i : ℝ))
    (hG : u ᵥ* G = 0)
    (hub_nonint : ¬ ∃ z : ℤ, u ⬝ᵥ b = (z : ℝ))
    (xy : MixedRealPoint nI nC)
    (hxy :
      xy ∈ mixed_split_hull (real_mixed_polyhedron A G b) π (Int.floor (u ⬝ᵥ b))) :
    1 ≤ mixed_gomory_fractional_cut_value A G b u xy := by
  rw [mixed_split_hull_real_mixed_polyhedron_def] at hxy
  let U : Set (MixedRealPoint nI nC) :=
    {xy : MixedRealPoint nI nC |
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ split_dot π xy.1 ≤ (Int.floor (u ⬝ᵥ b) : ℝ)} ∪
      {xy : MixedRealPoint nI nC |
        A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ (Int.floor (u ⬝ᵥ b) : ℝ) + 1 ≤ split_dot π xy.1}
  have hsubset :
      U ⊆ {z : MixedRealPoint nI nC | 1 ≤ mixed_gomory_fractional_cut_value A G b u z} := by
    intro z hz
    rcases hz with hz | hz
    · -- Points on the lower split branch satisfy Lemma 5.4 by the textbook slack-gap argument.
      exact mixedGomoryCut_validOnLowerBranch A G b u π hπ hG hub_nonint z hz.1 hz.2
    · -- The upper split branch is handled by the symmetric slack-gap argument.
      exact mixedGomoryCut_validOnUpperBranch A G b u π hπ hG hub_nonint z hz.1 hz.2
  -- The branchwise validity extends to the whole split hull because the cut halfspace is convex.
  exact convexHull_min hsubset (mixedGomoryCutHalfspace_convex A G b u) hxy

/-- Companion form of Lemma 5.4 using the bundled mixed Gomory multiplier conditions. -/
theorem mixed_gomory_fractional_cut_valid_on_split_hull_of_multiplier
    (A : Matrix (Fin m) (Fin nI) ℝ)
    (G : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A = fun i : Fin nI ↦ (π i : ℝ))
    (hu : IsMixedGomoryFractionalCutMultiplier A G b u)
    (xy : MixedRealPoint nI nC)
    (hxy :
      xy ∈ mixed_split_hull (real_mixed_polyhedron A G b) π (Int.floor (u ⬝ᵥ b))) :
    1 ≤ mixed_gomory_fractional_cut_value A G b u xy :=
  mixed_gomory_fractional_cut_valid_on_split_hull A G b u π hπ hu.2.1 hu.2.2 xy hxy

end Lemma54
