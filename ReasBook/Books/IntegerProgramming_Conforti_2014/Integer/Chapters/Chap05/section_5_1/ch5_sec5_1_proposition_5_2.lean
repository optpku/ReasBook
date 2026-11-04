/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Join
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_proposition_3_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_33
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_lemma_4_45
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped IntegerVectorNotation Matrix Pointwise SplitHullNotation

-- This file reuses the earlier chapter owners `is_polyhedron`, `is_rational_polyhedron`,
-- `recessionCone`, `rational_matrix_polyhedron`, `integerVectors`, `split_branch_lower`,
-- `split_branch_upper`, `split_strip`, `split_hull`, `split_closure`, and `IsMinimalFaceOf`.
-- The local API below keeps only the Proposition 5.2 statements that are not already owned by the
-- earlier Chapter 5 split infrastructure.

section Proposition52

variable {n : ℕ}

/-- Helper for Proposition 5.2: `split_dot π` sends translated rays to the expected affine-linear
expression. -/
lemma split_dot_add_smul
    (π : Fin n → ℤ)
    (x r : Fin n → ℝ)
    (a : ℝ) :
    split_dot π (x + a • r) = split_dot π x + a * split_dot π r := by
  -- Expand the dot product coordinatewise so the translation splits across the finite sum.
  rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
  calc
    ∑ j : Fin n, (π j : ℝ) * (x j + a * r j)
        = ∑ j : Fin n, ((π j : ℝ) * x j + a * ((π j : ℝ) * r j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
    _ = ∑ j : Fin n, (π j : ℝ) * x j + ∑ j : Fin n, a * ((π j : ℝ) * r j) := by
          rw [Finset.sum_add_distrib]
    _ = split_dot π x + a * split_dot π r := by
          rw [← Finset.mul_sum, split_dot_eq_sum, split_dot_eq_sum]

/-- Helper for Proposition 5.2: `split_dot π` is homogeneous under scalar multiplication. -/
lemma split_dot_smul
    (π : Fin n → ℤ)
    (r : Fin n → ℝ)
    (a : ℝ) :
    split_dot π (a • r) = a * split_dot π r := by
  -- This is the translated-ray identity specialized at the origin.
  simpa [split_dot_eq_sum] using split_dot_add_smul π 0 r a

/-- Helper for Proposition 5.2: the linear objective with coefficients `π` is exactly
`split_dot π`. -/
lemma castSplitObjective_dot
    (π : Fin n → ℤ)
    (x : Fin n → ℝ) :
    (fun j ↦ (π j : ℝ)) ⬝ᵥ x = split_dot π x := by
  -- Both sides are the same finite coordinate sum.
  rw [dotProduct, split_dot_eq_sum]

/-- Helper for Proposition 5.2: the negated split objective is `- split_dot π`. -/
lemma negCastSplitObjective_dot
    (π : Fin n → ℤ)
    (x : Fin n → ℝ) :
    (fun j ↦ -((π j : ℝ))) ⬝ᵥ x = - split_dot π x := by
  -- Expand the dot product and pull the pointwise negation through the finite sum.
  rw [dotProduct, split_dot_eq_sum]
  simp

/-- Helper for Proposition 5.2: intersecting a convex polyhedron with the lower split halfspace
preserves convexity. -/
lemma splitBranchLowerConvex
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    Convex ℝ (split_branch_lower P π π0) := by
  have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
  intro x hx y hy a b ha hb hab
  rcases (mem_split_branch_lower_iff.mp hx) with ⟨hxP, hxLower⟩
  rcases (mem_split_branch_lower_iff.mp hy) with ⟨hyP, hyLower⟩
  refine (mem_split_branch_lower_iff).2 ⟨hP_convex hxP hyP ha hb hab, ?_⟩
  -- Rewrite the split functional on the affine combination and combine the branch inequalities.
  have hsplit :
      split_dot π (a • x + b • y) = a * split_dot π x + b * split_dot π y := by
    rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
    calc
      ∑ j : Fin n, (π j : ℝ) * (a * x j + b * y j)
          = ∑ j : Fin n, (a * ((π j : ℝ) * x j) + b * ((π j : ℝ) * y j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = a * ∑ j : Fin n, (π j : ℝ) * x j + b * ∑ j : Fin n, (π j : ℝ) * y j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  calc
    split_dot π (a • x + b • y) = a * split_dot π x + b * split_dot π y := hsplit
    _ ≤ a * (π0 : ℝ) + b * (π0 : ℝ) := by
          gcongr
    _ = (π0 : ℝ) := by
          calc
            a * (π0 : ℝ) + b * (π0 : ℝ) = (a + b) * (π0 : ℝ) := by ring
            _ = (π0 : ℝ) := by rw [hab, one_mul]

/-- Helper for Proposition 5.2: intersecting a convex polyhedron with the upper split halfspace
preserves convexity. -/
lemma splitBranchUpperConvex
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    Convex ℝ (split_branch_upper P π π0) := by
  have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
  intro x hx y hy a b ha hb hab
  rcases (mem_split_branch_upper_iff.mp hx) with ⟨hxP, hxUpper⟩
  rcases (mem_split_branch_upper_iff.mp hy) with ⟨hyP, hyUpper⟩
  refine (mem_split_branch_upper_iff).2 ⟨hP_convex hxP hyP ha hb hab, ?_⟩
  -- Rewrite the split functional on the affine combination and combine the branch inequalities.
  have hsplit :
      split_dot π (a • x + b • y) = a * split_dot π x + b * split_dot π y := by
    rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
    calc
      ∑ j : Fin n, (π j : ℝ) * (a * x j + b * y j)
          = ∑ j : Fin n, (a * ((π j : ℝ) * x j) + b * ((π j : ℝ) * y j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = a * ∑ j : Fin n, (π j : ℝ) * x j + b * ∑ j : Fin n, (π j : ℝ) * y j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  calc
    split_dot π (a • x + b • y) = a * split_dot π x + b * split_dot π y := hsplit
    _ ≥ a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1) := by
          gcongr
    _ = (π0 : ℝ) + 1 := by
          calc
            a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1) = (a + b) * ((π0 : ℝ) + 1) := by ring
            _ = (π0 : ℝ) + 1 := by rw [hab, one_mul]

/-- Helper for Proposition 5.2: if `C` is convex, then adding the recession cone of `P` preserves
convexity. -/
lemma convex_add_recessionCone
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (P : Set (Fin n → ℝ)) :
    Convex ℝ (C + recessionCone P) := by
  intro x hx y hy a b ha hb hab
  rw [Set.mem_add] at hx hy ⊢
  rcases hx with ⟨xC, hxC, rx, hrx, rfl⟩
  rcases hy with ⟨yC, hyC, ry, hry, rfl⟩
  have hsum :
      a • rx + b • ry ∈ recessionCone P := by
    have hax : a • rx ∈ recessionCone P := smul_mem_recessionCone hrx ha
    have hby : b • ry ∈ recessionCone P := smul_mem_recessionCone hry hb
    exact (recessionPointedCone ℝ P).add_mem hax hby
  refine ⟨a • xC + b • yC, hC hxC hyC ha hb hab, a • rx + b • ry, hsum, ?_⟩
  ext i
  simp [Pi.add_apply, Pi.smul_apply]
  ring

/-- Part (1) of Proposition 5.2. Let `P` be a polyhedron and let `(π, π₀)` be a split.
If the two split branches are nonempty and admit decompositions
`Π₁ = conv(V₁) + rec(Π₁)` and `Π₂ = conv(V₂) + rec(Π₂)`, then
`P^(π, π₀) = conv(V₁ ∪ V₂) + rec(P)`. -/
theorem split_hull_eq_convexHull_union_add_recessionCone
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (hπ : π ≠ 0)
    (hPi1_nonempty : (split_branch_lower P π π0).Nonempty)
    (hPi2_nonempty : (split_branch_upper P π π0).Nonempty)
    (V1 V2 : Finset (Fin n → ℝ))
    (hPi1_repr :
      split_branch_lower P π π0 =
        convexHull ℝ (V1 : Set (Fin n → ℝ)) + recessionCone (split_branch_lower P π π0))
    (hPi2_repr :
      split_branch_upper P π π0 =
        convexHull ℝ (V2 : Set (Fin n → ℝ)) + recessionCone (split_branch_upper P π π0)) :
    P^(π, π0) =
      convexHull ℝ ((V1 ∪ V2 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) +
        recessionCone P := by
  classical
  let _ := hπ
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  let L : Set (Fin n → ℝ) := split_branch_lower (polyhedron_le_set A b) π π0
  let U : Set (Fin n → ℝ) := split_branch_upper (polyhedron_le_set A b) π π0
  let C1 : Set (Fin n → ℝ) := convexHull ℝ (V1 : Set (Fin n → ℝ))
  let C2 : Set (Fin n → ℝ) := convexHull ℝ (V2 : Set (Fin n → ℝ))
  let R : Set (Fin n → ℝ) := convexHull ℝ (((V1 ∪ V2 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) +
    recessionCone (polyhedron_le_set A b)
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := by
    rcases hPi1_nonempty with ⟨x, hx⟩
    exact ⟨x, (mem_split_branch_lower_iff.mp hx).1⟩
  have hL_convex : Convex ℝ L := by
    simpa [L] using splitBranchLowerConvex (polyhedron_le_set A b)
      ⟨m, A, b, rfl⟩ π π0
  have hU_convex : Convex ℝ U := by
    simpa [U] using splitBranchUpperConvex (polyhedron_le_set A b)
      ⟨m, A, b, rfl⟩ π π0
  have hC1_subset_L : C1 ⊆ L := by
    refine convexHull_min ?_ hL_convex
    intro v hv
    have hvL :
        v ∈ split_branch_lower (polyhedron_le_set A b) π π0 := by
      rw [hPi1_repr, Set.mem_add]
      exact ⟨v, subset_convexHull ℝ (V1 : Set (Fin n → ℝ)) hv, 0, zero_mem_recessionCone, by simp⟩
    simpa [L] using hvL
  have hC2_subset_U : C2 ⊆ U := by
    refine convexHull_min ?_ hU_convex
    intro v hv
    have hvU :
        v ∈ split_branch_upper (polyhedron_le_set A b) π π0 := by
      rw [hPi2_repr, Set.mem_add]
      exact ⟨v, subset_convexHull ℝ (V2 : Set (Fin n → ℝ)) hv, 0, zero_mem_recessionCone, by simp⟩
    simpa [U] using hvU
  have hC1_nonempty : C1.Nonempty := by
    rcases hPi1_nonempty with ⟨x, hx⟩
    rw [hPi1_repr, Set.mem_add] at hx
    rcases hx with ⟨q, hq, r, hr, hxrfl⟩
    exact ⟨q, hq⟩
  have hC2_nonempty : C2.Nonempty := by
    rcases hPi2_nonempty with ⟨x, hx⟩
    rw [hPi2_repr, Set.mem_add] at hx
    rcases hx with ⟨q, hq, r, hr, hxrfl⟩
    exact ⟨q, hq⟩
  have hV1_union : (V1 : Set (Fin n → ℝ)) ⊆
      (((V1 ∪ V2 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl hv)
  have hV2_union : (V2 : Set (Fin n → ℝ)) ⊆
      (((V1 ∪ V2 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inr hv)
  have hC1_convex : Convex ℝ C1 := convex_convexHull ℝ _
  have hC2_convex : Convex ℝ C2 := convex_convexHull ℝ _
  have hR_convex : Convex ℝ R := by
    simpa [R] using
      convex_add_recessionCone
        (convexHull ℝ (((V1 ∪ V2 : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))))
        (convex_convexHull ℝ _)
        (polyhedron_le_set A b)
  have hrecLower_mem :
      ∀ {r : Fin n → ℝ}, r ∈ recessionCone L → r ∈ recessionCone (polyhedron_le_set A b) := by
    intro r hr
    rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
    change A *ᵥ r ≤ 0
    rcases hPi1_nonempty with ⟨x0, hx0⟩
    have hx0P : x0 ∈ polyhedron_le_set A b := (mem_split_branch_lower_iff.mp hx0).1
    rw [mem_recessionCone_iff] at hr
    intro i
    by_contra hnot
    have hpos : 0 < (A *ᵥ r) i := lt_of_not_ge hnot
    let a : ℝ := (b i - (A *ᵥ x0) i + 1) / (A *ᵥ r) i
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      have hx0_le : (A *ᵥ x0) i ≤ b i := hx0P i
      refine div_nonneg ?_ hpos.le
      linarith
    have hxa : x0 + a • r ∈ L := hr hx0 a ha_nonneg
    have hrow : (A *ᵥ x0) i + a * (A *ᵥ r) i ≤ b i := by
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using
        (mem_split_branch_lower_iff.mp hxa).1 i
    have ha_mul : a * (A *ᵥ r) i = b i - (A *ᵥ x0) i + 1 := by
      dsimp [a]
      field_simp [hpos.ne']
    linarith
  have hrecUpper_mem :
      ∀ {r : Fin n → ℝ}, r ∈ recessionCone U → r ∈ recessionCone (polyhedron_le_set A b) := by
    intro r hr
    rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
    change A *ᵥ r ≤ 0
    rcases hPi2_nonempty with ⟨x0, hx0⟩
    have hx0P : x0 ∈ polyhedron_le_set A b := (mem_split_branch_upper_iff.mp hx0).1
    rw [mem_recessionCone_iff] at hr
    intro i
    by_contra hnot
    have hpos : 0 < (A *ᵥ r) i := lt_of_not_ge hnot
    let a : ℝ := (b i - (A *ᵥ x0) i + 1) / (A *ᵥ r) i
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      have hx0_le : (A *ᵥ x0) i ≤ b i := hx0P i
      refine div_nonneg ?_ hpos.le
      linarith
    have hxa : x0 + a • r ∈ U := hr hx0 a ha_nonneg
    have hrow : (A *ᵥ x0) i + a * (A *ᵥ r) i ≤ b i := by
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using
        (mem_split_branch_upper_iff.mp hxa).1 i
    have ha_mul : a * (A *ᵥ r) i = b i - (A *ᵥ x0) i + 1 := by
      dsimp [a]
      field_simp [hpos.ne']
    linarith
  refine subset_antisymm ?_ ?_
  · -- First place each split branch inside the target `conv(V₁ ∪ V₂) + rec(P)` and then lift
    -- that inclusion to the split hull by convexity.
    refine convexHull_min ?_ hR_convex
    intro x hx
    rcases hx with hx | hx
    · rw [hPi1_repr, Set.mem_add] at hx
      rcases hx with ⟨q, hq, r, hr, rfl⟩
      rw [Set.mem_add]
      exact ⟨q, convexHull_mono hV1_union hq, r, hrecLower_mem hr, rfl⟩
    · rw [hPi2_repr, Set.mem_add] at hx
      rcases hx with ⟨q, hq, r, hr, rfl⟩
      rw [Set.mem_add]
      exact ⟨q, convexHull_mono hV2_union hq, r, hrecUpper_mem hr, rfl⟩
  · -- Route correction: rather than unfold the whole split hull directly, decompose the finite
    -- convex part into a lower-upper segment and absorb the recession vector according to the sign
    -- of `split_dot π r`.
    intro x hx
    rw [Set.mem_add] at hx
    rcases hx with ⟨q, hq, r, hr, rfl⟩
    have hq_join :
        q ∈ convexJoin ℝ C1 C2 := by
      have hq' : q ∈ convexHull ℝ (C1 ∪ C2) := by
        simpa [C1, C2,
          convexHull_convexHull_union_left, convexHull_convexHull_union_right] using hq
      rw [hC1_convex.convexHull_union hC2_convex hC1_nonempty hC2_nonempty] at hq'
      exact hq'
    rcases mem_convexJoin.mp hq_join with ⟨q1, hq1, q2, hq2, hseg⟩
    have hq1L : q1 ∈ L := hC1_subset_L hq1
    have hq2U : q2 ∈ U := hC2_subset_U hq2
    have hq1P : q1 ∈ polyhedron_le_set A b := (mem_split_branch_lower_iff.mp hq1L).1
    have hq2P : q2 ∈ polyhedron_le_set A b := (mem_split_branch_upper_iff.mp hq2U).1
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    have hconvHull :
        Convex ℝ (convexHull ℝ (L ∪ U)) := convex_convexHull ℝ _
    by_cases hs_zero : split_dot π r = 0
    · -- When the split value of the recession direction vanishes, both branches are translation
      -- invariant along `r`, so the whole segment stays inside the split hull.
      have hq1rL : q1 + r ∈ L := by
        have hq1rP : q1 + r ∈ polyhedron_le_set A b := by
          simpa using (mem_recessionCone_iff.mp hr) hq1P 1 zero_le_one
        refine (mem_split_branch_lower_iff).2 ⟨hq1rP, ?_⟩
        rw [show q1 + r = q1 + (1 : ℝ) • r by simp, split_dot_add_smul, hs_zero]
        simpa using (mem_split_branch_lower_iff.mp hq1L).2
      have hq2rU : q2 + r ∈ U := by
        have hq2rP : q2 + r ∈ polyhedron_le_set A b := by
          simpa using (mem_recessionCone_iff.mp hr) hq2P 1 zero_le_one
        refine (mem_split_branch_upper_iff).2 ⟨hq2rP, ?_⟩
        rw [show q2 + r = q2 + (1 : ℝ) • r by simp, split_dot_add_smul, hs_zero]
        simpa using (mem_split_branch_upper_iff.mp hq2U).2
      have hline :
          AffineMap.lineMap (q1 + r) (q2 + r) t =
            AffineMap.lineMap q1 q2 t + r := by
        ext i
        simp [AffineMap.lineMap_apply_module]
        ring
      rw [split_hull]
      rw [← hline]
      have h1 : q1 + r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1rL)
      have h2 : q2 + r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2rU)
      simpa [AffineMap.lineMap_apply_module] using
        hconvHull h1 h2 (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    · by_cases hs_neg : split_dot π r < 0
      · by_cases ht_one : t = 1
        · -- If the finite part lies entirely on the upper side, push it far enough along `r`
          -- until it reaches the lower branch and then recover `q2 + r` as a segment point.
          have hq_eq : AffineMap.lineMap q1 q2 t = q2 := by simp [ht_one]
          let β : ℝ := (split_dot π q2 - (π0 : ℝ)) / (-split_dot π r) + 1
          have hβ_ge_one : 1 ≤ β := by
            dsimp [β]
            have hnum_nonneg : 0 ≤ split_dot π q2 - (π0 : ℝ) := by
              have hupper := (mem_split_branch_upper_iff.mp hq2U).2
              linarith
            have hden_pos : 0 < -split_dot π r := by linarith
            have hfrac_nonneg :
                0 ≤ (split_dot π q2 - (π0 : ℝ)) / (-split_dot π r) := by
              exact div_nonneg hnum_nonneg hden_pos.le
            linarith
          have hβ_nonneg : 0 ≤ β := by linarith
          have hβ_ne : β ≠ 0 := by linarith [hβ_ge_one]
          have hq2βL : q2 + β • r ∈ L := by
            refine (mem_split_branch_lower_iff).2
              ⟨(mem_recessionCone_iff.mp hr) hq2P β hβ_nonneg, ?_⟩
            have hcalc :
                split_dot π q2 + β * split_dot π r = (π0 : ℝ) + split_dot π r := by
              dsimp [β]
              field_simp [hs_zero]
              ring
            rw [split_dot_add_smul, hcalc]
            linarith
          have hparam : 1 - 1 / β ∈ Set.Icc (0 : ℝ) 1 := by
            constructor
            · have hdiv_le : 1 / β ≤ 1 := by
                field_simp [hβ_ne]
                nlinarith [hβ_ge_one]
              linarith
            · have hdiv_nonneg : 0 ≤ 1 / β := by positivity
              linarith
          have hline :
              AffineMap.lineMap (q2 + β • r) q2 (1 - 1 / β) = q2 + r := by
            ext i
            simp [AffineMap.lineMap_apply_module]
            field_simp [hβ_ne]
            ring
          rw [split_hull, hq_eq, ← hline]
          have h1 : q2 + β • r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq2βL)
          have h2 : q2 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2U)
          have hbetaInv_nonneg : 0 ≤ 1 / β := by
            positivity
          simpa [AffineMap.lineMap_apply_module] using
            hconvHull h1 h2 hbetaInv_nonneg hparam.1 (by linarith)
        · -- Otherwise the lower coefficient is positive, so one translated lower point absorbs
          -- the whole recession direction.
          have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 ht_one
          let α : ℝ := 1 / (1 - t)
          have hα_nonneg : 0 ≤ α := by
            dsimp [α]
            positivity
          have hα_ne : α ≠ 0 := by
            dsimp [α]
            positivity
          have hq1αL : q1 + α • r ∈ L := by
            refine (mem_split_branch_lower_iff).2
              ⟨(mem_recessionCone_iff.mp hr) hq1P α hα_nonneg, ?_⟩
            rw [split_dot_add_smul]
            have hlower := (mem_split_branch_lower_iff.mp hq1L).2
            have hmul_nonpos : α * split_dot π r ≤ 0 := by
              have hs_le : split_dot π r ≤ 0 := le_of_lt hs_neg
              exact mul_nonpos_of_nonneg_of_nonpos hα_nonneg hs_le
            linarith
          have hline :
              AffineMap.lineMap (q1 + α • r) q2 t =
                AffineMap.lineMap q1 q2 t + r := by
            ext i
            simp [AffineMap.lineMap_apply_module, α]
            field_simp [sub_ne_zero.mpr (ne_of_gt ht_lt_one)]
            ring
          rw [split_hull, ← hline]
          have h1 : q1 + α • r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1αL)
          have h2 : q2 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2U)
          simpa [AffineMap.lineMap_apply_module] using
            hconvHull h1 h2 (sub_nonneg.mpr ht.2) ht.1 (by linarith)
      · have hs_pos : 0 < split_dot π r := by
          have hs_le : 0 ≤ split_dot π r := le_of_not_gt hs_neg
          have hs_zero' : (0 : ℝ) ≠ split_dot π r := by
            intro hs_eq
            apply hs_zero
            simpa using hs_eq.symm
          exact lt_of_le_of_ne hs_le hs_zero'
        by_cases ht_zero : t = 0
        · -- If the finite part lies entirely on the lower side, push it far enough along `r`
          -- until it reaches the upper branch and then recover `q1 + r` as a segment point.
          have hq_eq : AffineMap.lineMap q1 q2 t = q1 := by simp [ht_zero]
          let β : ℝ := (((π0 : ℝ) + 1) - split_dot π q1) / split_dot π r + 1
          have hβ_ge_one : 1 ≤ β := by
            dsimp [β]
            have hnum_nonneg : 0 ≤ ((π0 : ℝ) + 1) - split_dot π q1 := by
              have hlower := (mem_split_branch_lower_iff.mp hq1L).2
              linarith
            have hfrac_nonneg : 0 ≤ (((π0 : ℝ) + 1) - split_dot π q1) / split_dot π r := by
              exact div_nonneg hnum_nonneg hs_pos.le
            linarith
          have hβ_nonneg : 0 ≤ β := by linarith
          have hβ_ne : β ≠ 0 := by linarith [hβ_ge_one]
          have hq1βU : q1 + β • r ∈ U := by
            refine (mem_split_branch_upper_iff).2
              ⟨(mem_recessionCone_iff.mp hr) hq1P β hβ_nonneg, ?_⟩
            have hcalc :
                split_dot π q1 + β * split_dot π r = (π0 : ℝ) + 1 + split_dot π r := by
              dsimp [β]
              field_simp [hs_zero]
              ring
            rw [split_dot_add_smul, hcalc]
            linarith
          have hparam : (1 / β : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
            constructor
            · positivity
            · field_simp [hβ_ne]
              nlinarith [hβ_ge_one]
          have hline :
              AffineMap.lineMap q1 (q1 + β • r) (1 / β) = q1 + r := by
            ext i
            simp [AffineMap.lineMap_apply_module]
            field_simp [hβ_ne]
            ring
          rw [split_hull, hq_eq, ← hline]
          have h1 : q1 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1L)
          have h2 : q1 + β • r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq1βU)
          simpa [AffineMap.lineMap_apply_module] using
            hconvHull h1 h2 (sub_nonneg.mpr hparam.2) hparam.1 (by linarith)
        · -- Otherwise the upper coefficient is positive, so one translated upper point absorbs
          -- the whole recession direction.
          have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (by simpa [eq_comm] using ht_zero)
          let α : ℝ := 1 / t
          have hα_nonneg : 0 ≤ α := by
            dsimp [α]
            positivity
          have hq2αU : q2 + α • r ∈ U := by
            refine (mem_split_branch_upper_iff).2
              ⟨(mem_recessionCone_iff.mp hr) hq2P α hα_nonneg, ?_⟩
            rw [split_dot_add_smul]
            have hupper := (mem_split_branch_upper_iff.mp hq2U).2
            have hmul_nonneg : 0 ≤ α * split_dot π r := by
              exact mul_nonneg hα_nonneg hs_pos.le
            linarith
          have hline :
              AffineMap.lineMap q1 (q2 + α • r) t =
                AffineMap.lineMap q1 q2 t + r := by
            ext i
            simp [AffineMap.lineMap_apply_module, α]
            field_simp [ne_of_gt ht_pos]
            ring
          rw [split_hull, ← hline]
          have h1 : q1 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1L)
          have h2 : q2 + α • r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2αU)
          simpa [AffineMap.lineMap_apply_module] using
            hconvHull h1 h2 (sub_nonneg.mpr ht.2) ht.1 (by linarith)

/-- Every split hull of a polyhedron is contained in the original polyhedron. -/
theorem split_hull_subset
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    P^(π, π0) ⊆ P := by
  have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
  refine convexHull_min ?_ hP_convex
  intro x hx
  rcases hx with hx | hx
  · exact (mem_split_branch_lower_iff.mp hx).1
  · exact (mem_split_branch_upper_iff.mp hx).1

/-- Helper for Proposition 5.2: the split hull of a polyhedron is again a polyhedron. -/
lemma split_hull_is_polyhedron
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    is_polyhedron (P^(π, π0)) := by
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  -- Rewrite the two split branches into Lemma 4.45's left/right polyhedra.
  simpa [split_hull, split_branch_lower, split_branch_upper, split_dot] using
    convexHull_split_polyhedra_is_polyhedron
      A b (fun j : Fin n ↦ (π j : ℝ)) (π0 : ℝ) ((π0 : ℝ) + 1)

/-- Helper for Proposition 5.2: if both split branches are nonempty, then every recession
direction of `P` is also a recession direction of the split hull. -/
lemma mem_recessionCone_split_hull_of_branches_nonempty
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (hPi1_nonempty : (split_branch_lower P π π0).Nonempty)
    (hPi2_nonempty : (split_branch_upper P π π0).Nonempty)
    {r : Fin n → ℝ}
    (hr : r ∈ recessionCone P) :
    r ∈ recessionCone (P^(π, π0)) := by
  let L : Set (Fin n → ℝ) := split_branch_lower P π π0
  let U : Set (Fin n → ℝ) := split_branch_upper P π π0
  have hL_convex : Convex ℝ L := by
    simpa [L] using splitBranchLowerConvex P hP_polyhedron π π0
  have hU_convex : Convex ℝ U := by
    simpa [U] using splitBranchUpperConvex P hP_polyhedron π π0
  rw [mem_recessionCone_iff]
  intro x hxHull a ha
  have hs : a • r ∈ recessionCone P := smul_mem_recessionCone hr ha
  have hx_join : x ∈ convexJoin ℝ L U := by
    have hx_union : x ∈ convexHull ℝ (L ∪ U) := by
      simpa [split_hull, L, U] using hxHull
    rw [hL_convex.convexHull_union hU_convex hPi1_nonempty hPi2_nonempty] at hx_union
    exact hx_union
  rcases mem_convexJoin.mp hx_join with ⟨q1, hq1, q2, hq2, hseg⟩
  have hq1P : q1 ∈ P := (mem_split_branch_lower_iff.mp hq1).1
  have hq2P : q2 ∈ P := (mem_split_branch_upper_iff.mp hq2).1
  rw [segment_eq_image_lineMap] at hseg
  rcases hseg with ⟨t, ht, rfl⟩
  have hconvHull :
      Convex ℝ (convexHull ℝ (L ∪ U)) := convex_convexHull ℝ _
  by_cases hs_zero : split_dot π (a • r) = 0
  · -- When the split functional is constant along the recession step, both branches remain stable.
    have hq1sL : q1 + a • r ∈ L := by
      have hq1sP : q1 + a • r ∈ P := (mem_recessionCone_iff.mp hr) hq1P a ha
      refine (mem_split_branch_lower_iff).2 ⟨hq1sP, ?_⟩
      have hs_zero' : a * split_dot π r = 0 := by
        simpa [split_dot_smul] using hs_zero
      rw [split_dot_add_smul, hs_zero']
      simpa using (mem_split_branch_lower_iff.mp hq1).2
    have hq2sU : q2 + a • r ∈ U := by
      have hq2sP : q2 + a • r ∈ P := (mem_recessionCone_iff.mp hr) hq2P a ha
      refine (mem_split_branch_upper_iff).2 ⟨hq2sP, ?_⟩
      have hs_zero' : a * split_dot π r = 0 := by
        simpa [split_dot_smul] using hs_zero
      rw [split_dot_add_smul, hs_zero']
      simpa using (mem_split_branch_upper_iff.mp hq2).2
    have hline :
        AffineMap.lineMap (q1 + a • r) (q2 + a • r) t =
          AffineMap.lineMap q1 q2 t + a • r := by
      ext i
      simp [AffineMap.lineMap_apply_module]
      ring
    rw [split_hull, ← hline]
    have h1 : q1 + a • r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1sL)
    have h2 : q2 + a • r ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2sU)
    simpa [AffineMap.lineMap_apply_module] using
      hconvHull h1 h2 (sub_nonneg.mpr ht.2) ht.1 (by linarith)
  · by_cases hs_neg : split_dot π (a • r) < 0
    · by_cases ht_one : t = 1
      · -- If the convex combination is already on the upper branch, move it far enough to hit the
        -- lower branch and recover the translated point on the resulting segment.
        have hq_eq : AffineMap.lineMap q1 q2 t = q2 := by simp [ht_one]
        let β : ℝ := (split_dot π q2 - (π0 : ℝ)) / (-split_dot π (a • r)) + 1
        have hβ_ge_one : 1 ≤ β := by
          dsimp [β]
          have hnum_nonneg : 0 ≤ split_dot π q2 - (π0 : ℝ) := by
            have hupper := (mem_split_branch_upper_iff.mp hq2).2
            linarith
          have hden_pos : 0 < -split_dot π (a • r) := by linarith
          have hfrac_nonneg :
              0 ≤ (split_dot π q2 - (π0 : ℝ)) / (-split_dot π (a • r)) := by
            exact div_nonneg hnum_nonneg hden_pos.le
          linarith
        have hβ_nonneg : 0 ≤ β := by linarith
        have hβ_ne : β ≠ 0 := by linarith [hβ_ge_one]
        have hq2βL : q2 + β • (a • r) ∈ L := by
          refine (mem_split_branch_lower_iff).2
            ⟨(mem_recessionCone_iff.mp hs) hq2P β hβ_nonneg, ?_⟩
          have hcalc :
              split_dot π q2 + β * split_dot π (a • r) = (π0 : ℝ) + split_dot π (a • r) := by
            dsimp [β]
            field_simp [hs_zero]
            ring
          rw [show q2 + β • (a • r) = q2 + β • (a • r) by rfl, split_dot_add_smul, hcalc]
          linarith
        have hparam : 1 - 1 / β ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · have hdiv_le : 1 / β ≤ 1 := by
              field_simp [hβ_ne]
              nlinarith [hβ_ge_one]
            linarith
          · have hdiv_nonneg : 0 ≤ 1 / β := by positivity
            linarith
        have hline :
            AffineMap.lineMap (q2 + β • (a • r)) q2 (1 - 1 / β) = q2 + a • r := by
          ext i
          simp [AffineMap.lineMap_apply_module]
          field_simp [hβ_ne]
          ring
        rw [split_hull, hq_eq, ← hline]
        have h1 : q2 + β • (a • r) ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq2βL)
        have h2 : q2 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2)
        have hbetaInv_nonneg : 0 ≤ 1 / β := by positivity
        simpa [AffineMap.lineMap_apply_module] using
          hconvHull h1 h2 hbetaInv_nonneg hparam.1 (by linarith)
      · -- Otherwise the lower coefficient is positive, so one translated lower point absorbs the
        -- whole recession step.
        have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 ht_one
        let α : ℝ := 1 / (1 - t)
        have hα_nonneg : 0 ≤ α := by
          dsimp [α]
          positivity
        have hq1αL : q1 + α • (a • r) ∈ L := by
          refine (mem_split_branch_lower_iff).2
            ⟨(mem_recessionCone_iff.mp hs) hq1P α hα_nonneg, ?_⟩
          rw [split_dot_add_smul]
          have hlower := (mem_split_branch_lower_iff.mp hq1).2
          have hmul_nonpos : α * split_dot π (a • r) ≤ 0 := by
            have hs_le : split_dot π (a • r) ≤ 0 := le_of_lt hs_neg
            exact mul_nonpos_of_nonneg_of_nonpos hα_nonneg hs_le
          linarith
        have hline :
            AffineMap.lineMap (q1 + α • (a • r)) q2 t =
              AffineMap.lineMap q1 q2 t + a • r := by
          ext i
          simp [AffineMap.lineMap_apply_module, α]
          field_simp [sub_ne_zero.mpr (ne_of_gt ht_lt_one)]
          ring
        rw [split_hull, ← hline]
        have h1 : q1 + α • (a • r) ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1αL)
        have h2 : q2 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2)
        simpa [AffineMap.lineMap_apply_module] using
          hconvHull h1 h2 (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    · have hs_pos : 0 < split_dot π (a • r) := by
        have hs_le : 0 ≤ split_dot π (a • r) := le_of_not_gt hs_neg
        have hs_zero' : (0 : ℝ) ≠ split_dot π (a • r) := by
          intro hs_eq
          apply hs_zero
          simpa using hs_eq.symm
        exact lt_of_le_of_ne hs_le hs_zero'
      by_cases ht_zero : t = 0
      · -- If the convex combination is already on the lower branch, move it far enough to hit the
        -- upper branch and recover the translated point on the resulting segment.
        have hq_eq : AffineMap.lineMap q1 q2 t = q1 := by simp [ht_zero]
        let β : ℝ := (((π0 : ℝ) + 1) - split_dot π q1) / split_dot π (a • r) + 1
        have hβ_ge_one : 1 ≤ β := by
          dsimp [β]
          have hnum_nonneg : 0 ≤ ((π0 : ℝ) + 1) - split_dot π q1 := by
            have hlower := (mem_split_branch_lower_iff.mp hq1).2
            linarith
          have hfrac_nonneg :
              0 ≤ (((π0 : ℝ) + 1) - split_dot π q1) / split_dot π (a • r) := by
            exact div_nonneg hnum_nonneg hs_pos.le
          linarith
        have hβ_nonneg : 0 ≤ β := by linarith
        have hβ_ne : β ≠ 0 := by linarith [hβ_ge_one]
        have hq1βU : q1 + β • (a • r) ∈ U := by
          refine (mem_split_branch_upper_iff).2
            ⟨(mem_recessionCone_iff.mp hs) hq1P β hβ_nonneg, ?_⟩
          have hcalc :
              split_dot π q1 + β * split_dot π (a • r) = (π0 : ℝ) + 1 + split_dot π (a • r) := by
            dsimp [β]
            field_simp [hs_zero]
            ring
          rw [split_dot_add_smul, hcalc]
          linarith
        have hparam : (1 / β : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · positivity
          · field_simp [hβ_ne]
            nlinarith [hβ_ge_one]
        have hline :
            AffineMap.lineMap q1 (q1 + β • (a • r)) (1 / β) = q1 + a • r := by
          ext i
          simp [AffineMap.lineMap_apply_module]
          field_simp [hβ_ne]
          ring
        rw [split_hull, hq_eq, ← hline]
        have h1 : q1 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1)
        have h2 : q1 + β • (a • r) ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq1βU)
        simpa [AffineMap.lineMap_apply_module] using
          hconvHull h1 h2 (sub_nonneg.mpr hparam.2) hparam.1 (by linarith)
      · -- Otherwise the upper coefficient is positive, so one translated upper point absorbs the
        -- whole recession step.
        have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (by simpa [eq_comm] using ht_zero)
        let α : ℝ := 1 / t
        have hα_nonneg : 0 ≤ α := by
          dsimp [α]
          positivity
        have hq2αU : q2 + α • (a • r) ∈ U := by
          refine (mem_split_branch_upper_iff).2
            ⟨(mem_recessionCone_iff.mp hs) hq2P α hα_nonneg, ?_⟩
          rw [split_dot_add_smul]
          have hupper := (mem_split_branch_upper_iff.mp hq2).2
          have hmul_nonneg : 0 ≤ α * split_dot π (a • r) := by
            exact mul_nonneg hα_nonneg hs_pos.le
          linarith
        have hline :
            AffineMap.lineMap q1 (q2 + α • (a • r)) t =
              AffineMap.lineMap q1 q2 t + a • r := by
          ext i
          simp [AffineMap.lineMap_apply_module, α]
          field_simp [ne_of_gt ht_pos]
          ring
        rw [split_hull, ← hline]
        have h1 : q1 ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inl hq1)
        have h2 : q2 + α • (a • r) ∈ convexHull ℝ (L ∪ U) := subset_convexHull ℝ _ (Or.inr hq2αU)
        simpa [AffineMap.lineMap_apply_module] using
          hconvHull h1 h2 (sub_nonneg.mpr ht.2) ht.1 (by linarith)

/-- Helper for Proposition 5.2: every valid inequality has nonpositive slope on recession
directions of a nonempty feasible region. -/
lemma validIneq_nonpositive_on_recessionCone
    {Q : Set (Fin n → ℝ)}
    {c r : Fin n → ℝ}
    {δ : ℝ}
    (hQ_nonempty : Q.Nonempty)
    (hvalid : is_valid_inequality Q c δ)
    (hr : r ∈ recessionCone Q) :
    c ⬝ᵥ r ≤ 0 := by
  obtain ⟨x0, hx0Q⟩ := hQ_nonempty
  rw [mem_recessionCone_iff] at hr
  -- If the recession slope were positive, a long enough recession step would violate validity.
  by_contra hnot
  have hslope_pos : 0 < c ⬝ᵥ r := lt_of_not_ge hnot
  let a : ℝ := (δ - c ⬝ᵥ x0 + 1) / (c ⬝ᵥ r)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    have hx0_valid : c ⬝ᵥ x0 ≤ δ := hvalid hx0Q
    refine div_nonneg ?_ hslope_pos.le
    linarith
  have hxa : x0 + a • r ∈ Q := hr hx0Q a ha_nonneg
  have hvalid_a : c ⬝ᵥ (x0 + a • r) ≤ δ := hvalid hxa
  have hdot :
      c ⬝ᵥ (x0 + a • r) = c ⬝ᵥ x0 + a * (c ⬝ᵥ r) := by
    simp [dotProduct_add, dotProduct_smul]
  have ha_mul : a * (c ⬝ᵥ r) = δ - c ⬝ᵥ x0 + 1 := by
    dsimp [a]
    field_simp [hslope_pos.ne']
  rw [hdot, ha_mul] at hvalid_a
  linarith

/-- Helper for Proposition 5.2: a lattice point has an integral split value. -/
lemma split_dot_integral_of_mem_integerVectors
    (π : Fin n → ℤ)
    {x : Fin n → ℝ}
    (hx : x ∈ ℤ^n) :
    ∃ k : ℤ, split_dot π x = (k : ℝ) := by
  -- Unpack the integer-vector witness and rewrite the split dot product as an integer sum.
  rcases mem_integerVectors_iff.mp hx with ⟨z, rfl⟩
  refine ⟨∑ j : Fin n, π j * z j, ?_⟩
  rw [split_dot_eq_sum]
  simp [Int.cast_sum, Int.cast_mul]

/-- Helper for Proposition 5.2: no lattice point can lie in the open split strip
`π₀ < π x < π₀ + 1`. -/
lemma not_mem_integerVectors_of_mem_split_strip
    (π : Fin n → ℤ)
    (π0 : ℤ)
    {x : Fin n → ℝ}
    (hx_strip : x ∈ split_strip π π0) :
    x ∉ ℤ^n := by
  intro hx_int
  rcases split_dot_integral_of_mem_integerVectors π hx_int with ⟨k, hk⟩
  rcases mem_split_strip_iff.mp hx_strip with ⟨hleft, hright⟩
  rw [hk] at hleft hright
  have hleft_int : π0 < k := by
    exact_mod_cast hleft
  have hright_int : k < π0 + 1 := by
    exact_mod_cast hright
  omega

/-- Helper for Proposition 5.2: a set contained in the split strip is disjoint from `ℤ^n`. -/
lemma disjoint_integerVectors_of_subset_split_strip
    {F : Set (Fin n → ℝ)}
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (hF_strip : F ⊆ split_strip π π0) :
    Disjoint F (ℤ^n) := by
  -- Reduce disjointness to the pointwise strip-vs-integrality contradiction.
  rw [Set.disjoint_left]
  intro x hxF hx_int
  exact not_mem_integerVectors_of_mem_split_strip π π0 (hF_strip hxF) hx_int

/-- Helper for Proposition 5.2: a subset of `P` disjoint from the split hull must lie in the open
split strip, because every point on either split branch already belongs to the split hull. -/
lemma subset_split_strip_of_subset_polyhedron_of_disjoint_splitHull
    {P E : Set (Fin n → ℝ)}
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (hEP : E ⊆ P)
    (hdisj : Disjoint E (P^(π, π0))) :
    E ⊆ split_strip π π0 := by
  intro x hxE
  have hxP : x ∈ P := hEP hxE
  have hx_not_splitHull : x ∉ P^(π, π0) := by
    intro hxHull
    exact Set.disjoint_left.mp hdisj hxE hxHull
  rw [mem_split_strip_iff]
  constructor
  · -- Otherwise `x` lies in the lower branch, hence already in the split hull.
    by_contra hx_not_left
    have hxLower : x ∈ split_branch_lower P π π0 := by
      exact (mem_split_branch_lower_iff).2 ⟨hxP, le_of_not_gt hx_not_left⟩
    apply hx_not_splitHull
    rw [split_hull]
    exact subset_convexHull ℝ _ (Or.inl hxLower)
  · -- Likewise, failing the upper-strip inequality would place `x` in the upper branch.
    by_contra hx_not_right
    have hxUpperBound : (π0 : ℝ) + 1 ≤ split_dot π x := by
      linarith
    have hxUpper : x ∈ split_branch_upper P π π0 := by
      exact (mem_split_branch_upper_iff).2 ⟨hxP, hxUpperBound⟩
    apply hx_not_splitHull
    rw [split_hull]
    exact subset_convexHull ℝ _ (Or.inr hxUpper)

/-- Helper for Proposition 5.2: a point of `P` that is not in the split hull lies in the open
split strip. -/
lemma mem_split_strip_of_mem_polyhedron_not_mem_splitHull
    {P : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x : Fin n → ℝ}
    (hxP : x ∈ P)
    (hx_not_splitHull : x ∉ P^(π, π0)) :
    x ∈ split_strip π π0 := by
  -- Apply the disjointness-to-strip bridge to the singleton witness set `{x}`.
  have hsubset : ({x} : Set (Fin n → ℝ)) ⊆ P := by
    intro y hy
    simpa using hy ▸ hxP
  have hdisj : Disjoint ({x} : Set (Fin n → ℝ)) (P^(π, π0)) := by
    rw [Set.disjoint_singleton_left]
    exact hx_not_splitHull
  have hxStrip :=
    subset_split_strip_of_subset_polyhedron_of_disjoint_splitHull π π0 hsubset hdisj
  simpa using hxStrip (by simp)

/-- Helper for Proposition 5.2: a witness `x ∈ P \ P^(π, π₀)` produces one nonempty exposed face
of `P` contained in the open split strip. -/
lemma exists_nonempty_exposedFace_subset_split_strip_of_mem_not_mem_splitHull
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (_hπ : π ≠ 0)
    {x : Fin n → ℝ}
    (hxP : x ∈ P)
    (hx_not_splitHull : x ∉ P^(π, π0)) :
    ∃ E : Set (Fin n → ℝ), E.Nonempty ∧ IsExposed ℝ P E ∧ E ⊆ split_strip π π0 := by
  classical
  rcases hP_polyhedron with ⟨m, A, b, rfl⟩
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x, hxP⟩
  have hx_strip : x ∈ split_strip π π0 := by
    -- The witness already lies strictly between the two split hyperplanes.
    exact mem_split_strip_of_mem_polyhedron_not_mem_splitHull hxP hx_not_splitHull
  let L : Set (Fin n → ℝ) := split_branch_lower (polyhedron_le_set A b) π π0
  let U : Set (Fin n → ℝ) := split_branch_upper (polyhedron_le_set A b) π π0
  by_cases hL_empty : L = ∅
  · let c : Fin n → ℝ := fun j ↦ -((π j : ℝ))
    have hvalid : is_valid_inequality (polyhedron_le_set A b) c (-(π0 : ℝ)) := by
      intro y hyP
      have hy_not_lower : ¬ split_dot π y ≤ (π0 : ℝ) := by
        intro hyLower
        have hyLowerMem : y ∈ L := (mem_split_branch_lower_iff).2 ⟨hyP, hyLower⟩
        simp [L, hL_empty] at hyLowerMem
      rw [negCastSplitObjective_dot]
      linarith
    have hDual_nonempty : Set.Nonempty (dual_feasible_region A c) := by
      refine
        (dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions A c).2 ?_
      intro r hrA
      have hrP : r ∈ recessionCone (polyhedron_le_set A b) := by
        rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
        exact hrA
      exact validIneq_nonpositive_on_recessionCone hP_nonempty hvalid hrP
    obtain ⟨xStar, hxStar, hGreatest⟩ :=
      linear_programming_duality_primal_optimum_exists A b c
        (by simpa [primal_feasible_region] using hP_nonempty)
        hDual_nonempty
    let E : Set (Fin n → ℝ) := face_set (polyhedron_le_set A b) c (c ⬝ᵥ xStar)
    have hE_nonempty : E.Nonempty := by
      refine ⟨xStar, ?_⟩
      exact (mem_face_set_iff).2 ⟨hxStar, rfl⟩
    have hE_exposed : IsExposed ℝ (polyhedron_le_set A b) E := by
      -- The maximizing equality set of a valid inequality is exposed.
      simpa [E] using isExposed_face_set_of_valid_inequality
        (P := polyhedron_le_set A b) (c := c) (δ := c ⬝ᵥ xStar)
        (by
          intro y hyP
          exact hGreatest.2 ⟨y, hyP, rfl⟩)
    have hE_strip : E ⊆ split_strip π π0 := by
      intro y hyE
      rcases mem_face_set_iff.mp hyE with ⟨hyP, hyEq⟩
      rw [mem_split_strip_iff]
      constructor
      · have hy_not_lower : ¬ split_dot π y ≤ (π0 : ℝ) := by
          intro hyLower
          have hyLowerMem : y ∈ L := (mem_split_branch_lower_iff).2 ⟨hyP, hyLower⟩
          simp [L, hL_empty] at hyLowerMem
        exact lt_of_not_ge hy_not_lower
      · have hx_le : c ⬝ᵥ x ≤ c ⬝ᵥ xStar := hGreatest.2 ⟨x, hxP, rfl⟩
        rw [negCastSplitObjective_dot, negCastSplitObjective_dot] at hx_le hyEq
        have hy_le_x : split_dot π y ≤ split_dot π x := by linarith
        exact lt_of_le_of_lt hy_le_x (mem_split_strip_iff.mp hx_strip).2
    exact ⟨E, hE_nonempty, hE_exposed, hE_strip⟩
  · by_cases hU_empty : U = ∅
    · let c : Fin n → ℝ := fun j ↦ (π j : ℝ)
      have hvalid : is_valid_inequality (polyhedron_le_set A b) c ((π0 : ℝ) + 1) := by
        intro y hyP
        have hy_not_upper : ¬ (π0 : ℝ) + 1 ≤ split_dot π y := by
          intro hyUpper
          have hyUpperMem : y ∈ U := (mem_split_branch_upper_iff).2 ⟨hyP, hyUpper⟩
          simp [U, hU_empty] at hyUpperMem
        rw [castSplitObjective_dot]
        linarith
      have hDual_nonempty : Set.Nonempty (dual_feasible_region A c) := by
        refine
          (dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions A c).2 ?_
        intro r hrA
        have hrP : r ∈ recessionCone (polyhedron_le_set A b) := by
          rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
          exact hrA
        exact validIneq_nonpositive_on_recessionCone hP_nonempty hvalid hrP
      obtain ⟨xStar, hxStar, hGreatest⟩ :=
        linear_programming_duality_primal_optimum_exists A b c
          (by simpa [primal_feasible_region] using hP_nonempty)
          hDual_nonempty
      let E : Set (Fin n → ℝ) := face_set (polyhedron_le_set A b) c (c ⬝ᵥ xStar)
      have hE_nonempty : E.Nonempty := by
        refine ⟨xStar, ?_⟩
        exact (mem_face_set_iff).2 ⟨hxStar, rfl⟩
      have hE_exposed : IsExposed ℝ (polyhedron_le_set A b) E := by
        -- The maximizing equality set of a valid inequality is exposed.
        simpa [E] using isExposed_face_set_of_valid_inequality
          (P := polyhedron_le_set A b) (c := c) (δ := c ⬝ᵥ xStar)
          (by
            intro y hyP
            exact hGreatest.2 ⟨y, hyP, rfl⟩)
      have hE_strip : E ⊆ split_strip π π0 := by
        intro y hyE
        rcases mem_face_set_iff.mp hyE with ⟨hyP, hyEq⟩
        rw [mem_split_strip_iff]
        constructor
        · have hx_le : c ⬝ᵥ x ≤ c ⬝ᵥ xStar := hGreatest.2 ⟨x, hxP, rfl⟩
          rw [castSplitObjective_dot, castSplitObjective_dot] at hx_le hyEq
          have hx_le_y : split_dot π x ≤ split_dot π y := by
            linarith
          exact lt_of_lt_of_le (mem_split_strip_iff.mp hx_strip).1 hx_le_y
        · have hy_not_upper : ¬ (π0 : ℝ) + 1 ≤ split_dot π y := by
            intro hyUpper
            have hyUpperMem : y ∈ U := (mem_split_branch_upper_iff).2 ⟨hyP, hyUpper⟩
            simp [U, hU_empty] at hyUpperMem
          linarith
      exact ⟨E, hE_nonempty, hE_exposed, hE_strip⟩
    · have hQ_polyhedron : is_polyhedron ((polyhedron_le_set A b)^(π, π0)) :=
        split_hull_is_polyhedron (polyhedron_le_set A b) ⟨m, A, b, rfl⟩ π π0
      rcases is_polyhedron_iff.mp hQ_polyhedron with ⟨mQ, B, d, hQ_eq⟩
      have hx_not_Q : x ∉ polyhedron_le_set B d := by
        simpa [hQ_eq] using hx_not_splitHull
      have hx_violate : ∃ i : Fin mQ, d i < (B *ᵥ x) i := by
        have hx_not_le : ¬ B *ᵥ x ≤ d := by
          simpa [mem_polyhedron_le_set_iff] using hx_not_Q
        simpa [Pi.le_def] using hx_not_le
      rcases hx_violate with ⟨i, hi_violate⟩
      let c : Fin n → ℝ := B i
      have hL_nonempty : L.Nonempty := Set.nonempty_iff_ne_empty.mpr hL_empty
      have hU_nonempty : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hU_empty
      have hQ_nonempty : (polyhedron_le_set B d).Nonempty := by
        rcases hL_nonempty with ⟨y, hy⟩
        have hyQ : y ∈ (polyhedron_le_set A b)^(π, π0) := by
          rw [split_hull]
          exact subset_convexHull ℝ (L ∪ U) (Or.inl hy)
        exact ⟨y, by simpa [hQ_eq] using hyQ⟩
      have hvalidQ : is_valid_inequality (polyhedron_le_set B d) c (d i) := by
        intro y hyQ
        exact hyQ i
      have hDual_nonempty : Set.Nonempty (dual_feasible_region A c) := by
        refine
          (dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions A c).2 ?_
        intro r hrA
        have hrP : r ∈ recessionCone (polyhedron_le_set A b) := by
          rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
          exact hrA
        have hrQ : r ∈ recessionCone ((polyhedron_le_set A b)^(π, π0)) :=
          mem_recessionCone_split_hull_of_branches_nonempty
            (polyhedron_le_set A b) ⟨m, A, b, rfl⟩ π π0
            (by simpa [L] using hL_nonempty)
            (by simpa [U] using hU_nonempty)
            hrP
        have hrQ' : r ∈ recessionCone (polyhedron_le_set B d) := by
          simpa [hQ_eq] using hrQ
        exact validIneq_nonpositive_on_recessionCone hQ_nonempty hvalidQ hrQ'
      obtain ⟨xStar, hxStar, hGreatest⟩ :=
        linear_programming_duality_primal_optimum_exists A b c
          (by simpa [primal_feasible_region] using hP_nonempty)
          hDual_nonempty
      let β : ℝ := c ⬝ᵥ xStar
      let E : Set (Fin n → ℝ) := face_set (polyhedron_le_set A b) c β
      have hβ_gt : d i < β := by
        have hx_le : c ⬝ᵥ x ≤ β := hGreatest.2 ⟨x, hxP, rfl⟩
        have hx_row : c ⬝ᵥ x = (B *ᵥ x) i := by
          simp [c, Matrix.mulVec]
        linarith
      have hE_nonempty : E.Nonempty := by
        refine ⟨xStar, ?_⟩
        exact (mem_face_set_iff).2 ⟨hxStar, rfl⟩
      have hE_exposed : IsExposed ℝ (polyhedron_le_set A b) E := by
        -- The maximizing equality set of the separating row objective is exposed.
        simpa [E, β] using isExposed_face_set_of_valid_inequality
          (P := polyhedron_le_set A b) (c := c) (δ := β)
          (by
            intro y hyP
            exact hGreatest.2 ⟨y, hyP, rfl⟩)
      have hE_disjoint :
          Disjoint E ((polyhedron_le_set A b)^(π, π0)) := by
        rw [Set.disjoint_left]
        intro y hyE hyQ
        have hyEq : c ⬝ᵥ y = β := (mem_face_set_iff.mp hyE).2
        have hyQle : c ⬝ᵥ y ≤ d i := by
          have hyQ' : y ∈ polyhedron_le_set B d := by simpa [hQ_eq] using hyQ
          exact hyQ' i
        linarith
      have hE_subset : E ⊆ polyhedron_le_set A b := by
        intro y hyE
        exact (mem_face_set_iff.mp hyE).1
      have hE_strip : E ⊆ split_strip π π0 :=
        subset_split_strip_of_subset_polyhedron_of_disjoint_splitHull π π0 hE_subset hE_disjoint
      exact ⟨E, hE_nonempty, hE_exposed, hE_strip⟩

/-- Helper for Proposition 5.2: every lineality direction of a nonempty set lies in the direction
of its affine span. -/
lemma linealitySubmodule_le_affineSpanDirection_of_nonempty
    {Q : Set (Fin n → ℝ)}
    (hQ_nonempty : Q.Nonempty) :
    linealitySubmodule Q ≤ (affineSpan ℝ Q).direction := by
  intro r hr
  obtain ⟨x0, hx0Q⟩ := hQ_nonempty
  have hx0_aff : x0 ∈ affineSpan ℝ Q := subset_affineSpan ℝ Q hx0Q
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff] at hr
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff]
  refine ⟨x0 + r, ?_, ?_⟩
  · -- Translate the base point once in the negative lineality direction to stay inside `Q`.
    simpa using subset_affineSpan ℝ Q (hr hx0Q 1)
  · -- That translated point differs from `x0` exactly by the lineality direction `r`.
    ext i
    simp

/-- Helper for Proposition 5.2: a nonempty exposed face whose affine-span dimension equals the
ambient lineality dimension is already a minimal face. -/
lemma isMinimalFaceOf_of_nonemptyExposedFace_linealityDim
    {P F : Set (Fin n → ℝ)}
    (hP_polyhedron : is_polyhedron P)
    (hF_nonempty : F.Nonempty)
    (hF_exposed : IsExposed ℝ P F)
    (hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (linealitySubmodule P)) :
    IsMinimalFaceOf ℝ P F := by
  have hLineality :
      linealitySpace F = linealitySpace P :=
    linealitySpace_eq_of_nonempty_face hP_polyhedron hF_exposed hF_nonempty
  have hLinealitySubmodule :
      linealitySubmodule F = linealitySubmodule P := by
    ext r
    rw [mem_linealitySubmodule_iff, mem_linealitySubmodule_iff, hLineality]
  have hle :
      linealitySubmodule F ≤ (affineSpan ℝ F).direction :=
    linealitySubmodule_le_affineSpanDirection_of_nonempty hF_nonempty
  have hfinrank :
      Module.finrank ℝ (linealitySubmodule F) =
        Module.finrank ℝ (affineSpan ℝ F).direction := by
    calc
      Module.finrank ℝ (linealitySubmodule F)
          = Module.finrank ℝ (linealitySubmodule P) := by
              rw [hLinealitySubmodule]
      _ = Module.finrank ℝ (affineSpan ℝ F).direction := hF_dim.symm
  have hdir :
      (affineSpan ℝ F).direction = linealitySubmodule F := by
    exact (Submodule.eq_of_le_of_finrank_eq hle hfinrank).symm
  rw [isMinimalFaceOf_iff]
  refine ⟨hF_nonempty, hF_exposed.isExtreme, ?_⟩
  intro G hG_nonempty hG_extreme hGF
  have hG_extreme_in_F : IsExtreme ℝ F G := by
    -- Restrict the ambient extremality to the exposed face `F`.
    exact hG_extreme.mono hF_exposed.isExtreme.subset hGF
  obtain ⟨x0, hx0G⟩ := hG_nonempty
  have hx0F : x0 ∈ F := hGF hx0G
  intro y hyF
  let r : Fin n → ℝ := y - x0
  have hy_dir : y -ᵥ x0 ∈ (affineSpan ℝ F).direction :=
    AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ F hyF)
      (subset_affineSpan ℝ F hx0F)
  have hr_lin : r ∈ linealitySubmodule F := by
    simpa [r, hdir, vsub_eq_sub] using hy_dir
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff] at hr_lin
  have hmirror' : x0 + (-1 : ℝ) • r ∈ F := hr_lin hx0F (-1)
  have hmirror : x0 - r ∈ F := by
    simpa [sub_eq_add_neg] using hmirror'
  have hseg : x0 ∈ openSegment ℝ (x0 - r) (x0 + r) := by
    simpa [r] using (mem_openSegment_sub_add (𝕜 := ℝ) x0 r)
  have hy_in_G : x0 + r ∈ G :=
    hG_extreme_in_F.right_mem_of_mem_openSegment
      hmirror (by simpa [r] using hyF) hx0G hseg
  simpa [r] using hy_in_G

/-- Helper for Proposition 5.2: every nonempty polyhedron contains a minimal face. -/
lemma existsMinimalFaceOfNonemptyPolyhedron
    (Q : Set (Fin n → ℝ))
    (hQ_polyhedron : is_polyhedron Q)
    (hQ_nonempty : Q.Nonempty) :
    ∃ F : Set (Fin n → ℝ), IsMinimalFaceOf ℝ Q F := by
  rcases hQ_polyhedron with ⟨m, A, b, rfl⟩
  have hLineality_le :
      Module.finrank ℝ (_root_.linealitySubmodule ℝ (polyhedron_le_set A b)) ≤
        Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    simpa using Submodule.finrank_mono
      (linealitySubmodule_le_affineSpanDirection_of_nonempty hQ_nonempty)
  let k : ℕ :=
    Module.finrank ℝ (_root_.linealitySubmodule ℝ (polyhedron_le_set A b))
  have hk_lineality :
      Module.finrank ℝ (_root_.linealitySubmodule ℝ (polyhedron_le_set A b)) ≤ k := by
    simp [k]
  have hk_polyhedron :
      k ≤ Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    simpa [k] using hLineality_le
  obtain ⟨F, hF_nonempty, hF_exposed, hF_dim⟩ :=
    exists_nonempty_face_of_finrank_between_linealitySpace_and_polyhedron
      A b hQ_nonempty k hk_lineality hk_polyhedron
  refine ⟨F, ?_⟩
  -- The selected face has the smallest possible affine dimension, namely the lineality dimension.
  exact isMinimalFaceOf_of_nonemptyExposedFace_linealityDim
    ⟨m, A, b, rfl⟩ hF_nonempty hF_exposed hF_dim

/-- Helper for Proposition 5.2: a minimal face inside an exposed face is still minimal in the
ambient polyhedron. -/
lemma isMinimalFaceOf_ambient_of_relativeMinimalFace
    {P E F : Set (Fin n → ℝ)}
    (hE_exposed : IsExposed ℝ P E)
    (hF_min : IsMinimalFaceOf ℝ E F) :
    IsMinimalFaceOf ℝ P F ∧ F ⊆ E := by
  refine ⟨?_, hF_min.subset⟩
  rw [isMinimalFaceOf_iff]
  refine ⟨hF_min.nonempty, hE_exposed.isExtreme.trans hF_min.isExtreme, ?_⟩
  intro G hG_nonempty hG_extreme hGF
  have hGF' : G ⊆ E := Set.Subset.trans hGF hF_min.subset
  have hG_extreme_in_E : IsExtreme ℝ E G := hG_extreme.mono hE_exposed.isExtreme.subset hGF'
  exact IsMinimalFaceOf.minimal (𝕜 := ℝ) hF_min hG_nonempty hG_extreme_in_E hGF

/-- Helper for Proposition 5.2: every nonempty exposed face of a polyhedron contains a minimal
ambient face. -/
lemma existsMinimalFace_subset_of_nonemptyExposedFace
    {P E : Set (Fin n → ℝ)}
    (hP_polyhedron : is_polyhedron P)
    (hE_exposed : IsExposed ℝ P E)
    (hE_nonempty : E.Nonempty) :
    ∃ F : Set (Fin n → ℝ), IsMinimalFaceOf ℝ P F ∧ F ⊆ E := by
  have hE_polyhedron : is_polyhedron E := by
    rcases hP_polyhedron with ⟨m, A, b, rfl⟩
    rcases exists_eq_active_constraint_face_of_isExposed A b E hE_exposed hE_nonempty with
      ⟨I, hE_eq⟩
    refine ⟨m + m, activeConstraintFaceMatrix A I, activeConstraintFaceRhs b I, ?_⟩
    calc
      E = active_constraint_face A b I := hE_eq
      _ = polyhedron_le_set (activeConstraintFaceMatrix A I) (activeConstraintFaceRhs b I) :=
            active_constraint_face_eq_polyhedronAux A b I
  obtain ⟨F, hF_min_rel⟩ := existsMinimalFaceOfNonemptyPolyhedron E hE_polyhedron hE_nonempty
  obtain ⟨hF_min, hFE⟩ :=
    isMinimalFaceOf_ambient_of_relativeMinimalFace hE_exposed hF_min_rel
  exact ⟨F, hF_min, hFE⟩

/-- Helper for Proposition 5.2: the integer hull of `P` is contained in every split hull of `P`
because each lattice point of `P` already lies in one split branch. -/
lemma integerHull_subset_split_hull
    (P : Set (Fin n → ℝ))
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    convexHull ℝ (P ∩ ℤ^n) ⊆ P^(π, π0) := by
  -- First place each lattice point in one split branch using integrality of `split_dot π`.
  have hPointwise : P ∩ ℤ^n ⊆ P^(π, π0) := by
    intro x hx
    rcases hx with ⟨hxP, hxInt⟩
    rcases split_dot_integral_of_mem_integerVectors π hxInt with ⟨k, hk⟩
    rw [split_hull]
    refine subset_convexHull ℝ _ ?_
    by_cases hLower : k ≤ π0
    · left
      refine (mem_split_branch_lower_iff).2 ⟨hxP, ?_⟩
      rw [hk]
      exact_mod_cast hLower
    · right
      have hUpperInt : π0 + 1 ≤ k := by omega
      refine (mem_split_branch_upper_iff).2 ⟨hxP, ?_⟩
      rw [hk]
      exact_mod_cast hUpperInt
  -- Convexity of the split hull upgrades the pointwise inclusion to the whole integer hull.
  exact convexHull_min hPointwise (convex_convexHull ℝ _)

/-- Helper for Proposition 5.2: strict containment of the split closure is witnessed by one strict
split hull. -/
lemma split_closure_ssubset_iff_exists_splitHull_ssubset
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P) :
    P^split ⊂ P ↔
      ∃ π : {π : Fin n → ℤ // π ≠ 0}, ∃ π0 : ℤ, P^(π.1, π0) ⊂ P := by
  constructor
  · intro hsplit
    have hx_exists : ∃ x, x ∈ P ∧ x ∉ P^split := by
      by_contra hx_exists
      have hP_subset : P ⊆ P^split := by
        intro x hxP
        by_contra hxSplit
        exact hx_exists ⟨x, hxP, hxSplit⟩
      exact hsplit.2 hP_subset
    rcases hx_exists with ⟨x, hxP, hxSplit⟩
    rw [mem_split_closure_iff] at hxSplit
    have hxSplit' :
        ∃ π : {π : Fin n → ℤ // π ≠ 0}, ∃ π0 : ℤ, x ∉ P^(π.1, π0) := by
      simpa only [not_forall] using hxSplit
    rcases hxSplit' with ⟨π, π0, hxSplit⟩
    refine ⟨π, π0, ?_⟩
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · exact split_hull_subset P hP_polyhedron π.1 π0
    · intro hEq
      exact hxSplit (hEq.symm ▸ hxP)
  · rintro ⟨π, π0, hsplit⟩
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · intro x hxSplitClosure
      exact hsplit.1 ((mem_split_closure_iff P x).mp hxSplitClosure π π0)
    · intro hEq
      have hP_subset_splitHull : P ⊆ P^(π.1, π0) := by
        intro x hxP
        have hxClosure : x ∈ P^split := by simpa [hEq] using hxP
        exact (mem_split_closure_iff P x).mp hxClosure π π0
      exact hsplit.2 hP_subset_splitHull

/-- Proposition 5.2 (2). Let `P` be a polyhedron and let `(π, π₀)` be a split.
Then `P^(π, π₀) ⊂ P` if and only if some minimal face of `P` is contained in the strip
`π₀ < π x < π₀ + 1`. -/
theorem split_hull_ssubset_iff_exists_minimalFace_subset_split_strip
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (hπ : π ≠ 0) :
    P^(π, π0) ⊂ P ↔
      ∃ F : Set (Fin n → ℝ), IsMinimalFaceOf ℝ P F ∧ F ⊆ split_strip π π0 := by
  constructor
  · intro hSplitStrict
    rw [Set.ssubset_iff_subset_ne] at hSplitStrict
    have hx_exists : ∃ x, x ∈ P ∧ x ∉ P^(π, π0) := by
      by_contra hx_exists
      have hP_subset_splitHull : P ⊆ P^(π, π0) := by
        intro x hxP
        by_contra hx_not_splitHull
        exact hx_exists ⟨x, hxP, hx_not_splitHull⟩
      exact hSplitStrict.2 (Set.Subset.antisymm hSplitStrict.1 hP_subset_splitHull)
    obtain ⟨x, hxP, hx_not_splitHull⟩ := hx_exists
    obtain ⟨E, hE_nonempty, hE_exposed, hE_strip⟩ :=
      exists_nonempty_exposedFace_subset_split_strip_of_mem_not_mem_splitHull
        P hP_polyhedron π π0 hπ hxP hx_not_splitHull
    -- Route correction: the old point-to-minimal-face route was too strong. The verified frontier
    -- now produces a nonempty exposed face `E` already contained in the strip.
    obtain ⟨F, hF_min, hFE⟩ :=
      existsMinimalFace_subset_of_nonemptyExposedFace hP_polyhedron hE_exposed hE_nonempty
    -- Descend once from `E` to a minimal face `F`, then compose the verified subset chain.
    exact ⟨F, hF_min, Set.Subset.trans hFE hE_strip⟩
  · rintro ⟨F, hF_min, hF_strip⟩
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · -- Every split hull is convexly generated from points already in `P`.
      exact split_hull_subset P hP_polyhedron π π0
    · intro hEq
      obtain ⟨x, hxF⟩ := hF_min.nonempty
      have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
      have hDiff_convex : Convex ℝ (P \ F) := hF_min.isExtreme.convex_diff hP_convex
      have hBranches_subset :
          split_branch_lower P π π0 ∪ split_branch_upper P π π0 ⊆ P \ F := by
        intro y hy
        rcases hy with hyLower | hyUpper
        · rcases mem_split_branch_lower_iff.mp hyLower with ⟨hyP, hyLowerBound⟩
          refine ⟨hyP, ?_⟩
          intro hyF
          rcases mem_split_strip_iff.mp (hF_strip hyF) with ⟨hyStripLeft, _⟩
          linarith
        · rcases mem_split_branch_upper_iff.mp hyUpper with ⟨hyP, hyUpperBound⟩
          refine ⟨hyP, ?_⟩
          intro hyF
          rcases mem_split_strip_iff.mp (hF_strip hyF) with ⟨_, hyStripRight⟩
          linarith
      have hHull_subset_diff : P^(π, π0) ⊆ P \ F := by
        -- The split hull stays in `P \ F` because both generating branches do.
        rw [split_hull]
        exact convexHull_min hBranches_subset hDiff_convex
      have hx_not_splitHull : x ∉ P^(π, π0) := by
        intro hxSplitHull
        exact (hHull_subset_diff hxSplitHull).2 hxF
      have hxP : x ∈ P := (IsMinimalFaceOf.subset (𝕜 := ℝ) hF_min) hxF
      exact hx_not_splitHull (hEq.symm ▸ hxP)

/-- Part (3) of Proposition 5.2. If `P` is a rational polyhedron, then `P^split ⊂ P`
if and only if the convex hull of the integer points of `P` is strictly contained in `P`. -/
theorem split_closure_ssubset_iff_integer_hull_ssubset
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    P^split ⊂ P ↔ convexHull ℝ (P ∩ ℤ^n) ⊂ P := by
  have hP_polyhedron : is_polyhedron P := by
    rcases hP_rational with ⟨m, A, b, rfl⟩
    exact ⟨m, A.map (Rat.castHom ℝ), fun i ↦ (b i : ℝ), rfl⟩
  constructor
  · intro hsplit
    rcases
        (split_closure_ssubset_iff_exists_splitHull_ssubset P hP_polyhedron).mp hsplit with
      ⟨π, π0, hSplitHull⟩
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · -- Every integer point lies in each split hull, so the whole integer hull does as well.
      exact (integerHull_subset_split_hull P π.1 π0).trans hSplitHull.1
    · intro hEq
      have hP_subset_splitHull : P ⊆ P^(π.1, π0) := by
        intro x hxP
        have hxIntHull : x ∈ convexHull ℝ (P ∩ ℤ^n) := hEq.symm ▸ hxP
        exact integerHull_subset_split_hull P π.1 π0 hxIntHull
      exact hSplitHull.2 hP_subset_splitHull
  · intro hIntegerHull
    have h_not_integral : ¬ is_integral P := by
      rw [is_integral_iff]
      intro hEq
      have hP_subset_integerHull : P ⊆ convexHull ℝ (P ∩ ℤ^n) := by
        intro x hxP
        exact hEq ▸ hxP
      exact hIntegerHull.2 hP_subset_integerHull
    have hWitness :
        ∃ c : Fin n → ℤ, ∃ z : ℝ,
          IsGreatest (((Int.cast ∘ c) ⬝ᵥ ·) '' P) z ∧ ¬ ∃ k : ℤ, z = k := by
      by_contra hWitness
      have hAllInteger :
          ∀ c z,
            IsGreatest (((Int.cast ∘ c) ⬝ᵥ ·) '' P) z →
              ∃ k : ℤ, z = k := by
        intro c z hz
        by_contra hz_not_int
        exact hWitness ⟨c, z, hz, hz_not_int⟩
      exact h_not_integral
        ((rational_polyhedron_is_integral_iff_integral_linear_maxima_are_integer
          P hP_rational).2 hAllInteger)
    rcases hWitness with ⟨c, z, hGreatest, hz_not_int⟩
    rcases hGreatest.1 with ⟨xStar, hxStarP, hxStarObj⟩
    have hc_nonzero : c ≠ 0 := by
      intro hc_zero
      have hz_zero : z = (0 : ℝ) := by
        rw [← hxStarObj]
        simp [hc_zero]
      exact hz_not_int ⟨0, by simpa using hz_zero⟩
    have hfloor_lt : (Int.floor z : ℝ) < z := by
      have hfloor_le : (Int.floor z : ℝ) ≤ z := Int.floor_le z
      by_contra hnot_lt
      have hz_eq : z = (Int.floor z : ℝ) := le_antisymm (not_lt.mp hnot_lt) hfloor_le
      exact hz_not_int ⟨Int.floor z, hz_eq⟩
    have hupper_empty : split_branch_upper P c (Int.floor z) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      intro y hyUpper
      rcases mem_split_branch_upper_iff.mp hyUpper with ⟨hyP, hyUpperBound⟩
      have hy_le : split_dot c y ≤ z := by
        simpa [split_dot] using hGreatest.2 ⟨y, hyP, rfl⟩
      have hz_lt_upper : z < (Int.floor z : ℝ) + 1 := Int.lt_floor_add_one z
      linarith
    have hLowerConvex : Convex ℝ (split_branch_lower P c (Int.floor z)) :=
      splitBranchLowerConvex P hP_polyhedron c (Int.floor z)
    have hsplitHull_eq_lower :
        P^(c, Int.floor z) = split_branch_lower P c (Int.floor z) := by
      rw [split_hull, hupper_empty, Set.union_empty, hLowerConvex.convexHull_eq]
    have hxStar_not_lower : xStar ∉ split_branch_lower P c (Int.floor z) := by
      intro hxLower
      rcases mem_split_branch_lower_iff.mp hxLower with ⟨_, hxLowerBound⟩
      have hxStarVal : split_dot c xStar = z := by
        simpa [split_dot] using hxStarObj
      linarith
    have hxStar_not_splitHull : xStar ∉ P^(c, Int.floor z) := by
      rw [hsplitHull_eq_lower]
      exact hxStar_not_lower
    refine
      (split_closure_ssubset_iff_exists_splitHull_ssubset P hP_polyhedron).mpr
        ⟨⟨c, hc_nonzero⟩, Int.floor z, ?_⟩
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · exact split_hull_subset P hP_polyhedron c (Int.floor z)
    · intro hEq
      exact hxStar_not_splitHull (hEq.symm ▸ hxStarP)

/-- For a rational polyhedron `P`, Proposition 5.2 (3) says that the split closure is strictly
smaller than `P` exactly when `P` is not integral in the Chapter 4.1 sense. -/
theorem split_closure_ssubset_iff_not_is_integral
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    P^split ⊂ P ↔ ¬ is_integral P := by
  rw [split_closure_ssubset_iff_integer_hull_ssubset P hP_rational, is_integral_iff,
    Set.ssubset_iff_subset_ne]
  constructor
  · intro hss h_integral
    exact hss.2 h_integral.symm
  · intro h_not_integral
    constructor
    · have hP_polyhedron : is_polyhedron P :=
        by
          rcases hP_rational with ⟨m, A, b, rfl⟩
          exact ⟨m, A.map (Rat.castHom ℝ), fun i ↦ (b i : ℝ), rfl⟩
      have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
      exact convexHull_min (by intro x hx; exact hx.1) hP_convex
    · exact fun h_eq ↦ h_not_integral h_eq.symm

end Proposition52
