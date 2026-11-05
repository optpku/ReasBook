/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_8

open scoped IntegerVectorNotation

-- Exercise 5.9 is source-facing, but its ambient mixed-space owner is already canonical in
-- Chapter 4 through `MixedRealPoint`, `mixed_integer_points`, and `mixed_linear_objective`.

section Exercise59

variable {n p : ℕ}

/-- The ambient real halfspace obtained by dropping the integrality restriction on the `x`
variables from Exercise 5.9. -/
def exercise_5_9_mixed_halfspace
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  {xy | mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b}

/-- Membership in `exercise_5_9_mixed_halfspace a g b` is exactly the defining one-row
inequality. -/
theorem mem_exercise_5_9_mixed_halfspace_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_9_mixed_halfspace a g b ↔
      mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b :=
  Iff.rfl

/-- The mixed-integer set
`S = {(x, y) ∈ ℤ^n × ℝ^p | ∑ a_j x_j + ∑ g_j y_j ≤ b}`
from Exercise 5.9, embedded in `ℝ^n × ℝ^p`. -/
def exercise_5_9_mixed_integer_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  mixed_integer_points (exercise_5_9_mixed_halfspace a g b)

/-- Membership in `exercise_5_9_mixed_integer_set a g b` means that the `x`-block is integral and
the defining one-row mixed inequality is satisfied. -/
theorem mem_exercise_5_9_mixed_integer_set_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_9_mixed_integer_set a g b ↔
      xy.1 ∈ ℤ^n ∧ mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b := by
  rw [exercise_5_9_mixed_integer_set, mem_mixed_integer_points_iff,
    mem_exercise_5_9_mixed_halfspace_iff, mem_mixed_integer_lattice_iff]
  simp [and_comm]

/-- The pure-integer one-row hull from Exercise 5.8, viewed in `ℝ^n × ℝ^p` by leaving the
continuous block free via the `x`-block projection. If all coefficients of `a` vanish, this
reduces to the constant halfspace `0 ≤ b`, so it is `Set.univ` for `0 ≤ b` and `∅` for `b < 0`.
-/
def exercise_5_9_pure_integer_hull
    (a : Fin n → ℤ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  if ∃ j : Fin n, a j ≠ 0 then
    {xy | xy.1 ∈ exercise_5_8_normalized_halfspace a b}
  else
    {_xy | 0 ≤ b}

/-- When some coefficient of `a` is nonzero, `exercise_5_9_pure_integer_hull a b` is the
normalized one-row halfspace from Exercise 5.8 on the `x`-block, with the `y`-block
unconstrained. -/
theorem exercise_5_9_pure_integer_hull_eq_normalized_halfspace
    (a : Fin n → ℤ)
    (b : ℝ)
    (ha : ∃ j : Fin n, a j ≠ 0) :
    exercise_5_9_pure_integer_hull a b =
      {xy : MixedRealPoint n p | xy.1 ∈ exercise_5_8_normalized_halfspace a b} := by
  simp [exercise_5_9_pure_integer_hull, ha]

/-- When every coefficient of `a` vanishes and `0 ≤ b`,
`exercise_5_9_pure_integer_hull a b` is all of `ℝ^n × ℝ^p`. -/
theorem exercise_5_9_pure_integer_hull_eq_univ_of_forall_eq_zero
    (a : Fin n → ℤ)
    (b : ℝ)
    (ha : ∀ j : Fin n, a j = 0)
    (hb : 0 ≤ b) :
    exercise_5_9_pure_integer_hull a b = (Set.univ : Set (MixedRealPoint n p)) := by
  have hzero : ¬ ∃ j : Fin n, a j ≠ 0 := by
    simp [ha]
  ext xy
  simp [exercise_5_9_pure_integer_hull, hzero, hb]

/-- When every coefficient of `a` vanishes and `b < 0`,
`exercise_5_9_pure_integer_hull a b` is empty. -/
theorem exercise_5_9_pure_integer_hull_eq_empty_of_forall_eq_zero
    (a : Fin n → ℤ)
    (b : ℝ)
    (ha : ∀ j : Fin n, a j = 0)
    (hb : b < 0) :
    exercise_5_9_pure_integer_hull a b = (∅ : Set (MixedRealPoint n p)) := by
  have hzero : ¬ ∃ j : Fin n, a j ≠ 0 := by
    simp [ha]
  have hnb : ¬ 0 ≤ b := not_le_of_gt hb
  ext xy
  simp [exercise_5_9_pure_integer_hull, hzero, hnb]

/-- The perfect formulation attached to Exercise 5.9: if some coefficient of `g` is nonzero, the
convex hull is the original mixed halfspace; if `g = 0`, one recovers the pure-integer one-row
hull on the `x`-block, with the `y`-block unconstrained. In the degenerate case `a = 0`, this
reduces further to `Set.univ` for `0 ≤ b` and to `∅` for `b < 0`. -/
def exercise_5_9_perfect_formulation
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  if ∃ j : Fin p, g j ≠ 0 then
    exercise_5_9_mixed_halfspace a g b
  else
    exercise_5_9_pure_integer_hull a b

/-- If some continuous coefficient is nonzero, the perfect formulation from Exercise 5.9 is the
original mixed halfspace. -/
theorem exercise_5_9_perfect_formulation_eq_mixed_halfspace
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (hg : ∃ j : Fin p, g j ≠ 0) :
    exercise_5_9_perfect_formulation a g b = exercise_5_9_mixed_halfspace a g b := by
  simp [exercise_5_9_perfect_formulation, hg]

/-- If every continuous coefficient vanishes, the perfect formulation from Exercise 5.9 reduces
to the pure-integer one-row hull on the `x`-block. -/
theorem exercise_5_9_perfect_formulation_eq_pure_integer_hull_of_forall_eq_zero
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (hg : ∀ j : Fin p, g j = 0) :
    exercise_5_9_perfect_formulation a g b = exercise_5_9_pure_integer_hull a b := by
  have hzero : ¬ ∃ j : Fin p, g j ≠ 0 := by
    simp [hg]
  simp [exercise_5_9_perfect_formulation, hzero]

/-- Helper for Exercise 5.9: every `x : Fin n → ℝ` lies in the convex hull of the product box
whose coordinates are the floor and ceiling of `x`. -/
lemma xBlock_mem_convexHull_floorCeilBox
    (x : Fin n → ℝ) :
    x ∈ convexHull ℝ
      (Set.univ.pi
        (fun i : Fin n ↦ ({(((Int.floor (x i)) : ℤ) : ℝ), (((Int.ceil (x i)) : ℤ) : ℝ)} : Set ℝ))) := by
  -- Place each coordinate in the convex hull of its floor/ceiling pair, then assemble them.
  refine mem_convexHull_pi ?_
  intro i hi
  have hfloorCeil : ((((Int.floor (x i)) : ℤ) : ℝ)) ≤ (((Int.ceil (x i)) : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_le_ceil (x i)
  rw [convexHull_pair, segment_eq_Icc hfloorCeil]
  constructor
  · exact Int.floor_le (x i)
  · exact Int.le_ceil (x i)

/-- Helper for Exercise 5.9: every vertex of the floor/ceiling box has integral coordinates. -/
lemma floorCeilBox_subset_integerVectors
    (x : Fin n → ℝ) :
    Set.univ.pi
        (fun i : Fin n ↦ ({(((Int.floor (x i)) : ℤ) : ℝ), (((Int.ceil (x i)) : ℤ) : ℝ)} : Set ℝ)) ⊆
      (ℤ^n : Set (Fin n → ℝ)) := by
  intro z hz
  rw [mem_integerVectors_iff_forall]
  intro i
  have hzi :
      z i ∈ ({(((Int.floor (x i)) : ℤ) : ℝ), (((Int.ceil (x i)) : ℤ) : ℝ)} : Set ℝ) := by
    exact hz i (by simp)
  rcases hzi with hzi | hzi
  · exact ⟨Int.floor (x i), hzi.symm⟩
  · exact ⟨Int.ceil (x i), hzi.symm⟩

/-- Helper for Exercise 5.9: a convex combination on the `x`-block can be lifted to the mixed
space while keeping the `y`-block fixed. -/
lemma mixedPoint_mem_convexHull_of_x_mem_convexHull
    {X : Set (Fin n → ℝ)}
    {x : Fin n → ℝ}
    {y : Fin p → ℝ}
    (hx : x ∈ convexHull ℝ X) :
    (x, y) ∈ convexHull ℝ {xy : MixedRealPoint n p | xy.1 ∈ X} := by
  rcases (mem_convexHull_iff_exists_fintype).1 hx with
    ⟨ι, _, w, z, hw₀, hw₁, hz, hxsum⟩
  -- Reuse the same barycentric weights after attaching the constant `y`-block.
  refine mem_convexHull_of_exists_fintype w (fun i ↦ (z i, y)) hw₀ hw₁ ?_ ?_
  · intro i
    exact hz i
  · refine Prod.ext ?_ ?_
    · simpa [Prod.fst_sum] using hxsum
    · calc
        (∑ i, w i • (z i, y)).2 = ∑ i, w i • y := by
              simp [Prod.snd_sum]
        _ = (∑ i, w i) • y := by
              rw [Finset.sum_smul]
        _ = y := by
              simp [hw₁]

/-- Helper for Exercise 5.9: if every coefficient of `g` vanishes, the mixed hull reduces to the
pure-integer hull on the `x`-block. -/
lemma convexHull_exercise_5_9_mixed_integer_set_eq_pure_integer_hull_of_forall_eq_zero
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (hg : ∀ j : Fin p, g j = 0) :
    convexHull ℝ (exercise_5_9_mixed_integer_set a g b) = exercise_5_9_pure_integer_hull a b := by
  have hset :
      exercise_5_9_mixed_integer_set a g b =
        {xy : MixedRealPoint n p | xy.1 ∈ exercise_5_8_integer_halfspace a b} := by
    ext xy
    rw [mem_exercise_5_9_mixed_integer_set_iff]
    have hrow :
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy = split_dot a xy.1 := by
      rw [mixed_linear_objective_def, split_dot_eq_sum]
      simp [dotProduct, hg]
    simpa [mem_exercise_5_8_integer_halfspace_iff, hrow]
  by_cases ha : ∃ i : Fin n, a i ≠ 0
  · have ha_nonzero : a ≠ 0 := by
      intro hzero
      rcases ha with ⟨i, hi⟩
      exact hi (by simpa [hzero] using congrFun hzero i)
    have h58 :
        convexHull ℝ (exercise_5_8_integer_halfspace a b) = exercise_5_8_normalized_halfspace a b :=
      convexHull_exercise_5_8_integer_halfspace_eq_normalized_halfspace a b ha_nonzero
    rw [exercise_5_9_pure_integer_hull_eq_normalized_halfspace a b ha]
    refine Set.Subset.antisymm ?_ ?_
    · have htarget_convex :
          Convex ℝ {xy : MixedRealPoint n p | xy.1 ∈ exercise_5_8_normalized_halfspace a b} := by
        have hxconv : Convex ℝ (exercise_5_8_normalized_halfspace a b) := by
          rw [← h58]
          exact convex_convexHull ℝ (exercise_5_8_integer_halfspace a b)
        simpa using hxconv.linear_preimage (LinearMap.fst ℝ (Fin n → ℝ) (Fin p → ℝ))
      refine convexHull_min ?_ htarget_convex
      intro xy hxy
      rw [hset] at hxy
      have hxHull : xy.1 ∈ convexHull ℝ (exercise_5_8_integer_halfspace a b) := by
        exact subset_convexHull ℝ _ hxy
      simpa [h58] using hxHull
    · intro xy hxy
      have hxHull : xy.1 ∈ convexHull ℝ (exercise_5_8_integer_halfspace a b) := by
        simpa [h58] using hxy
      have hxyHull :
          (xy.1, xy.2) ∈
            convexHull ℝ {uv : MixedRealPoint n p | uv.1 ∈ exercise_5_8_integer_halfspace a b} :=
        mixedPoint_mem_convexHull_of_x_mem_convexHull (y := xy.2) hxHull
      simpa [hset] using hxyHull
  · have ha_zero : ∀ i : Fin n, a i = 0 := by
      simpa using ha
    by_cases hb : 0 ≤ b
    · rw [exercise_5_9_pure_integer_hull_eq_univ_of_forall_eq_zero a b ha_zero hb]
      ext xy
      constructor
      · intro hxy
        simp
      · intro hxy
        have hbox :
            xy.1 ∈ convexHull ℝ
              (Set.univ.pi
                (fun i : Fin n ↦
                  ({(((Int.floor (xy.1 i)) : ℤ) : ℝ), (((Int.ceil (xy.1 i)) : ℤ) : ℝ)} : Set ℝ))) :=
          xBlock_mem_convexHull_floorCeilBox (x := xy.1)
        have hboxSubset :
            Set.univ.pi
                (fun i : Fin n ↦
                  ({(((Int.floor (xy.1 i)) : ℤ) : ℝ), (((Int.ceil (xy.1 i)) : ℤ) : ℝ)} : Set ℝ)) ⊆
              exercise_5_8_integer_halfspace a b := by
          intro z hz
          rw [mem_exercise_5_8_integer_halfspace_iff]
          refine ⟨floorCeilBox_subset_integerVectors (x := xy.1) hz, ?_⟩
          have hsplit : split_dot a z = 0 := by
            rw [split_dot_eq_sum]
            simp [ha_zero]
          simpa [hsplit] using hb
        have hxHull : xy.1 ∈ convexHull ℝ (exercise_5_8_integer_halfspace a b) := by
          exact (convexHull_mono hboxSubset) hbox
        have hxyHull :
            (xy.1, xy.2) ∈
              convexHull ℝ {uv : MixedRealPoint n p | uv.1 ∈ exercise_5_8_integer_halfspace a b} :=
          mixedPoint_mem_convexHull_of_x_mem_convexHull (y := xy.2) hxHull
        simpa [hset] using hxyHull
    · have hb_lt : b < 0 := lt_of_not_ge hb
      have hsource_empty : exercise_5_9_mixed_integer_set a g b = ∅ := by
        ext xy
        rw [hset]
        have hsplit : split_dot a xy.1 = 0 := by
          rw [split_dot_eq_sum]
          simp [ha_zero]
        simp [mem_exercise_5_8_integer_halfspace_iff, hsplit, not_le_of_gt hb_lt]
      rw [hsource_empty, exercise_5_9_pure_integer_hull_eq_empty_of_forall_eq_zero a b ha_zero hb_lt]
      simp

/-- Helper for Exercise 5.9: if some coefficient of `g` is nonzero, one continuous coordinate can
compensate for floor/ceiling rounding on the `x`-block, so the mixed hull is the full halfspace. -/
lemma convexHull_exercise_5_9_mixed_integer_set_eq_mixed_halfspace_of_exists_ne_zero
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (hg : ∃ j : Fin p, g j ≠ 0) :
    convexHull ℝ (exercise_5_9_mixed_integer_set a g b) = exercise_5_9_mixed_halfspace a g b := by
  rcases hg with ⟨j, hj⟩
  let Lx : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual (fun i ↦ (a i : ℝ))).toLinearMap
  let Ly : (Fin p → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual g).toLinearMap
  let L : MixedRealPoint n p →ₗ[ℝ] ℝ :=
    (Lx.comp (LinearMap.fst ℝ (Fin n → ℝ) (Fin p → ℝ))) +
      (Ly.comp (LinearMap.snd ℝ (Fin n → ℝ) (Fin p → ℝ)))
  have hsplitDot (x : Fin n → ℝ) :
      split_dot a x = (fun i ↦ (a i : ℝ)) ⬝ᵥ x := by
    rw [split_dot_eq_sum, dotProduct]
  have hL :
      ∀ xy : MixedRealPoint n p,
        L xy = mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy := by
    intro xy
    simp [L, Lx, Ly, dotProductStrongDual_apply, mixed_linear_objective]
  have hhalfspace_convex : Convex ℝ (exercise_5_9_mixed_halfspace a g b) := by
    have hset :
        exercise_5_9_mixed_halfspace a g b = {xy : MixedRealPoint n p | L xy ≤ b} := by
      ext xy
      simp [exercise_5_9_mixed_halfspace, hL]
    rw [hset]
    exact (convex_Iic b).linear_preimage L
  refine Set.Subset.antisymm ?_ ?_
  · refine convexHull_min ?_ hhalfspace_convex
    intro xy hxy
    exact (mem_exercise_5_9_mixed_integer_set_iff a g b xy).1 hxy |>.2
  · intro xy hxy
    have hxy_row :
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b := by
      exact (mem_exercise_5_9_mixed_halfspace_iff a g b xy).1 hxy
    have hxBox := xBlock_mem_convexHull_floorCeilBox (x := xy.1)
    rcases (mem_convexHull_iff_exists_fintype).1 hxBox with
      ⟨ι, _, w, z, hw₀, hw₁, hz, hxsum⟩
    let correction : ι → ℝ := fun i ↦ (split_dot a xy.1 - split_dot a (z i)) / g j
    let lifted : ι → MixedRealPoint n p := fun i ↦ (z i, xy.2 + Pi.single j (correction i))
    have hcorrection_cancel :
        ∀ i : ι, g j * correction i = split_dot a xy.1 - split_dot a (z i) := by
      intro i
      unfold correction
      field_simp [hj]
    have hlifted_mem : ∀ i : ι, lifted i ∈ exercise_5_9_mixed_integer_set a g b := by
      intro i
      rw [mem_exercise_5_9_mixed_integer_set_iff]
      refine ⟨floorCeilBox_subset_integerVectors (x := xy.1) (hz i), ?_⟩
      have hrow_lifted :
          mixed_linear_objective (fun i ↦ (a i : ℝ)) g (lifted i) =
            mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy := by
        calc
          mixed_linear_objective (fun i ↦ (a i : ℝ)) g (lifted i)
              = (fun i ↦ (a i : ℝ)) ⬝ᵥ z i + g ⬝ᵥ (xy.2 + Pi.single j (correction i)) := by
                  simp [lifted, mixed_linear_objective_def]
          _ = split_dot a (z i) + (g ⬝ᵥ xy.2 + g j * correction i) := by
                rw [← hsplitDot (z i), dotProduct_add, dotProduct_single]
          _ = split_dot a xy.1 + g ⬝ᵥ xy.2 := by
                rw [hcorrection_cancel i]
                ring
          _ = mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy := by
                rw [mixed_linear_objective_def, ← hsplitDot xy.1]
      simpa [hrow_lifted] using hxy_row
    have hweighted_split :
        ∑ i, w i * split_dot a (z i) = split_dot a xy.1 := by
      calc
        ∑ i, w i * split_dot a (z i)
            = ∑ i, (fun j ↦ (a j : ℝ)) ⬝ᵥ (w i • z i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hs :
                    (fun j ↦ (a j : ℝ)) ⬝ᵥ (w i • z i) = w i • split_dot a (z i) := by
                  rw [dotProduct_smul, ← hsplitDot (z i)]
                calc
                  w i * split_dot a (z i) = w i • split_dot a (z i) := by
                        simp [smul_eq_mul]
                  _ = (fun j ↦ (a j : ℝ)) ⬝ᵥ (w i • z i) := hs.symm
        _ = (fun j ↦ (a j : ℝ)) ⬝ᵥ ∑ i, w i • z i := by
              symm
              simpa using (dotProduct_sum (fun j ↦ (a j : ℝ)) Finset.univ (fun i ↦ w i • z i))
        _ = split_dot a xy.1 := by
              rw [hxsum, ← hsplitDot xy.1]
    have hweighted_const :
        ∑ i, w i * split_dot a xy.1 = split_dot a xy.1 := by
      calc
        ∑ i, w i * split_dot a xy.1 = (∑ i, w i) * split_dot a xy.1 := by
              rw [Finset.sum_mul]
        _ = split_dot a xy.1 := by
              simp [hw₁]
    have hcorrection_sum : ∑ i, w i * correction i = 0 := by
      calc
        ∑ i, w i * correction i
            = ∑ i, (w i * (split_dot a xy.1 - split_dot a (z i))) * (g j)⁻¹ := by
                unfold correction
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i, w i * (split_dot a xy.1 - split_dot a (z i))) * (g j)⁻¹ := by
              rw [Finset.sum_mul]
        _ = (∑ i, (w i * split_dot a xy.1 - w i * split_dot a (z i))) * (g j)⁻¹ := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = ((∑ i, w i * split_dot a xy.1) - ∑ i, w i * split_dot a (z i)) * (g j)⁻¹ := by
              rw [Finset.sum_sub_distrib]
        _ = 0 := by
              rw [hweighted_const, hweighted_split, sub_self, zero_mul]
    have hsum_lifted :
        ∑ i, w i • lifted i = xy := by
      refine Prod.ext ?_ ?_
      · simpa [lifted, Prod.fst_sum] using hxsum
      · funext k
        by_cases hk : k = j
        · subst k
          calc
            (∑ i, w i • lifted i).2 j = ∑ i, (w i * xy.2 j + w i * correction i) := by
                  simp [lifted, Prod.snd_sum, Pi.smul_apply]
            _ = ∑ i, w i * xy.2 j + ∑ i, w i * correction i := by
                  rw [Finset.sum_add_distrib]
            _ = (∑ i, w i) * xy.2 j + ∑ i, w i * correction i := by
                  rw [Finset.sum_mul]
            _ = xy.2 j := by
                  simp [hw₁, hcorrection_sum]
        · calc
            (∑ i, w i • lifted i).2 k = ∑ i, w i * xy.2 k := by
                  simp [lifted, Prod.snd_sum, Pi.smul_apply, hk]
            _ = (∑ i, w i) * xy.2 k := by
                  rw [Finset.sum_mul]
            _ = xy.2 k := by
                  simp [hw₁]
    exact mem_convexHull_of_exists_fintype w lifted hw₀ hw₁ hlifted_mem hsum_lifted

/-- Exercise 5.9. For
`S = {(x, y) ∈ ℤ^n × ℝ^p | ∑ a_j x_j + ∑ g_j y_j ≤ b}`,
the convex hull is the original halfspace whenever some continuous coefficient in `g` is nonzero;
if every coefficient of `g` vanishes, the convex hull is the pure-integer one-row hull from
Exercise 5.8 on the `x`-variables, with the `y`-variables left free. -/
theorem convexHull_exercise_5_9_mixed_integer_set_eq_perfect_formulation
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    convexHull ℝ (exercise_5_9_mixed_integer_set a g b) =
      exercise_5_9_perfect_formulation a g b := by
  by_cases hg : ∃ j : Fin p, g j ≠ 0
  · -- In the mixed branch, one nonzero continuous coefficient gives the full halfspace.
    rw [exercise_5_9_perfect_formulation_eq_mixed_halfspace a g b hg]
    exact convexHull_exercise_5_9_mixed_integer_set_eq_mixed_halfspace_of_exists_ne_zero a g b hg
  · have hg_zero : ∀ j : Fin p, g j = 0 := by
      simpa using hg
    -- In the pure branch, the set is a cylinder over Exercise 5.8.
    rw [exercise_5_9_perfect_formulation_eq_pure_integer_hull_of_forall_eq_zero a g b hg_zero]
    exact convexHull_exercise_5_9_mixed_integer_set_eq_pure_integer_hull_of_forall_eq_zero
      a g b hg_zero

end Exercise59
