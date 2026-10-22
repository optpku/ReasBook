/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [MetricSpace X]

/- The interval `[-1,1]` in `ℝ` is nonempty. -/
private lemma neg_one_le_one : (-1 : ℝ) ≤ 1 := by
  norm_num

/- The horizontal segment `{(t,0) : t ∈ [-1,1]}` viewed inside `ULift (ℝ × ℝ)`. -/
private def horizontalSegment : Set (ULift.{u} (ℝ × ℝ)) :=
  {p | p.down.2 = 0 ∧ p.down.1 ∈ Set.Icc (-1 : ℝ) 1}

/- Clamp a real number to the interval `[-1,1]`. -/
private noncomputable def clampToSegment : ℝ → Set.Icc (-1 : ℝ) 1 :=
  Set.projIcc (-1 : ℝ) 1 neg_one_le_one

/- A point that is no farther than every point of `C` realizes `Metric.infDist x C`. -/
private lemma dist_eq_infDist_of_forall_le {Y : Type u} [MetricSpace Y] {C : Set Y} {x p : Y}
    (hp : p ∈ C) (hmin : ∀ q ∈ C, dist x p ≤ dist x q) :
    dist x p = Metric.infDist x C := by
  -- Convert the pointwise minimizing property into the defining infimum formula.
  apply le_antisymm
  · rw [Metric.infDist_eq_iInf]
    let _ : Nonempty {q // q ∈ C} := ⟨⟨p, hp⟩⟩
    exact le_ciInf (fun q : {q // q ∈ C} ↦ hmin q.1 q.2)
  · exact Metric.infDist_le_dist_of_mem hp

/- Clamping to `[-1,1]` minimizes the distance to any point of that interval. -/
private lemma abs_sub_projIcc_le_abs_sub_of_mem_Icc (x t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |x - ((clampToSegment x : Set.Icc (-1 : ℝ) 1) : ℝ)| ≤ |x - t| := by
  -- Split according to whether `x` lies to the left, inside, or to the right of the interval.
  by_cases hxleft : x ≤ -1
  · rw [clampToSegment, Set.projIcc_of_le_left neg_one_le_one hxleft]
    have hx_nonpos : x - (-1 : ℝ) ≤ 0 := by
      linarith
    have hxt_nonpos : x - t ≤ 0 := by
      linarith [ht.1, hxleft]
    rw [abs_of_nonpos hx_nonpos, abs_of_nonpos hxt_nonpos]
    linarith [ht.1]
  · by_cases hxright : 1 ≤ x
    · rw [clampToSegment, Set.projIcc_of_right_le neg_one_le_one hxright]
      have hx_nonneg : 0 ≤ x - (1 : ℝ) := by
        linarith
      have hxt_nonneg : 0 ≤ x - t := by
        linarith [ht.2, hxright]
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hxt_nonneg]
      linarith [ht.2]
    · have hxmem : x ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor
        · linarith
        · linarith
      rw [clampToSegment, Set.projIcc_of_mem neg_one_le_one hxmem]
      simp

/- Clamping the first coordinate and setting the second coordinate to zero gives a best
approximation from the horizontal segment. -/
private lemma horizontal_segment_projection_is_best (x : ULift.{u} (ℝ × ℝ)) :
    IsBestApproximation x horizontalSegment
      (ULift.up (((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0)) := by
  constructor
  · -- The clamped point lies on the segment by construction.
    constructor
    · rfl
    · exact (clampToSegment x.down.1).2
  · -- Rewrite the sup-norm distances and compare only the first coordinates.
    apply dist_eq_infDist_of_forall_le
    · constructor
      · rfl
      · exact (clampToSegment x.down.1).2
    · intro q hq
      rw [show dist x
          (ULift.up (((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0)) =
            dist x.down
              ((((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0) : ℝ × ℝ) by
          rfl]
      rw [show dist x q = dist x.down q.down by rfl]
      rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, hq.1]
      have hclamp :
          |x.down.1 - ((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ)| ≤
            |x.down.1 - q.down.1| := by
        exact abs_sub_projIcc_le_abs_sub_of_mem_Icc x.down.1 q.down.1 hq.2
      exact max_le_max hclamp le_rfl

/- Every point of the horizontal segment is at distance at least `1` from `(0,1)`. -/
private lemma one_le_dist_top_point_of_mem_horizontal_segment (q : ULift.{u} (ℝ × ℝ))
    (hq : q ∈ horizontalSegment) :
    1 ≤ dist (ULift.up ((0 : ℝ), 1)) q := by
  -- The second coordinate already contributes distance `1` everywhere on the segment.
  rw [show dist (ULift.up ((0 : ℝ), 1)) q = dist ((0 : ℝ), 1) q.down by rfl]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hq.1]
  norm_num

-- Proof sketch: take `X = ULift (ℝ × ℝ)` with the sup norm inherited from `ℝ × ℝ`, and let `C`
-- be the horizontal segment `{(t, 0) : t ∈ Set.Icc (-1) 1}`. For each `x`, clamp the first
-- coordinate to `[-1, 1]` to obtain a point of `C` realizing `Metric.infDist x C`, so `C` is
-- proximinal. For the point with coordinates `(0, 1)`, every point of the segment is at distance
-- `1`, yielding at least two distinct best approximations and therefore showing that `C` is not
-- Chebyshev.
/-- Proposition 3.15.2: there exists a real normed linear space and a subset of it that is
proximinal but not Chebyshev. -/
theorem exists_proximinal_not_chebyshev_subset :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (C : Set X),
      IsProximinalIn C ∧ ¬ IsChebyshev C := by
  refine ⟨ULift.{u} (ℝ × ℝ), inferInstance, inferInstance, horizontalSegment, ?_, ?_⟩
  · -- Every point is best-approximated by clamping its first coordinate to `[-1,1]`.
    intro x
    refine ⟨ULift.up (((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0), ?_⟩
    exact horizontal_segment_projection_is_best x
  · -- The point `(0,1)` has two distinct best approximations on the segment.
    intro hcheb
    let x0 : ULift.{u} (ℝ × ℝ) := ULift.up ((0 : ℝ), 1)
    let p0 : ULift.{u} (ℝ × ℝ) := ULift.up ((0 : ℝ), 0)
    let p1 : ULift.{u} (ℝ × ℝ) := ULift.up ((1 : ℝ), 0)
    obtain ⟨p, hp, hp_unique⟩ := hcheb x0
    have hp0_mem : p0 ∈ horizontalSegment := by
      constructor
      · rfl
      · constructor <;> norm_num
    have hp1_mem : p1 ∈ horizontalSegment := by
      constructor
      · rfl
      · constructor <;> norm_num
    have hp0_dist : dist x0 p0 = 1 := by
      norm_num [x0, p0, Prod.dist_eq, Real.dist_eq]
    have hp1_dist : dist x0 p1 = 1 := by
      norm_num [x0, p1, Prod.dist_eq, Real.dist_eq]
    have hp0_best : IsBestApproximation x0 horizontalSegment p0 := by
      constructor
      · exact hp0_mem
      · apply dist_eq_infDist_of_forall_le hp0_mem
        intro q hq
        rw [hp0_dist]
        exact one_le_dist_top_point_of_mem_horizontal_segment q hq
    have hp1_best : IsBestApproximation x0 horizontalSegment p1 := by
      constructor
      · exact hp1_mem
      · apply dist_eq_infDist_of_forall_le hp1_mem
        intro q hq
        rw [hp1_dist]
        exact one_le_dist_top_point_of_mem_horizontal_segment q hq
    have hp_eq_p0 : p = p0 := (hp_unique p0 hp0_best).symm
    have hp_eq_p1 : p = p1 := (hp_unique p1 hp1_best).symm
    have hp0_eq_hp1 : p0 = p1 := hp_eq_p0.symm.trans hp_eq_p1
    change ULift.up ((0 : ℝ), 0) = ULift.up ((1 : ℝ), 0) at hp0_eq_hp1
    norm_num at hp0_eq_hp1
