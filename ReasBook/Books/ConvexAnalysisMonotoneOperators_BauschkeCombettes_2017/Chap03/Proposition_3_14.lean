/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

noncomputable section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Helper for Proposition 3.14: the weak image of a norm-closed ball in a real Hilbert space is
compact. -/
private lemma weak_image_closedBall_isCompact {x : 𝓗} {r : ℝ} (hr : 0 ≤ r) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall x r : Set (WeakSpace ℝ 𝓗)) := by
  -- First compactify the scaled unit ball using the earlier weak-compactness theorem.
  have hscaled :
      IsCompact ((toWeakSpace ℝ 𝓗) '' (r • {u : 𝓗 | ‖u‖ ≤ 1}) : Set (WeakSpace ℝ 𝓗)) :=
    isCompact_weakImage_smul_unit_ball r
  -- Then translate the compact weak image by the fixed center `x`.
  have htranslate :
      IsCompact
        ((fun w : WeakSpace ℝ 𝓗 ↦ toWeakSpace ℝ 𝓗 x + w) ''
          ((toWeakSpace ℝ 𝓗) '' (r • {u : 𝓗 | ‖u‖ ≤ 1}) : Set (WeakSpace ℝ 𝓗))) :=
    hscaled.image (continuous_const.add continuous_id)
  -- The geometric identity `closedBall x r = x + r • closedBall 0 1` aligns the sets.
  convert htranslate using 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← affinity_unitClosedBall hr x] at hy
    rcases Set.mem_vadd_set.mp hy with ⟨v, hv, hvEq⟩
    rcases hv with ⟨u, huBall, rfl⟩
    refine ⟨toWeakSpace ℝ 𝓗 (r • u), ?_, ?_⟩
    · refine ⟨r • u, ?_, rfl⟩
      refine ⟨u, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using huBall
    · simpa [hvEq, add_comm, add_left_comm, add_assoc]
  · rintro ⟨w, hw, hz⟩
    rcases hw with ⟨v, hv, rfl⟩
    rcases hv with ⟨u, hu, rfl⟩
    refine ⟨x + r • u, ?_, ?_⟩
    · rw [← affinity_unitClosedBall hr x]
      apply Set.mem_vadd_set.mpr
      refine ⟨r • u, ?_, by simp⟩
      exact ⟨u, by simpa [Metric.mem_closedBall, dist_eq_norm] using hu, rfl⟩
    · simpa [add_comm, add_left_comm, add_assoc] using hz

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 3.14: the weak image commutes with intersecting a set with a closed
ball. -/
private lemma weak_image_inter_closedBall_eq {C : Set 𝓗} {x : 𝓗} {r : ℝ} :
    ((toWeakSpace ℝ 𝓗) '' (C ∩ Metric.closedBall x r) : Set (WeakSpace ℝ 𝓗)) =
      ((toWeakSpace ℝ 𝓗) '' C) ∩ ((toWeakSpace ℝ 𝓗) '' Metric.closedBall x r) := by
  -- Injectivity of `toWeakSpace` lets us identify the two witnesses in the intersection.
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, rfl⟩, ⟨z, hz.2, rfl⟩⟩
  · rintro ⟨hyC, hyB⟩
    rcases hyC with ⟨z, hzC, hzEq⟩
    rcases hyB with ⟨w, hwB, hwEq⟩
    have hzw : z = w := (toWeakSpace ℝ 𝓗).injective (hzEq.trans hwEq.symm)
    exact ⟨z, ⟨hzC, hzw ▸ hwB⟩, hzEq⟩

/-- Helper for Proposition 3.14: the distance to a fixed point is lower semicontinuous for the weak
topology on a real Hilbert space. -/
private lemma weak_dist_lowerSemicontinuous (x : 𝓗) :
    LowerSemicontinuous (fun y : WeakSpace ℝ 𝓗 ↦ dist x ((toWeakSpace ℝ 𝓗).symm y)) := by
  -- Rewrite the distance as the supremum of weakly continuous coordinate functionals on the weak
  -- closed unit ball.
  have hrepr :
      (fun y : WeakSpace ℝ 𝓗 ↦ dist x ((toWeakSpace ℝ 𝓗).symm y)) =
        fun y : WeakSpace ℝ 𝓗 ↦
          ⨆ u : weakClosedUnitBall 𝓗,
            |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))| := by
    funext y
    calc
      dist x ((toWeakSpace ℝ 𝓗).symm y) = ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ := by
        rw [dist_eq_norm]
      _ = ‖evalOnWeakClosedUnitBall 𝓗 (x - ((toWeakSpace ℝ 𝓗).symm y))‖ := by
        rw [evalOnWeakClosedUnitBall_norm_eq (x - ((toWeakSpace ℝ 𝓗).symm y))]
      _ = ⨆ u : weakClosedUnitBall 𝓗,
            ‖evalOnWeakClosedUnitBall 𝓗 (x - ((toWeakSpace ℝ 𝓗).symm y)) u‖ := by
        rw [ContinuousMap.norm_eq_iSup_norm]
      _ = ⨆ u : weakClosedUnitBall 𝓗,
            |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))| := by
        rfl
  rw [hrepr]
  -- Each coordinate is continuous, so the pointwise supremum is lower semicontinuous.
  refine lowerSemicontinuous_ciSup ?_ ?_
  · intro y
    refine ⟨‖x - ((toWeakSpace ℝ 𝓗).symm y)‖, ?_⟩
    rintro _ ⟨u, rfl⟩
    calc
      |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))|
          ≤ ‖(toWeakSpace ℝ 𝓗).symm u‖ * ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ := by
        gcongr
        exact weakClosedUnitBall_norm_le_one u
      _ = ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ := by ring
  · intro u
    have hycont :
        Continuous fun y : WeakSpace ℝ 𝓗 ↦
          inner ℝ ((toWeakSpace ℝ 𝓗).symm u) ((toWeakSpace ℝ 𝓗).symm y) := by
      simpa [real_inner_comm] using
        (weakSpace_continuous_inner_right ((toWeakSpace ℝ 𝓗).symm u))
    have hcoord :
        Continuous fun y : WeakSpace ℝ 𝓗 ↦
          inner ℝ ((toWeakSpace ℝ 𝓗).symm u) x -
            inner ℝ ((toWeakSpace ℝ 𝓗).symm u) ((toWeakSpace ℝ 𝓗).symm y) :=
      continuous_const.sub hycont
    have habsEq :
        (fun y : WeakSpace ℝ 𝓗 ↦
          |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))|) =
        (fun y : WeakSpace ℝ 𝓗 ↦
          |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) x -
            inner ℝ ((toWeakSpace ℝ 𝓗).symm u) ((toWeakSpace ℝ 𝓗).symm y)|) := by
      funext y
      rw [inner_sub_right]
    rw [habsEq]
    exact (Continuous.abs hcoord).lowerSemicontinuous

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Proposition 3.14: a minimizer on the truncation `C ∩ closedBall x (dist x z)` is
already a global minimizer on `C`. -/
private lemma truncated_minimizer_le_all {C : Set 𝓗} {x z p : 𝓗}
    (hp : p ∈ C ∩ Metric.closedBall x (dist x z))
    (hmin : ∀ y ∈ C ∩ Metric.closedBall x (dist x z), dist x p ≤ dist x y) :
    ∀ y ∈ C, dist x p ≤ dist x y := by
  intro y hyC
  by_cases hyBall : y ∈ Metric.closedBall x (dist x z)
  · -- Inside the truncating ball we can invoke the local minimizing property directly.
    exact hmin y ⟨hyC, hyBall⟩
  · -- Outside the truncating ball, the radius bound on `p` gives the desired comparison.
    have hp_le : dist x p ≤ dist x z := by
      simpa [Metric.mem_closedBall, dist_comm] using hp.2
    have hy_gt : dist x z < dist x y := by
      have hyBall' : ¬ dist x y ≤ dist x z := by
        simpa [Metric.mem_closedBall, dist_comm] using hyBall
      exact lt_of_not_ge hyBall'
    exact le_trans hp_le hy_gt.le

-- Proof sketch: fix `x : 𝓗` and intersect `C` with a sufficiently large
-- closed ball centered at `x`.
-- By weak closedness and the weak compactness of closed balls in a Hilbert space, this intersection
-- is weakly compact. The norm-distance function is weakly lower semicontinuous, so it attains its
-- minimum there; the minimizer is then a best approximation from `C`.
/-- Proposition 3.14: every nonempty weakly closed subset of a real Hilbert space is proximinal,
so every point admits a best approximation in the set. -/
theorem exists_bestApproximation_of_nonempty_weaklyClosed {C : Set 𝓗} (hC : C.Nonempty)
    (hweak : IsClosed ((toWeakSpace ℝ 𝓗) '' C)) :
    IsProximinalIn C := by
  rw [isProximinalIn_iff_forall_exists_bestApproximation]
  intro x
  rcases hC with ⟨z, hzC⟩
  let D : Set 𝓗 := C ∩ Metric.closedBall x (dist x z)
  have hzD : z ∈ D := by
    -- The chosen point `z ∈ C` lies in the truncating ball by construction.
    exact ⟨hzC, by simp [Metric.mem_closedBall, dist_comm]⟩
  have hcompactD :
      IsCompact ((toWeakSpace ℝ 𝓗) '' D : Set (WeakSpace ℝ 𝓗)) := by
    -- The truncation is a weakly closed subset of the weakly compact image of the closed ball.
    rw [show D = C ∩ Metric.closedBall x (dist x z) by rfl, weak_image_inter_closedBall_eq]
    exact (weak_image_closedBall_isCompact dist_nonneg).inter_left hweak
  have hdistD :
      LowerSemicontinuousOn
        (fun y : WeakSpace ℝ 𝓗 ↦ dist x ((toWeakSpace ℝ 𝓗).symm y))
        (((toWeakSpace ℝ 𝓗) '' D : Set (WeakSpace ℝ 𝓗))) :=
    (weak_dist_lowerSemicontinuous x).lowerSemicontinuousOn _
  obtain ⟨w, hwD, hwmin⟩ :=
    hdistD.exists_isMinOn (Set.Nonempty.image _ ⟨z, hzD⟩) hcompactD
  rcases hwD with ⟨p, hpD, rfl⟩
  refine ⟨p, ?_⟩
  have hminD : ∀ y ∈ D, dist x p ≤ dist x y := by
    -- Pull the weak-space minimizer back to the original Hilbert space.
    intro y hyD
    have hyImage : toWeakSpace ℝ 𝓗 y ∈ (toWeakSpace ℝ 𝓗) '' D := ⟨y, hyD, rfl⟩
    simpa using hwmin hyImage
  have hglobal : ∀ y ∈ C, dist x p ≤ dist x y := truncated_minimizer_le_all hpD hminD
  refine ⟨hpD.1, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hpD.1)⟩
  rw [Metric.le_infDist ⟨p, hpD.1⟩]
  exact hglobal
