/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_24

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨?_⟩
  simpa using
    (AddCircle.measure_univ :
      (volume : Measure UnitAddCircle) Set.univ = ENNReal.ofReal (1 : ℝ))

/-- The quarter-arc of `AddCircle 1` centered at `0`. -/
abbrev addCircleQuarterArc : Set UnitAddCircle :=
  Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ)

-- Proof sketch: `addCircleQuarterArc` is a closed ball in the metric additive circle, hence a
-- Borel set.
/-- The canonical quarter-arc used in the irrational-rotation non-mixing example is measurable. -/
theorem measurableSet_addCircleQuarterArc :
    MeasurableSet addCircleQuarterArc := by
  simpa [addCircleQuarterArc] using
    (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ)))

/-- Helper for Example 20.28: the natural orbit of an irrational rotation amount is dense in
`UnitAddCircle`. -/
lemma denseRangeNsmulUnitAddCircleOfIrrational
    (r : ℝ) (hr : Irrational r) :
    DenseRange (fun n : ℕ ↦ n • (r : UnitAddCircle)) := by
  -- Convert the standard dense `ℤ`-orbit criterion to the natural-orbit version used below.
  rw [← denseRange_zsmul_iff_nsmul, AddCircle.denseRange_zsmul_coe_iff]
  simpa using hr

/-- Helper for Example 20.28: every tail of the irrational orbit meets the open ball centered at
`1 / 2`. -/
lemma exists_ge_nsmul_mem_oppositeBall
    (r : ℝ) (hr : Irrational r) (N : ℕ) :
    ∃ n ≥ N, n • (r : UnitAddCircle) ∈
      Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ) := by
  let a : UnitAddCircle := (r : UnitAddCircle)
  let U : Set UnitAddCircle :=
    (fun t : UnitAddCircle ↦ N • a + t) ⁻¹' Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)
  have hU_open : IsOpen U := by
    -- Translate the opposite ball by the already-chosen initial orbit segment.
    dsimp [U]
    exact (Metric.isOpen_ball).preimage (continuous_const.add continuous_id)
  have hU_nonempty : U.Nonempty := by
    -- The translated center lands back in the target ball, so the translated ball is nonempty.
    refine ⟨((1 / 2 : ℝ) : UnitAddCircle) - N • a, ?_⟩
    change N • a + (((1 / 2 : ℝ) : UnitAddCircle) - N • a) ∈
        Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Metric.mem_ball_self (show 0 < (1 / 8 : ℝ) by norm_num) :
        ((1 / 2 : ℝ) : UnitAddCircle) ∈
          Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ))
  obtain ⟨m, hm⟩ :=
    (denseRangeNsmulUnitAddCircleOfIrrational r hr).exists_mem_open hU_open hU_nonempty
  refine ⟨N + m, Nat.le_add_right N m, ?_⟩
  -- Repackage the translated hit as a large orbit time.
  change N • a + m • a ∈ Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ) at hm
  simpa [a, add_nsmul] using hm

/-- Helper for Example 20.28: translating the quarter-arc pulls it back to a closed ball centered
at the opposite point. -/
lemma quarterArc_preimage_add_eq_closedBall
    (t : UnitAddCircle) :
    (fun x : UnitAddCircle ↦ x + t) ⁻¹' addCircleQuarterArc =
      Metric.closedBall (-t) (1 / 8 : ℝ) := by
  -- The quarter-arc is itself a closed ball, so the translation preimage is the translated center.
  simpa [addCircleQuarterArc, sub_eq_add_neg] using
    (Metric.preimage_add_right_closedBall t (0 : UnitAddCircle) (1 / 8 : ℝ))

/-- Helper for Example 20.28: points within `1 / 8` of the antipode translate the quarter-arc to a
disjoint closed ball. -/
lemma quarterArcClosedBall_disjoint_of_mem_oppositeBall
    (t : UnitAddCircle)
    (ht : t ∈ Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)) :
    Disjoint (Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ))
      (Metric.closedBall (-t) (1 / 8 : ℝ)) := by
  have hhalf : dist (0 : UnitAddCircle) ((1 / 2 : ℝ) : UnitAddCircle) = 1 / 2 := by
    -- The point `1 / 2` is exactly the antipode of `0` on the unit additive circle.
    simpa [dist_eq_norm] using (AddCircle.norm_half_period_eq (p := (1 : ℝ)))
  have hdist : (1 / 4 : ℝ) < dist (0 : UnitAddCircle) t := by
    -- Anything within `1 / 8` of the antipode stays more than `1 / 4` away from `0`.
    have htriangle :
        dist (0 : UnitAddCircle) ((1 / 2 : ℝ) : UnitAddCircle) ≤
          dist (0 : UnitAddCircle) t + dist t ((1 / 2 : ℝ) : UnitAddCircle) :=
      dist_triangle _ _ _
    have hball : dist t ((1 / 2 : ℝ) : UnitAddCircle) < 1 / 8 := ht
    linarith
  have hdist_neg : dist (0 : UnitAddCircle) (-t) = dist (0 : UnitAddCircle) t := by
    -- Negation preserves the distance from `0` on the additive circle.
    simp [dist_eq_norm]
  -- Two closed balls of radius `1 / 8` cannot meet when their centers are more than `1 / 4` apart.
  refine Metric.closedBall_disjoint_closedBall ?_
  rw [hdist_neg]
  linarith

/-- Helper for Example 20.28: if the translation amount lies in the opposite open arc, then the
corresponding quarter-arc self-correlation term vanishes. -/
lemma iterateSelfCorrelation_eq_zero_of_nsmul_mem_oppositeBall
    (r : ℝ) {n : ℕ}
    (hn : n • (r : UnitAddCircle) ∈
      Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)) :
    volume
      (addCircleQuarterArc ∩
        (((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹' addCircleQuarterArc)) = 0 := by
  let t : UnitAddCircle := n • (r : UnitAddCircle)
  have hIter :
      ((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) =
        fun x : UnitAddCircle ↦ x + t := by
    -- Collapse the `n`th iterate of a translation to translation by `n • r`.
    simpa [t] using (add_right_iterate (r : UnitAddCircle) n)
  have hdisj :
      Disjoint (Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ))
        (Metric.closedBall (-t) (1 / 8 : ℝ)) :=
    quarterArcClosedBall_disjoint_of_mem_oppositeBall t (by simpa [t] using hn)
  -- Rewrite the iterate as a translation by `n • r`, then use the disjointness of the two arcs.
  rw [hIter, quarterArc_preimage_add_eq_closedBall, addCircleQuarterArc]
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, measure_empty]

/-- Example 20.28: for irrational `r`, the rotation `x ↦ x + r (mod 1)` on the circle fails the
mixing correlation limit for the quarter-arc `addCircleQuarterArc`; in particular, this ergodic
rotation is not mixing. -/
-- Proof sketch: use irrationality to choose a subsequence of the orbit of `0` that lands in the
-- opposite semicircle. Along that subsequence, the translated quarter-arcs are disjoint, so the
-- self-correlation terms are `0` while the product of the marginal measures stays positive.
theorem irrational_addCircle_rotation_quarterArc_selfCorrelation_not_tendsto
    (r : ℝ) (hr : Irrational r) :
    ¬ Tendsto
      (fun n : ℕ ↦
        volume
          (addCircleQuarterArc ∩
            ((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹' addCircleQuarterArc))
      atTop
      (nhds (volume addCircleQuarterArc * volume addCircleQuarterArc)) :=
  by
    have hquarterPos : 0 < volume addCircleQuarterArc := by
      -- The quarter-arc is a genuine closed ball of positive radius, so it has positive measure.
      simpa [addCircleQuarterArc] using
        (Metric.measure_closedBall_pos (μ := (volume : Measure UnitAddCircle))
          (0 : UnitAddCircle) (show 0 < (1 / 8 : ℝ) by norm_num))
    have hlimitPos : 0 < volume addCircleQuarterArc * volume addCircleQuarterArc := by
      exact ENNReal.mul_pos hquarterPos.ne' hquarterPos.ne'
    intro htendsto
    have hEventuallyPos :
        ∀ᶠ n in atTop,
          0 <
            volume
              (addCircleQuarterArc ∩
                (((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹'
                  addCircleQuarterArc)) := by
      -- Convergence to a positive limit forces eventual strict positivity.
      exact htendsto.eventually (Ioi_mem_nhds hlimitPos)
    rcases eventually_atTop.1 hEventuallyPos with ⟨N, hN⟩
    obtain ⟨n, hnN, hn⟩ := exists_ge_nsmul_mem_oppositeBall r hr N
    have hzero :
        volume
          (addCircleQuarterArc ∩
            (((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹'
              addCircleQuarterArc)) = 0 :=
      iterateSelfCorrelation_eq_zero_of_nsmul_mem_oppositeBall r hn
    exact (hN n hnN).ne' hzero

/-- The irrational rotation on `AddCircle 1` is not strongly mixing in the chapter sense. -/
theorem irrational_addCircle_rotation_not_stronglyMixing
    (r : ℝ) (hr : Irrational r) :
    ¬ IsStronglyMixing ((· + (r : UnitAddCircle))) volume := by
  intro hmix
  exact irrational_addCircle_rotation_quarterArc_selfCorrelation_not_tendsto r hr <|
    isStronglyMixing_tendsto_measure_inter_preimage_iterate hmix
      measurableSet_addCircleQuarterArc measurableSet_addCircleQuarterArc
