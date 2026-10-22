/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_24

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Remark 20.27: the weak-mixing Cesàro averages attached to `τ` and `P`. -/
private def WeakMixingAverages (τ : Ω → Ω) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Filter.Tendsto
      (fun n : ℕ ↦
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|))
      Filter.atTop
      (nhds 0)

/-- Helper for Remark 20.27: strong mixing makes the centered correlation error tend to `0`. -/
private lemma strongMixingCorrelationError_tendsto_zero
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto
      (fun n : ℕ ↦ P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B)
      Filter.atTop
      (nhds 0) := by
  -- Shift the strong-mixing limit by the constant correlation term so the limit becomes `0`.
  have hconst :
      Filter.Tendsto (fun _ : ℕ ↦ P.real A * P.real B) Filter.atTop (nhds (P.real A * P.real B)) :=
    tendsto_const_nhds
  simpa using (hstrong A B hA hB).sub hconst

/-- Helper for Remark 20.27: strong mixing makes the absolute correlation error tend to `0`. -/
private lemma strongMixingAbsCorrelationError_tendsto_zero
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto
      (fun n : ℕ ↦ |P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B|)
      Filter.atTop
      (nhds 0) := by
  -- Transport the zero-limit through the continuous absolute-value map.
  exact
    (continuous_abs.tendsto' _ _ abs_zero).comp
      (strongMixingCorrelationError_tendsto_zero (P := P) hstrong hA hB)

/-- Helper for Remark 20.27: strong mixing makes the Cesàro averages of absolute correlation
errors converge to `0`. -/
private lemma strongMixingCesaroAbsCorrelation_tendsto_zero
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|))
      Filter.atTop
      (nhds 0) := by
  -- Apply the Cesàro theorem to the convergent absolute-error sequence.
  simpa [one_div] using
    (strongMixingAbsCorrelationError_tendsto_zero (P := P) hstrong hA hB).cesaro

/-- Helper for Remark 20.27: strong mixing implies the weak-mixing Cesàro averages. -/
private lemma weakMixingAverages_of_isStronglyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) :
    WeakMixingAverages τ P := by
  intro A B hA hB
  -- The Cesàro helper is exactly the weak-mixing average required below.
  simpa using
    strongMixingCesaroAbsCorrelation_tendsto_zero (P := P) hstrong hA hB

/-- Helper for Remark 20.27: weak mixing forces every invariant measurable event to have
probability `0` or `1`. -/
lemma weakMixingInvariantEvent_probEqZeroOrOne
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hweak : WeakMixingAverages τ P) {A : Set Ω} (hA : MeasurableSet A) (hτA : τ ⁻¹' A = A) :
    P A = 0 ∨ P A = 1 := by
  let c : ℝ := |P.real A - P.real A * P.real A|
  have hlimit_zero := hweak A A hA hA
  have hlimit_const :
      Filter.Tendsto
        (fun n : ℕ ↦
          (1 / (n : ℝ)) *
            (Finset.sum (Finset.range n) fun i ↦
              |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|))
        Filter.atTop
        (nhds c) := by
    -- Once `A` is invariant, every weak-mixing average is the same constant.
    refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hfixed : Function.IsFixedPt (Set.preimage τ) A := hτA
    have hiterateA : ∀ j : ℕ, (τ^[j]) ⁻¹' A = A := by
      intro j
      exact (Function.IsFixedPt.preimage_iterate (f := τ) hfixed j).eq
    have hsum :
        Finset.sum (Finset.range n) (fun i ↦
          |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|) =
          n * c := by
      calc
        Finset.sum (Finset.range n) (fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|) =
            Finset.sum (Finset.range n) (fun _ ↦ c) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hiterateA i]
          simp [c]
        _ = n * c := by
          simp [c]
    -- Evaluate the Cesàro average of the constant sequence explicitly.
    rw [hsum]
    field_simp [hn0]
  have hc : c = 0 := tendsto_nhds_unique hlimit_const hlimit_zero
  have hreal : P.real A = 0 ∨ P.real A = 1 := by
    -- The only roots of `x - x^2` are `0` and `1`.
    have hmul : P.real A * (1 - P.real A) = 0 := by
      have habs : P.real A - P.real A * P.real A = 0 := abs_eq_zero.mp hc
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr <| by linarith
  rcases hreal with hzero | hone
  · left
    exact (measureReal_eq_zero_iff (μ := P) (s := A)).mp hzero
  · right
    exact (ENNReal.toReal_eq_one_iff (P A)).mp (by simpa [Measure.real] using hone)

/-- Helper for Remark 20.27: every probability-preserving system satisfying the weak-mixing
Cesàro averages is ergodic. -/
lemma ergodicOfWeakMixingAverages
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (hweak : WeakMixingAverages τ P) :
    Ergodic τ P := by
  -- Package measure preservation with the invariant-event zero-one law.
  refine { toMeasurePreserving := hτ, toPreErgodic := ?_ }
  refine ⟨?_⟩
  intro A hA hτA
  -- Weak mixing collapses every invariant event to measure `0` or `1`.
  rcases weakMixingInvariantEvent_probEqZeroOrOne P hweak hA hτA with hA0 | hA1
  · exact Filter.eventuallyConst_set'.2 <| Or.inl <| ae_eq_empty.2 hA0
  · have hA_compl : P Aᶜ = 0 := by
      rw [measure_compl hA (measure_ne_top P A), IsProbabilityMeasure.measure_univ, hA1, tsub_self]
    exact Filter.eventuallyConst_set'.2 <| Or.inr <| ae_eq_univ.2 hA_compl

-- Proof sketch: if the correlation sequence itself converges to `P A * P B` for every measurable
-- `A` and `B`, then the system is strongly mixing in the sense recalled in Definition 20.24.
-- Combining this with Theorem 20.23 yields ergodicity.
/-- Remark 20.27: the mixing correlation limit condition implies ergodicity. -/
theorem ergodic_of_isStronglyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω} (hτ : MeasurePreserving τ P P)
    (hstrong : IsStronglyMixing τ P) :
    Ergodic τ P := by
  -- Prove the weak-mixing averages locally, then apply the invariant-event zero-one law.
  have hweak : WeakMixingAverages τ P := weakMixingAverages_of_isStronglyMixing (P := P) hstrong
  exact ergodicOfWeakMixingAverages (P := P) hτ hweak

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨?_⟩
  simpa using
    (AddCircle.measure_univ :
      (volume : Measure UnitAddCircle) Set.univ = ENNReal.ofReal (1 : ℝ))

/-- Helper for Remark 20.27: the quarter-arc of `UnitAddCircle` centered at `0`. -/
abbrev addCircleQuarterArc : Set UnitAddCircle :=
  Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ)

/-- Helper for Remark 20.27: the quarter-arc obstruction set is measurable. -/
lemma measurableSet_addCircleQuarterArc :
    MeasurableSet addCircleQuarterArc := by
  -- The quarter-arc is a closed ball, hence a measurable Borel set.
  simpa [addCircleQuarterArc] using
    (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ)))

/-- Helper for Remark 20.27: every tail of the irrational `ℕ`-orbit hits the open ball around the
antipode `1 / 2`. -/
lemma exists_ge_nsmul_mem_oppositeBall
    (r : ℝ) (hr : Irrational r) (N : ℕ) :
    ∃ n ≥ N, n • (r : UnitAddCircle) ∈
      Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ) := by
  let a : UnitAddCircle := (r : UnitAddCircle)
  let U : Set UnitAddCircle :=
    (fun t : UnitAddCircle ↦ N • a + t) ⁻¹' Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)
  have hdense : DenseRange (fun n : ℕ ↦ n • a) := by
    -- Irrationality turns the natural orbit of `a` into a dense subset of the circle.
    rw [← denseRange_zsmul_iff_nsmul, AddCircle.denseRange_zsmul_coe_iff]
    simpa [a] using hr
  have hU_open : IsOpen U := by
    -- Translating an open ball preserves openness.
    dsimp [U]
    exact (Metric.isOpen_ball).preimage (continuous_const.add continuous_id)
  have hU_nonempty : U.Nonempty := by
    -- Translating the antipode back gives an explicit point in the preimage.
    refine ⟨((1 / 2 : ℝ) : UnitAddCircle) - N • a, ?_⟩
    change N • a + (((1 / 2 : ℝ) : UnitAddCircle) - N • a) ∈
        Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Metric.mem_ball_self (show 0 < (1 / 8 : ℝ) by norm_num) :
        ((1 / 2 : ℝ) : UnitAddCircle) ∈
          Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ))
  obtain ⟨m, hm⟩ := hdense.exists_mem_open hU_open hU_nonempty
  refine ⟨N + m, Nat.le_add_right N m, ?_⟩
  -- Repackage the dense hit as a large orbit time.
  change N • a + m • a ∈ Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ) at hm
  simpa [a, add_nsmul] using hm

/-- Helper for Remark 20.27: translating the quarter-arc pulls it back to a closed ball centered
at the opposite point. -/
lemma quarterArc_preimage_add_eq_closedBall
    (t : UnitAddCircle) :
    (fun x : UnitAddCircle ↦ x + t) ⁻¹' addCircleQuarterArc =
      Metric.closedBall (-t) (1 / 8 : ℝ) := by
  -- Normalize the translation preimage using the closed-ball transport formula.
  simpa [addCircleQuarterArc, sub_eq_add_neg] using
    (Metric.preimage_add_right_closedBall t (0 : UnitAddCircle) (1 / 8 : ℝ))

/-- Helper for Remark 20.27: translation amounts within `1 / 8` of the antipode move the
quarter-arc to a disjoint closed ball. -/
lemma quarterArcClosedBall_disjoint_of_mem_oppositeBall
    (t : UnitAddCircle)
    (ht : t ∈ Metric.ball ((1 / 2 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)) :
    Disjoint (Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ))
      (Metric.closedBall (-t) (1 / 8 : ℝ)) := by
  have hhalf : dist (0 : UnitAddCircle) ((1 / 2 : ℝ) : UnitAddCircle) = 1 / 2 := by
    -- The point `1 / 2` is the antipode of `0` on the additive circle.
    simpa [dist_eq_norm] using (AddCircle.norm_half_period_eq (p := (1 : ℝ)))
  have hdist : (1 / 4 : ℝ) < dist (0 : UnitAddCircle) t := by
    -- A point inside the antipodal `1 / 8`-ball stays more than `1 / 4` from `0`.
    have htriangle :
        dist (0 : UnitAddCircle) ((1 / 2 : ℝ) : UnitAddCircle) ≤
          dist (0 : UnitAddCircle) t + dist t ((1 / 2 : ℝ) : UnitAddCircle) :=
      dist_triangle _ _ _
    have hball : dist t ((1 / 2 : ℝ) : UnitAddCircle) < 1 / 8 := ht
    linarith
  have hdist_neg : dist (0 : UnitAddCircle) (-t) = dist (0 : UnitAddCircle) t := by
    -- Negation preserves the distance from `0`.
    simp [dist_eq_norm]
  -- Two closed balls of radius `1 / 8` are disjoint once their centers are more than `1 / 4`
  -- apart.
  refine Metric.closedBall_disjoint_closedBall ?_
  rw [hdist_neg]
  linarith

/-- Helper for Remark 20.27: if the orbit lands near the antipode, then the quarter-arc
self-correlation term vanishes. -/
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
    -- Collapse the iterate of a translation to translation by `n • r`.
    simpa [t] using (add_right_iterate (r : UnitAddCircle) n)
  have hdisj :
      Disjoint (Metric.closedBall (0 : UnitAddCircle) (1 / 8 : ℝ))
        (Metric.closedBall (-t) (1 / 8 : ℝ)) :=
    quarterArcClosedBall_disjoint_of_mem_oppositeBall t (by simpa [t] using hn)
  -- After normalizing the iterate and the preimage, the correlation is the measure of an empty
  -- intersection.
  rw [hIter, quarterArc_preimage_add_eq_closedBall, addCircleQuarterArc]
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, measure_empty]

/-- Helper for Remark 20.27: the quarter-arc self-correlation sequence of an irrational circle
rotation cannot converge to the product limit required by strong mixing. -/
theorem irrational_addCircle_rotation_quarterArc_selfCorrelation_not_tendsto
    (r : ℝ) (hr : Irrational r) :
    ¬ Filter.Tendsto
      (fun n : ℕ ↦
        volume
          (addCircleQuarterArc ∩
            (((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹' addCircleQuarterArc)))
      Filter.atTop
      (nhds (volume addCircleQuarterArc * volume addCircleQuarterArc)) := by
  have hquarterPos : 0 < volume addCircleQuarterArc := by
    -- A closed ball of positive radius in `UnitAddCircle` has positive measure.
    simpa [addCircleQuarterArc] using
      (Metric.measure_closedBall_pos (μ := (volume : Measure UnitAddCircle))
        (0 : UnitAddCircle) (show 0 < (1 / 8 : ℝ) by norm_num))
  have hlimitPos : 0 < volume addCircleQuarterArc * volume addCircleQuarterArc := by
    -- The limiting product is positive because each marginal measure is positive.
    exact ENNReal.mul_pos hquarterPos.ne' hquarterPos.ne'
  intro htendsto
  have hEventuallyPos :
      ∀ᶠ n in Filter.atTop,
        0 <
          volume
            (addCircleQuarterArc ∩
              (((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹'
                addCircleQuarterArc)) := by
    -- Convergence to a positive limit forces eventual positivity of the terms.
    exact htendsto.eventually (Ioi_mem_nhds hlimitPos)
  rcases Filter.eventually_atTop.1 hEventuallyPos with ⟨N, hN⟩
  obtain ⟨n, hnN, hn⟩ := exists_ge_nsmul_mem_oppositeBall r hr N
  have hzero :
      volume
        (addCircleQuarterArc ∩
          (((fun x : UnitAddCircle ↦ x + (r : UnitAddCircle))^[n]) ⁻¹'
            addCircleQuarterArc)) = 0 :=
    iterateSelfCorrelation_eq_zero_of_nsmul_mem_oppositeBall r hn
  exact (hN n hnN).ne' hzero

/-- Helper for Remark 20.27: an irrational circle rotation is not strongly mixing. -/
theorem irrational_addCircle_rotation_not_stronglyMixing
    (r : ℝ) (hr : Irrational r) :
    ¬ IsStronglyMixing ((· + (r : UnitAddCircle))) volume := by
  -- Route correction: instead of importing the later example, install the quarter-arc witness
  -- locally and contradict the strong-mixing self-correlation limit on that set.
  intro hmix
  exact irrational_addCircle_rotation_quarterArc_selfCorrelation_not_tendsto r hr <|
    isStronglyMixing_tendsto_measure_inter_preimage_iterate hmix
      measurableSet_addCircleQuarterArc measurableSet_addCircleQuarterArc

-- Proof sketch: use the standard irrational-rotation ergodicity criterion for the ergodic half,
-- and the later stable Chapter 20 quarter-arc counterexample for the non-mixing half.
/-- An irrational rotation on the circle is ergodic but not mixing. -/
theorem irrational_mod_one_rotation_ergodic_not_mixing :
    Ergodic ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle ∧
      ¬ IsStronglyMixing ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle := by
  refine ⟨?_, ?_⟩
  · -- `π` is irrational, so the circle rotation is ergodic.
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using
      ((mod_one_rotation_ergodic_iff_irrational Real.pi).2 irrational_pi)
  · -- Use the local quarter-arc obstruction to strong mixing for irrational rotations.
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using
      irrational_addCircle_rotation_not_stronglyMixing Real.pi irrational_pi
