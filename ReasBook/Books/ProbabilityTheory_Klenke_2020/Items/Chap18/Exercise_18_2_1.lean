/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_55
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
variable [CompleteSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
/-- Helper for Exercise 18.2.1: a coupling whose first transport moment is strictly below `r ^ 2`
forces the Lévy--Prokhorov distance to be at most `r`. -/
lemma levyProkhorovDist_le_of_couplingCost_lt_sq
    {P Q : ProbabilityMeasure E} {π : ProbabilityMeasure (E × E)} {r : ℝ}
    (hr : 0 < r) (hπ : IsCoupling π P Q)
    (hcost :
      ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2) ∂(π : Measure (E × E)) <
        ENNReal.ofReal (r ^ 2)) :
    levyProkhorovDist (P : Measure E) (Q : Measure E) ≤ r := by
  -- Control every measurable set through the coupling and a Markov tail bound.
  refine levyProkhorovDist_le_of_forall_le (μ := (P : Measure E)) (ν := (Q : Measure E))
      (δ := r) hr.le ?_
  intro ε B hε B_mble
  let bad : Set (E × E) := {z | r ≤ dist z.1 z.2}
  have hdist_meas : Measurable (fun z : E × E ↦ dist z.1 z.2) :=
    (continuous_fst.dist continuous_snd).measurable
  have hbad_mble : MeasurableSet bad := by
    change MeasurableSet ((fun z : E × E ↦ dist z.1 z.2) ⁻¹' Set.Ici r)
    exact hdist_meas measurableSet_Ici
  have hsubset : Prod.fst ⁻¹' B ⊆ Prod.snd ⁻¹' Metric.thickening ε B ∪ bad := by
    intro z hz
    by_cases hzthick : z.2 ∈ Metric.thickening ε B
    · exact Or.inl hzthick
    · right
      have hzB : z.1 ∈ B := hz
      have hdist : ε ≤ dist z.2 z.1 := by
        by_contra hlt
        have hlt' : dist z.2 z.1 < ε := by linarith
        exact hzthick <| Metric.mem_thickening_iff.mpr ⟨z.1, hzB, hlt'⟩
      simpa [dist_comm] using le_trans hε.le hdist
  have hfst :
      (π : Measure (E × E)) (Prod.fst ⁻¹' B) = (P : Measure E) B := by
    calc
      (π : Measure (E × E)) (Prod.fst ⁻¹' B) = (π : Measure (E × E)).fst B := by
        rw [Measure.fst_apply B_mble]
      _ = (P : Measure E) B := by
        simpa using congrArg (fun μ : Measure E ↦ μ B) hπ.1
  have hsnd :
      (π : Measure (E × E)) (Prod.snd ⁻¹' Metric.thickening ε B) =
        (Q : Measure E) (Metric.thickening ε B) := by
    calc
      (π : Measure (E × E)) (Prod.snd ⁻¹' Metric.thickening ε B) =
          (π : Measure (E × E)).snd (Metric.thickening ε B) := by
        rw [Measure.snd_apply Metric.isOpen_thickening.measurableSet]
      _ = (Q : Measure E) (Metric.thickening ε B) := by
        simpa using congrArg (fun μ : Measure E ↦ μ (Metric.thickening ε B)) hπ.2
  have hmeasCost :
      Measurable (fun z : E × E ↦ ENNReal.ofReal (dist z.1 z.2)) := by
    exact hdist_meas.ennreal_ofReal
  have hmarkov :
      ENNReal.ofReal r * (π : Measure (E × E)) bad ≤
        ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2) ∂(π : Measure (E × E)) := by
    simpa [bad, hr.le] using
      (MeasureTheory.mul_meas_ge_le_lintegral hmeasCost (ENNReal.ofReal r))
  have hbad_lt : (π : Measure (E × E)) bad < ENNReal.ofReal r := by
    have hr_ne_zero : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
    have hmul_lt :
        ENNReal.ofReal r * (π : Measure (E × E)) bad <
          ENNReal.ofReal r * ENNReal.ofReal r := by
      refine lt_of_le_of_lt hmarkov ?_
      simpa [pow_two, ENNReal.ofReal_mul, hr.le] using hcost
    exact (ENNReal.mul_lt_mul_iff_right hr_ne_zero ENNReal.ofReal_ne_top).1 hmul_lt
  -- Rewrite the marginal bounds through `π` and absorb the bad set by Markov.
  calc
    (P : Measure E) B = (π : Measure (E × E)) (Prod.fst ⁻¹' B) := hfst.symm
    _ ≤ (π : Measure (E × E)) (Prod.snd ⁻¹' Metric.thickening ε B) + (π : Measure (E × E)) bad :=
      (measure_mono hsubset).trans <| measure_union_le _ _
    _ = (Q : Measure E) (Metric.thickening ε B) + (π : Measure (E × E)) bad := by rw [hsnd]
    _ ≤ (Q : Measure E) (Metric.thickening ε B) + ENNReal.ofReal r :=
      add_le_add_right hbad_lt.le _
    _ ≤ (Q : Measure E) (Metric.thickening ε B) + ENNReal.ofReal ε :=
      add_le_add_right (ENNReal.ofReal_le_ofReal hε.le) _

omit [CompleteSpace E] in
/-- Helper for Exercise 18.2.1: any strict upper bound `r ^ 2` on the Wasserstein infimum already
forces the Lévy--Prokhorov distance to be at most `r`. -/
lemma levyProkhorovDist_le_of_wassersteinDistance_lt_sq
    {P Q : ProbabilityMeasure E} {r : ℝ} (hr : 0 < r)
    (hw : wassersteinDistance P Q < ENNReal.ofReal (r ^ 2)) :
    levyProkhorovDist (P : Measure E) (Q : Measure E) ≤ r := by
  -- Unpack one coupling witness from the defining `sInf`.
  obtain ⟨c, ⟨π, hπ, hc⟩, hc_lt⟩ := sInf_lt_iff.mp hw
  subst hc
  exact levyProkhorovDist_le_of_couplingCost_lt_sq hr hπ hc_lt

-- Proof sketch: apply Strassen's coupling characterization of the Lévy--Prokhorov distance and
-- then use Markov's inequality on the transport-cost random variable under a coupling realizing
-- the Wasserstein infimum. Rearranging the resulting estimate gives the squared form of the
-- textbook square-root bound.
omit [CompleteSpace E] in
/-- Companion square-root estimate for Exercise 18.2.1 (1): for probability measures on a Polish
metric space, the
Lévy--Prokhorov distance is bounded above by the square root of the Wasserstein transport cost,
written here in the equivalent squared form over `ℝ≥0∞`. -/
theorem levyProkhorovDist_sq_le_wassersteinDistance
    (P Q : ProbabilityMeasure E) :
    ENNReal.ofReal (levyProkhorovDist (P : Measure E) (Q : Measure E)) ^ (2 : ℕ) ≤
      wassersteinDistance P Q := by
  by_cases hzero : levyProkhorovDist (P : Measure E) (Q : Measure E) = 0
  · -- The zero-distance case is immediate.
    simp [hzero]
  -- Otherwise, argue by contradiction and choose an intermediate radius.
  set d := levyProkhorovDist (P : Measure E) (Q : Measure E)
  have hd_nonneg : 0 ≤ d := by
    simp [d, MeasureTheory.levyProkhorovDist]
  have hd_ne_zero : d ≠ 0 := by
    simpa [d] using hzero
  have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg hd_ne_zero.symm
  by_contra h
  have hsq : ¬ ENNReal.ofReal (d ^ 2) ≤ wassersteinDistance P Q := by
    simpa [pow_two, ENNReal.ofReal_mul, hd_nonneg] using h
  have hw_lt : wassersteinDistance P Q < ENNReal.ofReal (d ^ 2) := lt_of_not_ge hsq
  have hw_ne_top : wassersteinDistance P Q ≠ ∞ := by
    exact ne_of_lt (lt_of_lt_of_le hw_lt le_top)
  set w := (wassersteinDistance P Q).toReal with hwdef
  have hw_nonneg : 0 ≤ w := by
    rw [hwdef]
    exact ENNReal.toReal_nonneg
  have hw_real_lt : w < d ^ 2 := by
    have htoReal :
        (wassersteinDistance P Q).toReal < (ENNReal.ofReal (d ^ 2)).toReal := by
      exact (ENNReal.toReal_lt_toReal hw_ne_top ENNReal.ofReal_ne_top).2 hw_lt
    simpa [hwdef, ENNReal.toReal_ofReal, sq_nonneg d] using htoReal
  set r := (Real.sqrt w + d) / 2 with hrdef
  have hsqrt_lt_d : Real.sqrt w < d := by
    nlinarith [Real.sq_sqrt hw_nonneg, hw_real_lt, hd_pos]
  have hr_pos : 0 < r := by
    rw [hrdef]
    nlinarith [Real.sqrt_nonneg w, hd_pos]
  have hr_lt_d : r < d := by
    rw [hrdef]
    nlinarith [hsqrt_lt_d]
  have hsqrt_lt_r : Real.sqrt w < r := by
    rw [hrdef]
    nlinarith [hsqrt_lt_d]
  have hw_lt_rsq : wassersteinDistance P Q < ENNReal.ofReal (r ^ 2) := by
    have hw_real_lt_rsq : w < r ^ 2 := by
      have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
      nlinarith [Real.sq_sqrt hw_nonneg, hsqrt_lt_r, Real.sqrt_nonneg w, hr_nonneg]
    have hlt_ofReal : ENNReal.ofReal w < ENNReal.ofReal (r ^ 2) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hw_nonneg).2 hw_real_lt_rsq
    simpa [hwdef, ENNReal.ofReal_toReal hw_ne_top] using hlt_ofReal
  have hle : d ≤ r := levyProkhorovDist_le_of_wassersteinDistance_lt_sq hr_pos hw_lt_rsq
  exact not_lt_of_ge hle hr_lt_d

variable [BoundedSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]
  [BoundedSpace E] in
/-- Helper for Exercise 18.2.1: thickening a superlevel set of a `1`-Lipschitz test function by
`ε` is contained in the corresponding superlevel set of the shifted test function `g + ε`. -/
lemma thickening_superlevel_subset_add_le
    {g : BoundedContinuousFunction E ℝ} (hLip : LipschitzWith 1 g) {ε t : ℝ} :
    Metric.thickening ε {x | t ≤ g x} ⊆ {x | t ≤ g x + ε} := by
  intro x hx
  rcases Metric.mem_thickening_iff.mp hx with ⟨y, hy, hxy⟩
  -- Proof comment: a point within `ε` of a `t`-superlevel point stays in the `t`-superlevel of
  -- the shifted function because `g` is `1`-Lipschitz.
  have hdist_metric : dist (g y) (g x) ≤ dist y x := by
    simpa [edist_dist] using hLip y x
  have hdist : |g y - g x| ≤ ε := by
    have : dist (g y) (g x) ≤ ε :=
      hdist_metric.trans <| le_of_lt (by simpa [dist_comm] using hxy)
    simpa [Real.dist_eq] using this
  have hsub : g y - g x ≤ ε := (abs_le.mp hdist).2
  have hy' : t ≤ g y := by simpa using hy
  have hgy : g y ≤ g x + ε := by linarith
  exact le_trans hy' hgy

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] in
/-- Helper for Exercise 18.2.1: subtracting `sInf (Set.range f)` from a bounded Lipschitz test
preserves the `1`-Lipschitz constant, makes the function nonnegative, and bounds its norm by
`Metric.diam (Set.univ : Set E)`. -/
lemma normalizedLipschitzTest_bounds
    (f : BoundedContinuousFunction E ℝ) (hf : LipschitzWith 1 f) :
    let c : ℝ := sInf (Set.range f)
    let g : BoundedContinuousFunction E ℝ := f - BoundedContinuousFunction.const E c
    LipschitzWith 1 g ∧ (∀ x, 0 ≤ g x) ∧ ‖g‖ ≤ Metric.diam (Set.univ : Set E) := by
  let c : ℝ := sInf (Set.range f)
  let g : BoundedContinuousFunction E ℝ := f - BoundedContinuousFunction.const E c
  have h_range_f_bdd : Bornology.IsBounded (Set.range f) := by
    refine isBounded_iff_forall_norm_le.mpr ?_
    refine ⟨‖f‖, ?_⟩
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact BoundedContinuousFunction.norm_coe_le_norm f x
  have hLip_g : LipschitzWith 1 g := by
    -- Proof comment: subtracting a constant does not change pairwise differences.
    simpa [g] using hf.sub (LipschitzWith.const c)
  have h_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    -- Proof comment: `c = sInf (Set.range f)` is a lower bound for the range of `f`.
    have hc_le : c ≤ f x := by
      exact csInf_le h_range_f_bdd.bddBelow (show f x ∈ Set.range f by exact ⟨x, rfl⟩)
    simp [g, c, sub_nonneg.mpr hc_le]
  have h_range_bdd : Bornology.IsBounded (Set.range g) := by
    refine isBounded_iff_forall_norm_le.mpr ?_
    refine ⟨‖g‖, ?_⟩
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact BoundedContinuousFunction.norm_coe_le_norm g x
  have hsInf_nonneg : 0 ≤ sInf (Set.range g) := by
    refine Real.sInf_nonneg ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact h_nonneg x
  have hsInf_nonpos : sInf (Set.range g) ≤ 0 := by
    -- Proof comment: points of the range of `f` can approach its infimum arbitrarily closely, so
    -- the shifted range of `g` approaches `0` from above.
    by_cases hE : Nonempty E
    · let _ : Nonempty E := hE
      apply le_of_forall_pos_le_add
      intro ε hε
      rcases Real.lt_sInf_add_pos (Set.range_nonempty f) hε with ⟨y, hy_mem, hy⟩
      rcases hy_mem with ⟨x, rfl⟩
      have hxε : g x < ε := by
        simp [g, c] at hy ⊢
        linarith
      have hcs : sInf (Set.range g) ≤ g x := by
        exact csInf_le h_range_bdd.bddBelow (show g x ∈ Set.range g by exact ⟨x, rfl⟩)
      have : sInf (Set.range g) ≤ ε := by
        linarith
      simpa using this
    · have h_range : Set.range g = ∅ := by
        ext y
        constructor
        · intro hy
          rcases hy with ⟨x, rfl⟩
          exact (hE ⟨x⟩).elim
        · intro hy
          cases hy
      simp [h_range]
  have hsInf_eq : sInf (Set.range g) = 0 := le_antisymm hsInf_nonpos hsInf_nonneg
  have h_diam_range :
      Metric.diam (Set.range g) ≤ Metric.diam (Set.univ : Set E) := by
    have h_univ_bdd : Bornology.IsBounded (Set.univ : Set E) := by
      simpa using (Bornology.isBounded_univ (α := E)).2 (show BoundedSpace E from inferInstance)
    simpa [Set.image_univ] using hLip_g.diam_image_le (Set.univ : Set E) h_univ_bdd
  have h_norm_bound : ‖g‖ ≤ Metric.diam (Set.univ : Set E) := by
    refine (BoundedContinuousFunction.norm_le Metric.diam_nonneg).2 ?_
    intro x
    -- Proof comment: every function value lies between the infimum and supremum of the shifted
    -- range, and the infimum is `0`.
    have hx_mem : g x ∈ Set.range g := ⟨x, rfl⟩
    have hx_le_sSup : g x ≤ sSup (Set.range g) := (h_range_bdd.subset_Icc_sInf_sSup hx_mem).2
    have hsSup_le_diam : sSup (Set.range g) ≤ Metric.diam (Set.range g) := by
      rw [Real.diam_eq h_range_bdd, hsInf_eq]
      linarith
    have hx_le_diam : g x ≤ Metric.diam (Set.univ : Set E) := by
      calc
        g x ≤ sSup (Set.range g) := hx_le_sSup
        _ ≤ Metric.diam (Set.range g) := hsSup_le_diam
        _ ≤ Metric.diam (Set.univ : Set E) := h_diam_range
    simpa [Real.norm_eq_abs, abs_of_nonneg (h_nonneg x)] using hx_le_diam
  exact ⟨hLip_g, h_nonneg, h_norm_bound⟩

omit [CompleteSpace E] [SecondCountableTopology E] [BoundedSpace E] in
/-- Helper for Exercise 18.2.1: a nonnegative `1`-Lipschitz bounded continuous test function with
`‖g‖ ≤ M` has expectations differing by at most `(M + 1) * δ` whenever `δ` strictly exceeds the
Lévy--Prokhorov distance. -/
lemma integral_le_integral_add_mul_of_levyProkhorov
    {P Q : ProbabilityMeasure E} {g : BoundedContinuousFunction E ℝ} {M δ : ℝ}
    (hLip : LipschitzWith 1 g) (h_nonneg : ∀ x, 0 ≤ g x) (h_norm : ‖g‖ ≤ M)
    (hδ : levyProkhorovDist (P : Measure E) (Q : Measure E) < δ) :
    ∫ x, g x ∂(P : Measure E) ≤ ∫ x, g x ∂(Q : Measure E) + (M + 1) * δ := by
  have hLP_nonneg : 0 ≤ levyProkhorovDist (P : Measure E) (Q : Measure E) := by
    simp [MeasureTheory.levyProkhorovDist]
  have hδ_pos : 0 < δ := lt_of_le_of_lt hLP_nonneg hδ
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hLPEDist :
      levyProkhorovEDist (P : Measure E) (Q : Measure E) < ENNReal.ofReal δ := by
    refine (ENNReal.toReal_lt_toReal (levyProkhorovEDist_ne_top _ _) ENNReal.ofReal_ne_top).1 ?_
    simpa [MeasureTheory.levyProkhorovDist, ENNReal.toReal_ofReal hδ_nonneg] using hδ
  have hbase :=
    BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt
      (P : Measure E) (Q : Measure E) hδ_pos hLPEDist g (Filter.Eventually.of_forall h_nonneg)
  let gShift : BoundedContinuousFunction E ℝ := g + BoundedContinuousFunction.const E δ
  have hshift_nonneg : 0 ≤ᵐ[(Q : Measure E)] fun x ↦ gShift x := by
    exact Filter.Eventually.of_forall (fun x ↦ by
      change 0 ≤ g x + δ
      exact add_nonneg (h_nonneg x) hδ_nonneg)
  have hshift_upper : (fun x ↦ gShift x) ≤ᵐ[(Q : Measure E)] fun _ ↦ M + δ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hx_le : g x ≤ ‖g‖ := BoundedContinuousFunction.apply_le_norm g x
    simp [gShift]
    linarith
  have hthick_int :
      IntegrableOn
        (fun t : ℝ ↦ (Q : Measure E).real (Metric.thickening δ {a | t ≤ g a}))
        (Set.Ioc 0 ‖g‖) := by
    apply Measure.integrableOn_of_bounded (M := (Q : Measure E).real Set.univ)
        measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      intro s t hst
      exact measure_mono <|
        Metric.thickening_subset_of_subset δ (fun _ h ↦ hst.trans h)
    · apply Filter.Eventually.of_forall fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (Set.subset_univ _)
  have hshift_small_int :
      IntegrableOn (fun t : ℝ ↦ (Q : Measure E).real {a | t ≤ gShift a}) (Set.Ioc 0 ‖g‖) := by
    apply Measure.integrableOn_of_bounded (M := (Q : Measure E).real Set.univ)
        measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      intro s t hst
      exact measure_mono (fun _ h ↦ hst.trans h)
    · apply Filter.Eventually.of_forall fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (Set.subset_univ _)
  have hshift_big_int :
      IntegrableOn (fun t : ℝ ↦ (Q : Measure E).real {a | t ≤ gShift a}) (Set.Ioc 0 (M + δ)) := by
    apply Measure.integrableOn_of_bounded (M := (Q : Measure E).real Set.univ)
        measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      intro s t hst
      exact measure_mono (fun _ h ↦ hst.trans h)
    · apply Filter.Eventually.of_forall fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (Set.subset_univ _)
  have htail_le :
      ∫ t in Set.Ioc 0 ‖g‖, (Q : Measure E).real (Metric.thickening δ {a | t ≤ g a}) ≤
        ∫ t in Set.Ioc 0 ‖g‖, (Q : Measure E).real {a | t ≤ gShift a} := by
    refine setIntegral_mono_on hthick_int hshift_small_int measurableSet_Ioc ?_
    intro t ht
    exact measureReal_mono (thickening_superlevel_subset_add_le hLip)
  have h_end : ‖g‖ ≤ M + δ := by
    linarith
  have hshift_nonneg_set :
      0 ≤ᵐ[volume.restrict (Set.Ioc 0 (M + δ))]
        fun t : ℝ ↦ (Q : Measure E).real {a | t ≤ gShift a} := by
    exact Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg
  have htail_extend :
      ∫ t in Set.Ioc 0 ‖g‖, (Q : Measure E).real {a | t ≤ gShift a} ≤
        ∫ t in Set.Ioc 0 (M + δ), (Q : Measure E).real {a | t ≤ gShift a} := by
    refine setIntegral_mono_set hshift_big_int hshift_nonneg_set ?_
    exact Filter.Eventually.of_forall (Set.Ioc_subset_Ioc le_rfl h_end)
  have hlayer :
      ∫ t in Set.Ioc 0 (M + δ), (Q : Measure E).real {a | t ≤ gShift a} =
        ∫ x, gShift x ∂(Q : Measure E) := by
    symm
    exact (gShift.integrable (Q : Measure E)).integral_eq_integral_Ioc_meas_le
      hshift_nonneg hshift_upper
  have hshift_int :
      ∫ x, gShift x ∂(Q : Measure E) = ∫ x, g x ∂(Q : Measure E) + δ := by
    -- Proof comment: integrating a constant over a probability measure contributes exactly that
    -- constant.
    simpa [gShift, probReal_univ] using
      (g.integral_add_const (μ := (Q : Measure E)) δ)
  have hthick_bound :
      ∫ t in Set.Ioc 0 ‖g‖, (Q : Measure E).real (Metric.thickening δ {a | t ≤ g a}) ≤
        ∫ x, g x ∂(Q : Measure E) + δ := by
    exact htail_le.trans (htail_extend.trans <| hlayer.le.trans_eq hshift_int)
  have hmul : δ * ‖g‖ ≤ δ * M := mul_le_mul_of_nonneg_left h_norm hδ_nonneg
  -- Proof comment: the Prokhorov layer-cake estimate and the shifted upper cutoff together
  -- produce the linear `(M + 1) * δ` bound.
  calc
    ∫ x, g x ∂(P : Measure E)
      ≤ (∫ t in Set.Ioc 0 ‖g‖, (Q : Measure E).real (Metric.thickening δ {a | t ≤ g a})) +
          δ * ‖g‖ := hbase
    _ ≤ (∫ x, g x ∂(Q : Measure E) + δ) + δ * ‖g‖ := by
      gcongr
    _ ≤ (∫ x, g x ∂(Q : Measure E) + δ) + δ * M := by
      simpa [add_assoc] using add_le_add_left hmul (∫ x, g x ∂(Q : Measure E) + δ)
    _ = ∫ x, g x ∂(Q : Measure E) + (M + 1) * δ := by ring

-- Proof sketch: when `E` is bounded, use a coupling with Prohorov error close to
-- `levyProkhorovDist P Q`. The transport cost is controlled by `Metric.diam univ` on the matched
-- part of the coupling and by an additional `1` times the mismatch mass, giving the linear bound.
/-- Exercise 18.2.1: if the metric space `E` has finite diameter, then the Wasserstein
distance is bounded above by `(diam(E) + 1)` times the Lévy--Prokhorov distance, with the
Wasserstein metric written as its defining coupling-cost infimum. -/
theorem wassersteinDistance_le_diam_add_one_mul_levyProkhorovDist
    (P Q : ProbabilityMeasure E) :
    wassersteinDistance P Q ≤
      ENNReal.ofReal
        ((Metric.diam (Set.univ : Set E) + 1) *
          levyProkhorovDist (P : Measure E) (Q : Measure E)) := by
  rw [wassersteinDistance_eq_sSup_lipschitz]
  refine ENNReal.ofReal_le_ofReal ?_
  let C : ℝ := Metric.diam (Set.univ : Set E) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith [Metric.diam_nonneg (s := (Set.univ : Set E))]
  have hLP_nonneg : 0 ≤ levyProkhorovDist (P : Measure E) (Q : Measure E) := by
    simp [MeasureTheory.levyProkhorovDist]
  -- Proof comment: after dualizing Wasserstein, bound each `1`-Lipschitz witness by first
  -- normalizing it and then applying the quantitative Lévy--Prokhorov estimate.
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  refine Real.sSup_le ?_ ?_
  · intro r hr
    rcases hr with ⟨f, hf, rfl⟩
    let c : ℝ := sInf (Set.range f)
    let g : BoundedContinuousFunction E ℝ := f - BoundedContinuousFunction.const E c
    have hg_bounds :
        LipschitzWith 1 g ∧ (∀ x, 0 ≤ g x) ∧ ‖g‖ ≤ Metric.diam (Set.univ : Set E) := by
      simpa [c, g] using normalizedLipschitzTest_bounds (E := E) f hf
    rcases hg_bounds with ⟨hgLip, hgNonneg, hgNorm⟩
    have hPg :
        ∫ x, g x ∂(P : Measure E) = ∫ x, f x ∂(P : Measure E) - c := by
      simpa [g, c, sub_eq_add_neg, probReal_univ] using
        (f.integral_add_const (μ := (P : Measure E)) (-c))
    have hQg :
        ∫ x, g x ∂(Q : Measure E) = ∫ x, f x ∂(Q : Measure E) - c := by
      simpa [g, c, sub_eq_add_neg, probReal_univ] using
        (f.integral_add_const (μ := (Q : Measure E)) (-c))
    have hdiff :
        ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) =
          ∫ x, g x ∂(P : Measure E) - ∫ x, g x ∂(Q : Measure E) := by
      linarith
    have hδ :
        levyProkhorovDist (P : Measure E) (Q : Measure E) <
          levyProkhorovDist (P : Measure E) (Q : Measure E) + ε / C := by
      have : 0 < ε / C := by positivity
      linarith
    have hbound :=
      integral_le_integral_add_mul_of_levyProkhorov
        (P := P) (Q := Q) (g := g) (M := Metric.diam (Set.univ : Set E))
        hgLip hgNonneg hgNorm hδ
    have hmain :
        ∫ x, g x ∂(P : Measure E) - ∫ x, g x ∂(Q : Measure E) ≤
          (Metric.diam (Set.univ : Set E) + 1) *
            (levyProkhorovDist (P : Measure E) (Q : Measure E) + ε / C) := by
      linarith
    calc
      ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)
        = ∫ x, g x ∂(P : Measure E) - ∫ x, g x ∂(Q : Measure E) := hdiff
      _ ≤ (Metric.diam (Set.univ : Set E) + 1) *
            (levyProkhorovDist (P : Measure E) (Q : Measure E) + ε / C) := hmain
      _ = C * levyProkhorovDist (P : Measure E) (Q : Measure E) + ε := by
        field_simp [C, hC_pos.ne']
        ring
  · have : 0 ≤ ε := hε.le
    positivity

end ProbabilityTheory
