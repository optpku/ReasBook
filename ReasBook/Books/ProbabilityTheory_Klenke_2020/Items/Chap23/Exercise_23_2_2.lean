/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Lemma_23_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal

noncomputable section

/-- Helper for Exercise 23.2.2: the positive-parameter filter is nontrivial because `ε > 0`
approaches `0` from the right along a nonempty neighborhood basis. -/
private instance positiveParameterFilter_neBot :
    NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  rw [positiveParameterFilter]
  exact (show NeBot (𝓝[>] (0 : ℝ)) from inferInstance).comap_of_range_mem (by
    simpa [PositiveParameter, Subtype.range_coe] using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))

/-- Helper for Exercise 23.2.2: every interval `(-∞, δ)` with `δ > 0` is a right-neighborhood of
`0`. -/
private theorem Iio_mem_nhdsWithin_right_zero {δ : ℝ} (hδ : 0 < δ) :
    Set.Iio δ ∈ 𝓝[>] (0 : ℝ) := by
  -- Proof comment: `0` belongs to `(-∞, δ)`, and intersecting with `Set.Ioi 0` keeps only the
  -- punctured interval `(0, δ)`.
  refine mem_nhdsWithin.2 ?_
  refine ⟨Set.Iio δ, isOpen_Iio, ?_, ?_⟩
  · simpa using hδ
  · intro x hx
    exact hx.1

/-- The Gaussian family `μ_ε = 𝒩(0, ε²)` from Exercise 23.2.2. -/
def smallVarianceGaussianFamily : PositiveProbabilityFamily ℝ :=
  fun ε ↦
    ⟨gaussianReal 0 ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩, inferInstance⟩

-- Proof sketch: unfold `smallVarianceGaussianFamily`; the statement is exactly its defining
-- equation.
/-- Evaluating `smallVarianceGaussianFamily` at `ε` gives the centered Gaussian law with variance
`ε²`. -/
theorem smallVarianceGaussianFamily_apply (ε : PositiveParameter) :
    (smallVarianceGaussianFamily ε : Measure ℝ) =
      gaussianReal 0 ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩ := by
  -- The family was defined by this exact Gaussian formula.
  rfl

/-- The rate function from Exercise 23.2.2, equal to `0` at the origin and `∞` away from `0`. -/
def zeroDiracRateFunction (x : ℝ) : ℝ≥0∞ :=
  if x = 0 then 0 else ⊤

-- Proof sketch: unfold `zeroDiracRateFunction`; when `x ≠ 0` the defining `if` takes the second
-- branch.
/-- Away from the origin, `zeroDiracRateFunction` is infinite. -/
theorem zeroDiracRateFunction_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    zeroDiracRateFunction x = ⊤ := by
  -- Unfold the definition and take the nonzero branch of the `if`.
  simp [zeroDiracRateFunction, hx]

/-- Helper for Exercise 23.2.2: enlarging the underlying set can only increase the scaled
logarithmic mass. -/
private theorem scaledLogMassAlong_mono
    (μ : PositiveParameter → Measure ℝ) {s t : Set ℝ} (hst : s ⊆ t) (ε : PositiveParameter) :
    scaledLogMassAlong μ id s ε ≤ scaledLogMassAlong μ id t ε := by
  -- Proof comment: expand the logarithmic mass once, then use monotonicity of measure and of
  -- `ENNReal.log`.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def]
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast (le_of_lt ε.2)
  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (measure_mono hst)) hε

/-- Helper for Exercise 23.2.2: the small-variance Gaussian is the pushforward of the standard
normal under the scaling map `x ↦ ε x`. -/
private theorem smallVarianceGaussianFamily_eq_mapStandardNormal (ε : PositiveParameter) :
    (smallVarianceGaussianFamily ε : Measure ℝ) =
      (gaussianReal 0 1).map (fun x : ℝ ↦ (ε : ℝ) * x) := by
  -- Proof comment: `gaussianReal_map_const_mul` already computes the variance change under
  -- scaling, so the family definition matches the standard-normal pushforward verbatim.
  simpa [smallVarianceGaussianFamily, mul_comm, mul_left_comm, mul_assoc] using
    (gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) (ε : ℝ)).symm

/-- Helper for Exercise 23.2.2: the standard normal is symmetric, so opposite tails have the same
mass. -/
private theorem standardNormal_Iic_neg_eq_Ici (t : ℝ) :
    (gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Iic (-t)) =
      (gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Ici t) := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hsymm : ν.map (fun x : ℝ ↦ -x) = ν := by
    simpa [ν] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  -- Proof comment: push the left tail through the symmetry map `x ↦ -x`, which turns it into the
  -- right tail at `t`.
  calc
    ν (Set.Iic (-t)) = (ν.map (fun x : ℝ ↦ -x)) (Set.Iic (-t)) := by rw [hsymm]
    _ = ν (Set.Ici t) := by
      rw [Measure.map_apply measurable_neg measurableSet_Iic]
      congr 1
      ext x
      simp

/-- Helper for Exercise 23.2.2: the standard normal assigns mass `1 / 2` to the positive
half-line. -/
private theorem standardNormal_positiveHalfline_mass :
    (gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Ioi (0 : ℝ)) = (1 / 2 : ℝ≥0∞) := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hIci : ν (Set.Ici 0) = ν (Set.Iic 0) := by
    simpa [ν] using (standardNormal_Iic_neg_eq_Ici 0).symm
  have hnoAtoms : NoAtoms ν := by
    simpa [ν] using
      (noAtoms_gaussianReal (μ := 0) (v := (1 : NNReal)) (by norm_num : (1 : NNReal) ≠ 0))
  have hIci_eq_Ioi : ν (Set.Ici 0) = ν (Set.Ioi 0) := by
    have hunion : Set.Ioi (0 : ℝ) ∪ ({(0 : ℝ)} : Set ℝ) = Set.Ici 0 := by
      ext x
      simp
    have hdisj : Disjoint (Set.Ioi (0 : ℝ)) ({(0 : ℝ)} : Set ℝ) := by
      rw [Set.disjoint_singleton_right]
      simp
    -- Proof comment: atomlessness at the origin removes the singleton from the closed half-line.
    calc
      ν (Set.Ici 0) = ν (Set.Ioi 0 ∪ ({(0 : ℝ)} : Set ℝ)) := by rw [hunion]
      _ = ν (Set.Ioi 0) + ν ({(0 : ℝ)} : Set ℝ) := by
            rw [measure_union hdisj (measurableSet_singleton (x := (0 : ℝ)))]
      _ = ν (Set.Ioi 0) := by
            simp [hnoAtoms.measure_singleton]
  have hsum : ν (Set.Iic 0) + ν (Set.Ioi 0) = 1 := by
    simpa using prob_add_prob_compl (μ := ν) measurableSet_Iic
  have htwice : ν (Set.Ioi 0) + ν (Set.Ioi 0) = 1 := by
    -- Proof comment: symmetry identifies the left and right half-lines, so the two complementary
    -- masses coincide.
    calc
      ν (Set.Ioi 0) + ν (Set.Ioi 0) = ν (Set.Ici 0) + ν (Set.Ici 0) := by
            rw [← hIci_eq_Ioi]
      _ = ν (Set.Ici 0) + ν (Set.Iic 0) := by rw [hIci]
      _ = ν (Set.Ioi 0) + ν (Set.Iic 0) := by rw [hIci_eq_Ioi]
      _ = 1 := by simpa [add_comm] using hsum
  have htwice_real : 2 * (ν (Set.Ioi 0)).toReal = 1 := by
    have htmp := congrArg ENNReal.toReal htwice
    simpa [ENNReal.toReal_add, measure_ne_top ν _, two_mul] using htmp
  have hreal : (ν (Set.Ioi 0)).toReal = (1 / 2 : ℝ) := by
    linarith
  exact
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _) (by simp)).mp <| by
      simpa using hreal

/-- Helper for Exercise 23.2.2: every `μ_ε` assigns mass `1 / 2` to the positive half-line. -/
private theorem smallVarianceGaussianFamily_positiveHalfline_mass (ε : PositiveParameter) :
    (smallVarianceGaussianFamily ε : Measure ℝ) (Set.Ioi (0 : ℝ)) = (1 / 2 : ℝ≥0∞) := by
  -- Proof comment: transport the event `(0, ∞)` through the positive scaling map `x ↦ ε x`.
  rw [smallVarianceGaussianFamily_eq_mapStandardNormal ε]
  rw [Measure.map_apply (measurable_const_mul (ε : ℝ)) measurableSet_Ioi]
  rw [Set.preimage_const_mul_Ioi₀ (0 : ℝ) ε.2]
  simpa using standardNormal_positiveHalfline_mass

/-- Helper for Exercise 23.2.2: the standard normal symmetric tail is bounded by the direct
Chernoff estimate `2 * exp (-t^2 / 2)`. -/
private theorem standardNormal_symmetricTail_real_le {t : ℝ} (ht : 0 < t) :
    (gaussianReal (0 : ℝ) (1 : NNReal)).real (Set.Iic (-t) ∪ Set.Ici t) ≤
      2 * Real.exp (-(t ^ 2) / 2) := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hIntRight :
      Integrable (fun x : ℝ ↦ Real.exp (t * x)) ν := by
    -- Proof comment: the standard-normal mgf is finite at every real slope.
    simpa [ν] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := (1 : NNReal)) (t := t))
  have hIntLeft :
      Integrable (fun x : ℝ ↦ Real.exp (-t * x)) ν := by
    -- Proof comment: the same mgf input controls the reflected left-tail slope.
    simpa [ν] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := (1 : NNReal)) (t := -t))
  have hRight :
      ν.real (Set.Ici t) ≤ Real.exp (-(t ^ 2) / 2) := by
    have hChernoff :
        ν.real (Set.Ici t) ≤ Real.exp (-t * t) * mgf id ν t := by
      -- Proof comment: Chernoff's inequality bounds the right tail at the optimizing slope `t`.
      simpa [ν, Set.Ici] using
        (measure_ge_le_exp_mul_mgf (μ := ν) (X := id) (ε := t) (t := t) ht.le hIntRight)
    calc
      ν.real (Set.Ici t) ≤ Real.exp (-t * t) * mgf id ν t := hChernoff
      _ = Real.exp (-(t ^ 2) / 2) := by
        -- Proof comment: evaluating the standard-normal mgf leaves the expected quadratic cost.
        rw [show ν = gaussianReal (0 : ℝ) (1 : NNReal) by rfl, mgf_id_gaussianReal,
          ← Real.exp_add]
        congr 1
        norm_num
        ring_nf
  have hLeft :
      ν.real (Set.Iic (-t)) ≤ Real.exp (-(t ^ 2) / 2) := by
    have hChernoff :
        ν.real (Set.Iic (-t)) ≤ Real.exp (-(-t) * (-t)) * mgf id ν (-t) := by
      -- Proof comment: the lower-tail Chernoff estimate matches the same quadratic exponent.
      simpa [ν, Set.Iic] using
        (measure_le_le_exp_mul_mgf (μ := ν) (X := id) (ε := -t) (t := -t)
          (by linarith) hIntLeft)
    calc
      ν.real (Set.Iic (-t)) ≤ Real.exp (-(-t) * (-t)) * mgf id ν (-t) := hChernoff
      _ = Real.exp (-(t ^ 2) / 2) := by
        -- Proof comment: the reflected slope produces the same mgf contribution as the right tail.
        rw [show ν = gaussianReal (0 : ℝ) (1 : NNReal) by rfl, mgf_id_gaussianReal,
          ← Real.exp_add]
        congr 1
        norm_num
        ring_nf
  -- Proof comment: the symmetric tail is the union of the left and right tails, so the total mass
  -- is bounded by the sum of the two one-sided Chernoff estimates.
  calc
    ν.real (Set.Iic (-t) ∪ Set.Ici t) ≤ ν.real (Set.Iic (-t)) + ν.real (Set.Ici t) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(t ^ 2) / 2) + Real.exp (-(t ^ 2) / 2) := add_le_add hLeft hRight
    _ = 2 * Real.exp (-(t ^ 2) / 2) := by ring

/-- Helper for Exercise 23.2.2: outside a fixed ball, `μ_ε` is bounded by an explicit Gaussian tail
estimate once `ε ≤ r`. -/
private theorem smallVarianceGaussianFamily_tailMass_complBall_le {r : ℝ} (hr : 0 < r)
    {ε : PositiveParameter} (hεr : (ε : ℝ) ≤ r) :
    (smallVarianceGaussianFamily ε : Measure ℝ) ((Metric.ball 0 r)ᶜ) ≤
      ENNReal.ofReal (2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2))) := by
  -- Route correction: use the direct Gaussian Chernoff estimate, as in the sibling
  -- small-variance Gaussian exercise, instead of transporting through a standard-normal preimage.
  have hIntRight :
      Integrable (fun x : ℝ ↦ Real.exp ((r / (ε : ℝ) ^ 2) * x))
        (smallVarianceGaussianFamily ε) := by
    -- Proof comment: the Gaussian mgf is finite at every real slope, so the right-tail Chernoff
    -- bound is available at the optimizing slope `r / ε²`.
    simpa [smallVarianceGaussianFamily] using
      (integrable_exp_mul_gaussianReal
        (μ := 0) (v := ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩) (t := r / (ε : ℝ) ^ 2))
  have hIntLeft :
      Integrable (fun x : ℝ ↦ Real.exp ((-r / (ε : ℝ) ^ 2) * x))
        (smallVarianceGaussianFamily ε) := by
    -- Proof comment: the same mgf input controls the left tail after flipping the Chernoff slope.
    simpa [smallVarianceGaussianFamily] using
      (integrable_exp_mul_gaussianReal
        (μ := 0) (v := ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩) (t := -r / (ε : ℝ) ^ 2))
  have hSlopeNonneg : 0 ≤ r / (ε : ℝ) ^ 2 := by
    positivity
  have hSlopeNonpos : -r / (ε : ℝ) ^ 2 ≤ 0 := by
    have hneg : -(r / (ε : ℝ) ^ 2) ≤ 0 := by
      linarith [hSlopeNonneg]
    simpa [neg_div] using hneg
  have hεne : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  have hRight :
      (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Ici r) ≤
        Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) := by
    have hChernoff :
        (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Ici r) ≤
          Real.exp (-(r / (ε : ℝ) ^ 2) * r) *
            mgf id (smallVarianceGaussianFamily ε) (r / (ε : ℝ) ^ 2) := by
      -- Proof comment: the standard upper-tail Chernoff estimate controls the right half-line.
      simpa [Set.Ici] using
        (measure_ge_le_exp_mul_mgf (μ := (smallVarianceGaussianFamily ε : Measure ℝ)) (X := id)
          (ε := r) (t := r / (ε : ℝ) ^ 2) hSlopeNonneg hIntRight)
    calc
      (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Ici r) ≤
          Real.exp (-(r / (ε : ℝ) ^ 2) * r) *
            mgf id (smallVarianceGaussianFamily ε) (r / (ε : ℝ) ^ 2) :=
        hChernoff
      _ = Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) := by
        -- Proof comment: evaluating the Gaussian mgf at the optimizing slope leaves the desired
        -- quadratic exponent.
        rw [smallVarianceGaussianFamily_apply, mgf_id_gaussianReal, ← Real.exp_add]
        congr 1
        simp only [NNReal.coe_mk]
        field_simp [hεne]
        ring_nf
  have hLeft :
      (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Iic (-r)) ≤
        Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) := by
    have hChernoff :
        (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Iic (-r)) ≤
          Real.exp (-(-r / (ε : ℝ) ^ 2) * (-r)) *
            mgf id (smallVarianceGaussianFamily ε) (-r / (ε : ℝ) ^ 2) := by
      -- Proof comment: the lower-tail Chernoff estimate gives the same quadratic exponent.
      simpa [Set.Iic] using
        (measure_le_le_exp_mul_mgf (μ := (smallVarianceGaussianFamily ε : Measure ℝ)) (X := id)
          (ε := -r) (t := -r / (ε : ℝ) ^ 2) hSlopeNonpos hIntLeft)
    calc
      (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Iic (-r)) ≤
          Real.exp (-(-r / (ε : ℝ) ^ 2) * (-r)) *
            mgf id (smallVarianceGaussianFamily ε) (-r / (ε : ℝ) ^ 2) :=
        hChernoff
      _ = Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) := by
        -- Proof comment: the negative optimizing slope produces the same closed-form bound.
        rw [smallVarianceGaussianFamily_apply, mgf_id_gaussianReal, ← Real.exp_add]
        congr 1
        simp only [NNReal.coe_mk]
        field_simp [hεne]
        ring_nf
  have hTailSet : ((Metric.ball 0 r)ᶜ : Set ℝ) = Set.Iic (-r) ∪ Set.Ici r := by
    -- Proof comment: for a ball centered at `0`, being outside the ball is the same as lying in
    -- one of the two closed tails.
    ext x
    constructor
    · intro hx
      by_cases hxle : x ≤ -r
      · exact Or.inl hxle
      · have hxr : r ≤ x := by
          by_contra hxr
          exact hx <| by
            simpa [Metric.mem_ball, abs_lt] using ⟨lt_of_not_ge hxle, lt_of_not_ge hxr⟩
        exact Or.inr hxr
    · rintro (hx | hx) hball
      · have hballConj : -r < x ∧ x < r := by
          simpa [Metric.mem_ball, abs_lt] using hball
        have hlt : -r < x := hballConj.1
        exact (not_lt_of_ge hx) hlt
      · have hballConj : -r < x ∧ x < r := by
          simpa [Metric.mem_ball, abs_lt] using hball
        have hlt : x < r := hballConj.2
        exact (not_lt_of_ge hx) hlt
  have hTailReal :
      (smallVarianceGaussianFamily ε : Measure ℝ).real ((Metric.ball 0 r)ᶜ) ≤
        2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) := by
    rw [hTailSet]
    calc
      (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Iic (-r) ∪ Set.Ici r) ≤
          (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Iic (-r)) +
            (smallVarianceGaussianFamily ε : Measure ℝ).real (Set.Ici r) :=
        measureReal_union_le _ _
      _ ≤ Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) +
            Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) :=
        add_le_add hLeft hRight
      _ = 2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) := by ring
  have hMeasureNeTop :
      (smallVarianceGaussianFamily ε : Measure ℝ) ((Metric.ball 0 r)ᶜ) ≠ ∞ := by
    finiteness
  have hBoundNonneg : 0 ≤ 2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) := by
    positivity
  refine (ENNReal.le_ofReal_iff_toReal_le hMeasureNeTop hBoundNonneg).2 ?_
  simpa [Measure.real] using hTailReal

/-- Helper for Exercise 23.2.2: the explicit tail estimate turns into a logarithmic upper bound on
the scaled mass outside a fixed ball. -/
private theorem smallVarianceGaussianFamily_scaledLogMass_complBall_le_upperApprox {r : ℝ}
    (hr : 0 < r) {ε : PositiveParameter} (hεr : (ε : ℝ) ≤ r) :
    scaledLogMassAlong
        (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id ((Metric.ball 0 r)ᶜ) ε ≤
      (((((ε : ℝ) * Real.log 2 - r ^ 2 / (2 * (ε : ℝ))) : ℝ)) : EReal) := by
  let bound : ℝ := 2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2))
  have hMassENN :
      (smallVarianceGaussianFamily ε : Measure ℝ) ((Metric.ball 0 r)ᶜ) ≤ ENNReal.ofReal bound := by
    simpa [bound] using smallVarianceGaussianFamily_tailMass_complBall_le hr (ε := ε) hεr
  have hBoundPos : 0 < bound := by
    dsimp [bound]
    positivity
  have hεE : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  calc
    scaledLogMassAlong
        (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id ((Metric.ball 0 r)ᶜ) ε =
          ((ε : ℝ) : EReal) *
            ENNReal.log ((smallVarianceGaussianFamily ε : Measure ℝ) ((Metric.ball 0 r)ᶜ)) := by
      simpa using
        (scaledLogMassAlong_def
          (μ := fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ))
          (ε := id) (s := ((Metric.ball 0 r)ᶜ)) (i := ε))
    _ ≤ ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal bound) := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hMassENN) hεE
    _ = (((ε : ℝ) * Real.log bound : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos hBoundPos, ← EReal.coe_mul]
    _ = (((((ε : ℝ) * Real.log 2 - r ^ 2 / (2 * (ε : ℝ))) : ℝ)) : EReal) := by
      -- Proof comment: split the logarithm into the constant `log 2` term and the Gaussian
      -- exponent, then simplify the prefactor algebra.
      have hεpos : 0 < (ε : ℝ) := ε.2
      have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεpos
      congr 1
      dsimp [bound]
      rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
      field_simp [hεne]
      ring_nf

/-- Helper for Exercise 23.2.2: any closed set in `ℝ` that misses `0` is contained in the
complement of a small ball around the origin. -/
private theorem exists_ball_compl_subset_of_isClosed_zero_not_mem {C : Set ℝ} (hC : IsClosed C)
    (h0 : (0 : ℝ) ∉ C) :
    ∃ r > 0, C ⊆ (Metric.ball 0 r)ᶜ := by
  have hOpen : IsOpen Cᶜ := hC.isOpen_compl
  have h0mem : (0 : ℝ) ∈ Cᶜ := h0
  rcases Metric.isOpen_iff.mp hOpen 0 h0mem with ⟨r, hrPos, hrSub⟩
  refine ⟨r, hrPos, ?_⟩
  intro x hxC hxBall
  exact hrSub hxBall hxC

/-- Helper for Exercise 23.2.2: if a probability measure puts less than `1 / 2` mass on the
complement of a measurable set, then the set itself carries at least `1 / 2` mass. -/
private theorem one_half_le_measure_of_compl_lt_half
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ} (hs : MeasurableSet s)
    (hcompl : μ sᶜ < (1 / 2 : ℝ≥0∞)) :
    (1 / 2 : ℝ≥0∞) ≤ μ s := by
  have hsum : μ s + μ sᶜ = 1 := by
    simpa using prob_add_prob_compl (μ := μ) hs
  have hsum_real :
      (μ s).toReal + (μ sᶜ).toReal = 1 := by
    simpa [ENNReal.toReal_add, measure_ne_top μ _] using congrArg ENNReal.toReal hsum
  have hcompl_real : (μ sᶜ).toReal < (1 / 2 : ℝ) := by
    have hcompl' : μ sᶜ < ENNReal.ofReal (1 / 2 : ℝ) := by
      simpa using hcompl
    simpa using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hcompl'
  have hset_real : (1 / 2 : ℝ) ≤ (μ s).toReal := by
    linarith
  have hset : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ s := by
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2 hset_real
  simpa using hset

/-- Helper for Exercise 23.2.2: if a set contains `0`, then the image of the zero-Dirac rate
function on that set has infimum `0`. -/
private theorem zeroDiracRateFunction_sInf_image_eq_zero_of_zero_mem {s : Set ℝ}
    (h0 : (0 : ℝ) ∈ s) :
    sInf ((fun x : ℝ ↦ (zeroDiracRateFunction x : EReal)) '' s) = 0 := by
  apply le_antisymm
  · refine sInf_le ?_
    exact ⟨0, h0, by simp [zeroDiracRateFunction]⟩
  · refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · simp [zeroDiracRateFunction, hx0]
    · simp [zeroDiracRateFunction, hx0]

/-- Helper for Exercise 23.2.2: if a set misses `0`, then the image of the zero-Dirac rate
function on that set has infimum `⊤`. -/
private theorem zeroDiracRateFunction_sInf_image_eq_top_of_zero_not_mem {s : Set ℝ}
    (h0 : (0 : ℝ) ∉ s) :
    sInf ((fun x : ℝ ↦ (zeroDiracRateFunction x : EReal)) '' s) = ⊤ := by
  apply le_antisymm le_top
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : x ≠ 0 := by
    intro hxEq
    exact h0 (hxEq ▸ hx)
  simp [zeroDiracRateFunction, hx0]

/-- Helper for Exercise 23.2.2: on sets containing `0`, the LDP rate-side value is `0`. -/
private theorem neg_sInf_zeroDiracRateImage_eq_zero_of_zero_mem {s : Set ℝ} (h0 : (0 : ℝ) ∈ s) :
    -sInf ((fun x : ℝ ↦ (zeroDiracRateFunction x : EReal)) '' s) = 0 := by
  rw [zeroDiracRateFunction_sInf_image_eq_zero_of_zero_mem h0, neg_zero]

/-- Helper for Exercise 23.2.2: on sets missing `0`, the LDP rate-side value is `⊥`. -/
private theorem neg_sInf_zeroDiracRateImage_eq_bot_of_zero_not_mem {s : Set ℝ}
    (h0 : (0 : ℝ) ∉ s) :
    -sInf ((fun x : ℝ ↦ (zeroDiracRateFunction x : EReal)) '' s) = ⊥ := by
  rw [zeroDiracRateFunction_sInf_image_eq_top_of_zero_not_mem h0]
  simp

/-- Helper for Exercise 23.2.2: every logarithmic mass term is nonpositive because the
underlying family consists of probability measures. -/
private theorem smallVarianceGaussianFamily_scaledLogMass_nonpos (s : Set ℝ) (ε : PositiveParameter) :
    scaledLogMassAlong (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id s ε ≤ 0 := by
  rw [scaledLogMassAlong_def]
  have hmass :
      (smallVarianceGaussianFamily ε : Measure ℝ) s ≤ 1 := by
    calc
      (smallVarianceGaussianFamily ε : Measure ℝ) s
          ≤ (smallVarianceGaussianFamily ε : Measure ℝ) Set.univ := measure_mono (by simp)
      _ = 1 := by simp [smallVarianceGaussianFamily]
  have hlog :
      ENNReal.log ((smallVarianceGaussianFamily ε : Measure ℝ) s) ≤ 0 := by
    simpa using
      (ENNReal.log_le_log hmass :
        ENNReal.log ((smallVarianceGaussianFamily ε : Measure ℝ) s) ≤ ENNReal.log 1)
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast (le_of_lt ε.2)
  calc
    ((ε : ℝ) : EReal) * ENNReal.log ((smallVarianceGaussianFamily ε : Measure ℝ) s)
        ≤ ((ε : ℝ) : EReal) * 0 := by
            exact mul_le_mul_of_nonneg_left hlog hε
    _ = 0 := by simp

/-- Helper for Exercise 23.2.2: the lower comparison term `ε log (1 / 2)` is eventually above any
strictly negative test value along the positive-parameter filter. -/
private theorem eventually_lt_scaledLogHalf {y : EReal} (hy : y < 0) :
    ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
      y < ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) := by
  have hbase :
      Tendsto (fun ε : ℝ ↦ (ε : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞))
        (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) :=
    ENNReal.tendsto_smallNoiseLogConst (b := (1 / 2 : ℝ≥0∞)) (by norm_num) (by simp)
  have hcoe :
      Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    rw [positiveParameterFilter]
    exact Filter.map_comap_le
  have htendsto :
      Tendsto
        (fun ε : PositiveParameter => ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞))
        positiveParameterFilter (nhds (0 : EReal)) := by
    -- Proof comment: reindex the standard small-noise limit along the positive-parameter filter.
    simpa using hbase.comp hcoe
  -- Proof comment: `Ioi y` is a neighborhood of `0`, so eventual membership gives the desired
  -- strict inequality against every negative comparison value.
  exact htendsto (Ioi_mem_nhds hy)

/-- Helper for Exercise 23.2.2: the complement-ball logarithmic mass has limsup `⊥`. -/
private theorem scaledLogTailBound_complBall_limsup_bot {r : ℝ} (hr : 0 < r) :
    limsup
        (scaledLogMassAlong
          (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id ((Metric.ball 0 r)ᶜ))
        positiveParameterFilter = ⊥ := by
  apply le_antisymm
  · rw [Filter.limsup_le_iff']
    intro y hy
    by_cases hyTop : y = ⊤
    · simpa [hyTop]
    obtain ⟨z, hzLeft, hzRight⟩ := exists_between hy
    have hzBot : z ≠ ⊥ := ne_bot_of_gt hzLeft
    have hzTop : z ≠ ⊤ := ne_top_of_lt (hzRight.trans_le le_top)
    let yz : ℝ := z.toReal
    have hyz : ((yz : ℝ) : EReal) < y := by
      rw [EReal.coe_toReal hzTop hzBot]
      exact hzRight
    let k : ℝ := |yz| + Real.log 2 + 1
    let δ : ℝ := min r (min 1 (r ^ 2 / (2 * k)))
    have hkPos : 0 < k := by
      dsimp [k]
      positivity
    have hδPos : 0 < δ := by
      dsimp [δ]
      positivity
    have hcoe :
        Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
      rw [positiveParameterFilter]
      exact Filter.map_comap_le
    have hEventuallySmall :
        ∀ᶠ ε : PositiveParameter in positiveParameterFilter, (ε : ℝ) < δ := by
      -- Proof comment: all three cutoffs are enforced by choosing `ε` in a sufficiently small
      -- right-neighborhood of `0`.
      exact hcoe (Iio_mem_nhdsWithin_right_zero hδPos)
    filter_upwards [hEventuallySmall] with ε hεδ
    have hεr : (ε : ℝ) ≤ r := by
      have hδle : δ ≤ r := by
        dsimp [δ]
        exact min_le_left _ _
      linarith
    have hεone : (ε : ℝ) ≤ 1 := by
      have hδle : δ ≤ 1 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hεcut : (ε : ℝ) < r ^ 2 / (2 * k) := by
      have hδle : δ ≤ r ^ 2 / (2 * k) := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    have hScaledLe :
        scaledLogMassAlong
            (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id ((Metric.ball 0 r)ᶜ) ε ≤
          (((((ε : ℝ) * Real.log 2 - r ^ 2 / (2 * (ε : ℝ))) : ℝ)) : EReal) :=
      smallVarianceGaussianFamily_scaledLogMass_complBall_le_upperApprox hr hεr
    have hUpperDenom :
        k < r ^ 2 / (2 * (ε : ℝ)) := by
      have hTwoKPos : 0 < 2 * k := by
        positivity
      have hTwoEpsPos : 0 < 2 * (ε : ℝ) := by
        exact mul_pos (by norm_num) ε.2
      have hmul : (ε : ℝ) * (2 * k) < r ^ 2 := by
        exact (lt_div_iff₀ hTwoKPos).1 hεcut
      exact (lt_div_iff₀ hTwoEpsPos).2 (by nlinarith)
    have hLogTermLe : (ε : ℝ) * Real.log 2 ≤ Real.log 2 := by
      nlinarith [hεone, show 0 ≤ Real.log 2 by positivity]
    have hApproxLtReal :
        (ε : ℝ) * Real.log 2 - r ^ 2 / (2 * (ε : ℝ)) < yz := by
      have hStrong :
          |yz| + Real.log 2 + 1 < r ^ 2 / (2 * (ε : ℝ)) := by
        simpa [k, add_assoc, add_left_comm, add_comm] using hUpperDenom
      have hNegAbs : -|yz| - 1 < yz := by
        nlinarith [neg_abs_le yz]
      have hAux : (ε : ℝ) * Real.log 2 - r ^ 2 / (2 * (ε : ℝ)) < -|yz| - 1 := by
        nlinarith [hLogTermLe, hStrong]
      exact hAux.trans hNegAbs
    have hApproxLt :
        (((((ε : ℝ) * Real.log 2 - r ^ 2 / (2 * (ε : ℝ))) : ℝ)) : EReal) < y := by
      have hToZ :
          (((((ε : ℝ) * Real.log 2 - r ^ 2 / (2 * (ε : ℝ))) : ℝ)) : EReal) < ((yz : ℝ) : EReal) :=
        by exact_mod_cast hApproxLtReal
      exact hToZ.trans hyz
    exact hScaledLe.trans hApproxLt.le
  · exact bot_le

/-- Helper for Exercise 23.2.2: eventually the escape mass from a fixed ball is smaller than
`1 / 2`. -/
private theorem smallVarianceGaussianFamily_eventually_tailMass_lt_half {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
      (smallVarianceGaussianFamily ε : Measure ℝ) ((Metric.ball 0 r)ᶜ) < (1 / 2 : ℝ≥0∞) := by
  have hConst : 2 * Real.exp (-2 : ℝ) < (1 / 2 : ℝ) := by
    have hExpTwo : (4 : ℝ) < Real.exp 2 := by
      have hExpOne : (2 : ℝ) < Real.exp 1 := by
        have h : (1 : ℝ) + 1 < Real.exp 1 := by
          exact Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
        nlinarith
      have hPos : 0 < Real.exp 1 := Real.exp_pos 1
      have hSq : (4 : ℝ) < (Real.exp 1) ^ 2 := by
        nlinarith
      calc
        (4 : ℝ) < (Real.exp 1) ^ 2 := hSq
        _ = Real.exp 2 := by rw [sq, ← Real.exp_add]; norm_num
    calc
      2 * Real.exp (-2 : ℝ) = 2 / Real.exp 2 := by rw [Real.exp_neg, div_eq_mul_inv]
      _ < (1 / 2 : ℝ) := by
        exact (div_lt_iff₀ (Real.exp_pos 2)).2 (by nlinarith)
  have hConstENN : ENNReal.ofReal (2 * Real.exp (-2 : ℝ)) < (1 / 2 : ℝ≥0∞) := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hConst
  have hcoe :
      Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    rw [positiveParameterFilter]
    exact Filter.map_comap_le
  have hEventuallySmall :
      ∀ᶠ ε : PositiveParameter in positiveParameterFilter, (ε : ℝ) < r / 2 := by
    -- Proof comment: the Gaussian tail estimate becomes uniform once `ε` is much smaller than
    -- the fixed radius `r`.
    exact hcoe (Iio_mem_nhdsWithin_right_zero (δ := r / 2) (by positivity))
  filter_upwards [hEventuallySmall] with ε hεsmall
  have hεr : (ε : ℝ) ≤ r := by
    linarith
  have hTail :
      (smallVarianceGaussianFamily ε : Measure ℝ) ((Metric.ball 0 r)ᶜ) ≤
        ENNReal.ofReal (2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2))) :=
    smallVarianceGaussianFamily_tailMass_complBall_le hr hεr
  have hTwoEpsLt : 2 * (ε : ℝ) < r := by
    nlinarith
  have hMulSq : 4 * (ε : ℝ) ^ 2 < r ^ 2 := by
    have hDiffPos : 0 < r - 2 * (ε : ℝ) := by
      linarith
    have hSumPos : 0 < r + 2 * (ε : ℝ) := by
      exact add_pos hr (mul_pos (by norm_num) ε.2)
    have hProdPos : 0 < (r - 2 * (ε : ℝ)) * (r + 2 * (ε : ℝ)) := by
      exact mul_pos hDiffPos hSumPos
    nlinarith
  have hDenPos : 0 < 2 * (ε : ℝ) ^ 2 := by
    have hSqPos : 0 < (ε : ℝ) ^ 2 := by
      exact sq_pos_of_ne_zero (show (ε : ℝ) ≠ 0 by exact ne_of_gt ε.2)
    exact mul_pos (by norm_num) hSqPos
  have hQuotGt : (2 : ℝ) < r ^ 2 / (2 * (ε : ℝ) ^ 2) := by
    exact (lt_div_iff₀ hDenPos).2 (by nlinarith)
  have hExponentLe : -(r ^ 2) / (2 * (ε : ℝ) ^ 2) ≤ (-2 : ℝ) := by
    have hNeg : -(r ^ 2) / (2 * (ε : ℝ) ^ 2) < (-2 : ℝ) := by
      simpa [neg_div] using (neg_lt_neg hQuotGt)
    exact hNeg.le
  have hBoundLe :
      2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2)) ≤ 2 * Real.exp (-2 : ℝ) := by
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExponentLe) (by positivity)
  have hBoundLt :
      ENNReal.ofReal (2 * Real.exp (-(r ^ 2) / (2 * (ε : ℝ) ^ 2))) < (1 / 2 : ℝ≥0∞) := by
    exact (ENNReal.ofReal_le_ofReal hBoundLe).trans_lt hConstENN
  exact hTail.trans_lt hBoundLt

/-- Helper for Exercise 23.2.2: the rate function that vanishes at `0` and is infinite elsewhere
is a good rate function on `ℝ`. -/
private theorem zeroDiracRateFunction_isGood :
    IsGoodRateFunction zeroDiracRateFunction := by
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity reduces to the openness of the strict superlevel preimages.
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro y
    by_cases hy : y < (0 : ℝ≥0∞)
    · exact False.elim (not_lt_of_ge bot_le hy)
    · by_cases htop : y = ⊤
      · simpa [htop] using isOpen_empty
      · have hy0 : (0 : ℝ≥0∞) ≤ y := le_of_not_gt hy
        have hytop : y < ⊤ := lt_of_le_of_ne le_top htop
        have hpre : zeroDiracRateFunction ⁻¹' Set.Ioi y = ({0} : Set ℝ)ᶜ := by
          ext x
          by_cases hx : x = 0
          · simp [zeroDiracRateFunction, hx, hy0]
          · constructor
            · intro _
              simp [hx]
            · intro _
              simpa [zeroDiracRateFunction, hx] using hytop
        rw [hpre]
        simpa using isOpen_ne (x := (0 : ℝ))
  · intro a
    -- Every finite sublevel set is the singleton `{0}`.
    have hsublevel :
        zeroDiracRateFunction ⁻¹' Set.Iic (a : ℝ≥0∞) = ({0} : Set ℝ) := by
      ext x
      by_cases hx : x = 0
      · simp [zeroDiracRateFunction, hx]
      · simp [zeroDiracRateFunction, hx]
    rw [hsublevel]
    exact isCompact_singleton

-- Proof sketch: the Gaussian family collapses exponentially fast onto the singleton `{0}` as
-- `ε ↓ 0`, so the large-deviation bounds are governed by the rate that is `0` at `0` and `∞`
-- elsewhere; the finite sublevel sets are either empty or `{0}`, hence compact.
/-- Exercise 23.2.2: the family `μ_ε = 𝒩(0, ε²)` satisfies the large deviations principle with
good rate function `I(x) = ∞ · 𝟙_{ℝ \ {0}}(x)`, written here as the function that is `0` at `0`
and `∞` elsewhere. -/
theorem smallVarianceGaussianFamily_satisfiesLDPWithGoodRate :
    HasLargeDeviationsPrinciple smallVarianceGaussianFamily zeroDiracRateFunction ∧
      IsGoodRateFunction zeroDiracRateFunction := by
  refine ⟨?_, zeroDiracRateFunction_isGood⟩
  refine
    { lowerSemicontinuous := zeroDiracRateFunction_isGood.lowerSemicontinuous
      open_lower_bound := ?_
      closed_upper_bound := ?_ }
  · intro U hU
    by_cases h0 : (0 : ℝ) ∈ U
    · rw [neg_sInf_zeroDiracRateImage_eq_zero_of_zero_mem h0]
      rw [Filter.le_liminf_iff']
      intro y hy
      rcases Metric.isOpen_iff.mp hU 0 h0 with ⟨r, hr, hBallSub⟩
      have hHalfMass :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            (1 / 2 : ℝ≥0∞) ≤ (smallVarianceGaussianFamily ε : Measure ℝ) U := by
        have hTail :
            ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
              (smallVarianceGaussianFamily ε : Measure ℝ) Uᶜ < (1 / 2 : ℝ≥0∞) := by
          filter_upwards [smallVarianceGaussianFamily_eventually_tailMass_lt_half hr] with ε hε
          have hComplSub : Uᶜ ⊆ (Metric.ball 0 r)ᶜ := by
            intro x hxU hxBall
            exact hxU (hBallSub hxBall)
          exact lt_of_le_of_lt (measure_mono hComplSub) hε
        filter_upwards [hTail] with ε hε
        exact one_half_le_measure_of_compl_lt_half
          (μ := (smallVarianceGaussianFamily ε : Measure ℝ)) (s := U) hU.measurableSet hε
      have hCompare :
          ∀ᶠ ε : PositiveParameter in positiveParameterFilter,
            ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) ≤
              scaledLogMassAlong
                (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id U ε := by
        filter_upwards [hHalfMass] with ε hε
        have hεNonneg : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
          exact_mod_cast le_of_lt ε.2
        calc
          ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞) ≤
              ((ε : ℝ) : EReal) *
                ENNReal.log ((smallVarianceGaussianFamily ε : Measure ℝ) U) := by
                  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hε) hεNonneg
          _ = scaledLogMassAlong
                (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id U ε := by
                  simp [scaledLogMassAlong_def]
      filter_upwards [eventually_lt_scaledLogHalf hy, hCompare] with ε hyε hε
      exact hyε.le.trans hε
    · simpa [neg_sInf_zeroDiracRateImage_eq_bot_of_zero_not_mem h0] using
        (bot_le :
          (⊥ : EReal) ≤
            Filter.liminf
              (scaledLogMassAlong
                (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id U)
              positiveParameterFilter)
  · intro C hC
    by_cases h0 : (0 : ℝ) ∈ C
    · rw [neg_sInf_zeroDiracRateImage_eq_zero_of_zero_mem h0]
      exact limsup_le_of_le (by isBoundedDefault) <|
        Eventually.of_forall fun ε ↦ smallVarianceGaussianFamily_scaledLogMass_nonpos C ε
    · rcases exists_ball_compl_subset_of_isClosed_zero_not_mem hC h0 with ⟨r, hr, hSubset⟩
      rw [neg_sInf_zeroDiracRateImage_eq_bot_of_zero_not_mem h0]
      calc
        Filter.limsup
            (scaledLogMassAlong
              (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id C)
            positiveParameterFilter
            ≤ Filter.limsup
                (scaledLogMassAlong
                  (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) id ((Metric.ball 0 r)ᶜ))
                positiveParameterFilter := by
                  exact limsup_le_limsup <|
                    Eventually.of_forall fun ε ↦
                      scaledLogMassAlong_mono
                        (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) hSubset ε
        _ = ⊥ := scaledLogTailBound_complBall_limsup_bot hr

-- Proof sketch: take the open set `(0, ∞)`. Its rate infimum is `∞`, so the LDP lower bound gives
-- only `-∞`, while the Gaussian symmetry gives `μ_ε (0, ∞) = 1 / 2`, hence `ε log μ_ε (0, ∞) → 0`.
/-- The open half-line `(0, ∞)` witnesses that the lower bound in the large deviations principle
can be strict for `μ_ε = 𝒩(0, ε²)`. -/
theorem smallVarianceGaussianFamily_strict_lowerBound_on_positiveHalfline :
    -sInf ((fun x : ℝ ↦ (zeroDiracRateFunction x : EReal)) '' Set.Ioi (0 : ℝ)) <
      liminf
        (scaledLogMassAlong (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) (fun ε ↦ ε)
          (Set.Ioi (0 : ℝ)))
        positiveParameterFilter := by
  rw [neg_sInf_zeroDiracRateImage_eq_bot_of_zero_not_mem (s := Set.Ioi (0 : ℝ)) (by simp)]
  have hNonneg :
      (0 : EReal) ≤
        liminf
          (scaledLogMassAlong
            (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) (fun ε ↦ ε)
            (Set.Ioi (0 : ℝ)))
          positiveParameterFilter := by
    rw [Filter.le_liminf_iff']
    intro y hy
    filter_upwards [eventually_lt_scaledLogHalf hy] with ε hyε
    -- Proof comment: the event mass on the positive half-line is exactly `1 / 2` for every `ε`.
    simpa [scaledLogMassAlong_def, smallVarianceGaussianFamily_positiveHalfline_mass ε] using hyε.le
  -- Proof comment: the rate side is `⊥`, while the exponent liminf is at least `0`.
  exact lt_of_lt_of_le (by simp) hNonneg
