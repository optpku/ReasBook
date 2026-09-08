module

public import ReasLib.Analysis.Analytic.Sqrt
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- The normalized second-leg radius factor in the removable two-leg coordinates. -/
def radiusFactor (ε p h : ℝ) : ℝ :=
  (DFP.SecondLeg.canonicalFactors ε p h).1

/-- The signed extension of the scale coordinate obtained from the normalized radius
factor. -/
def signedEpsilon (ε p h : ℝ) : ℝ :=
  ε * Real.sqrt (radiusFactor ε p h)

/-- The normalized second-leg radius factor is jointly real analytic at `(0, 2, 1)`. -/
theorem analyticAt_radiusFactor :
    AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ radiusFactor x.1 x.2.1 x.2.2) (0, 2, 1) := by
  -- Project the canonical pair from the jointly analytic tuple of removable factors.
  have hcanonical := analyticAt_snd.comp
    (analyticAt_snd.comp DFP.SecondLeg.factorsAnalytic)
  -- Its first coordinate is definitionally the normalized radius factor.
  apply (analyticAt_fst.comp hcanonical).congr
  filter_upwards [] with x
  simp only [Function.comp_apply, DFP.SecondLeg.factors, radiusFactor]

/-- The first-leg removable spectral and gradient factors at zero signed scale. -/
private lemma firstLegFactorDataAtZero (p h : ℝ) :
    (DFP.FirstLeg.spectralFactors 0 p h, DFP.FirstLeg.gradientFactors 0 p h) =
      ((h * p, 1), (1, (p + 1) / 3)) := by
  -- At zero scale the metric is diagonal, so its spectral radical is exactly one.
  norm_num [DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
    RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
    RealSymmetric2.lowDenom]
  -- Normalize the remaining polynomial coordinates of the two factor pairs.
  ring

/-- The second-leg removable spectral and gradient factors at zero signed scale. -/
private lemma secondLegFactorDataAtZero (p h : ℝ) (p_pos : 0 < p) :
    (DFP.SecondLeg.spectralFactors 0 p h, DFP.SecondLeg.gradientFactors 0 p h) =
      ((h * p, 1),
        (1, 2 * (9 * h * p + (p + 1) ^ 2) / (9 * (p + 1)))) := by
  have hp_one_ne : p + 1 ≠ 0 := by
    linarith
  have hspectral : DFP.FirstLeg.spectralFactors 0 p h = (h * p, 1) := by
    -- Project the spectral coordinates from the first-leg zero-scale interface.
    exact congrArg Prod.fst (firstLegFactorDataAtZero p h)
  have hgradient : DFP.FirstLeg.gradientFactors 0 p h = (1, (p + 1) / 3) := by
    -- Project the gradient coordinates from the same first-leg interface.
    exact congrArg Prod.snd (firstLegFactorDataAtZero p h)
  -- Substitute the first-leg data and evaluate the diagonal second-leg eigensystem.
  norm_num [DFP.SecondLeg.spectralFactors, DFP.SecondLeg.gradientFactors,
    hspectral, hgradient, RealSymmetric2.low, RealSymmetric2.high,
    RealSymmetric2.gap, RealSymmetric2.lowDenom]
  -- Clear the sole variable denominator before polynomial normalization.
  field_simp [hp_one_ne]
  all_goals norm_num
  all_goals ring

/-- At zero signed scale, both canonical second-leg factors have explicit rational
values for positive shape and high-eigenvalue parameters. -/
private lemma canonicalFactorDataAtZero (p h : ℝ) (p_pos : 0 < p) (h_pos : 0 < h) :
    DFP.SecondLeg.canonicalFactors 0 p h =
      (9 * h * p * (p + 1) / (2 * (9 * h * p + (p + 1) ^ 2)),
        4 * (9 * h * p + (p + 1) ^ 2) ^ 2 / (81 * h * p * (p + 1) ^ 2)) := by
  have hdata := secondLegFactorDataAtZero p h p_pos
  have hspectral : DFP.SecondLeg.spectralFactors 0 p h = (h * p, 1) := by
    -- The first projection supplies the removable eigenvalue factors.
    exact congrArg Prod.fst hdata
  have hgradient : DFP.SecondLeg.gradientFactors 0 p h =
      (1, 2 * (9 * h * p + (p + 1) ^ 2) / (9 * (p + 1))) := by
    -- The second projection supplies the removable gradient factors.
    exact congrArg Prod.snd hdata
  have hp_ne : p ≠ 0 := ne_of_gt p_pos
  have hh_ne : h ≠ 0 := ne_of_gt h_pos
  have hp_one_ne : p + 1 ≠ 0 := by
    linarith
  have hdenom_pos : 0 < 9 * h * p + (p + 1) ^ 2 := by
    positivity
  have hdenom_ne : 9 * h * p + (p + 1) ^ 2 ≠ 0 := ne_of_gt hdenom_pos
  -- Substitute the two stable factor pairs before normalizing either quotient.
  unfold DFP.SecondLeg.canonicalFactors
  simp only [hspectral, hgradient]
  apply Prod.ext
  · -- Clear the nonzero high-gradient denominator in the radius coordinate.
    dsimp only [Prod.fst]
    field_simp [hp_one_ne, hdenom_ne]
  · -- Clear all positive factor denominators in the shape coordinate.
    dsimp only [Prod.snd]
    field_simp [hp_ne, hh_ne, hp_one_ne, hdenom_ne]
    ring

/-- At zero signed scale, the normalized second-leg radius factor has an explicit
rational value for positive shape and high-eigenvalue parameters. -/
theorem radiusFactor_zero (p h : ℝ) (p_pos : 0 < p) (h_pos : 0 < h) :
    radiusFactor 0 p h =
      9 * h * p * (p + 1) / (2 * (9 * h * p + (p + 1) ^ 2)) := by
  -- Project the radius coordinate from the normalized canonical pair.
  exact congrArg Prod.fst (canonicalFactorDataAtZero p h p_pos h_pos)

/-- The normalized second-leg radius factor equals one at `(0, 2, 1)`. -/
theorem radiusFactor_base :
    radiusFactor 0 2 1 = 1 := by
  -- Project the radius coordinate from the complete tuple of base factors.
  simpa only [DFP.SecondLeg.factors, radiusFactor] using
    congrArg (fun y ↦ y.2.2.1) DFP.SecondLeg.factorsBase

/-- The normalized second-leg radius factor is positive in a neighborhood of
`(0, 2, 1)`. -/
theorem radiusFactor_eventually_pos :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < radiusFactor x.1 x.2.1 x.2.2 := by
  have hbase : 0 < radiusFactor 0 2 1 := by
    rw [radiusFactor_base]
    norm_num
  -- Continuity preserves the strict positivity of the unit base value.
  apply analyticAt_radiusFactor.continuousAt.eventually
  apply Ioi_mem_nhds
  exact hbase

/-- The signed extension of the scale coordinate is jointly real analytic at
`(0, 2, 1)`. -/
theorem analyticAt_signedEpsilon :
    AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ signedEpsilon x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
  have hradius_ne : radiusFactor 0 2 1 ≠ 0 := by
    rw [radiusFactor_base]
    norm_num
  have hsqrt := AnalyticAt.sqrt analyticAt_radiusFactor hradius_ne
  -- Multiply the analytic square-root factor by the signed scale coordinate.
  apply (analyticAt_fst.mul hsqrt).congr
  filter_upwards [] with x
  rfl

/-- The signed factored two-leg state map sends the common scale, shape, and high
eigenvalue to `ε * √ℛ₂`, `p₂`, and `ℋ₂`. -/
def stateMap : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) := fun x ↦
  let canonical := DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2
  let spectral := DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2
  (signedEpsilon x.1 x.2.1 x.2.2, canonical.2, spectral.2)

/-- The first coordinate of the two-leg state map is its signed scale update. -/
@[simp]
theorem stateMap_fst (ε p h : ℝ) :
    (stateMap (ε, p, h)).1 = signedEpsilon ε p h := by
  rfl

/-- The signed factored state map has the explicit coordinates
`(ε * √ℛ₂, p₂, ℋ₂)`. -/
theorem stateMap_apply (ε p h : ℝ) :
    stateMap (ε, p, h) =
      (ε * Real.sqrt (DFP.SecondLeg.canonicalFactors ε p h).1,
        (DFP.SecondLeg.canonicalFactors ε p h).2,
        (DFP.SecondLeg.spectralFactors ε p h).2) := by
  -- Unfolding the named coordinates evaluates the two local bindings.
  rfl

/-- At zero signed scale, the transverse coordinates of the signed factored state
map have explicit values for positive shape and high-eigenvalue parameters. -/
theorem stateMap_zero_transverse (p h : ℝ) (p_pos : 0 < p) (h_pos : 0 < h) :
    (stateMap (0, p, h)).2 =
      (4 * (9 * h * p + (p + 1) ^ 2) ^ 2 / (81 * h * p * (p + 1) ^ 2), 1) := by
  have hspectral : DFP.SecondLeg.spectralFactors 0 p h = (h * p, 1) := by
    -- Project the high-eigenvalue factor from the zero-scale factor interface.
    exact congrArg Prod.fst (secondLegFactorDataAtZero p h p_pos)
  have hcanonical := canonicalFactorDataAtZero p h p_pos h_pos
  -- Expose the state coordinates, then substitute their zero-scale factor values.
  rw [stateMap_apply, hspectral, hcanonical]

/-- Near `(0, 2, 1)`, on the positive-scale branch, the signed factored state map
agrees with the state recovered from the actual second-leg spectral coordinates. -/
theorem stateMap_eventuallyEq_recovered :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.1 →
      stateMap x =
        (Real.sqrt (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).1,
          (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).2,
          (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2) := by
  filter_upwards [DFP.SecondLeg.canonicalFactorization,
    DFP.SecondLeg.spectrumFactorization] with x hcanonical hspectrum
  intro hε
  have hrecovered := hcanonical (ne_of_gt hε)
  -- Recovery supplies the square of the signed scale; positivity selects its sign.
  rw [stateMap_apply, hrecovered, hspectrum]
  dsimp only
  rw [Real.sqrt_mul (sq_nonneg x.1), Real.sqrt_sq hε.le]

/-- The signed factored state map fixes the common factored base point. -/
theorem stateMap_base : stateMap (0, 2, 1) = (0, 2, 1) := by
  have hspectral : DFP.SecondLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.SecondLeg.factors] using
      congrArg Prod.fst DFP.SecondLeg.factorsBase
  have hcanonical : DFP.SecondLeg.canonicalFactors 0 2 1 = (1, 2) := by
    simpa only [DFP.SecondLeg.factors] using
      congrArg (fun y ↦ y.2.2) DFP.SecondLeg.factorsBase
  -- Substitute the base factor values into the explicit state coordinates.
  rw [stateMap_apply, hspectral, hcanonical]
  norm_num

/-- The signed factored state map is real analytic at the common factored base point. -/
theorem stateMapAnalytic :
    AnalyticAt ℝ stateMap ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  have hall := DFP.SecondLeg.factorsAnalytic
  have hcanonical := analyticAt_snd.comp (analyticAt_snd.comp hall)
  have hshape := analyticAt_snd.comp hcanonical
  have hspectralHigh := analyticAt_snd.comp (analyticAt_fst.comp hall)
  -- Assemble the three analytic coordinates of the signed state map.
  apply (analyticAt_signedEpsilon.prod (hshape.prod hspectralHigh)).congr
  filter_upwards [] with x
  rfl

end DFP.TwoLeg
