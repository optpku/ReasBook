/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import Mathlib.Data.Set.Function
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import ReasLib.Optimization.DFP.Polar.CycleFamily
public import ReasLib.Optimization.DFP.Polar.Normalized.Dynamics

public section

noncomputable section

open scoped Topology

namespace DFP.Polar.TwoCycle

/-- The selected open parameter interval around `baseAngle` for the rational
normalization family. -/
def parameterSet : Set ℝ :=
  Set.Ioo (3 * baseAngle / 4) (5 * baseAngle / 4)

/-- The endpoint formula defining `parameterSet`. -/
theorem parameterSet_def :
    parameterSet = Set.Ioo (3 * baseAngle / 4) (5 * baseAngle / 4) := by
  -- The selected endpoints are exactly the defining interval.
  rfl

/-- The image of the selected parameter interval under the rational normalization. -/
def normalizationSet : Set ℝ :=
  cycleK '' parameterSet

/-- The normalization set is the image of `parameterSet` under `cycleK`. -/
theorem normalizationSet_def :
    normalizationSet = cycleK '' parameterSet := by
  -- The normalization domain is the image of the parameter interval.
  rfl

/-- The reference normalization `K₀ = cycleK baseAngle`. -/
def kZero : ℝ :=
  cycleK baseAngle

/-- The reference normalization is the value of `cycleK` at `baseAngle`. -/
theorem kZero_def :
    kZero = cycleK baseAngle := by
  -- The reference normalization is defined by evaluation at the base angle.
  rfl

/-- The total inverse of `cycleK` selected from `parameterSet`. -/
noncomputable def inverseParameter (K : ℝ) : ℝ :=
  Function.invFunOn cycleK parameterSet K

/-- The even normalized state using the selected `cycleW` coordinate. -/
def evenState (K : ℝ) : ℝ × ℝ × ℝ :=
  (K, K * cycleW (inverseParameter K),
    1 + K * cycleW (inverseParameter K) ^ 2)

/-- The coordinate formula defining `evenState`. -/
theorem evenState_apply (K : ℝ) :
    evenState K =
      (K, K * cycleW (inverseParameter K),
        1 + K * cycleW (inverseParameter K) ^ 2) := by
  -- Read the three coordinates of the even state.
  rfl

/-- The odd normalized state using the selected `cycleZ` coordinate. -/
def oddState (K : ℝ) : ℝ × ℝ × ℝ :=
  (K, K * cycleZ (inverseParameter K),
    1 + K * cycleZ (inverseParameter K) ^ 2)

/-- The coordinate formula defining `oddState`. -/
theorem oddState_apply (K : ℝ) :
    oddState K =
      (K, K * cycleZ (inverseParameter K),
        1 + K * cycleZ (inverseParameter K) ^ 2) := by
  -- Read the three coordinates of the odd state.
  rfl

/-- The explicit even state at the reference normalization. -/
def evenReference : ℝ × ℝ × ℝ :=
  (kZero, 1 / baseAngle, 3)

/-- The coordinate formula defining `evenReference`. -/
theorem evenReference_def :
    evenReference = (kZero, 1 / baseAngle, 3) := by
  -- Read the prescribed even reference coordinates.
  rfl

/-- The explicit odd state at the reference normalization. -/
def oddReference : ℝ × ℝ × ℝ :=
  (kZero, 1 / (2 * baseAngle), 3 / 2)

/-- The coordinate formula defining `oddReference`. -/
theorem oddReference_def :
    oddReference = (kZero, 1 / (2 * baseAngle), 3 / 2) := by
  -- Read the prescribed odd reference coordinates.
  rfl

/-- The limiting-cycle angle is positive. -/
private lemma baseAnglePos : 0 < baseAngle := by
  -- The prescribed angle is a positive multiple of π.
  rw [baseAngle_def]
  positivity

/-- All rational-family factors
are positive throughout the closed parameter interval. -/
private lemma parameterClosureBounds (ν : ℝ)
    (hν : ν ∈ Set.Icc (3 * baseAngle / 4) (5 * baseAngle / 4)) :
    0 < ν ∧ 0 < 2 * baseAngle - ν ∧ 0 < baseAngle + ν ∧
      0 < 2 * ν - baseAngle := by
  -- The endpoint inequalities keep ν away from each denominator zero.
  rcases hν with ⟨hlo, hhi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [baseAnglePos]
  · linarith [baseAnglePos]
  · linarith [baseAnglePos]
  · linarith [baseAnglePos]

/-- The rational-family factors
are positive on the selected open parameter interval. -/
private lemma parameterSetBounds (ν : ℝ) (hν : ν ∈ parameterSet) :
    0 < ν ∧ 0 < 2 * baseAngle - ν ∧ 0 < baseAngle + ν ∧
      0 < 2 * ν - baseAngle := by
  -- The open interval is contained in the corresponding closed interval.
  exact parameterClosureBounds ν (Set.Ioo_subset_Icc_self hν)

/-- On `parameterSet`, the two rational cycle coordinates differ by the
parameter. -/
theorem cycleW_sub_cycleZ (ν : ℝ) (hν : ν ∈ parameterSet) :
    cycleW ν - cycleZ ν = ν := by
  -- Clear the common positive denominator of the rational coordinates.
  have hb := parameterSetBounds ν hν
  rw [cycleW_def, cycleZ_def]
  rw [← sub_div]
  apply (div_eq_iff hb.2.2.2.ne').mpr
  ring

/-- On `parameterSet`, the reciprocal product of `cycleK` and `cycleZ` is
`baseAngle + ν`. -/
theorem one_div_cycleK_mul_cycleZ (ν : ℝ) (hν : ν ∈ parameterSet) :
    1 / (cycleK ν * cycleZ ν) = baseAngle + ν := by
  -- Cancel the nonzero factors in Kz before taking the reciprocal.
  have hb := parameterSetBounds ν hν
  rw [cycleK_def, cycleZ_def]
  field_simp [hb.1.ne', hb.2.1.ne', hb.2.2.1.ne', hb.2.2.2.ne']

/-- On `parameterSet`, the reciprocal product of `cycleK` and `cycleW` is
`2 * baseAngle - ν`. -/
theorem one_div_cycleK_mul_cycleW (ν : ℝ) (hν : ν ∈ parameterSet) :
    1 / (cycleK ν * cycleW ν) = 2 * baseAngle - ν := by
  -- Cancel the nonzero factors in Kw before taking the reciprocal.
  have hb := parameterSetBounds ν hν
  rw [cycleK_def, cycleW_def]
  field_simp [hb.1.ne', hb.2.1.ne', hb.2.2.1.ne', hb.2.2.2.ne']

/-- The reference normalization equals `1 / (2 * baseAngle ^ 2)`. -/
theorem kZero_eq :
    kZero = 1 / (2 * baseAngle ^ 2) := by
  -- Evaluate the explicit rational normalization at the base angle.
  rw [kZero_def, cycleK_def]
  field_simp [baseAnglePos.ne']
  all_goals ring

/-- Away from its poles,
`cycleK` has the strict derivative given by its rational cubic numerator. -/
private lemma hasStrictDerivAt_cycleK_of_ne (ν : ℝ) (hν : ν ≠ 0)
    (hleft : 2 * baseAngle - ν ≠ 0) (hright : baseAngle + ν ≠ 0) :
    HasStrictDerivAt cycleK
      ((2 * baseAngle ^ 3 + 2 * baseAngle ^ 2 * ν -
          5 * baseAngle * ν ^ 2 + 4 * ν ^ 3) /
        (ν * (2 * baseAngle - ν) * (baseAngle + ν)) ^ 2) ν := by
  -- Differentiate the numerator and its three denominator factors.
  have hid : HasStrictDerivAt (fun t : ℝ ↦ t) 1 ν := hasStrictDerivAt_id ν
  have hnum : HasStrictDerivAt (fun t : ℝ ↦ 2 * t - baseAngle) (2 * 1) ν :=
    (hid.const_mul 2).sub_const baseAngle
  have hden := (hid.mul (hid.const_sub (2 * baseAngle))).mul
    (hid.const_add baseAngle)
  have hd := hnum.fun_div hden (mul_ne_zero (mul_ne_zero hν hleft) hright)
  -- The quotient-rule numerator is exactly the displayed cubic polynomial.
  have hvalue :
      ((2 * 1) * (ν * (2 * baseAngle - ν) * (baseAngle + ν)) -
          (2 * ν - baseAngle) *
            ((1 * (2 * baseAngle - ν) + ν * -1) * (baseAngle + ν) +
              (ν * (2 * baseAngle - ν)) * 1)) /
        (ν * (2 * baseAngle - ν) * (baseAngle + ν)) ^ 2 =
      (2 * baseAngle ^ 3 + 2 * baseAngle ^ 2 * ν -
          5 * baseAngle * ν ^ 2 + 4 * ν ^ 3) /
        (ν * (2 * baseAngle - ν) * (baseAngle + ν)) ^ 2 := by
    ring
  rw [funext cycleK_def]
  exact hd.congr_deriv hvalue

/-- The derivative of `cycleK` at `baseAngle` is
`3 / (4 * baseAngle ^ 3)`. -/
theorem hasDerivAt_cycleK_baseAngle :
    HasDerivAt cycleK (3 / (4 * baseAngle ^ 3)) baseAngle := by
  -- Specialize the quotient derivative and normalize its coefficient.
  have hleft : 2 * baseAngle - baseAngle ≠ 0 := by
    linarith [baseAnglePos]
  have hright : baseAngle + baseAngle ≠ 0 := by
    linarith [baseAnglePos]
  have hd := (hasStrictDerivAt_cycleK_of_ne baseAngle
    baseAnglePos.ne' hleft hright).hasDerivAt
  have hvalue :
      (2 * baseAngle ^ 3 + 2 * baseAngle ^ 2 * baseAngle -
        5 * baseAngle * baseAngle ^ 2 + 4 * baseAngle ^ 3) /
        (baseAngle * (2 * baseAngle - baseAngle) *
          (baseAngle + baseAngle)) ^ 2 = 3 / (4 * baseAngle ^ 3) := by
    field_simp [baseAnglePos.ne']
    all_goals ring
  exact hd.congr_deriv hvalue

/-- The strict derivative of `cycleK` at `baseAngle` is
`3 / (4 * baseAngle ^ 3)`. -/
theorem hasStrictDerivAt_cycleK_baseAngle :
    HasStrictDerivAt cycleK (3 / (4 * baseAngle ^ 3)) baseAngle := by
  -- The rational derivative is strict; uniqueness identifies its coefficient.
  have hleft : 2 * baseAngle - baseAngle ≠ 0 := by
    linarith [baseAnglePos]
  have hright : baseAngle + baseAngle ≠ 0 := by
    linarith [baseAnglePos]
  have hd := hasStrictDerivAt_cycleK_of_ne baseAngle
    baseAnglePos.ne' hleft hright
  exact hd.congr_deriv (hd.hasDerivAt.unique hasDerivAt_cycleK_baseAngle)

/-- The derivative coefficient of `cycleK` at `baseAngle` is positive. -/
theorem cycleK_derivCoefficient_pos :
    0 < 3 / (4 * baseAngle ^ 3) := by
  -- The base angle and all powers in the derivative denominator are positive.
  have ha := baseAnglePos
  positivity

/-- The selected parameter interval is a neighborhood of `baseAngle`. -/
theorem parameterSet_mem_nhds :
    parameterSet ∈ 𝓝 baseAngle := by
  -- The base angle lies strictly between the chosen endpoints.
  rw [parameterSet_def]
  have hleft : 3 * baseAngle / 4 < baseAngle := by
    linarith [baseAnglePos]
  have hright : baseAngle < 5 * baseAngle / 4 := by
    linarith [baseAnglePos]
  exact Ioo_mem_nhds hleft hright

/-- `cycleK` is continuous
on the closed parameter interval. -/
private lemma cycleKContinuousOnParameterClosure :
    ContinuousOn cycleK (Set.Icc (3 * baseAngle / 4) (5 * baseAngle / 4)) := by
  -- Strict differentiability supplies continuity at every point of the interval.
  intro ν hν
  have hb := parameterClosureBounds ν hν
  exact (hasStrictDerivAt_cycleK_of_ne ν hb.1.ne' hb.2.1.ne'
    hb.2.2.1.ne').hasDerivAt.continuousAt.continuousWithinAt

/-- The rational normalization
is strictly increasing on the closed parameter interval. -/
private lemma cycleKStrictMonoOnParameterClosure :
    StrictMonoOn cycleK (Set.Icc (3 * baseAngle / 4) (5 * baseAngle / 4)) := by
  -- Use the positive derivative to control the entire interval.
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    cycleKContinuousOnParameterClosure ?_
  intro ν hν
  rw [interior_Icc] at hν
  have hb := parameterSetBounds ν hν
  rw [(hasStrictDerivAt_cycleK_of_ne ν hb.1.ne' hb.2.1.ne'
    hb.2.2.1.ne').hasDerivAt.deriv]
  -- Translating by the left endpoint makes every cubic coefficient positive.
  have hshift : 0 < ν - 3 * baseAngle / 4 := sub_pos.mpr hν.1
  have hpoly :
      2 * baseAngle ^ 3 + 2 * baseAngle ^ 2 * ν -
          5 * baseAngle * ν ^ 2 + 4 * ν ^ 3 =
      19 / 8 * baseAngle ^ 3 +
        5 / 4 * baseAngle ^ 2 * (ν - 3 * baseAngle / 4) +
        4 * baseAngle * (ν - 3 * baseAngle / 4) ^ 2 +
        4 * (ν - 3 * baseAngle / 4) ^ 3 := by
    ring
  rw [hpoly]
  have ha := baseAnglePos
  apply div_pos
  · positivity
  · exact sq_pos_of_pos (mul_pos (mul_pos hb.1 hb.2.1) hb.2.2.1)

/-- The rational normalization is a bijection from the selected parameter
interval onto `normalizationSet`. -/
theorem cycleK_bijOn_parameterSet :
    Set.BijOn cycleK parameterSet normalizationSet := by
  -- Strict monotonicity gives injectivity; the codomain is exactly the image.
  rw [normalizationSet_def]
  exact (cycleKStrictMonoOnParameterClosure.mono Set.Ioo_subset_Icc_self).injOn.bijOn_image

/-- The selected normalization image is a neighborhood of `kZero`. -/
theorem normalizationSet_mem_nhds :
    normalizationSet ∈ 𝓝 kZero := by
  -- The nonzero strict derivative makes the image a neighborhood of K₀.
  rw [normalizationSet_def, kZero_def,
    ← hasStrictDerivAt_cycleK_baseAngle.map_nhds_eq cycleK_derivCoefficient_pos.ne']
  exact Filter.image_mem_map parameterSet_mem_nhds

/-- The selected inverse maps `normalizationSet` into `parameterSet`. -/
theorem inverseParameter_mapsTo :
    Set.MapsTo inverseParameter normalizationSet parameterSet := by
  -- Surjectivity places the selected inverse in the parameter interval.
  exact cycleK_bijOn_parameterSet.surjOn.mapsTo_invFunOn

/-- The selected inverse and `cycleK` are two-sided inverses between the
selected parameter and normalization sets. -/
theorem inverseParameter_invOn :
    Set.InvOn inverseParameter cycleK parameterSet normalizationSet := by
  -- The canonical inverse-on-set API supplies both inverse identities.
  exact cycleK_bijOn_parameterSet.invOn_invFunOn

/-- The rational normalization and both cycle coordinates are positive on
`parameterSet`. -/
theorem cycleFamily_mapsTo_positive :
    Set.MapsTo (fun ν : ℝ ↦ (cycleK ν, cycleZ ν, cycleW ν)) parameterSet
      (Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
  -- Every numerator and denominator has positive factors on this interval.
  intro ν hν
  have hb := parameterSetBounds ν hν
  simp only [Set.mem_prod, Set.mem_Ioi, cycleK_def, cycleZ_def, cycleW_def]
  exact ⟨div_pos hb.2.2.2 (mul_pos (mul_pos hb.1 hb.2.1) hb.2.2.1),
    div_pos (mul_pos hb.1 hb.2.1) hb.2.2.2,
    div_pos (mul_pos hb.1 hb.2.2.1) hb.2.2.2⟩

/-- The selected inverse gives
positive normalization and rational coordinates on `normalizationSet`. -/
private lemma inverseCycleFamilyPositive (K : ℝ) (hK : K ∈ normalizationSet) :
    0 < K ∧ 0 < cycleZ (inverseParameter K) ∧ 0 < cycleW (inverseParameter K) := by
  -- Remove product-set membership and transport the normalization once.
  have hfamily := cycleFamily_mapsTo_positive (inverseParameter_mapsTo hK)
  simpa only [Set.mem_prod, Set.mem_Ioi, inverseParameter_invOn.2 hK] using hfamily

/-- The slope quotient of a quadratic state is its coordinate plus the
reciprocal product of its nonzero normalization and coordinate. -/
private lemma quadraticStateSlope (K u : ℝ) (hK : K ≠ 0) (hu : u ≠ 0) :
    (1 + K * u ^ 2) / (K * u) = u + 1 / (K * u) := by
  -- Clearing the common denominator leaves a polynomial identity.
  field_simp [hK, hu]
  all_goals ring

/-- The even-state slope is the selected `cycleZ` coordinate plus
`2 * baseAngle`. -/
theorem slope_evenState (K : ℝ) (hK : K ∈ normalizationSet) :
    Normalized.slope (evenState K) =
      cycleZ (inverseParameter K) + 2 * baseAngle := by
  -- Express V/C as w + 1/(Kw), then use the two rational identities.
  have hν := inverseParameter_mapsTo hK
  have hpos := inverseCycleFamilyPositive K hK
  have hrecip := one_div_cycleK_mul_cycleW _ hν
  rw [inverseParameter_invOn.2 hK] at hrecip
  rw [Normalized.slope_def, evenState_apply]
  dsimp only
  rw [quadraticStateSlope K _ hpos.1.ne' hpos.2.2.ne', hrecip]
  linarith [cycleW_sub_cycleZ _ hν]

/-- The odd-state slope is the selected `cycleW` coordinate plus `baseAngle`. -/
theorem slope_oddState (K : ℝ) (hK : K ∈ normalizationSet) :
    Normalized.slope (oddState K) = cycleW (inverseParameter K) + baseAngle := by
  -- Express V/C as z + 1/(Kz), then use the two rational identities.
  have hν := inverseParameter_mapsTo hK
  have hpos := inverseCycleFamilyPositive K hK
  have hrecip := one_div_cycleK_mul_cycleZ _ hν
  rw [inverseParameter_invOn.2 hK] at hrecip
  rw [Normalized.slope_def, oddState_apply]
  dsimp only
  rw [quadraticStateSlope K _ hpos.1.ne' hpos.2.1.ne', hrecip]
  linarith [cycleW_sub_cycleZ _ hν]

/-- The limiting stage with coefficient `2 * baseAngle` maps the even state to
the odd state. -/
theorem evenToOdd (K : ℝ) (hK : K ∈ normalizationSet) :
    Normalized.leadingStage (2 * baseAngle) (evenState K) = oddState K := by
  -- Subtracting the even-stage coefficient leaves the z coordinate.
  rw [Normalized.leadingStage_apply, ← Normalized.slope_def, slope_evenState K hK]
  simp only [add_sub_cancel_right, evenState_apply, oddState_apply]

/-- The limiting stage with coefficient `baseAngle` maps the odd state back to
the even state. -/
theorem oddToEven (K : ℝ) (hK : K ∈ normalizationSet) :
    Normalized.leadingStage baseAngle (oddState K) = evenState K := by
  -- Subtracting the odd-stage coefficient leaves the w coordinate.
  rw [Normalized.leadingStage_apply, ← Normalized.slope_def, slope_oddState K hK]
  simp only [add_sub_cancel_right, evenState_apply, oddState_apply]

/-- On `normalizationSet`, the symmetric matrix reconstructed from the even
state has determinant `K`. -/
theorem evenState_det (K : ℝ) (hK : K ∈ normalizationSet) :
    Matrix.det
      (RealSymmetric2.matrix (evenState K).1 (evenState K).2.1 (evenState K).2.2) = K := by
  -- Express the normalization as a member of the rational family.
  rcases hK with ⟨ν, _, rfl⟩
  -- The off-diagonal square cancels the quadratic diagonal contribution.
  simp only [evenState_apply, RealSymmetric2.matrix_eq, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- On `normalizationSet`, the symmetric matrix reconstructed from the odd
state has determinant `K`. -/
theorem oddState_det (K : ℝ) (hK : K ∈ normalizationSet) :
    Matrix.det
      (RealSymmetric2.matrix (oddState K).1 (oddState K).2.1 (oddState K).2.2) = K := by
  -- Express the normalization as a member of the rational family.
  rcases hK with ⟨ν, _, rfl⟩
  -- The same quadratic cancellation gives determinant K in the odd phase.
  simp only [oddState_apply, RealSymmetric2.matrix_eq, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The first diagonal and off-diagonal coordinates of the even state are
positive on `normalizationSet`. -/
theorem evenState_mapsTo_positive :
    Set.MapsTo evenState normalizationSet
      (Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.univ)) := by
  -- Transport the positive rational family along the selected inverse.
  intro K hK
  have hpos := inverseCycleFamilyPositive K hK
  exact ⟨hpos.1, mul_pos hpos.1 hpos.2.2, Set.mem_univ _⟩

/-- The first diagonal and off-diagonal coordinates of the odd state are
positive on `normalizationSet`. -/
theorem oddState_mapsTo_positive :
    Set.MapsTo oddState normalizationSet
      (Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.univ)) := by
  -- The odd off-diagonal coordinate is a product of positive factors.
  intro K hK
  have hpos := inverseCycleFamilyPositive K hK
  exact ⟨hpos.1, mul_pos hpos.1 hpos.2.1, Set.mem_univ _⟩

/-- The selected inverse sends `kZero` to `baseAngle`. -/
theorem inverseParameter_kZero :
    inverseParameter kZero = baseAngle := by
  -- Apply the left inverse at the interior reference parameter.
  have hbase : baseAngle ∈ parameterSet := by
    rw [parameterSet_def]
    constructor
    · linarith [baseAnglePos]
    · linarith [baseAnglePos]
  exact inverseParameter_invOn.1 hbase

/-- At `kZero`, the selected `cycleZ` coordinate equals `baseAngle`. -/
theorem cycleZ_inverseParameter_kZero :
    cycleZ (inverseParameter kZero) = baseAngle := by
  -- At the reference parameter the rational z coordinate reduces to a.
  rw [inverseParameter_kZero, cycleZ_def]
  field_simp [baseAnglePos.ne']

/-- At `kZero`, the selected `cycleW` coordinate equals `2 * baseAngle`. -/
theorem cycleW_inverseParameter_kZero :
    cycleW (inverseParameter kZero) = 2 * baseAngle := by
  -- At the reference parameter the rational w coordinate reduces to 2a.
  rw [inverseParameter_kZero, cycleW_def]
  field_simp [baseAnglePos.ne']
  all_goals ring

/-- The even state at `kZero` is `evenReference`. -/
theorem evenState_kZero :
    evenState kZero = evenReference := by
  -- Substitute w = 2a and K₀ = 1/(2a²) in the even coordinates.
  rw [evenState_apply, cycleW_inverseParameter_kZero, evenReference_def]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · rw [kZero_eq]
    field_simp [baseAnglePos.ne']
  · rw [kZero_eq]
    field_simp [baseAnglePos.ne']
    all_goals ring

/-- The odd state at `kZero` is `oddReference`. -/
theorem oddState_kZero :
    oddState kZero = oddReference := by
  -- Substitute z = a and K₀ = 1/(2a²) in the odd coordinates.
  rw [oddState_apply, cycleZ_inverseParameter_kZero, oddReference_def]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · rw [kZero_eq]
    field_simp [baseAnglePos.ne']
  · rw [kZero_eq]
    field_simp [baseAnglePos.ne']
    all_goals ring

/-- The slope of `evenReference` is `3 * baseAngle`. -/
theorem slope_evenReference :
    Normalized.slope evenReference = 3 * baseAngle := by
  -- Evaluate the quotient of the two explicit even reference coordinates.
  rw [Normalized.slope_def, evenReference_def]
  dsimp only
  field_simp [baseAnglePos.ne']

/-- The slope of `oddReference` is `3 * baseAngle`. -/
theorem slope_oddReference :
    Normalized.slope oddReference = 3 * baseAngle := by
  -- Evaluate the quotient of the two explicit odd reference coordinates.
  rw [Normalized.slope_def, oddReference_def]
  dsimp only
  field_simp [baseAnglePos.ne']

end DFP.Polar.TwoCycle
