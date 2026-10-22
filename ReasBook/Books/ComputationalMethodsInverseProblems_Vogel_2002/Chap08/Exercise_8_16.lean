/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4_1.Approximation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_16.ERealUniformity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_18

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

open scoped VariationalRegularization.Approximation

/-- Helper for Exercise 8.16: the pointwise norm bound is preserved by negation. -/
lemma admissibleTestField_negNormLeOne
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖(-v.toTestFunction) x‖ ≤ 1 := by
  -- Negation does not change the pointwise norm of the test field.
  intro x hx
  simpa using v.norm_le_one x hx

namespace AdmissibleTestField

/-- Helper for Exercise 8.16: the pointwise negative of an admissible test field is admissible. -/
def neg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    AdmissibleTestField Ω :=
  ofTestFunction (-v.toTestFunction) (admissibleTestField_negNormLeOne v)

/-- Helper for Exercise 8.16: the underlying test function of `v.neg` is `-v.toTestFunction`. -/
@[simp] theorem neg_toTestFunction
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    v.neg.toTestFunction = -v.toTestFunction := by
  -- The constructor `ofTestFunction` records the supplied negated test function verbatim.
  exact AdmissibleTestField.ofTestFunction_toTestFunction
    (-v.toTestFunction) (admissibleTestField_negNormLeOne v)

end AdmissibleTestField

namespace ApproximationUniformConvergence

/-- Helper for Exercise 8.16: the admissible divergence is continuous. -/
lemma admissibleDivergenceContinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    Continuous (admissibleDivergence v) := by
  -- Reuse the earlier Chapter 8 continuity API instead of rebuilding the divergence expansion.
  simpa using VariationalRegularization.admissibleDivergenceContinuous v

/-- Helper for Exercise 8.16: the admissible divergence has compact support. -/
lemma admissibleDivergenceHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    HasCompactSupport (admissibleDivergence v) := by
  -- Reuse the canonical compact-support API already proved in `Theorem_8_18`.
  simpa using VariationalRegularization.admissibleDivergenceHasCompactSupport v

/-- Helper for Exercise 8.16: the admissible divergence belongs to `L∞(Ω)`. -/
lemma admissibleDivergenceMemLpTop
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    MeasureTheory.MemLp (admissibleDivergence v) ⊤ (domainMeasure Ω) :=
  (admissibleDivergenceContinuous v).memLp_top_of_hasCompactSupport
    (admissibleDivergenceHasCompactSupport v) (domainMeasure Ω)

/-- Helper for Exercise 8.16: negating an admissible field negates its divergence. -/
@[simp] lemma admissibleDivergence_neg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence v.neg x = -admissibleDivergence v x := by
  -- Rewrite the derivative of the negated test field once, then simplify the coordinate sum.
  have hneg : fderiv ℝ (⇑(-v.toTestFunction)) x = -fderiv ℝ v.toTestFunction x := by
    change fderiv ℝ (fun y => -v.toTestFunction y) x = -fderiv ℝ v.toTestFunction x
    simp
  rw [admissibleDivergence_def, admissibleDivergence_def, AdmissibleTestField.neg_toTestFunction]
  rw [hneg]
  simp

/-- Helper for Exercise 8.16: the divergence pairing integrand is integrable. -/
lemma pairingIntegrable
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable (fun x ↦ f x * admissibleDivergence v x) (domainMeasure Ω) := by
  -- The `L¹` representative of `f` pairs integrably with the `L∞` divergence factor.
  have hf : MeasureTheory.MemLp (fun x ↦ f x) 1 (domainMeasure Ω) := by
    simpa using MeasureTheory.Lp.memLp f
  exact hf.integrable_mul (admissibleDivergenceMemLpTop v)

/-- Helper for Exercise 8.16: the negated pairing owner agrees with pairing against `v.neg`. -/
lemma negPairingIntegral_eq_pairing_neg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    (∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω) =
      admissibleDivergencePairing f v.neg := by
  -- Rewrite the negated divergence through `v.neg` and simplify the pointwise product.
  rw [admissibleDivergencePairing_def]
  simp [admissibleDivergence_neg, mul_comm]

/-- Helper for Exercise 8.16: the smooth penalty integrand is integrable on the finite domain. -/
lemma smoothPenaltyIntegrable
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable
      (fun x ↦ β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2))
      (domainMeasure Ω) := by
  -- On a finite-measure domain, continuity plus the uniform bound by `β` gives integrability.
  have hcont :
      Continuous fun x : EuclideanSpace ℝ (Fin d) ↦
        β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) := by
    have hv : Continuous v.toTestFunction := v.toTestFunction.continuous
    exact (Real.continuous_sqrt.comp
      (continuous_const.sub ((hv.norm).pow 2))).const_mul β
  refine MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable β ?_
  rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
  · filter_upwards with x hx
    have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
    have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
      nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
    have hinside_nonneg : 0 ≤ 1 - ‖v.toTestFunction x‖ ^ 2 := sub_nonneg.mpr hsq_le
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) :=
      Real.sqrt_nonneg _
    have hsqrt_le_one : Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ≤ 1 := by
      nlinarith [Real.sq_sqrt hinside_nonneg, hsqrt_nonneg]
    have hmul_nonneg :
        0 ≤ β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) :=
      mul_nonneg (le_of_lt hβ) hsqrt_nonneg
    simpa [Real.norm_of_nonneg hmul_nonneg] using
      mul_le_mul_of_nonneg_left hsqrt_le_one (le_of_lt hβ)
  · exact Ω.2.measurableSet

/-- Helper for Exercise 8.16: the smooth penalty integrand is nonnegative almost everywhere. -/
lemma smoothPenalty_nonneg_ae
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (β : ℝ)
    (hβ : 0 < β)
    (v : AdmissibleTestField Ω) :
    ∀ᵐ x ∂domainMeasure Ω,
      0 ≤ β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) := by
  -- The square-root factor is nonnegative, and the scalar `β` is positive.
  rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
  · filter_upwards with x hx
    have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
    have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
      nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
    have hinside_nonneg : 0 ≤ 1 - ‖v.toTestFunction x‖ ^ 2 := sub_nonneg.mpr hsq_le
    exact mul_nonneg (le_of_lt hβ) (Real.sqrt_nonneg _)
  · exact Ω.2.measurableSet

/-- Helper for Exercise 8.16: the smooth penalty integral is bounded by `β * Vol(Ω)`. -/
lemma smoothPenaltyIntegral_le_volume
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    (v : AdmissibleTestField Ω) :
    ∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ∂domainMeasure Ω ≤
      β * (domainMeasure Ω Set.univ).toReal := by
  -- Compare the penalty integrand with the constant function `β` and integrate that bound.
  have hbound :
      ∀ᵐ x ∂domainMeasure Ω,
        β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ≤ β := by
    rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
    · filter_upwards with x hx
      have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
      have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
        nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
      have hinside_nonneg : 0 ≤ 1 - ‖v.toTestFunction x‖ ^ 2 := sub_nonneg.mpr hsq_le
      have hsqrt_le_one : Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ≤ 1 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) := Real.sqrt_nonneg _
        nlinarith [Real.sq_sqrt hinside_nonneg, hsqrt_nonneg]
      exact mul_le_of_le_one_right (le_of_lt hβ) hsqrt_le_one
    · exact Ω.2.measurableSet
  have hmono := MeasureTheory.integral_mono_ae
    (smoothPenaltyIntegrable β hβ v)
    (MeasureTheory.integrable_const β)
    hbound
  simpa [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm] using hmono

/-- Helper for Exercise 8.16: the Huber penalty integrand is integrable on the finite domain. -/
lemma huberPenaltyIntegrable
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (ε : ℝ)
    (hε : 0 < ε)
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable
      (fun x ↦ (ε / 2) * ‖v.toTestFunction x‖ ^ 2)
      (domainMeasure Ω) := by
  -- On a finite-measure domain, continuity plus the uniform bound by `ε / 2` gives integrability.
  have hcont :
      Continuous fun x : EuclideanSpace ℝ (Fin d) ↦
        (ε / 2) * ‖v.toTestFunction x‖ ^ 2 := by
    have hv : Continuous v.toTestFunction := v.toTestFunction.continuous
    exact ((hv.norm).pow 2).const_mul (ε / 2)
  refine MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable (ε / 2) ?_
  rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
  · filter_upwards with x hx
    have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
    have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
      nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
    have hmul_nonneg :
        0 ≤ (ε / 2) * ‖v.toTestFunction x‖ ^ 2 := by
      positivity
    simpa [Real.norm_of_nonneg hmul_nonneg] using
      mul_le_mul_of_nonneg_left hsq_le (by positivity : 0 ≤ ε / 2)
  · exact Ω.2.measurableSet

/-- Helper for Exercise 8.16: the Huber penalty integrand is nonnegative almost everywhere. -/
lemma huberPenalty_nonneg_ae
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (hε : 0 < ε)
    (v : AdmissibleTestField Ω) :
    ∀ᵐ x ∂domainMeasure Ω,
      0 ≤ (ε / 2) * ‖v.toTestFunction x‖ ^ 2 := by
  -- Both factors in the Huber penalty are nonnegative.
  filter_upwards with x
  positivity

/-- Helper for Exercise 8.16: the Huber penalty integral is bounded by `(ε / 2) * Vol(Ω)`. -/
lemma huberPenaltyIntegral_le_volume
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (ε : ℝ)
    (hε : 0 < ε)
    (v : AdmissibleTestField Ω) :
    ∫ x, (ε / 2) * ‖v.toTestFunction x‖ ^ 2 ∂domainMeasure Ω ≤
      (ε / 2) * (domainMeasure Ω Set.univ).toReal := by
  -- Compare the Huber penalty with the constant function `ε / 2` and integrate that bound.
  have hbound :
      ∀ᵐ x ∂domainMeasure Ω,
        (ε / 2) * ‖v.toTestFunction x‖ ^ 2 ≤ ε / 2 := by
    rw [domainMeasure_def, MeasureTheory.ae_restrict_iff']
    · filter_upwards with x hx
      have hnormle : ‖v.toTestFunction x‖ ≤ 1 := v.norm_le_one x hx
      have hsq_le : ‖v.toTestFunction x‖ ^ 2 ≤ 1 := by
        nlinarith [hnormle, norm_nonneg (v.toTestFunction x)]
      exact mul_le_of_le_one_right (by positivity : 0 ≤ ε / 2) hsq_le
    · exact Ω.2.measurableSet
  have hmono := MeasureTheory.integral_mono_ae
    (huberPenaltyIntegrable ε hε v)
    (MeasureTheory.integrable_const (ε / 2))
    hbound
  simpa [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm] using hmono

/-- Helper for Exercise 8.16: the zero admissible field gives zero divergence. -/
@[simp] lemma admissibleDivergence_zero
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence (AdmissibleTestField.zero Ω) x = 0 := by
  -- Rewrite the derivative of the zero test field and simplify the coordinate sum.
  have hzero :
      fderiv ℝ (⇑(0 : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)) x = 0 := by
    change fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d))) x = 0
    simp
  rw [admissibleDivergence_def, AdmissibleTestField.zero_toTestFunction, hzero]
  simp

/-- Helper for Exercise 8.16: the total variation is nonnegative. -/
lemma totalVariation_nonneg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    (0 : EReal) ≤ totalVariation f := by
  -- The zero admissible field contributes the value `0` to the defining supremum.
  rw [totalVariation_def]
  refine le_sSup ?_
  refine ⟨AdmissibleTestField.zero Ω, by
    simp [admissibleDivergencePairing_def, admissibleDivergence_zero]⟩

/-- Helper for Exercise 8.16: the Huber approximation is nonnegative. -/
lemma huberApproxTotalVariation_nonneg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    (0 : EReal) ≤ J_ε ε f := by
  -- The zero admissible field contributes the value `0` to the defining supremum of `J_ε`.
  rw [huberApproxTotalVariation_def]
  refine le_sSup ?_
  refine ⟨AdmissibleTestField.zero Ω, ?_⟩
  simp [AdmissibleTestField.zero_toTestFunction, admissibleDivergence_zero]

/-- Helper for Exercise 8.16: ordered nonnegative `EReal` distance is the nonnegative
difference. -/
lemma edist_eq_toENNReal_sub_of_le
    {a b : EReal}
    (ha : 0 ≤ a)
    (hab : a ≤ b) :
    edist a b = (b - a).toENNReal := by
  -- Route correction: normalize the weak `EReal` distance on the ordered nonnegative cone before
  -- applying any additive error bound.
  revert ha hab
  refine EReal.induction₂
    (P := fun a b ↦ 0 ≤ a → a ≤ b → edist a b = (b - a).toENNReal)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b
  · intro _ _
    simp
  · intro x hx _ hab
    simp at hab
  · intro _ hab
    simp at hab
  · intro x hx _ hab
    simp at hab
  · intro _ hab
    simp at hab
  · intro x hx _ _
    rfl
  · intro x hx _ hab
    simp at hab
  · intro _ _
    rfl
  · -- On finite reals, the weak `EReal` distance is the nonnegative real difference.
    intro x y hx hxy
    have hx' : 0 ≤ x := by
      exact_mod_cast hx
    have hxE : (0 : EReal) ≤ (x : EReal) := by
      exact_mod_cast hx'
    have hxy' : x ≤ y := by
      exact_mod_cast hxy
    rw [EReal.toENNReal_sub hxE]
    change edist (x : WithTop ℝ) (y : WithTop ℝ) = ENNReal.ofReal y - ENNReal.ofReal x
    change edist x y = ENNReal.ofReal y - ENNReal.ofReal x
    rw [edist_dist]
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy'), neg_sub]
    simpa using ENNReal.ofReal_sub y hx'
  · intro _ hab
    simp at hab
  · intro x hx ha _
    have ha' : 0 ≤ x := by
      exact_mod_cast ha
    exact (not_le_of_gt hx ha').elim
  · intro x hx ha _
    have ha' : 0 ≤ x := by
      exact_mod_cast ha
    exact (not_le_of_gt hx ha').elim
  · intro ha _
    simp at ha
  · intro x hx ha _
    simp at ha
  · intro ha _
    simp at ha
  · intro x hx ha _
    simp at ha
  · intro ha _
    simp at ha

/-- Helper for Exercise 8.16: `edist` on nonnegative ordered `EReal`s is controlled by a real
upper error term. -/
lemma edist_le_of_nonneg_le_add
    {a b : EReal}
    {c : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hbc : b ≤ a + c)
    (_hc : 0 ≤ c) :
    edist a b ≤ ENNReal.ofReal c := by
  -- First rewrite the ordered nonnegative distance as a nonnegative `EReal` difference.
  calc
    edist a b = (b - a).toENNReal :=
      edist_eq_toENNReal_sub_of_le ha hab
    _ ≤ ((c : EReal)).toENNReal :=
      EReal.toENNReal_le_toENNReal (EReal.sub_le_of_le_add' hbc)
    _ = ENNReal.ofReal c := by
      simp

/-- Helper for Exercise 8.16: the Chapter 8 smooth approximation satisfies the source order
window around `TV`. -/
lemma smoothNormApproxTotalVariation_orderBounds
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    totalVariation f ≤ J_β β f ∧
      J_β β f ≤ totalVariation f + (((β * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal) := by
  constructor
  · -- Compare each divergence pairing with the `J_β` witness given by the negated test field.
    refine totalVariation_le_of_forall_admissibleDivergencePairing_le f ?_
    intro v
    rw [smoothNormApproxTotalVariation_def]
    have hmono :
        ∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω ≤
          ∫ x, f x * admissibleDivergence v x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2) ∂domainMeasure Ω := by
      have hleft :
          MeasureTheory.Integrable
            (fun x ↦ f x * admissibleDivergence v x) (domainMeasure Ω) :=
        pairingIntegrable f v
      have hright := smoothPenaltyIntegrable β hβ v.neg
      refine MeasureTheory.integral_mono_ae hleft (hleft.add hright) ?_
      filter_upwards [smoothPenalty_nonneg_ae β hβ v.neg] with x hx
      linarith
    have hwitness_eq :
        (((∫ x, f x * admissibleDivergence v x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
          ∂domainMeasure Ω) : ℝ) : EReal) =
          (((∫ x, (-(f x)) * admissibleDivergence v.neg x +
              β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
            ∂domainMeasure Ω) : ℝ) : EReal) := by
      -- Route correction: rewrite the `v.neg` witness pointwise instead of fighting the `Lp`-neg
      -- normal form inside the main inequality.
      congr 1
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      simp [admissibleDivergence_neg, mul_comm]
    calc
      (admissibleDivergencePairing f v : EReal)
          = (((∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω) : ℝ) : EReal) := by
              rw [admissibleDivergencePairing_def]
      _ ≤ (((∫ x, f x * admissibleDivergence v x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
          ∂domainMeasure Ω) : ℝ) : EReal) := by
              exact_mod_cast hmono
      _ = (((∫ x, (-(f x)) * admissibleDivergence v.neg x +
            β * Real.sqrt (1 - ‖v.neg.toTestFunction x‖ ^ 2)
          ∂domainMeasure Ω) : ℝ) : EReal) := hwitness_eq
      _ ≤ sSup (Set.range fun u : AdmissibleTestField Ω ↦
            (((∫ x, (-(f x)) * admissibleDivergence u x +
                    β * Real.sqrt (1 - ‖u.toTestFunction x‖ ^ 2)
                  ∂domainMeasure Ω) : ℝ) : EReal)) := by
              exact le_sSup ⟨v.neg, rfl⟩
  · -- Split the defining integral and bound the pairing and penalty terms separately.
    rw [smoothNormApproxTotalVariation_def]
    refine sSup_le ?_
    rintro _ ⟨v, rfl⟩
    calc
      (((∫ x, (-(f x)) * admissibleDivergence v x +
              β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
            ∂domainMeasure Ω) : ℝ) : EReal)
          = (((∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω) : ℝ) : EReal) +
              (((∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
                  ∂domainMeasure Ω) : ℝ) : EReal) := by
              have hleft₀ :
                  MeasureTheory.Integrable
                    (fun x ↦ ((-f) x) * admissibleDivergence v x) (domainMeasure Ω) :=
                pairingIntegrable (-f) v
              have hleft :
                  MeasureTheory.Integrable
                    (fun x ↦ (-(f x)) * admissibleDivergence v x) (domainMeasure Ω) := by
                refine hleft₀.congr ?_
                filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
                rw [hx]
                simp [neg_mul]
              have hright := smoothPenaltyIntegrable β hβ v
              rw [MeasureTheory.integral_add hleft hright]
              norm_num
      _ = (admissibleDivergencePairing f v.neg : EReal) +
            (((∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
                ∂domainMeasure Ω) : ℝ) : EReal) := by
              rw [negPairingIntegral_eq_pairing_neg]
      _ ≤ totalVariation f + (((β * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal) := by
              exact add_le_add
                (admissibleDivergencePairing_le_totalVariation f v.neg)
                (by exact_mod_cast smoothPenaltyIntegral_le_volume β hβ v)

/-- Helper for Exercise 8.16: the Chapter 8 Huber approximation satisfies the source order window
around `TV`. -/
lemma huberApproxTotalVariation_orderBounds
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (ε : ℝ)
    (hε : 0 < ε)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    totalVariation f -
        (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) ≤
      J_ε ε f ∧
      J_ε ε f ≤ totalVariation f := by
  let err : EReal := (((ε / 2) * (domainMeasure Ω Set.univ).toReal : ℝ) : EReal)
  constructor
  · -- First prove the additive version `TV ≤ J_ε + ((ε / 2)Vol(Ω))`, then rewrite it back.
    have hadd :
        totalVariation f ≤
          J_ε ε f + err := by
      refine totalVariation_le_of_forall_admissibleDivergencePairing_le f ?_
      intro v
      rw [huberApproxTotalVariation_def]
      have hpair₀ :
          MeasureTheory.Integrable
            (fun x ↦ ((-f) x) * admissibleDivergence v.neg x) (domainMeasure Ω) :=
        pairingIntegrable (-f) v.neg
      have hpair :
          MeasureTheory.Integrable
            (fun x ↦ (-(f x)) * admissibleDivergence v.neg x) (domainMeasure Ω) := by
        -- Normalize the negated `Lp` representative to the pointwise spelling used in the
        -- witness integrand.
        refine hpair₀.congr ?_
        filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
        rw [hx]
        simp
      have hwitness :
          MeasureTheory.Integrable
            (fun x ↦
              (-(f x)) * admissibleDivergence v.neg x -
                (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2) (domainMeasure Ω) :=
        hpair.sub (huberPenaltyIntegrable ε hε v.neg)
      have hdecomp :
          (admissibleDivergencePairing f v : EReal) =
            (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                    (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) +
              (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal) := by
        -- Split the pairing into the `J_ε` witness term plus the Huber penalty remainder.
        rw [admissibleDivergencePairing_def]
        calc
          (((∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω) : ℝ) : EReal)
              = (((∫ x,
                    ((-(f x)) * admissibleDivergence v.neg x -
                        (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2) +
                      (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) := by
                    congr 1
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards with x
                    simp [admissibleDivergence_neg, sub_eq_add_neg, add_assoc, mul_comm]
          _ = (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                    (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) +
                (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal) := by
                    rw [MeasureTheory.integral_add hwitness (huberPenaltyIntegrable ε hε v.neg)]
                    norm_num
      calc
        (admissibleDivergencePairing f v : EReal)
            = (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                    (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                  ∂domainMeasure Ω) : ℝ) : EReal) +
                (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal) := hdecomp
        _ ≤ sSup (Set.range fun u : AdmissibleTestField Ω ↦
              (((∫ x, (-(f x)) * admissibleDivergence u x -
                      (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                    ∂domainMeasure Ω) : ℝ) : EReal)) + err := by
              have hwitness_le :
                  (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                          (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                        ∂domainMeasure Ω) : ℝ) : EReal) ≤
                    sSup (Set.range fun u : AdmissibleTestField Ω ↦
                      (((∫ x, (-(f x)) * admissibleDivergence u x -
                              (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                            ∂domainMeasure Ω) : ℝ) : EReal)) := by
                exact le_sSup
                  (s := Set.range fun u : AdmissibleTestField Ω ↦
                    (((∫ x, (-(f x)) * admissibleDivergence u x -
                            (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                          ∂domainMeasure Ω) : ℝ) : EReal))
                  ⟨v.neg, rfl⟩
              have hpen :
                  (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                        ∂domainMeasure Ω) : ℝ) : EReal) ≤ err := by
                simpa [err] using
                  (show
                    (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                          ∂domainMeasure Ω) : ℝ) : EReal) ≤
                      (((((ε / 2) * (domainMeasure Ω Set.univ).toReal) : ℝ) : EReal)) by
                      exact_mod_cast huberPenaltyIntegral_le_volume ε hε v.neg)
              have hsum :
                  (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                          (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                        ∂domainMeasure Ω) : ℝ) : EReal) +
                    (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                          ∂domainMeasure Ω) : ℝ) : EReal) ≤
                      sSup (Set.range fun u : AdmissibleTestField Ω ↦
                        (((∫ x, (-(f x)) * admissibleDivergence u x -
                                (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                              ∂domainMeasure Ω) : ℝ) : EReal)) + err :=
                add_le_add hwitness_le hpen
              calc
                (((∫ x, (-(f x)) * admissibleDivergence v.neg x -
                        (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                      ∂domainMeasure Ω) : ℝ) : EReal) +
                    (((∫ x, (ε / 2) * ‖v.neg.toTestFunction x‖ ^ 2
                          ∂domainMeasure Ω) : ℝ) : EReal)
                    ≤ sSup (Set.range fun u : AdmissibleTestField Ω ↦
                      (((∫ x, (-(f x)) * admissibleDivergence u x -
                              (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                            ∂domainMeasure Ω) : ℝ) : EReal)) + err := hsum
                _ ≤ sSup (Set.range fun u : AdmissibleTestField Ω ↦
                      (((∫ x, (-(f x)) * admissibleDivergence u x -
                              (ε / 2) * ‖u.toTestFunction x‖ ^ 2
                            ∂domainMeasure Ω) : ℝ) : EReal)) + err := by
                      exact le_rfl
    -- Convert the additive window back to the textbook subtraction form.
    have herr_bot : err ≠ ⊥ := by
      simpa [err, EReal.coe_mul] using
        (EReal.coe_ne_bot ((ε / 2) * (domainMeasure Ω Set.univ).toReal))
    have herr_top : err ≠ ⊤ := by
      simpa [err, EReal.coe_mul] using
        (EReal.coe_ne_top ((ε / 2) * (domainMeasure Ω Set.univ).toReal))
    simpa [err] using
      (EReal.sub_le_iff_le_add (Or.inl herr_bot) (Or.inl herr_top)).2 hadd
  · -- Bound each Huber witness above by the unpenalized total-variation pairing.
    rw [huberApproxTotalVariation_def]
    refine sSup_le ?_
    rintro _ ⟨v, rfl⟩
    have hpair₀ :
        MeasureTheory.Integrable
          (fun x ↦ ((-f) x) * admissibleDivergence v x) (domainMeasure Ω) :=
      pairingIntegrable (-f) v
    have hpair :
        MeasureTheory.Integrable
          (fun x ↦ (-(f x)) * admissibleDivergence v x) (domainMeasure Ω) := by
      -- Normalize the negated `Lp` representative to the pointwise spelling used here.
      refine hpair₀.congr ?_
      filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
      rw [hx]
      simp
    have hmono :
        ∫ x, (-(f x)) * admissibleDivergence v x -
            (ε / 2) * ‖v.toTestFunction x‖ ^ 2 ∂domainMeasure Ω ≤
          ∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω := by
      -- The Huber penalty is nonnegative, so subtracting it can only decrease the witness.
      refine MeasureTheory.integral_mono_ae
        (hpair.sub (huberPenaltyIntegrable ε hε v))
        hpair ?_
      filter_upwards [huberPenalty_nonneg_ae ε hε v] with x hx
      linarith
    calc
      (((∫ x, (-(f x)) * admissibleDivergence v x -
              (ε / 2) * ‖v.toTestFunction x‖ ^ 2
            ∂domainMeasure Ω) : ℝ) : EReal)
          ≤ (((∫ x, (-(f x)) * admissibleDivergence v x
                ∂domainMeasure Ω) : ℝ) : EReal) := by
              exact_mod_cast hmono
      _ = (admissibleDivergencePairing f v.neg : EReal) := by
            rw [negPairingIntegral_eq_pairing_neg]
      _ ≤ totalVariation f := admissibleDivergencePairing_le_totalVariation f v.neg

/-- Helper for Exercise 8.16: a sufficiently small smooth scalar error forces a small `EReal`
distance. -/
lemma smoothNormApproxTotalVariation_edist_lt_of_smallError
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    {δ : ENNReal}
    (_hδ : 0 < δ)
    (hsmall :
      ENNReal.ofReal (β * (domainMeasure Ω Set.univ).toReal) < δ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    edist (totalVariation f) (J_β β f) < δ := by
  -- Feed the smooth additive source window directly into the ordered `EReal` distance bridge.
  rcases smoothNormApproxTotalVariation_orderBounds β hβ f with ⟨hlower, hupper⟩
  have hbound :
      edist (totalVariation f) (J_β β f) ≤
        ENNReal.ofReal (β * (domainMeasure Ω Set.univ).toReal) :=
    edist_le_of_nonneg_le_add
      (a := totalVariation f)
      (b := J_β β f)
      (c := β * (domainMeasure Ω Set.univ).toReal)
      (totalVariation_nonneg f)
      hlower
      hupper
      (by positivity)
  exact lt_of_le_of_lt hbound hsmall

/-- Helper for Exercise 8.16: a sufficiently small Huber scalar error forces a small `EReal`
distance. -/
lemma huberApproxTotalVariation_edist_lt_of_smallError
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (ε : ℝ)
    (hε : 0 < ε)
    {δ : ENNReal}
    (_hδ : 0 < δ)
    (hsmall :
      ENNReal.ofReal ((ε / 2) * (domainMeasure Ω Set.univ).toReal) < δ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    edist (totalVariation f) (J_ε ε f) < δ := by
  -- Rewrite the subtraction-form Huber window as an additive bound, then apply the same bridge.
  let err : EReal := (((ε / 2) * (domainMeasure Ω Set.univ).toReal : ℝ) : EReal)
  rcases huberApproxTotalVariation_orderBounds ε hε f with ⟨hlower, hupper⟩
  have hadd :
      totalVariation f ≤
        J_ε ε f + err := by
    have herr_bot : err ≠ ⊥ := by
      simpa [err, EReal.coe_mul] using
        (EReal.coe_ne_bot ((ε / 2) * (domainMeasure Ω Set.univ).toReal))
    have herr_top : err ≠ ⊤ := by
      simpa [err, EReal.coe_mul] using
        (EReal.coe_ne_top ((ε / 2) * (domainMeasure Ω Set.univ).toReal))
    simpa [err] using
      (EReal.sub_le_iff_le_add (Or.inl herr_bot) (Or.inl herr_top)).1 hlower
  have hbound :
      edist (J_ε ε f) (totalVariation f) ≤
        ENNReal.ofReal ((ε / 2) * (domainMeasure Ω Set.univ).toReal) :=
    edist_le_of_nonneg_le_add
      (a := J_ε ε f)
      (b := totalVariation f)
      (c := (ε / 2) * (domainMeasure Ω Set.univ).toReal)
      (huberApproxTotalVariation_nonneg ε f)
      hupper
      hadd
      (by positivity)
  exact lt_of_le_of_lt (by simpa [edist_comm] using hbound) hsmall

end ApproximationUniformConvergence

/-- Exercise 8.16 (1). As `β → 0⁺`, the Chapter 8 smooth-norm approximation
`J_β`, represented by `smoothNormApproxTotalVariation`, converges uniformly on
`S` toward `TV`, represented by `totalVariation`. -/
theorem smoothNormApproxTotalVariation_tendstoUniformlyOn
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) :
    TendstoUniformlyOn
      smoothNormApproxTotalVariation
      totalVariation
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      S := by
  -- Reduce uniform convergence to eventual `edist` control and feed in the smooth small-error
  -- companion lemma.
  rw [EMetric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hscalar :
      Filter.Tendsto
        (fun β : ℝ ↦ β * (domainMeasure Ω Set.univ).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (0 * (domainMeasure Ω Set.univ).toReal)) :=
    (continuous_id.mul continuous_const).continuousAt.continuousWithinAt
  have hofReal :
      Filter.Tendsto
        (fun β : ℝ ↦ ENNReal.ofReal (β * (domainMeasure Ω Set.univ).toReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (ENNReal.ofReal (0 * (domainMeasure Ω Set.univ).toReal))) := by
    -- The scalar error term tends to `0`, so its `ofReal` image is eventually smaller than `δ`.
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hscalar
  have hsmall :
      ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ENNReal.ofReal (β * (domainMeasure Ω Set.univ).toReal) < δ := by
    simpa only [Set.mem_setOf_eq] using
      hofReal.eventually (Iio_mem_nhds (by simpa using hδ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with β hβ hsmallβ f hf
  exact ApproximationUniformConvergence.smoothNormApproxTotalVariation_edist_lt_of_smallError
    β hβ hδ hsmallβ f

/-- The `edist` reformulation of
`smoothNormApproxTotalVariation_tendstoUniformlyOn`. -/
theorem smoothNormApproxTotalVariation_tendstoUniformlyOn_edist
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) :
    ∀ δ : ENNReal,
      0 < δ →
        ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ f, f ∈ S → edist (totalVariation f) (smoothNormApproxTotalVariation β f) < δ := by
  simpa [EMetric.tendstoUniformlyOn_iff] using smoothNormApproxTotalVariation_tendstoUniformlyOn S

/-- Exercise 8.16 (2). As `ε → 0⁺`, the Chapter 8 Huber approximation `J_ε`,
 represented by `huberApproxTotalVariation`, converges uniformly on `S` toward
`TV`, represented by `totalVariation`. -/
theorem huberApproxTotalVariation_tendstoUniformlyOn
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) :
    TendstoUniformlyOn
      huberApproxTotalVariation
      totalVariation
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      S := by
  -- The Huber convergence proof is the same filter wrapper, now using the Huber small-error
  -- companion lemma.
  rw [EMetric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hscalar :
      Filter.Tendsto
        (fun ε : ℝ ↦ (ε / 2) * (domainMeasure Ω Set.univ).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((0 / 2) * (domainMeasure Ω Set.univ).toReal)) :=
    ((continuous_id.div_const (2 : ℝ)).mul continuous_const).continuousAt.continuousWithinAt
  have hofReal :
      Filter.Tendsto
        (fun ε : ℝ ↦ ENNReal.ofReal ((ε / 2) * (domainMeasure Ω Set.univ).toReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (ENNReal.ofReal ((0 / 2) * (domainMeasure Ω Set.univ).toReal))) := by
    -- As `ε → 0⁺`, the Huber scalar error term also tends to `0`.
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hscalar
  have hsmall :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ENNReal.ofReal ((ε / 2) * (domainMeasure Ω Set.univ).toReal) < δ := by
    simpa only [Set.mem_setOf_eq] using
      hofReal.eventually (Iio_mem_nhds (by simpa using hδ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmallε f hf
  exact ApproximationUniformConvergence.huberApproxTotalVariation_edist_lt_of_smallError
    ε hε hδ hsmallε f

/-- The `edist` reformulation of
`huberApproxTotalVariation_tendstoUniformlyOn`. -/
theorem huberApproxTotalVariation_tendstoUniformlyOn_edist
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) :
    ∀ δ : ENNReal,
      0 < δ →
        ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ f, f ∈ S → edist (totalVariation f) (huberApproxTotalVariation ε f) < δ := by
  simpa [EMetric.tendstoUniformlyOn_iff] using huberApproxTotalVariation_tendstoUniformlyOn S

end VariationalRegularization
