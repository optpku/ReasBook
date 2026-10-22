/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_14.BV
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Instances.EReal.Lemmas

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- Helper for Theorem 8.15: negating an admissible test field preserves the pointwise unit-ball
constraint. -/
theorem admissibleTestFieldNegNormLeOne
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖(-v.toTestFunction) x‖ ≤ 1 := by
  -- Negation does not change the pointwise norm of the test field.
  intro x hx
  simpa using v.norm_le_one x hx

namespace AdmissibleTestField

/-- Helper for Theorem 8.15: the pointwise negative of an admissible test field is admissible. -/
def neg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    AdmissibleTestField Ω :=
  ofTestFunction (-v.toTestFunction) (admissibleTestFieldNegNormLeOne v)

/-- Helper for Theorem 8.15: the underlying test function of `v.neg` is `-v.toTestFunction`. -/
@[simp]
theorem neg_toTestFunction
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    v.neg.toTestFunction = -v.toTestFunction := by
  -- The constructor records the negated test function verbatim.
  exact ofTestFunction_toTestFunction (-v.toTestFunction) (admissibleTestFieldNegNormLeOne v)

end AdmissibleTestField

/-- Helper for Theorem 8.15: the zero admissible field has zero divergence. -/
@[simp]
theorem admissibleDivergence_zero
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence (AdmissibleTestField.zero Ω) x = 0 := by
  -- Rewrite the derivative of the zero test field and simplify the coordinate sum.
  have hzero :
      fderiv ℝ (⇑(0 : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)) x = 0 := by
    change fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) ↦ (0 : EuclideanSpace ℝ (Fin d))) x = 0
    simp
  rw [admissibleDivergence_def, AdmissibleTestField.zero_toTestFunction, hzero]
  simp

/-- Helper for Theorem 8.15: rewrite the divergence in the kernel-stable `PiLp` coordinate
spelling used by the derivative regularity lemmas. -/
theorem admissibleDivergence_eq_sum_ofLpFDeriv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence v x =
      ∑ i : Fin d,
        (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
  -- This is the same divergence formula, spelled in the `PiLp` normal form used by the kernel.
  rw [admissibleDivergence_def]

/-- Helper for Theorem 8.15: each coordinate summand in the divergence formula is continuous. -/
theorem admissibleDivergenceSummandContinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (i : Fin d) :
    Continuous
      (fun x ↦
        (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i) := by
  -- Freeze the derivative direction first so continuity is proved in a stable normal form.
  have hderiv :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))) := by
    have happly :
        Continuous
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
            (fderiv ℝ v.toTestFunction p.1) p.2) :=
      v.toTestFunction.contDiff.continuous_fderiv_apply (by simp)
    have hfreeze :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin d) ↦
            (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              (fderiv ℝ v.toTestFunction p.1) p.2)
              (x, WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      happly.comp (continuous_id.prodMk continuous_const)
    simpa [PiLp.toLp_single] using hfreeze
  -- Postcompose with the continuous coordinate projection.
  have happly :
      Continuous (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i
  change Continuous
    (fun x ↦
      (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i)
        (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))))
  exact happly.comp hderiv

/-- Helper for Theorem 8.15: each coordinate summand in the divergence formula has compact
support. -/
theorem admissibleDivergenceSummandHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (i : Fin d) :
    HasCompactSupport
      (fun x ↦
        (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i) := by
  -- Keep the derivative evaluation in one spelling before pushing support through the projection.
  have hderiv :
      HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))) := by
    simpa using
      (v.toTestFunction.hasCompactSupport.fderiv_apply ℝ (WithLp.toLp 2 (Pi.single i (1 : ℝ))))
  have hcoord :
      HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i)
            (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ)))) :=
    hderiv.comp_left (g := fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) rfl
  simpa using hcoord

/-- Helper for Theorem 8.15: the admissible divergence is continuous. -/
theorem admissibleDivergenceContinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    Continuous (admissibleDivergence v) := by
  -- Rewrite once to the stable `PiLp` normal form and sum the coordinate continuity lemmas there.
  have hsum :
      admissibleDivergence v =
        fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
    funext x
    exact admissibleDivergence_eq_sum_ofLpFDeriv v x
  rw [hsum]
  exact continuous_finsetSum Finset.univ fun i _ ↦ admissibleDivergenceSummandContinuous v i

/-- Helper for Theorem 8.15: the normalized `PiLp` divergence sum has compact support. -/
theorem admissibleDivergenceNormalizedHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    HasCompactSupport
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i) := by
  let φ : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x ↦
    (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i
  have hφ : ∀ i ∈ Finset.univ, HasCompactSupport (φ i) := by
    intro i _
    simpa [φ] using admissibleDivergenceSummandHasCompactSupport v i
  have hsum :
      (∑ i : Fin d, φ i) =
        fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
    funext x
    simp [φ]
  -- Sum the coordinate support lemmas before transporting back to the source-facing divergence.
  rw [← hsum]
  exact HasCompactSupport.finset_sum (s := Finset.univ) hφ

/-- Helper for Theorem 8.15: the admissible divergence has compact support. -/
theorem admissibleDivergenceHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    HasCompactSupport (admissibleDivergence v) := by
  -- Transport the normalized compact-support statement back to the source-facing divergence.
  have hsum :
      admissibleDivergence v =
        fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
    funext x
    exact admissibleDivergence_eq_sum_ofLpFDeriv v x
  rw [hsum]
  exact admissibleDivergenceNormalizedHasCompactSupport v

/-- Helper for Theorem 8.15: the admissible divergence belongs to `L∞(Ω)`. -/
theorem admissibleDivergenceMemLpTop
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    MeasureTheory.MemLp (admissibleDivergence v) ⊤ (domainMeasure Ω) :=
  (admissibleDivergenceContinuous v).memLp_top_of_hasCompactSupport
    (admissibleDivergenceHasCompactSupport v) (domainMeasure Ω)

/-- Helper for Theorem 8.15: negating an admissible field negates its divergence. -/
@[simp]
theorem admissibleDivergence_neg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence v.neg x = -admissibleDivergence v x := by
  -- Rewrite the derivative of the negated test field once, then simplify the coordinate sum.
  have hneg : fderiv ℝ (⇑(-v.toTestFunction)) x = -fderiv ℝ v.toTestFunction x := by
    change fderiv ℝ (fun y ↦ -v.toTestFunction y) x = -fderiv ℝ v.toTestFunction x
    simp
  rw [admissibleDivergence_def, admissibleDivergence_def, AdmissibleTestField.neg_toTestFunction]
  rw [hneg]
  simp

/-- Helper for Theorem 8.15: pairing against a fixed admissible divergence defines a continuous
linear functional on `L¹(Ω)`. -/
def totalVariationPairingCLM
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Lp ℝ 1 (domainMeasure Ω) →L[ℝ] ℝ :=
  let divLp : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω) :=
    MeasureTheory.MemLp.toLp (admissibleDivergence v) (admissibleDivergenceMemLpTop v)
  ((ContinuousLinearMap.apply ℝ ℝ) divLp).comp
    (ContinuousLinearMap.lpPairing (μ := domainMeasure Ω) (p := (1 : ENNReal))
      (q := (⊤ : ENNReal)) (ContinuousLinearMap.mul ℝ ℝ))

/-- Helper for Theorem 8.15: the pairing continuous linear map evaluates to the original
divergence pairing. -/
theorem totalVariationPairingCLM_apply
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    totalVariationPairingCLM v f = admissibleDivergencePairing f v := by
  -- Unfold the packaging once, then use the canonical `Lp` pairing integral formula.
  rw [admissibleDivergencePairing_def, totalVariationPairingCLM]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp (admissibleDivergenceMemLpTop v)] with x hx
  simp [hx]

/-- Helper for Theorem 8.15: pairing a negated `L¹(Ω)` representative against `v` is the same as
pairing the original function against `v.neg`. -/
theorem admissibleDivergencePairing_neg_eq_pairing_negField
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    admissibleDivergencePairing (-f) v = admissibleDivergencePairing f v.neg := by
  -- Rewrite the negated `L¹` representative pointwise and absorb the sign into `v.neg`.
  rw [admissibleDivergencePairing_def, admissibleDivergencePairing_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
  rw [hx]
  simp [admissibleDivergence_neg, mul_comm]

/-- Helper for Theorem 8.15: the raw Chapter 8 total variation is nonnegative. -/
theorem lpTotalVariationNonneg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    (0 : EReal) ≤ VariationalRegularization.totalVariation f := by
  -- The zero admissible field contributes the value `0` to the defining supremum.
  rw [totalVariation_def]
  refine le_sSup ?_
  refine ⟨AdmissibleTestField.zero Ω, by
    simp [admissibleDivergencePairing_def, admissibleDivergence_zero]⟩

/-- Helper for Theorem 8.15: the raw Chapter 8 total variation of the zero function is zero. -/
theorem lpTotalVariationZero
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    VariationalRegularization.totalVariation (0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) = 0 := by
  -- Bound the supremum above by `0`, then combine with nonnegativity.
  apply le_antisymm
  · refine totalVariation_le_of_forall_admissibleDivergencePairing_le (0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ?_
    intro v
    have hpair : admissibleDivergencePairing (0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) v = 0 := by
      rw [admissibleDivergencePairing_def]
      calc
        ∫ x, ((0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) x) * admissibleDivergence v x ∂domainMeasure Ω
            = ∫ x, (0 : ℝ) ∂domainMeasure Ω := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards
                  [MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := (1 : ENNReal))
                    (μ := domainMeasure Ω)] with x hx
                rw [hx, Pi.zero_apply]
                simp
        _ = 0 := by simp
    simpa [hpair]
  · exact lpTotalVariationNonneg (0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))

/-- Helper for Theorem 8.15: the raw Chapter 8 total variation is subadditive on `L¹(Ω)`. -/
theorem lpTotalVariationAddLe
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    VariationalRegularization.totalVariation (f + g) ≤
      VariationalRegularization.totalVariation f + VariationalRegularization.totalVariation g := by
  -- Compare each admissible pairing with the sum of its two raw total-variation bounds.
  refine totalVariation_le_of_forall_admissibleDivergencePairing_le (f + g) ?_
  intro v
  calc
    (admissibleDivergencePairing (f + g) v : EReal)
        = (admissibleDivergencePairing f v : EReal) +
            (admissibleDivergencePairing g v : EReal) := by
              rw [← totalVariationPairingCLM_apply (Ω := Ω) v (f + g), map_add,
                totalVariationPairingCLM_apply, totalVariationPairingCLM_apply, EReal.coe_add]
    _ ≤ VariationalRegularization.totalVariation f + VariationalRegularization.totalVariation g :=
      add_le_add
        (admissibleDivergencePairing_le_totalVariation f v)
        (admissibleDivergencePairing_le_totalVariation g v)

/-- Helper for Theorem 8.15: the raw Chapter 8 total variation is invariant under negation. -/
theorem lpTotalVariationNeg
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    VariationalRegularization.totalVariation (-f) = VariationalRegularization.totalVariation f := by
  apply le_antisymm
  · refine totalVariation_le_of_forall_admissibleDivergencePairing_le (-f) ?_
    intro v
    rw [admissibleDivergencePairing_neg_eq_pairing_negField]
    exact admissibleDivergencePairing_le_totalVariation f v.neg
  · refine totalVariation_le_of_forall_admissibleDivergencePairing_le f ?_
    intro v
    have hpair :
        admissibleDivergencePairing f v =
          admissibleDivergencePairing (-f) v.neg := by
      rw [admissibleDivergencePairing_def, admissibleDivergencePairing_def]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_neg f] with x hx
      rw [hx]
      simp [admissibleDivergence_neg, mul_comm]
    rw [hpair]
    exact admissibleDivergencePairing_le_totalVariation (-f) v.neg

/-- Helper for Theorem 8.15: real scaling increases the raw Chapter 8 total variation by at most
the scalar norm. -/
theorem lpTotalVariationSmulLe
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (a : ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    VariationalRegularization.totalVariation (a • f) ≤
      (((‖a‖ : ℝ) : EReal) * VariationalRegularization.totalVariation f) := by
  by_cases ha_zero : a = 0
  · -- The zero scalar collapses the raw total variation to zero.
    subst ha_zero
    simp [lpTotalVariationZero]
  by_cases ha_nonneg : 0 ≤ a
  · -- In the nonnegative case, factor the scalar directly through the pairing CLM.
    refine totalVariation_le_of_forall_admissibleDivergencePairing_le (a • f) ?_
    intro v
    calc
      (admissibleDivergencePairing (a • f) v : EReal)
          = (a : EReal) * (admissibleDivergencePairing f v : EReal) := by
              rw [← totalVariationPairingCLM_apply (Ω := Ω) v (a • f), map_smul,
                totalVariationPairingCLM_apply, smul_eq_mul, EReal.coe_mul]
      _ ≤ (a : EReal) * VariationalRegularization.totalVariation f := by
            exact mul_le_mul_of_nonneg_left
              (admissibleDivergencePairing_le_totalVariation f v) (by exact_mod_cast ha_nonneg)
      _ = (((‖a‖ : ℝ) : EReal) * VariationalRegularization.totalVariation f) := by
            simp [Real.norm_of_nonneg ha_nonneg]
  · -- For negative scalars, move the sign into the admissible field and reuse the positive case.
    have ha_lt : a < 0 := lt_of_not_ge ha_nonneg
    refine totalVariation_le_of_forall_admissibleDivergencePairing_le (a • f) ?_
    intro v
    calc
      (admissibleDivergencePairing (a • f) v : EReal)
          = ((-a : ℝ) : EReal) * (admissibleDivergencePairing f v.neg : EReal) := by
              rw [show a • f = (-a) • (-f) by simpa using (neg_smul_neg a f).symm]
              rw [← totalVariationPairingCLM_apply (Ω := Ω) v ((-a) • (-f)), map_smul,
                totalVariationPairingCLM_apply, smul_eq_mul, EReal.coe_mul,
                admissibleDivergencePairing_neg_eq_pairing_negField]
      _ ≤ ((-a : ℝ) : EReal) * VariationalRegularization.totalVariation f := by
            exact mul_le_mul_of_nonneg_left
              (admissibleDivergencePairing_le_totalVariation f v.neg)
              (by exact_mod_cast le_of_lt (neg_pos.mpr ha_lt))
      _ = (((‖a‖ : ℝ) : EReal) * VariationalRegularization.totalVariation f) := by
            simp [Real.norm_of_nonpos (le_of_lt ha_lt)]

namespace BV

variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

/-- Two elements of `BV(Ω)` are equal once their underlying `L¹(Ω)` realizations agree. -/
@[ext]
theorem ext {u v : BV(Ω)} (h : u.toL1 = v.toL1) : u = v := by
  -- Equality of the stored `L¹(Ω)` data determines equality in the defining subtype.
  exact Subtype.ext h

/-- The underlying `L¹(Ω)` projection on `BV(Ω)` is injective. -/
theorem toL1_injective : Function.Injective (fun u : BV(Ω) ↦ u.toL1) := by
  -- The subtype is determined by its first projection.
  intro u v h
  exact ext h

/-- The zero `L¹(Ω)` function is BV-admissible. -/
theorem isBV_zero : IsBV (0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) := by
  -- Both the `L¹` norm and the raw total variation vanish at the zero function.
  simpa [IsBV, lpTotalVariationZero]

/-- The sum of two bounded-variation functions is BV-admissible. -/
theorem isBV_add (u v : BV(Ω)) : IsBV (u.toL1 + v.toL1) := by
  -- Bound the BV quantity of the sum by the sum of the two already-finite BV quantities.
  have hu : (((‖u.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation u.toL1) < ⊤ := by
    simpa [IsBV] using isBV_toL1 u
  have hv : (((‖v.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation v.toL1) < ⊤ := by
    simpa [IsBV] using isBV_toL1 v
  rw [IsBV]
  have hnorm :
      ((‖u.toL1 + v.toL1‖ : ℝ) : EReal) ≤
        ((‖u.toL1‖ : ℝ) : EReal) + ((‖v.toL1‖ : ℝ) : EReal) := by
    exact_mod_cast norm_add_le u.toL1 v.toL1
  have hsum :
      ((‖u.toL1 + v.toL1‖ : ℝ) : EReal) +
          VariationalRegularization.totalVariation (u.toL1 + v.toL1) ≤
        (((‖u.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation u.toL1) +
          (((‖v.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation v.toL1) := by
    calc
      ((‖u.toL1 + v.toL1‖ : ℝ) : EReal) +
          VariationalRegularization.totalVariation (u.toL1 + v.toL1)
          ≤ (((‖u.toL1‖ : ℝ) : EReal) + ((‖v.toL1‖ : ℝ) : EReal)) +
              (VariationalRegularization.totalVariation u.toL1 +
                VariationalRegularization.totalVariation v.toL1) := by
                  exact add_le_add hnorm (lpTotalVariationAddLe u.toL1 v.toL1)
      _ = (((‖u.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation u.toL1) +
            (((‖v.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation v.toL1) := by
            ac_rfl
  exact lt_of_le_of_lt hsum (by simpa [add_assoc] using EReal.add_lt_top hu.ne hv.ne)

/-- The negation of a bounded-variation function is BV-admissible. -/
theorem isBV_neg (u : BV(Ω)) : IsBV (-u.toL1) := by
  -- The BV quantity is unchanged by negation.
  simpa [IsBV, lpTotalVariationNeg] using isBV_toL1 u

/-- The difference of two bounded-variation functions is BV-admissible. -/
theorem isBV_sub (u v : BV(Ω)) : IsBV (u.toL1 - v.toL1) := by
  -- Repackage the negative summand as a `BV(Ω)` element and reuse additive closure.
  let w : BV(Ω) := ⟨-v.toL1, isBV_neg v⟩
  have hw : IsBV (u.toL1 + w.toL1) := isBV_add u w
  change IsBV (u.toL1 + -v.toL1) at hw
  simpa [sub_eq_add_neg] using hw

/-- Natural-number multiples of bounded-variation functions stay BV-admissible. -/
theorem isBV_nsmul (n : ℕ) (u : BV(Ω)) : IsBV (n • u.toL1) := by
  induction n with
  | zero =>
      simpa using isBV_zero (Ω := Ω)
  | succ n ih =>
      let v : BV(Ω) := ⟨n • u.toL1, ih⟩
      have hv : IsBV (u.toL1 + v.toL1) := isBV_add u v
      change IsBV (u.toL1 + n • u.toL1) at hv
      simpa [succ_nsmul, add_comm] using hv

/-- Integer multiples of bounded-variation functions stay BV-admissible. -/
theorem isBV_zsmul (z : ℤ) (u : BV(Ω)) : IsBV (z • u.toL1) := by
  cases z with
  | ofNat n =>
      simpa using isBV_nsmul n u
  | negSucc n =>
      let v : BV(Ω) := ⟨(n + 1) • u.toL1, isBV_nsmul (n + 1) u⟩
      have hv : IsBV (-v.toL1) := isBV_neg v
      change IsBV (-((n + 1) • u.toL1)) at hv
      simpa using hv

/-- Real scalar multiples of bounded-variation functions stay BV-admissible. -/
theorem isBV_smul (a : ℝ) (u : BV(Ω)) : IsBV (a • u.toL1) := by
  -- The raw total variation scales at most by `‖a‖`, so finiteness is preserved.
  rw [IsBV]
  have hu : (((‖u.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation u.toL1) < ⊤ := by
    simpa [IsBV] using isBV_toL1 u
  have htv_top : VariationalRegularization.totalVariation u.toL1 ≠ ⊤ := by
    intro htop
    exact (show (((‖u.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation u.toL1) = ⊤ by
      simpa [htop] using EReal.add_top_of_ne_bot (EReal.coe_ne_bot ‖u.toL1‖)).not_lt hu
  have hbound :
      ((‖a • u.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation (a • u.toL1) ≤
        (((‖a‖ * ‖u.toL1‖ : ℝ) : EReal) +
          (((‖a‖ : ℝ) : EReal) * VariationalRegularization.totalVariation u.toL1)) := by
    have hnorm :
        ((‖a • u.toL1‖ : ℝ) : EReal) =
          (((‖a‖ * ‖u.toL1‖ : ℝ)) : EReal) := by
      exact_mod_cast (by simpa [Real.norm_eq_abs] using (norm_smul a u.toL1))
    exact add_le_add (le_of_eq hnorm) (lpTotalVariationSmulLe a u.toL1)
  have hfinite :
      (((‖a‖ * ‖u.toL1‖ : ℝ) : EReal) +
          (((‖a‖ : ℝ) : EReal) * VariationalRegularization.totalVariation u.toL1)) < ⊤ := by
    have hmul_top :
        (((‖a‖ : ℝ) : EReal) * VariationalRegularization.totalVariation u.toL1) ≠ ⊤ := by
      exact (EReal.mul_ne_top ((‖a‖ : ℝ) : EReal) (VariationalRegularization.totalVariation u.toL1)).2
        ⟨Or.inl (EReal.coe_ne_bot ‖a‖), Or.inl (by exact_mod_cast norm_nonneg a),
          Or.inl (EReal.coe_ne_top ‖a‖), Or.inr htv_top⟩
    exact EReal.add_lt_top (EReal.coe_ne_top (‖a‖ * ‖u.toL1‖)) hmul_top
  exact lt_of_le_of_lt hbound hfinite

end BV

/-- The zero element of `BV(Ω)` induced from the canonical `L¹(Ω)` zero. -/
instance {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} : Zero (BV(Ω)) :=
  ⟨⟨0, BV.isBV_zero⟩⟩

/-- Addition on `BV(Ω)` induced from the canonical `L¹(Ω)` addition. -/
instance {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} : Add (BV(Ω)) :=
  ⟨fun u v ↦ ⟨u.toL1 + v.toL1, BV.isBV_add u v⟩⟩

/-- Negation on `BV(Ω)` induced from the canonical `L¹(Ω)` negation. -/
instance {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} : Neg (BV(Ω)) :=
  ⟨fun u ↦ ⟨-u.toL1, BV.isBV_neg u⟩⟩

/-- Subtraction on `BV(Ω)` induced from the canonical `L¹(Ω)` subtraction. -/
instance {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} : Sub (BV(Ω)) :=
  ⟨fun u v ↦ ⟨u.toL1 - v.toL1, BV.isBV_sub u v⟩⟩

/-- Natural scalar multiplication on `BV(Ω)` induced from `L¹(Ω)`. -/
instance {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} : SMul ℕ (BV(Ω)) :=
  ⟨fun n u ↦ ⟨n • u.toL1, BV.isBV_nsmul n u⟩⟩

/-- Integer scalar multiplication on `BV(Ω)` induced from `L¹(Ω)`. -/
instance {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} : SMul ℤ (BV(Ω)) :=
  ⟨fun z u ↦ ⟨z • u.toL1, BV.isBV_zsmul z u⟩⟩

/-- Real scalar multiplication on `BV(Ω)` induced from `L¹(Ω)`. -/
instance {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} : SMul ℝ (BV(Ω)) :=
  ⟨fun a u ↦ ⟨a • u.toL1, BV.isBV_smul a u⟩⟩

namespace BV

variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

/-- Helper for Theorem 8.15: the raw total variation of a bounded-variation element is finite
above. -/
theorem lpTotalVariation_ne_top (u : BV(Ω)) :
    VariationalRegularization.totalVariation u.toL1 ≠ ⊤ := by
  -- A finite BV quantity cannot contain a `⊤` total-variation summand.
  intro htop
  have hlt := norm_add_totalVariation_lt_top u
  exact (show (((‖u.toL1‖ : ℝ) : EReal) + VariationalRegularization.totalVariation u.toL1) = ⊤ by
    simpa [htop] using EReal.add_top_of_ne_bot (EReal.coe_ne_bot ‖u.toL1‖)).not_lt hlt

/-- Helper for Theorem 8.15: the raw total variation of a bounded-variation element is never
`⊥`. -/
theorem lpTotalVariation_ne_bot (u : BV(Ω)) :
    VariationalRegularization.totalVariation u.toL1 ≠ ⊥ := by
  -- Nonnegativity rules out the lower infinite value.
  exact ne_of_gt <| lt_of_lt_of_le (by simp) (lpTotalVariationNonneg u.toL1)

/-- Helper for Theorem 8.15: the BV norm splits into the `L¹(Ω)` norm plus the real-valued raw
total variation. -/
theorem norm_eq_normToL1_add_lpTotalVariation (u : BV(Ω)) :
    ‖u‖ =
      ‖u.toL1‖ + (VariationalRegularization.totalVariation u.toL1).toReal := by
  -- Convert the defining `EReal.toReal` formula to an ordinary real sum using finiteness.
  rw [norm_def, EReal.toReal_add (EReal.coe_ne_top ‖u.toL1‖) (EReal.coe_ne_bot ‖u.toL1‖)
    (lpTotalVariation_ne_top u) (lpTotalVariation_ne_bot u)]
  simp

/-- The `L¹(Ω)` projection of the zero element of `BV(Ω)` is zero. -/
@[simp]
theorem toL1_zero : (0 : BV(Ω)).toL1 = 0 := rfl

/-- The `L¹(Ω)` projection of a sum in `BV(Ω)` is the sum of the projections. -/
@[simp]
theorem toL1_add (u v : BV(Ω)) : (u + v).toL1 = u.toL1 + v.toL1 := rfl

/-- The `L¹(Ω)` projection of a negation in `BV(Ω)` is the negation of the projection. -/
@[simp]
theorem toL1_neg (u : BV(Ω)) : (-u).toL1 = -u.toL1 := rfl

/-- The `L¹(Ω)` projection of a difference in `BV(Ω)` is the difference of the projections. -/
@[simp]
theorem toL1_sub (u v : BV(Ω)) : (u - v).toL1 = u.toL1 - v.toL1 := rfl

/-- The `L¹(Ω)` projection of a natural multiple in `BV(Ω)` is the corresponding multiple in
`L¹(Ω)`. -/
@[simp]
theorem toL1_nsmul (n : ℕ) (u : BV(Ω)) : (n • u).toL1 = n • u.toL1 := rfl

/-- The `L¹(Ω)` projection of an integer multiple in `BV(Ω)` is the corresponding multiple in
`L¹(Ω)`. -/
@[simp]
theorem toL1_zsmul (z : ℤ) (u : BV(Ω)) : (z • u).toL1 = z • u.toL1 := rfl

/-- The `L¹(Ω)` projection of a real scalar multiple in `BV(Ω)` is the corresponding scalar
multiple in `L¹(Ω)`. -/
@[simp]
theorem toL1_smul (a : ℝ) (u : BV(Ω)) : (a • u).toL1 = a • u.toL1 := rfl

/-- Helper for Theorem 8.15: the real-valued raw total variation is subadditive on `BV(Ω)`. -/
theorem lpTotalVariationToReal_add_le (u v : BV(Ω)) :
    (VariationalRegularization.totalVariation (u + v).toL1).toReal ≤
      (VariationalRegularization.totalVariation u.toL1).toReal +
        (VariationalRegularization.totalVariation v.toL1).toReal := by
  -- Transport the raw `EReal` inequality to reals using finiteness on BV elements.
  have hraw := lpTotalVariationAddLe u.toL1 v.toL1
  have htop :
      VariationalRegularization.totalVariation u.toL1 +
          VariationalRegularization.totalVariation v.toL1 ≠ ⊤ := by
    exact EReal.add_ne_top (lpTotalVariation_ne_top u) (lpTotalVariation_ne_top v)
  have hreal :
      (VariationalRegularization.totalVariation (u + v).toL1).toReal ≤
        (VariationalRegularization.totalVariation u.toL1 +
          VariationalRegularization.totalVariation v.toL1).toReal :=
    EReal.toReal_le_toReal hraw (lpTotalVariation_ne_bot (u + v)) htop
  calc
    (VariationalRegularization.totalVariation (u + v).toL1).toReal
        ≤ (VariationalRegularization.totalVariation u.toL1 +
            VariationalRegularization.totalVariation v.toL1).toReal := hreal
    _ = (VariationalRegularization.totalVariation u.toL1).toReal +
          (VariationalRegularization.totalVariation v.toL1).toReal := by
            rw [EReal.toReal_add (lpTotalVariation_ne_top u) (lpTotalVariation_ne_bot u)
              (lpTotalVariation_ne_top v) (lpTotalVariation_ne_bot v)]

/-- Helper for Theorem 8.15: real scaling commutes with the real-valued raw total variation on
`BV(Ω)`. -/
theorem lpTotalVariationToReal_smul (a : ℝ) (u : BV(Ω)) :
    (VariationalRegularization.totalVariation (a • u.toL1)).toReal =
      ‖a‖ * (VariationalRegularization.totalVariation u.toL1).toReal := by
  by_cases ha_zero : a = 0
  · -- The zero scalar collapses both sides to zero.
    subst ha_zero
    simp [lpTotalVariationZero]
  have ha_norm_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have hmul_top :
      (((‖a‖ : ℝ) : EReal) * VariationalRegularization.totalVariation u.toL1) ≠ ⊤ := by
    exact (EReal.mul_ne_top ((‖a‖ : ℝ) : EReal) (VariationalRegularization.totalVariation u.toL1)).2
      ⟨Or.inl (EReal.coe_ne_bot ‖a‖), Or.inl (by exact_mod_cast ha_norm_nonneg),
        Or.inl (EReal.coe_ne_top ‖a‖), Or.inr (lpTotalVariation_ne_top u)⟩
  have hle_raw := lpTotalVariationSmulLe a u.toL1
  have hle :
      (VariationalRegularization.totalVariation (a • u.toL1)).toReal ≤
        ‖a‖ * (VariationalRegularization.totalVariation u.toL1).toReal := by
    have htoReal :
        (VariationalRegularization.totalVariation (a • u.toL1)).toReal ≤
          ((((‖a‖ : ℝ) : EReal) *
            VariationalRegularization.totalVariation u.toL1)).toReal :=
      EReal.toReal_le_toReal hle_raw (lpTotalVariation_ne_bot (a • u)) hmul_top
    simpa [EReal.toReal_mul] using htoReal
  have hrev_raw := lpTotalVariationSmulLe a⁻¹ (a • u).toL1
  have hrev :
      (VariationalRegularization.totalVariation u.toL1).toReal ≤
        ‖a⁻¹‖ * (VariationalRegularization.totalVariation (a • u.toL1)).toReal := by
    have hmul_top_rev :
        (((‖a⁻¹‖ : ℝ) : EReal) *
            VariationalRegularization.totalVariation (a • u.toL1)) ≠ ⊤ := by
      exact (EReal.mul_ne_top ((‖a⁻¹‖ : ℝ) : EReal)
        (VariationalRegularization.totalVariation (a • u.toL1))).2
        ⟨Or.inl (EReal.coe_ne_bot ‖a⁻¹‖), Or.inl (by exact_mod_cast norm_nonneg a⁻¹),
          Or.inl (EReal.coe_ne_top ‖a⁻¹‖), Or.inr (lpTotalVariation_ne_top (a • u))⟩
    have hbot :
        VariationalRegularization.totalVariation (a⁻¹ • (a • u).toL1) ≠ ⊥ := by
      simpa [toL1_smul, smul_smul, inv_mul_cancel₀ ha_zero] using lpTotalVariation_ne_bot u
    have htoReal :
        (VariationalRegularization.totalVariation (a⁻¹ • (a • u).toL1)).toReal ≤
          ((((‖a⁻¹‖ : ℝ) : EReal) *
            VariationalRegularization.totalVariation (a • u.toL1))).toReal :=
      EReal.toReal_le_toReal hrev_raw hbot hmul_top_rev
    simpa [toL1_smul, smul_smul, inv_mul_cancel₀ ha_zero, EReal.toReal_mul] using htoReal
  have hnorm_mul_inv : ‖a‖ * ‖a⁻¹‖ = 1 := by
    calc
      ‖a‖ * ‖a⁻¹‖ = ‖a * a⁻¹‖ := by rw [norm_mul]
      _ = 1 := by simp [ha_zero]
  have hge :
      ‖a‖ * (VariationalRegularization.totalVariation u.toL1).toReal ≤
        (VariationalRegularization.totalVariation (a • u.toL1)).toReal := by
    calc
      ‖a‖ * (VariationalRegularization.totalVariation u.toL1).toReal
          ≤ ‖a‖ * (‖a⁻¹‖ *
              (VariationalRegularization.totalVariation (a • u.toL1)).toReal) := by
                exact mul_le_mul_of_nonneg_left hrev ha_norm_nonneg
      _ = (VariationalRegularization.totalVariation (a • u.toL1)).toReal := by
            rw [← mul_assoc, hnorm_mul_inv, one_mul]
  exact le_antisymm hle hge

/-- Helper for Theorem 8.15: the `L¹(Ω)` norm is controlled by the BV norm. -/
theorem normToL1_le (u : BV(Ω)) : ‖u.toL1‖ ≤ ‖u‖ := by
  -- The BV norm is the sum of the `L¹` norm and a nonnegative variation term.
  rw [norm_eq_normToL1_add_lpTotalVariation]
  have htv_nonneg : 0 ≤ (VariationalRegularization.totalVariation u.toL1).toReal := by
    exact EReal.toReal_nonneg (lpTotalVariationNonneg u.toL1)
  linarith

/-- Helper for Theorem 8.15: the real-valued raw total variation is controlled by the BV norm. -/
theorem lpTotalVariationToReal_le_norm (u : BV(Ω)) :
    (VariationalRegularization.totalVariation u.toL1).toReal ≤ ‖u‖ := by
  -- The same norm decomposition controls the variation summand.
  rw [norm_eq_normToL1_add_lpTotalVariation]
  have hnorm_nonneg : 0 ≤ ‖u.toL1‖ := norm_nonneg _
  linarith [hnorm_nonneg]

/-- Helper for Theorem 8.15: the raw `EReal` total variation is controlled by the BV norm. -/
theorem lpTotalVariation_le_coe_norm (u : BV(Ω)) :
    VariationalRegularization.totalVariation u.toL1 ≤ (‖u‖ : EReal) := by
  -- First compare `TV` with its finite real shadow, then compare that real shadow with the BV norm.
  have hreal : (((VariationalRegularization.totalVariation u.toL1).toReal : ℝ) : EReal) ≤ (‖u‖ : EReal) := by
    exact_mod_cast lpTotalVariationToReal_le_norm u
  exact (EReal.le_coe_toReal (lpTotalVariation_ne_top u)).trans hreal

/-- The Chapter 8 BV norm vanishes at zero. -/
theorem norm_zero : ‖(0 : BV(Ω))‖ = 0 := by
  -- Both summands in the norm decomposition vanish at zero.
  rw [norm_eq_normToL1_add_lpTotalVariation]
  simp [lpTotalVariationZero]

/-- The Chapter 8 BV norm is invariant under negation. -/
theorem norm_neg (u : BV(Ω)) : ‖-u‖ = ‖u‖ := by
  -- Negation preserves both the `L¹` norm and the raw total variation.
  rw [norm_eq_normToL1_add_lpTotalVariation, norm_eq_normToL1_add_lpTotalVariation]
  simp [lpTotalVariationNeg]

/-- The Chapter 8 BV norm is subadditive. -/
theorem norm_add_le (u v : BV(Ω)) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  -- Control the two BV norm summands separately, then regroup the result.
  calc
    ‖u + v‖
        = ‖(u + v).toL1‖ +
            (VariationalRegularization.totalVariation (u + v).toL1).toReal :=
          norm_eq_normToL1_add_lpTotalVariation (u + v)
    _ ≤ (‖u.toL1‖ + ‖v.toL1‖) +
          ((VariationalRegularization.totalVariation u.toL1).toReal +
            (VariationalRegularization.totalVariation v.toL1).toReal) := by
            gcongr
            · exact _root_.norm_add_le u.toL1 v.toL1
            · exact lpTotalVariationToReal_add_le u v
    _ = (‖u.toL1‖ + (VariationalRegularization.totalVariation u.toL1).toReal) +
          (‖v.toL1‖ + (VariationalRegularization.totalVariation v.toL1).toReal) := by ring
    _ = ‖u‖ + ‖v‖ := by
          rw [norm_eq_normToL1_add_lpTotalVariation, norm_eq_normToL1_add_lpTotalVariation]

/-- The Chapter 8 BV norm separates points. -/
theorem norm_eq_zero_iff (u : BV(Ω)) : ‖u‖ = 0 ↔ u = 0 := by
  constructor
  · intro hu
    -- Nonnegativity of both summands forces the underlying `L¹(Ω)` norm to vanish.
    rw [norm_eq_normToL1_add_lpTotalVariation] at hu
    have hnorm_nonneg : 0 ≤ ‖u.toL1‖ := norm_nonneg _
    have htv_nonneg : 0 ≤ (VariationalRegularization.totalVariation u.toL1).toReal := by
      exact EReal.toReal_nonneg (lpTotalVariationNonneg u.toL1)
    have hzero : ‖u.toL1‖ = 0 := by
      linarith
    apply ext
    exact norm_eq_zero.mp hzero
  · rintro rfl
    exact norm_zero

/-- Real scalar multiplication scales the Chapter 8 BV norm by `‖a‖`. -/
theorem norm_smul (a : ℝ) (u : BV(Ω)) : ‖a • u‖ = ‖a‖ * ‖u‖ := by
  -- Scale the two BV norm summands separately, then factor out `‖a‖`.
  calc
    ‖a • u‖
        = ‖(a • u).toL1‖ +
            (VariationalRegularization.totalVariation (a • u).toL1).toReal :=
          norm_eq_normToL1_add_lpTotalVariation (a • u)
    _ = ‖a‖ * ‖u.toL1‖ +
          ‖a‖ * (VariationalRegularization.totalVariation u.toL1).toReal := by
            rw [toL1_smul, _root_.norm_smul, lpTotalVariationToReal_smul, Real.norm_eq_abs]
    _ = ‖a‖ * (‖u.toL1‖ +
          (VariationalRegularization.totalVariation u.toL1).toReal) := by ring
    _ = ‖a‖ * ‖u‖ := by rw [norm_eq_normToL1_add_lpTotalVariation]

end BV

/-- The bounded-variation carrier `BV(Ω)` inherits its additive commutative group structure from
the underlying `L¹(Ω)` realization. -/
instance instAddCommGroupBV
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    AddCommGroup (BV(Ω)) :=
  Function.Injective.addCommGroup (fun u : BV(Ω) ↦ u.toL1) BV.toL1_injective
    BV.toL1_zero BV.toL1_add BV.toL1_neg BV.toL1_sub
    (fun u n ↦ BV.toL1_nsmul n u) (fun u z ↦ BV.toL1_zsmul z u)

/-- The bounded-variation carrier `BV(Ω)` inherits its real vector-space structure from the
underlying `L¹(Ω)` realization. -/
instance instModuleBV
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    Module ℝ (BV(Ω)) :=
  Function.Injective.module ℝ
    ⟨⟨fun u : BV(Ω) ↦ u.toL1, BV.toL1_zero⟩, BV.toL1_add⟩
    BV.toL1_injective
    BV.toL1_smul

/-- The bounded-variation carrier `BV(Ω)` carries the Chapter 8 normed additive-group structure
defined by `BV.norm_def`. -/
instance instNormedAddCommGroupBV
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    NormedAddCommGroup (BV(Ω)) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun u ↦ ‖u‖
      map_zero' := BV.norm_zero
      add_le' := BV.norm_add_le
      neg' := BV.norm_neg
      eq_zero_of_map_eq_zero' := fun u hu ↦ (BV.norm_eq_zero_iff u).1 hu }

/-- The bounded-variation carrier `BV(Ω)` carries the Chapter 8 normed real vector-space
structure compatible with the BV norm. -/
instance instNormedSpaceBV
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    NormedSpace ℝ (BV(Ω)) :=
  NormedSpace.ofCore
    { norm_nonneg := fun u ↦ norm_nonneg u
      norm_smul := BV.norm_smul
      norm_triangle := BV.norm_add_le
      norm_eq_zero_iff := BV.norm_eq_zero_iff }

end VariationalRegularization
