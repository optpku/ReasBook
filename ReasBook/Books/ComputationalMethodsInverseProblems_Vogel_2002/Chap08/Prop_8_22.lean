/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4_1.Approximation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_16
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_16.ERealUniformity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_22.BVBounded
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

public section

/-!
Proposition 8.22.

This file records the six source-facing clauses of Proposition 8.22 for the
Chapter 8 approximation functionals `J_β` and `J_ε`: convexity, weak-`L¹`
lower semicontinuity, and the corresponding uniform-convergence clauses toward
`TV` on BV-bounded subsets of the canonical `L¹(Ω)` carrier.
-/

noncomputable section

namespace VariationalRegularization

open scoped VariationalRegularization.Approximation

variable {d : ℕ}

/-- Helper for Proposition 8.22: rewrite `approximateTotalVariation` as an `iSup` over admissible
test fields. -/
lemma approximateTotalVariation_eq_iSup
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (φStar : EuclideanSpace ℝ (Fin d) → ℝ)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    approximateTotalVariation φStar f =
      ⨆ v : AdmissibleTestField Ω,
        (((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
              ∂domainMeasure Ω) : ℝ) : EReal) := by
  -- This normalization puts the owner into the `iSup` form used by both the convexity
  -- and weak-lower-semicontinuity arguments.
  rw [approximateTotalVariation_def, sSup_range]

/-- Helper for Proposition 8.22: the admissible divergence is continuous. -/
lemma admissibleDivergence_continuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    Continuous (admissibleDivergence v) := by
  -- Reuse the canonical continuity result proved earlier in Chapter 8.
  simpa using VariationalRegularization.admissibleDivergenceContinuous v

/-- Helper for Proposition 8.22: the admissible divergence has compact support. -/
lemma admissibleDivergence_hasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    HasCompactSupport (admissibleDivergence v) := by
  -- Reuse the canonical compact-support result for admissible divergences.
  simpa using VariationalRegularization.admissibleDivergenceHasCompactSupport v

/-- Helper for Proposition 8.22: the admissible divergence belongs to `L∞(Ω)`. -/
lemma admissibleDivergence_memLp_top
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    MeasureTheory.MemLp (admissibleDivergence v) ⊤ (domainMeasure Ω) := by
  -- Reuse the earlier `L∞` packaging of the admissible divergence.
  simpa using VariationalRegularization.admissibleDivergenceMemLpTop v

/-- Helper for Proposition 8.22: the divergence pairing against a fixed admissible test field is a
continuous linear functional on `L¹(Ω)`. -/
def admissibleDivergencePairingCLM
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Lp ℝ 1 (domainMeasure Ω) →L[ℝ] ℝ :=
  let divLp : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω) :=
    MeasureTheory.MemLp.toLp (admissibleDivergence v) (admissibleDivergence_memLp_top v)
  let lpPairing :
      MeasureTheory.Lp ℝ 1 (domainMeasure Ω) →L[ℝ]
        MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω) →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (domainMeasure Ω) (1 : ENNReal) (⊤ : ENNReal)
  ((ContinuousLinearMap.apply ℝ ℝ) divLp).comp
    lpPairing

/-- Helper for Proposition 8.22: evaluating the pairing continuous linear map recovers the original
divergence pairing. -/
lemma admissibleDivergencePairing_eq_pairingCLM_apply
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    admissibleDivergencePairingCLM v f = admissibleDivergencePairing f v := by
  -- Unfold the local packaging once and evaluate the standard `Lp` pairing integral.
  rw [admissibleDivergencePairing_def, admissibleDivergencePairingCLM]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp (admissibleDivergence_memLp_top v)] with x hx
  simp [hx]

/-- Helper for Proposition 8.22: evaluating a continuous linear functional is continuous on the
weak topology. -/
lemma continuous_evalOnWeakSpace
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) :
    Continuous fun x : WeakSpace ℝ E ↦ L ((toWeakSpace ℝ E).symm x) := by
  -- Route correction: weak-space continuity is exactly evaluation continuity for the defining
  -- weak topology, so we move to the underlying `WeakBilin` spelling once and use its API.
  change Continuous (fun x : WeakBilin (topDualPairing ℝ E).flip ↦ L x)
  exact WeakBilin.eval_continuous ((topDualPairing ℝ E).flip) L

/-- Helper for Proposition 8.22: if `φStar` is continuous and vanishes at `0`, then its fixed-test
field penalty is integrable. -/
lemma approximatePenalty_integrable
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φStar : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Continuous φStar)
    (hφ0 : φStar 0 = 0)
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable (fun x ↦ φStar (v.toTestFunction x)) (domainMeasure Ω) := by
  -- The composite stays compactly supported because `φStar` vanishes at the origin.
  have hμ :
      domainMeasure Ω =
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict
          (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    simpa [domainMeasure_def] using
      congrArg
        (fun μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) ↦
          μ.restrict (Ω : Set (EuclideanSpace ℝ (Fin d))))
        (EuclideanSpace.euclideanHausdorffMeasure_eq_volume d)
  rw [hμ]
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin d) ↦ φStar (v.toTestFunction x) :=
    hφ.comp v.toTestFunction.continuous
  have hlocal :
      MeasureTheory.LocallyIntegrableOn
        (fun x : EuclideanSpace ℝ (Fin d) ↦ φStar (v.toTestFunction x))
        (Ω : Set (EuclideanSpace ℝ (Fin d)))
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict
          (Ω : Set (EuclideanSpace ℝ (Fin d)))) := by
    exact hcont.continuousOn.locallyIntegrableOn Ω.2.measurableSet
  have hOn :
      MeasureTheory.IntegrableOn
        (fun x : EuclideanSpace ℝ (Fin d) ↦ φStar (v.toTestFunction x))
        (tsupport v.toTestFunction)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict
          (Ω : Set (EuclideanSpace ℝ (Fin d)))) :=
    hlocal.integrableOn_compact_subset v.toTestFunction.tsupport_subset
      v.toTestFunction.hasCompactSupport.isCompact
  have hsupp :
      Function.support (fun x : EuclideanSpace ℝ (Fin d) ↦ φStar (v.toTestFunction x)) ⊆
        tsupport v.toTestFunction := by
    exact (Function.support_comp_subset hφ0 v.toTestFunction).trans subset_closure
  exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp hOn

/-- Helper for Proposition 8.22: for penalties vanishing at `0`, the fixed-field owner splits into
the divergence pairing term minus a constant penalty. -/
lemma approximateTotalVariation_fixedField_eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φStar : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Continuous φStar)
    (hφ0 : φStar 0 = 0)
    (v : AdmissibleTestField Ω)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    ((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
          ∂domainMeasure Ω) : ℝ) =
      -admissibleDivergencePairingCLM v f -
        ∫ x, φStar (v.toTestFunction x) ∂domainMeasure Ω := by
  -- Split the witness into the negated pairing term and the fixed penalty constant.
  have hpair :
      MeasureTheory.Integrable (fun x ↦ f x * admissibleDivergence v x) (domainMeasure Ω) :=
    ApproximationUniformConvergence.pairingIntegrable f v
  have hnegPair :
      MeasureTheory.Integrable (fun x ↦ (-(f x)) * admissibleDivergence v x) (domainMeasure Ω) := by
    refine hpair.neg.congr ?_
    filter_upwards with x
    simp [neg_mul]
  have hpen : MeasureTheory.Integrable (fun x ↦ φStar (v.toTestFunction x)) (domainMeasure Ω) :=
    approximatePenalty_integrable hφ hφ0 v
  have hpairEq :
      (∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω) =
        -admissibleDivergencePairingCLM v f := by
    calc
      (∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω)
          = ∫ x, -(f x * admissibleDivergence v x) ∂domainMeasure Ω := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with x
              simp [neg_mul]
      _ = -∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω := by
            simpa using MeasureTheory.integral_neg
              (fun x : EuclideanSpace ℝ (Fin d) ↦ f x * admissibleDivergence v x)
      _ = -admissibleDivergencePairingCLM v f := by
            have hpairIntegral :
                (∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω) =
                  admissibleDivergencePairingCLM v f := by
              rw [← admissibleDivergencePairing_def,
                ← admissibleDivergencePairing_eq_pairingCLM_apply]
            rw [hpairIntegral]
  rw [MeasureTheory.integral_sub hnegPair hpen, hpairEq]

/-- Helper for Proposition 8.22: for penalties vanishing at `0`, the fixed-field owner respects
convex combinations. -/
lemma approximateTotalVariation_integrand_convexCombination
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φStar : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Continuous φStar)
    (hφ0 : φStar 0 = 0)
    (v : AdmissibleTestField Ω)
    {f g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    {a b : ℝ}
    (hab : a + b = 1) :
    (((∫ x, (-((a • f + b • g) x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
          ∂domainMeasure Ω) : ℝ) : EReal) =
      (a : EReal) *
          (((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
                ∂domainMeasure Ω) : ℝ) : EReal) +
        (b : EReal) *
          (((∫ x, (-(g x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
                ∂domainMeasure Ω) : ℝ) : EReal) := by
  -- Rewrite each witness as an affine functional of `f` plus the fixed penalty constant.
  let C : ℝ := ∫ x, φStar (v.toTestFunction x) ∂domainMeasure Ω
  have hlin :
      admissibleDivergencePairingCLM v (a • f + b • g) =
        a * admissibleDivergencePairingCLM v f + b * admissibleDivergencePairingCLM v g := by
    simp
  have hreal :
      -admissibleDivergencePairingCLM v (a • f + b • g) - C =
        a * (-admissibleDivergencePairingCLM v f - C) +
          b * (-admissibleDivergencePairingCLM v g - C) := by
    rw [hlin]
    calc
      -(a * admissibleDivergencePairingCLM v f + b * admissibleDivergencePairingCLM v g) - C
          = -(a * admissibleDivergencePairingCLM v f + b * admissibleDivergencePairingCLM v g) -
              (a + b) * C := by rw [hab, one_mul]
      _ = a * (-admissibleDivergencePairingCLM v f - C) +
            b * (-admissibleDivergencePairingCLM v g - C) := by ring
  have hcombo :
      (((∫ x, (-((a • f + b • g) x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
            ∂domainMeasure Ω) : ℝ) : EReal) =
        (((a * (-admissibleDivergencePairingCLM v f - C) +
            b * (-admissibleDivergencePairingCLM v g - C) : ℝ) : EReal)) := by
    calc
      (((∫ x, (-((a • f + b • g) x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
            ∂domainMeasure Ω) : ℝ) : EReal)
          = (((-admissibleDivergencePairingCLM v (a • f + b • g) - C : ℝ) : EReal)) := by
              simpa [C] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
                (approximateTotalVariation_fixedField_eq hφ hφ0 v (a • f + b • g))
      _ = (((a * (-admissibleDivergencePairingCLM v f - C) +
              b * (-admissibleDivergencePairingCLM v g - C) : ℝ) : EReal)) := by
            exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal
  have hf :
      (((-admissibleDivergencePairingCLM v f - C : ℝ) : EReal)) =
        (((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
              ∂domainMeasure Ω) : ℝ) : EReal) := by
    symm
    simpa [C] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
      (approximateTotalVariation_fixedField_eq hφ hφ0 v f)
  have hg :
      (((-admissibleDivergencePairingCLM v g - C : ℝ) : EReal)) =
        (((∫ x, (-(g x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
              ∂domainMeasure Ω) : ℝ) : EReal) := by
    symm
    simpa [C] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
      (approximateTotalVariation_fixedField_eq hφ hφ0 v g)
  calc
    (((∫ x, (-((a • f + b • g) x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
          ∂domainMeasure Ω) : ℝ) : EReal)
        = (((a * (-admissibleDivergencePairingCLM v f - C) +
              b * (-admissibleDivergencePairingCLM v g - C) : ℝ) : EReal)) := hcombo
    _ = (a : EReal) * (((-admissibleDivergencePairingCLM v f - C : ℝ) : EReal)) +
          (b : EReal) * (((-admissibleDivergencePairingCLM v g - C : ℝ) : EReal)) := by
            simp
    _ = (a : EReal) *
          (((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
                ∂domainMeasure Ω) : ℝ) : EReal) +
        (b : EReal) *
          (((∫ x, (-(g x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
                ∂domainMeasure Ω) : ℝ) : EReal) := by
            rw [hf, hg]

/-- Helper for Proposition 8.22: penalties vanishing at `0` yield a convex approximation owner. -/
lemma approximateTotalVariation_convex_of_zero
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φStar : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Continuous φStar)
    (hφ0 : φStar 0 = 0)
    {f g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : a + b = 1) :
    approximateTotalVariation φStar (a • f + b • g) ≤
      (a : EReal) * approximateTotalVariation φStar f +
        (b : EReal) * approximateTotalVariation φStar g := by
  -- Compare the supremum witness-by-witness and use monotonicity of multiplication by
  -- nonnegative weights.
  rw [approximateTotalVariation_eq_iSup,
    approximateTotalVariation_eq_iSup,
    approximateTotalVariation_eq_iSup]
  refine iSup_le ?_
  intro v
  calc
    (((∫ x, (-((a • f + b • g) x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
          ∂domainMeasure Ω) : ℝ) : EReal)
        = (a : EReal) *
            (((∫ x, (-(f x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
                  ∂domainMeasure Ω) : ℝ) : EReal) +
          (b : EReal) *
            (((∫ x, (-(g x)) * admissibleDivergence v x - φStar (v.toTestFunction x)
                  ∂domainMeasure Ω) : ℝ) : EReal) :=
          approximateTotalVariation_integrand_convexCombination hφ hφ0 v hab
    _ ≤ (a : EReal) * (⨆ w : AdmissibleTestField Ω,
            (((∫ x, (-(f x)) * admissibleDivergence w x - φStar (w.toTestFunction x)
                  ∂domainMeasure Ω) : ℝ) : EReal)) +
          (b : EReal) * (⨆ w : AdmissibleTestField Ω,
            (((∫ x, (-(g x)) * admissibleDivergence w x - φStar (w.toTestFunction x)
                  ∂domainMeasure Ω) : ℝ) : EReal)) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_left (le_iSup (fun w : AdmissibleTestField Ω ↦
                (((∫ x, (-(f x)) * admissibleDivergence w x - φStar (w.toTestFunction x)
                      ∂domainMeasure Ω) : ℝ) : EReal)) v) (by exact_mod_cast ha)
            · exact mul_le_mul_of_nonneg_left (le_iSup (fun w : AdmissibleTestField Ω ↦
                (((∫ x, (-(g x)) * admissibleDivergence w x - φStar (w.toTestFunction x)
                      ∂domainMeasure Ω) : ℝ) : EReal)) v) (by exact_mod_cast hb)

/-- Helper for Proposition 8.22: for penalties vanishing at `0`, each fixed-field owner is
continuous on the weak `L¹` topology. -/
lemma approximateTotalVariation_fixedField_continuous_weakL1_of_zero
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φStar : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Continuous φStar)
    (hφ0 : φStar 0 = 0)
    (v : AdmissibleTestField Ω) :
    Continuous
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        (((∫ y,
              (-((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x y)) *
                admissibleDivergence v y -
                φStar (v.toTestFunction y)
              ∂domainMeasure Ω) : ℝ) : EReal)) := by
  -- Rewrite the fixed-field witness as a weakly continuous linear evaluation plus a constant.
  let C : ℝ := ∫ y, φStar (v.toTestFunction y) ∂domainMeasure Ω
  have hcontReal :
      Continuous
        (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
          -admissibleDivergencePairingCLM v
              ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x) - C) := by
    exact (continuous_evalOnWeakSpace (admissibleDivergencePairingCLM v)).neg.sub continuous_const
  have hcontE :
      Continuous
        (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
          (((-admissibleDivergencePairingCLM v
                ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x) - C : ℝ) :
              EReal))) :=
    continuous_coe_real_ereal.comp hcontReal
  refine hcontE.congr ?_
  intro x
  simpa [C] using
    (congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
      (approximateTotalVariation_fixedField_eq hφ hφ0 v
        ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x))).symm

/-- Helper for Proposition 8.22: penalties vanishing at `0` give weak-`L¹` lower
semicontinuity of the approximation owner. -/
lemma approximateTotalVariation_lowerSemicontinuous_weakL1_of_zero
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φStar : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Continuous φStar)
    (hφ0 : φStar 0 = 0) :
    LowerSemicontinuous
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        approximateTotalVariation φStar
          ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) := by
  -- Expand the approximation functional as the supremum of the fixed-field witnesses.
  rw [show
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        approximateTotalVariation φStar
          ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) =
      (fun x ↦
        ⨆ v : AdmissibleTestField Ω,
          (((∫ y,
                (-((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x y)) *
                  admissibleDivergence v y -
                  φStar (v.toTestFunction y)
                ∂domainMeasure Ω) : ℝ) : EReal)) by
        funext x
        rw [approximateTotalVariation_eq_iSup]]
  exact lowerSemicontinuous_iSup fun v =>
    (approximateTotalVariation_fixedField_continuous_weakL1_of_zero hφ hφ0 v).lowerSemicontinuous

/-- Helper for Proposition 8.22: on a finite-measure domain, each fixed smooth-penalty witness is
the negated divergence pairing plus a constant smooth penalty term. -/
lemma smoothNormApproxTotalVariation_fixedField_eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    (v : AdmissibleTestField Ω)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    ((∫ x, (-(f x)) * admissibleDivergence v x +
          β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
        ∂domainMeasure Ω) : ℝ) =
      -admissibleDivergencePairingCLM v f +
        ∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ∂domainMeasure Ω := by
  -- The smooth witness differs from the fixed divergence pairing only by its constant penalty
  -- contribution.
  have hpair :
      MeasureTheory.Integrable (fun x ↦ f x * admissibleDivergence v x) (domainMeasure Ω) :=
    ApproximationUniformConvergence.pairingIntegrable f v
  have hnegPair :
      MeasureTheory.Integrable (fun x ↦ (-(f x)) * admissibleDivergence v x) (domainMeasure Ω) := by
    refine hpair.neg.congr ?_
    filter_upwards with x
    simp [neg_mul]
  have hpen :
      MeasureTheory.Integrable
        (fun x ↦ β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2))
        (domainMeasure Ω) :=
    ApproximationUniformConvergence.smoothPenaltyIntegrable β hβ v
  have hpairEq :
      (∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω) =
        -admissibleDivergencePairingCLM v f := by
    calc
      (∫ x, (-(f x)) * admissibleDivergence v x ∂domainMeasure Ω)
          = ∫ x, -(f x * admissibleDivergence v x) ∂domainMeasure Ω := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with x
              simp [neg_mul]
      _ = -∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω := by
            simpa using MeasureTheory.integral_neg
              (fun x : EuclideanSpace ℝ (Fin d) ↦ f x * admissibleDivergence v x)
      _ = -admissibleDivergencePairingCLM v f := by
            have hpairIntegral :
                (∫ x, f x * admissibleDivergence v x ∂domainMeasure Ω) =
                  admissibleDivergencePairingCLM v f := by
              rw [← admissibleDivergencePairing_def,
                ← admissibleDivergencePairing_eq_pairingCLM_apply]
            rw [hpairIntegral]
  rw [MeasureTheory.integral_add hnegPair hpen, hpairEq]

/-- Proposition 8.22.
For each positive `β`, the Chapter 8 smooth approximation `J_β` satisfies the usual
convexity inequality on the canonical `L¹(Ω)` carrier. -/
theorem smoothNormApproxTotalVariation_convex
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β)
    {f g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : a + b = 1) :
    J_β β (a • f + b • g) ≤ (a : EReal) * J_β β f + (b : EReal) * J_β β g := by
  -- Route correction: the smooth penalty does not vanish at `0`, so we compare the fixed-field
  -- witnesses directly using the finite-measure penalty integral.
  rw [smoothNormApproxTotalVariation_def, smoothNormApproxTotalVariation_def,
    smoothNormApproxTotalVariation_def]
  refine sSup_le ?_
  rintro _ ⟨v, rfl⟩
  let C : ℝ := ∫ x, β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2) ∂domainMeasure Ω
  have hlin :
      admissibleDivergencePairingCLM v (a • f + b • g) =
        a * admissibleDivergencePairingCLM v f + b * admissibleDivergencePairingCLM v g := by
    simp
  have hreal :
      -admissibleDivergencePairingCLM v (a • f + b • g) + C =
        a * (-admissibleDivergencePairingCLM v f + C) +
          b * (-admissibleDivergencePairingCLM v g + C) := by
    rw [hlin]
    calc
      -(a * admissibleDivergencePairingCLM v f + b * admissibleDivergencePairingCLM v g) + C
          = -(a * admissibleDivergencePairingCLM v f + b * admissibleDivergencePairingCLM v g) +
              (a + b) * C := by rw [hab, one_mul]
      _ = a * (-admissibleDivergencePairingCLM v f + C) +
            b * (-admissibleDivergencePairingCLM v g + C) := by ring
  have hf :
      (((-admissibleDivergencePairingCLM v f + C : ℝ) : EReal)) =
        (((∫ x, (-(f x)) * admissibleDivergence v x +
              β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
            ∂domainMeasure Ω) : ℝ) : EReal) := by
    symm
    simpa [C] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
      (smoothNormApproxTotalVariation_fixedField_eq β hβ v f)
  have hg :
      (((-admissibleDivergencePairingCLM v g + C : ℝ) : EReal)) =
        (((∫ x, (-(g x)) * admissibleDivergence v x +
              β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
            ∂domainMeasure Ω) : ℝ) : EReal) := by
    symm
    simpa [C] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
      (smoothNormApproxTotalVariation_fixedField_eq β hβ v g)
  calc
    (((∫ x, (-((a • f + b • g) x)) * admissibleDivergence v x +
            β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
          ∂domainMeasure Ω) : ℝ) : EReal)
        = (((-admissibleDivergencePairingCLM v (a • f + b • g) + C : ℝ) : EReal)) := by
            simpa [C] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
              (smoothNormApproxTotalVariation_fixedField_eq β hβ v (a • f + b • g))
    _ = (((a * (-admissibleDivergencePairingCLM v f + C) +
            b * (-admissibleDivergencePairingCLM v g + C) : ℝ) : EReal)) := by
          exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal
    _ = (a : EReal) * (((-admissibleDivergencePairingCLM v f + C : ℝ) : EReal)) +
          (b : EReal) * (((-admissibleDivergencePairingCLM v g + C : ℝ) : EReal)) := by
            simp
    _ = (a : EReal) *
          (((∫ x, (-(f x)) * admissibleDivergence v x +
                β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
              ∂domainMeasure Ω) : ℝ) : EReal) +
        (b : EReal) *
          (((∫ x, (-(g x)) * admissibleDivergence v x +
                β * Real.sqrt (1 - ‖v.toTestFunction x‖ ^ 2)
              ∂domainMeasure Ω) : ℝ) : EReal) := by
            rw [hf, hg]
    _ ≤ (a : EReal) *
          sSup (Set.range fun w : AdmissibleTestField Ω ↦
            (((∫ x, (-(f x)) * admissibleDivergence w x +
                    β * Real.sqrt (1 - ‖w.toTestFunction x‖ ^ 2)
                  ∂domainMeasure Ω) : ℝ) : EReal)) +
        (b : EReal) *
          sSup (Set.range fun w : AdmissibleTestField Ω ↦
            (((∫ x, (-(g x)) * admissibleDivergence w x +
                    β * Real.sqrt (1 - ‖w.toTestFunction x‖ ^ 2)
                  ∂domainMeasure Ω) : ℝ) : EReal)) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_left
                (le_sSup (s := Set.range fun w : AdmissibleTestField Ω ↦
                  (((∫ x, (-(f x)) * admissibleDivergence w x +
                          β * Real.sqrt (1 - ‖w.toTestFunction x‖ ^ 2)
                        ∂domainMeasure Ω) : ℝ) : EReal)) ⟨v, rfl⟩)
                (by exact_mod_cast ha)
            · exact mul_le_mul_of_nonneg_left
                (le_sSup (s := Set.range fun w : AdmissibleTestField Ω ↦
                  (((∫ x, (-(g x)) * admissibleDivergence w x +
                          β * Real.sqrt (1 - ‖w.toTestFunction x‖ ^ 2)
                        ∂domainMeasure Ω) : ℝ) : EReal)) ⟨v, rfl⟩)
                (by exact_mod_cast hb)

/-- Clause of Proposition 8.22. For each positive `ε`, the Chapter 8 Huber approximation `J_ε`
satisfies the usual convexity inequality on the canonical `L¹(Ω)` carrier. -/
theorem huberApproxTotalVariation_convex
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (_hε : 0 < ε)
    {f g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : a + b = 1) :
    J_ε ε (a • f + b • g) ≤ (a : EReal) * J_ε ε f + (b : EReal) * J_ε ε g := by
  -- The Huber penalty vanishes at `0`, so the generic zero-at-zero convexity lemma applies.
  have hφ : Continuous (fun y : EuclideanSpace ℝ (Fin d) ↦ (ε / 2) * ‖y‖ ^ 2) := by
    continuity
  have hφ0 : (fun y : EuclideanSpace ℝ (Fin d) ↦ (ε / 2) * ‖y‖ ^ 2) 0 = 0 := by
    simp
  simpa [huberApproxTotalVariation_eq_approximateTotalVariation] using
    approximateTotalVariation_convex_of_zero (Ω := Ω) hφ hφ0
      (f := f) (g := g) ha hb hab

/-- Clause of Proposition 8.22. For each positive `β`, the Chapter 8 smooth approximation `J_β`
is lower semicontinuous for the weak topology on `L¹(Ω)`. -/
theorem smoothNormApproxTotalVariation_lowerSemicontinuous_weakL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (β : ℝ)
    (hβ : 0 < β) :
    LowerSemicontinuous
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        J_β β ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) := by
  -- Route correction: the smooth penalty is not zero at the origin, so we prove continuity of
  -- each fixed witness directly from the finite-measure penalty integral.
  rw [show
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        J_β β ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) =
      (fun x ↦
        ⨆ v : AdmissibleTestField Ω,
          (((∫ y,
                (-((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x y)) *
                  admissibleDivergence v y +
                  β * Real.sqrt (1 - ‖v.toTestFunction y‖ ^ 2)
                ∂domainMeasure Ω) : ℝ) : EReal)) by
        funext x
        simp [smoothNormApproxTotalVariation_def, sSup_range]]
  exact lowerSemicontinuous_iSup fun v => by
    let C : ℝ := ∫ y, β * Real.sqrt (1 - ‖v.toTestFunction y‖ ^ 2) ∂domainMeasure Ω
    have hcontReal :
        Continuous
          (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
            -admissibleDivergencePairingCLM v
                ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x) + C) := by
      exact (continuous_evalOnWeakSpace (admissibleDivergencePairingCLM v)).neg.add continuous_const
    have hcontE :
        Continuous
          (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
            (((-admissibleDivergencePairingCLM v
                  ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x) + C : ℝ) :
                EReal))) :=
      continuous_coe_real_ereal.comp hcontReal
    refine (hcontE.congr ?_).lowerSemicontinuous
    intro x
    simpa [C] using
      (congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal))
        (smoothNormApproxTotalVariation_fixedField_eq β hβ v
          ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x))).symm

/-- Clause of Proposition 8.22. For each positive `ε`, the Chapter 8 Huber approximation `J_ε`
is lower semicontinuous for the weak topology on `L¹(Ω)`. -/
theorem huberApproxTotalVariation_lowerSemicontinuous_weakL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ε : ℝ)
    (_hε : 0 < ε) :
    LowerSemicontinuous
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        J_ε ε ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) := by
  -- The Huber penalty vanishes at `0`, so the generic zero-at-zero weak-lower-semicontinuity
  -- lemma applies unchanged.
  have hφ : Continuous (fun y : EuclideanSpace ℝ (Fin d) ↦ (ε / 2) * ‖y‖ ^ 2) := by
    continuity
  have hφ0 : (fun y : EuclideanSpace ℝ (Fin d) ↦ (ε / 2) * ‖y‖ ^ 2) 0 = 0 := by
    simp
  simpa [huberApproxTotalVariation_eq_approximateTotalVariation] using
    approximateTotalVariation_lowerSemicontinuous_weakL1_of_zero (Ω := Ω) hφ hφ0

/-- Clause of Proposition 8.22. As `β → 0⁺`, the Chapter 8 smooth approximation `J_β`
converges uniformly toward `TV` on every BV-bounded subset of `L¹(Ω)`. -/
theorem smoothNormApproxTotalVariation_tendstoUniformlyOn_isBVBounded
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))}
    (_hS : IsBVBounded S) :
    TendstoUniformlyOn
      smoothNormApproxTotalVariation
      totalVariation
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      S := by
  -- The imported convergence theorem is already uniform on arbitrary sets `S`.
  simpa using VariationalRegularization.smoothNormApproxTotalVariation_tendstoUniformlyOn
    (Ω := Ω) S

/-- Clause of Proposition 8.22. As `ε → 0⁺`, the Chapter 8 Huber approximation `J_ε`
converges uniformly toward `TV` on every BV-bounded subset of `L¹(Ω)`. -/
theorem huberApproxTotalVariation_tendstoUniformlyOn_isBVBounded
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {S : Set (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))}
    (_hS : IsBVBounded S) :
    TendstoUniformlyOn
      huberApproxTotalVariation
      totalVariation
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      S := by
  -- The imported convergence theorem is already uniform on arbitrary sets `S`.
  simpa using VariationalRegularization.huberApproxTotalVariation_tendstoUniformlyOn
    (Ω := Ω) S

end VariationalRegularization
