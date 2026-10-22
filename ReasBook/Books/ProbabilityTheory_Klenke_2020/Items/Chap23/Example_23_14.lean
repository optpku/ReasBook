/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory InformationTheory

noncomputable section

namespace ProbabilityTheory

/-- The two-point space `Σ = {-1,1}` underlying the symmetric Rademacher law. -/
inductive RademacherSign
  | negOne
  | one
  deriving DecidableEq, Fintype, Nonempty

open RademacherSign

/-- The two-point space `RademacherSign` carries the discrete measurable structure. -/
instance : MeasurableSpace RademacherSign := ⊤

/-- The measurable structure on `RademacherSign` is discrete. -/
instance : DiscreteMeasurableSpace RademacherSign := by
  infer_instance

/-- The uniform probability law on `Σ = {-1,1}`. -/
def rademacherUniformLaw : ProbabilityMeasure RademacherSign :=
  ⟨(PMF.uniformOfFintype RademacherSign).toMeasure, inferInstance⟩

-- Proof sketch: unfold `rademacherUniformLaw`; it is defined to be the probability measure coming
-- from the uniform pmf on the two-point space `RademacherSign`.
/-- The uniform law on `RademacherSign` is the measure associated with
`PMF.uniformOfFintype`. -/
theorem rademacherUniformLaw_toMeasure :
    (rademacherUniformLaw : Measure RademacherSign) =
      (PMF.uniformOfFintype RademacherSign).toMeasure := by
  -- Proof comment: `rademacherUniformLaw` was defined by packaging this measure as a
  -- `ProbabilityMeasure`.
  rfl

/-- The magnetization `m(ν) = ν({1}) - ν({-1})` of a probability law on `Σ = {-1,1}`. -/
def rademacherMagnetization (ν : ProbabilityMeasure RademacherSign) : ℝ :=
  (ν {one} : ℝ) - (ν {negOne} : ℝ)

-- Proof sketch: unfold `rademacherMagnetization`; the statement is exactly its defining formula.
/-- The magnetization of a law on `Σ = {-1,1}` is the difference between the masses at `1` and
`-1`. -/
theorem rademacherMagnetization_def (ν : ProbabilityMeasure RademacherSign) :
    rademacherMagnetization ν = (ν {one} : ℝ) - (ν {negOne} : ℝ) := by
  -- Proof comment: the theorem is exactly the defining equation of `rademacherMagnetization`.
  rfl

/-- Helper for Example 23.14: the Rademacher sign type has exactly two elements. -/
private theorem rademacherSign_card : Fintype.card RademacherSign = 2 := by
  decide

/-- Helper for Example 23.14: each coordinate of a discrete comparison mass function is finite
once its total mass is at most `1`. -/
private theorem pmfCoordinate_neTopOfTsumLeOne {E : Type*} (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (e : E) :
    q e ≠ ⊤ := by
  -- Proof comment: every coordinate is bounded by the total mass and hence by `1`.
  have hq_le_one : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
  exact ne_of_lt (lt_of_le_of_lt hq_le_one ENNReal.one_lt_top)

/-- Helper for Example 23.14: a discrete PMF can be written as a counting measure with density
`p / q` over the comparison weights `q`. -/
private theorem pmfToMeasure_eq_withDensityComparison {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E] [Fintype E]
    (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    let ν : Measure E := Measure.count.withDensity q
    p.toMeasure = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
  let ν : Measure E := Measure.count.withDensity q
  calc
    p.toMeasure = Measure.count.withDensity (fun e ↦ (p e : ENNReal)) := by
      -- Proof comment: rewrite `p.toMeasure` itself as a weighted counting measure.
      refine Measure.ext fun s hs ↦ ?_
      rw [p.toMeasure_apply hs, withDensity_apply _ hs]
      rw [← lintegral_indicator hs (fun e ↦ (p e : ENNReal)), lintegral_count]
    _ = (Measure.count.withDensity q).withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      -- Proof comment: compose the comparison weights `q` with the explicit ratio `p / q`.
      rw [← withDensity_mul (Measure.count : Measure E)]
      · refine withDensity_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro e
        by_cases hp : p e = 0
        · simp [hp]
        · have hq0 : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
          have hqTop : q e ≠ ⊤ := pmfCoordinate_neTopOfTsumLeOne q hq e
          have hmul : q e * (p e / q e) = p e := by
            calc
              q e * (p e / q e) = q e * (q e)⁻¹ * p e := by
                rw [ENNReal.div_eq_inv_mul, mul_assoc]
              _ = p e := by
                rw [ENNReal.mul_inv_cancel hq0 hqTop, one_mul]
          simpa [Pi.mul_apply] using hmul.symm
      · exact measurable_of_finite q
      · exact measurable_of_finite (fun e ↦ (p e : ENNReal) / q e)
    _ = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      rfl

/-- Helper for Example 23.14: on a finite discrete alphabet, the KL divergence against a
comparison mass function is the sum of the pointwise KL terms. -/
private theorem discreteKlDiv_eq_gapSeries {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E] [Fintype E]
    (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    let ν : Measure E := Measure.count.withDensity q
    klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
  let ν : Measure E := Measure.count.withDensity q
  letI : IsFiniteMeasure ν := by
    -- Proof comment: the comparison measure is finite because its total mass is at most `1`.
    refine ⟨?_⟩
    change (Measure.count.withDensity q) Set.univ < (⊤ : ENNReal)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact lt_of_le_of_lt hq ENNReal.one_lt_top
  have hpν : p.toMeasure ≪ ν := by
    rw [pmfToMeasure_eq_withDensityComparison p q hq hnozero]
    exact withDensity_absolutelyContinuous _ _
  change klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal))
  rw [klDiv_eq_lintegral_klFun_of_ac hpν]
  have hrn : p.toMeasure.rnDeriv ν =ᵐ[ν] fun e ↦ (p e : ENNReal) / q e := by
    rw [pmfToMeasure_eq_withDensityComparison p q hq hnozero]
    exact Measure.rnDeriv_withDensity ν (measurable_of_finite _)
  have hfun :
      (fun x ↦ ENNReal.ofReal (klFun (p.toMeasure.rnDeriv ν x).toReal)) =ᵐ[ν]
        fun e ↦ ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
    -- Proof comment: replace the Radon-Nikodym derivative by the explicit discrete density.
    filter_upwards [hrn] with x hx
    simp [hx]
  rw [lintegral_congr_ae hfun]
  rw [lintegral_withDensity_eq_lintegral_mul Measure.count]
  · rw [lintegral_count]
    congr with e
    have hqTop : q e ≠ ⊤ := pmfCoordinate_neTopOfTsumLeOne q hq e
    have hqReal_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    calc
      q e * ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) =
          ENNReal.ofReal (q e).toReal * ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
            rw [ENNReal.ofReal_toReal hqTop]
      _ = ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
            rw [← ENNReal.ofReal_mul hqReal_nonneg]
  · exact measurable_of_finite q
  · exact measurable_of_finite (fun e ↦ ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)))

/-- Helper for Example 23.14: on a finite discrete space, weighting counting measure by singleton
masses reconstructs the original probability law. -/
private theorem countWithDensity_singletonMass_eq {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E] [Fintype E]
    (μ : ProbabilityMeasure E) :
    Measure.count.withDensity (fun a ↦ (μ : Measure E) {a}) = (μ : Measure E) := by
  -- Proof comment: summing the singleton weights over a finite measurable set recovers the PMF.
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_count]
  simpa [Measure.toPMF_apply] using (((μ : Measure E).toPMF).toMeasure_apply_fintype s).symm

/-- Helper for Example 23.14: the Rademacher uniform law is counting measure weighted by `1 / 2`
on each atom. -/
private theorem rademacherUniformLaw_eq_countWithDensityHalf :
    Measure.count.withDensity (fun _ : RademacherSign => (1 / 2 : ENNReal)) =
      (rademacherUniformLaw : Measure RademacherSign) := by
  -- Proof comment: both measures assign the same mass `1 / 2` to every singleton.
  refine Measure.ext_of_singleton ?_
  intro a
  rw [withDensity_apply _ (measurableSet_singleton a), rademacherUniformLaw_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  simp [PMF.uniformOfFintype_apply, rademacherSign_card]

/-- Helper for Example 23.14: each singleton under the uniform Rademacher law has real mass
`1 / 2`. -/
private theorem rademacherUniformLaw_singleton_toReal (a : RademacherSign) :
    ((rademacherUniformLaw : Measure RademacherSign) {a}).toReal = (1 / 2 : ℝ) := by
  -- Proof comment: unfold the uniform PMF and evaluate it on a singleton of the two-point space.
  rw [rademacherUniformLaw_toMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  simp [PMF.uniformOfFintype_apply, rademacherSign_card]

/-- Helper for Example 23.14: the singleton masses of `ν` are the affine functions of the
magnetization `m(ν)`. -/
private theorem rademacherSingletonMasses_eq_halfAffine (ν : ProbabilityMeasure RademacherSign) :
    ((ν : Measure RademacherSign) {one}).toReal = (1 + rademacherMagnetization ν) / 2 ∧
      ((ν : Measure RademacherSign) {negOne}).toReal = (1 - rademacherMagnetization ν) / 2 := by
  have hsumENN :
      ((ν : Measure RademacherSign) {one}) + ((ν : Measure RademacherSign) {negOne}) = 1 := by
    -- Proof comment: the two singleton masses exhaust the total mass of the probability measure.
    have hdisj : Disjoint ({one} : Set RademacherSign) ({negOne} : Set RademacherSign) := by
      simp
    have huniv : ({one} : Set RademacherSign) ∪ ({negOne} : Set RademacherSign) = Set.univ := by
      ext a
      cases a <;> simp
    calc
      ((ν : Measure RademacherSign) {one}) + ((ν : Measure RademacherSign) {negOne})
          = (ν : Measure RademacherSign) (({one} : Set RademacherSign) ∪ ({negOne} : Set RademacherSign)) := by
              symm
              exact measure_union hdisj (measurableSet_singleton _)
      _ = 1 := by
              simpa [huniv] using ν.prop.measure_univ
  have hsum := congrArg ENNReal.toReal hsumENN
  have hsumReal :
      ((ν : Measure RademacherSign) {one}).toReal +
          ((ν : Measure RademacherSign) {negOne}).toReal = 1 := by
    have hone_top : (ν : Measure RademacherSign) {one} ≠ ⊤ := measure_ne_top _ _
    have hneg_top : (ν : Measure RademacherSign) {negOne} ≠ ⊤ := measure_ne_top _ _
    simpa [ENNReal.toReal_add, hone_top, hneg_top] using hsum
  have hone_real :
      ((ν : Measure RademacherSign) {one}).toReal = (ν {one} : ℝ) := by
    -- Proof comment: convert the measure-side singleton mass to the `ProbabilityMeasure` API.
    simpa [Measure.real] using
      (ProbabilityMeasure.measureReal_eq_coe_coeFn (ν := ν) ({one} : Set RademacherSign))
  have hneg_real :
      ((ν : Measure RademacherSign) {negOne}).toReal = (ν {negOne} : ℝ) := by
    -- Proof comment: the same conversion holds at the atom `{-1}`.
    simpa [Measure.real] using
      (ProbabilityMeasure.measureReal_eq_coe_coeFn (ν := ν) ({negOne} : Set RademacherSign))
  have hmag :
      rademacherMagnetization ν =
        ((ν : Measure RademacherSign) {one}).toReal -
          ((ν : Measure RademacherSign) {negOne}).toReal := by
    -- Proof comment: rewrite the magnetization through the measure-side singleton masses.
    rw [rademacherMagnetization_def, ← hone_real, ← hneg_real]
  constructor <;> linarith

/-- Helper for Example 23.14: the KL divergence against the uniform Rademacher law is the average
of the two scalar `klFun` terms indexed by the magnetization. -/
private theorem rademacherKlDiv_toReal_eq_halfKlFunSum (ν : ProbabilityMeasure RademacherSign) :
    (klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign)).toReal =
      (1 / 2 : ℝ) * klFun (1 + rademacherMagnetization ν) +
        (1 / 2 : ℝ) * klFun (1 - rademacherMagnetization ν) := by
  let p : PMF RademacherSign := (ν : Measure RademacherSign).toPMF
  let q : RademacherSign → ENNReal :=
    fun a ↦ (rademacherUniformLaw : Measure RademacherSign) {a}
  have hq : (∑' a : RademacherSign, q a) ≤ 1 := by
    -- Proof comment: these singleton masses are exactly the weights of the uniform PMF.
    exact le_of_eq <| by
      simpa [q, Measure.toPMF_apply] using
        (PMF.tsum_coe ((rademacherUniformLaw : Measure RademacherSign).toPMF))
  have hnozero : ∀ a ∈ p.support, q a ≠ 0 := by
    -- Proof comment: the uniform comparison mass is strictly positive on both atoms.
    intro a ha
    intro hqa
    have hmass := rademacherUniformLaw_singleton_toReal a
    simpa [q, hqa] using hmass
  have hkl :
      klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign) =
        ∑' a : RademacherSign,
          ENNReal.ofReal ((q a).toReal * klFun (((p a : ENNReal) / q a).toReal)) := by
    -- Proof comment: specialize the discrete KL expansion to the two-point comparison law.
    simpa [p, q, countWithDensity_singletonMass_eq (μ := rademacherUniformLaw)] using
      (discreteKlDiv_eq_gapSeries p q hq hnozero)
  rw [tsum_fintype] at hkl
  have hterm_ne_top :
      ∀ a ∈ (Finset.univ : Finset RademacherSign),
        ENNReal.ofReal ((q a).toReal * klFun (((p a : ENNReal) / q a).toReal)) ≠ ⊤ := by
    intro a ha
    have hnonneg : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
    simpa [ENNReal.ofReal_mul hnonneg] using
      (ENNReal.ofReal_ne_top :
        ENNReal.ofReal ((q a).toReal * klFun (((p a : ENNReal) / q a).toReal)) ≠ ⊤)
  have hklReal := congrArg ENNReal.toReal hkl
  rw [ENNReal.toReal_sum hterm_ne_top] at hklReal
  obtain ⟨hone_mass, hneg_mass⟩ := rademacherSingletonMasses_eq_halfAffine ν
  have hqone : (q one).toReal = (1 / 2 : ℝ) := by
    simpa [q] using rademacherUniformLaw_singleton_toReal one
  have hqneg : (q negOne).toReal = (1 / 2 : ℝ) := by
    simpa [q] using rademacherUniformLaw_singleton_toReal negOne
  have huniv : (Finset.univ : Finset RademacherSign) = {one, negOne} := by
    ext a
    cases a <;> simp
  have hone_ratio :
      (((p one : ENNReal) / q one).toReal) = 1 + rademacherMagnetization ν := by
    calc
      (((p one : ENNReal) / q one).toReal)
          = ((ν : Measure RademacherSign) {one}).toReal / (q one).toReal := by
              simp [p, q, Measure.toPMF_apply, ENNReal.toReal_div]
      _ = ((1 + rademacherMagnetization ν) / 2) / (1 / 2 : ℝ) := by
              rw [hone_mass, hqone]
      _ = 1 + rademacherMagnetization ν := by
              ring
  have hneg_ratio :
      (((p negOne : ENNReal) / q negOne).toReal) = 1 - rademacherMagnetization ν := by
    calc
      (((p negOne : ENNReal) / q negOne).toReal)
          = ((ν : Measure RademacherSign) {negOne}).toReal / (q negOne).toReal := by
              simp [p, q, Measure.toPMF_apply, ENNReal.toReal_div]
      _ = ((1 - rademacherMagnetization ν) / 2) / (1 / 2 : ℝ) := by
              rw [hneg_mass, hqneg]
      _ = 1 - rademacherMagnetization ν := by
              ring
  have hklReal_twoAtoms_raw :
      (klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign)).toReal =
        (q one).toReal * (ENNReal.ofReal (klFun (((p one : ENNReal) / q one).toReal))).toReal +
          (q negOne).toReal *
            (ENNReal.ofReal (klFun (((p negOne : ENNReal) / q negOne).toReal))).toReal := by
    -- Proof comment: `toReal` turns the finite `ENNReal` sum into the two real atom contributions.
    simpa [huniv, ENNReal.toReal_mul] using hklReal
  have hklReal_twoAtoms :
      (klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign)).toReal =
        (q one).toReal * klFun (((p one : ENNReal) / q one).toReal) +
          (q negOne).toReal * klFun (((p negOne : ENNReal) / q negOne).toReal) := by
    have hkone_nonneg : 0 ≤ klFun (((p one : ENNReal) / q one).toReal) :=
      klFun_nonneg ENNReal.toReal_nonneg
    have hkneg_nonneg : 0 ≤ klFun (((p negOne : ENNReal) / q negOne).toReal) :=
      klFun_nonneg ENNReal.toReal_nonneg
    -- Proof comment: each `ofReal` term is nonnegative because `klFun` is nonnegative.
    calc
      (klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign)).toReal
          = (q one).toReal * (ENNReal.ofReal (klFun (((p one : ENNReal) / q one).toReal))).toReal +
              (q negOne).toReal *
                (ENNReal.ofReal (klFun (((p negOne : ENNReal) / q negOne).toReal))).toReal :=
            hklReal_twoAtoms_raw
      _ = (q one).toReal * klFun (((p one : ENNReal) / q one).toReal) +
            (q negOne).toReal * klFun (((p negOne : ENNReal) / q negOne).toReal) := by
            rw [ENNReal.toReal_ofReal hkone_nonneg, ENNReal.toReal_ofReal hkneg_nonneg]
  -- Proof comment: substitute the uniform atom masses and the affine ratio formulas.
  calc
    (klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign)).toReal
        = (q one).toReal * klFun (((p one : ENNReal) / q one).toReal) +
            (q negOne).toReal * klFun (((p negOne : ENNReal) / q negOne).toReal) := hklReal_twoAtoms
    _ = (1 / 2 : ℝ) * klFun (1 + rademacherMagnetization ν) +
          (1 / 2 : ℝ) * klFun (1 - rademacherMagnetization ν) := by
            rw [hqone, hqneg, hone_ratio, hneg_ratio]

-- Proof sketch: the two-point space has only the atoms `-1` and `1`, and the Radon-Nikodym
-- derivative of `ν` with respect to the uniform law is constant on each singleton. Expanding the
-- finite two-atom Kullback-Leibler divergence yields the stated logarithmic expression.
/-- Example 23.14: on `Σ = {-1,1}`, modeled by `RademacherSign`, the relative entropy of
`ν ∈ M_1(Σ)` with respect to the uniform law is
`((1 + m(ν)) / 2) log (1 + m(ν)) + ((1 - m(ν)) / 2) log (1 - m(ν))`. This is the same explicit
rate function as in Theorem 23.1. -/
theorem rademacher_relativeEntropy_eq_magnetization_formula
    (ν : ProbabilityMeasure RademacherSign) :
    (klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign)).toReal =
      ((1 + rademacherMagnetization ν) / 2) * Real.log (1 + rademacherMagnetization ν) +
        ((1 - rademacherMagnetization ν) / 2) * Real.log (1 - rademacherMagnetization ν) := by
  -- Proof comment: first rewrite KL divergence as the average of the two scalar `klFun` terms.
  rw [rademacherKlDiv_toReal_eq_halfKlFunSum]
  -- Proof comment: expanding `klFun x = x log x + 1 - x` makes the affine linear terms cancel.
  rw [klFun_apply, klFun_apply]
  ring

end ProbabilityTheory
