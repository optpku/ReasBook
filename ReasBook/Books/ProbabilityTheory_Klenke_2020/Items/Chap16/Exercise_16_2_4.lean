/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Distributions.Exponential
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_28

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped Topology

namespace MeasureTheory.ProbabilityMeasure


/-- The stable index singled out by Exercise 16.2.4 from the heavier of the two power-law tails
when both tails are present, truncated at the Gaussian value `2`. -/
def exercise1624StableIndex (α β : ℝ) : ℝ :=
  min (2 : ℝ) (-max α β - 1)

/-- The stable index from Exercise 16.2.4 (i), determined by the tails whose coefficients are
nonzero. -/
def exercise1624CaseIStableIndex (ρ α β : ℝ) : ℝ :=
  if ρ = 0 then
    min (2 : ℝ) (-β - 1)
  else if ρ = 1 then
    min (2 : ℝ) (-α - 1)
  else
    exercise1624StableIndex α β

/-- Helper for Exercise 16.2.4: the textbook exponential law, promoted from `expMeasure` to a
probability measure so that it can be inserted into
`IsInDomainOfAttractionOfStableWithIndex`. -/
abbrev exercise1624ExponentialLaw (θ : ℝ) (hθ : 0 < θ) : ProbabilityMeasure ℝ :=
  ⟨expMeasure θ, isProbabilityMeasure_expMeasure hθ⟩

/-- Helper for Exercise 16.2.4: the textbook density from case (i). -/
def exercise1624CaseIDensity (ρ α β : ℝ) (x : ℝ) : ℝ :=
  if x < -1 then
    ρ * (-(1 + α)) * |x| ^ α
  else if 1 < x then
    (1 - ρ) * (-(1 + β)) * x ^ β
  else
    0

/-- Helper for Exercise 16.2.4: the normalization constant from case (iii), written as the inverse
of the sum of the even and odd zeta tails and using real parts so that it lands in `ℝ`. -/
def exercise1624CaseIIINormalizationConstant (α β : ℝ) : ℝ :=
  (((2 : ℝ) ^ α) * Complex.re (riemannZeta (-α)) +
      (1 - (2 : ℝ) ^ β) * Complex.re (riemannZeta (-β)))⁻¹

/-- Helper for Exercise 16.2.4: the odd/even singleton masses from case (iii). -/
def exercise1624CaseIIISingletonMass (α β : ℝ) (n : ℕ+) : ℝ :=
  if Even (n : ℕ) then
    exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ α
  else
    exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ β

/-- Expanding `exercise1624StableIndex` gives the heavier-tail formula from Exercise 16.2.4. -/
theorem exercise1624StableIndex_eq (α β : ℝ) :
    exercise1624StableIndex α β = min (2 : ℝ) (-max α β - 1) := by
  -- Proof comment: this is exactly the defining equation of `exercise1624StableIndex`.
  rfl

/-- Expanding `exercise1624CaseIStableIndex` gives the source-faithful case split from Exercise
16.2.4 (i). -/
theorem exercise1624CaseIStableIndex_eq (ρ α β : ℝ) :
    exercise1624CaseIStableIndex ρ α β =
      if ρ = 0 then
        min (2 : ℝ) (-β - 1)
      else if ρ = 1 then
        min (2 : ℝ) (-α - 1)
      else
        exercise1624StableIndex α β := by
  -- Proof comment: this theorem just unfolds the case split stored in the helper definition.
  rfl

/-- If the source exponents satisfy `α, β < -1`, then the Exercise 16.2.4 stable index belongs to
the stable range `(0, 2]`. -/
theorem exercise1624StableIndex_mem_Ioc
    {α β : ℝ} (hα : α < -1) (hβ : β < -1) :
    exercise1624StableIndex α β ∈ Set.Ioc (0 : ℝ) 2 := by
  -- Proof comment: both exponents are strictly below `-1`, so the heavier-tail exponent
  -- `-max α β - 1` is positive, and the outer `min 2` keeps the index at most `2`.
  rw [exercise1624StableIndex_eq]
  have hmax : max α β < -1 := max_lt_iff.mpr ⟨hα, hβ⟩
  have hpos : 0 < -max α β - 1 := by
    linarith
  exact ⟨lt_min zero_lt_two hpos, min_le_left _ _⟩

/-- Expanding `exercise1624CaseIDensity` recovers the source's piecewise formula from case (i). -/
theorem exercise1624CaseIDensity_eq (ρ α β x : ℝ) :
    exercise1624CaseIDensity ρ α β x =
      if x < -1 then
        ρ * (-(1 + α)) * |x| ^ α
      else if 1 < x then
        (1 - ρ) * (-(1 + β)) * x ^ β
      else
        0 := by
  -- Proof comment: this is a direct expansion of the piecewise density helper.
  rfl

/-- Expanding `exercise1624CaseIIINormalizationConstant` recovers the displayed zeta formula from
Exercise 16.2.4 (iii). -/
theorem exercise1624CaseIIINormalizationConstant_eq (α β : ℝ) :
    exercise1624CaseIIINormalizationConstant α β =
      (((2 : ℝ) ^ α) * Complex.re (riemannZeta (-α)) +
          (1 - (2 : ℝ) ^ β) * Complex.re (riemannZeta (-β)))⁻¹ := by
  -- Proof comment: this theorem only unfolds the normalization-constant definition.
  rfl

/-- Expanding `exercise1624CaseIIISingletonMass` recovers the odd/even power-law masses from case
(iii). -/
theorem exercise1624CaseIIISingletonMass_eq (α β : ℝ) (n : ℕ+) :
    exercise1624CaseIIISingletonMass α β n =
      if Even (n : ℕ) then
        exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ α
      else
        exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ β := by
  -- Proof comment: this is the defining odd/even split of the singleton masses.
  rfl

/-- `exercise1624ExponentialLaw θ hθ` is the probability measure carried by `expMeasure θ`. -/
theorem exercise1624ExponentialLaw_toMeasure
    (θ : ℝ) (hθ : 0 < θ) :
    ((exercise1624ExponentialLaw θ hθ : ProbabilityMeasure ℝ) : Measure ℝ) = expMeasure θ := by
  -- Proof comment: the helper is defined by bundling `expMeasure θ` with its probability proof.
  rfl

/-- Helper for Exercise 16.2.4: the law of a finite sum of independent copies of a probability
law is the corresponding convolution power. -/
lemma exercise1624HasLawFinsetSumPow
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (ν : ProbabilityMeasure ℝ)
    (Y : ι → Ω → ℝ) (hY_meas : ∀ i, Measurable (Y i))
    (hY_law : ∀ i, HasLaw (Y i) (ν : Measure ℝ) P)
    (hY_indep : iIndepFun Y P) :
    ∀ s : Finset ι,
      HasLaw (fun ω ↦ ∑ i ∈ s, Y i ω)
        (((ν ^ s.card : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) P := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sum has law `δ₀`, i.e. the zeroth convolution power.
      refine ProbabilityTheory.HasLaw.mk aemeasurable_const ?_
      simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
  | @insert i s hi ih =>
      let S : Ω → ℝ := fun ω ↦ ∑ j ∈ s, Y j ω
      have hSumEqS : (∑ j ∈ s, Y j) = S := by
        funext ω
        simp [S, Finset.sum_apply]
      have hsum :
          HasLaw S
            (((ν ^ s.card : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) P := by
        simpa [S] using ih
      have hindepSum :
          IndepFun (∑ j ∈ s, Y j) (Y i) P := by
        simpa using hY_indep.indepFun_finset_sum_of_notMem hY_meas hi
      have hindep : IndepFun S (Y i) P := by
        exact hSumEqS ▸ hindepSum
      have hstep :
          HasLaw
            (fun ω ↦ S ω + Y i ω)
            ((((ν ^ s.card : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ).conv
              (ν : Measure ℝ))
            P := by
        simpa [S, Pi.add_apply] using hindep.hasLaw_add hsum (hY_law i)
      -- Proof comment: adding one independent copy appends one more convolution factor.
      simpa [S, Finset.sum_insert hi, Finset.sum_apply, Pi.add_apply, pow_succ,
        Finset.card_insert_of_notMem hi, add_comm] using hstep

/-- Helper for Exercise 16.2.4: the standard Gaussian law is stable in the broad sense with
index `2`. -/
lemma exercise1624StandardGaussian_isStableWithIndexTwo :
    IsStableInBroadSenseWithIndex
      ((⟨gaussianReal (0 : ℝ) (1 : NNReal), inferInstance⟩ : ProbabilityMeasure ℝ)) 2 := by
  let μ : ProbabilityMeasure ℝ := ⟨gaussianReal (0 : ℝ) (1 : NNReal), inferInstance⟩
  refine ⟨?_, by simp, ?_⟩
  · intro x hx
    letI : NoAtoms (gaussianReal (0 : ℝ) (1 : NNReal)) := by
      simpa using
        (ProbabilityTheory.noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) one_ne_zero)
    have hzero : (gaussianReal (0 : ℝ) (1 : NNReal)) ({x} : Set ℝ) = 0 := by
      simpa using (Set.finite_singleton x).measure_zero (gaussianReal (0 : ℝ) (1 : NNReal))
    have hdirac : (gaussianReal (0 : ℝ) (1 : NNReal) : Measure ℝ) = (diracProba x : Measure ℝ) := by
      simpa [μ] using congrArg (fun η : ProbabilityMeasure ℝ ↦ (η : Measure ℝ)) hx
    have hone : (gaussianReal (0 : ℝ) (1 : NNReal)) ({x} : Set ℝ) = 1 := by
      rw [hdirac]
      simp [MeasureTheory.diracProba]
    rw [hone] at hzero
    norm_num at hzero
  · refine ⟨fun _ ↦ 0, ?_⟩
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    calc
      ((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)
          = (gaussianReal (0 : ℝ) (n : NNReal) : Measure ℝ) := by
              have hpow :
                  μ ^ (n : ℕ) =
                    (⟨gaussianReal (0 : ℝ) (n : NNReal), inferInstance⟩ : ProbabilityMeasure ℝ) := by
                simpa [μ] using
                  (measureConvolutionPower_gaussianReal_div_eq_gaussianReal
                    (m := (0 : ℝ)) (σ2 := (n : NNReal)) n)
              simpa using congrArg (fun η : ProbabilityMeasure ℝ ↦ (η : Measure ℝ)) hpow
      _ = Measure.map (fun x : ℝ ↦ Real.sqrt (n : ℝ) * x) (gaussianReal (0 : ℝ) (1 : NNReal)) := by
            symm
            simpa [Real.sq_sqrt (show 0 ≤ (n : ℝ) by exact_mod_cast n.2.le)] using
              (ProbabilityTheory.gaussianReal_map_const_mul
                (μ := (0 : ℝ)) (v := (1 : NNReal)) (Real.sqrt (n : ℝ)))
      _ = Measure.map (fun x : ℝ ↦ (n : ℝ) ^ (1 / (2 : ℝ)) * x + 0)
            (gaussianReal (0 : ℝ) (1 : NNReal)) := by
              congr with x
              simp [Real.sqrt_eq_rpow]
      _ = (map μ (measurable_affineMap ((n : ℝ) ^ (1 / (2 : ℝ))) 0).aemeasurable : Measure ℝ) := by
            rfl

/-- Helper for Exercise 16.2.4: any nondegenerate finite-variance law on `ℝ` is attracted to the
standard Gaussian, hence belongs to the stable domain of attraction with index `2`. -/
lemma exercise1624GaussianAttractionOfFiniteVarianceLaw
    {μ : ProbabilityMeasure ℝ}
    (hμ₂ : MemLp id 2 (μ : Measure ℝ))
    (hVar : Var[id; (μ : Measure ℝ)] ≠ 0) :
    IsInDomainOfAttractionOfStableWithIndex μ 2 := by
  let ν : ProbabilityMeasure ℝ := ⟨gaussianReal (0 : ℝ) (1 : NNReal), inferInstance⟩
  refine ⟨ν, ?_, exercise1624StandardGaussian_isStableWithIndexTwo⟩
  rw [mem_domainOfAttraction_iff]
  rcases ProbabilityTheory.exists_iid (ULift.{0} ℕ) ((μ : Measure ℝ)) with
    ⟨Ω, hΩ, P, Ylift, hYlift_meas, hYlift_law, hYlift_indep, hPprob⟩
  let PΩ : ProbabilityMeasure Ω := ⟨P, hPprob⟩
  let X : ℕ → Ω → ℝ := fun n ω ↦ Ylift ⟨n⟩ ω
  let a : ℕ+ → ℝ := fun n ↦ Real.sqrt ((n : ℝ) * Var[id; (μ : Measure ℝ)])
  let b : ℕ+ → ℝ := fun n ↦ (n : ℝ) * ∫ x, x ∂(μ : Measure ℝ)
  have hX_meas : ∀ n, Measurable (X n) := by
    intro n
    simpa [X] using hYlift_meas ⟨n⟩
  have hX_law : ∀ n, HasLaw (X n) (μ : Measure ℝ) PΩ := by
    intro n
    simpa [PΩ, X] using hYlift_law ⟨n⟩
  have hX_indep : iIndepFun X PΩ := by
    simpa [PΩ, X] using
      hYlift_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift.{0} ℕ))
        (fun _ _ hne => by simpa using hne)
  have hX_ident : ∀ n, IdentDistrib (X n) (X 0) (PΩ : Measure Ω) (PΩ : Measure Ω) := by
    intro n
    exact (hX_law n).identDistrib (hX_law 0)
  have hX_memLp : MemLp (X 0) 2 (PΩ : Measure Ω) := by
    have hX0_id :
        IdentDistrib (X 0) id (PΩ : Measure Ω) (μ : Measure ℝ) :=
      (hX_law 0).identDistrib (ProbabilityTheory.HasLaw.id (μ := (μ : Measure ℝ)))
    exact (hX0_id.memLp_iff).2 hμ₂
  have hX_var : Var[X 0; (PΩ : Measure Ω)] = Var[id; (μ : Measure ℝ)] := by
    exact (hX_law 0).variance_eq
  have hX_mean : (PΩ : Measure Ω)[X 0] = ∫ x, x ∂(μ : Measure ℝ) := by
    exact (hX_law 0).integral_eq
  refine ⟨a, b, ?_, ?_⟩
  · intro n
    have hvar_pos : 0 < Var[id; (μ : Measure ℝ)] :=
      lt_of_le_of_ne (variance_nonneg _ _) hVar.symm
    exact Real.sqrt_pos.2 (mul_pos (show 0 < (n : ℝ) by exact_mod_cast n.pos) hvar_pos)
  · have hclt :
        Tendsto
          (fun n ↦
            ProbabilityMeasure.map PΩ
              (aemeasurable_standardizedPartialSum (PΩ : Measure Ω) X
                (fun k ↦ (hX_ident k).aemeasurable_fst) n))
          atTop
          (𝓝 ν) := by
            simpa [ν] using
              standardizedPartialSumLaw_tendsto_standardGaussian
                (P := (PΩ : Measure Ω)) (X := X) hX_memLp
                (by simpa [hX_var] using hVar) hX_indep hX_ident
    have hcltShift :
        Tendsto
          (fun n ↦
            ProbabilityMeasure.map PΩ
              (aemeasurable_standardizedPartialSum (PΩ : Measure Ω) X
                (fun k ↦ (hX_ident k).aemeasurable_fst) (n + 1)))
          atTop
          (𝓝 ν) := by
            simpa using hclt.comp (tendsto_add_atTop_nat 1)
    have hstdLaw :
        ∀ n : ℕ,
          ProbabilityMeasure.map PΩ
              (aemeasurable_standardizedPartialSum (PΩ : Measure Ω) X
                (fun k ↦ (hX_ident k).aemeasurable_fst) (n + 1))
            = normalizedConvolutionLaw μ a b (Nat.succPNat n) := by
      intro n
      let n' : ℕ+ := Nat.succPNat n
      have hsum :
          HasLaw (fun ω ↦ ∑ i ∈ Finset.range (n + 1), X i ω)
            (((μ ^ (n' : ℕ) : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) PΩ := by
        simpa [n', Nat.succPNat_coe] using
          exercise1624HasLawFinsetSumPow PΩ μ X hX_meas hX_law hX_indep
            (Finset.range (n + 1))
      have hmap :
          Measure.map
              (standardizedPartialSum (PΩ : Measure Ω) X (n + 1))
              (PΩ : Measure Ω)
            = ((normalizedConvolutionLaw μ a b n' : ProbabilityMeasure ℝ) : Measure ℝ) := by
        calc
          Measure.map
              (standardizedPartialSum (PΩ : Measure Ω) X (n + 1))
              (PΩ : Measure Ω)
              =
                Measure.map
                  (fun ω ↦
                    (a n')⁻¹ * (∑ i ∈ Finset.range (n + 1), X i ω) + -(a n')⁻¹ * b n')
                  (PΩ : Measure Ω) := by
                    congr with ω
                    rw [standardizedPartialSum, hX_var, hX_mean]
                    simp [a, b, n', Nat.succPNat_coe]
                    ring
          _ =
              Measure.map
                (fun x : ℝ ↦ (a n')⁻¹ * x + -(a n')⁻¹ * b n')
                (((μ ^ (n' : ℕ) : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) := by
                  rw [show
                      (fun ω ↦ (a n')⁻¹ * ∑ i ∈ Finset.range (n + 1), X i ω + -(a n')⁻¹ * b n') =
                        (fun x : ℝ ↦ (a n')⁻¹ * x + -(a n')⁻¹ * b n') ∘
                          (fun ω ↦ ∑ i ∈ Finset.range (n + 1), X i ω) by
                        rfl]
                  rw [← Measure.map_map]
                  · rw [hsum.map_eq]
                  · fun_prop
                  · fun_prop
          _ =
              ((normalizedConvolutionLaw μ a b n' : ProbabilityMeasure ℝ) : Measure ℝ) := by
                rfl
      exact ProbabilityMeasure.toMeasure_injective hmap
    have hseqEq :
        (fun n : ℕ ↦
          ProbabilityMeasure.map PΩ
            (aemeasurable_standardizedPartialSum (PΩ : Measure Ω) X
              (fun k ↦ (hX_ident k).aemeasurable_fst) (n + 1))) =
          fun n : ℕ ↦ normalizedConvolutionLaw μ a b (Nat.succPNat n) := by
      funext n
      exact hstdLaw n
    have hnat :
        Tendsto (fun n : ℕ ↦ normalizedConvolutionLaw μ a b (Nat.succPNat n)) atTop (𝓝 ν) := by
      simpa [hseqEq] using hcltShift
    have hcomp := hnat.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Exercise 16.2.4: a square-integrable real law that is not a Dirac mass has
nonzero variance. -/
lemma exercise1624VarianceNeZeroOfNotDirac
    {μ : ProbabilityMeasure ℝ}
    (hμ₂ : MemLp id 2 (μ : Measure ℝ))
    (hμ_nontrivial : ∀ x : ℝ, μ ≠ diracProba x) :
    Var[id; (μ : Measure ℝ)] ≠ 0 := by
  -- Proof comment: the intended route uses the standard variance-zero characterization to show
  -- that the identity map is almost surely constant, hence the law is Dirac, contradicting
  -- `hμ_nontrivial`.
  intro hVar
  let m : ℝ := ∫ x, x ∂(μ : Measure ℝ)
  have hconst : id =ᵐ[(μ : Measure ℝ)] fun _ ↦ m := by
    simpa [m] using ae_eq_integral_of_variance_eq_zero hμ₂ hVar
  have hdiracMeasure : (μ : Measure ℝ) = (diracProba m : Measure ℝ) := by
    calc
      (μ : Measure ℝ) = Measure.map id (μ : Measure ℝ) := by
        rw [Measure.map_id]
      _ = Measure.map (fun _ : ℝ ↦ m) (μ : Measure ℝ) := by
        rw [Measure.map_congr hconst]
      _ = (diracProba m : Measure ℝ) := by
        rw [Measure.map_const]
        simp [MeasureTheory.diracProba]
  have hdirac : μ = diracProba m := ProbabilityMeasure.toMeasure_injective hdiracMeasure
  exact hμ_nontrivial m hdirac

/-- Helper for Exercise 16.2.4: the case-(i) density is pointwise nonnegative under the source
assumptions. -/
lemma exercise1624CaseIDensity_nonneg
    {ρ α β : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1) :
    ∀ x : ℝ, 0 ≤ exercise1624CaseIDensity ρ α β x := by
  intro x
  -- Proof comment: each branch is a nonnegative coefficient times a nonnegative power kernel.
  rw [exercise1624CaseIDensity_eq]
  split_ifs with hxneg hxpos
  · have hcoeff : 0 ≤ ρ * (-(1 + α)) := by
      refine mul_nonneg hρ.1 ?_
      linarith
    exact mul_nonneg hcoeff (Real.rpow_nonneg (abs_nonneg x) α)
  · have hcoeff : 0 ≤ (1 - ρ) * (-(1 + β)) := by
      refine mul_nonneg (sub_nonneg.mpr hρ.2) ?_
      linarith
    have hxnonneg : 0 ≤ x := le_trans zero_lt_one.le (le_of_lt hxpos)
    exact mul_nonneg hcoeff (Real.rpow_nonneg hxnonneg β)
  · norm_num

/-- Helper for Exercise 16.2.4: the right tail in case (i) is the explicit surviving positive-ray
power law. -/
lemma exercise1624CaseIRightTail_eq
    {μ : ProbabilityMeasure ℝ} {ρ α β x : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1)
    (hx : 1 ≤ x)
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun y ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β y))) :
    rightTail μ x = (1 - ρ) * x ^ (β + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hmeas : Measurable (exercise1624CaseIDensity ρ α β) := by
    -- Proof comment: the density is a measurable nested `if` with measurable power kernels.
    have hLeft : Measurable (fun z : ℝ ↦ ρ * (-(1 + α)) * |z| ^ α) := by
      fun_prop
    have hRight : Measurable (fun z : ℝ ↦ (1 - ρ) * (-(1 + β)) * z ^ β) := by
      fun_prop
    unfold exercise1624CaseIDensity
    exact Measurable.ite measurableSet_Iio hLeft
      (Measurable.ite measurableSet_Ioi hRight measurable_const)
  rw [rightTail, hμ, withDensity_apply _ measurableSet_Ici]
  change (∫⁻ a in Set.Ici x, ENNReal.ofReal (exercise1624CaseIDensity ρ α β a) ∂volume).toReal =
    (1 - ρ) * x ^ (β + 1)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ici x)] fun a : ℝ ↦ exercise1624CaseIDensity ρ α β a := by
    filter_upwards with a
    exact exercise1624CaseIDensity_nonneg hρ hα hβ a
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have hkernel :
      ∫ a in Set.Ici x, exercise1624CaseIDensity ρ α β a ∂volume =
        ∫ a in Set.Ioi x, (1 - ρ) * (-(1 + β)) * a ^ β ∂volume := by
    -- Proof comment: beyond `x ≥ 1`, only the positive-ray power branch of the density remains.
    rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha ↦ ?_
    have hxa : x < a := ha
    have h1a : 1 < a := lt_of_le_of_lt hx hxa
    have hnotNeg : ¬ a < -1 := by linarith
    rw [exercise1624CaseIDensity_eq, if_neg hnotNeg, if_pos h1a]
  rw [hkernel, integral_const_mul, integral_Ioi_rpow_of_lt hβ hx0]
  have hβne : β + 1 ≠ 0 := by
    linarith
  field_simp [hβne]
  ring

/-- Helper for Exercise 16.2.4: the left tail in case (i) is the explicit surviving negative-ray
power law. -/
lemma exercise1624CaseILeftTail_eq
    {μ : ProbabilityMeasure ℝ} {ρ α β x : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1)
    (hx : 1 ≤ x)
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun y ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β y))) :
    ((μ : Measure ℝ) (Set.Iic (-x))).toReal = ρ * x ^ (α + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hmeas : Measurable (exercise1624CaseIDensity ρ α β) := by
    -- Proof comment: the same branchwise measurability proof works on the negative-ray integral.
    have hLeft : Measurable (fun z : ℝ ↦ ρ * (-(1 + α)) * |z| ^ α) := by
      fun_prop
    have hRight : Measurable (fun z : ℝ ↦ (1 - ρ) * (-(1 + β)) * z ^ β) := by
      fun_prop
    unfold exercise1624CaseIDensity
    exact Measurable.ite measurableSet_Iio hLeft
      (Measurable.ite measurableSet_Ioi hRight measurable_const)
  rw [hμ, withDensity_apply _ measurableSet_Iic]
  change (∫⁻ a in Set.Iic (-x), ENNReal.ofReal (exercise1624CaseIDensity ρ α β a) ∂volume).toReal =
    ρ * x ^ (α + 1)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Iic (-x))] fun a : ℝ ↦ exercise1624CaseIDensity ρ α β a := by
    filter_upwards with a
    exact exercise1624CaseIDensity_nonneg hρ hα hβ a
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have hkernel :
      ∫ a in Set.Iic (-x), exercise1624CaseIDensity ρ α β a ∂volume =
        ∫ a in Set.Iio (-x), ρ * (-(1 + α)) * (-a) ^ α ∂volume := by
    -- Proof comment: on the negative ray, `|a| = -a` and only the left branch of the density
    -- contributes.
    rw [integral_Iic_eq_integral_Iio]
    refine setIntegral_congr_fun measurableSet_Iio fun a ha ↦ ?_
    have hax : a < -x := ha
    have haNeg : a < -1 := by
      linarith
    have hnotPos : ¬ 1 < a := by
      linarith
    have habs : |a| = -a := abs_of_nonpos (by linarith)
    rw [exercise1624CaseIDensity_eq, if_pos haNeg, habs]
  rw [hkernel]
  have hcomp :
      ∫ a in Set.Iio (-x), ρ * (-(1 + α)) * (-a) ^ α ∂volume =
        ∫ a in Set.Ioi x, ρ * (-(1 + α)) * a ^ α ∂volume := by
    calc
      ∫ a in Set.Iio (-x), ρ * (-(1 + α)) * (-a) ^ α ∂volume
          = ∫ a in Set.Iic (-x), ρ * (-(1 + α)) * (-a) ^ α ∂volume := by
              rw [← integral_Iic_eq_integral_Iio]
      _ = ∫ a in Set.Ioi x, ρ * (-(1 + α)) * a ^ α ∂volume := by
            simpa using (integral_comp_neg_Iic (-x) (fun t : ℝ ↦ ρ * (-(1 + α)) * t ^ α))
  rw [hcomp, integral_const_mul, integral_Ioi_rpow_of_lt hα hx0]
  have hαne : α + 1 ≠ 0 := by
    linarith
  field_simp [hαne]
  ring

/-- Helper for Exercise 16.2.4: the two-sided tail in case (i) splits into the explicit left and
right power-law tails once `x ≥ 1`. -/
lemma exercise1624CaseIAbsTail_eq
    {μ : ProbabilityMeasure ℝ} {ρ α β x : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1)
    (hx : 1 ≤ x)
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun y ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β y))) :
    absTail μ x = ρ * x ^ (α + 1) + (1 - ρ) * x ^ (β + 1) := by
  -- Proof comment: the intended proof splits `{|y| ≥ x}` into the left and right rays and then
  -- invokes the explicit one-sided tail formulas proved just above.
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsplit :
      {y : ℝ | x ≤ |y|} = Set.Iic (-x) ∪ Set.Ici x := by
    ext y
    constructor
    · intro hy
      have hyabs : x ≤ |y| := by simpa using hy
      by_cases hyleft : y ≤ -x
      · exact Or.inl hyleft
      · have hygt : -x < y := lt_of_not_ge hyleft
        have hyx : x ≤ y := by
          by_cases hyneg : y < 0
          · rw [abs_of_neg hyneg] at hyabs
            linarith
          · rw [abs_of_nonneg (le_of_not_gt hyneg)] at hyabs
            exact hyabs
        exact Or.inr hyx
    · intro hy
      rcases hy with hleft | hright
      · have hleft' : y ≤ -x := by simpa using hleft
        have hy_nonpos : y ≤ 0 := by linarith
        show x ≤ |y|
        rw [abs_of_nonpos hy_nonpos]
        linarith
      · have hright' : x ≤ y := by simpa using hright
        have hy_nonneg : 0 ≤ y := le_trans (show 0 ≤ x by linarith) hright'
        show x ≤ |y|
        rw [abs_of_nonneg hy_nonneg]
        exact hright'
  have hdisj : Disjoint (Set.Iic (-x)) (Set.Ici x) := by
    rw [Set.disjoint_left]
    intro y hleft hright
    have hleft' : y ≤ -x := by simpa using hleft
    have hright' : x ≤ y := by simpa using hright
    linarith
  have hleft_top : (μ : Measure ℝ) (Set.Iic (-x)) ≠ ⊤ := measure_ne_top _ _
  have hright_top : (μ : Measure ℝ) (Set.Ici x) ≠ ⊤ := measure_ne_top _ _
  unfold absTail
  rw [hsplit, measure_union hdisj measurableSet_Ici, ENNReal.toReal_add hleft_top hright_top]
  rw [exercise1624CaseILeftTail_eq hρ hα hβ hx hμ]
  change ρ * x ^ (α + 1) + rightTail μ x = ρ * x ^ (α + 1) + (1 - ρ) * x ^ (β + 1)
  rw [exercise1624CaseIRightTail_eq hρ hα hβ hx hμ]

/-- Helper for Exercise 16.2.4: the case-(i) law has zero mass at every singleton. -/
lemma exercise1624CaseISingleton_eq_zero
    {μ : ProbabilityMeasure ℝ} {ρ α β x : ℝ}
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun y ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β y))) :
    (μ : Measure ℝ) ({x} : Set ℝ) = 0 := by
  -- Proof comment: the law is absolutely continuous with respect to Lebesgue measure.
  rw [hμ, withDensity_apply _ (measurableSet_singleton x)]
  simp

/-- Helper for Exercise 16.2.4: the case-(i) law is never a Dirac mass because every singleton
has zero measure. -/
lemma exercise1624CaseINotDirac
    {μ : ProbabilityMeasure ℝ} {ρ α β : ℝ}
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun y ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β y))) :
    ∀ x : ℝ, μ ≠ diracProba x := by
  intro x hx
  have hzero : (μ : Measure ℝ) ({x} : Set ℝ) = 0 :=
    exercise1624CaseISingleton_eq_zero (ρ := ρ) (α := α) (β := β) (x := x) hμ
  have hone : (μ : Measure ℝ) ({x} : Set ℝ) = 1 := by
    simpa [MeasureTheory.diracProba] using
      congrArg (fun ν : ProbabilityMeasure ℝ ↦ (ν : Measure ℝ) ({x} : Set ℝ)) hx
  rw [hone] at hzero
  norm_num at hzero

/-- Helper for Exercise 16.2.4: the source-faithful case-(i) stable index is always bounded above
by `2`. -/
lemma exercise1624CaseIStableIndex_le_two
    (ρ α β : ℝ) :
    exercise1624CaseIStableIndex ρ α β ≤ 2 := by
  -- Proof comment: every branch is an explicit `min 2 (...)`.
  rw [exercise1624CaseIStableIndex_eq]
  split_ifs <;> simp [exercise1624StableIndex_eq]

/-- Helper for Exercise 16.2.4: the tail criterion `(16.29)` determines its index uniquely. -/
lemma exercise1624TailCriterion_index_unique
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hα : TailCriterion16_29 μ α) (hβ : TailCriterion16_29 μ β) :
    α = β := by
  have hEq : (2 : ℝ) ^ (-α) = (2 : ℝ) ^ (-β) :=
    tendsto_nhds_unique (hα 2 zero_lt_two) (hβ 2 zero_lt_two)
  have hLogEq :
      Real.log ((2 : ℝ) ^ (-α)) = Real.log ((2 : ℝ) ^ (-β)) := congrArg Real.log hEq
  rw [Real.log_rpow zero_lt_two, Real.log_rpow zero_lt_two] at hLogEq
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  nlinarith

/-- Helper for Exercise 16.2.4: if a power tail with exponent `t` dominates a smaller power tail
with exponent `s`, then the scaled tail ratio converges to `c^t`. -/
lemma exercise1624_twoPowerTail_ratio_tendsto_of_lt
    {A B s t c : ℝ}
    (hc : 0 < c) (hst : s < t) (hB : B ≠ 0) :
    Tendsto
      (fun x : ℝ ↦
        (A * (c * x) ^ s + B * (c * x) ^ t) /
          (A * x ^ s + B * x ^ t))
      atTop
      (𝓝 (c ^ t)) := by
  have hsmallRaw :
      Tendsto (fun x : ℝ ↦ x ^ (-(t - s))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (sub_pos.mpr hst)
  have hsmall :
      Tendsto (fun x : ℝ ↦ x ^ (s - t)) atTop (𝓝 0) := by
    convert hsmallRaw using 1
    ext x
    congr 1
    ring
  have hEventuallyEq :
      (fun x : ℝ ↦
        (A * (c * x) ^ s + B * (c * x) ^ t) /
          (A * x ^ s + B * x ^ t)) =ᶠ[atTop]
        (fun x : ℝ ↦
          (A * c ^ s * x ^ (s - t) + B * c ^ t) /
            (A * x ^ (s - t) + B)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hcx : 0 < c * x := mul_pos hc hx
    have hxt_ne : x ^ t ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    have hnum :
        A * (c * x) ^ s + B * (c * x) ^ t =
          (A * c ^ s * x ^ (s - t) + B * c ^ t) * x ^ t := by
      calc
        A * (c * x) ^ s + B * (c * x) ^ t
            = A * (c ^ s * x ^ s) + B * (c ^ t * x ^ t) := by
                rw [Real.mul_rpow hc.le hx.le, Real.mul_rpow hc.le hx.le]
        _ = A * (c ^ s * (x ^ (s - t) * x ^ t)) + B * (c ^ t * x ^ t) := by
              congr 2
              rw [← Real.rpow_add hx]
              congr 1
              ring
        _ = (A * c ^ s * x ^ (s - t) + B * c ^ t) * x ^ t := by ring
    have hden :
        A * x ^ s + B * x ^ t = (A * x ^ (s - t) + B) * x ^ t := by
      calc
        A * x ^ s + B * x ^ t = A * (x ^ (s - t) * x ^ t) + B * x ^ t := by
          congr 2
          rw [← Real.rpow_add hx]
          congr 1
          ring
        _ = (A * x ^ (s - t) + B) * x ^ t := by ring
    rw [hnum, hden, mul_div_mul_right _ _ hxt_ne]
  have hNum :
      Tendsto
        (fun x : ℝ ↦ A * c ^ s * x ^ (s - t) + B * c ^ t)
        atTop
        (𝓝 (B * c ^ t)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hsmall.const_mul (A * c ^ s)).add tendsto_const_nhds
  have hDen :
      Tendsto (fun x : ℝ ↦ A * x ^ (s - t) + B) atTop (𝓝 B) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hsmall.const_mul A).add tendsto_const_nhds
  refine Tendsto.congr' hEventuallyEq.symm ?_
  simpa [hB] using hNum.div hDen hB

/-- Helper for Exercise 16.2.4: the dominant summand in a two-power tail contributes asymptotic
share `1`. -/
lemma exercise1624_dominantPowerTail_share_tendsto_one
    {A B s t : ℝ}
    (hst : s < t) (hB : B ≠ 0) :
    Tendsto
      (fun x : ℝ ↦
        B * x ^ t / (A * x ^ s + B * x ^ t))
      atTop
      (𝓝 1) := by
  have hsmallRaw :
      Tendsto (fun x : ℝ ↦ x ^ (-(t - s))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (sub_pos.mpr hst)
  have hsmall :
      Tendsto (fun x : ℝ ↦ x ^ (s - t)) atTop (𝓝 0) := by
    convert hsmallRaw using 1
    ext x
    congr 1
    ring
  have hEventuallyEq :
      (fun x : ℝ ↦ B * x ^ t / (A * x ^ s + B * x ^ t)) =ᶠ[atTop]
        (fun x : ℝ ↦ B / (A * x ^ (s - t) + B)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hxt_ne : x ^ t ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    have hden :
        A * x ^ s + B * x ^ t = (A * x ^ (s - t) + B) * x ^ t := by
      calc
        A * x ^ s + B * x ^ t = A * (x ^ (s - t) * x ^ t) + B * x ^ t := by
          congr 2
          rw [← Real.rpow_add hx]
          congr 1
          ring
        _ = (A * x ^ (s - t) + B) * x ^ t := by ring
    rw [hden, mul_div_mul_right _ _ hxt_ne]
  have hDen :
      Tendsto (fun x : ℝ ↦ A * x ^ (s - t) + B) atTop (𝓝 B) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hsmall.const_mul A).add tendsto_const_nhds
  refine Tendsto.congr' hEventuallyEq.symm ?_
  simpa [hB] using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ B) atTop (𝓝 B)).div hDen hB

/-- Helper for Exercise 16.2.4: a single power tail scales exactly under dilation once `x` is
positive. -/
lemma exercise1624_singlePowerTail_ratio_tendsto
    {c s : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ (c * x) ^ s / x ^ s) atTop (𝓝 (c ^ s)) := by
  have hEventuallyEq :
      (fun x : ℝ ↦ (c * x) ^ s / x ^ s) =ᶠ[atTop]
        fun _ : ℝ ↦ c ^ s := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hxs : x ^ s ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    -- Proof comment: on the positive half-line, `Real.mul_rpow` splits the scale factor and the
    -- common `x ^ s` denominator cancels exactly.
    rw [Real.mul_rpow hc.le hx.le, mul_div_assoc, div_self hxs, mul_one]
  refine Tendsto.congr' hEventuallyEq.symm ?_
  simpa using tendsto_const_nhds

/-- Helper for Exercise 16.2.4: a positive right-tail power-law limit upgrades to the Chapter 16
tail criterion once the absolute tail eventually agrees with the right tail. -/
lemma tailCriterionOfEventualRightTailRpowLimit
    {μ : ProbabilityMeasure ℝ} {γ K : ℝ}
    (hK : 0 < K)
    (hRight :
      Tendsto (fun x : ℝ ↦ rightTail μ x / x ^ γ) atTop (𝓝 K))
    (hAbsEq :
      (fun x : ℝ ↦ absTail μ x) =ᶠ[atTop] fun x ↦ rightTail μ x)
    (hRightPos : ∀ᶠ x : ℝ in atTop, 0 < rightTail μ x) :
    TailCriterion16_29 μ (-γ) := by
  intro c hc
  have hcx : Tendsto (fun x : ℝ ↦ c * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' hc tendsto_id
  have hScaled :
      Tendsto (fun x : ℝ ↦ rightTail μ (c * x) / (c * x) ^ γ) atTop (𝓝 K) :=
    hRight.comp hcx
  have hRightRatio :
      Tendsto (fun x : ℝ ↦ rightTail μ (c * x) / rightTail μ x) atTop (𝓝 (c ^ γ)) := by
    have hNum :
        Tendsto
          (fun x : ℝ ↦
            (rightTail μ (c * x) / (c * x) ^ γ) * ((c * x) ^ γ / x ^ γ))
          atTop
          (𝓝 (K * c ^ γ)) :=
      hScaled.mul (exercise1624_singlePowerTail_ratio_tendsto (c := c) (s := γ) hc)
    have hExpr :
        Tendsto
          (fun x : ℝ ↦
            ((rightTail μ (c * x) / (c * x) ^ γ) * ((c * x) ^ γ / x ^ γ)) /
              (rightTail μ x / x ^ γ))
          atTop
          (𝓝 ((K * c ^ γ) / K)) :=
      hNum.div hRight (ne_of_gt hK)
    have hEventuallyEq :
        (fun x : ℝ ↦ rightTail μ (c * x) / rightTail μ x) =ᶠ[atTop]
          (fun x : ℝ ↦
            ((rightTail μ (c * x) / (c * x) ^ γ) * ((c * x) ^ γ / x ^ γ)) /
              (rightTail μ x / x ^ γ)) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), hRightPos] with x hx hrt
      have hxpow_ne : x ^ γ ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
      have hcxpow_ne : (c * x) ^ γ ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hc hx) _).ne'
      have hright_ne : rightTail μ x ≠ 0 := ne_of_gt hrt
      field_simp [hxpow_ne, hcxpow_ne, hright_ne]
    refine Tendsto.congr' hEventuallyEq.symm ?_
    have hLimitEq : (K * c ^ γ) / K = c ^ γ := by
      field_simp [ne_of_gt hK]
    simpa [hLimitEq] using hExpr
  have hAbsEqScaled :
      (fun x : ℝ ↦ absTail μ (c * x)) =ᶠ[atTop] fun x ↦ rightTail μ (c * x) :=
    hAbsEq.comp_tendsto hcx
  have hEventuallyEq :
      (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
        (fun x : ℝ ↦ rightTail μ (c * x) / rightTail μ x) := by
    filter_upwards [hAbsEqScaled, hAbsEq] with x hxScaled hx
    rw [hxScaled, hx]
  -- Proof comment: once both numerator and denominator tails are normalized to the right tail,
  -- the required ratio is exactly the right-tail regular-variation ratio.
  refine Tendsto.congr' hEventuallyEq.symm ?_
  simpa using hRightRatio

/-- Helper for Exercise 16.2.4: below the Gaussian boundary, the explicit case-(i) tails satisfy
the Chapter 16 tail criterion and positive-tail-share criterion. -/
lemma exercise1624CaseIHeavyTailCriteria
    {μ : ProbabilityMeasure ℝ} {ρ α β : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1)
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun x ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β x)))
    (hidx_lt_two : exercise1624CaseIStableIndex ρ α β < 2) :
    TailCriterion16_29 μ (exercise1624CaseIStableIndex ρ α β) ∧
      PositiveTailShareCriterion16_30 μ := by
  constructor
  · intro c hc
    by_cases hρ0 : ρ = 0
    · have hβ_lt_two : -β - 1 < 2 := by
        by_contra hnot
        have hβ_ge_two : 2 ≤ -β - 1 := not_lt.mp hnot
        rw [exercise1624CaseIStableIndex_eq, if_pos hρ0, min_eq_left hβ_ge_two] at hidx_lt_two
        linarith
      have hidx_eq : exercise1624CaseIStableIndex ρ α β = -β - 1 := by
        rw [exercise1624CaseIStableIndex_eq, if_pos hρ0, min_eq_right (le_of_lt hβ_lt_two)]
      have hEventuallyEq :
          (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
            fun x : ℝ ↦ (c * x) ^ (β + 1) / x ^ (β + 1) := by
        filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
        have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
        have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
        have hcx1 : 1 ≤ c * x := by
          have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
          have hc_ne : c ≠ 0 := ne_of_gt hc
          have hone : 1 < c * x := by
            simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
          exact le_of_lt hone
        -- Proof comment: when `ρ = 0`, the absolute tail is exactly the surviving right-hand
        -- power tail on both arguments.
        rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
          exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ, hρ0]
        norm_num
      refine Tendsto.congr' hEventuallyEq.symm ?_
      convert exercise1624_singlePowerTail_ratio_tendsto (c := c) (s := β + 1) hc using 2
      rw [hidx_eq]
      ring
    · by_cases hρ1 : ρ = 1
      · have hα_lt_two : -α - 1 < 2 := by
          by_contra hnot
          have hα_ge_two : 2 ≤ -α - 1 := not_lt.mp hnot
          rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_pos hρ1, min_eq_left hα_ge_two] at hidx_lt_two
          linarith
        have hidx_eq : exercise1624CaseIStableIndex ρ α β = -α - 1 := by
          rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_pos hρ1,
            min_eq_right (le_of_lt hα_lt_two)]
        have hEventuallyEq :
            (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
              fun x : ℝ ↦ (c * x) ^ (α + 1) / x ^ (α + 1) := by
          filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
          have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
          have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
          have hcx1 : 1 ≤ c * x := by
            have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
            have hc_ne : c ≠ 0 := ne_of_gt hc
            have hone : 1 < c * x := by
              simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
            exact le_of_lt hone
          -- Proof comment: when `ρ = 1`, only the left-hand power tail survives in `absTail`.
          rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
            exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ, hρ1]
          norm_num
        refine Tendsto.congr' hEventuallyEq.symm ?_
        convert exercise1624_singlePowerTail_ratio_tendsto (c := c) (s := α + 1) hc using 2
        rw [hidx_eq]
        ring
      · rcases lt_trichotomy α β with hlt | hEq | hgt
        · have hβ_lt_two : -β - 1 < 2 := by
            by_contra hnot
            have hβ_ge_two : 2 ≤ -β - 1 := not_lt.mp hnot
            rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
              exercise1624StableIndex_eq, max_eq_right (le_of_lt hlt), min_eq_left hβ_ge_two] at hidx_lt_two
            linarith
          have hidx_eq : exercise1624CaseIStableIndex ρ α β = -β - 1 := by
            rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
              exercise1624StableIndex_eq, max_eq_right (le_of_lt hlt),
              min_eq_right (le_of_lt hβ_lt_two)]
          have hB : 1 - ρ ≠ 0 := sub_ne_zero.mpr (by simpa [eq_comm] using hρ1)
          have hEventuallyEq :
              (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
                (fun x : ℝ ↦
                  (ρ * (c * x) ^ (α + 1) + (1 - ρ) * (c * x) ^ (β + 1)) /
                    (ρ * x ^ (α + 1) + (1 - ρ) * x ^ (β + 1))) := by
            filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
            have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
            have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
            have hcx1 : 1 ≤ c * x := by
              have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
              have hc_ne : c ≠ 0 := ne_of_gt hc
              have hone : 1 < c * x := by
                simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
              exact le_of_lt hone
            -- Proof comment: in the mixed branch with `α < β`, the exact two-power tail formula
            -- is available simultaneously at `x` and `c * x`.
            rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
              exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ]
          refine Tendsto.congr' hEventuallyEq.symm ?_
          convert
            exercise1624_twoPowerTail_ratio_tendsto_of_lt
              (A := ρ) (B := 1 - ρ) (s := α + 1) (t := β + 1) (c := c)
              hc (by linarith) hB using 2
          rw [hidx_eq]
          ring
        · subst β
          have hα_lt_two : -α - 1 < 2 := by
            by_contra hnot
            have hα_ge_two : 2 ≤ -α - 1 := not_lt.mp hnot
            rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
              exercise1624StableIndex_eq, max_self, min_eq_left hα_ge_two] at hidx_lt_two
            linarith
          have hidx_eq : exercise1624CaseIStableIndex ρ α α = -α - 1 := by
            rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
              exercise1624StableIndex_eq, max_self, min_eq_right (le_of_lt hα_lt_two)]
          have hEventuallyEq :
              (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
                fun x : ℝ ↦ (c * x) ^ (α + 1) / x ^ (α + 1) := by
            filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
            have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
            have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
            have hcx1 : 1 ≤ c * x := by
              have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
              have hc_ne : c ≠ 0 := ne_of_gt hc
              have hone : 1 < c * x := by
                simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
              exact le_of_lt hone
            -- Proof comment: equal exponents collapse the two-sided tail to one power because the
            -- two coefficients add to `1`.
            calc
              absTail μ (c * x) / absTail μ x
                  = (ρ * (c * x) ^ (α + 1) + (1 - ρ) * (c * x) ^ (α + 1)) /
                      (ρ * x ^ (α + 1) + (1 - ρ) * x ^ (α + 1)) := by
                        rw [exercise1624CaseIAbsTail_eq hρ hα hα hcx1 hμ,
                          exercise1624CaseIAbsTail_eq hρ hα hα hx1 hμ]
              _ = (c * x) ^ (α + 1) / x ^ (α + 1) := by ring_nf
          refine Tendsto.congr' hEventuallyEq.symm ?_
          convert exercise1624_singlePowerTail_ratio_tendsto (c := c) (s := α + 1) hc using 2
          rw [hidx_eq]
          ring
        · have hα_lt_two : -α - 1 < 2 := by
            by_contra hnot
            have hα_ge_two : 2 ≤ -α - 1 := not_lt.mp hnot
            rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
              exercise1624StableIndex_eq, max_eq_left (le_of_lt hgt), min_eq_left hα_ge_two] at hidx_lt_two
            linarith
          have hidx_eq : exercise1624CaseIStableIndex ρ α β = -α - 1 := by
            rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
              exercise1624StableIndex_eq, max_eq_left (le_of_lt hgt),
              min_eq_right (le_of_lt hα_lt_two)]
          have hB : ρ ≠ 0 := hρ0
          have hEventuallyEq :
              (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
                (fun x : ℝ ↦
                  ((1 - ρ) * (c * x) ^ (β + 1) + ρ * (c * x) ^ (α + 1)) /
                    ((1 - ρ) * x ^ (β + 1) + ρ * x ^ (α + 1))) := by
            filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
            have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
            have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
            have hcx1 : 1 ≤ c * x := by
              have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
              have hc_ne : c ≠ 0 := ne_of_gt hc
              have hone : 1 < c * x := by
                simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
              exact le_of_lt hone
            -- Proof comment: this is the symmetric mixed branch where the left-tail exponent is
            -- the dominant one, so we only swap the summand order before applying the same owner
            -- lemma.
            rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
              exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ]
            ring
          refine Tendsto.congr' hEventuallyEq.symm ?_
          convert
            exercise1624_twoPowerTail_ratio_tendsto_of_lt
              (A := 1 - ρ) (B := ρ) (s := β + 1) (t := α + 1) (c := c)
              hc (by linarith) hB using 2
          rw [hidx_eq]
          ring
  · by_cases hρ0 : ρ = 0
    · refine ⟨1, ?_⟩
      have hEventuallyEq :
          (fun x : ℝ ↦ rightTail μ x / absTail μ x) =ᶠ[atTop]
            fun _ : ℝ ↦ 1 := by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
        have hx1 : 1 ≤ x := le_of_lt hx
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
        have hpow_ne : x ^ (β + 1) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
        -- Proof comment: in the pure right-tail case, `rightTail` and `absTail` are identical
        -- beyond `1`.
        rw [exercise1624CaseIRightTail_eq hρ hα hβ hx1 hμ,
          exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ, hρ0]
        simp [hpow_ne]
      refine Tendsto.congr' hEventuallyEq.symm ?_
      simpa using tendsto_const_nhds
    · by_cases hρ1 : ρ = 1
      · refine ⟨0, ?_⟩
        have hEventuallyEq :
            (fun x : ℝ ↦ rightTail μ x / absTail μ x) =ᶠ[atTop]
              fun _ : ℝ ↦ 0 := by
          filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
          have hx1 : 1 ≤ x := le_of_lt hx
          -- Proof comment: in the pure left-tail case, the right tail vanishes exactly beyond `1`.
          rw [exercise1624CaseIRightTail_eq hρ hα hβ hx1 hμ,
            exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ, hρ1]
          norm_num
        refine Tendsto.congr' hEventuallyEq.symm ?_
        simpa using tendsto_const_nhds
      · rcases lt_trichotomy α β with hlt | hEq | hgt
        · refine ⟨1, ?_⟩
          have hB : 1 - ρ ≠ 0 := sub_ne_zero.mpr (by simpa [eq_comm] using hρ1)
          have hEventuallyEq :
              (fun x : ℝ ↦ rightTail μ x / absTail μ x) =ᶠ[atTop]
                (fun x : ℝ ↦
                  (1 - ρ) * x ^ (β + 1) /
                    (ρ * x ^ (α + 1) + (1 - ρ) * x ^ (β + 1))) := by
            filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
            have hx1 : 1 ≤ x := le_of_lt hx
            -- Proof comment: once `x ≥ 1`, the positive-tail share is the explicit ratio of the
            -- right-hand power tail against the full two-sided tail.
            rw [exercise1624CaseIRightTail_eq hρ hα hβ hx1 hμ,
              exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ]
          refine Tendsto.congr' hEventuallyEq.symm ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            exercise1624_dominantPowerTail_share_tendsto_one
              (A := ρ) (B := 1 - ρ) (s := α + 1) (t := β + 1) (by linarith) hB
        · subst β
          refine ⟨1 - ρ, ?_⟩
          have hEventuallyEq :
              (fun x : ℝ ↦ rightTail μ x / absTail μ x) =ᶠ[atTop]
                fun _ : ℝ ↦ 1 - ρ := by
            filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
            have hx1 : 1 ≤ x := le_of_lt hx
            have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
            have hpow_ne : x ^ (α + 1) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
            -- Proof comment: equal exponents make the share ratio constant because the common
            -- power cancels exactly.
            rw [exercise1624CaseIRightTail_eq hρ hα hα hx1 hμ,
              exercise1624CaseIAbsTail_eq hρ hα hα hx1 hμ]
            field_simp [hpow_ne]
            ring
          refine Tendsto.congr' hEventuallyEq.symm ?_
          simpa using tendsto_const_nhds
        · refine ⟨0, ?_⟩
          have hB : ρ ≠ 0 := hρ0
          have hdom :
              Tendsto
                (fun x : ℝ ↦
                  ρ * x ^ (α + 1) /
                    ((1 - ρ) * x ^ (β + 1) + ρ * x ^ (α + 1)))
                atTop
                (𝓝 1) := by
            simpa [add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
              exercise1624_dominantPowerTail_share_tendsto_one
                (A := 1 - ρ) (B := ρ) (s := β + 1) (t := α + 1) (by linarith) hB
          have hEventuallyEq :
              (fun x : ℝ ↦ rightTail μ x / absTail μ x) =ᶠ[atTop]
                (fun x : ℝ ↦
                  1 -
                    ρ * x ^ (α + 1) /
                      ((1 - ρ) * x ^ (β + 1) + ρ * x ^ (α + 1))) := by
            filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
            have hx1 : 1 ≤ x := le_of_lt hx
            have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
            have hρ_pos : 0 < ρ := lt_of_le_of_ne hρ.1 (by simpa [eq_comm] using hρ0)
            have hOneSub_pos : 0 < 1 - ρ := by
              refine sub_pos.mpr (lt_of_le_of_ne hρ.2 ?_)
              simpa [eq_comm] using hρ1
            have hden_pos :
                0 < (1 - ρ) * x ^ (β + 1) + ρ * x ^ (α + 1) := by
              refine add_pos ?_ ?_
              · exact mul_pos hOneSub_pos (Real.rpow_pos_of_pos hx0 _)
              · exact mul_pos hρ_pos (Real.rpow_pos_of_pos hx0 _)
            have hden_ne :
                (1 - ρ) * x ^ (β + 1) + ρ * x ^ (α + 1) ≠ 0 := ne_of_gt hden_pos
            -- Proof comment: when the left tail dominates, the right-tail share is one minus the
            -- dominant left-tail share.
            rw [exercise1624CaseIRightTail_eq hρ hα hβ hx1 hμ,
              exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ]
            field_simp [hden_ne]
            ring_nf
          refine Tendsto.congr' hEventuallyEq.symm ?_
          simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hdom

/-- Helper for Exercise 16.2.4: in the exact case-(i) Gaussian boundary, where the active
surviving tail is exactly `x⁻²`, the chapter tail criterion `(16.29)` holds with index `2`. -/
lemma exercise1624CaseIExactBoundaryTailCriterion
    {μ : ProbabilityMeasure ℝ} {ρ α β : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1)
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun x ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β x)))
    (hboundary :
      (ρ = 0 ∧ β = -3) ∨
        (ρ = 1 ∧ α = -3) ∨
          (ρ ≠ 0 ∧ ρ ≠ 1 ∧ max α β = -3)) :
    TailCriterion16_29 μ 2 := by
  intro c hc
  rcases hboundary with hRight | hLeft | hMixed
  · rcases hRight with ⟨hρ0, hβeq⟩
    have hEventuallyEq :
        (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
          fun x : ℝ ↦ (c * x) ^ (-2 : ℝ) / x ^ (-2 : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
      have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
      have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
      have hcx1 : 1 ≤ c * x := by
        have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
        have hc_ne : c ≠ 0 := ne_of_gt hc
        have hone : 1 < c * x := by
          simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
        exact le_of_lt hone
      -- Proof comment: in the pure right-tail boundary case the exact absolute tail is exactly
      -- `x⁻²`, so the required ratio is the single-power scaling ratio.
      calc
        absTail μ (c * x) / absTail μ x
            = (0 * (c * x) ^ (α + 1) + (1 - 0) * (c * x) ^ ((-3 : ℝ) + 1)) /
                (0 * x ^ (α + 1) + (1 - 0) * x ^ ((-3 : ℝ) + 1)) := by
                  rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
                    exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ, hρ0, hβeq]
        _ = (c * x) ^ (-2 : ℝ) / x ^ (-2 : ℝ) := by norm_num
    refine Tendsto.congr' hEventuallyEq.symm ?_
    simpa using exercise1624_singlePowerTail_ratio_tendsto (s := (-2 : ℝ)) hc
  · rcases hLeft with ⟨hρ1, hαeq⟩
    have hEventuallyEq :
        (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
          fun x : ℝ ↦ (c * x) ^ (-2 : ℝ) / x ^ (-2 : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
      have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
      have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
      have hcx1 : 1 ≤ c * x := by
        have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
        have hc_ne : c ≠ 0 := ne_of_gt hc
        have hone : 1 < c * x := by
          simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
        exact le_of_lt hone
      -- Proof comment: the pure left-tail boundary case has the same exact `x⁻²` tail after the
      -- left/right decomposition is collapsed.
      calc
        absTail μ (c * x) / absTail μ x
            = (1 * (c * x) ^ ((-3 : ℝ) + 1) + (1 - 1) * (c * x) ^ (β + 1)) /
                (1 * x ^ ((-3 : ℝ) + 1) + (1 - 1) * x ^ (β + 1)) := by
                  rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
                    exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ, hρ1, hαeq]
        _ = (c * x) ^ (-2 : ℝ) / x ^ (-2 : ℝ) := by norm_num
    refine Tendsto.congr' hEventuallyEq.symm ?_
    simpa using exercise1624_singlePowerTail_ratio_tendsto (s := (-2 : ℝ)) hc
  · rcases hMixed with ⟨hρ_ne_zero, hρ_ne_one, hmax⟩
    rcases lt_trichotomy α β with hlt | rfl | hgt
    · have hβeq : β = -3 := by
        simpa [max_eq_right (le_of_lt hlt)] using hmax
      have hB : 1 - ρ ≠ 0 := sub_ne_zero.mpr hρ_ne_one.symm
      have hcLimit : c ^ (β + 1) = (c ^ 2)⁻¹ := by
        calc
          c ^ (β + 1) = c ^ (-2 : ℝ) := by rw [hβeq]; norm_num
          _ = c ^ (-2 : ℤ) := by simp
          _ = (c ^ 2)⁻¹ := by
            rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      have hEventuallyEq :
          (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
            (fun x : ℝ ↦
              (ρ * (c * x) ^ (α + 1) + (1 - ρ) * (c * x) ^ (β + 1)) /
                (ρ * x ^ (α + 1) + (1 - ρ) * x ^ (β + 1))) := by
        filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
        have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
        have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
        have hcx1 : 1 ≤ c * x := by
          have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
          have hc_ne : c ≠ 0 := ne_of_gt hc
          have hone : 1 < c * x := by
            simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
          exact le_of_lt hone
        -- Proof comment: once both thresholds exceed `1`, the exact two-power tail formula is
        -- available simultaneously at `x` and at `c * x`.
        rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
          exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ]
      refine Tendsto.congr' hEventuallyEq.symm ?_
      simpa [hcLimit] using
        exercise1624_twoPowerTail_ratio_tendsto_of_lt
          (A := ρ) (B := 1 - ρ) (s := α + 1) (t := β + 1) (c := c)
          hc (by linarith) hB
    · have hαeq : α = -3 := by
        simpa using hmax
      have hEventuallyEq :
          (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
            fun x : ℝ ↦ (c * x) ^ (-2 : ℝ) / x ^ (-2 : ℝ) := by
        filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
        have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
        have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
        have hcx1 : 1 ≤ c * x := by
          have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
          have hc_ne : c ≠ 0 := ne_of_gt hc
          have hone : 1 < c * x := by
            simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
          exact le_of_lt hone
        -- Proof comment: when both exponents are `-3`, the two coefficients add to `1`, so the
        -- absolute tail again collapses to the single power `x⁻²`.
        calc
          absTail μ (c * x) / absTail μ x
              = (ρ * (c * x) ^ ((-3 : ℝ) + 1) + (1 - ρ) * (c * x) ^ ((-3 : ℝ) + 1)) /
                  (ρ * x ^ ((-3 : ℝ) + 1) + (1 - ρ) * x ^ ((-3 : ℝ) + 1)) := by
                    rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
                      exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ, hαeq]
          _ = (c * x) ^ (-2 : ℝ) / x ^ (-2 : ℝ) := by ring_nf
      refine Tendsto.congr' hEventuallyEq.symm ?_
      simpa using exercise1624_singlePowerTail_ratio_tendsto (s := (-2 : ℝ)) hc
    · have hαeq : α = -3 := by
        simpa [max_eq_left (le_of_lt hgt)] using hmax
      have hB : ρ ≠ 0 := hρ_ne_zero
      have hcLimit : c ^ (α + 1) = (c ^ 2)⁻¹ := by
        calc
          c ^ (α + 1) = c ^ (-2 : ℝ) := by rw [hαeq]; norm_num
          _ = c ^ (-2 : ℤ) := by simp
          _ = (c ^ 2)⁻¹ := by
            rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      have hEventuallyEq :
          (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) =ᶠ[atTop]
            (fun x : ℝ ↦
              ((1 - ρ) * (c * x) ^ (β + 1) + ρ * (c * x) ^ (α + 1)) /
                ((1 - ρ) * x ^ (β + 1) + ρ * x ^ (α + 1))) := by
        filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / c))] with x hx
        have hx1 : 1 ≤ x := le_of_lt <| lt_of_le_of_lt (le_max_left _ _) hx
        have hxdiv : 1 / c < x := lt_of_le_of_lt (le_max_right _ _) hx
        have hcx1 : 1 ≤ c * x := by
          have hcx : c * (1 / c) < c * x := mul_lt_mul_of_pos_left hxdiv hc
          have hc_ne : c ≠ 0 := ne_of_gt hc
          have hone : 1 < c * x := by
            simpa [one_div, hc_ne, mul_assoc, mul_comm, mul_left_comm] using hcx
          exact le_of_lt hone
        -- Proof comment: this is the symmetric mixed case where the left-tail exponent `α + 1`
        -- is the dominant surviving `-2` exponent.
        rw [exercise1624CaseIAbsTail_eq hρ hα hβ hcx1 hμ,
          exercise1624CaseIAbsTail_eq hρ hα hβ hx1 hμ]
        ring
      refine Tendsto.congr' hEventuallyEq.symm ?_
      simpa [hcLimit] using
        exercise1624_twoPowerTail_ratio_tendsto_of_lt
          (A := 1 - ρ) (B := ρ) (s := β + 1) (t := α + 1) (c := c)
          hc (by linarith) hB

/-- Helper for Exercise 16.2.4: in the strict case-(i) Gaussian branch, every active tail
exponent lies below `-3`, so the source law has finite second moment. -/
lemma stableWithIndexTwo_ofTailCriterionTwo
    {μ : ProbabilityMeasure ℝ}
    (hμ_nontrivial : ∀ x : ℝ, μ ≠ diracProba x)
    (hTail : TailCriterion16_29 μ 2) :
    ∃ ν : ProbabilityMeasure ℝ, μ ∈ domainOfAttraction ν ∧ IsStableInBroadSenseWithIndex ν 2 := by
  sorry

/-- Helper for Exercise 16.2.4: in the strict case-(i) Gaussian branch, every active tail
exponent lies below `-3`, so the source law has finite second moment. -/
lemma exercise1624CaseIFiniteSecondMomentOfStrictGaussianBranch
    {μ : ProbabilityMeasure ℝ} {ρ α β : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1)
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun x ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β x)))
    (hβ_strict : ρ ≠ 1 → β < -3)
    (hα_strict : ρ ≠ 0 → α < -3) :
    MemLp id 2 (μ : Measure ℝ) := by
  let leftKernel : ℝ → ℝ :=
    Set.indicator (Set.Iio (-1)) (fun x ↦ (ρ * (-(1 + α))) * (-x) ^ (α + 2))
  let rightKernel : ℝ → ℝ :=
    Set.indicator (Set.Ioi 1) (fun x ↦ ((1 - ρ) * (-(1 + β))) * x ^ (β + 2))
  have hleftInt : Integrable leftKernel volume := by
    by_cases hρ0 : ρ = 0
    · -- Proof comment: if the left coefficient vanishes, the negative-ray contribution is zero.
      have hzero : Integrable (fun _ : ℝ ↦ (0 : ℝ)) volume := by
        simpa using (integrable_zero volume : Integrable (fun _ : ℝ ↦ (0 : ℝ)) volume)
      refine hzero.congr ?_
      filter_upwards with x
      simp [leftKernel, hρ0]
    · have hα_tail : α + 2 < -1 := by
        have hα_strict' := hα_strict hρ0
        linarith
      have hbaseOn :
          IntegrableOn (fun x : ℝ ↦ (ρ * (-(1 + α))) * x ^ (α + 2)) (Set.Ioi 1) volume := by
        -- Proof comment: after replacing `x < -1` by the positive variable `-x`, the left tail is
        -- just a scalar multiple of an integrable `rpow` kernel.
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (integrableOn_Ioi_rpow_of_lt hα_tail zero_lt_one).const_mul (ρ * (-(1 + α)))
      have hbaseInt :
          Integrable (Set.indicator (Set.Ioi 1) (fun x : ℝ ↦ (ρ * (-(1 + α))) * x ^ (α + 2)))
            volume :=
        hbaseOn.integrable_indicator measurableSet_Ioi
      have hleftEq :
          leftKernel =
            fun x : ℝ ↦
              Set.indicator (Set.Ioi 1) (fun t : ℝ ↦ (ρ * (-(1 + α))) * t ^ (α + 2)) (-x) := by
        funext x
        by_cases hx : x < -1
        · have hneg : 1 < -x := by linarith
          simp [leftKernel, hx, hneg]
        · have hneg : ¬ 1 < -x := by linarith
          simp [leftKernel, hx, hneg]
      simpa [hleftEq] using hbaseInt.comp_neg
  have hrightInt : Integrable rightKernel volume := by
    by_cases hρ1 : ρ = 1
    · -- Proof comment: if the right coefficient vanishes, the positive-ray contribution is zero.
      have hzero : Integrable (fun _ : ℝ ↦ (0 : ℝ)) volume := by
        simpa using (integrable_zero volume : Integrable (fun _ : ℝ ↦ (0 : ℝ)) volume)
      refine hzero.congr ?_
      filter_upwards with x
      simp [rightKernel, hρ1]
    · have hβ_tail : β + 2 < -1 := by
        have hβ_strict' := hβ_strict hρ1
        linarith
      have hbaseOn :
          IntegrableOn (fun x : ℝ ↦ ((1 - ρ) * (-(1 + β))) * x ^ (β + 2)) (Set.Ioi 1) volume := by
        -- Proof comment: the positive tail is already written on `Ioi 1`, so the same `rpow`
        -- integrability owner applies directly.
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (integrableOn_Ioi_rpow_of_lt hβ_tail zero_lt_one).const_mul ((1 - ρ) * (-(1 + β)))
      exact hbaseOn.integrable_indicator measurableSet_Ioi
  have hkernelEq :
      (fun x : ℝ ↦ x ^ (2 : ℕ) * exercise1624CaseIDensity ρ α β x) =ᵐ[volume]
        fun x : ℝ ↦ leftKernel x + rightKernel x := by
    filter_upwards with x
    by_cases hxneg : x < -1
    · have hnotPos : ¬ 1 < x := by linarith
      have habs : |x| = -x := abs_of_neg (by linarith)
      have hneg : 0 < -x := by linarith
      -- Proof comment: on the negative ray, only the left tail survives and its second-moment
      -- density becomes the shifted `rpow` kernel stored in `leftKernel`.
      rw [exercise1624CaseIDensity_eq, if_pos hxneg]
      calc
        x ^ (2 : ℕ) * (ρ * (-(1 + α)) * |x| ^ α)
            = (ρ * (-(1 + α))) * ((-x) ^ (2 : ℕ) * (-x) ^ α) := by
                rw [habs, show x ^ (2 : ℕ) = (-x) ^ (2 : ℕ) by ring]
                ring
        _ = (ρ * (-(1 + α))) * ((-x) ^ (2 : ℝ) * (-x) ^ α) := by
              rw [show (-x) ^ (2 : ℕ) = (-x) ^ (2 : ℝ) by
                simpa using (Real.rpow_natCast (-x) 2).symm]
        _ = (ρ * (-(1 + α))) * (-x) ^ (α + 2) := by
              congr 1
              calc
                (-x) ^ (2 : ℝ) * (-x) ^ α = (-x) ^ α * (-x) ^ (2 : ℝ) := by ring
                _ = (-x) ^ (α + 2) := by rw [← Real.rpow_add hneg α 2]
        _ = leftKernel x + rightKernel x := by simp [leftKernel, rightKernel, hxneg, hnotPos]
    · by_cases hxpos : 1 < x
      · have hx0 : 0 < x := lt_trans zero_lt_one hxpos
        have hnotNeg : ¬ x < -1 := hxneg
      -- Proof comment: on the positive ray, only the right tail survives and its second-moment
      -- density is exactly the `rightKernel` owner.
        rw [exercise1624CaseIDensity_eq, if_neg hnotNeg, if_pos hxpos]
        calc
          x ^ (2 : ℕ) * ((1 - ρ) * (-(1 + β)) * x ^ β)
              = ((1 - ρ) * (-(1 + β))) * (x ^ (2 : ℕ) * x ^ β) := by ring
          _ = ((1 - ρ) * (-(1 + β))) * (x ^ (2 : ℝ) * x ^ β) := by
                rw [show x ^ (2 : ℕ) = x ^ (2 : ℝ) by
                  simpa using (Real.rpow_natCast x 2).symm]
          _ = ((1 - ρ) * (-(1 + β))) * x ^ (β + 2) := by
                congr 1
                calc
                  x ^ (2 : ℝ) * x ^ β = x ^ β * x ^ (2 : ℝ) := by ring
                  _ = x ^ (β + 2) := by rw [← Real.rpow_add hx0 β 2]
          _ = leftKernel x + rightKernel x := by simp [leftKernel, rightKernel, hxneg, hxpos]
      · -- Proof comment: between `-1` and `1`, the source density vanishes, so both kernel owners
        -- are zero as well.
        rw [exercise1624CaseIDensity_eq, if_neg hxneg, if_neg hxpos]
        simp [leftKernel, rightKernel, hxneg, hxpos]
  have hDensityMeas : Measurable (exercise1624CaseIDensity ρ α β) := by
    -- Proof comment: the density is the same measurable nested `if` used in the explicit tail
    -- calculations above.
    have hLeft : Measurable (fun z : ℝ ↦ ρ * (-(1 + α)) * |z| ^ α) := by
      fun_prop
    have hRight : Measurable (fun z : ℝ ↦ (1 - ρ) * (-(1 + β)) * z ^ β) := by
      fun_prop
    unfold exercise1624CaseIDensity
    exact Measurable.ite measurableSet_Iio hLeft
      (Measurable.ite measurableSet_Ioi hRight measurable_const)
  have hkernelInt :
      Integrable (fun x : ℝ ↦ x ^ (2 : ℕ) * exercise1624CaseIDensity ρ α β x) volume :=
    (hleftInt.add hrightInt).congr hkernelEq.symm
  have hweightedSq :
      Integrable
        (fun x : ℝ ↦
          x ^ (2 : ℕ) * (ENNReal.ofReal (exercise1624CaseIDensity ρ α β x)).toReal)
        volume := by
    -- Proof comment: the source density is pointwise nonnegative, so `ENNReal.toReal ∘ ofReal`
    -- returns the same kernel on the base measure.
    refine hkernelInt.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (exercise1624CaseIDensity_nonneg hρ hα hβ x)]
  have hsq :
      Integrable (fun x : ℝ ↦ x ^ (2 : ℕ)) (μ : Measure ℝ) := by
    rw [hμ]
    -- Proof comment: rewrite the integral under `withDensity` back to Lebesgue measure and use the
    -- explicit integrable kernel assembled from the two tails.
    exact
      (integrable_withDensity_iff
        (μ := volume)
        (f := fun x ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β x))
        hDensityMeas.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)
        (g := fun x : ℝ ↦ x ^ (2 : ℕ))).2 hweightedSq
  exact
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (by simpa using hsq)

/-- Case (i) of Exercise 16.2.4: if `μ` is exactly the source distribution on `ℝ` with density
`exercise1624CaseIDensity ρ α β`, then `μ` lies in the domain of attraction of a stable law with
index determined by the tails whose coefficients are nonzero. -/
theorem stableDomainOfAttractionExamples_i
    {μ : ProbabilityMeasure ℝ} {ρ α β : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α < -1) (hβ : β < -1)
    (hμ :
      (μ : Measure ℝ) =
        volume.withDensity
          (fun x ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β x))) :
    IsInDomainOfAttractionOfStableWithIndex μ (exercise1624CaseIStableIndex ρ α β) := by
  by_cases hidx_lt_two : exercise1624CaseIStableIndex ρ α β < 2
  · have hidx_pos : 0 < exercise1624CaseIStableIndex ρ α β := by
      by_cases hρ0 : ρ = 0
      · rw [exercise1624CaseIStableIndex_eq, if_pos hρ0]
        have hβ_pos : 0 < -β - 1 := by linarith
        exact lt_min zero_lt_two hβ_pos
      · by_cases hρ1 : ρ = 1
        · rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_pos hρ1]
          have hα_pos : 0 < -α - 1 := by linarith
          exact lt_min zero_lt_two hα_pos
        · rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
            exercise1624StableIndex_eq]
          have hmax : max α β < -1 := max_lt_iff.mpr ⟨hα, hβ⟩
          have hidx_raw_pos : 0 < -max α β - 1 := by linarith
          exact lt_min zero_lt_two hidx_raw_pos
    have hidx_mem : exercise1624CaseIStableIndex ρ α β ∈ Set.Ioo (0 : ℝ) 2 :=
      ⟨hidx_pos, hidx_lt_two⟩
    have hCriteria :=
      exercise1624CaseIHeavyTailCriteria hρ hα hβ hμ hidx_lt_two
    rcases stableDomainOfAttractionCriterion μ with ⟨_, _, hPartIII⟩
    unfold StableDomainOfAttractionCriterionPartIII at hPartIII
    have hPartIIIAtIndex :
        IsInDomainOfAttractionOfStableWithIndex μ (exercise1624CaseIStableIndex ρ α β) ↔
          TailCriterion16_29 μ (exercise1624CaseIStableIndex ρ α β) ∧
            PositiveTailShareCriterion16_30 μ := by
      apply hPartIII
      exact hidx_mem
    rcases hPartIIIAtIndex.2 hCriteria with
      ⟨ν, hμν, hνidx⟩
    exact ⟨ν, hμν, hνidx⟩
  · have hidx_eq_two : exercise1624CaseIStableIndex ρ α β = 2 := by
      exact le_antisymm (exercise1624CaseIStableIndex_le_two ρ α β) (le_of_not_gt hidx_lt_two)
    by_cases hboundary :
        (ρ = 0 ∧ β = -3) ∨
          (ρ = 1 ∧ α = -3) ∨
            (ρ ≠ 0 ∧ ρ ≠ 1 ∧ max α β = -3)
    · -- Proof comment: the exact `-3` boundary still satisfies the Gaussian tail criterion, so
      -- the theorem body now delegates to the dedicated Gaussian converse bridge at index `2`.
      have hTail :
          TailCriterion16_29 μ 2 :=
        exercise1624CaseIExactBoundaryTailCriterion hρ hα hβ hμ hboundary
      have hNotDirac : ∀ x : ℝ, μ ≠ diracProba x :=
        exercise1624CaseINotDirac hμ
      rcases stableWithIndexTwo_ofTailCriterionTwo hNotDirac hTail with ⟨ν, hμν, hνtwo⟩
      simpa [hidx_eq_two] using ⟨ν, hμν, hνtwo⟩
    · -- Route correction: the strict Gaussian branch is better handled through finite second
      -- moments and the CLT-based Gaussian attraction bridge, not by forcing the boundary
      -- tail-ratio owner beyond its natural `-3` scope.
      have hβ_strict : ρ ≠ 1 → β < -3 := by
        intro hρ1
        by_cases hρ0 : ρ = 0
        · have hβ_le : β ≤ -3 := by
            by_contra hβ_gt
            have hβ_lt : -β - 1 < 2 := by linarith
            rw [exercise1624CaseIStableIndex_eq, if_pos hρ0,
              min_eq_right (le_of_lt hβ_lt)] at hidx_eq_two
            linarith
          have hβ_ne : β ≠ -3 := by
            intro hβeq
            exact hboundary (Or.inl ⟨hρ0, hβeq⟩)
          exact lt_of_le_of_ne hβ_le hβ_ne
        · have hmax_lt : max α β < -3 := by
            have hmax_le : max α β ≤ -3 := by
              by_contra hmax_gt
              have hmax_lt_two : -max α β - 1 < 2 := by linarith
              rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
                exercise1624StableIndex_eq, min_eq_right (le_of_lt hmax_lt_two)] at hidx_eq_two
              linarith
            have hmax_ne : max α β ≠ -3 := by
              intro hmaxeq
              exact hboundary (Or.inr (Or.inr ⟨hρ0, hρ1, hmaxeq⟩))
            exact lt_of_le_of_ne hmax_le hmax_ne
          exact lt_of_le_of_lt (le_max_right α β) hmax_lt
      have hα_strict : ρ ≠ 0 → α < -3 := by
        intro hρ0
        by_cases hρ1 : ρ = 1
        · have hα_le : α ≤ -3 := by
            by_contra hα_gt
            have hα_lt_two : -α - 1 < 2 := by linarith
            rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_pos hρ1,
              min_eq_right (le_of_lt hα_lt_two)] at hidx_eq_two
            linarith
          have hα_ne : α ≠ -3 := by
            intro hαeq
            exact hboundary (Or.inr (Or.inl ⟨hρ1, hαeq⟩))
          exact lt_of_le_of_ne hα_le hα_ne
        · have hmax_lt : max α β < -3 := by
            have hmax_le : max α β ≤ -3 := by
              by_contra hmax_gt
              have hmax_lt_two : -max α β - 1 < 2 := by linarith
              rw [exercise1624CaseIStableIndex_eq, if_neg hρ0, if_neg hρ1,
                exercise1624StableIndex_eq, min_eq_right (le_of_lt hmax_lt_two)] at hidx_eq_two
              linarith
            have hmax_ne : max α β ≠ -3 := by
              intro hmaxeq
              exact hboundary (Or.inr (Or.inr ⟨hρ0, hρ1, hmaxeq⟩))
            exact lt_of_le_of_ne hmax_le hmax_ne
          exact lt_of_le_of_lt (le_max_left α β) hmax_lt
      have hμ₂ : MemLp id 2 (μ : Measure ℝ) :=
        exercise1624CaseIFiniteSecondMomentOfStrictGaussianBranch hρ hα hβ hμ hβ_strict hα_strict
      have hVar : Var[id; (μ : Measure ℝ)] ≠ 0 :=
        exercise1624VarianceNeZeroOfNotDirac hμ₂ (exercise1624CaseINotDirac hμ)
      simpa [hidx_eq_two] using
        exercise1624GaussianAttractionOfFiniteVarianceLaw (μ := μ) hμ₂ hVar

/-- Case (ii) of Exercise 16.2.4: the exponential distribution belongs to the Gaussian
(`α = 2`) domain of attraction. -/
-- TODO: realize iid exponential copies and transport the Chapter 15 standardized-sum CLT to a
-- Gaussian attracting witness for `exercise1624ExponentialLaw`.
theorem stableDomainOfAttractionExamples_ii
    (θ : ℝ) (hθ : 0 < θ) :
    IsInDomainOfAttractionOfStableWithIndex (exercise1624ExponentialLaw θ hθ) 2 := by
  -- Proof comment: route the exponential law through the reusable finite-variance Gaussian
  -- attraction bridge instead of a tail-criterion argument.
  refine exercise1624GaussianAttractionOfFiniteVarianceLaw ?_ ?_
  · simpa [exercise1624ExponentialLaw_toMeasure] using memLp_two_id_expMeasure hθ
  · have hVarFormula := (expMeasure_mean_variance θ hθ).2
    rw [exercise1624ExponentialLaw_toMeasure, hVarFormula]
    positivity

/-- Helper for Exercise 16.2.4: once the case-(iii) law is supported on positive integers, the
two-sided tail agrees with the right tail at every threshold. -/
lemma exercise1624CaseIIIAbsTail_eq_rightTail
    {μ : ProbabilityMeasure ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    {x : ℝ} :
    absTail μ x = rightTail μ x := by
  let S : Set ℝ := Set.range fun n : ℕ+ ↦ (n : ℝ)
  let A : Set ℝ := {y : ℝ | x ≤ |y|}
  let B : Set ℝ := Set.Ici x
  have hScompl_zero : (μ : Measure ℝ) Sᶜ = 0 := by
    have hzero := hsupport
    rw [ENNReal.toReal_eq_zero_iff] at hzero
    rcases hzero with hzero | htop
    · simpa [S] using hzero
    · exact (measure_ne_top (μ : Measure ℝ) Sᶜ htop).elim
  have hA_diff_zero : (μ : Measure ℝ) (A \ B) = 0 := by
    refine measure_mono_null ?_ hScompl_zero
    intro y hy
    by_contra hyS
    have hyS' : y ∈ S := by
      simpa [S] using hyS
    rcases hyS' with ⟨n, rfl⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast n.pos
    have hyB : (n : ℝ) ∉ Set.Ici x := hy.2
    have hyA : x ≤ |(n : ℝ)| := hy.1
    have hxn : (n : ℝ) ∈ Set.Ici x := by
      simpa [Set.mem_Ici, abs_of_pos hn_pos] using hyA
    exact hyB hxn
  have hB_diff_zero : (μ : Measure ℝ) (B \ A) = 0 := by
    refine measure_mono_null ?_ hScompl_zero
    intro y hy
    by_contra hyS
    have hyS' : y ∈ S := by
      simpa [S] using hyS
    rcases hyS' with ⟨n, rfl⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast n.pos
    have hyA : (n : ℝ) ∉ A := hy.2
    have hyB : (n : ℝ) ∈ Set.Ici x := hy.1
    have hxabs : x ≤ |(n : ℝ)| := by
      simpa [Set.mem_Ici, abs_of_pos hn_pos] using hyB
    exact hyA hxabs
  have hA_diff_eq : A \ (A ∩ B) = A \ B := by
    ext y
    simp [A, B]
  have hB_diff_eq : B \ (A ∩ B) = B \ A := by
    ext y
    simp [A, B]
  have hA_inter :
      (μ : Measure ℝ) (A ∩ B) = (μ : Measure ℝ) A := by
    -- Proof comment: outside the positive-integer support, the part of `A` missing from `B` has
    -- zero mass, so intersecting with `B` preserves the measure of `A`.
    have hdiff_zero : (μ : Measure ℝ) (A \ (A ∩ B)) = 0 := by
      simpa [hA_diff_eq] using hA_diff_zero
    exact measure_eq_measure_of_null_diff Set.inter_subset_left hdiff_zero
  have hB_inter :
      (μ : Measure ℝ) (A ∩ B) = (μ : Measure ℝ) B := by
    -- Proof comment: the symmetric argument shows that intersecting `B` with `A` loses only a
    -- null subset of the support complement.
    have hdiff_zero : (μ : Measure ℝ) (B \ (A ∩ B)) = 0 := by
      simpa [hB_diff_eq] using hB_diff_zero
    exact measure_eq_measure_of_null_diff Set.inter_subset_right hdiff_zero
  -- Proof comment: after identifying both events up to a null subset of the support complement,
  -- the tails are literally the same measure and hence have the same real value.
  unfold absTail rightTail
  exact congrArg ENNReal.toReal <|
    calc
      (μ : Measure ℝ) A = (μ : Measure ℝ) (A ∩ B) := hA_inter.symm
      _ = (μ : Measure ℝ) B := hB_inter

/-- Helper for Exercise 16.2.4: the positive-integer support in case (iii) is the disjoint
countable union of its singleton fibers. -/
lemma exercise1624CaseIIIRange_eq_iUnionSingleton :
    (Set.range fun n : ℕ+ ↦ (n : ℝ)) = ⋃ n : ℕ+, ({(n : ℝ)} : Set ℝ) := by
  -- Proof comment: every point in the range is, by definition, one of the singleton fibers, and
  -- conversely every singleton fiber sits inside the range.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨n, rfl⟩
    exact Set.mem_iUnion.2 ⟨n, by simp⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
    exact ⟨n, by simpa using hn.symm⟩

/-- Helper for Exercise 16.2.4: the normalization constant in case (iii) is strictly positive once
the singleton masses really define a probability law supported on `ℕ+`. -/
lemma exercise1624CaseIIINormalizationConstant_pos
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    0 < exercise1624CaseIIINormalizationConstant α β := by
  let S : Set ℝ := Set.range fun n : ℕ+ ↦ (n : ℝ)
  have hScompl_zero : (μ : Measure ℝ) Sᶜ = 0 := by
    rw [ENNReal.toReal_eq_zero_iff] at hsupport
    rcases hsupport with hzero | htop
    · simpa [S] using hzero
    · exact (measure_ne_top (μ : Measure ℝ) Sᶜ htop).elim
  have hS_meas : MeasurableSet S := by
    simpa [S] using (Set.countable_range fun n : ℕ+ ↦ (n : ℝ)).measurableSet
  have hS_one : (μ : Measure ℝ) S = 1 := by
    have hsum :
        (μ : Measure ℝ) S + (μ : Measure ℝ) Sᶜ = 1 := by
      simpa using measure_add_measure_compl (μ := (μ : Measure ℝ)) hS_meas
    rw [hScompl_zero, add_zero] at hsum
    exact hsum
  have hnonneg : 0 ≤ exercise1624CaseIIINormalizationConstant α β := by
    have hμ1_nonneg :
        0 ≤ ((μ : Measure ℝ) ({((1 : ℕ+) : ℝ)} : Set ℝ)).toReal :=
      ENNReal.toReal_nonneg
    have hmass_one :
        ((μ : Measure ℝ) ({((1 : ℕ+) : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIINormalizationConstant α β := by
      simpa [exercise1624CaseIIISingletonMass_eq] using hmass 1
    rw [hmass_one] at hμ1_nonneg
    simpa using hμ1_nonneg
  have hne :
      exercise1624CaseIIINormalizationConstant α β ≠ 0 := by
    intro hzero
    have hsingleton_zero :
        ∀ n : ℕ+, (μ : Measure ℝ) ({(n : ℝ)} : Set ℝ) = 0 := by
      intro n
      have htoReal :
          ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal = 0 := by
        rw [hmass n, exercise1624CaseIIISingletonMass_eq, hzero]
        split_ifs <;> simp
      rw [ENNReal.toReal_eq_zero_iff] at htoReal
      rcases htoReal with hzero' | htop
      · exact hzero'
      · exact (measure_ne_top (μ : Measure ℝ) ({(n : ℝ)} : Set ℝ) htop).elim
    have hS_zero : (μ : Measure ℝ) S = 0 := by
      calc
        (μ : Measure ℝ) S = (μ : Measure ℝ) (⋃ n : ℕ+, ({(n : ℝ)} : Set ℝ)) := by
          simpa [S] using
            congrArg (fun T : Set ℝ ↦ (μ : Measure ℝ) T)
              exercise1624CaseIIIRange_eq_iUnionSingleton
        _ = ∑' n : ℕ+, (μ : Measure ℝ) ({(n : ℝ)} : Set ℝ) := by
          refine measure_iUnion ?_ fun _ ↦ measurableSet_singleton _
          intro i j hij
          have hij' : (i : ℝ) ≠ (j : ℝ) := by
            exact_mod_cast hij
          simpa [Set.disjoint_singleton] using hij'
        _ = 0 := by
          rw [ENNReal.tsum_eq_zero]
          exact hsingleton_zero
    rw [hS_zero] at hS_one
    exact zero_ne_one hS_one
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Helper for Exercise 16.2.4: every singleton in the positive-integer support of case (iii)
has strictly positive mass. -/
lemma exercise1624CaseIIISingletonMass_pos
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n)
    (n : ℕ+) :
    0 < ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal := by
  have hc :
      0 < exercise1624CaseIIINormalizationConstant α β :=
    exercise1624CaseIIINormalizationConstant_pos hsupport hmass
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  -- Proof comment: once the normalization constant is positive, both the even and odd power-law
  -- singleton formulas are positive because the base `(n : ℝ)` is strictly positive.
  rw [hmass n, exercise1624CaseIIISingletonMass_eq]
  split_ifs with hEven
  · exact mul_pos hc (Real.rpow_pos_of_pos hn_pos _)
  · exact mul_pos hc (Real.rpow_pos_of_pos hn_pos _)

/-- Helper for Exercise 16.2.4: on the positive-integer support from case (iii), the right tail
is exactly the sum of the singleton masses above the threshold. -/
lemma exercise1624CaseIIIRightTail_eq_tsum
    {μ : ProbabilityMeasure ℝ} {α β x : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    rightTail μ x =
      ∑' n : ℕ+,
        if x ≤ (n : ℝ) then exercise1624CaseIIISingletonMass α β n else 0 := by
  let S : Set ℝ := Set.range fun n : ℕ+ ↦ (n : ℝ)
  let tailAtoms : ℕ+ → Set ℝ := fun n ↦
    if x ≤ (n : ℝ) then ({(n : ℝ)} : Set ℝ) else ∅
  have hScompl_zero : (μ : Measure ℝ) Sᶜ = 0 := by
    rw [ENNReal.toReal_eq_zero_iff] at hsupport
    rcases hsupport with hzero | htop
    · simpa [S] using hzero
    · exact (measure_ne_top (μ : Measure ℝ) Sᶜ htop).elim
  have hIci_inter :
      (μ : Measure ℝ) (Set.Ici x ∩ S) = (μ : Measure ℝ) (Set.Ici x) := by
    have hdiff_zero : (μ : Measure ℝ) (Set.Ici x \ (Set.Ici x ∩ S)) = 0 := by
      refine measure_mono_null ?_ hScompl_zero
      intro y hy
      by_contra hyS
      have hyS' : y ∈ S := by
        simpa using hyS
      exact hy.2 ⟨hy.1, hyS'⟩
    -- Proof comment: outside the positive-integer support, the tail event loses only a null set.
    exact measure_eq_measure_of_null_diff Set.inter_subset_left hdiff_zero
  have hTail_eq :
      Set.Ici x ∩ S = ⋃ n : ℕ+, tailAtoms n := by
    ext y
    constructor
    · intro hy
      rcases hy.2 with ⟨n, rfl⟩
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      have hx_le : x ≤ (n : ℝ) := hy.1
      simp [tailAtoms, hx_le]
    · intro hy
      rcases Set.mem_iUnion.1 hy with ⟨n, hn⟩
      by_cases hx_le : x ≤ (n : ℝ)
      · have hy_eq : y = (n : ℝ) := by
          simpa [tailAtoms, hx_le] using hn
        subst hy_eq
        exact ⟨hx_le, ⟨n, rfl⟩⟩
      · simpa [tailAtoms, hx_le] using hn
  have hTail_disj : Pairwise fun i j : ℕ+ ↦ Disjoint (tailAtoms i) (tailAtoms j) := by
    have hSingleton_disj :
        Pairwise fun i j : ℕ+ ↦ Disjoint ({(i : ℝ)} : Set ℝ) ({(j : ℝ)} : Set ℝ) := by
      intro i j hij
      have hij' : (i : ℝ) ≠ (j : ℝ) := by
        exact_mod_cast hij
      simpa [Set.disjoint_singleton] using hij'
    intro i j hij
    by_cases hi : x ≤ (i : ℝ) <;> by_cases hj : x ≤ (j : ℝ)
    · simpa [tailAtoms, hi, hj] using hSingleton_disj hij
    · simp [tailAtoms, hi, hj]
    · simp [tailAtoms, hi, hj]
    · simp [tailAtoms, hi, hj]
  have hTail_meas : ∀ n : ℕ+, MeasurableSet (tailAtoms n) := by
    intro n
    by_cases hx_le : x ≤ (n : ℝ)
    · simp [tailAtoms, hx_le]
    · simp [tailAtoms, hx_le]
  unfold rightTail
  -- Proof comment: after restricting to the positive-integer support, the tail is a disjoint
  -- countable union of singleton atoms, so its mass is the singleton series above `x`.
  calc
    ((μ : Measure ℝ) (Set.Ici x)).toReal = ((μ : Measure ℝ) (Set.Ici x ∩ S)).toReal := by
      rw [hIci_inter]
    _ = ((μ : Measure ℝ) (⋃ n : ℕ+, tailAtoms n)).toReal := by rw [hTail_eq]
    _ = (∑' n : ℕ+, (μ : Measure ℝ) (tailAtoms n)).toReal := by
      rw [measure_iUnion hTail_disj hTail_meas]
    _ = ∑' n : ℕ+, ((μ : Measure ℝ) (tailAtoms n)).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro n
      exact measure_ne_top (μ : Measure ℝ) (tailAtoms n)
    _ = ∑' n : ℕ+, if x ≤ (n : ℝ) then exercise1624CaseIIISingletonMass α β n else 0 := by
      refine tsum_congr fun n ↦ ?_
      by_cases hx_le : x ≤ (n : ℝ)
      · simp [tailAtoms, hx_le, hmass n]
      · simp [tailAtoms, hx_le]

/-- Helper for Exercise 16.2.4: every positive-step arithmetic subsequence of the summable
power tail `n ↦ (n : ℝ) ^ s` remains summable when `s < -1`. -/
lemma exercise1624_summableNatRpowAlongArithmetic
    {s : ℝ} (hs : s < -1) {a b : ℕ} (ha : 0 < a) :
    Summable (fun k : ℕ ↦ ((a * k + b : ℕ) : ℝ) ^ s) := by
  have hBase : Summable (fun n : ℕ ↦ (n : ℝ) ^ s) :=
    (Real.summable_nat_rpow).2 hs
  exact hBase.comp_injective <| by
    intro m n hmn
    apply Nat.eq_of_mul_eq_mul_left ha
    exact Nat.add_right_cancel hmn

/-- Helper for Exercise 16.2.4: after shifting `ℕ` to `ℕ+` via `Nat.succPNat`, the even
subsequence becomes the odd singleton branch and the odd subsequence becomes the even branch. -/
lemma exercise1624CaseIIISingletonMass_succ_evenOdd
    {α β : ℝ} (k : ℕ) :
    exercise1624CaseIIISingletonMass α β (Nat.succPNat (2 * k)) =
      exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ β ∧
    exercise1624CaseIIISingletonMass α β (Nat.succPNat (2 * k + 1)) =
      exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ α := by
  constructor
  · have hodd : ¬ Even (2 * k + 1) := Nat.not_even_two_mul_add_one k
    -- Proof comment: `Nat.succPNat (2 * k)` is the odd integer `2 * k + 1`, so the odd branch of
    -- `exercise1624CaseIIISingletonMass_eq` is the only surviving one.
    simp [exercise1624CaseIIISingletonMass_eq, Nat.succPNat_coe, hodd]
  · have heven : Even (2 * k + 2) := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using even_two_mul (k + 1)
    have hstep : (2 * k + 1 + 1 : ℝ) = (2 * k + 2 : ℝ) := by ring
    -- Proof comment: `Nat.succPNat (2 * k + 1)` is the even integer `2 * k + 2`, so the even
    -- branch of `exercise1624CaseIIISingletonMass_eq` applies directly.
    simpa [exercise1624CaseIIISingletonMass_eq, Nat.succPNat_coe, heven, hstep]

/-- Helper for Exercise 16.2.4: the exact case-(iii) right tail splits into its even and odd
power-law subseries once the `ℕ+` indexing is rewritten along `n = k + 1`. -/
lemma exercise1624CaseIIIRightTail_eq_evenOddSeries
    {μ : ProbabilityMeasure ℝ} {α β x : ℝ}
    (hα : α < -1) (hβ : β < -1)
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    rightTail μ x =
      (∑' k : ℕ,
        if x ≤ (2 * k + 2 : ℝ) then
          exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ α
        else
          0) +
        ∑' k : ℕ,
          if x ≤ (2 * k + 1 : ℝ) then
            exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ β
          else
            0 := by
  let c := exercise1624CaseIIINormalizationConstant α β
  let f : ℕ → ℝ := fun n ↦
    if x ≤ (n + 1 : ℝ) then exercise1624CaseIIISingletonMass α β (Nat.succPNat n) else 0
  have hc : 0 < c := exercise1624CaseIIINormalizationConstant_pos hsupport hmass
  have hf :
      rightTail μ x = ∑' n : ℕ, f n := by
    calc
      rightTail μ x
          = ∑' n : ℕ+, if x ≤ (n : ℝ) then exercise1624CaseIIISingletonMass α β n else 0 := by
              rw [exercise1624CaseIIIRightTail_eq_tsum hsupport hmass]
      _ = ∑' n : ℕ, f n := by
            symm
            simpa [f, Nat.succPNat_coe] using
              (Equiv.pnatEquivNat.symm.tsum_eq
                (fun n : ℕ+ ↦
                  if x ≤ (n : ℝ) then
                    exercise1624CaseIIISingletonMass α β n
                  else
                    0))
  have hOddDominated :
      Summable (fun k : ℕ ↦ c * (2 * k + 1 : ℝ) ^ β) := by
    simpa using
      (exercise1624_summableNatRpowAlongArithmetic
        (s := β) hβ (a := 2) (b := 1) (by decide : 0 < 2)).mul_left c
  have hEvenDominated :
      Summable (fun k : ℕ ↦ c * (2 * k + 2 : ℝ) ^ α) := by
    simpa using
      (exercise1624_summableNatRpowAlongArithmetic
        (s := α) hα (a := 2) (b := 2) (by decide : 0 < 2)).mul_left c
  have hEvenSubseries :
      Summable
        (fun k : ℕ ↦
          if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ β else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hOddDominated
    · intro k
      split_ifs with hk
      · exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _)
      · simp
    · intro k
      split_ifs with hk
      · simp
      · have hnonneg : 0 ≤ c * (2 * k + 1 : ℝ) ^ β := by
          exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _)
        exact by simpa using hnonneg
  have hOddSubseries :
      Summable
        (fun k : ℕ ↦
          if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ α else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hEvenDominated
    · intro k
      split_ifs with hk
      · exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _)
      · simp
    · intro k
      split_ifs with hk
      · simp
      · have hnonneg : 0 ≤ c * (2 * k + 2 : ℝ) ^ α := by
          exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _)
        exact by simpa using hnonneg
  have hEvenNatTerm (k : ℕ) :
      f (2 * k) =
        if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ β else 0 := by
    rcases exercise1624CaseIIISingletonMass_succ_evenOdd (α := α) (β := β) k with
      ⟨hEvenIndex, _⟩
    by_cases hk : x ≤ (2 * k + 1 : ℝ)
    · have hk' : x ≤ ((2 * k : ℕ) : ℝ) + 1 := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using hk
      have hcond : (((2 * k : ℕ) : ℝ) + 1) = (2 * k + 1 : ℝ) := by
        norm_num [Nat.cast_mul, Nat.cast_ofNat]
      simpa [f, c, hk, hk', hEvenIndex, hcond]
    · have hk' : ¬ x ≤ ((2 * k : ℕ) : ℝ) + 1 := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using hk
      have hcond : (((2 * k : ℕ) : ℝ) + 1) = (2 * k + 1 : ℝ) := by
        norm_num [Nat.cast_mul, Nat.cast_ofNat]
      simpa [f, c, hk, hk', hEvenIndex, hcond]
  have hOddNatTerm (k : ℕ) :
      f (2 * k + 1) =
        if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ α else 0 := by
    rcases exercise1624CaseIIISingletonMass_succ_evenOdd (α := α) (β := β) k with
      ⟨_, hOddIndex⟩
    by_cases hk : x ≤ (2 * k + 2 : ℝ)
    · have hk' : x ≤ ((2 * k + 1 : ℕ) : ℝ) + 1 := by
        have hEq : (((2 * k + 1 : ℕ) : ℝ) + 1) = (2 * k + 2 : ℝ) := by
          push_cast
          ring
        rw [hEq]
        exact hk
      dsimp [f]
      rw [if_pos hk', hOddIndex, if_pos hk]
    · have hk' : ¬ x ≤ ((2 * k + 1 : ℕ) : ℝ) + 1 := by
        intro hx'
        have hEq : (((2 * k + 1 : ℕ) : ℝ) + 1) = (2 * k + 2 : ℝ) := by
          push_cast
          ring
        rw [hEq] at hx'
        apply hk
        exact hx'
      dsimp [f]
      rw [if_neg hk', if_neg hk]
  have hEvenTerms : Summable (fun k : ℕ ↦ f (2 * k)) := by
    rw [show (fun k : ℕ ↦ f (2 * k)) =
      (fun k : ℕ ↦ if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ β else 0) by
      funext k
      exact hEvenNatTerm k]
    exact hEvenSubseries
  have hOddTerms : Summable (fun k : ℕ ↦ f (2 * k + 1)) := by
    rw [show (fun k : ℕ ↦ f (2 * k + 1)) =
      (fun k : ℕ ↦ if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ α else 0) by
      funext k
      exact hOddNatTerm k]
    exact hOddSubseries
  -- Proof comment: after shifting `ℕ+` to `ℕ`, split the resulting series into its odd and even
  -- subsequences once, so the theorem body can work with the two source tails separately.
  calc
    rightTail μ x = ∑' n : ℕ, f n := hf
    _ = ∑' k : ℕ, f (2 * k) + ∑' k : ℕ, f (2 * k + 1) := by
          symm
          exact tsum_even_add_odd hEvenTerms hOddTerms
    _ = (∑' k : ℕ,
          if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ α else 0) +
          ∑' k : ℕ,
            if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ β else 0 := by
          rw [add_comm]
          congr 1
          · refine tsum_congr fun k ↦ ?_
            -- Proof comment: the odd `ℕ` index `2 * k + 1` becomes the even atom `2 * k + 2`.
            exact hOddNatTerm k
          · refine tsum_congr fun k ↦ ?_
            -- Proof comment: the even `ℕ` index `2 * k` becomes the odd atom `2 * k + 1`.
            exact hEvenNatTerm k

/-- Helper for Exercise 16.2.4: the case-(iii) right tail stays strictly positive at every finite
threshold because there is always another positive-integer atom above that threshold. -/
lemma exercise1624CaseIIIRightTail_pos
    {μ : ProbabilityMeasure ℝ} {α β x : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    0 < rightTail μ x := by
  let n : ℕ+ := if hx : x < 1 then 1 else Nat.succPNat (Nat.ceil x)
  have hxn : x < (n : ℝ) := by
    by_cases hx : x < 1
    · simp [n, hx]
    · have hx0 : 0 ≤ x := by linarith
      have hceil : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
      simp [n, hx, Nat.succPNat_coe]
      have hceil_le : x ≤ (Nat.ceil x : ℝ) := by exact_mod_cast Nat.le_ceil x
      linarith
  have hsubset : ({(n : ℝ)} : Set ℝ) ⊆ Set.Ici x := by
    intro y hy
    have hy' : y = (n : ℝ) := by simpa using hy
    rw [hy']
    exact le_of_lt hxn
  have hmono :
      ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal ≤ rightTail μ x := by
    simpa [rightTail] using
      ENNReal.toReal_mono (measure_ne_top (μ : Measure ℝ) (Set.Ici x))
        (measure_mono hsubset)
  exact lt_of_lt_of_le (exercise1624CaseIIISingletonMass_pos hsupport hmass n) hmono

/-- Helper for Exercise 16.2.4: because case (iii) is supported on positive integers, the
positive-tail share criterion `(16.30)` has the constant limit `1`. -/
lemma exercise1624CaseIIIPositiveTailShareCriterion
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    PositiveTailShareCriterion16_30 μ := by
  refine ⟨1, ?_⟩
  have hEventuallyEq :
      (fun x : ℝ ↦ rightTail μ x / absTail μ x) =ᶠ[atTop]
        fun _ : ℝ ↦ 1 := by
    filter_upwards with x
    have hrt_pos : 0 < rightTail μ x := exercise1624CaseIIIRightTail_pos hsupport hmass
    -- Proof comment: on the positive-integer support, `absTail = rightTail`, and the strict
    -- positivity of the right tail removes the only potential `0 / 0` defect.
    rw [exercise1624CaseIIIAbsTail_eq_rightTail hsupport, div_self (ne_of_gt hrt_pos)]
  refine Tendsto.congr' hEventuallyEq.symm ?_
  simpa using tendsto_const_nhds

/-- Helper for Exercise 16.2.4: the case-(iii) law is not a Dirac mass because every finite
threshold still leaves a strictly positive right tail. -/
lemma exercise1624CaseIIINotDirac
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    ∀ x : ℝ, μ ≠ diracProba x := by
  intro x hx
  have htail_pos : 0 < rightTail μ (x + 1) :=
    exercise1624CaseIIIRightTail_pos (α := α) (β := β) (x := x + 1) hsupport hmass
  have htail_zero : rightTail μ (x + 1) = 0 := by
    rw [hx, rightTail]
    have hxnot : ¬ x ∈ Set.Ici (x + 1) := by
      simp [Set.mem_Ici]
    simp [MeasureTheory.diracProba, hxnot]
  linarith

/-- Helper for Exercise 16.2.4: the discrete `p`-series tail on `ℕ` has the same first-order
asymptotic as the matching improper integral. -/
lemma natRpowTail_div_natRpow_tendsto
    {s : ℝ} (hs : s < -1) :
    Tendsto
      (fun M : ℕ ↦ (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) / (M : ℝ) ^ (s + 1))
      atTop
      (𝓝 (-1 / (s + 1))) := by
  have hsNeg : s < 0 := by
    linarith
  have hsAnti : AntitoneOn (fun x : ℝ ↦ x ^ s) (Set.Ioi 0) :=
    (Real.strictAntiOn_rpow_Ioi_of_exponent_neg hsNeg).antitoneOn
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ s) := (Real.summable_nat_rpow).2 hs
  have htailSummable (M : ℕ) : Summable (fun k : ℕ ↦ ((M + k : ℕ) : ℝ) ^ s) := by
    -- Proof comment: each shifted tail is still a tail of the same summable `p`-series.
    simpa [Nat.add_comm] using ((_root_.summable_nat_add_iff M).2 hsum)
  have hpartial (M : ℕ) :
      Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range N, ((M + k : ℕ) : ℝ) ^ s) atTop
        (𝓝 (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s)) := by
    -- Proof comment: partial sums of the shifted tail converge to the corresponding `tsum`.
    exact
      (hasSum_iff_tendsto_nat_of_summable_norm ((htailSummable M).norm)).1
        (htailSummable M).hasSum
  have hEventuallyBounds :
      ∀ᶠ M : ℕ in atTop,
        (-1 / (s + 1)) ≤
          (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) / (M : ℝ) ^ (s + 1) ∧
        (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) / (M : ℝ) ^ (s + 1) ≤
          (-1 / (s + 1)) * ((((M : ℝ) - 1) / M) ^ (s + 1)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with M hM
    have hM1 : 1 ≤ M := by
      omega
    have hMpos : 0 < (M : ℝ) := by
      positivity
    have hMsubNatPos : 0 < M - 1 := by
      omega
    have hMsubPos : 0 < (((M - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hMsubNatPos
    have hLowerFinite (N : ℕ) :
        ∫ x in (M : ℝ)..((M + N : ℕ) : ℝ), x ^ s ≤
          ∑ k ∈ Finset.range N, ((M + k : ℕ) : ℝ) ^ s := by
      -- Proof comment: antitonicity puts each unit-interval integral below the left-endpoint
      -- sample, so the whole improper integral is bounded by the discrete tail.
      simpa [Finset.sum_Ico_eq_sum_range, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        (AntitoneOn.integral_le_sum_Ico (a := M) (b := M + N) (f := fun x : ℝ ↦ x ^ s)
          (show M ≤ M + N by omega)
          (hsAnti.mono (by
            intro x hx
            exact lt_of_lt_of_le hMpos hx.1)))
    have hUpperFinite (N : ℕ) :
        ∑ k ∈ Finset.range N, ((M + k : ℕ) : ℝ) ^ s ≤
          ∫ x in (((M - 1 : ℕ) : ℝ))..((((M - 1 : ℕ) + N : ℕ) : ℝ)), x ^ s := by
      -- Proof comment: shifting the antitone comparison one step to the left gives the matching
      -- upper integral bound.
      simpa [Finset.sum_Ico_eq_sum_range, Nat.cast_add, add_assoc, add_left_comm, add_comm,
        show (((M - 1 : ℕ) : ℝ) + 1) = M by exact_mod_cast Nat.sub_add_cancel hM1] using
        (AntitoneOn.sum_le_integral_Ico (a := M - 1) (b := (M - 1) + N) (f := fun x : ℝ ↦ x ^ s)
          (show M - 1 ≤ (M - 1) + N by omega)
          (hsAnti.mono (by
            intro x hx
            exact lt_of_lt_of_le hMsubPos hx.1)))
    have hbLower : Tendsto (fun N : ℕ ↦ ((M + N : ℕ) : ℝ)) atTop atTop := by
      simpa [add_comm] using
        ((Filter.tendsto_add_atTop_iff_nat M).2
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))
    have hbUpper : Tendsto (fun N : ℕ ↦ ((((M - 1 : ℕ) + N : ℕ) : ℝ))) atTop atTop := by
      simpa [add_comm] using
        ((Filter.tendsto_add_atTop_iff_nat (M - 1)).2
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))
    have hLowerTendsto :
        Tendsto (fun N : ℕ ↦ ∫ x in (M : ℝ)..((M + N : ℕ) : ℝ), x ^ s) atTop
          (𝓝 (∫ x in Set.Ioi (M : ℝ), x ^ s)) := by
      convert MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (M : ℝ))
        (f := fun x : ℝ ↦ x ^ s) (μ := volume)
        (integrableOn_Ioi_rpow_of_lt hs hMpos) hbLower using 1
    have hUpperTendsto :
        Tendsto (fun N : ℕ ↦ ∫ x in (((M - 1 : ℕ) : ℝ))..((((M - 1 : ℕ) + N : ℕ) : ℝ)), x ^ s)
          atTop
          (𝓝 (∫ x in Set.Ioi (((M - 1 : ℕ) : ℝ)), x ^ s)) := by
      convert MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (((M - 1 : ℕ) : ℝ)))
        (f := fun x : ℝ ↦ x ^ s) (μ := volume)
        (integrableOn_Ioi_rpow_of_lt hs hMsubPos) hbUpper using 1
    have hLower :
        ∫ x in Set.Ioi (M : ℝ), x ^ s ≤ (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) := by
      exact le_of_tendsto_of_tendsto' hLowerTendsto (hpartial M) hLowerFinite
    have hUpper :
        (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) ≤ ∫ x in Set.Ioi (((M - 1 : ℕ) : ℝ)), x ^ s := by
      exact le_of_tendsto_of_tendsto' (hpartial M) hUpperTendsto hUpperFinite
    have hMpowPos : 0 < (M : ℝ) ^ (s + 1) := Real.rpow_pos_of_pos hMpos _
    have hs1Ne : s + 1 ≠ 0 := by
      linarith
    have hLowerLimit :
        ∫ x in Set.Ioi (M : ℝ), x ^ s = - (M : ℝ) ^ (s + 1) / (s + 1) := by
      simpa using integral_Ioi_rpow_of_lt hs hMpos
    have hUpperLimit :
        ∫ x in Set.Ioi (((M - 1 : ℕ) : ℝ)), x ^ s =
          - (((M - 1 : ℕ) : ℝ) ^ (s + 1)) / (s + 1) := by
      simpa using integral_Ioi_rpow_of_lt hs hMsubPos
    constructor
    · have hquot :
          (∫ x in Set.Ioi (M : ℝ), x ^ s) / (M : ℝ) ^ (s + 1) ≤
            (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) / (M : ℝ) ^ (s + 1) :=
        div_le_div_of_nonneg_right hLower hMpowPos.le
      -- Proof comment: the lower improper integral evaluates exactly to the target constant.
      calc
        -1 / (s + 1) = (∫ x in Set.Ioi (M : ℝ), x ^ s) / (M : ℝ) ^ (s + 1) := by
          rw [hLowerLimit]
          field_simp [hMpowPos.ne', hs1Ne]
        _ ≤ (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) / (M : ℝ) ^ (s + 1) := hquot
    · have hquot :
          (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) / (M : ℝ) ^ (s + 1) ≤
            (∫ x in Set.Ioi (((M - 1 : ℕ) : ℝ)), x ^ s) / (M : ℝ) ^ (s + 1) :=
        div_le_div_of_nonneg_right hUpper hMpowPos.le
      -- Proof comment: the upper improper integral differs only by the ratio
      -- `((M - 1) / M) ^ (s + 1)`, which tends to `1`.
      calc
        (∑' k : ℕ, ((M + k : ℕ) : ℝ) ^ s) / (M : ℝ) ^ (s + 1) ≤
            (∫ x in Set.Ioi (((M - 1 : ℕ) : ℝ)), x ^ s) / (M : ℝ) ^ (s + 1) := hquot
        _ = (-1 / (s + 1)) * ((((M : ℝ) - 1) / M) ^ (s + 1)) := by
          rw [hUpperLimit, Nat.cast_sub hM1, Nat.cast_one]
          have hMsubNonneg : 0 ≤ (M : ℝ) - 1 := by
            have hreal : (1 : ℝ) ≤ M := by
              exact_mod_cast hM1
            linarith
          rw [Real.div_rpow hMsubNonneg hMpos.le]
          field_simp [hMpowPos.ne', hs1Ne]
  have hUpperRatio :
      Tendsto (fun M : ℕ ↦ (((M : ℝ) - 1) / M)) atTop (𝓝 1) := by
    have hratioSimple : Tendsto (fun M : ℕ ↦ 1 - (M : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using
        (tendsto_const_nhds.sub
          ((tendsto_inv_atTop_zero).comp
            (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)))
    refine Tendsto.congr' ?_ hratioSimple
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with M hM
    have hM0 : (M : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hM)
    field_simp [hM0]
  have hUpperPow :
      Tendsto (fun M : ℕ ↦ ((((M : ℝ) - 1) / M) ^ (s + 1))) atTop (𝓝 1) := by
    -- Proof comment: the correction factor is a continuous `rpow` at the limit point `1`.
    simpa using
      ((Real.continuousAt_rpow_const 1 (s + 1) (Or.inl one_ne_zero)).tendsto.comp hUpperRatio)
  have hUpperTendsto :
      Tendsto (fun M : ℕ ↦ (-1 / (s + 1)) * ((((M : ℝ) - 1) / M) ^ (s + 1))) atTop
        (𝓝 (-1 / (s + 1))) := by
    simpa using tendsto_const_nhds.mul hUpperPow
  -- Proof comment: the normalized discrete tail is trapped between the exact integral constant and
  -- an upper bound with a vanishing correction factor, so the squeeze theorem finishes the limit.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpperTendsto ?_ ?_
  · filter_upwards [hEventuallyBounds] with M hM
    exact hM.1
  · filter_upwards [hEventuallyBounds] with M hM
    exact hM.2

/-- Helper for Exercise 16.2.4: shifting a positive power-law argument by a fixed constant does
not change its leading asymptotic ratio. -/
lemma exercise1624_shiftedPower_div_rpow_tendsto_one
    {a s : ℝ} :
    Tendsto (fun x : ℝ ↦ (x + a) ^ s / x ^ s) atTop (𝓝 1) := by
  have hInner :
      Tendsto (fun x : ℝ ↦ 1 + a / x) atTop (𝓝 1) := by
    -- Proof comment: `a / x → 0`, so the shifted scaling factor converges to `1`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_const_nhds.add ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).const_mul a)
  have hPow :
      Tendsto (fun x : ℝ ↦ (1 + a / x) ^ s) atTop (𝓝 ((1 : ℝ) ^ s)) := by
    simpa using
      ((Real.continuousAt_rpow_const 1 s (Or.inl one_ne_zero)).tendsto.comp hInner)
  have hEventuallyEq :
      (fun x : ℝ ↦ (x + a) ^ s / x ^ s) =ᶠ[atTop]
        fun x : ℝ ↦ (1 + a / x) ^ s := by
    filter_upwards [Filter.eventually_gt_atTop (max 1 (-a + 1))] with x hx
    have hx_pos : 0 < x := by
      have h1 : (1 : ℝ) ≤ max 1 (-a + 1) := le_max_left _ _
      linarith
    have hxa_pos : 0 < x + a := by
      have hxa_gt_one : 1 < x + a := by
        linarith [hx, le_max_right (1 : ℝ) (-a + 1)]
      linarith
    have hdiv :
        (x + a) / x = 1 + a / x := by
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      field_simp [hx_ne]
    -- Proof comment: once both factors are positive, rewrite the shift as the multiplicative
    -- correction `1 + a / x` and split the `rpow` ratio exactly.
    rw [← Real.div_rpow hxa_pos.le hx_pos.le, hdiv]
  refine Tendsto.congr' hEventuallyEq.symm ?_
  simpa using hPow

/-- Helper for Exercise 16.2.4: the even parity branch of the case-(iii) right tail is governed by
the same Nat-tail asymptotic as the unshifted `p`-series. -/
lemma exercise1624EvenTail_div_rpow_tendsto
    {c s : ℝ} (hc : 0 < c) (hs : s < -1) :
    Tendsto
      (fun x : ℝ ↦
        (∑' k : ℕ, if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0) /
          x ^ (s + 1))
      atTop
      (𝓝 (c / (-2 * (s + 1)))) := by
  let N : ℝ → ℕ := fun x ↦ Nat.ceil (x / 2)
  have hNAtTop : Tendsto N atTop atTop := by
    -- Proof comment: the parity cutoff `⌈x / 2⌉` still tends to infinity with `x`.
    refine tendsto_nat_ceil_atTop.comp ?_
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Filter.Tendsto.const_mul_atTop' (show 0 < (1 / 2 : ℝ) by norm_num) tendsto_id)
  have hNat :
      Tendsto
        (fun x : ℝ ↦
          (∑' k : ℕ, (((N x + k : ℕ) : ℝ) ^ s)) /
            (N x : ℝ) ^ (s + 1))
        atTop
        (𝓝 (-1 / (s + 1))) :=
    (natRpowTail_div_natRpow_tendsto (s := s) hs).comp hNAtTop
  have hRatio :
      Tendsto (fun x : ℝ ↦ (N x : ℝ) / x) atTop (𝓝 (1 / 2 : ℝ)) := by
    -- Proof comment: `⌈x / 2⌉ / x` has the same limit as `(x / 2) / x`.
    simpa [N, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := (1 / 2 : ℝ)) (by norm_num))
  have hPowRatio :
      Tendsto
        (fun x : ℝ ↦ (N x : ℝ) ^ (s + 1) / x ^ (s + 1))
        atTop
        (𝓝 ((1 / 2 : ℝ) ^ (s + 1))) := by
    have hPow :
        Tendsto
          (fun x : ℝ ↦ (((N x : ℝ) / x) ^ (s + 1)))
          atTop
          (𝓝 ((1 / 2 : ℝ) ^ (s + 1))) := by
      simpa using
        ((Real.continuousAt_rpow_const (1 / 2 : ℝ) (s + 1) (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))).tendsto.comp hRatio)
    refine Tendsto.congr' ?_ hPow
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hNnonneg : 0 ≤ (N x : ℝ) := by positivity
    rw [← Real.div_rpow hNnonneg hx.le]
  have hEventuallyEq :
      (fun x : ℝ ↦
        (∑' k : ℕ, if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0) /
          x ^ (s + 1)) =ᶠ[atTop]
        (fun x : ℝ ↦
          c * (2 : ℝ) ^ s *
            (((∑' k : ℕ, (((N x + k : ℕ) : ℝ) ^ s)) / (N x : ℝ) ^ (s + 1)) *
              ((N x : ℝ) ^ (s + 1) / x ^ (s + 1)))) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hNpos : 0 < N x := by
      refine Nat.ceil_pos.mpr ?_
      positivity
    let f : ℕ → ℝ := fun n ↦ if N x ≤ n then c * (2 * n : ℝ) ^ s else 0
    have hBase : Summable (fun n : ℕ ↦ c * (2 * n : ℝ) ^ s) := by
      simpa using
        (exercise1624_summableNatRpowAlongArithmetic
          (s := s) hs (a := 2) (b := 0) (by decide : 0 < 2)).mul_left c
    have hf : Summable f := by
      refine Summable.of_nonneg_of_le ?_ ?_ hBase
      · intro n
        by_cases hn : N x ≤ n
        · simpa [f, hn] using mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
        · simp [f, hn]
      · intro n
        by_cases hn : N x ≤ n
        · simp [f, hn]
        · have hnonneg : 0 ≤ c * (2 * n : ℝ) ^ s := by
            exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
          simpa [f, hn] using hnonneg
    have hzero : f 0 = 0 := by
      simp [f, Nat.not_le_of_gt hNpos]
    have hOriginal :
        (∑' k : ℕ, if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0) =
          ∑' k : ℕ, f (k + 1) := by
      refine tsum_congr fun k ↦ ?_
      by_cases hk : x ≤ (2 * k + 2 : ℝ)
      · have hhalf : x / 2 ≤ (k + 1 : ℝ) := by
          nlinarith [hk]
        have hk' : N x ≤ k + 1 := by
          apply Nat.ceil_le.mpr
          simpa [Nat.cast_add, Nat.cast_ofNat] using hhalf
        have hstep : (2 * ((k + 1 : ℕ) : ℝ)) = (2 * k + 2 : ℝ) := by
          push_cast
          ring
        rw [if_pos hk]
        dsimp [f]
        rw [if_pos hk', hstep]
      · have hk' : ¬ N x ≤ k + 1 := by
          intro hle
          have hNle : (N x : ℝ) ≤ k + 1 := by
            exact_mod_cast hle
          have hhalf : x / 2 ≤ (k + 1 : ℝ) := by
            exact le_trans (Nat.le_ceil (x / 2)) hNle
          have hk'' : x ≤ (2 * k + 2 : ℝ) := by
            nlinarith
          exact hk hk''
        rw [if_neg hk]
        dsimp [f]
        rw [if_neg hk']
    have hShift :
        (∑' k : ℕ, f (k + 1)) = ∑' n : ℕ, f n := by
      have h := hf.tsum_eq_zero_add
      rw [hzero, zero_add] at h
      exact h.symm
    have hPrefixZero : (Finset.range (N x)).sum f = 0 := by
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      have hnot : ¬ N x ≤ n := Nat.not_le_of_gt (Finset.mem_range.mp hn)
      simp [f, hnot]
    have hTail :
        (∑' n : ℕ, f n) = ∑' k : ℕ, c * (2 * (N x + k) : ℝ) ^ s := by
      calc
        ∑' n : ℕ, f n = (∑ i ∈ Finset.range (N x), f i) + ∑' k : ℕ, f (k + N x) := by
          symm
          exact hf.sum_add_tsum_nat_add (N x)
        _ = ∑' k : ℕ, f (k + N x) := by rw [hPrefixZero, zero_add]
        _ = ∑' k : ℕ, c * (2 * (N x + k) : ℝ) ^ s := by
          refine tsum_congr fun k ↦ ?_
          have hk : N x ≤ k + N x := Nat.le_add_left _ _
          simp [f, hk, add_assoc, add_comm, add_left_comm]
    have hFactor :
        (∑' k : ℕ, c * (2 * (N x + k) : ℝ) ^ s) =
          c * (2 : ℝ) ^ s * ∑' k : ℕ, (((N x + k : ℕ) : ℝ) ^ s) := by
      calc
        ∑' k : ℕ, c * (2 * (N x + k) : ℝ) ^ s =
            ∑' k : ℕ, c * ((2 : ℝ) ^ s * (((N x + k : ℕ) : ℝ) ^ s)) := by
              refine tsum_congr fun k ↦ ?_
              have hNkNonneg : 0 ≤ (((N x + k : ℕ) : ℝ)) := by positivity
              have hcast : (2 * (N x + k) : ℝ) = (2 : ℝ) * (((N x + k : ℕ) : ℝ)) := by
                norm_num
              rw [hcast]
              rw [Real.mul_rpow (by positivity) hNkNonneg]
        _ = c * (∑' k : ℕ, (2 : ℝ) ^ s * (((N x + k : ℕ) : ℝ) ^ s)) := by
              rw [← _root_.tsum_mul_left]
        _ = c * ((2 : ℝ) ^ s * ∑' k : ℕ, (((N x + k : ℕ) : ℝ) ^ s)) := by
              congr 1
              rw [← _root_.tsum_mul_left]
        _ = c * (2 : ℝ) ^ s * ∑' k : ℕ, (((N x + k : ℕ) : ℝ) ^ s) := by ring
    have hNpow_ne : (N x : ℝ) ^ (s + 1) ≠ 0 :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _).ne'
    have hxpow_ne : x ^ (s + 1) ≠ 0 :=
      (Real.rpow_pos_of_pos hx _).ne'
    -- Proof comment: after the exact threshold rewrite, the even branch becomes the Nat tail
    -- times the cutoff-to-`x` normalization factor.
    rw [hOriginal, hShift, hTail, hFactor]
    field_simp [hNpow_ne, hxpow_ne]
  have hLimitRaw :
      Tendsto
        (fun x : ℝ ↦
          c * (2 : ℝ) ^ s *
            (((∑' k : ℕ, (((N x + k : ℕ) : ℝ) ^ s)) / (N x : ℝ) ^ (s + 1)) *
              ((N x : ℝ) ^ (s + 1) / x ^ (s + 1))))
        atTop
        (𝓝 (c * (2 : ℝ) ^ s * ((-1 / (s + 1)) * ((1 / 2 : ℝ) ^ (s + 1))))) := by
    exact tendsto_const_nhds.mul (hNat.mul hPowRatio)
  have hs1_ne : s + 1 ≠ 0 := by
    linarith
  have hTwoHalf :
      (2 : ℝ) ^ s * ((1 / 2 : ℝ) ^ (s + 1)) = 1 / 2 := by
    calc
      (2 : ℝ) ^ s * ((1 / 2 : ℝ) ^ (s + 1))
          = (2 : ℝ) ^ s * (((1 / 2 : ℝ) ^ s) * (1 / 2 : ℝ)) := by
              rw [show s + 1 = s + (1 : ℝ) by ring, Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ)),
                Real.rpow_one]
      _ = ((2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s) * (1 / 2 : ℝ) := by ring
      _ = ((2 * (1 / 2 : ℝ)) ^ s) * (1 / 2 : ℝ) := by
            rw [← Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ (1 / 2 : ℝ))]
      _ = 1 / 2 := by simp
  have hLimitConst :
      c * (2 : ℝ) ^ s * ((-1 / (s + 1)) * ((1 / 2 : ℝ) ^ (s + 1))) =
        c / (-2 * (s + 1)) := by
    calc
      c * (2 : ℝ) ^ s * ((-1 / (s + 1)) * ((1 / 2 : ℝ) ^ (s + 1)))
          = c * ((2 : ℝ) ^ s * ((1 / 2 : ℝ) ^ (s + 1))) * (-1 / (s + 1)) := by ring
      _ = c * (1 / 2 : ℝ) * (-1 / (s + 1)) := by rw [hTwoHalf]
      _ = c / (-2 * (s + 1)) := by
            field_simp [hs1_ne]
  have hLimit :
      Tendsto
        (fun x : ℝ ↦
          c * (2 : ℝ) ^ s *
            (((∑' k : ℕ, (((N x + k : ℕ) : ℝ) ^ s)) / (N x : ℝ) ^ (s + 1)) *
              ((N x : ℝ) ^ (s + 1) / x ^ (s + 1))))
        atTop
        (𝓝 (c / (-2 * (s + 1)))) := by
    convert hLimitRaw using 1
    rw [hLimitConst]
  refine Tendsto.congr' hEventuallyEq.symm hLimit

/-- Helper for Exercise 16.2.4: once `x` is large, the odd parity tail is trapped between the
adjacent shifted even tails. -/
lemma exercise1624OddTail_eventually_between_shiftedEvenTails
    {c s : ℝ} (hc : 0 < c) (hs : s < -1) :
    ∀ᶠ x : ℝ in atTop,
      ((∑' k : ℕ, if x + 1 ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0) ≤
        ∑' k : ℕ, if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ s else 0) ∧
      ((∑' k : ℕ, if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ s else 0) ≤
        ∑' k : ℕ, if x - 1 ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0) := by
  have hsNeg : s < 0 := by
    linarith
  have hAnti : AntitoneOn (fun t : ℝ ↦ t ^ s) (Set.Ioi 0) :=
    (Real.strictAntiOn_rpow_Ioi_of_exponent_neg hsNeg).antitoneOn
  have hOddBase : Summable (fun k : ℕ ↦ c * (2 * k + 1 : ℝ) ^ s) := by
    simpa using
      (exercise1624_summableNatRpowAlongArithmetic
        (s := s) hs (a := 2) (b := 1) (by decide : 0 < 2)).mul_left c
  have hEvenBase : Summable (fun k : ℕ ↦ c * (2 * k + 2 : ℝ) ^ s) := by
    simpa using
      (exercise1624_summableNatRpowAlongArithmetic
        (s := s) hs (a := 2) (b := 2) (by decide : 0 < 2)).mul_left c
  filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with x hx
  let lower : ℕ → ℝ := fun k ↦
    if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0
  let odd : ℕ → ℝ := fun k ↦
    if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ s else 0
  let upper : ℕ → ℝ := fun k ↦
    if x ≤ (2 * k + 3 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0
  have hLowerSummable : Summable lower := by
    refine Summable.of_nonneg_of_le ?_ ?_ hEvenBase
    · intro k
      by_cases hk : x ≤ (2 * k + 1 : ℝ)
      · simpa [lower, hk] using mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
      · simp [lower, hk]
    · intro k
      by_cases hk : x ≤ (2 * k + 1 : ℝ)
      · simp [lower, hk]
      · have hnonneg : 0 ≤ c * (2 * k + 2 : ℝ) ^ s := by
          exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
        simpa [lower, hk] using hnonneg
  have hOddSummable : Summable odd := by
    refine Summable.of_nonneg_of_le ?_ ?_ hOddBase
    · intro k
      by_cases hk : x ≤ (2 * k + 1 : ℝ)
      · simpa [odd, hk] using mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
      · simp [odd, hk]
    · intro k
      by_cases hk : x ≤ (2 * k + 1 : ℝ)
      · simp [odd, hk]
      · have hnonneg : 0 ≤ c * (2 * k + 1 : ℝ) ^ s := by
          exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
        simpa [odd, hk] using hnonneg
  have hUpperSummable : Summable upper := by
    refine Summable.of_nonneg_of_le ?_ ?_ hEvenBase
    · intro k
      by_cases hk : x ≤ (2 * k + 3 : ℝ)
      · simpa [upper, hk] using mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
      · simp [upper, hk]
    · intro k
      by_cases hk : x ≤ (2 * k + 3 : ℝ)
      · simp [upper, hk]
      · have hnonneg : 0 ≤ c * (2 * k + 2 : ℝ) ^ s := by
          exact mul_nonneg hc.le (Real.rpow_nonneg (by positivity) s)
        simpa [upper, hk] using hnonneg
  have hLowerLeOdd :
      (∑' k : ℕ, lower k) ≤ ∑' k : ℕ, odd k := by
    -- Proof comment: the lower shifted even tail uses the same threshold as the odd tail, and
    -- the negative exponent makes each even atom smaller than the preceding odd atom.
    refine Summable.tsum_le_tsum ?_ hLowerSummable hOddSummable
    intro k
    by_cases hk : x ≤ (2 * k + 1 : ℝ)
    · have hmono : (2 * k + 2 : ℝ) ^ s ≤ (2 * k + 1 : ℝ) ^ s := by
        have hpos1 : 0 < (2 * k + 1 : ℝ) := by positivity
        have hpos2 : 0 < (2 * k + 2 : ℝ) := by positivity
        exact hAnti hpos1 hpos2 (by linarith)
      simpa [lower, odd, hk] using mul_le_mul_of_nonneg_left hmono hc.le
    · simp [lower, odd, hk]
  let oddShift : ℕ → ℝ := fun k ↦ odd (k + 1)
  have hOddZero : odd 0 = 0 := by
    have hxnot : ¬ x ≤ (1 : ℝ) := by
      linarith
    simp [odd, hxnot]
  have hOddShiftEq : (∑' k : ℕ, oddShift k) = ∑' k : ℕ, odd k := by
    have h := hOddSummable.tsum_eq_zero_add
    rw [hOddZero, zero_add] at h
    simpa [oddShift] using h.symm
  have hOddShiftSummable : Summable oddShift := by
    simpa [oddShift, Nat.add_comm] using ((_root_.summable_nat_add_iff 1).2 hOddSummable)
  have hOddShiftLe : ∀ k : ℕ, oddShift k ≤ upper k := by
    intro k
    by_cases hk : x ≤ (2 * (k + 1) + 1 : ℝ)
    · have hmono : (2 * (k + 1) + 1 : ℝ) ^ s ≤ (2 * k + 2 : ℝ) ^ s := by
        have hpos1 : 0 < (2 * k + 2 : ℝ) := by positivity
        have hpos2 : 0 < (2 * (k + 1) + 1 : ℝ) := by positivity
        have hle : (2 * k + 2 : ℝ) ≤ 2 * (k + 1 : ℝ) + 1 := by
          nlinarith
        exact hAnti hpos1 hpos2 hle
      have hkUpper : x ≤ (2 * (k : ℝ) + 3) := by
        nlinarith [hk]
      have hthr : (2 * (k + 1) + 1 : ℝ) = 2 * (k : ℝ) + 3 := by
        ring
      have hkShift : x ≤ 2 * ((k + 1 : ℕ) : ℝ) + 1 := by
        simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hk
      simpa [oddShift, odd, upper, hkShift, hkUpper, hthr] using
        mul_le_mul_of_nonneg_left hmono hc.le
    · have hkUpper : ¬ x ≤ (2 * k + 3 : ℝ) := by
        nlinarith [hk]
      have hkShift : ¬ x ≤ 2 * ((k + 1 : ℕ) : ℝ) + 1 := by
        simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hk
      dsimp [oddShift, odd, upper]
      rw [if_neg hkShift, if_neg hkUpper]

  have hOddLeUpper :
      (∑' k : ℕ, odd k) ≤ ∑' k : ℕ, upper k := by
    -- Proof comment: after discarding the zero `k = 0` odd term, each remaining odd atom is
    -- bounded by the previous even atom at the next threshold.
    calc
      ∑' k : ℕ, odd k = ∑' k : ℕ, oddShift k := hOddShiftEq.symm
      _ ≤ ∑' k : ℕ, upper k := Summable.tsum_le_tsum hOddShiftLe hOddShiftSummable hUpperSummable
  constructor
  · have hLowerEq :
        (∑' k : ℕ, if x + 1 ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0) =
          ∑' k : ℕ, lower k := by
      refine tsum_congr fun k ↦ ?_
      by_cases hk : x ≤ (2 * k + 1 : ℝ)
      · have hk' : x + 1 ≤ (2 * k + 2 : ℝ) := by
          linarith
        simp [lower, hk, hk']
      · have hk' : ¬ x + 1 ≤ (2 * k + 2 : ℝ) := by
          linarith
        simp [lower, hk, hk']
    rw [hLowerEq]
    exact hLowerLeOdd
  · have hUpperEq :
        (∑' k : ℕ, if x - 1 ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0) =
          ∑' k : ℕ, upper k := by
      refine tsum_congr fun k ↦ ?_
      by_cases hk : x ≤ (2 * k + 3 : ℝ)
      · have hk' : x - 1 ≤ (2 * k + 2 : ℝ) := by
          linarith
        simp [upper, hk, hk']
      · have hk' : ¬ x - 1 ≤ (2 * k + 2 : ℝ) := by
          linarith
        simp [upper, hk, hk']
    rw [hUpperEq]
    exact hOddLeUpper

/-- Helper for Exercise 16.2.4: the odd parity branch inherits the same leading asymptotic as the
even branch by squeezing it between adjacent shifted even tails. -/
lemma exercise1624OddTail_div_rpow_tendsto
    {c s : ℝ} (hc : 0 < c) (hs : s < -1) :
    Tendsto
      (fun x : ℝ ↦
        (∑' k : ℕ, if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ s else 0) /
          x ^ (s + 1))
      atTop
      (𝓝 (c / (-2 * (s + 1)))) := by
  let K : ℝ := c / (-2 * (s + 1))
  let evenTail : ℝ → ℝ := fun x ↦
    ∑' k : ℕ, if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ s else 0
  let oddTail : ℝ → ℝ := fun x ↦
    ∑' k : ℕ, if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ s else 0
  have hEven :
      Tendsto (fun x : ℝ ↦ evenTail x / x ^ (s + 1)) atTop (𝓝 K) := by
    simpa [evenTail, K] using exercise1624EvenTail_div_rpow_tendsto (c := c) (s := s) hc hs
  have hBetween :
      ∀ᶠ x : ℝ in atTop, evenTail (x + 1) ≤ oddTail x ∧ oddTail x ≤ evenTail (x - 1) := by
    simpa [evenTail, oddTail] using
      exercise1624OddTail_eventually_between_shiftedEvenTails (c := c) (s := s) hc hs
  have hShiftPlusAtTop : Tendsto (fun x : ℝ ↦ x + 1) atTop atTop := by
    exact le_of_eq (Filter.map_add_atTop_eq (1 : ℝ))
  have hShiftMinusAtTop : Tendsto (fun x : ℝ ↦ x - 1) atTop atTop := by
    exact le_of_eq (Filter.map_sub_atTop_eq (1 : ℝ))
  have hLowerRaw :
      Tendsto (fun x : ℝ ↦ evenTail (x + 1) / (x + 1) ^ (s + 1)) atTop (𝓝 K) := by
    simpa using hEven.comp hShiftPlusAtTop
  have hUpperRaw :
      Tendsto (fun x : ℝ ↦ evenTail (x - 1) / (x - 1) ^ (s + 1)) atTop (𝓝 K) := by
    simpa using hEven.comp hShiftMinusAtTop
  have hShiftPlus :
      Tendsto (fun x : ℝ ↦ (x + 1) ^ (s + 1) / x ^ (s + 1)) atTop (𝓝 1) := by
    simpa using
      exercise1624_shiftedPower_div_rpow_tendsto_one (a := (1 : ℝ)) (s := s + 1)
  have hShiftMinus :
      Tendsto (fun x : ℝ ↦ (x - 1) ^ (s + 1) / x ^ (s + 1)) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg] using
      exercise1624_shiftedPower_div_rpow_tendsto_one (a := (-1 : ℝ)) (s := s + 1)
  have hLower :
      Tendsto (fun x : ℝ ↦ evenTail (x + 1) / x ^ (s + 1)) atTop (𝓝 K) := by
    have hProd := hLowerRaw.mul hShiftPlus
    have hEventuallyEq :
        (fun x : ℝ ↦ evenTail (x + 1) / x ^ (s + 1)) =ᶠ[atTop]
          fun x : ℝ ↦
            (evenTail (x + 1) / (x + 1) ^ (s + 1)) * ((x + 1) ^ (s + 1) / x ^ (s + 1)) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      have hx1 : 0 < x + 1 := by
        linarith
      have hxPow : x ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
      have hx1Pow : (x + 1) ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hx1 _).ne'
      field_simp [hxPow, hx1Pow]
    -- Proof comment: normalize the shifted lower comparison back to the original denominator
    -- `x ^ (s + 1)` before applying the squeeze theorem.
    refine Tendsto.congr' hEventuallyEq.symm ?_
    simpa [K] using hProd
  have hUpper :
      Tendsto (fun x : ℝ ↦ evenTail (x - 1) / x ^ (s + 1)) atTop (𝓝 K) := by
    have hProd := hUpperRaw.mul hShiftMinus
    have hEventuallyEq :
        (fun x : ℝ ↦ evenTail (x - 1) / x ^ (s + 1)) =ᶠ[atTop]
          fun x : ℝ ↦
            (evenTail (x - 1) / (x - 1) ^ (s + 1)) * ((x - 1) ^ (s + 1) / x ^ (s + 1)) := by
      filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with x hx
      have hx0 : 0 < x := by
        linarith
      have hx1 : 0 < x - 1 := by
        linarith
      have hxPow : x ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
      have hx1Pow : (x - 1) ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hx1 _).ne'
      field_simp [hxPow, hx1Pow]
    -- Proof comment: the upper shifted even tail is handled in exactly the same way after the
    -- eventual positivity of `x - 1` is enforced.
    refine Tendsto.congr' hEventuallyEq.symm ?_
    simpa [K] using hProd
  have hOddBounds :
      ∀ᶠ x : ℝ in atTop,
        evenTail (x + 1) / x ^ (s + 1) ≤ oddTail x / x ^ (s + 1) ∧
          oddTail x / x ^ (s + 1) ≤ evenTail (x - 1) / x ^ (s + 1) := by
    filter_upwards [hBetween, Filter.eventually_gt_atTop (2 : ℝ)] with x hxBetween hx
    have hx0 : 0 < x := by
      linarith
    have hxPowPos : 0 < x ^ (s + 1) := Real.rpow_pos_of_pos hx0 _
    constructor
    · exact div_le_div_of_nonneg_right hxBetween.1 hxPowPos.le
    · exact div_le_div_of_nonneg_right hxBetween.2 hxPowPos.le
  -- Proof comment: the odd tail is now squeezed between two shifted even tails with the same
  -- limit constant, so it shares the same leading asymptotic.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper ?_ ?_
  · filter_upwards [hOddBounds] with x hx
    exact hx.1
  · filter_upwards [hOddBounds] with x hx
    exact hx.2

/-- Helper for Exercise 16.2.4: if a branch already has asymptotic exponent `s + 1`, then
normalizing it by the heavier exponent `t + 1` with `s < t` forces the limit to vanish. -/
lemma exercise1624_div_rpow_tendsto_zero_of_lt
    {f : ℝ → ℝ} {L s t : ℝ}
    (hf : Tendsto (fun x : ℝ ↦ f x / x ^ (s + 1)) atTop (𝓝 L))
    (hst : s < t) :
    Tendsto (fun x : ℝ ↦ f x / x ^ (t + 1)) atTop (𝓝 0) := by
  have hDecayRaw : Tendsto (fun x : ℝ ↦ x ^ (-(t - s))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (sub_pos.mpr hst)
  have hDecay : Tendsto (fun x : ℝ ↦ x ^ ((s + 1) - (t + 1))) atTop (𝓝 0) := by
    convert hDecayRaw using 1
    ext x
    congr 1
    ring
  have hEventuallyEq :
      (fun x : ℝ ↦ f x / x ^ (t + 1)) =ᶠ[atTop]
        fun x : ℝ ↦ (f x / x ^ (s + 1)) * x ^ ((s + 1) - (t + 1)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hxPowS : x ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    have hxPowT : x ^ (t + 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    rw [Real.rpow_sub hx (s + 1) (t + 1)]
    field_simp [hxPowS, hxPowT]
  -- Proof comment: separate the smaller branch into its known asymptotic factor and one extra
  -- negative power of `x`, which tends to `0`.
  refine Tendsto.congr' hEventuallyEq.symm ?_
  simpa using hf.mul hDecay

/-- Helper for Exercise 16.2.4: the odd/even singleton tail in case (iii) should have one
dominant regularly varying exponent, namely `max α β + 1`. -/
lemma exercise1624CaseIIIRightTail_div_rpow_tendsto
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hα : α < -1) (hβ : β < -1)
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    ∃ K > 0, Tendsto (fun x : ℝ ↦ rightTail μ x / x ^ (max α β + 1)) atTop (𝓝 K) := by
  let c := exercise1624CaseIIINormalizationConstant α β
  let evenTail : ℝ → ℝ := fun x ↦
    ∑' k : ℕ, if x ≤ (2 * k + 2 : ℝ) then c * (2 * k + 2 : ℝ) ^ α else 0
  let oddTail : ℝ → ℝ := fun x ↦
    ∑' k : ℕ, if x ≤ (2 * k + 1 : ℝ) then c * (2 * k + 1 : ℝ) ^ β else 0
  have hc : 0 < c := by
    simpa [c] using exercise1624CaseIIINormalizationConstant_pos hsupport hmass
  have hRightTailEq (x : ℝ) : rightTail μ x = evenTail x + oddTail x := by
    simpa [c, evenTail, oddTail] using
      exercise1624CaseIIIRightTail_eq_evenOddSeries
        (μ := μ) (α := α) (β := β) (x := x) hα hβ hsupport hmass
  have hEven :
      Tendsto (fun x : ℝ ↦ evenTail x / x ^ (α + 1)) atTop (𝓝 (c / (-2 * (α + 1)))) := by
    simpa [c, evenTail] using
      exercise1624EvenTail_div_rpow_tendsto (c := c) (s := α) hc hα
  have hOdd :
      Tendsto (fun x : ℝ ↦ oddTail x / x ^ (β + 1)) atTop (𝓝 (c / (-2 * (β + 1)))) := by
    simpa [c, oddTail] using
      exercise1624OddTail_div_rpow_tendsto (c := c) (s := β) hc hβ
  -- Route correction: the failed direct odd-branch transport is replaced by the shifted-even-tail
  -- squeeze, so the main theorem only needs a flat dominant-exponent case split.
  rcases lt_trichotomy α β with hlt | hEq | hgt
  · have hEvenSmall :
      Tendsto (fun x : ℝ ↦ evenTail x / x ^ (β + 1)) atTop (𝓝 0) :=
      exercise1624_div_rpow_tendsto_zero_of_lt (f := evenTail) hEven hlt
    have hTailBeta :
        Tendsto (fun x : ℝ ↦ rightTail μ x / x ^ (β + 1)) atTop
          (𝓝 (c / (-2 * (β + 1)))) := by
      have hEventuallyEq :
          (fun x : ℝ ↦ rightTail μ x / x ^ (β + 1)) =ᶠ[atTop]
            fun x : ℝ ↦ evenTail x / x ^ (β + 1) + oddTail x / x ^ (β + 1) := by
        filter_upwards with x
        rw [hRightTailEq x, add_div]
      -- Proof comment: when `α < β`, the odd branch carries the heavier tail and the even branch
      -- vanishes after one extra negative power of `x`.
      refine Tendsto.congr' hEventuallyEq.symm ?_
      simpa using hEvenSmall.add hOdd
    have hKpos : 0 < c / (-2 * (β + 1)) := by
      have hden : 0 < -2 * (β + 1) := by
        nlinarith
      exact div_pos hc hden
    refine ⟨c / (-2 * (β + 1)), hKpos, ?_⟩
    convert hTailBeta using 1
    ext x
    rw [max_eq_right (le_of_lt hlt)]
  · subst β
    have hTailAlpha :
        Tendsto (fun x : ℝ ↦ rightTail μ x / x ^ (α + 1)) atTop
          (𝓝 (c / (-2 * (α + 1)) + c / (-2 * (α + 1)))) := by
      have hEventuallyEq :
          (fun x : ℝ ↦ rightTail μ x / x ^ (α + 1)) =ᶠ[atTop]
            fun x : ℝ ↦ evenTail x / x ^ (α + 1) + oddTail x / x ^ (α + 1) := by
        filter_upwards with x
        rw [hRightTailEq x, add_div]
      -- Proof comment: equal exponents make the even and odd branch limits add directly.
      refine Tendsto.congr' hEventuallyEq.symm ?_
      simpa using hEven.add hOdd
    have hα1ne : α + 1 ≠ 0 := by
      linarith
    have hConst :
        c / (-2 * (α + 1)) + c / (-2 * (α + 1)) = c / (-(α + 1)) := by
      field_simp [hα1ne]
      ring
    have hTail :
        Tendsto (fun x : ℝ ↦ rightTail μ x / x ^ (α + 1)) atTop (𝓝 (c / (-(α + 1)))) := by
      convert hTailAlpha using 1
      rw [hConst]
    have hKpos : 0 < c / (-(α + 1)) := by
      have hden : 0 < -(α + 1) := by
        linarith
      exact div_pos hc hden
    refine ⟨c / (-(α + 1)), hKpos, ?_⟩
    convert hTail using 1
    ext x
    rw [max_self]
  · have hOddSmall :
      Tendsto (fun x : ℝ ↦ oddTail x / x ^ (α + 1)) atTop (𝓝 0) :=
      exercise1624_div_rpow_tendsto_zero_of_lt (f := oddTail) hOdd hgt
    have hTailAlpha :
        Tendsto (fun x : ℝ ↦ rightTail μ x / x ^ (α + 1)) atTop
          (𝓝 (c / (-2 * (α + 1)))) := by
      have hEventuallyEq :
          (fun x : ℝ ↦ rightTail μ x / x ^ (α + 1)) =ᶠ[atTop]
            fun x : ℝ ↦ evenTail x / x ^ (α + 1) + oddTail x / x ^ (α + 1) := by
        filter_upwards with x
        rw [hRightTailEq x, add_div]
      -- Proof comment: this is the symmetric strict-dominance case, now with the even branch as
      -- the unique surviving heavy tail.
      refine Tendsto.congr' hEventuallyEq.symm ?_
      simpa using hEven.add hOddSmall
    have hKpos : 0 < c / (-2 * (α + 1)) := by
      have hden : 0 < -2 * (α + 1) := by
        nlinarith
      exact div_pos hc hden
    refine ⟨c / (-2 * (α + 1)), hKpos, ?_⟩
    convert hTailAlpha using 1
    ext x
    rw [max_eq_left (le_of_lt hgt)]

/-- Helper for Exercise 16.2.4: once the stable index is strictly below `2`, it is exactly the
raw heavy-tail exponent `-(max α β + 1)`. -/
lemma exercise1624CaseIIIStableIndex_eq_of_lt_two
    {α β : ℝ}
    (hidx_lt_two : exercise1624StableIndex α β < 2) :
    exercise1624StableIndex α β = -(max α β + 1) := by
  have hraw_lt_two : -max α β - 1 < 2 := by
    by_contra hnot
    have hraw_ge_two : 2 ≤ -max α β - 1 := not_lt.mp hnot
    rw [exercise1624StableIndex_eq, min_eq_left hraw_ge_two] at hidx_lt_two
    linarith
  -- Proof comment: once the outer `min 2` is inactive, only the heavier power exponent remains.
  rw [exercise1624StableIndex_eq, min_eq_right (le_of_lt hraw_lt_two)]
  ring

/-- Helper for Exercise 16.2.4: in the non-Gaussian case-(iii) branch, the positive-integer
support and the right-tail asymptotic imply the Chapter 16 tail criterion `(16.29)`. -/
lemma exercise1624CaseIIIHeavyTailCriterion
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hα : α < -1) (hβ : β < -1)
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n)
    (hidx_lt_two : exercise1624StableIndex α β < 2) :
    TailCriterion16_29 μ (exercise1624StableIndex α β) := by
  rcases exercise1624CaseIIIRightTail_div_rpow_tendsto hα hβ hsupport hmass with
    ⟨K, hK, hRight⟩
  have hidx_eq : exercise1624StableIndex α β = -(max α β + 1) :=
    exercise1624CaseIIIStableIndex_eq_of_lt_two hidx_lt_two
  have hAbsEq :
      (fun x : ℝ ↦ absTail μ x) =ᶠ[atTop] fun x ↦ rightTail μ x :=
    Filter.Eventually.of_forall fun x ↦ exercise1624CaseIIIAbsTail_eq_rightTail hsupport
  have hRightPos : ∀ᶠ x : ℝ in atTop, 0 < rightTail μ x :=
    Filter.Eventually.of_forall fun x ↦ exercise1624CaseIIIRightTail_pos hsupport hmass
  have hTail :
      TailCriterion16_29 μ (-(max α β + 1)) :=
    tailCriterionOfEventualRightTailRpowLimit (μ := μ) (γ := max α β + 1) (K := K)
      hK hRight hAbsEq hRightPos
  -- Proof comment: the local right-tail owner already returns the criterion at the raw exponent,
  -- so the branch closes after rewriting the stable index to that exponent.
  simpa [hidx_eq] using hTail

/-- Helper for Exercise 16.2.4: on the exact boundary `max α β = -3`, the case-(iii) right-tail
asymptotic specializes to the quadratic tail criterion `(16.29)` at index `2`. -/
lemma exercise1624CaseIIIExactBoundaryTailCriterion
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hα : α < -1) (hβ : β < -1)
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n)
    (hboundary : max α β = -3) :
    TailCriterion16_29 μ 2 := by
  rcases exercise1624CaseIIIRightTail_div_rpow_tendsto hα hβ hsupport hmass with
    ⟨K, hK, hRight⟩
  have hExp : max α β + 1 = (-2 : ℝ) := by
    rw [hboundary]
    ring
  have hRightBoundary :
      Tendsto (fun x : ℝ ↦ rightTail μ x / x ^ (-2 : ℝ)) atTop (𝓝 K) := by
    -- Proof comment: rewrite the boundary exponent once and reuse the already proved tail limit.
    simpa [hExp] using hRight
  have hAbsEq :
      (fun x : ℝ ↦ absTail μ x) =ᶠ[atTop] fun x ↦ rightTail μ x :=
    Filter.Eventually.of_forall fun x ↦ exercise1624CaseIIIAbsTail_eq_rightTail hsupport
  have hRightPos : ∀ᶠ x : ℝ in atTop, 0 < rightTail μ x :=
    Filter.Eventually.of_forall fun x ↦ exercise1624CaseIIIRightTail_pos hsupport hmass
  -- Proof comment: the boundary identity `max α β + 1 = -2` turns the right-tail regular
  -- variation owner directly into the quadratic tail criterion.
  simpa using
    tailCriterionOfEventualRightTailRpowLimit (μ := μ) (γ := (-2 : ℝ)) (K := K)
      hK hRightBoundary hAbsEq hRightPos

/-- Helper for Exercise 16.2.4: multiplying a singleton atom by the square observable shifts the
power-law exponent by `2`. -/
lemma exercise1624CaseIIISquareWeightedSingletonMass_eq
    {α β : ℝ} (n : ℕ+) :
    (n : ℝ) ^ (2 : ℕ) * exercise1624CaseIIISingletonMass α β n =
      if Even (n : ℕ) then
        exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ (α + 2)
      else
        exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ (β + 2) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  -- Proof comment: on each positive atom, multiplying by `x²` only shifts the active `rpow`
  -- exponent from `α` or `β` to `α + 2` or `β + 2`.
  rw [exercise1624CaseIIISingletonMass_eq]
  split_ifs with hEven
  · calc
      (n : ℝ) ^ (2 : ℕ) *
          (exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ α)
          =
        exercise1624CaseIIINormalizationConstant α β *
          ((n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ α) := by
            ring
    _ =
        exercise1624CaseIIINormalizationConstant α β *
          ((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ α) := by
            congr 1
            rw [show (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℝ) by
              simpa using (Real.rpow_natCast (n : ℝ) 2).symm]
    _ =
        exercise1624CaseIIINormalizationConstant α β *
          (n : ℝ) ^ (α + 2) := by
            congr 1
            calc
              (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ α
                  = (n : ℝ) ^ α * (n : ℝ) ^ (2 : ℝ) := by ring
              _ = (n : ℝ) ^ (α + 2) := by
                    rw [← Real.rpow_add hn_pos α 2]
  · calc
      (n : ℝ) ^ (2 : ℕ) *
          (exercise1624CaseIIINormalizationConstant α β * (n : ℝ) ^ β)
          =
        exercise1624CaseIIINormalizationConstant α β *
          ((n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ β) := by
            ring
    _ =
        exercise1624CaseIIINormalizationConstant α β *
          ((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ β) := by
            congr 1
            rw [show (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℝ) by
              simpa using (Real.rpow_natCast (n : ℝ) 2).symm]
    _ =
        exercise1624CaseIIINormalizationConstant α β *
          (n : ℝ) ^ (β + 2) := by
            congr 1
            calc
              (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ β
                  = (n : ℝ) ^ β * (n : ℝ) ^ (2 : ℝ) := by ring
              _ = (n : ℝ) ^ (β + 2) := by
                    rw [← Real.rpow_add hn_pos β 2]

/-- Helper for Exercise 16.2.4: the square-moment `lintegral` of the case-(iii) atomic law splits
once into the even and odd power-law series. -/
lemma exercise1624CaseIIISquareLIntegral_eq_evenOddSeries
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ) =
      (∑' k : ℕ,
        ENNReal.ofReal
          (exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ (α + 2))) +
        ∑' k : ℕ,
          ENNReal.ofReal
            (exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ (β + 2)) := by
  let S : Set ℝ := Set.range fun n : ℕ+ ↦ (n : ℝ)
  let f : ℕ → ENNReal := fun n ↦
    ENNReal.ofReal
      (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        exercise1624CaseIIISingletonMass α β (Nat.succPNat n))
  have hScompl_zero : (μ : Measure ℝ) Sᶜ = 0 := by
    rw [ENNReal.toReal_eq_zero_iff] at hsupport
    rcases hsupport with hzero | htop
    · simpa [S] using hzero
    · exact (measure_ne_top (μ : Measure ℝ) Sᶜ htop).elim
  have hSae : S =ᵐ[(μ : Measure ℝ)] Set.univ := by
    apply (MeasureTheory.ae_eq_univ_iff_measure_eq
      (μ := (μ : Measure ℝ))
      (hs := (Set.countable_range fun n : ℕ+ ↦ (n : ℝ)).measurableSet.nullMeasurableSet)).2
    exact MeasureTheory.measure_of_measure_compl_eq_zero hScompl_zero
  have hS_mem : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ S := by
    filter_upwards [hSae] with x hx
    simpa [Set.mem_univ] using hx.mpr trivial
  have hIndicator :
      S.indicator (fun x : ℝ ↦ ENNReal.ofReal (x ^ (2 : ℕ))) =ᵐ[(μ : Measure ℝ)]
        fun x : ℝ ↦ ENNReal.ofReal (x ^ (2 : ℕ)) := by
    filter_upwards [hS_mem] with x hx
    simp [Set.indicator_of_mem, hx]
  have hSingletonMassENN :
      ∀ n : ℕ+,
        (μ : Measure ℝ) ({(n : ℝ)} : Set ℝ) =
          ENNReal.ofReal (exercise1624CaseIIISingletonMass α β n) := by
    intro n
    calc
      (μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)
          = ENNReal.ofReal (((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal) := by
              rw [ENNReal.ofReal_toReal (measure_ne_top (μ : Measure ℝ) ({(n : ℝ)} : Set ℝ))]
      _ = ENNReal.ofReal (exercise1624CaseIIISingletonMass α β n) := by
            rw [hmass n]
  have hSingletonPairwise :
      Pairwise fun i j : ℕ+ ↦ Disjoint ({(i : ℝ)} : Set ℝ) ({(j : ℝ)} : Set ℝ) := by
    intro i j hij
    have hij' : (i : ℝ) ≠ (j : ℝ) := by
      exact_mod_cast hij
    simpa [Set.disjoint_singleton] using hij'
  have hIntegralSeries :
      ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ) =
        ∑' n : ℕ+,
          ENNReal.ofReal
            ((n : ℝ) ^ (2 : ℕ) * exercise1624CaseIIISingletonMass α β n) := by
    -- Proof comment: restrict to the countable atomic support, then collapse each singleton piece
    -- to the corresponding weighted atom.
    calc
      ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ)
          = ∫⁻ x, S.indicator (fun y : ℝ ↦ ENNReal.ofReal (y ^ (2 : ℕ))) x ∂(μ : Measure ℝ) := by
              exact lintegral_congr_ae hIndicator.symm
      _ = ∫⁻ x in S, ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ) := by
            rw [lintegral_indicator (Set.countable_range fun n : ℕ+ ↦ (n : ℝ)).measurableSet]
      _ = ∫⁻ x in ⋃ n : ℕ+, ({(n : ℝ)} : Set ℝ), ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ) := by
            simpa [S] using congrArg
              (fun T : Set ℝ ↦ ∫⁻ x in T, ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ))
              exercise1624CaseIIIRange_eq_iUnionSingleton
      _ = ∑' n : ℕ+, ∫⁻ x in ({(n : ℝ)} : Set ℝ), ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ) := by
            rw [MeasureTheory.lintegral_iUnion (fun _ ↦ measurableSet_singleton _) hSingletonPairwise]
      _ = ∑' n : ℕ+, ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ)) *
            (μ : Measure ℝ) ({(n : ℝ)} : Set ℝ) := by
            refine tsum_congr fun n ↦ ?_
            rw [mul_comm]
            simp
      _ = ∑' n : ℕ+, ENNReal.ofReal
            ((n : ℝ) ^ (2 : ℕ) * exercise1624CaseIIISingletonMass α β n) := by
            refine tsum_congr fun n ↦ ?_
            rw [hSingletonMassENN n]
            simpa [ENNReal.ofReal_mul, mul_comm]
  have hOddSquareTerm (k : ℕ) :
      f (2 * k + 1) =
        ENNReal.ofReal
          (exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ (α + 2)) := by
    have heven : Even (2 * k + 2) := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using even_two_mul (k + 1)
    have hstep : (2 * k + 1 + 1 : ℝ) = (2 * k + 2 : ℝ) := by ring
    simpa [f, Nat.succPNat_coe, heven, hstep] using
      congrArg ENNReal.ofReal
        (exercise1624CaseIIISquareWeightedSingletonMass_eq
          (α := α) (β := β) (n := Nat.succPNat (2 * k + 1)))
  have hEvenSquareTerm (k : ℕ) :
      f (2 * k) =
        ENNReal.ofReal
          (exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ (β + 2)) := by
    have hodd : ¬ Even (2 * k + 1) := Nat.not_even_two_mul_add_one k
    simpa [f, Nat.succPNat_coe, hodd] using
      congrArg ENNReal.ofReal
        (exercise1624CaseIIISquareWeightedSingletonMass_eq
          (α := α) (β := β) (n := Nat.succPNat (2 * k)))
  -- Proof comment: after shifting the `ℕ+` index to `ℕ`, split the singleton series into the odd
  -- and even subsequences and rewrite the square-weighted atoms with the exponent-shift owner.
  calc
    ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ)
        = ∑' n : ℕ, f n := by
            rw [hIntegralSeries]
            symm
            simpa [f, Nat.succPNat_coe] using
              (Equiv.pnatEquivNat.symm.tsum_eq
                (fun n : ℕ+ ↦
                  ENNReal.ofReal
                    ((n : ℝ) ^ (2 : ℕ) * exercise1624CaseIIISingletonMass α β n)))
    _ = ∑' k : ℕ, f (2 * k) + ∑' k : ℕ, f (2 * k + 1) := by
          symm
          exact tsum_even_add_odd ENNReal.summable ENNReal.summable
    _ =
        (∑' k : ℕ,
          ENNReal.ofReal
            (exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ (α + 2))) +
          ∑' k : ℕ,
            ENNReal.ofReal
              (exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ (β + 2)) := by
          rw [add_comm]
          congr 1
          · refine tsum_congr fun k ↦ ?_
            exact hOddSquareTerm k
          · refine tsum_congr fun k ↦ ?_
            exact hEvenSquareTerm k

/-- Helper for Exercise 16.2.4: in the strict Gaussian case-(iii) branch, the odd/even singleton
series has finite second moment, so the CLT-based Gaussian attraction bridge applies. -/
lemma exercise1624CaseIIIFiniteSecondMomentOfStrictGaussianBranch
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n)
    (hmax_lt : max α β < -3) :
    MemLp id 2 (μ : Measure ℝ) := by
  let c := exercise1624CaseIIINormalizationConstant α β
  have hα_tail : α + 2 < -1 := by
    have hα_le : α ≤ max α β := le_max_left α β
    linarith
  have hβ_tail : β + 2 < -1 := by
    have hβ_le : β ≤ max α β := le_max_right α β
    linarith
  have hEvenSummable :
      Summable (fun k : ℕ ↦ c * (2 * k + 2 : ℝ) ^ (α + 2)) := by
    simpa using
      (exercise1624_summableNatRpowAlongArithmetic
        (s := α + 2) hα_tail (a := 2) (b := 2) (by decide : 0 < 2)).mul_left c
  have hOddSummable :
      Summable (fun k : ℕ ↦ c * (2 * k + 1 : ℝ) ^ (β + 2)) := by
    simpa using
      (exercise1624_summableNatRpowAlongArithmetic
        (s := β + 2) hβ_tail (a := 2) (b := 1) (by decide : 0 < 2)).mul_left c
  have hSquareLIntegral_ne_top :
      ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂(μ : Measure ℝ) ≠ ⊤ := by
    rw [exercise1624CaseIIISquareLIntegral_eq_evenOddSeries hsupport hmass]
    have hc : 0 < c := by
      exact exercise1624CaseIIINormalizationConstant_pos hsupport hmass
    have hc_nonneg : 0 ≤ c := le_of_lt hc
    have hEvenNonneg (k : ℕ) : 0 ≤ c * (2 * k + 2 : ℝ) ^ (α + 2) := by
      exact mul_nonneg hc_nonneg (Real.rpow_nonneg (by positivity) _)
    have hOddNonneg (k : ℕ) : 0 ≤ c * (2 * k + 1 : ℝ) ^ (β + 2) := by
      exact mul_nonneg hc_nonneg (Real.rpow_nonneg (by positivity) _)
    let evenNN : ℕ → NNReal := fun k ↦
      Real.toNNReal
        (exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ (α + 2))
    let oddNN : ℕ → NNReal := fun k ↦
      Real.toNNReal
        (exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ (β + 2))
    have hEvenSummableNN : Summable (fun k : ℕ ↦ (evenNN k : ℝ)) := by
      simpa [evenNN, c, Real.toNNReal_of_nonneg, hEvenNonneg] using hEvenSummable
    have hOddSummableNN : Summable (fun k : ℕ ↦ (oddNN k : ℝ)) := by
      simpa [oddNN, c, Real.toNNReal_of_nonneg, hOddNonneg] using hOddSummable
    have hEvenTsum_ne_top :
        (∑' k : ℕ,
          ENNReal.ofReal
            (exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ (α + 2))) ≠ ⊤ := by
      have hNN :
          (fun k : ℕ ↦ (evenNN k : ENNReal)) =
            fun k : ℕ ↦
              ENNReal.ofReal
                (exercise1624CaseIIINormalizationConstant α β * (2 * k + 2 : ℝ) ^ (α + 2)) := by
        funext k
        simp [evenNN, ENNReal.ofReal, Real.toNNReal_of_nonneg, hEvenNonneg]
      simpa [hNN] using
        (ENNReal.tsum_coe_ne_top_iff_summable_coe
          (f := evenNN)).mpr hEvenSummableNN
    have hOddTsum_ne_top :
        (∑' k : ℕ,
          ENNReal.ofReal
            (exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ (β + 2))) ≠ ⊤ := by
      have hNN :
          (fun k : ℕ ↦ (oddNN k : ENNReal)) =
            fun k : ℕ ↦
              ENNReal.ofReal
                (exercise1624CaseIIINormalizationConstant α β * (2 * k + 1 : ℝ) ^ (β + 2)) := by
        funext k
        simp [oddNN, ENNReal.ofReal, Real.toNNReal_of_nonneg, hOddNonneg]
      simpa [hNN] using
        (ENNReal.tsum_coe_ne_top_iff_summable_coe
          (f := oddNN)).mpr hOddSummableNN
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact hEvenTsum_ne_top
    · exact hOddTsum_ne_top
  have hsq :
      Integrable (fun x : ℝ ↦ x ^ (2 : ℕ)) (μ : Measure ℝ) := by
    have hMeas :
        AEStronglyMeasurable (fun x : ℝ ↦ x ^ (2 : ℕ)) (μ : Measure ℝ) :=
      (measurable_id.pow_const 2).aestronglyMeasurable
    have hNonneg : 0 ≤ᵐ[(μ : Measure ℝ)] fun x : ℝ ↦ x ^ (2 : ℕ) :=
      Filter.Eventually.of_forall fun x ↦ by positivity
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        (μ := (μ : Measure ℝ))
        (f := fun x : ℝ ↦ x ^ (2 : ℕ))
        hMeas hNonneg).1 hSquareLIntegral_ne_top
  -- Proof comment: once the square moment is a finite sum of two `p`-series with exponents below
  -- `-1`, the standard `MemLp` bridge closes the strict Gaussian branch.
  exact
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (by simpa using hsq)

/-- Exercise 16.2.4, case (iii): if `μ` is exactly the source distribution on `ℕ` with odd/even
singleton masses given by `exercise1624CaseIIISingletonMass α β`, then `μ` lies in the domain of
attraction of a stable law with index `min (2, -max α β - 1)`. -/
-- TODO: use `hsupport` and `hmass` to identify the right tail with an odd/even power-law series,
-- then prove the corresponding Chapter 16 tail criterion and positive-tail-share limit.
theorem stableDomainOfAttractionExamples_iii
    {μ : ProbabilityMeasure ℝ} {α β : ℝ}
    (hα : α < -1) (hβ : β < -1)
    (hsupport :
      ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0)
    (hmass :
      ∀ n : ℕ+,
        ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
          exercise1624CaseIIISingletonMass α β n) :
    IsInDomainOfAttractionOfStableWithIndex μ (exercise1624StableIndex α β) := by
  -- Route correction: the case-(iii) proof should first normalize the two-sided tail to the
  -- right tail on the positive-integer support before any odd/even asymptotic splitting.
  have hShare : PositiveTailShareCriterion16_30 μ :=
    exercise1624CaseIIIPositiveTailShareCriterion hsupport hmass
  have hNotDirac : ∀ x : ℝ, μ ≠ diracProba x :=
    exercise1624CaseIIINotDirac hsupport hmass
  by_cases hidx_lt_two : exercise1624StableIndex α β < 2
  · have hidx_mem : exercise1624StableIndex α β ∈ Set.Ioo (0 : ℝ) 2 :=
      ⟨(exercise1624StableIndex_mem_Ioc hα hβ).1, hidx_lt_two⟩
    have hTail : TailCriterion16_29 μ (exercise1624StableIndex α β) :=
      exercise1624CaseIIIHeavyTailCriterion hα hβ hsupport hmass hidx_lt_two
    rcases stableDomainOfAttractionCriterion μ with ⟨_, _, hPartIII⟩
    unfold StableDomainOfAttractionCriterionPartIII at hPartIII
    have hPartIIIAtIndex :
        IsInDomainOfAttractionOfStableWithIndex μ (exercise1624StableIndex α β) ↔
          TailCriterion16_29 μ (exercise1624StableIndex α β) ∧
            PositiveTailShareCriterion16_30 μ := by
      apply hPartIII
      exact hidx_mem
    -- Proof comment: below the Gaussian cutoff, Part III now applies directly to the local
    -- tail criterion and the already proved positive-tail-share criterion.
    rcases hPartIIIAtIndex.2 ⟨hTail, hShare⟩ with ⟨ν, hμν, hνα⟩
    exact ⟨ν, hμν, hνα⟩
  · have hidx_eq_two : exercise1624StableIndex α β = 2 := by
      exact le_antisymm (exercise1624StableIndex_mem_Ioc hα hβ).2 (le_of_not_gt hidx_lt_two)
    by_cases hboundary : max α β = -3
    · have hTail : TailCriterion16_29 μ 2 :=
        exercise1624CaseIIIExactBoundaryTailCriterion hα hβ hsupport hmass hboundary
      rcases stableWithIndexTwo_ofTailCriterionTwo hNotDirac hTail with ⟨ν, hμν, hνtwo⟩
      -- Proof comment: at the exact `-3` boundary, the quadratic tail criterion gives the
      -- Gaussian attracting witness directly.
      simpa [hidx_eq_two] using ⟨ν, hμν, hνtwo⟩
    · have hmax_lt : max α β < -3 := by
        have hmax_le : max α β ≤ -3 := by
          by_contra hmax_gt
          have hraw_lt_two : -max α β - 1 < 2 := by
            linarith
          rw [exercise1624StableIndex_eq, min_eq_right (le_of_lt hraw_lt_two)] at hidx_eq_two
          linarith
        exact lt_of_le_of_ne hmax_le hboundary
      have hμ₂ : MemLp id 2 (μ : Measure ℝ) :=
        exercise1624CaseIIIFiniteSecondMomentOfStrictGaussianBranch hsupport hmass hmax_lt
      have hVar : Var[id; (μ : Measure ℝ)] ≠ 0 :=
        exercise1624VarianceNeZeroOfNotDirac hμ₂ hNotDirac
      -- Proof comment: away from the exact boundary, the discrete second moment is finite, so the
      -- proof switches to the CLT-based Gaussian attraction bridge.
      simpa [hidx_eq_two] using
        exercise1624GaussianAttractionOfFiniteVarianceLaw (μ := μ) hμ₂ hVar

/-- Summary for Exercise 16.2.4: for the three listed source laws, case (i) uses the source-faithful
surviving-tail index, case (iii) uses the heavier-tail index `min (2, -max α β - 1)`, and the
exponential law lies in the Gaussian domain of attraction. -/
theorem stableDomainOfAttractionExamples :
    (∀ {μ : ProbabilityMeasure ℝ} {ρ α β : ℝ},
      ρ ∈ Set.Icc (0 : ℝ) 1 →
        α < -1 →
          β < -1 →
            (μ : Measure ℝ) =
              volume.withDensity
                (fun x ↦ ENNReal.ofReal (exercise1624CaseIDensity ρ α β x)) →
              IsInDomainOfAttractionOfStableWithIndex μ (exercise1624CaseIStableIndex ρ α β)) ∧
      (∀ θ : ℝ, ∀ hθ : 0 < θ,
        IsInDomainOfAttractionOfStableWithIndex (exercise1624ExponentialLaw θ hθ) 2) ∧
      ∀ {μ : ProbabilityMeasure ℝ} {α β : ℝ},
        α < -1 →
          β < -1 →
            ((μ : Measure ℝ) (Set.range fun n : ℕ+ ↦ (n : ℝ))ᶜ).toReal = 0 →
              (∀ n : ℕ+,
                ((μ : Measure ℝ) ({(n : ℝ)} : Set ℝ)).toReal =
                  exercise1624CaseIIISingletonMass α β n) →
                IsInDomainOfAttractionOfStableWithIndex μ (exercise1624StableIndex α β) := by
  constructor
  · -- Proof comment: the first component is exactly case (i).
    intro μ ρ α β hρ hα hβ hμ
    exact stableDomainOfAttractionExamples_i hρ hα hβ hμ
  constructor
  · -- Proof comment: the second component is exactly case (ii).
    intro θ hθ
    exact stableDomainOfAttractionExamples_ii θ hθ
  · -- Proof comment: the third component is exactly case (iii).
    intro μ α β hα hβ hsupport hmass
    exact stableDomainOfAttractionExamples_iii hα hβ hsupport hmass

end MeasureTheory.ProbabilityMeasure
