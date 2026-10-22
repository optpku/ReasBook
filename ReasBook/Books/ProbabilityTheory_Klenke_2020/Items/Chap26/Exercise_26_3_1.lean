/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Example_26_11
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The Galton--Watson branching process started from `x` and driven by the offspring array `Y`.
The next generation is the sum of the offspring counts of the currently alive particles. -/
def branchingProcess (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ ↦ x
  | n + 1 => fun ω ↦ Finset.sum (Finset.range (branchingProcess x Y n ω)) (fun i ↦ Y n i ω)

-- Proof sketch: unfold the recursive definition of `branchingProcess` at time `0`.
/-- The branching process starts from the deterministic initial population `x`. -/
theorem branchingProcess_zero (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    branchingProcess x Y 0 = fun _ ↦ x := rfl

/-- Helper for Exercise 26.3.1: for a nonnegative state `x`, the Laplace factor
`exp (-(n x))` tends to the zero-indicator value as `n → ∞`. -/
theorem expNegNatMul_tendsto_zeroIndicator (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) * x))) atTop
      (nhds (if x = 0 then 1 else 0)) := by
  by_cases hx0 : x = 0
  · -- If `x = 0`, every Laplace factor is exactly `1`.
    simp [hx0]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * x) atTop atTop := by
      simpa using (tendsto_natCast_atTop_atTop.atTop_mul_const hxpos)
    -- For `x > 0`, the exponent tends to `-∞`, so the exponential tends to `0`.
    have hlim0 :
        Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) * x))) atTop (nhds (0 : ℝ)) := by
      have hneg : Tendsto (fun n : ℕ ↦ -((n : ℝ) * x)) atTop atBot := by
        exact tendsto_neg_atTop_atBot.comp hscaled
      exact Real.tendsto_exp_atBot.comp hneg
    simpa [hx0] using hlim0

/-- Helper for Exercise 26.3.1: along the natural Laplace parameters, the explicit CIR/Feller
branching Laplace transform converges to the extinction constant `exp (-2 z / (γ t))`. -/
theorem cirLaplaceTransform_nat_tendsto_extinctionConstant
    {γ z t : NNReal} (hγ : 0 < γ) (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ cirLaplaceTransform γ t z (n : ℝ)) atTop
      (nhds (Real.exp (-(2 * (z : ℝ)) / ((γ : ℝ) * (t : ℝ))))) := by
  have hd : (((γ : ℝ) / 2) * (t : ℝ)) ≠ 0 := by
    positivity
  have hratio :
      Tendsto
        (fun n : ℕ ↦ ((0 : ℝ) + (z : ℝ) * n) / (1 + (((γ : ℝ) / 2) * (t : ℝ)) * n))
        atTop
        (nhds ((z : ℝ) / (((γ : ℝ) / 2) * (t : ℝ)))) := by
    -- Rewrite the rational factor into the standard affine-over-affine limit template.
    simpa using
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (0 : ℝ) 1 (z : ℝ) hd)
  have hexp :
      Tendsto
        (fun n : ℕ ↦
          Real.exp (-(((0 : ℝ) + (z : ℝ) * n) / (1 + (((γ : ℝ) / 2) * (t : ℝ)) * n))))
        atTop
        (nhds (Real.exp (-((z : ℝ) / (((γ : ℝ) / 2) * (t : ℝ)))))) := by
    -- Continuity of `exp` transfers the scalar limit to the explicit Laplace formula.
    exact Real.continuous_exp.continuousAt.tendsto.comp hratio.neg
  have hexp_eq :
      Real.exp (-((z : ℝ) / (((γ : ℝ) / 2) * (t : ℝ)))) =
        Real.exp (-(2 * (z : ℝ)) / ((γ : ℝ) * (t : ℝ))) := by
    have hγ0 : (γ : ℝ) ≠ 0 := by positivity
    have ht0 : (t : ℝ) ≠ 0 := by positivity
    congr 1
    field_simp [hγ0, ht0]
  -- Rewrite `cirLaplaceTransform` into the same scalar normal form and conclude.
  have hrewrite :
      (fun n : ℕ ↦ cirLaplaceTransform γ t z (n : ℝ)) =ᶠ[atTop]
        (fun n ↦
          Real.exp (-(((0 : ℝ) + (z : ℝ) * n) / (1 + (((γ : ℝ) / 2) * (t : ℝ)) * n)))) := by
    exact Filter.Eventually.of_forall fun n ↦ by
      dsimp
      rw [cirLaplaceTransform_apply]
      ring
  have hexp' :
      Tendsto
        (fun n : ℕ ↦
          Real.exp (-(((0 : ℝ) + (z : ℝ) * n) / (1 + (((γ : ℝ) / 2) * (t : ℝ)) * n))))
        atTop
        (nhds (Real.exp (-(2 * (z : ℝ)) / ((γ : ℝ) * (t : ℝ))))) := by
    simpa [hexp_eq] using hexp
  exact Tendsto.congr' hrewrite.symm hexp'

/-- Helper for Exercise 26.3.1: the real-valued probability generating function attached to a law
on `ℕ`. -/
noncomputable def probabilityGeneratingFunctionReal (p : PMF ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, (p n).toReal * s ^ n

/-- Helper for Exercise 26.3.1: the real-valued pgf unfolds to its defining power series. -/
theorem probabilityGeneratingFunctionReal_apply (p : PMF ℕ) (s : ℝ) :
    probabilityGeneratingFunctionReal p s =
      ∑' n : ℕ, (p n).toReal * s ^ n := rfl

/-- Helper for Exercise 26.3.1: on `[0,1]`, the subtype-valued pgf is the real-valued pgf with
the same series. -/
theorem probabilityGeneratingFunction_coe_eq_real (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction p z : ℝ) = probabilityGeneratingFunctionReal p z := by
  rw [probabilityGeneratingFunction_apply, probabilityGeneratingFunctionReal_apply]

/-- Helper for Exercise 26.3.1: the critical geometric offspring distribution, i.e. the
geometric law with success probability `1 / 2`. -/
noncomputable abbrev criticalGeometricOffspringPMF : PMF ℕ :=
  geometricPMF
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)

/-- Helper for Exercise 26.3.1: on `[0,1]`, the critical geometric offspring pgf is the
fractional-linear map `s ↦ 1 / (2 - s)`. -/
lemma criticalGeometricOffspringPgf_eq_fractionalLinear {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal criticalGeometricOffspringPMF s = 1 / (2 - s) := by
  have hs_div_two_nonneg : 0 ≤ s / 2 := by
    nlinarith [hs.1]
  have hs_div_two_lt_one : s / 2 < 1 := by
    nlinarith [hs.2]
  have hratio : |s / 2| < 1 := by
    simpa [abs_of_nonneg hs_div_two_nonneg] using hs_div_two_lt_one
  have hs_ne : s ≠ 2 := by
    nlinarith [hs.2]
  -- Proof comment: rewrite the pgf series as a geometric series with ratio `s / 2`.
  rw [probabilityGeneratingFunctionReal_apply]
  calc
    ∑' n : ℕ, (criticalGeometricOffspringPMF n).toReal * s ^ n
        = ∑' n : ℕ, (1 / 2 : ℝ) * ((s / 2) ^ n) := by
            refine tsum_congr fun n ↦ ?_
            have hmass :
                (criticalGeometricOffspringPMF n).toReal = ((1 / 2 : ℝ) ^ n) * (1 / 2) := by
              rw [criticalGeometricOffspringPMF, geometricPMF]
              change (ENNReal.ofReal (geometricPMFReal (1 / 2 : ℝ) n)).toReal =
                ((1 / 2 : ℝ) ^ n) * (1 / 2)
              rw [ENNReal.toReal_ofReal]
              · have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
                  norm_num
                rw [geometricPMFReal, hhalf]
              · exact geometricPMFReal_nonneg (show 0 < (1 / 2 : ℝ) by norm_num)
                  (show (1 / 2 : ℝ) ≤ 1 by norm_num)
            rw [hmass]
            have hpow : ((1 / 2 : ℝ) ^ n) * s ^ n = (s / 2) ^ n := by
              rw [← mul_pow]
              ring_nf
            calc
              (((1 / 2 : ℝ) ^ n) * (1 / 2)) * s ^ n
                  = (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ n) * s ^ n) := by ring
              _ = (1 / 2 : ℝ) * (s / 2) ^ n := by rw [hpow]
    _ = (1 / 2 : ℝ) * ∑' n : ℕ, (s / 2) ^ n := by rw [tsum_mul_left]
    _ = (1 / 2 : ℝ) * (1 - s / 2)⁻¹ := by
          rw [(hasSum_geometric_of_abs_lt_one hratio).tsum_eq]
    _ = 1 / (2 - s) := by
          field_simp [hs_ne]

/-- Helper for Exercise 26.3.1: the `n`th iterate of the critical geometric offspring pgf at
`0` is the ratio `n / (n + 1)`. -/
theorem criticalGeometricIterate_zero_eq_ratio (n : ℕ) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) 0 =
      (n : ℝ) / ((n : ℝ) + 1) := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth iterate is the identity, so both sides are `0`.
      simp
  | succ n ih =>
      have hs : ((n : ℝ) / ((n : ℝ) + 1)) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · have hden : 0 < (n : ℝ) + 1 := by positivity
          have hfrac : (n : ℝ) / ((n : ℝ) + 1) = 1 - 1 / ((n : ℝ) + 1) := by
            field_simp [hden.ne']
            ring
          rw [hfrac]
          nlinarith [show 0 ≤ 1 / ((n : ℝ) + 1) by positivity]
      -- Proof comment: evaluate one more iterate by the fractional-linear pgf formula and then
      -- normalize the resulting rational identity.
      rw [Function.iterate_succ_apply', ih, criticalGeometricOffspringPgf_eq_fractionalLinear hs]
      have hden : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hden' : ((n : ℝ) + 2) ≠ 0 := by positivity
      have hfrac :
          (2 : ℝ) - (n : ℝ) / ((n : ℝ) + 1) = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
        field_simp [hden]
        ring
      rw [hfrac]
      have htwo : (n : ℝ) + 2 = (n : ℝ) + 1 + 1 := by ring
      simp [htwo]

/-- Helper for Exercise 26.3.1: the `x`-fold offspring law obtained by convolving the
one-particle offspring distribution `q` exactly `x` times. -/
def branchingOffspringPMF (q : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | n + 1 =>
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l)

-- Proof sketch: unfold the recursive definition of `branchingOffspringPMF` at `0`.
/-- The zeroth offspring convolution is the Dirac mass at `0`. -/
theorem branchingOffspringPMF_zero (q : PMF ℕ) :
    branchingOffspringPMF q 0 = PMF.pure 0 := by
  rfl

-- Proof sketch: unfold the recursive definition at `n + 1`.
/-- The successor step in the offspring-convolution recursion appends one more offspring law. -/
theorem branchingOffspringPMF_succ (q : PMF ℕ) (n : ℕ) :
    branchingOffspringPMF q (n + 1) =
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l) := by
  rfl

/-- Helper for Exercise 26.3.1: the singleton mass of a convolution on `ℕ` is the finite
antidiagonal sum of the singleton masses of its two factors. -/
theorem convolutionApplySingletonEqSumAntidiagonal
    {μ ν : Measure ℕ} [SFinite μ] [SFinite ν] (n : ℕ) :
    (μ ∗ ν) ({n} : Set ℕ) =
      ∑ p ∈ Finset.antidiagonal n, μ ({p.1} : Set ℕ) * ν ({p.2} : Set ℕ) := by
  -- Proof comment: rewrite convolution as the pushforward of the product law along addition.
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton n)]
  have hpreimage :
      (fun z : ℕ × ℕ ↦ z.1 + z.2) ⁻¹' ({n} : Set ℕ) = ↑(Finset.antidiagonal n) := by
    ext z
    simp [Finset.mem_antidiagonal]
  rw [hpreimage, ← MeasureTheory.sum_measure_singleton (μ := μ.prod ν)
    (s := Finset.antidiagonal n)]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsingleton :
      ({p} : Set (ℕ × ℕ)) = ({p.1} : Set ℕ) ×ˢ ({p.2} : Set ℕ) := by
    ext z
    rcases z with ⟨a, b⟩
    cases p
    simp
  rw [hsingleton]
  exact Measure.prod_prod (μ := μ) (ν := ν) ({p.1} : Set ℕ) ({p.2} : Set ℕ)

/-- Helper for Exercise 26.3.1: convolving the `n`-fold offspring law with one more copy of `q`
matches the recursive successor law. -/
theorem branchingOffspringPMF_toMeasure_succ (q : PMF ℕ) (n : ℕ) :
    ((branchingOffspringPMF q n).toMeasure ∗ q.toMeasure) =
      (branchingOffspringPMF q (n + 1)).toMeasure := by
  refine Measure.ext_of_singleton fun k ↦ ?_
  -- Proof comment: on the discrete state space `ℕ`, it is enough to compare singleton masses.
  rw [convolutionApplySingletonEqSumAntidiagonal]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b ↦
      (branchingOffspringPMF q n).toMeasure ({a} : Set ℕ) * q.toMeasure ({b} : Set ℕ)) k]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [branchingOffspringPMF_succ, PMF.bind_apply]
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    have hak : a ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    congr 1
    rw [← PMF.toMeasure_apply_singleton
      (q.map (fun l : ℕ ↦ a + l)) k (measurableSet_singleton k)]
    rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton k)]
    have hpre : (fun l : ℕ ↦ a + l) ⁻¹' ({k} : Set ℕ) = {k - a} := by
      ext l
      simp
      omega
    rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (k - a))]
  · intro a ha
    have hka : k < a := by
      have hnot : ¬ a < k + 1 := by
        simpa using ha
      omega
    have hzero : (q.map (fun l : ℕ ↦ a + l)) k = 0 := by
      rw [← PMF.toMeasure_apply_singleton
        (q.map (fun l : ℕ ↦ a + l)) k (measurableSet_singleton k)]
      rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton k)]
      have hpre : (fun l : ℕ ↦ a + l) ⁻¹' ({k} : Set ℕ) = ∅ := by
        ext l
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro h
        exact (Nat.not_le_of_gt hka) <| h ▸ Nat.le_add_right a l
      simp [hpre]
    simp [hzero]

/-- Helper for Exercise 26.3.1: the zero-mass of the `m`-fold offspring convolution is the `m`th
power of the zero-offspring mass. -/
theorem branchingOffspringPMF_zeroMass_eq_pow (q : PMF ℕ) (m : ℕ) :
    branchingOffspringPMF q m 0 = (q 0) ^ m := by
  induction m with
  | zero =>
      -- Proof comment: the zeroth offspring convolution is the Dirac mass at `0`.
      simp [branchingOffspringPMF_zero]
  | succ m ih =>
      -- Proof comment: to end at total offspring `0`, both the previous partial total and the new
      -- offspring count must already be `0`.
      rw [branchingOffspringPMF_succ, PMF.bind_apply, tsum_eq_single 0]
      · rw [← PMF.toMeasure_apply_singleton
          (q.map (fun l : ℕ ↦ 0 + l)) 0 (measurableSet_singleton 0)]
        rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton 0)]
        have hpre :
            (fun l : ℕ ↦ 0 + l) ⁻¹' ({0} : Set ℕ) = {0} := by
          ext l
          simp
        rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton 0)]
        calc
          branchingOffspringPMF q m 0 * q 0 = (q 0) ^ m * q 0 := by rw [ih]
          _ = (q 0) ^ (m + 1) := by rw [pow_succ', mul_comm]
      · intro k hk
        have hmap_zero : q.map (fun l : ℕ ↦ k + l) 0 = 0 := by
          rw [← PMF.toMeasure_apply_singleton
            (q.map (fun l : ℕ ↦ k + l)) 0 (measurableSet_singleton 0)]
          rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton 0)]
          have hpre :
              (fun l : ℕ ↦ k + l) ⁻¹' ({0} : Set ℕ) = ∅ := by
            ext l
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
            constructor
            · intro h
              omega
            · intro h
              exact False.elim h
          simp [hpre]
        simp [hmap_zero]

/-- Helper for Exercise 26.3.1: a finite sum of offspring variables in one fixed generation has
the recursive convolution law determined by `branchingOffspringPMF`. -/
theorem offspringRowSum_hasLaw
    [MeasurableSpace Ω] (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n m : ℕ) :
    HasLaw (fun ω ↦ Finset.sum (Finset.range m) (fun i ↦ Y n i ω))
      (branchingOffspringPMF q m).toMeasure (P : Measure Ω) := by
  induction m with
  | zero =>
      -- Proof comment: the empty offspring sum is the constant zero random variable.
      refine HasLaw.mk aemeasurable_const ?_
      ext s hs
      simp [branchingOffspringPMF_zero, PMF.toMeasure_pure]
  | succ m ih =>
      let rowSum : Ω → ℕ := fun ω ↦ Finset.sum (Finset.range m) (fun j ↦ Y n j ω)
      have hrowSum_eq : (∑ j ∈ Finset.range m, Y n j) = rowSum := by
        funext ω
        simp [rowSum]
      have hrow_indep : iIndepFun (fun i : ℕ ↦ Y n i) (P : Measure Ω) :=
        hY_indep.precomp (g := fun i : ℕ ↦ (n, i)) <| by
          intro i j hij
          simpa using congrArg Prod.snd hij
      have hsum_indep_base :
          IndepFun (∑ j ∈ Finset.range m, Y n j) (Y n m) (P : Measure Ω) :=
        by
          exact
          (hrow_indep.indepFun_sum_range_succ₀
            (fun i ↦ (hY_law n i).aemeasurable) m)
      have hsum_indep :
          IndepFun rowSum (Y n m) (P : Measure Ω) :=
        hsum_indep_base.congr (Filter.EventuallyEq.of_eq hrowSum_eq) Filter.EventuallyEq.rfl
      have ihRow :
          HasLaw rowSum (branchingOffspringPMF q m).toMeasure (P : Measure Ω) := by
        simpa [rowSum] using ih
      have hstep :
          HasLaw (fun ω ↦ rowSum ω + Y n m ω)
            (((branchingOffspringPMF q m).toMeasure) ∗ q.toMeasure) (P : Measure Ω) :=
        hsum_indep.hasLaw_add ihRow (hY_law n m)
      -- Proof comment: append one more independent offspring variable and normalize the
      -- resulting convolution with the recursive PMF law.
      simpa [rowSum, Finset.sum_range_succ, branchingOffspringPMF_toMeasure_succ] using hstep

/-- Helper for Exercise 26.3.1: the branching-process transition matrix
`p(x,y) = branchingOffspringPMF q x y`. -/
def branchingTransitionMatrix (q : PMF ℕ) : ℕ → ℕ → ENNReal :=
  fun x y ↦ branchingOffspringPMF q x y

/-- Evaluating the branching transition matrix at `(x,y)` is the corresponding offspring-convolution
mass. -/
theorem branchingTransitionMatrix_apply (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionMatrix q x y = branchingOffspringPMF q x y := rfl

/-- Helper for Exercise 26.3.1: the indicator of the extinction event integrates to the real-valued
measure of that event. -/
theorem extinctionIndicatorIntegral_eq_realMeasure
    [MeasurableSpace Ω] (μ : Measure Ω) (Zt : Ω → NNReal)
    (hA_nullMeas : NullMeasurableSet {ω | Zt ω = 0} μ) :
    ∫ ω, (if Zt ω = 0 then 1 else 0 : ℝ) ∂μ = μ.real {ω | Zt ω = 0} := by
  -- Proof comment: rewrite the indicator function as a set indicator and then use the standard
  -- set-integral formula for the constant integrand `1`.
  calc
    ∫ ω, (if Zt ω = 0 then 1 else 0 : ℝ) ∂μ
        = ∫ ω, Set.indicator {ω | Zt ω = 0} (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            by_cases hω : Zt ω = 0 <;> simp [hω]
    _ = ∫ ω in {ω | Zt ω = 0}, (1 : ℝ) ∂μ := by
          rw [MeasureTheory.integral_indicator₀ hA_nullMeas]
    _ = μ.real {ω | Zt ω = 0} := by
          rw [MeasureTheory.setIntegral_const]
          simp

section Measurable

variable [MeasurableSpace Ω]

-- Proof sketch: use the canonical CIR Laplace transform `cirLaplaceTransform γ t z` from
-- Example 26.11 for the one-time marginal `Zt` under the one-time law `Pz`, send the Laplace
-- parameter to `+∞`, and identify the limit of `E[e^{-λ Zt}]` with the extinction probability
-- `Pz[Zt = 0]`.
/-- First part of Exercise 26.3.1: if the solution of
`dZ_t = sqrt (γ Z_t) dW_t` started from `z` has the explicit CIR/Feller branching
Laplace transform, then its extinction probability at time `t` is
`exp (-2 z / (γ t))`. -/
theorem fellerBranchingDiffusion_extinctionProbability_eq
    (Pz : ProbabilityMeasure Ω) (Zt : Ω → NNReal)
    {γ z t : NNReal} (hγ : 0 < γ) (ht : 0 < t)
    (hLaplace : ∀ l : NNReal,
      ∫ ω, Real.exp (-((l : ℝ) * (Zt ω : ℝ))) ∂(Pz : Measure Ω) =
        cirLaplaceTransform γ t z l) :
    (Pz : Measure Ω) {ω | Zt ω = 0} =
      ENNReal.ofReal (Real.exp (-(2 * (z : ℝ)) / ((γ : ℝ) * (t : ℝ)))) := by
  let μ : Measure Ω := (Pz : Measure Ω)
  let A : Set Ω := {ω | Zt ω = 0}
  let F : ℕ → Ω → ℝ := fun n ω ↦ Real.exp (-((n : ℝ) * (Zt ω : ℝ)))
  have hF1_int : Integrable (F 1) μ := by
    by_contra hF1_notInt
    have h1 : ∫ ω, F 1 ω ∂μ = cirLaplaceTransform γ t z 1 := by
      simpa [F, μ] using hLaplace 1
    rw [MeasureTheory.integral_undef hF1_notInt] at h1
    rw [cirLaplaceTransform_apply] at h1
    exact (Real.exp_ne_zero _ ) h1.symm
  have hZt_meas :
      AEMeasurable (fun ω ↦ (Zt ω : ℝ)) μ := by
    have hExp_meas : AEMeasurable (F 1) μ := by
      exact hF1_int.aemeasurable
    have hExp_meas' :
        AEMeasurable (fun ω ↦ Real.exp ((-1 : ℝ) * (Zt ω : ℝ))) μ := by
      simpa [F] using hExp_meas
    -- Recover measurability of `Zt` from measurability of `exp (-Zt)`.
    exact
      Real.aemeasurable_of_aemeasurable_exp_mul
        (μ := μ) (f := fun ω ↦ (Zt ω : ℝ)) (t := (-1 : ℝ)) (by norm_num) hExp_meas'
  have hA_nullMeas : NullMeasurableSet A μ := by
    -- The extinction event is the preimage of `{0}` under the almost everywhere measurable state.
    simpa [A, Set.preimage, NNReal.coe_eq_zero] using
      hZt_meas.nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ))
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    have hFn_meas : AEMeasurable (F n) μ := by
      simpa [F, mul_comm, mul_left_comm, mul_assoc] using
        (hZt_meas.const_mul (-(n : ℝ))).exp
    exact hFn_meas.aestronglyMeasurable
  have hBound_int : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := by
    simp [μ]
  have hBound : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with ω
    have hnonneg : 0 ≤ F n ω := by
      exact (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hnonneg]
    have hle0 : -((n : ℝ) * (Zt ω : ℝ)) ≤ 0 := by
      have hmul_nonneg : 0 ≤ (n : ℝ) * (Zt ω : ℝ) := by
        positivity
      exact neg_nonpos.mpr hmul_nonneg
    calc
      F n ω = Real.exp (-((n : ℝ) * (Zt ω : ℝ))) := rfl
      _ ≤ Real.exp 0 := by
        exact Real.exp_le_exp.mpr hle0
      _ = 1 := by simp
  have hPointwise :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop (nhds (if Zt ω = 0 then 1 else 0)) := by
    filter_upwards with ω
    -- Send the natural Laplace parameter to infinity pointwise.
    simpa [F, NNReal.coe_eq_zero] using
      expNegNatMul_tendsto_zeroIndicator (Zt ω : ℝ) (NNReal.coe_nonneg (Zt ω))
  have hIntegralLimit :
      Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) atTop
        (nhds (∫ ω, (if Zt ω = 0 then 1 else 0 : ℝ) ∂μ)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ (1 : ℝ)) hF_meas hBound_int hBound hPointwise
  have hLaplaceNat :
      ∀ n : ℕ, ∫ ω, F n ω ∂μ = cirLaplaceTransform γ t z (n : ℝ) := by
    intro n
    simpa [F, μ] using hLaplace (n : NNReal)
  have hExplicitLimit :
      Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) atTop
        (nhds (Real.exp (-(2 * (z : ℝ)) / ((γ : ℝ) * (t : ℝ))))) := by
    rw [show (fun n : ℕ ↦ ∫ ω, F n ω ∂μ) =
        fun n : ℕ ↦ cirLaplaceTransform γ t z (n : ℝ) by
      funext n
      exact hLaplaceNat n]
    exact cirLaplaceTransform_nat_tendsto_extinctionConstant hγ ht
  have hIndicatorIntegral :
      ∫ ω, (if Zt ω = 0 then 1 else 0 : ℝ) ∂μ = μ.real A := by
    simpa [A] using
      extinctionIndicatorIntegral_eq_realMeasure (Ω := Ω) (μ := μ) Zt hA_nullMeas
  have hMeasureReal :
      μ.real A = Real.exp (-(2 * (z : ℝ)) / ((γ : ℝ) * (t : ℝ))) := by
    -- The dominated-convergence limit agrees with the explicit CIR limit.
    exact hIndicatorIntegral.symm.trans (tendsto_nhds_unique hIntegralLimit hExplicitLimit)
  -- Convert the real-valued measure identity back to the original `ENNReal` statement.
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) ENNReal.ofReal_ne_top).1
  simpa [A, Measure.real_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hMeasureReal

/-- Helper for Exercise 26.3.1: the sigma-algebra generated by all offspring coordinates from
rows strictly before generation `n`. -/
@[reducible] private def offspringPast
    (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 < n},
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) Nat.instMeasurableSpace

/-- Helper for Exercise 26.3.1: the sigma-algebra generated by the whole offspring row at
generation `n`. -/
@[reducible] private def offspringRowSpace
    (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 = n},
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) Nat.instMeasurableSpace

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 26.3.1: enlarging the time cutoff enlarges the past-offspring
sigma-algebra. -/
private lemma offspringPast_mono {Y : ℕ → ℕ → Ω → ℕ} :
    Monotone (offspringPast (Ω := Ω) Y) := by
  intro n k hnk
  refine iSup_le ?_
  intro ij
  refine iSup_le ?_
  intro hij
  exact le_iSup_of_le ij <| le_iSup_of_le (lt_of_lt_of_le hij hnk) le_rfl

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 26.3.1: each generation size is measurable with respect to the offspring
rows revealed up to that generation. -/
private lemma branchingProcess_measurable_offspringPast_self
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    ∀ n, Measurable[offspringPast (Ω := Ω) Y n] (branchingProcess x Y n) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial population is the deterministic constant `x`.
      simp [branchingProcess_zero]
  | succ n ih =>
      have hT :
          Measurable[offspringPast (Ω := Ω) Y (n + 1)] (branchingProcess x Y n) :=
        ih.mono
          (offspringPast_mono (Ω := Ω) (Y := Y) (show n ≤ n + 1 by omega))
          le_rfl
      have hX :
          ∀ i, Measurable[offspringPast (Ω := Ω) Y (n + 1)] (Y n i) := by
        intro i
        refine measurable_iff_comap_le.mpr ?_
        exact le_iSup_of_le (n, i) <| le_iSup_of_le (by simp) le_rfl
      -- Proof comment: the next generation is the random sum of the fresh row over the current
      -- population, so measurability follows from the Chapter 3 random-sum API.
      simpa [branchingProcess, natRandomSum] using
        (@measurable_natRandomSum Ω (offspringPast (Ω := Ω) Y (n + 1))
          (branchingProcess x Y n) hT (fun i ↦ Y n i) hX)

/-- Helper for Exercise 26.3.1: any earlier generation is measurable with respect to any later
past-offspring sigma-algebra. -/
private lemma branchingProcess_measurable_offspringPast
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    ∀ {k n}, k ≤ n → Measurable[offspringPast (Ω := Ω) Y n] (branchingProcess x Y k) := by
  intro k n hkn
  -- Proof comment: monotonicity of `offspringPast` lets us weaken the cutoff from `k` to `n`.
  exact (branchingProcess_measurable_offspringPast_self (x := x) (Y := Y) k).mono
    (offspringPast_mono (Ω := Ω) (Y := Y) hkn) le_rfl

/-- Helper for Exercise 26.3.1: evaluating the pgf of a law on `ℕ` at `0` isolates the mass at
`0`. -/
private lemma probabilityGeneratingFunction_zero_eq_zeroMass (p : PMF ℕ) :
    (probabilityGeneratingFunction p ⟨0, by simp⟩ : ℝ) = (p 0).toReal := by
  -- Proof comment: in the pgf series, only the zeroth term survives because `0 ^ (k + 1) = 0`.
  rw [probabilityGeneratingFunction_apply, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 26.3.1: integrating `0 ^ branchingProcess N Y n` is the real-valued
probability of the extinction event `{branchingProcess N Y n = 0}`. -/
private lemma branchingProcessZeroPowIntegral_eq_extinctionReal
    [MeasurableSpace Ω] (μ : Measure Ω) (Zℕ : Ω → ℕ)
    (hA_nullMeas : NullMeasurableSet {ω | Zℕ ω = 0} μ) :
    ∫ ω, (0 : ℝ) ^ Zℕ ω ∂μ = μ.real {ω | Zℕ ω = 0} := by
  let Z : Ω → NNReal := fun ω ↦ Zℕ ω
  have hpow_indicator :
      ∫ ω, (0 : ℝ) ^ Zℕ ω ∂μ =
        ∫ ω, (if Z ω = 0 then 1 else 0 : ℝ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    by_cases hω : Zℕ ω = 0
    · simp [Z, hω]
    · rcases Nat.exists_eq_succ_of_ne_zero hω with ⟨k, hk⟩
      simp [Z, hk]
  calc
    ∫ ω, (0 : ℝ) ^ Zℕ ω ∂μ
        = ∫ ω, (if Z ω = 0 then 1 else 0 : ℝ) ∂μ := hpow_indicator
    _ = μ.real {ω | Z ω = 0} := by
          have hZ_nullMeas : NullMeasurableSet {ω | Z ω = 0} μ := by
            simpa [Z, NNReal.coe_eq_zero] using hA_nullMeas
          exact extinctionIndicatorIntegral_eq_realMeasure (Ω := Ω) (μ := μ) Z hZ_nullMeas
    _ = μ.real {ω | Zℕ ω = 0} := by
          congr 1
          ext ω
          simp [Z]

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 26.3.1: a `HasLaw` witness identifies the induced `ℕ`-valued `PMF`. -/
private lemma natRandomVariableLaw_eq_of_hasLaw
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : PMF ℕ) {X : Ω → ℕ}
    (hX_meas : Measurable X)
    (hX : HasLaw X p.toMeasure μ) :
    natRandomVariableLaw μ X hX_meas = p := by
  ext k
  rw [← PMF.toMeasure_apply_singleton
    (natRandomVariableLaw μ X hX_meas) k (measurableSet_singleton k)]
  rw [natRandomVariableLaw_toMeasure, hX.map_eq]
  exact PMF.toMeasure_apply_singleton p k (measurableSet_singleton k)

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 26.3.1: equal measurable `ℕ`-valued random variables induce the same law.
-/
private lemma natRandomVariableLaw_congr
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℕ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : X = Y) :
    natRandomVariableLaw μ X hX = natRandomVariableLaw μ Y hY := by
  subst hXY
  rfl

/-- Helper for Exercise 26.3.1: if all offspring coordinates are measurable, then every
generation size in the branching process is measurable. -/
private lemma branchingProcess_measurable
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (hY_meas : ∀ n i, Measurable (Y n i)) :
    ∀ n, Measurable (branchingProcess x Y n) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial generation is the constant population `x`.
      simp [branchingProcess_zero]
  | succ n ih =>
      -- Proof comment: with measurable current generation and measurable offspring row, the next
      -- generation is a measurable random sum.
      simpa [branchingProcess, natRandomSum] using
        measurable_natRandomSum (branchingProcess x Y n) ih (fun i ↦ Y n i) (hY_meas n)

/-- Helper for Exercise 26.3.1: replacing the offspring array by an almost surely equal array
does not change the branching process at any fixed time. -/
private lemma branchingProcess_congr_ae
    (μ : Measure Ω) (x : ℕ) {Y Y' : ℕ → ℕ → Ω → ℕ}
    (hY : ∀ n i, Y n i =ᵐ[μ] Y' n i) :
    ∀ n, branchingProcess x Y n =ᵐ[μ] branchingProcess x Y' n := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: time `0` ignores the offspring array entirely.
      refine Filter.EventuallyEq.of_eq ?_
      funext ω
      simp [branchingProcess]
  | succ n ih =>
      have hrow : ∀ᵐ ω ∂μ, ∀ i, Y n i ω = Y' n i ω := by
        exact ae_all_iff.2 fun i ↦ hY n i
      -- Proof comment: on the full-measure event where both the previous generation and the
      -- entire current row agree, the successor generations agree term by term.
      filter_upwards [ih, hrow] with ω hprev hrowω
      simp [branchingProcess, hprev, hrowω]

/-- Helper for Exercise 26.3.1: the fresh offspring row at generation `n` is independent of all
earlier offspring rows. -/
private lemma offspringRowSpace_indep_offspringPast
    (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ k i, Measurable (Y k i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (n : ℕ) :
    Indep (offspringRowSpace (Ω := Ω) Y n)
      (offspringPast (Ω := Ω) Y n) (P : Measure Ω) := by
  let mY : ℕ × ℕ → MeasurableSpace Ω := fun ij ↦
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) inferInstance
  have hDisjoint :
      Disjoint {ij : ℕ × ℕ | ij.1 = n} {ij : ℕ × ℕ | ij.1 < n} := by
    refine Set.disjoint_left.2 ?_
    intro ij hij hpast
    exact lt_irrefl n (hij ▸ hpast)
  -- Proof comment: the row with index `n` and the strict past use disjoint coordinates of the
  -- i.i.d. offspring array, so `indep_iSup_of_disjoint` applies directly.
  simpa [mY, offspringRowSpace, offspringPast] using
    (ProbabilityTheory.indep_iSup_of_disjoint
      (m := mY)
      (h_le := fun ij ↦ (hY_meas ij.1 ij.2).comap_le)
      (h_indep := hY_indep.iIndep)
      hDisjoint)

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 26.3.1: the full current offspring row is measurable with respect to the
sigma-algebra generated by that row. -/
private lemma rowSequence_comap_le_offspringRowSpace
    (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    MeasurableSpace.comap (fun ω ↦ fun i : ℕ ↦ Y n i ω) inferInstance ≤
      offspringRowSpace (Ω := Ω) Y n := by
  let _ : MeasurableSpace Ω := offspringRowSpace (Ω := Ω) Y n
  have hrow_meas :
      Measurable (fun ω ↦ fun i : ℕ ↦ Y n i ω) := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_iff_comap_le.mpr <|
      le_iSup_of_le (n, i) <| le_iSup_of_le (by simp) le_rfl
  simpa using hrow_meas.comap_le

/-- Helper for Exercise 26.3.1: the current population size is independent of the fresh offspring
row used to build the next generation. -/
private lemma branchingProcess_indep_currentOffspringRow
    (P : ProbabilityMeasure Ω) (N : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ k i, Measurable (Y k i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (n : ℕ) :
    IndepFun (branchingProcess N Y n) (fun ω ↦ fun i : ℕ ↦ Y n i ω) (P : Measure Ω) := by
  have hbase :
      Indep (offspringRowSpace (Ω := Ω) Y n)
        (offspringPast (Ω := Ω) Y n) (P : Measure Ω) :=
    offspringRowSpace_indep_offspringPast (Ω := Ω) P Y hY_meas hY_indep n
  have hproc :
      MeasurableSpace.comap (branchingProcess N Y n) inferInstance ≤
        offspringPast (Ω := Ω) Y n :=
    (branchingProcess_measurable_offspringPast_self (x := N) (Y := Y) n).comap_le
  have hrow :
      MeasurableSpace.comap (fun ω ↦ fun i : ℕ ↦ Y n i ω) inferInstance ≤
        offspringRowSpace (Ω := Ω) Y n :=
    rowSequence_comap_le_offspringRowSpace (Ω := Ω) Y n
  have hIndep :
      Indep (MeasurableSpace.comap (branchingProcess N Y n) inferInstance)
        (MeasurableSpace.comap (fun ω ↦ fun i : ℕ ↦ Y n i ω) inferInstance)
        (P : Measure Ω) := by
    have hproc_row :
        Indep (MeasurableSpace.comap (branchingProcess N Y n) inferInstance)
          (offspringRowSpace (Ω := Ω) Y n) (P : Measure Ω) := by
      exact (ProbabilityTheory.indep_of_indep_of_le_right hbase hproc).symm
    -- Proof comment: `branchingProcess N Y n` is measurable with respect to the past, while the
    -- full row map is measurable with respect to the fresh-row sigma-algebra.
    exact ProbabilityTheory.indep_of_indep_of_le_right hproc_row hrow
  exact (ProbabilityTheory.IndepFun_iff_Indep _ _ _).2 hIndep

/-- Helper for Exercise 26.3.1: one branching step composes the current generation pgf with the
common offspring pgf. -/
private lemma branchingProcessPgf_succ_eq_comp
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (N n : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ k i, Measurable (Y k i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ k i, HasLaw (Y k i) q.toMeasure (P : Measure Ω))
    (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction
        (natRandomVariableLaw (P : Measure Ω) (branchingProcess N Y (n + 1))
          (branchingProcess_measurable (x := N) (Y := Y) hY_meas (n + 1))) z : ℝ) =
      (probabilityGeneratingFunction
        (natRandomVariableLaw (P : Measure Ω) (branchingProcess N Y n)
          (branchingProcess_measurable (x := N) (Y := Y) hY_meas n))
        (probabilityGeneratingFunction q z) : ℝ) := by
  have hbranch_indep :
      IndepFun (branchingProcess N Y n) (fun ω ↦ fun i : ℕ ↦ Y n i ω) (P : Measure Ω) :=
    branchingProcess_indep_currentOffspringRow (Ω := Ω) P N Y hY_meas hY_indep n
  have hrow_indep : iIndepFun (fun i : ℕ ↦ Y n i) (P : Measure Ω) :=
    hY_indep.precomp (g := fun i : ℕ ↦ (n, i)) <| by
      intro i j hij
      simpa using congrArg Prod.snd hij
  have hrow_ident :
      ∀ i, IdentDistrib (Y n i) (Y n 0) (P : Measure Ω) (P : Measure Ω) := by
    intro i
    exact (hY_law n i).identDistrib (hY_law n 0)
  have hrow_law :
      natRandomVariableLaw (P : Measure Ω) (Y n 0) (hY_meas n 0) = q := by
    simpa using natRandomVariableLaw_eq_of_hasLaw
      (μ := (P : Measure Ω)) (p := q) (hX_meas := hY_meas n 0) (hX := hY_law n 0)
  have hpgf_comp :
      (probabilityGeneratingFunction
          (natRandomVariableLaw (P : Measure Ω)
            (natRandomSum (branchingProcess N Y n) (fun i : ℕ ↦ Y n i))
            (measurable_natRandomSum (branchingProcess N Y n)
              (branchingProcess_measurable (x := N) (Y := Y) hY_meas n)
              (fun i : ℕ ↦ Y n i) (hY_meas n))) z : ℝ) =
        (probabilityGeneratingFunction
          (natRandomVariableLaw (P : Measure Ω) (branchingProcess N Y n)
            (branchingProcess_measurable (x := N) (Y := Y) hY_meas n))
          (probabilityGeneratingFunction
            (natRandomVariableLaw (P : Measure Ω) (Y n 0) (hY_meas n 0)) z) : ℝ) := by
    exact
      probabilityGeneratingFunction_natRandomSum_eq_comp_of_indepFun_of_iIndepFun_of_identDistrib
        (P := (P : Measure Ω)) (T := branchingProcess N Y n)
        (branchingProcess_measurable (x := N) (Y := Y) hY_meas n)
        (X := fun i : ℕ ↦ Y n i) (hY_meas n)
        hbranch_indep hrow_indep hrow_ident z
  have hsucc_fun :
      branchingProcess N Y (n + 1) = natRandomSum (branchingProcess N Y n) (fun i : ℕ ↦ Y n i) := by
    funext ω
    simp [branchingProcess, natRandomSum_apply]
  -- Proof comment: rewrite the successor generation as a random sum over the fresh row and then
  -- invoke the Chapter 3 pgf theorem for independent random sums.
  calc
    (probabilityGeneratingFunction
        (natRandomVariableLaw (P : Measure Ω) (branchingProcess N Y (n + 1))
          (branchingProcess_measurable (x := N) (Y := Y) hY_meas (n + 1))) z : ℝ)
        =
          (probabilityGeneratingFunction
            (natRandomVariableLaw (P : Measure Ω)
              (natRandomSum (branchingProcess N Y n) (fun i : ℕ ↦ Y n i))
              (measurable_natRandomSum (branchingProcess N Y n)
                (branchingProcess_measurable (x := N) (Y := Y) hY_meas n)
                (fun i : ℕ ↦ Y n i) (hY_meas n))) z : ℝ) := by
            rw [natRandomVariableLaw_congr (μ := (P : Measure Ω))
              (branchingProcess_measurable (x := N) (Y := Y) hY_meas (n + 1))
              (measurable_natRandomSum (branchingProcess N Y n)
                (branchingProcess_measurable (x := N) (Y := Y) hY_meas n)
                (fun i : ℕ ↦ Y n i) (hY_meas n)) hsucc_fun]
    _ = (probabilityGeneratingFunction
          (natRandomVariableLaw (P : Measure Ω) (branchingProcess N Y n)
            (branchingProcess_measurable (x := N) (Y := Y) hY_meas n))
          (probabilityGeneratingFunction
            (natRandomVariableLaw (P : Measure Ω) (Y n 0) (hY_meas n 0)) z) : ℝ) := by
          exact hpgf_comp
    _ = (probabilityGeneratingFunction
          (natRandomVariableLaw (P : Measure Ω) (branchingProcess N Y n)
            (branchingProcess_measurable (x := N) (Y := Y) hY_meas n))
          (probabilityGeneratingFunction q z) : ℝ) := by
          rw [hrow_law]

/-- Helper for Exercise 26.3.1: the pgf of the `n`th generation equals the `N`th power of the
`n`-fold iterate of the offspring pgf. -/
private lemma branchingProcessPgf_eq_iteratePow
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (N n : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_meas : ∀ k i, Measurable (Y k i))
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ k i, HasLaw (Y k i) q.toMeasure (P : Measure Ω))
    (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction
        (natRandomVariableLaw (P : Measure Ω) (branchingProcess N Y n)
          (branchingProcess_measurable (x := N) (Y := Y) hY_meas n)) z : ℝ) =
      ((((probabilityGeneratingFunctionReal q)^[n]) (z : ℝ)) ^ N) := by
  induction n generalizing z with
  | zero =>
      -- Proof comment: at time `0` the branching process is identically equal to `N`.
      rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral
        (P := (P : Measure Ω)) (X := branchingProcess N Y 0)
        (branchingProcess_measurable (x := N) (Y := Y) hY_meas 0) z]
      simp [branchingProcess_zero]
  | succ n ih =>
      rw [branchingProcessPgf_succ_eq_comp (P := P) (q := q) (N := N) (n := n)
        (Y := Y) hY_meas hY_indep hY_law z]
      have hstep := ih (probabilityGeneratingFunction q z)
      -- Proof comment: the induction hypothesis is applied at the offspring pgf, and the real
      -- and subtype-valued pgfs agree on `[0,1]`.
      simpa [Function.iterate_succ_apply, probabilityGeneratingFunction_coe_eq_real] using hstep

-- Proof sketch: write the extinction-by-generation-`n` probability as the `N`th power of the
-- one-ancestor extinction approximation, apply Lemma 21.44 at `s = 0` to compute the `n`th pgf
-- iterate of the canonical critical geometric offspring law, and then use independence of the
-- `N` initial lineages.
/-- Exercise 26.3.1 (2): for a Galton--Watson branching process started from `N` particles with
critical geometric offspring law, the probability of being extinct by generation `n` is
`(n / (n + 1))^N`. -/
theorem criticalGeometric_galtonWatson_extinctByTime_eq
    (P : ProbabilityMeasure Ω) (N n : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law :
      ∀ k i, HasLaw (Y k i) criticalGeometricOffspringPMF.toMeasure (P : Measure Ω)) :
    ((P : Measure Ω) {ω | branchingProcess N Y n ω = 0}) =
      ENNReal.ofReal (((n : ℝ) / ((n : ℝ) + 1)) ^ N) := by
  let Ym : ℕ → ℕ → Ω → ℕ := fun k i ↦ (hY_law k i).aemeasurable.mk (Y k i)
  let z0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  have hYm_meas : ∀ k i, Measurable (Ym k i) := by
    intro k i
    simpa [Ym] using (hY_law k i).aemeasurable.measurable_mk
  have hYm_ae : ∀ k i, Ym k i =ᵐ[(P : Measure Ω)] Y k i := by
    intro k i
    simpa [Ym] using (hY_law k i).aemeasurable.ae_eq_mk.symm
  have hYm_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Ym ni.1 ni.2) (P : Measure Ω) := by
    exact hY_indep.congr fun ni ↦ (hYm_ae ni.1 ni.2).symm
  have hYm_law :
      ∀ k i, HasLaw (Ym k i) criticalGeometricOffspringPMF.toMeasure (P : Measure Ω) := by
    intro k i
    exact (hY_law k i).congr (hYm_ae k i)
  have hbranch_ae :
      branchingProcess N Ym n =ᵐ[(P : Measure Ω)] branchingProcess N Y n :=
    branchingProcess_congr_ae (μ := (P : Measure Ω)) (x := N)
      (Y := Ym) (Y' := Y) hYm_ae n
  have hEvent_eq :
      (P : Measure Ω) {ω | branchingProcess N Y n ω = 0} =
        (P : Measure Ω) {ω | branchingProcess N Ym n ω = 0} := by
    refine measure_congr ?_
    filter_upwards [hbranch_ae] with ω hω
    apply propext
    constructor
    · intro h
      exact hω.trans h
    · intro h
      exact hω.symm.trans h
  have hYm_proc_meas : Measurable (branchingProcess N Ym n) :=
    branchingProcess_measurable (x := N) (Y := Ym) hYm_meas n
  have hA_nullMeas :
      NullMeasurableSet {ω | branchingProcess N Ym n ω = 0} (P : Measure Ω) := by
    simpa using
      hYm_proc_meas.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton 0)
  have hnonneg : 0 ≤ (((n : ℝ) / ((n : ℝ) + 1)) ^ N) := by
    positivity
  have hreal :
      (P : Measure Ω).real {ω | branchingProcess N Ym n ω = 0} =
        (((n : ℝ) / ((n : ℝ) + 1)) ^ N) := by
    have hpgf :=
      branchingProcessPgf_eq_iteratePow (P := P) (q := criticalGeometricOffspringPMF)
        (N := N) (n := n) (Y := Ym) hYm_meas hYm_indep hYm_law z0
    -- Proof comment: evaluate the generic pgf identity at `0`, where the integral representation
    -- of the pgf becomes the extinction-event probability.
    rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral
        (P := (P : Measure Ω)) (X := branchingProcess N Ym n) hYm_proc_meas z0,
      branchingProcessZeroPowIntegral_eq_extinctionReal (Ω := Ω) (μ := (P : Measure Ω))
        (Zℕ := branchingProcess N Ym n) hA_nullMeas,
      criticalGeometricIterate_zero_eq_ratio] at hpgf
    simpa [z0] using hpgf
  -- Proof comment: convert the real-valued extinction identity back to the original `ENNReal`
  -- probability statement.
  rw [hEvent_eq]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (P : Measure Ω)
    {ω | branchingProcess N Ym n ω = 0}) ENNReal.ofReal_ne_top).1
  simpa [Measure.real_def, ENNReal.toReal_ofReal hnonneg] using hreal

end Measurable

end ProbabilityTheory
