/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Exercise_24_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

section Poisson

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type u} [AddCommMonoid E] [MeasurableSpace E] [PseudoMetricSpace E]
  [BorelSpace E] [MeasurableAdd₂ E] [LocallyCompactSpace E] [PolishSpace E]

-- Semantic recall: the source-faithful one-step object is a marked Poisson point process on
-- `E × E` with kernel `κ(x, ·) = δ_x ∗ ν`, whose second marginal gives the evolved system.

/-- Helper for Example 24.25: evaluating `poissonMeasure r` on a singleton returns the Poisson pmf
value at that index. -/
private lemma poissonMeasure_apply_singleton
    (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite the Poisson law as the measure associated to the corresponding pmf.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Example 24.25: identical distribution of finite tuples transfers independence once
the tuple laws are equal. -/
lemma iIndepFun_of_identDistrib_finiteTuple
    {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {U : Ω → ∀ i, β i} {V : Ω' → ∀ i, β i}
    (hUV : IdentDistrib U V P Q)
    (hV : iIndepFun (fun i ω ↦ V ω i) Q) :
    iIndepFun (fun i ω ↦ U ω i) P := by
  have hU_meas : ∀ i, AEMeasurable (fun ω ↦ U ω i) P := fun i ↦
    (measurable_pi_apply i).comp_aemeasurable hUV.aemeasurable_fst
  have hV_meas : ∀ i, AEMeasurable (fun ω ↦ V ω i) Q := fun i ↦
    (measurable_pi_apply i).comp_aemeasurable hUV.aemeasurable_snd
  have hcoord :
      ∀ i, Measure.map (fun ω ↦ U ω i) P = Measure.map (fun ω ↦ V ω i) Q := by
    intro i
    simpa [Function.comp] using (hUV.comp (measurable_pi_apply i)).map_eq
  -- Proof comment: finite-family independence is equivalent to the tuple law being the product of
  -- the coordinate laws, and the tuple law is already shared by `U` and `V`.
  rw [iIndepFun_iff_map_fun_eq_pi_map hU_meas]
  calc
    Measure.map (fun ω i ↦ U ω i) P = Measure.map (fun ω i ↦ V ω i) Q := hUV.map_eq
    _ = Measure.pi (fun i ↦ Measure.map (fun ω ↦ V ω i) Q) :=
      (iIndepFun_iff_map_fun_eq_pi_map hV_meas).1 hV
    _ = Measure.pi (fun i ↦ Measure.map (fun ω ↦ U ω i) P) := by
          simp [hcoord]

/-- Helper for Example 24.25: equality of the embedded Poisson laws forces equality of the finite
Poisson parameters. -/
lemma poissonRate_eq_of_embeddedPoissonLaw_eq
    {a b : ENNReal}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hmap :
      Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure a.toNNReal) =
        Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure b.toNNReal)) :
    a = b := by
  have hzero := congrArg (fun ρ : Measure ENNReal ↦ ρ ({0} : Set ENNReal)) hmap
  have hleft :
      Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure a.toNNReal) ({0} : Set ENNReal) =
        ENNReal.ofReal (Real.exp (-a.toReal)) := by
    rw [Measure.map_apply_of_aemeasurable
      (measurable_of_countable (fun n : ℕ ↦ (n : ENNReal))).aemeasurable
      (measurableSet_singleton 0)]
    have hpre :
        (fun n : ℕ ↦ (n : ENNReal)) ⁻¹' ({0} : Set ENNReal) = ({0} : Set ℕ) := by
      ext n
      simp
    rw [hpre, poissonMeasure_apply_singleton]
    have htoReal : ((a.toNNReal : NNReal) : ℝ) = a.toReal := by
      simpa using (ENNReal.coe_toNNReal_eq_toReal a)
    simpa [poissonPMFReal, htoReal]
  have hright :
      Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure b.toNNReal) ({0} : Set ENNReal) =
        ENNReal.ofReal (Real.exp (-b.toReal)) := by
    rw [Measure.map_apply_of_aemeasurable
      (measurable_of_countable (fun n : ℕ ↦ (n : ENNReal))).aemeasurable
      (measurableSet_singleton 0)]
    have hpre :
        (fun n : ℕ ↦ (n : ENNReal)) ⁻¹' ({0} : Set ENNReal) = ({0} : Set ℕ) := by
      ext n
      simp
    rw [hpre, poissonMeasure_apply_singleton]
    have htoReal : ((b.toNNReal : NNReal) : ℝ) = b.toReal := by
      simpa using (ENNReal.coe_toNNReal_eq_toReal b)
    simpa [poissonPMFReal, htoReal]
  have hexp :
      Real.exp (-a.toReal) = Real.exp (-b.toReal) := by
    exact (ENNReal.ofReal_eq_ofReal_iff (Real.exp_nonneg _) (Real.exp_nonneg _)).mp <|
      by simpa [hleft, hright] using hzero
  have htoReal : a.toReal = b.toReal := by
    have hneg : -a.toReal = -b.toReal := Real.exp_injective hexp
    linarith
  -- Proof comment: the rate is finite on both sides, so equality of the real parameters upgrades
  -- back to equality in `ENNReal`.
  exact (ENNReal.toReal_eq_toReal_iff' ha hb).mp htoReal

/-- Helper for Example 24.25: agreement on every bounded measurable set determines a measure on
the chapter ambient space. -/
lemma measure_eq_of_eqOnBoundedSets
    {μ ν : Measure E}
    (hEq :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → μ A = ν A) :
    μ = ν := by
  let K : CompactExhaustion E := CompactExhaustion.choice E
  ext A hA
  have hmono : Monotone fun n : ℕ ↦ A ∩ K n := by
    intro m n hmn x hx
    exact ⟨hx.1, K.subset hmn hx.2⟩
  have hUnion : ⋃ n, A ∩ K n = A := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hx⟩
      exact hx.1
    · intro hxA
      rcases K.exists_mem x with ⟨n, hxK⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨hxA, hxK⟩⟩
  calc
    μ A = μ (⋃ n, A ∩ K n) := by rw [hUnion]
    _ = ⨆ n, μ (A ∩ K n) := hmono.measure_iUnion
    _ = ⨆ n, ν (A ∩ K n) := by
          congr with n
          exact hEq (hA.inter (K.isCompact n).measurableSet)
            ((K.isCompact n).isBounded.subset Set.inter_subset_right)
    _ = ν (⋃ n, A ∩ K n) := by rw [hmono.measure_iUnion]
    _ = ν A := by rw [hUnion]

/-- Composing a measure `μ` with the random-walk kernel `κ(x, ·) = δ_x ∗ ν` gives the convolved
intensity `μ ∗ ν`. -/
theorem diracConvolutionKernel_comp_measure_eq_conv
    {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E} :
    dirac_convolution_kernel (ν : Measure E) ∘ₘ μ = μ ∗ (ν : Measure E) := by
  -- Proof comment: evaluate the composed translation kernel at the unique point of the constant
  -- kernel and reuse the Chap. 14 convolution identity.
  have hconst :=
    congrArg
      (fun κ : Kernel E E ↦ κ (0 : E))
      (dirac_convolution_kernel_comp_const_eq_const_conv (μ := μ) (ν := (ν : Measure E)))
  simpa [Kernel.comp_apply] using hconst

/-- Helper for Example 24.25: the random-walk kernel `x ↦ δ_x ∗ ν` is Markov when `ν` is a
probability measure, hence in particular `s`-finite. -/
private instance instIsMarkovKernelDiracConvolutionKernel
    (ν : Measure E) [IsProbabilityMeasure ν] :
    IsMarkovKernel (dirac_convolution_kernel ν) := by
  refine ⟨?_⟩
  intro x
  rw [dirac_convolution_kernel_apply]
  infer_instance

/-- Helper for Example 24.25: evaluating a Poisson point process on one measurable set has the
Laplace transform of the corresponding Poisson counting variable. -/
private lemma evalLaplace_of_isPoissonPointProcess
    {P : ProbabilityMeasure Ω} {ρ : Measure E} {Z : Ω → Measure E}
    (hZ : IsPoissonPointProcess ρ P Z)
    {A : Set E} (hA : MeasurableSet A) (t : ENNReal) :
    ∫ ω, ennrealExpNeg (t * Z ω A) ∂(P : Measure Ω) =
      ennrealExpNeg ((1 - ENNReal.ofReal (ennrealExpNeg t)) * ρ A) := by
  let f : NonnegativeMeasurableFunction E :=
    ⟨Set.indicator A (fun _ ↦ t), measurable_const.indicator hA⟩
  have hLintegral :
      (fun ω ↦ ∫⁻ x, f x ∂Z ω) =
        (fun ω ↦ t * Z ω A) := by
    funext ω
    -- Proof comment: the indicator test function is constantly `t` on `A`, so its lower integral
    -- is exactly `t` times the mass of `A`.
    change
      ∫⁻ x, Set.indicator A (fun _ ↦ t) x ∂Z ω =
        t * Z ω A
    rw [lintegral_indicator_const hA]
  have hExponent :
      ∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f x)) ∂ρ =
        (1 - ENNReal.ofReal (ennrealExpNeg t)) * ρ A := by
    have hIntegrand :
        (fun x : E ↦
          (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f x))) =
          Set.indicator A (fun _ ↦ 1 - ENNReal.ofReal (ennrealExpNeg t)) := by
      funext x
      by_cases hx : x ∈ A
      · simp [f, hx]
      · simp [f, hx, ennrealExpNeg]
    -- Proof comment: off `A` the exponent kernel vanishes, and on `A` it is the constant
    -- coefficient `1 - e^{-t}`.
    rw [hIntegrand, lintegral_indicator_const hA]
  have hRaw :=
    poisson_point_process_laplaceTransform P ρ Z hZ f
  calc
    ∫ ω, ennrealExpNeg (t * Z ω A) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (∫⁻ x, f x ∂Z ω) ∂(P : Measure Ω) := by
            refine integral_congr_ae ?_
            filter_upwards with ω
            simpa using (congrArg ennrealExpNeg (congrFun hLintegral ω)).symm
    _ = ennrealExpNeg
          (∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f x)) ∂ρ) := hRaw
    _ = ennrealExpNeg ((1 - ENNReal.ofReal (ennrealExpNeg t)) * ρ A) := by
          rw [hExponent]

/-- Helper for Example 24.25: if the same random measure is Poisson with intensities `ρ₁` and
`ρ₂`, then the two intensity measures agree on every bounded measurable set where `ρ₁` is finite.
-/
private lemma poissonIntensity_eq_on_boundedSet_of_sharedProcess
    {P : ProbabilityMeasure Ω} {ρ₁ ρ₂ : Measure E} {Z : Ω → Measure E}
    (hZ₁ : IsPoissonPointProcess ρ₁ P Z)
    (hZ₂ : IsPoissonPointProcess ρ₂ P Z)
    {A : Set E} (hA : MeasurableSet A) (_hA_bdd : Bornology.IsBounded A)
    (hρ₁ : ρ₁ A ≠ ⊤) :
    ρ₁ A = ρ₂ A := by
  let c : ENNReal := 1 - ENNReal.ofReal (ennrealExpNeg (1 : ENNReal))
  have hc :
      c = ENNReal.ofReal (1 - Real.exp (-(1 : ℝ))) := by
    -- Proof comment: at the fixed scale `t = 1`, the Laplace coefficient is the finite real
    -- number `1 - e^{-1}`.
    simp [c, ennrealExpNeg, ENNReal.ofReal_sub, Real.exp_nonneg]
  have hCoeffPos : 0 < 1 - Real.exp (-(1 : ℝ)) := by
    have hExpLtOne : Real.exp (-(1 : ℝ)) < 1 := by
      exact Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hc_ne_zero : c ≠ 0 := by
    rw [hc]
    simp [hCoeffPos.ne']
  have hc_ne_top : c ≠ ⊤ := by
    rw [hc]
    simp
  have hLaplaceEq :
      ennrealExpNeg (c * ρ₁ A) = ennrealExpNeg (c * ρ₂ A) := by
    -- Proof comment: both PPP structures give the same bounded-set Laplace transform because
    -- they are carried by the same random measure `Z`.
    calc
      ennrealExpNeg (c * ρ₁ A)
          = ∫ ω, ennrealExpNeg ((1 : ENNReal) * Z ω A) ∂(P : Measure Ω) := by
              symm
              simpa [c] using evalLaplace_of_isPoissonPointProcess hZ₁ hA (1 : ENNReal)
      _ = ennrealExpNeg (c * ρ₂ A) := by
            simpa [c] using evalLaplace_of_isPoissonPointProcess hZ₂ hA (1 : ENNReal)
  have hProd₁_ne_top : c * ρ₁ A ≠ ⊤ :=
    ENNReal.mul_ne_top hc_ne_top hρ₁
  have hLeftPos : 0 < ennrealExpNeg (c * ρ₁ A) := by
    -- Proof comment: the left-hand Poisson rate is finite by hypothesis, so its Laplace value is
    -- the strictly positive real exponential of a finite number.
    rw [ennrealExpNeg, if_neg hProd₁_ne_top]
    exact Real.exp_pos _
  have hProd₂_ne_top : c * ρ₂ A ≠ ⊤ := by
    intro hProd₂_top
    have hLeftZero : ennrealExpNeg (c * ρ₁ A) = 0 := by
      rw [hLaplaceEq, ennrealExpNeg, if_pos hProd₂_top]
    exact (ne_of_gt hLeftPos) hLeftZero
  have hρ₂ : ρ₂ A ≠ ⊤ := by
    exact (lt_top_iff_ne_top.mp (ENNReal.lt_top_of_mul_ne_top_right hProd₂_ne_top hc_ne_zero))
  have hProdToReal :
      (c * ρ₁ A).toReal = (c * ρ₂ A).toReal := by
    have hExpEq :
        Real.exp (-(c * ρ₁ A).toReal) =
          Real.exp (-(c * ρ₂ A).toReal) := by
      rwa [ennrealExpNeg, if_neg hProd₁_ne_top, ennrealExpNeg, if_neg hProd₂_ne_top] at hLaplaceEq
    have hNegEq : -(c * ρ₁ A).toReal = -(c * ρ₂ A).toReal :=
      Real.exp_injective hExpEq
    linarith
  have hc_toReal_pos : 0 < c.toReal := by
    have hCoeffNonneg : 0 ≤ 1 - Real.exp (-(1 : ℝ)) := le_of_lt hCoeffPos
    rw [hc, ENNReal.toReal_ofReal hCoeffNonneg]
    exact hCoeffPos
  have hRateToReal :
      (ρ₁ A).toReal = (ρ₂ A).toReal := by
    have hMulToReal :
        c.toReal * (ρ₁ A).toReal = c.toReal * (ρ₂ A).toReal := by
      simpa [ENNReal.toReal_mul] using hProdToReal
    exact mul_left_cancel₀ (ne_of_gt hc_toReal_pos) hMulToReal
  -- Proof comment: the shared Laplace transform fixes the bounded-set rate, and finiteness of the
  -- second rate follows because the common Laplace value is strictly positive.
  exact (ENNReal.toReal_eq_toReal_iff' hρ₁ hρ₂).mp hRateToReal

/-- Helper for Example 24.25: the Laplace scales `s_n = (n + 1)⁻¹` used to recover finiteness
from the Laplace transform. -/
private def invSuccScaleReal (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Helper for Example 24.25: the extended-real Laplace kernel `ennrealExpNeg` is measurable. -/
private theorem measurable_ennrealExpNeg : Measurable ennrealExpNeg := by
  classical
  have hcore : Measurable (fun t : ℝ≥0∞ ↦ Real.exp (-t.toReal)) :=
    Real.measurable_exp.comp ENNReal.measurable_toReal.neg
  -- Proof comment: the only exceptional point is `∞`, where `ennrealExpNeg` is patched to `0`.
  simpa [ennrealExpNeg, Set.piecewise] using
    (measurable_const.piecewise (measurableSet_singleton (⊤ : ℝ≥0∞)) hcore)

/-- Helper for Example 24.25: `ennrealExpNeg` is pointwise nonnegative. -/
private theorem ennrealExpNeg_nonneg (t : ℝ≥0∞) : 0 ≤ ennrealExpNeg t := by
  by_cases ht : t = ⊤
  · simp [ennrealExpNeg, ht]
  · simp [ennrealExpNeg, ht]
    exact le_of_lt (Real.exp_pos _)

/-- Helper for Example 24.25: `ennrealExpNeg` is bounded above by `1`. -/
private theorem ennrealExpNeg_le_one (t : ℝ≥0∞) : ennrealExpNeg t ≤ 1 := by
  by_cases ht : t = ⊤
  · simp [ennrealExpNeg, ht]
  · have hto : 0 ≤ t.toReal := ENNReal.toReal_nonneg
    have hle : Real.exp (-t.toReal) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    simpa [ennrealExpNeg, ht] using hle

/-- Helper for Example 24.25: the scaled Laplace kernel converges to the indicator of finiteness.
-/
private theorem ennrealExpNeg_invSucc_mul_tendsto_indicator (y : ℝ≥0∞) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y))
      Filter.atTop (nhds (if y = ⊤ then (0 : ℝ) else 1)) := by
  by_cases hy : y = ⊤
  · have hconst :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          fun _ ↦ (0 : ℝ) := by
      funext n
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hs_pos : 0 < invSuccScaleReal n := by
        simpa [invSuccScaleReal] using one_div_pos.mpr hn
      have hs_pos' : 0 < ENNReal.ofReal (invSuccScaleReal n) := ENNReal.ofReal_pos.mpr hs_pos
      simp [hy, ennrealExpNeg, ne_of_gt hs_pos']
    rw [hconst]
    simp [hy]
  · have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
      change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul :
        Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * y.toReal) Filter.atTop
          (nhds (0 * y.toReal)) := by
      exact hs.mul tendsto_const_nhds
    have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
      Real.continuous_exp.comp continuous_neg
    have hexp :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) Filter.atTop
          (nhds (Real.exp (-(0 * y.toReal)))) := by
      exact hcont.continuousAt.tendsto.comp hmul
    have hrewrite :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) := by
      funext n
      have hmul_ne_top : ENNReal.ofReal (invSuccScaleReal n) * y ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp [invSuccScaleReal]) hy
      have hs_nonneg : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
      change Real.exp (-((ENNReal.ofReal (invSuccScaleReal n)).toReal * y.toReal)) = _
      rw [ENNReal.toReal_ofReal hs_nonneg]
    rw [hrewrite]
    simpa [hy] using hexp

/-- Helper for Example 24.25: small-scale Laplace expectations converge to the probability that
an extended-real random variable is finite. -/
private theorem laplaceInvSuccTendstoMeasureFinite
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {Y : α → ℝ≥0∞}
    (hY : Measurable Y) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ a, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ∂μ)
      Filter.atTop (nhds (μ {a | Y a < ⊤}).toReal) := by
  let A : Set α := {a | Y a < ⊤}
  let G : α → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hF_meas :
      ∀ n, AEStronglyMeasurable
        (fun a ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)) μ := by
    intro n
    exact (measurable_ennrealExpNeg.comp (measurable_const.mul hY)).aestronglyMeasurable
  have hBound :
      ∀ n, ∀ᵐ a ∂μ, ‖ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with a
    have hnonneg : 0 ≤ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) :=
      ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ≤ 1 :=
      ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hLim :
      ∀ᵐ a ∂μ, Filter.Tendsto
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a))
        Filter.atTop (nhds (G a)) := by
    filter_upwards with a
    by_cases ha : Y a = ⊤
    · simpa [A, G, ha] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
    · have ha' : Y a < ⊤ := lt_top_iff_ne_top.mpr ha
      simpa [A, G, ha, ha'] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : α ↦ (1 : ℝ)) hF_meas (integrable_const 1) hBound hLim
  have hA : MeasurableSet A := measurableSet_lt hY measurable_const
  have hGIntegral : ∫ a, G a ∂μ = (μ A).toReal := by
    -- Proof comment: the integral of the indicator of the finiteness event is its probability.
    rw [integral_indicator hA]
    simp [A, Measure.real_def]
  simpa [A, G, hGIntegral] using hDCT

/-- Helper for Example 24.25: finiteness on one compact exhaustion implies local finiteness of the
underlying measure. -/
private theorem compactExhaustionFinite_isLocallyFiniteMeasure
    (ν : Measure E) (K : CompactExhaustion E) (hν : ∀ n, ν (K n) < ⊤) :
    IsLocallyFiniteMeasure ν := by
  refine ⟨fun y ↦ ?_⟩
  rcases K.exists_mem_nhds y with ⟨n, hKn⟩
  exact ⟨K n, hKn, hν n⟩

/-- Helper for Example 24.25: almost-sure finiteness on a compact exhaustion upgrades to almost-
sure local finiteness. -/
private theorem ae_isLocallyFiniteMeasure_of_compactExhaustionFinite
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E}
    (K : CompactExhaustion E)
    (hX : ∀ n, ∀ᵐ ω ∂(P : Measure Ω), X ω (K n) < ⊤) :
    ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω) := by
  filter_upwards [ae_all_iff.2 hX] with ω hω
  exact compactExhaustionFinite_isLocallyFiniteMeasure (X ω) K hω

/-- Helper for Example 24.25: evaluating the second marginal on a bounded measurable set has the
Poisson Laplace transform with rate `(μ ∗ ν) A`. -/
private lemma sndMarginalEvalLaplace
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    {A : Set E} (hA : MeasurableSet A) (t : ENNReal) :
    ∫ ω, ennrealExpNeg (t * Xkappa ω A) ∂(P : Measure Ω) =
      ennrealExpNeg ((1 - ENNReal.ofReal (ennrealExpNeg t)) * (μ ∗ (ν : Measure E)) A) := by
  letI : IsSFiniteKernel (dirac_convolution_kernel (ν : Measure E)) := inferInstance
  let f : NonnegativeMeasurableFunction (E × E) :=
    ⟨Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t),
      measurable_const.indicator (measurable_snd hA)⟩
  have hLintegral :
      (fun ω ↦ ∫⁻ z, f z ∂Xi ω) =
        (fun ω ↦ t * Xkappa ω A) := by
    funext ω
    -- Proof comment: the cylinder indicator only records atoms whose second coordinate lies in
    -- `A`, so the lower integral is the scaled second marginal of `Xi`.
    change
      ∫⁻ z, Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t) z ∂Xi ω =
        t * Xkappa ω A
    rw [lintegral_indicator_const (measurable_snd hA)]
    rw [hXkappa, Measure.snd_apply hA]
  have hExponent :
      ∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f z))
        ∂(μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) =
        (1 - ENNReal.ofReal (ennrealExpNeg t)) * (μ ∗ (ν : Measure E)) A := by
    have hIntegrand :
        (fun z : E × E ↦
          (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f z))) =
          Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ 1 - ENNReal.ofReal (ennrealExpNeg t)) := by
      funext z
      by_cases hz : z ∈ Prod.snd ⁻¹' A
      · simp [f, hz]
      · simp [f, hz, ennrealExpNeg]
    -- Proof comment: the exponent integrand is constant on the cylinder and vanishes off it, so
    -- only the second marginal intensity `(μ ∗ ν) A` remains.
    rw [hIntegrand, lintegral_indicator_const (measurable_snd hA)]
    rw [← Measure.snd_apply hA, Measure.snd_compProd, diracConvolutionKernel_comp_measure_eq_conv]
  have hRaw :=
    poisson_point_process_laplaceTransform P
      (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) Xi hXi f
  calc
    ∫ ω, ennrealExpNeg (t * Xkappa ω A) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (∫⁻ z, f z ∂Xi ω) ∂(P : Measure Ω) := by
            refine integral_congr_ae ?_
            filter_upwards with ω
            simpa using (congrArg ennrealExpNeg (congrFun hLintegral ω)).symm
    _ = ennrealExpNeg
          (∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f z))
            ∂(μ ⊗ₘ dirac_convolution_kernel (ν : Measure E))) := hRaw
    _ = ennrealExpNeg ((1 - ENNReal.ofReal (ennrealExpNeg t)) * (μ ∗ (ν : Measure E)) A) := by
          rw [hExponent]

/-- Helper for Example 24.25: the second marginal of the marked random-walk witness is a
boundedly finite random measure once `(μ ∗ ν)` is finite on bounded measurable sets. -/
private lemma sndMarginalIsBoundedlyFiniteRandomMeasure
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    (hμν_finite :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        (μ ∗ (ν : Measure E)) A ≠ ⊤) :
    IsBoundedlyFiniteRandomMeasure P Xkappa := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: `Xkappa` is the measurable second-marginal map applied to the measurable
    -- marked process `Xi`.
    simpa [hXkappa, Measure.snd] using
      (Measure.measurable_map Prod.snd measurable_snd).comp hXi.1.measurable
  · intro A hA hA_bdd
    let Y : Ω → ℝ≥0∞ := fun ω ↦ Xkappa ω A
    have hYMeas : Measurable Y := (Measure.measurable_coe hA).comp <| by
      simpa [hXkappa, Measure.snd] using
        (Measure.measurable_map Prod.snd measurable_snd).comp hXi.1.measurable
    have hLeft :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)
            ∂(P : Measure Ω))
          Filter.atTop (nhds ((P : Measure Ω) {ω | Y ω < ⊤}).toReal) := by
      simpa [Y] using
        laplaceInvSuccTendstoMeasureFinite (μ := (P : Measure Ω)) hYMeas
    have hsNonneg : ∀ n, 0 ≤ invSuccScaleReal n := by
      intro n
      have hn : 0 ≤ (n : ℝ) + 1 := by positivity
      simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
    have hCoeffNonneg : ∀ n, 0 ≤ 1 - Real.exp (-(invSuccScaleReal n)) := by
      intro n
      have hExpLeOne : Real.exp (-(invSuccScaleReal n)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith [hsNonneg n]
      linarith
    have hScaledEq :
        ∀ n,
          ((1 - ENNReal.ofReal
              (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
            (μ ∗ (ν : Measure E)) A) =
            ENNReal.ofReal
              ((1 - Real.exp (-(invSuccScaleReal n))) *
                ((μ ∗ (ν : Measure E)) A).toReal) := by
      intro n
      have hExpNonneg : 0 ≤ Real.exp (-(invSuccScaleReal n)) := Real.exp_nonneg _
      have hCoeffEq :
          1 - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n))) =
            ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n))) := by
        have hExpEval :
            ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)) =
              Real.exp (-(invSuccScaleReal n)) := by
          rw [ennrealExpNeg]
          simp [hsNonneg n]
        calc
          1 - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))
              = ENNReal.ofReal 1 - ENNReal.ofReal (Real.exp (-(invSuccScaleReal n))) := by
                  rw [hExpEval]
                  simp
          _ = ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n))) := by
                simpa using (ENNReal.ofReal_sub 1 hExpNonneg).symm
      rw [hCoeffEq]
      rw [ENNReal.ofReal_mul (hCoeffNonneg n), ENNReal.ofReal_toReal (hμν_finite hA hA_bdd)]
    have hRight :
        Filter.Tendsto
          (fun n : ℕ ↦
            ennrealExpNeg
              (((1 - ENNReal.ofReal
                  (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
                (μ ∗ (ν : Measure E)) A)))
          Filter.atTop (nhds 1) := by
      have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
        change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      have hKernelLimit :
          Filter.Tendsto
            (fun n : ℕ ↦
              (1 - Real.exp (-(invSuccScaleReal n))) *
                ((μ ∗ (ν : Measure E)) A).toReal)
            Filter.atTop (nhds 0) := by
        have hCont :
            Continuous fun r : ℝ ↦
              (1 - Real.exp (-r)) * ((μ ∗ (ν : Measure E)) A).toReal :=
          (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).mul continuous_const
        simpa using hCont.continuousAt.tendsto.comp hs
      have hRewrite :
          (fun n : ℕ ↦
            ennrealExpNeg
              (((1 - ENNReal.ofReal
                  (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
                (μ ∗ (ν : Measure E)) A))) =
            (fun n : ℕ ↦
              Real.exp
                (-((1 - Real.exp (-(invSuccScaleReal n))) *
                  ((μ ∗ (ν : Measure E)) A).toReal))) := by
        funext n
        rw [hScaledEq n, ennrealExpNeg]
        have hProdNonneg :
            0 ≤
              (1 - Real.exp (-(invSuccScaleReal n))) *
                ((μ ∗ (ν : Measure E)) A).toReal :=
          mul_nonneg (hCoeffNonneg n) ENNReal.toReal_nonneg
        simp [hProdNonneg]
      rw [hRewrite]
      have hContExp : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
        Real.continuous_exp.comp continuous_neg
      simpa using hContExp.continuousAt.tendsto.comp hKernelLimit
    have hLaplaceScaled :
        ∀ n,
          ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)
            ∂(P : Measure Ω) =
            ennrealExpNeg
              (((1 - ENNReal.ofReal
                  (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
                (μ ∗ (ν : Measure E)) A)) := by
      intro n
      simpa [Y] using
        sndMarginalEvalLaplace hXi hXkappa hA (ENNReal.ofReal (invSuccScaleReal n))
    have hLeftOne :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)
            ∂(P : Measure Ω))
          Filter.atTop (nhds 1) := by
      simpa [hLaplaceScaled] using hRight
    have hBOne : ((P : Measure Ω) {ω | Y ω < ⊤}).toReal = 1 :=
      tendsto_nhds_unique hLeft hLeftOne
    have hBMeas : MeasurableSet {ω | Y ω < ⊤} := measurableSet_lt hYMeas measurable_const
    have hBProbOne : (P : Measure Ω) {ω | Y ω < ⊤} = 1 :=
      (ENNReal.toReal_eq_one_iff ((P : Measure Ω) {ω | Y ω < ⊤})).mp hBOne
    -- Proof comment: the small-scale Laplace limit shows that every bounded evaluation is finite
    -- with probability one.
    simpa [Y] using
      (MeasureTheory.mem_ae_iff_prob_eq_one (μ := (P : Measure Ω)) hBMeas).2 hBProbOne

/-- Helper for Example 24.25: the second marginal is a random measure once it is finite on every
compact exhaustion piece almost surely. -/
private lemma sndMarginalIsRandomMeasure
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    (hμν_finite :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        (μ ∗ (ν : Measure E)) A ≠ ⊤) :
    IsRandomMeasure P Xkappa := by
  let K : CompactExhaustion E := CompactExhaustion.choice E
  refine ⟨?_, ?_⟩
  · simpa [hXkappa, Measure.snd] using
      (Measure.measurable_map Prod.snd measurable_snd).comp hXi.1.measurable
  · exact ae_isLocallyFiniteMeasure_of_compactExhaustionFinite K fun n ↦
      (sndMarginalIsBoundedlyFiniteRandomMeasure hXi hXkappa hμν_finite).ae_lt_top_apply
        (A := K n) (K.isCompact n).measurableSet (K.isCompact n).isBounded

/-- Helper for Example 24.25: independent increments pass from the marked Poisson point process to
its second marginal by pulling disjoint families back along `Prod.snd`. -/
private lemma sndMarginalHasIndependentIncrements
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd) :
    HasIndependentIncrements P Xkappa := by
  rcases (ProbabilityTheory.isPoissonPointProcess_iff
    (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi).1 hXi with
    ⟨_, hXiIndep, _, _⟩
  intro n A hA hDisj
  -- Proof comment: evaluations of the second marginal on `A i` are evaluations of `Xi` on the
  -- pairwise disjoint cylinders `Prod.snd ⁻¹' A i`.
  simpa [hXkappa, Measure.snd_apply, hA] using
    hXiIndep n (fun i ↦ Prod.snd ⁻¹' A i) (fun i ↦ measurable_snd (hA i)) <| by
      intro i j hij
      exact (hDisj hij).preimage Prod.snd

-- Helper routing note for Example 24.25: compare the real-valued count laws first and only then
-- transport back to `ENNReal`.
/-- Helper for Example 24.25: a bounded measurable cell of a Poisson point process has the
expected one-cell complex phase factor. -/
private lemma poissonCountToReal_complexPhase_of_isPoissonPointProcess
    {P : ProbabilityMeasure Ω} {ρ : Measure E} {Y : Ω → Measure E}
    (hY : IsPoissonPointProcess ρ P Y)
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_finite : ρ A ≠ ⊤) (t : ℝ) :
    ∫ ω, Complex.exp ((((t * (Y ω A).toReal : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω) =
      Complex.exp (((ρ A).toReal : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  let f : RealValuedBoundedMeasurableFunction E :=
    ⟨Set.indicator A (fun _ ↦ t), measurable_const.indicator hA, ⟨|t|, fun x ↦ by
      by_cases hx : x ∈ A
      · simp [hx]
      · simp [hx]⟩⟩
  rcases (ProbabilityTheory.isPoissonPointProcess_iff ρ P Y).1 hY with
    ⟨_, _, _, hCount⟩
  have hCountLaw :
      HasLaw (fun ω ↦ Y ω A)
        (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure (ρ A).toNNReal))
        (P : Measure Ω) :=
    hCount hA hA_bdd hA_finite
  have hFinitePoisson :
      ∀ᵐ z : ENNReal ∂(Measure.map (fun n : ℕ ↦ (n : ENNReal))
        (poissonMeasure (ρ A).toNNReal)), z < ⊤ := by
    exact
      (ae_map_iff (measurable_of_countable (fun n : ℕ ↦ (n : ENNReal))).aemeasurable
        (measurableSet_lt measurable_id measurable_const)).2 <|
        Filter.Eventually.of_forall fun n ↦ by simp
  have hFiniteAe : ∀ᵐ ω ∂(P : Measure Ω), Y ω A < ⊤ :=
    (hCountLaw.ae_iff (measurable_id.lt measurable_const)).2 hFinitePoisson
  have haeInt : ∀ᵐ ω ∂(P : Measure Ω), Integrable f (Y ω) := by
    -- Proof comment: on the almost-sure event `Y ω A < ⊤`, the indicator-constant test function
    -- is integrable because it is supported on one finite-mass cell.
    filter_upwards [hFiniteAe] with ω hω
    have hIntOn : IntegrableOn (fun _ : E ↦ t) A (Y ω) := integrableOn_const hω.ne
    simpa [f] using hIntOn.integrable_indicator hA
  have hμInt :
      Integrable (fun x ↦ Complex.exp ((f x : ℂ) * Complex.I) - 1) ρ := by
    -- Proof comment: the exponent-side integrand is again an indicator of a constant on the
    -- finite cell `A`.
    have hIntegrand :
        (fun x ↦ Complex.exp ((f x : ℂ) * Complex.I) - 1) =
          Set.indicator A (fun _ ↦ Complex.exp ((t : ℂ) * Complex.I) - 1) := by
      funext x
      by_cases hx : x ∈ A
      · simp [f, hx]
      · simp [f, hx]
    have hIntOn :
        IntegrableOn (fun _ : E ↦ Complex.exp ((t : ℂ) * Complex.I) - 1) A ρ :=
      integrableOn_const hA_finite
    rw [hIntegrand]
    exact hIntOn.integrable_indicator hA
  have hExponent :
      ∫ x, (Complex.exp ((f x : ℂ) * Complex.I) - 1) ∂ρ =
        ((ρ A).toReal : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1) := by
    -- Proof comment: the intensity-side integral collapses to the mass of `A` times the constant
    -- phase coefficient.
    have hIntegrand :
        (fun x ↦ Complex.exp ((f x : ℂ) * Complex.I) - 1) =
          Set.indicator A (fun _ ↦ Complex.exp ((t : ℂ) * Complex.I) - 1) := by
      funext x
      by_cases hx : x ∈ A
      · simp [f, hx]
      · simp [f, hx]
    rw [hIntegrand]
    rw [integral_indicator_const (Complex.exp ((t : ℂ) * Complex.I) - 1) hA, measureReal_def]
    rfl
  have hChar :=
    poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction
      P ρ Y hY f haeInt hμInt
  calc
    ∫ ω, Complex.exp ((((t * (Y ω A).toReal : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω)
      = ∫ ω, Complex.exp ((((∫ x, f x ∂Y ω : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω) := by
          refine integral_congr_ae ?_
          filter_upwards [hFiniteAe] with ω hω
          have hIntegral :
              ∫ x, f x ∂Y ω = t * (Y ω A).toReal := by
            change ∫ x, Set.indicator A (fun _ ↦ t) x ∂Y ω = t * (Y ω A).toReal
            rw [integral_indicator_const t hA, measureReal_def]
            simp [smul_eq_mul, mul_comm]
          simpa [hIntegral]
    _ = Complex.exp (∫ x, (Complex.exp ((f x : ℂ) * Complex.I) - 1) ∂ρ) := hChar
    _ = Complex.exp (((ρ A).toReal : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
          rw [hExponent]

/-- Helper for Example 24.25: the second marginal count on a bounded measurable cell has the
same complex phase factor as a Poisson count of rate `(μ ∗ ν) A`. -/
private lemma sndMarginalCountToReal_complexPhase_expectation
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    (hμν_finite :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        (μ ∗ (ν : Measure E)) A ≠ ⊤)
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_finite : (μ ∗ (ν : Measure E)) A ≠ ⊤) (t : ℝ) :
    ∫ ω, Complex.exp ((((t * (Xkappa ω A).toReal : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω) =
      Complex.exp ((((μ ∗ (ν : Measure E)) A).toReal : ℂ) *
        (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  letI : IsSFiniteKernel (dirac_convolution_kernel (ν : Measure E)) := inferInstance
  let f : RealValuedBoundedMeasurableFunction (E × E) :=
    ⟨Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t),
      measurable_const.indicator (measurable_snd hA), ⟨|t|, fun z ↦ by
        by_cases hz : z ∈ Prod.snd ⁻¹' A
        · simp [hz]
        · simp [hz]⟩⟩
  have hFiniteAe :
      ∀ᵐ ω ∂(P : Measure Ω), Xkappa ω A < ⊤ :=
    (sndMarginalIsBoundedlyFiniteRandomMeasure hXi hXkappa hμν_finite).ae_lt_top_apply hA hA_bdd
  have haeInt : ∀ᵐ ω ∂(P : Measure Ω), Integrable f (Xi ω) := by
    -- Proof comment: the cylinder indicator integrates over `Xi ω` to the second marginal mass
    -- `Xkappa ω A`, which is finite almost surely on bounded `A`.
    filter_upwards [hFiniteAe] with ω hω
    have hIntOn :
        IntegrableOn (fun _ : E × E ↦ t) (Prod.snd ⁻¹' A) (Xi ω) := by
      have hCylinderEval : Xi ω (Prod.snd ⁻¹' A) = Xkappa ω A := by
        rw [hXkappa, Measure.snd_apply hA]
      exact integrableOn_const (by rw [hCylinderEval]; exact hω.ne)
    simpa [f] using hIntOn.integrable_indicator (measurable_snd hA)
  have hCylinderFinite :
      (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) (Prod.snd ⁻¹' A) ≠ ⊤ := by
    rw [← Measure.snd_apply hA, Measure.snd_compProd, diracConvolutionKernel_comp_measure_eq_conv]
    exact hA_finite
  have hμInt :
      Integrable (fun z ↦ Complex.exp ((f z : ℂ) * Complex.I) - 1)
        (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) := by
    -- Proof comment: the exponent-side integrand is supported on the same finite cylinder and is
    -- constant there.
    have hIntegrand :
        (fun z ↦ Complex.exp ((f z : ℂ) * Complex.I) - 1) =
          Set.indicator (Prod.snd ⁻¹' A)
            (fun _ ↦ Complex.exp ((t : ℂ) * Complex.I) - 1) := by
      funext z
      by_cases hz : z ∈ Prod.snd ⁻¹' A
      · simp [f, hz]
      · simp [f, hz]
    have hIntOn :
        IntegrableOn
          (fun _ : E × E ↦ Complex.exp ((t : ℂ) * Complex.I) - 1)
          (Prod.snd ⁻¹' A)
          (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) :=
      integrableOn_const hCylinderFinite
    rw [hIntegrand]
    exact hIntOn.integrable_indicator (measurable_snd hA)
  have hExponent :
      ∫ z, (Complex.exp ((f z : ℂ) * Complex.I) - 1)
          ∂(μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) =
        (((μ ∗ (ν : Measure E)) A).toReal : ℂ) *
          (Complex.exp ((t : ℂ) * Complex.I) - 1) := by
    -- Proof comment: the product-space exponent integral collapses to the second marginal mass of
    -- the cylinder, hence to `(μ ∗ ν) A`.
    have hIntegrand :
        (fun z ↦ Complex.exp ((f z : ℂ) * Complex.I) - 1) =
          Set.indicator (Prod.snd ⁻¹' A)
            (fun _ ↦ Complex.exp ((t : ℂ) * Complex.I) - 1) := by
      funext z
      by_cases hz : z ∈ Prod.snd ⁻¹' A
      · simp [f, hz]
      · simp [f, hz]
    rw [hIntegrand]
    rw [integral_indicator_const (Complex.exp ((t : ℂ) * Complex.I) - 1) (measurable_snd hA)]
    rw [measureReal_def, ← Measure.snd_apply hA, Measure.snd_compProd,
      diracConvolutionKernel_comp_measure_eq_conv]
    rfl
  have hChar :=
    poisson_point_process_characteristicFunction_onHonestDomain_of_boundedRealFunction
      P (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) Xi hXi f haeInt hμInt
  calc
    ∫ ω, Complex.exp ((((t * (Xkappa ω A).toReal : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω)
      = ∫ ω, Complex.exp ((((∫ z, f z ∂Xi ω : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω) := by
          refine integral_congr_ae ?_
          filter_upwards [hFiniteAe] with ω hω
          have hIntegral :
              ∫ z, f z ∂Xi ω = t * (Xkappa ω A).toReal := by
            change
              ∫ z, Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t) z ∂Xi ω =
                t * (Xkappa ω A).toReal
            rw [integral_indicator_const t (measurable_snd hA)]
            rw [measureReal_def, hXkappa, Measure.snd_apply hA]
            simp [smul_eq_mul, mul_comm]
          simpa [hIntegral]
    _ = Complex.exp
          (∫ z, (Complex.exp ((f z : ℂ) * Complex.I) - 1)
            ∂(μ ⊗ₘ dirac_convolution_kernel (ν : Measure E))) := hChar
    _ = Complex.exp ((((μ ∗ (ν : Measure E)) A).toReal : ℂ) *
          (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
          rw [hExponent]

/-- Helper for Example 24.25: the real-valued second-marginal count law agrees with the real-cast
Poisson law of rate `(μ ∗ ν) A`. -/
private lemma sndMarginalCountToReal_hasLawPoisson
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    (hμν_finite :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        (μ ∗ (ν : Measure E)) A ≠ ⊤)
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_finite : (μ ∗ (ν : Measure E)) A ≠ ⊤) :
    HasLaw (fun ω ↦ (Xkappa ω A).toReal)
      (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal))
      (P : Measure Ω) := by
  let μconv : BoundedlyFiniteMeasure E :=
    ⟨μ ∗ (ν : Measure E), fun B hB hB_bdd ↦ lt_top_iff_ne_top.mpr (hμν_finite hB hB_bdd)⟩
  rcases exists_poisson_point_process_with_intensity_measure μconv with
    ⟨Ω', _, P', Y, hY⟩
  have hXkappaMeas : Measurable Xkappa := by
    simpa [hXkappa, Measure.snd] using
      (Measure.measurable_map Prod.snd measurable_snd).comp hXi.1.measurable
  have hXcountMeas : Measurable (fun ω ↦ (Xkappa ω A).toReal) :=
    ENNReal.measurable_toReal.comp ((Measure.measurable_coe hA).comp hXkappaMeas)
  have hYcountMeas : Measurable (fun ω : Ω' ↦ (Y ω A).toReal) :=
    ENNReal.measurable_toReal.comp ((Measure.measurable_coe hA).comp hY.1.measurable)
  have hMapEq :
      Measure.map (fun ω ↦ (Xkappa ω A).toReal) (P : Measure Ω) =
        Measure.map (fun n : ℕ ↦ (n : ℝ))
          (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal) := by
    -- Proof comment: compare the real-valued count laws through their characteristic functions;
    -- both sides have the same one-cell phase factor.
    refine Measure.ext_of_charFun <| funext fun t ↦ ?_
    have hPhaseMeasX_t :
        AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)))
          (Measure.map (fun ω ↦ (Xkappa ω A).toReal) (P : Measure Ω)) := by
      exact
        ((((Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const
          Complex.I).cexp).aestronglyMeasurable)
    have hPhaseMeasY_t :
        AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)))
          (Measure.map (fun ω : Ω' ↦ (Y ω A).toReal) (P' : Measure Ω')) := by
      exact
        ((((Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const
          Complex.I).cexp).aestronglyMeasurable)
    calc
      MeasureTheory.charFun
          (Measure.map (fun ω ↦ (Xkappa ω A).toReal) (P : Measure Ω)) t
        = ∫ ω, Complex.exp ((((t * (Xkappa ω A).toReal : ℝ) : ℂ) * Complex.I)) ∂(P : Measure Ω) := by
            rw [MeasureTheory.charFun_apply_real]
            simpa using integral_map hXcountMeas.aemeasurable hPhaseMeasX_t
      _ = Complex.exp ((((μ ∗ (ν : Measure E)) A).toReal : ℂ) *
            (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
              exact sndMarginalCountToReal_complexPhase_expectation
                hXi hXkappa hμν_finite hA hA_bdd hA_finite t
      _ = ∫ ω, Complex.exp ((((t * (Y ω A).toReal : ℝ) : ℂ) * Complex.I)) ∂(P' : Measure Ω') := by
            symm
            exact poissonCountToReal_complexPhase_of_isPoissonPointProcess
              hY hA hA_bdd hA_finite t
      _ = MeasureTheory.charFun
            (Measure.map (fun ω : Ω' ↦ (Y ω A).toReal) (P' : Measure Ω')) t := by
            symm
            rw [MeasureTheory.charFun_apply_real]
            simpa using integral_map hYcountMeas.aemeasurable hPhaseMeasY_t
      _ = MeasureTheory.charFun
            (Measure.map (fun n : ℕ ↦ (n : ℝ))
              (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal)) t := by
            have hYLaw :
                HasLaw (fun ω : Ω' ↦ (Y ω A).toReal)
                  (Measure.map (fun n : ℕ ↦ (n : ℝ))
                    (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal))
                  (P' : Measure Ω') :=
              poissonCountToReal_hasLaw_onBoundedSet
                P' (μ ∗ (ν : Measure E)) Y hY hA hA_bdd hA_finite
            rw [← hYLaw.map_eq]
  exact ⟨hXcountMeas.aemeasurable, hMapEq⟩

/-- Helper for Example 24.25: bounded measurable evaluations of the second marginal have the
Poisson law with rate `(μ ∗ ν) A`. -/
private lemma sndMarginalEval_hasLawPoisson
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    (hμν_finite :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        (μ ∗ (ν : Measure E)) A ≠ ⊤)
    {A : Set E} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_finite : (μ ∗ (ν : Measure E)) A ≠ ⊤) :
    HasLaw (fun ω ↦ Xkappa ω A)
      (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal))
      (P : Measure Ω) := by
  have hRealLaw :=
    sndMarginalCountToReal_hasLawPoisson hXi hXkappa hμν_finite hA hA_bdd hA_finite
  have hOfRealLaw :
      HasLaw ENNReal.ofReal
        (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal))
        (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal)) := by
    refine ⟨ENNReal.measurable_ofReal.aemeasurable, ?_⟩
    -- Proof comment: on natural numbers, transporting first to `ℝ` and then back with
    -- `ENNReal.ofReal` is exactly the canonical embedding `ℕ → ℝ≥0∞`.
    rw [AEMeasurable.map_map_of_aemeasurable ENNReal.measurable_ofReal.aemeasurable
      (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).aemeasurable]
    exact Measure.map_congr (Filter.Eventually.of_forall fun n ↦ by simp)
  have hComp :
      HasLaw (ENNReal.ofReal ∘ fun ω ↦ (Xkappa ω A).toReal)
        (Measure.map (fun n : ℕ ↦ (n : ENNReal))
          (poissonMeasure ((μ ∗ (ν : Measure E)) A).toNNReal))
        (P : Measure Ω) :=
    HasLaw.comp hOfRealLaw hRealLaw
  have hFiniteAe :
      ∀ᵐ ω ∂(P : Measure Ω), Xkappa ω A < ⊤ :=
    (sndMarginalIsBoundedlyFiniteRandomMeasure hXi hXkappa hμν_finite).ae_lt_top_apply hA hA_bdd
  have hCompEq :
      (ENNReal.ofReal ∘ fun ω ↦ (Xkappa ω A).toReal) =ᵐ[(P : Measure Ω)]
        (fun ω ↦ Xkappa ω A) := by
    -- Proof comment: the final transport back from the real-valued count is valid almost surely
    -- because boundedly finite evaluations are finite almost surely.
    filter_upwards [hFiniteAe] with ω hω
    simp [Function.comp, ENNReal.ofReal_toReal, hω.ne]
  exact hComp.congr hCompEq.symm

/-- A Poisson point process remains Poisson after one independent random-walk step when the step
is modeled by an explicit marked Poisson point process and the convolved intensity is finite on
bounded measurable sets. -/
theorem randomWalkPointProcessStep_isPoissonPointProcess
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {X : Ω → Measure E} (hX : IsPoissonPointProcess μ P X)
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    (hXiFst : (fun ω ↦ (Xi ω).fst) =ᵐ[(P : Measure Ω)] X)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    (hμν_finite :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        (μ ∗ (ν : Measure E)) A ≠ ⊤) :
    IsPoissonPointProcess (μ ∗ (ν : Measure E)) P Xkappa := by
  let μconv : BoundedlyFiniteMeasure E :=
    ⟨μ ∗ (ν : Measure E), fun A hA hA_bdd ↦ lt_top_iff_ne_top.mpr (hμν_finite hA hA_bdd)⟩
  let hXkappaBF :
      IsBoundedlyFiniteRandomMeasure P Xkappa :=
    sndMarginalIsBoundedlyFiniteRandomMeasure hXi hXkappa hμν_finite
  let hXkappaRandom :
      IsRandomMeasure P Xkappa :=
    sndMarginalIsRandomMeasure hXi hXkappa hμν_finite
  refine (ProbabilityTheory.isPoissonPointProcess_iff (μ ∗ (ν : Measure E)) P Xkappa).2 ?_
  refine ⟨hXkappaRandom, ?_, boundedlyFiniteMeasure_isLocallyFinite μconv, ?_⟩
  · exact sndMarginalHasIndependentIncrements hXi hXkappa
  · intro A hA hA_bdd hA_finite
    exact sndMarginalEval_hasLawPoisson hXi hXkappa hμν_finite hA hA_bdd hA_finite

-- Proof sketch: the previous theorem gives the one-step law
-- `Xkappa ∼ PPP_(μ ∗ (ν : Measure E))` for the source-faithful marked-process step, under the
-- same bounded-set finiteness side condition. Hence the evolved particle system has the same
-- Poisson intensity `μ` exactly when convolution with `ν` fixes `μ`.
/-- Example 24.25: if `Xi` is the marked Poisson point process realizing the independent
random-walk step with kernel `κ(x, ·) = δ_x ∗ ν` and `Xkappa` is its second marginal, then the
one-step evolved system is a Poisson point process with intensity `μ` if and only if `μ ∗ ν = μ`,
provided the evolved intensity is finite on bounded measurable sets. This is the source-faithful
invariant-distribution criterion behind the PPP random-walk example. -/
theorem poissonPointProcess_randomWalkStep_invariant_iff
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {X : Ω → Measure E} (hX : IsPoissonPointProcess μ P X)
    {Xi : Ω → Measure (E × E)}
    (hXi : IsPoissonPointProcess (μ ⊗ₘ dirac_convolution_kernel (ν : Measure E)) P Xi)
    (hXiFst : (fun ω ↦ (Xi ω).fst) =ᵐ[(P : Measure Ω)] X)
    {Xkappa : Ω → Measure E}
    (hXkappa : Xkappa = fun ω ↦ (Xi ω).snd)
    (hμν_finite :
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        (μ ∗ (ν : Measure E)) A ≠ ⊤) :
    IsPoissonPointProcess μ P Xkappa ↔
      μ ∗ (ν : Measure E) = μ := by
  constructor
  · intro hInvariant
    have hStep :
        IsPoissonPointProcess (μ ∗ (ν : Measure E)) P Xkappa :=
      randomWalkPointProcessStep_isPoissonPointProcess
        hX hXi hXiFst hXkappa hμν_finite
    have hEqOnBounded :
        ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
          (μ ∗ (ν : Measure E)) A = μ A := by
      intro A hA hA_bdd
      -- Proof comment: the same process `Xkappa` cannot have two different bounded-set Poisson
      -- rates, and the one-step rate is finite by the convolution hypothesis.
      exact poissonIntensity_eq_on_boundedSet_of_sharedProcess
        hStep hInvariant hA hA_bdd (hμν_finite hA hA_bdd)
    exact measure_eq_of_eqOnBoundedSets hEqOnBounded
  · intro hInvariant
    -- Route correction: instead of reconstructing the random-walk step again, rewrite the
    -- intensity in the one-step theorem by the assumed invariance equation.
    simpa [hInvariant] using
      (randomWalkPointProcessStep_isPoissonPointProcess
        (P := P) (μ := μ) (ν := ν) (X := X) hX
        (Xi := Xi) hXi hXiFst (Xkappa := Xkappa) hXkappa hμν_finite)

end Poisson

end ProbabilityTheory
