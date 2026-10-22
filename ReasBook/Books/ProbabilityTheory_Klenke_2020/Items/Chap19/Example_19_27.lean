/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_33
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval
open unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- `source-facing`: Example 19.27 studies the asymmetric nearest-neighbor walk on `ℤ` and the
associated geometric conductance network.
`core/canonical`: Chapter 17 and Chapter 19 already provide the owner notions
`IsTransientState`, `IsRandomWalkWithWeights`, `biasedSimpleRandomWalkStepPMF`,
`biasedSimpleRandomWalkKernel_apply_singleton`.
`bridge/view`: the local declarations below identify the biased walk kernel with the conductance
transition matrix and isolate the monotone-path irreducibility argument. -/

/-- Helper for Example 19.27: the one-step increment law of the one-dimensional biased nearest-
neighbor walk, jumping to `1` with probability `p` and to `-1` with probability `1 - p`. -/
def biasedSimpleRandomWalkStepPMF (p : I) : PMF ℤ :=
  (PMF.bernoulli (unitInterval.toNNReal p) (by simpa using p.2.2)).map
    fun b ↦ if b then (1 : ℤ) else -1

/-- Helper for Example 19.27: evaluating the biased nearest-neighbor kernel on a singleton target
recovers the usual two-point transition formula. -/
theorem biasedSimpleRandomWalkKernel_apply_singleton (p : I) (x y : ℤ) :
    dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y} =
      if y = x + 1 then ENNReal.ofReal (p : ℝ)
      else if y = x - 1 then ENNReal.ofReal (1 - (p : ℝ))
      else 0 := by
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : ℤ ↦ x + z) ⁻¹' ({y} : Set ℤ) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (y - x))]
  by_cases hy1 : y = x + 1
  · have hy_sub : y - x = 1 := by
      omega
    have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
    rw [hy_sub]
    -- Proof comment: on the right-jump branch the singleton mass is the Bernoulli success
    -- probability.
    simp [biasedSimpleRandomWalkStepPMF, PMF.map_apply, PMF.bernoulli_apply, hy1]
    simpa [unitInterval.toNNReal] using (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
  · by_cases hy_left : y = x - 1
    · have hy_sub : y - x = -1 := by
        omega
      have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
      have hbranch : x - 1 ≠ x + 1 := by
        omega
      have hcoe : ENNReal.ofNNReal (unitInterval.toNNReal p) = ENNReal.ofReal (p : ℝ) := by
        simpa [unitInterval.toNNReal] using (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
      rw [hy_sub]
      -- Proof comment: on the left-jump branch the complementary Bernoulli mass is `1 - p`.
      simp [biasedSimpleRandomWalkStepPMF, PMF.map_apply, PMF.bernoulli_apply, hy_left]
      rw [if_neg hbranch]
      calc
        1 - ENNReal.ofNNReal (unitInterval.toNNReal p)
            = 1 - ENNReal.ofReal (p : ℝ) := by
                rw [hcoe]
        _ = ENNReal.ofReal (1 - (p : ℝ)) := by
              symm
              simpa using (ENNReal.ofReal_sub 1 hp_nonneg)
    · have hy_sub_one : y - x ≠ 1 := by
        omega
      have hy_sub_negOne : y - x ≠ -1 := by
        omega
      have hpmf_zero : biasedSimpleRandomWalkStepPMF p (y - x) = 0 := by
        rw [biasedSimpleRandomWalkStepPMF, PMF.map_apply]
        apply ENNReal.tsum_eq_zero.2
        intro b
        cases b <;> simp [hy_sub_one, hy_sub_negOne]
      -- Proof comment: away from the two support points, the step law assigns zero mass.
      simp [hy1, hy_left, hpmf_zero]

/-- Helper for Example 19.27: at bias `1`, each one-step kernel row is the Dirac mass at the
deterministic successor state. -/
private lemma biasedSimpleRandomWalkOne_kernel_eq_diracSucc (x : ℤ) :
    dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure x =
      Measure.dirac (x + 1) := by
  refine Measure.ext_of_singleton fun y ↦ ?_
  by_cases hy : y = x + 1
  · subst hy
    -- Proof comment: at bias `1`, the only allowed step is the deterministic jump to `x + 1`.
    rw [biasedSimpleRandomWalkKernel_apply_singleton]
    simp
  · -- Proof comment: away from `x + 1`, the deterministic step law has zero singleton mass.
    rw [biasedSimpleRandomWalkKernel_apply_singleton]
    simp [hy]

/-- Helper for Example 19.27: when the bias is `1`, the walk moves deterministically to `x + n`
after `n` steps. -/
theorem biasedSimpleRandomWalkOne_pow_eq_dirac (x : ℤ) :
    ∀ n : ℕ,
      ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure ^ n) x) =
        Measure.dirac (x + n) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it leaves the starting state
      -- fixed.
      simpa using (Kernel.id_apply x)
  | succ n ih =>
      have hstepLaw :
          (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure = Measure.dirac (1 : ℤ) := by
        refine Measure.ext_of_singleton fun z ↦ ?_
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
        by_cases hz : z = 1
        · subst hz
          simp [biasedSimpleRandomWalkStepPMF]
        · simp [biasedSimpleRandomWalkStepPMF, hz]
      refine Measure.ext_of_singleton fun y ↦ ?_
      -- Proof comment: compose the inductive Dirac law with the deterministic one-step shift.
      rw [Kernel.pow_succ_apply_eq_lintegral
        (dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure)
        n x (measurableSet_singleton y)]
      rw [ih]
      -- Proof comment: after rewriting the step law as `δ₁`, the convolution stays a Dirac mass
      -- at the translated successor state.
      simpa [hstepLaw, add_assoc] using
        (show
          ∫⁻ a,
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure a {y}
              ∂Measure.dirac (x + n) =
            Measure.dirac (x + n + 1) {y} by
            simp [hstepLaw, dirac_convolution_kernel_apply, Measure.dirac_conv])

/-- Helper for Example 19.27: the biased walk is the random environment with constant right-jump
probability `p`. -/
def biasedSimpleRandomWalkEnvironment (p : I) : RandomEnvironment where
  rightJumpProb := fun _ ↦ unitInterval.toNNReal p
  rightJumpProb_le_one := fun _ ↦ by
    simpa [unitInterval.toNNReal] using p.2.2

/-- Helper for Example 19.27: the constant environment is elliptic whenever `0 < p < 1`. -/
theorem biasedSimpleRandomWalkEnvironment_isElliptic
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (biasedSimpleRandomWalkEnvironment p).IsElliptic := by
  constructor
  intro x
  constructor
  · exact_mod_cast hp0
  · exact_mod_cast hp1

/-- Helper for Example 19.27: the RWRE transition matrix of the constant environment agrees with
the biased nearest-neighbor convolution kernel. -/
theorem biasedSimpleRandomWalkEnvironment_transitionMatrix
    (p : I) (x y : ℤ) :
    randomEnvironmentTransitionMatrix (biasedSimpleRandomWalkEnvironment p) x y =
      dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y} := by
  by_cases hy1 : y = x + 1
  · subst y
    rw [randomEnvironmentTransitionMatrix_right, biasedSimpleRandomWalkKernel_apply_singleton]
    have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
    simpa [biasedSimpleRandomWalkEnvironment, unitInterval.toNNReal] using
      (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
  · by_cases hy2 : y = x - 1
    · subst y
      rw [randomEnvironmentTransitionMatrix_left, biasedSimpleRandomWalkKernel_apply_singleton]
      have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
      have hp_le_one : (p : ℝ) ≤ 1 := p.2.2
      have hneq : x - 1 ≠ x + 1 := by
        omega
      have hright :
          ((biasedSimpleRandomWalkEnvironment p).rightJumpProb x : ℝ≥0∞) =
            ENNReal.ofReal (p : ℝ) := by
        simpa [biasedSimpleRandomWalkEnvironment, unitInterval.toNNReal] using
          (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
      have hleft :
          (1 : ℝ≥0∞) - (biasedSimpleRandomWalkEnvironment p).rightJumpProb x =
            ENNReal.ofReal (1 - (p : ℝ)) := by
        calc
          (1 : ℝ≥0∞) - (biasedSimpleRandomWalkEnvironment p).rightJumpProb x
              = 1 - ENNReal.ofReal (p : ℝ) := by
                  rw [hright]
          _ = ENNReal.ofReal (1 - (p : ℝ)) := by
                symm
                simpa using (ENNReal.ofReal_sub 1 hp_nonneg)
      simpa [biasedSimpleRandomWalkEnvironment, hneq] using hleft
    · rw [randomEnvironmentTransitionMatrix_apply, biasedSimpleRandomWalkKernel_apply_singleton]
      simp [hy1, hy2]

/-- Helper for Example 19.27: the realization spelling with the biased convolution kernel can be
transported to the equivalent constant-environment matrix spelling. -/
theorem isMarkovProcessRealization_biasedSimpleRandomWalkEnvironment
    (p : I) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      P X] :
    IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel (randomEnvironmentTransitionMatrix (biasedSimpleRandomWalkEnvironment p)) ^ n)
      P X := by
  have hkernel :
      discreteMatrixKernel (randomEnvironmentTransitionMatrix (biasedSimpleRandomWalkEnvironment p)) =
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure := by
    ext x s hs
    have hrow :
        discreteMatrixKernel (randomEnvironmentTransitionMatrix (biasedSimpleRandomWalkEnvironment p)) x =
          dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x := by
      refine Measure.ext_of_singleton fun y ↦ ?_
      rw [rwreKernel_apply_singleton]
      exact biasedSimpleRandomWalkEnvironment_transitionMatrix p x y
    exact congrArg (fun μ ↦ μ s) hrow
  simpa [hkernel] using
    (inferInstance :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
        P X)

/-- Helper for Example 19.27: in the constant environment, the Solomon ratio is the fixed value
`(1 - p) / p`. -/
theorem biasedSimpleRandomWalkEnvironment_ratio
    (p : I) (hp0 : 0 < (p : ℝ)) (x : ℤ) :
    ρ[biasedSimpleRandomWalkEnvironment p](x) =
      ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := hp0.le
  have hp_le_one : (p : ℝ) ≤ 1 := p.2.2
  have hnum :
      (1 : ℝ≥0∞) - (biasedSimpleRandomWalkEnvironment p).rightJumpProb x =
        ENNReal.ofReal (1 - (p : ℝ)) := by
    have hden :
        ((biasedSimpleRandomWalkEnvironment p).rightJumpProb x : ℝ≥0∞) =
          ENNReal.ofReal (p : ℝ) := by
      simpa [biasedSimpleRandomWalkEnvironment, unitInterval.toNNReal] using
        (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
    calc
      (1 : ℝ≥0∞) - (biasedSimpleRandomWalkEnvironment p).rightJumpProb x
          = 1 - ENNReal.ofReal (p : ℝ) := by
              rw [hden]
      _ = ENNReal.ofReal (1 - (p : ℝ)) := by
            symm
            simpa using (ENNReal.ofReal_sub 1 hp_nonneg)
  have hden :
      ((biasedSimpleRandomWalkEnvironment p).rightJumpProb x : ℝ≥0∞) =
        ENNReal.ofReal (p : ℝ) := by
    simpa [biasedSimpleRandomWalkEnvironment, unitInterval.toNNReal] using
      (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
  rw [randomEnvironmentRatio, hnum, hden, ← ENNReal.ofReal_div_of_pos hp0]

/-- Helper for Example 19.27: the rightward Solomon products of the constant environment are the
geometric powers of `(1 - p) / p`. -/
theorem biasedSimpleRandomWalkEnvironment_rightSeriesTerm
    (p : I) (hp0 : 0 < (p : ℝ)) :
    ∀ n : ℕ,
      randomEnvironmentRightSeriesTerm (biasedSimpleRandomWalkEnvironment p) n =
        ENNReal.ofReal (((1 - (p : ℝ)) / (p : ℝ)) ^ (n + 1))
  | 0 => by
      simp [randomEnvironmentRightSeriesTerm, biasedSimpleRandomWalkEnvironment_ratio p hp0 0]
  | n + 1 => by
      have hratio_nonneg : 0 ≤ ((1 - (p : ℝ)) / (p : ℝ)) := by
        exact div_nonneg (sub_nonneg.mpr p.2.2) hp0.le
      rw [randomEnvironmentRightSeriesTerm_succ,
        biasedSimpleRandomWalkEnvironment_rightSeriesTerm p hp0 n,
        biasedSimpleRandomWalkEnvironment_ratio p hp0 (n + 1)]
      rw [← ENNReal.ofReal_mul]
      · simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]
      · exact pow_nonneg hratio_nonneg _

/-- Helper for Example 19.27: in the constant environment with `p > 1 / 2`, the right Solomon
series is finite. -/
theorem biasedSimpleRandomWalkEnvironment_rightSeries_lt_top
    (p : I) (hp : 1 / 2 < (p : ℝ)) :
    R⁺[biasedSimpleRandomWalkEnvironment p] < ∞ := by
  let r : ℝ := (1 - (p : ℝ)) / (p : ℝ)
  have hp0 : 0 < (p : ℝ) := by
    linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (sub_nonneg.mpr p.2.2) hp0.le
  have hr_lt_one : r < 1 := by
    dsimp [r]
    field_simp [hp0.ne']
    linarith
  have hr_enn_lt_one : ENNReal.ofReal r < 1 := by
    rwa [ENNReal.ofReal_lt_one]
  calc
    R⁺[biasedSimpleRandomWalkEnvironment p]
        = ∑' n : ℕ, ENNReal.ofReal (r ^ (n + 1)) := by
            rw [randomEnvironmentRightSeries_def]
            refine tsum_congr fun n ↦ ?_
            simpa [r] using
              biasedSimpleRandomWalkEnvironment_rightSeriesTerm p hp0 n
    _ = ∑' n : ℕ, (ENNReal.ofReal r) ^ (n + 1) := by
          refine tsum_congr fun n ↦ ?_
          simpa using (ENNReal.ofReal_pow hr_nonneg (n + 1))
    _ = ENNReal.ofReal r * (1 - ENNReal.ofReal r)⁻¹ := by
          simpa using ENNReal.tsum_geometric_add_one (ENNReal.ofReal r)
    _ < ∞ := by
      have hgeom_lt_top : (1 - ENNReal.ofReal r)⁻¹ < ∞ := by
        simpa using (tsum_geometric_lt_top (r := ENNReal.ofReal r)).2 hr_enn_lt_one
      exact ENNReal.mul_lt_top (by simpa [hr_lt_one.ne] using ENNReal.ofReal_ne_top) hgeom_lt_top

/-- Helper for Example 19.27: on the discrete state space `ℤ`, a convolution kernel is recovered
from its singleton masses by `discreteMatrixKernel`. -/
private theorem diracConvolutionKernel_eq_discreteMatrixKernel (ν : Measure ℤ) :
    discreteMatrixKernel (fun x y ↦ dirac_convolution_kernel ν x {y}) =
      dirac_convolution_kernel ν := by
  -- Proof comment: on the discrete space `ℤ`, the singleton masses determine the whole row law.
  ext x s hs
  have hrow :
      discreteMatrixKernel (fun a b ↦ dirac_convolution_kernel ν a {b}) x =
        dirac_convolution_kernel ν x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp
    · intro z hz
      simp [hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Example 19.27: a normalized conductance matrix has row sum `1` once the row
weights are finite and positive. -/
theorem conductanceTransitionMatrix_isStochastic
    {C : ℤ → ℤ → ℝ≥0∞}
    (hC_finite : ∀ x : ℤ, conductance C x < ∞)
    (hC_pos : ∀ x : ℤ, 0 < conductance C x) :
    IsStochasticMatrix (conductanceTransitionMatrix C) := by
  intro x
  calc
    ∑' y : ℤ, conductanceTransitionMatrix C x y
        = ∑' y : ℤ, C x y * (conductance C x)⁻¹ := by
            simp_rw [conductanceTransitionMatrix_apply, div_eq_mul_inv]
    _ = (∑' y : ℤ, C x y) * (conductance C x)⁻¹ := ENNReal.tsum_mul_right
    _ = conductance C x * (conductance C x)⁻¹ := by rw [← conductance]
    _ = 1 := ENNReal.mul_inv_cancel (ne_of_gt (hC_pos x)) (ne_of_lt (hC_finite x))

/-- Helper for Example 19.27: the normalized conductance matrix is the random walk with weights
`C`. -/
theorem conductanceTransitionMatrix_isRandomWalkWithWeights
    {C : ℤ → ℤ → ℝ≥0∞}
    (hC_symm : ∀ x y : ℤ, C x y = C y x)
    (hC_finite : ∀ x : ℤ, conductance C x < ∞)
    (hC_pos : ∀ x : ℤ, 0 < conductance C x) :
    IsRandomWalkWithWeights (conductanceTransitionMatrix C) C where
  isStochastic := conductanceTransitionMatrix_isStochastic hC_finite hC_pos
  symmetric := hC_symm
  transition_eq := conductanceTransitionMatrix_apply C

/-- The conductance family on `ℤ` from Example 19.27: the edge `{x, x + 1}` carries weight
`(p / (1 - p)) ^ x`, and all non-nearest-neighbor pairs have conductance `0`. -/
def asymmetricNearestNeighborWalkConductance (p : I) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then
      ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ x)
    else if y = x - 1 then
      ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ y)
    else
      0

/-- Helper for Example 19.27: evaluating the conductance family just unfolds its defining
nearest-neighbor cases. -/
theorem asymmetricNearestNeighborWalkConductance_apply (p : I) (x y : ℤ) :
    asymmetricNearestNeighborWalkConductance p x y =
      if y = x + 1 then
        ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ x)
      else if y = x - 1 then
        ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ y)
      else
        0 := by
  -- Proof comment: this is exactly the defining `if`-expression.
  rfl

/-- Helper for Example 19.27: the two nonzero conductances in the `x`-row combine into the stable
normal form `q ^ (x - 1) / (1 - p)`. -/
theorem asymmetricNearestNeighborWalk_vertexWeight_normalize
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (x : ℤ) :
    let q : ℝ := (p : ℝ) / (1 - (p : ℝ))
    q ^ x + q ^ (x - 1) = q ^ (x - 1) / (1 - (p : ℝ)) := by
  set q : ℝ := (p : ℝ) / (1 - (p : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    exact div_pos hp0 (sub_pos.mpr hp1)
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hstep : q ^ x = q ^ (x - 1) * q := by
    have hx : x = (x - 1) + 1 := by
      omega
    rw [hx, zpow_add₀ hq_ne]
    simp
  have hsub : 1 - (p : ℝ) ≠ 0 := by
    linarith
  -- Proof comment: factor out the common power `q ^ (x - 1)` and simplify `q + 1`.
  calc
    q ^ x + q ^ (x - 1) = q ^ (x - 1) * q + q ^ (x - 1) := by
      rw [hstep]
    _ = q ^ (x - 1) * (q + 1) := by
      ring
    _ = q ^ (x - 1) / (1 - (p : ℝ)) := by
      dsimp [q]
      field_simp [hsub]
      ring

/-- Helper for Example 19.27: the total conductance leaving `x` has the expected geometric closed
form. -/
theorem asymmetricNearestNeighborWalk_vertexWeight
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (x : ℤ) :
    conductance (asymmetricNearestNeighborWalkConductance p) x =
      ENNReal.ofReal ((((p : ℝ) / (1 - (p : ℝ))) ^ (x - 1)) / (1 - (p : ℝ))) := by
  classical
  -- Proof comment: only the two neighbors `x ± 1` contribute to the row sum.
  have hsupport :
      ∀ y ∉ ({x + 1, x - 1} : Finset ℤ), asymmetricNearestNeighborWalkConductance p x y = 0 := by
    intro y hy
    have hy_right : y ≠ x + 1 := by
      intro hy'
      exact hy (by simp [hy'])
    have hy_left : y ≠ x - 1 := by
      intro hy'
      exact hy (by simp [hy'])
    simp [asymmetricNearestNeighborWalkConductance, hy_right, hy_left]
  rw [conductance, tsum_eq_sum hsupport]
  have hneq : x + 1 ≠ x - 1 := by
    omega
  have hneq' : x - 1 ≠ x + 1 := by
    omega
  simp [asymmetricNearestNeighborWalkConductance, hneq, hneq']
  set q : ℝ := (p : ℝ) / (1 - (p : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    exact div_pos hp0 (sub_pos.mpr hp1)
  have hq_nonneg : 0 ≤ q := hq_pos.le
  rw [← ENNReal.ofReal_add (zpow_nonneg hq_nonneg _) (zpow_nonneg hq_nonneg _)]
  -- Proof comment: the remaining real identity is the normalized two-edge formula.
  congr 1
  simpa [q] using asymmetricNearestNeighborWalk_vertexWeight_normalize p hp0 hp1 x

/-- The Example 19.27 conductances reproduce the canonical biased nearest-neighbor kernel on `ℤ`.
-/
theorem conductanceTransitionMatrix_asymmetricNearestNeighborWalkConductance
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    conductanceTransitionMatrix (asymmetricNearestNeighborWalkConductance p) =
      fun x y ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y} := by
  ext x y
  set q : ℝ := (p : ℝ) / (1 - (p : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    exact div_pos hp0 (sub_pos.mpr hp1)
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsub_pos : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hsub_ne : 1 - (p : ℝ) ≠ 0 := ne_of_gt hsub_pos
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hrow_pos : 0 < q ^ (x - 1) / (1 - (p : ℝ)) := by
    exact div_pos (zpow_pos hq_pos _) hsub_pos
  rw [conductanceTransitionMatrix_apply]
  rw [asymmetricNearestNeighborWalk_vertexWeight p hp0 hp1 x]
  rw [biasedSimpleRandomWalkKernel_apply_singleton p x y]
  by_cases hy1 : y = x + 1
  · subst y
    have hpow : q ^ x = q ^ (x - 1) * q := by
      have hx : x = (x - 1) + 1 := by
        omega
      rw [hx, zpow_add₀ hq_ne]
      simp
    -- Proof comment: on the right-jump branch, the normalized conductance is exactly `p`.
    simp [asymmetricNearestNeighborWalkConductance]
    rw [← ENNReal.ofReal_div_of_pos hrow_pos]
    congr 1
    rw [hpow]
    dsimp [q]
    field_simp [hsub_ne, hp_ne]
  · by_cases hy_left : y = x - 1
    · subst y
      have hbranch : x - 1 ≠ x + 1 := by
        omega
      -- Proof comment: on the left-jump branch, the same normalization yields `1 - p`.
      simp [asymmetricNearestNeighborWalkConductance, hbranch]
      rw [← ENNReal.ofReal_div_of_pos hrow_pos]
      congr 1
      have hqpow_ne : q ^ (x - 1) ≠ 0 := zpow_ne_zero _ hq_ne
      dsimp [q]
      field_simp [hqpow_ne, hsub_ne]
    · simp [asymmetricNearestNeighborWalkConductance, hy1, hy_left]

/-- Helper for Example 19.27: the nearest-neighbor conductance profile is symmetric in its two
arguments. -/
theorem asymmetricNearestNeighborWalkConductance_symmetric (p : I) (x y : ℤ) :
    asymmetricNearestNeighborWalkConductance p x y =
      asymmetricNearestNeighborWalkConductance p y x := by
  -- Proof comment: both orientations of a nearest-neighbor edge carry the same weight.
  by_cases hy1 : y = x + 1
  · subst y
    simp [asymmetricNearestNeighborWalkConductance, add_assoc]
  · by_cases hy_left : y = x - 1
    · subst y
      simp [asymmetricNearestNeighborWalkConductance, sub_eq_add_neg]
    · have hx_right : x ≠ y + 1 := by
        omega
      have hx_left : x ≠ y - 1 := by
        omega
      simp [asymmetricNearestNeighborWalkConductance, hy1, hy_left, hx_right, hx_left]

/-- Helper for Example 19.27: the total conductance leaving `0` is exactly `1 / p`. -/
theorem asymmetricNearestNeighborWalk_conductance_zero
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    conductance (asymmetricNearestNeighborWalkConductance p) 0 =
      ENNReal.ofReal ((p : ℝ)⁻¹) := by
  have hsub_ne : 1 - (p : ℝ) ≠ 0 := by
    linarith
  have hp_ne : (p : ℝ) ≠ 0 := by
    linarith
  -- Proof comment: the explicit row-sum formula at `x = 0` collapses to the reciprocal `1 / p`.
  rw [asymmetricNearestNeighborWalk_vertexWeight p hp0 hp1 0]
  simp
  congr 1
  field_simp [hsub_ne, hp_ne]

/-- Helper for Example 19.27: at the endpoint bias `p = 1`, the total conductance leaving `0`
is exactly `1`. -/
theorem asymmetricNearestNeighborWalk_conductance_zero_one :
    conductance (asymmetricNearestNeighborWalkConductance (1 : I)) 0 = 1 := by
  classical
  -- Proof comment: only the neighbors `1` and `-1` contribute to the row sum at `0`.
  have hsupport :
      ∀ y ∉ ({(1 : ℤ), (-1 : ℤ)} : Finset ℤ),
        asymmetricNearestNeighborWalkConductance (1 : I) 0 y = 0 := by
    intro y hy
    have hy_right : y ≠ 1 := by
      intro hy'
      exact hy (by simp [hy'])
    have hy_left : y ≠ -1 := by
      intro hy'
      exact hy (by simp [hy'])
    simp [asymmetricNearestNeighborWalkConductance, hy_right, hy_left]
  rw [conductance, tsum_eq_sum hsupport]
  have hneq : (1 : ℤ) ≠ -1 := by
    norm_num
  simp [asymmetricNearestNeighborWalkConductance, hneq]

/-- Helper for Example 19.27: the asymmetric conductance transition matrix is a random walk with
weights given by the same conductance family. -/
theorem asymmetricNearestNeighborWalk_isRandomWalkWithWeights
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    IsRandomWalkWithWeights
      (conductanceTransitionMatrix (asymmetricNearestNeighborWalkConductance p))
      (asymmetricNearestNeighborWalkConductance p) := by
  -- Proof comment: Example 19.10 packages the conductance normalization once symmetry and
  -- finite positive row sums are known.
  refine conductanceTransitionMatrix_isRandomWalkWithWeights ?_ ?_ ?_
  · intro x y
    exact asymmetricNearestNeighborWalkConductance_symmetric p x y
  · intro x
    rw [asymmetricNearestNeighborWalk_vertexWeight p hp0 hp1 x]
    simp
  · intro x
    rw [asymmetricNearestNeighborWalk_vertexWeight p hp0 hp1 x]
    exact ENNReal.ofReal_pos.mpr <|
      div_pos (zpow_pos (div_pos hp0 (sub_pos.mpr hp1)) _) (sub_pos.mpr hp1)

/-- Helper for Example 19.27: the biased-walk realization can be transported to the conductance
kernel spelling used by Theorem 19.25. -/
theorem isMarkovProcessRealization_asymmetricNearestNeighborWalkConductance
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      P X] :
    IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (conductanceTransitionMatrix (asymmetricNearestNeighborWalkConductance p)) ^ n)
      P X := by
  have hkernel :
      discreteMatrixKernel (conductanceTransitionMatrix (asymmetricNearestNeighborWalkConductance p)) =
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure := by
    rw [conductanceTransitionMatrix_asymmetricNearestNeighborWalkConductance p hp0 hp1]
    -- Proof comment: the singleton-mass matrix recovers the original convolution kernel.
    simpa using
      (diracConvolutionKernel_eq_discreteMatrixKernel
        (ν := (biasedSimpleRandomWalkStepPMF p).toMeasure))
  -- Proof comment: after the one-time kernel identification, the realization instance is just a
  -- transport across the equal semigroups.
  simpa [hkernel] using
    (inferInstance :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
        P X)

/-- Helper for Example 19.27: the deterministic right-shift walk corresponding to `p = 1` never
returns to any starting state, so every state is transient. -/
theorem biasedSimpleRandomWalkOne_allStatesTransient
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure ^ n)
      P X] :
    ∀ x : ℤ, IsTransientState P X x := by
  intro x
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure ^ n)
        P X := inferInstance
  have hhit_zero :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 0 := by
    have hnull :
        ∀ n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = x} = 0 := by
      intro n
      by_cases hn : 0 < n
      · have hset : {ω | 0 < n ∧ X n ω = x} = {ω | X n ω = x} := by
          ext ω
          simp [hn]
        have hpreimage : {ω | X n ω = x} = X n ⁻¹' ({x} : Set ℤ) := by
          ext ω
          simp
        rw [hset]
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton x)]
        rw [hReal.transition_eq x n, biasedSimpleRandomWalkOne_pow_eq_dirac]
        have hneq : x ≠ x + n := by
          omega
        simp [hneq]
      · have hset : {ω | 0 < n ∧ X n ω = x} = (∅ : Set Ω) := by
          ext ω
          simp [hn]
        rw [hset]
        simp
    have hUnion :
        {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = ⋃ n : ℕ, {ω | 0 < n ∧ X n ω = x} := by
      ext ω
      simp
    rw [hUnion]
    exact measure_iUnion_null hnull
  -- Proof comment: the positive-time return event has measure `0`, so the return probability is
  -- `0 < 1` and the state is transient.
  rw [IsTransientState, everHitsProbability_def]
  simp [Measure.real, hhit_zero]

/-- The resistance series attached to the Example 19.27 conductance model is summable when
`p > 1 / 2`. -/
theorem summable_asymmetricNearestNeighborWalk_resistanceSeries
    (p : I) (hp : 1 / 2 < (p : ℝ)) :
    Summable (fun n : ℕ ↦ ((1 - (p : ℝ)) / (p : ℝ)) ^ n) := by
  have hp0 : 0 < (p : ℝ) := by
    linarith
  have hq_nonneg : 0 ≤ (1 - (p : ℝ)) / (p : ℝ) := by
    exact div_nonneg (sub_nonneg.mpr p.2.2) hp0.le
  have hq_lt_one : (1 - (p : ℝ)) / (p : ℝ) < 1 := by
    have := hp
    field_simp [hp0.ne']
    linarith
  -- Proof comment: the resistance terms form a geometric series with ratio in `[0, 1)`.
  exact summable_geometric_of_lt_one hq_nonneg hq_lt_one

/-- The geometric resistance series in Example 19.27 sums to `p / (2p - 1)`. -/
theorem asymmetricNearestNeighborWalk_resistanceSeries_eq
    (p : I) (hp : 1 / 2 < (p : ℝ)) :
    ∑' n : ℕ, ((1 - (p : ℝ)) / (p : ℝ)) ^ n = (p : ℝ) / (2 * (p : ℝ) - 1) := by
  have hp0 : 0 < (p : ℝ) := by
    linarith
  have hq_nonneg : 0 ≤ (1 - (p : ℝ)) / (p : ℝ) := by
    exact div_nonneg (sub_nonneg.mpr p.2.2) hp0.le
  have hq_lt_one : (1 - (p : ℝ)) / (p : ℝ) < 1 := by
    field_simp [hp0.ne']
    linarith
  have hgeom :
      ∑' n : ℕ, ((1 - (p : ℝ)) / (p : ℝ)) ^ n =
        1 / (1 - ((1 - (p : ℝ)) / (p : ℝ))) := by
    simpa [one_div] using tsum_geometric_of_lt_one hq_nonneg hq_lt_one
  rw [hgeom]
  field_simp [hp0.ne']
  ring

/-- Helper for Example 19.27: a right-drift biased walk on `ℤ` is not recurrent. -/
theorem biasedSimpleRandomWalk_not_recurrent_of_half_lt
    (p : I) (hp : 1 / 2 < (p : ℝ))
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      P X] :
    ¬ IsRecurrentMarkovChain P X := by
  by_cases hp_eq_one : (p : ℝ) = 1
  · intro hrec
    have hp_eq : p = (1 : I) := Subtype.ext hp_eq_one
    subst hp_eq
    have htrans := biasedSimpleRandomWalkOne_allStatesTransient P X
    have hnot_transient0 : ¬ IsTransientState P X 0 := by
      rw [IsTransientState, hrec 0]
      simp
    exact hnot_transient0 (htrans 0)
  have hp0 : 0 < (p : ℝ) := by
    linarith
  have hp1 : (p : ℝ) < 1 := by
    exact lt_of_le_of_ne p.2.2 hp_eq_one
  let W : RandomEnvironment := biasedSimpleRandomWalkEnvironment p
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    isMarkovProcessRealization_biasedSimpleRandomWalkEnvironment p P X
  have hW : W.IsElliptic := by
    exact biasedSimpleRandomWalkEnvironment_isElliptic p hp0 hp1
  have hRplus_lt_top : R⁺[W] < ∞ := by
    simpa [W] using biasedSimpleRandomWalkEnvironment_rightSeries_lt_top p hp
  intro hrec
  have hrec0 : IsRecurrentState P X 0 := hrec 0
  have hres_top :
      effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 = ∞ := by
    exact
      (randomEnvironmentStateZeroRecurrent_iff_effectiveResistanceToInfinity_eq_top
        (W := W) (P := P) (X := X) hW).1 hrec0
  have hparallel_lt_top :
      ((R⁻[W])⁻¹ + (R⁺[W])⁻¹)⁻¹ < ∞ := by
    have hsum_pos : 0 < (R⁻[W])⁻¹ + (R⁺[W])⁻¹ := by
      exact lt_of_lt_of_le ((ENNReal.inv_pos).2 hRplus_lt_top.ne)
        (le_add_of_nonneg_left (zero_le _))
    rw [lt_top_iff_ne_top]
    exact (ENNReal.inv_ne_top).2 (ne_of_gt hsum_pos)
  have hres_lt_top :
      effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 < ∞ := by
    rw [randomEnvironment_effectiveResistanceToInfinity_eq_parallel
      (W := W) (P := P) (X := X) hW]
    exact hparallel_lt_top
  exact (ne_of_lt hres_lt_top) hres_top

/-- Helper for Example 19.27: composing a positive first-step singleton mass with a positive
`n`-step singleton mass yields a positive `(n + 1)`-step singleton mass. -/
private theorem discreteKernel_singleton_pos_succ
    {p : ℤ → ℤ → ℝ≥0∞} {x y z : ℤ} {n : ℕ}
    (hxy : 0 < ((discreteMatrixKernel p ^ n) x) ({y} : Set ℤ))
    (hyz : 0 < (discreteMatrixKernel p) y ({z} : Set ℤ)) :
    0 < ((discreteMatrixKernel p ^ (n + 1)) x) ({z} : Set ℤ) := by
  let κ := discreteMatrixKernel p
  have hmeas : Measurable fun w : ℤ ↦ κ w ({z} : Set ℤ) :=
    Kernel.measurable_coe κ (measurableSet_singleton z)
  have hySupport : y ∈ Function.support fun w : ℤ ↦ κ w ({z} : Set ℤ) := by
    change (κ y) ({z} : Set ℤ) ≠ 0
    exact ne_of_gt hyz
  have hsupportPos :
      0 < ((κ ^ n) x) (Function.support fun w : ℤ ↦ κ w ({z} : Set ℤ)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the composition integral is positive because the support of the one-step
  -- singleton mass already contains the intermediate state `y`.
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Example 19.27: following `n` successive right jumps from `x` has strictly positive
`n`-step mass under the biased kernel. -/
private theorem biasedSimpleRandomWalkRightPathMass_pos
    (p : I) (hp0 : 0 < (p : ℝ)) (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (fun a b ↦
            dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
          ({x + n} : Set ℤ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (fun a b ↦
                dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
              ({x + n} : Set ℤ) := ih x
      have hlast :
          0 <
            (discreteMatrixKernel fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) (x + n)
              ({x + (n + 1)} : Set ℤ) := by
        have htarget : x + ((n : ℤ) + 1) = (x + n) + 1 := by
          omega
        have hleft : (x + n) + 1 ≠ (x + n) - 1 := by
          omega
        rw [htarget, discreteMatrixKernel_apply_singleton, biasedSimpleRandomWalkKernel_apply_singleton]
        simpa [hleft] using ENNReal.ofReal_pos.2 hp0
      exact discreteKernel_singleton_pos_succ hrest hlast

/-- Helper for Example 19.27: following `n` successive left jumps from `x` has strictly positive
`n`-step mass under the biased kernel. -/
private theorem biasedSimpleRandomWalkLeftPathMass_pos
    (p : I) (hp1 : (p : ℝ) < 1) (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (fun a b ↦
            dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
          ({x - n} : Set ℤ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel again charges the starting point with mass `1`.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (fun a b ↦
                dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
              ({x - n} : Set ℤ) := ih x
      have hlast :
          0 <
            (discreteMatrixKernel fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) (x - n)
              ({x - (n + 1)} : Set ℤ) := by
        have htarget : x - ((n : ℤ) + 1) = (x - n) - 1 := by
          omega
        have hright : (x - n) - 1 ≠ (x - n) + 1 := by
          omega
        rw [htarget, discreteMatrixKernel_apply_singleton, biasedSimpleRandomWalkKernel_apply_singleton]
        simpa [hright] using ENNReal.ofReal_pos.2 (sub_pos.mpr hp1)
      exact discreteKernel_singleton_pos_succ hrest hlast

/-- Helper for Example 19.27: the biased nearest-neighbor kernel on `ℤ` is irreducible because
every target can be reached by a monotone path of right or left jumps with positive mass. -/
theorem biasedSimpleRandomWalkKernel_isIrreducible
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Kernel.IsIrreducible (Measure.count : Measure ℤ)
      (discreteMatrixKernel fun x y ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y}) := by
  refine ⟨?_⟩
  intro A hA hcount x
  have hA_nonempty : A.Nonempty := by
    by_contra hA_empty
    simp [Set.not_nonempty_iff_eq_empty.mp hA_empty] at hcount
  rcases hA_nonempty with ⟨y, hyA⟩
  by_cases hxy : x ≤ y
  · let n : ℕ := Int.toNat (y - x)
    have hy : y = x + n := by
      dsimp [n]
      omega
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
            ({y} : Set ℤ) := by
      simpa [hy] using biasedSimpleRandomWalkRightPathMass_pos p hp0 x n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))
  · let n : ℕ := Int.toNat (x - y)
    have hy : y = x - n := by
      dsimp [n]
      omega
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
            ({y} : Set ℤ) := by
      simpa [hy] using biasedSimpleRandomWalkLeftPathMass_pos p hp1 x n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))

/-- Helper for Example 19.27: the conductance-kernel spelling of the asymmetric walk is likewise
irreducible. -/
theorem asymmetricNearestNeighborWalkKernel_isIrreducible
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Kernel.IsIrreducible (Measure.count : Measure ℤ)
      (discreteMatrixKernel
        (conductanceTransitionMatrix (asymmetricNearestNeighborWalkConductance p))) := by
  have htransition :
      conductanceTransitionMatrix (asymmetricNearestNeighborWalkConductance p) =
        fun x y ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y} := by
    exact conductanceTransitionMatrix_asymmetricNearestNeighborWalkConductance p hp0 hp1
  -- Proof comment: transport irreducibility across the already proved kernel identification.
  simpa [htransition] using biasedSimpleRandomWalkKernel_isIrreducible p hp0 hp1

/-- Example 19.27: if `p > 1 / 2`, then every state of the asymmetric nearest-neighbor random walk
on `ℤ` with jump probabilities `p` to the right and `1 - p` to the left is transient. -/
theorem asymmetricNearestNeighborWalk_allStatesTransient_of_half_lt
    (p : I) (hp : 1 / 2 < (p : ℝ))
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      P X] :
    ∀ x : ℤ, IsTransientState P X x := by
  by_cases hp_one : (p : ℝ) = 1
  · have hp_eq : p = (1 : I) := Subtype.ext hp_one
    subst hp_eq
    -- Proof comment: at the endpoint `p = 1`, the walk is the deterministic right shift.
    exact biasedSimpleRandomWalkOne_allStatesTransient P X
  · have hp0 : 0 < (p : ℝ) := by
      linarith
    have hp1 : (p : ℝ) < 1 := by
      exact lt_of_le_of_ne p.2.2 hp_one
    have hnot_recurrent : ¬ IsRecurrentMarkovChain P X :=
      biasedSimpleRandomWalk_not_recurrent_of_half_lt p hp P X
    let stepMeasure : Measure ℤ := (biasedSimpleRandomWalkStepPMF p).toMeasure
    have hkernel :
        discreteMatrixKernel (fun x y ↦ (Measure.dirac x ∗ stepMeasure) {y}) =
          dirac_convolution_kernel stepMeasure := by
      simpa [stepMeasure, dirac_convolution_kernel_apply] using
        (diracConvolutionKernel_eq_discreteMatrixKernel
          (ν := stepMeasure))
    letI :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            (discreteMatrixKernel fun x y ↦ (Measure.dirac x ∗ stepMeasure) {y}) ^ n)
          P X := by
      simpa [stepMeasure, hkernel] using
        (inferInstance :
          IsMarkovProcessRealization
            (fun n : ℕ ↦ dirac_convolution_kernel stepMeasure ^ n)
            P X)
    letI :
        Kernel.IsIrreducible (Measure.count : Measure ℤ)
          (discreteMatrixKernel fun x y ↦ (Measure.dirac x ∗ stepMeasure) {y}) := by
      simpa [stepMeasure, dirac_convolution_kernel_apply] using
        biasedSimpleRandomWalkKernel_isIrreducible p hp0 hp1
    have hrec_or_trans :
        IsRecurrentMarkovChain P X ∨ ∀ x : ℤ, IsTransientState P X x :=
      irreducibleMarkovChain_recurrent_or_transient_of_discreteMatrixKernel_isIrreducible
        (p := fun x y ↦ (Measure.dirac x ∗ stepMeasure) {y})
        (P := P) (X := X)
    cases hrec_or_trans with
    | inl hrec =>
        exact False.elim (hnot_recurrent hrec)
    | inr htrans =>
        exact htrans

end ProbabilityTheory
