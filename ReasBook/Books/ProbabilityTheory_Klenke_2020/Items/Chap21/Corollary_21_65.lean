/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_64

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "PathSpace" => C(NNReal, ℝ)

/-- Helper for Corollary 21.65: restricting independent process-path random variables to a finite
time family preserves independence. -/
lemma indepFun_restrict_of_indepProcessPaths
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ)
    (I : Finset NNReal) :
    IndepFun (fun ω ↦ I.restrict (fun t ↦ W t ω)) (fun ω ↦ I.restrict (fun t ↦ Wtilde t ω)) μ := by
  -- Proof comment: compose the path-valued independence with the measurable finite restriction map.
  simpa using hindep.comp (hφ := Finset.measurable_restrict I) (hψ := Finset.measurable_restrict I)

/-- Helper for Corollary 21.65: independence of the whole process paths forces every mixed
fixed-time covariance to vanish. -/
lemma covariance_eq_zero_of_indepProcessPaths
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ)
    (s t : NNReal) :
    cov[W s, Wtilde t; μ] = 0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hindepEval : (W s) ⟂ᵢ[μ] (Wtilde t) := by
    -- Proof comment: fixed-time evaluation is measurable on the ambient path space.
    simpa using hindep.comp (hφ := measurable_pi_apply s) (hψ := measurable_pi_apply t)
  exact hindepEval.covariance_eq_zero
    (brownianEval_memLp_two_ofBrownianMotion hW s)
    (brownianEval_memLp_two_ofBrownianMotion hWtilde t)

/-- Helper for Corollary 21.65: multiplying the normalization constant by `Real.sqrt 2` gives
`1`. -/
lemma sqrt_two_mul_inv_sqrt_two : Real.sqrt 2 * (1 / Real.sqrt 2 : ℝ) = 1 := by
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  -- Proof comment: the normalization factor is the reciprocal of `Real.sqrt 2`.
  field_simp [hsqrt_ne]

/-- Helper for Corollary 21.65: scaling two paths scales each dyadic mixed partition sum by the
product of the two scalars. -/
lemma dyadicQuadraticCovariationSum_smul_eq_local
    (a b : ℝ) (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadic_quadratic_covariation_sum (a • F) (b • G) T n =
      (a * b) * dyadic_quadratic_covariation_sum F G T n := by
  let N := partitionBoundIndex Definition2158.dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k)
  -- Proof comment: both scalar factors pull through each dyadic increment and combine into
  -- `a * b`.
  rw [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum]
  have hscaled :
      Finset.sum (Finset.range N)
          (fun k ↦
            ((a • F) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                (a • F) (Definition2158.dyadicPartitionSequence n k)) *
              ((b • G) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                (b • G) (Definition2158.dyadicPartitionSequence n k))) =
        Finset.sum (Finset.range N) (fun k ↦ (a * ΔF k) * (b * ΔG k)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hFsmul :
        a * F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
            a * F (Definition2158.dyadicPartitionSequence n k) =
          a * ΔF k := by
      dsimp [ΔF]
      ring
    have hGsmul :
        b * G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
            b * G (Definition2158.dyadicPartitionSequence n k) =
          b * ΔG k := by
      dsimp [ΔG]
      ring
    simp [Pi.smul_apply, hFsmul, hGsmul]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          ((a • F) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              (a • F) (Definition2158.dyadicPartitionSequence n k)) *
            ((b • G) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              (b • G) (Definition2158.dyadicPartitionSequence n k))) =
        Finset.sum (Finset.range N) (fun k ↦ (a * ΔF k) * (b * ΔG k)) := hscaled
    _ = Finset.sum (Finset.range N) (fun k ↦ (a * b) * (ΔF k * ΔG k)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring
    _ = (a * b) * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) := by
      rw [Finset.mul_sum]
    _ = (a * b) * dyadic_quadratic_covariation_sum F G T n := by
      simp [N, ΔF, ΔG, dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum]

/-- Helper for Corollary 21.65: scaling both paths scales the dyadic quadratic-covariation
witness by the product of the two scalars. -/
lemma hasQuadraticCovariationAlong_smul_local
    {F G : PathSpace} {covFG : NNReal → ℝ}
    (hFG : HasQuadraticCovariationAlong F G covFG) (a b : ℝ) :
    HasQuadraticCovariationAlong (a • F) (b • G) (fun T ↦ (a * b) * covFG T) := by
  intro T
  have hsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the scaled mixed dyadic sum and then move the scalar factor outside
  -- the limit.
  convert hsum.const_mul (a * b) using 1
  ext n
  simpa [dyadic_quadratic_covariation_sum] using
    (dyadicQuadraticCovariationSum_smul_eq_local a b F G T n)

/-- Helper for Corollary 21.65: polarization turns square-variation witnesses of `F + G` and
`F - G` into a dyadic quadratic-covariation witness of `F` and `G`. -/
lemma hasQuadraticCovariationAlong_polarization_local
    {F G : PathSpace} {brAdd brSub : NNReal → ℝ}
    (hAdd : HasSquareVariationAlong (F + G) brAdd)
    (hSub : HasSquareVariationAlong (F - G) brSub) :
    HasQuadraticCovariationAlong F G ((1 / 4 : ℝ) • (brAdd - brSub)) := by
  intro T
  have hpolarized :
      Tendsto
        (fun n ↦
          ((dyadic_p_variation_sum 2 (F + G) T n) -
            (dyadic_p_variation_sum 2 (F - G) T n)) / 4)
        atTop
        (nhds (((1 / 4 : ℝ) • (brAdd - brSub)) T)) := by
    -- Proof comment: the mixed dyadic sums are the polarized difference of the two square
    -- variation sums, so their limit is the same polarized difference of the witness paths.
    simpa [Pi.smul_apply, Pi.sub_apply, div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((HasSquareVariationAlongPartition.tendsto_partition_sum hAdd T).sub
        (HasSquareVariationAlongPartition.tendsto_partition_sum hSub T)).mul_const (1 / 4 : ℝ)
  convert hpolarized using 1
  ext n
  simpa [dyadic_quadratic_covariation_sum, dyadic_p_variation_sum] using
    (partitionQuadraticCovariationSum_eq_polarization
      Definition2158.dyadicPartitionSequence F G T n)

/-- Helper for Corollary 21.65: almost every continuous Brownian sample path has dyadic square
variation `T ↦ T`. -/
lemma aeHasSquareVariationAlongIdentityDyadic_ofBrownian
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W) :
    ∀ᵐ ω ∂μ,
      ∀ hWω : Continuous (processPath W ω),
        HasSquareVariationAlong
          (⟨processPath W ω, hWω⟩ : PathSpace)
          (fun T : NNReal ↦ (T : ℝ)) := by
  -- Route correction: use the earlier dyadic Brownian owner theorem instead of the later
  -- continuous-square-variation detour through `Theorem_21_70`.
  filter_upwards
    [hW.ae_tendsto_partitionQuadraticVariationApproximationUpTo
      Definition2158.dyadicPartitionSequence] with ω hω
  intro hWω
  -- Proof comment: specialize the Brownian convergence theorem at the chosen sample path and
  -- then rewrite the constant-weight quadratic sum to the dyadic square-variation sum.
  intro T
  have hWeighted :
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ))
            (⟨processPath W ω, hWω⟩ : PathSpace)
            Definition2158.dyadicPartitionSequence
            T
            n)
        atTop
        (nhds (T : ℝ)) := by
    simpa [processPath] using hω T
  convert hWeighted using 1
  ext n
  symm
  exact
    _root_.weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum
      (X := (⟨processPath W ω, hWω⟩ : PathSpace))
      (P := Definition2158.dyadicPartitionSequence)
      (T := T)
      (n := n)

/-- Helper for Corollary 21.65: if the normalized sum and normalized difference both have dyadic
square variation `T ↦ T`, then the original two paths have zero dyadic quadratic covariation. -/
lemma hasQuadraticCovariationAlong_zero_of_normalizedIdentitySquareVariation
    {F G : PathSpace}
    (hAdd :
      HasSquareVariationAlong
        (((1 / Real.sqrt 2 : ℝ) • F) + ((1 / Real.sqrt 2 : ℝ) • G))
        (fun T : NNReal ↦ (T : ℝ)))
    (hSub :
      HasSquareVariationAlong
        (((1 / Real.sqrt 2 : ℝ) • F) - ((1 / Real.sqrt 2 : ℝ) • G))
        (fun T : NNReal ↦ (T : ℝ))) :
    HasQuadraticCovariationAlong F G 0 := by
  have hScaled :
    HasQuadraticCovariationAlong
        (((1 / Real.sqrt 2 : ℝ) • F))
        (((1 / Real.sqrt 2 : ℝ) • G))
        0 := by
    -- Proof comment: polarization turns the two normalized square-variation witnesses into the
    -- covariation witness for the normalized pair, and the two identity paths cancel.
    simpa [Pi.smul_apply] using
      (hasQuadraticCovariationAlong_polarization_local
        (F := ((1 / Real.sqrt 2 : ℝ) • F))
        (G := ((1 / Real.sqrt 2 : ℝ) • G))
        (brAdd := fun T : NNReal ↦ (T : ℝ))
        (brSub := fun T : NNReal ↦ (T : ℝ))
        hAdd hSub)
  -- Proof comment: rescale both normalized paths by `√2` to recover the original pair.
  simpa [smul_smul, sqrt_two_mul_inv_sqrt_two] using
    (hasQuadraticCovariationAlong_smul_local hScaled (Real.sqrt 2) (Real.sqrt 2))

/-- Helper for Corollary 21.65: every finite restriction of the normalized sum
`((W + Wtilde) / √2)` has a Gaussian law. -/
lemma hasGaussianLaw_restrict_normalizedAdd_of_indep
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ)
    (I : Finset NNReal) :
    HasGaussianLaw
      (fun ω ↦
        I.restrict
          (fun t ↦
            (1 / Real.sqrt 2 : ℝ) * W t ω + (1 / Real.sqrt 2 : ℝ) * Wtilde t ω))
      μ := by
  let a : ℝ := 1 / Real.sqrt 2
  have hWLaw :
      HasGaussianLaw (fun ω ↦ I.restrict (W · ω)) μ :=
    hW.isGaussianProcess.hasGaussianLaw I
  have hWtildeLaw :
      HasGaussianLaw (fun ω ↦ I.restrict (Wtilde · ω)) μ :=
    hWtilde.isGaussianProcess.hasGaussianLaw I
  have hJoint :
      HasGaussianLaw
        (fun ω ↦ I.restrict (W · ω) + I.restrict (Wtilde · ω)) μ :=
    (indepFun_restrict_of_indepProcessPaths hindep I).hasGaussianLaw hWLaw hWtildeLaw |>.add
  have hScaled :
      HasGaussianLaw
        (a • fun ω ↦ I.restrict (W · ω) + I.restrict (Wtilde · ω)) μ :=
    hJoint.smul a
  have hEq :
      (a • fun ω ↦ I.restrict (W · ω) + I.restrict (Wtilde · ω)) =
        fun ω ↦ I.restrict (fun t ↦ a * W t ω + a * Wtilde t ω) := by
    funext ω
    ext i
    simp [Pi.smul_apply, mul_add]
  -- Proof comment: finite-dimensional Gaussianity is preserved by summing the independent
  -- Brownian restriction vectors and scaling by the constant `1 / √2`.
  simpa [a] using hScaled.congr (Filter.Eventually.of_forall (fun ω ↦ congrFun hEq ω))

/-- Helper for Corollary 21.65: the normalized sum `((W + Wtilde) / √2)` is centered at each
fixed time. -/
lemma integral_normalizedAdd_eq_zero
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (t : NNReal) :
    ∫ ω, ((1 / Real.sqrt 2 : ℝ) * W t ω + (1 / Real.sqrt 2 : ℝ) * Wtilde t ω) ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let a : ℝ := 1 / Real.sqrt 2
  have hIntW : Integrable (fun ω ↦ a * W t ω) μ :=
    ((brownianEval_memLp_two_ofBrownianMotion hW t).const_mul a).integrable (by norm_num)
  have hIntWtilde : Integrable (fun ω ↦ a * Wtilde t ω) μ :=
    ((brownianEval_memLp_two_ofBrownianMotion hWtilde t).const_mul a).integrable (by norm_num)
  -- Proof comment: expectation is linear, and both Brownian marginals are centered.
  rw [integral_add hIntW hIntWtilde, integral_const_mul, integral_const_mul,
    IsBrownianMotion.mean_zero hW t, IsBrownianMotion.mean_zero hWtilde t]
  ring

/-- Helper for Corollary 21.65: the normalized sum `((W + Wtilde) / √2)` has Brownian covariance
kernel `s ∧ t`. -/
lemma covariance_normalizedAdd_eq
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ)
    (s t : NNReal) :
    cov[fun ω ↦ (1 / Real.sqrt 2 : ℝ) * W s ω + (1 / Real.sqrt 2 : ℝ) * Wtilde s ω,
      fun ω ↦ (1 / Real.sqrt 2 : ℝ) * W t ω + (1 / Real.sqrt 2 : ℝ) * Wtilde t ω; μ]
      =
        ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let a : ℝ := 1 / Real.sqrt 2
  have ha_sq : a ^ 2 = (1 / 2 : ℝ) := by
    simp [a]
  let x : ℝ := ((s ⊓ t : NNReal) : ℝ)
  have hsW_mem : MemLp (W s) 2 μ := brownianEval_memLp_two_ofBrownianMotion hW s
  have hsWtilde_mem : MemLp (Wtilde s) 2 μ := brownianEval_memLp_two_ofBrownianMotion hWtilde s
  have htW_mem : MemLp (W t) 2 μ := brownianEval_memLp_two_ofBrownianMotion hW t
  have htWtilde_mem : MemLp (Wtilde t) 2 μ := brownianEval_memLp_two_ofBrownianMotion hWtilde t
  have hsA_mem : MemLp (fun ω ↦ a * W s ω) 2 μ := hsW_mem.const_mul a
  have hsB_mem : MemLp (fun ω ↦ a * Wtilde s ω) 2 μ := hsWtilde_mem.const_mul a
  have htA_mem : MemLp (fun ω ↦ a * W t ω) 2 μ := htW_mem.const_mul a
  have htB_mem : MemLp (fun ω ↦ a * Wtilde t ω) 2 μ := htWtilde_mem.const_mul a
  have htSum_mem : MemLp (fun ω ↦ a * W t ω + a * Wtilde t ω) 2 μ := htA_mem.add htB_mem
  have hcross₁ : cov[W s, Wtilde t; μ] = 0 :=
    covariance_eq_zero_of_indepProcessPaths hW hWtilde hindep s t
  have hcross₂ : cov[Wtilde s, W t; μ] = 0 := by
    rw [covariance_comm]
    simpa using covariance_eq_zero_of_indepProcessPaths hW hWtilde hindep t s
  have hWW : cov[W s, W t; μ] = x := by
    simpa [x] using IsBrownianMotion.covariance_eq hW s t
  have hWtildeWtilde : cov[Wtilde s, Wtilde t; μ] = x := by
    simpa [x] using IsBrownianMotion.covariance_eq hWtilde s t
  -- Proof comment: bilinearity reduces the covariance to four terms; the mixed ones vanish by
  -- independence and the two diagonal Brownian terms add up to `x`.
  have hCov :
      cov[fun ω ↦ a * W s ω + a * Wtilde s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ] = x := by
    have hLeft :
        cov[fun ω ↦ a * W s ω + a * Wtilde s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ]
          =
            cov[fun ω ↦ a * W s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ] +
              cov[fun ω ↦ a * Wtilde s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ] := by
      simpa [Pi.add_apply] using
        (covariance_add_left hsA_mem hsB_mem htSum_mem :
          cov[(fun ω ↦ a * W s ω) + fun ω ↦ a * Wtilde s ω,
            fun ω ↦ a * W t ω + a * Wtilde t ω; μ]
            =
              cov[fun ω ↦ a * W s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ] +
                cov[fun ω ↦ a * Wtilde s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ])
    have hRight₁ :
        cov[fun ω ↦ a * W s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ]
          =
            cov[fun ω ↦ a * W s ω, fun ω ↦ a * W t ω; μ] +
              cov[fun ω ↦ a * W s ω, fun ω ↦ a * Wtilde t ω; μ] := by
      simpa [Pi.add_apply] using
        (covariance_add_right hsA_mem htA_mem htB_mem :
          cov[fun ω ↦ a * W s ω, (fun ω ↦ a * W t ω) + fun ω ↦ a * Wtilde t ω; μ]
            =
              cov[fun ω ↦ a * W s ω, fun ω ↦ a * W t ω; μ] +
                cov[fun ω ↦ a * W s ω, fun ω ↦ a * Wtilde t ω; μ])
    have hRight₂ :
        cov[fun ω ↦ a * Wtilde s ω, fun ω ↦ a * W t ω + a * Wtilde t ω; μ]
          =
            cov[fun ω ↦ a * Wtilde s ω, fun ω ↦ a * W t ω; μ] +
              cov[fun ω ↦ a * Wtilde s ω, fun ω ↦ a * Wtilde t ω; μ] := by
      simpa [Pi.add_apply] using
        (covariance_add_right hsB_mem htA_mem htB_mem :
          cov[fun ω ↦ a * Wtilde s ω, (fun ω ↦ a * W t ω) + fun ω ↦ a * Wtilde t ω; μ]
            =
              cov[fun ω ↦ a * Wtilde s ω, fun ω ↦ a * W t ω; μ] +
                cov[fun ω ↦ a * Wtilde s ω, fun ω ↦ a * Wtilde t ω; μ])
    rw [hLeft, hRight₁, hRight₂]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    rw [hWW, hcross₁, hcross₂, hWtildeWtilde]
    ring_nf
    rw [ha_sq]
    ring
  simpa [a, x] using hCov

/-- Helper for Corollary 21.65: the normalized sum `((W + Wtilde) / √2)` is again a Brownian
motion when the two Brownian paths are independent. -/
lemma isBrownianMotion_normalizedAdd_of_indep
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ)
    :
    IsBrownianMotion μ
      (fun t ω ↦ (1 / Real.sqrt 2 : ℝ) * W t ω + (1 / Real.sqrt 2 : ℝ) * Wtilde t ω) := by
  -- Route correction: use the canonical Brownian characterization from Theorem 21.11 instead of
  -- re-implementing the Gaussian-to-Brownian bridge in this item file.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: both Brownian motions start from `0`, so the linear combination does too.
    funext ω
    simp [hW.zero, hWtilde.zero]
  · exact ⟨fun I ↦ hasGaussianLaw_restrict_normalizedAdd_of_indep hW hWtilde hindep I⟩
  · intro t
    exact integral_normalizedAdd_eq_zero hW hWtilde t
  · intro s t
    exact covariance_normalizedAdd_eq hW hWtilde hindep s t
  · -- Proof comment: almost-sure continuity is stable under finite linear combinations.
    let a : ℝ := 1 / Real.sqrt 2
    filter_upwards [hW.continuous_paths, hWtilde.continuous_paths] with ω hWω hWtildeω
    simpa [processPath, a] using
      (hWω.const_mul a).add (hWtildeω.const_mul a)

/-- Helper for Corollary 21.65: negating a Brownian motion again yields a Brownian motion. -/
lemma brownianNeg
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W) :
    IsBrownianMotion μ (fun t ω ↦ -W t ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the time-zero value stays `0` after negating the path.
    funext ω
    simp [hW.zero]
  · -- Proof comment: independent increments are preserved by the measurable map `x ↦ -x`.
    simpa using hW.indepIncrements.neg
  · -- Proof comment: each increment of `-W` is the negative of the matching increment of `W`.
    intro r s t
    convert (hW.stationaryIncrements r s t).comp measurable_neg using 1
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
  · intro t ht
    -- Proof comment: centered Gaussian marginals are symmetric under sign change.
    simpa using ProbabilityTheory.gaussianReal_neg (hW.gaussian_marginal ht)
  · -- Proof comment: pointwise negation preserves continuity of each sample path.
    filter_upwards [hW.continuous_paths] with ω hω
    simpa [processPath] using hω.neg

/-- Helper for Corollary 21.65: the normalized difference `((W - Wtilde) / √2)` is again a
Brownian motion when the two Brownian paths are independent. -/
lemma isBrownianMotion_normalizedSub_of_indep
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ)
    :
    IsBrownianMotion μ
      (fun t ω ↦ (1 / Real.sqrt 2 : ℝ) * W t ω - (1 / Real.sqrt 2 : ℝ) * Wtilde t ω) := by
  -- Proof comment: rewrite the difference as the normalized sum with the negated second Brownian
  -- motion, then reuse the addition case.
  simpa [sub_eq_add_neg, mul_add, mul_comm, mul_left_comm, mul_assoc] using
    isBrownianMotion_normalizedAdd_of_indep hW (brownianNeg hWtilde) hindep.neg_right

/-- Helper for Corollary 21.65: almost surely, the normalized sum and normalized difference of
two independent Brownian paths both have dyadic square variation `T ↦ T`. -/
lemma aeNormalizedAddSub_haveIdentitySquareVariation
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ) :
    ∀ᵐ ω ∂μ,
      ∀ hWω : Continuous (processPath W ω),
      ∀ hWtildeω : Continuous (processPath Wtilde ω),
        HasSquareVariationAlong
          (((1 / Real.sqrt 2 : ℝ) • (⟨processPath W ω, hWω⟩ : PathSpace)) +
            ((1 / Real.sqrt 2 : ℝ) • (⟨processPath Wtilde ω, hWtildeω⟩ : PathSpace)))
          (fun T : NNReal ↦ (T : ℝ)) ∧
        HasSquareVariationAlong
          (((1 / Real.sqrt 2 : ℝ) • (⟨processPath W ω, hWω⟩ : PathSpace)) -
            ((1 / Real.sqrt 2 : ℝ) • (⟨processPath Wtilde ω, hWtildeω⟩ : PathSpace)))
          (fun T : NNReal ↦ (T : ℝ)) := by
  let hAddBrownian :=
    isBrownianMotion_normalizedAdd_of_indep hW hWtilde hindep
  let hSubBrownian :=
    isBrownianMotion_normalizedSub_of_indep hW hWtilde hindep
  filter_upwards
    [aeHasSquareVariationAlongIdentityDyadic_ofBrownian hAddBrownian,
      aeHasSquareVariationAlongIdentityDyadic_ofBrownian hSubBrownian] with ω hAddω hSubω
  intro hWω hWtildeω
  have hAddCont :
      Continuous
        (processPath
          (fun t ω ↦ (1 / Real.sqrt 2 : ℝ) * W t ω + (1 / Real.sqrt 2 : ℝ) * Wtilde t ω)
          ω) := by
    -- Proof comment: continuity of the normalized sum is inherited from the two input paths.
    simpa [processPath] using
      (hWω.const_mul (1 / Real.sqrt 2 : ℝ)).add
        (hWtildeω.const_mul (1 / Real.sqrt 2 : ℝ))
  have hSubCont :
      Continuous
        (processPath
          (fun t ω ↦ (1 / Real.sqrt 2 : ℝ) * W t ω - (1 / Real.sqrt 2 : ℝ) * Wtilde t ω)
          ω) := by
    -- Proof comment: the same continuity argument works for the normalized difference.
    simpa [processPath] using
      (hWω.const_mul (1 / Real.sqrt 2 : ℝ)).sub
        (hWtildeω.const_mul (1 / Real.sqrt 2 : ℝ))
  refine ⟨?_, ?_⟩
  · -- Proof comment: reinterpret the normalized Brownian sample path as the scaled path sum.
    simpa [processPath, Pi.smul_apply] using hAddω hAddCont
  · -- Proof comment: reinterpret the normalized Brownian sample path as the scaled path
    -- difference.
    simpa [processPath, Pi.smul_apply] using hSubω hSubCont

/- Corollary 21.65 is a `source-facing` process-level consequence in the Brownian-motion API.
Its core/canonical owner is `IsBrownianMotion`; the pathwise dyadic-bracket predicate
`HasQuadraticCovariationAlong` is only the `bridge/view` used in the almost-sure conclusion.
The primitive data are the two Brownian processes and independence of their process paths. -/

-- Proof sketch: the normalized sum and difference are Brownian motions, so each has dyadic
-- square variation `T ↦ T` almost surely. On that same event, Remark 21.61 polarizes the two
-- square-variation witnesses into zero dyadic covariation for the original pair.
/-- Corollary 21.65: if `W` and `Wtilde` are independent Brownian motions, then almost every pair
of sample paths has vanishing dyadic quadratic covariation; equivalently, `⟪W, Wtilde⟫_T = 0` for
every `T ≥ 0`. -/
theorem covariation_ae_eq_zero_of_indep_brownian
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ) :
    ∀ᵐ ω ∂μ,
      ∀ hWω : Continuous (processPath W ω),
      ∀ hWtildeω : Continuous (processPath Wtilde ω),
          HasQuadraticCovariationAlong
            ⟨processPath W ω, hWω⟩
            ⟨processPath Wtilde ω, hWtildeω⟩
            0 := by
  filter_upwards [aeNormalizedAddSub_haveIdentitySquareVariation hW hWtilde hindep] with ω hω
  intro hWω hWtildeω
  -- Route correction: abandon the mixed-increment horizon argument and follow the textbook
  -- polarization route through the normalized Brownian sum and difference.
  exact
    hasQuadraticCovariationAlong_zero_of_normalizedIdentitySquareVariation
      (F := ⟨processPath W ω, hWω⟩)
      (G := ⟨processPath Wtilde ω, hWtildeω⟩)
      (hAdd := (hω hWω hWtildeω).1)
      (hSub := (hω hWω hWtildeω).2)

end ProbabilityTheory
