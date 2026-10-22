/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 8.32: rewrite the translated residual mean into the textbook conditional
mean. -/
lemma sumResidualMean_rewrite (μ1 μ2 α x : ℝ) :
    (μ1 - α * (μ1 + μ2)) + α * x = μ1 + α * (x - μ1 - μ2) := by
  ring

/-- Helper for Example 8.32: coercing the Gaussian variance parameter `⟨σ², _⟩ : ℝ≥0` back to
`ℝ` recovers the square `σ²`. -/
lemma gaussianSquareVariance_coe (σ : ℝ) :
    ((⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) : ℝ) = σ ^ 2 := by
  rfl

/-- Helper for Example 8.32: conditioning an affine perturbation `a * X + U` on `X` only shifts
the law of the independent residual `U`. -/
lemma condDistrib_affine_of_indepFun
    (P : Measure Ω) [IsFiniteMeasure P] {X U : Ω → ℝ}
    (hU : AEMeasurable U P) (hX : AEMeasurable X P) (a : ℝ) (hUX : IndepFun U X P) :
    condDistrib (fun ω ↦ a * X ω + U ω) X P =ᵐ[P.map X]
      fun x ↦ (P.map U).map (fun u ↦ a * x + u) := by
  let ν : Measure ℝ := P.map X
  let η : Measure ℝ := P.map U
  let κ : Kernel ℝ ℝ :=
    ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ η).map fun z : ℝ × ℝ ↦ a * z.1 + z.2
  have hAffine_meas : Measurable fun z : ℝ × ℝ ↦ a * z.1 + z.2 := by
    fun_prop
  have hPairAffine_meas : Measurable fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2) := by
    fun_prop
  have hκ_apply : ∀ x : ℝ, κ x = η.map (fun u ↦ a * x + u) := by
    intro x
    change
      (((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ η).map fun z : ℝ × ℝ ↦ a * z.1 + z.2) x =
        η.map (fun u ↦ a * x + u)
    rw [Kernel.map_apply _ hAffine_meas, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
    rw [Measure.dirac_prod, Measure.map_map hAffine_meas measurable_prodMk_left]
    rfl
  have hUX_map : P.map (fun ω ↦ (X ω, U ω)) = ν.prod η := by
    simpa [ν, η] using
      (indepFun_iff_map_prod_eq_prod_map_map hX hU).mp hUX.symm
  have hmap :
      P.map (fun ω ↦ (X ω, a * X ω + U ω)) =
        (ν.prod η).map (fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2)) := by
    rw [← hUX_map]
    change P.map ((fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2)) ∘ fun ω ↦ (X ω, U ω)) =
      Measure.map (fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2)) (Measure.map (fun ω ↦ (X ω, U ω)) P)
    rw [AEMeasurable.map_map_of_aemeasurable hPairAffine_meas.aemeasurable (hX.prodMk hU)]
  have hcomp :
      (ν.prod η).map (fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2)) = ν ⊗ₘ κ := by
    refine Measure.ext_prod ?_
    intro s t hs ht
    rw [Measure.map_apply hPairAffine_meas (hs.prod ht), Measure.compProd_apply_prod hs ht]
    rw [Measure.prod_apply (hPairAffine_meas (hs.prod ht))]
    have hslice :
        (fun x : ℝ ↦
          η (Prod.mk x ⁻¹' ((fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2)) ⁻¹' (s ×ˢ t)))) =
        s.indicator (fun x ↦ κ x t) := by
      funext x
      by_cases hx : x ∈ s
      · have hpre :
            Prod.mk x ⁻¹' ((fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2)) ⁻¹' (s ×ˢ t)) =
              (fun u : ℝ ↦ a * x + u) ⁻¹' t := by
          ext u
          simp [hx]
        rw [hpre, Set.indicator_of_mem hx, hκ_apply x]
        simpa using
          (Measure.map_apply (μ := η) (f := fun u : ℝ ↦ a * x + u) (by fun_prop) ht).symm
      · have hpre :
            Prod.mk x ⁻¹' ((fun z : ℝ × ℝ ↦ (z.1, a * z.1 + z.2)) ⁻¹' (s ×ˢ t)) = ∅ := by
          ext u
          simp [hx]
        simp [hpre, Set.indicator, hx]
    rw [hslice, lintegral_indicator hs]
  have hkernel :
      P.map (fun ω ↦ (X ω, a * X ω + U ω)) = P.map X ⊗ₘ κ := by
    simpa [ν] using hmap.trans hcomp
  have hcond :
      condDistrib (fun ω ↦ a * X ω + U ω) X P =ᵐ[P.map X] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd X ((hX.const_mul a).add hU) hkernel
  filter_upwards [hcond] with x hx
  rw [hx, hκ_apply]

/-- Helper for Example 8.32: the residual-sum pair obtained from `(Z₁, Z₂)` by an affine linear
change of variables is jointly Gaussian. -/
lemma sumResidualPairHasGaussianLaw
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
    let X : Ω → ℝ := Z1 + Z2
    let U : Ω → ℝ := fun ω ↦ Z1 ω - α * X ω
    HasGaussianLaw (fun ω ↦ (U ω, X ω)) P := by
  let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
  let X : Ω → ℝ := Z1 + Z2
  let U : Ω → ℝ := fun ω ↦ Z1 ω - α * X ω
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ) -
        α • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hpair : HasGaussianLaw (fun ω ↦ (Z1 ω, Z2 ω)) P := by
    -- Proof comment: independent Gaussian coordinates are jointly Gaussian.
    exact hindep.hasGaussianLaw hZ1.hasGaussianLaw hZ2.hasGaussianLaw
  have hL :
      (L ∘ fun ω ↦ (Z1 ω, Z2 ω)) =ᵐ[P] fun ω ↦ (U ω, X ω) := by
    -- Proof comment: `L` is chosen so that its coordinates are exactly the residual and the sum.
    filter_upwards [] with ω
    simp [L, U, X, α, sub_eq_add_neg, mul_add, add_comm]
  exact (hpair.map L).congr hL

/-- Helper for Example 8.32: the regression residual `U := Z₁ - α (Z₁ + Z₂)` is uncorrelated with
the sum `X := Z₁ + Z₂`. -/
lemma sumResidualCovariance_eq_zero
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
    let X : Ω → ℝ := Z1 + Z2
    let U : Ω → ℝ := fun ω ↦ Z1 ω - α * X ω
    cov[U, X; P] = 0 := by
  letI : IsProbabilityMeasure P := hZ1.isProbabilityMeasure
  let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
  let X : Ω → ℝ := Z1 + Z2
  let U : Ω → ℝ := fun ω ↦ Z1 ω - α * X ω
  suffices hmain : cov[U, X; P] = 0 by
    simpa [α, X, U] using hmain
  have hZ1_mem : MemLp Z1 2 P := hZ1.hasGaussianLaw.memLp_two
  have hZ2_mem : MemLp Z2 2 P := hZ2.hasGaussianLaw.memLp_two
  have hX_mem : MemLp X 2 P := by
    simpa [X] using hZ1_mem.add hZ2_mem
  have hαX_mem : MemLp (fun ω ↦ α * X ω) 2 P := by
    simpa [Pi.smul_apply] using hX_mem.const_mul α
  have hcov12 : cov[Z1, Z2; P] = 0 := hindep.covariance_eq_zero hZ1_mem hZ2_mem
  have hcovZ1X : cov[Z1, X; P] = σ1 ^ 2 := by
    -- Proof comment: expand against `X = Z₁ + Z₂` and remove the mixed covariance by independence.
    dsimp [X]
    rw [covariance_add_right hZ1_mem hZ1_mem hZ2_mem, hcov12, add_zero,
      covariance_self hZ1_mem.aemeasurable, hZ1.variance_eq, variance_id_gaussianReal]
    simp
  have hvarX : Var[X; P] = σ1 ^ 2 + σ2 ^ 2 := by
    -- Proof comment: the sum variance is the sum of the diagonal variances
    -- because the cross term vanishes.
    dsimp [X]
    rw [variance_add hZ1_mem hZ2_mem, hcov12, hZ1.variance_eq,
      hZ2.variance_eq, variance_id_gaussianReal, variance_id_gaussianReal]
    simp
  by_cases hsum : σ1 ^ 2 + σ2 ^ 2 = 0
  · have hσ1 : σ1 = 0 := by
      nlinarith [sq_nonneg σ1, sq_nonneg σ2]
    have hσ2 : σ2 = 0 := by
      nlinarith [sq_nonneg σ1, sq_nonneg σ2]
    have hU_eq : U = Z1 := by
      funext ω
      simp [U, X, α, hσ1, hσ2]
    -- Proof comment: in the degenerate branch both Gaussian variances vanish,
    -- so the covariance is zero.
    rw [hU_eq]
    simpa [hσ1] using hcovZ1X
  · -- Proof comment: rewrite `cov[U, X]` as `cov[Z₁, X] - α Var[X]` and simplify the scalar factor.
    dsimp [U]
    rw [covariance_fun_sub_left hZ1_mem hαX_mem hX_mem,
      covariance_const_mul_left, covariance_self hX_mem.aemeasurable, hcovZ1X, hvarX]
    dsimp [α]
    field_simp [hsum]
    ring

/-- Helper for Example 8.32: once the residual-sum pair is Gaussian and uncorrelated, the residual
is independent of the sum. -/
lemma sumResidual_indepFun
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
    let X : Ω → ℝ := Z1 + Z2
    let U : Ω → ℝ := fun ω ↦ Z1 ω - α * X ω
    IndepFun U X P := by
  let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
  let X : Ω → ℝ := Z1 + Z2
  let U : Ω → ℝ := fun ω ↦ Z1 ω - α * X ω
  -- Route correction: the old monolithic proof mixed Gaussian transport and covariance algebra;
  -- the proof is now split into those two stable helper lemmas.
  simpa [α, X, U] using
    (sumResidualPairHasGaussianLaw P μ1 μ2 σ1 σ2 hZ1 hZ2 hindep).indepFun_of_covariance_eq_zero
      (sumResidualCovariance_eq_zero P μ1 μ2 σ1 σ2 hZ1 hZ2 hindep)

/-- Helper for Example 8.32: the regression residual of `Z₁` against `Z₁ + Z₂` is Gaussian with
the textbook mean and variance. -/
lemma sumResidualLaw_eq_gaussian
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
    let U : Ω → ℝ := fun ω ↦ Z1 ω - α * (Z1 ω + Z2 ω)
    P.map U =
      gaussianReal
        (μ1 - α * (μ1 + μ2))
        ⟨(σ1 ^ 2 * σ2 ^ 2) / (σ1 ^ 2 + σ2 ^ 2), by positivity⟩ := by
  let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
  let U : Ω → ℝ := fun ω ↦ Z1 ω - α * (Z1 ω + Z2 ω)
  by_cases hsum : σ1 ^ 2 + σ2 ^ 2 = 0
  · have hσ1 : σ1 = 0 := by
      nlinarith [sq_nonneg σ1, sq_nonneg σ2]
    have hσ2 : σ2 = 0 := by
      nlinarith [sq_nonneg σ1, sq_nonneg σ2]
    -- Proof comment: when both variances vanish, `Z₁` is already the deterministic residual.
    simpa [U, α, hsum, hσ1, hσ2] using hZ1.map_eq
  · let c1 : ℝ := σ2 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
    let c2 : ℝ := -(σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2))
    have hU_repr : U = fun ω ↦ c1 * Z1 ω + c2 * Z2 ω := by
      funext ω
      dsimp [U, α, c1, c2]
      field_simp [hsum]
      ring_nf
    have hscaled1 :
        HasLaw (fun ω ↦ c1 * Z1 ω)
          (gaussianReal (c1 * μ1)
            (⟨c1 ^ 2, sq_nonneg c1⟩ * ⟨σ1 ^ 2, sq_nonneg σ1⟩)) P :=
      gaussianReal_const_mul hZ1 c1
    have hscaled2 :
        HasLaw (fun ω ↦ c2 * Z2 ω)
          (gaussianReal (c2 * μ2)
            (⟨c2 ^ 2, sq_nonneg c2⟩ * ⟨σ2 ^ 2, sq_nonneg σ2⟩)) P :=
      gaussianReal_const_mul hZ2 c2
    have hscaled_indep :
        IndepFun (fun ω ↦ c1 * Z1 ω) (fun ω ↦ c2 * Z2 ω) P :=
      by
        -- Proof comment: scaling each coordinate is a measurable
        -- postcomposition of the original pair.
        simpa [Function.comp] using
          hindep.comp (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
    have hsum_map :
        P.map (fun ω ↦ c1 * Z1 ω + c2 * Z2 ω) =
          gaussianReal
            (c1 * μ1 + c2 * μ2)
            ((⟨c1 ^ 2, sq_nonneg c1⟩ * ⟨σ1 ^ 2, sq_nonneg σ1⟩) +
              (⟨c2 ^ 2, sq_nonneg c2⟩ * ⟨σ2 ^ 2, sq_nonneg σ2⟩)) := by
      simpa using
        gaussianReal_add_gaussianReal_of_indepFun hscaled_indep hscaled1.map_eq hscaled2.map_eq
    have hmean :
        c1 * μ1 + c2 * μ2 = μ1 - α * (μ1 + μ2) := by
      dsimp [α, c1, c2]
      field_simp [hsum]
      ring_nf
    have hvar_real :
        (c1 ^ 2) * (σ1 ^ 2) + (c2 ^ 2) * (σ2 ^ 2) = (σ1 ^ 2 * σ2 ^ 2) / (σ1 ^ 2 + σ2 ^ 2) := by
      dsimp [c1, c2]
      field_simp [hsum]
      ring_nf
    -- Proof comment: rewrite the residual as a sum of two independent scaled Gaussians.
    calc
      P.map U = P.map (fun ω ↦ c1 * Z1 ω + c2 * Z2 ω) := by rw [hU_repr]
      _ = gaussianReal
            (c1 * μ1 + c2 * μ2)
            ((⟨c1 ^ 2, sq_nonneg c1⟩ * ⟨σ1 ^ 2, sq_nonneg σ1⟩) +
              (⟨c2 ^ 2, sq_nonneg c2⟩ * ⟨σ2 ^ 2, sq_nonneg σ2⟩)) := by
          simpa using hsum_map
      _ = gaussianReal
            (μ1 - α * (μ1 + μ2))
            ⟨(σ1 ^ 2 * σ2 ^ 2) / (σ1 ^ 2 + σ2 ^ 2), by positivity⟩ := by
          apply gaussianReal_ext_iff.2
          constructor
          · exact hmean
          · apply Subtype.ext
            exact hvar_real

-- Proof sketch: use `ProbabilityTheory.condDistrib` as the regular conditional distribution of
-- `Z₁` given `Z₁ + Z₂`. The independent Gaussian laws imply that `(Z₁ + Z₂, Z₁)` is jointly
-- Gaussian, compute its mean and covariance, and then identify the disintegration along the first
-- coordinate with the one-dimensional Gaussian law having the textbook conditional mean and
-- conditional variance.
/-- Example 8.32: in kernel form, if `Z₁` and `Z₂` are independent Gaussian random variables with
laws `N(μ₁, σ₁²)` and `N(μ₂, σ₂²)`, then the regular conditional distribution kernel of `Z₁` given
`Z₁ + Z₂` is, for `P.map (Z₁ + Z₂)`-almost every `x`, the Gaussian law
`N(μ₁ + (σ₁² / (σ₁² + σ₂²)) (x - μ₁ - μ₂), (σ₁²σ₂²)/(σ₁² + σ₂²))`. -/
theorem condDistrib_gaussian_left_given_sum_ae_eq
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    letI : IsProbabilityMeasure P := hZ1.isProbabilityMeasure
    condDistrib Z1 (Z1 + Z2) P =ᵐ[P.map (Z1 + Z2)]
      fun x ↦
        gaussianReal
          (μ1 + (σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)) * (x - μ1 - μ2))
          ⟨(σ1 ^ 2 * σ2 ^ 2) / (σ1 ^ 2 + σ2 ^ 2), by positivity⟩ := by
  letI : IsProbabilityMeasure P := hZ1.isProbabilityMeasure
  let α : ℝ := σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)
  let X : Ω → ℝ := Z1 + Z2
  let U : Ω → ℝ := fun ω ↦ Z1 ω - α * X ω
  have hX : AEMeasurable X P := by
    -- Proof comment: the conditioning variable is the measurable sum `Z₁ + Z₂`.
    simpa [X] using hZ1.aemeasurable.add hZ2.aemeasurable
  have hU : AEMeasurable U P := by
    -- Proof comment: the residual is an affine combination of measurable random variables.
    simpa [U, X, Pi.smul_apply] using
      hZ1.aemeasurable.sub ((hZ1.aemeasurable.add hZ2.aemeasurable).const_mul α)
  have hZ1_repr : (fun ω ↦ α * X ω + U ω) = Z1 := by
    -- Proof comment: this is the regression decomposition `Z₁ = α X + U`.
    funext ω
    dsimp [U, X]
    ring
  have hcond :
      condDistrib Z1 X P =ᵐ[P.map X]
        fun x ↦ (P.map U).map (fun u ↦ α * x + u) := by
    simpa [hZ1_repr] using
      condDistrib_affine_of_indepFun P hU hX α
        (sumResidual_indepFun P μ1 μ2 σ1 σ2 hZ1 hZ2 hindep)
  have hU_map := sumResidualLaw_eq_gaussian P μ1 μ2 σ1 σ2 hZ1 hZ2 hindep
  -- Proof comment: translate the residual Gaussian by `x ↦ α * x + u` and rewrite the mean.
  filter_upwards [hcond] with x hx
  rw [hx]
  simpa [α, U, X, gaussianReal_map_const_add, sumResidualMean_rewrite μ1 μ2 α x] using
    congrArg (fun ν : Measure ℝ ↦ ν.map (fun u ↦ α * x + u)) hU_map

/-- Pointwise form of `condDistrib_gaussian_left_given_sum_ae_eq`. -/
theorem condDistrib_gaussian_left_given_sum_ae_eq_apply
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    letI : IsProbabilityMeasure P := hZ1.isProbabilityMeasure
    ∀ᵐ x ∂P.map (Z1 + Z2),
      condDistrib Z1 (Z1 + Z2) P x =
        gaussianReal
          (μ1 + (σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)) * (x - μ1 - μ2))
          ⟨(σ1 ^ 2 * σ2 ^ 2) / (σ1 ^ 2 + σ2 ^ 2), by positivity⟩ := by
  simpa using condDistrib_gaussian_left_given_sum_ae_eq P μ1 μ2 σ1 σ2 hZ1 hZ2 hindep
