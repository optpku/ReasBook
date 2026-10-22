/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Filter.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Assumption_6_1_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_7

noncomputable section

open Filter

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace TrustRegionAlgorithm

/-- Helper for Chapter06 Theorem 6.1.8: a finite set of active-successful indices leaves a tail
with no active-successful iterations. -/
lemma existsSuccessFreeTailOfFiniteActiveSuccessful
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (hfinite : Set.Finite {k : ℕ | A.activeSuccessfulAt k}) :
    ∃ N : ℕ, ∀ k ≥ N, ¬ A.activeSuccessfulAt k := by
  classical
  let s : Set ℕ := {k : ℕ | A.activeSuccessfulAt k}
  have hsFinite : s.Finite := by
    simpa [s] using hfinite
  by_cases hs : s.Nonempty
  · rcases Set.exists_max_image s id hsFinite hs with ⟨m, hm, hmax⟩
    refine ⟨m + 1, ?_⟩
    intro k hk hActiveSuccessful
    have hk_le : k ≤ m := hmax k (by simpa [s] using hActiveSuccessful)
    exact (Nat.not_succ_le_self m) (le_trans hk hk_le)
  · refine ⟨0, ?_⟩
    intro k _ hActiveSuccessful
    exact hs ⟨k, by simpa [s] using hActiveSuccessful⟩

/-- Helper for Chapter06 Theorem 6.1.8: on an exact-stop run, any tail iteration that is not
active-successful leaves the iterate unchanged. -/
lemma iterateSuccEq_of_notActiveSuccessful_exactStop
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (hε : A.ε = 0)
    (hStutter : ∀ k : ℕ, A.terminatedAt k → A.x (k + 1) = A.x k)
    {k : ℕ} (hk : ¬ A.activeSuccessfulAt k) :
    A.x (k + 1) = A.x k := by
  by_cases hActive : A.activeAt k
  · have hNotSuccessful : ¬ A.successfulAt k := fun hSuccessful ↦ hk ⟨hActive, hSuccessful⟩
    -- Active but unsuccessful iterations reject the trial step, so the iterate stays fixed.
    have hReject : ¬ A.η1 ≤ A.r k := by
      simpa [TrustRegionAlgorithm.successfulAt] using hNotSuccessful
    rw [A.iterate_update k hActive]
    simp [hReject]
  · -- Under exact stopping, every non-active iteration is already terminated.
    have hTerm : A.terminatedAt k := by
      rw [TrustRegionAlgorithm.terminatedAt, TrustRegionAlgorithm.activeAt_iff, hε] at *
      exact le_of_not_gt hActive
    exact hStutter k hTerm

/-- Helper for Chapter06 Theorem 6.1.8: once active-successful iterations disappear, the iterate
tail is constant with anchor `A.x N`. -/
lemma iterateEqAnchorOfSuccessFreeTail
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (hε : A.ε = 0)
    (hStutter : ∀ k : ℕ, A.terminatedAt k → A.x (k + 1) = A.x k)
    {N : ℕ}
    (hTail : ∀ k ≥ N, ¬ A.activeSuccessfulAt k) :
    ∀ k ≥ N, A.x k = A.x N := by
  intro k hk
  rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hStep :
          A.x (N + m + 1) = A.x (N + m) := by
        exact A.iterateSuccEq_of_notActiveSuccessful_exactStop hε hStutter
          (hTail (N + m) (Nat.le_add_right N m))
      -- Collapse one more tail step and then reuse the induction hypothesis.
      calc
        A.x (N + (m + 1)) = A.x (N + m + 1) := by
          simp [Nat.add_assoc]
        _ = A.x (N + m) := hStep
        _ = A.x N := ih (Nat.le_add_right N m)

/-- Helper for Chapter06 Theorem 6.1.8: a success-free exact-stop tail forces the whole iterate
sequence to converge to its anchor point. -/
lemma tendstoConstOfSuccessFreeTail
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (hε : A.ε = 0)
    (hStutter : ∀ k : ℕ, A.terminatedAt k → A.x (k + 1) = A.x k)
    {N : ℕ}
    (hTail : ∀ k ≥ N, ¬ A.activeSuccessfulAt k) :
    Tendsto A atTop (nhds (A.x N)) := by
  -- The eventually constant tail reduces convergence to `tendsto_const_nhds`.
  have hEventuallyEq : (fun _ : ℕ ↦ A.x N) =ᶠ[atTop] A := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    symm
    exact A.iterateEqAnchorOfSuccessFreeTail hε hStutter hTail k hk
  exact Tendsto.congr' hEventuallyEq tendsto_const_nhds

/-- Helper for Chapter06 Theorem 6.1.8: on a success-free exact-stop tail, gradient uniqueness
forces every later recorded gradient to agree with the anchor gradient. -/
lemma gradientEqAnchorOfSuccessFreeTail
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (hε : A.ε = 0)
    (hStutter : ∀ k : ℕ, A.terminatedAt k → A.x (k + 1) = A.x k)
    {N : ℕ}
    (hTail : ∀ k ≥ N, ¬ A.activeSuccessfulAt k)
    {k : ℕ} (hk : N ≤ k) :
    A.g k = A.g N := by
  have hx : A.x k = A.x N := A.iterateEqAnchorOfSuccessFreeTail hε hStutter hTail k hk
  -- The tail iterate is the same point, so the gradient witness is unique there.
  have hGradAtK : HasGradientAt f (A.g k) (A.x N) := by
    simpa [hx] using A.hasGradientAt k
  exact hGradAtK.unique (A.hasGradientAt N)

/-- Helper for Chapter06 Theorem 6.1.8: any active iteration of the positive-tolerance clone is
already active for the original exact-stop run. -/
lemma activeAt_of_positiveToleranceVariantActive
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    {ε' : ℝ} (hε' : 0 ≤ ε') (hε : A.ε = 0)
    {k : ℕ} (hk : ε' < ‖A.g k‖) :
    A.activeAt k := by
  rw [TrustRegionAlgorithm.activeAt_iff, hε, TrustRegionAlgorithm.gradientNormAt_eq]
  exact lt_of_le_of_lt hε' hk

/-- Helper for Chapter06 Theorem 6.1.8: replace the exact stopping tolerance by a positive
parameter while keeping all iterate, step, model, ratio, and radius data unchanged. -/
def positiveToleranceVariant
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (ε' : ℝ) (hε' : 0 ≤ ε') (hε : A.ε = 0) :
    TrustRegionAlgorithm n f where
  ε := ε'
  η1 := A.η1
  η2 := A.η2
  γ1 := A.γ1
  γ2 := A.γ2
  β₂ := A.β₂
  x0 := A.x0
  ΔMax := A.ΔMax
  Δ0 := A.Δ0
  x := A.x
  s := A.s
  g := A.g
  B := A.B
  r := A.r
  Δ := A.Δ
  epsilon_nonneg := hε'
  eta1_pos := A.eta1_pos
  eta1_le_eta2 := A.eta1_le_eta2
  eta2_lt_one := A.eta2_lt_one
  gamma1_mem := A.gamma1_mem
  gamma2_gt_one := A.gamma2_gt_one
  beta2_mem := A.beta2_mem
  deltaMax_pos := A.deltaMax_pos
  delta0_mem := A.delta0_mem
  x_zero := A.x_zero
  delta_zero := A.delta_zero
  delta_mem := A.delta_mem
  hasGradientAt := A.hasGradientAt
  B_symm := A.B_symm
  step_isApproximateSolution := fun k hk ↦
    A.step_isApproximateSolution k (A.activeAt_of_positiveToleranceVariantActive hε' hε hk)
  ratio_eq := fun k hk ↦
    A.ratio_eq k (A.activeAt_of_positiveToleranceVariantActive hε' hε hk)
  iterate_update := fun k hk ↦
    A.iterate_update k (A.activeAt_of_positiveToleranceVariantActive hε' hε hk)
  radius_update := fun k hk ↦
    A.radius_update k (A.activeAt_of_positiveToleranceVariantActive hε' hε hk)

/-- Helper for Chapter06 Theorem 6.1.8: the positive-tolerance clone keeps the same successful
and very-successful predicates because it copies `η₁`, `η₂`, and `r`. -/
@[simp] lemma positiveToleranceVariant_verySuccessfulAt_iff
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (ε' : ℝ) (hε' : 0 ≤ ε') (hε : A.ε = 0) (k : ℕ) :
    (A.positiveToleranceVariant ε' hε' hε).verySuccessfulAt k ↔ A.verySuccessfulAt k :=
  Iff.rfl

/-- Helper for Chapter06 Theorem 6.1.8: the positive-tolerance clone keeps the same step radius
sequence. -/
@[simp] lemma positiveToleranceVariant_delta_eq
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (ε' : ℝ) (hε' : 0 ≤ ε') (hε : A.ε = 0) (k : ℕ) :
    (A.positiveToleranceVariant ε' hε' hε).Δ k = A.Δ k :=
  rfl

/-- Helper for Chapter06 Theorem 6.1.8: the positive-tolerance clone keeps the same gradient
sequence. -/
@[simp] lemma positiveToleranceVariant_g_eq
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (ε' : ℝ) (hε' : 0 ≤ ε') (hε : A.ε = 0) (k : ℕ) :
    (A.positiveToleranceVariant ε' hε' hε).g k = A.g k :=
  rfl

/-- Helper for Chapter06 Theorem 6.1.8: Assumption `(A₀)` transfers to the positive-tolerance
clone because its subproblems and steps are unchanged. -/
instance positiveToleranceVariant_trustRegionAssumptionA0
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    [TrustRegionAssumptionA0 f A.x0 A.subproblem A.s]
    (ε' : ℝ) (hε' : 0 ≤ ε') (hε : A.ε = 0) :
    TrustRegionAssumptionA0 f
      (A.positiveToleranceVariant ε' hε' hε).x0
      (A.positiveToleranceVariant ε' hε' hε).subproblem
      (A.positiveToleranceVariant ε' hε' hε).s := by
  let hA0 : TrustRegionAssumptionA0 f A.x0 A.subproblem A.s := inferInstance
  refine
    { hessianOperatorNorm_bounded := ?_
      levelSet_bounded := by simpa [positiveToleranceVariant] using hA0.levelSet_bounded
      contDiffOn_levelSet := by simpa [positiveToleranceVariant] using hA0.contDiffOn_levelSet
      step_norm_bounded := ?_ }
  · simpa [positiveToleranceVariant, TrustRegionAlgorithm.subproblem] using
      hA0.hessianOperatorNorm_bounded
  · simpa [positiveToleranceVariant, TrustRegionAlgorithm.subproblem] using
      hA0.step_norm_bounded

/-- Helper for Chapter06 Theorem 6.1.8: on any tail of active unsuccessful iterations, the
trust-region radius decays at least geometrically with factor `γ₁`. -/
lemma radiusGeometricDecayOnSuccessFreeActiveTail
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    {N : ℕ}
    (hTail : ∀ k ≥ N, A.activeAt k ∧ ¬ A.successfulAt k) :
    ∀ m : ℕ, A.Δ (N + m) ≤ A.γ1 ^ m * A.Δ N := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hk : A.activeAt (N + m) ∧ ¬ A.successfulAt (N + m) :=
        hTail (N + m) (Nat.le_add_right N m)
      have hShrink : A.Δ (N + m + 1) ≤ A.γ1 * A.Δ (N + m) :=
        (A.radius_shrink (N + m) hk.1 (lt_of_not_ge hk.2)).2
      have hγ1_nonneg : 0 ≤ A.γ1 := le_of_lt A.gamma1_mem.1
      -- Apply the shrink estimate once and then the induction hypothesis.
      calc
        A.Δ (N + (m + 1)) = A.Δ (N + m + 1) := by
          simp [Nat.add_assoc]
        _ ≤ A.γ1 * A.Δ (N + m) := hShrink
        _ ≤ A.γ1 * (A.γ1 ^ m * A.Δ N) := by
          exact mul_le_mul_of_nonneg_left ih hγ1_nonneg
        _ = A.γ1 ^ (m + 1) * A.Δ N := by
          ring_nf

/-- Helper for Chapter06 Theorem 6.1.8: the geometric radius bound eventually drops below any
positive threshold. -/
lemma exists_smallRadiusOfGeometricDecay
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    {N : ℕ}
    (hDecay : ∀ m : ℕ, A.Δ (N + m) ≤ A.γ1 ^ m * A.Δ N)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, A.Δ (N + m) < δ := by
  have hPow :
      Tendsto (fun m : ℕ ↦ A.γ1 ^ m * A.Δ N) atTop (nhds 0) := by
    have hPowLeft :
        Tendsto (fun m : ℕ ↦ A.Δ N * A.γ1 ^ m) atTop (nhds 0) := by
      simpa using Tendsto.const_mul (A.Δ N)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt A.gamma1_mem.1) A.gamma1_mem.2)
    simpa [mul_comm] using hPowLeft
  have hEventuallySmall :
      ∀ᶠ m : ℕ in atTop, A.γ1 ^ m * A.Δ N < δ :=
    hPow.eventually (Iio_mem_nhds hδ)
  rcases Filter.eventually_atTop.1 hEventuallySmall with ⟨M, hM⟩
  refine ⟨M, lt_of_le_of_lt (hDecay M) ?_⟩
  exact hM M le_rfl

end TrustRegionAlgorithm

/-- Chapter06 Theorem 6.1.8: under Assumption `(A₀)`, if the trust-region algorithm `A` has
only finitely many active successful iterations, uses exact stopping `A.ε = 0`, and stutters
after termination, then the iterate sequence converges to a first-order stationary point of `f`.
-/
theorem trustRegionAlgorithm_tendsto_stationary_of_finiteSuccessfulIterations
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    [TrustRegionAssumptionA0 f A.x0 A.subproblem A.s]
    (hfinite : Set.Finite {k : ℕ | A.activeSuccessfulAt k})
    (hε : A.ε = 0)
    (hStutter : ∀ k : ℕ, A.terminatedAt k → A.x (k + 1) = A.x k) :
    ∃ xStar : Point, Tendsto A atTop (nhds xStar) ∧ IsStationaryPoint f xStar := by
  rcases A.existsSuccessFreeTailOfFiniteActiveSuccessful hfinite with ⟨N, hTail⟩
  refine ⟨A.x N, ?_, ?_⟩
  · -- The success-free tail makes the iterate sequence eventually constant.
    exact A.tendstoConstOfSuccessFreeTail hε hStutter hTail
  · -- Route correction: prove stationarity directly from the success-free tail instead of using
    -- later Chapter 6 convergence results.
    rw [isStationaryPoint_iff]
    refine ⟨?_, (A.hasGradientAt N).differentiableAt⟩
    have hAnchorGradZero : A.g N = 0 := by
      by_contra hGradNe
      have hGradNormPos : 0 < ‖A.g N‖ := norm_pos_iff.mpr hGradNe
      have hTailGrad :
          ∀ k ≥ N, A.g k = A.g N := by
        intro k hk
        exact A.gradientEqAnchorOfSuccessFreeTail hε hStutter hTail hk
      have hTailActiveAndUnsuccessful :
          ∀ k ≥ N, A.activeAt k ∧ ¬ A.successfulAt k := by
        intro k hk
        have hActive : A.activeAt k := by
          rw [TrustRegionAlgorithm.activeAt_iff, hε, TrustRegionAlgorithm.gradientNormAt_eq,
            hTailGrad k hk]
          exact hGradNormPos
        have hNotSuccessful : ¬ A.successfulAt k := fun hSuccessful ↦ hTail k hk
          ⟨hActive, hSuccessful⟩
        exact ⟨hActive, hNotSuccessful⟩
      have hDecay :
          ∀ m : ℕ, A.Δ (N + m) ≤ A.γ1 ^ m * A.Δ N :=
        A.radiusGeometricDecayOnSuccessFreeActiveTail hTailActiveAndUnsuccessful
      let ε' : ℝ := ‖A.g N‖ / 2
      have hε'_pos : 0 < ε' := by
        dsimp [ε']
        linarith
      let A' := A.positiveToleranceVariant ε' hε'_pos.le hε
      rcases A'.existsVerySuccessfulThreshold_ofTrustRegionAssumptionA0 hε'_pos with
        ⟨deltaTilde, hDeltaTildePos, hThreshold⟩
      rcases A.exists_smallRadiusOfGeometricDecay hDecay hDeltaTildePos with ⟨m, hm⟩
      have hVariantActive : A'.activeAt (N + m) := by
        rw [TrustRegionAlgorithm.activeAt_iff, TrustRegionAlgorithm.gradientNormAt_eq]
        change ε' < ‖A.g (N + m)‖
        rw [hTailGrad (N + m) (Nat.le_add_right N m)]
        dsimp [ε']
        linarith
      have hVerySuccessful : A.verySuccessfulAt (N + m) := by
        simpa [A'] using (hThreshold (N + m) hVariantActive hm).1
      exact (hTailActiveAndUnsuccessful (N + m) (Nat.le_add_right N m)).2
        (le_trans A.eta1_le_eta2 hVerySuccessful)
    -- The recorded zero anchor gradient matches the actual gradient of `f` at the anchor point.
    simpa [hAnchorGradZero] using (A.hasGradientAt N).gradient
