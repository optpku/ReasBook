/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.BrownianMotionVectorStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_40

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

open Lean Elab Term Meta

/-- Helper for Theorem 25.42: elaborates the imported centered annulus profile owner from
Theorem 25.40. -/
elab "importedCenteredAnnulusProfileConst" : term => do
  return ← mkConstWithFreshMVarLevels <|
    Name.str
      (Name.str
        (Name.num
          (Name.str
            (Name.str
              (Name.str
                (Name.str
                  (Name.str Name.anonymous "_private")
                  "Books.ProbabilityTheory_Klenke_2020")
                "Items")
              "Chap25")
            "Theorem_25_40")
          0)
        "ProbabilityTheory")
      "centeredAnnulusProfile"

/-- Helper for Theorem 25.42: elaborates the imported bounded annulus exit-probability identity
from Theorem 25.40. -/
elab "importedAnnulusInnerExitProbabilityEqProfileConst" : term => do
  return ← mkConstWithFreshMVarLevels <|
    Name.str
      (Name.str
        (Name.num
          (Name.str
            (Name.str
              (Name.str
                (Name.str
                  (Name.str Name.anonymous "_private")
                  "Books.ProbabilityTheory_Klenke_2020")
                "Items")
              "Chap25")
            "Theorem_25_40")
          0)
        "ProbabilityTheory")
      "annulusInnerExitProbability_eq_profile"

/-- Definition 25.41: a set `A ⊆ State` is polar for the family of laws `P x` and the
`State`-valued
process `W` if, for every starting point `x`, the strictly positive hitting time of `A` is almost
surely infinite under `P x`. -/
def IsPolarSet (P : State → ProbabilityMeasure Ω) (W : VectorProcess) (A : Set State) : Prop :=
  ∀ x : State, ∀ᵐ ω ∂(P x : Measure Ω), (τ_[W, A]) ω = ⊤

/-- A set is polar exactly when, under each starting law `P x`, the path avoids the target at all
strictly positive times almost surely. -/
theorem isPolarSet_iff
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess) (A : Set State) :
    IsPolarSet P W A ↔
      ∀ x : State, ∀ᵐ ω ∂(P x : Measure Ω), ∀ t : NNReal, 0 < t → W t ω ∉ A := by
  constructor
  · intro h x
    -- Proof comment: unfold the strict positive hitting clock into the pointwise avoidance
    -- characterization from Theorem 25.40.
    filter_upwards [h x] with ω hω
    exact (strictPositiveHittingTime_eq_top_iff W A ω).1 hω
  · intro h x
    -- Proof comment: the same characterization turns almost-sure avoidance back into `τ = ⊤`.
    filter_upwards [h x] with ω hω
    exact (strictPositiveHittingTime_eq_top_iff W A ω).2 hω

/-- Helper for Theorem 25.42: a local model of the centered annulus profile imported from
Theorem 25.40. -/
private def centeredAnnulusProfileModel (ρ R : ℝ) : State → ℝ :=
  fun z ↦
    if d = 1 then
      (R - ‖z‖) / (R - ρ)
    else if d = 2 then
      (Real.log R - Real.log ‖z‖) / (Real.log R - Real.log ρ)
    else
      ((ρ / ‖z‖) ^ (d - 2) - (ρ / R) ^ (d - 2)) / (1 - (ρ / R) ^ (d - 2))

/-- The empty set is polar for every family of laws and every state-valued process. -/
@[simp] theorem isPolarSet_empty
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess) :
    IsPolarSet P W ∅ := by
  -- Proof comment: no path can ever hit the empty set, so strict positive avoidance is trivial.
  rw [isPolarSet_iff]
  intro x
  filter_upwards with ω t ht
  simp

section BrownianPolarSets

variable (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
variable (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)

/-- Helper for Theorem 25.42: covariance is unchanged when both slices are replaced by
almost-everywhere equal versions. -/
private theorem covariance_congr_ae
    {μ : Measure Ω} {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Proof comment: first transport the expectations, then rewrite the covariance integrand
  -- pointwise almost everywhere.
  have hIntX : μ[X] = μ[X'] := MeasureTheory.integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := MeasureTheory.integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Theorem 25.42: subtracting the deterministic start turns Brownian motion started at
`x` into Brownian motion started at `0`. -/
private theorem brownianStartedAt_sub_const_startedAtZero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ B t ω - x) 0 := by
  refine
    { stronglyMeasurable := ?_
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: subtracting a constant preserves measurability of each deterministic slice.
    intro t
    exact (hB.stronglyMeasurable t).sub stronglyMeasurable_const
  · -- Proof comment: at time `0`, the recentered value is zero exactly when the original value is
    -- the deterministic start `x`.
    have hpreimage :
        (fun ω ↦ B 0 ω - x) ⁻¹' ({0} : Set ℝ) = B 0 ⁻¹' ({x} : Set ℝ) := by
      ext ω
      constructor
      · intro hω
        change B 0 ω - x = 0 at hω
        change B 0 ω = x
        linarith
      · intro hω
        have hxω : B 0 ω = x := by simpa using hω
        change B 0 ω - x = 0
        simp [hxω]
    rw [hpreimage]
    exact hB.start
  · -- Proof comment: recentering cancels from every increment, so independence is unchanged.
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB.indepIncrements n t ht
  · -- Proof comment: the same cancellation shows that increment laws remain stationary.
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: the positive-time Gaussian marginal is translated from mean `x` to mean `0`.
    simpa using ProbabilityTheory.gaussianReal_sub_const (hB.gaussian_marginal ht) x
  · -- Proof comment: path continuity is preserved under subtraction of a deterministic constant.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Theorem 25.42: pointwise negation preserves Brownian motion. -/
private theorem neg_isBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (fun t ω ↦ -B t ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the pointwise zero initial condition is stable under negation.
    funext ω
    simp [hB.zero]
  · -- Proof comment: independent increments are preserved by the measurable map `x ↦ -x`.
    simpa using hB.indepIncrements.neg
  · -- Proof comment: each negated increment is the negation of the original increment.
    intro r s t
    convert (hB.stationaryIncrements r s t).comp measurable_neg using 1
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
    · funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
  · intro t ht
    -- Proof comment: centered Gaussian marginals are symmetric under negation.
    simpa using ProbabilityTheory.gaussianReal_neg (hB.gaussian_marginal ht)
  · -- Proof comment: negating a continuous path preserves continuity.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.neg

/-- Helper for Theorem 25.42: patching only time `0` by the literal value `0` turns a Brownian
motion started at `0` into a standard Brownian motion. -/
private theorem pointwiseZeroVersion_isBrownianMotion_startedAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotionStartedAt μ B 0) :
    IsBrownianMotion μ (fun t ω ↦ if t = 0 then 0 else B t ω) := by
  let B0 : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else B t ω
  have hZeroAe : B 0 =ᵐ[μ] fun _ ↦ 0 :=
    brownianStart_ae_eq_const_of_measurable (hB.stronglyMeasurable 0).measurable hB
  have hmod : ∀ t : NNReal, B0 t =ᵐ[μ] B t := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simpa [B0] using hZeroAe.symm
    · exact Filter.Eventually.of_forall fun ω ↦ by simp [B0, ht]
  have hgauss : IsGaussianProcess B μ :=
    IsBrownianMotionStartedAt.isGaussianProcess_zero hB
  have hgauss0 : IsGaussianProcess B0 μ := hgauss.congr fun t ↦ (hmod t).symm
  have hmean : ∀ t : NNReal, ∫ ω, B t ω ∂μ = 0 :=
    (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance μ B).1 hB
      |>.2.2.1
  have hmean0 : ∀ t : NNReal, ∫ ω, B0 t ω ∂μ = 0 := by
    intro t
    -- Proof comment: the timewise modification agrees with the original Brownian slice almost
    -- surely, so the centered mean identity transfers immediately.
    rw [integral_congr_ae (hmod t), hmean t]
  have hcov0 : ∀ s t : NNReal, cov[B0 s, B0 t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance depends only on the almost-sure equivalence classes of the two
    -- deterministic-time slices.
    rw [covariance_congr_ae (hmod s) (hmod t), startedAtZero_covariance_eq hB s t]
  have hcont0 : HasAlmostSurelyContinuousPaths μ B0 := by
    -- Proof comment: on the full-measure start event `B 0 = 0`, the patched process agrees with
    -- the original Brownian path at every time.
    filter_upwards [hB.continuous_paths, hZeroAe] with ω hωcont hω0
    have hEq : (fun t : NNReal ↦ B0 t ω) = fun t : NNReal ↦ B t ω := by
      funext t
      by_cases ht : t = 0
      · subst ht
        simpa [B0] using hω0.symm
      · simp [B0, ht]
    have hPathEq : processPath B0 ω = processPath B ω := by
      simpa [processPath] using hEq
    simpa [HasAlmostSurelyContinuousPaths] using hPathEq ▸ hωcont
  -- Proof comment: the patched process now satisfies the standard centered Gaussian Brownian
  -- characterization with a literal time-zero value.
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ B0).2
      ⟨by
          funext ω
          simp [B0]
        , hgauss0, hmean0, hcov0, hcont0⟩

/-- Helper for Theorem 25.42: after recentering at the deterministic start point, replacing the
time-zero value by the literal origin gives the standard Brownian spelling used in the restart
argument. -/
private theorem brownianVectorStartedAt_zeroPatched_isStandard
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x) (x : State) :
    IsStandardBrownianMotionVector (P x : Measure Ω)
      (fun t ω ↦ if t = 0 then 0 else W t ω - x) := by
  let Z : VectorProcess := fun t ω ↦ W t ω - x
  let F : Fin d → (NNReal → ℝ) → NNReal → ℝ :=
    fun _ f t ↦ if t = 0 then 0 else f t
  have hZ : IsBrownianMotionVectorStartedAt (P x : Measure Ω) Z 0 := by
    refine
      { isBrownianMotionStartedAt := ?_
        iIndepFun := ?_ }
    · intro i
      -- Proof comment: every coordinate is the recentered scalar Brownian motion started at `0`.
      simpa [Z] using
        brownianStartedAt_sub_const_startedAtZero
          ((hW x).isBrownianMotionStartedAt i)
    · have hFmeas :
          ∀ i : Fin d, Measurable (fun f : NNReal → ℝ ↦ f - fun _ ↦ x i) := by
        intro i
        refine measurable_pi_lambda _ fun t ↦ ?_
        exact (measurable_pi_apply t).sub measurable_const
      -- Proof comment: deterministic recentering preserves coordinate independence on path space.
      simpa [Z] using (hW x).iIndepFun.comp (fun i f t ↦ f t - x i) hFmeas
  have hF_meas : ∀ i : Fin d, Measurable (F i) := by
    intro i
    refine measurable_pi_lambda _ fun t ↦ ?_
    by_cases ht : t = 0
    · simp [F, ht]
    · simpa [F, ht] using (measurable_pi_apply t : Measurable fun f : NNReal → ℝ ↦ f t)
  refine
    { isBrownianMotion := ?_
      iIndepFun := ?_ }
  · intro i
    -- Proof comment: patching the zero-time value coordinatewise upgrades the recentered vector
    -- to the standard Brownian spelling.
    convert
      pointwiseZeroVersion_isBrownianMotion_startedAtZero
        (μ := (P x : Measure Ω)) (B := fun t ω ↦ Z t ω i) (hZ.isBrownianMotionStartedAt i) using 1
    funext t ω
    by_cases ht : t = 0 <;> simp [Z, ht]
  · -- Proof comment: the same measurable time-zero patch preserves coordinate independence.
    convert hZ.iIndepFun.comp (fun i ↦ F i) hF_meas using 1
    funext i ω t
    by_cases ht : t = 0 <;> simp [F, Z, ht]

/-- Helper for Theorem 25.42: dividing a positive radius by `n + 2` produces a positive radius
strictly smaller than the original one. -/
private theorem div_natCast_add_two_pos_and_lt {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < R / (n + 2 : ℝ) ∧ R / (n + 2 : ℝ) < R := by
  -- Proof comment: the denominator is always larger than `1`, so division preserves positivity
  -- and strictly contracts the radius.
  have hden : 1 < (n + 2 : ℝ) := by
    nlinarith
  constructor
  · positivity
  · exact div_lt_self hR hden

/-- Helper for Theorem 25.42: cancelling a nonzero radius after dividing by `n + 2` leaves the
expected reciprocal factor. -/
private theorem div_natCast_add_two_div_self {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    (R / (n + 2 : ℝ)) / R = 1 / (n + 2 : ℝ) := by
  -- Proof comment: clear denominators once and reduce to a ring identity.
  field_simp [hR]

/-- Helper for Theorem 25.42: shifting a Brownian motion by a deterministic time and recentering
by its value there again gives a Brownian motion. -/
private theorem shiftedIncrement_isBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (T : NNReal) :
    IsBrownianMotion μ (fun t ω ↦ B (T + t) ω - B T ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the recentered shifted process still starts from `0`.
    funext ω
    simp
  · -- Proof comment: increments on the translated mesh are the original Brownian increments.
    rw [hasIndepIncrements_iff_nat]
    intro t ht
    simpa [add_assoc] using
      hB.indepIncrements.nat (t := fun i ↦ T + t i)
        (fun i j hij ↦ by
          simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (ht hij) T)
  · -- Proof comment: deterministic time translation preserves stationary increments verbatim.
    intro r s t
    simpa [add_assoc, add_left_comm, add_comm] using
      hB.stationaryIncrements (T + r) s t
  · intro t ht
    -- Proof comment: the shifted marginal is an increment of `B`, hence has the same centered
    -- Gaussian law as the original Brownian motion at time `t`.
    have hId :
        IdentDistrib
          (fun ω ↦ B (T + t) ω - B T ω)
          (fun ω ↦ B t ω - B 0 ω)
          μ μ := by
      simpa [add_assoc, add_comm, add_left_comm] using
        hB.stationaryIncrements.identDistrib_increment (r := 0) (s := t) (t := T)
    have hLaw0 : HasLaw (fun ω ↦ B t ω - B 0 ω) (gaussianReal 0 t) μ := by
      simpa [hB.zero] using hB.gaussian_marginal ht
    exact hId.symm.hasLaw hLaw0
  · -- Proof comment: shifting time and subtracting the anchor keeps almost-sure continuity.
    filter_upwards [hB.continuous_paths] with ω hω
    have hshift : Continuous (fun t : NNReal ↦ B (T + t) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hshift.sub continuous_const

/-- Helper for Theorem 25.42: translating a standard real Brownian motion by a constant produces
Brownian motion started from that constant. -/
private theorem translatedBrownianMotionStartedAt
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (x : ℝ) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ x + B t ω) x := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  refine
    { stronglyMeasurable := fun t ↦ (hB.stronglyMeasurable t).const_add x
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: adding the deterministic start point preserves the time-zero identity.
    have hpreimage : (fun ω ↦ x + B 0 ω) ⁻¹' ({x} : Set ℝ) = Set.univ := by
      ext ω
      simp [hB.zero]
    rw [hpreimage]
    simp
  · -- Proof comment: the deterministic translation cancels in every increment.
    rw [hasIndepIncrements_iff_nat]
    intro t ht
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hB.indepIncrements.nat (t := t) ht
  · -- Proof comment: stationary increments are unchanged by adding the same constant.
    intro r s t
    have hleft :
        (fun ω ↦ (x + B ((s + t) + r) ω) - (x + B (t + r) ω)) =
          (fun ω ↦ B ((s + t) + r) ω - B (t + r) ω) := by
      funext ω
      ring
    have hright :
        (fun ω ↦ (x + B (s + r) ω) - (x + B r ω)) =
          (fun ω ↦ B (s + r) ω - B r ω) := by
      funext ω
      ring
    simpa [hleft, hright] using hB.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: the time-`t` marginal is the centered Gaussian translated by `x`.
    simpa [add_comm] using ProbabilityTheory.gaussianReal_add_const (hB.gaussian_marginal ht) x
  · -- Proof comment: deterministic translation preserves path continuity.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using continuous_const.add hω

/-- Helper for Theorem 25.42: deterministic-time recentering preserves the standard
`d`-dimensional Brownian-vector structure. -/
private theorem shiftedIncrement_isStandardBrownianVector
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    IsStandardBrownianMotionVector μ (fun t ω ↦ W (T + t) ω - W T ω) := by
  let F : (NNReal → ℝ) → (NNReal → ℝ) := fun f t ↦ f (T + t) - f T
  have hF_meas : Measurable F := by
    -- Proof comment: measurability of the shifted-path transform is checked coordinatewise.
    refine measurable_pi_lambda _ ?_
    intro t
    exact (measurable_pi_apply (T + t)).sub (measurable_pi_apply T)
  refine
    { isBrownianMotion := fun i ↦ by
        -- Proof comment: each coordinate is exactly the shifted scalar Brownian motion.
        simpa using
          shiftedIncrement_isBrownianMotion
            (μ := μ) (B := fun t ω ↦ W t ω i) (hB := hW.isBrownianMotion i) T
      iIndepFun := by
        -- Proof comment: coordinate independence is preserved by the same measurable path map.
        simpa [F] using hW.iIndepFun.comp (fun _ ↦ F) (fun _ ↦ hF_meas) }

/-- Helper for Theorem 25.42: restarting after a deterministic time and then translating by a
deterministic state produces a Brownian vector started from that state. -/
private theorem translatedRestart_isBrownianVectorStartedAt
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (x : State) (T : NNReal) :
    IsBrownianMotionVectorStartedAt
      μ (fun t ω ↦ x + (W (T + t) ω - W T ω)) x := by
  let U : VectorProcess := fun t ω ↦ W (T + t) ω - W T ω
  let V : VectorProcess := fun t ω ↦ x + U t ω
  let G : Fin d → (NNReal → ℝ) → (NNReal → ℝ) := fun i f t ↦ x i + f t
  have hG_meas : ∀ i : Fin d, Measurable (G i) := by
    intro i
    refine measurable_pi_lambda _ ?_
    intro t
    exact measurable_const.add (measurable_pi_apply t)
  have hU : IsStandardBrownianMotionVector μ U :=
    shiftedIncrement_isStandardBrownianVector (μ := μ) (W := W) hW T
  refine
    { isBrownianMotionStartedAt := fun i ↦ by
        -- Proof comment: each coordinate is the translated restarted centered coordinate.
        have hshift :
            IsBrownianMotion μ (fun t ω ↦ U t ω i) :=
          hU.isBrownianMotion i
        simpa [U, V, G] using translatedBrownianMotionStartedAt (μ := μ) hshift (x i)
      iIndepFun := by
        -- Proof comment: coordinate independence survives the same translation on path space.
        simpa [U, V, G] using hU.iIndepFun.comp (fun i ↦ G i) hG_meas }

/-- Helper for Theorem 25.42: every deterministic coordinate of a standard Brownian vector lies
in `L²`. -/
private theorem brownianCoordinateEval_memLpTwo
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) (t : NNReal) :
    MemLp (fun ω ↦ W t ω i) 2 μ := by
  let B : NNReal → Ω → ℝ := fun s ω ↦ W s ω i
  have hB : IsBrownianMotion μ B := hW.isBrownianMotion i
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  by_cases ht : t = 0
  · -- Proof comment: at time `0`, the coordinate is the constant zero function.
    subst ht
    simp [B, hB.zero]
  · -- Proof comment: positive-time Brownian marginals are Gaussian, hence square-integrable.
    have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht
    have hLaw : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht_pos
    have hVar : Var[B t; μ] = t := by
      simpa using hLaw.variance_eq
    have hVar_ne : Var[B t; μ] ≠ 0 := by
      rw [hVar]
      exact_mod_cast ht
    simpa [B] using
      memLp_two_of_variance_ne_zero hLaw.aemeasurable.aestronglyMeasurable hVar_ne

/-- Helper for Theorem 25.42: a standard Brownian vector is a Gaussian process in the Euclidean
state space. -/
private theorem standardBrownianVector_isGaussianProcess
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) :
    IsGaussianProcess W μ := by
  classical
  letI : IsStandardBrownianMotionVector μ W := hW
  let ψ : State ≃L[ℝ] (Fin d → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)
  refine
    { hasGaussianLaw := fun I ↦ ?_ }
  let Xi : Fin d → Ω → I → ℝ := fun i ω t ↦ W t ω i
  have hXi_gauss : ∀ i : Fin d, HasGaussianLaw (Xi i) μ := by
    intro i
    let hBi : IsBrownianMotion μ (fun t ω ↦ W t ω i) := inferInstance
    let hGi : IsGaussianProcess (fun t ω ↦ W t ω i) μ :=
      IsBrownianMotion.isGaussianProcess hBi
    simpa [Xi] using hGi.hasGaussianLaw I
  have hXi_indep : iIndepFun Xi μ := by
    -- Proof comment: coordinate-path independence survives restriction to the finite time set.
    refine hW.iIndepFun.comp (fun _ f ↦ I.restrict f) ?_
    intro i
    exact measurable_pi_lambda _ fun t ↦ measurable_pi_apply (t : NNReal)
  let L : (Fin d → I → ℝ) →L[ℝ] I → State :=
    { toFun := fun x t ↦ ψ.symm (fun i ↦ x i t)
      map_add' := by
        intro x y
        ext t i
        rfl
      map_smul' := by
        intro c x
        ext t i
        rfl
      cont := by
        refine continuous_pi fun t ↦ ?_
        exact ψ.symm.continuous.comp <| continuous_pi fun i ↦
          (continuous_apply t).comp (continuous_apply i) }
  have hgauss :
      HasGaussianLaw (fun ω ↦ fun i ↦ Xi i ω) μ :=
    ProbabilityTheory.iIndepFun.hasGaussianLaw hXi_gauss hXi_indep
  -- Proof comment: repackage the coordinatewise Gaussian law back into the Euclidean space.
  simpa [Xi] using hgauss.map L

/-- Helper for Theorem 25.42: at a rational deterministic time, the current Brownian state is
independent of the rational future increment path. -/
private theorem futureIncrementRatPath_indep_currentState
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (q : ℚ≥0) :
    IndepFun
      (fun ω (s : ℚ≥0) ↦ W ((q : NNReal) + s) ω - W q ω)
      (fun ω ↦ W q ω)
      μ := by
  let X : ℚ≥0 → Ω → State := fun s ω ↦ W ((q : NNReal) + s) ω - W q ω
  let Y : Unit → Ω → State := fun _ ω ↦ W q ω
  have hWG :
      IsGaussianProcess W μ :=
    standardBrownianVector_isGaussianProcess (μ := μ) (W := W) hW
  have hJoint : IsGaussianProcess (Sum.elim X Y) μ := by
    refine hWG.of_isGaussianProcess ?_
    intro z
    cases z with
    | inl s =>
        let tq : NNReal := (q : NNReal) + s
        let I : Finset NNReal := {tq, (q : NNReal)}
        have htq : tq ∈ I := by simp [I, tq]
        have hqI : (q : NNReal) ∈ I := by simp [I]
        refine
          ⟨I,
            { toFun := fun x ↦ x (⟨tq, htq⟩ : I) - x (⟨(q : NNReal), hqI⟩ : I)
              map_add' := by
                intro x y
                ext i
                change
                  (x (⟨tq, htq⟩ : I)).ofLp i + (y (⟨tq, htq⟩ : I)).ofLp i -
                      ((x (⟨(q : NNReal), hqI⟩ : I)).ofLp i +
                        (y (⟨(q : NNReal), hqI⟩ : I)).ofLp i) =
                    ((x (⟨tq, htq⟩ : I)).ofLp i - (x (⟨(q : NNReal), hqI⟩ : I)).ofLp i) +
                      ((y (⟨tq, htq⟩ : I)).ofLp i - (y (⟨(q : NNReal), hqI⟩ : I)).ofLp i)
                ring
              map_smul' := by
                intro c x
                ext i
                change
                  c * (x (⟨tq, htq⟩ : I)).ofLp i - c * (x (⟨(q : NNReal), hqI⟩ : I)).ofLp i =
                    c * ((x (⟨tq, htq⟩ : I)).ofLp i - (x (⟨(q : NNReal), hqI⟩ : I)).ofLp i)
                ring
              cont := by
                fun_prop },
            ?_⟩
        · -- Proof comment: a future state difference is a linear projection of the two-time law.
          intro ω
          simp [X, tq]
    | inr u =>
        let I : Finset NNReal := {(q : NNReal)}
        have hqI : (q : NNReal) ∈ I := by simp [I]
        refine
          ⟨I,
            { toFun := fun x ↦ x (⟨(q : NNReal), hqI⟩ : I)
              map_add' := by
                intro x y
                rfl
              map_smul' := by
                intro c x
                rfl
              cont := by
                fun_prop },
            ?_⟩
        · -- Proof comment: the anchor state is just the evaluation at time `q`.
          intro ω
          cases u
          simp [Y, I]
  have hIndepFamily :
      IndepFun (fun ω s ↦ X s ω) (fun ω u ↦ Y u ω) μ := by
    -- Proof comment: the joint Gaussian family is independent once every cross covariance of
    -- inner products vanishes.
    refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_inner hJoint ?_ ?_ ?_
    · intro s
      exact
        ((ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
              ((q : NNReal) + s)).measurable.sub
          (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
            (q : NNReal)).measurable).aemeasurable
    · intro u
      cases u
      exact
        (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
          (q : NNReal)).aemeasurable
    · intro s u x y
      cases u
      have hXinner :
          (fun ω ↦ inner ℝ x (X s ω)) = fun ω ↦ ∑ i, x i * X s ω i := by
        -- Proof comment: `PiLp.inner_apply` gives the Euclidean inner product coordinatewise.
        ext ω
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (RCLike.inner_apply' (x.ofLp i) ((X s ω).ofLp i))
      have hYinner :
          (fun ω ↦ inner ℝ y (Y () ω)) = fun ω ↦ ∑ j, y j * Y () ω j := by
        -- Proof comment: the anchor-state inner product is normalized the same way.
        ext ω
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (RCLike.inner_apply' (y.ofLp i) ((Y () ω).ofLp i))
      have hXcoord_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ X s ω i) 2 μ := by
        intro i
        exact
          (brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i ((q : NNReal) + s)).sub
            (brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i (q : NNReal))
      have hYcoord_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ Y () ω i) 2 μ := by
        intro i
        simpa [Y] using
          brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i (q : NNReal)
      have hXsum_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ x i * X s ω i) 2 μ := by
        intro i
        exact (hXcoord_mem i).const_mul (x i)
      have hYsum_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ y i * Y () ω i) 2 μ := by
        intro i
        exact (hYcoord_mem i).const_mul (y i)
      rw [hXinner, hYinner, covariance_fun_sum_fun_sum hXsum_mem hYsum_mem]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_cases hij : i = j
      · subst hij
        have htq_mem :
            MemLp (fun ω ↦ W ((q : NNReal) + s) ω i) 2 μ :=
          brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i ((q : NNReal) + s)
        have hq_mem :
            MemLp (fun ω ↦ W (q : NNReal) ω i) 2 μ :=
          brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i (q : NNReal)
        have htq_cov :
            cov[(fun ω ↦ W ((q : NNReal) + s) ω i), (fun ω ↦ W (q : NNReal) ω i); μ] =
              ((q : NNReal) : ℝ) := by
          simpa [inf_eq_right.mpr (show (q : NNReal) ≤ (q : NNReal) + s by simp)] using
            IsBrownianMotion.covariance_eq
              (show IsBrownianMotion μ (fun t ω ↦ W t ω i) from inferInstance)
              ((q : NNReal) + s) (q : NNReal)
        have hq_cov :
            cov[(fun ω ↦ W (q : NNReal) ω i), (fun ω ↦ W (q : NNReal) ω i); μ] =
              ((q : NNReal) : ℝ) := by
          simpa using
            IsBrownianMotion.covariance_eq
              (show IsBrownianMotion μ (fun t ω ↦ W t ω i) from inferInstance)
              (q : NNReal) (q : NNReal)
        calc
          cov[fun ω ↦ x i * X s ω i, fun ω ↦ y i * Y () ω i; μ]
              = x i * (y i *
                  cov[(fun ω ↦ W ((q : NNReal) + s) ω i - W (q : NNReal) ω i),
                    (fun ω ↦ W (q : NNReal) ω i); μ]) := by
                      simp [X, Y, covariance_const_mul_left, covariance_const_mul_right,
                        mul_left_comm]
          _ = x i * (y i * 0) := by
                rw [covariance_fun_sub_left htq_mem hq_mem hq_mem, htq_cov, hq_cov]
                ring
          _ = 0 := by ring
      · have hcoord_indep :
            IndepFun
              (fun ω ↦ W ((q : NNReal) + s) ω i - W (q : NNReal) ω i)
              (fun ω ↦ W (q : NNReal) ω j)
              μ := by
          -- Proof comment: distinct coordinates are independent as path processes, hence so are
          -- these deterministic-time functionals of the past and future coordinates.
          exact
            (hW.iIndepFun.indepFun (i := i) (j := j) hij).comp
              ((measurable_pi_apply ((q : NNReal) + s)).sub
                (measurable_pi_apply (q : NNReal)))
              (measurable_pi_apply (q : NNReal))
        have hcovXY :
            cov[(fun ω ↦ (X s ω).ofLp i), (fun ω ↦ (Y () ω).ofLp j); μ] = 0 := by
          simpa [X, Y] using hcoord_indep.covariance_eq_zero (hXcoord_mem i) (hYcoord_mem j)
        calc
          cov[fun ω ↦ x i * X s ω i, fun ω ↦ y j * Y () ω j; μ]
              = x i * (y j * cov[(fun ω ↦ X s ω i), (fun ω ↦ Y () ω j); μ]) := by
                  simp [covariance_const_mul_left, covariance_const_mul_right,
                    mul_left_comm]
          _ = x i * (y j * 0) := by
                rw [hcovXY]
          _ = 0 := by ring
  -- Proof comment: evaluating the independent `Unit`-indexed family at `()` recovers the anchor.
  simpa [X, Y] using
    hIndepFamily.comp measurable_id (by simpa using measurable_pi_apply ())

/-- Helper for Theorem 25.42: in dimension `1`, Brownian motion started at `y` almost surely
returns to `y` at some strictly positive time. -/
private theorem returnsToStart_ae_of_dimension_one
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : d = 1) (y : State) :
    ∀ᵐ ω ∂(P y : Measure Ω), ∃ t : NNReal, 0 < t ∧ W t ω = y := by
  subst hd
  let B : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0 - y 0
  let B0 : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else B t ω
  have hB : IsBrownianMotionStartedAt (P y : Measure _) B 0 := by
    -- Proof comment: recenter the unique coordinate so that the scalar path starts from `0`.
    simpa [B] using
      brownianStartedAt_sub_const_startedAtZero ((hW y).isBrownianMotionStartedAt 0)
  have hB0 : IsBrownianMotion (P y : Measure Ω) B0 :=
    pointwiseZeroVersion_isBrownianMotion_startedAtZero hB
  have hB0neg : IsBrownianMotion (P y : Measure Ω) (fun t ω ↦ -B0 t ω) :=
    neg_isBrownianMotion hB0
  have hOnePos : (0 : ℝ) < 1 := by
    norm_num
  have hcont :
      ∀ᵐ ω ∂(P y : Measure _), Continuous (fun t : NNReal ↦ B0 t ω) := by
    -- Proof comment: the patched scalar Brownian motion keeps almost-surely continuous paths.
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hB0.continuous_paths
  have hhitPos :
      ∀ᵐ ω ∂(P y : Measure _), ∃ t : NNReal, B0 t ω = 1 := by
    filter_upwards [brownianLevelHittingTime_ae_ne_top (μ := (P y : Measure _)) (B := B0)
      (hB := hB0) (hb := hOnePos)] with ω hω
    exact (brownianLevelHittingTime_ne_top_iff_exists_eq (B := B0) (b := (1 : ℝ)) (ω := ω)).1 hω
  have hhitNeg :
      ∀ᵐ ω ∂(P y : Measure _), ∃ t : NNReal, B0 t ω = -1 := by
    filter_upwards [brownianLevelHittingTime_ae_ne_top (μ := (P y : Measure _))
      (B := fun t ω ↦ -B0 t ω) (hB := hB0neg) (hb := hOnePos)] with ω hω
    rcases (brownianLevelHittingTime_ne_top_iff_exists_eq (B := fun t ω ↦ -B0 t ω)
      (b := (1 : ℝ)) (ω := ω)).1 hω with ⟨t, ht⟩
    exact ⟨t, by linarith [ht]⟩
  filter_upwards [hcont, hhitPos, hhitNeg] with ω hcontω hpos hneg
  rcases hpos with ⟨tPos, htPos⟩
  rcases hneg with ⟨tNeg, htNeg⟩
  have htPos_ne : tPos ≠ 0 := by
    intro ht
    have : B0 0 ω = (1 : ℝ) := by simpa [ht] using htPos
    simp [B0] at this
  have htNeg_ne : tNeg ≠ 0 := by
    intro ht
    have : B0 0 ω = (-1 : ℝ) := by simpa [ht] using htNeg
    simp [B0] at this
  have htPos_pos : 0 < tPos := pos_iff_ne_zero.2 htPos_ne
  have htNeg_pos : 0 < tNeg := pos_iff_ne_zero.2 htNeg_ne
  by_cases horder : tNeg ≤ tPos
  · have hzero_mem : (0 : ℝ) ∈ Set.Icc (B0 tNeg ω) (B0 tPos ω) := by
      simp [htNeg, htPos]
    obtain ⟨t, ht_mem, ht_zero⟩ :=
      (intermediate_value_Icc (a := tNeg) (b := tPos) horder hcontω.continuousOn) hzero_mem
    have ht_pos : 0 < t := lt_of_lt_of_le htNeg_pos ht_mem.1
    refine ⟨t, ht_pos, ?_⟩
    ext i
    fin_cases i
    have hcoord : B0 t ω = 0 := ht_zero
    have : W t ω 0 = y 0 := by
      have hcoord' : W t ω 0 - y 0 = 0 := by
        simpa [B0, B, ht_pos.ne'] using hcoord
      linarith
    simpa using this
  · have horder' : tPos ≤ tNeg := le_of_not_ge horder
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (-B0 tPos ω) (-B0 tNeg ω) := by
      simp [htPos, htNeg]
    obtain ⟨t, ht_mem, ht_zero⟩ :=
      (intermediate_value_Icc (a := tPos) (b := tNeg) horder' hcontω.neg.continuousOn) hzero_mem
    have ht_pos : 0 < t := lt_of_lt_of_le htPos_pos ht_mem.1
    refine ⟨t, ht_pos, ?_⟩
    ext i
    fin_cases i
    have hcoord : B0 t ω = 0 := by
      linarith [ht_zero]
    have : W t ω 0 = y 0 := by
      have hcoord' : W t ω 0 - y 0 = 0 := by
        simpa [B0, B, ht_pos.ne'] using hcoord
      linarith
    simpa using this

/-- Helper for Theorem 25.42: in dimensions `d > 2`, Brownian motion started away from `y`
almost surely never hits the singleton `{y}` at positive times. -/
private theorem singletonAvoidanceStartedAt_of_ne_dimension_gt_two
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess} {x y : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x)
    (hd : 2 < d) (hxy : x ≠ y) :
    ∀ᵐ ω ∂μ, (τ_[W, ({y} : Set State)]) ω = ⊤ := by
  let hitSingleton : Set Ω := {ω | (τ_[W, ({y} : Set State)]) ω < ⊤}
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have hdist_ne : dist x y ≠ 0 := ne_of_gt hdist
  have hsubset :
      ∀ n : ℕ,
        hitSingleton ⊆
          {ω | (τ_[W, Metric.ball y (dist x y / (n + 2 : ℝ))]) ω < ⊤} := by
    intro n ω hω
    rcases (strictPositiveHittingTime_lt_top_iff W ({y} : Set State) ω).1 hω with
      ⟨t, ht_pos, ht_mem⟩
    have ht_eq : W t ω = y := by simpa using ht_mem
    have hr_pos : 0 < dist x y / (n + 2 : ℝ) :=
      (div_natCast_add_two_pos_and_lt (R := dist x y) hdist n).1
    refine (strictPositiveHittingTime_lt_top_iff W
      (Metric.ball y (dist x y / (n + 2 : ℝ))) ω).2 ?_
    refine ⟨t, ht_pos, ?_⟩
    rw [Metric.mem_ball, ht_eq]
    simpa using hr_pos
  have hbound :
      ∀ n : ℕ, μ hitSingleton ≤ ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2)) := by
    intro n
    have hr :=
      div_natCast_add_two_pos_and_lt (R := dist x y) hdist n
    calc
      μ hitSingleton ≤ μ {ω | (τ_[W, Metric.ball y (dist x y / (n + 2 : ℝ))]) ω < ⊤} := by
            exact measure_mono (hsubset n)
      _ = if d ≤ 2 then 1
            else ENNReal.ofReal (((dist x y / (n + 2 : ℝ)) / dist x y) ^ (d - 2)) := by
            simpa using
              brownian_hits_ball_probability
                (μ := (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)) (W := W) (x := x) (hW := hW)
                (r := dist x y / (n + 2 : ℝ)) hr.1 (y := y) hr.2
      _ = ENNReal.ofReal (((dist x y / (n + 2 : ℝ)) / dist x y) ^ (d - 2)) := by
            have hnot : ¬ d ≤ 2 := by omega
            simp [hnot]
      _ = ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2)) := by
            rw [div_natCast_add_two_div_self hdist_ne]
  have hhit_zero : μ hitSingleton = 0 := by
    by_contra hhit_ne
    have hhit_lt_top : μ hitSingleton < ⊤ := measure_lt_top _ _
    have hhit_ne_top : μ hitSingleton ≠ ⊤ := hhit_lt_top.ne
    have hhit_real_pos : 0 < (μ hitSingleton).toReal :=
      ENNReal.toReal_pos hhit_ne hhit_ne_top
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hhit_real_pos
    have hbase_le :
        (1 / (n + 2 : ℝ)) ≤ 1 / (n + 1 : ℝ) := by
      have hden : (n + 1 : ℝ) ≤ n + 2 := by
        nlinarith
      exact one_div_le_one_div_of_le (by positivity) hden
    have hbase_lt :
        1 / (n + 2 : ℝ) < (μ hitSingleton).toReal := lt_of_le_of_lt hbase_le hn
    have hk : 1 ≤ d - 2 := by omega
    have hbase_le_one : (1 / (n + 2 : ℝ)) ≤ 1 := by
      have hden : (1 : ℝ) ≤ n + 2 := by
        nlinarith
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
    have hpow_le :
        (1 / (n + 2 : ℝ)) ^ (d - 2) ≤ 1 / (n + 2 : ℝ) := by
      have hk' : d - 2 = (d - 3) + 1 := by
        omega
      have hpow_le_one : (1 / (n + 2 : ℝ)) ^ (d - 3) ≤ 1 := by
        exact pow_le_one₀ (by positivity) hbase_le_one
      have hbase_nonneg : 0 ≤ 1 / (n + 2 : ℝ) := by
        positivity
      rw [hk', pow_succ']
      nlinarith [mul_le_mul_of_nonneg_right hpow_le_one hbase_nonneg]
    have hpow_lt :
        (1 / (n + 2 : ℝ)) ^ (d - 2) < (μ hitSingleton).toReal :=
      lt_of_le_of_lt hpow_le hbase_lt
    have hsmall :
        ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2)) < μ hitSingleton := by
      exact
        (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hhit_ne_top).2 hpow_lt
    exact not_lt_of_ge (hbound n) hsmall
  have havoid_ae : ∀ᵐ ω ∂μ, ω ∉ hitSingleton := compl_mem_ae_iff.2 hhit_zero
  filter_upwards [havoid_ae] with ω hω
  by_cases htop : (τ_[W, ({y} : Set State)]) ω = ⊤
  · exact htop
  · exfalso
    exact hω (lt_top_iff_ne_top.2 htop)

/-- Helper for Theorem 25.42: the family-level `d > 2` off-start branch is just the
measure-local singleton-avoidance theorem specialized to `P x`. -/
private theorem singletonAvoidance_of_ne_dimension_gt_two
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : 2 < d) {x y : State} (hxy : x ≠ y) :
    ∀ᵐ ω ∂(P x : Measure Ω), (τ_[W, ({y} : Set State)]) ω = ⊤ := by
  -- Proof comment: this wrapper keeps the original public helper shape while reusing the
  -- measure-local theorem that also fits the restart proof below.
  simpa using
    singletonAvoidanceStartedAt_of_ne_dimension_gt_two
      (Ω := Ω) (d := d) (μ := (P x : Measure Ω)) (W := W) (x := x) (y := y)
      (hW := hW x) hd hxy

/-- Helper for Theorem 25.42: on a continuous path, an exact singleton hit forces bounded annulus
hits for every exponentially shrinking inner radius. -/
private theorem singletonHit_subset_iUnion_iInter_expAnnulusHitEvents
    {W : VectorProcess} {x y : State} (hxy : x ≠ y) :
    {ω | Continuous (fun t : NNReal ↦ W t ω) ∧
        (τ_[W, ({y} : Set State)]) ω < ⊤} ⊆
      ⋃ m : ℕ, ⋂ n : ℕ,
        {ω |
          (τ_[W, Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))]) ω <
            hittingAfter W (Metric.ball y (dist x y + m + 1))ᶜ 0 ω} := by
  intro ω hω
  rcases hω with ⟨hcont, hhit⟩
  rcases (strictPositiveHittingTime_lt_top_iff W ({y} : Set State) ω).1 hhit with
    ⟨t, ht_pos, ht_hit⟩
  let S : Set State := (fun s : NNReal ↦ W s ω - y) '' Set.Icc (0 : NNReal) t
  have hScompact : IsCompact S := by
    -- Proof comment: a continuous path segment over the compact time interval `[0, t]` has compact
    -- image after recentering at `y`.
    simpa [S] using IsCompact.image isCompact_Icc (hcont.sub continuous_const)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := S) hScompact.isBounded
  obtain ⟨m, hmC⟩ : ∃ m : ℕ, C ≤ (m : ℝ) := exists_nat_ge C
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  refine Set.mem_iUnion.2 ⟨m, Set.mem_iInter.2 ?_⟩
  intro n
  have hradius_pos : 0 < dist x y * Real.exp (-(n + 1 : ℝ)) := by
    positivity
  have hinner_mem :
      W t ω ∈ Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ))) := by
    -- Proof comment: the exact hit time lands at the annulus center, so it lies in every
    -- positive-radius inner ball.
    rw [Metric.mem_ball, ht_hit, dist_self]
    simpa using hradius_pos
  have hinner_le :
      (τ_[W, Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))]) ω ≤ t :=
    strictPositiveHittingTime_le_of_mem
      W (Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))) ω ht_pos hinner_mem
  have houter_gt :
      (t : WithTop NNReal) <
        hittingAfter W (Metric.ball y (dist x y + m + 1))ᶜ 0 ω := by
    by_contra hnot
    let outerBall : Set State := Metric.ball y (dist x y + m + 1)
    let exitSet : Set NNReal := {s : NNReal | W s ω ∈ outerBallᶜ}
    have hτ_finite : hittingAfter W outerBallᶜ 0 ω ≠ ⊤ := by
      intro htop
      have ht_lt_top : (t : WithTop NNReal) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro ht_top
        cases ht_top
      exact hnot (htop ▸ ht_lt_top)
    have hExitExists : ∃ s : NNReal, W s ω ∈ outerBallᶜ := by
      simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hτ_finite
      rcases hτ_finite with ⟨s, _, hsExit⟩
      exact ⟨s, hsExit⟩
    have hExitClosed : IsClosed exitSet := by
      change IsClosed ((fun s : NNReal ↦ W s ω) ⁻¹' outerBallᶜ)
      simpa [outerBall] using Metric.isOpen_ball.isClosed_compl.preimage hcont
    have hsInf_mem : sInf exitSet ∈ exitSet :=
      hExitClosed.csInf_mem
        (by
          rcases hExitExists with ⟨s, hsExit⟩
          exact ⟨s, hsExit⟩)
        ⟨0, fun s _ ↦ bot_le⟩
    have hτ_eq : (hittingAfter W outerBallᶜ 0 ω).untopA = sInf exitSet := by
      rw [hittingAfter]
      rw [if_pos]
      · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ outerBallᶜ} = exitSet by
            ext s
            simp [exitSet]]
        simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf exitSet))
      · rcases hExitExists with ⟨s, hsExit⟩
        exact ⟨s, bot_le, hsExit⟩
    have hτ_mem :
        W (hittingAfter W outerBallᶜ 0 ω).untopA ω ∈ outerBallᶜ := by
      simpa [exitSet, hτ_eq] using hsInf_mem
    have hle :
        hittingAfter W outerBallᶜ 0 ω ≤ t :=
      le_of_not_gt hnot
    have hτ_le : (hittingAfter W outerBallᶜ 0 ω).untopA ≤ t := by
      lift hittingAfter W outerBallᶜ 0 ω to NNReal using hτ_finite with τ hτ
      have hτ_idx : (hittingAfter W outerBallᶜ 0 ω).untopA = τ := by
        rw [← hτ]
        simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := τ))
      have hle' : τ ≤ t := by
        exact_mod_cast hle
      exact hτ_idx ▸ hle'
    have hτ_memIcc :
        (hittingAfter W outerBallᶜ 0 ω).untopA ∈ Set.Icc (0 : NNReal) t := by
      exact ⟨bot_le, hτ_le⟩
    have hs_memS : W (hittingAfter W outerBallᶜ 0 ω).untopA ω - y ∈ S := by
      exact ⟨(hittingAfter W outerBallᶜ 0 ω).untopA, hτ_memIcc, rfl⟩
    have hs_norm_le :
        ‖W (hittingAfter W outerBallᶜ 0 ω).untopA ω - y‖ ≤ C := hC _ hs_memS
    have hs_dist_le :
        dist (W (hittingAfter W outerBallᶜ 0 ω).untopA ω) y ≤ C := by
      simpa [dist_eq_norm] using hs_norm_le
    have hC_lt_outer : C < dist x y + m + 1 := by
      linarith
    have hs_ball :
        W (hittingAfter W outerBallᶜ 0 ω).untopA ω ∈ outerBall := by
      simpa [outerBall, Metric.mem_ball] using lt_of_le_of_lt hs_dist_le hC_lt_outer
    exact hτ_mem hs_ball
  -- Proof comment: the inner hitting clock is bounded by the concrete hit time `t`, while the
  -- bounded outer exit time stays strictly larger than `t`.
  exact lt_of_le_of_lt hinner_le houter_gt

/-- Helper for Theorem 25.42: on the continuity event, the bounded planar annulus hit probability
is controlled by the logarithmic radial profile. -/
private theorem planarExpAnnulusHitEvent_prob_le_ratio_onContinuous
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess} {x y : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x)
    (hd2 : d = 2) (hxy : x ≠ y) (m n : ℕ) :
    μ {ω |
        Continuous (fun t : NNReal ↦ W t ω) ∧
          (τ_[W, Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))]) ω <
            hittingAfter W (Metric.ball y (dist x y + m + 1))ᶜ 0 ω} ≤
      ENNReal.ofReal
        ((Real.log (dist x y + m + 1) - Real.log (dist x y)) /
          ((Real.log (dist x y + m + 1) - Real.log (dist x y)) + (n + 1 : ℝ))) := by
  -- Route correction: the missing planar annulus input is now isolated in the exact
  -- continuity-intersected normal form consumed by Theorem 25.42.
  let ρ : ℝ := dist x y * Real.exp (-(n + 1 : ℝ))
  let R : ℝ := dist x y + m + 1
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have hρ : 0 < ρ := by
    -- Proof comment: the inner radius is the positive start distance scaled by a positive
    -- exponential factor.
    dsimp [ρ]
    positivity
  have hρx : ρ < dist x y := by
    -- Proof comment: the exponential factor is strictly less than `1`, so the inner radius stays
    -- strictly below the start radius.
    dsimp [ρ]
    have hexp_lt : Real.exp (-(n + 1 : ℝ)) < 1 := by
      have hneg : -(n + 1 : ℝ) < 0 := by
        nlinarith
      simpa using Real.exp_lt_one_iff.mpr hneg
    rw [show dist x y = dist x y * 1 by ring]
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_lt_mul_of_pos_left hexp_lt hdist
  have hR : dist x y < R := by
    -- Proof comment: the outer radius is the start radius buffered by the positive increment
    -- `m + 1`.
    dsimp [R]
    have hm_pos : (0 : ℝ) < m + 1 := by positivity
    linarith
  have hsubset :
      {ω |
          Continuous (fun t : NNReal ↦ W t ω) ∧
            (τ_[W, Metric.ball y ρ]) ω < hittingAfter W (Metric.ball y R)ᶜ 0 ω} ⊆
        {ω | (τ_[W, Metric.ball y ρ]) ω < hittingAfter W (Metric.ball y R)ᶜ 0 ω} := by
    -- Proof comment: dropping the continuity conjunct only enlarges the event.
    intro ω hω
    exact hω.2
  have hprob :
      μ {ω | (τ_[W, Metric.ball y ρ]) ω < hittingAfter W (Metric.ball y R)ᶜ 0 ω} =
        ENNReal.ofReal
          (importedCenteredAnnulusProfileConst (d := d) ρ R (x - y)) := by
    -- Proof comment: the earlier annulus theorem already identifies the bounded inner-before-outer
    -- probability with the centered annulus profile at the translated start point.
    simpa [ρ, R] using
      (importedAnnulusInnerExitProbabilityEqProfileConst
        (d := d) (Ω := Ω) (μ := (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
        (W := W) (x := x) (y := y) hW hρ hρx hR)
  have hprofile :
      importedCenteredAnnulusProfileConst (d := d) ρ R (x - y) =
        ((Real.log R - Real.log (dist x y)) /
          ((Real.log R - Real.log (dist x y)) + (n + 1 : ℝ))) := by
    -- Proof comment: in dimension `2`, the centered annulus profile is the logarithmic branch,
    -- and the chosen inner radius turns the denominator into the displayed affine term.
    subst hd2
    have hnorm : ‖x - y‖ = dist x y := by
      simp [dist_eq_norm, sub_eq_add_neg]
    have hlogρ :
        Real.log ρ = Real.log (dist x y) - (n + 1 : ℝ) := by
      rw [show ρ = dist x y * Real.exp (-(n + 1 : ℝ)) by rfl]
      rw [Real.log_mul hdist.ne' (Real.exp_ne_zero _), Real.log_exp]
      ring
    change centeredAnnulusProfileModel (d := 2) ρ R (x - y) =
      ((Real.log R - Real.log (dist x y)) /
        ((Real.log R - Real.log (dist x y)) + (n + 1 : ℝ)))
    simp [centeredAnnulusProfileModel]
    rw [hnorm, hlogρ]
    ring
  calc
    μ {ω |
        Continuous (fun t : NNReal ↦ W t ω) ∧
          (τ_[W, Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))]) ω <
            hittingAfter W (Metric.ball y (dist x y + m + 1))ᶜ 0 ω}
        ≤ μ {ω | (τ_[W, Metric.ball y ρ]) ω < hittingAfter W (Metric.ball y R)ᶜ 0 ω} := by
          simpa [ρ, R] using measure_mono hsubset
    _ = ENNReal.ofReal
          (importedCenteredAnnulusProfileConst (d := d) ρ R (x - y)) := hprob
    _ = ENNReal.ofReal
          ((Real.log (dist x y + m + 1) - Real.log (dist x y)) /
            ((Real.log (dist x y + m + 1) - Real.log (dist x y)) + (n + 1 : ℝ))) := by
          simpa [R] using congrArg ENNReal.ofReal hprofile

/-- Helper for Theorem 25.42: each fixed bounded annulus column has measure zero in the planar
off-start case once the continuity-intersected annulus estimate is available. -/
private theorem planarAnnulusColumn_measure_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess} {x y : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x)
    (hd2 : d = 2) (hxy : x ≠ y) (m : ℕ) :
    μ (⋂ n : ℕ,
      {ω |
        (τ_[W, Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))]) ω <
          hittingAfter W (Metric.ball y (dist x y + m + 1))ᶜ 0 ω}) = 0 := by
  let annulusHitEvent : ℕ → Set Ω := fun n ↦
    {ω |
      (τ_[W, Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))]) ω <
        hittingAfter W (Metric.ball y (dist x y + m + 1))ᶜ 0 ω}
  let badCont : Set Ω := {ω | ¬ Continuous (fun t : NNReal ↦ W t ω)}
  let c : ℝ := Real.log (dist x y + m + 1) - Real.log (dist x y)
  have hcont :
      ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω) :=
    brownianVectorStartedAt_aeContinuous hW
  have hbad_zero : μ badCont = 0 := by
    -- Proof comment: Brownian paths are almost surely continuous, so the complement event is
    -- null.
    simpa [badCont] using (ae_iff.1 hcont)
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have hc : 0 < c := by
    -- Proof comment: the outer radius is strictly larger than the start radius, so the logarithmic
    -- gap is positive.
    dsimp [c]
    refine sub_pos.mpr ?_
    refine Real.log_lt_log hdist ?_
    have hm_pos : (0 : ℝ) < m + 1 := by positivity
    linarith
  have hbound :
      ∀ n : ℕ, μ (⋂ k : ℕ, annulusHitEvent k) ≤ ENNReal.ofReal (c / (c + (n + 1 : ℝ))) := by
    intro n
    have hsplit :
        annulusHitEvent n ⊆
          badCont ∪ {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ annulusHitEvent n} := by
      intro ω hω
      by_cases hωcont : Continuous (fun t : NNReal ↦ W t ω)
      · exact Or.inr ⟨hωcont, hω⟩
      · exact Or.inl hωcont
    calc
      μ (⋂ k : ℕ, annulusHitEvent k) ≤ μ (annulusHitEvent n) := by
          exact measure_mono (Set.iInter_subset annulusHitEvent n)
      _ ≤ μ (badCont ∪ {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ annulusHitEvent n}) := by
          exact measure_mono hsplit
      _ ≤ μ badCont +
            μ {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ annulusHitEvent n} :=
          measure_union_le _ _
      _ ≤ μ badCont + ENNReal.ofReal (c / (c + (n + 1 : ℝ))) := by
          exact add_le_add le_rfl <| by
            simpa [annulusHitEvent, c] using
              planarExpAnnulusHitEvent_prob_le_ratio_onContinuous
                (Ω := Ω) (d := d) (μ := μ) (W := W) (x := x) (y := y)
                hW hd2 hxy m n
      _ = ENNReal.ofReal (c / (c + (n + 1 : ℝ))) := by
          rw [hbad_zero, zero_add]
  by_contra hcolumn_ne
  have hcolumn_lt_top : μ (⋂ k : ℕ, annulusHitEvent k) < ⊤ := measure_lt_top _ _
  have hcolumn_ne_top : μ (⋂ k : ℕ, annulusHitEvent k) ≠ ⊤ := hcolumn_lt_top.ne
  let p : ℝ := (μ (⋂ k : ℕ, annulusHitEvent k)).toReal
  have hp : 0 < p := by
    -- Proof comment: a nonzero finite measure has strictly positive real part.
    dsimp [p]
    exact ENNReal.toReal_pos hcolumn_ne hcolumn_ne_top
  obtain ⟨n, hn⟩ := exists_nat_gt (c / p)
  have hn' : c / p < (n : ℝ) + 1 := by
    linarith
  have hsmall_linear : c / ((n : ℝ) + 1) < p := by
    have hmul : c < ((n : ℝ) + 1) * p := by
      exact (div_lt_iff₀ hp).1 hn'
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    exact (div_lt_iff₀ hden_pos).2 (by simpa [mul_comm] using hmul)
  have hratio_le : c / (c + (n + 1 : ℝ)) ≤ c / ((n : ℝ) + 1) := by
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    have hden_le : (n : ℝ) + 1 ≤ c + (n + 1 : ℝ) := by linarith
    exact div_le_div_of_nonneg_left hc.le hden_pos hden_le
  have hsmall_ratio : c / (c + (n + 1 : ℝ)) < p :=
    lt_of_le_of_lt hratio_le hsmall_linear
  have hsmall :
      ENNReal.ofReal (c / (c + (n + 1 : ℝ))) < μ (⋂ k : ℕ, annulusHitEvent k) := by
    -- Proof comment: convert the real-valued strict upper bound back to `ENNReal`.
    exact
      (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hcolumn_ne_top).2 <| by
        simpa [p] using hsmall_ratio
  exact not_lt_of_ge (hbound n) hsmall

/-- Helper for Theorem 25.42: in dimension `2`, Brownian motion started away from `y` almost
surely never hits the singleton `{y}` at positive times. -/
private theorem singletonAvoidanceStartedAt_of_ne_dimension_two
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess} {x y : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x)
    (hd2 : d = 2) (hxy : x ≠ y) :
    ∀ᵐ ω ∂μ, (τ_[W, ({y} : Set State)]) ω = ⊤ := by
  let hitSingleton : Set Ω := {ω | (τ_[W, ({y} : Set State)]) ω < ⊤}
  let annulusHitEvent : ℕ → ℕ → Set Ω := fun m n ↦
    {ω |
      (τ_[W, Metric.ball y (dist x y * Real.exp (-(n + 1 : ℝ)))]) ω <
        hittingAfter W (Metric.ball y (dist x y + m + 1))ᶜ 0 ω}
  have hcont :
      ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω) :=
    brownianVectorStartedAt_aeContinuous hW
  have hsubset :
      {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ hitSingleton} ⊆
        ⋃ m : ℕ, ⋂ n : ℕ, annulusHitEvent m n := by
    -- Proof comment: exact singleton hits reduce pathwise to bounded annulus events once the path
    -- is known to be continuous on the hitting interval.
    simpa [hitSingleton, annulusHitEvent] using
      singletonHit_subset_iUnion_iInter_expAnnulusHitEvents
        (Ω := Ω) (d := d) (W := W) (x := x) (y := y) hxy
  let badCont : Set Ω := {ω | ¬ Continuous (fun t : NNReal ↦ W t ω)}
  let annulusColumn : ℕ → Set Ω := fun m ↦ ⋂ n : ℕ, annulusHitEvent m n
  have hbad_zero : μ badCont = 0 := by
    -- Proof comment: almost-sure continuity kills the exceptional noncontinuous paths.
    simpa [badCont] using (ae_iff.1 hcont)
  have hcolumn_zero : ∀ m : ℕ, μ (annulusColumn m) = 0 := by
    intro m
    -- Proof comment: each fixed outer radius gives a shrinking annulus column whose measure tends
    -- to zero via the bounded planar annulus estimate.
    simpa [annulusColumn, annulusHitEvent] using
      planarAnnulusColumn_measure_zero
        (Ω := Ω) (d := d) (μ := μ) (W := W) (x := x) (y := y)
        hW hd2 hxy m
  have hunion_zero : μ (⋃ m : ℕ, annulusColumn m) = 0 := by
    -- Proof comment: the union over the bounded annulus columns is still null because each column
    -- already has measure zero.
    refine le_antisymm ?_ (zero_le _)
    calc
      μ (⋃ m : ℕ, annulusColumn m) ≤ ∑' m : ℕ, μ (annulusColumn m) := measure_iUnion_le _
      _ = 0 := by simp [hcolumn_zero]
  have hcontHit_zero : μ {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ hitSingleton} = 0 := by
    -- Proof comment: the pathwise reduction `hsubset` puts every continuous exact singleton hit
    -- into the null union of bounded annulus columns.
    exact measure_mono_null hsubset hunion_zero
  have hhit_subset :
      hitSingleton ⊆ badCont ∪ {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ hitSingleton} := by
    intro ω hω
    by_cases hωcont : Continuous (fun t : NNReal ↦ W t ω)
    · exact Or.inr ⟨hωcont, hω⟩
    · exact Or.inl hωcont
  have hhit_zero : μ hitSingleton = 0 := by
    -- Proof comment: every singleton hit lies either on the null noncontinuous exceptional set or
    -- on the null continuous-hit set above.
    refine le_antisymm ?_ (zero_le _)
    calc
      μ hitSingleton ≤
          μ (badCont ∪ {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ hitSingleton}) := by
            exact measure_mono hhit_subset
      _ ≤ μ badCont + μ {ω | Continuous (fun t : NNReal ↦ W t ω) ∧ ω ∈ hitSingleton} :=
          measure_union_le _ _
      _ = 0 := by rw [hbad_zero, hcontHit_zero, zero_add]
  have havoid_ae : ∀ᵐ ω ∂μ, ω ∉ hitSingleton := compl_mem_ae_iff.2 hhit_zero
  filter_upwards [havoid_ae] with ω hω
  by_cases htop : (τ_[W, ({y} : Set State)]) ω = ⊤
  · exact htop
  · exfalso
    exact hω (lt_top_iff_ne_top.2 htop)

/-- Helper for Theorem 25.42: the family-level `d = 2` off-start branch is the measure-local
dimension-`2` singleton-avoidance theorem specialized to `P x`. -/
private theorem singletonAvoidance_of_ne_dimension_two
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd2 : d = 2) {x y : State} (hxy : x ≠ y) :
    ∀ᵐ ω ∂(P x : Measure Ω), (τ_[W, ({y} : Set State)]) ω = ⊤ := by
  -- Proof comment: the explicit-family theorem is only a wrapper around the measure-local input
  -- needed for the start-point restart argument.
  simpa using
    singletonAvoidanceStartedAt_of_ne_dimension_two
      (Ω := Ω) (d := d) (μ := (P x : Measure Ω)) (W := W) (x := x) (y := y)
      (hW := hW x) hd2 hxy

/-- Helper for Theorem 25.42: the bounded restart approximation event records arbitrarily fine
positive rational-time returns to `y` inside the time window `[0, M]`. -/
private def restartBoundedSingletonApproxEvent (y : State) (M : NNReal) :
    Set (State × (ℚ≥0 → State)) :=
  {p |
    ∀ n : ℕ, ∃ q : ℚ≥0, 0 < (q : NNReal) ∧ (q : NNReal) ≤ M ∧
      dist (p.1 + p.2 q) y < 1 / (n + 1 : ℝ)}

/-- Helper for Theorem 25.42: the bounded rational restart approximation event is measurable
because it is a countable intersection of countable unions of open distance conditions. -/
private theorem restartBoundedSingletonApproxEvent_measurable
    (y : State) (M : NNReal) :
    MeasurableSet (restartBoundedSingletonApproxEvent (d := d) y M) := by
  classical
  have hstep :
      ∀ n : ℕ,
        MeasurableSet
          (⋃ q : ℚ≥0,
            {p : State × (ℚ≥0 → State) |
              0 < (q : NNReal) ∧ (q : NNReal) ≤ M ∧
                dist (p.1 + p.2 q) y < 1 / (n + 1 : ℝ)}) := by
    intro n
    refine MeasurableSet.iUnion fun q : ℚ≥0 ↦ ?_
    by_cases hq0 : 0 < (q : NNReal)
    · by_cases hqM : (q : NNReal) ≤ M
      · have hsum :
            Measurable (fun p : State × (ℚ≥0 → State) ↦ p.1 + p.2 q) := by
          exact measurable_fst.add ((measurable_pi_apply q).comp measurable_snd)
        have hdist :
            Measurable fun p : State × (ℚ≥0 → State) ↦
              dist (p.1 + p.2 q) y < 1 / (n + 1 : ℝ) :=
          (hsum.dist measurable_const).lt measurable_const
        -- Proof comment: once the rational-time side conditions are fixed, only the open distance
        -- inequality remains.
        simpa [hq0, hqM, and_assoc] using hdist
      · simp [hq0, hqM]
    · simp [hq0]
  have hrepr :
      restartBoundedSingletonApproxEvent (d := d) y M =
        ⋂ n : ℕ,
          ⋃ q : ℚ≥0,
            {p : State × (ℚ≥0 → State) |
              0 < (q : NNReal) ∧ (q : NNReal) ≤ M ∧
                dist (p.1 + p.2 q) y < 1 / (n + 1 : ℝ)} := by
    ext p
    simp [restartBoundedSingletonApproxEvent]
  -- Proof comment: rewriting to the explicit `iInter`/`iUnion` normal form makes measurability
  -- immediate from the stepwise open conditions.
  rw [hrepr]
  exact MeasurableSet.iInter hstep

/-- Helper for Theorem 25.42: a genuine bounded hit of `y` along a continuous path yields the
bounded rational approximation event needed for the restart argument. -/
private theorem restartBoundedSingletonApproxEvent_of_exactHit
    {f : NNReal → State} {y : State} {M t : NNReal}
    (hcont : Continuous f) (ht : 0 < t) (htM : t ≤ M) (hft : f t = y) :
    ∀ n : ℕ, ∃ q : ℚ≥0, 0 < (q : NNReal) ∧ (q : NNReal) ≤ M ∧
      dist (f q) y < 1 / (n + 1 : ℝ) := by
  intro n
  let ε : ℝ := 1 / (n + 1 : ℝ)
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  let U : Set NNReal := {s | dist (f s) y < ε}
  have hUopen : IsOpen U := by
    -- Proof comment: continuity pulls the open `ε`-ball around `y` back to an open time set.
    simpa [U, ε] using Metric.isOpen_ball.preimage hcont
  have htU : t ∈ U := by
    -- Proof comment: the exact hit sits in every `ε`-ball around `y`.
    simpa [U, ε, hft] using hεpos
  have hUNhds : U ∈ nhds t := hUopen.mem_nhds htU
  have hhalf_lt : t / 2 < t := by
    linarith
  rcases
      (mem_nhds_iff_exists_Ioo_subset'
        (show ∃ l : NNReal, l < t from ⟨t / 2, hhalf_lt⟩)
        (show ∃ r : NNReal, t < r from
          ⟨t + 1, by simpa using lt_add_of_pos_right t zero_lt_one⟩)).1 hUNhds with
      ⟨l, r, ⟨hlt, htr⟩, hIoo⟩
  have hleft_lt_t : (max l (t / 2) : NNReal) < t := by
    refine max_lt_iff.2 ?_
    exact ⟨hlt, hhalf_lt⟩
  obtain ⟨q, hqleft, hqt⟩ :=
    exists_rat_btwn (show ((max l (t / 2) : NNReal) : ℝ) < (t : ℝ) by
      exact_mod_cast hleft_lt_t)
  let qnn : ℚ≥0 := ⟨q, by
    have hhalf_pos : (0 : ℝ) < ((t / 2 : NNReal) : ℝ) := by
      exact_mod_cast (show (0 : NNReal) < t / 2 by linarith)
    have hqpos_real : (0 : ℝ) < q := by
      exact lt_of_lt_of_le hhalf_pos
        (le_trans (by exact_mod_cast (le_max_right l (t / 2))) hqleft.le)
    have hqpos : (0 : ℚ) < q := by
      exact_mod_cast hqpos_real
    exact le_of_lt hqpos⟩
  have hql_nn : l < (qnn : NNReal) := by
    exact lt_of_le_of_lt (le_max_left _ _) (by exact_mod_cast hqleft)
  have hqt_nn : (qnn : NNReal) < t := by
    exact_mod_cast hqt
  have hq_mem : (qnn : NNReal) ∈ U := by
    apply hIoo
    exact ⟨hql_nn, hqt_nn.trans htr⟩
  refine ⟨qnn, ?_, hqt_nn.le.trans htM, ?_⟩
  · have hhalf_pos : (0 : NNReal) < t / 2 := by
      linarith
    exact lt_of_lt_of_le hhalf_pos (le_trans (le_max_right _ _) hqleft.le)
  · simpa [U, ε] using hq_mem

/-- Helper for Theorem 25.42: on a continuous path that starts away from `y`, the bounded rational
restart approximation event forces an actual bounded exact hit of `y`. -/
private theorem exactHit_of_restartBoundedSingletonApproxEvent
    {f : NNReal → State} {x y : State} {M : NNReal}
    (hcont : Continuous f) (h0 : f 0 = x) (hxy : x ≠ y)
    (hApprox :
      ∀ n : ℕ, ∃ q : ℚ≥0, 0 < (q : NNReal) ∧ (q : NNReal) ≤ M ∧
        dist (f q) y < 1 / (n + 1 : ℝ)) :
    ∃ t : NNReal, 0 < t ∧ t ≤ M ∧ f t = y := by
  let R : Set State := f '' Set.Icc (0 : NNReal) M
  have hRclosed : IsClosed R := by
    -- Proof comment: the path image of the compact time interval stays compact, hence closed.
    simpa [R] using (IsCompact.image isCompact_Icc hcont).isClosed
  have hyClosure : y ∈ closure R := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    rcases hApprox n with ⟨q, hqpos, hqM, hqdist⟩
    have hqdist' : dist y (f q) < 1 / (n + 1 : ℝ) := by
      simpa [dist_comm] using hqdist
    refine ⟨f q, ?_, lt_trans hqdist' hn⟩
    exact ⟨q, ⟨by simp, hqM⟩, rfl⟩
  have hyR : y ∈ R := by
    simpa [hRclosed.closure_eq] using hyClosure
  rcases hyR with ⟨t, htI, hty⟩
  have ht_ne : t ≠ 0 := by
    intro ht0
    apply hxy
    calc
      x = f 0 := h0.symm
      _ = y := by simpa [ht0] using hty
  -- Proof comment: closedness of the bounded image upgrades the approximation event to an actual
  -- hit, and the start-point separation excludes the degenerate time `0`.
  exact ⟨t, pos_iff_ne_zero.mpr ht_ne, htI.2, hty⟩

/-- Helper for Theorem 25.42: every positive-time marginal of a Brownian vector in dimensions
`d ≥ 2` avoids its deterministic start point with probability zero. -/
private theorem brownianVectorStartedAt_fixedTime_eq_start_prob_eq_zero
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : 2 ≤ d) (x : State) {t : NNReal} (ht : 0 < t) :
    (P x : Measure Ω) {ω | W t ω = x} = 0 := by
  let i0 : Fin d := ⟨0, by omega⟩
  let B : NNReal → Ω → ℝ := fun s ω ↦ W s ω i0
  have hB : IsBrownianMotionStartedAt (P x : Measure Ω) B (x i0) := by
    -- Proof comment: project to the first coordinate, where the deterministic-time law is a
    -- scalar Gaussian.
    simpa [B] using (hW x).isBrownianMotionStartedAt i0
  have hMeas : Measurable (B t) := (hB.stronglyMeasurable t).measurable
  have hLaw : HasLaw (B t) (gaussianReal (x i0) t) (P x : Measure Ω) := hB.gaussian_marginal ht
  have hsubset : {ω | W t ω = x} ⊆ {ω | B t ω = x i0} := by
    intro ω hω
    change W t ω = x at hω
    simpa [B] using congrArg (fun z : State ↦ z i0) hω
  apply le_antisymm
  · calc
      (P x : Measure Ω) {ω | W t ω = x}
          ≤ (P x : Measure Ω) {ω | B t ω = x i0} := measure_mono hsubset
      _ = (P x : Measure Ω).map (B t) ({x i0} : Set ℝ) := by
            symm
            rw [Measure.map_apply hMeas (MeasurableSet.singleton (x i0))]
            rfl
      _ = gaussianReal (x i0) t ({x i0} : Set ℝ) := by
            rw [hLaw.map_eq]
      _ = 0 := by
            exact (noAtoms_gaussianReal (ne_of_gt ht)).measure_singleton (x i0)
  · exact bot_le

/-- Helper for Theorem 25.42: the fixed-time start-point equality event is null, so almost every
positive-time Brownian state differs from the deterministic start. -/
private theorem brownianVectorStartedAt_fixedTime_ne_start_ae
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : 2 ≤ d) (x : State) {t : NNReal} (ht : 0 < t) :
    ∀ᵐ ω ∂(P x : Measure Ω), W t ω ≠ x := by
  -- Proof comment: the null singleton event from the previous lemma is exactly the complement of
  -- the desired almost-sure inequality.
  exact compl_mem_ae_iff.2 <| by
    simpa using
      brownianVectorStartedAt_fixedTime_eq_start_prob_eq_zero P W hW hd x ht

/-- Helper for Theorem 25.42: after restarting at a positive rational time, the start-at-`y`
branch reduces to the already available off-start singleton-avoidance statements. -/
private theorem singletonAvoidance_at_start_of_dimension_two_le
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : 2 ≤ d) (y : State) :
    ∀ᵐ ω ∂(P y : Measure Ω), (τ_[W, ({y} : Set State)]) ω = ⊤ := by
  let μ : Measure Ω := (P y : Measure Ω)
  let U : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - y
  have hU :
      IsStandardBrownianMotionVector μ U :=
    brownianVectorStartedAt_zeroPatched_isStandard P W hW y
  have hUstarted : IsBrownianMotionVectorStartedAt μ U 0 := by
    letI : IsStandardBrownianMotionVector μ U := hU
    infer_instance
  have hcontU :
      ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ U t ω) :=
    brownianVectorStartedAt_aeContinuous (Ω := Ω) (d := d) (μ := μ) (W := U) (x := 0) hUstarted
  let hitZero : Set Ω := {ω | (τ_[U, ({0} : Set State)]) ω < ⊤}
  let restartApproxEvent : ℕ → ℚ≥0 → Set Ω := fun m q ↦
    if hq : 0 < q then
      {ω |
        (U q ω, fun s : ℚ≥0 ↦ U ((q : NNReal) + s) ω - U q ω) ∈
          restartBoundedSingletonApproxEvent (d := d) (0 : State) m}
    else
      ∅
  have hrestart_zero :
      ∀ m : ℕ, ∀ q : ℚ≥0, μ (restartApproxEvent m q) = 0 := by
    intro m q
    by_cases hq : 0 < q
    · let X : Ω → State := fun ω ↦ U q ω
      let Z : Ω → ℚ≥0 → State := fun ω s ↦ U ((q : NNReal) + s) ω - U q ω
      let A : Set (State × (ℚ≥0 → State)) :=
        restartBoundedSingletonApproxEvent (d := d) (0 : State) m
      have hq_nnreal : 0 < (q : NNReal) := by
        exact_mod_cast hq
      have hX_meas : Measurable X := by
        simpa [X] using
          (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hU
            (q : NNReal)).measurable
      have hZ_meas : Measurable Z := by
        refine measurable_pi_lambda _ fun s ↦ ?_
        exact
          (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hU
              ((q : NNReal) + s)).measurable.sub
              ((ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hU
              (q : NNReal)).measurable)
      have hA_meas : MeasurableSet A :=
        restartBoundedSingletonApproxEvent_measurable (d := d) (y := (0 : State)) m
      have hsection :
          ∀ x : State, x ≠ 0 → ∀ᵐ z ∂μ.map Z, (x, z) ∉ A := by
        intro x hx
        let V : VectorProcess := fun t ω ↦ x + (U ((q : NNReal) + t) ω - U q ω)
        have hV :
            IsBrownianMotionVectorStartedAt μ V x :=
          translatedRestart_isBrownianVectorStartedAt
            (μ := μ) (d := d) (W := U) hU x (q : NNReal)
        have hAvoid :
            ∀ᵐ ω ∂μ, (τ_[V, ({0} : Set State)]) ω = ⊤ := by
          by_cases hd2 : d = 2
          · -- Proof comment: the planar off-start branch is exactly the remaining annulus input.
            simpa using
              singletonAvoidanceStartedAt_of_ne_dimension_two
                (Ω := Ω) (d := d) (μ := μ) (W := V) (x := x) (y := (0 : State))
                hV hd2 hx
          · have hdgt : 2 < d := by
              omega
            -- Proof comment: in higher dimensions, the already-proved shrinking-ball estimate
            -- gives the restarted singleton avoidance directly.
            simpa using
              singletonAvoidanceStartedAt_of_ne_dimension_gt_two
                (Ω := Ω) (d := d) (μ := μ) (W := V) (x := x) (y := (0 : State))
                hV hdgt hx
        have hcontV :
            ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ V t ω) :=
          brownianVectorStartedAt_aeContinuous
            (Ω := Ω) (d := d) (μ := μ) (W := V) (x := x) hV
        let S : Set (ℚ≥0 → State) := {z | (x, z) ∈ A}
        have hS_meas : MeasurableSet S := by
          exact measurable_prodMk_left hA_meas
        have hsection_pre :
            ∀ᵐ ω ∂μ, Z ω ∉ S := by
          filter_upwards [hAvoid, hcontV] with ω hωAvoid hωCont
          intro hωS
          have hApprox :
              ∀ n : ℕ, ∃ r : ℚ≥0, 0 < (r : NNReal) ∧ (r : NNReal) ≤ m ∧
                dist (V r ω) (0 : State) < 1 / (n + 1 : ℝ) := by
            simpa
              [A, S, V, Z, restartBoundedSingletonApproxEvent, add_assoc, add_left_comm, add_comm]
              using hωS
          have hExact :
              ∃ t : NNReal, 0 < t ∧ t ≤ m ∧ V t ω = (0 : State) :=
            exactHit_of_restartBoundedSingletonApproxEvent
              (f := fun t : NNReal ↦ V t ω) (x := x) (y := (0 : State))
              hωCont (by simp [V]) hx hApprox
          rcases hExact with ⟨t, ht_pos, _, ht_zero⟩
          have hτlt :
              (τ_[V, ({0} : Set State)]) ω < ⊤ :=
            (strictPositiveHittingTime_lt_top_iff V ({0} : Set State) ω).2
              ⟨t, ht_pos, by simp [ht_zero]⟩
          exact (ne_of_lt hτlt) hωAvoid
        exact (ae_map_iff hZ_meas.aemeasurable hS_meas.compl).2 hsection_pre
      let B : Set (State × (ℚ≥0 → State)) := {p | p.1 ≠ 0} ∩ A
      have hB_meas : MeasurableSet B := by
        have hneq_meas : MeasurableSet {p : State × (ℚ≥0 → State) | p.1 ≠ (0 : State)} := by
          exact (isClosed_eq continuous_fst continuous_const).measurableSet.compl
        exact hneq_meas.inter hA_meas
      have hprod_ae :
          ∀ᵐ p : State × (ℚ≥0 → State) ∂((μ.map X).prod (μ.map Z)), p ∉ B := by
        rw [Measure.ae_prod_iff_ae_ae hB_meas.compl]
        filter_upwards with x
        by_cases hx : x = 0
        · exact Filter.Eventually.of_forall fun z ↦ by simp [B, hx]
        · exact (hsection x hx).mono fun z hz ↦ by simp [B, hx, hz]
      have hpair_map :
          μ.map (fun ω ↦ (X ω, Z ω)) = (μ.map X).prod (μ.map Z) := by
        exact
          (indepFun_iff_map_prod_eq_prod_map_map hX_meas.aemeasurable hZ_meas.aemeasurable).1
            (futureIncrementRatPath_indep_currentState
              (μ := μ) (d := d) (W := U) hU q).symm
      have hpair_ae :
          ∀ᵐ ω ∂μ, (X ω, Z ω) ∉ B := by
        rw
          [← ae_map_iff (hX_meas.aemeasurable.prodMk hZ_meas.aemeasurable) hB_meas.compl,
            hpair_map]
        exact hprod_ae
      have hX_ne_zero :
          ∀ᵐ ω ∂μ, X ω ≠ 0 := by
        -- Proof comment: at every positive restart time, the Brownian state is almost surely
        -- away from the deterministic start, hence the recentered state is almost surely nonzero.
        filter_upwards
          [brownianVectorStartedAt_fixedTime_ne_start_ae
            (Ω := Ω) (d := d) (P := P) (W := W) hW hd y hq_nnreal] with ω hω
        simpa [X, U, hq_nnreal.ne'] using sub_ne_zero.mpr hω
      have havoid_event :
          ∀ᵐ ω ∂μ, ω ∉ {ω |
            (U q ω, fun s : ℚ≥0 ↦ U ((q : NNReal) + s) ω - U q ω) ∈ A} := by
        filter_upwards [hpair_ae, hX_ne_zero] with ω hωPair hωX
        intro hωA
        exact hωPair ⟨hωX, hωA⟩
      have hEventZero :
          μ {ω |
              (U q ω, fun s : ℚ≥0 ↦ U ((q : NNReal) + s) ω - U q ω) ∈ A} = 0 :=
        compl_mem_ae_iff.1 havoid_event
      simpa [restartApproxEvent, hq, A, hEventZero]
    · simp [restartApproxEvent, hq]
  have hrestartUnion_zero :
      μ (⋃ m : ℕ, ⋃ q : ℚ≥0, restartApproxEvent m q) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      μ (⋃ m : ℕ, ⋃ q : ℚ≥0, restartApproxEvent m q)
          ≤ ∑' m : ℕ, μ (⋃ q : ℚ≥0, restartApproxEvent m q) := by
            exact measure_iUnion_le (fun m ↦ ⋃ q : ℚ≥0, restartApproxEvent m q)
      _ ≤ ∑' m : ℕ, ∑' q : ℚ≥0, μ (restartApproxEvent m q) := by
            refine ENNReal.tsum_le_tsum ?_
            intro m
            exact measure_iUnion_le (fun q : ℚ≥0 ↦ restartApproxEvent m q)
      _ = 0 := by
            simp [hrestart_zero]
  have hhit_subset :
      hitZero ⊆
        {ω | ¬ Continuous (fun t : NNReal ↦ U t ω)} ∪
          ⋃ m : ℕ, ⋃ q : ℚ≥0, restartApproxEvent m q := by
    intro ω hω
    by_cases hωCont : Continuous (fun t : NNReal ↦ U t ω)
    · right
      rcases (strictPositiveHittingTime_lt_top_iff U ({0} : Set State) ω).1 hω with
        ⟨t, ht_pos, ht_zero⟩
      obtain ⟨m, hm⟩ := exists_nat_ge t
      obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn (show (0 : ℝ) < (t : ℝ) by exact_mod_cast ht_pos)
      let qnn : ℚ≥0 := ⟨q, le_of_lt (by exact_mod_cast hq0)⟩
      have hqnn_pos : 0 < qnn := by
        exact_mod_cast hq0
      have hqnn_pos_nnreal : 0 < (qnn : NNReal) := by
        exact_mod_cast hq0
      have hqnn_lt_t : (qnn : NNReal) < t := by
        exact_mod_cast hqt
      have hshiftCont : Continuous (fun s : NNReal ↦ U ((qnn : NNReal) + s) ω) :=
        hωCont.comp (continuous_const.add continuous_id)
      have hshiftHit :
          U ((qnn : NNReal) + (t - (qnn : NNReal))) ω = (0 : State) := by
        rw [add_tsub_cancel_of_le hqnn_lt_t.le]
        exact ht_zero
      have hApprox :
          ∀ n : ℕ, ∃ r : ℚ≥0, 0 < (r : NNReal) ∧ (r : NNReal) ≤ m ∧
            dist (U ((qnn : NNReal) + r) ω) (0 : State) < 1 / (n + 1 : ℝ) :=
        restartBoundedSingletonApproxEvent_of_exactHit
          (f := fun s : NNReal ↦ U ((qnn : NNReal) + s) ω) (y := (0 : State))
          (M := m) (t := t - (qnn : NNReal))
          hshiftCont (tsub_pos_of_lt hqnn_lt_t) (le_trans (tsub_le_self) hm) hshiftHit
      have hEvent :
          (U qnn ω, fun s : ℚ≥0 ↦ U ((qnn : NNReal) + s) ω - U qnn ω) ∈
            restartBoundedSingletonApproxEvent (d := d) (0 : State) m := by
        intro n
        rcases hApprox n with ⟨r, hr_pos, hrm, hr_dist⟩
        refine ⟨r, hr_pos, hrm, ?_⟩
        simpa [add_assoc, add_left_comm, add_comm]
          using hr_dist
      refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨qnn, ?_⟩⟩
      show ω ∈ restartApproxEvent m qnn
      simp [restartApproxEvent, hqnn_pos, hEvent]
    · exact Or.inl hωCont
  have hBadContZero :
      μ {ω | ¬ Continuous (fun t : NNReal ↦ U t ω)} = 0 :=
    by
      have hGoodCont :
          ∀ᵐ ω ∂μ, ω ∉ {ω | ¬ Continuous (fun t : NNReal ↦ U t ω)} := by
        filter_upwards [hcontU] with ω hω
        simpa using hω
      exact compl_mem_ae_iff.1 hGoodCont
  have hHitZero :
      μ hitZero = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      μ hitZero
          ≤ μ ({ω | ¬ Continuous (fun t : NNReal ↦ U t ω)} ∪
              ⋃ m : ℕ, ⋃ q : ℚ≥0, restartApproxEvent m q) := by
            exact measure_mono hhit_subset
      _ ≤ μ {ω | ¬ Continuous (fun t : NNReal ↦ U t ω)} +
            μ (⋃ m : ℕ, ⋃ q : ℚ≥0, restartApproxEvent m q) := by
            exact measure_union_le _ _
      _ = 0 := by simp [hBadContZero, hrestartUnion_zero]
  have hAvoidZero :
      ∀ᵐ ω ∂μ, (τ_[U, ({0} : Set State)]) ω = ⊤ :=
    by
      have hAvoidSet : ∀ᵐ ω ∂μ, ω ∉ hitZero := compl_mem_ae_iff.2 hHitZero
      filter_upwards [hAvoidSet] with ω hω
      by_cases hτ : (τ_[U, ({0} : Set State)]) ω = ⊤
      · exact hτ
      · exfalso
        exact hω (lt_top_iff_ne_top.2 hτ)
  -- Proof comment: positive-time hits of `y` for `W` are exactly positive-time hits of `0` for
  -- the recentered standard Brownian motion `U`.
  filter_upwards [hAvoidZero] with ω hω
  refine (strictPositiveHittingTime_eq_top_iff W ({y} : Set State) ω).2 ?_
  intro t ht hty
  have hAvoidU := (strictPositiveHittingTime_eq_top_iff U ({0} : Set State) ω).1 hω
  have : U t ω ∉ ({0} : Set State) := hAvoidU t ht
  exact this (by simpa [U, ht.ne'] using sub_eq_zero.mpr (by simpa using hty))

/- Proof sketch: if `A` is nonempty, choose `y ∈ A`. In dimension `1`, one-dimensional Brownian
motion started at `y` returns arbitrarily close to `y` at arbitrarily large times almost surely by
Theorem 25.39, so `A` cannot be polar. The empty set is polar by definition. -/
variable (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
variable (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)

/-- Helper for Theorem 25.42: the dimension-`1` polar-set criterion with explicit Brownian-family
binders. -/
private theorem isPolarSet_iff_eq_empty_of_dimension_one_core
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : d = 1) (A : Set State) :
    IsPolarSet P W A ↔ A = ∅ := by
  constructor
  · intro hPolar
    by_cases hA : A = ∅
    · exact hA
    have hA_nonempty : A.Nonempty := by
      by_contra hAempty
      exact hA (Set.not_nonempty_iff_eq_empty.mp hAempty)
    rcases hA_nonempty with ⟨y, hyA⟩
    rw [isPolarSet_iff] at hPolar
    have hreturn := returnsToStart_ae_of_dimension_one P W hW hd y
    have hcontr :
        ∀ᵐ ω ∂(P y : Measure Ω), False := by
      -- Proof comment: polarity forbids every strictly positive revisit of `A`, but the
      -- one-dimensional return lemma gives such a revisit to the chosen point `y ∈ A`.
      filter_upwards [hPolar y, hreturn] with ω hω hret
      rcases hret with ⟨t, ht_pos, ht_eq⟩
      exact hω t ht_pos (by simp [hyA, ht_eq])
    have hzero_univ : (P y : Measure Ω) Set.univ = 0 := by
      simpa [ae_iff] using hcontr
    have : False := by
      simpa using hzero_univ
    exact False.elim this
  · intro hA
    -- Proof comment: the empty set is polar by the defining avoidance characterization.
    simpa [hA] using isPolarSet_empty P W

/-- First clause of Theorem 25.42: if `d = 1`, then a set in `ℝ^d` is polar exactly when it is
empty. -/
theorem isPolarSet_iff_eq_empty_of_dimension_one
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : d = 1) (A : Set State) :
    IsPolarSet P W A ↔ A = ∅ := by
  simpa using isPolarSet_iff_eq_empty_of_dimension_one_core P W hW hd A

/- Proof sketch: translate the singleton to `{0}` and use the ball-hitting formula from
Theorem 25.40. For `x ≠ y`, the probability of ever hitting `{y}` is the limit of the ball-hit
probabilities as the radius tends to `0`, which is `0` in dimensions `d ≥ 2`. For `x = y`, use
the strong Markov property together with the fact that Brownian motion is almost surely away from
its starting point at each fixed positive time. -/
/-- Theorem 25.42 (2): if `d ≥ 2`, then every singleton `{y}` in `ℝ^d` is polar. -/
theorem isPolarSet_singleton_of_dimension_two_le
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hd : 2 ≤ d) (y : State) :
    IsPolarSet P W {y} := by
  intro x
  by_cases hxy : x = y
  · cases hxy
    -- Proof comment: after recentering at `y`, the positive-time start branch becomes a standard
    -- Brownian restart problem with only the off-start singleton-avoidance input remaining.
    simpa using singletonAvoidance_at_start_of_dimension_two_le P W hW hd y
  · by_cases hd2 : d = 2
    · -- Proof comment: the only remaining gap is the off-start planar annulus theorem.
      simpa using singletonAvoidance_of_ne_dimension_two P W hW hd2 hxy
    · have hdgt : 2 < d := by
        omega
      -- Proof comment: in dimensions `d > 2`, the already-proved shrinking-ball estimate is the
      -- full off-start singleton-avoidance theorem.
      simpa using
        singletonAvoidance_of_ne_dimension_gt_two
          (Ω := Ω) (d := d) (P := P) (W := W) (hW := hW) (x := x) (y := y) hdgt hxy

end BrownianPolarSets

end ProbabilityTheory
