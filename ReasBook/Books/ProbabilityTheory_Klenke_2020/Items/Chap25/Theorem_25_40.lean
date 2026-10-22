/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.BrownianMotionVectorStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Lemma_25_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Corollary_25_35.QuadraticPrimitiveBridge
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Topology Laplacian
open scoped ProbabilityTheory Topology Manifold BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 25.40: the time derivative of a function on `State × ℝ`, taken in the
last coordinate. This local wrapper keeps the time-independent Ito-lift route available without
importing the heavier Chapter 25 time-dependent file. -/
private noncomputable def timePartialDeriv_theorem25_40 (F : State × ℝ → ℝ) : State × ℝ → ℝ :=
  fun xt ↦ deriv (fun s : ℝ ↦ F (xt.1, s)) xt.2

/-- Helper for Theorem 25.40: a local `C^{2,1}` owner for time-dependent lifts. The current file
only needs this wrapper to record the translated time-independent route for a future Ito bridge.
-/
private class IsTimeSpaceC21_theorem25_40 (F : State × ℝ → ℝ) : Prop where
  hasDerivAt_time (xt : State × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ F (xt.1, s))
      (timePartialDeriv_theorem25_40 F xt)
      xt.2
  continuous_timePartialDeriv : Continuous (timePartialDeriv_theorem25_40 F)
  hasDerivAt_space (i : Fin d) (xt : State × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ F (xt.1 + EuclideanSpace.single i (s - xt.1 i), xt.2))
      ((∂[i] fun x : State ↦ F (x, xt.2)) xt.1)
      (xt.1 i)
  continuous_spacePartialDeriv (i : Fin d) :
    Continuous (fun xt : State × ℝ ↦ (∂[i] fun x : State ↦ F (x, xt.2)) xt.1)
  hasDerivAt_spaceSecond (i j : Fin d) (xt : State × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        (∂[i] fun x : State ↦ F (x, xt.2))
          (xt.1 + EuclideanSpace.single j (s - xt.1 j)))
      ((∂²[i, j] fun x : State ↦ F (x, xt.2)) xt.1)
      (xt.1 j)
  continuous_spaceSecondPartialDeriv (i j : Fin d) :
    Continuous (fun xt : State × ℝ ↦ (∂²[i, j] fun x : State ↦ F (x, xt.2)) xt.1)

/-- Helper for Theorem 25.40: for `F ∈ C²(State)`, each coordinate partial derivative `∂[i] F`
is continuous. This keeps the theorem-local regularity route independent of the heavier Chapter
25 files. -/
private theorem continuousPartialDeriv_theorem25_40
    (F : State → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin d) :
    Continuous (∂[i] F) := by
  have happly :
      Continuous fun x : State ↦ (fderiv ℝ F x) (EuclideanSpace.single i (1 : ℝ)) := by
    -- Proof comment: a `C²` map has continuous Fréchet derivative, and evaluation at the fixed
    -- basis vector `eᵢ` preserves continuity.
    simpa using
      (hF.continuous_fderiv_apply (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).comp
        (continuous_id.prodMk continuous_const)
  -- Proof comment: rewrite the coordinate derivative through the Fréchet derivative formula from
  -- Theorem 25.30.
  simpa [partialDeriv_eq_fderiv_apply F (hF.differentiable (by norm_num)) i] using happly

/-- The strictly positive first hitting time of `A` by `X`, with value `⊤` when the path never
hits `A` after time `0`. This local interface avoids importing the broken Chapter 21 exercise
while keeping the Chapter 25 statements unchanged. -/
def strictPositiveHittingTime (X : NNReal → Ω → State) (A : Set State) : Ω → WithTop NNReal :=
  fun ω ↦
    if _ : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A then
      ((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal)
    else ⊤

scoped notation:arg "τ_[" X ", " A "]" => strictPositiveHittingTime X A

/-- Helper for Theorem 25.40: `τ_[X, A] ω = ⊤` exactly when the path avoids `A` at every strictly
positive time. -/
theorem strictPositiveHittingTime_eq_top_iff
    {Ω₀ : Type u} (X : NNReal → Ω₀ → State) (A : Set State) (ω : Ω₀) :
    (τ_[X, A]) ω = ⊤ ↔ ∀ t : NNReal, 0 < t → X t ω ∉ A := by
  by_cases h : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A
  · rcases h with ⟨t, ht, hA⟩
    have h' : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A := ⟨t, ht, hA⟩
    constructor
    · intro hEq
      have hne :
          (((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal) : WithTop NNReal) ≠ ⊤ := by
        intro htop
        cases htop
      exact False.elim <| hne <| by simpa [strictPositiveHittingTime, h'] using hEq
    · intro havoid
      exfalso
      exact havoid t ht hA
  · constructor
    · intro _ t ht hA
      exact h ⟨t, ht, hA⟩
    · intro havoid
      simp [strictPositiveHittingTime, h]

/-- Helper for Theorem 25.40: finiteness of the strict positive hitting time is equivalent to the
existence of a strictly positive hit. -/
theorem strictPositiveHittingTime_lt_top_iff
    {Ω₀ : Type u} (X : NNReal → Ω₀ → State) (A : Set State) (ω : Ω₀) :
    (τ_[X, A]) ω < ⊤ ↔ ∃ t : NNReal, 0 < t ∧ X t ω ∈ A := by
  constructor
  · intro hτ
    by_contra hHit
    have htop : (τ_[X, A]) ω = ⊤ := by
      -- Proof comment: if no positive hit exists, the preceding owner lemma forces the clock to
      -- be `⊤`.
      refine (strictPositiveHittingTime_eq_top_iff X A ω).2 ?_
      intro t ht hA
      exact hHit ⟨t, ht, hA⟩
    exact (ne_of_lt hτ) htop
  · rintro ⟨t, ht, hA⟩
    have htop : (τ_[X, A]) ω ≠ ⊤ := by
      intro htop
      -- Proof comment: a realized positive hit contradicts the top-clock characterization.
      exact ((strictPositiveHittingTime_eq_top_iff X A ω).1 htop) t ht hA
    exact lt_of_le_of_ne le_top htop

/-- Helper for Theorem 25.40: a realized strictly positive hit bounds the strict positive hitting
time from above. -/
theorem strictPositiveHittingTime_le_of_mem
    {Ω₀ : Type u} (X : NNReal → Ω₀ → State) (A : Set State) (ω : Ω₀) {t : NNReal}
    (ht : 0 < t) (hA : X t ω ∈ A) :
    (τ_[X, A]) ω ≤ t := by
  by_cases hHit : ∃ s : NNReal, 0 < s ∧ X s ω ∈ A
  · have hsInf_le : sInf {s : NNReal | 0 < s ∧ X s ω ∈ A} ≤ t :=
      csInf_le
        ⟨0, by
          intro s hs
          exact hs.1.le⟩
        (by
          exact ⟨ht, hA⟩)
    simpa [strictPositiveHittingTime, hHit] using (show ((sInf {s : NNReal | 0 < s ∧ X s ω ∈ A}
      : NNReal) : WithTop NNReal) ≤ t from by exact_mod_cast hsInf_le)
  · exact False.elim (hHit ⟨t, ht, hA⟩)

/-- Helper for Theorem 25.40: the strict positive ball-hitting event can be rewritten as the event
that the path actually enters the ball at some positive time. -/
theorem strictPositiveHittingEvent_eq_exists_hit
    {Ω₀ : Type u} (X : NNReal → Ω₀ → State) (A : Set State) :
    {ω | (τ_[X, A]) ω < ⊤} = {ω | ∃ t : NNReal, 0 < t ∧ X t ω ∈ A} := by
  -- Proof comment: convert the event pointwise using the clock characterization.
  ext ω
  exact strictPositiveHittingTime_lt_top_iff X A ω

/-- Helper for Theorem 25.40: a Brownian vector started at a deterministic point has almost surely
continuous sample paths. -/
theorem brownianVectorStartedAt_aeContinuous
    {μ : Measure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x) :
    ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω) := by
  have hcont_coord :
      ∀ i : Fin d, ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω i) := by
    intro i
    -- Proof comment: each coordinate owner already carries the almost-sure continuity statement.
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      (hW.isBrownianMotionStartedAt i).continuous_paths
  have hall :
      ∀ᵐ ω ∂μ, ∀ i : Fin d, Continuous (fun t : NNReal ↦ W t ω i) := by
    rw [ae_all_iff]
    intro i
    exact hcont_coord i
  filter_upwards [hall] with ω hω
  have hcoords : Continuous (fun t : NNReal ↦ fun i : Fin d ↦ W t ω i) :=
    continuous_pi fun i ↦ hω i
  -- Proof comment: continuity of the Euclidean path is coordinatewise continuity on the finite
  -- product model of `State`.
  simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp hcoords

/-- Helper for Theorem 25.40: a Brownian vector started at a deterministic point also starts
there almost surely at time `0` as a `State`-valued process. -/
private theorem brownianVectorStart_ae_eq_const
    (μ : ProbabilityMeasure Ω)
    {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x := by
  have hcoords :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ i : Fin d, W 0 ω i = x i := by
    rw [ae_all_iff]
    intro i
    exact
      brownianStart_ae_eq_const_of_measurable
        ((hW.isBrownianMotionStartedAt i).stronglyMeasurable 0).measurable
        (hW.isBrownianMotionStartedAt i)
  -- Proof comment: coordinatewise almost-sure equality upgrades to equality in the Euclidean
  -- state space by extensionality.
  filter_upwards [hcoords] with ω hω
  ext i
  exact hω i

/-- Helper for Theorem 25.40: in dimension `0`, the Euclidean state space is a subsingleton. -/
theorem stateSubsingleton_of_zero_dim (hd : d = 0) : Subsingleton State := by
  subst hd
  infer_instance

/-- Helper for Theorem 25.40: the distance between any two points vanishes in dimension `0`. -/
theorem dist_eq_zero_of_zero_dim (hd : d = 0) (x y : State) : dist x y = 0 := by
  letI : Subsingleton State := stateSubsingleton_of_zero_dim (d := d) hd
  have hxy : x = y := Subsingleton.elim x y
  simp [hxy]

/-- Helper for Theorem 25.40: the radius assumption rules out the degenerate zero-dimensional
state space. -/
theorem ne_zero_of_radius_lt_dist
    (x y : State) {r : ℝ} (hr : 0 < r) (hxy : r < dist x y) :
    d ≠ 0 := by
  intro hd
  have hdist : dist x y = 0 := dist_eq_zero_of_zero_dim (d := d) hd x y
  linarith

/-- Helper for Theorem 25.40: subtracting the deterministic starting point from a scalar Brownian
motion started at `x` produces a Brownian motion started at `0`. -/
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
  · -- Proof comment: subtracting a constant preserves strong measurability of each time slice.
    intro t
    exact (hB.stronglyMeasurable t).sub stronglyMeasurable_const
  · -- Proof comment: the recentered time-zero event is exactly the original start event at `x`.
    have hpreimage :
        (fun ω ↦ B 0 ω - x) ⁻¹' ({0} : Set ℝ) = B 0 ⁻¹' ({x} : Set ℝ) := by
      ext ω
      constructor
      · intro hω
        change B 0 ω - x = 0 at hω
        change B 0 ω = x
        linarith
      · intro hω
        have hxω : B 0 ω = x := by
          simpa using hω
        change B 0 ω - x = 0
        simp [hxω]
    rw [hpreimage]
    exact hB.start
  · -- Proof comment: subtracting the same constant from every time slice does not change
    -- increments.
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB.indepIncrements n t ht
  · -- Proof comment: stationary increments are preserved by the same cancellation.
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB.stationaryIncrements r s t
  · -- Proof comment: the time-`t` marginal is translated from mean `x` to mean `0`.
    intro t ht
    simpa using ProbabilityTheory.gaussianReal_sub_const (hB.gaussian_marginal ht) x
  · -- Proof comment: path continuity is preserved under subtraction of a deterministic constant.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Theorem 25.40: covariance is unchanged under almost-everywhere replacement of the
two random variables. -/
private theorem covariance_congr_ae_theorem25_40
    {μ : Measure Ω} {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : μ[X] = μ[X'] := MeasureTheory.integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := MeasureTheory.integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Theorem 25.40: patching the time-zero value of a Brownian motion started at `0`
to the literal constant `0` yields the standard Brownian spelling. -/
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
    -- Proof comment: the pointwise-zero version is a deterministic-time modification of `B`, so
    -- the centered mean identity transports slice by slice.
    rw [integral_congr_ae (hmod t), hmean t]
  have hcov0 : ∀ s t : NNReal, cov[B0 s, B0 t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance is invariant under almost-everywhere equality of the individual
    -- deterministic-time slices.
    rw [covariance_congr_ae_theorem25_40 (hmod s) (hmod t), startedAtZero_covariance_eq hB s t]
  have hcont0 : HasAlmostSurelyContinuousPaths μ B0 := by
    -- Proof comment: on the full-measure start event `B 0 = 0`, the patched path agrees with the
    -- original continuous Brownian path at every time.
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
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ B0).2
      ⟨by
          funext ω
          simp [B0]
        , hgauss0, hmean0, hcov0, hcont0⟩

/-- Helper for Theorem 25.40: patching a Brownian motion started at `0` on one measurable null
set by the constant-zero path preserves the Brownian law and makes every sample path continuous.
This is the scalar owner-level bridge used to build a same-space continuous modification of a
Brownian vector started at a deterministic point. -/
private theorem zeroStarted_nullPatch_isBrownianMotion
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotionStartedAt μ B 0)
    {N : Set Ω} (hN_meas : MeasurableSet N) (hN_null : μ N = 0)
    (hcont : ∀ ω ∉ N, Continuous fun t : NNReal ↦ B t ω)
    (hzero : ∀ ω ∉ N, B 0 ω = 0) :
    IsBrownianMotion μ (fun t ω ↦ if ω ∈ N then 0 else B t ω) := by
  let Bc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else B t ω
  have hOutside : ∀ᵐ ω ∂μ, ω ∉ N := by
    exact compl_mem_ae_iff.mpr hN_null
  have hmod : ∀ t : NNReal, Bc t =ᵐ[μ] B t := by
    intro t
    filter_upwards [hOutside] with ω hω
    simp [Bc, hω]
  have hgauss : IsGaussianProcess B μ :=
    IsBrownianMotionStartedAt.isGaussianProcess_zero hB
  have hgaussc : IsGaussianProcess Bc μ := hgauss.congr fun t ↦ (hmod t).symm
  have hmean : ∀ t : NNReal, ∫ ω, B t ω ∂μ = 0 :=
    (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance μ B).1 hB
      |>.2.2.1
  have hmeanc : ∀ t : NNReal, ∫ ω, Bc t ω ∂μ = 0 := by
    intro t
    -- Proof comment: deterministic-time null-set patching preserves the centered mean of each
    -- Brownian slice.
    rw [integral_congr_ae (hmod t), hmean t]
  have hcovc : ∀ s t : NNReal, cov[Bc s, Bc t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance is unchanged when both deterministic-time slices are replaced
    -- almost everywhere by the null-set patch.
    rw [covariance_congr_ae_theorem25_40 (hmod s) (hmod t), startedAtZero_covariance_eq hB s t]
  have hcontc : HasAlmostSurelyContinuousPaths μ Bc := by
    -- Proof comment: off the chosen null set the path is the original continuous sample path, and
    -- on the null set it is the constant-zero path.
    filter_upwards [hOutside] with ω hω
    by_cases hωN : ω ∈ N
    · have hPathEq : processPath Bc ω = fun _ : NNReal ↦ (0 : ℝ) := by
        funext t
        simp [processPath, Bc, hωN]
      simpa [HasAlmostSurelyContinuousPaths] using
        hPathEq ▸ (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
    · have hPathEq : processPath Bc ω = fun t : NNReal ↦ B t ω := by
        funext t
        simp [processPath, Bc, hωN]
      simpa [HasAlmostSurelyContinuousPaths] using hPathEq ▸ hcont ω hωN
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ Bc).2
      ⟨by
          funext ω
          by_cases hω : ω ∈ N
          · simp [Bc, hω]
          · simp [Bc, hω, hzero ω hω]
        , hgaussc, hmeanc, hcovc, hcontc⟩

/-- Helper for Theorem 25.40: a Brownian vector started at `x` admits a same-space modification
whose sample paths are everywhere continuous and which agrees with the original process at all
times outside one measurable null set. -/
private theorem existsContinuousBrownianVectorStartedAtModification
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    ∃ Wc : VectorProcess,
      IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω) ∧
      (∀ ω : Ω, Wc 0 ω = x) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, W t ω = Wc t ω) := by
  have hcont_ae :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous fun t : NNReal ↦ W t ω :=
    brownianVectorStartedAt_aeContinuous hW
  have hstart_ae :
      ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x := by
    have hcoords :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ i : Fin d, W 0 ω i = x i := by
      rw [ae_all_iff]
      intro i
      exact
        brownianStart_ae_eq_const_of_measurable
          ((hW.isBrownianMotionStartedAt i).stronglyMeasurable 0).measurable
          (hW.isBrownianMotionStartedAt i)
    filter_upwards [hcoords] with ω hω
    ext i
    exact hω i
  have hgood :
      ∀ᵐ ω ∂(μ : Measure Ω), (Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x :=
    hcont_ae.and hstart_ae
  let bad : Set Ω := {ω | ¬ ((Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x)}
  have hbad_null : (μ : Measure Ω) bad = 0 := by
    simpa [bad] using (ae_iff.1 hgood)
  obtain ⟨N, hbad_subset, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hbad_null
  have hN_good :
      ∀ ω : Ω, ω ∉ N → (Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x := by
    intro ω hωN
    by_contra hbadω
    exact hωN (hbad_subset hbadω)
  let Wc : VectorProcess := fun t ω ↦ if ω ∈ N then x else W t ω
  have hWc_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa [Wc, hω] using (continuous_const : Continuous fun _ : NNReal ↦ x)
    · simpa [Wc, hω] using (hN_good ω hω).1
  have hWc_eq :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, W t ω = Wc t ω := by
    filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω t
    have hω' : ω ∉ N := by simpa using hω
    simp [Wc, hω']
  have hWc_start : ∀ ω : Ω, Wc 0 ω = x := by
    intro ω
    by_cases hω : ω ∈ N
    · simp [Wc, hω]
    · simpa [Wc, hω] using (hN_good ω hω).2
  have hWc_owner : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x := by
    refine
      { isBrownianMotionStartedAt := ?_
        iIndepFun := ?_ }
    · intro i
      let B : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
      let Bc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else B t ω
      have hB : IsBrownianMotionStartedAt (μ : Measure Ω) B 0 := by
        -- Proof comment: recenter the `i`-th coordinate at its deterministic start value.
        simpa [B] using
          brownianStartedAt_sub_const_startedAtZero
            (hW.isBrownianMotionStartedAt i)
      have hBc : IsBrownianMotion (μ : Measure Ω) Bc := by
        -- Proof comment: patch the recentered coordinate on the common null set so every sample
        -- path becomes continuous.
        apply zeroStarted_nullPatch_isBrownianMotion
          (μ := (μ : Measure Ω)) (B := B) hB hN_meas hN_null
        · intro ω hω
          have hcoord_cont : Continuous fun t : NNReal ↦ Wc t ω i := by
            simpa using
              (continuous_apply i).comp
                ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp (hWc_cont ω))
          simpa [Wc, hω] using hcoord_cont.sub continuous_const
        · intro ω hω
          have hi : W 0 ω i = x i := by
            simpa [Wc, hω] using congrArg (fun y : State ↦ y i) (hWc_start ω)
          simp [B, hi]
      -- Proof comment: adding the deterministic start value back recovers the patched coordinate
      -- of `Wc`.
      have hTranslated :
          IsBrownianMotionStartedAt
            (μ : Measure Ω) (fun t ω ↦ x i + Bc t ω) (x i) := by
        letI : IsProbabilityMeasure (μ : Measure Ω) := by infer_instance
        refine
          { stronglyMeasurable := fun t ↦ (hBc.stronglyMeasurable t).const_add (x i)
            start := ?_
            indepIncrements := ?_
            stationaryIncrements := ?_
            gaussian_marginal := ?_
            continuous_paths := ?_ }
        · have hpreimage : (fun ω ↦ x i + Bc 0 ω) ⁻¹' ({x i} : Set ℝ) = Set.univ := by
            ext ω
            simp [hBc.zero]
          rw [hpreimage]
          simp
        · rw [hasIndepIncrements_iff_nat]
          intro t ht
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            hBc.indepIncrements.nat (t := t) ht
        · intro r s t
          have hleft :
              (fun ω ↦ (x i + Bc ((s + t) + r) ω) - (x i + Bc (t + r) ω)) =
                (fun ω ↦ Bc ((s + t) + r) ω - Bc (t + r) ω) := by
            funext ω
            ring
          have hright :
              (fun ω ↦ (x i + Bc (s + r) ω) - (x i + Bc r ω)) =
                (fun ω ↦ Bc (s + r) ω - Bc r ω) := by
            funext ω
            ring
          simpa [hleft, hright] using hBc.stationaryIncrements r s t
        · intro t ht
          simpa [add_comm] using ProbabilityTheory.gaussianReal_add_const
            (hBc.gaussian_marginal ht) (x i)
        · filter_upwards [hBc.continuous_paths] with ω hω
          simpa [HasAlmostSurelyContinuousPaths, processPath] using continuous_const.add hω
      convert hTranslated using 1
      funext t ω
      by_cases hω : ω ∈ N <;> simp [Wc, B, Bc, hω, sub_eq_add_neg, add_assoc, add_left_comm]
    · have hcoord_eq :
          ∀ i : Fin d,
            (fun ω ↦ fun t : NNReal ↦ W t ω i) =ᵐ[(μ : Measure Ω)]
              (fun ω ↦ fun t : NNReal ↦ Wc t ω i) := by
        intro i
        filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω
        have hω' : ω ∉ N := by simpa using hω
        funext t
        simp [Wc, hω']
      -- Proof comment: patching on one common null set preserves the independence of the
      -- coordinate-path family.
      exact hW.iIndepFun.congr hcoord_eq
  exact ⟨Wc, hWc_owner, hWc_cont, hWc_start, hWc_eq⟩

/-- Helper for Theorem 25.40: recentering a Brownian vector at its deterministic start and
patching time `0` produces a standard Brownian vector on the same sample space. -/
private theorem brownianVectorStartedAt_zeroPatched_isStandard
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x) :
    IsStandardBrownianMotionVector μ
      (fun t ω ↦ if t = 0 then 0 else W t ω - x) := by
  let Z : VectorProcess := fun t ω ↦ W t ω - x
  let F : Fin d → (NNReal → ℝ) → NNReal → ℝ :=
    fun _ f t ↦ if t = 0 then 0 else f t
  have hZ : IsBrownianMotionVectorStartedAt μ Z 0 := by
    refine
      { isBrownianMotionStartedAt := ?_
        iIndepFun := ?_ }
    · intro i
      -- Proof comment: each coordinate is the recentered scalar Brownian motion started at `0`.
      simpa [Z] using
        brownianStartedAt_sub_const_startedAtZero
          (hB := hW.isBrownianMotionStartedAt i)
    · -- Proof comment: coordinate independence is preserved by deterministic recentering.
      have hF_meas : ∀ i : Fin d, Measurable (fun f : NNReal → ℝ ↦ F i f) := by
        intro i
        refine measurable_pi_lambda _ fun t ↦ ?_
        by_cases ht : t = 0
        · simp [F, ht]
        · simpa [F, ht] using
            (measurable_pi_apply t : Measurable fun f : NNReal → ℝ ↦ f t)
      simpa [Z, F, sub_eq_add_neg] using hW.iIndepFun.comp (fun i ↦ fun f t ↦ f t - x i) <| by
        intro i
        refine measurable_pi_lambda _ fun t ↦ ?_
        exact (measurable_pi_apply t).sub measurable_const
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
    -- Proof comment: each coordinate is the pointwise-zero version of the recentered scalar
    -- Brownian motion started at `0`.
    convert
      pointwiseZeroVersion_isBrownianMotion_startedAtZero
        (μ := μ) (B := fun t ω ↦ Z t ω i) (hB := hZ.isBrownianMotionStartedAt i) using 1
    funext t ω
    by_cases ht : t = 0 <;> simp [Z, ht]
  · -- Proof comment: coordinate independence survives the same measurable patching at time `0`.
    convert hZ.iIndepFun.comp (fun i ↦ F i) hF_meas using 1
    funext i ω t
    by_cases ht : t = 0 <;> simp [F, Z, ht]

/-- Helper for Theorem 25.40: translating a standard real Brownian motion by a deterministic
constant produces Brownian motion started from that constant. -/
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
  · -- Proof comment: stationary increments are unchanged by adding the same constant everywhere.
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
  · -- Proof comment: deterministic translation preserves almost-sure continuity of sample paths.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using continuous_const.add hω

/-- Helper for Theorem 25.40: translating a standard Brownian vector by a deterministic state
produces a Brownian vector started from that state. -/
private theorem translatedStandardBrownianVectorStartedAt
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) (z : State) :
    IsBrownianMotionVectorStartedAt μ (fun t ω ↦ z + W t ω) z := by
  let G : Fin d → (NNReal → ℝ) → (NNReal → ℝ) := fun i f t ↦ z i + f t
  have hG_meas : ∀ i : Fin d, Measurable (G i) := by
    intro i
    refine measurable_pi_lambda _ ?_
    intro t
    exact measurable_const.add (measurable_pi_apply t)
  refine
    { isBrownianMotionStartedAt := fun i ↦ by
        -- Proof comment: each coordinate is the deterministic translation of a scalar standard
        -- Brownian motion.
        have hcoord : IsBrownianMotion μ (fun t ω ↦ W t ω i) := hW.isBrownianMotion i
        simpa [G] using translatedBrownianMotionStartedAt (μ := μ) hcoord (z i)
      iIndepFun := by
        -- Proof comment: coordinate independence survives the same deterministic translation on
        -- path space.
        simpa [G] using hW.iIndepFun.comp (fun i ↦ G i) hG_meas }

/-- Helper for Theorem 25.40: subtracting a deterministic state from a scalar Brownian motion
started at `x` shifts the deterministic start to `x - y` without changing the Brownian
increments. -/
private theorem brownianStartedAt_sub_const_startedAtSub
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x y : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ B t ω - y) (x - y) := by
  refine
    { stronglyMeasurable := ?_
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: subtracting a deterministic constant preserves measurability of each slice.
    intro t
    exact (hB.stronglyMeasurable t).sub stronglyMeasurable_const
  · -- Proof comment: the shifted start event is the original start event rewritten by arithmetic.
    have hpreimage :
        (fun ω ↦ B 0 ω - y) ⁻¹' ({x - y} : Set ℝ) = B 0 ⁻¹' ({x} : Set ℝ) := by
      ext ω
      constructor
      · intro hω
        change B 0 ω - y = x - y at hω
        change B 0 ω = x
        linarith
      · intro hω
        have hxω : B 0 ω = x := by
          simpa using hω
        change B 0 ω - y = x - y
        linarith
    rw [hpreimage]
    exact hB.start
  · -- Proof comment: subtracting the same deterministic state leaves every increment unchanged.
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB.indepIncrements n t ht
  · -- Proof comment: stationarity is the same cancellation identity on both compared increments.
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: the time-`t` marginal is the original Gaussian translated by `-y`.
    simpa using ProbabilityTheory.gaussianReal_sub_const (hB.gaussian_marginal ht) y
  · -- Proof comment: path continuity is stable under subtraction of a deterministic constant.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Theorem 25.40: subtracting a deterministic center `y` from a Brownian vector
started at `x` produces a Brownian vector started at `x - y`. -/
private theorem brownianVectorStartedAt_sub_const_startedAtSub
    {μ : Measure Ω} {W : VectorProcess} {x y : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x) :
    IsBrownianMotionVectorStartedAt μ (fun t ω ↦ W t ω - y) (x - y) := by
  let F : Fin d → (NNReal → ℝ) → NNReal → ℝ := fun i f t ↦ f t - y i
  have hF_meas : ∀ i : Fin d, Measurable (F i) := by
    intro i
    refine measurable_pi_lambda _ fun t ↦ ?_
    exact (measurable_pi_apply t).sub measurable_const
  refine
    { isBrownianMotionStartedAt := ?_
      iIndepFun := ?_ }
  · intro i
    -- Proof comment: each coordinate is the scalar shifted Brownian motion started at `x i - y i`.
    simpa [F] using
      brownianStartedAt_sub_const_startedAtSub
        (μ := μ) (B := fun t ω ↦ W t ω i) (x := x i) (y := y i)
        (hW.isBrownianMotionStartedAt i)
  · -- Proof comment: coordinate independence survives measurable deterministic recentering on path
    -- space.
    simpa [F] using hW.iIndepFun.comp (fun i ↦ F i) hF_meas

/-- Helper for Theorem 25.40: Brownian motion exits any open set with compact closure almost
surely in finite time under one fixed starting law. -/
private theorem ae_exitTime_lt_top_of_isCompact_closure_startedAt
    [NeZero d]
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {G : Set State} {x : State}
    (hx : x ∈ G)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hG : IsOpen G) (hGcpt : IsCompact (closure G)) :
    ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Gᶜ 0 ω < ⊤ := by
  let i : Fin d := 0
  obtain ⟨R, hRsubset⟩ := hGcpt.isBounded.subset_closedBall (0 : State)
  have hxClosure : x ∈ closure G := subset_closure hx
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hRsubset hxClosure
  have hxi_abs : |x i| ≤ R := by
    calc
      |x i| = ‖x i‖ := by simp
      _ ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
      _ ≤ R := hxR
  let a : ℝ := -(R + 1) - x i
  let b : ℝ := R + 1 - x i
  have ha : a < 0 := by
    -- Proof comment: the recentered lower level stays strictly negative because `x` lies in the
    -- ambient compact ball.
    have hxi_lower : -R ≤ x i := (abs_le.mp hxi_abs).1
    dsimp [a]
    linarith
  have hb : 0 < b := by
    -- Proof comment: the recentered upper level stays strictly positive for the same reason.
    have hxi_upper : x i ≤ R := (abs_le.mp hxi_abs).2
    dsimp [b]
    linarith
  let B0 : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else W t ω i - x i
  have hB0 : IsBrownianMotion (μ : Measure Ω) B0 := by
    let Z : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    have hZ : IsBrownianMotionStartedAt (μ : Measure Ω) Z 0 := by
      -- Proof comment: recenter the chosen coordinate so the scalar motion starts at `0`.
      simpa [Z] using
        brownianStartedAt_sub_const_startedAtZero
          ((hW.isBrownianMotionStartedAt i))
    -- Proof comment: patch the time-zero value to the literal constant `0` to match the standard
    -- Brownian-motion owner theorem from Chapter 21.
    simpa [B0, Z] using
      pointwiseZeroVersion_isBrownianMotion_startedAtZero
        (μ := (μ : Measure Ω)) (B := Z) hZ
  have hτscalar :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter B0 ({a, b} : Set ℝ) 0 ω ≠ ⊤ :=
    brownianMotion_twoSidedHittingTime_ae_ne_top (hB := hB0) (a := a) (b := b) ha hb
  filter_upwards [hτscalar] with ω hω
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hω
  rcases hω with ⟨t, ht_nonneg, hτ_mem⟩
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    have hB0_zero : B0 t ω = 0 := by
      simp [B0, ht0]
    rcases hτ_mem with hτa | hτb
    · have : a = 0 := by rw [← hτa]; exact hB0_zero
      linarith
    · have : b = 0 := by rw [← hτb]; exact hB0_zero
      linarith
  have hcoord_hit :
      W t ω i = -(R + 1) ∨ W t ω i = R + 1 := by
    rcases hτ_mem with hτa | hτb
    · left
      have hEq : W t ω i - x i = a := by
        simpa [B0, ht_ne_zero] using hτa
      dsimp [a] at hEq
      linarith
    · right
      have hEq : W t ω i - x i = b := by
        simpa [B0, ht_ne_zero] using hτb
      dsimp [b] at hEq
      linarith
  have hcoord_abs : |W t ω i| = R + 1 := by
    rcases hcoord_hit with hleft | hright
    · have hRp1_nonneg : 0 ≤ R + 1 := by linarith [hxR]
      rw [hleft, abs_neg, abs_of_nonneg hRp1_nonneg]
    · have hRp1_nonneg : 0 ≤ R + 1 := by linarith [hxR]
      rw [hright, abs_of_nonneg hRp1_nonneg]
  have hnot_closedBall : W t ω ∉ Metric.closedBall (0 : State) R := by
    intro hball
    have hnorm_le : ‖W t ω‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hcoord_le : R + 1 ≤ ‖W t ω‖ := by
      calc
        R + 1 = |W t ω i| := hcoord_abs.symm
        _ = ‖W t ω i‖ := by simp
        _ ≤ ‖W t ω‖ := by simpa using PiLp.norm_apply_le (W t ω) i
    linarith
  have hWt_mem : W t ω ∈ Gᶜ := by
    -- Proof comment: a point whose chosen coordinate has magnitude `R + 1` lies outside the
    -- containing closed ball, hence outside `G`.
    intro hWtG
    exact hnot_closedBall (hRsubset (subset_closure hWtG))
  have hτ_le : hittingAfter W Gᶜ 0 ω ≤ t := by
    -- Proof comment: once the path reaches `Gᶜ` at time `t`, the exit time from `G` is no later
    -- than `t`.
    exact
      hittingAfter_le_of_mem
        (u := W) (s := Gᶜ) (n := (0 : NNReal)) (i := t) (ω := ω) ht_nonneg hWt_mem
  exact lt_of_le_of_lt hτ_le (by simpa using (WithTop.coe_lt_top t))

/-- Helper for Theorem 25.40: the open concentric annulus between radii `r` and `R` around `y`.
-/
private def concentricAnnulus (y : State) (r R : ℝ) : Set State :=
  Metric.ball y R \ Metric.closedBall y r

/-- Helper for Theorem 25.40: the concentric annulus is open because it is an open ball with the
closed inner ball removed. -/
private theorem concentricAnnulus_isOpen (y : State) (r R : ℝ) :
    IsOpen (concentricAnnulus y r R) := by
  -- Proof comment: subtracting the closed inner ball from the open outer ball preserves openness.
  simpa [concentricAnnulus] using Metric.isOpen_ball.sdiff Metric.isClosed_closedBall

/-- Helper for Theorem 25.40: every inner-sphere point is approximated from within the annulus by
moving a short distance radially outward. -/
private theorem innerSphere_subset_closure_concentricAnnulus
    (y x : State) {r R : ℝ} (hr : 0 < r) (hR : r < R)
    (hx : x ∈ Metric.sphere y r) :
    x ∈ closure (concentricAnnulus y r R) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) ((R - r) / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · linarith
    · linarith
  have hδlt : r + δ < R := by
    have hδle : δ ≤ (R - r) / 2 := min_le_right _ _
    linarith
  have hδε : δ < ε := by
    have hδle : δ ≤ ε / 2 := min_le_left _ _
    linarith
  let z : State := x + (δ / r) • (x - y)
  refine ⟨z, ?_, ?_⟩
  · have hnorm : ‖x - y‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_eq_add_neg] using hx
    have hzsub : z - y = (1 + δ / r) • (x - y) := by
      ext i
      simp [z, sub_eq_add_neg]
      ring_nf
    have hzdist : dist z y = r + δ := by
      have hrne : r ≠ 0 := hr.ne'
      have hfac : 0 ≤ 1 + δ / r := by positivity
      calc
        dist z y = ‖z - y‖ := dist_eq_norm _ _
        _ = ‖(1 + δ / r) • (x - y)‖ := by rw [hzsub]
        _ = |1 + δ / r| * ‖x - y‖ := norm_smul _ _
        _ = (1 + δ / r) * ‖x - y‖ := by simp [abs_of_nonneg hfac]
        _ = (1 + δ / r) * r := by rw [hnorm]
        _ = r + δ := by field_simp [hrne]
    have hzr : r < dist z y := by simpa [hzdist]
    have hzR : dist z y < R := by simpa [hzdist] using hδlt
    -- Proof comment: the perturbed point has radius strictly between `r` and `R`, so it lies in
    -- the annulus.
    simp [concentricAnnulus, Metric.mem_ball, Metric.mem_closedBall, hzR, not_le_of_gt hzr]
  · have hnorm : ‖x - y‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_eq_add_neg] using hx
    have hzdistx : dist z x = δ := by
      have hrne : r ≠ 0 := hr.ne'
      have hfac : 0 ≤ δ / r := by positivity
      calc
        dist z x = ‖z - x‖ := dist_eq_norm _ _
        _ = ‖(δ / r) • (x - y)‖ := by
              simp [z, sub_eq_add_neg]
        _ = |δ / r| * ‖x - y‖ := norm_smul _ _
        _ = (δ / r) * ‖x - y‖ := by simp [abs_of_nonneg hfac]
        _ = (δ / r) * r := by rw [hnorm]
        _ = δ := by field_simp [hrne]
    have hzdistx' : dist x z = δ := by
      simpa [dist_comm] using hzdistx
    -- Proof comment: the same radial perturbation stays within the requested `ε`-ball around `x`.
    exact lt_of_eq_of_lt hzdistx' hδε

/-- Helper for Theorem 25.40: the closure of the open annulus is the closed annulus obtained by
adding back the two bounding spheres. -/
private theorem concentricAnnulus_closure_eq
    (y : State) {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    closure (concentricAnnulus y r R) = Metric.closedBall y R \ Metric.ball y r := by
  apply subset_antisymm
  · refine closure_minimal ?_ ?_
    · intro x hx
      refine ⟨Metric.ball_subset_closedBall hx.1, ?_⟩
      intro hxball
      exact hx.2 (Metric.ball_subset_closedBall hxball)
    · -- Proof comment: the target closed annulus is closed because it is a closed ball minus an
      -- open ball.
      simpa using Metric.isClosed_closedBall.sdiff Metric.isOpen_ball
  · intro x hx
    rcases hx with ⟨hxR, hxr⟩
    by_cases hEq : dist x y = r
    · -- Proof comment: inner-sphere points were isolated in the radial approximation lemma.
      exact innerSphere_subset_closure_concentricAnnulus y x hr hR (by
        simpa [Metric.mem_sphere] using hEq)
    · have hxnotclosed : x ∉ Metric.closedBall y r := by
        intro hxclosed
        have hle : dist x y ≤ r := by simpa [Metric.mem_closedBall] using hxclosed
        have hlt : dist x y < r := lt_of_le_of_ne hle hEq
        exact hxr hlt
      have hxCore : x ∈ closure (Metric.ball y R) \ closure (Metric.closedBall y r) := by
        refine ⟨?_, ?_⟩
        · simpa [closure_ball y (by linarith [hr, hR])] using hxR
        · simpa [Metric.isClosed_closedBall.closure_eq] using hxnotclosed
      -- Proof comment: every closed-annulus point off the inner sphere is already covered by the
      -- general `closure_diff` inclusion.
      exact closure_diff hxCore

/-- Helper for Theorem 25.40: the annulus frontier is exactly the disjoint union of the inner and
outer spheres. -/
private theorem concentricAnnulusFrontier_eq
    (y : State) {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    frontier (concentricAnnulus y r R) = Metric.sphere y r ∪ Metric.sphere y R := by
  have hopen : IsOpen (concentricAnnulus y r R) := concentricAnnulus_isOpen y r R
  rw [frontier, concentricAnnulus_closure_eq y hr hR, hopen.interior_eq]
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxmem, hxnot⟩
    have hxRle : dist x y ≤ R := by simpa [Metric.mem_closedBall] using hxmem.1
    have hxrle : r ≤ dist x y := le_of_not_gt hxmem.2
    by_cases hEqR : dist x y = R
    · exact Or.inr (by simpa [Metric.mem_sphere] using hEqR)
    · by_cases hEqr : dist x y = r
      · exact Or.inl (by simpa [Metric.mem_sphere] using hEqr)
      · have hrlt : r < dist x y := lt_of_le_of_ne hxrle (Ne.symm hEqr)
        have hRlt : dist x y < R := lt_of_le_of_ne hxRle hEqR
        -- Proof comment: away from the two sphere radii, a closed-annulus point lies in the open
        -- annulus itself, contradicting frontier membership.
        exact (hxnot (by
          simp [concentricAnnulus, Metric.mem_ball, Metric.mem_closedBall, hRlt,
            not_le_of_gt hrlt])).elim
  · intro hx
    rcases hx with hx | hx
    · refine ⟨?_, ?_⟩
      · have hxr : dist x y = r := by simpa [Metric.mem_sphere] using hx
        simp [Metric.mem_closedBall, Metric.mem_ball, hxr, le_of_lt hR]
      · have hxr : dist x y = r := by simpa [Metric.mem_sphere] using hx
        simp [concentricAnnulus, Metric.mem_ball, Metric.mem_closedBall, hxr]
    · refine ⟨?_, ?_⟩
      · have hxR : dist x y = R := by simpa [Metric.mem_sphere] using hx
        simp [Metric.mem_closedBall, Metric.mem_ball, hxR, le_of_lt hR]
      · have hxR : dist x y = R := by simpa [Metric.mem_sphere] using hx
        simp [concentricAnnulus, Metric.mem_ball, Metric.mem_closedBall, hxR]

/-- Helper for Theorem 25.40: the closure of a bounded concentric annulus is compact because it is
contained in the outer closed ball. -/
private theorem isCompact_closure_concentricAnnulus
    (y : State) {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    IsCompact (closure (concentricAnnulus y r R)) := by
  -- Proof comment: rewrite the closure as a closed subset of the outer closed ball and inherit
  -- compactness from `isCompact_closedBall`.
  rw [concentricAnnulus_closure_eq y hr hR]
  refine IsCompact.of_isClosed_subset (isCompact_closedBall y R)
    (Metric.isClosed_closedBall.sdiff Metric.isOpen_ball) ?_
  intro z hz
  exact hz.1

/-- Helper for Theorem 25.40: if a continuous path stays in `G` at all earlier times and is in
`Gᶜ` at time `t > 0`, then the time-`t` value lies on `frontier G`. -/
private theorem memFrontierOfContinuousPathOfLeftMem
    {G : Set State} {W : VectorProcess} {ω : Ω} {t : NNReal}
    (hcont : Continuous fun s : NNReal ↦ W s ω)
    (ht_pos : 0 < t) (ht_mem : W t ω ∈ Gᶜ)
    (hleft : ∀ s : NNReal, s < t → W s ω ∈ G) :
    W t ω ∈ frontier G := by
  have hmemClosure : W t ω ∈ closure G := by
    rw [mem_closure_iff]
    intro o ho hWt
    have hPreimage : {s : NNReal | W s ω ∈ o} ∈ 𝓝 t := by
      -- Proof comment: continuity of the path at time `t` pulls a neighborhood of `W t ω` back
      -- to a neighborhood of `t`.
      exact hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds ho hWt)
    rcases mem_nhds_iff.mp hPreimage with ⟨u, hu_subset, hu_open, ht_mem_u⟩
    have ht_closure : t ∈ closure (Set.Iio t) := by
      -- Proof comment: because `t > 0`, times strictly below `t` accumulate at `t` from the
      -- left.
      have hclosureIio : closure (Set.Iio t : Set NNReal) = Set.Iic t :=
        closure_Iio' ⟨0, ht_pos⟩
      rw [hclosureIio]
      simp
    rcases (mem_closure_iff.mp ht_closure) u hu_open ht_mem_u with ⟨s, hs_mem_u, hs_lt_t⟩
    have hWs_mem_o : W s ω ∈ o := hu_subset hs_mem_u
    have hWs_mem_G : W s ω ∈ G := hleft s hs_lt_t
    -- Proof comment: every neighborhood of `W t ω` contains an earlier path value still inside
    -- `G`, so `W t ω` belongs to `closure G`.
    exact ⟨W s ω, hWs_mem_o, hWs_mem_G⟩
  -- Proof comment: combine the closure information from the left with the actual time-`t`
  -- membership in `Gᶜ`.
  rw [frontier_eq_closure_inter_closure]
  exact ⟨hmemClosure, subset_closure ht_mem⟩

/-- Helper for Theorem 25.40: a continuous-path process with measurable exit data admits a
measurable frontier-valued exit map by using a fixed frontier point on the `τ = ⊤` branch. -/
private theorem existsMeasurableFrontierExitValue_ofContinuousPaths
    {G : Set State} {W : VectorProcess}
    (hFrontier : (frontier G).Nonempty)
    (hG : IsOpen G)
    (hτmeas : Measurable (hittingAfter W Gᶜ 0))
    (hStoppedMeas : Measurable (stoppedValue W (hittingAfter W Gᶜ 0)))
    (hcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hStart : ∀ ω : Ω, W 0 ω ∈ G) :
    ∃ exitValue : Ω → frontier G, Measurable exitValue ∧
      (∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω) := by
  rcases hFrontier with ⟨z₀, hz₀⟩
  let rawExit : Ω → State :=
    {ω | hittingAfter W Gᶜ 0 ω < ⊤}.piecewise
      (stoppedValue W (hittingAfter W Gᶜ 0))
      (fun _ ↦ z₀)
  have hFiniteMeas :
      MeasurableSet {ω : Ω | hittingAfter W Gᶜ 0 ω < (⊤ : WithTop NNReal)} :=
    hτmeas measurableSet_Iio
  have hStoppedFrontier :
      ∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        stoppedValue W (hittingAfter W Gᶜ 0) ω ∈ frontier G := by
    intro ω hω
    have hτ_ne_top : hittingAfter W Gᶜ 0 ω ≠ ⊤ := ne_of_lt hω
    let hitSet : Set NNReal := {t : NNReal | W t ω ∈ Gᶜ}
    have hHitExists : ∃ t : NNReal, W t ω ∈ Gᶜ := by
      -- Proof comment: finite exit time gives an actual time when the path reaches `Gᶜ`.
      simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hτ_ne_top
      rcases hτ_ne_top with ⟨t, _, ht_mem⟩
      exact ⟨t, ht_mem⟩
    have hHitNonempty : hitSet.Nonempty := by
      rcases hHitExists with ⟨t, ht_mem⟩
      exact ⟨t, ht_mem⟩
    have hHitClosed : IsClosed hitSet := by
      -- Proof comment: continuity of the path turns the closed target set `Gᶜ` into a closed
      -- hitting-time set.
      have hClosedGc : IsClosed (Gᶜ : Set State) := isClosed_compl_iff.mpr hG
      change IsClosed ((fun t : NNReal ↦ W t ω) ⁻¹' (Gᶜ : Set State))
      exact hClosedGc.preimage (hcont ω)
    have hHitBddBelow : BddBelow hitSet := ⟨0, fun _ _ ↦ bot_le⟩
    have hsInf_mem : sInf hitSet ∈ hitSet :=
      hHitClosed.csInf_mem hHitNonempty hHitBddBelow
    have hτ_eq : (hittingAfter W Gᶜ 0 ω).untopA = sInf hitSet := by
      -- Proof comment: over `NNReal`, the lower-bound side condition in `hittingAfter` is
      -- automatic, so the clock is the infimum of the raw hit set.
      rw [hittingAfter]
      rw [if_pos]
      · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ Gᶜ} = hitSet by
            ext t
            simp [hitSet]]
        simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
      · rcases hHitExists with ⟨t, ht_mem⟩
        exact ⟨t, bot_le, ht_mem⟩
    have hHitMem :
        W (hittingAfter W Gᶜ 0 ω).untopA ω ∈ Gᶜ := by
      simpa [hitSet, hτ_eq] using hsInf_mem
    have hτuntop_ne_zero : (hittingAfter W Gᶜ 0 ω).untopA ≠ 0 := by
      intro hτ_zero
      have hZeroMem : W 0 ω ∈ Gᶜ := by
        simpa [hτ_zero] using hHitMem
      exact hZeroMem (hStart ω)
    have hτuntop_pos : 0 < (hittingAfter W Gᶜ 0 ω).untopA := by
      exact lt_of_le_of_ne bot_le hτuntop_ne_zero.symm
    have hLeft :
        ∀ s : NNReal, s < (hittingAfter W Gᶜ 0 ω).untopA → W s ω ∈ G := by
      intro s hs
      have hs_hit : (s : WithTop NNReal) < hittingAfter W Gᶜ 0 ω := by
        lift hittingAfter W Gᶜ 0 ω to NNReal using hτ_ne_top with t ht
        have hτ_idx : (hittingAfter W Gᶜ 0 ω).untopA = t := by
          rw [← ht]
          simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := t))
        have hs_t : s < t := by
          simpa [hτ_idx] using hs
        have hs_coe : (s : WithTop NNReal) < (t : WithTop NNReal) := by
          exact_mod_cast hs_t
        exact ht ▸ hs_coe
      have hNotGc :
          W s ω ∉ Gᶜ :=
        notMem_of_lt_hittingAfter
          (u := W) (s := Gᶜ) (n := (0 : NNReal)) (ω := ω) (k := s) hs_hit (by simp)
      simpa using hNotGc
    -- Proof comment: the path stays in `G` just before the first exit and lands in `Gᶜ` at the
    -- exit time, so continuity forces the stopped value onto the frontier.
    simpa [stoppedValue, hτ_ne_top] using
      memFrontierOfContinuousPathOfLeftMem
        (W := W) (G := G) (ω := ω) (t := (hittingAfter W Gᶜ 0 ω).untopA)
        (hcont ω) hτuntop_pos hHitMem hLeft
  have hRawFrontier : ∀ ω : Ω, rawExit ω ∈ frontier G := by
    intro ω
    by_cases hω_fin : hittingAfter W Gᶜ 0 ω < ⊤
    · simpa [rawExit, hω_fin] using hStoppedFrontier ω hω_fin
    · simp [rawExit, hω_fin, hz₀]
  let exitValue : Ω → frontier G := fun ω ↦ ⟨rawExit ω, hRawFrontier ω⟩
  have hRawMeas : Measurable rawExit := by
    exact hStoppedMeas.piecewise hFiniteMeas measurable_const
  have hExitMeas : Measurable (fun ω ↦ (⟨rawExit ω, hRawFrontier ω⟩ : frontier G)) :=
    hRawMeas.codRestrict hRawFrontier
  refine ⟨exitValue, hExitMeas, ?_⟩
  intro ω hω
  -- Proof comment: on the finite-exit branch the packaged frontier value is exactly the stopped
  -- process value.
  simp [exitValue, rawExit, hω]

/-- Helper for Theorem 25.40: the centered radial Dirichlet profile on the annulus
`concentricAnnulus 0 ρ R`, written in a Lean-friendly dimension split. -/
private def centeredAnnulusProfile (ρ R : ℝ) : State → ℝ :=
  fun z ↦
    if d = 1 then
      (R - ‖z‖) / (R - ρ)
    else if d = 2 then
      (Real.log R - Real.log ‖z‖) / (Real.log R - Real.log ρ)
    else
      ((ρ / ‖z‖) ^ (d - 2) - (ρ / R) ^ (d - 2)) / (1 - (ρ / R) ^ (d - 2))

/-- Helper for Theorem 25.40: points in the closure of the centered annulus stay at radius at
least `ρ`. -/
private theorem radius_le_norm_of_mem_closure_centeredAnnulus
    {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) {z : State}
    (hz : z ∈ closure (concentricAnnulus (0 : State) ρ R)) :
    ρ ≤ ‖z‖ := by
  have hzClosed :
      z ∈ Metric.closedBall (0 : State) R \ Metric.ball (0 : State) ρ := by
    simpa [concentricAnnulus_closure_eq (d := d) (y := (0 : State)) hr hR] using hz
  have hzNotBall : z ∉ Metric.ball (0 : State) ρ := hzClosed.2
  have hnot : ¬ dist z (0 : State) < ρ := by
    simpa [Metric.mem_ball] using hzNotBall
  -- Proof comment: closure points outside the open inner ball still satisfy the annulus lower
  -- radius bound.
  simpa [dist_eq_norm] using le_of_not_gt hnot

/-- Helper for Theorem 25.40: the closed annulus stays uniformly away from the singularity at
`0`. -/
private theorem norm_ne_zero_of_mem_closure_centeredAnnulus
    {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) {z : State}
    (hz : z ∈ closure (concentricAnnulus (0 : State) ρ R)) :
    ‖z‖ ≠ 0 := by
  have hρle : ρ ≤ ‖z‖ := radius_le_norm_of_mem_closure_centeredAnnulus (d := d) hr hR hz
  -- Proof comment: the inner-radius bound upgrades immediately to a strict positive norm.
  exact ne_of_gt (lt_of_lt_of_le hr hρle)

/-- Helper for Theorem 25.40: the centered annulus profile is continuous on the closed annulus,
because that closure avoids the singularity at `0`. -/
private theorem centeredAnnulusProfile_continuousOnClosure
    [NeZero d] {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) :
    ContinuousOn (centeredAnnulusProfile (d := d) ρ R)
      (closure (concentricAnnulus (0 : State) ρ R)) := by
  intro z hz
  have hnorm_ne : ‖z‖ ≠ 0 :=
    norm_ne_zero_of_mem_closure_centeredAnnulus (d := d) hr hR hz
  by_cases h1 : d = 1
  · -- Proof comment: in dimension `1`, the profile is an affine function of the norm.
    have hconstR : ContinuousAt (fun _ : State ↦ (R : ℝ)) z := continuousAt_const
    have hbranch :
        ContinuousWithinAt (fun x : State ↦ (R - ‖x‖) / (R - ρ))
          (closure (concentricAnnulus (0 : State) ρ R)) z :=
      ((hconstR.sub continuous_norm.continuousAt).div_const (R - ρ)).continuousWithinAt
    convert hbranch using 1
    ext x
    simp [centeredAnnulusProfile, h1]
  · by_cases h2 : d = 2
    · -- Proof comment: on the closed annulus, `‖z‖ ≠ 0`, so the logarithmic branch is continuous.
      have hlog :
          ContinuousAt (fun w : State ↦ Real.log ‖w‖) z := by
        exact (Real.continuousAt_log hnorm_ne).comp continuous_norm.continuousAt
      have hconstLogR : ContinuousAt (fun _ : State ↦ Real.log R) z := continuousAt_const
      have hbranch :
          ContinuousWithinAt
            (fun x : State ↦ (Real.log R - Real.log ‖x‖) / (Real.log R - Real.log ρ))
            (closure (concentricAnnulus (0 : State) ρ R)) z :=
        ((hconstLogR.sub hlog).div_const (Real.log R - Real.log ρ)).continuousWithinAt
      convert hbranch using 1
      ext x
      simp [centeredAnnulusProfile, h2]
    · -- Proof comment: in dimensions `d > 2`, only the reciprocal-radius term needs the
      -- annulus lower bound to keep division by `‖z‖` continuous.
      have hratio :
          ContinuousAt (fun w : State ↦ ρ / ‖w‖) z := by
        exact continuousAt_const.div continuous_norm.continuousAt hnorm_ne
      have hpow :
          ContinuousAt (fun w : State ↦ (ρ / ‖w‖) ^ (d - 2)) z := hratio.pow (d - 2)
      have hconstOuter : ContinuousAt (fun _ : State ↦ (ρ / R) ^ (d - 2 : ℕ)) z := continuousAt_const
      have hbranch :
          ContinuousWithinAt
            (fun x : State ↦
              ((ρ / ‖x‖) ^ (d - 2) - (ρ / R) ^ (d - 2)) / (1 - (ρ / R) ^ (d - 2)))
            (closure (concentricAnnulus (0 : State) ρ R)) z :=
        ((hpow.sub hconstOuter).div_const (1 - (ρ / R) ^ (d - 2))).continuousWithinAt
      convert hbranch using 1
      ext x
      simp [centeredAnnulusProfile, h1, h2]

/-- Helper for Theorem 25.40: the centered annulus profile takes the boundary value `1` on the
inner sphere. -/
private theorem centeredAnnulusProfile_eq_one_of_mem_innerSphere
    [NeZero d] {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) {z : State}
    (hz : z ∈ Metric.sphere (0 : State) ρ) :
    centeredAnnulusProfile (d := d) ρ R z = 1 := by
  have hnorm : ‖z‖ = ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  by_cases h1 : d = 1
  · -- Proof comment: in dimension `1`, the affine radius profile is normalized by the same
    -- nonzero denominator on both numerator and denominator.
    have hden_ne : R - ρ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hR)
    simpa [centeredAnnulusProfile, h1, hnorm] using div_self hden_ne
  · by_cases h2 : d = 2
    · -- Proof comment: in dimension `2`, the logarithmic numerator and denominator coincide on
      -- the inner sphere, and strict monotonicity of `log` keeps the denominator nonzero.
      have hlog_lt : Real.log ρ < Real.log R := Real.log_lt_log hr hR
      have hden_ne : Real.log R - Real.log ρ ≠ 0 :=
        sub_ne_zero.mpr (ne_of_gt hlog_lt)
      simpa [centeredAnnulusProfile, h2, hnorm] using div_self hden_ne
    · -- Proof comment: in dimensions `d > 2`, the positive-exponent profile is normalized so the
      -- inner-sphere ratio is exactly `1`.
      simp [centeredAnnulusProfile, h1, h2]
      have hd_exp_pos : 0 < d - 2 := by
        have hd0 : d ≠ 0 := NeZero.ne d
        omega
      have hbase_lt : ρ / R < 1 := by
        have hRpos : 0 < R := by linarith
        exact (div_lt_one hRpos).2 hR
      have hbase_nonneg : 0 ≤ ρ / R := div_nonneg hr.le (by linarith [hR])
      have hpow_lt_one : (ρ / R) ^ (d - 2) < 1 :=
        pow_lt_one₀ hbase_nonneg hbase_lt hd_exp_pos.ne'
      have hden_ne : 1 - (ρ / R) ^ (d - 2) ≠ 0 :=
        sub_ne_zero.mpr (ne_of_lt hpow_lt_one).symm
      have hratio : ρ / ‖z‖ = 1 := by simp [hnorm, hr.ne']
      rw [hratio]
      simp [hden_ne]

/-- Helper for Theorem 25.40: the centered annulus profile takes the boundary value `0` on the
outer sphere. -/
private theorem centeredAnnulusProfile_eq_zero_of_mem_outerSphere
    [NeZero d] {ρ R : ℝ} {z : State}
    (hz : z ∈ Metric.sphere (0 : State) R) :
    centeredAnnulusProfile (d := d) ρ R z = 0 := by
  have hnorm : ‖z‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  by_cases h1 : d = 1
  · -- Proof comment: in dimension `1`, the affine profile vanishes because its numerator is
    -- `R - R`.
    simp [centeredAnnulusProfile, h1, hnorm]
  · by_cases h2 : d = 2
    · -- Proof comment: in dimension `2`, the logarithmic numerator vanishes on the outer sphere.
      simp [centeredAnnulusProfile, h2, hnorm]
    · -- Proof comment: in dimensions `d > 2`, the two positive-exponent terms coincide on the
      -- outer sphere, so the numerator is zero.
      simp [centeredAnnulusProfile, h2, hnorm]

/-- Helper for Theorem 25.40: the centered annulus profile matches the `1/0` boundary indicator
on the frontier of the centered annulus. -/
private theorem centeredAnnulusProfile_boundaryIndicator
    [NeZero d] {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R)
    (z : frontier (concentricAnnulus (0 : State) ρ R)) :
    centeredAnnulusProfile (d := d) ρ R z =
      if (z : State) ∈ Metric.sphere (0 : State) ρ then 1 else 0 := by
  have hz : (z : State) ∈ Metric.sphere (0 : State) ρ ∪ Metric.sphere (0 : State) R := by
    simpa [concentricAnnulusFrontier_eq (d := d) (y := (0 : State)) hr hR] using z.property
  rcases hz with hz | hz
  · -- Proof comment: on the inner sphere, the preceding normalization lemma gives the boundary
    -- value `1`.
    rw [if_pos hz]
    exact centeredAnnulusProfile_eq_one_of_mem_innerSphere (d := d) hr hR hz
  · have hz_not_inner : (z : State) ∉ Metric.sphere (0 : State) ρ := by
      intro hz_inner
      have hdist_inner : dist (z : State) 0 = ρ := by
        simpa [Metric.mem_sphere] using hz_inner
      have hdist_outer : dist (z : State) 0 = R := by
        simpa [Metric.mem_sphere] using hz
      linarith
    -- Proof comment: on the outer sphere, the same profile vanishes and the indicator switches to
    -- `0`.
    rw [if_neg hz_not_inner]
    exact centeredAnnulusProfile_eq_zero_of_mem_outerSphere (d := d) hz

local notation "State1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Theorem 25.40: the Euclidean norm on `ℝ¹` is the absolute value of the unique
coordinate. -/
private theorem norm_eq_abs_firstCoordinate_state1 (w : State1) :
    ‖w‖ = |w 0| := by
  have hw_single : w = EuclideanSpace.single (𝕜 := ℝ) (ι := Fin 1) (0 : Fin 1) (w 0) := by
    ext i
    fin_cases i
    simp
  have hsingle_norm :
      ‖EuclideanSpace.single (𝕜 := ℝ) (ι := Fin 1) (0 : Fin 1) (w 0)‖ = ‖w 0‖ := by
    simpa using
      (EuclideanSpace.norm_single (𝕜 := ℝ) (ι := Fin 1) (i := (0 : Fin 1)) (a := w 0))
  have hnorm_eq :
      ‖w‖ = ‖EuclideanSpace.single (𝕜 := ℝ) (ι := Fin 1) (0 : Fin 1) (w 0)‖ :=
    congrArg norm hw_single
  calc
    ‖w‖ = ‖EuclideanSpace.single (𝕜 := ℝ) (ι := Fin 1) (0 : Fin 1) (w 0)‖ := hnorm_eq
    _ = ‖w 0‖ := hsingle_norm
    _ = |w 0| := by simp

/-- Helper for Theorem 25.40: on `ℝ¹`, the unique coordinate projection is harmonic because its
second derivative vanishes identically. -/
private theorem firstCoordinate_harmonicAt_state1 (z : State1) :
    InnerProductSpace.HarmonicAt (fun w : State1 ↦ w 0) z := by
  let p : State1 →L[ℝ] ℝ :=
    show State1 →L[ℝ] ℝ from EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0
  have hp : (fun w : State1 ↦ w 0) = p := by
    funext w
    simp [p]
  rw [hp]
  refine ⟨p.contDiff.contDiffAt, ?_⟩
  have hiter2 : iteratedFDeriv ℝ 2 p = 0 := by
    have hfd : fderiv ℝ (⇑p) = fun _ : State1 ↦ p := by
      funext x
      exact ContinuousLinearMap.fderiv (f := p) (x := x)
    funext x
    ext m
    rw [iteratedFDeriv_two_apply, hfd, fderiv_const_apply]
    simp
  filter_upwards with x
  -- Proof comment: a linear functional has zero second derivative everywhere, so its Laplacian
  -- vanishes pointwise.
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hiter2]
  simp

/-- Helper for Theorem 25.40: on `ℝ¹`, the norm is harmonic away from `0` because locally it is
either the identity or its negative on the unique coordinate. -/
private theorem norm_harmonicAt_state1_of_ne_zero {z : State1} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (fun w : State1 ↦ ‖w‖) z := by
  let p : State1 →L[ℝ] ℝ :=
    show State1 →L[ℝ] ℝ from EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0
  have hz_coord_ne : z 0 ≠ 0 := by
    intro hz0
    apply hz
    ext i
    fin_cases i
    simp [hz0]
  by_cases hzpos : 0 < z 0
  · have hpos : {w : State1 | 0 < w 0} ∈ 𝓝 z :=
      IsOpen.mem_nhds (isOpen_lt continuous_const p.continuous) hzpos
    have hlocal : (fun w : State1 ↦ ‖w‖) =ᶠ[𝓝 z] fun w : State1 ↦ w 0 := by
      filter_upwards [hpos] with w hw
      -- Proof comment: on a neighborhood where the unique coordinate stays positive, the norm is
      -- just that coordinate.
      rw [norm_eq_abs_firstCoordinate_state1]
      simp [abs_of_pos hw]
    rw [InnerProductSpace.harmonicAt_congr_nhds hlocal]
    exact firstCoordinate_harmonicAt_state1 z
  · have hzneg : z 0 < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz_coord_ne
    have hneg : {w : State1 | w 0 < 0} ∈ 𝓝 z :=
      IsOpen.mem_nhds (isOpen_lt p.continuous continuous_const) hzneg
    have hlocal : (fun w : State1 ↦ ‖w‖) =ᶠ[𝓝 z] fun w : State1 ↦ -(w 0) := by
      filter_upwards [hneg] with w hw
      -- Proof comment: on a neighborhood where the unique coordinate stays negative, the norm is
      -- its negation.
      rw [norm_eq_abs_firstCoordinate_state1]
      simp [abs_of_neg hw]
    rw [InnerProductSpace.harmonicAt_congr_nhds hlocal]
    exact (firstCoordinate_harmonicAt_state1 z).neg

/-- Helper for Theorem 25.40: pulling back a harmonic function along a real linear isometry from
`ℝ²` to `ℂ` preserves pointwise harmonicity. -/
private theorem harmonicAt_precomp_complexIsometry
    {f : ℂ → ℝ} {e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ}
    {z : EuclideanSpace ℝ (Fin 2)} :
    InnerProductSpace.HarmonicAt f (e z) →
      InnerProductSpace.HarmonicAt (fun w : EuclideanSpace ℝ (Fin 2) ↦ f (e w)) z := by
  intro h
  refine ⟨h.1.comp z e.contDiff.contDiffAt, ?_⟩
  have hzero :
      ∀ᶠ w in 𝓝 z, Laplacian.laplacian f (e w) = 0 :=
    e.continuousAt.tendsto.eventually h.2
  filter_upwards [hzero] with w hwlap
  -- Proof comment: the Laplacian is invariant under precomposition by the linear isometry `e`,
  -- because the second derivative transports by `iteratedFDerivWithin_comp_right` and the
  -- orthonormal basis of `ℝ²` maps to an orthonormal basis of `ℂ`.
  have hpoint :
      Laplacian.laplacian (fun u : EuclideanSpace ℝ (Fin 2) ↦ f (e u)) w =
        Laplacian.laplacian f (e w) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (f := fun u : EuclideanSpace ℝ (Fin 2) ↦ f (e u))
      (v := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2)))]
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (f := f)
      (v := (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))).map e)]
    simp only [OrthonormalBasis.map_apply]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiter :
        iteratedFDeriv ℝ 2 (fun u : EuclideanSpace ℝ (Fin 2) ↦ f (e u)) w =
          (iteratedFDeriv ℝ 2 f (e w)).compContinuousLinearMap
            (fun _ : Fin 2 ↦ e.toContinuousLinearEquiv.toContinuousLinearMap) := by
      simpa [Function.comp, iteratedFDerivWithin_univ] using
        (e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right
          (f := f) (s := (Set.univ : Set ℂ)) (x := w) (i := 2) (by simp))
    have hcomp :=
      congrArg
        (fun T :
            ContinuousMultilinearMap ℝ
              (fun _ : Fin 2 ↦ EuclideanSpace ℝ (Fin 2)) ℝ ↦
            T ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i,
              (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i])
        hiter
    have hvec :
        (fun j : Fin 2 ↦
          e
            (![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i,
              (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i] j)) =
          ![e ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i),
            e ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))) i)] := by
      ext j
      fin_cases j <;> rfl
    simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hvec] using hcomp
  rw [hpoint]
  simpa using hwlap

/-- Helper for Theorem 25.40: on `ℝ²`, the logarithmic radial profile is harmonic away from the
origin by transporting the complex-plane owner along the standard real-linear isometry. -/
private theorem logNorm_harmonicAt_dimTwo_of_ne_zero
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖w‖) z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hez_ne : e z ≠ 0 := by
    intro hez
    apply hz
    exact e.injective (by simpa using hez)
  have hcomplex : InnerProductSpace.HarmonicAt (fun w : ℂ ↦ Real.log ‖w‖) (e z) := by
    -- Proof comment: on the complex plane, the harmonic owner is already provided by the
    -- analytic `log ‖·‖` theorem away from the origin.
    simpa using
      (AnalyticAt.harmonicAt_log_norm
        (f := fun w : ℂ ↦ w) (z := e z) analyticAt_id hez_ne)
  have hpullback :
      InnerProductSpace.HarmonicAt
        (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖e w‖) z :=
    harmonicAt_precomp_complexIsometry
      (f := fun w : ℂ ↦ Real.log ‖w‖) (e := e) (z := z) hcomplex
  -- Proof comment: the chosen isometry preserves the norm, so the pulled-back profile is exactly
  -- the Euclidean logarithmic profile.
  have hprofile :
      (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖e w‖) =
        (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖w‖) := by
    funext w
    rw [LinearIsometryEquiv.norm_map]
  exact hprofile ▸ hpullback

/-- Helper for Theorem 25.40: this is the constant bilinear owner underlying the derivative of
`z ↦ innerSL ℝ z`, kept explicit so the higher-dimensional radial Laplacian proof stays in one
stable spelling world. -/
private noncomputable def normSqDerivLinear :
    State →L[ℝ] State →L[ℝ] ℝ :=
  IsBoundedLinearMap.toContinuousLinearMap
    (f := (innerSL ℝ : State →L⋆[ℝ] State →L[ℝ] ℝ))
    ((innerSL ℝ).isBoundedLinearMap)

/-- Helper for Theorem 25.40: evaluating the constant bilinear owner from `normSqDerivLinear`
recovers the ambient real inner product. -/
private theorem normSqDerivLinear_apply
    (v w : State) :
    normSqDerivLinear (d := d) v w = inner ℝ v w := by
  -- Proof comment: `normSqDerivLinear` is just `innerSL` rebundled as a constant bilinear map.
  rfl

/-- Helper for Theorem 25.40: differentiating the field `z ↦ 2 • innerSL ℝ z` produces the
constant bilinear owner `2 • normSqDerivLinear`. -/
private theorem hasFDerivAt_normSqDeriv
    (x : State) :
    HasFDerivAt
      (fun z : State ↦ (2 : ℝ) • innerSL ℝ z)
      ((2 : ℝ) • normSqDerivLinear (d := d))
      x := by
  have hinner :
      HasFDerivAt
        (fun z : State ↦ innerSL ℝ z)
        (normSqDerivLinear (d := d))
        x :=
    (innerSL ℝ).isBoundedLinearMap.hasFDerivAt
  -- Proof comment: the variable field is linear in `z`, so only the constant bilinear owner
  -- remains after differentiation.
  simpa using hinner.const_smul (2 : ℝ)

/-- Helper for Theorem 25.40: the centered squared norm has derivative `2 • innerSL ℝ x`. This is
the stable entry point for the higher-dimensional radial Laplacian computation. -/
private theorem hasFDerivAt_normSq
    (x : State) :
    HasFDerivAt
      (fun z : State ↦ ‖z‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ x)
      x := by
  -- Proof comment: the centered squared norm is the special case `a = 0` of the standard
  -- translated squared-norm derivative formula.
  simpa [two_nsmul, two_smul] using
    ((ContinuousLinearMap.id ℝ State).hasFDerivAt.norm_sq :
      HasFDerivAt
        (fun z : State ↦ ‖z‖ ^ 2)
        (2 • ((innerSL ℝ) x).comp (ContinuousLinearMap.id ℝ State))
        x)

/-- Helper for Theorem 25.40: tracing the squared directional derivatives of the centered norm
over the standard orthonormal basis collapses to `4 * ‖x‖²`. -/
private theorem normSqDerivTrace_eq_four_normSq
    {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i, ((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
      ((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) =
        4 * (‖x‖ ^ 2) := by
  have hsum :=
    OrthonormalBasis.sum_inner_mul_inner
      (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) x x
  -- Proof comment: the orthonormal-basis trace of the squared directional derivatives reduces to
  -- the standard Parseval identity for `x`, with the outer factor `2` contributing the factor `4`.
  calc
    ∑ i, ((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
        ((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) =
      ∑ i,
        4 *
          (inner ℝ x ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
            inner ℝ ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) x) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [real_inner_comm]
            ring
    _ = 4 * inner ℝ x x := by
          rw [← Finset.mul_sum]
          simpa [real_inner_comm] using hsum
    _ = 4 * (‖x‖ ^ 2) := by simp

/-- Helper for Theorem 25.40: the expensive centered second-derivative normalization for
`z ↦ (‖z‖²)^(1 - d / 2)` is isolated in one spelling world before the Laplacian trace
computation. -/
private theorem centeredNormSqPoissonNumeratorSecondFDeriv_eq
    {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    let s : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
    let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      fun z ↦ (2 : ℝ) • innerSL ℝ z
    let q : ℝ := 1 - (d : ℝ) / 2
    let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (s z) ^ (q - 1)
    fderiv ℝ
        (fun z : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ (fun w : EuclideanSpace ℝ (Fin d) ↦ (s w) ^ q) z)
        x =
      coeff x • ((2 : ℝ) • normSqDerivLinear (d := d)) +
        (fderiv ℝ coeff x).smulRight (ds x) := by
  let s : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
  let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fun z ↦ (2 : ℝ) • innerSL ℝ z
  let q : ℝ := 1 - (d : ℝ) / 2
  let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (s z) ^ (q - 1)
  have hsx_ne : s x ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hs :
      HasFDerivAt s (ds x) x := by
    -- Proof comment: the centered squared norm has the already packaged first derivative `ds x`.
    simpa [s, ds] using hasFDerivAt_normSq (d := d) x
  have hds :
      HasFDerivAt ds ((2 : ℝ) • normSqDerivLinear (d := d)) x := by
    -- Proof comment: the derivative field of the centered squared norm is affine in `z`, so its
    -- derivative is the constant bilinear owner from `normSqDerivLinear`.
    simpa [ds] using hasFDerivAt_normSqDeriv (d := d) x
  have hcoeffPow :
      HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin d) ↦ (s z) ^ (q - 1))
        (((q - 1) * (s x) ^ ((q - 1) - 1)) • ds x)
        x := by
    -- Proof comment: away from `0`, the intermediate radial power is differentiable because the
    -- squared norm does not vanish at `x`.
    simpa [s, smul_smul, mul_assoc] using
      (hs.rpow_const (p := q - 1) (Or.inl hsx_ne))
  have hcoeff :
      HasFDerivAt coeff
        ((q * ((q - 1) * (s x) ^ ((q - 1) - 1))) • ds x)
        x := by
    -- Proof comment: the coefficient field is the previous radial factor scaled by the constant
    -- `q`.
    simpa [coeff, smul_smul, mul_assoc] using hcoeffPow.const_mul q
  have hcoeff_fderiv :
      fderiv ℝ coeff x =
        (q * ((q - 1) * (s x) ^ ((q - 1) - 1))) • ds x := by
    exact hcoeff.fderiv
  have hradialFDerivNear :
      (fun z : EuclideanSpace ℝ (Fin d) ↦
        fderiv ℝ (fun w : EuclideanSpace ℝ (Fin d) ↦ (s w) ^ q) z) =ᶠ[𝓝 x]
        fun z : EuclideanSpace ℝ (Fin d) ↦ coeff z • ds z := by
    have hRadius : 0 < ‖x‖ / 2 := half_pos (norm_pos_iff.mpr hx)
    filter_upwards [Metric.ball_mem_nhds x hRadius] with z hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hdist : ‖x‖ < ‖x‖ / 2 := by
        simpa [Metric.mem_ball, dist_eq_norm, hz0, norm_sub_rev] using hz
      linarith [norm_nonneg x]
    simpa [s, coeff, q, ds, smul_smul, mul_assoc] using
      (hasFDerivAt_normSq (d := d) z).rpow_const
        (p := q) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz_ne)))
      |>.fderiv
  have hSecond_fderiv :
      fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) ↦ coeff z • ds z) x =
        coeff x • ((2 : ℝ) • normSqDerivLinear (d := d)) +
          (fderiv ℝ coeff x).smulRight (ds x) := by
    -- Proof comment: once the first derivative is written as `coeff z • ds z`, one product rule
    -- gives the second derivative in a stable normal form.
    simpa [hcoeff_fderiv] using (hcoeff.smul hds).fderiv
  have hSecondField :
      fderiv ℝ
          (fun z : EuclideanSpace ℝ (Fin d) ↦
            fderiv ℝ (fun w : EuclideanSpace ℝ (Fin d) ↦ (s w) ^ q) z)
          x =
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) ↦ coeff z • ds z) x :=
    hradialFDerivNear.fderiv_eq
  -- Proof comment: the neighborhood identification turns the product-rule derivative into the
  -- desired second-derivative formula for the centered Newtonian numerator.
  exact hSecondField.trans hSecond_fderiv

/-- Helper for Theorem 25.40: the derivative of the scalar coefficient
`z ↦ (1 - d / 2) * (‖z‖²)^(- d / 2)` is the expected radial multiple of `2 • innerSL ℝ x`. -/
private theorem centeredNormSqPoissonCoefficientFDeriv_eq
    {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    let s : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
    let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      fun z ↦ (2 : ℝ) • innerSL ℝ z
    let q : ℝ := 1 - (d : ℝ) / 2
    let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (s z) ^ (q - 1)
    fderiv ℝ coeff x =
      (q * ((q - 1) * (s x) ^ ((q - 1) - 1))) • ds x := by
  let s : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
  let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fun z ↦ (2 : ℝ) • innerSL ℝ z
  let q : ℝ := 1 - (d : ℝ) / 2
  let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (s z) ^ (q - 1)
  have hsx_ne : s x ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hs :
      HasFDerivAt s (ds x) x := by
    -- Proof comment: the centered squared norm already has the packaged derivative field `ds`.
    simpa [s, ds] using hasFDerivAt_normSq (d := d) x
  have hcoeffPow :
      HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin d) ↦ (s z) ^ (q - 1))
        (((q - 1) * (s x) ^ ((q - 1) - 1)) • ds x)
        x := by
    -- Proof comment: off the origin, the coefficient's radial power differentiates by the
    -- one-variable `rpow` chain rule.
    simpa [s, smul_smul, mul_assoc] using
      (hs.rpow_const (p := q - 1) (Or.inl hsx_ne))
  have hcoeff :
      HasFDerivAt coeff
        ((q * ((q - 1) * (s x) ^ ((q - 1) - 1))) • ds x)
        x := by
    -- Proof comment: the remaining scalar factor `q` is constant, so it only rescales the
    -- derivative of the radial power term.
    simpa [coeff, smul_smul, mul_assoc] using hcoeffPow.const_mul q
  exact hcoeff.fderiv

/-- Helper for Theorem 25.40: the quadratic trace term coming from the coefficient derivative
collapses to a single scalar multiple of `4 * ‖x‖²`. -/
private theorem normSqPoissonNumeratorInnerTrace_eq
    {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i,
      2 *
        (2 *
          ((d : ℝ) / 2 *
            ((1 - (d : ℝ) / 2) *
              ((‖x‖ ^ 2) ^ (-(d : ℝ) / 2 - 1) *
                (inner ℝ x ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
                  inner ℝ x ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i)))))) =
      (d : ℝ) / 2 *
        ((1 - (d : ℝ) / 2) * (4 * (‖x‖ ^ 2 * (‖x‖ ^ 2) ^ (-(d : ℝ) / 2 - 1)))) := by
  let c : ℝ := (d : ℝ) / 2 * ((1 - (d : ℝ) / 2) * (‖x‖ ^ 2) ^ (-(d : ℝ) / 2 - 1))
  calc
    ∑ i,
        2 *
          (2 *
            ((d : ℝ) / 2 *
              ((1 - (d : ℝ) / 2) *
                ((‖x‖ ^ 2) ^ (-(d : ℝ) / 2 - 1) *
                  (inner ℝ x ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
                    inner ℝ x ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i)))))) =
      ∑ i,
        c *
          (((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
            ((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [c]
            ring
    _ = c *
        ∑ i,
          (((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
            ((2 : ℝ) • innerSL ℝ x) ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i)) := by
            rw [← Finset.mul_sum]
    _ = c * (4 * (‖x‖ ^ 2)) := by rw [normSqDerivTrace_eq_four_normSq]
    _ = (d : ℝ) / 2 *
        ((1 - (d : ℝ) / 2) * (4 * (‖x‖ ^ 2 * (‖x‖ ^ 2) ^ (-(d : ℝ) / 2 - 1)))) := by
          simp [c]
          ring

/-- Helper for Theorem 25.40: the post-trace scalar coefficients in the centered Newtonian
Laplacian cancellation sum to `0`. -/
private theorem normSqPoissonNumeratorLaplacianScalarClosure
    {d : ℕ} {s : ℝ} (hs_nonneg : 0 ≤ s) (hs_ne : s ≠ 0) :
    let q : ℝ := 1 - (d : ℝ) / 2
    (q * s ^ (q - 1)) * (2 * (d : ℝ)) +
      (q * ((q - 1) * s ^ ((q - 1) - 1))) * (4 * s) = 0 := by
  have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg hs_ne.symm
  have hs_one : s ^ (1 : ℝ) = s := by
    simpa using (Real.rpow_natCast s 1)
  have hs_mul : s ^ ((1 - (d : ℝ) / 2 - 1) - 1) * s = s ^ (1 - (d : ℝ) / 2 - 1) := by
    -- Proof comment: isolate the single `rpow` multiplication needed to factor the Laplacian
    -- trace into one common radial power.
    nth_rewrite 2 [hs_one.symm]
    rw [← Real.rpow_add hs_pos]
    ring_nf
  -- Proof comment: after the `rpow` normalization, the remaining coefficients cancel because
  -- `2 * d + 4 * ((1 - d / 2) - 1) = 0`.
  dsimp
  rw [← hs_mul]
  ring_nf

/-- Helper for Theorem 25.40: the quadratic trace term built from
`z ↦ 2 • innerSL ℝ z` matches the scalar quantity `4 * ‖x‖²` needed in the centered Newtonian
Laplacian normalization. -/
private theorem normSqPoissonNumeratorQuadraticTrace_eq
    {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    let s : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
    let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      fun z ↦ (2 : ℝ) • innerSL ℝ z
    ∑ i,
      ds x ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) *
        ds x ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))) i) = 4 * s x := by
  -- Proof comment: this is the exact `ds`-spelling of the centered Parseval identity already
  -- established as `normSqDerivTrace_eq_four_normSq`.
  simpa using normSqDerivTrace_eq_four_normSq (d := d) x

/-- Helper for Theorem 25.40: rewriting the centered Newtonian numerator second derivative at `x`
into the stable `coeff • d²s + d coeff ⊗ ds` normal form refreshes the elaboration budget before
the Laplacian trace is assembled. -/
private theorem centeredNormSqPoissonNumeratorSecondFDeriv_rewrite
    {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    let sFun : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
    let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      fun z ↦ (2 : ℝ) • innerSL ℝ z
    let q : ℝ := 1 - (d : ℝ) / 2
    let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (sFun z) ^ (q - 1)
    fderiv ℝ
        (fun z : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ (fun w : EuclideanSpace ℝ (Fin d) ↦ (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2)) z)
        x =
      coeff x • ((2 : ℝ) • normSqDerivLinear (d := d)) +
        (fderiv ℝ coeff x).smulRight (ds x) := by
  let sFun : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
  let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fun z ↦ (2 : ℝ) • innerSL ℝ z
  let q : ℝ := 1 - (d : ℝ) / 2
  let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (sFun z) ^ (q - 1)
  -- Proof comment: keep the heavy second-derivative normalization in its own declaration so the
  -- final Laplacian proof only performs lightweight rewrites.
  simpa [sFun, ds, q, coeff] using
    centeredNormSqPoissonNumeratorSecondFDeriv_eq (d := d) hx

/-- Helper for Theorem 25.40: the coefficient derivative in the centered Newtonian numerator is a
scalar multiple of the first-derivative field `ds`. -/
private theorem centeredNormSqPoissonCoefficientFDeriv_rewrite
    {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    let sFun : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
    let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      fun z ↦ (2 : ℝ) • innerSL ℝ z
    let q : ℝ := 1 - (d : ℝ) / 2
    let s : ℝ := sFun x
    let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (sFun z) ^ (q - 1)
    fderiv ℝ coeff x =
      (q * ((q - 1) * s ^ ((q - 1) - 1))) • ds x := by
  let sFun : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
  let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fun z ↦ (2 : ℝ) • innerSL ℝ z
  let q : ℝ := 1 - (d : ℝ) / 2
  let s : ℝ := sFun x
  let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (sFun z) ^ (q - 1)
  -- Proof comment: isolating the coefficient derivative in a separate lemma avoids repeating the
  -- same `rpow` elaboration inside the Laplacian trace assembly.
  simpa [sFun, ds, q, coeff, s] using
    centeredNormSqPoissonCoefficientFDeriv_eq (d := d) hx

/-- Helper for Theorem 25.40: tracing the constant bilinear part `2 • normSqDerivLinear` over the
standard orthonormal basis yields exactly `2 * d`. -/
private theorem normSqPoissonNumeratorLinearTrace_eq_scalar
    {d : ℕ} :
    let basis := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
    ∑ i, ((2 : ℝ) • normSqDerivLinear (d := d)) (basis i) (basis i) = 2 * (d : ℝ) := by
  let basis := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
  -- Proof comment: the trace only sees the `d` unit diagonal values of the orthonormal basis.
  calc
    ∑ i, ((2 : ℝ) • normSqDerivLinear (d := d)) (basis i) (basis i) =
        ∑ i, (2 : ℝ) * inner ℝ (basis i) (basis i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [basis, normSqDerivLinear_apply, mul_comm]
    _ = ∑ i, (2 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [basis]
    _ = 2 * (d : ℝ) := by
          simp [basis]
          ring

/-- Helper for Theorem 25.40: tracing the `smulRight` term built from `ds x` factors as the
scalar coefficient times the quadratic Parseval trace `4 * ‖x‖²`. -/
private theorem normSqPoissonNumeratorSmulRightTrace_eq_scalar
    {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      fun z ↦ (2 : ℝ) • innerSL ℝ z
    let basis := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
    let s : ℝ := ‖x‖ ^ 2
    ∑ i, ((c • ds x).smulRight (ds x)) (basis i) (basis i) = c * (4 * s) := by
  let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fun z ↦ (2 : ℝ) • innerSL ℝ z
  let basis := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
  let s : ℝ := ‖x‖ ^ 2
  have hQuadraticCore :
      ∑ i, ds x (basis i) * ds x (basis i) = 4 * s := by
    -- Proof comment: this is the previously isolated quadratic trace collapse specialized to the
    -- exact `ds` spelling used in the Laplacian computation.
    simpa [ds, basis, s] using normSqPoissonNumeratorQuadraticTrace_eq (d := d) x
  -- Proof comment: `smulRight` contributes a scalar factor `c` and then the same quadratic trace
  -- of `ds x` against the standard basis.
  calc
    ∑ i, ((c • ds x).smulRight (ds x)) (basis i) (basis i) =
        c * ∑ i, ds x (basis i) * ds x (basis i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [ContinuousLinearMap.smulRight_apply, mul_assoc, mul_left_comm, mul_comm]
    _ = c * (4 * s) := by rw [hQuadraticCore]

/-- Helper for Theorem 25.40: after rewriting the centered Newtonian numerator Laplacian as the
standard-basis Hessian trace, the remaining multilinear evaluation collapses to the scalar
cancellation term handled by `normSqPoissonNumeratorLaplacianScalarClosure`. -/
private theorem normSqPoissonNumeratorHessianTrace_eq_scalar
    {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    let s : ℝ := ‖x‖ ^ 2
    let q : ℝ := 1 - (d : ℝ) / 2
    Laplacian.laplacian
      (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) x =
      (q * s ^ (q - 1)) * (2 * (d : ℝ)) +
        (q * ((q - 1) * s ^ ((q - 1) - 1))) * (4 * s) := by
  let sFun : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ ‖z‖ ^ 2
  let ds : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    fun z ↦ (2 : ℝ) • innerSL ℝ z
  let q : ℝ := 1 - (d : ℝ) / 2
  let s : ℝ := sFun x
  let coeff : EuclideanSpace ℝ (Fin d) → ℝ := fun z ↦ q * (sFun z) ^ (q - 1)
  let basis := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
  have hLaplacian :
      Laplacian.laplacian
          (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) x =
        ∑ i, iteratedFDeriv ℝ 2
          (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) x
          ![basis i, basis i] := by
    -- Proof comment: rewrite the Laplacian once into the standard-basis Hessian trace before
    -- consuming the already normalized second-derivative formula.
    simpa [basis] using
      congrFun
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
          (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) basis)
        x
  have hSecond :
      fderiv ℝ
          (fun z : EuclideanSpace ℝ (Fin d) ↦
            fderiv ℝ
              (fun w : EuclideanSpace ℝ (Fin d) ↦ (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2)) z)
          x =
        coeff x • ((2 : ℝ) • normSqDerivLinear (d := d)) +
          (fderiv ℝ coeff x).smulRight (ds x) := by
    simpa [sFun, ds, q, coeff] using
      centeredNormSqPoissonNumeratorSecondFDeriv_rewrite (d := d) hx
  have hCoeff :
      fderiv ℝ coeff x =
        (q * ((q - 1) * s ^ ((q - 1) - 1))) • ds x := by
    simpa [sFun, ds, q, coeff, s] using
      centeredNormSqPoissonCoefficientFDeriv_rewrite (d := d) hx
  have hConstTrace :
      ∑ i, (coeff x • ((2 : ℝ) • normSqDerivLinear (d := d))) (basis i) (basis i) =
        (q * s ^ (q - 1)) * (2 * (d : ℝ)) := by
    -- Proof comment: once the basis trace of `2 • normSqDerivLinear` is closed independently,
    -- the outer scalar coefficient only needs a single `simp`.
    calc
      ∑ i, (coeff x • ((2 : ℝ) • normSqDerivLinear (d := d))) (basis i) (basis i) =
          coeff x * ∑ i, ((2 : ℝ) • normSqDerivLinear (d := d)) (basis i) (basis i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [coeff, mul_assoc]
      _ = coeff x * (2 * (d : ℝ)) := by
            simpa [basis] using
              congrArg (fun t : ℝ ↦ coeff x * t)
                (normSqPoissonNumeratorLinearTrace_eq_scalar (d := d))
      _ = (q * s ^ (q - 1)) * (2 * (d : ℝ)) := by
            simp [coeff, s]
  have hQuadraticTrace :
      ∑ i, (((q * ((q - 1) * s ^ ((q - 1) - 1))) • ds x).smulRight (ds x))
          (basis i) (basis i) =
        (q * ((q - 1) * s ^ ((q - 1) - 1))) * (4 * s) := by
    -- Proof comment: the `smulRight` trace is delegated to the standalone quadratic-trace lemma.
    simpa [ds, basis, s] using
      normSqPoissonNumeratorSmulRightTrace_eq_scalar
        (d := d) x (q * ((q - 1) * s ^ ((q - 1) - 1)))
  calc
    Laplacian.laplacian
        (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) x =
      ∑ i, iteratedFDeriv ℝ 2
        (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) x
        ![basis i, basis i] := hLaplacian
    _ = ∑ i, fderiv ℝ
          (fderiv ℝ
            (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2))) x
          (basis i) (basis i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [iteratedFDeriv_two_apply]
    _ = ∑ i,
          (coeff x • ((2 : ℝ) • normSqDerivLinear (d := d)) +
            (fderiv ℝ coeff x).smulRight (ds x))
            (basis i) (basis i) := by
            rw [hSecond]
    _ =
        ∑ i, (coeff x • ((2 : ℝ) • normSqDerivLinear (d := d))) (basis i) (basis i) +
          ∑ i, ((fderiv ℝ coeff x).smulRight (ds x)) (basis i) (basis i) := by
            simp [Finset.sum_add_distrib]
    _ =
        (q * s ^ (q - 1)) * (2 * (d : ℝ)) +
          ∑ i, (((q * ((q - 1) * s ^ ((q - 1) - 1))) • ds x).smulRight (ds x))
            (basis i) (basis i) := by
            rw [hConstTrace, hCoeff]
    _ =
        (q * s ^ (q - 1)) * (2 * (d : ℝ)) +
          (q * ((q - 1) * s ^ ((q - 1) - 1))) * (4 * s) := by
            rw [hQuadraticTrace]

/-- Helper for Theorem 25.40: away from `0`, the centered Newtonian numerator
`(‖z‖²)^(1 - d / 2)` has vanishing Laplacian. -/
private theorem laplacian_normSqPoissonNumeratorPower_eq_zero
    {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    Laplacian.laplacian
      (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) x = 0 := by
  have hsx_ne : ‖x‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hsx_nonneg : 0 ≤ ‖x‖ ^ 2 := by positivity
  have htrace :
      let s : ℝ := ‖x‖ ^ 2
      let q : ℝ := 1 - (d : ℝ) / 2
      Laplacian.laplacian
        (fun z : EuclideanSpace ℝ (Fin d) ↦ (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2)) x =
        (q * s ^ (q - 1)) * (2 * (d : ℝ)) +
          (q * ((q - 1) * s ^ ((q - 1) - 1))) * (4 * s) := by
    simpa using normSqPoissonNumeratorHessianTrace_eq_scalar (d := d) hx
  have hclosure :
      let s : ℝ := ‖x‖ ^ 2
      let q : ℝ := 1 - (d : ℝ) / 2
      (q * s ^ (q - 1)) * (2 * (d : ℝ)) +
        (q * ((q - 1) * s ^ ((q - 1) - 1))) * (4 * s) = 0 := by
    simpa using
      normSqPoissonNumeratorLaplacianScalarClosure
        (d := d) (s := ‖x‖ ^ 2) hsx_nonneg hsx_ne
  -- Proof comment: once the exact Hessian trace is reduced to the scalar radial expression, the
  -- previously verified scalar cancellation lemma closes the Laplacian identity immediately.
  simpa using htrace.trans hclosure

/-- Helper for Theorem 25.40: away from `0`, the centered Newtonian numerator
`(‖w‖²)^(1 - d / 2)` is harmonic. -/
private theorem normSqPoissonNumeratorPower_harmonicAt_of_ne_zero
    {d : ℕ} {z : EuclideanSpace ℝ (Fin d)} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt
      (fun w : EuclideanSpace ℝ (Fin d) ↦ (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2))
      z := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: off the origin, the centered squared norm never vanishes, so the radial
    -- real power is genuinely `C²`.
    have hs_ne : ‖z‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    simpa using
      ((contDiffAt_id.norm_sq ℝ).rpow_const_of_ne
        (p := 1 - (d : ℝ) / 2) hs_ne)
  · have hz_dist_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    filter_upwards [Metric.ball_mem_nhds z (half_pos hz_dist_pos)] with w hw
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hdist : ‖z‖ < ‖z‖ / 2 := by
        simpa [Metric.mem_ball, dist_eq_norm, hw0, norm_sub_rev] using hw
      linarith [norm_nonneg z]
    -- Proof comment: the Laplacian formula above is stable on a punctured neighborhood around
    -- `z`, so it supplies the eventual-zero half of harmonicity.
    exact laplacian_normSqPoissonNumeratorPower_eq_zero (d := d) hw_ne

/-- Helper for Theorem 25.40: off `0`, the Newtonian kernel `(ρ / ‖w‖)^(d - 2)` is a constant
multiple of the centered numerator `(‖w‖²)^(1 - d / 2)`. -/
private theorem radialPowerCore_eq_constMul_normSqPoissonNumeratorPower
    {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) :
    (ρ / ‖w‖) ^ (d - 2) =
      (ρ ^ (d - 2 : ℕ)) * (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2) := by
  have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hw_norm_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
  have hcast : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub hd]
    norm_num
  -- Route correction: this rewrite is only valid once `d - 2` is interpreted as the nonnegative
  -- real exponent `(d : ℝ) - 2`; the earlier no-hypothesis statement was false in low
  -- dimensions.
  calc
    (ρ / ‖w‖) ^ (d - 2) = ρ ^ (d - 2 : ℕ) * (‖w‖⁻¹) ^ (d - 2) := by
      rw [div_eq_mul_inv, mul_pow]
    _ = ρ ^ (d - 2 : ℕ) * (‖w‖ ^ (d - 2 : ℕ))⁻¹ := by
      rw [inv_pow]
    _ = ρ ^ (d - 2 : ℕ) * (‖w‖ ^ ((d - 2 : ℕ) : ℝ))⁻¹ := by
      congr 1
      rw [← Real.rpow_natCast]
    _ = ρ ^ (d - 2 : ℕ) * ‖w‖ ^ (-((d - 2 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hw_norm_nonneg]
    _ = ρ ^ (d - 2 : ℕ) * ‖w‖ ^ (2 * (1 - (d : ℝ) / 2)) := by
      congr 2
      linarith
    _ = (ρ ^ (d - 2 : ℕ)) * (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2) := by
      have hrpow :
          ‖w‖ ^ (2 * (1 - (d : ℝ) / 2)) = (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2) := by
        simpa using (Real.rpow_mul hw_norm_nonneg 2 (1 - (d : ℝ) / 2))
      rw [hrpow]

/-- Helper for Theorem 25.40: in dimensions strictly larger than `2`, the Newtonian radial core is
harmonic away from the origin. -/
private theorem radialPowerCore_harmonicAt_dimGtTwo_of_ne_zero
    {d : ℕ} [NeZero d] (hd : 2 < d) {ρ : ℝ} (hρ : 0 < ρ)
    {z : EuclideanSpace ℝ (Fin d)}
    (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt
      (fun w : EuclideanSpace ℝ (Fin d) ↦ (ρ / ‖w‖) ^ (d - 2)) z := by
  have hcore :
      InnerProductSpace.HarmonicAt
        (fun w : EuclideanSpace ℝ (Fin d) ↦ (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2))
        z :=
    normSqPoissonNumeratorPower_harmonicAt_of_ne_zero (d := d) hz
  have hscaled :
      InnerProductSpace.HarmonicAt
        (fun w : EuclideanSpace ℝ (Fin d) ↦
          (ρ ^ (d - 2 : ℕ)) * (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2))
        z := by
    -- Proof comment: after isolating the centered harmonic core, the Newtonian kernel differs
    -- from it only by a constant scalar factor depending on `ρ`.
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using
      hcore.const_smul (c := ρ ^ (d - 2 : ℕ))
  have hzball :
      Metric.ball z (‖z‖ / 2) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (half_pos (norm_pos_iff.mpr hz))
  have hEq :
      (fun w : EuclideanSpace ℝ (Fin d) ↦ (ρ / ‖w‖) ^ (d - 2)) =ᶠ[𝓝 z]
        fun w ↦ (ρ ^ (d - 2 : ℕ)) * (‖w‖ ^ 2) ^ (1 - (d : ℝ) / 2) := by
    filter_upwards [hzball] with w hw
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hdist : ‖z‖ < ‖z‖ / 2 := by
        simpa [Metric.mem_ball, dist_eq_norm, hw0, norm_sub_rev] using hw
      linarith [norm_nonneg z]
    -- Proof comment: on a punctured neighborhood of `z`, the explicit Newtonian kernel rewrites
    -- exactly to the centered harmonic numerator times a constant factor.
    exact radialPowerCore_eq_constMul_normSqPoissonNumeratorPower (d := d) hd.le hw_ne
  -- Proof comment: harmonicity is local, so the punctured-neighborhood rewrite transfers the
  -- harmonic owner from the centered numerator to the Newtonian kernel.
  exact (InnerProductSpace.harmonicAt_congr_nhds hEq).2 hscaled

/-- Helper for Theorem 25.40: the continuity-on-closure part of the annulus Dirichlet package is
already established, so the remaining PDE gap is only harmonicity on the open annulus. -/
private theorem centeredAnnulusProfile_harmonicAt_of_ne_zero
    [NeZero d] {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) {z : State} (hz_ne : z ≠ 0) :
    InnerProductSpace.HarmonicAt (centeredAnnulusProfile (d := d) ρ R) z := by
  by_cases h1 : d = 1
  · subst h1
    have hnorm_ne : ‖z‖ ≠ 0 := by
      simpa [norm_eq_zero] using hz_ne
    have hnorm_harm :
        InnerProductSpace.HarmonicAt (fun w : State1 ↦ ‖w‖) z :=
      norm_harmonicAt_state1_of_ne_zero hz_ne
    have hsub :
        InnerProductSpace.HarmonicAt (fun w : State1 ↦ R - ‖w‖) z :=
      (InnerProductSpace.harmonicAt_const (x := z) R).sub hnorm_harm
    have hbranch :
        InnerProductSpace.HarmonicAt
          (fun w : State1 ↦ (R - ‖w‖) / (R - ρ)) z := by
      -- Proof comment: away from `0`, the one-dimensional branch is just an affine rescaling of
      -- the harmonic norm function.
      convert hsub.const_smul (c := (R - ρ)⁻¹) using 1
      funext w
      simp [Pi.smul_apply, div_eq_mul_inv, smul_eq_mul, mul_comm]
    simpa [centeredAnnulusProfile] using hbranch
  · by_cases h2 : d = 2
    · subst h2
      have hnorm_ne : ‖z‖ ≠ 0 := by
        simpa [norm_eq_zero] using hz_ne
      have hlog :
          InnerProductSpace.HarmonicAt
            (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log ‖w‖) z :=
        logNorm_harmonicAt_dimTwo_of_ne_zero hz_ne
      have hsub :
          InnerProductSpace.HarmonicAt
            (fun w : EuclideanSpace ℝ (Fin 2) ↦ Real.log R - Real.log ‖w‖) z :=
        (InnerProductSpace.harmonicAt_const (x := z) (Real.log R)).sub hlog
      have hbranch :
          InnerProductSpace.HarmonicAt
            (fun w : EuclideanSpace ℝ (Fin 2) ↦
              (Real.log R - Real.log ‖w‖) / (Real.log R - Real.log ρ)) z := by
        -- Proof comment: the planar branch is the same affine rescaling pattern applied to the
        -- harmonic logarithmic core.
        convert hsub.const_smul (c := (Real.log R - Real.log ρ)⁻¹) using 1
        funext w
        simp [Pi.smul_apply, div_eq_mul_inv, smul_eq_mul, mul_comm]
      simpa [centeredAnnulusProfile] using hbranch
    · have hd_gt_two : 2 < d := by
        have hd0 : d ≠ 0 := NeZero.ne d
        omega
      have hcore :
          InnerProductSpace.HarmonicAt
            (fun w : State ↦ (ρ / ‖w‖) ^ (d - 2)) z :=
        radialPowerCore_harmonicAt_dimGtTwo_of_ne_zero (d := d) hd_gt_two hr hz_ne
      have hsub :
          InnerProductSpace.HarmonicAt
            (fun w : State ↦ (ρ / ‖w‖) ^ (d - 2) - (ρ / R) ^ (d - 2)) z :=
        hcore.sub (InnerProductSpace.harmonicAt_const (x := z) ((ρ / R) ^ (d - 2)))
      have hbranch :
          InnerProductSpace.HarmonicAt
            (fun w : State ↦
              ((ρ / ‖w‖) ^ (d - 2) - (ρ / R) ^ (d - 2)) / (1 - (ρ / R) ^ (d - 2))) z := by
        -- Proof comment: in dimensions `d > 2`, the Newtonian radial core stays harmonic away
        -- from `0`, and the annulus profile is again an affine rescaling of that core.
        convert hsub.const_smul (c := (1 - (ρ / R) ^ (d - 2))⁻¹) using 1
        funext w
        simp [Pi.smul_apply, div_eq_mul_inv, smul_eq_mul, mul_comm]
      have hprofile :
          centeredAnnulusProfile (d := d) ρ R =
            (fun w : State ↦
              ((ρ / ‖w‖) ^ (d - 2) - (ρ / R) ^ (d - 2)) / (1 - (ρ / R) ^ (d - 2))) := by
        funext w
        simp [centeredAnnulusProfile, h1, h2]
      exact hprofile ▸ hbranch

/-- Helper for Theorem 25.40: because the closed annulus stays a positive distance from `0`, the
explicit profile admits a global `C²` cutoff extension that agrees with it on `closure G` and is
still harmonic there. This is the global-smoothness interface needed for the remaining stopped
Itô step. -/
private theorem existsCenteredAnnulusProfileExtensionOnClosure
    [NeZero d] {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) :
    ∃ F : State → ℝ,
      ContDiff ℝ 2 F ∧
      InnerProductSpace.HarmonicOnNhd F (closure (concentricAnnulus (0 : State) ρ R)) ∧
      Set.EqOn F (centeredAnnulusProfile (d := d) ρ R)
        (closure (concentricAnnulus (0 : State) ρ R)) := by
  let G : Set State := concentricAnnulus (0 : State) ρ R
  let T : Set State := {z : State | ρ / 2 < ‖z‖}
  have hTopen : IsOpen T := by
    simpa [T] using isOpen_lt continuous_const continuous_norm
  have hClosureG_subset_T : closure G ⊆ T := by
    intro z hz
    dsimp [T]
    have hρle : ρ ≤ ‖z‖ :=
      radius_le_norm_of_mem_closure_centeredAnnulus (d := d) hr hR hz
    linarith
  rcases exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, State)) (M := State) (n := (2 : ℕ∞)) (s := closure G) (t := T)
      isClosed_closure
      (by simpa [hTopen.interior_eq] using hClosureG_subset_T) with
    ⟨φ, hOne, hZero, hRange⟩
  let F : State → ℝ := fun x ↦ φ x * centeredAnnulusProfile (d := d) ρ R x
  have hφ : ContDiff ℝ 2 φ := by
    simpa using φ.contMDiff.contDiff
  have hT_subset_ballCompl : T ⊆ (Metric.ball (0 : State) (ρ / 2))ᶜ := by
    intro z hz
    dsimp [T] at hz
    simp [Metric.mem_ball, dist_eq_norm, not_lt.mpr hz.le]
  have hClosureT_subset_ballCompl :
      closure T ⊆ (Metric.ball (0 : State) (ρ / 2))ᶜ :=
    closure_minimal hT_subset_ballCompl Metric.isOpen_ball.isClosed_compl
  have hF_contDiff : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ closure T
    · have hxBall : x ∈ (Metric.ball (0 : State) (ρ / 2))ᶜ :=
        hClosureT_subset_ballCompl hx
      have hhalf_le : ρ / 2 ≤ ‖x‖ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hxBall
      have hx_ne : x ≠ 0 := by
        intro hx0
        have : ρ / 2 ≤ 0 := by simpa [hx0] using hhalf_le
        linarith
      -- Proof comment: on the closure of the cutoff support, the explicit profile is already
      -- harmonic away from `0`, hence `C²`.
      exact hφ.contDiffAt.mul
        (centeredAnnulusProfile_harmonicAt_of_ne_zero (d := d) hr hR hx_ne).1
    · have hFzero : F =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        have hOutside : (closure T)ᶜ ∈ 𝓝 x :=
          isClosed_closure.isOpen_compl.mem_nhds hx
        filter_upwards [hOutside] with y hy
        have hyT : y ∉ T := fun hyT ↦ hy (subset_closure hyT)
        simp [F, T, hZero y hyT]
      -- Proof comment: outside the cutoff support, the extension vanishes on a whole
      -- neighborhood and is therefore locally constant.
      exact contDiffAt_const.congr_of_eventuallyEq hFzero
  have hF_harmonic :
      InnerProductSpace.HarmonicOnNhd F (closure G) := by
    intro x hxG
    have hφx : ∀ᶠ y in 𝓝 x, φ y = 1 :=
      mem_nhdsSet_iff_forall.mp hOne x hxG
    have hEq : F =ᶠ[𝓝 x] centeredAnnulusProfile (d := d) ρ R := by
      filter_upwards [hφx] with y hy
      simp [F, hy]
    have hx_ne : x ≠ 0 := by
      intro hx0
      exact
        norm_ne_zero_of_mem_closure_centeredAnnulus (d := d) hr hR hxG
          (by simpa [hx0])
    -- Proof comment: on the whole closed annulus the cutoff is identically `1`, so harmonicity
    -- reduces to the explicit away-from-zero PDE owner.
    exact
      (InnerProductSpace.harmonicAt_congr_nhds hEq).2 <|
        centeredAnnulusProfile_harmonicAt_of_ne_zero (d := d) hr hR hx_ne
  have hF_eq :
      Set.EqOn F (centeredAnnulusProfile (d := d) ρ R) (closure G) := by
    intro x hxG
    have hφx : ∀ᶠ y in 𝓝 x, φ y = 1 :=
      mem_nhdsSet_iff_forall.mp hOne x hxG
    have hx1 : φ x = 1 := hφx.self_of_nhds
    -- Proof comment: evaluating the neighborhood identity at the closed-annulus point yields
    -- literal equality with the explicit profile there.
    simp [F, hx1]
  exact ⟨F, hF_contDiff, hF_harmonic, hF_eq⟩

/-- Helper for Theorem 25.40: the continuity-on-closure part of the annulus Dirichlet package is
already established, so the remaining PDE gap is only harmonicity on the open annulus. -/
private theorem centeredAnnulusProfile_harmonicContOnCl
    [NeZero d] {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) :
    InnerProductSpace.HarmonicContOnCl
      (centeredAnnulusProfile (d := d) ρ R)
      (concentricAnnulus (0 : State) ρ R) := by
  refine ⟨?_, centeredAnnulusProfile_continuousOnClosure (d := d) hr hR⟩
  -- Route correction: the continuity and boundary layers are already stable, so the unresolved
  -- PDE owner is now exactly the branchwise harmonicity of the explicit profile on the open
  -- annulus.
  intro z hz
  have hz_closure :
      z ∈ closure (concentricAnnulus (0 : State) ρ R) :=
    subset_closure hz
  have hnorm_ne :
      ‖z‖ ≠ 0 :=
    norm_ne_zero_of_mem_closure_centeredAnnulus (d := d) hr hR hz_closure
  have hz_ne : z ≠ 0 := by
    intro hz0
    exact hnorm_ne (by simpa [hz0])
  -- Proof comment: inside the open annulus, the explicit profile is harmonic simply because the
  -- point stays away from the singularity at `0`.
  exact centeredAnnulusProfile_harmonicAt_of_ne_zero (d := d) hr hR hz_ne

/-- Helper for Theorem 25.40: the centered radial profile should first be packaged as the
Dirichlet solution on the centered annulus before the stochastic argument specializes
Theorem 25.38. -/
private theorem centeredAnnulusProfile_solvesDirichlet
    [NeZero d] {ρ R : ℝ} (hr : 0 < ρ) (hR : ρ < R) :
    SolvesDirichletProblem
      (concentricAnnulus (0 : State) ρ R)
      (fun z : frontier (concentricAnnulus (0 : State) ρ R) ↦
        if (z : State) ∈ Metric.sphere (0 : State) ρ then 1 else 0)
      (centeredAnnulusProfile (d := d) ρ R) := by
  refine ⟨centeredAnnulusProfile_harmonicContOnCl (d := d) hr hR, ?_⟩
  -- Proof comment: after packaging the continuous extension on `closure`, the boundary part is
  -- exactly the previously verified `1/0` frontier normalization.
  intro z
  exact centeredAnnulusProfile_boundaryIndicator (d := d) hr hR z

/-- Helper for Theorem 25.40: centering at `y` turns the start point `x` into a point of the
centered annulus whenever `ρ < dist x y < R`. -/
private theorem sub_mem_centeredAnnulus_of_lt_dist_lt
    {ρ R : ℝ} {x y : State} (hρx : ρ < dist x y) (hR : dist x y < R) :
    x - y ∈ concentricAnnulus (0 : State) ρ R := by
  constructor
  · -- Proof comment: the translated start point stays inside the outer ball because its norm is
    -- exactly the original distance to the center `y`.
    simpa [Metric.mem_ball, dist_eq_norm] using hR
  · -- Proof comment: the same radius identity shows that the translated start point stays outside
    -- the closed inner ball.
    have hnot : ¬ dist x y ≤ ρ := not_le_of_gt hρx
    simpa [concentricAnnulus, Metric.mem_closedBall, dist_eq_norm] using hnot

/-- Helper for Theorem 25.40: the centered Brownian motion started inside a bounded annulus exits
that annulus almost surely in finite time. -/
private theorem ae_annulusExit_lt_top_startedAt
    [NeZero d]
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x0 : State} {ρ R : ℝ}
    (hx0 : x0 ∈ concentricAnnulus (0 : State) ρ R)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x0)
    (hr : 0 < ρ) (hR : ρ < R) :
    ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤ := by
  -- Proof comment: the concentric annulus is open with compact closure, so the general
  -- compact-domain exit theorem applies directly at the fixed start `x0`.
  exact
    ae_exitTime_lt_top_of_isCompact_closure_startedAt
      (x := x0) hx0 hW (concentricAnnulus_isOpen (0 : State) ρ R)
      (isCompact_closure_concentricAnnulus (d := d) (y := (0 : State)) hr hR)

/-- Helper for Theorem 25.40: if a Brownian path is pointwise continuous, then the exit clock from
an open precompact stage is a stopping time for the natural filtration of the path. This is the
closed-target distance-process reduction needed before measurability of the annulus exit data. -/
private theorem stageExit_isStoppingTime_of_continuous
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U)) :
    IsStoppingTime
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (hittingAfter W Uᶜ 0) := by
  classical
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  let D : NNReal → Ω → ℝ := fun t ω ↦ Metric.infDist (W t ω) Uᶜ
  have hUne : U ≠ Set.univ := by
    intro hUuniv
    have hCompactUniv : IsCompact (Set.univ : Set State) := by
      simpa [hUuniv] using hUcpt
    exact (noncompact_univ State) hCompactUniv
  have hUc_nonempty : (Uᶜ : Set State).Nonempty := Set.nonempty_compl.2 hUne
  have hDsm : ∀ t : NNReal, StronglyMeasurable (D t) := by
    intro t
    -- Proof comment: each distance slice is a continuous image of the measurable Brownian slice.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWsm t).measurable).stronglyMeasurable
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hDcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ D t ω := by
    intro ω
    -- Proof comment: the distance-to-target process inherits continuity from the Brownian path.
    exact (Metric.continuous_infDist_pt (Uᶜ)).comp (hWcont ω)
  have hDadapted : Adapted (Filtration.natural W hWsm) D := by
    intro t
    -- Proof comment: the distance slice depends only on the Brownian position at the same time.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWstrong.stronglyMeasurable_le (i := t) (j := t) le_rfl).measurable)
  have hDnat :
      Filtration.natural D hDsm ≤ Filtration.natural W hWsm :=
    (adapted_iff_natural_le hDsm).1 hDadapted
  have hτdist :
      IsStoppingTime (Filtration.natural D hDsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    have hpair : ({(0 : ℝ), 0} : Set ℝ) = ({0} : Set ℝ) := by
      ext y
      simp
    -- Proof comment: the stage exit clock is the zero-hitting time of the distance process.
    simpa [hpair] using
      twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := D) hDsm hDcont (a := 0) (b := 0)
  have hEqτ :
      hittingAfter W Uᶜ 0 = hittingAfter D ({0} : Set ℝ) 0 := by
    ext ω
    have hclosedUc : IsClosed (Uᶜ : Set State) := isClosed_compl_iff.mpr hUo
    have hCond :
        (∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ) ↔
          ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := by
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    change
      (if ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ Uᶜ} : NNReal) : ENNReal)
        else ⊤) =
        (if ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ D i ω ∈ ({0} : Set ℝ)} : NNReal) :
            ENNReal)
        else ⊤)
    by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ
    · have h' : ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := hCond.mp h
      rw [if_pos h, if_pos h']
      congr 1
      ext j
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    · have h' : ¬ ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := mt hCond.mpr h
      -- Proof comment: if neither process ever reaches zero, both clocks stay at `⊤`.
      rw [if_neg h, if_neg h']
  have hτdistW :
      IsStoppingTime (Filtration.natural W hWsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    intro i
    exact hDnat i _ (hτdist i)
  -- Proof comment: rewrite the exit clock through the distance process and pull the scalar owner
  -- back along the natural-filtration comparison.
  simpa [hEqτ] using hτdistW

/-- Helper for Theorem 25.40: the same continuous exit clock is a stopping time as soon as the
clock is almost surely finite, because that hypothesis rules out the degenerate case `U = univ`.
-/
private theorem stageExit_isStoppingTime_of_continuous_of_aeExitFinite
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤) :
    IsStoppingTime
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (hittingAfter W Uᶜ 0) := by
  classical
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  let D : NNReal → Ω → ℝ := fun t ω ↦ Metric.infDist (W t ω) Uᶜ
  have hUne : U ≠ Set.univ := by
    intro hUuniv
    have hTop :
        ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω = ⊤ := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      simp [hUuniv]
    have hFalse : ∀ᵐ ω ∂(μ : Measure Ω), False := by
      filter_upwards [hExitFinite, hTop] with ω hωfin hωtop
      exact (ne_of_lt hωfin) hωtop
    have hUnivZero : (μ : Measure Ω) Set.univ = 0 := by
      simp [ae_iff] at hFalse
    have hUnivOne : (μ : Measure Ω) Set.univ = 1 := by
      simp
    rw [hUnivZero] at hUnivOne
    norm_num at hUnivOne
  have hUc_nonempty : (Uᶜ : Set State).Nonempty := Set.nonempty_compl.2 hUne
  have hDsm : ∀ t : NNReal, StronglyMeasurable (D t) := by
    intro t
    -- Proof comment: each distance slice is a continuous image of the measurable Brownian slice.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWsm t).measurable).stronglyMeasurable
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hDcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ D t ω := by
    intro ω
    -- Proof comment: the distance-to-target process inherits continuity from the Brownian path.
    exact (Metric.continuous_infDist_pt (Uᶜ)).comp (hWcont ω)
  have hDadapted : Adapted (Filtration.natural W hWsm) D := by
    intro t
    -- Proof comment: the distance slice depends only on the Brownian position at the same time.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWstrong.stronglyMeasurable_le (i := t) (j := t) le_rfl).measurable)
  have hDnat :
      Filtration.natural D hDsm ≤ Filtration.natural W hWsm :=
    (adapted_iff_natural_le hDsm).1 hDadapted
  have hτdist :
      IsStoppingTime (Filtration.natural D hDsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    have hpair : ({(0 : ℝ), 0} : Set ℝ) = ({0} : Set ℝ) := by
      ext y
      simp
    -- Proof comment: the stage exit clock is the zero-hitting time of the distance process.
    simpa [hpair] using
      twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := D) hDsm hDcont (a := 0) (b := 0)
  have hEqτ :
      hittingAfter W Uᶜ 0 = hittingAfter D ({0} : Set ℝ) 0 := by
    ext ω
    have hclosedUc : IsClosed (Uᶜ : Set State) := isClosed_compl_iff.mpr hUo
    have hCond :
        (∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ) ↔
          ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := by
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    change
      (if ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ Uᶜ} : NNReal) : ENNReal)
        else ⊤) =
        (if ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ D i ω ∈ ({0} : Set ℝ)} : NNReal) :
            ENNReal)
        else ⊤)
    by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ
    · have h' : ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := hCond.mp h
      rw [if_pos h, if_pos h']
      congr 1
      ext j
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    · have h' : ¬ ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := mt hCond.mpr h
      -- Proof comment: if neither process ever reaches zero, both clocks stay at `⊤`.
      rw [if_neg h, if_neg h']
  have hτdistW :
      IsStoppingTime (Filtration.natural W hWsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    intro i
    exact hDnat i _ (hτdist i)
  -- Proof comment: rewrite the exit clock through the distance process and pull the scalar owner
  -- back along the natural-filtration comparison.
  simpa [hEqτ] using hτdistW

/-- Helper for Theorem 25.40: on a continuous Brownian stage, the exit clock is measurable in the
ambient sample-space sigma algebra. This packages the natural-filtration stopping-time owner into
the plain measurability surface needed by the annulus exit-map constructor. -/
private theorem measurable_stageExit_of_continuous
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U)) :
    Measurable (hittingAfter W Uᶜ 0) := by
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  have hτ :
      IsStoppingTime (Filtration.natural W hWsm) (hittingAfter W Uᶜ 0) :=
    stageExit_isStoppingTime_of_continuous hW hWcont hUo hUcpt
  -- Proof comment: a stopping time becomes an ambient measurable map after forgetting the
  -- stopping-time sigma algebra.
  exact hτ.measurable.mono hτ.measurableSpace_le le_rfl

/-- Helper for Theorem 25.40: on a continuous Brownian stage, the stopped exit position is
measurable. This isolates the progressive-measurability bookkeeping before building the annulus
frontier-valued exit map. -/
private theorem measurable_stageStoppedValue_of_continuous
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U)) :
    Measurable (stoppedValue W (hittingAfter W Uᶜ 0)) := by
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  have hτ :
      IsStoppingTime (Filtration.natural W hWsm) (hittingAfter W Uᶜ 0) :=
    stageExit_isStoppingTime_of_continuous hW hWcont hUo hUcpt
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hWprog :
      ProgMeasurable (Filtration.natural W hWsm) W :=
    hWstrong.progMeasurable_of_continuous hWcont
  -- Proof comment: progressive measurability of the Brownian stage and the stopping-time owner
  -- give measurability of the stopped exit position.
  exact (measurable_stoppedValue hWprog hτ).mono hτ.measurableSpace_le le_rfl

/-- Helper for Theorem 25.40: a continuous Brownian motion started at an interior annulus point
admits a measurable frontier-valued annulus exit map. This isolates the exit-data packaging from
the remaining fixed-start exit-expectation identity. -/
private theorem centeredAnnulusExitData_ofContinuousStartedAt
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State} {ρ R : ℝ}
    (hx0 : x0 ∈ concentricAnnulus (0 : State) ρ R)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hWcStart : ∀ ω : Ω, Wc 0 ω = x0)
    (hr : 0 < ρ) (hR : ρ < R) :
    ∃ exitValue : Ω → frontier (concentricAnnulus (0 : State) ρ R),
      Measurable exitValue ∧
        (∀ ω : Ω, hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤ →
          (exitValue ω : State) =
            stoppedValue Wc (hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0) ω) := by
  let G : Set State := concentricAnnulus (0 : State) ρ R
  have hG : IsOpen G := by
    simpa [G] using concentricAnnulus_isOpen (0 : State) ρ R
  have hGcpt : IsCompact (closure G) := by
    simpa [G] using isCompact_closure_concentricAnnulus (d := d) (y := (0 : State)) hr hR
  have hτmeas : Measurable (hittingAfter Wc Gᶜ 0) :=
    measurable_stageExit_of_continuous hWc hWcCont hG hGcpt
  have hStoppedMeas : Measurable (stoppedValue Wc (hittingAfter Wc Gᶜ 0)) :=
    measurable_stageStoppedValue_of_continuous hWc hWcCont hG hGcpt
  have hInnerSphere : (Metric.sphere (0 : State) ρ).Nonempty := by
    let h : (Metric.sphere (0 : State) ρ).Nonempty ↔ 0 ≤ ρ :=
      NormedSpace.sphere_nonempty
    exact h.2 hr.le
  have hFrontier : (frontier G).Nonempty := by
    rcases hInnerSphere with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [G, concentricAnnulusFrontier_eq (d := d) (y := (0 : State)) hr hR] using Or.inl hz
  have hStart : ∀ ω : Ω, Wc 0 ω ∈ G := by
    intro ω
    simpa [G, hWcStart ω] using hx0
  -- Proof comment: once the clock and the stopped value are measurable, the existing generic
  -- frontier-exit packager applies directly to the centered annulus.
  exact
    existsMeasurableFrontierExitValue_ofContinuousPaths
      (G := G) (W := Wc) hFrontier hG hτmeas hStoppedMeas hWcCont hStart

omit [NeZero d] in
/-- Helper for Theorem 25.40: compact closure gives a deterministic uniform bound for a Dirichlet
solution on `closure G`. This is the domination input needed for the later annulus-exit limit
argument. -/
private theorem existsAbsLeOnClosure
    {G : Set State} {f : frontier G → ℝ} {u : State → ℝ}
    (hGcpt : IsCompact (closure G)) (hu : SolvesDirichletProblem G f u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure G, |u z| ≤ C := by
  have hImageCompact : IsCompact (u '' closure G) :=
    hGcpt.image_of_continuousOn hu.continuousOn_closure
  rcases hImageCompact.bddBelow with ⟨l, hl⟩
  rcases hImageCompact.bddAbove with ⟨r, hr⟩
  refine ⟨max |l| |r|, by positivity, ?_⟩
  intro z hz
  have hzImage : u z ∈ u '' closure G := ⟨z, hz, rfl⟩
  have hlz : l ≤ u z := hl hzImage
  have hrz : u z ≤ r := hr hzImage
  -- Proof comment: compactness bounds the image of `u`, so the larger endpoint controls the
  -- absolute value on the whole closed domain.
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc
      -max |l| |r| ≤ -|l| := neg_le_neg (le_max_left |l| |r|)
      _ ≤ l := neg_abs_le l
      _ ≤ u z := hlz
  · calc
      u z ≤ r := hrz
      _ ≤ |r| := le_abs_self r
      _ ≤ max |l| |r| := le_max_right |l| |r|

omit [NeZero d] in
/-- Helper for Theorem 25.40: a continuous path that hits a closed target by finite time actually
lands in that target at its hitting time. This local owner is placed before the annulus-exit
support lemmas so they do not depend on later file order. -/
private theorem mem_closedSet_at_hittingAfter_of_lt_top_local
    {A : Set State} {W : VectorProcess} {ω : Ω}
    (hAclosed : IsClosed A)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hτ : hittingAfter W A 0 ω < ⊤) :
    W (hittingAfter W A 0 ω).untopA ω ∈ A := by
  have hτ_ne_top : hittingAfter W A 0 ω ≠ ⊤ := ne_of_lt hτ
  let hitSet : Set NNReal := {t : NNReal | W t ω ∈ A}
  have hHitExists : ∃ t : NNReal, W t ω ∈ A := by
    simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hτ_ne_top
    rcases hτ_ne_top with ⟨t, _, htA⟩
    exact ⟨t, htA⟩
  have hHitNonempty : hitSet.Nonempty := by
    rcases hHitExists with ⟨t, htA⟩
    exact ⟨t, htA⟩
  have hHitClosed : IsClosed hitSet := by
    change IsClosed ((fun t : NNReal ↦ W t ω) ⁻¹' A)
    exact hAclosed.preimage hcont
  have hHitBddBelow : BddBelow hitSet := ⟨0, fun _ _ ↦ bot_le⟩
  have hsInf_mem : sInf hitSet ∈ hitSet :=
    hHitClosed.csInf_mem hHitNonempty hHitBddBelow
  have hτ_eq : (hittingAfter W A 0 ω).untopA = sInf hitSet := by
    rw [hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ A} = hitSet by
            ext t
            simp [hitSet]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hHitExists with ⟨t, htA⟩
      exact ⟨t, bot_le, htA⟩
  simpa [hitSet, hτ_eq] using hsInf_mem

omit [NeZero d] in
/-- Helper for Theorem 25.40: for an open stage `U`, a continuous path started in `U` reaches the
closure of `U` at its finite exit time from `U`. -/
private theorem mem_closure_at_exit_of_lt_top
    {U : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤) :
    W (hittingAfter W Uᶜ 0 ω).untopA ω ∈ closure U := by
  let τU : NNReal := (hittingAfter W Uᶜ 0 ω).untopA
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  have hτ_mem : W τU ω ∈ Uᶜ := by
    -- Proof comment: the finite exit point lies in the closed complement by the closed-target
    -- hitting-time owner already available in this file.
    simpa [τU] using
      mem_closedSet_at_hittingAfter_of_lt_top_local
        (A := Uᶜ)
        (hAclosed := isClosed_compl_iff.mpr hUo)
        hcont
        hτ
  have hτ_pos : 0 < τU := by
    by_contra hτ_pos
    have hτ_zero : τU = 0 := le_antisymm (le_of_not_gt hτ_pos) bot_le
    have hW0_mem : W 0 ω ∈ Uᶜ := by
      simpa [hτ_zero] using hτ_mem
    exact hW0_mem hStart
  have hτ_coe : ((τU : NNReal) : WithTop NNReal) = hittingAfter W Uᶜ 0 ω := by
    rw [show τU = (hittingAfter W Uᶜ 0 ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hτ_ne_top]
    exact WithTop.coe_untop _ _
  have hLeftU : ∀ s : NNReal, s < τU → W s ω ∈ U := by
    intro s hs
    have hs_lt_hit : (s : WithTop NNReal) < hittingAfter W Uᶜ 0 ω := by
      rw [← hτ_coe]
      exact_mod_cast hs
    have hs_not_mem :
        W s ω ∉ Uᶜ :=
      notMem_of_lt_hittingAfter
        (u := W) (s := Uᶜ) (n := (0 : NNReal)) (ω := ω) hs_lt_hit (by simp)
    simpa using hs_not_mem
  rw [mem_closure_iff]
  intro o ho hτo
  have hPreimage : {s : NNReal | W s ω ∈ o} ∈ 𝓝 τU := by
    exact hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds ho hτo)
  rcases mem_nhds_iff.mp hPreimage with ⟨u, hu_subset, hu_open, hτu⟩
  have hτ_leftClosure : τU ∈ closure (Set.Iio τU : Set NNReal) := by
    have hclosureIio : closure (Set.Iio τU : Set NNReal) = Set.Iic τU :=
      closure_Iio' ⟨0, hτ_pos⟩
    rw [hclosureIio]
    simp
  rcases (mem_closure_iff.mp hτ_leftClosure) u hu_open hτu with ⟨s, hs_mem_u, hs_lt⟩
  -- Proof comment: every neighborhood of the exit point contains earlier path values still in
  -- `U`, so the exit point lies in `closure U`.
  exact ⟨W s ω, hu_subset hs_mem_u, hLeftU s hs_lt⟩

omit [NeZero d] in
/-- Helper for Theorem 25.40: the finite stopped exit value lies in `closure U`. This is the
`stoppedValue` spelling of the previous exit-point statement. -/
private theorem stoppedValue_mem_closure_at_exit_of_lt_top
    {U : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤) :
    stoppedValue W (hittingAfter W Uᶜ 0) ω ∈ closure U := by
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  -- Proof comment: under finite exit, `stoppedValue` is definitionally the path value at the
  -- concrete exit time.
  simpa [stoppedValue, hτ_ne_top] using
    mem_closure_at_exit_of_lt_top
      (U := U) (W := W) (ω := ω) hUo hcont hStart hτ

omit [NeZero d] in
/-- Helper for Theorem 25.40: once the exit time from `U` is finite, the stage-stopped path is
eventually constant along the deterministic integer horizons. -/
private theorem tendsto_stageStoppedProcess_nat_to_stoppedValue
    {W : VectorProcess} {U : Set State} {ω : Ω}
    (hτfin : hittingAfter W Uᶜ 0 ω < ⊤) :
    Tendsto
      (fun n : ℕ ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω)
      atTop
      (𝓝 (stoppedValue W (hittingAfter W Uᶜ 0) ω)) := by
  have hEventuallyEq :
      (fun n : ℕ ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω) =ᶠ[atTop]
        fun _ ↦ stoppedValue W (hittingAfter W Uᶜ 0) ω := by
    filter_upwards
        [tendsto_natCast_atTop_atTop.eventually_ge_atTop
          ((hittingAfter W Uᶜ 0 ω).untopA)] with n hn
    have hτn : hittingAfter W Uᶜ 0 ω ≤ (n : ENNReal) :=
      (WithTop.untopA_le_iff
        (x := hittingAfter W Uᶜ 0 ω) (hx := ne_top_of_lt hτfin)).1 hn
    -- Proof comment: once the deterministic horizon dominates the finite exit time, the stopped
    -- path has already frozen at the terminal exit value.
    simpa [stoppedValue] using
      (stoppedProcess_eq_of_ge
        (u := W) (τ := hittingAfter W Uᶜ 0) (ω := ω) (i := (n : NNReal)) hτn)
  exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds

omit [NeZero d] in
/-- Helper for Theorem 25.40: composing the stage-stopped path with a continuous function
preserves the deterministic-horizon convergence to the terminal stopped value. -/
private theorem tendsto_stageStoppedExtension_nat_to_stoppedValue
    {W : VectorProcess} {U : Set State} {F : State → ℝ} {ω : Ω}
    (hτfin : hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F) :
    Tendsto
      (fun n : ℕ ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω))
      atTop
      (𝓝 (F (stoppedValue W (hittingAfter W Uᶜ 0) ω))) := by
  -- Proof comment: the stage-stopped path is eventually constant, so continuity of `F`
  -- transports the limit to the terminal stopped value.
  exact hFcont.continuousAt.tendsto.comp <|
    tendsto_stageStoppedProcess_nat_to_stoppedValue (W := W) (U := U) hτfin

omit [NeZero d] in
/-- Helper for Theorem 25.40: if `closure U ⊆ V`, then every deterministic-horizon stop
`W_{R ∧ τ_{Uᶜ}}` stays inside `V`. This is the geometric bridge needed for the later uniform
closure bound. -/
private theorem stageStoppedProcess_mem_buffer
    {U V : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hUV : closure U ⊆ V)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤)
    (R : NNReal) :
    stoppedProcess W (hittingAfter W Uᶜ 0) R ω ∈ V := by
  let τU : NNReal := (hittingAfter W Uᶜ 0 ω).untopA
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  have hτ_coe : ((τU : NNReal) : WithTop NNReal) = hittingAfter W Uᶜ 0 ω := by
    rw [show τU = (hittingAfter W Uᶜ 0 ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hτ_ne_top]
    exact WithTop.coe_untop _ _
  by_cases hRτ : R < τU
  · have hStopped :
        stoppedProcess W (hittingAfter W Uᶜ 0) R ω = W R ω := by
      apply stoppedProcess_eq_of_le
      rw [← hτ_coe]
      exact le_of_lt (by exact_mod_cast hRτ)
    have hInside : W R ω ∈ U := by
      have hRt : (R : WithTop NNReal) < hittingAfter W Uᶜ 0 ω := by
        rw [← hτ_coe]
        exact_mod_cast hRτ
      have hNot :
          W R ω ∉ Uᶜ :=
        notMem_of_lt_hittingAfter
          (u := W) (s := Uᶜ) (n := (0 : NNReal)) (ω := ω) hRt (by simp)
      simpa using hNot
    -- Proof comment: before the exit time, the deterministic stop is still inside `U`, hence
    -- inside every buffer containing `closure U`.
    rw [hStopped]
    exact hUV (subset_closure hInside)
  · have hτR : τU ≤ R := le_of_not_gt hRτ
    have hStopped :
        stoppedProcess W (hittingAfter W Uᶜ 0) R ω = W τU ω := by
      apply stoppedProcess_eq_of_ge
      rw [← hτ_coe]
      exact_mod_cast hτR
    have hExitClosure :
        W τU ω ∈ closure U := by
      simpa [τU] using
        mem_closure_at_exit_of_lt_top
          (U := U)
          hUo
          hcont
          hStart
          hτ
    -- Proof comment: once the deterministic cap reaches the exit time, the stopped path is the
    -- actual exit point, which belongs to `closure U ⊆ V`.
    rw [hStopped]
    exact hUV hExitClosure

/-- Helper for Theorem 25.40: after recentering the continuous Brownian modification at `x0` and
patching only the time-zero value, adding `x0` back recovers the original path at every time
outside one null set. -/
private theorem stageTranslatedPatchedBrownian_ae_allTimes_eq_original
    (μ : ProbabilityMeasure Ω)
    {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x0 + B t ω = Wc t ω := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), Wc 0 ω = x0 :=
    brownianVectorStart_ae_eq_const (μ := μ) hWc
  filter_upwards [hStartAe] with ω hω t
  by_cases ht : t = 0
  · subst ht
    -- Proof comment: at time `0`, the patch sets `B 0` to `0`, so adding `x0` back gives the
    -- deterministic Brownian start point.
    simpa [B, hω]
  · -- Proof comment: away from time `0`, the recentering is exactly cancelled by adding `x0`.
    simpa [B, ht, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

omit [NeZero d] in
/-- Helper for Theorem 25.40: stopping preserves continuity of `State`-valued sample paths. This
keeps the later stopped-owner transport at the path level instead of repeatedly unfolding
`stoppedProcess`. -/
private theorem continuous_stoppedVectorProcess_of_continuous
    {X : VectorProcess} {σ : Ω → ENNReal} {ω : Ω}
    (hXCont : Continuous fun t : NNReal ↦ X t ω) :
    Continuous fun t : NNReal ↦ stoppedProcess X σ t ω := by
  have hfinite : ∀ t : NNReal, min (t : ENNReal) (σ ω) ≠ ⊤ := fun t ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  let clipped : NNReal → {s : ENNReal | s ≠ ⊤} := fun t ↦
    ⟨min (t : ENNReal) (σ ω), hfinite t⟩
  have hclipped : Continuous clipped := by
    -- Proof comment: the stopped path is the original path precomposed with the clipped time map.
    exact (ENNReal.continuous_coe.inf continuous_const).subtype_mk hfinite
  have htime : Continuous fun t : NNReal ↦ WithTop.untop (clipped t).1 (clipped t).2 := by
    simpa [clipped] using (WithTop.continuous_untop.comp hclipped)
  have hEq :
      (fun t : NNReal ↦ stoppedProcess X σ t ω) =
        fun t : NNReal ↦ X (WithTop.untop (clipped t).1 (clipped t).2) ω := by
    funext t
    change X ((min (t : ENNReal) (σ ω)).untopA) ω =
      X (WithTop.untop (min (t : ENNReal) (σ ω)) (hfinite t)) ω
    rw [WithTop.untopA_eq_untop (hfinite t)]
    rfl
  rw [hEq]
  exact hXCont.comp htime

omit [NeZero d] in
/-- Helper for Theorem 25.40: if `x0 + B t ω = Wc t ω` holds for every deterministic time, then
the same translation identity also holds after stopping both paths at the same clock. This
packages the only stopped-path transport used by the stochastic core. -/
private theorem translatedPatchedBrownian_stopped_eq_original
    {Wc B : VectorProcess} {τ : Ω → ENNReal} {x0 : State} {ω : Ω}
    (hEq : ∀ t : NNReal, x0 + B t ω = Wc t ω)
    (t : NNReal) :
    x0 + stoppedProcess B τ t ω = stoppedProcess Wc τ t ω := by
  by_cases hτ : τ ω = ⊤
  · -- Proof comment: if the stop never occurs, both stopped paths are the original paths at
    -- time `t`, so the claim is exactly the given translation identity.
    simpa [stoppedProcess, hτ] using hEq t
  · let s : NNReal := (τ ω).untopA
    have hs : ((s : NNReal) : ENNReal) = τ ω := by
      dsimp [s]
      rw [WithTop.untopA_eq_untop hτ]
      exact WithTop.coe_untop _ _
    by_cases ht : s ≤ t
    · -- Proof comment: after the stopping time, both paths are frozen at the common stopped
      -- value, so it suffices to compare them at the frozen time `s`.
      have hτle : τ ω ≤ (t : ENNReal) := by
        rw [← hs]
        exact_mod_cast ht
      have hBstop :
          stoppedProcess B τ t ω = B s ω := by
        simpa [s] using
          (stoppedProcess_eq_of_ge (u := B) (τ := τ) (ω := ω) (i := t) hτle)
      have hWstop :
          stoppedProcess Wc τ t ω = Wc s ω := by
        simpa [s] using
          (stoppedProcess_eq_of_ge (u := Wc) (τ := τ) (ω := ω) (i := t) hτle)
      simpa [hBstop, hWstop] using hEq s
    · -- Proof comment: before the stopping time, both stopped paths still agree with the raw
      -- processes at time `t`.
      have hτgt : t < s := lt_of_not_ge ht
      have htle : (t : ENNReal) ≤ τ ω := by
        rw [← hs]
        exact le_of_lt (by exact_mod_cast hτgt)
      have hBstop :
          stoppedProcess B τ t ω = B t ω := by
        exact stoppedProcess_eq_of_le (u := B) (τ := τ) (ω := ω) (i := t) htle
      have hWstop :
          stoppedProcess Wc τ t ω = Wc t ω := by
        exact stoppedProcess_eq_of_le (u := Wc) (τ := τ) (ω := ω) (i := t) htle
      simpa [hBstop, hWstop] using hEq t

/-- Helper for Theorem 25.40: a harmonic-neighborhood owner already implies pointwise vanishing
of the Laplacian on the owned set. -/
private theorem differentiablePartialDeriv_shiftedConstLift_theorem25_40
    (F : State → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin d) :
    Differentiable ℝ (∂[i] F) := by
  let ei : State := EuclideanSpace.single i (1 : ℝ)
  have hfd :
      ContDiff ℝ 1 (fun y ↦ (fderiv ℝ F y) ei) := by
    -- Proof comment: the coordinate derivative is the Fréchet derivative evaluated on the basis
    -- vector `eᵢ`, so one derivative of `F` already controls this map.
    simpa [ei] using
      ((contDiff_succ_iff_fderiv_apply (𝕜 := ℝ) (D := State) (E := ℝ) (n := 1)
        (f := F)).mp hF).2.2 ei
  -- Proof comment: rewrite the named partial derivative through `fderiv` and use the `C¹`
  -- regularity of that evaluation map.
  simpa [partialDeriv_eq_fderiv_apply F (hF.differentiable (by norm_num)) i] using
    hfd.differentiable_one

/-- Helper for Theorem 25.40: the time-independent translated lift `(z,t) ↦ F (x + z)` is a
`C^{2,1}` function as soon as `F` is `C²` on `State`. -/
private theorem shiftedConstLift_isTimeSpaceC21_theorem25_40
    {F : State → ℝ} {x : State}
    (hF : ContDiff ℝ 2 F) :
    IsTimeSpaceC21_theorem25_40 (fun xt : State × ℝ ↦ F (x + xt.1)) := by
  let G : State → ℝ := fun z ↦ F (x + z)
  have hG : ContDiff ℝ 2 G := by
    -- Proof comment: translation by the fixed base point `x` preserves `C²` regularity.
    simpa [G] using hF.comp ((contDiff_const.add contDiff_id).of_le le_top)
  refine
    { hasDerivAt_time := ?_
      continuous_timePartialDeriv := ?_
      hasDerivAt_space := ?_
      continuous_spacePartialDeriv := ?_
      hasDerivAt_spaceSecond := ?_
      continuous_spaceSecondPartialDeriv := ?_ }
  · intro xt
    -- Proof comment: the translated lift is independent of the time coordinate.
    simpa [G, timePartialDeriv_theorem25_40] using
      (hasDerivAt_const (x := xt.2) (c := G xt.1))
  ·
    have hzero :
        timePartialDeriv_theorem25_40 (fun xt : State × ℝ ↦ F (x + xt.1)) =
          fun _ : State × ℝ ↦ (0 : ℝ) := by
      funext xt
      simp [timePartialDeriv_theorem25_40]
    -- Proof comment: after identifying the time derivative with `0`, continuity is immediate.
    simpa [hzero] using (continuous_const : Continuous fun _ : State × ℝ ↦ (0 : ℝ))
  · intro i xt
    let ei : State := EuclideanSpace.single i (1 : ℝ)
    have hline :
        HasDerivAt
          (fun s : ℝ ↦ xt.1 + (s - xt.1 i) • ei)
          ei
          (xt.1 i) := by
      have hsub :
          HasDerivAt (fun s : ℝ ↦ s - xt.1 i) (1 : ℝ) (xt.1 i) := by
        simpa using (hasDerivAt_id (xt.1 i)).sub_const (xt.1 i)
      -- Proof comment: the spatial coordinate line is an affine map with constant derivative
      -- `eᵢ`.
      simpa [ei, one_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hsub.smul_const ei).const_add xt.1
    have haxis :
        (fun s : ℝ ↦ G (xt.1 + EuclideanSpace.single i (s - xt.1 i))) =
          fun s : ℝ ↦ G (xt.1 + (s - xt.1 i) • ei) := by
      funext s
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj
        simp [ei, EuclideanSpace.single]
      · simp [ei, EuclideanSpace.single, hj]
    have hDiff :
        HasDerivAt
          (fun s : ℝ ↦ G (xt.1 + (s - xt.1 i) • ei))
          ((fderiv ℝ G xt.1) ei)
          (xt.1 i) := by
      -- Proof comment: compose the translated spatial `C²` function with the affine coordinate
      -- line through `xt.1`.
      simpa [ei] using
        (((hG.differentiable (by norm_num) (xt.1 + (xt.1 i - xt.1 i) • ei)).hasFDerivAt).comp
          (xt.1 i) hline.hasFDerivAt).hasDerivAt
    -- Proof comment: the spatial first derivative is computed along the translated coordinate
    -- line, exactly as in the time-independent `C^{2,1}` template.
    simpa [G, haxis, partialDeriv_eq_fderiv_apply G (hG.differentiable (by norm_num)) i] using
      hDiff
  · intro i
    -- Proof comment: the continuous coordinate derivatives of the translated lift are exactly
    -- the coordinate derivatives of the translated spatial function `G`.
    simpa [G, add_assoc] using (continuousPartialDeriv_theorem25_40 G hG i).comp continuous_fst
  · intro i j xt
    let ej : State := EuclideanSpace.single j (1 : ℝ)
    have hGj : Differentiable ℝ (∂[i] G) :=
      differentiablePartialDeriv_shiftedConstLift_theorem25_40 G hG i
    have hline :
        HasDerivAt
          (fun s : ℝ ↦ xt.1 + (s - xt.1 j) • ej)
          ej
          (xt.1 j) := by
      have hsub :
          HasDerivAt (fun s : ℝ ↦ s - xt.1 j) (1 : ℝ) (xt.1 j) := by
        simpa using (hasDerivAt_id (xt.1 j)).sub_const (xt.1 j)
      -- Proof comment: the second coordinate-line differentiation uses the same affine map,
      -- now in the `j`-th direction.
      simpa [ej, one_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hsub.smul_const ej).const_add xt.1
    have haxis :
        (fun s : ℝ ↦ (∂[i] G) (xt.1 + EuclideanSpace.single j (s - xt.1 j))) =
          fun s : ℝ ↦ (∂[i] G) (xt.1 + (s - xt.1 j) • ej) := by
      funext s
      congr 1
      ext k
      by_cases hk : k = j
      · subst hk
        simp [ej, EuclideanSpace.single]
      · simp [ej, EuclideanSpace.single, hk]
    have hDiff :
        HasDerivAt
          (fun s : ℝ ↦ (∂[i] G) (xt.1 + (s - xt.1 j) • ej))
          ((fderiv ℝ (∂[i] G) xt.1) ej)
          (xt.1 j) := by
      -- Proof comment: apply the same affine-line composition argument to the first translated
      -- partial derivative.
      simpa [ej] using
        (((hGj (xt.1 + (xt.1 j - xt.1 j) • ej)).hasFDerivAt).comp
          (xt.1 j) hline.hasFDerivAt).hasDerivAt
    -- Proof comment: the second spatial derivative is the same computation applied to the first
    -- translated partial derivative.
    simpa [G, haxis, secondPartialDeriv_eq_fderiv_apply G i j hGj] using hDiff
  · intro i j
    -- Proof comment: the second translated coordinate derivatives stay continuous because the
    -- translated spatial function `G` is still `C²`.
    simpa [G, add_assoc] using (continuous_secondPartialDeriv G hG i j).comp continuous_fst

/-- Helper for Theorem 25.40: a harmonic-neighborhood owner already implies pointwise vanishing
of the Laplacian on the owned set. -/
private theorem laplacian_eq_zero_on_buffer
    {F : State → ℝ} {V : Set State}
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    {z : State} (hz : z ∈ V) :
    Δ F z = 0 := by
  -- Proof comment: the harmonic-neighborhood API gives an eventual identity `ΔF = 0` around `z`,
  -- so evaluating that neighborhood statement at `z` itself closes the goal.
  exact (hFharm z hz).2.self_of_nhds

/-- Helper for Theorem 25.40: every deterministic-horizon stop of the continuous Brownian stage
stays in the harmonic buffer, so the Laplacian of the extension vanishes there almost surely. -/
private theorem stageStoppedLaplacian_eq_zero
    {μ : ProbabilityMeasure Ω}
    {Wc : VectorProcess} {U V : Set State} {F : State → ℝ} {x : State}
    (hx : x ∈ U)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hτfin : ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Δ F (stoppedProcess Wc (hittingAfter Wc Uᶜ 0) t ω) = 0 := by
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), Wc 0 ω = x :=
    brownianVectorStart_ae_eq_const (μ := μ) hWc
  filter_upwards [hτfin, hStartAe] with ω hωfin hωstart t
  have hStart : Wc 0 ω ∈ U := by
    simpa [hωstart] using hx
  have hmemV :
      stoppedProcess Wc (hittingAfter Wc Uᶜ 0) t ω ∈ V :=
    stageStoppedProcess_mem_buffer
      (U := U) (V := V) (W := Wc) (ω := ω)
      hUo
      (hWcCont ω)
      hStart
      hUV
      hωfin
      t
  -- Proof comment: once the deterministic stop is known to stay in `V`, harmonicity kills the
  -- Laplacian at that stopped point.
  exact laplacian_eq_zero_on_buffer hFharm hmemV

/-- Helper for Theorem 25.40: after recentering and patching the Brownian path, the stopped
Laplacian-zero identity transports from the original path to the shifted stopped spelling used in
the annulus proof. -/
private theorem shiftedStoppedExtension_laplacian_eq_zero
    {μ : ProbabilityMeasure Ω}
    {Wc : VectorProcess} {U V : Set State} {F : State → ℝ} {x : State}
    (hx : x ∈ U)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hτfin : ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Δ F (x + stoppedProcess B (hittingAfter Wc Uᶜ 0) t ω) = 0 := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x
  have hTranslate :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x + B t ω = Wc t ω :=
    stageTranslatedPatchedBrownian_ae_allTimes_eq_original (μ := μ) hWc
  have hStoppedLap :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        Δ F (stoppedProcess Wc (hittingAfter Wc Uᶜ 0) t ω) = 0 :=
    stageStoppedLaplacian_eq_zero
      (μ := μ) (Wc := Wc) (U := U) (V := V) (F := F) (x := x)
      hx hWc hWcCont hUo hUV hτfin hFharm
  filter_upwards [hTranslate, hStoppedLap] with ω hωTranslate hωLap t
  have hStoppedEq :
      x + stoppedProcess B (hittingAfter Wc Uᶜ 0) t ω =
        stoppedProcess Wc (hittingAfter Wc Uᶜ 0) t ω :=
    translatedPatchedBrownian_stopped_eq_original
      (Wc := Wc) (B := B) (τ := hittingAfter Wc Uᶜ 0) (x0 := x) (ω := ω)
      hωTranslate
      t
  -- Proof comment: rewrite the shifted stopped point back to the original stopped Brownian path,
  -- where the vanishing-Laplacian statement is already available.
  rw [hStoppedEq]
  exact hωLap t

/-- Helper for Theorem 25.40: after recentering and patching the Brownian path, evaluating `F`
on the translated stopped path agrees almost surely at every time with evaluating `F` on the
original stopped Brownian path. -/
private theorem shiftedStageStoppedExtension_ae_allTimes_eq_original_theorem25_40
    {μ : ProbabilityMeasure Ω}
    {Wc : VectorProcess} {U : Set State} {F : State → ℝ} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      F (x0 + stoppedProcess B (hittingAfter Wc Uᶜ 0) t ω) =
        F (stoppedProcess Wc (hittingAfter Wc Uᶜ 0) t ω) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  have hTranslate :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x0 + B t ω = Wc t ω :=
    stageTranslatedPatchedBrownian_ae_allTimes_eq_original (μ := μ) hWc
  filter_upwards [hTranslate] with ω hω t
  -- Proof comment: rewrite the shifted stopped path back to the original Brownian stop before
  -- evaluating `F`.
  rw [translatedPatchedBrownian_stopped_eq_original
    (Wc := Wc) (B := B) (τ := hittingAfter Wc Uᶜ 0) (x0 := x0) (ω := ω) hω t]

/-- Helper for Theorem 25.40: after stopping the translated harmonic surface, the drift vanishes
and the translated stopped spelling agrees almost surely at every time with the original stopped
increment. This isolates the exact pathwise identity needed for the remaining martingale step.
-/
private theorem shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
    {μ : ProbabilityMeasure Ω}
    {Wc : VectorProcess} {U V : Set State} {F : State → ℝ} {x0 : State}
    (hx0 : x0 ∈ U)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hτfin : ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Uᶜ 0
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ t ω -
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ s.toNNReal ω) =
        F (stoppedProcess Wc τ t ω) - F x0 := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Uᶜ 0
  have hRewrite :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        F (x0 + stoppedProcess B τ t ω) =
          F (stoppedProcess Wc τ t ω) :=
    shiftedStageStoppedExtension_ae_allTimes_eq_original_theorem25_40
      (μ := μ) (Wc := Wc) (U := U) (F := F) (x0 := x0) hWc
  have hDriftZero :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ s.toNNReal ω) = 0 := by
    have hShiftedLap :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          Δ F (x0 + stoppedProcess B τ t ω) = 0 := by
      -- Proof comment: the stopped translated path stays in the harmonic buffer, so the
      -- Laplacian vanishes pointwise there.
      simpa [B, τ, stoppedProcess] using
        shiftedStoppedExtension_laplacian_eq_zero
          (μ := μ) (Wc := Wc) (U := U) (V := V) (F := F) (x := x0)
          hx0 hWc hWcCont hUo hUV hτfin hFharm
    filter_upwards [hShiftedLap] with ω hω t
    have hIntegrandZero :
        (fun s : ℝ ↦ ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ s.toNNReal ω)) =
          fun _ : ℝ ↦ (0 : ℝ) := by
      funext s
      simp [hω s.toNNReal]
    -- Proof comment: once the translated stopped Laplacian is pointwise zero, the whole drift
    -- integral collapses to the zero function on `[0, t]`.
    rw [hIntegrandZero]
    simp
  have hStoppedRewrite :
      stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ =
        (fun t ω ↦ F (x0 + stoppedProcess B τ t ω) - F x0) := by
    funext t ω
    -- Proof comment: both spellings evaluate `F` at the same clipped translated Brownian state.
    simp [stoppedProcess, B, τ]
  filter_upwards [hRewrite, hDriftZero] with ω hωRewrite hωDrift t
  -- Proof comment: rewrite the stopped translated surface to the explicit stopped-state spelling,
  -- then kill the drift integral and transport back to the original stopped increment.
  rw [hStoppedRewrite, hωDrift t, sub_zero]
  simp [hωRewrite t]

omit [NeZero d] in
/-- Helper for Theorem 25.40: the explicit centered annulus profile is Borel measurable. -/
private theorem measurable_centeredAnnulusProfile {ρ R : ℝ} :
    Measurable (centeredAnnulusProfile (d := d) ρ R) := by
  classical
  unfold centeredAnnulusProfile
  by_cases h1 : d = 1
  · simp [h1]
    measurability
  · by_cases h2 : d = 2
    · simp [h1, h2]
      measurability
    · simp [h1, h2]
      measurability

omit [NeZero d] in
/-- Helper for Theorem 25.40: each deterministic-horizon stopped annulus-profile slice is
almost-everywhere strongly measurable. This is the measurability input for dominated convergence
at integer horizons. -/
private theorem aestronglyMeasurable_centeredAnnulusProfile_stageStopped_atNat
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State} {ρ R : ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (n : ℕ) :
    AEStronglyMeasurable
      (fun ω ↦ centeredAnnulusProfile (d := d) ρ R (stoppedProcess W (hittingAfter W Uᶜ 0) n ω))
      (μ : Measure Ω) := by
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  have hτ :
      IsStoppingTime (Filtration.natural W hWsm) (hittingAfter W Uᶜ 0) :=
    stageExit_isStoppingTime_of_continuous hW hWcont hUo hUcpt
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hWprog :
      ProgMeasurable (Filtration.natural W hWsm) W :=
    hWstrong.progMeasurable_of_continuous hWcont
  have hσ :
      IsStoppingTime
        (Filtration.natural W hWsm)
        (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) :=
    hτ.min_const (n : NNReal)
  have hStoppedMeas :
      Measurable
        (stoppedValue W (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal))) :=
    (measurable_stoppedValue hWprog hσ).mono hσ.measurableSpace_le le_rfl
  have hStoppedEq :
      (fun ω ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω) =
        stoppedValue W (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) := by
    funext ω
    -- Proof comment: the deterministic time slice of a stopped process is the stopped value at
    -- the clipped stopping time `τ ∧ n`.
    simpa [min_comm] using
      (stoppedProcess_eq_stoppedValue_apply
        (u := W) (τ := hittingAfter W Uᶜ 0) (i := (n : NNReal)) ω).symm
  have hMeas :
      Measurable
        (fun ω ↦ centeredAnnulusProfile (d := d) ρ R
          (stoppedProcess W (hittingAfter W Uᶜ 0) n ω)) := by
    have hProfileMeas :
        Measurable (centeredAnnulusProfile (d := d) ρ R) :=
      measurable_centeredAnnulusProfile (d := d) (ρ := ρ) (R := R)
    -- Proof comment: rewrite the deterministic-horizon stopped value through the measurable
    -- clipped stopping time and then compose with the explicit annulus profile.
    simpa [hStoppedEq] using hProfileMeas.comp hStoppedMeas
  exact hMeas.aestronglyMeasurable

/-- Helper for Theorem 25.40: finite sums of local martingales are local martingales. This keeps
the later Itô assembly at the natural finite-sum surface instead of repeatedly reproving the same
induction. -/
private theorem finsetSum_isLocalMartingale
    {μ : Measure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    (s : Finset (Fin d)) {X : Fin d → NNReal → Ω → ℝ}
    (hX : ∀ i ∈ s, IsLocalMartingale ℱ μ (X i)) :
    IsLocalMartingale ℱ μ (fun t ω ↦ ∑ i in s, X i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty finite sum is the zero process, which is a martingale and hence
      -- a local martingale.
      simpa using (MeasureTheory.martingale_zero ℝ ℱ μ).isLocalMartingale
  | @insert i s hi hs =>
      have hiMart : IsLocalMartingale ℱ μ (X i) := hX i (by simp)
      have hsMart : IsLocalMartingale ℱ μ (fun t ω ↦ ∑ j in s, X j t ω) := by
        refine hs ?_
        intro j hj
        exact hX j (by simp [hj])
      -- Proof comment: insert-step local-martingale stability is just additivity together with
      -- the finite-sum normal form.
      simpa [Finset.sum_insert, hi] using hiMart.add hsMart

/-- Helper for Theorem 25.40: finite sums of almost surely continuous processes remain almost
surely continuous. -/
private theorem finsetSum_hasAlmostSurelyContinuousPaths
    {μ : Measure Ω}
    (s : Finset (Fin d)) {X : Fin d → NNReal → Ω → ℝ}
    (hX : ∀ i ∈ s, HasAlmostSurelyContinuousPaths μ (X i)) :
    HasAlmostSurelyContinuousPaths μ (fun t ω ↦ ∑ i in s, X i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sum is the constant-zero path on every sample.
      filter_upwards with ω
      simp [HasAlmostSurelyContinuousPaths, processPath]
  | @insert i s hi hs =>
      have hiCont : HasAlmostSurelyContinuousPaths μ (X i) := hX i (by simp)
      have hsCont : HasAlmostSurelyContinuousPaths μ (fun t ω ↦ ∑ j in s, X j t ω) := by
        refine hs ?_
        intro j hj
        exact hX j (by simp [hj])
      -- Proof comment: continuity of the inserted summand and of the remaining sum combine by
      -- ordinary continuity of addition.
      filter_upwards [hiCont, hsCont] with ω hωi hωs
      simpa [HasAlmostSurelyContinuousPaths, processPath, Finset.sum_insert, hi] using
        hωi.add hωs

/-- Helper for Theorem 25.40: two almost surely continuous modifications agree simultaneously at
all times almost surely. This is the transport step needed before evaluating an Itô decomposition
at the random clipped time `t ∧ τ(ω)`. -/
private theorem ae_all_eq_of_modifications_of_aeContinuous_local
    {μ : Measure Ω}
    {X Y : NNReal → Ω → ℝ}
    (hXY : AreModifications μ X Y)
    (hXcont : HasAlmostSurelyContinuousPaths μ X)
    (hYcont : HasAlmostSurelyContinuousPaths μ Y) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω := by
  have hRat : ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, X (q : NNReal) ω = Y (q : NNReal) ω := by
    rw [ae_all_iff]
    intro q
    simpa using hXY (q : NNReal)
  filter_upwards [hRat, hXcont, hYcont] with ω hωRat hωX hωY t
  have hEqOn :
      Set.EqOn (fun s : NNReal ↦ X s ω) (fun s : NNReal ↦ Y s ω)
        (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    exact hωRat q
  -- Proof comment: rational times are dense in `NNReal`, so equality on the dense set plus
  -- continuity of both sample paths upgrades to equality at every time.
  exact congrFun (Continuous.ext_on nnratDense hωX hωY hEqOn) t

/-- Helper for Theorem 25.40: once the Laplacian vanishes along the stopped path, the associated
deterministic drift primitive is identically zero as well. This isolates the drift-killing step
from the still-missing unstopped Itô owner. -/
private theorem stoppedLaplacianIntegral_eq_zero
    {μ : Measure Ω} {W : VectorProcess} {τ : Ω → ENNReal} {F : State → ℝ}
    (hLap :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        Δ F (stoppedProcess W τ t ω) = 0) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        ((1 : ℝ) / 2) * Δ F (stoppedProcess W τ s.toNNReal ω) = 0 := by
  filter_upwards [hLap] with ω hω t
  have hIntegrandZero :
      (fun s : ℝ ↦ ((1 : ℝ) / 2) * Δ F (stoppedProcess W τ s.toNNReal ω)) =
        fun _ : ℝ ↦ (0 : ℝ) := by
    funext s
    simp [hω s.toNNReal]
  -- Proof comment: after rewriting the integrand to the zero function pointwise, the stopped
  -- drift primitive collapses to the zero integral.
  rw [hIntegrandZero]
  simp

/-- Helper for Theorem 25.40: composing a measurable state observable with a process preserves
strong adaptedness in the natural filtration of that process. -/
private theorem stateComposition_stronglyAdapted_natural_theorem25_40
    {W : VectorProcess} (hWsm : ∀ t : NNReal, StronglyMeasurable (W t))
    {F : State → ℝ} (hFmeas : Measurable F) :
    StronglyAdapted (Filtration.natural W hWsm) (fun t ω ↦ F (W t ω)) := by
  intro t
  have hWt :
      StronglyMeasurable[Filtration.natural W hWsm t] (W t) :=
    Filtration.stronglyAdapted_natural (u := W) hWsm t
  -- Proof comment: each deterministic-time slice factors through the current state `W t ω`
  -- followed by the measurable observable `F`.
  simpa using hFmeas.stronglyMeasurable.comp_measurable hWt.measurable

/-- Helper for Theorem 25.40: enlarging the filtration preserves a continuous local martingale.
This is the transport step needed when a scalar coordinate owner is first built in its own natural
filtration and then used in the recombined vector filtration. -/
private theorem isContinuousLocalMartingale_of_le_filtration_theorem25_40
    {μ : Measure Ω}
    {ℱ 𝒢 : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    (hℱ𝒢 : ℱ ≤ 𝒢)
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    IsContinuousLocalMartingale 𝒢 μ M := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM.local_martingale with ⟨hMadapted, τSeq, hτSeq⟩
  refine
    { local_martingale := ?_
      continuous := hM.continuous }
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hlim, hStopped⟩
  refine (isLocalMartingale_iff 𝒢 μ M).2 ⟨?_, τSeq, ?_⟩
  · intro t
    -- Proof comment: measurability of each deterministic-time slice survives when the ambient
    -- filtration is enlarged.
    exact (hMadapted t).mono (hℱ𝒢 t) le_rfl
  · refine (isLocalizingSequence_iff 𝒢 μ M τSeq).2 ⟨?_, hlim, ?_⟩
    · intro n t
      -- Proof comment: the same localizing sequence remains a sequence of stopping times in the
      -- larger filtration.
      exact (hStopping n t).mono (hℱ𝒢 t) le_rfl
    · intro n
      obtain ⟨hMart, hUI⟩ := hStopped n
      -- Proof comment: each stopped martingale transports across the filtration inclusion while
      -- uniform integrability is measure-theoretic and needs no change.
      exact ⟨martingale_of_le_filtration hℱ𝒢 hMart, hUI⟩

/-- Helper for Theorem 25.40: enlarging the filtration also preserves a chosen continuous
square-variation process. This lets the deterministic Brownian clock move from the scalar natural
filtration to the recombined vector filtration without changing its pathwise meaning. -/
private theorem isContinuousSquareVariationProcess_of_le_filtration_theorem25_40
    {μ : Measure Ω}
    {ℱ 𝒢 : Filtration NNReal ‹MeasurableSpace Ω›}
    {M A : NNReal → Ω → ℝ}
    (hℱ𝒢 : ℱ ≤ 𝒢)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) :
    IsContinuousSquareVariationProcess 𝒢 μ M A := by
  refine
    { zero := hA.zero
      adapted := ?_
      continuous := hA.continuous
      monotone := hA.monotone
      local_martingale_sq_sub := ?_ }
  · intro t
    -- Proof comment: adaptedness of the compensator survives the same filtration inclusion.
    exact (hA.adapted t).mono (hℱ𝒢 t) le_rfl
  · -- Proof comment: the compensated square process is a continuous local martingale in the
    -- smaller filtration, so the previous transport lemma moves it to the larger filtration.
    exact
      isContinuousLocalMartingale_of_le_filtration_theorem25_40
        (μ := μ) hℱ𝒢 hA.local_martingale_sq_sub

/-- Helper for Theorem 25.40: the natural filtration of one coordinate continuous version of the
shifted zero-patched Brownian path is contained in the natural filtration of the recombined vector
continuous version built from all coordinates. -/
private theorem coordinateContinuousVersionNatural_le_shiftedVectorNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let B : Fin d → NNReal → Ω → ℝ :=
      fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
    let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
      fun j ↦
        (brownianVectorStartedAt_zeroPatched_isStandard
          (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
    let Bc : Fin d → NNReal → Ω → ℝ :=
      fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
    let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
    let Bi : NNReal → Ω → ℝ := Bc i
    Filtration.natural Bi
        (by
          intro t
          let hBi :
              IsBrownianMotion (μ : Measure Ω) Bi :=
            brownianContinuousVersion_isBrownianMotion_theorem25_40
              (μ := (μ : Measure Ω)) (B := B i) (hB i)
          simpa [Bi] using hBi.stronglyMeasurable t)
      ≤
      Filtration.natural Bv
        (by
          intro t
          let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
          rw [stronglyMeasurable_iff_measurable]
          have hcoords : Measurable (ψ ∘ Bv t) := by
            refine measurable_pi_lambda _ fun j ↦ ?_
            let hBcj :
                IsBrownianMotion (μ : Measure Ω) (Bc j) :=
              brownianContinuousVersion_isBrownianMotion_theorem25_40
                (μ := (μ : Measure Ω)) (B := B j) (hB j)
            simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
          exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords) := by
  let B : Fin d → NNReal → Ω → ℝ :=
    fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
  let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
    fun j ↦
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
  let Bc : Fin d → NNReal → Ω → ℝ :=
    fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
  let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
  let Bi : NNReal → Ω → ℝ := Bc i
  have hBi_sm : ∀ t : NNReal, StronglyMeasurable (Bi t) := by
    intro t
    let hBi :
        IsBrownianMotion (μ : Measure Ω) Bi :=
      brownianContinuousVersion_isBrownianMotion_theorem25_40
        (μ := (μ : Measure Ω)) (B := B i) (hB i)
    simpa [Bi] using hBi.stronglyMeasurable t
  have hBv_sm : ∀ t : NNReal, StronglyMeasurable (Bv t) := by
    intro t
    let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
    rw [stronglyMeasurable_iff_measurable]
    have hcoords : Measurable (ψ ∘ Bv t) := by
      refine measurable_pi_lambda _ fun j ↦ ?_
      let hBcj :
          IsBrownianMotion (μ : Measure Ω) (Bc j) :=
        brownianContinuousVersion_isBrownianMotion_theorem25_40
          (μ := (μ : Measure Ω)) (B := B j) (hB j)
      simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
    exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords
  have hBi_adapted :
      Adapted (Filtration.natural Bv hBv_sm) Bi := by
    have hCoordStrong :
        StronglyAdapted
          (Filtration.natural Bv hBv_sm)
          (fun t ω ↦ (Bv t ω : State) i) :=
      stateComposition_stronglyAdapted_natural_theorem25_40
        (W := Bv) (hWsm := hBv_sm)
        (F := fun x : State ↦ x i)
        ((continuous_apply i).measurable)
    -- Proof comment: the scalar coordinate process is just the `i`-th projection of the
    -- recombined vector process, so it is adapted to the vector natural filtration.
    simpa [Bi, Bv] using hCoordStrong.adapted
  -- Proof comment: once the coordinate process is adapted to the vector natural filtration, the
  -- defining universal property of natural filtrations gives the desired inclusion.
  exact (adapted_iff_natural_le hBi_sm).mp hBi_adapted

/-- Helper for Theorem 25.40: after transporting across the preceding natural-filtration
inclusion, each coordinate continuous version remains a continuous local martingale in the
recombined shifted-vector filtration. -/
private theorem
    shiftedPatchedBrownianCoordinateContinuousVersion_isContinuousLocalMartingaleShiftedVectorNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let B : Fin d → NNReal → Ω → ℝ :=
      fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
    let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
      fun j ↦
        (brownianVectorStartedAt_zeroPatched_isStandard
          (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
    let Bc : Fin d → NNReal → Ω → ℝ :=
      fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
    let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
    let Bi : NNReal → Ω → ℝ := Bc i
    IsContinuousLocalMartingale
      (Filtration.natural Bv
        (by
          intro t
          let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
          rw [stronglyMeasurable_iff_measurable]
          have hcoords : Measurable (ψ ∘ Bv t) := by
            refine measurable_pi_lambda _ fun j ↦ ?_
            let hBcj :
                IsBrownianMotion (μ : Measure Ω) (Bc j) :=
              brownianContinuousVersion_isBrownianMotion_theorem25_40
                (μ := (μ : Measure Ω)) (B := B j) (hB j)
            simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
          exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords))
      (μ : Measure Ω)
      Bi := by
  let B : Fin d → NNReal → Ω → ℝ :=
    fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
  let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
    fun j ↦
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
  let Bc : Fin d → NNReal → Ω → ℝ :=
    fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
  let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
  let Bi : NNReal → Ω → ℝ := Bc i
  have hNatLe :
      Filtration.natural Bi
        (by
          intro t
          let hBi :
              IsBrownianMotion (μ : Measure Ω) Bi :=
            brownianContinuousVersion_isBrownianMotion_theorem25_40
              (μ := (μ : Measure Ω)) (B := B i) (hB i)
          simpa [Bi] using hBi.stronglyMeasurable t)
      ≤
      Filtration.natural Bv
        (by
          intro t
          let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
          rw [stronglyMeasurable_iff_measurable]
          have hcoords : Measurable (ψ ∘ Bv t) := by
            refine measurable_pi_lambda _ fun j ↦ ?_
            let hBcj :
                IsBrownianMotion (μ : Measure Ω) (Bc j) :=
              brownianContinuousVersion_isBrownianMotion_theorem25_40
                (μ := (μ : Measure Ω)) (B := B j) (hB j)
            simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
          exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords) :=
    coordinateContinuousVersionNatural_le_shiftedVectorNatural_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  have hCoordLocal :
      IsContinuousLocalMartingale
        (Filtration.natural Bi
          (by
            intro t
            let hBi :
                IsBrownianMotion (μ : Measure Ω) Bi :=
              brownianContinuousVersion_isBrownianMotion_theorem25_40
                (μ := (μ : Measure Ω)) (B := B i) (hB i)
            simpa [Bi] using hBi.stronglyMeasurable t))
        (μ : Measure Ω)
        Bi := by
    simpa [Bi, Bc, B, hB] using
      shiftedPatchedBrownianCoordinateContinuousVersion_isContinuousLocalMartingaleNatural_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  -- Proof comment: the coordinate local martingale is first built in its scalar natural
  -- filtration and then transported into the recombined vector natural filtration.
  exact
    isContinuousLocalMartingale_of_le_filtration_theorem25_40
      (μ := (μ : Measure Ω)) hNatLe hCoordLocal

/-- Helper for Theorem 25.40: in the shifted vector natural filtration, each coordinate
continuous version still has the deterministic clock as a square-variation process. This is the
square-variation companion to the transported coordinate local-martingale owner above. -/
private theorem
    shiftedPatchedBrownianCoordinateContinuousVersion_time_isContinuousSquareVariationProcessShiftedVectorNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let B : Fin d → NNReal → Ω → ℝ :=
      fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
    let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
      fun j ↦
        (brownianVectorStartedAt_zeroPatched_isStandard
          (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
    let Bc : Fin d → NNReal → Ω → ℝ :=
      fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
    let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
    let Bi : NNReal → Ω → ℝ := Bc i
    IsContinuousSquareVariationProcess
      (Filtration.natural Bv
        (by
          intro t
          let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
          rw [stronglyMeasurable_iff_measurable]
          have hcoords : Measurable (ψ ∘ Bv t) := by
            refine measurable_pi_lambda _ fun j ↦ ?_
            let hBcj :
                IsBrownianMotion (μ : Measure Ω) (Bc j) :=
              brownianContinuousVersion_isBrownianMotion_theorem25_40
                (μ := (μ : Measure Ω)) (B := B j) (hB j)
            simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
          exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords))
      (μ : Measure Ω)
      Bi
      (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := by
  let B : Fin d → NNReal → Ω → ℝ :=
    fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
  let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
    fun j ↦
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
  let Bc : Fin d → NNReal → Ω → ℝ :=
    fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
  let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
  let Bi : NNReal → Ω → ℝ := Bc i
  have hNatLe :
      Filtration.natural Bi
        (by
          intro t
          let hBi :
              IsBrownianMotion (μ : Measure Ω) Bi :=
            brownianContinuousVersion_isBrownianMotion_theorem25_40
              (μ := (μ : Measure Ω)) (B := B i) (hB i)
          simpa [Bi] using hBi.stronglyMeasurable t)
      ≤
      Filtration.natural Bv
        (by
          intro t
          let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
          rw [stronglyMeasurable_iff_measurable]
          have hcoords : Measurable (ψ ∘ Bv t) := by
            refine measurable_pi_lambda _ fun j ↦ ?_
            let hBcj :
                IsBrownianMotion (μ : Measure Ω) (Bc j) :=
              brownianContinuousVersion_isBrownianMotion_theorem25_40
                (μ := (μ : Measure Ω)) (B := B j) (hB j)
            simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
          exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords) :=
    coordinateContinuousVersionNatural_le_shiftedVectorNatural_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  have hSqNat :
      IsContinuousSquareVariationProcess
        (Filtration.natural Bi
          (by
            intro t
            let hBi :
                IsBrownianMotion (μ : Measure Ω) Bi :=
              brownianContinuousVersion_isBrownianMotion_theorem25_40
                (μ := (μ : Measure Ω)) (B := B i) (hB i)
            simpa [Bi] using hBi.stronglyMeasurable t))
        (μ : Measure Ω)
        Bi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := by
    let hBi : IsBrownianMotion (μ : Measure Ω) Bi :=
      brownianContinuousVersion_isBrownianMotion_theorem25_40
        (μ := (μ : Measure Ω)) (B := B i) (hB i)
    have hSqMart :
        Martingale
          (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ))
          (Filtration.natural Bi
            (by
              intro t
              simpa [Bi] using hBi.stronglyMeasurable t))
          (μ : Measure Ω) :=
      brownian_sq_sub_time_martingale (hB := hBi)
    refine
      { zero := by
          funext ω
          simp
        adapted := adapted_const' _ (fun t : NNReal ↦ (t : ℝ))
        continuous := ?_
        monotone := ?_
        local_martingale_sq_sub := ?_ }
    · intro ω
      -- Proof comment: the deterministic clock remains continuous in the scalar coordinate
      -- filtration as well.
      simpa using continuous_subtype_val
    · intro ω s t hst
      exact_mod_cast hst
    · refine
        { local_martingale :=
            martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_40 hSqMart
          continuous := ?_ }
      intro ω
      -- Proof comment: Brownian continuity makes the compensated square process continuous.
      simpa [Bi, Bc, B] using
        ((_root_.brownianContinuousVersion_continuous
          (μ := (μ : Measure Ω)) (B := B i) (hB i) ω).pow 2).sub continuous_subtype_val
  -- Proof comment: the deterministic Brownian clock is first owned in the scalar natural
  -- filtration and then transported to the recombined shifted-vector filtration.
  exact
    isContinuousSquareVariationProcess_of_le_filtration_theorem25_40
      (μ := (μ : Measure Ω)) hNatLe hSqNat

/-- Helper for Theorem 25.40: in the shifted vector natural filtration, each coordinate
continuous version therefore carries the theorem-local absolutely continuous square-variation
package with unit density. This closes the square-variation side of the fixed-horizon Itô route.
-/
private theorem
    shiftedPatchedBrownianCoordinateContinuousVersion_hasAbsolutelyContinuousSquareVariationShiftedVectorNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let B : Fin d → NNReal → Ω → ℝ :=
      fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
    let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
      fun j ↦
        (brownianVectorStartedAt_zeroPatched_isStandard
          (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
    let Bc : Fin d → NNReal → Ω → ℝ :=
      fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
    let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
    let Bi : NNReal → Ω → ℝ := Bc i
    let hM :
        IsContinuousLocalMartingale
          (Filtration.natural Bv
            (by
              intro t
              let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
              rw [stronglyMeasurable_iff_measurable]
              have hcoords : Measurable (ψ ∘ Bv t) := by
                refine measurable_pi_lambda _ fun j ↦ ?_
                let hBcj :
                    IsBrownianMotion (μ : Measure Ω) (Bc j) :=
                  brownianContinuousVersion_isBrownianMotion_theorem25_40
                    (μ := (μ : Measure Ω)) (B := B j) (hB j)
                simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
              exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords))
          (μ : Measure Ω)
          Bi :=
      shiftedPatchedBrownianCoordinateContinuousVersion_isContinuousLocalMartingaleShiftedVectorNatural_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc i
    HasAbsolutelyContinuousSquareVariation_theorem25_40 Bi hM := by
  let B : Fin d → NNReal → Ω → ℝ :=
    fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
  let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
    fun j ↦
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
  let Bc : Fin d → NNReal → Ω → ℝ :=
    fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
  let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
  let Bi : NNReal → Ω → ℝ := Bc i
  let hM :
      IsContinuousLocalMartingale
        (Filtration.natural Bv
          (by
            intro t
            let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
            rw [stronglyMeasurable_iff_measurable]
            have hcoords : Measurable (ψ ∘ Bv t) := by
              refine measurable_pi_lambda _ fun j ↦ ?_
              let hBcj :
                  IsBrownianMotion (μ : Measure Ω) (Bc j) :=
                brownianContinuousVersion_isBrownianMotion_theorem25_40
                  (μ := (μ : Measure Ω)) (B := B j) (hB j)
              simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
            exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords))
        (μ : Measure Ω)
        Bi :=
    shiftedPatchedBrownianCoordinateContinuousVersion_isContinuousLocalMartingaleShiftedVectorNatural_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  have hA :
      IsContinuousSquareVariationProcess
        (Filtration.natural Bv
          (by
            intro t
            let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
            rw [stronglyMeasurable_iff_measurable]
            have hcoords : Measurable (ψ ∘ Bv t) := by
              refine measurable_pi_lambda _ fun j ↦ ?_
              let hBcj :
                  IsBrownianMotion (μ : Measure Ω) (Bc j) :=
                brownianContinuousVersion_isBrownianMotion_theorem25_40
                  (μ := (μ : Measure Ω)) (B := B j) (hB j)
              simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
            exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords))
        (μ : Measure Ω)
        Bi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) :=
    shiftedPatchedBrownianCoordinateContinuousVersion_time_isContinuousSquareVariationProcessShiftedVectorNatural_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), hA, ?_, ?_⟩
  · -- Proof comment: the unit density is deterministic, so progressive measurability is
    -- immediate in the shifted vector filtration.
    simpa using
      (progMeasurable_const : ProgMeasurable
        (Filtration.natural Bv
          (by
            intro t
            let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
            rw [stronglyMeasurable_iff_measurable]
            have hcoords : Measurable (ψ ∘ Bv t) := by
              refine measurable_pi_lambda _ fun j ↦ ?_
              let hBcj :
                  IsBrownianMotion (μ : Measure Ω) (Bc j) :=
                brownianContinuousVersion_isBrownianMotion_theorem25_40
                  (μ := (μ : Measure Ω)) (B := B j) (hB j)
              simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
            exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords))
        (fun _ _ : Ω ↦ (1 : ℝ)))
  · intro t ω
    -- Proof comment: the transported square variation is still the deterministic clock, so the
    -- integral identity is the same elementary constant-density computation.
    simp

/-- Helper for Theorem 25.40: recombining the coordinatewise continuous versions of the shifted
zero-patched Brownian coordinates gives an everywhere-continuous `State`-valued path. -/
private theorem shiftedPatchedBrownianContinuousVersion_recombinedContinuous_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) :
    let B : Fin d → NNReal → Ω → ℝ :=
      fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
    let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
      fun j ↦
        (brownianVectorStartedAt_zeroPatched_isStandard
          (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
    let Bc : Fin d → NNReal → Ω → ℝ :=
      fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
    let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
    ∀ ω : Ω, Continuous fun t : NNReal ↦ Bv t ω := by
  let B : Fin d → NNReal → Ω → ℝ :=
    fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
  let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
    fun j ↦
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
  let Bc : Fin d → NNReal → Ω → ℝ :=
    fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
  let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
  intro ω
  have hcoords : Continuous (fun t : NNReal ↦ fun j : Fin d ↦ Bc j t ω) := by
    refine continuous_pi fun j ↦ ?_
    -- Proof comment: each recombined coordinate is the canonical continuous Brownian version of
    -- the corresponding zero-patched centered coordinate.
    exact _root_.brownianContinuousVersion_continuous
      (μ := (μ : Measure Ω)) (B := B j) (hB j) ω
  -- Proof comment: continuity in the Euclidean state space is coordinatewise continuity in the
  -- finite product model of `State`.
  simpa [Bv] using (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp hcoords

/-- Helper for Theorem 25.40: the translated coordinate derivatives along the recombined
coordinatewise continuous Brownian surface are progressively measurable in its natural
filtration. -/
private theorem shiftedPatchedBrownianPartialDeriv_progMeasurableShiftedVectorNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    {F : State → ℝ} (hF : ContDiff ℝ 2 F) (i : Fin d) :
    let B : Fin d → NNReal → Ω → ℝ :=
      fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
    let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
      fun j ↦
        (brownianVectorStartedAt_zeroPatched_isStandard
          (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
    let Bc : Fin d → NNReal → Ω → ℝ :=
      fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
    let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
    let hBv_sm : ∀ t : NNReal, StronglyMeasurable (Bv t) := by
      intro t
      let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
      rw [stronglyMeasurable_iff_measurable]
      have hcoords : Measurable (ψ ∘ Bv t) := by
        refine measurable_pi_lambda _ fun j ↦ ?_
        let hBcj :
            IsBrownianMotion (μ : Measure Ω) (Bc j) :=
          brownianContinuousVersion_isBrownianMotion_theorem25_40
            (μ := (μ : Measure Ω)) (B := B j) (hB j)
        simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
      exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords
    ProgMeasurable
      (Filtration.natural Bv hBv_sm)
      (fun t ω ↦ (∂[i] F) (x0 + Bv t ω)) := by
  let B : Fin d → NNReal → Ω → ℝ :=
    fun j t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) j
  let hB : ∀ j : Fin d, IsBrownianMotion (μ : Measure Ω) (B j) :=
    fun j ↦
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion j
  let Bc : Fin d → NNReal → Ω → ℝ :=
    fun j ↦ brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B j) (hB j)
  let Bv : VectorProcess := fun t ω ↦ fun j ↦ Bc j t ω
  let hBv_sm : ∀ t : NNReal, StronglyMeasurable (Bv t) := by
    intro t
    let ψ : State ≃ᵐ (Fin d → ℝ) := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
    rw [stronglyMeasurable_iff_measurable]
    have hcoords : Measurable (ψ ∘ Bv t) := by
      refine measurable_pi_lambda _ fun j ↦ ?_
      let hBcj :
          IsBrownianMotion (μ : Measure Ω) (Bc j) :=
        brownianContinuousVersion_isBrownianMotion_theorem25_40
          (μ := (μ : Measure Ω)) (B := B j) (hB j)
      simpa [Bv] using hBcj.stronglyMeasurable t |>.measurable
    exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords
  have hObsCont : Continuous (fun z : State ↦ (∂[i] F) (x0 + z)) := by
    -- Proof comment: the observable is just the `i`-th partial derivative of `F` precomposed
    -- with translation by `x0`.
    simpa [add_assoc] using
      (continuousPartialDeriv_theorem25_40 F hF i).comp (continuous_const.add continuous_id)
  have hObsStrong :
      StronglyAdapted
        (Filtration.natural Bv hBv_sm)
        (fun t ω ↦ (∂[i] F) (x0 + Bv t ω)) :=
    stateComposition_stronglyAdapted_natural_theorem25_40
      (W := Bv) (hWsm := hBv_sm)
      (F := fun z : State ↦ (∂[i] F) (x0 + z))
      hObsCont.measurable
  have hObsContPath :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ (∂[i] F) (x0 + Bv t ω) := by
    intro ω
    -- Proof comment: compose the continuous sample path of the recombined Brownian surface with
    -- the continuous translated partial-derivative observable.
    exact hObsCont.comp
      (shiftedPatchedBrownianContinuousVersion_recombinedContinuous_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc ω)
  -- Proof comment: continuity upgrades strong adaptedness to progressive measurability.
  exact hObsStrong.progMeasurable_of_continuous hObsContPath

/-- Helper for Theorem 25.40: a continuous adapted process inherits the local-martingale owner of
an all-times almost surely equal model. -/
private theorem isLocalMartingale_congr_ae_allTimes_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N : NNReal → Ω → ℝ}
    (hM : IsLocalMartingale ℱ μ M)
    (hN_adapted : Adapted ℱ N)
    (hN_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω)
    (hMN : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω) :
    IsLocalMartingale ℱ μ N := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨_, τSeq, hτSeq⟩
  refine (isLocalMartingale_iff ℱ μ N).2 ⟨hN_adapted, τSeq, ?_⟩
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hlim, hStopped⟩
  refine (isLocalizingSequence_iff ℱ μ N τSeq).2 ⟨hStopping, hlim, ?_⟩
  intro n
  obtain ⟨hMart, hUI⟩ := hStopped n
  have hStoppedEq :
      ∀ t : NNReal,
        stoppedProcess M (τSeq n) t =ᵐ[μ] stoppedProcess N (τSeq n) t := by
    intro t
    -- Proof comment: compare both stopped processes at the shared clipped time `t ∧ τₙ(ω)`.
    filter_upwards [hMN] with ω hω
    simpa [stoppedProcess] using hω ((min (t : ENNReal) (τSeq n ω)).untopA)
  have hStoppedStrong :
      StronglyAdapted ℱ (stoppedProcess N (τSeq n)) := by
    -- Proof comment: continuity lets the target process retain strong adaptedness after stopping
    -- at the common localizing sequence.
    exact hN_adapted.stronglyAdapted.stoppedProcess hN_cont (hStopping n)
  refine ⟨martingale_congr_ae hMart hStoppedStrong hStoppedEq, ?_⟩
  -- Proof comment: uniform integrability is invariant under deterministic-time almost-sure
  -- equality of the stopped family.
  exact (uniformIntegrable_congr_ae hStoppedEq).1 hUI

/-- Helper for Theorem 25.40: an almost surely continuous local martingale can be patched on one
measurable null set to obtain an everywhere-continuous local martingale modification. -/
private theorem patchAeContinuousLocalMartingaleToEverywhere_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    (hM : IsLocalMartingale ℱ μ M)
    (hMcont : HasAlmostSurelyContinuousPaths μ M) :
    ∃ Mc : NNReal → Ω → ℝ,
      AreModifications μ Mc M ∧
      IsLocalMartingale ℱ μ Mc ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Mc t ω) := by
  let bad : Set Ω := {ω | ¬ Continuous fun t : NNReal ↦ M t ω}
  have hbad_null : μ bad = 0 := by
    simpa [bad, HasAlmostSurelyContinuousPaths, processPath] using (ae_iff.1 hMcont)
  obtain ⟨N, hbad_subset, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hbad_null
  let Mc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else M t ω
  have hMc_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Mc t ω := by
    intro ω
    by_cases hωN : ω ∈ N
    · -- Proof comment: on the measurable exceptional set, the patch is the constant zero path.
      simpa [Mc, hωN] using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
    · have hωcont : Continuous fun t : NNReal ↦ M t ω := by
        by_contra hnot
        have hωbad : ω ∈ bad := by
          simpa [bad] using hnot
        exact hωN (hbad_subset hωbad)
      -- Proof comment: off the measurable hull of the discontinuity event, the patch agrees
      -- literally with the original continuous sample path.
      simpa [Mc, hωN] using hωcont
  have hMc_mod : AreModifications μ Mc M := by
    intro t
    filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hωN
    -- Proof comment: outside the measurable null set, the patch leaves every deterministic-time
    -- slice unchanged.
    simp [Mc, hωN]
  have hMc_all :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = Mc t ω := by
    filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hωN t
    -- Proof comment: the all-times equality is the same null-set comparison, now recorded
    -- uniformly in the deterministic time parameter.
    simp [Mc, hωN]
  have hMc_adapted : Adapted ℱ Mc := by
    intro t
    -- Proof comment: each deterministic-time slice is a measurable piecewise combination of the
    -- constant-zero slice and the original adapted slice.
    change Measurable[ℱ t] (fun ω ↦ if ω ∈ N then 0 else M t ω)
    exact Measurable.ite hN_meas measurable_const (hM.adapted t)
  have hMc_local : IsLocalMartingale ℱ μ Mc :=
    isLocalMartingale_congr_ae_allTimes_theorem25_40
      hM
      hMc_adapted
      hMc_cont
      hMc_all
  exact ⟨Mc, hMc_mod, hMc_local, hMc_cont⟩

/-- Helper for Theorem 25.40: once a continuous local-martingale owner is stopped at `τ`, any
continuous adapted all-times almost surely equal target process is itself a local martingale. -/
private theorem stoppedOwner_transfers_isLocalMartingale_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {N T : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hN : IsLocalMartingale ℱ μ N)
    (hN_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω)
    (hτ : IsStoppingTime ℱ τ)
    (hT_adapted : Adapted ℱ T)
    (hT_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ T t ω)
    (hEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, stoppedProcess N τ t ω = T t ω) :
    IsLocalMartingale ℱ μ T := by
  have hStopped : IsLocalMartingale ℱ μ (stoppedProcess N τ) :=
    isLocalMartingale_stoppedProcess hN hN_cont hτ
  -- Proof comment: after stopping the owner, the all-times almost-sure identity transfers the
  -- local-martingale structure to the target process.
  exact
    isLocalMartingale_congr_ae_allTimes_theorem25_40
      hStopped
      hT_adapted
      hT_cont
      hEq

/-- Helper for Theorem 25.40: stopping commutes with composing `Wc` with `F` and subtracting the
deterministic starting value `F x0`. -/
private theorem stageStoppedExtension_eq_stoppedIncrement_theorem25_40
    {Wc : VectorProcess} {F : State → ℝ} {x0 : State} {τ : Ω → ENNReal} :
    (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0) =
      stoppedProcess (fun t ω ↦ F (Wc t ω) - F x0) τ := by
  -- Proof comment: both spellings evaluate `F` at the same clipped time `t ∧ τ(ω)`.
  funext t ω
  rfl

/-- Helper for Theorem 25.40: once a bounded local martingale is written as a process minus its
initial constant, every deterministic-time slice has expectation equal to that initial value. This
isolates the purely martingale-theoretic part of the stopped annulus argument from the missing
harmonic-owner construction. -/
private theorem expectation_eq_of_bounded_localMartingale_increment
    {μ : ProbabilityMeasure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} {c : ℝ}
    (hLocal : IsLocalMartingale ℱ (μ : Measure Ω) (fun t ω ↦ M t ω - c))
    (hBounded : BoundedInTimeAe (μ : Measure Ω) (fun t ω ↦ M t ω - c))
    (hInitial : M 0 =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ c) :
    ∀ n : ℕ, c = ∫ ω, M n ω ∂(μ : Measure Ω) := by
  intro n
  have hMart :
      Martingale (fun t ω ↦ M t ω - c) ℱ (μ : Measure Ω) :=
    martingale_of_bounded_local_martingale hLocal hBounded
  have hZeroIntegral :
      ∫ ω, M n ω - c ∂(μ : Measure Ω) = 0 := by
    have hConstEq :
        ∫ ω, M n ω - c ∂(μ : Measure Ω) =
          ∫ ω, M 0 ω - c ∂(μ : Measure Ω) := by
      -- Proof comment: boundedness upgrades the local martingale to a genuine martingale, so its
      -- deterministic-time expectations are constant.
      simpa [setIntegral_univ] using
        (hMart.setIntegral_eq
          (show (0 : NNReal) ≤ n by exact zero_le _)
          (s := Set.univ)
          MeasurableSet.univ).symm
    have hInitialZero :
        (fun ω ↦ M 0 ω - c) =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ (0 : ℝ) := by
      filter_upwards [hInitial] with ω hω
      simp [hω]
    calc
      ∫ ω, M n ω - c ∂(μ : Measure Ω) =
          ∫ ω, M 0 ω - c ∂(μ : Measure Ω) :=
        hConstEq
      _ = 0 := by
        rw [integral_congr_ae hInitialZero]
        simp
  have hSliceIntegrable : Integrable (M n) (μ : Measure Ω) := by
    have hAdd :
        Integrable (fun ω ↦ (M n ω - c) + c) (μ : Measure Ω) :=
      (hMart.integrable n).add (integrable_const c)
    have hEq :
        (fun ω ↦ (M n ω - c) + c) = M n := by
      funext ω
      ring
    exact hEq ▸ hAdd
  have hConstIntegrable : Integrable (fun _ : Ω ↦ c) (μ : Measure Ω) :=
    integrable_const c
  have hSub :
      ∫ ω, M n ω - c ∂(μ : Measure Ω) =
        ∫ ω, M n ω ∂(μ : Measure Ω) - ∫ ω, c ∂(μ : Measure Ω) := by
    -- Proof comment: rewrite the increment integral as the difference of the slice integral and
    -- the deterministic starting constant.
    simpa [Pi.sub_apply] using integral_sub hSliceIntegrable hConstIntegrable
  have hConstIntegral : ∫ ω, c ∂(μ : Measure Ω) = c := by
    simp
  linarith [hZeroIntegral, hSub, hConstIntegral]

/-- Helper for Theorem 25.40: on a finite-measure space, a martingale is already a local
martingale via the deterministic localizing sequence `τₙ ≡ n`. -/
private theorem martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_40
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M (fun n _ ↦ (n : ENNReal))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa using
      martingale_uniformIntegrable_stoppedProcess_constTime
        (μ := μ) (ℱ := ℱ) hM (n := (n : NNReal))

/-- Helper for Theorem 25.40: the canonical everywhere-continuous patch of a scalar Brownian
motion is again a Brownian motion. -/
private theorem brownianContinuousVersion_isBrownianMotion_theorem25_40
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (_root_.brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: Brownian motion is characterized by its fixed-time Gaussian law and
  -- covariance, and those deterministic-time data are unchanged under the continuous-version
  -- modification.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    simpa using brownianContinuousVersion_zero (μ := μ) (B := B) hB ω
  · exact
      hB.isGaussianProcess.congr
        (fun t ↦ brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)
  · intro t
    exact
      (integral_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.mean_zero t)
  · intro s t
    exact
      (covariance_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB s)
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.covariance_eq s t)
  · filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Theorem 25.40: a theorem-local absolutely continuous square-variation witness is a
continuous square-variation process whose compensator is given by integrating a progressively
measurable density along time. -/
private def HasAbsolutelyContinuousSquareVariation_theorem25_40
    {μ : Measure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    (M : NNReal → Ω → ℝ)
    (hM : IsContinuousLocalMartingale ℱ μ M) : Prop :=
  ∃ density : NNReal → Ω → NNReal,
    ∃ squareVariation : NNReal → Ω → ℝ,
      IsContinuousSquareVariationProcess ℱ μ M squareVariation ∧
        ProgMeasurable ℱ (fun t ω ↦ (density t ω : ℝ)) ∧
        ∀ t : NNReal, ∀ ω : Ω,
          squareVariation t ω =
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (density s.toNNReal ω : ℝ)

/-- Helper for Theorem 25.40: the centered coordinate in the natural filtration of `Wc` already
fits the theorem-local absolutely-continuous square-variation interface with unit density. -/
private theorem centeredCoordinate_hasAbsolutelyContinuousSquareVariation_naturalWc_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let hZi : IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    HasAbsolutelyContinuousSquareVariation_theorem25_40 Zi hZi := by
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let hPair :=
    centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i
  let hZi : IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi := hPair.1
  have hSq :
      IsContinuousSquareVariationProcess
        ℱWc
        (μ : Measure Ω)
        Zi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := hPair.2
  refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), hSq, ?_, ?_⟩
  · -- Proof comment: the bracket density is the deterministic constant `1`, so progressive
    -- measurability is immediate on the theorem-local square-variation interface.
    simpa using
      (progMeasurable_const : ProgMeasurable ℱWc (fun _ _ : Ω ↦ (1 : ℝ)))
  · intro t ω
    -- Proof comment: the chosen square variation is still the deterministic clock, so the
    -- integral identity is the constant-density computation `∫_0^t 1 ds = t`.
    simp [Real.volume_Icc]

/-- Helper for Theorem 25.40: each coordinate of the zero-patched centered Brownian path has the
standard continuous-version local-martingale owner in its own natural filtration. -/
private theorem
    shiftedPatchedBrownianCoordinateContinuousVersion_isContinuousLocalMartingaleNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let B : NNReal → Ω → ℝ :=
      fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
    let hB : IsBrownianMotion (μ : Measure Ω) B :=
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion i
    let Bc : NNReal → Ω → ℝ :=
      brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B) hB
    let hBc : IsBrownianMotion (μ : Measure Ω) Bc :=
      brownianContinuousVersion_isBrownianMotion_theorem25_40
        (μ := (μ : Measure Ω)) (B := B) hB
    IsContinuousLocalMartingale
      (Filtration.natural Bc hBc.stronglyMeasurable)
      (μ : Measure Ω)
      Bc := by
  let B : NNReal → Ω → ℝ :=
    fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
  let hB : IsBrownianMotion (μ : Measure Ω) B :=
    (brownianVectorStartedAt_zeroPatched_isStandard
      (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion i
  let Bc : NNReal → Ω → ℝ :=
    _root_.brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B) hB
  let hBc : IsBrownianMotion (μ : Measure Ω) Bc :=
    brownianContinuousVersion_isBrownianMotion_theorem25_40
      (μ := (μ : Measure Ω)) (B := B) hB
  let ℱc := Filtration.natural Bc hBc.stronglyMeasurable
  have hMart : Martingale Bc ℱc (μ : Measure Ω) :=
    brownianMartingale_natural (μ := (μ : Measure Ω)) (B := Bc) hBc
  -- Proof comment: after recentering and patching time `0`, the coordinate is an ordinary scalar
  -- Brownian motion, so its canonical continuous patch is a martingale in its own natural
  -- filtration and hence a continuous local martingale on the finite probability space.
  refine
    { local_martingale :=
        martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_40 hMart
      continuous := ?_ }
  intro ω
  simpa [Bc] using
    _root_.brownianContinuousVersion_continuous
      (μ := (μ : Measure Ω)) (B := B) hB ω

/-- Helper for Theorem 25.40: the same coordinate continuous version has deterministic time as its
canonical square variation, hence an absolutely continuous square-variation witness. -/
private theorem
    shiftedPatchedBrownianCoordinateContinuousVersion_hasAbsolutelyContinuousSquareVariationNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let B : NNReal → Ω → ℝ :=
      fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
    let hB : IsBrownianMotion (μ : Measure Ω) B :=
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion i
    let Bc : NNReal → Ω → ℝ :=
      brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B) hB
    let hBc : IsBrownianMotion (μ : Measure Ω) Bc :=
      brownianContinuousVersion_isBrownianMotion_theorem25_40
        (μ := (μ : Measure Ω)) (B := B) hB
    let ℱc := Filtration.natural Bc hBc.stronglyMeasurable
    let hM : IsContinuousLocalMartingale ℱc (μ : Measure Ω) Bc :=
      shiftedPatchedBrownianCoordinateContinuousVersion_isContinuousLocalMartingaleNatural_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc i
    HasAbsolutelyContinuousSquareVariation_theorem25_40 Bc hM := by
  let B : NNReal → Ω → ℝ :=
    fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
  let hB : IsBrownianMotion (μ : Measure Ω) B :=
    (brownianVectorStartedAt_zeroPatched_isStandard
      (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion i
  let Bc : NNReal → Ω → ℝ :=
    _root_.brownianContinuousVersion (μ := (μ : Measure Ω)) (B := B) hB
  let hBc : IsBrownianMotion (μ : Measure Ω) Bc :=
    brownianContinuousVersion_isBrownianMotion_theorem25_40
      (μ := (μ : Measure Ω)) (B := B) hB
  let ℱc := Filtration.natural Bc hBc.stronglyMeasurable
  let hM : IsContinuousLocalMartingale ℱc (μ : Measure Ω) Bc :=
    shiftedPatchedBrownianCoordinateContinuousVersion_isContinuousLocalMartingaleNatural_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  have hA :
      IsContinuousSquareVariationProcess
        (μ := (μ : Measure Ω))
        ℱc
        Bc
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := by
    have hSqMart :
        Martingale (fun t ω ↦ Bc t ω ^ 2 - (t : ℝ)) ℱc (μ : Measure Ω) :=
      brownian_sq_sub_time_martingale (hB := hBc)
    -- Proof comment: the compensated square of Brownian motion is a martingale, so the
    -- deterministic clock is a valid square-variation process for the continuous patch.
    refine
      { zero := by
          funext ω
          simp
        adapted := adapted_const' ℱc (fun t : NNReal ↦ (t : ℝ))
        continuous := ?_
        monotone := ?_
        local_martingale_sq_sub := ?_ }
    · intro ω
      simpa using continuous_subtype_val
    · intro ω s t hst
      exact_mod_cast hst
    · refine
        { local_martingale :=
            martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_40 hSqMart
          continuous := ?_ }
      intro ω
      simpa [Bc] using
        ((_root_.brownianContinuousVersion_continuous
          (μ := (μ : Measure Ω)) (B := B) hB ω).pow 2).sub continuous_subtype_val
  refine
    ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), hA, ?_, ?_⟩
  · -- Proof comment: the bracket density is the deterministic constant `1`, so progressive
    -- measurability is immediate.
    simpa using
      (progMeasurable_const : ProgMeasurable ℱc (fun _ _ : Ω ↦ (1 : ℝ)))
  · intro t ω
    -- Proof comment: the chosen square variation is literally the deterministic clock, whose
    -- density on `[0,t]` is the constant function `1`.
    simp [Real.volume_Icc]

/-- Helper for Theorem 25.40: if every deterministic horizon stop of a continuous adapted process
is a martingale, then the process is a continuous local martingale. -/
private theorem isContinuousLocalMartingale_of_constStoppedMartingale_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {Y : NNReal → Ω → ℝ}
    (hY_adapted : Adapted ℱ Y)
    (hY_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω)
    (hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱ μ) :
    IsContinuousLocalMartingale ℱ μ Y := by
  refine
    { local_martingale := ?_
      continuous := hY_cont }
  refine (isLocalMartingale_iff ℱ μ Y).2 ⟨hY_adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ Y (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    -- Proof comment: deterministic horizons are stopping times.
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    -- Proof comment: the deterministic localizing sequence `n` increases to `∞`.
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    have hMart :
        Martingale (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ :=
      hStopped n
    have hUI :
        UniformIntegrable
          (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          1
          μ := by
      have hDet :
          Martingale
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ ∧
            UniformIntegrable
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) 1 μ :=
        martingaleUniformIntegrable_stoppedProcessConstTime
          (ℱ := ℱ)
          (μ := μ)
          (X := stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          hMart
          (n : NNReal)
      -- Proof comment: stopping again at the same deterministic horizon does not change the
      -- process, so the uniform integrability descends to the original deterministic stop.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hDet.2
    exact ⟨hMart, hUI⟩

/-- Helper for Theorem 25.40: the natural filtration of the pointwise-zero patched centered
coordinate is contained in the natural filtration of the ambient Brownian vector process `Wc`. -/
private theorem pointwiseZeroCoordinateNatural_le_brownianNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
    Filtration.natural Bi
        (by
          intro t
          by_cases ht : t = 0
          · simp [Bi, ht]
          ·
            have hcoord :
                Measurable (fun ω : Ω ↦ Wc t ω i - x0 i) :=
              (((continuous_apply i).measurable.comp
                (brownianVectorStartedAt_stronglyMeasurable hWc t).measurable).sub
                measurable_const)
            simpa [Bi, ht] using hcoord.stronglyMeasurable)
      ≤
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc) := by
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
  have hBi_sm : ∀ t : NNReal, StronglyMeasurable (Bi t) := by
    intro t
    by_cases ht : t = 0
    · simp [Bi, ht]
    ·
      have hcoord :
          Measurable (fun ω : Ω ↦ Wc t ω i - x0 i) :=
        (((continuous_apply i).measurable.comp
          (brownianVectorStartedAt_stronglyMeasurable hWc t).measurable).sub
          measurable_const)
      simpa [Bi, ht] using hcoord.stronglyMeasurable
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hBi_adapted : Adapted ℱWc Bi := by
    have hcoordStrong :
        StronglyAdapted ℱWc (fun t ω ↦ Wc t ω i - x0 i) := by
      intro t
      have hslice :
          StronglyMeasurable[ℱWc t] (Wc t) :=
        Filtration.stronglyAdapted_natural
          (u := Wc) (brownianVectorStartedAt_stronglyMeasurable hWc) t
      exact
        ((((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).sub
          measurable_const).stronglyMeasurable)
    intro t
    by_cases ht : t = 0
    · simpa [Bi, ht] using
        (stronglyMeasurable_const : StronglyMeasurable[ℱWc t] fun _ : Ω ↦ (0 : ℝ)).measurable
    · simpa [Bi, ht] using (hcoordStrong t).measurable
  -- Proof comment: once every deterministic-time slice of the scalar coordinate process is
  -- adapted to the ambient Brownian filtration, the natural-filtration universal property gives
  -- the desired inclusion.
  exact (adapted_iff_natural_le hBi_sm).mp hBi_adapted

/-- Helper for Theorem 25.40: the zero-patched centered coordinate differs from the raw centered
coordinate only at time `0`, and Brownian motion started at `x0` already hits that value almost
surely. -/
private theorem centeredCoordinate_zeroPatched_eq_ae_allTimes_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, Bi t ω = Zi t ω := by
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), Wc 0 ω = x0 :=
    brownianVectorStart_ae_eq_const (μ := μ) hWc
  filter_upwards [hStartAe] with ω hω t
  by_cases ht : t = 0
  · -- Proof comment: at time `0`, the zero patch agrees with the raw centered coordinate because
    -- Brownian motion starts from `x0` almost surely.
    subst ht
    simp [Bi, Zi, hω]
  · -- Proof comment: away from time `0`, the zero patch is definitionally the centered
    -- coordinate.
    simp [Bi, Zi, ht]

/-- Helper for Theorem 25.40: the compensated square of the zero-patched centered coordinate
agrees almost surely at every deterministic time with the compensated square of the raw centered
coordinate. -/
private theorem centeredCoordinate_compensatedSquare_zeroPatched_eq_ae_allTimes_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Bi t ω ^ 2 - (t : ℝ) = Zi t ω ^ 2 - (t : ℝ) := by
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
  filter_upwards
      [centeredCoordinate_zeroPatched_eq_ae_allTimes_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc i] with ω hω t
  -- Proof comment: once the coordinates agree pointwise, the compensated squares agree by the
  -- same deterministic algebra.
  rw [hω t]

/-- Helper for Theorem 25.40: in the natural filtration of `Wc`, each centered coordinate
`t ↦ Wc t ω i - x0 i` is a continuous local martingale with deterministic time as square
variation. -/
private theorem centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi ∧
      IsContinuousSquareVariationProcess
        ℱWc
        (μ : Measure Ω)
        Zi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := by
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else Wc t ω - x0) i
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hBi : IsBrownianMotion (μ : Measure Ω) Bi := by
    -- Proof comment: patching the time-zero value of the centered coordinate produces the
    -- standard Brownian coordinate used to access the canonical martingale owners.
    simpa [Bi] using
      (brownianVectorStartedAt_zeroPatched_isStandard
        (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc).isBrownianMotion i
  have hBiNatLe :
      Filtration.natural Bi hBi.stronglyMeasurable ≤ ℱWc := by
    simpa [Bi, ℱWc] using
      pointwiseZeroCoordinateNatural_le_brownianNatural_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  have hBiMartNat :
      Martingale Bi (Filtration.natural Bi hBi.stronglyMeasurable) (μ : Measure Ω) :=
    brownianMartingale_natural (μ := (μ : Measure Ω)) (B := Bi) hBi
  have hBiLocal :
      IsLocalMartingale ℱWc (μ : Measure Ω) Bi :=
    martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_40
      (martingale_of_le_filtration hBiNatLe hBiMartNat)
  have hZi_adapted : Adapted ℱWc Zi := by
    have hcoordStrong :
        StronglyAdapted ℱWc Zi := by
      intro t
      have hslice :
          StronglyMeasurable[ℱWc t] (Wc t) :=
        Filtration.stronglyAdapted_natural
          (u := Wc) (brownianVectorStartedAt_stronglyMeasurable hWc) t
      exact
        ((((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).sub
          measurable_const).stronglyMeasurable)
    exact hcoordStrong.adapted
  have hZi_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Zi t ω := by
    intro ω
    -- Proof comment: the centered coordinate is the continuous Brownian coordinate minus the
    -- deterministic starting value.
    simpa [Zi] using ((EuclideanSpace.proj i).continuous.comp (hWcCont ω)).sub continuous_const
  have hBiEqZi :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, Bi t ω = Zi t ω := by
    -- Proof comment: use the dedicated zero-patch bridge so the local-martingale transport stays
    -- in one canonical spelling.
    simpa [Bi, Zi] using
      centeredCoordinate_zeroPatched_eq_ae_allTimes_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc i
  have hZi_local :
      IsLocalMartingale ℱWc (μ : Measure Ω) Zi :=
    isLocalMartingale_congr_ae_allTimes_theorem25_40
      hBiLocal
      hZi_adapted
      hZi_cont
      hBiEqZi
  have hZi_sq_local :
      IsLocalMartingale
        ℱWc
        (μ : Measure Ω)
        (fun t ω ↦ Zi t ω ^ 2 - (t : ℝ)) := by
    have hBiSqMartNat :
        Martingale
          (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ))
          (Filtration.natural Bi hBi.stronglyMeasurable)
          (μ : Measure Ω) :=
      brownian_sq_sub_time_martingale (μ := (μ : Measure Ω)) (B := Bi) hBi
    have hBiSqLocal :
        IsLocalMartingale
          ℱWc
          (μ : Measure Ω)
          (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ)) :=
      martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_40
        (martingale_of_le_filtration hBiNatLe hBiSqMartNat)
    have hZiSq_adapted :
        Adapted ℱWc (fun t ω ↦ Zi t ω ^ 2 - (t : ℝ)) := by
      simpa [pow_two] using
        (hZi_adapted.mul hZi_adapted).sub
          (adapted_const' ℱWc (fun t : NNReal ↦ (t : ℝ)))
    have hZiSq_cont :
        ∀ ω : Ω, Continuous fun t : NNReal ↦ Zi t ω ^ 2 - (t : ℝ) := by
      intro ω
      -- Proof comment: the compensated square is continuous because both the coordinate path and
      -- the deterministic time clock are continuous.
      simpa [pow_two] using (hZi_cont ω).mul (hZi_cont ω) |>.sub continuous_subtype_val
    have hBiSqEqZiSq :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          Bi t ω ^ 2 - (t : ℝ) = Zi t ω ^ 2 - (t : ℝ) := by
      -- Proof comment: reuse the extracted compensated-square bridge instead of rebuilding the
      -- same time-zero case split locally.
      simpa [Bi, Zi] using
        centeredCoordinate_compensatedSquare_zeroPatched_eq_ae_allTimes_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) hWc i
    exact
      isLocalMartingale_congr_ae_allTimes_theorem25_40
        hBiSqLocal
        hZiSq_adapted
        hZiSq_cont
        hBiSqEqZiSq
  have hZi_contLocal :
      IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi := by
    exact ⟨hZi_local, hZi_cont⟩
  refine ⟨hZi_contLocal, ?_⟩
  refine
    { zero := by
        funext ω
        simp
      adapted := adapted_const' ℱWc (fun t : NNReal ↦ (t : ℝ))
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · intro ω
    -- Proof comment: the deterministic time clock is continuous on `NNReal`.
    simpa using continuous_subtype_val
  · intro ω s t hst
    exact_mod_cast hst
  · refine
      { local_martingale := hZi_sq_local
        continuous := ?_ }
    intro ω
    -- Proof comment: the compensated square of the centered coordinate is continuous because the
    -- coordinate path and the deterministic clock are continuous.
    simpa [Zi, pow_two] using
      (((EuclideanSpace.proj i).continuous.comp (hWcCont ω)).sub continuous_const).mul
        (((EuclideanSpace.proj i).continuous.comp (hWcCont ω)).sub continuous_const) |>.sub
        continuous_subtype_val

/-- Helper for Theorem 25.40: every deterministic horizon stop of the visible stopped harmonic
increment is a martingale once the translated stopped-surface assembly is available. This isolates
the remaining fixed-horizon stochastic blocker from the later local-martingale reconstruction. -/
private theorem visibleStoppedIncrement_constStop_boundedInTimeAe_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcont : Continuous F)
    (T : NNReal) :
    BoundedInTimeAe
      (μ : Measure Ω)
      (stoppedProcess
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)
        (fun _ ↦ (T : ENNReal))) := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  have hClosureBound :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure G, |F z| ≤ C := by
    have hImageCompact : IsCompact (F '' closure G) :=
      hGcpt.image_of_continuousOn hFcont.continuousOn
    rcases hImageCompact.bddBelow with ⟨l, hl⟩
    rcases hImageCompact.bddAbove with ⟨r, hr⟩
    refine ⟨max |l| |r|, by positivity, ?_⟩
    intro z hz
    have hzImage : F z ∈ F '' closure G := ⟨z, hz, rfl⟩
    have hlz : l ≤ F z := hl hzImage
    have hrz : F z ≤ r := hr hzImage
    -- Proof comment: compactness bounds the image of `F` on `closure G`, so the larger endpoint
    -- controls the absolute value of every stopped sample value.
    refine abs_le.mpr ⟨?_, ?_⟩
    · calc
        -max |l| |r| ≤ -|l| := neg_le_neg (le_max_left |l| |r|)
        _ ≤ l := neg_abs_le l
        _ ≤ F z := hlz
    · calc
        F z ≤ r := hrz
        _ ≤ |r| := le_abs_self r
        _ ≤ max |l| |r| := le_max_right |l| |r|
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), Wc 0 ω = x0 :=
    brownianVectorStart_ae_eq_const (μ := μ) hWc
  rcases hClosureBound with ⟨C, hCnonneg, hC⟩
  refine ⟨C + |F x0|, ?_⟩
  filter_upwards [hExitFinite, hStartAe] with ω hωfin hωstart t
  have hStart : Wc 0 ω ∈ G := by
    simpa [hωstart] using hx0
  have hmem :
      stoppedProcess Wc τ (min t T) ω ∈ closure G :=
    stageStoppedProcess_mem_buffer
      (U := G) (V := closure G) (W := Wc) (ω := ω)
      hGo
      (hWcCont ω)
      hStart
      (by intro z hz; exact hz)
      hωfin
      (min t T)
  -- Proof comment: the outer deterministic stop only evaluates the already bounded stopped
  -- Brownian increment at the clipped horizon `min t T`.
  calc
    |stoppedProcess
        (fun s ω ↦ F (stoppedProcess Wc τ s ω) - F x0)
        (fun _ ↦ (T : ENNReal)) t ω|
        = |F (stoppedProcess Wc τ (min t T) ω) - F x0| := by
            simp [τ, stoppedProcessConstTime_eq_min]
    _ ≤ |F (stoppedProcess Wc τ (min t T) ω)| + |F x0| := by
          simpa [sub_eq_add_neg, abs_neg] using
            (abs_add_le (F (stoppedProcess Wc τ (min t T) ω)) (-F x0))
    _ ≤ C + |F x0| := add_le_add (hC _ hmem) le_rfl

/-- Helper for Theorem 25.40: the original deterministic-horizon stopped increment is strongly
adapted to the natural filtration of `Wc`. This is the measurable target used when the shifted
deterministic stop is rewritten back to an owner of the visible increment. -/
private theorem visibleStoppedIncrement_constStop_stronglyAdapted_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcont : Continuous F)
    (T : NNReal) :
    StronglyAdapted
      (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
      (stoppedProcess
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)
        (fun _ ↦ (T : ENNReal))) := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hτstop : IsStoppingTime ℱWc τ :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := Wc) (U := G) (x := x0) hWc hWcCont hGo hExitFinite
  have hRawStrong :
      StronglyAdapted ℱWc (fun t ω ↦ F (Wc t ω) - F x0) := by
    intro t
    -- Proof comment: each deterministic-time slice is the measurable observable `F` composed
    -- with the Brownian state at time `t`, followed by subtraction of the constant `F x0`.
    exact
      ((stateComposition_stronglyAdapted_natural_theorem25_40
          (hWsm := brownianVectorStartedAt_stronglyMeasurable hWc)
          (hFmeas := hFcont.measurable)) t).sub stronglyMeasurable_const
  have hRawCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (Wc t ω) - F x0 := by
    intro ω
    simpa using (hFcont.comp (hWcCont ω)).sub continuous_const
  have hStoppedStrong :
      StronglyAdapted ℱWc (stoppedProcess (fun t ω ↦ F (Wc t ω) - F x0) τ) :=
    hRawStrong.stoppedProcess hRawCont hτstop
  have hTargetAdapted :
      Adapted ℱWc (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0) := by
    -- Proof comment: normalize the visible increment to the stopped-raw-process spelling before
    -- reading off adaptedness from the stopping-time API.
    simpa [τ, stageStoppedExtension_eq_stoppedIncrement_theorem25_40
      (Wc := Wc) (F := F) (x0 := x0) (τ := τ)] using hStoppedStrong.adapted
  intro t
  have hBase :
      Measurable[ℱWc t]
        (fun ω ↦ F (stoppedProcess Wc τ (min t T) ω) - F x0) := by
    exact (hTargetAdapted (min t T)).mono (ℱWc.mono (min_le_left _ _)) le_rfl
  -- Proof comment: the outer deterministic stop only evaluates the already adapted visible
  -- increment at the clipped time `min t T`.
  simpa [stoppedProcessConstTime_eq_min] using hBase.stronglyMeasurable

/-- Helper for Theorem 25.40: once the clipped deterministic horizon `c` is positive, the shifted
stopped surface is either zero on the event `τ = 0` or exactly the original stopped increment.
This pointwise normal form is the measurability bridge for the translated deterministic stop. -/
private theorem shiftedStoppedExtension_value_eq_if_exitAtZero_theorem25_40
    {Wc : VectorProcess} {G : Set State} {F : State → ℝ} {x0 : State}
    {ω : Ω} {c : NNReal} (hc : c ≠ 0) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    F (x0 + stoppedProcess B τ c ω) - F x0 =
      if τ ω = 0 then 0 else F (stoppedProcess Wc τ c ω) - F x0 := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let s : NNReal := WithTop.untopA (min (c : ENNReal) (τ ω))
  have hs_eq :
      ((s : NNReal) : ENNReal) = min (c : ENNReal) (τ ω) := by
    have hmin_ne_top : min (c : ENNReal) (τ ω) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    have hs_def : s = WithTop.untop (min (c : ENNReal) (τ ω)) hmin_ne_top := by
      simpa [s] using
        (WithTop.untopA_eq_untop (a := min (c : ENNReal) (τ ω)) hmin_ne_top)
    calc
      ((s : NNReal) : ENNReal) =
          ((WithTop.untop (min (c : ENNReal) (τ ω)) hmin_ne_top : NNReal) : ENNReal) := by
            rw [hs_def]
      _ = min (c : ENNReal) (τ ω) := WithTop.coe_untop _ _
  by_cases hτ0 : τ ω = 0
  · have hs_zero : s = 0 := by
      exact_mod_cast (by simpa [hτ0] using hs_eq)
    have hStopB0 : stoppedProcess B τ c ω = 0 := by
      rw [show stoppedProcess B τ c ω = B s ω by simp [s, τ, stoppedProcess]]
      simp [B, hs_zero]
    -- Proof comment: if the exit clock has already hit `0`, the stopped shifted path is frozen
    -- at the patched origin, so the translated surface vanishes.
    calc
      F (x0 + stoppedProcess B τ c ω) - F x0 = F (x0 + 0) - F x0 := by rw [hStopB0]
      _ = 0 := by simp
      _ = if τ ω = 0 then 0 else F (stoppedProcess Wc τ c ω) - F x0 := by simp [hτ0]
  · have hc0 : (c : ENNReal) ≠ 0 := by
      exact_mod_cast hc
    have hc_pos : 0 < (c : ENNReal) := bot_lt_iff_ne_bot.mpr hc0
    have hτ_pos : 0 < τ ω := bot_lt_iff_ne_bot.mpr hτ0
    have hs_ne_zero : s ≠ 0 := by
      intro hs_zero
      have hmin_zero : min (c : ENNReal) (τ ω) = 0 := by
        exact hs_eq.symm.trans (by simpa [hs_zero] using (rfl : ((s : NNReal) : ENNReal) = 0))
      have : 0 < min (c : ENNReal) (τ ω) := lt_min hc_pos hτ_pos
      exact (ne_of_gt this) hmin_zero
    have hStopB : stoppedProcess B τ c ω = B s ω := by
      simp [B, s, τ, stoppedProcess]
    have hStopW : stoppedProcess Wc τ c ω = Wc s ω := by
      simp [s, τ, stoppedProcess]
    -- Proof comment: away from the exceptional event `τ = 0`, the clipped time is nonzero, so
    -- the shifted patch is literally `Wc - x0` at the common stopped time.
    calc
      F (x0 + stoppedProcess B τ c ω) - F x0
          = F (x0 + B s ω) - F x0 := by rw [hStopB]
      _ = F (Wc s ω) - F x0 := by
            have hShift : x0 + B s ω = Wc s ω := by
              simpa [B, hs_ne_zero] using add_sub_cancel_left x0 (Wc s ω)
            rw [hShift]
      _ = F (stoppedProcess Wc τ c ω) - F x0 := by rw [hStopW]
      _ = if τ ω = 0 then 0 else F (stoppedProcess Wc τ c ω) - F x0 := by simp [hτ0]

/-- Helper for Theorem 25.40: the translated deterministic stop is strongly adapted once the
visible deterministic stop is known to be strongly adapted. This isolates the `τ = 0` slice
analysis from the later martingale transports. -/
private theorem shiftedTranslatedSurface_constStop_stronglyAdapted_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcont : Continuous F)
    (T : NNReal) :
    StronglyAdapted
      (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
      (stoppedProcess
        (stoppedProcess
          (fun t ω ↦ F (x0 + (if t = 0 then 0 else Wc t ω - x0)) - F x0)
          (hittingAfter Wc Gᶜ 0))
        (fun _ ↦ (T : ENNReal))) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hOrigStrong :
      StronglyAdapted
        ℱWc
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
          (fun _ ↦ (T : ENNReal))) :=
    visibleStoppedIncrement_constStop_stronglyAdapted_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
      hWc hWcCont hGo hExitFinite hFcont T
  have hτstop : IsStoppingTime ℱWc τ :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := Wc) (U := G) (x := x0) hWc hWcCont hGo hExitFinite
  intro t
  let c : NNReal := min t T
  by_cases hc : c = 0
  · have hZeroSlice :
        stoppedProcess
            (stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t =
          fun _ : Ω ↦ 0 := by
      funext ω
      have hInner0 :
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ 0 ω = 0 := by
        simp [B, τ, stoppedProcess]
      -- Proof comment: when the clipped deterministic time is `0`, the translated stop has not
      -- moved from the patched origin, so the whole slice is the zero random variable.
      calc
        stoppedProcess
            (stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t ω
            = stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ 0 ω := by
                simp [stoppedProcessConstTime_eq_min, c, hc]
        _ = 0 := hInner0
    rw [hZeroSlice]
    simpa using
      (stronglyMeasurable_const : StronglyMeasurable[ℱWc t] fun _ : Ω ↦ (0 : ℝ))
  · have hSlice :
        stoppedProcess
            (stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t =
          fun ω ↦ if τ ω = 0 then 0 else
            stoppedProcess
              (fun s ω ↦ F (stoppedProcess Wc τ s ω) - F x0)
              (fun _ ↦ (T : ENNReal)) t ω := by
      funext ω
      have hValue :
          F (x0 + stoppedProcess B τ c ω) - F x0 =
            if τ ω = 0 then 0 else F (stoppedProcess Wc τ c ω) - F x0 :=
        shiftedStoppedExtension_value_eq_if_exitAtZero_theorem25_40
          (Wc := Wc) (G := G) (F := F) (x0 := x0) (ω := ω) (c := c) hc
      -- Proof comment: for positive clipped time, the translated slice is either the zero
      -- branch on `τ = 0` or the visible deterministic stop at the same clipped time.
      simpa [B, τ, c, stoppedProcessConstTime_eq_min, stoppedProcess] using hValue
    rw [hSlice]
    have hTauZero :
        MeasurableSet[ℱWc t] {ω | τ ω = 0} := by
      exact hτstop.measurableSet_eq_le (i := 0) (j := t) (by exact zero_le t)
    exact
      (Measurable.ite hTauZero measurable_const (hOrigStrong t).measurable).stronglyMeasurable

/-- Helper for Theorem 25.40: once an owner of the visible stopped increment is available, the
translated deterministic stop is already a martingale. This isolates the final transport step from
the still-missing owner construction. -/
private theorem shiftedTranslatedSurface_constStop_martingale_of_originalOwner_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcont : Continuous F)
    {Nc : NNReal → Ω → ℝ}
    (hNc_local :
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        Nc)
    (hNc_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Nc t ω)
    (hNc_mod :
      AreModifications
        (μ : Measure Ω)
        Nc
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (stoppedProcess
            (fun t ω ↦ F (x0 + (if t = 0 then 0 else Wc t ω - x0)) - F x0)
            (hittingAfter Wc Gᶜ 0))
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω) := by
  intro T
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hShiftStrong :
      StronglyAdapted
        ℱWc
        (stoppedProcess
          (stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ)
          (fun _ ↦ (T : ENNReal))) :=
    shiftedTranslatedSurface_constStop_stronglyAdapted_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
      hWc hWcCont hGo hExitFinite hFcont T
  have hOrigCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (stoppedProcess Wc τ t ω) - F x0 := by
    intro ω
    have hStoppedCont :
        Continuous fun t : NNReal ↦ stoppedProcess Wc τ t ω :=
      continuous_stoppedVectorProcess_of_continuous
        (X := Wc) (σ := τ) (ω := ω) (hWcCont ω)
    -- Proof comment: the stopped state path stays continuous, so composing with `F` and
    -- subtracting the deterministic start value preserves continuity pathwise.
    simpa using (hFcont.comp hStoppedCont).sub continuous_const
  have hOwnerOrig :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        Nc t ω = F (stoppedProcess Wc τ t ω) - F x0 :=
    ae_all_eq_of_modifications_of_aeContinuous_local
      hNc_mod
      (Filter.Eventually.of_forall hNc_cont)
      (Filter.Eventually.of_forall hOrigCont)
  have hOrigBounded :
      BoundedInTimeAe
        (μ : Measure Ω)
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
          (fun _ ↦ (T : ENNReal))) :=
    visibleStoppedIncrement_constStop_boundedInTimeAe_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
      hx0 hWc hWcCont hGo hGcpt hExitFinite hFcont T
  have hOwnerStopEqOrigAll :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess Nc (fun _ ↦ (T : ENNReal)) t ω =
          stoppedProcess
            (fun s ω ↦ F (stoppedProcess Wc τ s ω) - F x0)
            (fun _ ↦ (T : ENNReal)) t ω := by
    filter_upwards [hOwnerOrig] with ω hω t
    simpa [stoppedProcessConstTime_eq_min] using hω (min t T)
  have hOwnerBounded :
      BoundedInTimeAe
        (μ : Measure Ω)
        (stoppedProcess Nc (fun _ ↦ (T : ENNReal))) := by
    rcases hOrigBounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [hC, hOwnerStopEqOrigAll] with ω hωBound hωEq t
    simpa [hωEq t] using hωBound t
  have hOwnerMart :
      Martingale
        (stoppedProcess Nc (fun _ ↦ (T : ENNReal)))
        ℱWc
        (μ : Measure Ω) := by
    have hOwnerStoppedLocal :
        IsLocalMartingale ℱWc (μ : Measure Ω)
          (stoppedProcess Nc (fun _ ↦ (T : ENNReal))) :=
      isLocalMartingale_stoppedProcess hNc_local hNc_cont (isStoppingTime_const ℱWc T)
    -- Proof comment: boundedness upgrades the owner's deterministic stop from a local
    -- martingale to a genuine martingale.
    exact martingale_of_bounded_local_martingale hOwnerStoppedLocal hOwnerBounded
  have hShiftOrig :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω =
          F (stoppedProcess Wc τ t ω) - F x0 := by
    filter_upwards
      [shiftedStageStoppedExtension_ae_allTimes_eq_original_theorem25_40
        (μ := μ) (Wc := Wc) (U := G) (F := F) (x0 := x0) hWc] with ω hω t
    -- Proof comment: on the all-times translation event, the shifted stopped surface is exactly
    -- the original stopped increment.
    simpa [B, τ, stoppedProcess] using congrArg (fun z : ℝ ↦ z - F x0) (hω t)
  have hStopEqAll :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess Nc (fun _ ↦ (T : ENNReal)) t ω =
          stoppedProcess
            (stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t ω := by
    filter_upwards [hOwnerOrig, hShiftOrig] with ω hωOwner hωShift t
    calc
      stoppedProcess Nc (fun _ ↦ (T : ENNReal)) t ω = Nc (min t T) ω := by
        simp [stoppedProcessConstTime_eq_min]
      _ = F (stoppedProcess Wc τ (min t T) ω) - F x0 := hωOwner (min t T)
      _ = stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ (min t T) ω := by
        exact (hωShift (min t T)).symm
      _ =
          stoppedProcess
            (stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t ω := by
              simp [stoppedProcessConstTime_eq_min]
  have hStopEq :
      ∀ t : NNReal,
        stoppedProcess Nc (fun _ ↦ (T : ENNReal)) t =ᵐ[(μ : Measure Ω)]
          stoppedProcess
            (stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t := by
    intro t
    filter_upwards [hStopEqAll] with ω hω
    exact hω t
  -- Proof comment: once the owner's deterministic stop is a martingale and the shifted stop is
  -- strongly adapted, timewise almost-sure equality transports the martingale property.
  exact martingale_congr_ae hOwnerMart hShiftStrong hStopEq

/-- Helper for Theorem 25.40: once the visible stopped increment already has a continuous local
martingale owner, every deterministic horizon stop is a martingale. This isolates the remaining
blocker to owner construction rather than fixed-horizon transport. -/
private theorem visibleStoppedIncrement_constStop_martingale_of_originalOwner_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    {Nc : NNReal → Ω → ℝ}
    (hNc_local :
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        Nc)
    (hNc_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Nc t ω)
    (hNc_mod :
      AreModifications
        (μ : Measure Ω)
        Nc
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  have hStoppedSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ t ω -
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ s.toNNReal ω) =
          F (stoppedProcess Wc τ t ω) - F x0 := by
    -- Proof comment: the translated stopped surface minus its Itô drift already rewrites back to
    -- the visible stopped increment at every deterministic time almost surely.
    simpa [B, τ] using
      shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
        (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x0 := x0)
        hx0 hWc hWcCont hGo hGV hExitFinite hFharm
  intro T
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hDriftZero :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ s.toNNReal ω) = 0 := by
    -- Proof comment: harmonicity kills the stopped Laplacian drift on the translated surface.
    simpa [B, τ, stoppedProcess] using
      stoppedLaplacianIntegral_eq_zero
        (μ := (μ : Measure Ω))
        (W := fun t ω ↦ x0 + B t ω)
        (τ := τ)
        (F := F)
        (by
          simpa [B, τ, stoppedProcess] using
            shiftedStoppedExtension_laplacian_eq_zero
              (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x := x0)
              hx0 hWc hWcCont hGo hGV hExitFinite hFharm)
  have hTargetStrong :
      StronglyAdapted
        ℱWc
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
          (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: deterministic stopping preserves strong adaptedness of the visible target.
    simpa [τ, ℱWc] using
      visibleStoppedIncrement_constStop_stronglyAdapted_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff.continuous T
  have hEq :
      ∀ t : NNReal,
        stoppedProcess
            (stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t =ᵐ[(μ : Measure Ω)]
          stoppedProcess
            (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
            (fun _ ↦ (T : ENNReal)) t := by
    intro t
    filter_upwards [hStoppedSurface, hDriftZero] with ω hωSurface hωDrift
    have hAtMin := hωSurface (min t T)
    have hDriftAtMin := hωDrift (min t T)
    -- Proof comment: compare both deterministic stops at the clipped time `min t T`, then remove
    -- the already vanishing harmonic drift.
    rw [hDriftAtMin, sub_zero] at hAtMin
    simpa [stoppedProcessConstTime_eq_min] using hAtMin
  have hTranslatedMart :
      Martingale
        (stoppedProcess
          (stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ)
          (fun _ ↦ (T : ENNReal)))
        ℱWc
        (μ : Measure Ω) := by
    -- Proof comment: once an owner of the visible stopped increment is available, the translated
    -- deterministic stop is exactly the earlier owner-transport theorem.
    simpa [B, τ] using
      shiftedTranslatedSurface_constStop_martingale_of_originalOwner_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hx0 hWc hWcCont hGo hGcpt hExitFinite hFcontDiff.continuous
        hNc_local hNc_cont hNc_mod T
  -- Proof comment: once the translated deterministic stop is known to be a martingale, the
  -- visible stopped increment inherits that property by the all-times almost-sure rewrite above.
  exact martingale_congr_ae hTranslatedMart hTargetStrong hEq

/-- Helper for Theorem 25.40: pointwise continuity of scalar coordinate processes is preserved by
finite sums. This keeps the owner-packaging step at the natural finite-sum level. -/
private theorem finsetSum_continuous_theorem25_40
    (s : Finset (Fin d)) {X : Fin d → NNReal → Ω → ℝ}
    (hX : ∀ i ∈ s, ∀ ω : Ω, Continuous fun t : NNReal ↦ X i t ω) :
    ∀ ω : Ω, Continuous fun t : NNReal ↦ ∑ i in s, X i t ω := by
  intro ω
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty finite sum is the constant-zero path.
      simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  | @insert i s hi hs =>
      have hiCont : Continuous fun t : NNReal ↦ X i t ω := hX i (by simp) ω
      have hsCont : Continuous fun t : NNReal ↦ ∑ j in s, X j t ω := by
        refine hs ?_
        intro j hj
        exact hX j (by simp [hj])
      -- Proof comment: continuity of the inserted summand and the recursive tail combines under
      -- addition.
      simpa [Finset.sum_insert, hi] using hiCont.add hsCont

/-- Helper for Theorem 25.40: once the coordinate family is available in the stopped-owner
spelling, the direct translated owner is only finite-sum bookkeeping. -/
private theorem shiftedTranslatedSurface_constLiftIto_of_coordinateFamily_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    {N : Fin d → NNReal → Ω → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hN_local :
      ∀ i : Fin d,
        IsLocalMartingale
          (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
          (μ : Measure Ω)
          (N i))
    (hN_cont : ∀ i : Fin d, ∀ ω : Ω, Continuous fun t : NNReal ↦ N i t ω)
    (hEq :
      let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
      let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun s ω ↦ ∑ i : Fin d, N i s ω) τ t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    ∃ Nc : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        Nc ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Nc t ω) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess Nc τ t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let Nc : NNReal → Ω → ℝ := fun t ω ↦ ∑ i : Fin d, N i t ω
  refine ⟨Nc, ?_, ?_, ?_⟩
  · -- Proof comment: the packaged owner is the finite sum of the coordinate local martingales.
    exact
      finsetSum_isLocalMartingale
        (μ := (μ : Measure Ω))
        (ℱ := Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        Finset.univ
        (fun i _ ↦ hN_local i)
  · -- Proof comment: pointwise continuity packages coordinatewise by the same finite-sum route.
    exact
      finsetSum_continuous_theorem25_40
        (s := Finset.univ)
        (X := N)
        (fun i _ ↦ hN_cont i)
  · -- Proof comment: after naming the finite sum as `Nc`, the coordinate-family identity is
    -- already the required translated owner formula.
    simpa [Nc, B, τ] using hEq

/-- Helper for Theorem 25.40: the visible stopped increment is adapted to the natural filtration
of `Wc`. This isolates the raw-process stopping argument from the still-missing fixed-horizon
martingale bridge. -/
private theorem visibleStoppedIncrement_adapted_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcont : Continuous F) :
    Adapted
      (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
      (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hτstop : IsStoppingTime ℱWc τ :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := Wc) (U := G) (x := x0) hWc hWcCont hGo hExitFinite
  have hRawStrong :
      StronglyAdapted ℱWc (fun t ω ↦ F (Wc t ω) - F x0) := by
    intro t
    -- Proof comment: each deterministic-time slice is the measurable observable `F` composed
    -- with the Brownian state at time `t`, followed by subtraction of the constant `F x0`.
    exact
      ((stateComposition_stronglyAdapted_natural_theorem25_40
          (hWsm := brownianVectorStartedAt_stronglyMeasurable hWc)
          (hFmeas := hFcont.measurable)) t).sub stronglyMeasurable_const
  have hRawCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (Wc t ω) - F x0 := by
    intro ω
    simpa using (hFcont.comp (hWcCont ω)).sub continuous_const
  have hStoppedStrong :
      StronglyAdapted ℱWc (stoppedProcess (fun t ω ↦ F (Wc t ω) - F x0) τ) :=
    hRawStrong.stoppedProcess hRawCont hτstop
  -- Proof comment: normalize the visible increment to the stopped-raw-process spelling before
  -- reading off adaptedness from the stopping-time API.
  simpa [τ, stageStoppedExtension_eq_stoppedIncrement_theorem25_40
    (Wc := Wc) (F := F) (x0 := x0) (τ := τ)] using hStoppedStrong.adapted

/-- Helper for Theorem 25.40: the visible stopped increment has continuous sample paths because
stopping preserves continuity of the Brownian path and `F` is continuous. This is the pathwise
input consumed by the constant-localizer criterion before the fixed-horizon martingale bridge is
invoked. -/
private theorem visibleStoppedIncrement_pathContinuous_theorem25_40
    {Wc : VectorProcess} {x0 : State} {G : Set State} {F : State → ℝ}
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hFcontDiff : ContDiff ℝ 2 F) :
    ∀ ω : Ω, Continuous fun t : NNReal ↦
      F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0 := by
  intro ω
  have hStoppedCont :
      Continuous fun t : NNReal ↦ stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω :=
    continuous_stoppedVectorProcess_of_continuous
      (X := Wc) (σ := hittingAfter Wc Gᶜ 0) (ω := ω) (hWcCont ω)
  -- Proof comment: compose the continuous stopped state path with `F` and subtract the
  -- deterministic base value.
  simpa using (hFcontDiff.continuous.comp hStoppedCont).sub continuous_const

/-- Helper for Theorem 25.40: `EqUpTo μ T X Y` records one measurable null set outside which
`X` and `Y` agree at every deterministic time in `[0,T]`. -/
private def EqUpTo {α : Type _} (μ : Measure Ω) (T : NNReal)
    (X Y : NNReal → Ω → α) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
    ∀ ⦃t : NNReal⦄, t ≤ T → {ω | X t ω ≠ Y t ω} ⊆ N

/-- Helper for Theorem 25.40: equality up to a horizon is reflexive. -/
private theorem eqUpTo_rfl
    {μ : Measure Ω} {α : Type _} (T : NNReal) (X : NNReal → Ω → α) :
    EqUpTo μ T X X := by
  -- Proof comment: a process has no disagreement set with itself.
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht ω hω
  simp at hω

/-- Helper for Theorem 25.40: equality up to a horizon is symmetric. -/
private theorem eqUpTo_sym
    {μ : Measure Ω} {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    EqUpTo μ T Y X := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  exact hN_sub ht (by
    intro hEq
    exact hω hEq.symm)

/-- Helper for Theorem 25.40: equality up to a horizon composes transitively. -/
private theorem eqUpTo_trans
    {μ : Measure Ω} {α : Type _} {T : NNReal}
    {X Y Z : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) (hYZ : EqUpTo μ T Y Z) :
    EqUpTo μ T X Z := by
  rcases hXY with ⟨NXY, hNXY_meas, hNXY_null, hNXY_sub⟩
  rcases hYZ with ⟨NYZ, hNYZ_meas, hNYZ_null, hNYZ_sub⟩
  refine ⟨NXY ∪ NYZ, hNXY_meas.union hNYZ_meas, ?_, ?_⟩
  · have hUnionLe : μ (NXY ∪ NYZ) ≤ μ NXY + μ NYZ := measure_union_le NXY NYZ
    refine le_antisymm ?_ bot_le
    simpa [hNXY_null, hNYZ_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXYω : X t ω ≠ Y t ω
    · exact Set.mem_union_left NYZ (hNXY_sub ht hXYω)
    · have hEqXY : X t ω = Y t ω := not_ne_iff.mp hXYω
      have hYZω : Y t ω ≠ Z t ω := by
        intro hEqYZ
        exact hω (hEqXY.trans hEqYZ)
      exact Set.mem_union_right NXY (hNYZ_sub ht hYZω)

/-- Helper for Theorem 25.40: one `EqUpTo` witness can be read as equality on `[0,T]` outside a
single measurable null set. -/
private theorem eqUpTo_forall_eq
    {μ : Measure Ω} {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
      ∀ ⦃t : NNReal⦄, t ≤ T → ∀ ⦃ω : Ω⦄, ω ∉ N → X t ω = Y t ω := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  by_contra hneq
  exact hω (hN_sub ht hneq)

/-- Helper for Theorem 25.40: finite-horizon equality is stable under addition. -/
private theorem eqUpTo_add
    {μ : Measure Ω} {T : NNReal}
    {X X' Y Y' : NNReal → Ω → ℝ}
    (hX : EqUpTo μ T X X') (hY : EqUpTo μ T Y Y') :
    EqUpTo μ T
      (fun t ω ↦ X t ω + Y t ω)
      (fun t ω ↦ X' t ω + Y' t ω) := by
  rcases hX with ⟨NX, hNX_meas, hNX_null, hNX_sub⟩
  rcases hY with ⟨NY, hNY_meas, hNY_null, hNY_sub⟩
  refine ⟨NX ∪ NY, hNX_meas.union hNY_meas, ?_, ?_⟩
  · have hUnionLe : μ (NX ∪ NY) ≤ μ NX + μ NY := measure_union_le NX NY
    refine le_antisymm ?_ bot_le
    simpa [hNX_null, hNY_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXω : X t ω ≠ X' t ω
    · exact Set.mem_union_left NY (hNX_sub ht hXω)
    · have hEqX : X t ω = X' t ω := not_ne_iff.mp hXω
      have hYω : Y t ω ≠ Y' t ω := by
        intro hEqY
        apply hω
        simpa [hEqX, hEqY]
      exact Set.mem_union_right NX (hNY_sub ht hYω)

/-- Helper for Theorem 25.40: one all-times almost-sure identity gives equality up to every
deterministic horizon. -/
private theorem eqUpTo_of_ae_allTimes
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω) :
    EqUpTo μ T X Y := by
  classical
  let N : Set Ω := {ω | ¬ ∀ t : NNReal, X t ω = Y t ω}
  refine ⟨toMeasurable μ N, measurableSet_toMeasurable _ _, ?_, ?_⟩
  · -- Proof comment: the measurable hull of the exceptional set is still null because the
    -- equality already holds almost surely at every deterministic time.
    rw [measure_toMeasurable]
    simpa [N, ae_iff] using hXY
  · intro t ht ω hω
    exact subset_toMeasurable μ N (by
      change ¬ ∀ s : NNReal, X s ω = Y s ω
      intro hAll
      exact hω (hAll t))

/-- Helper for Theorem 25.40: an indistinguishability witness already gives equality on every
deterministic horizon. This is the transport adapter from the Chapter 25.21 owner API to the
theorem-local `EqUpTo` spelling. -/
private theorem eqUpTo_of_areIndistinguishable_theorem25_40
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : AreIndistinguishable μ X Y) :
    EqUpTo μ T X Y := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  -- Proof comment: the single measurable null set from indistinguishability already controls the
  -- disagreement event at each deterministic time in `[0, T]`.
  exact ⟨N, hN_meas, hN_null, fun _ _ ↦ hN_sub _⟩

/-- Helper for Theorem 25.40: finite sums preserve equality up to a deterministic horizon. -/
private theorem eqUpTo_finsetSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {μ : Measure Ω} {T : NNReal}
    {X Y : ι → NNReal → Ω → ℝ}
    (hXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i)) :
    EqUpTo μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ X i t ω))
      (fun t ω ↦ Finset.sum s (fun i ↦ Y i t ω)) := by
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sums are literally the same zero process.
      simpa using eqUpTo_rfl (μ := μ) T (fun _ _ ↦ (0 : ℝ))
  | @insert a s ha ih =>
      have hsXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i) := by
        intro i hi
        exact hXY i (by simp [hi])
      -- Proof comment: combine the head witness with the recursive tail witness and rewrite both
      -- finite sums into head-plus-tail normal form.
      simpa [Finset.sum_insert, ha] using eqUpTo_add (hXY a (by simp)) (ih hsXY)

/-- Helper for Theorem 25.40: deterministic stopping at `T` turns an `EqUpTo` witness on `[0,T]`
into all-times almost-sure equality of the stopped processes. -/
private theorem ae_eq_stoppedProcess_const_of_eqUpTo
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : EqUpTo μ T X Y) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω =
        stoppedProcess Y (fun _ ↦ (T : ENNReal)) t ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hXY with
    ⟨N, hN_meas, hN_null, hN_eq⟩
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := compl_mem_ae_iff.mpr hN_null
  filter_upwards [hNae] with ω hω t
  -- Proof comment: both stopped processes are read at the clipped time `min t T`, which stays
  -- inside the horizon already controlled by `EqUpTo`.
  simpa [stoppedProcessConstTime_eq_min] using hN_eq (min_le_right t T) hω

/-- Helper for Theorem 25.40: a deterministic bound transfers across an all-times almost-sure
identity. -/
private theorem boundedInTimeAe_of_ae_allTimes_eq_theorem25_40
    {μ : Measure Ω} {X Y : NNReal → Ω → ℝ}
    (hX : BoundedInTimeAe μ X)
    (hEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω) :
    BoundedInTimeAe μ Y := by
  rcases hX with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC, hEq] with ω hωBound hωEq t
  simpa [hωEq t] using hωBound t

/-- Helper for Theorem 25.40: `N` is a continuous local martingale up to `T` if it agrees on
`[0,T]` with some genuine continuous local martingale. -/
private def IsContinuousLocalMartingaleUpTo_theorem25_40
    (ℱ : Filtration NNReal ‹MeasurableSpace Ω›) (μ : Measure Ω)
    (T : NNReal) (N : NNReal → Ω → ℝ) : Prop :=
  ∃ N' : NNReal → Ω → ℝ,
    IsContinuousLocalMartingale ℱ μ N' ∧ EqUpTo μ T N N'

/-- Helper for Theorem 25.40: a genuine continuous local martingale is automatically a witness
up to any deterministic horizon. -/
private theorem isContinuousLocalMartingaleUpTo_of_isContinuousLocalMartingale_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {T : NNReal} {N : NNReal → Ω → ℝ}
    (hN : IsContinuousLocalMartingale ℱ μ N) :
    IsContinuousLocalMartingaleUpTo_theorem25_40 ℱ μ T N := by
  -- Proof comment: keep the same process as the genuine witness and record reflexive equality on
  -- the horizon.
  exact ⟨N, hN, eqUpTo_rfl (μ := μ) T N⟩

/-- Helper for Theorem 25.40: finite sums preserve the local `...UpTo` witness on a fixed
deterministic horizon. -/
private theorem finsetSum_isContinuousLocalMartingaleUpTo_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    (s : Finset (Fin d)) {T : NNReal} {N : Fin d → NNReal → Ω → ℝ}
    (hN : ∀ i ∈ s, IsContinuousLocalMartingaleUpTo_theorem25_40 ℱ μ T (N i)) :
    IsContinuousLocalMartingaleUpTo_theorem25_40 ℱ μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ N i t ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ _ ↦ (0 : ℝ), ?_, ?_⟩
      · refine
          { local_martingale := ?_
            continuous := ?_ }
        · simpa using (MeasureTheory.martingale_zero ℝ ℱ μ).isLocalMartingale
        · intro ω
          simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      · simpa using eqUpTo_rfl (μ := μ) T (fun _ _ ↦ (0 : ℝ))
  | @insert i s hi hs =>
      rcases hN i (by simp) with ⟨Ni, hNi, hEqi⟩
      have hsN :
          ∀ j ∈ s, IsContinuousLocalMartingaleUpTo_theorem25_40 ℱ μ T (N j) := by
        intro j hj
        exact hN j (by simp [hj])
      rcases hs hsN with ⟨Ns, hNs, hEqs⟩
      let Nsum : NNReal → Ω → ℝ := fun t ω ↦ Ni t ω + Ns t ω
      refine ⟨Nsum, ?_, ?_⟩
      · refine
          { local_martingale := hNi.local_martingale.add hNs.local_martingale
            continuous := ?_ }
        intro ω
        -- Proof comment: the witness sum is continuous because both component witnesses already
        -- have continuous sample paths.
        simpa [Nsum] using (hNi.continuous ω).add (hNs.continuous ω)
      · have hEqSum :
          EqUpTo μ T
            (fun t ω ↦ N i t ω + Finset.sum s (fun j ↦ N j t ω))
            Nsum :=
          eqUpTo_add hEqi hEqs
        -- Proof comment: rewrite the visible sum into head-plus-tail form, then consume the
        -- combined horizonwise equality witness.
        simpa [Nsum, Finset.sum_insert, hi] using hEqSum

/-- Helper for Theorem 25.40: a bounded deterministic stop is a martingale once it agrees on
`[0,T]` with a continuous-local-martingale-up-to witness. -/
private theorem martingale_of_constStopped_eqUpTo_localMartingaleUpTo_theorem25_40
    {μ : ProbabilityMeasure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X N : NNReal → Ω → ℝ} {T : NNReal}
    (hX_strong :
      StronglyAdapted ℱ (stoppedProcess X (fun _ ↦ (T : ENNReal))))
    (hX_bounded :
      BoundedInTimeAe (μ : Measure Ω)
        (stoppedProcess X (fun _ ↦ (T : ENNReal))))
    (hXN : EqUpTo (μ : Measure Ω) T X N)
    (hN_upTo :
      IsContinuousLocalMartingaleUpTo_theorem25_40 ℱ (μ : Measure Ω) T N) :
    Martingale (stoppedProcess X (fun _ ↦ (T : ENNReal))) ℱ (μ : Measure Ω) := by
  rcases hN_upTo with ⟨N', hN', hNN'⟩
  have hOwnerEq :
      EqUpTo (μ : Measure Ω) T N' X :=
    eqUpTo_trans (eqUpTo_sym hNN') (eqUpTo_sym hXN)
  have hOwnerStopEq :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N' (fun _ ↦ (T : ENNReal)) t ω =
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω :=
    ae_eq_stoppedProcess_const_of_eqUpTo hOwnerEq
  have hOwnerStoppedLocal :
      IsLocalMartingale ℱ (μ : Measure Ω)
        (stoppedProcess N' (fun _ ↦ (T : ENNReal))) :=
    ProbabilityTheory.isLocalMartingale_stoppedProcess
      hN'.local_martingale
      hN'.continuous
      (isStoppingTime_const ℱ T)
  have hOwnerStoppedBounded :
      BoundedInTimeAe (μ : Measure Ω)
        (stoppedProcess N' (fun _ ↦ (T : ENNReal))) :=
    by
      have hOwnerStopEq_symm :
          ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
            stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω =
              stoppedProcess N' (fun _ ↦ (T : ENNReal)) t ω := by
        filter_upwards [hOwnerStopEq] with ω hω t
        exact (hω t).symm
      exact
        boundedInTimeAe_of_ae_allTimes_eq_theorem25_40
          hX_bounded
          hOwnerStopEq_symm
  have hOwnerStoppedMart :
      Martingale (stoppedProcess N' (fun _ ↦ (T : ENNReal))) ℱ (μ : Measure Ω) :=
    martingale_of_bounded_local_martingale hOwnerStoppedLocal hOwnerStoppedBounded
  have hTargetStopEq :
      ∀ t : NNReal,
        stoppedProcess N' (fun _ ↦ (T : ENNReal)) t =ᵐ[(μ : Measure Ω)]
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t := by
    intro t
    filter_upwards [hOwnerStopEq] with ω hω
    exact hω t
  -- Proof comment: the owner stop is already a martingale, and the visible deterministic stop
  -- inherits that property through timewise almost-sure equality plus its packaged
  -- strong adaptedness.
  exact martingale_congr_ae hOwnerStoppedMart hX_strong hTargetStopEq

/-- Helper for Theorem 25.40: for each coordinate, the stopped partial-derivative coefficient
has finite square energy on every deterministic interval `[0,T]`. The only input is that the raw
partial-derivative path is continuous before the exit time and the stopped coefficient is zero
afterwards. -/
private def coordinatePartialDerivProcess_theorem25_40
    {Wc : VectorProcess} {F : State → ℝ}
    (i : Fin d) : NNReal → Ω → ℝ :=
  fun r ω ↦ (∂[i] F) (Wc r ω)

/-- Helper for Theorem 25.40: for each coordinate, the stopped partial-derivative coefficient
has finite square energy on every deterministic interval `[0,T]`. The only input is that the raw
partial-derivative path is continuous before the exit time and the stopped coefficient is zero
afterwards. -/
private theorem stoppedPartialDeriv_sqIntegrableOnIcc_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess}
    {G : Set State} {F : State → ℝ}
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T : NNReal) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      IntegrableOn
        (fun s : ℝ ↦
          (ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_40
                (Ω := Ω) (Wc := Wc) (F := F) i)
              (hittingAfter Wc Gᶜ 0)
              s.toNNReal
              ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
  filter_upwards [hExitFinite] with ω hωfin
  let τω : NNReal := (hittingAfter Wc Gᶜ 0 ω).untopA
  have hτω : ((τώ : NNReal) : ENNReal) = hittingAfter Wc Gᶜ 0 ω := by
    dsimp [τώ]
    rw [WithTop.untopA_eq_untop (ne_of_lt hωfin)]
    exact WithTop.coe_untop _ _
  let S : NNReal := min T τω
  let rawCoeff : ℝ → ℝ := fun s ↦
    coordinatePartialDerivProcess_theorem25_40
      (Ω := Ω) (Wc := Wc) (F := F) i s.toNNReal ω
  let stoppedCoeff : ℝ → ℝ := fun s ↦
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_40
        (Ω := Ω) (Wc := Wc) (F := F) i)
      (hittingAfter Wc Gᶜ 0)
      s.toNNReal
      ω
  have hRawCont : Continuous rawCoeff := by
    -- Proof comment: compose the continuous Brownian sample path with the continuous
    -- partial-derivative observable.
    exact (continuousPartialDeriv_theorem25_40 F hFcontDiff i).comp
      ((hWcCont ω).comp continuous_real_toNNReal)
  have hRawSqInt :
      IntegrableOn (fun s : ℝ ↦ rawCoeff s ^ 2) (Set.Icc (0 : ℝ) (S : ℝ)) := by
    -- Proof comment: on the clipped interval `[0, T ∧ τ(ω)]`, the unstopped coefficient is a
    -- continuous real path on a compact interval.
    simpa [rawCoeff] using (hRawCont.pow 2).integrableOn_Icc
  have hStoppedSqIntSmall :
      IntegrableOn (fun s : ℝ ↦ stoppedCoeff s ^ 2) (Set.Icc (0 : ℝ) (S : ℝ)) := by
    refine hRawSqInt.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hs_toNNReal_le_S : s.toNNReal ≤ S := by
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2
    have hs_toNNReal_le_τω : s.toNNReal ≤ τω :=
      hs_toNNReal_le_S.trans (min_le_right T τω)
    have hs_le_exit :
        (s.toNNReal : ENNReal) ≤ hittingAfter Wc Gᶜ 0 ω := by
      have hs_le_exit' : (s.toNNReal : ENNReal) ≤ (τω : ENNReal) := by
        exact_mod_cast hs_toNNReal_le_τω
      -- Proof comment: on the clipped horizon the stopping indicator is still active, so the
      -- stopped coefficient agrees with the raw partial derivative.
      exact hs_le_exit'.trans_eq hτω
    dsimp [stoppedCoeff]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs_le_exit]
  have hStoppedSqInt :
      IntegrableOn (fun s : ℝ ↦ stoppedCoeff s ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)) := by
    refine IntegrableOn.of_forall_diff_eq_zero hStoppedSqIntSmall measurableSet_Icc ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1.1
    have hs_not_le_S : ¬ s ≤ S := by
      intro hsS
      exact hs.2 ⟨hs_nonneg, hsS⟩
    have hs_not_le_exit :
        ¬ (s.toNNReal : ENNReal) ≤ hittingAfter Wc Gᶜ 0 ω := by
      intro hs_le_exit
      have hs_toNNReal_le_τω : s.toNNReal ≤ τω := by
        -- Proof comment: once the exit clock is finite, comparison in `ENNReal` drops back to
        -- the underlying `NNReal` value of the exit time.
        exact_mod_cast (hτω.symm ▸ hs_le_exit)
      have hs_le_τω : s ≤ τω := by
        simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le_τω
      exact hs_not_le_S (le_min hs.1.2 hs_le_τω)
    -- Proof comment: beyond the clipped exit horizon, the stopped coefficient is identically
    -- zero, so the remaining tail contributes no energy.
    dsimp [stoppedCoeff]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs_not_le_exit]
    simp
  simpa [stoppedCoeff] using hStoppedSqInt

/-- Helper for Theorem 25.40: in the original Brownian natural filtration, stopping the `i`-th
partial-derivative coefficient before the exit time preserves progressive measurability. -/
private theorem centeredCoordinateStoppedPartialDerivProgMeasurableNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) :
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let Hi : NNReal → Ω → ℝ :=
      coordinatePartialDerivProcess_theorem25_40 (Ω := Ω) (Wc := Wc) (F := F) i
    ProgMeasurable ℱWc (processBeforeStoppingTime Hi τ) := by
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let Hi : NNReal → Ω → ℝ :=
    coordinatePartialDerivProcess_theorem25_40 (Ω := Ω) (Wc := Wc) (F := F) i
  have hτstop : IsStoppingTime ℱWc τ :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := Wc) (U := G) (x := x0) hWc hWcCont hGo hExitFinite
  have hHi_strong : StronglyAdapted ℱWc Hi := by
    intro t
    -- Proof comment: each deterministic-time slice is the continuous observable `∂[i] F`
    -- applied to the Brownian state at time `t`.
    exact
      stateComposition_stronglyAdapted_natural_theorem25_40
        (W := Wc)
        (hWsm := brownianVectorStartedAt_stronglyMeasurable hWc)
        (F := ∂[i] F)
        (hFmeas := (continuousPartialDeriv_theorem25_40 F hFcontDiff i).measurable)
        t
  have hHi_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Hi t ω := by
    intro ω
    -- Proof comment: the stopped coefficient is the continuous partial derivative observed along
    -- the continuous Brownian sample path.
    simpa [Hi] using ((continuousPartialDeriv_theorem25_40 F hFcontDiff i).comp (hWcCont ω))
  have hHi_prog : ProgMeasurable ℱWc Hi :=
    hHi_strong.progMeasurable_of_continuous hHi_cont
  -- Proof comment: once the raw coefficient is progressively measurable and the exit clock is a
  -- stopping time, the stopped coefficient stays progressively measurable on the same filtration.
  exact MeasureTheory.processBeforeStoppingTime_progMeasurable hHi_prog hτstop

/-- Helper for Theorem 25.40: after deterministically cutting off the exit-stopped `i`-th
partial-derivative coefficient at horizon `T`, the same square-energy witness extends to every
test interval `[0,U]` because the cutoff vanishes beyond `T`. -/
private theorem stoppedPartialDeriv_constCutoff_sqIntegrableOnIcc_allHorizons_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess}
    {G : Set State} {F : State → ℝ}
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T U : NNReal) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      IntegrableOn
        (fun s : ℝ ↦
          (ProbabilityTheory.processBeforeStoppingTime
              (ProbabilityTheory.processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_40
                  (Ω := Ω) (Wc := Wc) (F := F) i)
                (hittingAfter Wc Gᶜ 0))
              (fun _ ↦ (T : ENNReal))
              s.toNNReal
              ω) ^ 2)
        (Set.Icc (0 : ℝ) (U : ℝ)) := by
  have hBase :
      ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (ProbabilityTheory.processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_40
                  (Ω := Ω) (Wc := Wc) (F := F) i)
                (hittingAfter Wc Gᶜ 0)
                s.toNNReal
                ω) ^ 2)
          (Set.Icc (0 : ℝ) (T : ℝ)) :=
    stoppedPartialDeriv_sqIntegrableOnIcc_theorem25_40
      (μ := μ) (Wc := Wc) (G := G) (F := F)
      hWcCont hExitFinite hFcontDiff i T
  filter_upwards [hBase] with ω hω
  let g : ℝ → ℝ := fun s ↦
    (ProbabilityTheory.processBeforeStoppingTime
        (ProbabilityTheory.processBeforeStoppingTime
          (coordinatePartialDerivProcess_theorem25_40
            (Ω := Ω) (Wc := Wc) (F := F) i)
          (hittingAfter Wc Gᶜ 0))
        (fun _ ↦ (T : ENNReal))
        s.toNNReal
        ω) ^ 2
  have hBaseCut :
      IntegrableOn g (Set.Icc (0 : ℝ) (T : ℝ)) := by
    refine hω.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hs_toNNReal_le : s.toNNReal ≤ T := by
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2
    have hs_cutoff : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      exact_mod_cast hs_toNNReal_le
    -- Proof comment: on the base interval `[0,T]`, the deterministic cutoff leaves the
    -- exit-stopped coefficient unchanged.
    dsimp [g]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs_cutoff]
  have hCut :
      IntegrableOn g (Set.Icc (0 : ℝ) (U : ℝ)) := by
    refine IntegrableOn.of_forall_diff_eq_zero hBaseCut measurableSet_Icc ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1.1
    have hs_not_le : ¬ s ≤ T := by
      intro hs_le
      exact hs.2 ⟨hs_nonneg, hs_le⟩
    have hs_not_cutoff :
        ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      intro hs_cutoff
      have hs_toNNReal_le : s.toNNReal ≤ T := by
        exact_mod_cast hs_cutoff
      have hs_le : s ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le
      exact hs_not_le hs_le
    -- Proof comment: once `s > T`, the deterministic cutoff kills the coefficient, so the tail
    -- contributes zero energy on `[0,U]`.
    dsimp [g]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs_not_cutoff]
    simp
  simpa [g] using hCut

/-- Helper for Theorem 25.40: the fixed-horizon cutoff coefficient also satisfies the exact
unit-density bracket-energy spelling needed for the deterministic-cutoff Itô input. This is just
the previous square-integrability lemma rewritten with the constant density `1`. -/
private theorem stoppedPartialDeriv_constCutoff_unitDensityIntegrable_allHorizons_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess}
    {G : Set State} {F : State → ℝ}
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T U : NNReal) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      IntegrableOn
        (fun s : ℝ ↦
          (ProbabilityTheory.processBeforeStoppingTime
              (ProbabilityTheory.processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_40
                  (Ω := Ω) (Wc := Wc) (F := F) i)
                (hittingAfter Wc Gᶜ 0))
              (fun _ ↦ (T : ENNReal))
              s.toNNReal
              ω) ^ 2 * (1 : ℝ))
        (Set.Icc (0 : ℝ) (U : ℝ)) := by
  have hSq :
      ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (ProbabilityTheory.processBeforeStoppingTime
                (ProbabilityTheory.processBeforeStoppingTime
                  (coordinatePartialDerivProcess_theorem25_40
                    (Ω := Ω) (Wc := Wc) (F := F) i)
                  (hittingAfter Wc Gᶜ 0))
                (fun _ ↦ (T : ENNReal))
                s.toNNReal
                ω) ^ 2)
          (Set.Icc (0 : ℝ) (U : ℝ)) :=
    stoppedPartialDeriv_constCutoff_sqIntegrableOnIcc_allHorizons_theorem25_40
      (μ := μ) (Wc := Wc) (G := G) (F := F)
      hWcCont hExitFinite hFcontDiff i T U
  filter_upwards [hSq] with ω hω
  -- Proof comment: the bracket density has already been normalized to the constant `1`, so the
  -- integrand is definitionally the same square energy as above.
  simpa using hω

/-- Helper for Theorem 25.40: the translated stopped surface with vanishing harmonic drift is
already equal to the visible stopped increment on `[0,T]`, so it yields an `EqUpTo` bridge
without any further stochastic input. -/
private theorem visibleStoppedIncrement_eqUpTo_shiftedTranslatedSurface_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let X : NNReal → Ω → ℝ :=
      fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0
    EqUpTo (μ : Measure Ω) T X
      (fun t ω ↦
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let X : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0
  have hSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) =
          X t ω := by
    -- Proof comment: the earlier translated-surface rewrite already identifies the driftless
    -- stopped surface with the visible stopped increment at every deterministic time.
    simpa [B, τ, X] using
      shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
        (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x0 := x0)
        hx0 hWc hWcCont hGo hGV hExitFinite hFharm
  have hSurfaceSymm :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        X t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) := by
    filter_upwards [hSurface] with ω hω t
    exact (hω t).symm
  exact eqUpTo_of_ae_allTimes hSurfaceSymm

/-- Helper for Theorem 25.40: under harmonicity, the corrected cutoff-drift surface agrees on
`[0,T]` with the older stopped-surface spelling because both drift integrals vanish identically.
-/
private theorem shiftedTranslatedSurface_cutoffDrift_eq_oldDrift_under_harmonic_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    EqUpTo (μ : Measure Ω) T
      (fun t ω ↦
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Δ F (x0 + B s ω))
                τ
                u.toNNReal
                ω)
      (fun t ω ↦
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  have hShiftedLap :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        Δ F (x0 + stoppedProcess B τ t ω) = 0 := by
    -- Proof comment: harmonicity kills the Laplacian along the translated stopped path.
    simpa [B, τ, stoppedProcess] using
      shiftedStoppedExtension_laplacian_eq_zero
        (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x := x0)
        hx0 hWc hWcCont hGo hGV hExitFinite hFharm
  have hOldDriftZero :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) = 0 := by
    -- Proof comment: the old drift spelling is the primitive of the already-vanishing stopped
    -- Laplacian.
    simpa [B, τ, stoppedProcess] using
      stoppedLaplacianIntegral_eq_zero
        (μ := (μ : Measure Ω))
        (W := fun s ω ↦ x0 + B s ω)
        (τ := τ)
        (F := F)
        (by
          simpa [B, τ, stoppedProcess] using hShiftedLap)
  have hCutoffDriftZero :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x0 + B s ω))
              τ
              u.toNNReal
              ω = 0 := by
    filter_upwards [hShiftedLap] with ω hω t
    have hIntegrandZero :
        (fun s : ℝ ↦
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun u ω ↦ Δ F (x0 + B u ω))
              τ
              s.toNNReal
              ω) = fun _ : ℝ ↦ (0 : ℝ) := by
      funext s
      by_cases hs : (s.toNNReal : ENNReal) ≤ τ ω
      · have hStopEq : stoppedProcess B τ s.toNNReal ω = B s.toNNReal ω := by
          exact stoppedProcess_eq_of_le (u := B) (τ := τ) (ω := ω) (i := s.toNNReal) hs
        have hLapAt : Δ F (x0 + B s.toNNReal ω) = 0 := by
          simpa [hStopEq] using hω s.toNNReal
        rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs]
        simp [hLapAt]
      · rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs]
        simp
    -- Proof comment: the cutoff drift vanishes because the integrand is zero before `τ` by
    -- harmonicity and is forced to zero after `τ` by the cutoff itself.
    rw [hIntegrandZero]
    simp
  have hEqAll :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x0 + B s ω))
                  τ
                  u.toNNReal
                  ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) := by
    filter_upwards [hCutoffDriftZero, hOldDriftZero] with ω hωCutoff hωOld t
    rw [hωCutoff t, hωOld t]
  exact eqUpTo_of_ae_allTimes hEqAll

/-- Helper for Theorem 25.40: one centered coordinate already satisfies the exact deterministic
cutoff Itô input package needed at the remaining frontier. This isolates the true blocker from
the already-solved progressive-measurability and unit-density bracket bookkeeping. -/
private theorem coordinateConstCutoffItoInputData_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T : NNReal) :
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
    let hZi :
        IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        τ
    ProgMeasurable ℱWc Hi ∧
      (∀ U : NNReal, ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (ProbabilityTheory.processBeforeStoppingTime
                Hi
                (fun _ ↦ (T : ENNReal))
                s.toNNReal
                ω) ^ 2 * (1 : ℝ))
          (Set.Icc (0 : ℝ) (U : ℝ))) ∧
      HasAbsolutelyContinuousSquareVariation_theorem25_40 Zi hZi := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
  let hZi :
      IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
  let Hi : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_40
        (Ω := Ω) (Wc := Wc) (F := F) i)
      τ
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the exit-stopped coefficient is progressively measurable in the natural
    -- filtration of `Wc`; this is exactly the measurable input for the deterministic-cutoff Ito
    -- constructor.
    simpa [ℱWc, τ, Hi] using
      centeredCoordinateStoppedPartialDerivProgMeasurableNatural_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff i
  · intro U
    -- Proof comment: after adding the deterministic cutoff at horizon `T`, the unit-density
    -- square-energy bound holds on every test interval `[0,U]`.
    simpa [τ, Hi] using
      stoppedPartialDeriv_constCutoff_unitDensityIntegrable_allHorizons_theorem25_40
        (μ := μ) (Wc := Wc) (G := G) (F := F)
        hWcCont hExitFinite hFcontDiff i T U
  · -- Proof comment: the centered coordinate already carries the theorem-local absolutely
    -- continuous square-variation witness with unit density.
    simpa [ℱWc, Zi, hZi] using
      centeredCoordinate_hasAbsolutelyContinuousSquareVariation_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i

/-- Helper for Theorem 25.40: the theorem-local square-variation package is exactly the Chapter
25.21 input structure, just written under a local name to avoid importing the heavier later
frontier too early. -/
private noncomputable def globalHasAbsolutelyContinuousSquareVariation_of_local_theorem25_40
    {μ : Measure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr :
      HasAbsolutelyContinuousSquareVariation_theorem25_40 M hM) :
    ProbabilityTheory.HasAbsolutelyContinuousSquareVariation M hM :=
  let density := Classical.choose hbr
  let hDensity := Classical.choose_spec hbr
  let squareVariation := Classical.choose hDensity
  let hSquareVariation := Classical.choose_spec hDensity
  -- Proof comment: both interfaces store the same five clauses; only the declaration name
  -- changes when we move from the theorem-local wrapper to the Chapter 25.21 API.
  ⟨density, squareVariation, hSquareVariation.1, hSquareVariation.2.1, hSquareVariation.2.2⟩

/-- Helper for Theorem 25.40: for one coordinate, the Chapter 25.21 owner theorem already
produces a continuous-local-martingale witness whose canonical process is the deterministic-cutoff
coordinate Itô term. -/
private theorem coordinateConstCutoffItoUpTo_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T : NNReal) :
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
    let hZi :
        IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        τ
    ∃ N : NNReal → Ω → ℝ,
      IsContinuousLocalMartingaleUpTo_theorem25_40 ℱWc (μ : Measure Ω) T N ∧
      EqUpTo (μ : Measure Ω) T
        N
        (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi) := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
  let hZi :
      IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
  let Hi : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_40
        (Ω := Ω) (Wc := Wc) (F := F) i)
      τ
  let Hcut : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (T : ENNReal))
  rcases
      coordinateConstCutoffItoInputData_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff i T with
    ⟨hHi_prog, hHi_sq, hbr_local⟩
  let hbr :
      ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi :=
    globalHasAbsolutelyContinuousSquareVariation_of_local_theorem25_40
      (hM := hZi) hbr_local
  have hHcut_prog : ProgMeasurable ℱWc Hcut := by
    -- Proof comment: deterministic cutoff preserves progressive measurability of the raw
    -- exit-stopped coefficient.
    exact
      MeasureTheory.processBeforeStoppingTime_progMeasurable
        hHi_prog
        (isStoppingTime_const ℱWc T)
  have hHcut_sq :
      ∀ U : NNReal, ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (Hcut s.toNNReal ω) ^ 2 * (hbr.density s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (U : ℝ)) := by
    intro U
    filter_upwards [hHi_sq U] with ω hω
    -- Proof comment: the theorem-local bracket density for the centered coordinate is the
    -- constant `1`, so the deterministic-cutoff energy estimate matches the Chapter 25.21 input
    -- after one pointwise rewrite of the density factor.
    refine hω.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hDensity :
        (hbr.density s.toNNReal ω : ℝ) = 1 := by
      simp [hbr, globalHasAbsolutelyContinuousSquareVariation_of_local_theorem25_40, hbr_local]
    rw [hDensity, mul_one]
  rcases
      ProbabilityTheory.exists_continuousLocalMartingaleItoIntegral
        hZi hbr hHcut_prog hHcut_sq with
    ⟨N, hN⟩
  refine ⟨N, ?_, ?_⟩
  · -- Proof comment: the Chapter 25.21 witness is already a genuine continuous local martingale,
    -- so it is automatically a witness up to the fixed deterministic horizon `T`.
    exact
      isContinuousLocalMartingaleUpTo_of_isContinuousLocalMartingale_theorem25_40
        hN.continuousLocalMartingale
  · -- Proof comment: the owner clause identifies `N` with the canonical dyadic Itô process on a
    -- single null set for the deterministic-cutoff integrand; transport that canonical process
    -- back to `Hi` on `[0, T]` using the Chapter 25.21 cutoff comparison.
    have hEqCutoff :
        EqUpTo (μ : Measure Ω) T
        (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hcut)
        (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi) := by
      exact eqUpTo_sym <|
        by
          simpa [EqUpTo, ProbabilityTheory.Theorem25_21.EqUpTo, Hcut, Hi] using
            (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
              (μ := (μ : Measure Ω))
              (ℱ := ℱWc)
              (hM := hZi)
              (H := Hi)
              T)
    exact
      eqUpTo_trans
        (eqUpTo_of_areIndistinguishable_theorem25_40
          (T := T)
          (hN.itoIntegral.indistinguishable_canonical))
        hEqCutoff

/-- Helper for Theorem 25.40: the zero-patched centered vector path agrees almost surely at every
deterministic time with the raw centered Brownian path. -/
private theorem centeredPath_zeroPatched_eq_ae_allTimes_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = Wc t ω - x0 := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), Wc 0 ω = x0 :=
    brownianVectorStart_ae_eq_const (μ := μ) hWc
  filter_upwards [hStartAe] with ω hω t
  by_cases ht : t = 0
  · -- Proof comment: at time `0`, the patched process matches the raw centered path because the
    -- Brownian vector starts from `x0` almost surely.
    subst ht
    simp [B, hω]
  · -- Proof comment: away from time `0`, the zero-patched process is definitionally the raw
    -- centered Brownian path.
    simp [B, ht]

/-- Helper for Theorem 25.40: translating the input of a `C²` function preserves the `C²`
regularity needed for the centered pathwise Itô route. -/
private theorem translatedContDiff_theorem25_40
    {F : State → ℝ} (hFcontDiff : ContDiff ℝ 2 F) (x0 : State) :
    ContDiff ℝ 2 (fun z : State ↦ F (x0 + z)) := by
  -- Proof comment: the centered-path route uses the shifted observable `z ↦ F (x0 + z)`, so we
  -- package once that affine translation preserves the ambient `C²` regularity.
  simpa using hFcontDiff.comp ((contDiff_const.add contDiff_id).of_le le_top)

/-- Helper for Theorem 25.40: the coordinate partial derivatives of a translated observable are
the translated coordinate partial derivatives of the original observable. -/
private theorem translatedPartialDeriv_eq_theorem25_40
    {F : State → ℝ} (hF : Differentiable ℝ F) (x0 z : State) (i : Fin d) :
    (∂[i] fun w : State ↦ F (x0 + w)) z = (∂[i] F) (x0 + z) := by
  let G : State → ℝ := fun w : State ↦ F (x0 + w)
  have hG : Differentiable ℝ G := by
    intro w
    -- Proof comment: affine translation by the fixed base point `x0` preserves differentiability.
    exact ((hF (x0 + w)).hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x0)).differentiableAt
  have hFDeriv :
      fderiv ℝ G z = fderiv ℝ F (x0 + z) := by
    have hcomp :
        HasFDerivAt G (fderiv ℝ F (x0 + z)) z := by
      -- Proof comment: the Fréchet derivative of the translation map is the identity, so the
      -- shifted observable has the same derivative matrix as `F` at the translated point.
      simpa [G] using (hF (x0 + z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_add x0)
    simpa using hcomp.fderiv
  have hEval :
      (fderiv ℝ G z) (EuclideanSpace.single i (1 : ℝ)) =
        (fderiv ℝ F (x0 + z)) (EuclideanSpace.single i (1 : ℝ)) := by
    -- Proof comment: after identifying the translated Fréchet derivatives, evaluate both sides
    -- on the `i`-th basis vector to recover the coordinate partial derivative.
    simpa using
      congrArg
        (fun L : State →L[ℝ] ℝ ↦ L (EuclideanSpace.single i (1 : ℝ)))
        hFDeriv
  -- Proof comment: rewrite both coordinate partial derivatives through `fderiv` and compare the
  -- translated Fréchet derivatives at the matching point.
  simpa [partialDeriv_eq_fderiv_apply G hG i, partialDeriv_eq_fderiv_apply F hF i] using hEval

/-- Helper for Theorem 25.40: second coordinate partial derivatives commute with translation in
the same way as first coordinate partial derivatives. -/
private theorem translatedSecondPartialDeriv_eq_theorem25_40
    {F : State → ℝ} (hF : ContDiff ℝ 2 F) (x0 z : State) (i j : Fin d) :
    (∂²[i, j] fun w : State ↦ F (x0 + w)) z = (∂²[i, j] F) (x0 + z) := by
  have hFirst :
      (∂[i] fun w : State ↦ F (x0 + w)) =
        fun w : State ↦ (∂[i] F) (x0 + w) := by
    funext w
    -- Proof comment: the first translated partial derivative already matches the translated
    -- partial derivative of `F` pointwise.
    exact
      translatedPartialDeriv_eq_theorem25_40
        (F := F)
        (hF := hF.differentiable (by norm_num))
        x0
        w
        i
  -- Proof comment: once the first translated partial derivative is identified pointwise, apply
  -- the same translation lemma to the differentiable function `∂[i] F`.
  rw [secondPartialDeriv, hFirst]
  exact
    translatedPartialDeriv_eq_theorem25_40
      (F := ∂[i] F)
      (hF := differentiablePartialDeriv_shiftedConstLift_theorem25_40 F hF i)
      x0
      z
      j

/-- Helper for Theorem 25.40: the Kronecker-delta bracket primitive is the set integral of the
constant density `1` on the diagonal and `0` off the diagonal. -/
private theorem kroneckerPrimitive_eq_setIntegral_theorem25_40
    (i j : Fin d) (T : NNReal) :
    (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (if i = j then (1 : ℝ) else 0)) =
      if i = j then (T : ℝ) else 0 := by
  by_cases hij : i = j
  · subst hij
    have hle : (0 : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast T.2
    -- Proof comment: on the diagonal, the constant-density primitive is just the length of the
    -- interval `[0, T]`.
    rw [if_pos rfl, MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le hle]
    simp
  · -- Proof comment: off the diagonal, the Kronecker density vanishes identically.
    simp [hij, MeasureTheory.setIntegral_const]

/-- Helper for Theorem 25.40: the constant Kronecker-delta density is integrable on every compact
interval. -/
private theorem kroneckerDensity_integrableOn_theorem25_40
    (i j : Fin d) (b : ℝ) :
    IntegrableOn (fun s : ℝ ↦ if i = j then (1 : ℝ) else 0) (Set.Icc (0 : ℝ) b) := by
  -- Proof comment: the density is either the constant `1` or the constant `0`.
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Helper for Theorem 25.40: a Kronecker-delta quadratic-covariation family collapses the raw
double correction term to the diagonal set-integral family. -/
private theorem kroneckerQuadraticCorrection_eq_diagIntegrals_theorem25_40
    {F : State → ℝ} (hF : ContDiff ℝ 2 F)
    {X : VectorPathSpace d}
    (hcov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          (fun T ↦ if i = j then (T : ℝ) else 0))
    (T : NNReal) :
    ((1 : ℝ) / 2) *
        ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (X s))
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            T
      =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂²[i, i] F) (X s.toNNReal) := by
  have hpair :
      ∀ i j : Fin d,
        pathwiseQuadraticCovariationIntegral
          (fun s ↦ (∂²[i, j] F) (X s))
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          T
        =
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (if i = j then (1 : ℝ) else 0) * (∂²[i, j] F) (X s.toNNReal) := by
    intro i j
    -- Proof comment: rewrite each pairwise covariation term through the earlier scalar-density
    -- bridge, using the Kronecker primitive as `∫ 1` on the diagonal and `∫ 0` off the diagonal.
    exact
      pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationDensity
        (fun s ↦ (∂²[i, j] F) (X s))
        (Yi := vectorPathComponent X i)
        (Yj := vectorPathComponent X j)
        (aii := fun _ : ℝ ↦ (1 : ℝ))
        (aij := fun _ : ℝ ↦ if i = j then (1 : ℝ) else 0)
        (ajj := fun _ : ℝ ↦ (1 : ℝ))
        (by simpa [kroneckerPrimitive_eq_setIntegral_theorem25_40] using hcov i i)
        (by simpa [kroneckerPrimitive_eq_setIntegral_theorem25_40] using hcov j j)
        (by simpa [kroneckerPrimitive_eq_setIntegral_theorem25_40] using hcov i j)
        (fun n ↦ by simpa using kroneckerDensity_integrableOn_theorem25_40 i i (n : ℝ))
        (fun n ↦ by simpa using kroneckerDensity_integrableOn_theorem25_40 i j (n : ℝ))
        (fun n ↦ by simpa using kroneckerDensity_integrableOn_theorem25_40 j j (n : ℝ))
        ((continuous_secondPartialDeriv F hF i j).comp X.continuous)
        T
        (by simpa using kroneckerDensity_integrableOn_theorem25_40 i j (T : ℝ))
  -- Proof comment: after each pairwise term is rewritten to its density integral, every
  -- off-diagonal summand is zero and each diagonal summand is the expected second derivative.
  calc
    ((1 : ℝ) / 2) *
        ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (X s))
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            T
      =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d, ∑ j : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              (if i = j then (1 : ℝ) else 0) * (∂²[i, j] F) (X s.toNNReal) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hpair i j
    _ =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂²[i, i] F) (X s.toNNReal) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            simp [hj]
          · intro hi_not_mem
            exact False.elim (hi_not_mem (Finset.mem_univ i))

/-- Helper for Theorem 25.40: before the exit time, the theorem-local stopped coordinate
integrand is just the raw translated partial derivative observed along the centered Brownian path.
-/
private theorem stoppedCoordinatePartial_beforeExit_eq_theorem25_40
    {Wc : VectorProcess} {x0 : State} {G : Set State} {F : State → ℝ}
    {B : VectorProcess} {ω : Ω} (hω : ∀ t : NNReal, B t ω = Wc t ω - x0)
    (i : Fin d) {t : NNReal}
    (ht : (t : ENNReal) ≤ hittingAfter Wc Gᶜ 0 ω) :
    ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        (hittingAfter Wc Gᶜ 0)
        t
        ω =
      (∂[i] F) (x0 + B t ω) := by
  rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos ht]
  have hstate : x0 + B t ω = Wc t ω := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun z : State ↦ x0 + z) (hω t)
  -- Proof comment: after unfolding the coefficient process, the before-exit rewrite is exactly
  -- the translated state identity `x0 + B t ω = Wc t ω`.
  simpa [coordinatePartialDerivProcess_theorem25_40, hstate]

/-- Helper for Theorem 25.40: after the exit time, the theorem-local stopped coordinate
integrand vanishes identically. -/
private theorem stoppedCoordinatePartial_afterExit_eq_zero_theorem25_40
    {Wc : VectorProcess} {G : Set State} {F : State → ℝ}
    (i : Fin d) {ω : Ω} {t : NNReal}
    (ht : hittingAfter Wc Gᶜ 0 ω < (t : ENNReal)) :
    ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        (hittingAfter Wc Gᶜ 0)
        t
        ω = 0 := by
  -- Proof comment: once the evaluation time lies strictly after the exit horizon, the stopping
  -- operator kills the coordinate coefficient by definition.
  rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg (not_le_of_lt ht)]

/-- Helper for Theorem 25.40: on a fixed sample, the stopped coordinate coefficient is exactly
the raw translated coefficient cut off at the clipped exit time. -/
private theorem sampleStoppedCoordinate_eq_constCutoffRaw_theorem25_40
    {Wc : VectorProcess} {x0 : State} {G : Set State} {F : State → ℝ}
    {B : VectorProcess} {ω : Ω}
    (hω : ∀ t : NNReal, B t ω = Wc t ω - x0)
    (hF : Differentiable ℝ F)
    (i : Fin d) {T : NNReal}
    (hT : (T : ENNReal) = hittingAfter Wc Gᶜ 0 ω) :
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        (hittingAfter Wc Gᶜ 0)
    ∀ s : NNReal,
      Hi s ω =
        if (s : ENNReal) ≤ (T : ENNReal) then
          (∂[i] fun z : State ↦ F (x0 + z)) (B s ω)
        else
          0 := by
  intro Hi s
  by_cases hs : (s : ENNReal) ≤ (T : ENNReal)
  · have hs_exit : (s : ENNReal) ≤ hittingAfter Wc Gᶜ 0 ω := by
      simpa [hT] using hs
    -- Proof comment: before the clipped horizon, the stopped coefficient is still the raw
    -- translated partial derivative observed along the centered sample path.
    calc
      Hi s ω = (∂[i] F) (x0 + B s ω) := by
        exact
          stoppedCoordinatePartial_beforeExit_eq_theorem25_40
            (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B) (ω := ω)
            hω i hs_exit
      _ = (∂[i] fun z : State ↦ F (x0 + z)) (B s ω) := by
            symm
            exact translatedPartialDeriv_eq_theorem25_40 (F := F) (hF := hF) x0 (B s ω) i
      _ =
          if (s : ENNReal) ≤ (T : ENNReal) then
            (∂[i] fun z : State ↦ F (x0 + z)) (B s ω)
          else
            0 := by
              simp [hs]
  · have hs_exit : hittingAfter Wc Gᶜ 0 ω < (s : ENNReal) := by
      have hs_not_exit : ¬ (s : ENNReal) ≤ hittingAfter Wc Gᶜ 0 ω := by
        simpa [hT] using hs
      exact lt_of_not_ge hs_not_exit
    -- Proof comment: once the sample time is strictly past the clipped horizon, both the stopped
    -- coefficient and its deterministic cutoff are already zero.
    calc
      Hi s ω = 0 := by
        exact
          stoppedCoordinatePartial_afterExit_eq_zero_theorem25_40
            (Wc := Wc) (G := G) (F := F) i hs_exit
      _ =
          if (s : ENNReal) ≤ (T : ENNReal) then
            (∂[i] fun z : State ↦ F (x0 + z)) (B s ω)
          else
            0 := by
              simp [hs]

/-- Helper for Theorem 25.40: at a fixed horizon `T`, the canonical Itô value depends only on the
samplewise coefficient values on `Set.Icc 0 T`. -/
private theorem continuousLocalMartingaleItoIntegralProcess_eq_of_eqOnIcc_theorem25_40
    {μ : Measure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M K L : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {T : NNReal} {ω : Ω}
    (hKL : Set.EqOn (fun s : NNReal ↦ K s ω) (fun s ↦ L s ω) (Set.Icc 0 T)) :
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM K T ω =
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM L T ω := by
  let X : C(NNReal, ℝ) := ⟨fun s ↦ M s ω, hM.continuous ω⟩
  have hRows :
      partitionPathwiseItoApproximationUpTo
          (fun s ↦ K s ω)
          X
          Definition2158.dyadicPartitionSequence
          T =
        partitionPathwiseItoApproximationUpTo
          (fun s ↦ L s ω)
          X
          Definition2158.dyadicPartitionSequence
          T := by
    funext row
    -- Proof comment: every dyadic left endpoint contributing to the fixed-horizon row lies in
    -- `Set.Icc 0 T`, so the intervalwise coefficient identity rewrites the whole row sequence.
    exact
      partitionPathwiseItoApproximationUpTo_congrOn_Icc
        (P := Definition2158.dyadicPartitionSequence)
        (X := X)
        (T := T)
        hKL
        row
  -- Proof comment: the canonical Itô value is defined as the `limUnder` of the dyadic rows, so
  -- equality of the row family pins down the same fixed-time value.
  rw [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess,
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess,
    pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
  exact congrArg (limUnder atTop) hRows

/-- Helper for Theorem 25.40: at the matching cutoff horizon `T`, cutting the coefficient off at
`T` does not change the canonical Itô value. -/
private theorem continuousLocalMartingaleItoIntegralProcess_eq_constCutoffValue_theorem25_40
    {μ : Measure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal) (ω : Ω) :
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM
        (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T
        ω =
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM H T ω := by
  -- Proof comment: on `Set.Icc 0 T`, the deterministic cutoff already agrees pointwise with the
  -- original coefficient.
  exact
    continuousLocalMartingaleItoIntegralProcess_eq_of_eqOnIcc_theorem25_40
      (μ := μ)
      (ℱ := ℱ)
      (M := M)
      (K := ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (L := H)
      (hM := hM)
      (T := T)
      (ω := ω)
      (by
        intro s hs
        simp [ProbabilityTheory.processBeforeStoppingTime_apply, hs.2])

/-- Helper for Theorem 25.40: on a good centered sample path, the theorem-local canonical
coordinate owner is exactly the corresponding pathwise Itô integral along that centered path. -/
private theorem canonicalCoordinate_apply_eq_centeredPathwiseItoIntegral_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ} {B : VectorProcess}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (ω : Ω)
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = Wc t ω - x0)
    (i : Fin d) (t : NNReal) :
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
    let hZi :
        IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        (hittingAfter Wc Gᶜ 0)
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
      pathwiseItoIntegralAlong
        (fun s : NNReal ↦ Hi s ω)
        (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) i)
        Definition2158.dyadicPartitionSequence
        t := by
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
  let hZi :
      IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
  let Hi : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_40
        (Ω := Ω) (Wc := Wc) (F := F) i)
      (hittingAfter Wc Gᶜ 0)
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hPath :
      (⟨fun s ↦ Zi s ω, hZi.continuous ω⟩ : C(NNReal, ℝ)) = vectorPathComponent Xω i := by
    ext s
    simpa [Zi, Xω, vectorPathComponent] using (congrArg (fun z : State ↦ z i) (hω s)).symm
  -- Proof comment: unfold the canonical stochastic Itô process once, then transport its driving
  -- path to the centered vector-path coordinate via the extracted path equality `hPath`.
  simp only [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess]
  simpa [Hi, Xω] using
    congrArg
      (fun X : C(NNReal, ℝ) ↦
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ Hi s ω)
          X
          Definition2158.dyadicPartitionSequence
          t)
      hPath

/-- Helper for Theorem 25.40: the raw translated coordinate coefficient is progressively
measurable in the natural filtration of the centered Brownian vector. -/
private theorem rawCoordinatePartialDerivProgMeasurableNatural_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) :
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (Wc t ω - x0)
    ProgMeasurable ℱWc Hi := by
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (Wc t ω - x0)
  have hHi_strong : StronglyAdapted ℱWc Hi := by
    intro t
    -- Proof comment: each deterministic-time slice is the continuous observable
    -- `z ↦ ∂[i]F(z - x0)` applied to the Brownian state at time `t`.
    exact
      stateComposition_stronglyAdapted_natural_theorem25_40
        (W := Wc)
        (hWsm := brownianVectorStartedAt_stronglyMeasurable hWc)
        (hFmeas := ((continuousPartialDeriv_theorem25_40 F hFcontDiff i).comp
          (continuous_id.sub continuous_const)).measurable)
        t
  have hHi_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Hi t ω := by
    intro ω
    -- Proof comment: along each sample path, the raw translated coefficient is a continuous
    -- partial derivative observed on the centered Brownian path `Wc_t(ω) - x0`.
    simpa [Hi] using
      ((continuousPartialDeriv_theorem25_40 F hFcontDiff i).comp
        ((hWcCont ω).sub continuous_const))
  -- Proof comment: strong adaptation plus pathwise continuity promotes the coefficient to a
  -- progressively measurable process in the natural filtration.
  exact hHi_strong.progMeasurable_of_continuous hHi_cont

/-- Helper for Theorem 25.40: the raw translated coordinate coefficient satisfies the finite
bracket-energy hypothesis needed for the Chapter 25.22 subsequence machinery. -/
private theorem rawCoordinatePartialDerivHasFiniteBracketEnergy_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) :
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
    let hZi :
        IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    let hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi :=
      centeredCoordinate_hasAbsolutelyContinuousSquareVariation_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i
    let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (Wc t ω - x0)
    ProbabilityTheory.HasFiniteBracketEnergy hbr Hi := by
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
  let hZi :
      IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
  let hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi :=
    centeredCoordinate_hasAbsolutelyContinuousSquareVariation_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i
  let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (Wc t ω - x0)
  have hHi_prog : ProgMeasurable ℱWc Hi := by
    -- Proof comment: the preceding theorem already packages progressive measurability of the raw
    -- translated coefficient.
    simpa [ℱWc, Hi] using
      rawCoordinatePartialDerivProgMeasurableNatural_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (F := F)
        hWc hWcCont hFcontDiff i
  have hHi_sq :
      ∀ T : NNReal, ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (Hi s.toNNReal ω) ^ 2 * (hbr.density s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)) := by
    intro T
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hRealCont : Continuous fun s : ℝ ↦ Hi s.toNNReal ω := by
      -- Proof comment: composing the raw translated coefficient with `Real.toNNReal` preserves
      -- the samplewise continuity used for compact-interval square integrability.
      simpa [Hi] using
        ((continuousPartialDeriv_theorem25_40 F hFcontDiff i).comp
          (((hWcCont ω).sub continuous_const).comp continuous_real_toNNReal))
    have hSq :
        IntegrableOn
          (fun s : ℝ ↦ (Hi s.toNNReal ω) ^ 2)
          (Set.Icc (0 : ℝ) (T : ℝ)) := by
      simpa using (hRealCont.pow 2).integrableOn_Icc
    refine hSq.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hDensity : (hbr.density s.toNNReal ω : ℝ) = 1 := by
      simp [hbr]
    rw [hDensity, mul_one]
  -- Proof comment: with unit bracket density, compact-interval square integrability of the raw
  -- translated coefficient is exactly the Chapter 25.22 finite-energy condition.
  simpa [ProbabilityTheory.HasFiniteBracketEnergy] using
    Theorem25_22.brownianRepresentationItoIntegrand_hasFiniteBracketEnergy
      (ℱ := ℱWc)
      (μ := (μ : Measure Ω))
      hbr
      hHi_prog
      hHi_sq

/-- Helper for Theorem 25.40: for the raw translated coordinate coefficient, the canonical
stochastic Itô owner agrees with the pathwise dyadic owner along the centered sample path. -/
private theorem canonicalRawCoordinate_apply_eq_centeredPathwiseItoIntegral_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {F : State → ℝ} {B : VectorProcess}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (ω : Ω)
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = Wc t ω - x0)
    (i : Fin d) (t : NNReal) :
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
    let hZi :
        IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    let Hi : NNReal → Ω → ℝ := fun s ξ ↦ (∂[i] F) (Wc s ξ - x0)
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
      pathwiseItoIntegralAlong
        (fun s : NNReal ↦ Hi s ω)
        (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) i)
        Definition2158.dyadicPartitionSequence
        t := by
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
  let hZi :
      IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
  let Hi : NNReal → Ω → ℝ := fun s ξ ↦ (∂[i] F) (Wc s ξ - x0)
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hPath :
      (⟨fun s ↦ Zi s ω, hZi.continuous ω⟩ : C(NNReal, ℝ)) = vectorPathComponent Xω i := by
    -- Proof comment: the centered scalar coordinate path is exactly the `i`-th coordinate of
    -- the centered vector path `Xω`.
    ext s
    simpa [Zi, Xω, vectorPathComponent] using (congrArg (fun z : State ↦ z i) (hω s)).symm
  -- Proof comment: unfold the canonical stochastic owner once, then transport its driving path
  -- to the centered sample-path coordinate via the exact path identity `hPath`.
  simp only [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess]
  simpa [Hi, Xω] using
    congrArg
      (fun X : C(NNReal, ℝ) ↦
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ Hi s ω)
          X
          Definition2158.dyadicPartitionSequence
          t)
      hPath

/-- Helper for Theorem 25.40: any explicit pathwise witness for the raw centered coordinate
integral immediately yields convergence of the clipped dyadic rows to the canonical
`pathwiseItoIntegralAlong` value. -/
private theorem rawClippedCoordinateRows_tendsto_of_hasPathwiseWitness_theorem25_40
    {B : VectorProcess} {F : State → ℝ}
    {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (i : Fin d) (T : NNReal)
    (hIto :
      let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
      ∃ I : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          I) :
    let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T
          n)
      atTop
      (𝓝
        (pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T)) := by
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  rcases hIto with ⟨I, hI⟩
  -- Proof comment: once a genuine pathwise Itô realization is available, its defining
  -- convergence statement is exactly the target, and the canonical `pathwiseItoIntegralAlong`
  -- value is recovered by the owner equality.
  simpa [Xω, hI.eq_pathwiseItoIntegralAlong] using hI.tendsto T

/-- Helper for Theorem 25.40: strict-mono reindexing preserves any already established clipped
raw-coordinate convergence on a fixed centered sample path. -/
private theorem
    rawClippedCoordinateRows_tendsto_alongStrictMono_of_hasPathwiseWitness_theorem25_40
    {B : VectorProcess} {F : State → ℝ}
    {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (i : Fin d) (T : NNReal)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hIto :
      let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
      ∃ I : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          I) :
    let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T
          (φ n))
      atTop
      (𝓝
        (pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T)) := by
  -- Proof comment: reindex the convergent clipped row family along the strict-mono selector `φ`;
  -- the limiting pathwise Itô value is unchanged.
  exact
    (rawClippedCoordinateRows_tendsto_of_hasPathwiseWitness_theorem25_40
      (B := B) (F := F) (ω := ω) hcontω i T hIto).comp hφ.tendsto_atTop

/-- Helper for Theorem 25.40: on the diagonal, a square-variation witness is already a
quadratic-covariation witness. -/
private theorem selfCovariation_of_squareVariation_theorem25_40
    {Y : C(NNReal, ℝ)} {V : NNReal → ℝ}
    (hY : HasSquareVariationAlong Y V) :
    HasQuadraticCovariationAlong Y Y V := by
  have hEq :
      partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence Y Y =
        partitionPVariationSum Definition2158.dyadicPartitionSequence 2 Y := by
    funext T n
    simp [partitionQuadraticCovariationSum, partitionPVariationSum, sq_abs]
  -- Proof comment: along the diagonal the mixed dyadic sum is exactly the dyadic square
  -- variation sum, so the same limiting primitive works verbatim.
  intro T
  simpa [dyadic_quadratic_covariation_sum, dyadic_p_variation_sum, hEq] using
    (HasSquareVariationAlong.tendsto_partition_sum hY T)

/-- Helper for Theorem 25.40: the dyadic mixed quadratic-covariation sum is bounded by the
geometric mean of the two dyadic square-variation sums. -/
private theorem abs_partitionQuadraticCovariationSum_le_sqrt_mul_theorem25_40
    (F G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    |partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence F G T n| ≤
      Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n) *
        Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n) := by
  let s := Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k)
  have hAbs :
      |partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence F G T n| ≤
        Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) := by
    -- Proof comment: control the absolute mixed sum by the sum of absolute mixed increments.
    simpa [partitionQuadraticCovariationSum, s, ΔF, ΔG, abs_mul] using
      (Finset.abs_sum_le_sum_abs (s := s) (f := fun k ↦ ΔF k * ΔG k))
  have hCS :
      Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) ≤
        Real.sqrt (Finset.sum s (fun k ↦ |ΔF k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |ΔG k| ^ 2)) := by
    -- Proof comment: Cauchy-Schwarz gives the geometric-mean bound on the dyadic mixed row.
    exact Real.sum_mul_le_sqrt_mul_sqrt s (fun k ↦ |ΔF k|) (fun k ↦ |ΔG k|)
  calc
    |partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence F G T n|
        ≤ Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) := hAbs
    _ ≤ Real.sqrt (Finset.sum s (fun k ↦ |ΔF k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |ΔG k| ^ 2)) := hCS
    _ =
        Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n) *
          Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n) := by
          simp [partitionPVariationSum, s, ΔF, ΔG]

/-- Helper for Theorem 25.40: if the right path has zero square variation, then the mixed
quadratic covariation vanishes. -/
private theorem hasQuadraticCovariationAlong_zero_of_rightZeroSquareVariation_theorem25_40
    {F G : C(NNReal, ℝ)} {VF : NNReal → ℝ}
    (hVF : HasSquareVariationAlong F VF)
    (hG : HasSquareVariationAlong G 0) :
    HasQuadraticCovariationAlong F G 0 := by
  intro T
  have hFsqrt :
      Tendsto
        (fun n ↦ Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n))
        atTop
        (nhds (Real.sqrt (VF T))) := by
    exact
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hVF T)
  have hGsqrt :
      Tendsto
        (fun n ↦ Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n))
        atTop
        (nhds 0) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hG T))
  have hBound :
      Tendsto
        (fun n ↦
          Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n) *
            Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: the right square-root factor tends to `0`, so the geometric-mean bound
    -- also tends to `0`.
    simpa [Real.sqrt_zero] using hFsqrt.mul hGsqrt
  exact
    (tendsto_zero_iff_norm_tendsto_zero).2 <| by
      simpa [Real.norm_eq_abs] using
        (squeeze_zero
          (fun n ↦ abs_nonneg _)
          (fun n ↦ abs_partitionQuadraticCovariationSum_le_sqrt_mul_theorem25_40 F G T n)
          hBound)

/-- Helper for Theorem 25.40: if the left path has zero square variation, then the mixed
quadratic covariation vanishes. -/
private theorem hasQuadraticCovariationAlong_zero_of_leftZeroSquareVariation_theorem25_40
    {F G : C(NNReal, ℝ)} {VG : NNReal → ℝ}
    (hF : HasSquareVariationAlong F 0)
    (hVG : HasSquareVariationAlong G VG) :
    HasQuadraticCovariationAlong F G 0 := by
  intro T
  have hFsqrt :
      Tendsto
        (fun n ↦ Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n))
        atTop
        (nhds 0) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hF T))
  have hGsqrt :
      Tendsto
        (fun n ↦ Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n))
        atTop
        (nhds (Real.sqrt (VG T))) := by
    exact
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hVG T)
  have hBound :
      Tendsto
        (fun n ↦
          Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n) *
            Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: this time the left square-root factor tends to `0`.
    simpa [Real.sqrt_zero] using hFsqrt.mul hGsqrt
  exact
    (tendsto_zero_iff_norm_tendsto_zero).2 <| by
      simpa [Real.norm_eq_abs] using
        (squeeze_zero
          (fun n ↦ abs_nonneg _)
          (fun n ↦ abs_partitionQuadraticCovariationSum_le_sqrt_mul_theorem25_40 F G T n)
          hBound)

/-- Helper for Theorem 25.40: the deterministic time path has locally bounded variation on
`[0, ∞)`. -/
private theorem deterministicTimePath_locallyBoundedVariation_theorem25_40 :
    LocallyBoundedVariationOn
      ((⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)) : NNReal → ℝ)
      Set.univ := by
  have hmono : MonotoneOn (fun s : NNReal ↦ (s : ℝ)) Set.univ := by
    intro s _ t _ hst
    exact_mod_cast hst
  -- Proof comment: monotone real-valued paths are locally of bounded variation.
  exact hmono.locallyBoundedVariationOn

/-- Helper for Theorem 25.40: append deterministic time to a fixed centered path to build the
time-space graph `t ↦ (Xω t, t)`. -/
private noncomputable def goodCenteredPathTimeGraphPoint_theorem25_40
    (Xω : VectorPathSpace d) (t : NNReal) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 fun i : Fin (d + 1) ↦
    Fin.lastCases (motive := fun _ ↦ ℝ)
      (t : ℝ)
      (fun j : Fin d ↦ Xω t j)
      i

/-- Helper for Theorem 25.40: the spatial coordinates of the time-space graph recover the
original centered path coordinates. -/
private theorem goodCenteredPathTimeGraphPoint_castSucc_theorem25_40
    (Xω : VectorPathSpace d) (t : NNReal) (i : Fin d) :
    goodCenteredPathTimeGraphPoint_theorem25_40 Xω t (Fin.castSucc i) = Xω t i := by
  -- Proof comment: spatial coordinates are selected from the `Fin.lastCases` branch carrying
  -- the original path values.
  simp [goodCenteredPathTimeGraphPoint_theorem25_40]

/-- Helper for Theorem 25.40: the last coordinate of the time-space graph is the deterministic
time input itself. -/
private theorem goodCenteredPathTimeGraphPoint_last_theorem25_40
    (Xω : VectorPathSpace d) (t : NNReal) :
    goodCenteredPathTimeGraphPoint_theorem25_40 Xω t (Fin.last d) = (t : ℝ) := by
  -- Proof comment: on the last coordinate, `Fin.lastCases` returns the deterministic time.
  simp [goodCenteredPathTimeGraphPoint_theorem25_40]

/-- Helper for Theorem 25.40: the time-space graph of a continuous centered path is itself a
continuous path in dimension `d + 1`. -/
private theorem goodCenteredPathTimeGraph_continuous_theorem25_40
    (Xω : VectorPathSpace d) :
    Continuous fun t : NNReal ↦ goodCenteredPathTimeGraphPoint_theorem25_40 Xω t := by
  have hcoords :
      Continuous
        (fun t : NNReal ↦
          fun i : Fin (d + 1) ↦
            Fin.lastCases (motive := fun _ ↦ ℝ)
              (t : ℝ)
              (fun j : Fin d ↦ Xω t j)
              i) := by
    exact
      continuous_pi fun i ↦
        Fin.lastCases
          (simpa using (continuous_subtype_val : Continuous fun t : NNReal ↦ (t : ℝ)))
          (fun j ↦ by simpa using (continuous_apply j).comp Xω.continuous)
          i
  -- Proof comment: continuity of the graph path is checked coordinatewise.
  simpa [goodCenteredPathTimeGraphPoint_theorem25_40] using
    (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) ↦ ℝ)).comp hcoords

/-- Helper for Theorem 25.40: bundle the deterministic time-space graph of one centered path as a
path in `VectorPathSpace (d + 1)`. -/
private noncomputable def goodCenteredPathTimeGraph_theorem25_40
    (Xω : VectorPathSpace d) :
    VectorPathSpace (d + 1) :=
  ⟨fun s ↦ goodCenteredPathTimeGraphPoint_theorem25_40 Xω s,
    goodCenteredPathTimeGraph_continuous_theorem25_40 Xω⟩

/-- Helper for Theorem 25.40: the graph-path components split into the original centered spatial
coordinates and the deterministic time path. -/
private theorem vectorPathComponent_goodCenteredPathTimeGraph_eq_theorem25_40
    (Xω : VectorPathSpace d) :
    (∀ i : Fin d,
      vectorPathComponent
          (goodCenteredPathTimeGraph_theorem25_40 Xω)
          (Fin.castSucc i) =
        vectorPathComponent Xω i) ∧
      vectorPathComponent
          (goodCenteredPathTimeGraph_theorem25_40 Xω)
          (Fin.last d) =
        (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)) := by
  constructor
  · intro i
    -- Proof comment: the spatial graph components are literally the original centered
    -- coordinate paths.
    ext s
    simp [vectorPathComponent, goodCenteredPathTimeGraph_theorem25_40,
      goodCenteredPathTimeGraphPoint_castSucc_theorem25_40]
  · -- Proof comment: the last graph component is the deterministic time path.
    ext s
    simp [vectorPathComponent, goodCenteredPathTimeGraph_theorem25_40,
      goodCenteredPathTimeGraphPoint_last_theorem25_40]

/-- Helper for Theorem 25.40: the deterministic time-space graph of a good centered path carries
the expected Kronecker spatial covariations and zero mixed/time covariations. -/
private theorem goodCenteredPath_timeGraphCovariationFamily_theorem25_40
    {Xω : VectorPathSpace d}
    (hCov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent Xω i)
          (vectorPathComponent Xω j)
          (fun T ↦ if i = j then (T : ℝ) else 0)) :
    let Xωbar : VectorPathSpace (d + 1) := goodCenteredPathTimeGraph_theorem25_40 Xω
    (∀ i j : Fin d,
      HasQuadraticCovariationAlong
        (vectorPathComponent Xωbar (Fin.castSucc i))
        (vectorPathComponent Xωbar (Fin.castSucc j))
        (fun T ↦ if i = j then (T : ℝ) else 0)) ∧
    (∀ i : Fin d,
      HasQuadraticCovariationAlong
        (vectorPathComponent Xωbar (Fin.castSucc i))
        (vectorPathComponent Xωbar (Fin.last d))
        0) ∧
    (∀ i : Fin d,
      HasQuadraticCovariationAlong
        (vectorPathComponent Xωbar (Fin.last d))
        (vectorPathComponent Xωbar (Fin.castSucc i))
        0) ∧
    HasQuadraticCovariationAlong
      (vectorPathComponent Xωbar (Fin.last d))
      (vectorPathComponent Xωbar (Fin.last d))
      0 := by
  intro Xωbar
  have hsplit := vectorPathComponent_goodCenteredPathTimeGraph_eq_theorem25_40 Xω
  have htimeSq :
      HasSquareVariationAlong
        ((⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)))
        0 := by
    exact
      hasSquareVariationAlong_zero_of_locallyBoundedVariationOn
        deterministicTimePath_locallyBoundedVariation_theorem25_40
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    -- Proof comment: the spatial-spatial graph covariations are exactly the original centered
    -- path covariations after rewriting the graph coordinates.
    simpa [Xωbar, hsplit.1 i, hsplit.1 j] using hCov i j
  · intro i
    have hsqω :
        HasSquareVariationAlong (vectorPathComponent Xω i) (fun T ↦ (T : ℝ)) :=
      hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self (hCov i i)
    -- Proof comment: the deterministic time coordinate has zero square variation, so every
    -- spatial-time mixed covariation vanishes.
    simpa [Xωbar, hsplit.1 i, hsplit.2] using
      hasQuadraticCovariationAlong_zero_of_rightZeroSquareVariation_theorem25_40 hsqω htimeSq
  · intro i
    have hsqω :
        HasSquareVariationAlong (vectorPathComponent Xω i) (fun T ↦ (T : ℝ)) :=
      hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self (hCov i i)
    -- Proof comment: the same zero-square-variation argument also kills the mixed covariation
    -- when the deterministic time path appears on the left.
    simpa [Xωbar, hsplit.2, hsplit.1 i] using
      hasQuadraticCovariationAlong_zero_of_leftZeroSquareVariation_theorem25_40 htimeSq hsqω
  · -- Proof comment: the deterministic time path has zero square variation, so its
    -- self-covariation is identically zero as well.
    simpa [Xωbar, hsplit.2] using
      selfCovariation_of_squareVariation_theorem25_40 htimeSq

/-- Helper for Theorem 25.40: the deterministic time-space graph of a Brownian-good centered
path is itself a good path in dimension `d + 1`. -/
private theorem goodCenteredPathTimeGraph_mem_cqv_theorem25_40
    {Xω : VectorPathSpace d}
    (hCov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent Xω i)
          (vectorPathComponent Xω j)
          (fun T ↦ if i = j then (T : ℝ) else 0)) :
    goodCenteredPathTimeGraph_theorem25_40 Xω ∈ (𝒞_qv^(d + 1)) := by
  let Xωbar : VectorPathSpace (d + 1) := goodCenteredPathTimeGraph_theorem25_40 Xω
  let spatialCov : Fin d → Fin d → C(NNReal, ℝ) := fun i j ↦
    ⟨fun T ↦ if i = j then (T : ℝ) else 0, by
      by_cases hij : i = j
      · simpa [hij] using (continuous_subtype_val : Continuous fun T : NNReal ↦ (T : ℝ))
      · simpa [hij] using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))⟩
  have hGraph :=
    goodCenteredPath_timeGraphCovariationFamily_theorem25_40 (Xω := Xω) hCov
  refine (mem_𝒞_qv_d_iff_exists_family Xωbar).2 ?_
  refine ⟨fun i j ↦
    Fin.lastCases (motive := fun _ ↦ Fin (d + 1) → C(NNReal, ℝ))
      0
      (fun i' ↦
        Fin.lastCases (motive := fun _ ↦ C(NNReal, ℝ))
          0
          (fun j' ↦ spatialCov i' j')
          j)
      i, ?_⟩
  intro i j
  refine Fin.lastCases ?_ ?_ i
  · refine Fin.lastCases ?_ ?_ j
    · -- Proof comment: the time-time graph covariation is the zero path.
      simpa [Xωbar] using hGraph.2.2.2
    · intro j'
      -- Proof comment: every time-spatial mixed graph covariation is identically zero.
      simpa [Xωbar] using hGraph.2.2.1 j'
  · intro i'
    refine Fin.lastCases ?_ ?_ j
    · -- Proof comment: every spatial-time mixed graph covariation is identically zero.
      simpa [Xωbar] using hGraph.2.1 i'
    · intro j'
      -- Proof comment: on the spatial block, the graph covariation family is exactly the
      -- original Kronecker family carried by `Xω`.
      simpa [Xωbar, spatialCov] using hGraph.1 i' j'

/-- Helper for Theorem 25.40: forgetting the terminal graph coordinate recovers the spatial
`State` point. -/
private noncomputable def shiftedConstTimeSpaceGraphSpatialPart_theorem25_40
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    State :=
  WithLp.toLp 2 fun i : Fin d ↦ z (Fin.castSucc i)

/-- Helper for Theorem 25.40: the spatial graph projection reads off the corresponding
nonterminal coordinate. -/
private theorem shiftedConstTimeSpaceGraphSpatialPart_apply_theorem25_40
    (z : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z i = z (Fin.castSucc i) := by
  -- Proof comment: the graph projection is defined by `WithLp.toLp` on the nonterminal
  -- coordinates, so evaluation at `i` recovers `i.castSucc`.
  simp [shiftedConstTimeSpaceGraphSpatialPart_theorem25_40, PiLp.toLp_apply]

/-- Helper for Theorem 25.40: evaluating the spatial graph projection on the deterministic
time-space graph recovers the original centered path value. -/
private theorem shiftedConstTimeSpaceGraphSpatialPart_goodCenteredPathTimeGraph_theorem25_40
    (Xω : VectorPathSpace d) (t : NNReal) :
    shiftedConstTimeSpaceGraphSpatialPart_theorem25_40
        (goodCenteredPathTimeGraph_theorem25_40 Xω t) =
      Xω t := by
  -- Proof comment: every spatial graph coordinate is literally the corresponding coordinate of
  -- the original centered path.
  ext i
  simp [goodCenteredPathTimeGraph_theorem25_40,
    goodCenteredPathTimeGraphPoint_castSucc_theorem25_40,
    shiftedConstTimeSpaceGraphSpatialPart_apply_theorem25_40]

/-- Helper for Theorem 25.40: the time-independent lift of `F` to the Euclidean graph model
ignores the terminal time coordinate. -/
private noncomputable def shiftedConstTimeSpaceGraphLift_theorem25_40
    (F : State → ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
  fun z ↦ F (shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z)

/-- Helper for Theorem 25.40: moving a spatial graph coordinate changes only the matching
spatial coordinate of the lifted function. -/
private theorem shiftedConstTimeSpaceGraphLift_spaceLine_eq_theorem25_40
    (F : State → ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    (fun s : ℝ ↦
      shiftedConstTimeSpaceGraphLift_theorem25_40 F
        (z + EuclideanSpace.single (Fin.castSucc i) (s - z (Fin.castSucc i)))) =
      (fun s : ℝ ↦
        F
          (shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z +
            EuclideanSpace.single i
              (s - shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z i))) := by
  -- Proof comment: the lift depends only on the first `d` graph coordinates, so updating
  -- `i.castSucc` is exactly a spatial-axis update for `F`.
  funext s
  simp [shiftedConstTimeSpaceGraphLift_theorem25_40]
  congr 1
  ext j
  by_cases hji : j = i
  · subst hji
    simp [shiftedConstTimeSpaceGraphSpatialPart_apply_theorem25_40]
  · simp [shiftedConstTimeSpaceGraphSpatialPart_apply_theorem25_40, EuclideanSpace.single, hji]

/-- Helper for Theorem 25.40: moving the last graph coordinate leaves the time-independent lift
unchanged. -/
private theorem shiftedConstTimeSpaceGraphLift_timeLine_eq_theorem25_40
    (F : State → ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (fun s : ℝ ↦
      shiftedConstTimeSpaceGraphLift_theorem25_40 F
        (z + EuclideanSpace.single (Fin.last d) (s - z (Fin.last d)))) =
      fun _ : ℝ ↦ F (shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z) := by
  -- Proof comment: changing the terminal graph coordinate only changes time, and the
  -- time-independent lift does not see that coordinate.
  funext s
  simp [shiftedConstTimeSpaceGraphLift_theorem25_40,
    shiftedConstTimeSpaceGraphSpatialPart_apply_theorem25_40, EuclideanSpace.single,
    Fin.castSucc_ne_last]

/-- Helper for Theorem 25.40: the spatial partials of the specialized graph lift are exactly the
spatial partials of `F` evaluated at the projected graph point. -/
private theorem shiftedConstTimeSpaceGraphLift_spatialPartialDeriv_theorem25_40
    {F : State → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin d) (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (∂[Fin.castSucc i] (shiftedConstTimeSpaceGraphLift_theorem25_40 F)) z =
      (∂[i] F) (shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z) := by
  let Fpair : State × ℝ → ℝ := fun xt ↦ F xt.1
  have hPair : IsTimeSpaceC21_theorem25_40 Fpair := by
    -- Proof comment: the pair-valued lift `Fpair (x,t) = F x` is exactly the time-independent
    -- `C^{2,1}` owner proved earlier for the shifted-constant lift.
    simpa [Fpair] using
      shiftedConstLift_isTimeSpaceC21_theorem25_40
        (F := F)
        (x := (0 : State))
        hF
  have hDeriv :
      HasDerivAt
        (fun s : ℝ ↦
          shiftedConstTimeSpaceGraphLift_theorem25_40 F
            (z + EuclideanSpace.single (Fin.castSucc i) (s - z (Fin.castSucc i))))
        ((∂[i] F) (shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z))
        (z (Fin.castSucc i)) := by
    -- Proof comment: after rewriting the graph-axis line to the corresponding spatial line of
    -- `F`, the `C^{2,1}` owner supplies the required derivative.
    simpa [Fpair, shiftedConstTimeSpaceGraphLift_spaceLine_eq_theorem25_40] using
      hPair.hasDerivAt_space i
        (shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z, z (Fin.last d))
  -- Proof comment: `partialDeriv` is defined from the one-variable derivative along the chosen
  -- graph axis.
  exact hDeriv.deriv

/-- Helper for Theorem 25.40: the terminal graph-coordinate partial of the specialized lift
vanishes because the lift is time-independent. -/
private theorem shiftedConstTimeSpaceGraphLift_timePartialDeriv_theorem25_40
    (F : State → ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (∂[Fin.last d] (shiftedConstTimeSpaceGraphLift_theorem25_40 F)) z = 0 := by
  have hDeriv :
      HasDerivAt
        (fun s : ℝ ↦
          shiftedConstTimeSpaceGraphLift_theorem25_40 F
            (z + EuclideanSpace.single (Fin.last d) (s - z (Fin.last d))))
        0
        (z (Fin.last d)) := by
    -- Proof comment: along the terminal graph axis the lifted function is constant, so the
    -- derivative is `0`.
    simpa [shiftedConstTimeSpaceGraphLift_timeLine_eq_theorem25_40] using
      (hasDerivAt_const
        (x := z (Fin.last d))
        (c := F (shiftedConstTimeSpaceGraphSpatialPart_theorem25_40 z)))
  exact hDeriv.deriv

/-- Helper for Theorem 25.40: the first-order dyadic row of the specialized graph lift is
exactly the sum of the spatial coordinate rows, with no residual time-row term. -/
private theorem shiftedConstTimeSpaceGraphFirstOrder_eq_spatialRows_theorem25_40
    {F : State → ℝ} (hF : ContDiff ℝ 2 F)
    {Xω : VectorPathSpace d}
    (_hCov :
      ∀ j k : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent Xω j)
          (vectorPathComponent Xω k)
          (fun T ↦ if j = k then (T : ℝ) else 0))
    (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo
        (shiftedConstTimeSpaceGraphLift_theorem25_40 F)
        (goodCenteredPathTimeGraph_theorem25_40 Xω)
        T
        n
      =
        ∑ j : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[j] F) (Xω s))
            (vectorPathComponent Xω j)
            Definition2158.dyadicPartitionSequence
            T
            n := by
  let liftF : EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
    shiftedConstTimeSpaceGraphLift_theorem25_40 F
  let Xωbar : VectorPathSpace (d + 1) := goodCenteredPathTimeGraph_theorem25_40 Xω
  have hsplit := vectorPathComponent_goodCenteredPathTimeGraph_eq_theorem25_40 Xω
  have hSpatialTerm :
      ∀ j : Fin d,
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[Fin.castSucc j] liftF) (Xωbar s))
            (vectorPathComponent Xωbar (Fin.castSucc j))
            Definition2158.dyadicPartitionSequence
            T
            n
          =
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[j] F) (Xω s))
              (vectorPathComponent Xω j)
              Definition2158.dyadicPartitionSequence
              T
              n := by
    intro j
    congr
    · funext s
      -- Proof comment: evaluating the specialized graph-lift spatial partial on the graph path
      -- collapses back to the original centered coefficient `(∂[j] F) (Xω s)`.
      simpa [liftF, Xωbar,
        shiftedConstTimeSpaceGraphSpatialPart_goodCenteredPathTimeGraph_theorem25_40] using
        shiftedConstTimeSpaceGraphLift_spatialPartialDeriv_theorem25_40
          (F := F)
          hF
          j
          (goodCenteredPathTimeGraph_theorem25_40 Xω s)
    · -- Proof comment: the spatial graph component is exactly the original `j`-th coordinate
      -- path of `Xω`.
      simpa [Xωbar] using hsplit.1 j
  have hTimeTerm :
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[Fin.last d] liftF) (Xωbar s))
          (vectorPathComponent Xωbar (Fin.last d))
          Definition2158.dyadicPartitionSequence
          T
          n
        =
          0 := by
    -- Proof comment: the terminal graph derivative is identically `0`, so the time row
    -- contributes nothing.
    simp [liftF, Xωbar, hsplit.2,
      shiftedConstTimeSpaceGraphLift_timePartialDeriv_theorem25_40]
  have hRowSplit :
      dyadicMultidimensionalItoApproximationUpTo
          liftF
          Xωbar
          T
          n
        =
          ∑ k : Fin (d + 1),
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[k] liftF) (Xωbar s))
              (vectorPathComponent Xωbar k)
              Definition2158.dyadicPartitionSequence
              T
              n := by
    -- Proof comment: unfolding the multidimensional dyadic row rewrites it as the finite sum of
    -- its scalar coordinate rows.
    rw [dyadicMultidimensionalItoApproximationUpTo, Finset.sum_comm]
    simp [partitionPathwiseItoApproximationUpTo]
  calc
    dyadicMultidimensionalItoApproximationUpTo
        (shiftedConstTimeSpaceGraphLift_theorem25_40 F)
        (goodCenteredPathTimeGraph_theorem25_40 Xω)
        T
        n
      =
        ∑ k : Fin (d + 1),
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[k] liftF) (Xωbar s))
            (vectorPathComponent Xωbar k)
            Definition2158.dyadicPartitionSequence
            T
            n := hRowSplit
    _ =
        (∑ j : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[Fin.castSucc j] liftF) (Xωbar s))
            (vectorPathComponent Xωbar (Fin.castSucc j))
            Definition2158.dyadicPartitionSequence
            T
            n) +
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[Fin.last d] liftF) (Xωbar s))
            (vectorPathComponent Xωbar (Fin.last d))
            Definition2158.dyadicPartitionSequence
            T
            n := by
          rw [Fin.sum_univ_castSucc]
    _ =
        ∑ j : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[Fin.castSucc j] liftF) (Xωbar s))
            (vectorPathComponent Xωbar (Fin.castSucc j))
            Definition2158.dyadicPartitionSequence
            T
            n := by
          rw [hTimeTerm, add_zero]
    _ =
        ∑ j : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[j] F) (Xω s))
            (vectorPathComponent Xω j)
            Definition2158.dyadicPartitionSequence
            T
            n := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hSpatialTerm j

/-- Helper for Theorem 25.40: the remaining owner theorem should be a fixed-path pathwise witness
for the translated `i`-th coordinate integrand. Once this witness exists, the refinement theorem
below is only the identity reindexing wrapper over the already-proved row convergence helper. -/
private theorem coordinatePathwiseItoWitness_onBrownianGoodCenteredPath_theorem25_40
    {F : State → ℝ}
    (hF : ContDiff ℝ 2 F)
    {Xω : VectorPathSpace d}
    (hCov :
      ∀ j k : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent Xω j)
          (vectorPathComponent Xω k)
          (fun T ↦ if j = k then (T : ℝ) else 0))
    (i : Fin d) :
    ∃ I : NNReal → ℝ,
      HasPathwiseItoIntegralAlong
        (fun s : NNReal ↦ (∂[i] F) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        I := by
  -- Route correction: the graph-path membership is now proved separately, so the remaining
  -- blocker is the missing owner bridge from the time-space graph Ito formula back to a genuine
  -- pathwise witness for the single coordinate row.
  have hGraphMem :
      goodCenteredPathTimeGraph_theorem25_40 Xω ∈ (𝒞_qv^(d + 1)) :=
    goodCenteredPathTimeGraph_mem_cqv_theorem25_40 (Xω := Xω) hCov
  have hGraphRows :
      ∀ T : NNReal, ∀ n : ℕ,
        dyadicMultidimensionalItoApproximationUpTo
            (shiftedConstTimeSpaceGraphLift_theorem25_40 F)
            (goodCenteredPathTimeGraph_theorem25_40 Xω)
            T
            n
          =
            ∑ j : Fin d,
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[j] F) (Xω s))
                (vectorPathComponent Xω j)
                Definition2158.dyadicPartitionSequence
                T
                n := by
    intro T n
    -- Proof comment: the graph-lift bridge now rewrites the graph first-order row to the exact
    -- spatial coordinate family attached to `Xω`.
    simpa using
      shiftedConstTimeSpaceGraphFirstOrder_eq_spatialRows_theorem25_40
        (F := F)
        hF
        (Xω := Xω)
        hCov
        T
        n
  -- TODO: apply Theorem 25.30 to the graph path using `hGraphMem`, rewrite the graph first-order
  -- row through `hGraphRows`, and extract the single `i`-th coordinate limit. The remaining
  -- blocker is the deterministic single-row extraction step from the convergent graph-level
  -- spatial sum.
  sorry

/-- Helper for Theorem 25.40: on a fixed Brownian-good centered path, the full Kronecker
coordinate-covariation family is the correct deterministic input for the coordinate-row
refinement theorem used by the after-exit freeze argument. -/
private theorem coordinateRefinement_onBrownianGoodCenteredPath_theorem25_40
    {F : State → ℝ}
    (hF : ContDiff ℝ 2 F)
    {Xω : VectorPathSpace d}
    (hCov :
      ∀ j k : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent Xω j)
          (vectorPathComponent Xω k)
          (fun T ↦ if j = k then (T : ℝ) else 0))
    (i : Fin d) :
    ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[i] F) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                T
                (φ (ψ n)))
            atTop
          (𝓝
              (pathwiseItoIntegralAlong
                (fun s : NNReal ↦ (∂[i] F) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                T)) := by
  intro φ hφ
  rcases
      coordinatePathwiseItoWitness_onBrownianGoodCenteredPath_theorem25_40
        (F := F) hF (Xω := Xω) hCov i with
    ⟨I, hI⟩
  refine ⟨id, strictMono_id, ?_⟩
  intro T
  let B : NNReal → PUnit → State := fun s _ ↦ Xω s
  have hcontUnit : Continuous fun s : NNReal ↦ B s PUnit.unit := by
    -- Proof comment: the singleton process `B` is literally the fixed centered path `Xω`.
    simpa [B] using Xω.continuous
  let Xω' : VectorPathSpace d := ⟨fun s ↦ B s PUnit.unit, hcontUnit⟩
  have hXeq : Xω' = Xω := by
    -- Proof comment: the singleton continuous path `Xω'` and the original path `Xω` have the
    -- same underlying pointwise values, so they are equal as continuous maps.
    ext s
    rfl
  have hItoUnit :
      ∃ J : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω' s))
          (vectorPathComponent Xω' i)
          Definition2158.dyadicPartitionSequence
          J := by
    refine ⟨I, ?_⟩
    -- Proof comment: after identifying the singleton process with `Xω`, the pathwise witness
    -- from the previous theorem is unchanged.
    simpa [Xω'] using (hXeq ▸ hI)
  have hBase :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (Xω' s))
            (vectorPathComponent Xω' i)
            Definition2158.dyadicPartitionSequence
            T
            (φ n))
        atTop
        (𝓝
          (pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F) (Xω' s))
            (vectorPathComponent Xω' i)
            Definition2158.dyadicPartitionSequence
            T)) := by
    simpa [B, Xω'] using
      rawClippedCoordinateRows_tendsto_alongStrictMono_of_hasPathwiseWitness_theorem25_40
        (Ω := PUnit)
        (B := B)
        (F := F)
        (ω := PUnit.unit)
        hcontUnit
        i
        T
        (φ := φ)
        hφ
        hItoUnit
  -- Proof comment: once the single-coordinate witness exists, strict-mono reindexing preserves
  -- convergence, so the refinement theorem is the identity selector.
  simpa [Xω'] using (hXeq ▸ hBase)

/-- Helper for Theorem 25.40: on the raw centered Brownian sample path, the scalar centered
coordinate path is exactly the corresponding coordinate projection of the centered vector path. -/
private theorem rawCenteredCoordinatePath_eq_vectorPathComponent_theorem25_40
    {Wc : VectorProcess} {x0 : State} {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ Wc t ω - x0)
    (i : Fin d) :
    (⟨fun s ↦ Wc s ω i - x0 i, ((continuous_apply i).comp hcontω)⟩ : C(NNReal, ℝ)) =
      vectorPathComponent (⟨fun s ↦ Wc s ω - x0, hcontω⟩ : VectorPathSpace d) i := by
  -- Proof comment: evaluating the centered vector path in coordinate `i` literally recovers the
  -- centered scalar coordinate process.
  ext s
  simp [vectorPathComponent]

/-- Helper for Theorem 25.40: after reindexing any strict-mono dyadic row family, the Chapter
25.2.1 subsequence theorem still yields a further strict-mono refinement whose raw centered
coordinate rows converge almost surely to the canonical stochastic coordinate owner. -/
private theorem existsCenteredCoordinateRefinementSubsequence_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hF : ContDiff ℝ 2 F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (i : Fin d) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ T : NNReal,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F) (Wc s ω - x0))
              (⟨fun s ↦ Wc s ω i - x0 i,
                ((continuous_apply i).comp ((hWcCont ω).sub continuous_const))⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              (φ (ψ n)))
          atTop
          (𝓝
            (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
              ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
                (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1)
              (fun s ξ ↦ (∂[i] F) (Wc s ξ - x0))
              T
              ω)) := by
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
  let hZi :
      IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
  let hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi :=
    centeredCoordinate_hasAbsolutelyContinuousSquareVariation_naturalWc_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i
  let Hi : NNReal → Ω → ℝ := fun s ξ ↦ (∂[i] F) (Wc s ξ - x0)
  have hHi_prog : ProgMeasurable ℱWc Hi := by
    -- Proof comment: the earlier natural-filtration measurability lemma already packages the
    -- coefficient owner required by the Chapter 25.2.1 subsequence theorem.
    simpa [ℱWc, Hi] using
      rawCoordinatePartialDerivProgMeasurableNatural_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (F := F) hWc hWcCont hF i
  have hHi_cont : ∀ ω : Ω, Continuous fun s : NNReal ↦ Hi s ω := by
    intro ω
    -- Proof comment: along each sample path, the raw translated partial derivative is a
    -- continuous observable of the centered Brownian path.
    simpa [Hi] using
      ((continuousPartialDeriv_theorem25_40 F hF i).comp
        ((hWcCont ω).sub continuous_const))
  have hFiniteEnergy : ProbabilityTheory.HasFiniteBracketEnergy hbr Hi := by
    -- Proof comment: the centered Brownian coordinate has unit bracket density, so the previous
    -- finite-energy lemma applies without any further normalization.
    simpa [ℱWc, Zi, hZi, hbr, Hi] using
      rawCoordinatePartialDerivHasFiniteBracketEnergy_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (F := F) hWc hWcCont hF i
  let Pφ : ℕ → ℕ → NNReal := fun n k ↦ Definition2158.dyadicPartitionSequence (φ n) k
  letI : IsAdmissiblePartitionSequence Pφ :=
    isAdmissiblePartitionSequence_comp (P := Definition2158.dyadicPartitionSequence) hφ
  obtain ⟨ψ, hψ, hψae⟩ :=
    ProbabilityTheory.exists_partitionSubsequence_with_ae_pathwise_itoApproximation
      (μ := (μ : Measure Ω)) (ℱ := ℱWc) (M := Zi) (H := Hi)
      hZi hbr hHi_prog hHi_cont hFiniteEnergy Pφ
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψae] with ω hω T
  -- Proof comment: unfolding the reindexed partition sequence shows that the refined `Pφ`-rows
  -- are exactly the original dyadic rows along the composite selector `φ ∘ ψ`.
  simpa [Pφ, Hi, Zi, Function.comp] using hω T

/-- Helper for Theorem 25.40: after reindexing a strict-mono dyadic row family, the Chapter
25.2.1 subsequence theorem still yields a further strict-mono refinement that converges almost
surely at every horizon to any already-identified target process. -/
private theorem dyadicRowSubseqRefinement_exists_ae_tendsto_theorem25_40
    {μ : ProbabilityMeasure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H L : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ (μ : Measure Ω) M)
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (hHProg : ProgMeasurable ℱ H)
    (hHCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hFiniteEnergy : HasFiniteBracketEnergy hbr H)
    (hTargetId :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ T : NNReal,
        continuousLocalMartingaleItoIntegralProcess hM H T ω = L T ω)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ T : NNReal,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t : NNReal ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              (φ (ψ n)))
          atTop
          (𝓝 (L T ω)) := by
  let Pφ : ℕ → ℕ → NNReal := fun n k ↦ Definition2158.dyadicPartitionSequence (φ n) k
  letI : IsAdmissiblePartitionSequence Pφ :=
    isAdmissiblePartitionSequence_comp (P := Definition2158.dyadicPartitionSequence) hφ
  obtain ⟨ψ, hψ, hψae⟩ :=
    ProbabilityTheory.exists_partitionSubsequence_with_ae_pathwise_itoApproximation
      (μ := (μ : Measure Ω))
      (ℱ := ℱ)
      (M := M)
      (H := H)
      hM
      hbr
      hHProg
      hHCont
      hFiniteEnergy
      Pφ
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψae, hTargetId] with ω hω hωId T
  -- Proof comment: after reindexing by `φ`, the refined `Pφ` rows are exactly the original
  -- dyadic rows along `φ ∘ ψ`, and the target identification replaces the canonical Itô value by
  -- the chosen process `L`.
  simpa [Pφ, Function.comp, hωId T] using hω T

/-- Helper for Theorem 25.40: after any strict-mono reindexing, the zero-patched centered
Brownian coordinate rows admit a further strict-mono refinement that converges almost surely to
the canonical pathwise dyadic owner. -/
private theorem centeredCoordinateRefinementSubsequence_ae_tendsto_pathwise_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hF : ContDiff ℝ 2 F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (i : Fin d) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T
                  (φ (ψ n)))
              atTop
              (𝓝
                (pathwiseItoIntegralAlong
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T)) := by
  intro B
  obtain ⟨ψ, hψ, hψae⟩ :=
    existsCenteredCoordinateRefinementSubsequence_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (F := F) hWc hWcCont hF hφ i
  have hGood :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          Xω ∈ (𝒞_qv^d) ∧
            ∀ i j : Fin d,
              HasQuadraticCovariationAlong
                (vectorPathComponent Xω i)
                (vectorPathComponent Xω j)
                (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      zeroPatchedCenteredGoodPath_ae_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont
  have hEqAe :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = Wc t ω - x0 := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hGood, hEqAe, hψae] with ω hGoodω hω hSubseq
  rcases hGoodω with ⟨hcontω, hGoodω⟩
  refine ⟨hcontω, ?_⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  intro T
  have hPath :
      (⟨fun s ↦ Wc s ω i - x0 i,
        ((continuous_apply i).comp ((hWcCont ω).sub continuous_const))⟩ : C(NNReal, ℝ)) =
        vectorPathComponent Xω i := by
    -- Proof comment: the centered scalar coordinate path is exactly the `i`-th coordinate of
    -- the centered vector path `Xω`.
    simpa [Xω] using
      rawCenteredCoordinatePath_eq_vectorPathComponent_theorem25_40
        (Wc := Wc) (x0 := x0) (((hWcCont ω).sub continuous_const)) i
  have hCoeff :
      (fun s : NNReal ↦ (∂[i] F) (Wc s ω - x0)) =
        fun s : NNReal ↦ (∂[i] F) (Xω s) := by
    -- Proof comment: the pointwise identity `B s ω = Wc s ω - x0` rewrites the raw translated
    -- coefficient into the theorem-local centered path spelling.
    funext s
    simpa [Xω] using congrArg (fun z : State ↦ (∂[i] F) z) (hω s).symm
  have hRows :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F) (Wc s ω - x0))
          (⟨fun s ↦ Wc s ω i - x0 i,
            ((continuous_apply i).comp ((hWcCont ω).sub continuous_const))⟩ : C(NNReal, ℝ))
          Definition2158.dyadicPartitionSequence
          T
          (φ (ψ n))) =
        fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T
            (φ (ψ n)) := by
    -- Proof comment: after rewriting the coefficient and the driving scalar path, the refined
    -- dyadic rows are literally the theorem-local centered rows.
    funext n
    rw [hPath, hCoeff]
  have hLimit :
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
          ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1)
          (fun s ξ ↦ (∂[i] F) (Wc s ξ - x0))
          T
          ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
    -- Proof comment: the canonical stochastic owner is already identified with the centered
    -- pathwise owner once the sample path is rewritten to `Xω`.
    calc
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
          ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1)
          (fun s ξ ↦ (∂[i] F) (Wc s ξ - x0))
          T
          ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Wc s ω - x0))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
            simpa [Xω] using
              canonicalRawCoordinate_apply_eq_centeredPathwiseItoIntegral_theorem25_40
                (μ := μ) (Wc := Wc) (x0 := x0) (F := F) (B := B)
                hWc
                hWcCont
                ω
                hcontω
                hω
                i
                T
      _ =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
            rw [hCoeff]
  have hBase :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (Wc s ω - x0))
            (⟨fun s ↦ Wc s ω i - x0 i,
              ((continuous_apply i).comp ((hWcCont ω).sub continuous_const))⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            (φ (ψ n)))
        atTop
        (𝓝
          (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
            ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
              (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1)
            (fun s ξ ↦ (∂[i] F) (Wc s ξ - x0))
            T
            ω)) :=
    hSubseq T
  rw [hRows] at hBase
  simpa [hLimit] using hBase

/-- Helper for Theorem 25.40: the coordinate-refinement subsequence theorem does not depend on
which continuity proof is used for the centered sample path. This lets later arguments reuse one
common witness across all coordinates. -/
private theorem
    centeredCoordinateRefinementSubsequence_ae_tendsto_allContinuousWitnesses_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hF : ContDiff ℝ 2 F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (i : Fin d) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T
                  (φ (ψ n)))
              atTop
              (𝓝
                (pathwiseItoIntegralAlong
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T)) := by
  intro B
  obtain ⟨ψ, hψ, hψae⟩ :=
    centeredCoordinateRefinementSubsequence_ae_tendsto_pathwise_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (F := F) hWc hWcCont hF hφ i
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψae] with ω hω hcontω
  rcases hω with ⟨hcontω', hω'⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  let Xω' : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω'⟩
  have hXeq : Xω = Xω' := by
    ext s
    rfl
  intro T
  -- Proof comment: the row family only sees the underlying path `fun s ↦ B s ω`, so changing
  -- the proof of continuity leaves both the reindexed sequence and its canonical limit unchanged.
  simpa [Xω, Xω'] using (hXeq.symm ▸ hω' T)

/-- Helper for Theorem 25.40: one strict-mono selector can be chosen so that almost every
centered sample path carries simultaneous coordinate-row convergence for every `i : Fin d`. -/
private theorem existsCommonCoordinateRefinementSubsequence_ae_tendsto_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hF : ContDiff ℝ 2 F) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          ∀ i : Fin d, ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T
                  (χ n))
              atTop
              (𝓝
                (pathwiseItoIntegralAlong
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T)) := by
  intro B
  have hFinset :
      ∀ s : Finset (Fin d),
        ∃ χ : ℕ → ℕ, StrictMono χ ∧
          ∀ᵐ ω ∂(μ : Measure Ω),
            ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
              let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
              ∀ i : Fin d, i ∈ s → ∀ T : NNReal,
                Tendsto
                  (fun n ↦
                    partitionPathwiseItoApproximationUpTo
                      (fun s : NNReal ↦ (∂[i] F) (Xω s))
                      (vectorPathComponent Xω i)
                      Definition2158.dyadicPartitionSequence
                      T
                      (χ n))
                  atTop
                  (𝓝
                    (pathwiseItoIntegralAlong
                      (fun s : NNReal ↦ (∂[i] F) (Xω s))
                      (vectorPathComponent Xω i)
                      Definition2158.dyadicPartitionSequence
                      T)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨id, strictMono_id, ?_⟩
        refine Filter.Eventually.of_forall ?_
        intro ω hcontω i hi T
        exact False.elim (Finset.not_mem_empty i hi)
    | @insert i s hi hs =>
        rcases hs with ⟨χ, hχ, hχae⟩
        obtain ⟨ψ, hψ, hψae⟩ :=
          centeredCoordinateRefinementSubsequence_ae_tendsto_allContinuousWitnesses_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) (F := F) hWc hWcCont hF hχ i
        refine ⟨χ ∘ ψ, hχ.comp hψ, ?_⟩
        filter_upwards [hχae, hψae] with ω hωs hωi hcontω
        intro j hj T
        rcases Finset.mem_insert.mp hj with rfl | hj
        · -- Proof comment: the newly inserted coordinate uses the fresh refinement theorem
          -- directly along the common selector `χ ∘ ψ`.
          simpa [Function.comp] using hωi hcontω T
        · -- Proof comment: every previously handled coordinate keeps its limit after one more
          -- strict-mono reindexing because convergence persists along subsequences.
          simpa [Function.comp] using (hωs hcontω j hj T).comp hψ.tendsto_atTop
  rcases hFinset Finset.univ with ⟨χ, hχ, hχae⟩
  refine ⟨χ, hχ, ?_⟩
  filter_upwards [hχae] with ω hω hcontω
  intro i T
  -- Proof comment: the induction runs over `Finset.univ`, so the resulting selector works for
  -- every coordinate simultaneously.
  exact hω hcontω i (by simp) T

/-- Helper for Theorem 25.40: expanding the multidimensional dyadic Itô row shows that it is the
finite sum of the coordinate dyadic rows. This keeps the first-order frontier at the finite-row
level before the remaining `limUnder` exchange is addressed. -/
private theorem dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_40
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo F X T n =
      ∑ k : Fin d,
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ (∂[k] F) (X t))
          (vectorPathComponent X k)
          Definition2158.dyadicPartitionSequence
          T
          n := by
  -- Proof comment: unfold the multidimensional dyadic row and interchange the finite sum over
  -- partition cells with the finite sum over coordinates.
  rw [dyadicMultidimensionalItoApproximationUpTo, Finset.sum_comm]
  simp [partitionPathwiseItoApproximationUpTo]

/-- Helper for Theorem 25.40: along any strict-mono family of partition rows, the predecessor
point converges to the target horizon because the mesh tends to zero. -/
private theorem partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_40
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hmesh
      (fun n ↦ bot_le)
      ?_
  intro n
  -- Proof comment: every predecessor point lies within one mesh width of `T`, so shrinking
  -- mesh forces the predecessor horizon to converge to `T`.
  simpa [edist_comm] using partitionPredecessorPointWithinMeshEarly P (φ n) T

/-- Helper for Theorem 25.40: a truncated dyadic Itô row is the predecessor-horizon row plus the
single boundary increment on its last active cell. -/
private theorem partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_40
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {T : NNReal} {n : ℕ} :
    partitionPathwiseItoApproximationUpTo H X P T n =
      partitionPathwiseItoApproximationUpTo H X P (partitionPredecessorPointEarly P n T) n +
        H (partitionPredecessorPointEarly P n T) *
          (X T - X (partitionPredecessorPointEarly P n T)) := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0 : T ≤ 0 := by
        simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
      exact le_antisymm hle0 bot_le
    -- Proof comment: when the truncation index is zero, both sums are empty and the boundary
    -- increment vanishes because the horizon is already `0`.
    subst hT0
    simp [partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hpred : partitionPredecessorPointEarly P n T = P n k := by
      -- Proof comment: once the truncation index is positive, the predecessor point is the last
      -- active left endpoint in that row.
      simp [partitionPredecessorPointEarly, hk]
    have hpredIdx :
        partitionBoundIndex P n (partitionPredecessorPointEarly P n T) = k := by
      -- Proof comment: the predecessor horizon is itself the partition point `P n k`.
      rw [hpred, partitionBoundIndex_eq_of_partitionPoint]
    have hnext :
        partitionNextPointUpTo P n k T = T := by
      -- Proof comment: at the last contributing index, the clipped successor hits the target
      -- horizon exactly.
      rw [partitionNextPointUpTo, min_eq_right]
      simpa [hk] using le_partitionBoundIndex_time P n T
    have hprefix :
        ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x T) - X (P n x)) =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_ltT : j + 1 < partitionBoundIndex P n T := by
        simpa [hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
      have hnextT : partitionNextPointUpTo P n j T = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) T hj_ltT)
      have hnextPred : partitionNextPointUpTo P n j (P n k) = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact
          ((IsAdmissiblePartitionSequence.strictMono (P := P) n).monotone)
            (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      rw [hnextT, hnextPred]
    calc
      partitionPathwiseItoApproximationUpTo H X P T n =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x T) - X (P n x)) +
              H (P n k) * (X T - X (P n k)) := by
            rw [partitionPathwiseItoApproximationUpTo, hk, Finset.sum_range_succ, hnext]
      _ =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) +
              H (P n k) * (X T - X (P n k)) := by
            rw [hprefix]
      _ =
          partitionPathwiseItoApproximationUpTo H X P (partitionPredecessorPointEarly P n T) n +
            H (partitionPredecessorPointEarly P n T) *
              (X T - X (partitionPredecessorPointEarly P n T)) := by
            rw [partitionPathwiseItoApproximationUpTo, hpredIdx, hpred]
            simp

/-- Helper for Theorem 25.40: a truncated dyadic Itô row only depends on the coefficient values
at the sampled left endpoints that actually occur in that row. -/
private theorem partitionPathwiseItoApproximationUpTo_eq_of_leftEndpointEq_theorem25_40
    {K L : NNReal → ℝ} {X : C(NNReal, ℝ)}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {T : NNReal} {row : ℕ}
    (hKL : ∀ j : ℕ, j < partitionBoundIndex P row T → K (P row j) = L (P row j)) :
    partitionPathwiseItoApproximationUpTo K X P T row =
      partitionPathwiseItoApproximationUpTo L X P T row := by
  -- Proof comment: after unfolding the row, each summand is indexed by one sampled left
  -- endpoint `P row j`, so the hypothesis rewrites the finite sum termwise.
  rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hKL j (Finset.mem_range.mp hj)]

/-- Helper for Theorem 25.40: if two horizons lie in the same partition cell, then the raw
pathwise row sums differ only by the final boundary increment between those two times. -/
private theorem partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary_raw_theorem25_40
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {S T : NNReal} {n : ℕ} (hST : S ≤ T)
    (hSame : partitionBoundIndex P n S = partitionBoundIndex P n T) :
    partitionPathwiseItoApproximationUpTo H X P T n =
      partitionPathwiseItoApproximationUpTo H X P S n +
        H (partitionPredecessorPointEarly P n T) * (X T - X S) := by
  by_cases hidx : partitionBoundIndex P n T = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0 : T ≤ 0 := by
        simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
      exact le_antisymm hle0 bot_le
    have hS0 : S = 0 := by
      exact le_antisymm (le_trans hST (by simpa [hT0])) bot_le
    -- Proof comment: when the common truncation index is `0`, both horizons are already `0`,
    -- so both finite sums and the boundary increment vanish.
    subst hT0
    subst hS0
    simp [partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hidx
    let pred := partitionPredecessorPointEarly P n T
    have hidxS : partitionBoundIndex P n S = k + 1 := by
      rw [hSame, hk]
    have hpredEq : partitionPredecessorPointEarly P n S = pred := by
      -- Proof comment: same-cell horizons have the same predecessor endpoint on the chosen row.
      simp [pred, partitionPredecessorPointEarly, hk, hidxS]
    have hTpred :
        partitionPathwiseItoApproximationUpTo H X P T n =
          partitionPathwiseItoApproximationUpTo H X P pred n +
            H pred * (X T - X pred) := by
      -- Proof comment: the later horizon `T` differs from its predecessor row by one boundary
      -- increment on the final active cell.
      simpa [pred] using
        partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_40
          H X P (T := T) (n := n)
    have hSpred :
        partitionPathwiseItoApproximationUpTo H X P S n =
          partitionPathwiseItoApproximationUpTo H X P pred n +
            H pred * (X S - X pred) := by
      -- Proof comment: the earlier same-cell horizon `S` has exactly the same predecessor row.
      simpa [pred, hpredEq] using
        partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_40
          H X P (T := S) (n := n)
    have hPrefix :
        partitionPathwiseItoApproximationUpTo H X P pred n =
          partitionPathwiseItoApproximationUpTo H X P S n -
            H pred * (X S - X pred) := by
      linarith [hSpred]
    -- Proof comment: subtracting the shared predecessor-row decomposition leaves only the last
    -- boundary increment from `S` to `T`.
    calc
      partitionPathwiseItoApproximationUpTo H X P T n =
          partitionPathwiseItoApproximationUpTo H X P pred n +
            H pred * (X T - X pred) := hTpred
      _ =
          (partitionPathwiseItoApproximationUpTo H X P S n -
              H pred * (X S - X pred)) +
            H pred * (X T - X pred) := by
              rw [hPrefix]
      _ =
          partitionPathwiseItoApproximationUpTo H X P S n +
            H pred * (X T - X S) := by
              ring

/-- Helper for Theorem 25.40: in the non-partition branch, the clipped-successor raw row and the
raw row at the clipped horizon lie in the same dyadic cell, so they differ by exactly one
predecessor-side boundary increment. -/
private theorem rawRow_firstPastExit_nonPartition_eq_clipped_plus_boundary_theorem25_40
    (H : NNReal → ℝ) (X : C(NNReal, ℝ)) {S T : NNReal} {n : ℕ}
    (hST : S ≤ T)
    (hSame :
      partitionBoundIndex Definition2158.dyadicPartitionSequence n S =
        partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    partitionPathwiseItoApproximationUpTo
        H
        X
        Definition2158.dyadicPartitionSequence
        T
        n =
      partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          S
          n +
        H (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T) *
          (X T - X S) := by
  -- Proof comment: the non-partition branch is exactly the dyadic same-cell raw-row identity.
  simpa using
    partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary_raw_theorem25_40
      H X Definition2158.dyadicPartitionSequence hST hSame

/-- Helper for Theorem 25.40: once every sampled left endpoint in a tail lies strictly after the
exit horizon, the stopped coordinate coefficient kills that entire tail sum. -/
private theorem stoppedCoordinateRowTail_eq_zero_afterTime_theorem25_40
    {Wc : VectorProcess} {G : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {ω : Ω} {T t : NNReal} {row first : ℕ}
    (hT : (T : ENNReal) = hittingAfter Wc Gᶜ 0 ω)
    (hAfter : T < P row first) :
    ∑ j in Finset.Ico first (partitionBoundIndex P row t),
      ProbabilityTheory.processBeforeStoppingTime
          (coordinatePartialDerivProcess_theorem25_40
            (Ω := Ω) (Wc := Wc) (F := F) i)
          (hittingAfter Wc Gᶜ 0)
          (P row j)
          ω *
        (X (partitionNextPointUpTo P row j t) - X (P row j)) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hj_ge : first ≤ j := (Finset.mem_Ico.mp hj).1
  have hleft_le :
      P row first ≤ P row j :=
    (instStrictMono_of_isAdmissiblePartitionSequence (P := P) row).monotone hj_ge
  have hAfter_j : T < P row j := lt_of_lt_of_le hAfter hleft_le
  have hCoeff :
      ProbabilityTheory.processBeforeStoppingTime
          (coordinatePartialDerivProcess_theorem25_40
            (Ω := Ω) (Wc := Wc) (F := F) i)
          (hittingAfter Wc Gᶜ 0)
          (P row j)
          ω =
        0 := by
    have hExit :
        hittingAfter Wc Gᶜ 0 ω < ((P row j : NNReal) : ENNReal) := by
      rw [← hT]
      exact_mod_cast hAfter_j
    -- Proof comment: every sampled time in the tail lies strictly after the exit horizon, so the
    -- stopped coordinate integrand vanishes pointwise there.
    exact
      stoppedCoordinatePartial_afterExit_eq_zero_theorem25_40
        (Wc := Wc) (G := G) (F := F) i hExit
  -- Proof comment: after the pointwise coefficient rewrite, each tail summand is literally zero.
  simp [hCoeff]

/-- Helper for Theorem 25.40: in the partition-point branch, advancing one same-row clipped
successor adds exactly the single increment sampled at that partition point. -/
private theorem rawRow_firstPastExit_partitionPoint_eq_clipped_plus_boundary_theorem25_40
    (H : NNReal → ℝ) (X : C(NNReal, ℝ)) {t T : NNReal} {n m : ℕ}
    (hT : T = Definition2158.dyadicPartitionSequence n m)
    (hm : m < partitionBoundIndex Definition2158.dyadicPartitionSequence n t) :
    partitionPathwiseItoApproximationUpTo
        H
        X
        Definition2158.dyadicPartitionSequence
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
        n =
      partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          T
          n +
        H T *
          (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) - X T) := by
  have hStep :
      partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
          n -
        partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          T
          n =
      H T *
        (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) - X T) := by
    -- Proof comment: the imported same-row theorem already computes the one-step row increment;
    -- rewriting the partition point as `T` puts it in the horizon spelling used here.
    simpa [hT] using
      partitionPathwiseItoApproximationUpTo_nextPoint_sub_sameRow H X t n m hm
  -- Proof comment: rearrange the one-step increment identity into the forward row-equality form
  -- needed in the clipped-successor branch.
  linarith [hStep]

/-- Helper for Theorem 25.40: the single boundary increment from the predecessor-point
decomposition vanishes along any strict-mono subsequence when both the coefficient and path are
continuous. -/
private theorem partitionItoBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_40
    (H : NNReal → ℝ) (hH : Continuous H) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto
      (fun n ↦
        H (partitionPredecessorPointEarly P (φ n) T) *
          (X T - X (partitionPredecessorPointEarly P (φ n) T)))
      atTop
      (𝓝 0) := by
  have hpred :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) :=
    partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_40 P hφ T
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 (H T)) :=
    hH.continuousAt.tendsto.comp hpred
  have hPath :
      Tendsto
        (fun n ↦ X (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 (X T)) :=
    X.continuous.continuousAt.tendsto.comp hpred
  have hIncrement :
      Tendsto
        (fun n ↦ X T - X (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
      tendsto_const_nhds
    have hSub :
        Tendsto
          (fun n ↦ X T - X (partitionPredecessorPointEarly P (φ n) T))
          atTop
          (𝓝 (X T - X T)) :=
      hConst.sub hPath
    simpa using hSub
  -- Proof comment: the coefficient converges to its target value while the boundary increment
  -- itself converges to zero, so the product vanishes.
  simpa using hCoeff.mul hIncrement

/-- Helper for Theorem 25.40: the first clipped successor after the predecessor cell still
converges to the target horizon along any strict-mono family of rows. -/
private theorem partitionBoundarySuccessor_tendsto_alongStrictMonoRows_theorem25_40
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto
      (fun n ↦
        partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T)
      atTop
      (𝓝 T) := by
  by_cases hT0 : T = 0
  · subst hT0
    have hzero :
        (fun n ↦
          partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) 0 - 1) 0) =
          fun _ : ℕ ↦ 0 := by
      funext n
      simp [partitionNextPointUpTo, partitionBoundIndex_zero,
        IsAdmissiblePartitionSequence.zero_eq (P := P) (φ n)]
    rw [hzero]
    exact tendsto_const_nhds
  · have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
      hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
    rw [tendsto_iff_edist_tendsto_0]
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by simpa using hmesh.add hmesh)
        (fun n ↦ bot_le)
        ?_
    intro n
    let row := φ n
    have hidx_ne_zero : partitionBoundIndex P row T ≠ 0 := by
      intro hzero
      have hT_le_zero : T ≤ 0 := by
        have hle : T ≤ P row 0 := by
          simpa [hzero] using le_partitionBoundIndex_time P row T
        simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) row] using hle
      exact (not_lt_of_ge hT_le_zero) (bot_lt_iff_ne_bot.mpr hT0)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P row T = k + 1 :=
      ⟨partitionBoundIndex P row T - 1, (Nat.sub_add_cancel (Nat.pos_of_ne_zero hidx_ne_zero)).symm⟩
    have hpred :
        partitionPredecessorPointEarly P row T = P row k := by
      -- Proof comment: for positive truncation index, the predecessor point is the last active
      -- left endpoint of the row.
      simp [partitionPredecessorPointEarly, hk]
    have hsucc :
        partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T =
          partitionNextPointUpTo P row k T := by
      simp [hk]
    have hk_lt : k < partitionBoundIndex P row T := by
      simpa [hk] using Nat.lt_succ_self k
    have hsucc_mesh :
        edist
            (partitionPredecessorPointEarly P row T)
            (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T)
          ≤ partitionMesh P row := by
      -- Proof comment: the clipped successor of the predecessor cell lies within one mesh width
      -- of that predecessor endpoint.
      rw [hpred, hsucc]
      simpa using
        edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh P row k T hk_lt
    have hpred_mesh :
        edist (partitionPredecessorPointEarly P row T) T ≤ partitionMesh P row :=
      partitionPredecessorPointWithinMeshEarly P row T
    calc
      edist
          (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T)
          T
        ≤ edist
            (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T)
            (partitionPredecessorPointEarly P row T) +
          edist (partitionPredecessorPointEarly P row T) T := by
            exact edist_triangle _ _ _
      _ ≤ partitionMesh P row + partitionMesh P row := by
            exact add_le_add (by simpa [edist_comm] using hsucc_mesh) hpred_mesh

/-- Helper for Theorem 25.40: the boundary increment from the predecessor cell to its clipped
successor also vanishes along any strict-mono family of rows. -/
private theorem partitionItoSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_40
    (H : NNReal → ℝ) (hH : Continuous H) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto
      (fun n ↦
        H (partitionPredecessorPointEarly P (φ n) T) *
          (X (partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T) - X T))
      atTop
      (𝓝 0) := by
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 (H T)) := by
    -- Proof comment: the coefficient is still sampled at the predecessor points converging to
    -- the target horizon.
    exact
      hH.continuousAt.tendsto.comp
        (partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_40 P hφ T)
  have hSucc :
      Tendsto
        (fun n ↦ X (partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T))
        atTop
        (𝓝 (X T)) :=
    X.continuous.continuousAt.tendsto.comp
      (partitionBoundarySuccessor_tendsto_alongStrictMonoRows_theorem25_40 P hφ T)
  have hIncrement :
      Tendsto
        (fun n ↦
          X (partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T) - X T)
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
      tendsto_const_nhds
    -- Proof comment: continuity of the path at the clipped successor times forces the successor
    -- boundary increment to vanish.
    simpa using hSucc.sub hConst
  -- Proof comment: the predecessor coefficient stays bounded near its limit while the successor
  -- side boundary increment itself vanishes, so the product goes to `0`.
  simpa using hCoeff.mul hIncrement

/-- Helper for Theorem 25.40: if the sampled left endpoint is exactly the target horizon on each
row, then the next clipped successor along those rows still converges back to that same horizon as
the mesh tends to zero. -/
private theorem partitionExactSuccessor_tendsto_alongStrictMonoRows_theorem25_40
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ κ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hκ : ∀ n : ℕ, T = P (φ n) (κ n))
    (hκ_lt : ∀ n : ℕ, κ n < partitionBoundIndex P (φ n) t) :
    Tendsto
      (fun n ↦ partitionNextPointUpTo P (φ n) (κ n) t)
      atTop
      (𝓝 T) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hmesh
      (fun n ↦ bot_le)
      ?_
  intro n
  have hstep :
      edist
          (P (φ n) (κ n))
          (partitionNextPointUpTo P (φ n) (κ n) t)
        ≤ partitionMesh P (φ n) :=
    edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh
      P
      (φ n)
      (κ n)
      t
      (hκ_lt n)
  calc
    edist (partitionNextPointUpTo P (φ n) (κ n) t) T
      = edist (partitionNextPointUpTo P (φ n) (κ n) t) (P (φ n) (κ n)) := by
          rw [hκ n]
    _ = edist (P (φ n) (κ n)) (partitionNextPointUpTo P (φ n) (κ n) t) := by
          rw [edist_comm]
    _ ≤ partitionMesh P (φ n) := hstep

/-- Helper for Theorem 25.40: when the target horizon is itself a sampled partition point on each
row, the corresponding one-step exact-successor boundary increment still vanishes along any
strict-mono family of rows. -/
private theorem partitionItoExactSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_40
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ κ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hκ : ∀ n : ℕ, T = P (φ n) (κ n))
    (hκ_lt : ∀ n : ℕ, κ n < partitionBoundIndex P (φ n) t) :
    Tendsto
      (fun n ↦
        H T *
          (X (partitionNextPointUpTo P (φ n) (κ n) t) - X T))
      atTop
      (𝓝 0) := by
  have hSucc :
      Tendsto
        (fun n ↦ X (partitionNextPointUpTo P (φ n) (κ n) t))
        atTop
        (𝓝 (X T)) :=
    X.continuous.continuousAt.tendsto.comp
      (partitionExactSuccessor_tendsto_alongStrictMonoRows_theorem25_40
        P
        hφ
        hκ
        hκ_lt)
  have hIncrement :
      Tendsto
        (fun n ↦ X (partitionNextPointUpTo P (φ n) (κ n) t) - X T)
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
      tendsto_const_nhds
    -- Proof comment: continuity of the path at the exact partition-point horizon forces the
    -- one-step successor increment itself to vanish.
    simpa using hSucc.sub hConst
  -- Proof comment: here the coefficient is frozen at the exact partition point `T`, so only the
  -- vanishing successor increment remains asymptotically.
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ H T) atTop (𝓝 (H T))).mul hIncrement

/-- Helper for Theorem 25.40: convergence at `atTop` follows once every strict-mono subsequence
admits a further strict-mono refinement converging to the same limit. -/
private theorem tendstoAtTopOfStrictMonoSubseqTendsto_theorem25_40
    {α : Type*} [TopologicalSpace α] {u : ℕ → α} {a : α}
    (hRefine :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun n ↦ u (φ (ψ n))) atTop (𝓝 a)) :
    Tendsto u atTop (𝓝 a) := by
  -- Proof comment: reduce the statement to the standard subsequence criterion by extracting a
  -- strict-mono subsequence from every arbitrary `atTop`-tending row map.
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨φ, hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, hψ, hlim⟩ := hRefine (ns ∘ φ) hnsφ
  refine ⟨φ ∘ ψ, ?_⟩
  -- Proof comment: the composed refinement is exactly the convergent subsequence requested by
  -- `Filter.tendsto_of_subseq_tendsto`.
  simpa [Function.comp] using hlim

/-- Helper for Theorem 25.40: along any strict-mono family of dyadic rows, one can pass to a
strict-mono refinement on which the clipped horizon is either always an exact partition point or
always strictly inside the active dyadic cell. -/
private theorem exists_strictMono_refinement_partition_or_nonPartition_theorem25_40
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (T : NNReal) :
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ n : ℕ, T = P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T)) ∨
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ n : ℕ, T < P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T)) := by
  let exactRow : ℕ → Prop := fun n ↦
    T = P (φ n) (partitionBoundIndex P (φ n) T)
  by_cases hFreqExact : ∃ᶠ n in atTop, exactRow n
  · obtain ⟨ψ, hψ, hExact⟩ := extraction_of_frequently_atTop hFreqExact
    -- Proof comment: if exact partition rows occur frequently, extract a refinement on which
    -- every chosen row hits the clipped horizon exactly.
    exact Or.inl ⟨ψ, hψ, hExact⟩
  · have hEventuallyNon : ∀ᶠ n in atTop, ¬ exactRow n := by
      simpa [Filter.Frequently] using hFreqExact
    have hFreqNon : ∃ᶠ n in atTop, ¬ exactRow n :=
      hEventuallyNon.frequently
    obtain ⟨ψ, hψ, hNonExact⟩ := extraction_of_frequently_atTop hFreqNon
    refine Or.inr ⟨ψ, hψ, ?_⟩
    intro n
    have hle :
        T ≤ P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T) :=
      le_partitionBoundIndex_time P (φ (ψ n)) T
    have hne :
        T ≠ P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T) := by
      simpa [exactRow] using hNonExact n
    -- Proof comment: outside the exact-partition branch, the defining bound-index point is still
    -- above `T`, hence it lies strictly above `T`.
    exact lt_of_le_of_ne hle hne

/-- Helper for Theorem 25.40: in the genuine after-exit non-partition branch, the stopped
coordinate row at horizon `t` is exactly the raw row evaluated at the clipped successor horizon on
the same dyadic row. -/
private theorem stoppedCoordinateRow_eq_rawFirstPastExit_nonPartition_theorem25_40
    {Wc : VectorProcess} {G : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter Wc Gᶜ 0 ω)
    (hAfter : T < t)
    (hNonPart :
      T < Definition2158.dyadicPartitionSequence n
        (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    (hK :
      ∀ j : ℕ,
        j < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
          ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_40
                (Ω := Ω) (Wc := Wc) (F := F) i)
              (hittingAfter Wc Gᶜ 0)
              (Definition2158.dyadicPartitionSequence n j)
              ω =
            K (Definition2158.dyadicPartitionSequence n j)) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            (hittingAfter Wc Gᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        (partitionNextPointUpTo
          Definition2158.dyadicPartitionSequence
          n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
          t)
        n := by
  let P := Definition2158.dyadicPartitionSequence
  let k := partitionBoundIndex P n T
  let succ := partitionNextPointUpTo P n (k - 1) t
  let stoppedCoeff : NNReal → ℝ := fun s ↦
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_40
        (Ω := Ω) (Wc := Wc) (F := F) i)
      (hittingAfter Wc Gᶜ 0)
      s
      ω
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hT_lt_zero : T < 0 := by
      simpa [P, k, hk0, IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hNonPart
    exact (not_lt_of_ge bot_le) hT_lt_zero
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne_zero
  have hT_lt_succ : T < succ := by
    -- Proof comment: in the non-partition branch, both the chosen next partition point and the
    -- target horizon `t` lie strictly after the exit time `T`.
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact lt_min hNonPart hAfter
  have hsucc_le_pk : succ ≤ P n k := by
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hsuccIdx : partitionBoundIndex P n succ = k := by
    have hpred_lt_T : P n k' < T := by
      have hk'_lt : k' < k := by
        simpa [k, hk'] using Nat.lt_succ_self k'
      exact partitionPoint_lt_time_of_lt_partitionBoundIndex P n k' T hk'_lt
    have hpred_lt_succ : P n k' < succ := lt_trans hpred_lt_T hT_lt_succ
    -- Proof comment: the clipped successor stays in the same dyadic cell, so its truncation
    -- index is still `k`.
    simpa [k, hk'] using
      partitionBoundIndex_eq_succ_of_lt_of_le P n k' hpred_lt_succ (by
        simpa [k, hk'] using hsucc_le_pk)
  have hk_le_t : k ≤ partitionBoundIndex P n t := by
    calc
      k = partitionBoundIndex P n succ := hsuccIdx.symm
      _ ≤ partitionBoundIndex P n t := partitionBoundIndex_monotone P n (by
        dsimp [succ]
        rw [partitionNextPointUpTo]
        exact min_le_right _ _)
  have hPrefix :
      ∑ j in Finset.range k,
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j))
        =
      ∑ j in Finset.range k,
        K (P n j) *
          (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hK j (by simpa [k] using Finset.mem_range.mp hj)]
    have hj1_le_k : j + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hnext :
        partitionNextPointUpTo P n j t =
          partitionNextPointUpTo P n j succ := by
      rcases lt_or_eq_of_le hj1_le_k with hj1_lt | hj1_eq
      · have hj1_lt_t : j + 1 < partitionBoundIndex P n t :=
          lt_of_lt_of_le hj1_lt hk_le_t
        have hj1_lt_succ : j + 1 < partitionBoundIndex P n succ := by
          simpa [hsuccIdx] using hj1_lt
        have hnext_t : partitionNextPointUpTo P n j t = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) t hj1_lt_t)
        have hnext_succ : partitionNextPointUpTo P n j succ = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt
              (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) succ hj1_lt_succ)
        rw [hnext_t, hnext_succ]
      · have hj_eq : j = k - 1 := by
          omega
        -- Proof comment: at the last contributing left endpoint, both clipped successors are the
        -- chosen clipped successor horizon itself.
        have hnext_t : partitionNextPointUpTo P n j t = succ := by
          simpa [succ, hj_eq]
        have hnext_succ : partitionNextPointUpTo P n j succ = succ := by
          rw [hj_eq, partitionNextPointUpTo, min_eq_right]
          exact hsucc_le_pk
        rw [hnext_t, hnext_succ]
    rw [hnext]
  have hTail :
      ∑ j in Finset.Ico k (partitionBoundIndex P n t),
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j)) = 0 := by
    -- Proof comment: once the row index reaches `k`, every sampled left endpoint is already
    -- strictly after the exit time, so the stopped coefficient kills the tail.
    simpa [P, k, stoppedCoeff] using
      stoppedCoordinateRowTail_eq_zero_afterTime_theorem25_40
        (Wc := Wc) (G := G) (F := F) i X P (ω := ω) (T := T) (t := t) (row := n)
        (first := k) hT hNonPart
  have hRawSucc :
      partitionPathwiseItoApproximationUpTo K X P succ n =
        ∑ j in Finset.range k,
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    rw [partitionPathwiseItoApproximationUpTo, hsuccIdx]
  calc
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            (hittingAfter Wc Gᶜ 0)
            s
            ω)
        X
        P
        t
        n
      =
        ∑ j in Finset.range k,
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) +
        ∑ j in Finset.Ico k (partitionBoundIndex P n t),
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) := by
          rw [partitionPathwiseItoApproximationUpTo, ← Finset.sum_range_add_sum_Ico _ hk_le_t]
    _ =
        ∑ j in Finset.range k,
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
          rw [hTail, add_zero, hPrefix]
    _ = partitionPathwiseItoApproximationUpTo K X P succ n := hRawSucc.symm

/-- Helper for Theorem 25.40: in the partition-point branch, the stopped coordinate row at
horizon `t` is exactly the raw row evaluated at the clipped successor horizon on that same row. -/
private theorem stoppedCoordinateRow_eq_rawClippedSuccessor_partitionPoint_theorem25_40
    {Wc : VectorProcess} {G : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n m : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter Wc Gᶜ 0 ω)
    (hPart : T = Definition2158.dyadicPartitionSequence n m)
    (hm : m < partitionBoundIndex Definition2158.dyadicPartitionSequence n t)
    (hK :
      ∀ j : ℕ, j ≤ m →
        ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            (hittingAfter Wc Gᶜ 0)
            (Definition2158.dyadicPartitionSequence n j)
            ω =
          K (Definition2158.dyadicPartitionSequence n j)) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            (hittingAfter Wc Gᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
        n := by
  let P := Definition2158.dyadicPartitionSequence
  let succ := partitionNextPointUpTo P n m t
  let stoppedCoeff : NNReal → ℝ := fun s ↦
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_40
        (Ω := Ω) (Wc := Wc) (F := F) i)
      (hittingAfter Wc Gᶜ 0)
      s
      ω
  have hT_lt_succ : T < succ := by
    -- Proof comment: in the exact-partition branch, the clipped successor lies strictly after
    -- `T = P n m` because `m` is still below the truncation index of `t`.
    have hsucc_eq : succ = P n (m + 1) := by
      dsimp [succ]
      rw [partitionNextPointUpTo, min_eq_left]
      exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (m + 1) t hm)
    rw [hsucc_eq, hPart]
    exact (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n) (Nat.lt_succ_self m)
  have hsucc_le_next : succ ≤ P n (m + 1) := by
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hsuccIdx : partitionBoundIndex P n succ = m + 1 := by
    -- Proof comment: the clipped successor sits between `P n m` and `P n (m + 1)`, so its
    -- truncation index is exactly `m + 1`.
    rw [hPart] at hT_lt_succ
    exact partitionBoundIndex_eq_succ_of_lt_of_le P n m hT_lt_succ hsucc_le_next
  have hm_le_t : m + 1 ≤ partitionBoundIndex P n t := Nat.succ_le_of_lt hm
  have hPrefix :
      ∑ j in Finset.range (m + 1),
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j))
        =
      ∑ j in Finset.range (m + 1),
        K (P n j) *
          (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hK j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    have hj1_le : j + 1 ≤ m + 1 := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hnext :
        partitionNextPointUpTo P n j t =
          partitionNextPointUpTo P n j succ := by
      rcases lt_or_eq_of_le hj1_le with hj1_lt | hj1_eq
      · have hnext_t : partitionNextPointUpTo P n j t = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) t
              (lt_of_lt_of_le hj1_lt hm_le_t))
        have hnext_succ : partitionNextPointUpTo P n j succ = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt
              (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) succ (by
                simpa [hsuccIdx] using hj1_lt))
        rw [hnext_t, hnext_succ]
      · have hj_eq : j = m := by
          omega
        -- Proof comment: at the boundary index `m`, both clipped successors are the same chosen
        -- one-step horizon.
        have hnext_t : partitionNextPointUpTo P n j t = succ := by
          simpa [succ, hj_eq]
        have hnext_succ : partitionNextPointUpTo P n j succ = succ := by
          rw [hj_eq, succ, partitionNextPointUpTo, min_eq_right]
          exact hsucc_le_next
        rw [hnext_t, hnext_succ]
    rw [hnext]
  have hTail :
      ∑ j in Finset.Ico (m + 1) (partitionBoundIndex P n t),
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j)) = 0 := by
    have hAfterStart : T < P n (m + 1) := by
      rw [hPart]
      exact (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n) (Nat.lt_succ_self m)
    -- Proof comment: every later sampled left endpoint is strictly after exit, so the stopped
    -- coefficient kills the remaining tail.
    simpa [P, stoppedCoeff] using
      stoppedCoordinateRowTail_eq_zero_afterTime_theorem25_40
        (Wc := Wc) (G := G) (F := F) i X P (ω := ω) (T := T) (t := t) (row := n)
        (first := m + 1) hT hAfterStart
  have hRawSucc :
      partitionPathwiseItoApproximationUpTo K X P succ n =
        ∑ j in Finset.range (m + 1),
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    rw [partitionPathwiseItoApproximationUpTo, hsuccIdx]
  calc
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            (hittingAfter Wc Gᶜ 0)
            s
            ω)
        X
        P
        t
        n
      =
        ∑ j in Finset.range (m + 1),
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) +
        ∑ j in Finset.Ico (m + 1) (partitionBoundIndex P n t),
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) := by
          rw [partitionPathwiseItoApproximationUpTo, ← Finset.sum_range_add_sum_Ico _ hm_le_t]
    _ =
        ∑ j in Finset.range (m + 1),
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
          rw [hTail, add_zero, hPrefix]
    _ = partitionPathwiseItoApproximationUpTo K X P succ n := hRawSucc.symm

/-- Helper for Theorem 25.40: after exit, the stopped coordinate row at horizon `t` is always a
raw row on the same dyadic row, evaluated at the exact/non-partition successor horizon chosen by
the clipped exit time `T`. -/
private def afterExitMovingHorizon_theorem25_40
    (n : ℕ) (T t : NNReal) : NNReal :=
  if hExact :
      T =
        Definition2158.dyadicPartitionSequence n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) then
    partitionNextPointUpTo
      Definition2158.dyadicPartitionSequence
      n
      (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)
      t
  else
    partitionNextPointUpTo
      Definition2158.dyadicPartitionSequence
      n
      (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
      t

/-- Helper for Theorem 25.40: once the raw translated coordinate coefficient is known on every
sampled left endpoint up to the clipped exit time, the after-exit stopped row at time `t`
rewrites uniformly to the raw row at the exact/non-partition successor horizon from the same
dyadic cell. -/
private theorem stoppedCoordinateRow_eq_rawMovingHorizon_afterExit_theorem25_40
    {Wc : VectorProcess} {G : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter Wc Gᶜ 0 ω)
    (hAfter : T < t)
    (hK_lt :
      ∀ j : ℕ,
        j < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
          ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_40
                (Ω := Ω) (Wc := Wc) (F := F) i)
              (hittingAfter Wc Gᶜ 0)
              (Definition2158.dyadicPartitionSequence n j)
              ω =
            K (Definition2158.dyadicPartitionSequence n j)) :
    (hK_exact :
      T =
          Definition2158.dyadicPartitionSequence n
            (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) →
        ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            (hittingAfter Wc Gᶜ 0)
            T
            ω =
          K T) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            (hittingAfter Wc Gᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        (afterExitMovingHorizon_theorem25_40 n T t)
        n := by
  let P := Definition2158.dyadicPartitionSequence
  let k := partitionBoundIndex P n T
  by_cases hExact : T = P n k
  · have hk_lt_t : k < partitionBoundIndex P n t := by
      by_contra hk_not
      have hk_ge : partitionBoundIndex P n t ≤ k := Nat.not_lt.mp hk_not
      have hbound_le : P n (partitionBoundIndex P n t) ≤ P n k :=
        (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n).monotone hk_ge
      have hbound_lt_t : P n (partitionBoundIndex P n t) < t := by
        calc
          P n (partitionBoundIndex P n t) ≤ P n k := hbound_le
          _ = T := hExact.symm
          _ < t := hAfter
      exact (not_lt_of_ge (le_partitionBoundIndex_time P n t)) hbound_lt_t
    have hK :
        ∀ j : ℕ,
          j ≤ k →
            ProbabilityTheory.processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_40
                  (Ω := Ω) (Wc := Wc) (F := F) i)
                (hittingAfter Wc Gᶜ 0)
                (P n j)
                ω =
              K (P n j) := by
      intro j hj
      rcases lt_or_eq_of_le hj with hj_lt | rfl
      · exact hK_lt j hj_lt
      · simpa [P, k, hExact] using hK_exact hExact
    -- Proof comment: in the exact-partition branch, the moving horizon is the clipped next
    -- partition point, so the packaged exact-row identity applies directly.
    simpa [afterExitMovingHorizon_theorem25_40, P, k, hExact] using
      stoppedCoordinateRow_eq_rawClippedSuccessor_partitionPoint_theorem25_40
        (Wc := Wc) (G := G) (F := F) i X (ω := ω) (t := t) (T := T) (n := n) (m := k)
        (K := K) hT hExact hk_lt_t hK
  · have hNonPart : T < P n k := by
      have hle : T ≤ P n k := le_partitionBoundIndex_time P n T
      exact lt_of_le_of_ne hle hExact
    -- Proof comment: outside the exact-partition branch, the clipped exit time stays strictly
    -- inside the active cell, so the non-partition moving-successor identity gives the rewrite.
    simpa [afterExitMovingHorizon_theorem25_40, P, k, hExact] using
      stoppedCoordinateRow_eq_rawFirstPastExit_nonPartition_theorem25_40
        (Wc := Wc) (G := G) (F := F) i X (ω := ω) (t := t) (T := T) (n := n)
        (K := K) hT hAfter hNonPart hK_lt

/-- Helper for Theorem 25.40: on rows where the clipped horizon is itself a partition point, the
moving-horizon raw row differs from the clipped raw row by exactly the one-step exact-successor
boundary increment, so that error tends to `0` along any strict-mono row family. -/
private theorem rawCoordinateExactSuccessorError_tendsto_zero_afterExit_theorem25_40
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    {φ κ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hκ :
      ∀ n : ℕ,
        T = Definition2158.dyadicPartitionSequence (φ n) (κ n))
    (hκ_lt :
      ∀ n : ℕ,
        κ n < partitionBoundIndex Definition2158.dyadicPartitionSequence (φ n) t) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t)
            (φ n) -
          partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            T
            (φ n))
      atTop
      (𝓝 0) := by
  have hEq :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t)
            (φ n) -
          partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            T
            (φ n)) =
        fun n ↦
          H T *
            (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t) -
              X T) := by
    funext n
    have hRow :
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t)
            (φ n) =
          partitionPathwiseItoApproximationUpTo
              H
              X
              Definition2158.dyadicPartitionSequence
              T
              (φ n) +
            H T *
              (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t) -
                X T) := by
      -- Proof comment: on an exact-partition row, moving from `T` to the clipped successor adds
      -- only the one-step boundary increment sampled at `T`.
      exact
        rawRow_firstPastExit_partitionPoint_eq_clipped_plus_boundary_theorem25_40
          (H := H)
          (X := X)
          (t := t)
          (T := T)
          (n := φ n)
          (m := κ n)
          (hκ n)
          (hκ_lt n)
    linarith
  have hBoundary :
      Tendsto
        (fun n ↦
          H T *
            (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t) -
              X T))
        atTop
        (𝓝 0) := by
    -- Proof comment: the exact-successor boundary increment vanishes because the clipped
    -- successor converges back to the fixed partition point `T`.
    simpa using
      partitionItoExactSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_40
        (H := H)
        (X := X)
        (P := Definition2158.dyadicPartitionSequence)
        hφ
        hκ
        hκ_lt
  rw [hEq]
  exact hBoundary

/-- Helper for Theorem 25.40: in the genuine after-exit non-partition branch, the clipped
successor selected by the later horizon `t` still converges back to the clipped exit time `T`
along any strict-mono family of rows. -/
private theorem partitionAfterExitSuccessor_tendsto_alongStrictMonoRows_theorem25_40
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hAfter : T < t)
    (hNonPart :
      ∀ n : ℕ,
        T < P (φ n) (partitionBoundIndex P (φ n) T)) :
    Tendsto
      (fun n ↦
        partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) t)
      atTop
      (𝓝 T) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      (by simpa using hmesh.add hmesh)
      (fun n ↦ bot_le)
      ?_
  intro n
  let row := φ n
  let k := partitionBoundIndex P row T
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hT_lt_zero : T < 0 := by
      simpa [row, k, hk0, IsAdmissiblePartitionSequence.zero_eq (P := P) row] using hNonPart n
    exact (not_lt_of_ge bot_le) hT_lt_zero
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = k' + 1 :=
    Nat.exists_eq_succ_of_ne_zero hk_ne_zero
  have hpred :
      partitionPredecessorPointEarly P row T = P row k' := by
    -- Proof comment: the non-partition hypothesis forces a positive truncation index, so the
    -- predecessor point is the last active left endpoint on this row.
    simp [row, k, partitionPredecessorPointEarly, hk']
  have hk'_lt_t : k' < partitionBoundIndex P row t := by
    have hpred_lt_T : P row k' < T := by
      -- Proof comment: the predecessor endpoint sits strictly before the clipped horizon `T`.
      simpa [row, k, hk'] using
        partitionPoint_lt_time_of_lt_truncationBoundIndex P row k' T (Nat.lt_succ_self k')
    by_contra hk'_not
    have hle : partitionBoundIndex P row t ≤ k' := Nat.not_lt.mp hk'_not
    have ht_le : t ≤ P row k' := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P row t) hle)
    exact (not_le_of_gt (lt_of_lt_of_lt hpred_lt_T hAfter)) ht_le
  have hsucc_mesh :
      edist
          (partitionPredecessorPointEarly P row T)
          (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) t)
        ≤ partitionMesh P row := by
    -- Proof comment: once the predecessor endpoint is fixed, the later-horizon clipped
    -- successor lies within one mesh width of that predecessor.
    rw [hpred]
    simpa [row, k, hk'] using
      edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh P row k' t hk'_lt_t
  have hpred_mesh :
      edist (partitionPredecessorPointEarly P row T) T ≤ partitionMesh P row :=
    partitionPredecessorPointWithinMeshEarly P row T
  calc
    edist (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) t) T
      ≤
        edist
            (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) t)
            (partitionPredecessorPointEarly P row T) +
          edist (partitionPredecessorPointEarly P row T) T := by
            exact edist_triangle _ _ _
    _ ≤ partitionMesh P row + partitionMesh P row := by
          exact add_le_add (by simpa [edist_comm] using hsucc_mesh) hpred_mesh

/-- Helper for Theorem 25.40: in the genuine after-exit non-partition branch, the moving-horizon
raw row differs from the clipped raw row by one same-cell boundary increment, and that error
tends to `0` along any strict-mono family of rows. -/
private theorem rawCoordinateNonPartitionSuccessorError_tendsto_zero_afterExit_theorem25_40
    (H : NNReal → ℝ) (hH : Continuous H) (X : C(NNReal, ℝ))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hAfter : T < t)
    (hNonPart :
      ∀ n : ℕ,
        T <
          Definition2158.dyadicPartitionSequence
            (φ n)
            (partitionBoundIndex Definition2158.dyadicPartitionSequence (φ n) T)) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo
              Definition2158.dyadicPartitionSequence
              (φ n)
              (partitionBoundIndex Definition2158.dyadicPartitionSequence (φ n) T - 1)
              t)
            (φ n) -
          partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            T
            (φ n))
      atTop
      (𝓝 0) := by
  let P := Definition2158.dyadicPartitionSequence
  let succ : ℕ → NNReal := fun n ↦
    partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) t
  have hEq :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo H X P (succ n) (φ n) -
          partitionPathwiseItoApproximationUpTo H X P T (φ n)) =
        fun n ↦
          H (partitionPredecessorPointEarly P (φ n) T) * (X (succ n) - X T) := by
    funext n
    let row := φ n
    let k := partitionBoundIndex P row T
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      have hT_lt_zero : T < 0 := by
        simpa [P, row, k, hk0, IsAdmissiblePartitionSequence.zero_eq (P := P) row] using
          hNonPart n
      exact (not_lt_of_ge bot_le) hT_lt_zero
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = k' + 1 :=
      Nat.exists_eq_succ_of_ne_zero hk_ne_zero
    have hpred_lt_T : P row k' < T := by
      -- Proof comment: the predecessor endpoint of the active non-partition cell lies strictly
      -- before the clipped horizon `T`.
      simpa [P, row, k, hk'] using
        partitionPoint_lt_time_of_lt_truncationBoundIndex P row k' T (Nat.lt_succ_self k')
    have hT_lt_succ : T < succ n := by
      -- Proof comment: both the later horizon `t` and the next partition point on the active
      -- cell stay strictly above `T`, so the clipped successor lies strictly to the right of `T`.
      dsimp [succ]
      rw [partitionNextPointUpTo]
      exact lt_min (hNonPart n) hAfter
    have hsucc_le_pk : succ n ≤ P row k := by
      dsimp [succ]
      rw [partitionNextPointUpTo]
      exact min_le_left _ _
    have hsuccIdx : partitionBoundIndex P row (succ n) = k := by
      have hpred_lt_succ : P row k' < succ n := lt_trans hpred_lt_T hT_lt_succ
      -- Proof comment: the moving horizon still lies in the same active cell, so the
      -- truncation index remains equal to the clipped-horizon index `k`.
      simpa [P, row, k, hk'] using
        partitionBoundIndex_eq_succ_of_lt_of_le
          P
          row
          k'
          hpred_lt_succ
          (by simpa [P, row, k, hk'] using hsucc_le_pk)
    have hPredEq :
        partitionPredecessorPointEarly P row (succ n) =
          partitionPredecessorPointEarly P row T := by
      -- Proof comment: horizons in the same dyadic cell have the same predecessor endpoint.
      simp [P, row, partitionPredecessorPointEarly, hsuccIdx, k, hk']
    have hRow :
        partitionPathwiseItoApproximationUpTo H X P (succ n) row =
          partitionPathwiseItoApproximationUpTo H X P T row +
            H (partitionPredecessorPointEarly P row T) * (X (succ n) - X T) := by
      calc
        partitionPathwiseItoApproximationUpTo H X P (succ n) row =
            partitionPathwiseItoApproximationUpTo H X P T row +
              H (partitionPredecessorPointEarly P row (succ n)) * (X (succ n) - X T) := by
                exact
                  rawRow_firstPastExit_nonPartition_eq_clipped_plus_boundary_theorem25_40
                    (H := H)
                    (X := X)
                    (S := T)
                    (T := succ n)
                    (n := row)
                    (le_of_lt hT_lt_succ)
                    (by simpa [P, row, k] using hsuccIdx.symm)
        _ =
            partitionPathwiseItoApproximationUpTo H X P T row +
              H (partitionPredecessorPointEarly P row T) * (X (succ n) - X T) := by
                rw [hPredEq]
    linarith
  have hBoundary :
      Tendsto
        (fun n ↦
          H (partitionPredecessorPointEarly P (φ n) T) * (X (succ n) - X T))
        atTop
        (𝓝 0) := by
    have hCoeff :
        Tendsto
          (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T))
          atTop
          (𝓝 (H T)) := by
      -- Proof comment: the predecessor endpoints still converge to `T`, so the sampled
      -- coefficient converges to its target value by continuity of `H`.
      exact
        hH.continuousAt.tendsto.comp
          (partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_40 P hφ T)
    have hSucc :
        Tendsto (fun n ↦ X (succ n)) atTop (𝓝 (X T)) :=
      X.continuous.continuousAt.tendsto.comp
        (partitionAfterExitSuccessor_tendsto_alongStrictMonoRows_theorem25_40
          P
          hφ
          hAfter
          hNonPart)
    have hIncrement :
        Tendsto (fun n ↦ X (succ n) - X T) atTop (𝓝 0) := by
      have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
        tendsto_const_nhds
      -- Proof comment: once the moving clipped successors converge back to `T`, the final
      -- same-cell path increment itself vanishes.
      simpa using hSucc.sub hConst
    -- Proof comment: the predecessor coefficient remains bounded near `T` while the moving
    -- same-cell increment vanishes, so the whole error term tends to `0`.
    simpa using hCoeff.mul hIncrement
  rw [hEq]
  exact hBoundary

/-- Helper for Theorem 25.40: every coordinate path of `X ∈ 𝒞_qv^d` has scalar continuous square
variation along the dyadic partition sequence. -/
private theorem vectorPathComponent_mem_𝒞_qvAlong_of_mem_𝒞_qv_d_theorem25_40
    {X : VectorPathSpace d} (hX : X ∈ (𝒞_qv^d)) (i : Fin d) :
    vectorPathComponent X i ∈ 𝒞_qvAlong Definition2158.dyadicPartitionSequence := by
  rcases (mem_𝒞_qv_d_iff_exists_family X).mp hX with ⟨cov, hcov⟩
  refine (mem_𝒞_qvAlong_iff _).2 ?_
  refine ⟨cov i i, ?_⟩
  -- Proof comment: the scalar coordinate inherits continuous square variation from the chosen
  -- self-covariation path inside the `𝒞_qv^d` family of `X`.
  simpa using
    hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self (hcov i i)

/-- Helper for Theorem 25.40: once every strict-mono clipped-horizon row family admits a further
strict-mono refinement converging to the clipped canonical value, the exact/non-partition
boundary-error lemmas transport that limit to the after-exit moving-horizon rows. -/
private theorem rawMovingHorizon_tendsto_clippedCanonical_afterExit_theorem25_40
    {F0 : State → ℝ} (hF0 : ContDiff ℝ 2 F0)
    {Xω : VectorPathSpace d}
    (i : Fin d) {t Tω : NNReal} (hTω_lt_t : Tω < t)
    {L : ℝ}
    (hL :
      L =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          Tω)
    (hRefine :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                Tω
                (φ (ψ n)))
            atTop
            (𝓝 L)) :
    Tendsto
      (fun row ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          (afterExitMovingHorizon_theorem25_40 row Tω t)
          row)
      atTop
      (𝓝 L) := by
  have hCoeffCont : Continuous fun s : NNReal ↦ (∂[i] F0) (Xω s) := by
    -- Proof comment: both after-exit transport branches only use continuity of the translated
    -- coefficient along the fixed centered path.
    exact (continuousPartialDeriv_theorem25_40 F0 hF0 i).comp Xω.continuous
  refine tendstoAtTopOfStrictMonoSubseqTendsto_theorem25_40 ?_
  intro φ hφ
  obtain hExact | hNonPart :=
    exists_strictMono_refinement_partition_or_nonPartition_theorem25_40
      Definition2158.dyadicPartitionSequence
      (φ := φ)
      Tω
  · rcases hExact with ⟨ψ, hψ, hExactRows⟩
    let clipped : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        Tω
        (φ (ψ n))
    let moving : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
              (afterExitMovingHorizon_theorem25_40 (φ (ψ n)) Tω t)
              (φ (ψ n))
    let κ : ℕ → ℕ := fun n ↦
      partitionBoundIndex Definition2158.dyadicPartitionSequence (φ (ψ n)) Tω
    have hκ :
        ∀ n : ℕ,
          Tω = Definition2158.dyadicPartitionSequence (φ (ψ n)) (κ n) := by
      intro n
      simpa [κ] using hExactRows n
    have hκ_lt :
        ∀ n : ℕ,
          κ n < partitionBoundIndex Definition2158.dyadicPartitionSequence (φ (ψ n)) t := by
      intro n
      have hpoint_lt_t :
          Definition2158.dyadicPartitionSequence (φ (ψ n)) (κ n) < t := by
        rw [← hκ n]
        exact hTω_lt_t
      exact
        lt_partitionBoundIndex_of_partitionPoint_lt_time
          Definition2158.dyadicPartitionSequence
          (φ (ψ n))
          (κ n)
          t
          hpoint_lt_t
    have hBase :
        Tendsto clipped atTop (𝓝 L) := by
      -- Proof comment: the exact-partition branch now uses the caller-supplied universal
      -- clipped-horizon refinement theorem at the composed selector `φ ∘ ψ`.
      simpa [clipped, Function.comp] using hRefine (φ ∘ ψ) (hφ.comp hψ)
    have hMovingEq :
        moving =
          fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              (partitionNextPointUpTo
                Definition2158.dyadicPartitionSequence
                (φ (ψ n))
                (κ n)
                t)
              (φ (ψ n)) := by
      funext n
      simp [moving, κ, afterExitMovingHorizon_theorem25_40, hκ n]
    have hError :
        Tendsto (fun n ↦ moving n - clipped n) atTop (𝓝 0) := by
      rw [hMovingEq]
      -- Proof comment: in the exact-partition branch, only the one-step exact-successor
      -- boundary increment separates the moving horizon from the clipped horizon `Tω`.
      simpa [clipped, Function.comp] using
        rawCoordinateExactSuccessorError_tendsto_zero_afterExit_theorem25_40
          (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (X := vectorPathComponent Xω i)
          (φ := φ ∘ ψ)
          (κ := κ)
          (hφ := hφ.comp hψ)
          (T := Tω)
          (t := t)
          hκ
          hκ_lt
    have hTransport :
        Tendsto moving atTop (𝓝 L) := by
      have hCombined :
          Tendsto
            (fun n ↦ clipped n + (moving n - clipped n))
            atTop
            (𝓝 (L + 0)) :=
        hBase.add hError
      -- Proof comment: add the vanishing exact-successor boundary error back to the convergent
      -- clipped row family to recover the moving-horizon row limit.
      convert hCombined using 1
      · ext n
        ring
      · simp
    exact ⟨ψ, hψ, hTransport⟩
  · rcases hNonPart with ⟨ψ, hψ, hNonPartRows⟩
    let clipped : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        Tω
        (φ (ψ n))
    let moving : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        (afterExitMovingHorizon_theorem25_40 (φ (ψ n)) Tω t)
        (φ (ψ n))
    have hBase :
        Tendsto clipped atTop (𝓝 L) := by
      -- Proof comment: the non-partition branch uses the same universal clipped-horizon
      -- refinement input; only the boundary-error normalization changes.
      simpa [clipped, Function.comp] using hRefine (φ ∘ ψ) (hφ.comp hψ)
    have hMovingEq :
        moving =
          fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              (partitionNextPointUpTo
                Definition2158.dyadicPartitionSequence
                (φ (ψ n))
                (partitionBoundIndex
                  Definition2158.dyadicPartitionSequence
                  (φ (ψ n))
                  Tω - 1)
                t)
              (φ (ψ n)) := by
      funext n
      have hNotExact :
          ¬ Tω =
            Definition2158.dyadicPartitionSequence
              (φ (ψ n))
              (partitionBoundIndex
                Definition2158.dyadicPartitionSequence
                (φ (ψ n))
                Tω) := by
        exact ne_of_lt (hNonPartRows n)
      simp [moving, afterExitMovingHorizon_theorem25_40, hNotExact]
    have hError :
        Tendsto (fun n ↦ moving n - clipped n) atTop (𝓝 0) := by
      rw [hMovingEq]
      -- Proof comment: in the non-partition branch, the moving horizon stays in the same active
      -- dyadic cell as `Tω`, so the only difference is the same-cell boundary increment.
      simpa [clipped, Function.comp] using
        rawCoordinateNonPartitionSuccessorError_tendsto_zero_afterExit_theorem25_40
          (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
          hCoeffCont
          (X := vectorPathComponent Xω i)
          (φ := φ ∘ ψ)
          (hφ := hφ.comp hψ)
          (T := Tω)
          (t := t)
          hTω_lt_t
          hNonPartRows
    have hTransport :
        Tendsto moving atTop (𝓝 L) := by
      have hCombined :
          Tendsto
            (fun n ↦ clipped n + (moving n - clipped n))
            atTop
            (𝓝 (L + 0)) :=
        hBase.add hError
      -- Proof comment: add back the vanishing same-cell boundary error to transport the
      -- clipped-horizon limit to the moving-horizon raw rows.
      convert hCombined using 1
      · ext n
        ring
      · simp
    exact ⟨ψ, hψ, hTransport⟩

/-- Helper for Theorem 25.40: after the exit time, the dyadic row of the theorem-local
deterministic cutoff coefficient at horizon `U'` is exactly the raw moving-horizon row on the
fixed centered sample path. -/
private theorem constCutoffCoordinateRows_eq_rawMovingHorizon_afterExit_theorem25_40
    {Wc : VectorProcess} {x0 : State} {G : Set State} {F : State → ℝ}
    {B : VectorProcess} {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = Wc t ω - x0)
    (hF : Differentiable ℝ F)
    (i : Fin d) {T U' : NNReal}
    (hT : (T : ENNReal) = hittingAfter Wc Gᶜ 0 ω)
    (hTU : T < U') :
    let F0 : State → ℝ := fun z : State ↦ F (x0 + z)
    let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        (hittingAfter Wc Gᶜ 0)
    let HiCut : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (T : ENNReal))
    ∀ row : ℕ,
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ HiCut s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row
        =
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          (afterExitMovingHorizon_theorem25_40 row T U')
          row := by
  intro F0 Xω Hi HiCut row
  have hHiSample :
      ∀ s : NNReal,
        Hi s ω =
          if (s : ENNReal) ≤ (T : ENNReal) then
            (∂[i] F0) (Xω s)
          else
            0 := by
    -- Proof comment: along the fixed sample, the exit-stopped coordinate coefficient is exactly
    -- the raw translated coefficient clipped at the exit horizon `T`.
    simpa [Hi, F0, Xω] using
      sampleStoppedCoordinate_eq_constCutoffRaw_theorem25_40
        (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B) (ω := ω)
        hω
        hF
        i
        (T := T)
        hT
  have hHiCutSample : ∀ s : NNReal, HiCut s ω = Hi s ω := by
    intro s
    by_cases hs : (s : ENNReal) ≤ (T : ENNReal)
    · -- Proof comment: before `T`, the extra deterministic cutoff leaves the already stopped
      -- coefficient unchanged.
      simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs]
    · have hHiZero : Hi s ω = 0 := by
        simpa [hs] using hHiSample s
      -- Proof comment: after `T`, both the exit-stopped coefficient and its deterministic
      -- cutoff are already zero on the fixed sample.
      simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs, hHiZero]
  have hCutToStop :
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ HiCut s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row
        =
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ Hi s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row := by
    -- Proof comment: the fixed-sample coefficient equality `HiCut = Hi` lets us normalize the
    -- dyadic row to the single-stopped coefficient before applying the after-exit row rewrite.
    exact
      partitionPathwiseItoApproximationUpTo_congrOn_Icc
        (P := Definition2158.dyadicPartitionSequence)
        (X := vectorPathComponent Xω i)
        (T := U')
        (hKL := by
          intro s hs
          exact hHiCutSample s)
        row
  have hRawRow :
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ Hi s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row
        =
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          (afterExitMovingHorizon_theorem25_40 row T U')
          row := by
    -- Proof comment: once the sample coefficient is normalized, the existing exact/non-partition
    -- after-exit row decomposition transports the stopped row to the raw moving-horizon row.
    exact
      stoppedCoordinateRow_eq_rawMovingHorizon_afterExit_theorem25_40
        (Wc := Wc)
        (G := G)
        (F := F)
        i
        (vectorPathComponent Xω i)
        (ω := ω)
        (t := U')
        (T := T)
        (n := row)
        (K := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        hT
        hTU
        (by
          intro j hj
          have hs_le_T :
              Definition2158.dyadicPartitionSequence row j ≤ T := by
            exact
              (partitionPoint_mem_Icc_of_lt_partitionBoundIndex
                Definition2158.dyadicPartitionSequence
                row
                j
                T
                hj).2
          have hs_cutoff :
              ((Definition2158.dyadicPartitionSequence row j : NNReal) : ENNReal) ≤
                (T : ENNReal) := by
            exact_mod_cast hs_le_T
          simpa [hs_cutoff] using
            hHiSample (Definition2158.dyadicPartitionSequence row j))
        (by
          intro hExact
          simpa [hExact] using hHiSample T)
  exact hCutToStop.trans hRawRow

/-- Helper for Theorem 25.40: once the coordinate coefficient is deterministically cut off at the
sample-specific horizon `T`, the canonical cutoff coordinate is frozen at every later time after
both time slices are identified with the same raw clipped limit. -/
private theorem constCutoffCanonicalCoordinate_freeze_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {G : Set State} {x0 : State}
    {F : State → ℝ} {B : VectorProcess}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = Wc t ω - x0)
    (i : Fin d) {T U' : NNReal}
    (hT : (T : ENNReal) = hittingAfter Wc Gᶜ 0 ω)
    (hTU : T < U')
    (hRefine :
      let F0 : State → ℝ := fun z : State ↦ F (x0 + z)
      let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                T
                (φ (ψ n)))
            atTop
            (𝓝
              (pathwiseItoIntegralAlong
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                T))) :
    let F0 : State → ℝ := fun z : State ↦ F (x0 + z)
    let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
    let hZi :
        IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        (hittingAfter Wc Gᶜ 0)
    let HiCut : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (T : ENNReal))
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut U' ω =
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut T ω := by
  intro F0 Xω ℱWc Zi hZi Hi HiCut
  have hF0 : ContDiff ℝ 2 F0 := by
    -- Proof comment: the theorem-local raw coefficient is the translated `F`, so its regularity
    -- is exactly the translated `ContDiff` package already available in the file.
    simpa [F0] using translatedContDiff_theorem25_40 (F := F) hFcontDiff x0
  have hT_le :
      (T : ENNReal) ≤ hittingAfter Wc Gᶜ 0 ω := by
    simpa [hT] using le_rfl
  have hCanonicalAtClipped :
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut T ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
    have hCanonicalHi :
        ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi T ω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := by
      -- Proof comment: first rewrite the stochastic canonical coordinate to its dyadic pathwise
      -- spelling along the fixed centered sample path.
      simpa [ℱWc, Zi, hZi, Hi, Xω] using
        canonicalCoordinate_apply_eq_centeredPathwiseItoIntegral_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B)
          hWc hWcCont ω hcontω hω i T
    have hRows :
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T
            n) =
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              T
              n) := by
      funext n
      -- Proof comment: on the clipped interval `[0, T]`, the theorem-local stopped coefficient
      -- is exactly the raw translated partial derivative along the centered sample path.
      exact
        partitionPathwiseItoApproximationUpTo_eq_of_leftEndpointEq_theorem25_40
          (P := Definition2158.dyadicPartitionSequence)
          (X := vectorPathComponent Xω i)
          (T := T)
          (row := n)
          (hKL := by
            intro j hj
            have hs_le_T :
                Definition2158.dyadicPartitionSequence n j ≤ T := by
              exact
                (partitionPoint_mem_Icc_of_lt_partitionBoundIndex
                  Definition2158.dyadicPartitionSequence
                  n
                  j
                  T
                  hj).2
            have hs_le_exit :
                ((Definition2158.dyadicPartitionSequence n j : NNReal) : ENNReal) ≤
                  hittingAfter Wc Gᶜ 0 ω := by
              exact le_trans (by exact_mod_cast hs_le_T) hT_le
            calc
              Hi (Definition2158.dyadicPartitionSequence n j) ω =
                  (∂[i] F) (x0 + B (Definition2158.dyadicPartitionSequence n j) ω) := by
                exact
                  stoppedCoordinatePartial_beforeExit_eq_theorem25_40
                    (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B) (ω := ω)
                    hω i hs_le_exit
              _ = (∂[i] F) (x0 + Xω (Definition2158.dyadicPartitionSequence n j)) := by
                    simp [Xω]
              _ = (∂[i] F0) (Xω (Definition2158.dyadicPartitionSequence n j)) := by
                    symm
                    exact
                      translatedPartialDeriv_eq_theorem25_40
                        (F := F)
                        (hF := hFcontDiff.differentiable (by norm_num))
                        x0
                        (Xω (Definition2158.dyadicPartitionSequence n j))
                        i))
    have hPathwiseEq :
        pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := by
      -- Proof comment: equality of the whole clipped dyadic row family identifies the two
      -- canonical `pathwiseItoIntegralAlong` values.
      rw [pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
      exact congrArg (limUnder atTop) hRows
    calc
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut T ω =
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi T ω := by
            exact
              continuousLocalMartingaleItoIntegralProcess_eq_constCutoffValue_theorem25_40
                (μ := (μ : Measure Ω))
                (ℱ := ℱWc)
                (M := Zi)
                (H := Hi)
                (hM := hZi)
                T
                ω
      _ =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := hCanonicalHi
      _ =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := hPathwiseEq
  have hMovingRows :
      (fun row ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ HiCut s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row) =
        fun row ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            (afterExitMovingHorizon_theorem25_40 row T U')
            row := by
    funext row
    -- Proof comment: after the exit time, every theorem-local cutoff row at horizon `U'`
    -- matches the raw moving-horizon row on the same dyadic level.
    simpa [F0, Xω, Hi, HiCut] using
      constCutoffCoordinateRows_eq_rawMovingHorizon_afterExit_theorem25_40
        (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B) (ω := ω)
        hcontω
        hω
        (hFcontDiff.differentiable (by norm_num))
        i
        (T := T)
        (U' := U')
        hT
        hTU
        row
  have hMovingLimit :
      Tendsto
        (fun row ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            (afterExitMovingHorizon_theorem25_40 row T U')
            row)
        atTop
        (𝓝
          (pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T)) := by
    -- Proof comment: the theorem-local refinement package is exactly the deterministic input
    -- needed to transport the clipped-horizon limit to the after-exit moving-horizon rows.
    exact
      rawMovingHorizon_tendsto_clippedCanonical_afterExit_theorem25_40
        (F0 := F0)
        hF0
        i
        hTU
        rfl
        (by simpa [F0, Xω] using hRefine)
  have hCanonicalAtLater :
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut U' ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
    have hCutLimit :
        Tendsto
          (fun row ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ HiCut s ω)
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              U'
              row)
          atTop
          (𝓝
            (pathwiseItoIntegralAlong
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              T)) := by
      -- Proof comment: rewrite the visible cutoff row family to the raw moving-horizon family
      -- and reuse the after-exit transport limit.
      rw [hMovingRows]
      exact hMovingLimit
    -- Proof comment: once the theorem-local cutoff row family has a genuine limit, the canonical
    -- fixed-time owner at `U'` is exactly that limit.
    rw [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess]
    exact pathwiseItoIntegralAlong_eq_of_tendsto U' hCutLimit
  -- Proof comment: both the later deterministic cutoff value and the clipped-horizon value are
  -- now identified with the same raw clipped canonical limit.
  exact hCanonicalAtLater.trans hCanonicalAtClipped.symm

/-- Helper for Theorem 25.40: the bracket witness of a deterministically cut-off coefficient is
already frozen by the same deterministic stop. -/
private theorem constCutoffBracket_eq_stoppedConstTime_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal) :
    stoppedProcess
        (bracketDensityIntegralUpTo hbr
          (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))))
        (fun _ ↦ (T : ENNReal)) =
      bracketDensityIntegralUpTo hbr
        (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) := by
  funext t ω
  by_cases ht : t ≤ T
  · -- Proof comment: before the cutoff horizon, deterministic stopping reads the same bracket
    -- witness at time `t`.
    simp [stoppedProcessConstTime_eq_min, min_eq_left ht]
  · have hTt : T ≤ t := le_of_not_ge ht
    have hTt_real : (T : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hTt
    let f : ℝ → ℝ := fun s ↦
      (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
        (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ)
    have hCutoffZero :
        ∀ ⦃s : ℝ⦄, s ∈ Set.Icc (0 : ℝ) (t : ℝ) →
          ¬ s ∈ Set.Icc (0 : ℝ) (T : ℝ) →
            f s = 0 := by
      intro s hs hs_not_mem
      have hsT : ¬ s ≤ (T : ℝ) := by
        intro hs_le_T
        exact hs_not_mem ⟨hs.1, hs_le_T⟩
      have hs_not_cutoff : ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
        intro hs_cutoff
        exact hsT ((Real.toNNReal_le_iff_le_coe).1 (by exact_mod_cast hs_cutoff))
      -- Proof comment: beyond `T`, the deterministic cutoff kills the coefficient, so the
      -- bracket-density integrand itself vanishes.
      simp [f, ProbabilityTheory.processBeforeStoppingTime_apply, hs_not_cutoff]
    have hIndicatorEq :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), f s) =
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := by
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro s hs
      by_cases hs_mem : s ∈ Set.Icc (0 : ℝ) (T : ℝ)
      · -- Proof comment: on `[0,T]`, the indicator leaves the bracket-density integrand
        -- unchanged.
        simp [Set.indicator_of_mem, hs_mem]
      · -- Proof comment: on `(T,t]`, the deterministic cutoff has already forced the integrand
        -- to vanish.
        simp [Set.indicator_of_notMem, hs_mem, hCutoffZero hs hs_mem]
    have hSubset :
        Set.Icc (0 : ℝ) (T : ℝ) ⊆ Set.Icc (0 : ℝ) (t : ℝ) := by
      intro s hs
      exact ⟨hs.1, hs.2.trans hTt_real⟩
    have hFreeze :
        bracketDensityIntegralUpTo hbr
            (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
            t
            ω =
          bracketDensityIntegralUpTo hbr
            (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
            T
            ω := by
      -- Proof comment: after rewriting the later-horizon integral by the indicator of `[0,T]`,
      -- only the original interval `[0,T]` remains.
      simpa [bracketDensityIntegralUpTo, f] using
        (calc
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), f s =
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
                Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := hIndicatorEq
          _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s := by
            rw [MeasureTheory.integral_indicator measurableSet_Icc]
            simp [Measure.restrict_restrict, Set.inter_eq_right.mpr hSubset, measurableSet_Icc])
    -- Proof comment: once the bracket witness is constant after `T`, its deterministic stop at
    -- `T` is literally the same process.
    calc
      stoppedProcess
          (bracketDensityIntegralUpTo hbr
            (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))))
          (fun _ ↦ (T : ENNReal))
          t
          ω =
        bracketDensityIntegralUpTo hbr
          (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T
          ω := by
            simp [stoppedProcessConstTime_eq_min, min_eq_right hTt]
      _ =
        bracketDensityIntegralUpTo hbr
          (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          t
          ω := hFreeze.symm

/-- Helper for Theorem 25.40: on the diagonal, a square-variation witness is already the matching
quadratic-covariation witness. -/
private theorem selfContinuousQuadraticCovariation_of_squareVariation_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M A : NNReal → Ω → ℝ}
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) :
    IsContinuousQuadraticCovariationProcess ℱ μ M M A := by
  refine
    { zero := hA.zero
      adapted := hA.adapted
      continuous := hA.continuous
      locally_finite_variation := hA.locally_finite_variation
      local_martingale_mul_sub := ?_ }
  -- Proof comment: on the diagonal, the compensated product `M * M - A` is exactly the square-
  -- variation local martingale `M^2 - A`.
  simpa using hA.local_martingale_sq_sub

/-- Helper for Theorem 25.40: if two continuous local martingales share the same square-variation
witness and the same quadratic-covariation witness, then their difference has zero square
variation. -/
private theorem subZeroSquareVariation_of_sharedWitness_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A) :
    IsContinuousSquareVariationProcess ℱ μ
      (fun t ω ↦ M t ω - N t ω)
      (fun _ _ ↦ (0 : ℝ)) := by
  refine
    { zero := ?_
      adapted := ?_
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · funext ω
    simp
  · intro t
    simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
  · intro ω
    simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · intro ω s t hst
    simp
  · have hQuadCont :
        IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω) := by
      refine ⟨hQuad.local_martingale_mul_sub, ?_⟩
      intro ω
      exact (hMmart.continuous ω).mul (hNmart.continuous ω) |>.sub (hQuad.continuous ω)
    refine
      { local_martingale := ?_
        continuous := ?_ }
    · let hDoubleQuad : IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            (M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)) :=
          isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hQuadCont hQuadCont
      have hTarget :
          IsContinuousLocalMartingale ℱ μ
            (fun t ω ↦
              (M t ω ^ 2 - A t ω) +
                ((N t ω ^ 2 - A t ω) -
                  ((M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)))) :=
        isContinuousLocalMartingale_addLocal
          (ℱ := ℱ)
          (μ := μ)
          hAleft.local_martingale_sq_sub
          (isContinuousLocalMartingale_subLocal
            (ℱ := ℱ)
            (μ := μ)
            hAright.local_martingale_sq_sub
            hDoubleQuad)
      convert hTarget.local_martingale using 1
      funext t ω
      ring
    · intro ω
      let hDoubleQuad : IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            (M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)) :=
          isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hQuadCont hQuadCont
      let hTarget :
          IsContinuousLocalMartingale ℱ μ
            (fun t ω ↦
              (M t ω ^ 2 - A t ω) +
                ((N t ω ^ 2 - A t ω) -
                  ((M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)))) :=
        isContinuousLocalMartingale_addLocal
          (ℱ := ℱ)
          (μ := μ)
          hAleft.local_martingale_sq_sub
          (isContinuousLocalMartingale_subLocal
            (ℱ := ℱ)
            (μ := μ)
            hAright.local_martingale_sq_sub
            hDoubleQuad)
      simpa using hTarget.continuous ω

/-- Helper for Theorem 25.40: a continuous local martingale with zero square variation is almost
surely zero at every deterministic time once its initial value vanishes almost surely. -/
private theorem aeEqZeroAtTimeOfZeroSquareVariation_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hXsq : IsContinuousSquareVariationProcess ℱ μ X (fun _ _ ↦ (0 : ℝ)))
    (hX0 : X 0 =ᵐ[μ] fun _ : Ω ↦ 0)
    (T : NNReal) :
    X T =ᵐ[μ] fun _ : Ω ↦ 0 := by
  rcases _root_.ProbabilityTheory.existsUnique_continuousSquareVariationProcess
      (ℱ := ℱ) (μ := μ) hX with
    ⟨B, _hB, huniq⟩
  have hCanonEqB :
      AreIndistinguishable μ (⟨X⟩[hX]) B := by
    exact huniq _ (continuousSquareVariationProcess_spec hX)
  have hBEqZero :
      AreIndistinguishable μ B (fun _ _ ↦ (0 : ℝ)) := by
    exact huniq _ hXsq
  have hCanonEqZero :
      AreIndistinguishable μ (⟨X⟩[hX]) (fun _ _ ↦ (0 : ℝ)) := by
    exact areIndistinguishable_trans hCanonEqB hBEqZero
  have hZeroAllTimes :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0 := by
    rcases hCanonEqZero with ⟨bad, _hbad_meas, hbad_null, hbad_sub⟩
    have hbad_ae : ∀ᵐ ω ∂μ, ω ∉ bad :=
      compl_mem_ae_iff.mpr hbad_null
    filter_upwards [hbad_ae] with ω hωbad t
    by_contra hneq
    exact hωbad (hbad_sub t hneq)
  have hConstAtTime :
      X T =ᵐ[μ] X 0 :=
    ae_eq_initial_at_time_of_ae_squareVariation_eq_zero ℱ hX hZeroAllTimes T
  exact hConstAtTime.trans hX0

/-- Helper for Theorem 25.40: shared square-variation and quadratic-covariation witnesses force
two continuous local martingales to agree almost surely at any fixed deterministic time once
their initial values agree. -/
private theorem aeEqAtTimeOfSharedWitness_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hZero : M 0 =ᵐ[μ] N 0)
    (T : NNReal) :
    M T =ᵐ[μ] N T := by
  have hSubSq :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦ M t ω - N t ω)
        (fun _ _ ↦ (0 : ℝ)) :=
    subZeroSquareVariation_of_sharedWitness_theorem25_40
      hMmart hNmart hAleft hAright hQuad
  have hSubZero :
      (fun ω ↦ M 0 ω - N 0 ω) =ᵐ[μ] fun _ : Ω ↦ 0 := by
    -- Proof comment: the shared initial-value hypothesis turns the difference process into a
    -- zero-start continuous local martingale.
    filter_upwards [hZero] with ω hω
    simp [hω]
  have hSubAtTime :
      (fun ω ↦ M T ω - N T ω) =ᵐ[μ] fun _ : Ω ↦ 0 :=
    aeEqZeroAtTimeOfZeroSquareVariation_theorem25_40
      (ℱ := ℱ)
      (μ := μ)
      (X := fun t ω ↦ M t ω - N t ω)
      (isContinuousLocalMartingale_subLocal (ℱ := ℱ) (μ := μ) hMmart hNmart)
      hSubSq
      hSubZero
      T
  -- Proof comment: once the difference vanishes almost surely at time `T`, the endpoint values
  -- must agree there.
  filter_upwards [hSubAtTime] with ω hω
  exact sub_eq_zero.mp hω

/-- Helper for Theorem 25.40: if two continuous compensators agree up to `T` off one null set and
are both frozen after `T`, then they agree for all deterministic times off one null set. -/
private theorem aeEqAllTimesOfEqUpToAndFrozenAfter_theorem25_40
    {μ : Measure Ω} {A B : NNReal → Ω → ℝ}
    {T : NNReal}
    (hEq : EqUpTo μ T A B)
    (hAfreeze :
      ∀ ω : Ω, ∀ t : NNReal, T ≤ t → A t ω = A T ω)
    (hBfreeze :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → B t ω = B T ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEq with
    ⟨S, _hSmeas, hSnull, hSeq⟩
  have hSae : ∀ᵐ ω ∂μ, ω ∉ S :=
    compl_mem_ae_iff.mpr hSnull
  filter_upwards [hSae, hBfreeze] with ω hωS hBω t
  by_cases ht : t ≤ T
  · -- Proof comment: below the horizon, the original `EqUpTo` witness already gives the pointwise
    -- compensator equality.
    exact hSeq ht hωS
  · have hTt : T ≤ t := le_of_not_ge ht
    -- Proof comment: above `T`, both compensators collapse to their terminal time-`T` value.
    calc
      A t ω = A T ω := hAfreeze ω t hTt
      _ = B T ω := hSeq le_rfl hωS
      _ = B t ω := (hBω t hTt).symm

/-- Helper for Theorem 25.40: an all-times almost-sure compensator identity transports a genuine
quadratic-covariation witness to the replacement compensator. -/
private theorem continuousQuadraticCovariation_of_ae_eq_allTimes_compensator_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A B : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hCovB : IsContinuousQuadraticCovariationProcess ℱ μ M N B)
    (hAzero : A 0 = 0)
    (hAadapted : Adapted ℱ A)
    (hAcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ A t ω)
    (hALFV :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ A t ω, hAcont ω⟩ : C(NNReal, ℝ))
          Set.univ)
    (hABall : ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω) :
    IsContinuousQuadraticCovariationProcess ℱ μ M N A := by
  have hMulAdapted :
      Adapted ℱ (fun t ω ↦ M t ω * N t ω) := by
    exact hM.adapted.mul hN.adapted
  have hMulCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω * N t ω := by
    intro ω
    exact (hM.continuous ω).mul (hN.continuous ω)
  refine
    { zero := hAzero
      adapted := hAadapted
      continuous := hAcont
      locally_finite_variation := hALFV
      local_martingale_mul_sub := ?_ }
  -- Proof comment: once `A` and `B` agree at all deterministic times outside one null set, the
  -- compensated product local martingale transports from `B` to `A`.
  exact
    isLocalMartingale_congr_ae_allTimes_theorem25_40
      hCovB.local_martingale_mul_sub
      (hMulAdapted.sub hAadapted)
      (fun ω ↦ (hMulCont ω).sub (hAcont ω))
      (by
        filter_upwards [hABall] with ω hω t
        simp [hω t])

/-- Helper for Theorem 25.40: once the right path is frozen after `T`, the dyadic mixed row at a
later horizon differs from the horizon-`T` row by one explicit boundary increment. -/
private theorem
    partitionQuadraticCovariationSum_eq_terminal_plus_boundary_of_rightConstAfter_theorem25_40
    {F G : PathSpace}
    {T t : NNReal}
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T)
    (n : ℕ) :
    partitionQuadraticCovariationSum
        Definition2158.dyadicPartitionSequence
        F
        G
        t
        n =
      partitionQuadraticCovariationSum
          Definition2158.dyadicPartitionSequence
          F
          G
          T
          n +
        (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
            F T) *
          (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
  let P := Definition2158.dyadicPartitionSequence
  let K := partitionBoundIndex P n T
  let N := partitionBoundIndex P n t
  let termt : ℕ → ℝ := fun k ↦
    (F (partitionNextPointUpTo P n k t) - F (P n k)) *
      (G (partitionNextPointUpTo P n k t) - G (P n k))
  let termT : ℕ → ℝ := fun k ↦
    (F (partitionNextPointUpTo P n k T) - F (P n k)) *
      (G (partitionNextPointUpTo P n k T) - G (P n k))
  have hKN : K ≤ N := dyadicPartitionBoundIndex_monotone n hTt
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [K, hK0] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by
        simpa [P, Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hle0' bot_le
    subst hT0
    have hsumt_zero :
        partitionQuadraticCovariationSum P F G t n = 0 := by
      rw [partitionQuadraticCovariationSum]
      have htail :
          ∀ k ∈ Finset.range (partitionBoundIndex P n t), termt k = 0 := by
        intro k hk
        have hk_mem :
            P n k ∈ Set.Icc 0 t :=
          Theorem25_22.partitionPoint_mem_Icc_of_lt_partitionBoundIndex
            P n k t (Finset.mem_range.mp hk)
        have hnext_mem :
            partitionNextPointUpTo P n k t ∈ Set.Icc 0 t := by
          constructor
          · exact bot_le
          · simp [partitionNextPointUpTo]
        have hleft : G (P n k) = G 0 := hGconst (P n k) hk_mem.1
        have hright : G (partitionNextPointUpTo P n k t) = G 0 := hGconst _ hnext_mem.1
        -- Proof comment: once the right path is frozen from time `0`, every mixed increment is
        -- zero.
        simp [termt, hleft, hright]
      refine Finset.sum_eq_zero ?_
      intro k hk
      exact htail k hk
    have hsumT_zero :
        partitionQuadraticCovariationSum P F G 0 n = 0 := by
      simp [P, partitionQuadraticCovariationSum, dyadicPartitionBoundIndex_zero]
    -- Proof comment: if `T = 0`, both truncated mixed rows and the boundary factor vanish.
    simp [P, K, hK0, hsumt_zero, hsumT_zero, dyadicSquareVariationBoundaryPoint,
      Definition2158.dyadicPartitionSequence, partitionNextPointUpTo]
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, K = j + 1 := ⟨K - 1, (Nat.sub_add_cancel hKpos).symm⟩
    have hjBoundT : j < K := by
      rw [hj]
      exact Nat.lt_succ_self j
    have hjBoundt : j < N := lt_of_lt_of_le hjBoundT hKN
    have hPj_lt_T : P n j < T := by
      simpa [K] using dyadicPartition_lt_time_of_lt_boundIndex n hjBoundT
    have hPj1_ge_T : T ≤ P n (j + 1) := by
      simpa [K, hj] using le_partitionBoundIndex_time P n T
    have htruncate_t :
        partitionQuadraticCovariationSum P F G t n =
          Finset.sum (Finset.range (j + 1)) termt := by
      rw [partitionQuadraticCovariationSum]
      have hsplit :
          Finset.sum (Finset.range N) termt =
            Finset.sum (Finset.range (j + 1)) termt +
              Finset.sum (Finset.Ico (j + 1) N) termt := by
        symm
        exact Finset.sum_range_add_sum_Ico termt (Nat.succ_le_of_lt hjBoundt)
      have htail :
          Finset.sum (Finset.Ico (j + 1) N) termt = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        have hk_ge : j + 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hPk_ge_T : T ≤ P n k := by
          exact le_trans hPj1_ge_T
            ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone hk_ge)
        have hk_lt_N : k < N := (Finset.mem_Ico.mp hk).2
        have hnext_ge_T : T ≤ partitionNextPointUpTo P n k t := by
          rw [partitionNextPointUpTo]
          exact le_min
            (le_trans hPk_ge_T
              ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone
                (Nat.le_succ k)))
            hTt
        have hleft : G (P n k) = G T := hGconst _ hPk_ge_T
        have hright : G (partitionNextPointUpTo P n k t) = G T := hGconst _ hnext_ge_T
        -- Proof comment: every cell strictly after the boundary cell contributes zero because
        -- the right path is already frozen there.
        simp [termt, hleft, hright]
      rw [hsplit, htail, add_zero]
    have hprefix :
        Finset.sum (Finset.range j) termt =
          Finset.sum (Finset.range j) termT := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk_lt_j : k < j := Finset.mem_range.mp hk
      have hk1_lt_K : k + 1 < K := by
        rw [hj]
        exact Nat.succ_lt_succ hk_lt_j
      have hk1_lt_T : P n (k + 1) < T := by
        simpa [K] using dyadicPartition_lt_time_of_lt_boundIndex n hk1_lt_K
      have hnext_t :
          partitionNextPointUpTo P n k t = P n (k + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (lt_of_lt_of_le hk1_lt_T hTt)
      have hnext_T :
          partitionNextPointUpTo P n k T = P n (k + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt hk1_lt_T
      -- Proof comment: strictly before the boundary cell, the two horizons use the same
      -- successor point.
      simp [termt, termT, hnext_t, hnext_T]
    have htermT_last :
        termT j =
          (F T - F (dyadicSquareVariationBoundaryPoint T n)) *
            (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
      have hnext_T :
          partitionNextPointUpTo P n j T = T := by
        rw [partitionNextPointUpTo, min_eq_right hPj1_ge_T]
      have hboundary :
          dyadicSquareVariationBoundaryPoint T n = P n j := by
        simp [dyadicSquareVariationBoundaryPoint, P, K, hj]
      -- Proof comment: on the last horizon-`T` cell, the right endpoint is exactly `T`.
      simp [termT, hnext_T, hboundary]
    have htermt_last :
        termt j =
          (F (partitionNextPointUpTo P n j t) - F (dyadicSquareVariationBoundaryPoint T n)) *
            (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
      have hnext_ge_T : T ≤ partitionNextPointUpTo P n j t := by
        rw [partitionNextPointUpTo]
        exact le_min
          (le_trans hPj1_ge_T
            ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone
              (Nat.le_succ j)))
          hTt
      have hboundary :
          dyadicSquareVariationBoundaryPoint T n = P n j := by
        simp [dyadicSquareVariationBoundaryPoint, P, K, hj]
      have hfreeze :
          G (partitionNextPointUpTo P n j t) = G T := hGconst _ hnext_ge_T
      -- Proof comment: on the unique boundary cell, only the right increment freezes.
      simp [termt, hfreeze, hboundary]
    have hsumT :
        partitionQuadraticCovariationSum P F G T n =
          Finset.sum (Finset.range j) termT + termT j := by
      simp [partitionQuadraticCovariationSum, K, hj, termT, Finset.sum_range_succ]
    have hsumt :
        partitionQuadraticCovariationSum P F G t n =
          Finset.sum (Finset.range j) termt + termt j := by
      rw [htruncate_t, Finset.sum_range_succ]
    -- Proof comment: after canceling the common prefix, only the explicit boundary increment
    -- remains.
    calc
      partitionQuadraticCovariationSum P F G t n
          = Finset.sum (Finset.range j) termT + termt j := by
              rw [hsumt, hprefix]
      _ = partitionQuadraticCovariationSum P F G T n - termT j + termt j := by
            rw [hsumT]
            ring
      _ = partitionQuadraticCovariationSum P F G T n +
            ((F (partitionNextPointUpTo P n j t) - F T) *
                (G T - G (dyadicSquareVariationBoundaryPoint T n))) := by
            rw [htermT_last, htermt_last]
            ring
      _ = partitionQuadraticCovariationSum P F G T n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n))) := by
            simp [P, K, hj]

/-- Helper for Theorem 25.40: if `T < t`, the clipped successor of the predecessor cell for `T`
at horizon `t` still converges back to `T`. -/
private theorem tendsto_boundarySuccessor_of_lt_theorem25_40
    (t T : NNReal)
    (hTt : T < t) :
    Tendsto
      (fun n ↦
        partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
          t)
      atTop
      (𝓝 T) := by
  let P := Definition2158.dyadicPartitionSequence
  let pred : ℕ → NNReal := fun n ↦ dyadicSquareVariationBoundaryPoint T n
  let succ : ℕ → NNReal := fun n ↦
    partitionNextPointUpTo P n (partitionBoundIndex P n T - 1) t
  have hpred : Tendsto pred atTop (𝓝 T) := tendsto_dyadicSquareVariationBoundaryPoint T
  have hmesh :
      Tendsto (fun n : ℕ ↦ partitionMesh P n) atTop (𝓝 0) :=
    Definition2158.tendsto_partitionMesh_dyadicPartitionSequence
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hεhalf : 0 < ε / 2 := by positivity
  rcases Metric.tendsto_atTop.1 hpred (ε / 2) hεhalf with ⟨N₁, hN₁⟩
  rcases
      (ENNReal.tendsto_atTop_zero.mp hmesh) (ENNReal.ofReal (ε / 2))
        (ENNReal.ofReal_pos.mpr hεhalf) with
    ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hpred_dist : dist (pred n) T < ε / 2 := hN₁ n hn₁
  have hpred_le_T : pred n ≤ T := by
    simpa [pred, dyadicSquareVariationBoundaryPoint, dyadicPartitionPredecessorPoint] using
      dyadicPartitionPredecessorPoint_le_time n T
  have hpred_lt : pred n < t := lt_of_le_of_lt hpred_le_T hTt
  have hpred_lt_bound :
      partitionBoundIndex P n T - 1 < partitionBoundIndex P n t := by
    have hpred_eq :
        pred n = P n (partitionBoundIndex P n T - 1) := by
      rfl
    have hlt :
        P n (partitionBoundIndex P n T - 1) < t := by
      simpa [hpred_eq] using hpred_lt
    exact lt_partitionBoundIndex_of_dyadicPartitionPoint_lt_time n
      (partitionBoundIndex P n T - 1) t hlt
  have hsucc_edist :
      edist (pred n) (succ n) ≤ partitionMesh P n := by
    simpa [pred, succ, P] using
      edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n
        (partitionBoundIndex P n T - 1) t hpred_lt_bound
  have hsucc_dist :
      dist (pred n) (succ n) ≤ ε / 2 := by
    have hmesh_le :
        partitionMesh P n ≤ ENNReal.ofReal (ε / 2) := hN₂ n hn₂
    have hsucc_edist' :
        edist (pred n) (succ n) ≤ ENNReal.ofReal (ε / 2) :=
      le_trans hsucc_edist hmesh_le
    exact
      (ENNReal.ofReal_le_ofReal_iff hεhalf.le).mp
        (by simpa [edist_dist] using hsucc_edist')
  -- Proof comment: the predecessor already converges to `T`, and the successor stays within one
  -- mesh width of that predecessor.
  calc
    dist (succ n) T ≤ dist (succ n) (pred n) + dist T (pred n) :=
      dist_triangle_right (succ n) T (pred n)
    _ < ε / 2 + ε / 2 := by
      exact add_lt_add_of_le_of_lt
        (by simpa [dist_comm] using hsucc_dist)
        (by simpa [dist_comm] using hpred_dist)
    _ = ε := by ring

/-- Helper for Theorem 25.40: if the right path is frozen after `T`, the unique boundary
increment relating the horizon-`t` and horizon-`T` dyadic mixed rows vanishes. -/
private theorem tendsto_boundaryMixedIncrement_zero_of_rightConstAfter_theorem25_40
    {F G : PathSpace}
    {T t : NNReal}
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T) :
    Tendsto
      (fun n ↦
        (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
            F T) *
          (G T - G (dyadicSquareVariationBoundaryPoint T n)))
      atTop
      (𝓝 0) := by
  by_cases hEq : t = T
  · subst hEq
    -- Proof comment: at the terminal horizon itself, the boundary factor is identically zero.
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    rcases Nat.eq_zero_or_pos
        (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) with hidx | hidx
    · have hT0 : T = 0 := by
        have hle0 : T ≤ Definition2158.dyadicPartitionSequence n 0 := by
          simpa [hidx] using
            le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
        have hle0' : T ≤ 0 := by
          simpa [Definition2158.dyadicPartitionSequence] using hle0
        exact le_antisymm hle0' bot_le
      simp [dyadicSquareVariationBoundaryPoint, hidx, hT0]
    · obtain ⟨j, hj⟩ :
          ∃ j : ℕ,
            partitionBoundIndex Definition2158.dyadicPartitionSequence n T = j + 1 :=
          ⟨partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1,
            (Nat.sub_add_cancel hidx).symm⟩
      have hnext :
          partitionNextPointUpTo Definition2158.dyadicPartitionSequence n j T = T := by
        have hT_le :
            T ≤ Definition2158.dyadicPartitionSequence n (j + 1) := by
          simpa [hj] using
            le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
        rw [partitionNextPointUpTo, min_eq_right hT_le]
      simp [hj, hnext]
  · have hLt : T < t := lt_of_le_of_ne hTt (Ne.symm hEq)
    have hsucc :
        Tendsto
          (fun n ↦
            F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t))
          atTop
          (𝓝 (F T)) :=
      F.continuous.continuousAt.tendsto.comp
        (tendsto_boundarySuccessor_of_lt_theorem25_40 t T hLt)
    have hpred :
        Tendsto (fun n ↦ G (dyadicSquareVariationBoundaryPoint T n)) atTop (𝓝 (G T)) :=
      G.continuous.continuousAt.tendsto.comp
        (tendsto_dyadicSquareVariationBoundaryPoint T)
    have hleft :
        Tendsto
          (fun n ↦
            F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) - F T)
          atTop
          (𝓝 0) := by
      simpa using hsucc.sub tendsto_const_nhds
    have hright :
        Tendsto (fun n ↦ G T - G (dyadicSquareVariationBoundaryPoint T n))
          atTop
          (𝓝 0) := by
      simpa using tendsto_const_nhds.sub hpred
    -- Proof comment: both boundary endpoints converge to `T`, so each factor vanishes.
    simpa using hleft.mul hright

/-- Helper for Theorem 25.40: a pathwise quadratic-covariation witness against a path that is
constant after `T` must itself be frozen after `T`. -/
private theorem hasQuadraticCovariationAlong_eq_terminal_of_rightConstAfter_theorem25_40
    {F G : PathSpace}
    {B : NNReal → ℝ}
    {T t : NNReal}
    (hB : HasQuadraticCovariationAlong F G B)
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T) :
    B t = B T := by
  have hrewrite :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            T
            n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n))))
        atTop
        (𝓝 (B T)) := by
    simpa using
      (HasQuadraticCovariationAlong.tendsto_partition_sum hB T).add
        (tendsto_boundaryMixedIncrement_zero_of_rightConstAfter_theorem25_40
          (F := F) (G := G) hTt hGconst)
  have hEqRows :
      (fun n ↦
        partitionQuadraticCovariationSum
          Definition2158.dyadicPartitionSequence
          F
          G
          t
          n) =ᶠ[atTop]
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            T
            n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n)))) :=
    Filter.Eventually.of_forall fun n ↦
      partitionQuadraticCovariationSum_eq_terminal_plus_boundary_of_rightConstAfter_theorem25_40
        (F := F) (G := G) hTt hGconst n
  have hLimitAtT :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            t
            n)
        atTop
        (𝓝 (B T)) :=
    Tendsto.congr' hEqRows hrewrite
  -- Proof comment: the same dyadic mixed row at horizon `t` converges both to `B t` and to
  -- `B T`, so uniqueness of limits freezes the witness.
  exact tendsto_nhds_unique
    (HasQuadraticCovariationAlong.tendsto_partition_sum hB t)
    hLimitAtT

/-- Helper for Theorem 25.40: a genuine quadratic-covariation process with the second coordinate
deterministically stopped at `T` has a compensator frozen almost surely after `T`. -/
private theorem aeCompensatorEqTerminalOfRightStoppedCovariation_theorem25_40
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X A : NNReal → Ω → ℝ}
    (T : NNReal)
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hA :
      IsContinuousQuadraticCovariationProcess ℱ μ
        X
        (stoppedProcess X (fun _ ↦ (T : ENNReal)))
        A) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
  let Xstop : NNReal → Ω → ℝ := stoppedProcess X (fun _ ↦ (T : ENNReal))
  have hXstop :
      IsContinuousLocalMartingale ℱ μ Xstop := by
    refine
      { local_martingale :=
          _root_.ProbabilityTheory.isLocalMartingale_stoppedProcess
            hX.local_martingale
            hX.continuous
            (isStoppingTime_const ℱ T)
        continuous := ?_ }
    intro ω
    exact continuous_stoppedProcess_of_continuous hX.continuous ω
  filter_upwards
    [aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
      (μ := μ)
      (ℱ := ℱ)
      (M := X)
      (N := Xstop)
      (A := A)
      hX
      hXstop
      hA] with ω hω t hTt
  let F : PathSpace := ⟨fun s ↦ X s ω, hX.continuous ω⟩
  let G : PathSpace := ⟨fun s ↦ Xstop s ω, hXstop.continuous ω⟩
  have hGconst : ∀ s : NNReal, T ≤ s → G s = G T := by
    intro s hs
    -- Proof comment: after the deterministic stop time, the second path is literally frozen at
    -- the value `X T ω`.
    calc
      G s = X T ω := by
        simp [G, Xstop, stoppedProcessConstTime_eq_min, min_eq_right hs]
      _ = G T := by
        simp [G, Xstop, stoppedProcessConstTime_eq_min]
  simpa [F, G] using
    hasQuadraticCovariationAlong_eq_terminal_of_rightConstAfter_theorem25_40
      (F := F)
      (G := G)
      (B := fun s ↦ A s ω)
      hω
      hTt
      hGconst

/-- Helper for Theorem 25.40: for a deterministic cutoff `T`, the canonical cutoff coordinate is
almost surely frozen at every later deterministic time. -/
private theorem constCutoffCanonicalCoordinate_ae_eq_terminalValue_of_le_theorem25_40
    {μ : ProbabilityMeasure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ (μ : Measure Ω) M}
    {hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation M hM}
    (T U : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hTU : T ≤ U) :
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM
        (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        U =ᵐ[(μ : Measure Ω)]
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM
        (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        T := by
  let Ncut :
      NNReal → Ω → ℝ :=
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM
      (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  let Nstop :
      NNReal → Ω → ℝ :=
    stoppedProcess Ncut (fun _ ↦ (T : ENNReal))
  let A :
      NNReal → Ω → ℝ :=
    bracketDensityIntegralUpTo hbr
      (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  have hCanonical :
      IsContinuousLocalMartingale ℱ (μ : Measure Ω) Ncut ∧
        IsContinuousSquareVariationProcess ℱ (μ : Measure Ω) Ncut A := by
    -- Proof comment: the Chapter 25.21 canonical global clauses already package the deterministic
    -- cutoff coordinate and its bracket witness.
    simpa [Ncut, A] using
      canonicalConstCutoffGlobalClauses
        (μ := (μ : Measure Ω))
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        (hbr := hbr)
        T
        hH_prog
        hH_sq
  have hStoppedMart :
      IsLocalMartingale ℱ (μ : Measure Ω) Nstop := by
    -- Proof comment: deterministic stopping preserves the local-martingale clause of the
    -- canonical cutoff coordinate.
    simpa [Nstop] using
      _root_.ProbabilityTheory.isLocalMartingale_stoppedProcess
        hCanonical.1.local_martingale
        hCanonical.1.continuous
        (isStoppingTime_const ℱ T)
  have hStoppedCanonical :
      IsContinuousLocalMartingale ℱ (μ : Measure Ω) Nstop := by
    refine
      { local_martingale := hStoppedMart
        continuous := ?_ }
    intro ω
    simpa [Nstop] using continuous_stoppedProcess_of_continuous hCanonical.1.continuous ω
  have hStoppedSq :
      IsContinuousSquareVariationProcess ℱ (μ : Measure Ω) Nstop A := by
    have hStoppedSqRaw :
        IsContinuousSquareVariationProcess ℱ (μ : Measure Ω)
          Nstop
          (stoppedProcess A (fun _ ↦ (T : ENNReal))) := by
      -- Proof comment: first stop the canonical square-variation witness at the same
      -- deterministic horizon.
      simpa [Nstop, A] using
        _root_.ProbabilityTheory.stoppedSquareVariationProcess
          (ℱ := ℱ)
          (μ := (μ : Measure Ω))
          hCanonical.2
          (isStoppingTime_const ℱ T)
    -- Proof comment: for a deterministic cutoff coefficient, the bracket witness is already
    -- frozen after `T`, so stopping it does not change the process.
    simpa [A, constCutoffBracket_eq_stoppedConstTime_theorem25_40
      (μ := (μ : Measure Ω)) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using
      hStoppedSqRaw
  have hEqUpTo :
      EqUpTo (μ : Measure Ω) T Ncut Nstop := by
    refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
    intro t ht ω hω
    exact hω (by
      simpa [Nstop, stoppedProcessConstTime_eq_min, min_eq_left ht])
  have hSelfQuad :
      IsContinuousQuadraticCovariationProcess ℱ (μ : Measure Ω) Ncut Ncut A := by
    exact selfContinuousQuadraticCovariation_of_squareVariation_theorem25_40 hCanonical.2
  have hCross :
      IsContinuousQuadraticCovariationProcess ℱ (μ : Measure Ω) Ncut Nstop A := by
    rcases
        _root_.ProbabilityTheory.existsUnique_continuousQuadraticCovariationProcess
          (((ProbabilityTheory.mem_Mlocc_iff ℱ (μ : Measure Ω) Ncut)).2 hCanonical.1)
          (((ProbabilityTheory.mem_Mlocc_iff ℱ (μ : Measure Ω) Nstop)).2 hStoppedCanonical) with
      ⟨B, hCrossRaw, _huniq⟩
    have hCanonicalEqB :
        EqUpTo (μ : Measure Ω) T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM hM
            (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          B := by
      exact
        eqUpTo_quadraticCovariationIntegralUpTo_of_continuousQuadraticCovariationProcessLocal
          (μ := (μ : Measure Ω))
          (ℱ := ℱ)
          (M₁ := M)
          (M₂ := M)
          (H₁ := H)
          (H₂ := H)
          (hM₁ := hM)
          (hM₂ := hM)
          (hbr₁ := hbr)
          (hbr₂ := hbr)
          T
          (eqUpTo_rfl (μ := (μ : Measure Ω)) T Ncut)
          hEqUpTo
          hCanonical.1
          hStoppedCanonical
          hCanonical.2
          hStoppedSq
          hCrossRaw
    have hCanonicalEqA :
        EqUpTo (μ : Measure Ω) T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM hM
            (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          A := by
      exact
        eqUpTo_quadraticCovariationIntegralUpTo_of_continuousQuadraticCovariationProcessLocal
          (μ := (μ : Measure Ω))
          (ℱ := ℱ)
          (M₁ := M)
          (M₂ := M)
          (H₁ := H)
          (H₂ := H)
          (hM₁ := hM)
          (hM₂ := hM)
          (hbr₁ := hbr)
          (hbr₂ := hbr)
          T
          (eqUpTo_rfl (μ := (μ : Measure Ω)) T Ncut)
          (eqUpTo_rfl (μ := (μ : Measure Ω)) T Ncut)
          hCanonical.1
          hCanonical.1
          hCanonical.2
          hCanonical.2
          hSelfQuad
    have hEqBAUpTo : EqUpTo (μ : Measure Ω) T B A := by
      -- Proof comment: both compensators agree on `[0,T]` with the same canonical mixed bracket.
      exact eqUpTo_trans (eqUpTo_sym hCanonicalEqB) hCanonicalEqA
    have hAfreeze :
        ∀ ω : Ω, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
      intro ω t hTt
      have hAeq :
          stoppedProcess A (fun _ ↦ (T : ENNReal)) t ω = A t ω := by
        simpa [A, constCutoffBracket_eq_stoppedConstTime_theorem25_40
          (μ := (μ : Measure Ω)) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using rfl
      calc
        A t ω = stoppedProcess A (fun _ ↦ (T : ENNReal)) t ω := hAeq.symm
        _ = A T ω := by
          simpa [stoppedProcessConstTime_eq_min, min_eq_right hTt] using
            congrFun (stoppedProcessConstTime_eq_min (X := A) T t) ω
    have hBfreeze :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, T ≤ t → B t ω = B T ω := by
      -- Route correction: freeze the genuine witness by the new pathwise right-constant
      -- covariation argument, not by another owner-side construction.
      exact
        aeCompensatorEqTerminalOfRightStoppedCovariation_theorem25_40
          (μ := (μ : Measure Ω))
          (ℱ := ℱ)
          (X := Ncut)
          (A := B)
          T
          hCanonical.1
          hCrossRaw
    have hABall :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, A t ω = B t ω := by
      exact
        aeEqAllTimesOfEqUpToAndFrozenAfter_theorem25_40
          (μ := (μ : Measure Ω))
          (T := T)
          hEqBAUpTo.symm
          hAfreeze
          hBfreeze
    -- Proof comment: transport the genuine witness `B` to the canonical compensator `A` using
    -- the all-times almost-sure equality of compensators.
    exact
      continuousQuadraticCovariation_of_ae_eq_allTimes_compensator_theorem25_40
        (μ := (μ : Measure Ω))
        (ℱ := ℱ)
        hCanonical.1
        hStoppedCanonical
        hCrossRaw
        hCanonical.2.zero
        hCanonical.2.adapted
        hCanonical.2.continuous
        (locallyFiniteVariation_of_continuous_monotone
          (μ := (μ : Measure Ω))
          hCanonical.2.continuous
          hCanonical.2.monotone)
        hABall
  have hZero :
      Ncut 0 =ᵐ[(μ : Measure Ω)] Nstop 0 := by
    -- Proof comment: deterministic stopping never changes the time-`0` value.
    refine Filter.Eventually.of_forall ?_
    intro ω
    simp [Nstop, stoppedProcess]
  have hEqAtU :
      Ncut U =ᵐ[(μ : Measure Ω)] Nstop U := by
    exact
      aeEqAtTimeOfSharedWitness_theorem25_40
        (ℱ := ℱ)
        (μ := (μ : Measure Ω))
        hCanonical.1
        hStoppedCanonical
        hCanonical.2
        hStoppedSq
        hCross
        hZero
        U
  have hStoppedAtU :
      Nstop U =ᵐ[(μ : Measure Ω)] Ncut T := by
    -- Proof comment: after time `T`, the deterministic stop is literally frozen at `Ncut T`.
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [Nstop, min_eq_right hTU] using
      congrFun (stoppedProcessConstTime_eq_min (X := Ncut) T U) ω
  -- Proof comment: compare the later value with its deterministic stop and normalize that stop
  -- at time `U`.
  simpa [Ncut] using hEqAtU.trans hStoppedAtU

/-- Helper for Theorem 25.40: after moving the after-exit transport to the correct almost-sure
surface, the deterministically cut off coordinate canonical value is frozen once the exit time
has passed. -/
private theorem constCutoffCanonicalCoordinate_freeze_ae_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {G : Set State} {x0 : State}
    {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (t : NNReal) :
    let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
    let hZi :
        IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        τ
    ∀ᵐ ω ∂(μ : Measure Ω),
      let Tω : NNReal := (min (t : ENNReal) (τ ω)).untopA
      let HiCut : NNReal → Ω → ℝ :=
        ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (Tω : ENNReal))
      τ ω < t →
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω =
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω := by
  intro _B τ ℱWc Zi hZi Hi
  let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
  have hGood :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun s : NNReal ↦ B s ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          Xω ∈ (𝒞_qv^d) ∧
            ∀ i j : Fin d,
              HasQuadraticCovariationAlong
                (vectorPathComponent Xω i)
                (vectorPathComponent Xω j)
                (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      zeroPatchedCenteredGoodPath_ae_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont
  have hEqAe :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal, B s ω = Wc s ω - x0 := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc
  filter_upwards [hGood, hEqAe] with ω hGoodω hω
  intro Tω HiCut hτ_lt_t
  have hTω_ne_top : min (t : ENNReal) (τ ω) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (by simp))
  have hTω_coe : (Tω : ENNReal) = min (t : ENNReal) (τ ω) := by
    dsimp [Tω]
    rw [WithTop.untopA_eq_untop hTω_ne_top]
    exact WithTop.coe_untop _ _
  have hTω_eq_exit : (Tω : ENNReal) = τ ω := by
    rw [hTω_coe, min_eq_right (le_of_lt hτ_lt_t)]
  have hTω_lt_t : Tω < t := by
    exact_mod_cast (show (Tω : ENNReal) < (t : ENNReal) by
      rw [hTω_eq_exit]
      exact hτ_lt_t)
  rcases hGoodω with ⟨hcontω, hGoodω⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  let F0 : State → ℝ := fun z : State ↦ F (x0 + z)
  have hF0 : ContDiff ℝ 2 F0 := by
    simpa [F0] using translatedContDiff_theorem25_40 (F := F) hFcontDiff x0
  have hRefine :
      let F0 : State → ℝ := fun z : State ↦ F (x0 + z)
      let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                Tω
                (φ (ψ n)))
            atTop
            (𝓝
              (pathwiseItoIntegralAlong
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                Tω)) := by
    intro F0 Xω φ hφ
    rcases
        coordinateRefinement_onBrownianGoodCenteredPath_theorem25_40
          (F := F0)
          (hF := by simpa [F0] using hF0)
          (Xω := Xω)
          (hCov := by
            simpa [Xω] using hGoodω.2)
          i
          φ
          hφ with
      ⟨ψ, hψ, hψAll⟩
    exact ⟨ψ, hψ, hψAll Tω⟩
  -- Proof comment: after fixing one good centered path and identifying `Tω` with the exit time,
  -- the deterministic samplewise freeze theorem closes the after-exit equality.
  simpa [τ, ℱWc, Zi, hZi, Hi, HiCut, B, Xω, Tω, F0] using
    constCutoffCanonicalCoordinate_freeze_theorem25_40
      (μ := μ)
      (Wc := Wc)
      (G := G)
      (x0 := x0)
      (F := F)
      (B := B)
      hWc
      hWcCont
      hFcontDiff
      (ω := ω)
      hcontω
      hω
      i
      (T := Tω)
      (U' := t)
      hTω_eq_exit
      hTω_lt_t
      hRefine

/-- Helper for Theorem 25.40: finite sums preserve convergence, so the canonical `limUnder`
value of a finite row sum is the sum of the pointwise limits. -/
private lemma limUnder_finset_sum_eq_of_tendsto_theorem25_40
    {ι : Type _} (s : Finset ι) {f : ι → ℕ → ℝ} {L : ι → ℝ}
    (h : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (L i))) :
    limUnder atTop (fun row ↦ Finset.sum s fun i ↦ f i row) = Finset.sum s L := by
  -- Proof comment: finite sums commute with convergence, so the rowwise `limUnder` is exactly
  -- the sum of the coordinate limits.
  simpa using (tendsto_finset_sum s fun i hi ↦ h i hi).limUnder_eq

/-- Helper for Theorem 25.40: once a fixed-horizon dyadic Itô row has a genuine limit, that
limit is automatically the canonical `pathwiseItoIntegralAlong` value. -/
private theorem partitionPathwiseItoApproximationUpTo_tendsto_canonical_of_exists_limit_theorem25_40
    {H : NNReal → ℝ} {X : C(NNReal, ℝ)} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P]
    (T : NNReal)
    (hExist :
      ∃ L : ℝ,
        Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (𝓝 L)) :
    Tendsto
      (partitionPathwiseItoApproximationUpTo H X P T)
      atTop
      (𝓝 (pathwiseItoIntegralAlong H X P T)) := by
  rcases hExist with ⟨L, hL⟩
  have hCanonical : pathwiseItoIntegralAlong H X P T = L :=
    pathwiseItoIntegralAlong_eq_of_tendsto T hL
  -- Proof comment: identify the canonical `limUnder` owner with the explicit limit `L`, then
  -- reuse the established convergence to `L`.
  simpa [hCanonical] using hL

/-- Helper for Theorem 25.40: the translated diagonal Hessian correction on the clipped horizon
is exactly the stopped Laplacian integral on `[0, t]`. -/
private theorem translatedDiagIntegral_eq_stoppedLaplacianIntegral_theorem25_40
    {x0 : State} {F : State → ℝ} {B : VectorProcess} {τ : Ω → ENNReal}
    {ω : Ω} {Xω : VectorPathSpace d} {t Tω : NNReal}
    (hFcontDiff : ContDiff ℝ 2 F)
    (hXω : ∀ s : NNReal, Xω s = B s ω)
    (hTω_coe : (Tω : ENNReal) = min (t : ENNReal) (τ ω))
    (hTω_le : (Tω : ENNReal) ≤ τ ω) :
    ((1 : ℝ) / 2) *
        ∑ i : Fin d,
          ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ),
            (∂²[i, i] (fun z : State ↦ F (x0 + z))) (Xω s.toNNReal)
      =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x0 + B s ω))
              τ
              u.toNNReal
              ω := by
  let F0 : State → ℝ := fun z : State ↦ F (x0 + z)
  have hF0 : ContDiff ℝ 2 F0 := by
    simpa [F0] using translatedContDiff_theorem25_40 (F := F) hFcontDiff x0
  let rawLap : ℝ → ℝ := fun s ↦ ((1 : ℝ) / 2) * Δ F (x0 + B s.toNNReal ω)
  let stoppedLap : ℝ → ℝ := fun s ↦
    ((1 : ℝ) / 2) *
      ProbabilityTheory.processBeforeStoppingTime
        (fun u ω ↦ Δ F (x0 + B u ω))
        τ
        s.toNNReal
        ω
  have hTω_le_t : Tω ≤ t := by
    have hle : (Tω : ENNReal) ≤ (t : ENNReal) := by
      rw [hTω_coe]
      exact min_le_left _ _
    exact_mod_cast hle
  have hDiagTermInt :
      ∀ i : Fin d,
        IntegrableOn
          (fun s : ℝ ↦ (∂²[i, i] F0) (Xω s.toNNReal))
          (Set.Icc (0 : ℝ) (Tω : ℝ)) := by
    intro i
    have hCont :
        Continuous fun s : ℝ ↦ (∂²[i, i] F0) (Xω s.toNNReal) := by
      -- Proof comment: the translated second partial derivative is continuous, and the sample
      -- path stays continuous after composing with `Real.toNNReal`.
      exact
        (continuous_secondPartialDeriv F0 hF0 i i).comp
          (Xω.continuous.comp continuous_real_toNNReal)
    simpa using hCont.integrableOn_Icc
  have hDiagIntegrand :
      (fun s : ℝ ↦ ∑ i : Fin d, (∂²[i, i] F0) (Xω s.toNNReal)) =
        fun s : ℝ ↦ Δ F (x0 + B s.toNNReal ω) := by
    funext s
    calc
      ∑ i : Fin d, (∂²[i, i] F0) (Xω s.toNNReal)
          = ∑ i : Fin d, (∂²[i, i] F) (x0 + Xω s.toNNReal) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              symm
              exact
                translatedSecondPartialDeriv_eq_theorem25_40
                  (F := F) hFcontDiff x0 (Xω s.toNNReal) i i
      _ = Δ F (x0 + Xω s.toNNReal) := by
            symm
            exact laplacian_eq_sum_secondPartialDeriv F hFcontDiff (x0 + Xω s.toNNReal)
      _ = Δ F (x0 + B s.toNNReal ω) := by
            rw [hXω s.toNNReal]
  have hIndicatorSubset :
      Set.Icc (0 : ℝ) (Tω : ℝ) ⊆ Set.Icc (0 : ℝ) (t : ℝ) := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hTω_le_t⟩
  have hIndicatorEq :
      Set.indicator (Set.Icc (0 : ℝ) (Tω : ℝ)) rawLap =
        Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) stoppedLap := by
    funext s
    by_cases hsTω : s ∈ Set.Icc (0 : ℝ) (Tω : ℝ)
    · have hs_nonneg : 0 ≤ s := hsTω.1
      have hs_le_exit :
          (s.toNNReal : ENNReal) ≤ τ ω := by
        have hs_toNNReal_le_Tω : s.toNNReal ≤ Tω := by
          exact (Real.toNNReal_le_iff_le_coe).2 hsTω.2
        have hmin :
            (s.toNNReal : ENNReal) ≤ min (t : ENNReal) (τ ω) := by
          rw [← hTω_coe]
          exact_mod_cast hs_toNNReal_le_Tω
        exact (le_min_iff.mp hmin).2
      have hst : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := hIndicatorSubset hsTω
      -- Proof comment: on the clipped interval `[0, Tω]`, the stopped integrand is still the
      -- raw translated Laplacian because the exit clock has not yet been reached.
      simp [Set.indicator, hsTω, hst, stoppedLap, rawLap,
        ProbabilityTheory.processBeforeStoppingTime_apply, hs_le_exit]
    · by_cases hst : s ∈ Set.Icc (0 : ℝ) (t : ℝ)
      · have hs_nonneg : 0 ≤ s := hst.1
        have hs_not_le_Tω : ¬ s ≤ Tω := by
          intro hs_le_Tω
          exact hsTω ⟨hs_nonneg, hs_le_Tω⟩
        have hs_not_le_exit :
            ¬ (s.toNNReal : ENNReal) ≤ τ ω := by
          intro hs_le_exit
          have hs_toNNReal_le_t : s.toNNReal ≤ t := by
            exact (Real.toNNReal_le_iff_le_coe).2 hst.2
          have hs_toNNReal_le_Tω : s.toNNReal ≤ Tω := by
            have hmin :
                (s.toNNReal : ENNReal) ≤ (Tω : ENNReal) := by
              rw [hTω_coe]
              exact le_min (by exact_mod_cast hs_toNNReal_le_t) hs_le_exit
            exact_mod_cast hmin
          have hs_le_Tω : s ≤ Tω := by
            simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le_Tω
          exact hs_not_le_Tω hs_le_Tω
        -- Proof comment: on `(Tω, t]`, the clipped horizon has passed the exit time, so the
        -- stopped Laplacian integrand is forced to zero.
        simp [Set.indicator, hsTω, hst, stoppedLap, rawLap,
          ProbabilityTheory.processBeforeStoppingTime_apply, hs_not_le_exit]
      · simp [Set.indicator, hsTω, hst, stoppedLap, rawLap]
  -- Proof comment: collapse the diagonal sum to the Laplacian of `F` along the centered path and
  -- then absorb the deterministic cutoff into the stopped indicator on `[0, t]`.
  calc
    ((1 : ℝ) / 2) *
        ∑ i : Fin d,
          ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), (∂²[i, i] F0) (Xω s.toNNReal)
        =
          ((1 : ℝ) / 2) *
            ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ),
              ∑ i : Fin d, (∂²[i, i] F0) (Xω s.toNNReal) := by
            rw [← integral_finset_sum Finset.univ hDiagTermInt]
    _ = ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), rawLap s := by
          rw [← integral_const_mul]
          congr 1
          exact hDiagIntegrand
    _ = ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) (Tω : ℝ)) rawLap s := by
          rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) stoppedLap s := by
          rw [hIndicatorEq.symm]
    _ =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x0 + B s ω))
              τ
              u.toNNReal
              ω := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
          rfl

/-- Helper for Theorem 25.40: almost every sample path of a standard Brownian vector carries the
full Kronecker-delta coordinate quadratic-covariation family, written directly on the canonical
vector-path coordinates. -/
private theorem standardBrownianCoordinateCovariationFamily_ae_theorem25_40
    {μ : ProbabilityMeasure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector (μ : Measure Ω) W) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
        ∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
            (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) j)
            (fun T ↦ if i = j then (T : ℝ) else 0) := by
  have hdiag :
      ∀ i : Fin d,
        ∀ᵐ ω ∂(μ : Measure Ω),
          ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (fun T ↦ (T : ℝ)) := by
    intro i
    filter_upwards
      [(hW.isBrownianMotion i).ae_tendsto_partitionQuadraticVariationApproximationUpTo
        Definition2158.dyadicPartitionSequence] with ω hω hcontω
    -- Proof comment: the diagonal coordinate path is a scalar Brownian path, so its quadratic
    -- variation converges to the deterministic clock.
    refine selfCovariation_of_tendstoQuadraticVariation ?_
    intro T
    simpa [vectorPathComponent, processPath] using hω T
  have hoff :
      ∀ i j : Fin d, i ≠ j →
        ∀ᵐ ω ∂(μ : Measure Ω),
          ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) j)
              0 := by
    intro i j hij
    filter_upwards
      [covariation_ae_eq_zero_of_indep_brownian
        (hW.isBrownianMotion i)
        (hW.isBrownianMotion j)
        (hW.iIndepFun.indepFun hij)] with ω hω hcontω
    -- Proof comment: distinct Brownian coordinates are independent, so their pathwise quadratic
    -- covariation vanishes on the same full-measure event.
    simpa [vectorPathComponent, processPath] using
      hω
        ((continuous_apply i).comp hcontω)
        ((continuous_apply j).comp hcontω)
  have hpair :
      ∀ i j : Fin d,
        ∀ᵐ ω ∂(μ : Measure Ω),
          ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) j)
              (fun T ↦ if i = j then (T : ℝ) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      filter_upwards [hdiag i] with ω hω hcontω
      -- Proof comment: on the diagonal the Kronecker-delta primitive is exactly the time path.
      simpa using hω hcontω
    · filter_upwards [hoff i j hij] with ω hω hcontω
      -- Proof comment: off the diagonal the Kronecker-delta primitive is identically zero.
      simpa [hij] using hω hcontω
  filter_upwards
    [ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ hpair i j] with ω hω hcontω i j
  -- Proof comment: the finite index family can be intersected into one reusable almost-sure
  -- event carrying all pairwise coordinate covariations at once.
  exact hω i j hcontω

/-- Helper for Theorem 25.40: the zero-patched centered path admits one almost-sure good event on
which it is continuous and lies in the Chapter 25 class `𝒞_qv^d` with the standard Brownian
Kronecker coordinate covariations. -/
private theorem zeroPatchedCenteredGoodPath_ae_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    ∀ᵐ ω ∂(μ : Measure Ω),
      ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
        let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
        Xω ∈ (𝒞_qv^d) ∧
          ∀ i j : Fin d,
            HasQuadraticCovariationAlong
              (vectorPathComponent Xω i)
              (vectorPathComponent Xω j)
              (fun T ↦ if i = j then (T : ℝ) else 0) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  have hEqAe :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = Wc t ω - x0 := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc
  have hCovAe :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
          ∀ i j : Fin d,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) j)
              (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      standardBrownianCoordinateCovariationFamily_ae_theorem25_40
        (μ := μ)
        (W := B)
        (brownianVectorStartedAt_zeroPatched_isStandard
          (μ := (μ : Measure Ω)) (W := Wc) (x := x0) hWc)
  filter_upwards [hEqAe, hCovAe] with ω hω hCovω
  have hRawCont : Continuous fun t : NNReal ↦ Wc t ω - x0 := by
    -- Proof comment: the unpatched centered path is continuous because the Brownian stage is
    -- continuous and the deterministic center `x0` is constant.
    simpa [sub_eq_add_neg] using (hWcCont ω).add continuous_const
  have hcontω : Continuous fun t : NNReal ↦ B t ω := by
    -- Proof comment: on the almost-sure start-point event, the zero patch agrees at every time
    -- with the raw centered path, so continuity transports across that all-times equality.
    have hEq :
        (fun t : NNReal ↦ B t ω) = fun t : NNReal ↦ Wc t ω - x0 := funext hω
    exact hEq.symm ▸ hRawCont
  refine ⟨hcontω, ?_⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hFamily :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent Xω i)
          (vectorPathComponent Xω j)
          (fun T ↦ if i = j then (T : ℝ) else 0) := by
    intro i j
    simpa [Xω] using hCovω hcontω i j
  have hXω : Xω ∈ (𝒞_qv^d) := by
    refine (mem_𝒞_qv_d_iff_exists_family Xω).2 ?_
    refine ⟨fun i j ↦ fun T ↦ if i = j then (T : ℝ) else 0, ?_⟩
    intro i j
    exact hFamily i j
  -- Proof comment: one pathwise continuity witness and one Kronecker family already package the
  -- centered sample path into the Chapter 25 `𝒞_qv^d` interface.
  exact ⟨hXω, hFamily⟩

/-- Helper for Theorem 25.40: the remaining stochastic input is to identify the translated
driftless stopped surface on `[0,T]` with a finite sum of coordinate cutoff Itô owners that is a
continuous local martingale up to `T`. -/
private theorem stoppedCenteredPatchedIto_aeAllTimes_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let canonical :
        Fin d → NNReal → Ω → ℝ := fun i =>
          let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
          let hZi :
              IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
            (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
              (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
          let Hi : NNReal → Ω → ℝ :=
            ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_40
                (Ω := Ω) (Wc := Wc) (F := F) i)
              τ
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Δ F (x0 + B s ω))
                τ
                u.toNNReal
                ω =
        ∑ i : Fin d, canonical i t ω := by
  -- Route correction: the remaining blocker is the samplewise stopped-Itô identity itself, not
  -- the later `EqUpTo` packaging.
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let canonical :
      Fin d → NNReal → Ω → ℝ := fun i =>
        let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
        let hZi :
            IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            τ
        ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
  have hGood :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          Xω ∈ (𝒞_qv^d) ∧
            ∀ i j : Fin d,
              HasQuadraticCovariationAlong
                (vectorPathComponent Xω i)
                (vectorPathComponent Xω j)
                (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      zeroPatchedCenteredGoodPath_ae_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont
  have hEqAe :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = Wc t ω - x0 := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) hWc
  let F0 : State → ℝ := fun z : State ↦ F (x0 + z)
  have hF0 : ContDiff ℝ 2 F0 := by
    simpa [F0] using translatedContDiff_theorem25_40 (F := F) hFcontDiff x0
  obtain ⟨χ, hχ, hχae⟩ :=
    existsCommonCoordinateRefinementSubsequence_ae_tendsto_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (F := F0) hWc hWcCont hF0
  have hFreezeAll :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∀ i : Fin d,
          let Tω : NNReal := (min (t : ENNReal) (τ ω)).untopA
          let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
          let hZi :
              IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
            (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
              (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
          let Hi : NNReal → Ω → ℝ :=
            ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_40
                (Ω := Ω) (Wc := Wc) (F := F) i)
              τ
          let HiCut : NNReal → Ω → ℝ :=
            ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (Tω : ENNReal))
          τ ω < t →
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω := by
    rw [ae_all_iff]
    intro i
    simpa [B, τ, ℱWc] using
      constCutoffCanonicalCoordinate_freeze_ae_theorem25_40
        (μ := μ)
        (Wc := Wc)
        (G := G)
        (x0 := x0)
        (F := F)
        hWc
        hWcCont
        hFcontDiff
        i
        t
  filter_upwards [hExitFinite, hGood, hEqAe, hχae, hFreezeAll] with
      ω hτω hGoodω hω hχω hFreezeω t
  rcases hGoodω with ⟨hcontω, hGoodω⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hGoodω' :
      Xω ∈ (𝒞_qv^d) ∧
        ∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent Xω i)
            (vectorPathComponent Xω j)
            (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [Xω] using hGoodω
  have hXω : Xω ∈ (𝒞_qv^d) := hGoodω'.1
  let Tω : NNReal := (min (t : ENNReal) (τ ω)).untopA
  have hminFin : min (t : ENNReal) (τ ω) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (by simp))
  have hTω_coe : (Tω : ENNReal) = min (t : ENNReal) (τ ω) := by
    dsimp [Tω]
    rw [WithTop.untopA_eq_untop hminFin]
    exact WithTop.coe_untop _ _
  have hTω_le : (Tω : ENNReal) ≤ τ ω := by
    rw [hTω_coe]
    exact min_le_right _ _
  have hLeft :
      F0 (Xω Tω) - F0 (Xω 0) =
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω := by
    -- Proof comment: evaluating the translated observable at the clipped horizon `Tω` is exactly
    -- the theorem-local stopped surface because `Xω` is the centered sample path and `Xω 0 = 0`.
    simp [F0, Xω, Tω, stoppedProcess, B]
  let quadω : ℝ :=
    ((1 : ℝ) / 2) *
      ∑ i : Fin d, ∑ j : Fin d,
        pathwiseQuadraticCovariationIntegral
          (fun s ↦ (∂²[i, j] F0) (Xω s))
          (vectorPathComponent Xω i)
          (vectorPathComponent Xω j)
          Tω
  have hPathwiseCore :
      stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω =
        pathwiseMultidimensionalItoIntegral F0 Xω Tω + quadω := by
    -- Proof comment: apply Theorem 25.30 at the clipped horizon `Tω`, then replace the
    -- theorem-local stopped surface by the translated left side `F0 (Xω Tω) - F0 (Xω 0)`.
    calc
      stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω
          = F0 (Xω Tω) - F0 (Xω 0) := hLeft.symm
      _ =
          pathwiseMultidimensionalItoIntegral F0 Xω Tω + quadω := by
            simpa using
              pathwiseMultidimensionalItoFormula F0 hF0 Xω hXω Tω
  have hReduced :
      stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω - quadω =
        pathwiseMultidimensionalItoIntegral F0 Xω Tω := by
    -- Proof comment: after moving the raw quadratic correction to the left, the remaining term is
    -- exactly the canonical multidimensional pathwise Itô integral.
    calc
      stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω - quadω =
          (pathwiseMultidimensionalItoIntegral F0 Xω Tω + quadω) - quadω := by
          rw [hPathwiseCore]
      _ = pathwiseMultidimensionalItoIntegral F0 Xω Tω := by ring
  have hQuadDiag :
      quadω =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), (∂²[i, i] F0) (Xω s.toNNReal) := by
    -- Proof comment: the raw quadratic-covariation correction is now reduced to the diagonal
    -- set-integral family by the dedicated Kronecker-delta bridge above.
    simpa [quadω] using
      kroneckerQuadraticCorrection_eq_diagIntegrals_theorem25_40
        (F := F0) hF0 (X := Xω) hGoodω'.2 Tω
  have hCoordinateAtClipped :
      ∀ i : Fin d,
        canonical i Tω ω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω := by
    intro i
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_40
          (Ω := Ω) (Wc := Wc) (F := F) i)
        τ
    have hCanonicalHi :
        canonical i Tω ω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω := by
      -- Proof comment: first rewrite the theorem-local stochastic canonical coordinate to its
      -- dyadic pathwise spelling along the centered sample path.
      simpa [canonical, Hi, Xω] using
        canonicalCoordinate_apply_eq_centeredPathwiseItoIntegral_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B)
          hWc hWcCont ω hcontω hω i Tω
    have hRows :
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω
            n) =
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              Tω
              n) := by
      funext n
      -- Proof comment: every sampled left endpoint in the clipped row lies before the exit
      -- horizon, so the stopped coefficient agrees there with the translated raw partial
      -- derivative along the centered path.
      exact
        partitionPathwiseItoApproximationUpTo_eq_of_leftEndpointEq_theorem25_40
          (P := Definition2158.dyadicPartitionSequence)
          (X := vectorPathComponent Xω i)
          (T := Tω)
          (row := n)
          (hKL := by
            intro j hj
            have hs_le_Tω :
                Definition2158.dyadicPartitionSequence n j ≤ Tω := by
              exact
                (partitionPoint_mem_Icc_of_lt_partitionBoundIndex
                  Definition2158.dyadicPartitionSequence
                  n
                  j
                  Tω
                  hj).2
            have hs_le_exit :
                ((Definition2158.dyadicPartitionSequence n j : NNReal) : ENNReal) ≤ τ ω := by
              exact le_trans (by exact_mod_cast hs_le_Tω) hTω_le
            calc
              Hi (Definition2158.dyadicPartitionSequence n j) ω =
                  (∂[i] F) (x0 + B (Definition2158.dyadicPartitionSequence n j) ω) := by
                exact
                  stoppedCoordinatePartial_beforeExit_eq_theorem25_40
                    (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B) (ω := ω)
                    hω i hs_le_exit
              _ = (∂[i] F) (x0 + Xω (Definition2158.dyadicPartitionSequence n j)) := by
                simp [Xω]
              _ = (∂[i] F0) (Xω (Definition2158.dyadicPartitionSequence n j)) := by
                symm
                exact
                  translatedPartialDeriv_eq_theorem25_40
                    (F := F)
                    (hF := hFcontDiff.differentiable (by norm_num))
                    x0
                    (Xω (Definition2158.dyadicPartitionSequence n j))
                    i))
    have hPathwiseEq :
        pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω := by
      -- Proof comment: the canonical pathwise integral is a `limUnder` of the dyadic rows, so
      -- identical rows give identical fixed-horizon canonical values.
      rw [pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
      exact congrArg (limUnder atTop) hRows
    exact hCanonicalHi.trans hPathwiseEq
  have hRawRowDecomp :
      ∀ i : Fin d, ∀ n : ℕ,
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω
            n
          =
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)
            n
          +
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i Tω -
                vectorPathComponent Xω i
                  (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) := by
    intro i n
    -- Proof comment: the clipped raw coordinate row already splits into a predecessor-horizon row
    -- plus one explicit boundary increment on the final active cell.
    simpa using
      partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_40
        (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (X := vectorPathComponent Xω i)
        (P := Definition2158.dyadicPartitionSequence)
        (T := Tω)
        (n := n)
  have hRawBoundaryTendsto :
      ∀ i : Fin d,
        Tendsto
          (fun n ↦
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i Tω -
                vectorPathComponent Xω i
                  (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)))
          atTop
          (𝓝 0) := by
    intro i
    have hCoeffCont : Continuous fun s : NNReal ↦ (∂[i] F0) (Xω s) := by
      -- Proof comment: the translated partial derivative is continuous and the centered sample
      -- path `Xω` is continuous.
      exact (continuousPartialDeriv_theorem25_40 F0 hF0 i).comp Xω.continuous
    -- Proof comment: the explicit predecessor-cell boundary term from the raw coordinate row
    -- vanishes as the dyadic mesh shrinks.
    simpa using
      partitionItoBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_40
        (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        hCoeffCont
        (X := vectorPathComponent Xω i)
        (P := Definition2158.dyadicPartitionSequence)
        (hφ := fun a b hab ↦ hab)
        (T := Tω)
  have hRawSuccessorBoundaryTendsto :
      ∀ i : Fin d,
        Tendsto
          (fun n ↦
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i
                  (partitionNextPointUpTo
                    Definition2158.dyadicPartitionSequence
                    n
                    (partitionBoundIndex Definition2158.dyadicPartitionSequence n Tω - 1)
                    Tω) -
                vectorPathComponent Xω i Tω))
          atTop
          (𝓝 0) := by
    intro i
    have hCoeffCont : Continuous fun s : NNReal ↦ (∂[i] F0) (Xω s) := by
      -- Proof comment: the same translated partial derivative is continuous along the centered
      -- sample path, so the successor-side boundary term is controlled by the new geometric
      -- convergence lemma.
      exact (continuousPartialDeriv_theorem25_40 F0 hF0 i).comp Xω.continuous
    simpa using
      partitionItoSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_40
        (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        hCoeffCont
        (X := vectorPathComponent Xω i)
        (P := Definition2158.dyadicPartitionSequence)
        (hφ := fun a b hab ↦ hab)
        (T := Tω)
  have hSummedRawBoundaryTendsto :
      Tendsto
        (fun n ↦
          ∑ i : Fin d,
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i Tω -
                vectorPathComponent Xω i
                  (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)))
        atTop
        (𝓝 0) := by
    -- Proof comment: the finite sum of predecessor-side boundary errors still vanishes because
    -- every coordinate boundary term already tends to `0`.
    simpa using
      tendsto_finset_sum Finset.univ fun i hi ↦ hRawBoundaryTendsto i
  have hSummedRawSuccessorBoundaryTendsto :
      Tendsto
        (fun n ↦
          ∑ i : Fin d,
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i
                  (partitionNextPointUpTo
                    Definition2158.dyadicPartitionSequence
                    n
                    (partitionBoundIndex Definition2158.dyadicPartitionSequence n Tω - 1)
                    Tω) -
                vectorPathComponent Xω i Tω))
        atTop
        (𝓝 0) := by
    -- Proof comment: the same finite-sum packaging kills the successor-side boundary family.
    simpa using
      tendsto_finset_sum Finset.univ fun i hi ↦ hRawSuccessorBoundaryTendsto i
  have hDyadicMultidimTendsto :
      Tendsto
        (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F0 Xω Tω n)
        atTop
        (𝓝 (pathwiseMultidimensionalItoIntegral F0 Xω Tω)) := by
    -- Proof comment: Theorem 25.30 already gives convergence of the clipped multidimensional
    -- dyadic rows on every good centered path.
    simpa using
      tendsto_dyadicMultidimensionalItoApproximationUpTo F0 hF0 Xω hXω Tω
  have hRawClippedCoordinateSubseqTendsto :
      ∀ i : Fin d,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              Tω
              (χ n))
          atTop
          (𝓝 (canonical i Tω ω)) := by
    intro i
    -- Proof comment: the selector `χ` was chosen globally before fixing `ω`, so on this good
    -- sample path the clipped raw coordinate rows already converge to the clipped canonical
    -- limit along that common subsequence.
    simpa [hCoordinateAtClipped i] using hχω hcontω i Tω
  have hClippedFirstOrder :
      pathwiseMultidimensionalItoIntegral F0 Xω Tω = ∑ i : Fin d, canonical i Tω ω := by
    have hDyadicMultidimSubseqTendsto :
        Tendsto
          (fun n ↦
            dyadicMultidimensionalItoApproximationUpTo F0 Xω Tω (χ n))
          atTop
          (𝓝 (pathwiseMultidimensionalItoIntegral F0 Xω Tω)) :=
      hDyadicMultidimTendsto.comp hχ.tendsto_atTop
    have hSummedCoordinateSubseqTendsto :
        Tendsto
          (fun n ↦
            ∑ i : Fin d,
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                Tω
                (χ n))
          atTop
          (𝓝 (∑ i : Fin d, canonical i Tω ω)) := by
      -- Proof comment: along the common selector `χ`, every coordinate row converges on this
      -- sample path, so the finite sum converges to the sum of the coordinate limits.
      simpa using
        tendsto_finset_sum Finset.univ fun i hi ↦ hRawClippedCoordinateSubseqTendsto i
    have hDyadicToCanonical :
        Tendsto
          (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F0 Xω Tω (χ n))
          atTop
          (𝓝 (∑ i : Fin d, canonical i Tω ω)) := by
      -- Proof comment: each chosen multidimensional dyadic row is still exactly the sum of the
      -- chosen coordinate rows, so the subsequence inherits the same finite-sum limit.
      simpa [dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_40]
        using hSummedCoordinateSubseqTendsto
    -- Proof comment: the common subsequence `χ` of the multidimensional dyadic row now has two
    -- candidate limits, so uniqueness identifies the clipped Itô value with the summed clipped
    -- coordinate limit.
    exact (tendsto_nhds_unique hDyadicMultidimSubseqTendsto hDyadicToCanonical).symm
  have hFirstOrder :
      pathwiseMultidimensionalItoIntegral F0 Xω Tω = ∑ i : Fin d, canonical i t ω := by
    by_cases ht_beforeExit : (t : ENNReal) ≤ τ ω
    · have hTω_eq_t : Tω = t := by
        apply ENNReal.coe_injective
        rw [hTω_coe, min_eq_left ht_beforeExit]
      -- Proof comment: before exit, the clipped horizon is exactly `t`, so the clipped common
      -- limit `hClippedFirstOrder` already matches the target sum at time `t`.
      simpa [hTω_eq_t] using hClippedFirstOrder
    · -- Proof comment: after exit, it remains to transport each canonical stopped coordinate
      -- value from time `t` back to the clipped horizon `Tω` by comparing the stopped rows at
      -- `t` with the clipped raw rows at `Tω` through the exact/non-partition row API.
      have hAfter : τ ω < t := lt_of_not_ge ht_beforeExit
      have hTω_eq_exit : (Tω : ENNReal) = τ ω := by
        rw [hTω_coe, min_eq_right (le_of_lt hAfter)]
      have hTω_lt_t : Tω < t := by
        exact_mod_cast (show (Tω : ENNReal) < (t : ENNReal) by
          rw [hTω_eq_exit]
          exact hAfter)
      have hCoordinateAfterExit :
          ∀ i : Fin d, canonical i t ω = canonical i Tω ω := by
        intro i
        let Zi : NNReal → Ω → ℝ := fun s ξ ↦ Wc s ξ i - x0 i
        let hZi :
            IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            τ
        let HiCut : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (Tω : ENNReal))
        have hHiSample :
            ∀ s : NNReal,
              Hi s ω =
                if (s : ENNReal) ≤ (Tω : ENNReal) then
                  (∂[i] F0) (Xω s)
                else
                  0 := by
          -- Proof comment: after exit, the samplewise stopped coefficient is exactly the raw
          -- translated coefficient cut off at the clipped horizon `Tω`.
          simpa [Hi, F0, Xω, τ] using
            sampleStoppedCoordinate_eq_constCutoffRaw_theorem25_40
              (Wc := Wc) (x0 := x0) (G := G) (F := F) (B := B) (ω := ω)
              hω
              (hFcontDiff.differentiable (by norm_num))
              i
              (T := Tω)
              hTω_eq_exit
        have hHiCutSample :
            ∀ s : NNReal, HiCut s ω = Hi s ω := by
          intro s
          by_cases hs : (s : ENNReal) ≤ (Tω : ENNReal)
          · -- Proof comment: before `Tω`, cutting the already-stopped coefficient again at
            -- `Tω` does nothing.
            simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs]
          · have hHiZero : Hi s ω = 0 := by
              simpa [hs] using hHiSample s
            -- Proof comment: after `Tω`, both the original samplewise stopped coefficient and
            -- the additional deterministic cutoff are already zero.
            simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs, hHiZero]
        have hAtTimeT :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω := by
          -- Proof comment: at the fixed sample `ω`, the coefficient used by the canonical
          -- coordinate already agrees with its deterministic cutoff on the whole interval
          -- `Set.Icc 0 t`.
          exact
            continuousLocalMartingaleItoIntegralProcess_eq_of_eqOnIcc_theorem25_40
              (μ := (μ : Measure Ω))
              (ℱ := ℱWc)
              (M := Zi)
              (K := Hi)
              (L := HiCut)
              (hM := hZi)
              (T := t)
              (ω := ω)
              (by
                intro s hs
                exact (hHiCutSample s).symm)
        have hAtTimeTω :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi Tω ω := by
          -- Proof comment: at the clipped horizon itself, the deterministic cutoff is exactly
          -- the original coefficient.
          exact
            continuousLocalMartingaleItoIntegralProcess_eq_constCutoffValue_theorem25_40
              (μ := (μ : Measure Ω))
              (ℱ := ℱWc)
              (M := Zi)
              (H := Hi)
              (hM := hZi)
              Tω
              ω
        have hCutoffFreeze :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω := by
          -- Route correction: the after-exit coordinate transport now uses the almost-sure
          -- cutoff-freeze theorem on the correct quantifier surface, avoiding the old impossible
          -- fixed-path witness chain.
          simpa [Tω, Zi, hZi, Hi, HiCut] using hFreezeω i hAfter
        have hCoordinateEq :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi Tω ω := by
          -- Proof comment: both time slices are compared through the same deterministic-cutoff
          -- canonical coordinate, which is the only remaining missing freeze step.
          exact hAtTimeT.trans (hCutoffFreeze.trans hAtTimeTω)
        simpa [canonical, Zi, hZi, Hi, τ] using hCoordinateEq
      -- Proof comment: once every coordinate is transported from the after-exit time `t` back to
      -- the clipped horizon `Tω`, the already-established clipped identity closes the branch by
      -- finite summation.
      calc
        pathwiseMultidimensionalItoIntegral F0 Xω Tω = ∑ i : Fin d, canonical i Tω ω :=
          hClippedFirstOrder
        _ = ∑ i : Fin d, canonical i t ω := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          symm
          exact hCoordinateAfterExit i
  have hQuadIntegral :
      quadω =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x0 + B s ω))
              τ
              u.toNNReal
              ω := by
    -- Proof comment: the quadratic correction is already diagonalized by `hQuadDiag`; the new
    -- translated-Laplacian helper rewrites that diagonal form back to the stopped drift integral.
    calc
      quadω =
          ((1 : ℝ) / 2) *
            ∑ i : Fin d,
              ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), (∂²[i, i] F0) (Xω s.toNNReal) := hQuadDiag
      _ =
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Δ F (x0 + B s ω))
                τ
                u.toNNReal
                ω := by
            simpa [F0] using
              translatedDiagIntegral_eq_stoppedLaplacianIntegral_theorem25_40
                (x0 := x0) (F := F) (B := B) (τ := τ) (ω := ω) (Xω := Xω) (t := t)
                (Tω := Tω) hFcontDiff (fun s ↦ rfl) hTω_coe hTω_le
  calc
    stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x0 + B s ω))
              τ
              u.toNNReal
              ω
      =
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω - quadω := by
          rw [hQuadIntegral]
    _ = pathwiseMultidimensionalItoIntegral F0 Xω Tω := hReduced
    _ = ∑ i : Fin d, canonical i t ω := hFirstOrder

/-- Helper for Theorem 25.40: once the samplewise stopped-Itô identity is available, converting it
to the theorem-local `EqUpTo` spelling is immediate. -/
private theorem canonicalFamilyEqUpTo_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    let canonical :
        Fin d → NNReal → Ω → ℝ := fun i =>
          let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
          let hZi :
              IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
            (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
              (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
          let Hi : NNReal → Ω → ℝ :=
            ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_40
                (Ω := Ω) (Wc := Wc) (F := F) i)
              τ
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
    EqUpTo (μ : Measure Ω) T
      (fun t ω ↦
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Δ F (x0 + B s ω))
                τ
                u.toNNReal
                ω)
      (fun t ω ↦ ∑ i : Fin d, canonical i t ω) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  let canonical :
      Fin d → NNReal → Ω → ℝ := fun i =>
        let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
        let hZi :
            IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            τ
        ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
  have hAll :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x0 + B s ω))
                  τ
                  u.toNNReal
                  ω =
          ∑ i : Fin d, canonical i t ω := by
    -- Proof comment: the dedicated samplewise helper isolates the pathwise Itô theorem and all
    -- normalization work from the later horizonwise packaging.
    simpa [B, τ, ℱWc, canonical] using
      stoppedCenteredPatchedIto_aeAllTimes_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff T
  -- Proof comment: one all-times almost-sure identity immediately yields equality up to the fixed
  -- deterministic horizon `T`.
  exact eqUpTo_of_ae_allTimes hAll

/-- Helper for Theorem 25.40: the remaining stochastic input is to identify the translated
driftless stopped surface on `[0,T]` with a finite sum of coordinate cutoff Itô owners that is a
continuous local martingale up to `T`. -/
private theorem shiftedTranslatedSurface_eqUpTo_coordinateConstCutoffFamily_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    ∃ N : Fin d → NNReal → Ω → ℝ,
      (∀ i : Fin d,
        IsContinuousLocalMartingaleUpTo_theorem25_40 ℱWc (μ : Measure Ω) T (N i)) ∧
      EqUpTo (μ : Measure Ω) T
        (fun t ω ↦
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x0 + B s ω))
                  τ
                  u.toNNReal
                  ω)
        (fun t ω ↦ ∑ i : Fin d, N i t ω) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hCoordinateInput :
      ∀ i : Fin d,
        let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
        let hZi :
            IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            τ
        ProgMeasurable ℱWc Hi ∧
          (∀ U : NNReal, ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
              (fun s : ℝ ↦
                (ProbabilityTheory.processBeforeStoppingTime
                    Hi
                    (fun _ ↦ (T : ENNReal))
                    s.toNNReal
                    ω) ^ 2 * (1 : ℝ))
              (Set.Icc (0 : ℝ) (U : ℝ))) ∧
          HasAbsolutelyContinuousSquareVariation_theorem25_40 Zi hZi := by
    intro i
    -- Proof comment: the new packaged helper keeps the frontier focused on the stochastic
    -- constructor itself rather than reopening the same analytic side conditions coordinatewise.
    simpa [ℱWc, τ] using
      coordinateConstCutoffItoInputData_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff i T
  classical
  let canonical :
      Fin d → NNReal → Ω → ℝ := fun i =>
        let Zi : NNReal → Ω → ℝ := fun t ω ↦ Wc t ω i - x0 i
        let hZi :
            IsContinuousLocalMartingale ℱWc (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalWc_theorem25_40
            (μ := μ) (Wc := Wc) (x0 := x0) hWc hWcCont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_40
              (Ω := Ω) (Wc := Wc) (F := F) i)
            τ
        ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
  let N : Fin d → NNReal → Ω → ℝ := fun i ↦
    Classical.choose <|
      coordinateConstCutoffItoUpTo_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff i T
  have hN_upTo :
      ∀ i : Fin d,
        IsContinuousLocalMartingaleUpTo_theorem25_40 ℱWc (μ : Measure Ω) T (N i) := by
    intro i
    exact
      (Classical.choose_spec <|
        coordinateConstCutoffItoUpTo_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
          hWc hWcCont hGo hExitFinite hFcontDiff i T).1
  have hN_canonical :
      ∀ i : Fin d,
        EqUpTo (μ : Measure Ω) T (N i) (canonical i) := by
    intro i
    exact
      (Classical.choose_spec <|
        coordinateConstCutoffItoUpTo_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
          hWc hWcCont hGo hExitFinite hFcontDiff i T).2
  have hCanonicalFamily :
      EqUpTo (μ : Measure Ω) T
        (fun t ω ↦
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x0 + B s ω))
                  τ
                  u.toNNReal
                  ω)
        (fun t ω ↦ ∑ i : Fin d, canonical i t ω) := by
    -- Proof comment: the dedicated wrapper already packages the samplewise stopped-Itô identity
    -- into the theorem-local finite-horizon `EqUpTo` relation.
    simpa [B, τ, ℱWc, canonical] using
      canonicalFamilyEqUpTo_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff T
  have hTransport :
      EqUpTo (μ : Measure Ω) T
        (fun t ω ↦ ∑ i : Fin d, canonical i t ω)
        (fun t ω ↦ ∑ i : Fin d, N i t ω) := by
    -- Proof comment: after the canonical stopped-Ito comparison is known, the selected coordinate
    -- owners replace the canonical dyadic realizations termwise on the same horizon.
    exact
      eqUpTo_sym <|
        eqUpTo_finsetSum
          (s := Finset.univ)
          (μ := (μ : Measure Ω))
          (T := T)
          (X := N)
          (Y := canonical)
          (fun i _ ↦ hN_canonical i)
  refine ⟨N, hN_upTo, ?_⟩
  -- Proof comment: compose the canonical comparison with the termwise transport from canonical
  -- coordinate integrals to the chosen Chapter 25.21 witnesses.
  exact eqUpTo_trans hCanonicalFamily hTransport

/-- Helper for Theorem 25.40: the remaining stochastic input is to identify the translated
driftless stopped surface on `[0,T]` with a finite sum of coordinate cutoff Itô owners that is a
continuous local martingale up to `T`. -/
private theorem shiftedTranslatedSurface_constCutoffItoBridge_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    ∃ Nsum : NNReal → Ω → ℝ,
      EqUpTo (μ : Measure Ω) T
        (fun t ω ↦
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x0 + B s ω))
                  τ
                  u.toNNReal
                  ω)
        Nsum ∧
      IsContinuousLocalMartingaleUpTo_theorem25_40 ℱWc (μ : Measure Ω) T Nsum := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  rcases
      shiftedTranslatedSurface_eqUpTo_coordinateConstCutoffFamily_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff T with
    ⟨N, hN_upTo, hEqFamily⟩
  let Nsum : NNReal → Ω → ℝ := fun t ω ↦ ∑ i : Fin d, N i t ω
  refine ⟨Nsum, ?_, ?_⟩
  · -- Proof comment: the coordinate-family theorem already identifies the translated stopped
    -- surface with the finite sum of the coordinate owners on `[0, T]`.
    simpa [Nsum] using hEqFamily
  · -- Proof comment: once each coordinate owner is available up to the same fixed horizon,
    -- finite-sum packaging supplies the required local-martingale-up-to witness for their sum.
    exact
      finsetSum_isContinuousLocalMartingaleUpTo_theorem25_40
        (μ := (μ : Measure Ω))
        (ℱ := ℱWc)
        (s := Finset.univ)
        (T := T)
        (N := N)
        (fun i _ ↦ hN_upTo i)

/-- Helper for Theorem 25.40: the only remaining fixed-horizon blocker is to compare the visible
deterministic stop with the finite sum of the coordinate Itô owners in the natural filtration of
`Wc`. All purely measurable and boundedness prerequisites are already isolated here. -/
private theorem visibleStoppedIncrement_constStop_martingaleFrontier_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω) := by
  intro T
  let X : NNReal → Ω → ℝ :=
    fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hX_strong :
      StronglyAdapted ℱWc (stoppedProcess X (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: deterministic stopping preserves strong adaptedness of the visible target,
    -- so the remaining issue is purely the fixed-horizon martingale bridge.
    simpa [X, ℱWc] using
      visibleStoppedIncrement_constStop_stronglyAdapted_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff.continuous T
  have hX_bounded :
      BoundedInTimeAe (μ : Measure Ω) (stoppedProcess X (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: compactness of `closure G` already gives the deterministic bound needed for
    -- the bounded-local-martingale upgrade once the fixed-horizon comparison is supplied.
    simpa [X] using
      visibleStoppedIncrement_constStop_boundedInTimeAe_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hx0 hWc hWcCont hGo hGcpt hExitFinite hFcontDiff.continuous T
  let Y : NNReal → Ω → ℝ := fun t ω ↦
    stoppedProcess (fun s ω ↦ F (x0 + (if s = 0 then 0 else Wc s ω - x0)) - F x0)
      (hittingAfter Wc Gᶜ 0)
      t
      ω -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        ((1 : ℝ) / 2) *
          ProbabilityTheory.processBeforeStoppingTime
            (fun s ω ↦
              Δ F
                (x0 +
                  (if s = 0 then 0 else Wc s ω - x0)))
            (hittingAfter Wc Gᶜ 0)
            u.toNNReal
            ω
  have hSurfaceEq :
      EqUpTo (μ : Measure Ω) T X Y := by
    let Yold : NNReal → Ω → ℝ := fun t ω ↦
      stoppedProcess (fun s ω ↦ F (x0 + (if s = 0 then 0 else Wc s ω - x0)) - F x0)
        (hittingAfter Wc Gᶜ 0)
        t
        ω -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            Δ F
              (x0 +
                stoppedProcess
                  (fun s ω ↦ if s = 0 then 0 else Wc s ω - x0)
                  (hittingAfter Wc Gᶜ 0)
                  u.toNNReal
                  ω)
    have hSurfaceEqOld :
        EqUpTo (μ : Measure Ω) T X Yold := by
      -- Proof comment: the visible stopped increment already agrees on `[0,T]` with the older
      -- translated stopped surface after the harmonic drift is removed.
      simpa [X, Yold] using
        visibleStoppedIncrement_eqUpTo_shiftedTranslatedSurface_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
          hx0 hWc hWcCont hGo hGV hExitFinite hFharm T
    have hCutoffEqOld :
        EqUpTo (μ : Measure Ω) T Y Yold := by
      -- Proof comment: under harmonicity, the corrected cutoff-drift surface and the older
      -- stopped-drift spelling coincide because both drift terms vanish.
      simpa [Y, Yold] using
        shiftedTranslatedSurface_cutoffDrift_eq_oldDrift_under_harmonic_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
        hx0 hWc hWcCont hGo hGV hExitFinite hFharm T
    exact eqUpTo_trans hSurfaceEqOld (eqUpTo_sym hCutoffEqOld)
  have hCanonicalBridge :
      ∃ Nsum : NNReal → Ω → ℝ,
        EqUpTo (μ : Measure Ω) T Y Nsum ∧
          IsContinuousLocalMartingaleUpTo_theorem25_40 ℱWc (μ : Measure Ω) T Nsum := by
    -- Proof comment: the remaining stochastic gap is now isolated as a bridge from the driftless
    -- translated stopped surface to a summed coordinate cutoff Itô owner on `[0,T]`.
    simpa [Y, ℱWc] using
      shiftedTranslatedSurface_constCutoffItoBridge_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff T
  rcases hCanonicalBridge with ⟨Nsum, hEqSurfaceSum, hNsum_upTo⟩
  have hEqSum : EqUpTo (μ : Measure Ω) T X Nsum :=
    eqUpTo_trans hSurfaceEq hEqSurfaceSum
  -- Proof comment: once the fixed-horizon comparison is isolated explicitly, the deterministic
  -- stop is a martingale by the generic bounded `EqUpTo` transport lemma above.
  exact
    martingale_of_constStopped_eqUpTo_localMartingaleUpTo_theorem25_40
      (μ := μ)
      (ℱ := ℱWc)
      (X := X)
      (N := Nsum)
      (T := T)
      hX_strong
      hX_bounded
      hEqSum
      hNsum_upTo

/-- Helper for Theorem 25.40: the only remaining stochastic frontier is the direct local-
martingale statement for the visible stopped harmonic increment. -/
private theorem shiftedTranslatedSurface_hasContinuousLocalMartingaleOwner_frontier_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    ∃ N : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        N ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N τ t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) := by
  -- Route correction: the old cycle tried to reconstruct this translated owner from the visible
  -- local-martingale frontier, but the frontier itself naturally wants to consume such an owner.
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let N : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0
  have hLocal :
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        N := by
    let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
    have hTargetAdapted :
        Adapted ℱWc N := by
      -- Proof comment: the visible stopped increment already has the required adaptedness in the
      -- natural filtration of `Wc`.
      simpa [N, τ, ℱWc] using
        visibleStoppedIncrement_adapted_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
          hWc hWcCont hGo hExitFinite hFcontDiff.continuous
    have hTargetCont :
        ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω := by
      -- Proof comment: continuity was separated from the stochastic core so the remaining blocker
      -- is only the deterministic-horizon martingale theorem.
      simpa [N] using
        visibleStoppedIncrement_pathContinuous_theorem25_40
          (Wc := Wc) (x0 := x0) (G := G) (F := F) hWcCont hFcontDiff
    have hStopped :
        ∀ T : NNReal,
          Martingale
            (stoppedProcess N (fun _ ↦ (T : ENNReal)))
            ℱWc
            (μ : Measure Ω) := by
      intro T
      -- Proof comment: the only remaining fixed-horizon bridge is now isolated in a dedicated
      -- theorem, so the local-martingale reconstruction here just consumes that package.
      simpa [N, τ, ℱWc] using
        visibleStoppedIncrement_constStop_martingaleFrontier_theorem25_40
          (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
          hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm T
    -- Proof comment: once the deterministic-horizon martingale bridge is available, the standard
    -- constant-localizer criterion yields the visible stopped increment as a local martingale.
    exact
      (isContinuousLocalMartingale_of_constStoppedMartingale_theorem25_40
        (μ := (μ : Measure Ω))
        (ℱ := ℱWc)
        hTargetAdapted
        hTargetCont
        hStopped).local_martingale
  have hSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) =
          F (stoppedProcess Wc τ t ω) - F x0 := by
    -- Proof comment: the translated stopped surface minus its harmonic drift was already rewritten
    -- back to the visible stopped increment earlier in the file.
    simpa [B, τ] using
      shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
        (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x0 := x0)
        hx0 hWc hWcCont hGo hGV hExitFinite hFharm
  refine ⟨N, hLocal, ?_, ?_⟩
  · intro ω
    have hStoppedCont :
        Continuous fun t : NNReal ↦ stoppedProcess Wc τ t ω :=
      continuous_stoppedVectorProcess_of_continuous
        (X := Wc) (σ := τ) (ω := ω) (hWcCont ω)
    -- Proof comment: continuity of the stopped state path survives composition with `F` and
    -- subtraction of the deterministic base value.
    simpa [N] using (hFcontDiff.continuous.comp hStoppedCont).sub continuous_const
  · filter_upwards [hSurface] with ω hω t
    have hDouble :
        stoppedProcess (stoppedProcess Wc τ) τ = stoppedProcess Wc τ := by
      -- Proof comment: stopping twice at the same random clock only clips time by `τ` once.
      simpa [min_self] using
        (stoppedProcess_stoppedProcess' :
          stoppedProcess (stoppedProcess Wc τ) τ =
            stoppedProcess Wc (fun ω ↦ min (τ ω) (τ ω)))
    have hEval :
        stoppedProcess (stoppedProcess Wc τ) τ t ω = stoppedProcess Wc τ t ω := by
      exact congrFun (congrFun hDouble t) ω
    calc
      stoppedProcess N τ t ω = F (stoppedProcess Wc τ t ω) - F x0 := by
        change F (stoppedProcess (stoppedProcess Wc τ) τ t ω) - F x0 =
          F (stoppedProcess Wc τ t ω) - F x0
        rw [hEval]
      _ = stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) := by
        exact (hω t).symm

/-- Helper for Theorem 25.40: once a translated stopped-surface owner is available, the visible
stopped increment is already a local martingale by the stopped-owner transport route. -/
private theorem visibleStoppedIncrement_localMartingale_of_translatedOwner_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ} {N : NNReal → Ω → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    (hN_local :
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        N)
    (hN_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω)
    (hOwner :
      let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
      let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
        stoppedProcess N τ s ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ s ω -
            ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) :
    IsLocalMartingale
      (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
      (μ : Measure Ω)
      (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hτstop : IsStoppingTime ℱWc τ :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := Wc) (U := G) (x := x0) hWc hWcCont hGo hExitFinite
  have hTargetAdapted :
      Adapted ℱWc (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0) := by
    -- Proof comment: adaptedness of the visible stopped increment was already isolated from the
    -- stochastic owner construction.
    simpa [τ, ℱWc] using
      visibleStoppedIncrement_adapted_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff.continuous
  have hTargetCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (stoppedProcess Wc τ t ω) - F x0 := by
    intro ω
    have hStoppedCont :
        Continuous fun t : NNReal ↦ stoppedProcess Wc τ t ω :=
      continuous_stoppedVectorProcess_of_continuous
        (X := Wc) (σ := τ) (ω := ω) (hWcCont ω)
    -- Proof comment: continuity of the stopped Brownian state path survives composition with `F`
    -- and subtraction of the deterministic base value.
    simpa using (hFcontDiff.continuous.comp hStoppedCont).sub continuous_const
  let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
  have hTargetEq :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N τ t ω = F (stoppedProcess Wc τ t ω) - F x0 := by
    have hSurface :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
              ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
                ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) =
            F (stoppedProcess Wc τ t ω) - F x0 := by
      -- Proof comment: the translated stopped surface minus its harmonic drift was already
      -- rewritten back to the visible stopped increment earlier in the file.
      simpa [B, τ] using
        shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
          (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x0 := x0)
          hx0 hWc hWcCont hGo hGV hExitFinite hFharm
    filter_upwards [hOwner, hSurface] with ω hωOwner hωSurface t
    -- Proof comment: combine the owner identity with the translated-surface rewrite at the same
    -- deterministic time to identify the stopped owner with the visible target process.
    calc
      stoppedProcess N τ t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) := hωOwner t
      _ = F (stoppedProcess Wc τ t ω) - F x0 := hωSurface t
  -- Proof comment: stop the owner at the exit clock and transfer the local-martingale structure
  -- across the all-times almost-sure identity with the visible target process.
  exact
    stoppedOwner_transfers_isLocalMartingale_theorem25_40
      (μ := (μ : Measure Ω))
      (ℱ := ℱWc)
      (N := N)
      (T := fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
      hN_local
      hN_cont
      hτstop
      hTargetAdapted
      hTargetCont
      hTargetEq

/-- Helper for Theorem 25.40: the only remaining stochastic frontier is the direct local-
martingale statement for the visible stopped harmonic increment. -/
private theorem visibleStoppedIncrement_localMartingaleFrontier_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    IsLocalMartingale
      (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
      (μ : Measure Ω)
      (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hTargetAdapted :
      Adapted ℱWc (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0) := by
    -- Proof comment: adaptedness of the visible stopped increment was isolated from the
    -- martingale bridge, so the direct local-martingale proof reuses that API.
    simpa [τ, ℱWc] using
      visibleStoppedIncrement_adapted_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
        hWc hWcCont hGo hExitFinite hFcontDiff.continuous
  have hTargetCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (stoppedProcess Wc τ t ω) - F x0 := by
    -- Proof comment: continuity was already separated from the stochastic bridge, so the direct
    -- local-martingale reconstruction only cites the earlier pathwise lemma.
    simpa [τ] using
      visibleStoppedIncrement_pathContinuous_theorem25_40
        (Wc := Wc) (x0 := x0) (G := G) (F := F) hWcCont hFcontDiff
  have hStopped :
      ∀ T : NNReal,
        Martingale
          (stoppedProcess (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
            (fun _ ↦ (T : ENNReal)))
          ℱWc
          (μ : Measure Ω) := by
    intro T
    -- Proof comment: the remaining fixed-horizon step is now recorded independently of the
    -- owner theorem, so the direct visible local-martingale route no longer cycles through it.
    simpa [τ, ℱWc] using
      visibleStoppedIncrement_constStop_martingaleFrontier_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
        hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm T
  -- Proof comment: once the deterministic-horizon martingale bridge is isolated explicitly, the
  -- constant-localizer criterion gives the visible stopped increment as a local martingale.
  exact
    (isContinuousLocalMartingale_of_constStoppedMartingale_theorem25_40
      (μ := (μ : Measure Ω))
      (ℱ := ℱWc)
      hTargetAdapted
      hTargetCont
      hStopped).local_martingale

/-- Helper for Theorem 25.40: once the visible stopped increment is available as a local
martingale, the translated stopped-surface owner is obtained by choosing that visible increment as
the owner and rewriting the translated surface back to it. -/
private theorem shiftedTranslatedSurface_hasContinuousLocalMartingaleOwner_direct_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    ∃ N : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        N ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N τ t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) := by
  -- Proof comment: the owner-first frontier is now explicit earlier in the file, so this later
  -- theorem is only a thin alias of that structural blocker.
  exact
    shiftedTranslatedSurface_hasContinuousLocalMartingaleOwner_frontier_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
      hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm

/-- Helper for Theorem 25.40: once the translated stopped surface has a continuous local-
martingale owner, stopping that owner at the exit clock and removing the harmonic drift rewrites
it back to the visible stopped increment at all deterministic times almost surely. -/
private theorem translatedSurfaceOwner_stopped_ae_eq_target_core_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    {N : NNReal → Ω → ℝ}
    (hOwner :
      let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
      let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
        stoppedProcess N τ s ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ s ω -
            ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω))
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    :
    let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
      stoppedProcess N τ s ω =
        F (stoppedProcess Wc τ s ω) - F x0 := by
  let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  have hTranslatedSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ s ω -
            ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) =
          F (stoppedProcess Wc τ s ω) - F x0 :=
    shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
      (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x0 := x0)
      hx0 hWc hWcCont hGo hGV hExitFinite hFharm
  have hDriftZero :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
        ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
          ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) = 0 := by
    -- Proof comment: harmonicity kills the translated stopped drift pointwise, so its primitive
    -- vanishes as well.
    simpa [B, τ, stoppedProcess] using
      stoppedLaplacianIntegral_eq_zero
        (μ := (μ : Measure Ω))
        (W := fun s ω ↦ x0 + B s ω)
        (τ := τ)
        (F := F)
        (by
          simpa [B, τ, stoppedProcess] using
            shiftedStoppedExtension_laplacian_eq_zero
              (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x := x0)
              hx0 hWc hWcCont hGo hGV hExitFinite hFharm)
  filter_upwards [hOwner, hTranslatedSurface, hDriftZero] with ω hωOwner hωSurface hωDrift s
  -- Proof comment: the owner identifies with the translated stopped surface minus the drift, and
  -- the harmonicity input makes that drift vanish, so the owner matches the visible target.
  calc
    stoppedProcess N τ s ω
        = stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ s ω -
            ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) := hωOwner s
    _ = F (stoppedProcess Wc τ s ω) - F x0 := hωSurface s

/-- Helper for Theorem 25.40: once the direct visible local-martingale frontier is isolated, the
visible stopped increment packages itself as a continuous local-martingale owner. -/
private theorem visibleStoppedIncrement_hasContinuousLocalMartingaleOwner_core_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∃ Nc : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        Nc ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Nc t ω) ∧
      AreModifications
        (μ : Measure Ω)
        Nc
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let Nc : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0
  have hLocal :
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        Nc := by
    -- Proof comment: after isolating the direct visible local-martingale frontier, the owner is
    -- just the visible stopped increment itself.
    simpa [Nc, τ] using
      visibleStoppedIncrement_localMartingaleFrontier_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
        hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm
  have hCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ Nc t ω := by
    intro ω
    have hStoppedCont :
        Continuous fun t : NNReal ↦ stoppedProcess Wc τ t ω :=
      continuous_stoppedVectorProcess_of_continuous
        (X := Wc) (σ := τ) (ω := ω) (hWcCont ω)
    -- Proof comment: continuity of the stopped state path is already packaged, so composing with
    -- `F` and subtracting `F x0` preserves continuity.
    simpa [Nc] using (hFcontDiff.continuous.comp hStoppedCont).sub continuous_const
  refine ⟨Nc, hLocal, hCont, ?_⟩
  intro t
  filter_upwards with ω
  rfl

/-- Helper for Theorem 25.40: once the visible stopped increment has already been packaged as a
continuous local martingale owner, the translated deterministic stop is just a transport wrapper
around the earlier owner-based martingale theorem. -/
private theorem shiftedTranslatedSurface_constStop_martingaleDirect_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (stoppedProcess
            (fun t ω ↦ F (x0 + (if t = 0 then 0 else Wc t ω - x0)) - F x0)
            (hittingAfter Wc Gᶜ 0))
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        := by
  intro T
  rcases
      visibleStoppedIncrement_hasContinuousLocalMartingaleOwner_core_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
        hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm with
    ⟨Nc, hNc_local, hNc_cont, hNc_mod⟩
  -- Proof comment: after the visible stopped increment is repaired as a local martingale, the
  -- translated deterministic stop is only the earlier owner-based transport theorem.
  exact
    shiftedTranslatedSurface_constStop_martingale_of_originalOwner_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)
      hx0 hWc hWcCont hGo hGcpt hExitFinite hFcontDiff.continuous
      hNc_local hNc_cont hNc_mod T

/-- Helper for Theorem 25.40: once the translated deterministic stop is proved directly, the
visible deterministic stop follows by the already isolated drift-zero rewrite back to the original
stopped increment. -/
private theorem visibleStoppedIncrement_constStop_martingaleDirect_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  have hStoppedSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ t ω -
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ s.toNNReal ω) =
          F (stoppedProcess Wc τ t ω) - F x0 := by
    -- Proof comment: the translated stopped surface minus its Itô drift already rewrites back to
    -- the visible stopped increment at every deterministic time almost surely.
    simpa [B, τ] using
      shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
        (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x0 := x0)
        hx0 hWc hWcCont hGo hGV hExitFinite hFharm
  intro T
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hDriftZero :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ s.toNNReal ω) = 0 := by
    -- Proof comment: harmonicity kills the stopped Laplacian drift on the translated surface.
    simpa [B, τ, stoppedProcess] using
      stoppedLaplacianIntegral_eq_zero
        (μ := (μ : Measure Ω))
        (W := fun t ω ↦ x0 + B t ω)
        (τ := τ)
        (F := F)
        (by
          simpa [B, τ, stoppedProcess] using
            shiftedStoppedExtension_laplacian_eq_zero
              (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x := x0)
              hx0 hWc hWcCont hGo hGV hExitFinite hFharm)
  have hTargetStrong :
      StronglyAdapted
        ℱWc
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
          (fun _ ↦ (T : ENNReal))) := by
    have hTargetAdapted :
        Adapted ℱWc (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0) := by
      have hτstop : IsStoppingTime ℱWc τ :=
        stageExit_isStoppingTime_of_continuous_of_aeExitFinite
          (μ := μ) (W := Wc) (U := G) (x := x0) hWc hWcCont hGo hExitFinite
      have hRawStrong :
          StronglyAdapted ℱWc (fun t ω ↦ F (Wc t ω) - F x0) := by
        intro t
        -- Proof comment: each deterministic-time slice is the measurable observable `F`
        -- applied to the current Brownian state, followed by subtraction of `F x0`.
        exact
          ((stateComposition_stronglyAdapted_natural_theorem25_40
              (hWsm := brownianVectorStartedAt_stronglyMeasurable hWc)
              (hFmeas := hFcontDiff.continuous.measurable)) t).sub stronglyMeasurable_const
      have hRawCont :
          ∀ ω : Ω, Continuous fun t : NNReal ↦ F (Wc t ω) - F x0 := by
        intro ω
        simpa using (hFcontDiff.continuous.comp (hWcCont ω)).sub continuous_const
      have hStoppedStrong :
          StronglyAdapted ℱWc (stoppedProcess (fun t ω ↦ F (Wc t ω) - F x0) τ) :=
        hRawStrong.stoppedProcess hRawCont hτstop
      -- Proof comment: normalize the visible target to the stopped unstopped increment spelling
      -- before reading off adaptedness.
      simpa [stageStoppedExtension_eq_stoppedIncrement_theorem25_40
        (Wc := Wc) (F := F) (x0 := x0) (τ := τ)] using hStoppedStrong.adapted
    have hTargetCont :
        ∀ ω : Ω, Continuous fun t : NNReal ↦ F (stoppedProcess Wc τ t ω) - F x0 := by
      intro ω
      have hStoppedCont :
          Continuous fun t : NNReal ↦ stoppedProcess Wc τ t ω :=
        continuous_stoppedVectorProcess_of_continuous
          (X := Wc) (σ := τ) (ω := ω) (hWcCont ω)
      -- Proof comment: continuity of the stopped state path survives composition with `F` and
      -- subtraction of the deterministic base value.
      simpa using (hFcontDiff.continuous.comp hStoppedCont).sub continuous_const
    -- Proof comment: deterministic stopping preserves strong adaptedness for the continuous
    -- visible target process.
    exact hTargetAdapted.stronglyAdapted.stoppedProcess hTargetCont (isStoppingTime_const ℱWc T)
  have hEq :
      ∀ t : NNReal,
        stoppedProcess
            (stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ)
            (fun _ ↦ (T : ENNReal)) t =ᵐ[(μ : Measure Ω)]
          stoppedProcess
            (fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0)
            (fun _ ↦ (T : ENNReal)) t := by
    intro t
    filter_upwards [hStoppedSurface, hDriftZero] with ω hωSurface hωDrift
    have hAtMin := hωSurface (min t T)
    have hDriftAtMin := hωDrift (min t T)
    -- Proof comment: compare both deterministic stops at the clipped time `min t T`, then remove
    -- the already vanishing harmonic drift.
    rw [hDriftAtMin, sub_zero] at hAtMin
    simpa [stoppedProcessConstTime_eq_min] using hAtMin
  have hTranslatedMart :
      Martingale
        (stoppedProcess
          (stoppedProcess (fun t ω ↦ F (x0 + B t ω) - F x0) τ)
          (fun _ ↦ (T : ENNReal)))
        ℱWc
        (μ : Measure Ω) := by
    -- Proof comment: this is the single earlier fixed-horizon martingale bridge that cuts the
    -- owner/local-martingale cycle.
    simpa [B, τ] using
      shiftedTranslatedSurface_constStop_martingaleDirect_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
        hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm T
  -- Proof comment: once the translated deterministic stop is known to be a martingale, the
  -- visible stopped increment inherits that property by the all-times almost-sure rewrite above.
  exact martingale_congr_ae hTranslatedMart hTargetStrong hEq

/-- Helper for Theorem 25.40: every deterministic horizon stop of the visible stopped harmonic
increment is a martingale once the translated stopped-surface assembly is available. This isolates
the remaining fixed-horizon stochastic blocker from the later local-martingale reconstruction. -/
private theorem visibleStoppedIncrement_constStop_martingale_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω) := by
  -- Proof comment: the fixed-horizon blocker is now isolated in the frontier theorem above, so
  -- this later alias just reuses that dedicated statement.
  exact
    visibleStoppedIncrement_constStop_martingaleFrontier_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
      hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm

/-- Helper for Theorem 25.40: the remaining stochastic core is to reconstruct the visible stopped
harmonic increment as a local martingale from its deterministic horizon stops. -/
private theorem visibleStoppedIncrement_isLocalMartingale_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
      IsLocalMartingale
      (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
      (μ : Measure Ω)
      (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  -- Proof comment: after the route correction, this theorem is exactly the direct frontier
  -- theorem, with no remaining owner transport.
  exact
    visibleStoppedIncrement_localMartingaleFrontier_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
      hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm

/-- Helper for Theorem 25.40: the visible stopped increment has continuous sample paths because
stopping preserves continuity of the Brownian path and `F` is continuous. -/
private theorem visibleStoppedIncrement_continuous_theorem25_40
    {Wc : VectorProcess} {x0 : State} {G : Set State} {F : State → ℝ}
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hFcontDiff : ContDiff ℝ 2 F) :
    ∀ ω : Ω, Continuous fun t : NNReal ↦
      F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0 := by
  -- Proof comment: this later alias reuses the earlier pathwise continuity helper so the same
  -- continuity argument is not duplicated across the owner and self-owner packages.
  exact
    visibleStoppedIncrement_pathContinuous_theorem25_40
      (Wc := Wc) (x0 := x0) (G := G) (F := F) hWcCont hFcontDiff

/-- Helper for Theorem 25.40: the visible stopped increment is a deterministic-time modification
of itself. This isolates the final owner packaging from the earlier stochastic bridge. -/
private theorem visibleStoppedIncrement_selfModification_theorem25_40
    (μ : ProbabilityMeasure Ω)
    {Wc : VectorProcess} {x0 : State} {G : Set State} {F : State → ℝ} :
    AreModifications
      (μ : Measure Ω)
      (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)
      (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  intro t
  filter_upwards with ω
  rfl

/-- Helper for Theorem 25.40: once the visible stopped increment is known to be a local
martingale, the existential owner package is immediate by taking the process itself. -/
private theorem visibleStoppedIncrement_owner_of_localMartingale_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G : Set State} {F : State → ℝ}
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hLocal :
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)) :
    ∃ Nc : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        Nc ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Nc t ω) ∧
      AreModifications
        (μ : Measure Ω)
        Nc
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  -- Proof comment: once the local-martingale core is available, choose the visible stopped
  -- increment itself as the owner and package continuity and modification reflexively.
  refine
    ⟨fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0, ?_, ?_, ?_⟩
  · exact hLocal
  · exact
      visibleStoppedIncrement_continuous_theorem25_40
        (Wc := Wc) (x0 := x0) (G := G) (F := F) hWcCont hFcontDiff
  · exact
      visibleStoppedIncrement_selfModification_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (F := F)

/-- Helper for Theorem 25.40: once the visible stopped increment is proved to be a local
martingale, the earlier existential owner statement is immediate from the self-owner package
already isolated above. -/
private theorem visibleStoppedIncrement_hasContinuousLocalMartingaleOwner_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∃ Nc : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        Nc ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Nc t ω) ∧
      AreModifications
        (μ : Measure Ω)
        Nc
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  -- Route correction: the owner-first route is now available earlier in the file, so this later
  -- theorem is only a thin alias of the repaired core helper.
  exact
    visibleStoppedIncrement_hasContinuousLocalMartingaleOwner_core_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
      hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm

/-- Helper for Theorem 25.40: stopping the already stopped visible increment at the same exit
clock does not change the process. This is the idempotence rewrite used to package the owner
theorem around the visible stopped increment itself. -/
private theorem stageStoppedIncrement_stopped_eq_self_theorem25_40
    {Wc : VectorProcess} {F : State → ℝ} {x0 : State} {τ : Ω → ENNReal}
    (t : NNReal) (ω : Ω) :
    stoppedProcess (fun s ω ↦ F (stoppedProcess Wc τ s ω) - F x0) τ t ω =
      F (stoppedProcess Wc τ t ω) - F x0 := by
  have hDouble :
      stoppedProcess (stoppedProcess Wc τ) τ = stoppedProcess Wc τ := by
    -- Proof comment: stopping twice at the same random clock only clips time by `τ` once.
    simpa [min_self] using
      (stoppedProcess_stoppedProcess' :
        stoppedProcess (stoppedProcess Wc τ) τ =
          stoppedProcess Wc (fun ω ↦ min (τ ω) (τ ω)))
  have hEval :
      stoppedProcess (stoppedProcess Wc τ) τ t ω = stoppedProcess Wc τ t ω := by
    exact congrFun (congrFun hDouble t) ω
  -- Proof comment: unfold the outer stop and rewrite the inner double-stopped state path by the
  -- idempotence equality above.
  change F (stoppedProcess (stoppedProcess Wc τ) τ t ω) - F x0 =
    F (stoppedProcess Wc τ t ω) - F x0
  rw [hEval]

/-- Helper for Theorem 25.40: once the visible stopped increment is known to be a local
martingale, it already witnesses the translated owner statement. The only extra work is rewriting
the double stop away and using the previously proved translated stopped-surface identity. -/
private theorem translatedSurface_hasContinuousLocalMartingaleOwner_of_visibleStoppedIncrement_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    (hLocal :
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0)) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    ∃ N : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        N ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N τ t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
  let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
  let N : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess Wc τ t ω) - F x0
  have hSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) =
          F (stoppedProcess Wc τ t ω) - F x0 := by
    -- Proof comment: the translated stopped surface minus its drift was already rewritten back to
    -- the visible stopped increment earlier in the file.
    simpa [B, τ] using
      shiftedStoppedTranslatedExtension_ae_eq_originalIncrement_theorem25_40
        (μ := μ) (Wc := Wc) (U := G) (V := V) (F := F) (x0 := x0)
        hx0 hWc hWcCont hGo hGV hExitFinite hFharm
  refine ⟨N, ?_, ?_, ?_⟩
  · -- Proof comment: the chosen owner is exactly the visible stopped increment process.
    simpa [N, τ] using hLocal
  · intro ω
    have hStoppedCont :
        Continuous fun t : NNReal ↦ stoppedProcess Wc τ t ω :=
      continuous_stoppedVectorProcess_of_continuous
        (X := Wc) (σ := τ) (ω := ω) (hWcCont ω)
    -- Proof comment: continuity of the stopped state path survives composition with `F` and
    -- subtraction of the deterministic base value.
    simpa [N] using (hFcontDiff.continuous.comp hStoppedCont).sub continuous_const
  · filter_upwards [hSurface] with ω hω t
    calc
      stoppedProcess N τ t ω = F (stoppedProcess Wc τ t ω) - F x0 := by
        simpa [N] using
          stageStoppedIncrement_stopped_eq_self_theorem25_40
            (Wc := Wc) (F := F) (x0 := x0) (τ := τ) t ω
      _ = stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω) := by
        exact (hω t).symm

private theorem translatedSurface_hasContinuousLocalMartingaleOwner_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else Wc t ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    ∃ N : NNReal → Ω → ℝ,
      IsLocalMartingale
        (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
        (μ : Measure Ω)
        N ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N τ t ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω)) := by
  -- Route correction: the existential owner statement is now reduced to the direct local-
  -- martingale theorem for the visible stopped increment itself. Once that theorem is available,
  -- the owner is just the visible stopped increment together with the translated-surface rewrite.
  exact
    translatedSurface_hasContinuousLocalMartingaleOwner_of_visibleStoppedIncrement_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
      hx0 hWc hWcCont hGo hGV hExitFinite hFcontDiff hFharm
      (visibleStoppedIncrement_isLocalMartingale_theorem25_40
        (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
        hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm)

/-- Helper for Theorem 25.40: once the translated owner is stopped at the exit clock, the
vanishing harmonic drift rewrites it to the visible stopped increment at all times almost surely.
-/
private theorem translatedSurfaceOwner_stopped_ae_eq_target_theorem25_40
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G)
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    {N : NNReal → Ω → ℝ}
    (hOwner :
      let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
      let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
        stoppedProcess N τ s ω =
          stoppedProcess (fun s ω ↦ F (x0 + B s ω) - F x0) τ s ω -
            ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
              ((1 : ℝ) / 2) * Δ F (x0 + stoppedProcess B τ u.toNNReal ω))
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    :
    let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else Wc s ω - x0
    let τ : Ω → ENNReal := hittingAfter Wc Gᶜ 0
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
      stoppedProcess N τ s ω =
        F (stoppedProcess Wc τ s ω) - F x0 := by
  simpa using
    translatedSurfaceOwner_stopped_ae_eq_target_core_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
      hx0 hWc hWcCont hGo hGV hExitFinite hOwner hFharm

/-- Helper for Theorem 25.40: the stopped annulus extension should be a local martingale once the
missing unstopped Itô decomposition is supplied. This isolates the live stochastic blocker from
the deterministic expectation argument below. -/
private theorem stageStoppedExtension_increment_isLocalMartingale
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State}
    {G V : Set State} {F : State → ℝ}
    (hx0 : x0 ∈ G)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hGo : IsOpen G) (hGcpt : IsCompact (closure G))
    (hGV : closure G ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    IsLocalMartingale
      (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
      (μ : Measure Ω)
      (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
  -- Proof comment: after repairing the helper interface to carry compact closure, this theorem is
  -- exactly the direct visible stopped-increment local-martingale theorem above.
  exact
    visibleStoppedIncrement_isLocalMartingale_theorem25_40
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := V) (F := F)
      hx0 hWc hWcCont hGo hGcpt hGV hExitFinite hFcontDiff hFharm

/-- Helper for Theorem 25.40: the deterministic-time annulus-profile identity is the remaining
stochastic-core input. Once it is available, the fixed-start exit expectation follows by the
already packaged terminal limit and a dominated-convergence argument. -/
private theorem centeredAnnulusProfile_expectation_eq_at_natStop
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State} {ρ R : ℝ}
    (hx0 : x0 ∈ concentricAnnulus (0 : State) ρ R)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤)
    (hr : 0 < ρ) (hR : ρ < R) :
    ∀ n : ℕ,
      centeredAnnulusProfile (d := d) ρ R x0 =
        ∫ ω,
          centeredAnnulusProfile (d := d) ρ R
            (stoppedProcess Wc
              (hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0) n ω) ∂
            (μ : Measure Ω) := by
  let G : Set State := concentricAnnulus (0 : State) ρ R
  have hd0 : d ≠ 0 := by
    intro hd
    have hdist : dist x0 (0 : State) = 0 :=
      dist_eq_zero_of_zero_dim (d := d) hd x0 0
    have hxClosed : x0 ∈ Metric.closedBall (0 : State) ρ := by
      simpa [Metric.mem_closedBall, hdist] using hr.le
    exact hx0.2 hxClosed
  letI : NeZero d := ⟨hd0⟩
  have hGsolves :
      SolvesDirichletProblem
        G
        (fun z : frontier G ↦
          if (z : State) ∈ Metric.sphere (0 : State) ρ then 1 else 0)
        (centeredAnnulusProfile (d := d) ρ R) := by
    simpa [G] using centeredAnnulusProfile_solvesDirichlet (d := d) hr hR
  have hGcpt : IsCompact (closure G) := by
    simpa [G] using
      isCompact_closure_concentricAnnulus (d := d) (y := (0 : State)) hr hR
  obtain ⟨F, hFcontDiff, hFharmClosure, hFeqClosure⟩ :=
    existsCenteredAnnulusProfileExtensionOnClosure (d := d) hr hR
  have hFx :
      F x0 = centeredAnnulusProfile (d := d) ρ R x0 := by
    exact hFeqClosure (subset_closure hx0)
  have hStartAe :
      ∀ᵐ ω ∂(μ : Measure Ω), Wc 0 ω = x0 :=
    brownianVectorStart_ae_eq_const (μ := μ) hWc
  have hClosureBound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closure G, |centeredAnnulusProfile (d := d) ρ R z| ≤ C :=
    existsAbsLeOnClosure (d := d) hGcpt hGsolves
  have hStoppedEqProfile :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) =
          centeredAnnulusProfile (d := d) ρ R
            (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) := by
    filter_upwards [hExitFinite, hStartAe] with ω hωfin hωstart t
    have hStart : Wc 0 ω ∈ G := by
      simpa [G, hωstart] using hx0
    have hmem :
        stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω ∈ closure G :=
      stageStoppedProcess_mem_buffer
        (U := G) (V := closure G) (W := Wc) (ω := ω)
        (by simpa [G] using concentricAnnulus_isOpen (0 : State) ρ R)
        (hWcCont ω) hStart (by intro z hz; exact hz) hωfin t
    -- Proof comment: every deterministic stopped value stays on the closed annulus, where the
    -- cutoff extension agrees pointwise with the explicit annulus profile.
    exact hFeqClosure _ hmem
  have hStoppedExtensionBounded :
      BoundedInTimeAe (μ : Measure Ω)
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) := by
    rcases hClosureBound with ⟨C, hCnonneg, hC⟩
    refine ⟨C + |F x0|, ?_⟩
    filter_upwards [hExitFinite, hStartAe, hStoppedEqProfile] with ω hωfin hωstart hωeq t
    have hStart : Wc 0 ω ∈ G := by
      simpa [G, hωstart] using hx0
    have hmem :
        stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω ∈ closure G :=
      stageStoppedProcess_mem_buffer
        (U := G) (V := closure G) (W := Wc) (ω := ω)
        (by simpa [G] using concentricAnnulus_isOpen (0 : State) ρ R)
        (hWcCont ω) hStart (by intro z hz; exact hz) hωfin t
    -- Proof comment: rewrite back to the explicit annulus profile on the closed annulus and then
    -- use the compact-closure bound plus the deterministic offset `F x0`.
    calc
      |F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0|
          = |centeredAnnulusProfile (d := d) ρ R
              (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0| := by
              rw [hωeq t]
      _ ≤ |centeredAnnulusProfile (d := d) ρ R
            (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω)| + |F x0| := by
            simpa [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (centeredAnnulusProfile (d := d) ρ R
                  (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω))
                (-F x0))
      _ ≤ C + |F x0| := add_le_add (hC _ hmem) le_rfl
  intro n
  have hIntegralEq :
      ∫ ω, F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω) ∂(μ : Measure Ω) =
        ∫ ω,
          centeredAnnulusProfile (d := d) ρ R
            (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω) ∂(μ : Measure Ω) := by
    refine integral_congr_ae ?_
    filter_upwards [hStoppedEqProfile] with ω hω
    exact hω n
  let M : NNReal → Ω → ℝ :=
    fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω)
  have hInitialAe : M 0 =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ F x0 := by
    filter_upwards [hStartAe] with ω hωstart
    have hStop0 :
        stoppedProcess Wc (hittingAfter Wc Gᶜ 0) 0 ω = Wc 0 ω :=
      stoppedProcess_eq_of_le
        (u := Wc) (τ := hittingAfter Wc Gᶜ 0) (ω := ω) (i := 0) bot_le
    -- Proof comment: at the zero horizon, the stopped path is still at the deterministic Brownian
    -- start point, so the extension slice equals `F x0` almost surely.
    simp [M, hStop0, hωstart]
  rw [← hFx, ← hIntegralEq]
  let ℱWc : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc)
  have hStoppedLocal :
      IsLocalMartingale ℱWc (μ : Measure Ω)
        (fun t ω ↦ F (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) t ω) - F x0) :=
    stageStoppedExtension_increment_isLocalMartingale
      (μ := μ) (Wc := Wc) (x0 := x0) (G := G) (V := closure G) (F := F)
      hx0
      hWc
      hWcCont
      (by simpa [G] using concentricAnnulus_isOpen (0 : State) ρ R)
      hGcpt
      (by intro z hz; exact hz)
      hExitFinite
      hFcontDiff
      hFharmClosure
  -- Proof comment: all annulus-specific stochastic work is now packaged in
  -- `stageStoppedExtension_increment_isLocalMartingale`, so the remaining step is the generic
  -- bounded-local-martingale expectation identity.
  exact
    expectation_eq_of_bounded_localMartingale_increment
      (μ := μ) (ℱ := ℱWc) (M := M) (c := F x0)
      hStoppedLocal
      hStoppedExtensionBounded
      hInitialAe
      n

/-- Helper for Theorem 25.40: once the annulus profile solves the Dirichlet problem, the
probability of hitting the inner ball before exiting the outer ball should be identified with that
profile by a fixed-start specialization of Theorem 25.38. -/
private theorem centeredAnnulusProfile_exitExpectation_startedAt
    {μ : ProbabilityMeasure Ω} {Wc : VectorProcess} {x0 : State} {ρ R : ℝ}
    (hx0 : x0 ∈ concentricAnnulus (0 : State) ρ R)
    (hWc : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x0)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤)
    {exitValue : Ω → frontier (concentricAnnulus (0 : State) ρ R)}
    (hExitMeas : Measurable exitValue)
    (hExitValue :
      ∀ ω : Ω, hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤ →
        (exitValue ω : State) =
          stoppedValue Wc
            (hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0) ω)
    (hr : 0 < ρ) (hR : ρ < R) :
    centeredAnnulusProfile (d := d) ρ R x0 =
      ∫ ω, centeredAnnulusProfile (d := d) ρ R (exitValue ω : State) ∂(μ : Measure Ω) := by
  let G : Set State := concentricAnnulus (0 : State) ρ R
  have hd0 : d ≠ 0 := by
    intro hd
    have hdist : dist x0 (0 : State) = 0 :=
      dist_eq_zero_of_zero_dim (d := d) hd x0 0
    have hxClosed : x0 ∈ Metric.closedBall (0 : State) ρ := by
      simpa [Metric.mem_closedBall, hdist] using hr.le
    exact hx0.2 hxClosed
  letI : NeZero d := ⟨hd0⟩
  have hGsolves :
      SolvesDirichletProblem
        G
        (fun z : frontier G ↦
          if (z : State) ∈ Metric.sphere (0 : State) ρ then 1 else 0)
        (centeredAnnulusProfile (d := d) ρ R) := by
    simpa [G] using centeredAnnulusProfile_solvesDirichlet (d := d) hr hR
  have hGcpt : IsCompact (closure G) := by
    simpa [G] using
      isCompact_closure_concentricAnnulus (d := d) (y := (0 : State)) hr hR
  have hClosureBound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closure G, |centeredAnnulusProfile (d := d) ρ R z| ≤ C :=
    existsAbsLeOnClosure (d := d) hGcpt hGsolves
  have hExitValueLimit :
      ∀ᵐ ω ∂(μ : Measure Ω),
        Tendsto
          (fun n : ℕ ↦
            centeredAnnulusProfile (d := d) ρ R
              (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω))
          atTop
          (𝓝 (centeredAnnulusProfile (d := d) ρ R (exitValue ω : State))) := by
    filter_upwards [hExitFinite] with ω hωfin
    have hEventuallyEq :
        (fun n : ℕ ↦
          centeredAnnulusProfile (d := d) ρ R
            (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω)) =ᶠ[atTop]
          fun _ ↦
            centeredAnnulusProfile (d := d) ρ R
              (stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω) := by
      filter_upwards
          [tendsto_natCast_atTop_atTop.eventually_ge_atTop
            ((hittingAfter Wc Gᶜ 0 ω).untopA)] with n hn
      have hτn : hittingAfter Wc Gᶜ 0 ω ≤ (n : ENNReal) :=
        (WithTop.untopA_le_iff
          (x := hittingAfter Wc Gᶜ 0 ω) (hx := ne_top_of_lt hωfin)).1 hn
      have hStopped :
          stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω =
            stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω := by
        simpa [stoppedValue] using
          (stoppedProcess_eq_of_ge
            (u := Wc) (τ := hittingAfter Wc Gᶜ 0) (ω := ω) (i := (n : NNReal)) hτn)
      simp [hStopped]
    have hLimit : Tendsto
        (fun n : ℕ ↦
          centeredAnnulusProfile (d := d) ρ R
            (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω))
        atTop
        (𝓝
          (centeredAnnulusProfile (d := d) ρ R
            (stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω))) :=
      Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
    -- Proof comment: the deterministic-time convergence layer is now stable; the remaining gap is
    -- the deterministic-time martingale identity before passing to this limit.
    simpa [hExitValue ω hωfin] using hLimit
  have hNatIdentity :
      ∀ n : ℕ,
        centeredAnnulusProfile (d := d) ρ R x0 =
          ∫ ω,
            centeredAnnulusProfile (d := d) ρ R
              (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω) ∂(μ : Measure Ω) :=
    centeredAnnulusProfile_expectation_eq_at_natStop
      (d := d) (μ := μ) (Wc := Wc) (x0 := x0) (ρ := ρ) (R := R)
      hx0 hWc hWcCont hExitFinite hr hR
  rcases hClosureBound with ⟨C, hCnonneg, hC⟩
  have hMeasNat :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω ↦
            centeredAnnulusProfile (d := d) ρ R
              (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω))
          (μ : Measure Ω) := by
    intro n
    exact
      aestronglyMeasurable_centeredAnnulusProfile_stageStopped_atNat
        (d := d) (μ := μ) (W := Wc) (U := G) (x := x0) (ρ := ρ) (R := R)
        hWc hWcCont (by simpa [G] using concentricAnnulus_isOpen (0 : State) ρ R) hGcpt n
  have hStartAe :
      ∀ᵐ ω ∂(μ : Measure Ω), Wc 0 ω = x0 :=
    brownianVectorStart_ae_eq_const (μ := μ) hWc
  have hBoundNat :
      ∀ n : ℕ, ∀ᵐ ω ∂(μ : Measure Ω),
        |centeredAnnulusProfile (d := d) ρ R
          (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω)| ≤ C := by
    intro n
    filter_upwards [hExitFinite, hStartAe] with ω hωfin hωstart
    have hStart : Wc 0 ω ∈ G := by
      simpa [G, hωstart] using hx0
    have hmem :
        stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω ∈ closure G :=
      stageStoppedProcess_mem_buffer
        (U := G) (V := closure G) (W := Wc) (ω := ω)
        (by simpa [G] using concentricAnnulus_isOpen (0 : State) ρ R)
        (hWcCont ω)
        hStart
        (by intro z hz; exact hz)
        hωfin
        n
    exact hC _ hmem
  have hIntegralTendsto :
      Tendsto
        (fun n : ℕ ↦
          ∫ ω,
            centeredAnnulusProfile (d := d) ρ R
              (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω) ∂(μ : Measure Ω))
        atTop
        (𝓝
          (∫ ω, centeredAnnulusProfile (d := d) ρ R (exitValue ω : State) ∂(μ : Measure Ω))) := by
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ ↦ C)
        hMeasNat
        (integrable_const C)
        hBoundNat
        hExitValueLimit
  have hConstTendsto :
      Tendsto
        (fun n : ℕ ↦
          ∫ ω,
            centeredAnnulusProfile (d := d) ρ R
              (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω) ∂(μ : Measure Ω))
        atTop
        (𝓝 (centeredAnnulusProfile (d := d) ρ R x0)) := by
    have hSeqEq :
        (fun n : ℕ ↦
          ∫ ω,
            centeredAnnulusProfile (d := d) ρ R
              (stoppedProcess Wc (hittingAfter Wc Gᶜ 0) n ω) ∂(μ : Measure Ω)) =
          fun _ : ℕ ↦ centeredAnnulusProfile (d := d) ρ R x0 := by
      funext n
      exact (hNatIdentity n).symm
    simpa [hSeqEq] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ centeredAnnulusProfile (d := d) ρ R x0) atTop
          (𝓝 (centeredAnnulusProfile (d := d) ρ R x0)))
  -- Proof comment: after isolating the deterministic-time martingale identity in
  -- `hNatIdentity`, the original fixed-start exit formula is a pure dominated-convergence
  -- comparison of two limits.
  exact (tendsto_nhds_unique hIntegralTendsto hConstTendsto).symm

/-- Helper for Theorem 25.40: translating the state space by `y` rewrites the `hittingAfter`
clock against a centered target into the corresponding uncentered target clock. -/
private theorem hittingAfter_sub_const_eq
    {W : VectorProcess} {ω : Ω}
    (y : State) {A B : Set State}
    (hAB : ∀ z : State, z - y ∈ A ↔ z ∈ B) :
    hittingAfter (fun t ω ↦ W t ω - y) A 0 ω = hittingAfter W B 0 ω := by
  classical
  unfold hittingAfter
  by_cases hB : ∃ t : NNReal, (0 : NNReal) ≤ t ∧ W t ω ∈ B
  · have hA : ∃ t : NNReal, (0 : NNReal) ≤ t ∧ W t ω - y ∈ A := by
      rcases hB with ⟨t, ht0, htB⟩
      exact ⟨t, ht0, (hAB (W t ω)).2 htB⟩
    have hSet :
        {t : NNReal | (0 : NNReal) ≤ t ∧ W t ω - y ∈ A} =
          {t : NNReal | (0 : NNReal) ≤ t ∧ W t ω ∈ B} := by
      ext t
      simp [hAB (W t ω)]
    rw [if_pos hA, if_pos hB]
    exact congrArg (fun s : Set NNReal ↦ (((sInf s : NNReal) : WithTop NNReal))) hSet
  · have hA : ¬ ∃ t : NNReal, (0 : NNReal) ≤ t ∧ W t ω - y ∈ A := by
      intro hA
      apply hB
      rcases hA with ⟨t, ht0, htA⟩
      exact ⟨t, ht0, (hAB (W t ω)).1 htA⟩
    rw [if_neg hA, if_neg hB]

/-- Helper for Theorem 25.40: for a continuous path started in the annulus, exiting the annulus on
the inner sphere is equivalent to hitting the centered closed ball before the outer-ball exit. -/
private theorem annulusExitOnInnerSphere_iff_closedBallBeforeOuter
    {W : VectorProcess} {ω : Ω} {ρ R : ℝ}
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hstart : W 0 ω ∈ concentricAnnulus (0 : State) ρ R)
    (hτfin : hittingAfter W (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤)
    (hr : 0 < ρ) (hR : ρ < R) :
    stoppedValue W (hittingAfter W (concentricAnnulus (0 : State) ρ R)ᶜ 0) ω ∈
        Metric.sphere (0 : State) ρ ↔
      hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω <
        hittingAfter W (Metric.ball (0 : State) R)ᶜ 0 ω := by
  let G : Set State := concentricAnnulus (0 : State) ρ R
  let τ : NNReal := (hittingAfter W Gᶜ 0 ω).untopA
  have hτ_ne_top : hittingAfter W Gᶜ 0 ω ≠ ⊤ := ne_of_lt hτfin
  have hτ_eq : ((τ : NNReal) : WithTop NNReal) = hittingAfter W Gᶜ 0 ω := by
    rw [show τ = (hittingAfter W Gᶜ 0 ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hτ_ne_top]
    exact WithTop.coe_untop _ hτ_ne_top
  have hBeforeMemG : ∀ s : NNReal, s < τ → W s ω ∈ G := by
    intro s hs
    have hs_lt : (s : WithTop NNReal) < hittingAfter W Gᶜ 0 ω := by
      rw [← hτ_eq]
      exact_mod_cast hs
    have hs_not_mem : W s ω ∉ Gᶜ :=
      notMem_of_lt_hittingAfter
        (u := W) (s := Gᶜ) (n := (0 : NNReal)) (ω := ω) hs_lt (by simp)
    simpa using hs_not_mem
  -- Route correction: the same-radius open-ball event is false; the right deterministic normal
  -- form is the centered closed-ball-before-outer event. The remaining proof is the pathwise
  -- continuity argument identifying the annulus exit time with that closed-ball hit time.
  constructor
  · intro hInner
    have hτSphere : W τ ω ∈ Metric.sphere (0 : State) ρ := by
      simpa [τ, stoppedValue, hτ_ne_top] using hInner
    have hτClosed : W τ ω ∈ Metric.closedBall (0 : State) ρ := by
      simpa [Metric.mem_sphere, Metric.mem_closedBall] using hτSphere
    have hτBall : W τ ω ∈ Metric.ball (0 : State) R := by
      rcases hτSphere with hτSphere
      exact Metric.mem_ball.2 (by linarith [hτSphere])
    have hClosed_le :
        hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω ≤ τ :=
      hittingAfter_le_of_mem
        (u := W) (s := Metric.closedBall (0 : State) ρ) (n := (0 : NNReal)) (ω := ω)
        (by simp) hτClosed
    have hOuter_lt :
        (τ : WithTop NNReal) < hittingAfter W (Metric.ball (0 : State) R)ᶜ 0 ω := by
      by_contra hNotLt
      have hOuter_le :
          hittingAfter W (Metric.ball (0 : State) R)ᶜ 0 ω ≤ τ :=
        le_of_not_gt hNotLt
      have hOuter_fin :
          hittingAfter W (Metric.ball (0 : State) R)ᶜ 0 ω < ⊤ :=
        lt_of_le_of_lt hOuter_le ENNReal.coe_lt_top
      let τR : NNReal := (hittingAfter W (Metric.ball (0 : State) R)ᶜ 0 ω).untopA
      have hτR_mem :
          W τR ω ∈ (Metric.ball (0 : State) R)ᶜ := by
        simpa [τR] using
          mem_closedSet_at_hittingAfter_of_lt_top_local
            (A := (Metric.ball (0 : State) R)ᶜ) (W := W)
            (isClosed_compl_iff.mpr Metric.isOpen_ball) hcont hOuter_fin
      have hτR_le : τR ≤ τ := by
        exact_mod_cast hOuter_le
      have hτR_ne : τR ≠ τ := by
        intro hEq
        exact hτR_mem (by simpa [hEq] using hτBall)
      have hτR_lt : τR < τ := lt_of_le_of_ne hτR_le hτR_ne
      have hτR_memG : W τR ω ∈ G := hBeforeMemG τR hτR_lt
      exact hτR_mem hτR_memG.1
    exact lt_of_le_of_lt hClosed_le hOuter_lt
  · intro hBefore
    have hClosed_fin :
        hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω < ⊤ :=
      lt_of_lt_of_le hBefore le_top
    let τρ : NNReal := (hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω).untopA
    have hτρ_ne_top : hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω ≠ ⊤ :=
      ne_of_lt hClosed_fin
    have hτρ_eq :
        ((τρ : NNReal) : WithTop NNReal) =
          hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω := by
      rw [show τρ = (hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω).untopA by rfl]
      rw [WithTop.untopA_eq_untop hτρ_ne_top]
      exact WithTop.coe_untop _ hτρ_ne_top
    have hτρ_memClosed :
        W τρ ω ∈ Metric.closedBall (0 : State) ρ := by
      simpa [τρ] using
        mem_closedSet_at_hittingAfter_of_lt_top_local
          (A := Metric.closedBall (0 : State) ρ) (W := W)
          Metric.isClosed_closedBall hcont hClosed_fin
    have hτρ_pos : 0 < τρ := by
      by_contra hNotPos
      have hZero : τρ = 0 := le_antisymm (le_of_not_gt hNotPos) bot_le
      exact hstart.2 (by simpa [hZero] using hτρ_memClosed)
    have hBeforeMemGρ : ∀ s : NNReal, s < τρ → W s ω ∈ G := by
      intro s hs
      have hs_lt_closed :
          (s : WithTop NNReal) < hittingAfter W (Metric.closedBall (0 : State) ρ) 0 ω := by
        rw [← hτρ_eq]
        exact_mod_cast hs
      have hs_lt_outer :
          (s : WithTop NNReal) < hittingAfter W (Metric.ball (0 : State) R)ᶜ 0 ω :=
        lt_trans (by
          rw [← hτρ_eq]
          exact_mod_cast hs) hBefore
      have hs_not_closed : W s ω ∉ Metric.closedBall (0 : State) ρ :=
        notMem_of_lt_hittingAfter
          (u := W) (s := Metric.closedBall (0 : State) ρ) (n := (0 : NNReal)) (ω := ω)
          hs_lt_closed (by simp)
      have hs_not_outer : W s ω ∉ (Metric.ball (0 : State) R)ᶜ :=
        notMem_of_lt_hittingAfter
          (u := W) (s := (Metric.ball (0 : State) R)ᶜ) (n := (0 : NNReal)) (ω := ω)
          hs_lt_outer (by simp)
      exact ⟨by simpa using hs_not_outer, by simpa using hs_not_closed⟩
    have hAnnulus_le :
        hittingAfter W Gᶜ 0 ω ≤ τρ := by
      have hτρ_memGcompl : W τρ ω ∈ Gᶜ := by
        intro hMemG
        exact hMemG.2 hτρ_memClosed
      exact
        hittingAfter_le_of_mem
          (u := W) (s := Gᶜ) (n := (0 : NNReal)) (ω := ω) (by simp) hτρ_memGcompl
    have hτ_le_τρ : τ ≤ τρ := by
      exact_mod_cast (show ((τ : NNReal) : WithTop NNReal) ≤ τρ by simpa [hτ_eq] using hAnnulus_le)
    have hτρ_le_τ : τρ ≤ τ := by
      by_contra hNotLe
      have hτ_lt_τρ : τ < τρ := lt_of_not_ge hNotLe
      have hτ_memGcompl : W τ ω ∈ Gᶜ := by
        simpa [τ] using
          mem_closedSet_at_hittingAfter_of_lt_top_local
            (A := Gᶜ) (W := W)
            (isClosed_compl_iff.mpr <| concentricAnnulus_isOpen (0 : State) ρ R) hcont hτfin
      have hτ_memG : W τ ω ∈ G := hBeforeMemGρ τ hτ_lt_τρ
      exact hτ_memGcompl hτ_memG
    have hτ_eq_τρ : τ = τρ := le_antisymm hτ_le_τρ hτρ_le_τ
    have hτNotBall : W τ ω ∉ Metric.ball (0 : State) ρ := by
      intro hτBall
      have hPreimage :
          {s : NNReal | W s ω ∈ Metric.ball (0 : State) ρ} ∈ 𝓝 τ := by
        exact hcont.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hτBall)
      rcases mem_nhds_iff.mp hPreimage with ⟨u, hu_subset, hu_open, hτ_mem_u⟩
      have hτ_pos : 0 < τ := by simpa [hτ_eq_τρ] using hτρ_pos
      have hτ_leftClosure : τ ∈ closure (Set.Iio τ : Set NNReal) := by
        have hclosureIio : closure (Set.Iio τ : Set NNReal) = Set.Iic τ :=
          closure_Iio' ⟨0, hτ_pos⟩
        rw [hclosureIio]
        simp
      rcases (mem_closure_iff.mp hτ_leftClosure) u hu_open hτ_mem_u with ⟨s, hs_mem_u, hs_lt⟩
      have hs_ball : W s ω ∈ Metric.ball (0 : State) ρ := hu_subset hs_mem_u
      exact hBeforeMemGρ s (by simpa [hτ_eq_τρ] using hs_lt).2 (Metric.ball_subset_closedBall hs_ball)
    have hτClosed : W τ ω ∈ Metric.closedBall (0 : State) ρ := by
      simpa [hτ_eq_τρ] using hτρ_memClosed
    have hdist_le : dist (W τ ω) (0 : State) ≤ ρ := by
      simpa [Metric.mem_closedBall] using hτClosed
    have hdist_ge : ρ ≤ dist (W τ ω) (0 : State) := by
      simpa [Metric.mem_ball] using hτNotBall
    have hτSphere : W τ ω ∈ Metric.sphere (0 : State) ρ := by
      exact Metric.mem_sphere.2 (le_antisymm hdist_le hdist_ge)
    simpa [τ, stoppedValue, hτ_ne_top] using hτSphere

/-- Helper for Theorem 25.40: after centering at `y`, the frontier event that the annulus exit map
lands on the inner sphere agrees almost surely with the closed-ball-before-outer event for `W`. -/
private theorem annulusExitValueInnerSphereEvent_ae_eq_closedBallBeforeOuter
    (μ : ProbabilityMeasure Ω) (W : VectorProcess) (y : State)
    {ρ R : ℝ}
    {Wc : VectorProcess} {x0 : State}
    {exitValue : Ω → frontier (concentricAnnulus (0 : State) ρ R)}
    (hx0 : x0 ∈ concentricAnnulus (0 : State) ρ R)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hWcStart : ∀ ω : Ω, Wc 0 ω = x0)
    (hEqAllTimes :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, W t ω - y = Wc t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤)
    (hExitValue :
      ∀ ω : Ω, hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0 ω < ⊤ →
        (exitValue ω : State) =
          stoppedValue Wc
            (hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0) ω) :
    {ω | (exitValue ω : State) ∈ Metric.sphere (0 : State) ρ} =ᵐ[(μ : Measure Ω)]
      {ω |
        hittingAfter W (Metric.closedBall y ρ) 0 ω <
          hittingAfter W (Metric.ball y R)ᶜ 0 ω} := by
  filter_upwards [hEqAllTimes, hExitFinite] with ω hωEq hωFin
  have hStartω : Wc 0 ω ∈ concentricAnnulus (0 : State) ρ R := by
    simpa [hWcStart ω] using hx0
  have hClosedClock :
      hittingAfter Wc (Metric.closedBall (0 : State) ρ) 0 ω =
        hittingAfter W (Metric.closedBall y ρ) 0 ω := by
    have hEqCentered :
        hittingAfter (fun t ω ↦ W t ω - y) (Metric.closedBall (0 : State) ρ) 0 ω =
          hittingAfter Wc (Metric.closedBall (0 : State) ρ) 0 ω :=
      (hittingAfter_stoppedValue_eq_of_forall_eq
        (A := Metric.closedBall (0 : State) ρ) (W := fun t ω ↦ W t ω - y) (Wc := Wc)
        (ω := ω) hωEq).1
    have hTranslate :
        hittingAfter (fun t ω ↦ W t ω - y) (Metric.closedBall (0 : State) ρ) 0 ω =
          hittingAfter W (Metric.closedBall y ρ) 0 ω :=
      hittingAfter_sub_const_eq (W := W) (ω := ω) y <|
        by
          intro z
          simpa [Metric.mem_closedBall, dist_eq_norm]
    calc
      hittingAfter Wc (Metric.closedBall (0 : State) ρ) 0 ω =
          hittingAfter (fun t ω ↦ W t ω - y) (Metric.closedBall (0 : State) ρ) 0 ω :=
        hEqCentered.symm
      _ = hittingAfter W (Metric.closedBall y ρ) 0 ω := hTranslate
  have hOuterClock :
      hittingAfter Wc (Metric.ball (0 : State) R)ᶜ 0 ω =
        hittingAfter W (Metric.ball y R)ᶜ 0 ω := by
    have hEqCentered :
        hittingAfter (fun t ω ↦ W t ω - y) (Metric.ball (0 : State) R)ᶜ 0 ω =
          hittingAfter Wc (Metric.ball (0 : State) R)ᶜ 0 ω :=
      (hittingAfter_stoppedValue_eq_of_forall_eq
        (A := (Metric.ball (0 : State) R)ᶜ) (W := fun t ω ↦ W t ω - y) (Wc := Wc)
        (ω := ω) hωEq).1
    have hTranslate :
        hittingAfter (fun t ω ↦ W t ω - y) (Metric.ball (0 : State) R)ᶜ 0 ω =
          hittingAfter W (Metric.ball y R)ᶜ 0 ω :=
      hittingAfter_sub_const_eq (W := W) (ω := ω) y <|
        by
          intro z
          simpa [Metric.mem_ball, dist_eq_norm]
    calc
      hittingAfter Wc (Metric.ball (0 : State) R)ᶜ 0 ω =
          hittingAfter (fun t ω ↦ W t ω - y) (Metric.ball (0 : State) R)ᶜ 0 ω :=
        hEqCentered.symm
      _ = hittingAfter W (Metric.ball y R)ᶜ 0 ω := hTranslate
  constructor
  · intro hInner
    have hInnerWc :
        stoppedValue Wc (hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0) ω ∈
          Metric.sphere (0 : State) ρ := by
      simpa [hExitValue ω hωFin] using hInner
    have hClosedWc :
        hittingAfter Wc (Metric.closedBall (0 : State) ρ) 0 ω <
          hittingAfter Wc (Metric.ball (0 : State) R)ᶜ 0 ω :=
      (annulusExitOnInnerSphere_iff_closedBallBeforeOuter
        (W := Wc) (ω := ω) (ρ := ρ) (R := R) hWcCont hStartω hωFin hr hR).1 hInnerWc
    simpa [hClosedClock, hOuterClock] using hClosedWc
  · intro hClosed
    have hClosedWc :
        hittingAfter Wc (Metric.closedBall (0 : State) ρ) 0 ω <
          hittingAfter Wc (Metric.ball (0 : State) R)ᶜ 0 ω := by
      simpa [hClosedClock, hOuterClock] using hClosed
    have hInnerWc :
        stoppedValue Wc (hittingAfter Wc (concentricAnnulus (0 : State) ρ R)ᶜ 0) ω ∈
          Metric.sphere (0 : State) ρ :=
      (annulusExitOnInnerSphere_iff_closedBallBeforeOuter
        (W := Wc) (ω := ω) (ρ := ρ) (R := R) hWcCont hStartω hωFin hr hR).2 hClosedWc
    simpa [hExitValue ω hωFin] using hInnerWc

/-- Helper for Theorem 25.40: once the centered exit-expectation identity is known, the profile
value is exactly the measure of the inner-sphere exit event. -/
private theorem exitValueInnerSphere_measure_eq_profile
    {μ : ProbabilityMeasure Ω} {x0 : State} {ρ R : ℝ}
    {exitValue : Ω → frontier (concentricAnnulus (0 : State) ρ R)}
    (hExitMeas : Measurable exitValue)
    (hProfile :
      centeredAnnulusProfile (d := d) ρ R x0 =
        ∫ ω, centeredAnnulusProfile (d := d) ρ R (exitValue ω : State) ∂(μ : Measure Ω))
    (hr : 0 < ρ) (hR : ρ < R) :
    (μ : Measure Ω) {ω | (exitValue ω : State) ∈ Metric.sphere (0 : State) ρ} =
      ENNReal.ofReal (centeredAnnulusProfile (d := d) ρ R x0) := by
  let A : Set Ω := {ω | (exitValue ω : State) ∈ Metric.sphere (0 : State) ρ}
  have hA_meas : MeasurableSet A := by
    have hExitStateMeas : Measurable fun ω : Ω ↦ (exitValue ω : State) :=
      continuous_subtype_val.measurable.comp hExitMeas
    simpa [A] using hExitStateMeas Metric.isClosed_sphere.measurableSet
  have hBoundary :
      (fun ω ↦ centeredAnnulusProfile (d := d) ρ R (exitValue ω : State)) =
        A.indicator (fun _ : Ω ↦ (1 : ℝ)) := by
    funext ω
    simpa [A, Set.indicator] using
      centeredAnnulusProfile_boundaryIndicator (d := d) hr hR (exitValue ω)
  calc
    (μ : Measure Ω) A = ENNReal.ofReal ((μ : Measure Ω).real A) := by
      exact (MeasureTheory.ofReal_measureReal (μ := (μ : Measure Ω)) (s := A)).symm
    _ = ENNReal.ofReal (∫ ω, A.indicator (fun _ : Ω ↦ (1 : ℝ)) ω ∂(μ : Measure Ω)) := by
      congr 1
      rw [integral_indicator_const (μ := (μ : Measure Ω)) (1 : ℝ) hA_meas]
      simp [smul_eq_mul]
    _ = ENNReal.ofReal
          (∫ ω, centeredAnnulusProfile (d := d) ρ R (exitValue ω : State) ∂(μ : Measure Ω)) := by
      congr 1
      rw [hBoundary]
    _ = ENNReal.ofReal (centeredAnnulusProfile (d := d) ρ R x0) := by
      rw [hProfile]

/-- Helper for Theorem 25.40: the fixed-outer closed-ball-before-outer event already has the
annulus-profile probability. This is the corrected event computed by the annulus exit
distribution. -/
private theorem annulusClosedBallBeforeOuter_probability_eq_profile
    (μ : ProbabilityMeasure Ω) (W : VectorProcess) (x y : State)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    {ρ R : ℝ} (hr : 0 < ρ) (hρx : ρ < dist x y) (hR : dist x y < R) :
    (μ : Measure Ω)
        {ω |
          hittingAfter W (Metric.closedBall y ρ) 0 ω <
            hittingAfter W (Metric.ball y R)ᶜ 0 ω} =
      ENNReal.ofReal (centeredAnnulusProfile (d := d) ρ R (x - y)) := by
  let x0 : State := x - y
  let G : Set State := concentricAnnulus (0 : State) ρ R
  have hd0 : d ≠ 0 := ne_zero_of_radius_lt_dist (d := d) x y hr hρx
  letI : NeZero d := ⟨hd0⟩
  have hx0 : x0 ∈ G := by
    -- Proof comment: after centering at `y`, the start point lies in the bounded annulus between
    -- radii `ρ` and `R`.
    exact sub_mem_centeredAnnulus_of_lt_dist_lt (d := d) hρx hR
  let Wy : VectorProcess := fun t ω ↦ W t ω - y
  have hWy :
      IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wy x0 := by
    -- Proof comment: after translating the center `y` to the origin, the Brownian start moves to
    -- `x - y`.
    simpa [Wy, x0] using
      brownianVectorStartedAt_sub_const_startedAtSub
        (μ := (μ : Measure Ω)) (W := W) (x := x) (y := y) hW
  rcases
      existsContinuousBrownianVectorStartedAtModification
        (μ := μ) (W := Wy) (x := x0) hWy with
    ⟨Wc, hWc, hWcCont, hWcStart, hWcEq⟩
  have hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wy Gᶜ 0 ω < ⊤ := by
    -- Proof comment: the centered process starts inside a bounded annulus, so its first annulus
    -- exit is almost surely finite.
    simpa [G] using
      ae_annulusExit_lt_top_startedAt
        (μ := μ) (W := Wy) (x0 := x0) hx0 hWy hr (by linarith)
  have hStageEq :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter Wy Gᶜ 0 ω = hittingAfter Wc Gᶜ 0 ω ∧
          stoppedValue Wy (hittingAfter Wy Gᶜ 0) ω =
            stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω := by
    -- Proof comment: the same-space continuous modification agrees with `Wy` at every time
    -- outside one null set, so the annulus exit clock and stopped value transport almost surely.
    exact
      stageExitStoppedValue_ae_eq_continuousVersion
        (μ := (μ : Measure Ω)) (W := Wy) (Wc := Wc) (U := G) hWcEq
  rcases
      centeredAnnulusExitData_ofContinuousStartedAt
        (μ := μ) (Wc := Wc) (x0 := x0) (ρ := ρ) (R := R)
        hx0 hWc hWcCont hWcStart hr (by linarith) with
    ⟨exitValue, hExitMeas, hExitValue⟩
  have hExitFiniteWc :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc Gᶜ 0 ω < ⊤ := by
    -- Proof comment: the same-space continuous modification shares the finite annulus exit clock
    -- almost surely with the translated Brownian motion `Wy`.
    filter_upwards [hExitFinite, hStageEq] with ω hω hEq
    simpa [hEq.1] using hω
  let E : Set Ω :=
    {ω |
      hittingAfter W (Metric.closedBall y ρ) 0 ω <
        hittingAfter W (Metric.ball y R)ᶜ 0 ω}
  let A : Set Ω := {ω | (exitValue ω : State) ∈ Metric.sphere (0 : State) ρ}
  have hProfileExit :
      centeredAnnulusProfile (d := d) ρ R x0 =
        ∫ ω, centeredAnnulusProfile (d := d) ρ R (exitValue ω : State) ∂(μ : Measure Ω) :=
    centeredAnnulusProfile_exitExpectation_startedAt
      (d := d) (μ := μ) (Wc := Wc) (x0 := x0) (ρ := ρ) (R := R)
      hx0 hWc hWcCont hExitFiniteWc hExitMeas hExitValue hr (by linarith)
  have hEventEq : A =ᵐ[(μ : Measure Ω)] E := by
    simpa [A, E] using
      annulusExitValueInnerSphereEvent_ae_eq_closedBallBeforeOuter
        (d := d) (μ := μ) (W := W) (y := y) (ρ := ρ) (R := R) (Wc := Wc)
        (x0 := x0) (exitValue := exitValue) hx0 hWcCont hWcStart hWcEq hExitFiniteWc hExitValue
  -- Proof comment: once the fixed-start exit expectation is isolated, the corrected closed-ball
  -- event is computed by the same centered inner-sphere exit set, so the boundary-indicator
  -- integral still collapses directly to its event measure.
  calc
    (μ : Measure Ω) E = (μ : Measure Ω) A := by
      exact measure_congr hEventEq.symm
    _ = ENNReal.ofReal (centeredAnnulusProfile (d := d) ρ R x0) := by
      exact exitValueInnerSphere_measure_eq_profile
        (d := d) (μ := μ) (x0 := x0) (ρ := ρ) (R := R)
        (exitValue := exitValue) hExitMeas hProfileExit hr (by linarith)

/-- Helper for Theorem 25.40: a continuous path that hits a closed target by finite time actually
lands in that target at its hitting time. -/
private theorem mem_closedSet_at_hittingAfter_of_lt_top
    {A : Set State} {W : VectorProcess} {ω : Ω}
    (hAclosed : IsClosed A)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hτ : hittingAfter W A 0 ω < ⊤) :
    W (hittingAfter W A 0 ω).untopA ω ∈ A := by
  have hτ_ne_top : hittingAfter W A 0 ω ≠ ⊤ := ne_of_lt hτ
  let hitSet : Set NNReal := {t : NNReal | W t ω ∈ A}
  have hHitExists : ∃ t : NNReal, W t ω ∈ A := by
    -- Proof comment: finite hitting time means the raw hitting set is nonempty.
    simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hτ_ne_top
    rcases hτ_ne_top with ⟨t, _, htA⟩
    exact ⟨t, htA⟩
  have hHitNonempty : hitSet.Nonempty := by
    rcases hHitExists with ⟨t, htA⟩
    exact ⟨t, htA⟩
  have hHitClosed : IsClosed hitSet := by
    -- Proof comment: continuity of the path turns a closed target into a closed set of hit times.
    change IsClosed ((fun t : NNReal ↦ W t ω) ⁻¹' A)
    exact hAclosed.preimage hcont
  have hHitBddBelow : BddBelow hitSet := ⟨0, fun _ _ ↦ bot_le⟩
  have hsInf_mem : sInf hitSet ∈ hitSet :=
    hHitClosed.csInf_mem hHitNonempty hHitBddBelow
  have hτ_eq : (hittingAfter W A 0 ω).untopA = sInf hitSet := by
    -- Proof comment: with start time `0`, the owner hitting time is the infimum of the raw hit
    -- set because every `NNReal` time is automatically nonnegative.
    rw [hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ A} = hitSet by
            ext t
            simp [hitSet]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hHitExists with ⟨t, htA⟩
      exact ⟨t, bot_le, htA⟩
  simpa [hitSet, hτ_eq] using hsInf_mem

/-- Helper for Theorem 25.40: if two paths agree at every time, then their `hittingAfter` clocks
and corresponding stopped values against the same target set agree as well. This packages the
pathwise transport from the original centered Brownian spelling to its continuous modification. -/
private theorem hittingAfter_stoppedValue_eq_of_forall_eq
    {A : Set State} {W Wc : VectorProcess} {ω : Ω}
    (hall : ∀ t : NNReal, W t ω = Wc t ω) :
    hittingAfter W A 0 ω = hittingAfter Wc A 0 ω ∧
      stoppedValue W (hittingAfter W A 0) ω =
        stoppedValue Wc (hittingAfter Wc A 0) ω := by
  have hHit :
      hittingAfter W A 0 ω = hittingAfter Wc A 0 ω := by
    classical
    unfold hittingAfter
    by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ A
    · have h' : ∃ j, (0 : NNReal) ≤ j ∧ Wc j ω ∈ A := by
        rcases h with ⟨j, hj0, hjA⟩
        exact ⟨j, hj0, by simpa [hall j] using hjA⟩
      have hSet :
          {j : NNReal | (0 : NNReal) ≤ j ∧ W j ω ∈ A} =
            {j : NNReal | (0 : NNReal) ≤ j ∧ Wc j ω ∈ A} := by
        ext j
        simp [hall j]
      rw [if_pos h, if_pos h']
      exact congrArg (fun s : Set NNReal ↦ (((sInf s : NNReal) : WithTop NNReal))) hSet
    · have h' : ¬ ∃ j, (0 : NNReal) ≤ j ∧ Wc j ω ∈ A := by
        intro h'
        apply h
        rcases h' with ⟨j, hj0, hjA⟩
        exact ⟨j, hj0, by simpa [hall j] using hjA⟩
      rw [if_neg h, if_neg h']
  refine ⟨hHit, ?_⟩
  calc
    stoppedValue W (hittingAfter W A 0) ω = W (hittingAfter W A 0 ω).untopA ω := rfl
    _ = Wc (hittingAfter W A 0 ω).untopA ω := by simpa using hall _
    _ = Wc (hittingAfter Wc A 0 ω).untopA ω := by rw [hHit]
    _ = stoppedValue Wc (hittingAfter Wc A 0) ω := rfl

/-- Helper for Theorem 25.40: the annulus exit clock and exit value agree almost surely between a
Brownian path and a same-space continuous modification that coincides with it at every time
outside one null set. -/
private theorem stageExitStoppedValue_ae_eq_continuousVersion
    {μ : Measure Ω} {W Wc : VectorProcess} {U : Set State}
    (hEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, W t ω = Wc t ω) :
    ∀ᵐ ω ∂μ,
      hittingAfter W Uᶜ 0 ω = hittingAfter Wc Uᶜ 0 ω ∧
        stoppedValue W (hittingAfter W Uᶜ 0) ω =
          stoppedValue Wc (hittingAfter Wc Uᶜ 0) ω := by
  filter_upwards [hEq] with ω hω
  simpa using hittingAfter_stoppedValue_eq_of_forall_eq (A := Uᶜ) hω

/-- Helper for Theorem 25.40: if the strict positive hitting clock of `A` lies strictly below an
upper bound `T`, then some actual strict positive hit occurs strictly before `T`. -/
private theorem exists_strictPositiveHit_before_of_lt
    {A : Set State} {W : VectorProcess} {ω : Ω} {T : WithTop NNReal}
    (hτ : (τ_[W, A]) ω < T) :
    ∃ t : NNReal, 0 < t ∧ W t ω ∈ A ∧ (t : WithTop NNReal) < T := by
  have hτ_top : (τ_[W, A]) ω < ⊤ := lt_of_lt_of_le hτ le_top
  rcases (strictPositiveHittingTime_lt_top_iff W A ω).1 hτ_top with ⟨t₀, ht₀, ht₀A⟩
  by_cases hT : T = ⊤
  · -- Proof comment: if the upper bound is `⊤`, any realized strict positive hit already lies
    -- below it.
    rw [hT]
    exact ⟨t₀, ht₀, ht₀A, ENNReal.coe_lt_top⟩
  · lift T to NNReal using hT with b hb
    let hitSet : Set NNReal := {t : NNReal | 0 < t ∧ W t ω ∈ A}
    have hHit : ∃ t : NNReal, 0 < t ∧ W t ω ∈ A := ⟨t₀, ht₀, ht₀A⟩
    have hNotAllGe : ¬ ∀ t ∈ hitSet, b ≤ t := by
      intro hAll
      have hsInf_ge : b ≤ sInf hitSet := by
        refine le_csInf ?_ ?_
        · exact ⟨t₀, by simpa [hitSet] using ⟨ht₀, ht₀A⟩⟩
        · intro t ht
          exact hAll t ht
      have hτ_eq :
          ((τ_[W, A]) ω : WithTop NNReal) = ((sInf hitSet : NNReal) : WithTop NNReal) := by
        simp [strictPositiveHittingTime, hHit, hitSet]
      have hsInf_lt_b :
          ((sInf hitSet : NNReal) : WithTop NNReal) < (b : WithTop NNReal) := by
        simpa [hτ_eq, hb] using hτ
      have hsInf_ge' :
          (b : WithTop NNReal) ≤ ((sInf hitSet : NNReal) : WithTop NNReal) := by
        exact_mod_cast hsInf_ge
      exact not_le_of_gt hsInf_lt_b hsInf_ge'
    push Not at hNotAllGe
    rcases hNotAllGe with ⟨t, htHit, htlt⟩
    have htlt' : (t : WithTop NNReal) < (b : WithTop NNReal) := by
      exact_mod_cast htlt
    exact ⟨t, htHit.1, htHit.2, by simpa [hb] using htlt'⟩

/-- Helper for Theorem 25.40: if a continuous path stays inside the outer ball on the whole
interval `[0, t]`, then the complement-exit time of that outer ball is strictly larger than `t`.
-/
private theorem lt_hittingAfter_outerBall_compl_of_forall_mem_Icc
    {W : VectorProcess} {ω : Ω} {y : State} {R : ℝ} {t : NNReal}
    (hcont : Continuous fun s : NNReal ↦ W s ω)
    (hInside : ∀ s : NNReal, s ∈ Set.Icc 0 t → W s ω ∈ Metric.ball y R) :
    (t : WithTop NNReal) < hittingAfter W (Metric.ball y R)ᶜ 0 ω := by
  by_contra hNotLt
  have hτ_le : hittingAfter W (Metric.ball y R)ᶜ 0 ω ≤ t := le_of_not_gt hNotLt
  have hτ_finite : hittingAfter W (Metric.ball y R)ᶜ 0 ω < ⊤ :=
    lt_of_le_of_lt hτ_le ENNReal.coe_lt_top
  have hτ_mem :
      W (hittingAfter W (Metric.ball y R)ᶜ 0 ω).untopA ω ∈ (Metric.ball y R)ᶜ :=
    mem_closedSet_at_hittingAfter_of_lt_top
      (A := (Metric.ball y R)ᶜ) (W := W)
      (isClosed_compl_iff.mpr Metric.isOpen_ball) hcont hτ_finite
  lift hittingAfter W (Metric.ball y R)ᶜ 0 ω to NNReal using hτ_finite.ne with τ hτ_eq
  have hτ_ne_top : hittingAfter W (Metric.ball y R)ᶜ 0 ω ≠ ⊤ := by
    rw [← hτ_eq]
    exact ENNReal.coe_ne_top
  have hτ_untop_eq : (hittingAfter W (Metric.ball y R)ᶜ 0 ω).untopA = τ := by
    apply le_antisymm
    · exact
        (WithTop.untopA_le_iff
          (x := hittingAfter W (Metric.ball y R)ᶜ 0 ω) (a := τ) hτ_ne_top).2
        (by simpa [hτ_eq])
    · exact
        (WithTop.le_untopA_iff
          (x := hittingAfter W (Metric.ball y R)ᶜ 0 ω) (a := τ) hτ_ne_top).2
        (by simpa [hτ_eq])
  have hτ_mem' : W τ ω ∈ (Metric.ball y R)ᶜ := by
    exact hτ_untop_eq ▸ hτ_mem
  have hτ_le' : τ ≤ t := by
    exact_mod_cast hτ_le
  have hτ_inside : W τ ω ∈ Metric.ball y R :=
    hInside τ ⟨bot_le, hτ_le'⟩
  exact hτ_mem' hτ_inside

/-- Helper for Theorem 25.40: on the almost-sure continuous-path event, eventual entry into the
inner ball is the increasing union of the annulus exit events with larger and larger outer radii.
-/
private theorem ae_hitBallEvent_eq_iUnion_annulusExitEvents
    (μ : ProbabilityMeasure Ω) (W : VectorProcess) (x y : State)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (r : ℝ) :
    {ω | ∃ t : NNReal, 0 < t ∧ W t ω ∈ Metric.ball y r} =ᵐ[(μ : Measure Ω)]
      ⋃ n : ℕ,
        {ω | (τ_[W, Metric.ball y r]) ω <
            hittingAfter W (Metric.ball y (dist x y + n + 1))ᶜ 0 ω} := by
  have hcont :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous (fun t : NNReal ↦ W t ω) :=
    brownianVectorStartedAt_aeContinuous hW
  filter_upwards [hcont] with ω hω
  apply propext
  change ω ∈ {ω | ∃ t : NNReal, 0 < t ∧ W t ω ∈ Metric.ball y r} ↔
      ω ∈ ⋃ n : ℕ,
        {ω | (τ_[W, Metric.ball y r]) ω <
            hittingAfter W (Metric.ball y (dist x y + n + 1))ᶜ 0 ω}
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, htBall⟩
    let radiusAlongPath : NNReal → ℝ := fun s ↦ dist (W s ω) y
    have hRadiusCont : Continuous radiusAlongPath := by
      -- Proof comment: the pathwise radius from `y` is continuous because both the Brownian path
      -- and the distance map are continuous.
      exact hω.dist continuous_const
    have hRadiusCompact :
        IsCompact (radiusAlongPath '' Set.Icc (0 : NNReal) t) :=
      isCompact_Icc.image_of_continuousOn hRadiusCont.continuousOn
    rcases hRadiusCompact.bddAbove with ⟨M, hM⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, M < dist x y + n + 1 := by
      obtain ⟨n, hn⟩ := exists_nat_gt (M - dist x y - 1)
      refine ⟨n, ?_⟩
      have hn' : M - dist x y - 1 < (n : ℝ) := by
        exact_mod_cast hn
      linarith
    have hInside :
        ∀ s : NNReal, s ∈ Set.Icc 0 t →
          W s ω ∈ Metric.ball y (dist x y + n + 1) := by
      intro s hs
      have hsImage : radiusAlongPath s ∈ radiusAlongPath '' Set.Icc (0 : NNReal) t :=
        ⟨s, hs, rfl⟩
      have hs_le_M : radiusAlongPath s ≤ M := hM hsImage
      exact Metric.mem_ball.2 (lt_of_le_of_lt hs_le_M hn)
    have ht_outer :
        (t : WithTop NNReal) <
          hittingAfter W (Metric.ball y (dist x y + n + 1))ᶜ 0 ω :=
      lt_hittingAfter_outerBall_compl_of_forall_mem_Icc
        (W := W) (ω := ω) (y := y) (R := dist x y + n + 1) hω hInside
    have hτ_le_t :
        (τ_[W, Metric.ball y r]) ω ≤ t :=
      strictPositiveHittingTime_le_of_mem W (Metric.ball y r) ω ht htBall
    have hτ_le_t' :
        (((τ_[W, Metric.ball y r]) ω : WithTop NNReal)) ≤ t := by
      exact_mod_cast hτ_le_t
    -- Proof comment: the realized hit at time `t` bounds the inner-ball clock from above, while
    -- continuity keeps the path inside a sufficiently large outer ball up to time `t`.
    exact ⟨n, lt_of_le_of_lt hτ_le_t' ht_outer⟩
  · intro hω
    rcases hω with ⟨n, hn⟩
    rcases exists_strictPositiveHit_before_of_lt
        (A := Metric.ball y r) (W := W) (ω := ω)
        (T := hittingAfter W (Metric.ball y (dist x y + n + 1))ᶜ 0 ω) hn with
      ⟨t, ht, htBall, _⟩
    -- Proof comment: once the strict positive hitting clock is strictly below the outer exit time,
    -- the infimum defining that clock yields an actual strict positive hit before that exit.
    exact ⟨t, ht, htBall⟩

/-- Helper for Theorem 25.40: after rewriting the annulus exit probabilities by the explicit
profile, the remaining outer-radius limit should be computed once as a standalone asymptotic
lemma. -/
private theorem annulusProfile_tendsto_target_along_nat
    (x y : State) (r : ℝ) (hr : 0 < r) (hxy : r < dist x y) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ENNReal.ofReal
          (centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y)))
      Filter.atTop
      (𝓝 (if d ≤ 2 then 1 else ENNReal.ofReal ((r / dist x y) ^ (d - 2)))) := by
  have hdist_pos : 0 < dist x y := lt_trans hr hxy
  have hR_atTop : Filter.Tendsto (fun n : ℕ ↦ (dist x y + n + 1 : ℝ)) Filter.atTop Filter.atTop := by
    -- Proof comment: the outer radius `dist x y + n + 1` grows linearly with `n`.
    simpa [add_assoc, add_left_comm, add_comm] using
      Filter.atTop.tendsto_atTop_add_const_right (dist x y + 1) tendsto_natCast_atTop_atTop
  have hnorm : ‖x - y‖ = dist x y := by
    simpa [dist_eq_norm, sub_eq_add_neg] using (dist_eq_norm x y).symm
  by_cases h1 : d = 1
  · have htail :
        Filter.Tendsto
          (fun n : ℕ ↦ (dist x y - r) / (dist x y + n + 1 - r : ℝ))
          Filter.atTop
          (𝓝 0) := by
      have hden_atTop :
          Filter.Tendsto (fun n : ℕ ↦ (dist x y + n + 1 - r : ℝ)) Filter.atTop Filter.atTop := by
        -- Proof comment: subtracting the fixed inner radius still leaves an affine sequence going
        -- to `+∞`.
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          Filter.atTop.tendsto_atTop_add_const_right (dist x y + 1 - r)
            tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop hden_atTop
    have hreal :
        Filter.Tendsto
          (fun n : ℕ ↦ centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y))
          Filter.atTop
          (𝓝 1) := by
      have hrewrite :
          (fun n : ℕ ↦ centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y)) =
            fun n : ℕ ↦ 1 - (dist x y - r) / (dist x y + n + 1 - r : ℝ) := by
        funext n
        have hden_ne : (dist x y + n + 1 - r : ℝ) ≠ 0 := by
          have : 0 < dist x y + n + 1 - r := by
            have hn : (0 : ℝ) < n + 1 := by positivity
            linarith
          linarith
        simp [centeredAnnulusProfile, h1, hnorm]
        field_simp [hden_ne]
        ring
      rw [hrewrite]
      simpa using tendsto_const_nhds.sub htail
    -- Proof comment: the one-dimensional affine profile is `1` plus a vanishing `1 / R` tail.
    simpa [h1] using ENNReal.tendsto_ofReal hreal
  · by_cases h2 : d = 2
    · have hlog_atTop :
          Filter.Tendsto (fun n : ℕ ↦ Real.log (dist x y + n + 1 : ℝ)) Filter.atTop Filter.atTop :=
        Real.tendsto_log_atTop.comp hR_atTop
      have htail :
          Filter.Tendsto
            (fun n : ℕ ↦
              (Real.log r - Real.log (dist x y)) /
                (Real.log (dist x y + n + 1) - Real.log r))
            Filter.atTop
            (𝓝 0) := by
        have hden_atTop :
            Filter.Tendsto
              (fun n : ℕ ↦ Real.log (dist x y + n + 1) - Real.log r)
              Filter.atTop
              Filter.atTop := by
          -- Proof comment: subtracting the constant boundary term `log r` preserves divergence of
          -- the outer logarithm.
          simpa [sub_eq_add_neg] using
            Filter.atTop.tendsto_atTop_add_const_right (-Real.log r) hlog_atTop
        exact tendsto_const_nhds.div_atTop hden_atTop
      have hreal :
          Filter.Tendsto
            (fun n : ℕ ↦ centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y))
            Filter.atTop
            (𝓝 1) := by
        have hrewrite :
            (fun n : ℕ ↦ centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y)) =
              fun n : ℕ ↦
                1 + (Real.log r - Real.log (dist x y)) /
                  (Real.log (dist x y + n + 1) - Real.log r) := by
          funext n
          have hRpos : 0 < dist x y + n + 1 := by
            have hn : (0 : ℝ) < n + 1 := by positivity
            linarith
          have hden_ne : Real.log (dist x y + n + 1) - Real.log r ≠ 0 := by
            have hlog_lt :
                Real.log r < Real.log (dist x y + n + 1) := by
              exact Real.log_lt_log hr (by linarith)
            exact sub_ne_zero.mpr <| by
              intro hEq
              exact (ne_of_lt hlog_lt) hEq.symm
          simp [centeredAnnulusProfile, h2, hnorm]
          field_simp [hden_ne]
          ring
        rw [hrewrite]
        simpa using tendsto_const_nhds.add htail
      -- Proof comment: the planar logarithmic profile differs from `1` by a constant divided by
      -- a logarithmic denominator that diverges to `+∞`.
      simpa [h1, h2] using ENNReal.tendsto_ofReal hreal
    · have hdgt : 2 < d := by
        have hd0 : d ≠ 0 := ne_zero_of_radius_lt_dist (d := d) x y hr hxy
        omega
      let b : ℕ → ℝ := fun n ↦ (r / (dist x y + n + 1 : ℝ)) ^ (d - 2)
      have hb_base :
          Filter.Tendsto (fun n : ℕ ↦ r / (dist x y + n + 1 : ℝ)) Filter.atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hR_atTop
      have hb :
          Filter.Tendsto b Filter.atTop (𝓝 0) := by
        -- Proof comment: the decaying outer-ratio term is a positive integer power of a quantity
        -- that already tends to `0`.
        have hpow :
            Filter.Tendsto
              (fun n : ℕ ↦ (r / (dist x y + n + 1 : ℝ)) ^ (d - 2))
              Filter.atTop
              (𝓝 ((0 : ℝ) ^ (d - 2))) :=
          (continuous_pow (d - 2)).continuousAt.tendsto.comp hb_base
        have hk : 0 < d - 2 := by omega
        simpa [b, hk.ne'] using hpow
      let a : ℝ := (r / dist x y) ^ (d - 2)
      have hreal :
          Filter.Tendsto
            (fun n : ℕ ↦ centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y))
            Filter.atTop
            (𝓝 a) := by
        have hrewrite :
            (fun n : ℕ ↦ centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y)) =
              fun n : ℕ ↦ (a - b n) / (1 - b n) := by
          funext n
          simp [centeredAnnulusProfile, h1, h2, hnorm, a, b]
        rw [hrewrite]
        have hnum : Filter.Tendsto (fun n : ℕ ↦ a - b n) Filter.atTop (𝓝 (a - 0)) :=
          tendsto_const_nhds.sub hb
        have hden : Filter.Tendsto (fun n : ℕ ↦ 1 - b n) Filter.atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub hb
        simpa using hnum.div hden
      have hdle : ¬ d ≤ 2 := by
        omega
      -- Proof comment: in dimensions `d > 2`, the explicit annulus profile is a rational
      -- expression in the decaying outer term `b n`, so it converges to the power-law target.
      simpa [a, h1, h2, hdle] using ENNReal.tendsto_ofReal hreal

/-- Helper for Theorem 25.40: once the Brownian path starts outside `Metric.ball y ρ`, the fixed
open-ball-before-outer event is exactly the union of the corresponding smaller closed-ball-before-
outer events. -/
private theorem openBallBeforeOuter_iff_exists_closedBallBeforeOuterApprox
    {W : VectorProcess} {ω : Ω} {x y : State} {ρ R : ℝ}
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω = x) (hr : 0 < ρ) (hρx : ρ < dist x y) :
    ((τ_[W, Metric.ball y ρ]) ω < hittingAfter W (Metric.ball y R)ᶜ 0 ω) ↔
      ∃ n : ℕ,
        hittingAfter W (Metric.closedBall y (ρ * (n + 1) / (n + 2))) 0 ω <
          hittingAfter W (Metric.ball y R)ᶜ 0 ω := by
  constructor
  · intro hOpen
    rcases exists_strictPositiveHit_before_of_lt
        (A := Metric.ball y ρ) (W := W) (ω := ω)
        (T := hittingAfter W (Metric.ball y R)ᶜ 0 ω) hOpen with
      ⟨t, ht, htBall, htOuter⟩
    let δ : ℝ := ρ - dist (W t ω) y
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact sub_pos.mpr (Metric.mem_ball.1 htBall)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ρ / δ - 2 < n := exists_nat_gt (ρ / δ - 2)
    have hfrac_lt : ρ / ((n : ℝ) + 2) < δ := by
      have hbound : ρ / δ < (n : ℝ) + 2 := by
        have hn' : ρ / δ - 2 < (n : ℝ) := by exact_mod_cast hn
        linarith
      have hmul_lt : ρ < δ * ((n : ℝ) + 2) := by
        exact (div_lt_iff₀ hδpos).1 hbound
      have hn2_pos : 0 < (n : ℝ) + 2 := by positivity
      exact (div_lt_iff₀ hn2_pos).2 (by simpa [mul_comm] using hmul_lt)
    have happrox_eq :
        ρ * ((n : ℝ) + 1) / ((n : ℝ) + 2) = ρ - ρ / ((n : ℝ) + 2) := by
      have hn2_ne : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hn2_ne]
      ring
    have hmemClosed :
        W t ω ∈ Metric.closedBall y (ρ * (n + 1) / (n + 2)) := by
      refine Metric.mem_closedBall.2 ?_
      rw [happrox_eq]
      dsimp [δ] at hfrac_lt
      linarith
    exact ⟨n, lt_of_le_of_lt
      (hittingAfter_le_of_mem
        (u := W) (s := Metric.closedBall y (ρ * (n + 1) / (n + 2))) (n := (0 : NNReal))
        (ω := ω) (by exact ht.le) hmemClosed)
      htOuter⟩
  · rintro ⟨n, hClosed⟩
    let ρn : ℝ := ρ * (n + 1) / (n + 2)
    have hfrac_lt_one : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
      have hn2_pos : 0 < (n : ℝ) + 2 := by positivity
      exact (div_lt_iff₀ hn2_pos).2 (by linarith)
    have hρn_lt_ρ : ρn < ρ := by
      dsimp [ρn]
      nlinarith [hfrac_lt_one, hr]
    have hρn_lt_dist : ρn < dist x y := lt_trans hρn_lt_ρ hρx
    have hClosed_fin :
        hittingAfter W (Metric.closedBall y ρn) 0 ω < ⊤ :=
      lt_of_lt_of_le hClosed le_top
    let t : NNReal := (hittingAfter W (Metric.closedBall y ρn) 0 ω).untopA
    have ht_eq :
        ((t : NNReal) : WithTop NNReal) = hittingAfter W (Metric.closedBall y ρn) 0 ω := by
      rw [show t = (hittingAfter W (Metric.closedBall y ρn) 0 ω).untopA by rfl]
      rw [WithTop.untopA_eq_untop (ne_of_lt hClosed_fin)]
      exact WithTop.coe_untop _ (ne_of_lt hClosed_fin)
    have ht_memClosed : W t ω ∈ Metric.closedBall y ρn := by
      simpa [t] using
        mem_closedSet_at_hittingAfter_of_lt_top
          (A := Metric.closedBall y ρn) (W := W)
          Metric.isClosed_closedBall hcont hClosed_fin
    have hStartOut : W 0 ω ∉ Metric.closedBall y ρn := by
      have hxOut : x ∉ Metric.closedBall y ρn := by
        simpa [Metric.mem_closedBall] using not_le_of_gt hρn_lt_dist
      simpa [hStart] using hxOut
    have ht_pos : 0 < t := by
      by_contra hNotPos
      have hZero : t = 0 := le_antisymm (le_of_not_gt hNotPos) bot_le
      exact hStartOut (by simpa [hZero] using ht_memClosed)
    have ht_memBall : W t ω ∈ Metric.ball y ρ := by
      refine Metric.mem_ball.2 (lt_of_le_of_lt ?_ hρn_lt_ρ)
      simpa [Metric.mem_closedBall] using ht_memClosed
    have hOpen_le :
        (τ_[W, Metric.ball y ρ]) ω ≤ t :=
      strictPositiveHittingTime_le_of_mem W (Metric.ball y ρ) ω ht_pos ht_memBall
    have ht_lt_outer :
        (t : WithTop NNReal) < hittingAfter W (Metric.ball y R)ᶜ 0 ω := by
      simpa [ht_eq] using hClosed
    exact lt_of_le_of_lt hOpen_le ht_lt_outer

/-- Helper for Theorem 25.40: the annulus profile at fixed outer radius is continuous under the
standard inner-radius approximants `ρ * (n + 1) / (n + 2) ↑ ρ`. -/
private theorem centeredAnnulusProfile_tendsto_innerRadius_approximants
    (x y : State) {ρ R : ℝ} (hr : 0 < ρ) (hρx : ρ < dist x y) (hR : dist x y < R) :
    Filter.Tendsto
      (fun n : ℕ ↦ centeredAnnulusProfile (d := d) (ρ * (n + 1) / (n + 2)) R (x - y))
      Filter.atTop
      (𝓝 (centeredAnnulusProfile (d := d) ρ R (x - y))) := by
  have hnorm : ‖x - y‖ = dist x y := by
    simpa [dist_eq_norm, sub_eq_add_neg] using (dist_eq_norm x y).symm
  have hρR : ρ < R := lt_trans hρx hR
  have hρApprox :
      Filter.Tendsto (fun n : ℕ ↦ ρ * ((n : ℝ) + 1) / ((n : ℝ) + 2)) Filter.atTop (𝓝 ρ) := by
    have hden :
        Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)) Filter.atTop Filter.atTop := by
      simpa [add_assoc, add_left_comm, add_comm] using
        Filter.atTop.tendsto_atTop_add_const_right (2 : ℝ) tendsto_natCast_atTop_atTop
    have htail :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero.comp hden)
    have hfrac :
        Filter.Tendsto
          (fun n : ℕ ↦ ((n : ℝ) + 1) / ((n : ℝ) + 2))
          Filter.atTop
          (𝓝 1) := by
      have hEq :
          (fun n : ℕ ↦ ((n : ℝ) + 1) / ((n : ℝ) + 2)) =
            fun n : ℕ ↦ 1 - (1 : ℝ) / ((n : ℝ) + 2) := by
        funext n
        have hn2_ne : (n : ℝ) + 2 ≠ 0 := by positivity
        field_simp [hn2_ne]
        ring
      rw [hEq]
      simpa using tendsto_const_nhds.sub htail
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hfrac.const_mul ρ : Filter.Tendsto
        (fun n : ℕ ↦ ρ * (((n : ℝ) + 1) / ((n : ℝ) + 2))) Filter.atTop (𝓝 (ρ * 1)))
  by_cases h1 : d = 1
  · have hden :
        Filter.Tendsto
          (fun n : ℕ ↦ R - ρ * (n + 1) / (n + 2))
          Filter.atTop
          (𝓝 (R - ρ)) :=
      tendsto_const_nhds.sub hρApprox
      have hreal :
          Filter.Tendsto
            (fun n : ℕ ↦ centeredAnnulusProfile (d := d) (ρ * (n + 1) / (n + 2)) R (x - y))
            Filter.atTop
            (𝓝 ((R - dist x y) / (R - ρ))) := by
        simpa [centeredAnnulusProfile, h1, hnorm] using
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (R - dist x y : ℝ)) Filter.atTop
          (𝓝 (R - dist x y))).div hden
            (sub_ne_zero.mpr (ne_of_gt hρR).symm)
    simpa [centeredAnnulusProfile, h1, hnorm] using hreal
  · by_cases h2 : d = 2
    · have hlog :
          Filter.Tendsto
            (fun n : ℕ ↦ Real.log (ρ * (n + 1) / (n + 2)))
            Filter.atTop
            (𝓝 (Real.log ρ)) := by
        exact (Real.continuousAt_log hr.ne').tendsto.comp hρApprox
      have hden :
          Filter.Tendsto
            (fun n : ℕ ↦ Real.log R - Real.log (ρ * (n + 1) / (n + 2)))
            Filter.atTop
            (𝓝 (Real.log R - Real.log ρ)) :=
        tendsto_const_nhds.sub hlog
      have hreal :
          Filter.Tendsto
            (fun n : ℕ ↦ centeredAnnulusProfile (d := d) (ρ * (n + 1) / (n + 2)) R (x - y))
            Filter.atTop
            (𝓝 ((Real.log R - Real.log (dist x y)) / (Real.log R - Real.log ρ))) := by
        have hlog_denom_ne : Real.log R - Real.log ρ ≠ 0 := by
          have hlog_lt : Real.log ρ < Real.log R := by
            apply Real.strictMonoOn_log
            · exact hr
            · linarith [hr, hρR]
          exact sub_ne_zero.mpr (ne_of_gt hlog_lt).symm
        simpa [centeredAnnulusProfile, h2, hnorm] using
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ ↦ (Real.log R - Real.log (dist x y) : ℝ))
              Filter.atTop (𝓝 (Real.log R - Real.log (dist x y)))).div hden hlog_denom_ne
      simpa [centeredAnnulusProfile, h1, h2, hnorm] using hreal
    · have hdgt : 2 < d := by
        have hd0 : d ≠ 0 := ne_zero_of_radius_lt_dist (d := d) x y hr hρx
        omega
      have hratio_lt : ρ / R < 1 := by
        have hRpos : 0 < R := lt_trans hr hρR
        exact (div_lt_one hRpos).2 hρR
      have hratio_nonneg : 0 ≤ ρ / R := div_nonneg hr.le (le_of_lt (lt_trans hr hρR))
      have hk_pos : 0 < d - 2 := by omega
      have hpow_lt_one : (ρ / R) ^ (d - 2) < 1 :=
        pow_lt_one₀ hratio_nonneg hratio_lt hk_pos.ne'
      have hden_ne : 1 - (ρ / R) ^ (d - 2) ≠ 0 :=
        sub_ne_zero.mpr (ne_of_lt hpow_lt_one).symm
      have htoDist :
          Filter.Tendsto
            (fun n : ℕ ↦ (ρ * (n + 1) / (n + 2) : ℝ) / dist x y)
            Filter.atTop
            (𝓝 (ρ / dist x y)) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (tendsto_const_nhds.mul hρApprox :
            Filter.Tendsto
              (fun n : ℕ ↦ (1 / dist x y : ℝ) * (ρ * ((n : ℝ) + 1) / ((n : ℝ) + 2)))
              Filter.atTop
              (𝓝 ((1 / dist x y : ℝ) * ρ)))
      have htoR :
          Filter.Tendsto
            (fun n : ℕ ↦ (ρ * (n + 1) / (n + 2) : ℝ) / R)
            Filter.atTop
            (𝓝 (ρ / R)) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (tendsto_const_nhds.mul hρApprox :
            Filter.Tendsto
              (fun n : ℕ ↦ (1 / R : ℝ) * (ρ * ((n : ℝ) + 1) / ((n : ℝ) + 2)))
              Filter.atTop
              (𝓝 ((1 / R : ℝ) * ρ)))
      have hpowDist :
          Filter.Tendsto
            (fun n : ℕ ↦ ((ρ * (n + 1) / (n + 2) : ℝ) / dist x y) ^ (d - 2))
            Filter.atTop
            (𝓝 ((ρ / dist x y) ^ (d - 2))) :=
        (continuous_pow (d - 2)).continuousAt.tendsto.comp htoDist
      have hpowR :
          Filter.Tendsto
            (fun n : ℕ ↦ ((ρ * (n + 1) / (n + 2) : ℝ) / R) ^ (d - 2))
            Filter.atTop
            (𝓝 ((ρ / R) ^ (d - 2))) :=
        (continuous_pow (d - 2)).continuousAt.tendsto.comp htoR
        have hreal :
            Filter.Tendsto
              (fun n : ℕ ↦ centeredAnnulusProfile (d := d) (ρ * (n + 1) / (n + 2)) R (x - y))
              Filter.atTop
              (𝓝 ((((ρ / dist x y) ^ (d - 2)) - (ρ / R) ^ (d - 2)) /
                (1 - (ρ / R) ^ (d - 2)))) := by
        have hnum :
            Filter.Tendsto
              (fun n : ℕ ↦
                (((ρ * (n + 1) / (n + 2) : ℝ) / dist x y) ^ (d - 2)) -
                  (((ρ * (n + 1) / (n + 2) : ℝ) / R) ^ (d - 2)))
              Filter.atTop
              (𝓝 (((ρ / dist x y) ^ (d - 2)) - (ρ / R) ^ (d - 2))) :=
          hpowDist.sub hpowR
        have hden :
            Filter.Tendsto
              (fun n : ℕ ↦ 1 - (((ρ * (n + 1) / (n + 2) : ℝ) / R) ^ (d - 2)))
              Filter.atTop
              (𝓝 (1 - (ρ / R) ^ (d - 2))) :=
          tendsto_const_nhds.sub hpowR
        simpa [centeredAnnulusProfile, h1, h2, hnorm] using hnum.div hden hden_ne
      simpa [centeredAnnulusProfile, h1, h2, hnorm, hden_ne] using hreal

/-- Helper for Theorem 25.40: after replacing the wrong same-radius event by the closed-ball
formula, the fixed-outer open-ball probability follows from the monotone inner-radius union. -/
private theorem annulusInnerExitProbability_eq_profile
    (μ : ProbabilityMeasure Ω) (W : VectorProcess) (x y : State)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    {ρ R : ℝ} (hr : 0 < ρ) (hρx : ρ < dist x y) (hR : dist x y < R) :
    (μ : Measure Ω) {ω | (τ_[W, Metric.ball y ρ]) ω < hittingAfter W (Metric.ball y R)ᶜ 0 ω} =
      ENNReal.ofReal (centeredAnnulusProfile (d := d) ρ R (x - y)) := by
  let E : Set Ω := {ω | (τ_[W, Metric.ball y ρ]) ω < hittingAfter W (Metric.ball y R)ᶜ 0 ω}
  let F : ℕ → Set Ω := fun n ↦
    {ω |
      hittingAfter W (Metric.closedBall y (ρ * (n + 1) / (n + 2))) 0 ω <
        hittingAfter W (Metric.ball y R)ᶜ 0 ω}
  have hContAe :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous (fun t : NNReal ↦ W t ω) :=
    brownianVectorStartedAt_aeContinuous hW
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  have hEventEq : E =ᵐ[(μ : Measure Ω)] ⋃ n : ℕ, F n := by
    filter_upwards [hContAe, hStartAe] with ω hωCont hω0
    apply propext
    simpa [E, F, Set.mem_iUnion] using
      openBallBeforeOuter_iff_exists_closedBallBeforeOuterApprox
        (W := W) (ω := ω) (x := x) (y := y) (ρ := ρ) (R := R) hωCont hω0 hr hρx
  have hF_mono : Monotone F := by
    intro n m hnm
    intro ω hω
    dsimp [F] at hω ⊢
    have hfrac :
        ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
      have hn2_pos : 0 < (n : ℝ) + 2 := by positivity
      have hm2_pos : 0 < (m : ℝ) + 2 := by positivity
      have hcross :
          ((n : ℝ) + 1) * ((m : ℝ) + 2) ≤ ((m : ℝ) + 1) * ((n : ℝ) + 2) := by
        have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
        nlinarith
      exact (div_le_div_iff₀ hn2_pos hm2_pos).2 hcross
    have hradius :
        ρ * (n + 1) / (n + 2) ≤ ρ * (m + 1) / (m + 2) := by
      nlinarith [hfrac, hr]
    exact lt_of_lt_of_le hω
      (hittingAfter_anti W (0 : NNReal) (Metric.closedBall_subset_closedBall hradius) ω)
  have hMeasureUnion :
      (μ : Measure Ω) (⋃ n : ℕ, F n) = ⨆ n : ℕ, (μ : Measure Ω) (F n) :=
    hF_mono.measure_iUnion
  have hMeasureSeq :
      (fun n : ℕ ↦ (μ : Measure Ω) (F n)) =
        fun n : ℕ ↦
          ENNReal.ofReal
            (centeredAnnulusProfile (d := d) (ρ * (n + 1) / (n + 2)) R (x - y)) := by
    funext n
    have hρn_pos : 0 < ρ * (n + 1) / (n + 2) := by positivity
    have hρn_lt_ρ : ρ * (n + 1) / (n + 2) < ρ := by
      have hn2_pos : 0 < (n : ℝ) + 2 := by positivity
      have hfrac_lt_one : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
        exact (div_lt_iff₀ hn2_pos).2 (by linarith)
      have hmul_lt :
          ρ * (((n : ℝ) + 1) / ((n : ℝ) + 2)) < ρ * 1 := by
        exact mul_lt_mul_of_pos_left hfrac_lt_one hr
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul_lt
    exact
      annulusClosedBallBeforeOuter_probability_eq_profile
        (d := d) μ W x y hW hρn_pos (lt_trans hρn_lt_ρ hρx) hR
  have hMeasureSeq_mono : Monotone (fun n : ℕ ↦ (μ : Measure Ω) (F n)) := by
    intro n m hnm
    exact measure_mono (hF_mono hnm)
  have hMeasureSeq_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ (μ : Measure Ω) (F n))
        Filter.atTop
        (𝓝 (ENNReal.ofReal (centeredAnnulusProfile (d := d) ρ R (x - y)))) := by
    rw [hMeasureSeq]
    exact ENNReal.tendsto_ofReal <|
      centeredAnnulusProfile_tendsto_innerRadius_approximants (d := d) x y hr hρx hR
  -- Proof comment: the closed-ball probabilities form an increasing exhaustion of the open-ball
  -- event, and the explicit annulus profile is continuous along the chosen inner-radius
  -- approximants.
  calc
    (μ : Measure Ω) E = (μ : Measure Ω) (⋃ n : ℕ, F n) := by
      exact measure_congr hEventEq
    _ = ⨆ n : ℕ, (μ : Measure Ω) (F n) := hMeasureUnion
    _ = ENNReal.ofReal (centeredAnnulusProfile (d := d) ρ R (x - y)) := by
      exact iSup_eq_of_tendsto hMeasureSeq_mono hMeasureSeq_tendsto

-- Proof sketch: translate the ball center to `0`, identify the event that the Brownian path
-- started from `x` enters `Metric.ball y r` with finiteness of the positive-time hitting time
-- `τ_[W, Metric.ball y r]`, apply Theorem 25.38 to the concentric annulus between radii `r` and
-- `R`, and then let `R → ∞`.
/-- Theorem 25.40: for `r > 0` and points `x y : State` with `r < dist x y`, the probability that
the Brownian path started from `x` ever enters the open ball `Metric.ball y r`, equivalently that
the positive-time hitting time `τ_[W, Metric.ball y r]` is finite, is `1` in dimensions `d ≤ 2`
and `(r / dist x y)^(d - 2)` in dimensions `d > 2`. -/
theorem brownian_hits_ball_probability
    (μ : ProbabilityMeasure Ω) (W : VectorProcess) (x : State)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (r : ℝ) (hr : 0 < r) (y : State) (hxy : r < dist x y) :
    (μ : Measure Ω) {ω | (τ_[W, Metric.ball y r]) ω < ⊤} =
      if d ≤ 2 then 1 else ENNReal.ofReal ((r / dist x y) ^ (d - 2)) := by
  have hhit :
      {ω | (τ_[W, Metric.ball y r]) ω < ⊤} =
        {ω | ∃ t : NNReal, 0 < t ∧ W t ω ∈ Metric.ball y r} :=
    strictPositiveHittingEvent_eq_exists_hit W (Metric.ball y r)
  have hcont : ∀ᵐ ω ∂(μ : Measure Ω), Continuous (fun t : NNReal ↦ W t ω) :=
    brownianVectorStartedAt_aeContinuous hW
  have hd0 : d ≠ 0 := ne_zero_of_radius_lt_dist (d := d) x y hr hxy
  letI : NeZero d := ⟨hd0⟩
  let W0 : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hW0 : IsStandardBrownianMotionVector (μ : Measure Ω) W0 :=
    brownianVectorStartedAt_zeroPatched_isStandard hW
  have hTranslated :
      ∀ z : State, IsBrownianMotionVectorStartedAt (μ : Measure Ω) (fun t ω ↦ z + W0 t ω) z := by
    intro z
    exact translatedStandardBrownianVectorStartedAt hW0 z
  -- Proof comment: the verified prefix rewrites the event as an actual positive hit, records the
  -- almost-sure path continuity needed for the monotone union over outer radii, removes the
  -- degenerate `d = 0` branch, upgrades the fixed-start process to the standard recentered
  -- process `W0`, and then rebuilds the same-sample-space Brownian family `z + W0` needed for
  -- the Theorem 25.38 specialization.
  -- Route correction: the remaining gap is no longer the Brownian-family transport. What still
  -- has to be proved is the harmonic/continuous package for `centeredAnnulusProfile` together with
  -- the pathwise union rewrite from open-ball hitting to inner-before-outer annulus exit events.
  -- The boundary normalization layer is now available from
  -- `centeredAnnulusProfile_boundaryIndicator`, and the Theorem 25.38 specialization surface is
  -- already available from `existsMeasurableFrontierExitValue_ofContinuousPaths` together with
  -- `isCompact_closure_concentricAnnulus`.
  let E : ℕ → Set Ω := fun n ↦
    {ω | (τ_[W, Metric.ball y r]) ω <
        hittingAfter W (Metric.ball y (dist x y + n + 1))ᶜ 0 ω}
  have hAE :
      {ω | (τ_[W, Metric.ball y r]) ω < ⊤} =ᵐ[(μ : Measure Ω)] ⋃ n : ℕ, E n := by
    trans {ω | ∃ t : NNReal, 0 < t ∧ W t ω ∈ Metric.ball y r}
    · exact Filter.EventuallyEq.of_eq hhit
    · simpa [E] using ae_hitBallEvent_eq_iUnion_annulusExitEvents μ W x y hW r
  have hE_mono : Monotone E := by
    intro n m hnm
    intro ω hω
    dsimp [E] at hω ⊢
    have hRadius : dist x y + n + 1 ≤ dist x y + m + 1 := by
      have hnm_real : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith
    have hBall :
        Metric.ball y (dist x y + n + 1) ⊆ Metric.ball y (dist x y + m + 1) :=
      Metric.ball_subset_ball hRadius
    have hOuter :
        (Metric.ball y (dist x y + m + 1))ᶜ ⊆ (Metric.ball y (dist x y + n + 1))ᶜ :=
      Set.compl_subset_compl.mpr hBall
    exact lt_of_lt_of_le hω (hittingAfter_anti W (0 : NNReal) hOuter ω)
  have hMeasureUnion :
      (μ : Measure Ω) (⋃ n : ℕ, E n) = ⨆ n : ℕ, (μ : Measure Ω) (E n) :=
    hE_mono.measure_iUnion
  have hMeasureSeq :
      (fun n : ℕ ↦ (μ : Measure Ω) (E n)) =
        fun n : ℕ ↦
          ENNReal.ofReal
            (centeredAnnulusProfile (d := d) r (dist x y + n + 1) (x - y)) := by
    funext n
    exact
      annulusInnerExitProbability_eq_profile μ W x y hW hr hxy (by
        have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        linarith)
  have hMeasureSeq_mono : Monotone (fun n : ℕ ↦ (μ : Measure Ω) (E n)) := by
    intro n m hnm
    exact measure_mono (hE_mono hnm)
  have hMeasureSeq_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ (μ : Measure Ω) (E n))
        Filter.atTop
        (𝓝 (if d ≤ 2 then 1 else ENNReal.ofReal ((r / dist x y) ^ (d - 2)))) := by
    rw [hMeasureSeq]
    exact annulusProfile_tendsto_target_along_nat (d := d) x y r hr hxy
  calc
    (μ : Measure Ω) {ω | (τ_[W, Metric.ball y r]) ω < ⊤} =
        (μ : Measure Ω) (⋃ n : ℕ, E n) := by
          exact measure_congr hAE
    _ = ⨆ n : ℕ, (μ : Measure Ω) (E n) := hMeasureUnion
    _ = if d ≤ 2 then 1 else ENNReal.ofReal ((r / dist x y) ^ (d - 2)) := by
          exact iSup_eq_of_tendsto hMeasureSeq_mono hMeasureSeq_tendsto

end ProbabilityTheory
