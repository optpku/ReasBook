/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

attribute [local instance] Classical.propDecidable

/-- Helper for Exercise 21.2.6: covariance is unchanged by almost-everywhere replacement of either
argument. -/
private lemma covariance_congr_ae {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Proof comment: rewrite both expectations by almost-sure equality and then identify the
  -- covariance integrands pointwise.
  have hIntX : μ[X] = μ[X'] := integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := integral_congr_ae hY
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- The first time at which the path of `B` meets the affine boundary `t ↦ a * t + b`. -/
def brownianAffineBoundaryHittingTime (B : NNReal → Ω → ℝ) (a b : ℝ) : Ω → ENNReal :=
  hittingAfter (fun t ω ↦ B t ω - a * (t : ℝ)) ({b} : Set ℝ) (0 : NNReal)

-- Proof sketch: `brownianAffineBoundaryHittingTime` is the canonical hitting time `hittingAfter`
-- for the drifted process `t ↦ B_t - a t` into the singleton level `{b}`.
omit [MeasurableSpace Ω] in
/-- Expanding `brownianAffineBoundaryHittingTime` gives the canonical owner `hittingAfter` for the
drifted process `t ↦ B_t - a t` at the level `b`. -/
theorem brownianAffineBoundaryHittingTime_eq_hittingAfter
    (B : NNReal → Ω → ℝ) (a b : ℝ) :
    brownianAffineBoundaryHittingTime B a b =
      hittingAfter (fun t ω ↦ B t ω - a * (t : ℝ)) ({b} : Set ℝ) (0 : NNReal) := by
  rfl

/-- The samplewise factor `e^{-λτ}` attached to the affine-boundary hitting time `τ`, taken to be
`0` on the event that the boundary is never hit. -/
def brownianAffineBoundaryHittingTimeLaplaceWeight
    (B : NNReal → Ω → ℝ) (a b lam : ℝ) : Ω → ℝ :=
  fun ω ↦
    Set.indicator
      {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
      (fun ω ↦ Real.exp (-lam * (brownianAffineBoundaryHittingTime B a b ω).toReal)) ω

-- Proof sketch: unfold `brownianAffineBoundaryHittingTimeLaplaceWeight`.
omit [MeasurableSpace Ω] in
/-- The affine-boundary Laplace weight is the exponential factor on the finite-hitting event and
vanishes otherwise. -/
theorem brownianAffineBoundaryHittingTimeLaplaceWeight_def
    (B : NNReal → Ω → ℝ) (a b lam : ℝ) :
    brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam =
      fun ω ↦
        Set.indicator
          {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
          (fun ω ↦ Real.exp (-lam * (brownianAffineBoundaryHittingTime B a b ω).toReal)) ω := by
  rfl

section BrownianMotionExercise

variable {μ : Measure Ω}
variable {B : NNReal → Ω → ℝ}

/-- Helper for Exercise 21.2.6: the quadratic root `θ = a + √(a² + 2 λ)` satisfies
`θ² / 2 - a * θ = λ`. -/
lemma affineBoundaryTheta_quadratic {a lam : ℝ} (hlam : 0 ≤ lam) :
    let θ := a + Real.sqrt (a ^ 2 + 2 * lam)
    θ ^ 2 / 2 - a * θ = lam := by
  -- Expand the quadratic expression and then evaluate the square root term.
  dsimp
  have hs : 0 ≤ a ^ 2 + 2 * lam := by
    nlinarith [sq_nonneg a, hlam]
  calc
    (a + Real.sqrt (a ^ 2 + 2 * lam)) ^ 2 / 2 - a * (a + Real.sqrt (a ^ 2 + 2 * lam))
        = ((Real.sqrt (a ^ 2 + 2 * lam)) ^ 2 - a ^ 2) / 2 := by
            ring
    _ = ((a ^ 2 + 2 * lam) - a ^ 2) / 2 := by
          rw [Real.sq_sqrt hs]
    _ = lam := by
          ring

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 21.2.6: at `λ = 0`, the affine-boundary Laplace weight is the indicator
of the finite-hit event. -/
lemma brownianAffineBoundaryHittingTimeLaplaceWeight_zero
    (B : NNReal → Ω → ℝ) (a b : ℝ) :
    brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 =
      Set.indicator
        {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
        (fun _ ↦ (1 : ℝ)) := by
  -- At parameter `λ = 0`, the exponential factor collapses to the constant `1`.
  funext ω
  simp [brownianAffineBoundaryHittingTimeLaplaceWeight_def]

/-- Helper for Exercise 21.2.6: the zero-parameter closed form simplifies to
`min 1 (exp (-2 b a))`. -/
lemma brownianAffineBoundaryHittingTime_zeroParameter_closedForm
    {a b : ℝ} (hb : 0 < b) :
    Real.exp (-b * a - b * Real.sqrt (a ^ 2)) = min 1 (Real.exp (-2 * b * a)) := by
  -- Split on the sign of `a`, which determines the absolute value in `√(a²) = |a|`.
  rw [Real.sqrt_sq_eq_abs]
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    have hle : Real.exp (-2 * b * a) ≤ 1 := by
      have hnonpos : -2 * b * a ≤ 0 := by
        nlinarith
      simpa using Real.exp_le_one_iff.mpr hnonpos
    rw [min_eq_right hle]
    ring_nf
  · have ha' : a < 0 := lt_of_not_ge ha
    rw [abs_of_neg ha']
    have hle : 1 ≤ Real.exp (-2 * b * a) := by
      have hnonneg : 0 ≤ -2 * b * a := by
        nlinarith
      simpa using Real.one_le_exp_iff.mpr hnonneg
    rw [min_eq_left hle]
    ring_nf
    simp

/-- Helper for Exercise 21.2.6: at a finite sample point, stopping the deterministic time process
at `τ` recovers `ENNReal.toReal (τ ω)`. -/
private lemma stoppedValue_ennrealTimeProcess_eq_toReal
    {τ : Ω → ENNReal} {ω : Ω} (hτ : τ ω ≠ ⊤) :
    stoppedValue (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) τ ω = ENNReal.toReal (τ ω) := by
  -- Proof comment: on the finite branch, `untopA` exposes the underlying `NNReal` time and the
  -- deterministic time process evaluates to its real coercion.
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hτ
  have ht' : τ ω = (t : ENNReal) := by
    simpa using ht.symm
  rw [stoppedValue, ht']
  change (((t : ENNReal).untopA : NNReal) : ℝ) = (t : ℝ)
  rfl

/-- Helper for Exercise 21.2.6: stopping at `τ ∧ t` is the same as stopping at `τ` on the branch
`{τ ≤ t}` and at the deterministic time `t` otherwise. -/
private lemma stoppedValue_minConst_eq_if
    {X : NNReal → Ω → ℝ} {τ : Ω → ENNReal} {t : NNReal} {ω : Ω} :
    stoppedValue X (fun ω' ↦ min (τ ω') (t : ENNReal)) ω =
      if τ ω ≤ (t : ENNReal) then stoppedValue X τ ω else X t ω := by
  by_cases hτt : τ ω ≤ (t : ENNReal)
  · -- Proof comment: on the hit branch, the minimum keeps the original stopping time `τ`.
    have hmin_eq : min (τ ω) (t : ENNReal) = τ ω := min_eq_left hτt
    have hidx : (min (τ ω) (t : ENNReal)).untopA = (τ ω).untopA := by
      rw [hmin_eq]
    rw [if_pos hτt, stoppedValue]
    exact congrArg (fun k ↦ X k ω) hidx
  · -- Proof comment: before the hit, the minimum collapses to the deterministic horizon `t`.
    have hmin_eq : min (τ ω) (t : ENNReal) = (t : ENNReal) :=
      min_eq_right (le_of_not_ge hτt)
    have hidx : (min (τ ω) (t : ENNReal)).untopA = t := by
      rw [hmin_eq]
      rfl
    rw [if_neg hτt, stoppedValue]
    exact congrArg (fun k ↦ X k ω) hidx

/-- Helper for Exercise 21.2.6: clipping a stopping time by a deterministic horizon rewrites its
stopped value as the corresponding stopped-process slice. -/
private lemma stoppedValue_min_const_eq_stoppedProcess
    {M : NNReal → Ω → ℝ} {τ : Ω → ENNReal} {t : NNReal} :
    stoppedValue M (fun ω ↦ min (τ ω) (t : ENNReal)) =
      stoppedProcess M τ t := by
  ext ω
  -- Proof comment: both sides evaluate `M` at the same clipped time, up to commutativity of
  -- `min`.
  change M (min (τ ω) (t : ENNReal)).untopA ω =
    M (min (t : ENNReal) (τ ω)).untopA ω
  rw [min_comm]

/-- Helper for Exercise 21.2.6: dyadic ceiling approximation of a finite nonnegative random time.
-/
private def dyadicCeilApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

/-- Helper for Exercise 21.2.6: the dyadic ceiling event `{σⁿ ≤ t}` rewrites as the original
stopping event at the latest dyadic mesh point not exceeding `t`. -/
private lemma dyadicCeilApprox_event_le_eq
    (n : ℕ) (τ : Ω → NNReal) (t : NNReal) :
    {ω | (dyadicCeilApprox n τ ω : ENNReal) ≤ t} =
      {ω | (τ ω : ENNReal) ≤
        ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) /
          ((2 : NNReal) ^ n))} := by
  ext ω
  have hbody :
      dyadicCeilApprox n τ ω ≤ t ↔
        τ ω ≤
          ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) /
            ((2 : NNReal) ^ n)) := by
    let c : NNReal := (2 : NNReal) ^ n
    have hc_pos : 0 < c := by
      -- Proof comment: the dyadic denominator is strictly positive.
      dsimp [c]
      positivity
    have hDiv :
        dyadicCeilApprox n τ ω ≤ t ↔
          (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t := by
      -- Proof comment: multiplying by the positive dyadic scale clears the denominator.
      dsimp [dyadicCeilApprox, c]
      rw [div_le_iff₀ hc_pos]
      simpa [c, mul_comm]
    have hCeilFloor :
        (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t ↔
          Nat.ceil (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
      constructor
      · intro h
        have hreal :
            ((Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℕ) : ℝ) ≤ (((c * t : NNReal) : ℝ)) := by
          exact_mod_cast h
        exact Nat.le_floor hreal
      · intro h
        have hnn :
            (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤
              (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) := by
          exact_mod_cast h
        exact le_trans hnn <| by
          have hfloorReal :
              (((Nat.floor (((c * t : NNReal) : ℝ)) : ℕ) : ℝ)) ≤ (((c * t : NNReal) : ℝ)) := by
            exact Nat.floor_le (show 0 ≤ (((c * t : NNReal) : ℝ)) by positivity)
          exact_mod_cast hfloorReal
    have hFloorDiv :
        Nat.ceil (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) ↔
          τ ω ≤ (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) / c := by
      constructor
      · intro h
        have hreal : (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
          exact Nat.ceil_le.mp h
        have hnn' : c * τ ω ≤ (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) := by
          exact_mod_cast hreal
        exact (le_div_iff₀ hc_pos).2 (by simpa [mul_comm] using hnn')
      · intro h
        have hnn' : c * τ ω ≤ (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) := by
          have hmul := (le_div_iff₀ hc_pos).1 h
          simpa [mul_comm] using hmul
        have hreal : (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
          exact_mod_cast hnn'
        exact Nat.ceil_le.2 hreal
    -- Proof comment: the dyadic ceiling only checks whether `τ` already lies below the previous
    -- mesh point.
    exact hDiv.trans (hCeilFloor.trans hFloorDiv)
  exact_mod_cast hbody

/-- Helper for Exercise 21.2.6: dyadic ceiling approximations of `NNReal`-valued stopping times
are still stopping times. -/
private lemma dyadicCeilApprox_isStoppingTime
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›} {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal) := by
  intro t
  let q : NNReal :=
    ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) / ((2 : NNReal) ^ n))
  have hpow_pos : 0 < (2 : NNReal) ^ n := by
    -- Proof comment: the dyadic scale is positive, so division preserves inequalities.
    positivity
  have hq_le_t : q ≤ t := by
    -- Proof comment: the dyadic predecessor of `t` never exceeds `t`.
    dsimp [q]
    refine (div_le_iff₀ hpow_pos).2 ?_
    have hfloor :
        ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal)) ≤
          ((2 : NNReal) ^ n) * t := by
      have hfloorReal :
          (((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ)) : ℕ) : ℝ) ≤
            ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) := by
        exact Nat.floor_le (show 0 ≤ ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) by positivity)
      exact_mod_cast hfloorReal
    simpa [mul_comm] using hfloor
  -- Proof comment: rewrite the dyadic event through the original stopping event and transport it
  -- along filtration monotonicity.
  change MeasurableSet[ℱ t] {ω | (dyadicCeilApprox n τ ω : ENNReal) ≤ t}
  rw [dyadicCeilApprox_event_le_eq (n := n) (τ := τ) (t := t)]
  simpa [q] using (ℱ.mono hq_le_t _ (hτ.measurableSet_le q))

/-- Helper for Exercise 21.2.6: every dyadic ceiling approximation has countable range. -/
private lemma dyadicCeilApprox_countableRange
    (n : ℕ) (τ : Ω → NNReal) :
    (Set.range fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal)).Countable := by
  refine
    ((Set.countable_range
      fun k : ℕ ↦ ((((k : NNReal) / ((2 : NNReal) ^ n)) : NNReal) : ENNReal))).mono ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ), ?_⟩
  -- Proof comment: every dyadic ceiling value lies on the mesh `2⁻ⁿ ℕ`.
  simp [dyadicCeilApprox]

/-- Helper for Exercise 21.2.6: the dyadic ceilings converge pointwise back to the original
finite time. -/
private lemma dyadicCeilApprox_tendsto
    (ρ : Ω → NNReal) :
    ∀ ω, Tendsto (fun m ↦ dyadicCeilApprox m ρ ω) atTop (nhds (ρ ω)) := by
  intro ω
  have hEq :
      (fun m ↦ dyadicCeilApprox m ρ ω) =
        fun m ↦ (((Nat.ceil ((ρ ω : ℝ) * (2 : ℝ) ^ m) : ℕ) : NNReal) / (2 : NNReal) ^ m) := by
    funext m
    unfold dyadicCeilApprox
    congr 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (congrArg (fun x : NNReal ↦ (x : ℝ)) (mul_comm ((2 : NNReal) ^ m) (ρ ω)))
  -- Proof comment: this is the standard dyadic ceiling convergence `⌈ρ 2^m⌉ / 2^m → ρ`.
  rw [hEq]
  refine (NNReal.tendsto_coe).mp ?_
  simpa using
    (tendsto_nat_ceil_mul_div_atTop (a := (ρ ω : ℝ))
      (show 0 ≤ (ρ ω : ℝ) from (ρ ω).2)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Exercise 21.2.6: continuity of a sample path transports convergence of finite
times to convergence of the associated stopped values. -/
private lemma stoppedValue_tendsto_of_timeApprox
    {M : NNReal → Ω → ℝ}
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    {ρm : ℕ → Ω → NNReal} {ρ : Ω → NNReal}
    (hρ : ∀ ω, Tendsto (fun m ↦ ρm m ω) atTop (nhds (ρ ω))) :
    ∀ ω,
      Tendsto
        (fun m ↦ stoppedValue M (fun ω' ↦ ((ρm m ω' : NNReal) : ENNReal)) ω)
        atTop
        (nhds (stoppedValue M (fun ω' ↦ ((ρ ω' : NNReal) : ENNReal)) ω)) := by
  intro ω
  -- Proof comment: for finite stopping times, `stoppedValue` is just evaluation at that time.
  simpa [stoppedValue] using ((hM_cont ω).tendsto (ρ ω)).comp (hρ ω)

/-- Helper for Exercise 21.2.6: `L¹` convergence on the ambient measure controls integrals over
every restricted measure. -/
private lemma tendsto_restrictedIntegral_of_tendsto_L1
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {s : Set Ω}
    (hg : Integrable g μ) (hfi : ∀ n, Integrable (f n) μ)
    (hL1 : Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ ω in s, f n ω ∂μ) atTop (nhds (∫ ω in s, g ω ∂μ)) := by
  have hL1_restrict :
      Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 (μ.restrict s)) atTop (nhds 0) := by
    -- Proof comment: restricting the measure can only decrease the `L¹` seminorm.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 ?_ ?_
    · intro n
      exact bot_le
    · intro n
      exact eLpNorm_mono_measure (fun ω ↦ f n ω - g ω) Measure.restrict_le_self
  -- Proof comment: continuity of the integral on `L¹` now gives convergence of the restricted
  -- integrals.
  exact tendsto_integral_of_L1' g hg.restrict
    (Filter.Eventually.of_forall fun n ↦ (hfi n).restrict) hL1_restrict

/-- Helper for Exercise 21.2.6: dyadic ceiling approximations of a finite stopping time give an
integrable exact stopped slice together with `L¹` convergence of the dyadic slices. -/
private lemma stoppedProcess_dyadicCeilApprox_limitData
    [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (r : NNReal) :
    Integrable (stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r) μ ∧
      Tendsto
        (fun m ↦
          eLpNorm
            (fun ω ↦
              stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω -
                stoppedProcess M (fun ω' ↦ (σ ω' : ENNReal)) r ω)
            1 μ)
        atTop (nhds 0) := by
  let τm : ℕ → Ω → ENNReal := fun m ω ↦
    min ((dyadicCeilApprox m σ ω : NNReal) : ENNReal) (r : ENNReal)
  let τ : Ω → ENNReal := fun ω ↦ min ((σ ω : NNReal) : ENNReal) (r : ENNReal)
  have hτm_stop : ∀ m, IsStoppingTime ℱ (τm m) := by
    intro m
    exact (dyadicCeilApprox_isStoppingTime (ℱ := ℱ) hσ m).min_const r
  have hτm_le : ∀ m ω, τm m ω ≤ (r : ENNReal) := by
    intro m ω
    exact min_le_right _ _
  have hτm_count : ∀ m, (Set.range (τm m)).Countable := by
    intro m
    refine
      ((dyadicCeilApprox_countableRange m σ).image fun u : ENNReal ↦ min u (r : ENNReal)).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨(dyadicCeilApprox m σ ω : ENNReal), ⟨ω, rfl⟩, rfl⟩
  have hCond :
      ∀ m, stoppedValue M (τm m) =ᵐ[μ] μ[M r | (hτm_stop m).measurableSpace] := by
    intro m
    -- Proof comment: each clipped dyadic stop has countable range and stays below `r`, so the
    -- countable-range optional sampling theorem applies to it.
    exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hτm_stop m) (hτm_le m) (hτm_count m)
  have hUIcond :
      UniformIntegrable
        (fun m : ℕ ↦ μ[M r | (hτm_stop m).measurableSpace]) 1 μ :=
    (hM.integrable r).uniformIntegrable_condExp fun m ↦ (hτm_stop m).measurableSpace_le
  have hUIstopped : UniformIntegrable (fun m : ℕ ↦ stoppedValue M (τm m)) 1 μ :=
    hUIcond.ae_eq fun m ↦ (hCond m).symm
  have hApprox :
      ∀ ω, Tendsto (fun m ↦ min (dyadicCeilApprox m σ ω) r) atTop (nhds (min (σ ω) r)) := by
    intro ω
    -- Proof comment: the dyadic times converge pointwise to `σ(ω)`, and clipping by `r`
    -- preserves that limit.
    exact ((continuous_id.min continuous_const).tendsto (σ ω)).comp
      (dyadicCeilApprox_tendsto σ ω)
  have hAeTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m ↦ stoppedValue M (τm m) ω) atTop (nhds (stoppedValue M τ ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    -- Proof comment: continuity of the sample path turns convergence of the dyadic times into
    -- convergence of the corresponding stopped values.
    simpa [τm, τ] using
      stoppedValue_tendsto_of_timeApprox
        (M := M) hM_cont
        (ρm := fun m ω' ↦ min (dyadicCeilApprox m σ ω') r)
        (ρ := fun ω' ↦ min (σ ω') r) hApprox ω
  have hInt : Integrable (stoppedValue M τ) μ :=
    hUIstopped.integrable_of_ae_tendsto hAeTendsto
  have hL1 :
      Tendsto
        (fun m ↦ eLpNorm (fun ω ↦ stoppedValue M (τm m) ω - stoppedValue M τ ω) 1 μ)
        atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun m ↦ hUIstopped.aestronglyMeasurable m)
      (memLp_one_iff_integrable.2 hInt) hUIstopped.unifIntegrable hAeTendsto
  have hτ_eq :
      stoppedValue M τ = stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r := by
    simpa [τ] using
      (stoppedValue_min_const_eq_stoppedProcess
        (M := M) (τ := fun ω ↦ (σ ω : ENNReal)) (t := r))
  have hτm_eq :
      ∀ m, stoppedValue M (τm m) =
        stoppedProcess M (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) r := by
    intro m
    simpa [τm] using
      (stoppedValue_min_const_eq_stoppedProcess
        (M := M) (τ := fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) (t := r))
  constructor
  · -- Proof comment: the exact stopped slice is the integrable `L¹` limit of the dyadic slices.
    simpa [hτ_eq] using hInt
  · -- Proof comment: rewrite the `L¹` convergence back into the stopped-process normal form.
    simpa [hτ_eq, hτm_eq] using hL1

/-- Helper for Exercise 21.2.6: a continuous martingale preserves expectation at a clipped finite
stopping time. -/
private lemma expected_stoppedValue_min_const_eq_initial
    [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ)
    (r : NNReal) :
    ∫ ω, stoppedValue M (fun ω' ↦ min (τ ω') (r : ENNReal)) ω ∂μ =
      ∫ ω, M 0 ω ∂μ := by
  let σ : Ω → NNReal := fun ω ↦ ENNReal.toNNReal (min (τ ω) (r : ENNReal))
  have hσ_eq :
      (fun ω ↦ ((σ ω : NNReal) : ENNReal)) = fun ω ↦ min (τ ω) (r : ENNReal) := by
    funext ω
    simp [σ, ENNReal.coe_toNNReal, ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)]
  have hσ_stop : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal) := by
    rw [hσ_eq]
    exact hτ.min_const r
  have hInt :
      Integrable (stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r) μ :=
    (stoppedProcess_dyadicCeilApprox_limitData
      (μ := μ) (ℱ := ℱ) (M := M) hM hM_cont hσ_stop r).1
  have hL1 :
      Tendsto
        (fun m ↦
          eLpNorm
            (fun ω ↦
              stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω -
                stoppedProcess M (fun ω' ↦ (σ ω' : ENNReal)) r ω)
            1 μ)
        atTop (nhds 0) :=
    (stoppedProcess_dyadicCeilApprox_limitData
      (μ := μ) (ℱ := ℱ) (M := M) hM hM_cont hσ_stop r).2
  have hIntegralTendsto :
      Tendsto
        (fun m ↦ ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ)
        atTop
        (nhds (∫ ω, stoppedProcess M (fun ω' ↦ (σ ω' : ENNReal)) r ω ∂μ)) := by
    -- Proof comment: `L¹` convergence of the dyadic slices gives convergence of their
    -- expectations.
    exact tendsto_integral_of_L1' _ hInt
      (Filter.Eventually.of_forall fun m ↦ by
        have hσm :
            IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal) :=
          dyadicCeilApprox_isStoppingTime (ℱ := ℱ) hσ_stop m
        exact
          (stoppedProcess_dyadicCeilApprox_limitData
            (μ := μ) (ℱ := ℱ) (M := M) hM hM_cont hσm r).1)
      hL1
  have hIntegralEq :
      ∀ m,
        ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ =
          ∫ ω, M r ω ∂μ := by
    intro m
    let τm : Ω → ENNReal := fun ω ↦ min ((dyadicCeilApprox m σ ω : NNReal) : ENNReal) (r : ENNReal)
    have hτm_stop : IsStoppingTime ℱ τm := by
      exact (dyadicCeilApprox_isStoppingTime (ℱ := ℱ) hσ_stop m).min_const r
    have hτm_le : ∀ ω, τm ω ≤ (r : ENNReal) := by
      intro ω
      exact min_le_right _ _
    have hτm_count : (Set.range τm).Countable := by
      refine ((dyadicCeilApprox_countableRange m σ).image fun u : ENNReal ↦ min u (r : ENNReal)).mono ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨(dyadicCeilApprox m σ ω : ENNReal), ⟨ω, rfl⟩, rfl⟩
    have hCond :
        stoppedValue M τm =ᵐ[μ] μ[M r | hτm_stop.measurableSpace] :=
      hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτm_stop hτm_le hτm_count
    have hStoppedEq :
        stoppedValue M τm =
          stoppedProcess M (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) r := by
      simpa [τm] using
        (stoppedValue_min_const_eq_stoppedProcess
          (M := M) (τ := fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) (t := r))
    -- Proof comment: integrate the conditional expectation identity and then use the martingale
    -- expectation invariance between deterministic times `0` and `r`.
    calc
      ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ
          = ∫ ω, stoppedValue M τm ω ∂μ := by simp [hStoppedEq]
      _ = ∫ ω, μ[M r | hτm_stop.measurableSpace] ω ∂μ := integral_congr_ae hCond
      _ = ∫ ω, M r ω ∂μ := integral_condExp hτm_stop.measurableSpace_le
  have hConstEq : ∫ ω, stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r ω ∂μ = ∫ ω, M r ω ∂μ := by
    have hConstTendsto :
        Tendsto
          (fun m ↦ ∫ ω, stoppedProcess M (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω ∂μ)
          atTop
          (nhds (∫ ω, M r ω ∂μ)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.of_forall fun m ↦ (hIntegralEq m).symm
    exact tendsto_nhds_unique hIntegralTendsto hConstTendsto
  have hStoppedEq :
      stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r =
        stoppedValue M (fun ω' ↦ min (τ ω') (r : ENNReal)) := by
    ext ω
    have hσ_eqω :
        ((σ ω : NNReal) : ENNReal) = min (τ ω) (r : ENNReal) := by
      simpa [σ, ENNReal.coe_toNNReal,
        ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)]
    change M (min (r : ENNReal) ((σ ω : NNReal) : ENNReal)).untopA ω =
      M (min (τ ω) (r : ENNReal)).untopA ω
    have hmin : min (min (τ ω) (r : ENNReal)) (r : ENNReal) = min (τ ω) (r : ENNReal) := by
      rw [min_eq_left (min_le_right _ _)]
    rw [hσ_eqω, min_comm, hmin]
  calc
    ∫ ω, stoppedValue M (fun ω' ↦ min (τ ω') (r : ENNReal)) ω ∂μ
        = ∫ ω, stoppedProcess M (fun ω ↦ (σ ω : ENNReal)) r ω ∂μ := by
            simp [hStoppedEq]
    _ = ∫ ω, M r ω ∂μ := hConstEq
    _ = ∫ ω, M 0 ω ∂μ := by
          simpa [setIntegral_univ] using
            (hM.setIntegral_eq (show (0 : NNReal) ≤ r by exact zero_le _)
              (s := Set.univ) MeasurableSet.univ).symm

/-- Helper for Exercise 21.2.6: the affine-boundary hitting time is infinite exactly when the
drifted path never reaches the level `b`. -/
lemma brownianAffineBoundaryHittingTime_eq_top_iff
    {B : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω} :
    brownianAffineBoundaryHittingTime B a b ω = ⊤ ↔
      ∀ t : NNReal, B t ω - a * (t : ℝ) ≠ b := by
  -- Proof comment: `brownianAffineBoundaryHittingTime` is just `hittingAfter` for the drifted
  -- path, so the owner theorem specializes directly to singleton avoidance.
  simpa [brownianAffineBoundaryHittingTime_eq_hittingAfter, Set.mem_singleton_iff] using
    (hittingAfter_eq_top_iff
      (u := fun t ω ↦ B t ω - a * (t : ℝ))
      (s := ({b} : Set ℝ))
      (n := (0 : NNReal))
      (ω := ω))

/-- Helper for Exercise 21.2.6: finite affine-boundary hitting time is equivalent to an actual
sample-path hit of the drifted process at level `b`. -/
lemma brownianAffineBoundaryHittingTime_ne_top_iff_exists_eq
    {B : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω} :
    brownianAffineBoundaryHittingTime B a b ω ≠ ⊤ ↔
      ∃ t : NNReal, B t ω - a * (t : ℝ) = b := by
  -- Proof comment: negate the previous top-characterization and rewrite singleton membership as
  -- pointwise equality.
  constructor
  · intro hne
    by_contra hnot
    exact
      hne <|
        (brownianAffineBoundaryHittingTime_eq_top_iff (B := B) (a := a) (b := b) (ω := ω)).2
          (fun t ht ↦ hnot ⟨t, ht⟩)
  · rintro ⟨t, ht⟩ htop
    exact
      (brownianAffineBoundaryHittingTime_eq_top_iff (B := B) (a := a) (b := b) (ω := ω)).1 htop
        t ht

/-- Helper for Exercise 21.2.6: an explicit affine-boundary hit at time `t` bounds the hitting
time by `t`. -/
lemma brownianAffineBoundaryHittingTime_le_of_eq
    {B : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω} {t : NNReal}
    (ht : B t ω - a * (t : ℝ) = b) :
    brownianAffineBoundaryHittingTime B a b ω ≤ t := by
  -- Proof comment: once the drifted path equals `b` at time `t`, the canonical singleton hitting
  -- time cannot be larger than `t`.
  simpa [brownianAffineBoundaryHittingTime_eq_hittingAfter, Set.mem_singleton_iff, ht] using
    (hittingAfter_le_of_mem
      (u := fun s ω ↦ B s ω - a * (s : ℝ))
      (s := ({b} : Set ℝ))
      (n := (0 : NNReal))
      (ω := ω)
      (by simp)
      (by simpa [Set.mem_singleton_iff] using ht))

/-- Helper for Exercise 21.2.6: whenever the affine-boundary hitting time is finite, the drifted
path `t ↦ B t - a t` is exactly at level `b` at that hitting time. -/
lemma driftedBrownian_value_eq_boundary_at_hittingTime
    {a b : ℝ} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ))
    (hω : brownianAffineBoundaryHittingTime B a b ω < ⊤) :
    B (brownianAffineBoundaryHittingTime B a b ω).untopA ω -
      a * ((brownianAffineBoundaryHittingTime B a b ω).untopA : ℝ) = b := by
  classical
  let hitSet : Set NNReal := {t | B t ω - a * (t : ℝ) = b}
  have hτ : brownianAffineBoundaryHittingTime B a b ω ≠ ⊤ := ne_of_lt hω
  have hhit : ∃ t : NNReal, B t ω - a * (t : ℝ) = b :=
    (brownianAffineBoundaryHittingTime_ne_top_iff_exists_eq
      (B := B) (a := a) (b := b) (ω := ω)).1 hτ
  have hnonempty : hitSet.Nonempty := by
    rcases hhit with ⟨t, ht⟩
    exact ⟨t, ht⟩
  have hclosed : IsClosed hitSet := by
    -- Proof comment: the affine hit set is the preimage of the closed singleton `{b}` under the
    -- continuous drifted sample path.
    simpa [hitSet] using (isClosed_singleton : IsClosed ({b} : Set ℝ)).preimage hcont
  have hbddBelow : BddBelow hitSet := by
    refine ⟨0, ?_⟩
    intro t ht
    exact bot_le
  have hsInf_mem : sInf hitSet ∈ hitSet := hclosed.csInf_mem hnonempty hbddBelow
  have hτ_eq : (brownianAffineBoundaryHittingTime B a b ω).untopA = sInf hitSet := by
    -- Proof comment: once an actual hit exists, `hittingAfter` is the infimum of the affine hit
    -- set, and `untopA` removes the finite-time wrapper.
    rw [brownianAffineBoundaryHittingTime_eq_hittingAfter, hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ B i ω - a * (i : ℝ) ∈ ({b} : Set ℝ)} = hitSet by
            ext t
            simp [hitSet, Set.mem_singleton_iff]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hhit with ⟨t, ht⟩
      exact ⟨t, bot_le, by simpa [Set.mem_singleton_iff] using ht⟩
  simpa [hitSet, hτ_eq] using hsInf_mem

/-- Helper for Exercise 21.2.6: on a continuous drifted path, the event `{τ ≤ T}` is equivalent
to hitting the affine boundary at some deterministic time in `[0, T]`. -/
lemma brownianAffineBoundaryHittingTime_le_iff_exists_eq_of_continuous
    {a b : ℝ} {ω : Ω} (hcont : Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ)) {T : NNReal} :
    brownianAffineBoundaryHittingTime B a b ω ≤ T ↔
      ∃ s ∈ Set.Icc (0 : NNReal) T, B s ω - a * (s : ℝ) = b := by
  constructor
  · intro hτT
    have hτ_ne_top :
        brownianAffineBoundaryHittingTime B a b ω ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hτT
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hτ_ne_top
    have hτ_eq : brownianAffineBoundaryHittingTime B a b ω = (t : ENNReal) := by
      simpa using ht.symm
    refine ⟨t, ?_, ?_⟩
    constructor
    · simp
    · have hτT' : (t : ENNReal) ≤ T := by
        simpa [hτ_eq] using hτT
      exact_mod_cast hτT'
    · -- Proof comment: continuity upgrades the finite hitting time to an exact boundary hit.
      have hτ_lt : brownianAffineBoundaryHittingTime B a b ω < ⊤ := by
        rw [hτ_eq]
        simp
      simpa [hτ_eq] using
        driftedBrownian_value_eq_boundary_at_hittingTime
          (B := B) (a := a) (b := b) hcont hτ_lt
  · rintro ⟨s, hs, hs_eq⟩
    -- Proof comment: any deterministic affine hit inside `[0, T]` bounds the first hit by `T`.
    exact
      le_trans
        (brownianAffineBoundaryHittingTime_le_of_eq
          (B := B) (a := a) (b := b) (ω := ω) (t := s) hs_eq)
        (by exact_mod_cast hs.2)

/-- Helper for Exercise 21.2.6: on a continuous drifted path, the event `{τ ≤ u}` is equivalent
to rational-time approximations of the boundary value `b` inside `[0, u]`. -/
private lemma brownianAffineBoundaryHittingTime_le_iff_forall_nnrat_approx
    {B : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ)) (u : NNReal) :
    brownianAffineBoundaryHittingTime B a b ω ≤ u ↔
      ∀ n : ℕ, ∃ q : ℚ≥0, (q : NNReal) ≤ u ∧
        |(B (q : NNReal) ω - a * (q : ℝ)) - b| < (1 : ℝ) / (n + 1) := by
  constructor
  · intro hτu n
    let ε : ℝ := (1 : ℝ) / (n + 1)
    have hεpos : 0 < ε := by
      dsimp [ε]
      positivity
    have hτne : brownianAffineBoundaryHittingTime B a b ω ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hτu
    let t : NNReal := (brownianAffineBoundaryHittingTime B a b ω).untopA
    have htle : t ≤ u := by
      have hτu' :
          (((brownianAffineBoundaryHittingTime B a b ω).untopA : NNReal) : ENNReal) ≤
            (u : ENNReal) := by
        have hs :
            (((brownianAffineBoundaryHittingTime B a b ω).untopA : NNReal) : ENNReal) =
              brownianAffineBoundaryHittingTime B a b ω := by
          cases hτval : brownianAffineBoundaryHittingTime B a b ω with
          | top =>
              simp [hτval] at hτne
          | coe x =>
              rfl
        exact hs ▸ hτu
      exact ENNReal.coe_le_coe.mp hτu'
    have htb : B t ω - a * (t : ℝ) = b := by
      -- Proof comment: once the finite affine hit time is identified with `t`, the drifted path
      -- is exactly on the boundary at that time.
      simpa [t] using
        driftedBrownian_value_eq_boundary_at_hittingTime
          (B := B) (a := a) (b := b) (ω := ω)
          hcont (lt_top_iff_ne_top.mpr hτne)
    by_cases ht0 : t = 0
    · refine ⟨0, ?_, ?_⟩
      · simpa [t, ht0] using htle
      · have hB0 : B 0 ω - a * (0 : ℝ) = b := by
          simpa [t, ht0] using htb
        have hB0' : B 0 ω = b := by
          simpa using hB0
        have hpos : 0 < (1 : ℝ) / (n + 1) := by
          positivity
        simpa [hB0', ε] using hpos
    · have htpos : 0 < t := by
        exact bot_lt_iff_ne_bot.mpr ht0
      let U : Set NNReal := {s : NNReal | B s ω - a * (s : ℝ) ∈ Set.Ioo (b - ε) (b + ε)}
      have hUopen : IsOpen U := by
        -- Proof comment: continuity of the drifted path gives a time neighborhood on which the
        -- path remains within `ε` of the boundary value.
        simpa [U] using (isOpen_Ioo.preimage hcont)
      have htU : t ∈ U := by
        simpa [U, ε, htb] using hεpos
      have hUNhds : U ∈ 𝓝 t := hUopen.mem_nhds htU
      rcases mem_nhds_iff_exists_Ioo_subset'
          (show ∃ l : NNReal, l < t from ⟨0, htpos⟩)
          (show ∃ r : NNReal, t < r from
            ⟨t + 1, by simpa using lt_add_of_pos_right t zero_lt_one⟩)
          |>.1 hUNhds with ⟨l, r, ⟨hlt, htr⟩, hIoo⟩
      obtain ⟨q, hql, hqt⟩ := exists_rat_btwn (show (l : ℝ) < (t : ℝ) by exact_mod_cast hlt)
      have hq_nonneg : 0 ≤ q := by
        have h0le_l : (0 : ℝ) ≤ (l : ℝ) := by
          exact_mod_cast (show 0 ≤ l by simp)
        exact Rat.cast_nonneg.mp (le_trans h0le_l hql.le)
      let qnn : ℚ≥0 := ⟨q, hq_nonneg⟩
      have hql_nn : l < (qnn : NNReal) := by
        exact_mod_cast hql
      have hqt_nn : (qnn : NNReal) < t := by
        exact_mod_cast hqt
      refine ⟨qnn, le_trans hqt_nn.le htle, ?_⟩
      have hqU : (qnn : NNReal) ∈ U := hIoo ⟨hql_nn, lt_trans hqt_nn htr⟩
      rcases hqU with ⟨hqlo, hqhi⟩
      have hleft : -ε < (B (qnn : NNReal) ω - a * (qnn : ℝ)) - b := by
        have hqlo' : b - ε < B (qnn : NNReal) ω - a * (qnn : ℝ) := hqlo
        linarith
      have hright : (B (qnn : NNReal) ω - a * (qnn : ℝ)) - b < ε := by
        have hqhi' : B (qnn : NNReal) ω - a * (qnn : ℝ) < b + ε := hqhi
        linarith
      exact abs_lt.2 ⟨hleft, hright⟩
  · intro hApprox
    let R : Set ℝ := (fun t : NNReal ↦ B t ω - a * (t : ℝ)) '' Set.Icc (0 : NNReal) u
    have hRclosed : IsClosed R := by
      -- Proof comment: the image of the compact time interval under the continuous drifted path
      -- is compact, hence closed.
      simpa [R] using (IsCompact.image isCompact_Icc hcont).isClosed
    have hbClosure : b ∈ closure R := by
      -- Proof comment: the rational approximations force `b` into the closure of the drifted
      -- path image on `[0, u]`.
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      rcases hApprox n with ⟨q, hqu, hqε⟩
      have hqε' : |b - (B (q : NNReal) ω - a * (q : ℝ))| < (1 : ℝ) / (n + 1) := by
        simpa [abs_sub_comm] using hqε
      refine ⟨B (q : NNReal) ω - a * (q : ℝ), ?_, ?_⟩
      · refine ⟨(q : NNReal), ?_, rfl⟩
        exact ⟨by simp, hqu⟩
      · change |b - (B (q : NNReal) ω - a * (q : ℝ))| < ε
        exact lt_trans hqε' hn
    have hbR : b ∈ R := by
      simpa [hRclosed.closure_eq] using hbClosure
    rcases hbR with ⟨t, htI, htb⟩
    exact
      (brownianAffineBoundaryHittingTime_le_of_eq
        (B := B) (a := a) (b := b) (ω := ω) (t := t) htb).trans
        (by exact_mod_cast htI.2)

/-- Helper for Exercise 21.2.6: for strongly measurable time slices and continuous drifted paths,
the affine-boundary hitting time is a stopping time for the natural filtration. -/
lemma brownianAffineBoundaryHittingTime_isStoppingTime
    {B : NNReal → Ω → ℝ} {a b : ℝ} (hBsm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous (fun t : NNReal ↦ B t ω - a * (t : ℝ))) :
    IsStoppingTime (Filtration.natural B hBsm) (brownianAffineBoundaryHittingTime B a b) := by
  -- Route correction: the usable owner theorem on the current surface is the explicit
  -- rational-approximation description of `{τ ≤ u}` inside the natural filtration at time `u`.
  intro u
  let ℱB : Filtration NNReal ‹MeasurableSpace Ω› := Filtration.natural B hBsm
  change MeasurableSet[ℱB u] {ω | brownianAffineBoundaryHittingTime B a b ω ≤ u}
  have hStrong : StronglyAdapted ℱB B := Filtration.stronglyAdapted_natural hBsm
  have hSlice :
      ∀ n : ℕ, ∀ q : {q : ℚ≥0 // (q : NNReal) ≤ u},
        MeasurableSet[ℱB u]
          {ω | |(B (q : NNReal) ω - a * (q : ℝ)) - b| < (1 : ℝ) / (n + 1)} := by
    intro n q
    have hMeas :
        StronglyMeasurable[ℱB u] (fun ω ↦ B (q : NNReal) ω - a * (q : ℝ)) := by
      exact
        (hStrong.stronglyMeasurable_le (i := (q : NNReal)) (j := u) q.2).sub
          stronglyMeasurable_const
    have hPre :
        {ω | |(B (q : NNReal) ω - a * (q : ℝ)) - b| < (1 : ℝ) / (n + 1)} =
          (fun ω ↦ B (q : NNReal) ω - a * (q : ℝ)) ⁻¹'
            Set.Ioo (b - (1 : ℝ) / (n + 1)) (b + (1 : ℝ) / (n + 1)) := by
      ext ω
      constructor
      · intro hω
        change |(B (q : NNReal) ω - a * (q : ℝ)) - b| < (1 : ℝ) / (n + 1) at hω
        rcases abs_lt.1 hω with ⟨hleft, hright⟩
        constructor <;> linarith
      · intro hω
        change B (q : NNReal) ω - a * (q : ℝ) ∈
          Set.Ioo (b - (1 : ℝ) / (n + 1)) (b + (1 : ℝ) / (n + 1)) at hω
        rcases hω with ⟨hleft, hright⟩
        have hleft' : -((1 : ℝ) / (n + 1)) < (B (q : NNReal) ω - a * (q : ℝ)) - b := by
          linarith
        have hright' : (B (q : NNReal) ω - a * (q : ℝ)) - b < (1 : ℝ) / (n + 1) := by
          linarith
        exact abs_lt.2 ⟨hleft', hright'⟩
    rw [hPre]
    exact hMeas.measurable isOpen_Ioo.measurableSet
  have hEvent :
      {ω | brownianAffineBoundaryHittingTime B a b ω ≤ u} =
        ⋂ n : ℕ,
          ⋃ q : {q : ℚ≥0 // (q : NNReal) ≤ u},
            {ω | |(B (q : NNReal) ω - a * (q : ℝ)) - b| < (1 : ℝ) / (n + 1)} := by
    -- Proof comment: the affine first-hit event is visible through rational-time approximations
    -- of the drifted path inside the deterministic time window `[0, u]`.
    ext ω
    simp [brownianAffineBoundaryHittingTime_le_iff_forall_nnrat_approx
      (B := B) (a := a) (b := b) (ω := ω) (hcont ω) u]
  rw [hEvent]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion fun q ↦ hSlice n q

/-- Helper for Exercise 21.2.6: along a continuous sample path, every time strictly before the
affine-boundary hitting time still lies strictly below the boundary. -/
lemma driftedBrownian_value_lt_boundary_of_lt_hittingTime
    (hB : IsBrownianMotion μ B) {a b : ℝ} (hb : 0 < b) {n : NNReal} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ))
    (hbefore : (n : ENNReal) < brownianAffineBoundaryHittingTime B a b ω) :
    B n ω - a * (n : ℝ) < b := by
  let f : NNReal → ℝ := fun t ↦ B t ω - a * (t : ℝ)
  have hzero : f 0 = 0 := by
    -- Proof comment: Brownian motion starts at `0`, and the affine correction vanishes at time
    -- `0`.
    simpa [f] using congrFun hB.zero ω
  -- Proof comment: if the drifted path had already reached or exceeded `b` by time `n`,
  -- continuity on `[0,n]` would produce an earlier exact affine hit, contradicting `n < τ`.
  by_contra hnot_lt
  have hge : b ≤ f n := by
    exact le_of_not_gt hnot_lt
  have hb_mem : b ∈ Set.Icc (f 0) (f n) := by
    refine ⟨?_, hge⟩
    simpa [hzero] using hb.le
  obtain ⟨s, hs_mem, hs_eq⟩ :=
    (intermediate_value_Icc
      (a := (0 : NNReal))
      (b := n)
      (by simp)
      hcont.continuousOn) hb_mem
  have hτ_le_s : brownianAffineBoundaryHittingTime B a b ω ≤ s := by
    -- Proof comment: any exact affine hit at time `s ≤ n` bounds the hitting time by `s`.
    exact brownianAffineBoundaryHittingTime_le_of_eq
      (B := B) (a := a) (b := b) (ω := ω) (t := s) hs_eq
  have hτ_le_n : brownianAffineBoundaryHittingTime B a b ω ≤ (n : ENNReal) := by
    exact le_trans hτ_le_s (by exact_mod_cast hs_mem.2)
  exact (not_lt_of_ge hτ_le_n) hbefore

/-- Helper for Exercise 21.2.6: for `λ > 0`, the root
`θ = a + √(a² + 2 λ)` is strictly positive. -/
private lemma affineBoundaryTheta_pos {a lam : ℝ} (hlam : 0 < lam) :
    0 < a + Real.sqrt (a ^ 2 + 2 * lam) := by
  have hnonneg : 0 ≤ a ^ 2 + 2 * lam := by
    nlinarith [sq_nonneg a, hlam]
  by_cases ha : 0 ≤ a
  · -- Proof comment: when `a` is nonnegative, the positive square-root term dominates.
    have hsqrt_pos : 0 < Real.sqrt (a ^ 2 + 2 * lam) := by
      apply Real.sqrt_pos.2
      nlinarith [sq_nonneg a, hlam]
    nlinarith
  · -- Proof comment: when `a < 0`, compare `√(a² + 2 λ)` against `-a` using the strict
    -- positivity of `2 λ`.
    have hsquare : (-a) ^ 2 < (Real.sqrt (a ^ 2 + 2 * lam)) ^ 2 := by
      rw [Real.sq_sqrt hnonneg]
      nlinarith [hlam]
    have hsqrt_gt : -a < Real.sqrt (a ^ 2 + 2 * lam) := by
      have hneg_nonneg : 0 ≤ -a := by
        linarith
      have hsqrt_nonneg : 0 ≤ Real.sqrt (a ^ 2 + 2 * lam) := Real.sqrt_nonneg _
      nlinarith
    linarith

/-- Helper for Exercise 21.2.6: on the finite-hit branch, the exponential martingale evaluated at
the affine-boundary hitting time rewrites to the Laplace weight with parameter
`θ = a + √(a² + 2 λ)`. -/
private lemma affineBoundaryStoppedExponential_eq_laplaceWeight
    {a b lam : ℝ} (hlam : 0 ≤ lam) {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ))
    (hω : brownianAffineBoundaryHittingTime B a b ω < ⊤) :
    let θ := a + Real.sqrt (a ^ 2 + 2 * lam)
    Real.exp
        (θ * B (brownianAffineBoundaryHittingTime B a b ω).untopA ω -
          (θ ^ 2 / 2) * (brownianAffineBoundaryHittingTime B a b ω).toReal) =
      Real.exp
        (θ * b - lam * (brownianAffineBoundaryHittingTime B a b ω).toReal) := by
  -- Proof comment: evaluate the drifted Brownian path at the hitting time and then use the
  -- quadratic identity defining `θ`.
  dsimp
  have hquad := affineBoundaryTheta_quadratic (a := a) (lam := lam) hlam
  have hτ_ne : brownianAffineBoundaryHittingTime B a b ω ≠ ⊤ := ne_of_lt hω
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hτ_ne
  have hτ_eq : brownianAffineBoundaryHittingTime B a b ω = (t : ENNReal) := by
    simpa using ht.symm
  have hhit :
      B (brownianAffineBoundaryHittingTime B a b ω).untopA ω -
        a * ((brownianAffineBoundaryHittingTime B a b ω).untopA : ℝ) = b :=
    driftedBrownian_value_eq_boundary_at_hittingTime
      (B := B) (a := a) (b := b) (ω := ω) hcont hω
  have hhit_t : B t ω - a * (t : ℝ) = b := by
    simpa [hτ_eq] using hhit
  have hB_eq : B t ω = a * (t : ℝ) + b := by
    linarith
  rw [hτ_eq] at ⊢
  let θ : ℝ := a + Real.sqrt (a ^ 2 + 2 * lam)
  have hquadθ : θ ^ 2 / 2 - a * θ = lam := by
    simpa [θ] using hquad
  change Real.exp (θ * B t ω - (θ ^ 2 / 2) * (t : ℝ)) =
      Real.exp (θ * b - lam * (t : ℝ))
  rw [hB_eq]
  have hexponent :
      θ * (a * (t : ℝ) + b) - (θ ^ 2 / 2) * (t : ℝ) = θ * b - lam * (t : ℝ) := by
    nlinarith [hquadθ]
  rw [hexponent]

/-- Helper for Exercise 21.2.6: stopping the exponential martingale at `τ ∧ T` splits into the
finite-hit Laplace branch and the deterministic-horizon miss branch. -/
private lemma affineBoundaryStoppedExponential_minConst_eq_split
    {a b lam : ℝ} (hlam : 0 ≤ lam) {T : NNReal} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ)) :
    let θ := a + Real.sqrt (a ^ 2 + 2 * lam)
    stoppedValue
        (fun t : NNReal ↦ fun ω' : Ω ↦
          Real.exp (θ * B t ω' - (θ ^ 2 / 2) * (t : ℝ)))
        (fun ω' ↦ min (brownianAffineBoundaryHittingTime B a b ω') (T : ENNReal)) ω =
      if brownianAffineBoundaryHittingTime B a b ω ≤ (T : ENNReal) then
        Real.exp (θ * b - lam * (brownianAffineBoundaryHittingTime B a b ω).toReal)
      else
        Real.exp (θ * (B T ω - a * (T : ℝ)) - lam * (T : ℝ)) := by
  -- Proof comment: first split `τ ∧ T` into the hit and miss branches, then rewrite the hit
  -- branch with the affine-boundary identity and normalize the miss branch with the quadratic
  -- relation for `θ`.
  dsimp
  let θ : ℝ := a + Real.sqrt (a ^ 2 + 2 * lam)
  have hquad : θ ^ 2 / 2 - a * θ = lam := by
    simpa [θ] using affineBoundaryTheta_quadratic (a := a) (lam := lam) hlam
  rw [stoppedValue_minConst_eq_if
    (X := fun t : NNReal ↦ fun ω' : Ω ↦ Real.exp (θ * B t ω' - (θ ^ 2 / 2) * (t : ℝ)))
    (τ := brownianAffineBoundaryHittingTime B a b) (t := T) (ω := ω)]
  by_cases hτT : brownianAffineBoundaryHittingTime B a b ω ≤ (T : ENNReal)
  · have hτ_lt : brownianAffineBoundaryHittingTime B a b ω < ⊤ := by
      exact lt_of_le_of_lt hτT (by simp)
    have hTimeEq :
        (((brownianAffineBoundaryHittingTime B a b ω).untopA : NNReal) : ℝ) =
          (brownianAffineBoundaryHittingTime B a b ω).toReal := by
      -- Proof comment: on the finite-hit branch, the stopped deterministic time process returns
      -- exactly `τ.toReal`.
      simpa [stoppedValue] using
        (stoppedValue_ennrealTimeProcess_eq_toReal
          (τ := brownianAffineBoundaryHittingTime B a b)
          (ω := ω)
          (hτ := ne_of_lt hτ_lt))
    -- Proof comment: on `{τ ≤ T}`, the stopped value is the exponential martingale at `τ`,
    -- which the boundary evaluation lemma rewrites to the Laplace factor.
    simpa [hτT, θ, stoppedValue, hTimeEq] using
      affineBoundaryStoppedExponential_eq_laplaceWeight
        (B := B) (a := a) (b := b) (lam := lam) (ω := ω) hlam hcont hτ_lt
  · -- Proof comment: on the miss branch, the stop occurs at the deterministic horizon `T`, so
    -- only the quadratic normalization of the exponent remains.
    have hexponent :
        θ * B T ω - (θ ^ 2 / 2) * (T : ℝ) =
          θ * (B T ω - a * (T : ℝ)) - lam * (T : ℝ) := by
      nlinarith [hquad]
    rw [if_neg hτT, if_neg hτT]
    rw [hexponent]

/-- Helper for Exercise 21.2.6: before the affine-boundary hitting time, the miss branch of the
stopped exponential is bounded by the boundary value itself once `θ > 0`. -/
private lemma affineBoundaryMissBranch_bound
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam)
    {T : NNReal} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ))
    (hmiss : (T : ENNReal) < brownianAffineBoundaryHittingTime B a b ω) :
    let θ := a + Real.sqrt (a ^ 2 + 2 * lam)
    Real.exp (θ * (B T ω - a * (T : ℝ)) - lam * (T : ℝ)) ≤
      Real.exp (θ * b - lam * (T : ℝ)) := by
  -- Proof comment: before the hit, the drifted path is still strictly below `b`; multiplying by
  -- the positive coefficient `θ` preserves the order and `exp` is monotone.
  dsimp
  have hθpos := affineBoundaryTheta_pos (a := a) (lam := lam) hlam
  have hlt :
      B T ω - a * (T : ℝ) < b :=
    driftedBrownian_value_lt_boundary_of_lt_hittingTime
      (μ := μ) (B := B) hB (a := a) (b := b) hb hcont hmiss
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Helper for Exercise 21.2.6: the correct law object for `τ.toReal` first restricts to the
finite-hit event, so the `τ = ∞` mass does not collapse to `0`. -/
private def brownianAffineBoundaryFiniteHitMeasure
    {μ : Measure Ω} (B : NNReal → Ω → ℝ) (a b : ℝ) : Measure ℝ :=
  (μ.restrict {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}).map
    (fun ω ↦ (brownianAffineBoundaryHittingTime B a b ω).toReal)

/-- Helper for Exercise 21.2.6: the set of sample points where the Brownian path is not
continuous. -/
private def brownianPathDiscontinuitySet
    (_hB : IsBrownianMotion μ B) : Set Ω :=
  {ω | ¬ Continuous (fun t : NNReal ↦ B t ω)}

/-- Helper for Exercise 21.2.6: Brownian sample-path discontinuities form a null set. -/
private lemma brownianPathDiscontinuitySet_null
    (hB : IsBrownianMotion μ B) :
    μ (brownianPathDiscontinuitySet (μ := μ) (B := B) hB) = 0 := by
  -- Proof comment: almost-sure continuity of Brownian paths is exactly the statement that the
  -- discontinuity set is null.
  have hcont_ae : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ B t ω) := by
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hB.continuous_paths
  simpa [brownianPathDiscontinuitySet] using (ae_iff.mp hcont_ae)

/-- Helper for Exercise 21.2.6: enlarge the path-discontinuity set to a measurable null set once
and for all. -/
private lemma brownianPathExceptionSet_exists
    (hB : IsBrownianMotion μ B) :
    ∃ N : Set Ω,
      brownianPathDiscontinuitySet (μ := μ) (B := B) hB ⊆ N ∧ MeasurableSet N ∧ μ N = 0 := by
  -- Proof comment: `exists_measurable_superset_of_null` packages the null exceptional set into a
  -- measurable one so later piecewise constructions stay measurable.
  exact exists_measurable_superset_of_null
    (brownianPathDiscontinuitySet_null (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.2.6: the measurable null exceptional set used to patch Brownian paths
to an everywhere-continuous version. -/
private def brownianPathExceptionSet
    (hB : IsBrownianMotion μ B) : Set Ω :=
  Classical.choose (brownianPathExceptionSet_exists (μ := μ) (B := B) hB)

/-- Helper for Exercise 21.2.6: the discontinuity set is contained in the chosen measurable null
exceptional set. -/
private lemma brownianPathDiscontinuitySet_subset_exceptionSet
    (hB : IsBrownianMotion μ B) :
    brownianPathDiscontinuitySet (μ := μ) (B := B) hB ⊆
      brownianPathExceptionSet (μ := μ) (B := B) hB :=
  (Classical.choose_spec (brownianPathExceptionSet_exists (μ := μ) (B := B) hB)).1

/-- Helper for Exercise 21.2.6: the chosen Brownian path exceptional set is measurable. -/
private lemma brownianPathExceptionSet_measurable
    (hB : IsBrownianMotion μ B) :
    MeasurableSet (brownianPathExceptionSet (μ := μ) (B := B) hB) :=
  (Classical.choose_spec (brownianPathExceptionSet_exists (μ := μ) (B := B) hB)).2.1

/-- Helper for Exercise 21.2.6: the chosen Brownian path exceptional set is null. -/
private lemma brownianPathExceptionSet_null
    (hB : IsBrownianMotion μ B) :
    μ (brownianPathExceptionSet (μ := μ) (B := B) hB) = 0 :=
  (Classical.choose_spec (brownianPathExceptionSet_exists (μ := μ) (B := B) hB)).2.2

/-- Helper for Exercise 21.2.6: patch Brownian paths by setting them to `0` on the measurable
null exceptional set. -/
private def brownianPathContinuousVersion
    (hB : IsBrownianMotion μ B) : NNReal → Ω → ℝ :=
  fun t ↦
    Set.piecewise
      (brownianPathExceptionSet (μ := μ) (B := B) hB)
      (fun _ ↦ (0 : ℝ))
      (B t)

/-- Helper for Exercise 21.2.6: the patched Brownian paths are everywhere continuous. -/
private lemma brownianPathContinuousVersion_continuous
    (hB : IsBrownianMotion μ B) :
    ∀ ω, Continuous (fun t ↦ brownianPathContinuousVersion (μ := μ) (B := B) hB t ω) := by
  -- Proof comment: off the exceptional set the patched path agrees with the original Brownian
  -- path, while on the exceptional set it is identically zero.
  classical
  intro ω
  by_cases hω : ω ∈ brownianPathExceptionSet (μ := μ) (B := B) hB
  · simpa [brownianPathContinuousVersion, hω] using
      (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · have hcont : Continuous (fun t : NNReal ↦ B t ω) := by
      by_contra hnot
      exact hω <|
        brownianPathDiscontinuitySet_subset_exceptionSet (μ := μ) (B := B) hB
          (by simpa [brownianPathDiscontinuitySet] using hnot)
    simpa [brownianPathContinuousVersion, hω] using hcont

/-- Helper for Exercise 21.2.6: the patched Brownian version agrees almost everywhere with the
original process at every deterministic time. -/
private lemma brownianPathContinuousVersion_ae_eq
    (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      brownianPathContinuousVersion (μ := μ) (B := B) hB t ω = B t ω := by
  -- Proof comment: the patch changes the process only on the measurable null exceptional set.
  have hN_ae :
      ∀ᵐ ω ∂μ, ω ∉ brownianPathExceptionSet (μ := μ) (B := B) hB := by
    exact compl_mem_ae_iff.mpr (brownianPathExceptionSet_null (μ := μ) (B := B) hB)
  filter_upwards [hN_ae] with ω hω t
  simp [brownianPathContinuousVersion, hω]

/-- Helper for Exercise 21.2.6: the patched process is a modification of the original Brownian
motion. -/
private lemma brownianPathContinuousVersion_areModifications
    (hB : IsBrownianMotion μ B) :
    AreModifications μ B (brownianPathContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: fixed-time almost-everywhere equality is exactly the modification relation.
  intro t
  filter_upwards [brownianPathContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  simpa using (hω t).symm

/-- Helper for Exercise 21.2.6: patching Brownian motion on the measurable null exceptional set
preserves the Brownian owner. -/
private lemma brownianPathContinuousVersion_isBrownianMotion
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (brownianPathContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: the Brownian characterization is stable under fixed-time almost-everywhere
  -- modification, and the patch already has continuous sample paths by construction.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    by_cases hω : ω ∈ brownianPathExceptionSet (μ := μ) (B := B) hB
    · simp [brownianPathContinuousVersion, hω]
    · simp [brownianPathContinuousVersion, hω, hB.zero]
  · exact
      (IsBrownianMotion.isGaussianProcess hB).congr
        (fun t ↦ brownianPathContinuousVersion_areModifications (μ := μ) (B := B) hB t)
  · intro t
    exact
      (integral_congr_ae
        (brownianPathContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (IsBrownianMotion.mean_zero hB t)
  · intro s t
    exact
      (covariance_congr_ae
        (brownianPathContinuousVersion_areModifications (μ := μ) (B := B) hB s)
        (brownianPathContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (IsBrownianMotion.covariance_eq hB s t)
  · filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      brownianPathContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Exercise 21.2.6: if two sample paths agree pointwise at `ω`, then their affine
boundary hitting times agree at `ω`. -/
private lemma brownianAffineBoundaryHittingTime_eq_of_forall_eq
    {X Y : NNReal → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hω : ∀ t : NNReal, X t ω = Y t ω) :
    brownianAffineBoundaryHittingTime X a b ω = brownianAffineBoundaryHittingTime Y a b ω := by
  -- Proof comment: unfolding `hittingAfter` shows that the affine hitting time only depends on
  -- the pointwise drifted path values.
  rw [brownianAffineBoundaryHittingTime_eq_hittingAfter, brownianAffineBoundaryHittingTime_eq_hittingAfter]
  rw [hittingAfter_def, hittingAfter_def]
  change
    (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω - a * (j : ℝ) ∈ ({b} : Set ℝ) then
        ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω - a * (i : ℝ) ∈ ({b} : Set ℝ)} : NNReal) :
          ENNReal)
      else ⊤) =
      (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω - a * (j : ℝ) ∈ ({b} : Set ℝ) then
        ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ Y i ω - a * (i : ℝ) ∈ ({b} : Set ℝ)} : NNReal) :
          ENNReal)
      else ⊤)
  have hExists :
      (∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω - a * (j : ℝ) ∈ ({b} : Set ℝ)) ↔
        ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω - a * (j : ℝ) ∈ ({b} : Set ℝ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
  have hSet :
      {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω - a * (i : ℝ) ∈ ({b} : Set ℝ)} =
        {i : NNReal | (0 : NNReal) ≤ i ∧ Y i ω - a * (i : ℝ) ∈ ({b} : Set ℝ)} := by
    ext i
    simp [hω i]
  by_cases hX : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω - a * (j : ℝ) ∈ ({b} : Set ℝ)
  · have hY : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω - a * (j : ℝ) ∈ ({b} : Set ℝ) :=
      hExists.mp hX
    rw [if_pos hX, if_pos hY]
    simpa using congrArg (fun s : Set NNReal ↦ ((sInf s : NNReal) : ENNReal)) hSet
  · have hY : ¬ ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω - a * (j : ℝ) ∈ ({b} : Set ℝ) := by
      exact mt hExists.mpr hX
    rw [if_neg hX, if_neg hY]

/-- Helper for Exercise 21.2.6: for measurable time slices and everywhere-continuous drifted
paths, the affine-boundary hitting time is measurable. -/
private lemma measurable_brownianAffineBoundaryHittingTime_of_continuous
    {X : NNReal → Ω → ℝ} {a b : ℝ} (hXmeas : ∀ t, Measurable (X t))
    (hXcont : ∀ ω, Continuous (fun t : NNReal ↦ X t ω - a * (t : ℝ))) :
    Measurable (brownianAffineBoundaryHittingTime X a b) := by
  classical
  refine measurable_of_Iic ?_
  intro s
  by_cases hs : s = ⊤
  · -- Proof comment: the top threshold contributes the whole space.
    simp [hs]
  · let t : NNReal := s.toNNReal
    have hs_eq : (t : ENNReal) = s := ENNReal.coe_toNNReal hs
    let ratWindow : Set ℝ := Set.Icc (0 : ℝ) (t : ℝ) ∩ Set.range Rat.cast
    have hclosure_ratWindow : closure ratWindow = Set.Icc (0 : ℝ) (t : ℝ) := by
      by_cases ht : t = 0
      · ext x
        simp [ratWindow, ht]
      · have hnontrivial : (Set.Icc (0 : ℝ) (t : ℝ)).Nontrivial := by
          refine ⟨0, by simp, (t : ℝ), by simp, ?_⟩
          exact_mod_cast (Ne.symm ht)
        simpa [ratWindow] using
          closure_ordConnected_inter_rat
            (s := Set.Icc (0 : ℝ) (t : ℝ))
            Set.ordConnected_Icc hnontrivial
    have hset :
        {ω | brownianAffineBoundaryHittingTime X a b ω ≤ (t : ENNReal)} =
          ⋂ n : ℕ, ⋃ q : {q : ℚ // 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ)},
            {ω | |X (Real.toNNReal (q : ℝ)) ω - a * (Real.toNNReal (q : ℝ) : ℝ) - b|
                < (1 : ℝ) / (n + 1)} := by
      ext ω
      let g : ℝ → ℝ := fun r ↦ X (Real.toNNReal r) ω - a * (Real.toNNReal r : ℝ)
      have hgcont : Continuous g := by
        -- Proof comment: compose the continuous drifted path with `Real.toNNReal`.
        simpa [g] using (hXcont ω).comp continuous_real_toNNReal
      have hcompact_ratWindow : IsCompact (closure ratWindow) := by
        rw [hclosure_ratWindow]
        simpa using (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (t : ℝ)))
      have hclosure_image :
          g '' closure ratWindow = closure (g '' ratWindow) :=
        image_closure_of_isCompact hcompact_ratWindow hgcont.continuousOn
      constructor
      · intro hτ_le
        rw [Set.mem_iInter]
        intro n
        have hτ_ne : brownianAffineBoundaryHittingTime X a b ω ≠ ⊤ :=
          ne_top_of_le_ne_top (by simp) hτ_le
        have hτ_lt : brownianAffineBoundaryHittingTime X a b ω < ⊤ :=
          lt_top_iff_ne_top.mpr hτ_ne
        have hhit :
            X (brownianAffineBoundaryHittingTime X a b ω).untopA ω -
              a * ((brownianAffineBoundaryHittingTime X a b ω).untopA : ℝ) = b := by
          -- Proof comment: continuity recovers the exact boundary value at the first finite hit.
          simpa using
            driftedBrownian_value_eq_boundary_at_hittingTime
              (B := X) (a := a) (b := b) (ω := ω) (hXcont ω) hτ_lt
        have htime_mem : ((brownianAffineBoundaryHittingTime X a b ω).untopA : ℝ) ∈
            closure ratWindow := by
          rw [hclosure_ratWindow]
          constructor
          · exact ((brownianAffineBoundaryHittingTime X a b ω).untopA).2
          · have hτ_le' : (brownianAffineBoundaryHittingTime X a b ω).untopA ≤ t := by
              have hτ_coe :
                  (((brownianAffineBoundaryHittingTime X a b ω).untopA : NNReal) : ENNReal) =
                    brownianAffineBoundaryHittingTime X a b ω := by
                cases hτval : brownianAffineBoundaryHittingTime X a b ω with
                | top =>
                    simp [hτval] at hτ_ne
                | coe x =>
                    rfl
              have hτ_le'' :
                  (((brownianAffineBoundaryHittingTime X a b ω).untopA : NNReal) : ENNReal) ≤
                    (t : ENNReal) := by
                rw [hτ_coe]
                exact hτ_le
              exact_mod_cast hτ_le''
            exact_mod_cast hτ_le'
        have hb_mem_closure : b ∈ closure (g '' ratWindow) := by
          rw [← hclosure_image]
          exact ⟨(brownianAffineBoundaryHittingTime X a b ω).untopA, htime_mem, by simpa [g] using hhit⟩
        have hε_pos : 0 < (1 : ℝ) / (n + 1) := by positivity
        rcases Metric.mem_closure_iff.1 hb_mem_closure ((1 : ℝ) / (n + 1)) hε_pos with
          ⟨y, hy_mem, hy_close⟩
        rcases hy_mem with ⟨r, hr_mem, rfl⟩
        rcases hr_mem.2 with ⟨q, rfl⟩
        have hclose' :
            |g q - b| < (1 : ℝ) / (n + 1) := by
          simpa [Real.dist_eq, abs_sub_comm] using hy_close
        refine Set.mem_iUnion.2 ⟨⟨q, by exact_mod_cast hr_mem.1.1, hr_mem.1.2⟩, ?_⟩
        simpa [g] using hclose'
      · intro hω
        have happ :
            ∀ n : ℕ, ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ) ∧
              |X (Real.toNNReal q) ω - a * (Real.toNNReal q : ℝ) - b| < (1 : ℝ) / (n + 1) := by
          intro n
          rw [Set.mem_iInter] at hω
          rcases Set.mem_iUnion.1 (hω n) with ⟨q, hq⟩
          exact ⟨q, q.2.1, q.2.2, by simpa using hq⟩
        have hb_mem_closure : b ∈ closure (g '' ratWindow) := by
          refine Metric.mem_closure_iff.2 ?_
          intro ε hε
          rcases exists_nat_one_div_lt hε with ⟨n, hn⟩
          rcases happ n with ⟨q, hq_nonneg, hq_le, hq_close⟩
          have hclose' : |g q - b| < (1 : ℝ) / (n + 1) := by
            simpa [g] using hq_close
          have hdist : dist b (g q) < (1 : ℝ) / (n + 1) := by
            simpa [Real.dist_eq, abs_sub_comm] using hclose'
          refine ⟨g q, ?_, lt_trans hdist hn⟩
          refine ⟨(q : ℝ), ?_, by simp [g]⟩
          exact ⟨⟨by exact_mod_cast hq_nonneg, hq_le⟩, ⟨q, rfl⟩⟩
        have hb_mem_image : b ∈ g '' closure ratWindow := by
          rw [hclosure_image]
          exact hb_mem_closure
        rcases hb_mem_image with ⟨r, hr_mem, hr_eq⟩
        rw [hclosure_ratWindow] at hr_mem
        have hτ_le_r :
            brownianAffineBoundaryHittingTime X a b ω ≤ (Real.toNNReal r : ENNReal) := by
          -- Proof comment: any exact affine hit inside the compact window bounds the hitting time.
          exact brownianAffineBoundaryHittingTime_le_of_eq
            (B := X) (a := a) (b := b) (ω := ω) (t := Real.toNNReal r)
            (by simpa [g] using hr_eq)
        have hr_le : Real.toNNReal r ≤ t := by
          have : (Real.toNNReal r : ℝ) ≤ (t : ℝ) := by
            simpa [Real.toNNReal_of_nonneg hr_mem.1] using hr_mem.2
          exact_mod_cast this
        exact le_trans hτ_le_r (by exact_mod_cast hr_le)
    -- Proof comment: the threshold event is a countable intersection of countable unions of
    -- measurable deterministic-time approximation events.
    rw [← hs_eq]
    have hmeas :
        MeasurableSet {ω | brownianAffineBoundaryHittingTime X a b ω ≤ (t : ENNReal)} := by
      rw [hset]
      refine MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion fun q ↦ ?_
      exact measurableSet_lt
        ((((hXmeas (Real.toNNReal (q : ℝ))).sub measurable_const).sub measurable_const).abs)
        measurable_const
    simpa [Set.preimage] using hmeas

/-- Helper for Exercise 21.2.6: the real-valued affine hitting time agrees almost everywhere with
the one built from the everywhere-continuous Brownian version. -/
private lemma brownianAffineBoundaryHittingTime_toReal_ae_eq_continuousVersion
    (hB : IsBrownianMotion μ B) {a b : ℝ} :
    (fun ω ↦ (brownianAffineBoundaryHittingTime B a b ω).toReal) =ᵐ[μ]
      fun ω ↦
        (brownianAffineBoundaryHittingTime
          (brownianPathContinuousVersion (μ := μ) (B := B) hB) a b ω).toReal := by
  -- Proof comment: off the measurable null exceptional set, the patched and original Brownian
  -- paths agree pointwise, so their affine hitting times match exactly.
  let Bc := brownianPathContinuousVersion (μ := μ) (B := B) hB
  filter_upwards [brownianPathContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  have hτ :
      brownianAffineBoundaryHittingTime B a b ω =
        brownianAffineBoundaryHittingTime Bc a b ω :=
    brownianAffineBoundaryHittingTime_eq_of_forall_eq
      (a := a) (b := b) (ω := ω) (X := B) (Y := Bc) (fun t ↦ (hω t).symm)
  simp [Bc, hτ]

/-- Helper for Exercise 21.2.6: the affine-boundary hitting time, viewed as the real-valued random
variable `ω ↦ (τ ω).toReal`, is almost everywhere measurable. -/
theorem aemeasurable_brownianAffineBoundaryHittingTime_toReal
    (hB : IsBrownianMotion μ B) (a b : ℝ) :
    AEMeasurable (fun ω ↦ (brownianAffineBoundaryHittingTime B a b ω).toReal) μ := by
  let Bc := brownianPathContinuousVersion (μ := μ) (B := B) hB
  have hMeasBc : Measurable (brownianAffineBoundaryHittingTime Bc a b) := by
    -- Proof comment: once the Brownian paths are patched to be everywhere continuous, the
    -- measurable-time-slice hitting-time argument applies directly.
    refine measurable_brownianAffineBoundaryHittingTime_of_continuous
      (X := Bc) (a := a) (b := b) ?_ ?_
    · intro t
      have hBt : Measurable (B t) := (hB.stronglyMeasurable t).measurable
      have hN : MeasurableSet (brownianPathExceptionSet (μ := μ) (B := B) hB) :=
        brownianPathExceptionSet_measurable (μ := μ) (B := B) hB
      simpa [Bc, brownianPathContinuousVersion] using
        Measurable.piecewise hN measurable_const hBt
    · intro ω
      exact
        (brownianPathContinuousVersion_continuous (μ := μ) (B := B) hB ω).sub
          (continuous_const.mul continuous_subtype_val)
  have hAEMeasBc :
      AEMeasurable (fun ω ↦ (brownianAffineBoundaryHittingTime Bc a b ω).toReal) μ :=
    hMeasBc.aemeasurable.ennreal_toReal
  -- Proof comment: transfer almost-everywhere measurability back to the original Brownian motion
  -- through pathwise equality off the exceptional null set.
  exact AEMeasurable.congr hAEMeasBc
    (brownianAffineBoundaryHittingTime_toReal_ae_eq_continuousVersion
      (μ := μ) (B := B) (a := a) (b := b) hB).symm

/-- Helper for Exercise 21.2.6: a continuous path started below the boundary hits the level `b`
exactly when bounded rational times approximate `b` from below arbitrarily well. -/
private lemma affineLevelHit_iff_existsNatRatLowerApprox
    {f : NNReal → ℝ} {b : ℝ} (hcont : Continuous f) (h0 : f 0 < b) :
    (∃ t : NNReal, f t = b) ↔
      ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0, (q : ℝ) ≤ N ∧ b - (m + 1 : ℝ)⁻¹ ≤ f (q : NNReal) := by
  constructor
  · rintro ⟨t, ht⟩
    have ht_ne_zero : t ≠ 0 := by
      intro ht0
      have hEq : f 0 = b := by simpa [ht0] using ht
      have : b < b := by simpa [hEq] using h0
      exact lt_irrefl _ this
    have ht_pos_nn : 0 < t := by
      exact pos_iff_ne_zero.mpr ht_ne_zero
    have ht_pos : 0 < (t : ℝ) := by
      exact_mod_cast ht_pos_nn
    refine ⟨Nat.ceil (t : ℝ), ?_⟩
    intro m
    have hεpos : 0 < (m + 1 : ℝ)⁻¹ := by
      positivity
    -- Proof comment: continuity at the hit time lets us replace the exact hit by nearby rational
    -- times whose values stay within `(m + 1)⁻¹` of the boundary from below.
    rcases (Metric.continuousAt_iff.mp hcont.continuousAt) _ hεpos with ⟨δ, hδpos, hδ⟩
    let η : ℝ := min (δ / 2) ((t : ℝ) / 2)
    have hηpos : 0 < η := by
      dsimp [η]
      positivity
    obtain ⟨r, hr_left, hr_right⟩ : ∃ r : ℚ, (t : ℝ) - η < r ∧ r < (t : ℝ) := by
      exact exists_rat_btwn (by linarith)
    have hη_le_half : η ≤ (t : ℝ) / 2 := by
      dsimp [η]
      exact min_le_right _ _
    have hleft_pos : 0 < (t : ℝ) - η := by
      linarith
    have hr_pos : 0 < (r : ℝ) := lt_trans hleft_pos hr_left
    let q : ℚ≥0 := ⟨r, by exact_mod_cast hr_pos.le⟩
    have hq_le_N : (q : ℝ) ≤ Nat.ceil (t : ℝ) := by
      exact le_trans hr_right.le (Nat.le_ceil (t : ℝ))
    have hq_close_real : |((q : NNReal) : ℝ) - t| < δ := by
      rw [abs_of_nonpos]
      · have hη_le_deltaHalf : η ≤ δ / 2 := by
          dsimp [η]
          exact min_le_left _ _
        have hη_lt_delta : η < δ := by
          linarith
        have hsub_lt_eta : (t : ℝ) - (q : ℝ) < η := by
          change (t : ℝ) - (r : ℝ) < η
          linarith
        have hsub_lt_delta : (t : ℝ) - (q : ℝ) < δ := lt_trans hsub_lt_eta hη_lt_delta
        have hrewrite : -((((q : NNReal) : ℝ) - t)) = (t : ℝ) - (q : ℝ) := by
          have hq_coe : (((q : NNReal) : ℝ)) = (q : ℝ) := rfl
          rw [hq_coe]
          simp [sub_eq_add_neg, add_comm]
        rw [hrewrite]
        exact hsub_lt_delta
      · exact sub_nonpos.mpr hr_right.le
    have hq_close : dist (q : NNReal) t < δ := by
      simpa [NNReal.dist_eq] using hq_close_real
    have hq_value : |f (q : NNReal) - b| < (m + 1 : ℝ)⁻¹ := by
      simpa [Real.dist_eq, ht] using hδ hq_close
    refine ⟨q, hq_le_N, ?_⟩
    have hq_lower : -((m + 1 : ℝ)⁻¹) < f (q : NNReal) - b := (abs_lt.mp hq_value).1
    linarith
  · rintro ⟨N, hN⟩
    by_contra hhit
    have hlt : ∀ s ∈ Set.Icc (0 : NNReal) N, f s < b := by
      intro s hs
      by_contra hs_not_lt
      have hsb : b ≤ f s := le_of_not_gt hs_not_lt
      have hsgt : b < f s := by
        have hs_ne : f s ≠ b := by
          intro hs_eq
          exact hhit ⟨s, hs_eq⟩
        exact lt_of_le_of_ne hsb hs_ne.symm
      have hlevel : b ∈ Set.Icc (f 0) (f s) := ⟨le_of_lt h0, le_of_lt hsgt⟩
      obtain ⟨t, -, ht_eq⟩ :=
        (intermediate_value_Icc (a := (0 : NNReal)) (b := s) hs.1 hcont.continuousOn) hlevel
      exact hhit ⟨t, ht_eq⟩
    have hgap : ∀ s ∈ Set.Icc (0 : NNReal) N, 0 < b - f s := by
      intro s hs
      linarith [hlt s hs]
    -- Proof comment: compactness on `[0, N]` gives a uniform positive gap to `b`, which rules out
    -- the claimed rational lower approximations.
    obtain ⟨ε, hεpos, hεbound⟩ :=
      isCompact_Icc.exists_forall_le'
        (f := fun s : NNReal ↦ b - f s)
        (hf := (continuous_const.sub hcont).continuousOn)
        (a := (0 : ℝ))
        hgap
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hεpos
    rcases hN m with ⟨q, hqN, hqApprox⟩
    have hq_mem : (q : NNReal) ∈ Set.Icc (0 : NNReal) N := by
      constructor
      · positivity
      · exact_mod_cast hqN
    have hqGap : ε ≤ b - f (q : NNReal) := hεbound (q : NNReal) hq_mem
    have hqUpper : b - f (q : NNReal) ≤ (m + 1 : ℝ)⁻¹ := by
      linarith
    have hεle : ε ≤ (m + 1 : ℝ)⁻¹ := le_trans hqGap hqUpper
    exact (not_lt_of_ge hεle) (by simpa [one_div] using hm)

/-- Helper for Exercise 21.2.6: the finite-hit event admits a countable rational lower-approximation
normal form. -/
private def affineBoundaryRatApproxEvent
    (B : NNReal → Ω → ℝ) (a b : ℝ) : Set Ω :=
  {ω |
    ∃ N : ℕ, ∀ m : ℕ, ∃ q : ℚ≥0,
      (q : ℝ) ≤ N ∧ b - (m + 1 : ℝ)⁻¹ ≤ B q ω - a * (q : ℝ)}

/-- Helper for Exercise 21.2.6: the rational lower-approximation event is null measurable because
it is built from countably many deterministic-time Brownian marginals. -/
private lemma affineBoundaryRatApproxEvent_nullMeasurable
    (hB : IsBrownianMotion μ B) {a b : ℝ} :
    NullMeasurableSet (affineBoundaryRatApproxEvent B a b) μ := by
  let sectionEvent : ℕ → ℕ → ℚ≥0 → Set Ω := fun N m q ↦
    {ω | (q : ℝ) ≤ N ∧ b - (m + 1 : ℝ)⁻¹ ≤ B q ω - a * (q : ℝ)}
  let lowerApproxEvent : ℕ → ℕ → Set Ω := fun N m ↦
    ⋃ q : ℚ≥0, sectionEvent N m q
  let pathEvent : ℕ → Set Ω := fun N ↦
    ⋂ m : ℕ, lowerApproxEvent N m
  have hSectionNull : ∀ N m q, NullMeasurableSet (sectionEvent N m q) μ := by
    intro N m q
    by_cases hqN : (q : ℝ) ≤ N
    · have hEval : AEMeasurable (fun ω ↦ B q ω - a * (q : ℝ)) μ := by
        exact (hB.aemeasurable q).sub aemeasurable_const
      have hSection :
          sectionEvent N m q = {ω | b - (m + 1 : ℝ)⁻¹ ≤ B q ω - a * (q : ℝ)} := by
        ext ω
        constructor
        · intro hω
          exact hω.2
        · intro hω
          exact ⟨hqN, hω⟩
      rw [hSection]
      exact nullMeasurableSet_le aemeasurable_const hEval
    · have hSection : sectionEvent N m q = (∅ : Set Ω) := by
        ext ω
        constructor
        · intro hω
          exact (hqN hω.1).elim
        · intro hω
          exact False.elim hω
      rw [hSection]
      exact nullMeasurableSet_empty
  have hLowerApproxNull : ∀ N m, NullMeasurableSet (lowerApproxEvent N m) μ := by
    intro N m
    exact NullMeasurableSet.iUnion fun q ↦ hSectionNull N m q
  have hPathNull : ∀ N, NullMeasurableSet (pathEvent N) μ := by
    intro N
    exact NullMeasurableSet.iInter fun m ↦ hLowerApproxNull N m
  -- Proof comment: only countable unions and intersections remain after isolating the single-time
  -- inequalities.
  simpa [affineBoundaryRatApproxEvent, sectionEvent, lowerApproxEvent, pathEvent,
    Set.setOf_exists, Set.setOf_forall] using
    NullMeasurableSet.iUnion hPathNull

/-- Helper for Exercise 21.2.6: on almost every continuous Brownian path, finite affine-boundary
hitting is equivalent to the countable rational lower-approximation event. -/
private lemma brownianAffineBoundaryFiniteHitEvent_ae_eq_ratApprox
    (hB : IsBrownianMotion μ B) {a b : ℝ} (hb : 0 < b) :
    {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤} =ᵐ[μ]
      affineBoundaryRatApproxEvent B a b := by
  filter_upwards [hB.continuous_paths] with ω hωcont
  let f : NNReal → ℝ := fun t ↦ B t ω - a * (t : ℝ)
  have hcontDrift : Continuous f := by
    -- Proof comment: subtracting the deterministic affine drift preserves path continuity.
    exact hωcont.sub (continuous_const.mul continuous_subtype_val)
  have hzero : f 0 = 0 := by
    simpa [f] using congrFun hB.zero ω
  have hstart : f 0 < b := by
    simpa [hzero] using hb
  apply propext
  constructor
  · intro hω
    have hhit : ∃ t : NNReal, f t = b := by
      exact
        (brownianAffineBoundaryHittingTime_ne_top_iff_exists_eq
          (B := B) (a := a) (b := b) (ω := ω)).1 (ne_of_lt hω)
    -- Proof comment: the deterministic continuity lemma converts an exact hit into a countable
    -- family of rational lower approximations.
    simpa [affineBoundaryRatApproxEvent, f] using
      (affineLevelHit_iff_existsNatRatLowerApprox
        (f := f) (b := b) hcontDrift hstart).mp hhit
  · intro hω
    have hhit : ∃ t : NNReal, f t = b := by
      simpa [affineBoundaryRatApproxEvent, f] using
        (affineLevelHit_iff_existsNatRatLowerApprox
          (f := f) (b := b) hcontDrift hstart).mpr hω
    -- Proof comment: any realized affine hit forces the canonical hitting time to be finite.
    exact lt_top_iff_ne_top.mpr <|
      (brownianAffineBoundaryHittingTime_ne_top_iff_exists_eq
        (B := B) (a := a) (b := b) (ω := ω)).2 hhit

/-- Helper for Exercise 21.2.6: the finite-hit event is null measurable thanks to its countable
rational approximation description. -/
private lemma brownianAffineBoundaryFiniteHitEvent_nullMeasurable
    (hB : IsBrownianMotion μ B) {a b : ℝ} (hb : 0 < b) :
    NullMeasurableSet {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤} μ := by
  -- Proof comment: transport null measurability from the countable rational event along the AE
  -- equivalence on continuous Brownian paths.
  exact
    (affineBoundaryRatApproxEvent_nullMeasurable (μ := μ) (B := B) (a := a) (b := b) hB).congr
      (brownianAffineBoundaryFiniteHitEvent_ae_eq_ratApprox
        (μ := μ) (B := B) (a := a) (b := b) hB hb).symm

/-- Helper for Exercise 21.2.6: rewrite the Brownian-space integral as the Laplace integral
against the finite-hit pushforward law. -/
private lemma brownianAffineBoundaryLaplace_eq_integral_finiteHitMeasure
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} (hb : 0 < b) :
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam ω ∂μ =
      ∫ x : ℝ, Real.exp (-lam * x) ∂ brownianAffineBoundaryFiniteHitMeasure (μ := μ) B a b := by
  let s : Set Ω := {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
  let τr : Ω → ℝ := fun ω ↦ (brownianAffineBoundaryHittingTime B a b ω).toReal
  have hs_null : NullMeasurableSet s μ :=
    brownianAffineBoundaryFiniteHitEvent_nullMeasurable (μ := μ) (B := B) (a := a) (b := b) hB hb
  have hτr : AEMeasurable τr μ :=
    aemeasurable_brownianAffineBoundaryHittingTime_toReal (μ := μ) (B := B) hB a b
  have hExp_meas :
      AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (-lam * x))
        (brownianAffineBoundaryFiniteHitMeasure (μ := μ) B a b) :=
    (by
      have hCont : Continuous (fun x : ℝ ↦ Real.exp (-lam * x)) := by
        fun_prop
      exact hCont.aestronglyMeasurable)
  calc
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam ω ∂μ
        = ∫ ω in s, Real.exp (-lam * τr ω) ∂μ := by
            -- Proof comment: move the indicator defining the Laplace weight into a set integral
            -- over the finite-hit event.
            rw [brownianAffineBoundaryHittingTimeLaplaceWeight_def]
            simpa [s, τr] using
              (MeasureTheory.integral_indicator₀
                (μ := μ)
                (s := s)
                (f := fun ω : Ω ↦ Real.exp (-lam * τr ω))
                hs_null)
    _ = ∫ ω, Real.exp (-lam * τr ω) ∂μ.restrict s := by
          rfl
    _ = ∫ x : ℝ, Real.exp (-lam * x) ∂ brownianAffineBoundaryFiniteHitMeasure (μ := μ) B a b := by
          -- Proof comment: the finite-hit law is exactly the pushforward of `τ.toReal` under the
          -- restricted measure.
          symm
          rw [brownianAffineBoundaryFiniteHitMeasure]
          exact MeasureTheory.integral_map hτr.restrict hExp_meas

/-- Helper for Exercise 21.2.6: the affine-boundary Laplace weight is almost everywhere
measurable. -/
private lemma aemeasurable_brownianAffineBoundaryHittingTimeLaplaceWeight
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} (hb : 0 < b) :
    AEMeasurable (brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam) μ := by
  let τr : Ω → ℝ := fun ω ↦ (brownianAffineBoundaryHittingTime B a b ω).toReal
  have hτr : AEMeasurable τr μ :=
    aemeasurable_brownianAffineBoundaryHittingTime_toReal (μ := μ) (B := B) hB a b
  have hEvent :
      NullMeasurableSet {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤} μ :=
    brownianAffineBoundaryFiniteHitEvent_nullMeasurable
      (μ := μ) (B := B) (a := a) (b := b) hB hb
  have hExp :
      AEMeasurable (fun ω ↦ Real.exp (-lam * τr ω)) μ := by
    -- Proof comment: compose the almost-everywhere measurable hitting time with the continuous
    -- exponential kernel `x ↦ exp (-λ x)`.
    have hKernelMeas : Measurable (fun x : ℝ ↦ Real.exp (-lam * x)) := by
      have hKernelCont : Continuous (fun x : ℝ ↦ Real.exp (-lam * x)) := by
        fun_prop
      exact hKernelCont.measurable
    exact hKernelMeas.comp_aemeasurable hτr
  -- Proof comment: the Laplace weight is just the exponential kernel restricted to the
  -- null-measurable finite-hit event.
  simpa [brownianAffineBoundaryHittingTimeLaplaceWeight_def, τr] using hExp.indicator₀ hEvent

/-- Helper for Exercise 21.2.6: replacing Brownian motion by its continuous version leaves the
final Laplace weight unchanged almost everywhere. -/
private lemma brownianAffineBoundaryHittingTimeLaplaceWeight_ae_eq_continuousVersion
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} :
    brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam =ᵐ[μ]
      brownianAffineBoundaryHittingTimeLaplaceWeight
        (brownianPathContinuousVersion (μ := μ) (B := B) hB) a b lam := by
  let Bc := brownianPathContinuousVersion (μ := μ) (B := B) hB
  filter_upwards [brownianPathContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  have hτ :
      brownianAffineBoundaryHittingTime B a b ω =
        brownianAffineBoundaryHittingTime Bc a b ω :=
    brownianAffineBoundaryHittingTime_eq_of_forall_eq
      (a := a) (b := b) (ω := ω) (X := B) (Y := Bc) (fun t ↦ (hω t).symm)
  -- Proof comment: once the affine hitting times agree pointwise, both the indicator branch and
  -- the exponential branch of the Laplace weight become definitionally identical.
  by_cases hfin : brownianAffineBoundaryHittingTime B a b ω < ⊤
  · have hfinBc : brownianAffineBoundaryHittingTime Bc a b ω < ⊤ := by
      simpa [Bc, hτ] using hfin
    simp [brownianAffineBoundaryHittingTimeLaplaceWeight_def, Bc, hτ, hfinBc]
  · have hfinBc : ¬ brownianAffineBoundaryHittingTime Bc a b ω < ⊤ := by
      simpa [Bc, hτ] using hfin
    simp [brownianAffineBoundaryHittingTimeLaplaceWeight_def, Bc, hτ, hfinBc]

/-- Helper for Exercise 21.2.6: for continuous drifted paths, the stopped exponential at `τ ∧ T`
already has the exact hit-plus-miss normal form needed for the horizon limit. -/
private lemma affineBoundaryStoppedExponential_minConst_eq_hitWeight_add_missBranch
    {a b lam : ℝ} (hlam : 0 ≤ lam) {T : NNReal}
    (hcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ B t ω - a * (t : ℝ)) :
    let θ := a + Real.sqrt (a ^ 2 + 2 * lam)
    let τ := brownianAffineBoundaryHittingTime B a b
    stoppedValue
        (fun t : NNReal ↦ fun ω : Ω ↦
          Real.exp (θ * B t ω - (θ ^ 2 / 2) * (t : ℝ)))
        (fun ω ↦ min (τ ω) (T : ENNReal)) =
      fun ω ↦
        Real.exp (θ * b) *
            Set.indicator
              {ω' | τ ω' ≤ (T : ENNReal)}
              (fun ω' ↦ Real.exp (-lam * (τ ω').toReal)) ω +
          Set.indicator
            {ω' | (T : ENNReal) < τ ω'}
            (fun ω' ↦ Real.exp (θ * (B T ω' - a * (T : ℝ)) - lam * (T : ℝ))) ω := by
  dsimp
  let θ : ℝ := a + Real.sqrt (a ^ 2 + 2 * lam)
  let τ : Ω → ENNReal := brownianAffineBoundaryHittingTime B a b
  ext ω
  have hsplit :
      stoppedValue
          (fun t : NNReal ↦ fun ω' : Ω ↦ Real.exp (θ * B t ω' - (θ ^ 2 / 2) * (t : ℝ)))
          (fun ω' ↦ min (τ ω') (T : ENNReal)) ω =
        if τ ω ≤ (T : ENNReal) then
          Real.exp (θ * b - lam * (τ ω).toReal)
        else
          Real.exp (θ * (B T ω - a * (T : ℝ)) - lam * (T : ℝ)) := by
    simpa [θ, τ] using
      affineBoundaryStoppedExponential_minConst_eq_split
        (B := B) (a := a) (b := b) (lam := lam) (T := T) (ω := ω) hlam (hcont ω)
  by_cases hτT : τ ω ≤ (T : ENNReal)
  · -- Proof comment: on the hit branch, the miss indicator vanishes and the stopped value factors
    -- into `exp (θ b)` times the truncated Laplace weight.
    rw [if_pos hτT] at hsplit
    calc
      stoppedValue
          (fun t : NNReal ↦ fun ω' : Ω ↦ Real.exp (θ * B t ω' - (θ ^ 2 / 2) * (t : ℝ)))
          (fun ω' ↦ min (τ ω') (T : ENNReal)) ω
          = Real.exp (θ * b - lam * (τ ω).toReal) := hsplit
      _ = Real.exp (θ * b) * Real.exp (-lam * (τ ω).toReal) := by
            rw [show θ * b - lam * (τ ω).toReal = θ * b + (-lam * (τ ω).toReal) by ring]
            rw [Real.exp_add]
      _ =
          Real.exp (θ * b) *
              Set.indicator
                {ω' | τ ω' ≤ (T : ENNReal)}
                (fun ω' ↦ Real.exp (-lam * (τ ω').toReal)) ω +
            Set.indicator
              {ω' | (T : ENNReal) < τ ω'}
              (fun ω' ↦ Real.exp (θ * (B T ω' - a * (T : ℝ)) - lam * (T : ℝ))) ω := by
            simp [hτT, τ]
  · have hTτ : (T : ENNReal) < τ ω := lt_of_not_ge hτT
    -- Proof comment: on the miss branch, the hit indicator vanishes and only the deterministic
    -- horizon term remains.
    rw [if_neg hτT] at hsplit
    calc
      stoppedValue
          (fun t : NNReal ↦ fun ω' : Ω ↦ Real.exp (θ * B t ω' - (θ ^ 2 / 2) * (t : ℝ)))
          (fun ω' ↦ min (τ ω') (T : ENNReal)) ω
          = Real.exp (θ * (B T ω - a * (T : ℝ)) - lam * (T : ℝ)) := hsplit
      _ =
          Real.exp (θ * b) *
              Set.indicator
                {ω' | τ ω' ≤ (T : ENNReal)}
                (fun ω' ↦ Real.exp (-lam * (τ ω').toReal)) ω +
            Set.indicator
              {ω' | (T : ENNReal) < τ ω'}
              (fun ω' ↦ Real.exp (θ * (B T ω' - a * (T : ℝ)) - lam * (T : ℝ))) ω := by
            simp [hτT, hTτ, τ]

/-- Helper for Exercise 21.2.6: the positive-parameter Laplace transform follows from optional
sampling at the clipped affine-boundary hitting time on the continuous Brownian version. -/
private lemma brownianAffineBoundaryHittingTime_laplaceTransform_pos
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam) :
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam ω ∂μ =
      Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Bc := brownianPathContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianPathContinuousVersion_isBrownianMotion (μ := μ) (B := B) hB
  let ℱBc := Filtration.natural Bc hBc.stronglyMeasurable
  let τ : Ω → ENNReal := brownianAffineBoundaryHittingTime Bc a b
  let θ : ℝ := a + Real.sqrt (a ^ 2 + 2 * lam)
  let M : NNReal → Ω → ℝ :=
    fun t ω ↦ Real.exp (θ * Bc t ω - (θ ^ 2 / 2) * (t : ℝ))
  let G : ℕ → Ω → ℝ := fun n ω ↦
    Real.exp (θ * b) *
      Set.indicator
        {ω' | τ ω' ≤ (n : ENNReal)}
        (fun ω' ↦ Real.exp (-lam * (τ ω').toReal)) ω
  let R : ℕ → Ω → ℝ := fun n ω ↦
    Set.indicator
      {ω' | (n : ENNReal) < τ ω'}
      (fun ω' ↦ Real.exp (θ * (Bc n ω' - a * (n : ℝ)) - lam * (n : ℝ))) ω
  have hBc_cont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ Bc t ω - a * (t : ℝ) := by
    intro ω
    exact
      (brownianPathContinuousVersion_continuous (μ := μ) (B := B) hB ω).sub
        (continuous_const.mul continuous_subtype_val)
  have hM_mart : Martingale M ℱBc μ := by
    -- Proof comment: Exercise 21.2.3 provides the exponential martingale for the continuous
    -- Brownian version `Bc`.
    simpa [M, ℱBc, θ] using brownianStochasticExponential_martingale hBc θ
  have hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω := by
    intro ω
    -- Proof comment: the continuous Brownian version makes every exponential sample path
    -- continuous in time.
    have hBcω : Continuous fun t : NNReal ↦ Bc t ω := by
      simpa [Bc] using brownianPathContinuousVersion_continuous (μ := μ) (B := B) hB ω
    dsimp [M]
    exact Real.continuous_exp.comp
      ((continuous_const.mul hBcω).sub (continuous_const.mul continuous_subtype_val))
  have hτ_stop : IsStoppingTime ℱBc τ := by
    -- Proof comment: for the continuous version `Bc`, the affine hitting time is a genuine
    -- stopping time for the natural filtration.
    simpa [τ, ℱBc] using
      brownianAffineBoundaryHittingTime_isStoppingTime
        (B := Bc) (a := a) (b := b)
        (fun t ↦ hBc.stronglyMeasurable t) hBc_cont
  have hτ_meas : Measurable τ := hτ_stop.measurable'
  have hWeight0_int :
      Integrable (brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b 0) μ := by
    have hFinite_meas : MeasurableSet {ω | τ ω < ⊤} := by
      simpa [τ] using measurableSet_lt hτ_meas measurable_const
    -- Proof comment: the zero-parameter weight is just the indicator of the finite-hit event.
    rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
    simpa [τ] using (integrable_const (μ := μ) (1 : ℝ)).indicator hFinite_meas
  have hBound_int :
      Integrable
        (fun ω ↦ Real.exp (θ * b) * brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b 0 ω)
        μ := hWeight0_int.const_mul (Real.exp (θ * b))
  have hStoppedIntegral : ∀ n : ℕ,
      ∫ ω, stoppedValue M (fun ω' ↦ min (τ ω') (n : ENNReal)) ω ∂μ = 1 := by
    intro n
    calc
      ∫ ω, stoppedValue M (fun ω' ↦ min (τ ω') (n : ENNReal)) ω ∂μ
          = ∫ ω, M 0 ω ∂μ := by
              exact expected_stoppedValue_min_const_eq_initial hM_mart hM_cont hτ_stop n
      _ = ∫ ω, (1 : ℝ) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with ω
            have hzeroω : Bc 0 ω = 0 := by
              simpa [Bc] using congrFun hBc.zero ω
            simp [M, hzeroω]
      _ = 1 := by simp
  have hSplit :
      ∀ n : ℕ,
        stoppedValue M (fun ω' ↦ min (τ ω') (n : ENNReal)) =
          fun ω ↦ G n ω + R n ω := by
    intro n
    -- Proof comment: rewrite the clipped stopped exponential once into the exact hit-plus-miss
    -- normal form that survives the horizon limit.
    simpa [M, G, R, τ, θ] using
      affineBoundaryStoppedExponential_minConst_eq_hitWeight_add_missBranch
        (B := Bc) (a := a) (b := b) (lam := lam) (T := n) (le_of_lt hlam) hBc_cont
  have hG_meas : ∀ n : ℕ, AEStronglyMeasurable (G n) μ := by
    intro n
    have hKernel :
        AEMeasurable (fun ω ↦ Real.exp (-lam * (τ ω).toReal)) μ := by
      have hτr : AEMeasurable (fun ω ↦ (τ ω).toReal) μ := hτ_meas.aemeasurable.ennreal_toReal
      have hExpMeas : Measurable (fun x : ℝ ↦ Real.exp (-lam * x)) := by
        have hExpCont : Continuous (fun x : ℝ ↦ Real.exp (-lam * x)) := by
          fun_prop
        exact hExpCont.measurable
      exact hExpMeas.comp_aemeasurable hτr
    have hLe_meas : MeasurableSet {ω | τ ω ≤ (n : ENNReal)} := by
      exact hτ_stop.measurableSpace_le _ (hτ_stop.measurableSet_le' n)
    exact (hKernel.aestronglyMeasurable.indicator hLe_meas).const_mul _
  have hG_bound :
      ∀ n : ℕ, ∀ᵐ ω ∂μ,
        ‖G n ω‖ ≤
          Real.exp (θ * b) * brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b 0 ω := by
    intro n
    filter_upwards with ω
    by_cases hτn : τ ω ≤ (n : ENNReal)
    · have hfin : τ ω < ⊤ := lt_of_le_of_lt hτn (by simp)
      have hExp_nonneg : 0 ≤ Real.exp (-lam * (τ ω).toReal) := by positivity
      have hExp_le_one : Real.exp (-lam * (τ ω).toReal) ≤ 1 := by
        have hnonpos : -lam * (τ ω).toReal ≤ 0 := by
          have hτ_nonneg : 0 ≤ (τ ω).toReal := ENNReal.toReal_nonneg
          nlinarith
        simpa using Real.exp_le_one_iff.mpr hnonpos
      have hθb_nonneg : 0 ≤ Real.exp (θ * b) := by positivity
      have hWeight0_eq :
          brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b 0 ω = 1 := by
        rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
        simp [τ, hfin]
      rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
      rw [show ‖G n ω‖ = Real.exp (θ * b) * Real.exp (-lam * (τ ω).toReal) by
        simp [G, hτn, hfin, Real.norm_of_nonneg, hθb_nonneg, hExp_nonneg]]
      simpa [τ, hfin] using mul_le_mul_of_nonneg_left hExp_le_one hθb_nonneg
    · have hRhs_nonneg :
          0 ≤ Real.exp (θ * b) * brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b 0 ω := by
        have hWeight0_nonneg :
            0 ≤ brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b 0 ω := by
          rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
          by_cases hfin : τ ω < ⊤ <;> simp [τ, hfin]
        positivity
      simp [G, hτn, hRhs_nonneg]
  have hG_int : ∀ n : ℕ, Integrable (G n) μ := by
    intro n
    refine Integrable.mono' hBound_int (hG_meas n) ?_
    exact hG_bound n
  have hG_tendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ ↦ G n ω) atTop
          (𝓝 (Real.exp (θ * b) *
            brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω)) := by
    filter_upwards with ω
    by_cases hfin : τ ω < ⊤
    · rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hfin) with ⟨t, ht⟩
      have hτ_eq : τ ω = (t : ENNReal) := by
        simpa using ht.symm
      have hEventually :
          ∀ᶠ n : ℕ in atTop,
            G n ω =
              Real.exp (θ * b) * brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨Nat.ceil (t : ℝ), ?_⟩
        intro n hn
        have htn_real : (t : ℝ) ≤ n := le_trans (Nat.le_ceil (t : ℝ)) (by exact_mod_cast hn)
        have htn : (t : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast htn_real
        have hτn : τ ω ≤ (n : ENNReal) := by simpa [hτ_eq] using htn
        simp [G, brownianAffineBoundaryHittingTimeLaplaceWeight_def, τ, hτn, hfin]
      exact Tendsto.congr' (hEventually.mono fun n hn ↦ hn.symm) tendsto_const_nhds
    · have hEventually :
          ∀ᶠ n : ℕ in atTop,
            G n ω =
              Real.exp (θ * b) * brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω := by
        refine Filter.Eventually.of_forall ?_
        intro n
        have hτn : ¬ τ ω ≤ (n : ENNReal) := by
          intro hτn
          exact hfin (lt_of_le_of_lt hτn (by simp))
        simp [G, brownianAffineBoundaryHittingTimeLaplaceWeight_def, τ, hfin, hτn]
      exact Tendsto.congr' (hEventually.mono fun n hn ↦ hn.symm) tendsto_const_nhds
  have hG_integral_tendsto :
      Tendsto (fun n : ℕ ↦ ∫ ω, G n ω ∂μ) atTop
        (𝓝 (∫ ω,
          Real.exp (θ * b) * brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω ∂μ)) := by
    -- Proof comment: dominated convergence handles the truncated hit branch once it is expressed
    -- in the exact indicator normal form.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun ω ↦
        Real.exp (θ * b) * brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b 0 ω)
      hG_meas hBound_int hG_bound hG_tendsto
  have hR_meas : ∀ n : ℕ, AEStronglyMeasurable (R n) μ := by
    intro n
    have hTermMeas :
        Measurable (fun ω ↦ Real.exp (θ * (Bc n ω - a * (n : ℝ)) - lam * (n : ℝ))) := by
      have hBc_meas : Measurable (Bc n) := (hBc.stronglyMeasurable n).measurable
      exact
        Real.continuous_exp.measurable.comp
          ((measurable_const.mul (hBc_meas.sub measurable_const)).sub measurable_const)
    have hGt_meas : MeasurableSet {ω | (n : ENNReal) < τ ω} := by
      exact measurableSet_lt measurable_const hτ_meas
    exact (hTermMeas.aemeasurable.aestronglyMeasurable.indicator hGt_meas)
  have hR_int : ∀ n : ℕ, Integrable (R n) μ := by
    intro n
    refine Integrable.mono' (g := fun _ : Ω ↦ Real.exp (θ * b - lam * (n : ℝ)))
      (integrable_const _) (hR_meas n) ?_
    filter_upwards with ω
    by_cases hmiss : (n : ENNReal) < τ ω
    · have hbound :=
        affineBoundaryMissBranch_bound
          (μ := μ) (B := Bc) hBc (a := a) (b := b) (lam := lam) hb hlam
          (T := n) (ω := ω) (hBc_cont ω) hmiss
      have hterm_nonneg :
          0 ≤ Real.exp (θ * (Bc n ω - a * (n : ℝ)) - lam * (n : ℝ)) := by positivity
      have hR_eq :
          R n ω = Real.exp (θ * (Bc n ω - a * (n : ℝ)) - lam * (n : ℝ)) := by
        simp [R, hmiss]
      rw [hR_eq, Real.norm_of_nonneg hterm_nonneg]
      exact hbound
    · have hconst_nonneg : 0 ≤ Real.exp (θ * b - lam * (n : ℝ)) := by positivity
      simp [R, hmiss, hconst_nonneg]
  have hR_nonneg : ∀ n : ℕ, 0 ≤ ∫ ω, R n ω ∂μ := by
    intro n
    refine integral_nonneg_of_ae ?_
    filter_upwards with ω
    by_cases hmiss : (n : ENNReal) < τ ω
    · have hterm_nonneg :
          0 ≤ Real.exp (θ * (Bc n ω - a * (n : ℝ)) - lam * (n : ℝ)) := by positivity
      simp [R, hmiss, hterm_nonneg]
    · simp [R, hmiss]
  have hR_le : ∀ n : ℕ, ∫ ω, R n ω ∂μ ≤ Real.exp (θ * b - lam * (n : ℝ)) := by
    intro n
    calc
      ∫ ω, R n ω ∂μ ≤ ∫ ω, Real.exp (θ * b - lam * (n : ℝ)) ∂μ := by
        refine integral_mono_ae (hR_int n) (integrable_const _) ?_
        filter_upwards with ω
        by_cases hmiss : (n : ENNReal) < τ ω
        · simpa [R, hmiss] using
            (affineBoundaryMissBranch_bound
              (μ := μ) (B := Bc) hBc (a := a) (b := b) (lam := lam) hb hlam
              (T := n) (ω := ω) (hBc_cont ω) hmiss)
        · have hconst_nonneg : 0 ≤ Real.exp (θ * b - lam * (n : ℝ)) := by positivity
          simp [R, hmiss, hconst_nonneg]
      _ = Real.exp (θ * b - lam * (n : ℝ)) := by simp
  have hScalar_tendsto :
      Tendsto (fun n : ℕ ↦ Real.exp (θ * b - lam * (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    have hnegExp :
        Tendsto (fun n : ℕ ↦ Real.exp (-lam * (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      refine Real.tendsto_exp_atBot.comp ?_
      simpa [mul_comm] using
        (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (show -lam < 0 by linarith))
    have hRewrite :
        (fun n : ℕ ↦ Real.exp (θ * b - lam * (n : ℝ))) =
          fun n : ℕ ↦ Real.exp (θ * b) * Real.exp (-lam * (n : ℝ)) := by
      funext n
      rw [show θ * b - lam * (n : ℝ) = θ * b + (-lam * (n : ℝ)) by ring, Real.exp_add]
    rw [hRewrite]
    simpa using Tendsto.const_mul (Real.exp (θ * b)) hnegExp
  have hR_tendsto :
      Tendsto (fun n : ℕ ↦ ∫ ω, R n ω ∂μ) atTop (𝓝 (0 : ℝ)) := by
    -- Proof comment: the miss branch is squeezed between `0` and a scalar exponential envelope
    -- that decays because `λ > 0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hScalar_tendsto ?_ ?_
    · intro n
      exact hR_nonneg n
    · intro n
      exact hR_le n
  have hSplitIntegralEq : ∀ n : ℕ, ∫ ω, G n ω ∂μ + ∫ ω, R n ω ∂μ = 1 := by
    intro n
    calc
      ∫ ω, G n ω ∂μ + ∫ ω, R n ω ∂μ = ∫ ω, G n ω + R n ω ∂μ := by
        symm
        exact integral_add (hG_int n) (hR_int n)
      _ = 1 := by
        simpa [hSplit n] using hStoppedIntegral n
  have hSum_const :
      Tendsto (fun n : ℕ ↦ ∫ ω, G n ω ∂μ + ∫ ω, R n ω ∂μ) atTop (𝓝 (1 : ℝ)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact Filter.Eventually.of_forall fun n ↦ (hSplitIntegralEq n).symm
  have hBc_identity :
      Real.exp (θ * b) *
          (∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω ∂μ) = 1 := by
    have hSum_limit :
        Tendsto (fun n : ℕ ↦ ∫ ω, G n ω ∂μ + ∫ ω, R n ω ∂μ) atTop
          (𝓝
            (Real.exp (θ * b) *
                (∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω ∂μ) +
              0)) := by
      simpa [integral_const_mul] using hG_integral_tendsto.add hR_tendsto
    simpa using tendsto_nhds_unique hSum_limit hSum_const
  have hBc_formula :
      ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω ∂μ =
        Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := by
    have hExp_ne : Real.exp (θ * b) ≠ 0 := Real.exp_ne_zero _
    apply (mul_left_cancel₀ hExp_ne)
    calc
      Real.exp (θ * b) *
          (∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω ∂μ) = 1 :=
        hBc_identity
      _ = Real.exp (θ * b) * Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := by
            calc
              1 = Real.exp ((θ * b) + (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam))) := by
                    have hzero :
                        (θ * b) + (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) = 0 := by
                      dsimp [θ]
                      ring
                    rw [hzero]
                    simp
              _ = Real.exp (θ * b) * Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := by
                    rw [Real.exp_add]
  calc
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam ω ∂μ
        =
          ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight Bc a b lam ω ∂μ := by
            exact integral_congr_ae <|
              brownianAffineBoundaryHittingTimeLaplaceWeight_ae_eq_continuousVersion
                (μ := μ) (B := B) (a := a) (b := b) (lam := lam) hB
    _ = Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := hBc_formula

/-- Helper for Exercise 21.2.6: the zero-parameter case is the limit of the positive-parameter
Laplace transform. -/
private lemma brownianAffineBoundaryHittingTime_laplaceTransform_zero
    (hB : IsBrownianMotion μ B) {a b : ℝ} (hb : 0 < b) :
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 ω ∂μ =
      Real.exp (-b * a - b * Real.sqrt (a ^ 2)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let lamSeq : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hLamSeq_zero : Tendsto lamSeq atTop (𝓝 (0 : ℝ)) := by
    have hNat :
        Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa [lamSeq, one_div] using tendsto_inv_atTop_zero.comp hNat
  have hWeight0_int :
      Integrable (brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0) μ := by
    have hFinite_null :
        NullMeasurableSet {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤} μ :=
      brownianAffineBoundaryFiniteHitEvent_nullMeasurable
        (μ := μ) (B := B) (a := a) (b := b) hB hb
    -- Proof comment: on the original Brownian motion, the zero-parameter weight is the
    -- null-measurable indicator of the finite-hit event.
    rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
    exact (integrable_const (μ := μ) (1 : ℝ)).indicator₀ hFinite_null
  have hWeight_meas :
      ∀ n : ℕ, AEStronglyMeasurable (brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n))
        μ := by
    intro n
    exact
      (aemeasurable_brownianAffineBoundaryHittingTimeLaplaceWeight
        (μ := μ) (B := B) hB (a := a) (b := b) (lam := lamSeq n) hb).aestronglyMeasurable
  have hWeight_bound :
      ∀ n : ℕ, ∀ᵐ ω ∂μ,
        ‖brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n) ω‖ ≤
          brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 ω := by
    intro n
    filter_upwards with ω
    by_cases hfin : brownianAffineBoundaryHittingTime B a b ω < ⊤
    · have hlamSeq_nonneg : 0 ≤ lamSeq n := by
        dsimp [lamSeq]
        positivity
      have hExp_nonneg :
          0 ≤
            Real.exp
              (-(lamSeq n) * (brownianAffineBoundaryHittingTime B a b ω).toReal) := by positivity
      have hExp_le_one :
          Real.exp
              (-(lamSeq n) * (brownianAffineBoundaryHittingTime B a b ω).toReal) ≤ 1 := by
        have hτ_nonneg : 0 ≤ (brownianAffineBoundaryHittingTime B a b ω).toReal :=
          ENNReal.toReal_nonneg
        have hprod_nonneg :
            0 ≤ lamSeq n * (brownianAffineBoundaryHittingTime B a b ω).toReal := by
          exact mul_nonneg hlamSeq_nonneg hτ_nonneg
        have hnonpos :
            -(lamSeq n) * (brownianAffineBoundaryHittingTime B a b ω).toReal ≤ 0 := by
          nlinarith
        simpa using Real.exp_le_one_iff.mpr hnonpos
      have hWeight0_eq :
          brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 ω = 1 := by
        rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
        simp [hfin]
      rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
      rw [show
          ‖brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n) ω‖ =
            Real.exp (-(lamSeq n) * (brownianAffineBoundaryHittingTime B a b ω).toReal) by
            simp [brownianAffineBoundaryHittingTimeLaplaceWeight_def, hfin, Real.norm_of_nonneg,
              hExp_nonneg]]
      simpa [hfin] using hExp_le_one
    · simp [brownianAffineBoundaryHittingTimeLaplaceWeight_def,
      brownianAffineBoundaryHittingTimeLaplaceWeight_zero, hfin]
  have hWeight_tendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ ↦ brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n) ω)
          atTop (𝓝 (brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 ω)) := by
    filter_upwards with ω
    by_cases hfin : brownianAffineBoundaryHittingTime B a b ω < ⊤
    · have hExp_tendsto :
          Tendsto
            (fun n : ℕ ↦
              Real.exp (-(lamSeq n) * (brownianAffineBoundaryHittingTime B a b ω).toReal))
            atTop (𝓝 (1 : ℝ)) := by
        have hCont :
            Continuous
              (fun x : ℝ ↦
                Real.exp (-(x) * (brownianAffineBoundaryHittingTime B a b ω).toReal)) := by
          fun_prop
        simpa [lamSeq] using hCont.continuousAt.tendsto.comp hLamSeq_zero
      have hEventually :
          ∀ᶠ n : ℕ in atTop,
            brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n) ω =
              Real.exp (-(lamSeq n) * (brownianAffineBoundaryHittingTime B a b ω).toReal) := by
        exact Filter.Eventually.of_forall fun n ↦ by
          simp [brownianAffineBoundaryHittingTimeLaplaceWeight_def, hfin]
      refine Tendsto.congr' (hEventually.mono fun n hn ↦ hn.symm) ?_
      simpa [brownianAffineBoundaryHittingTimeLaplaceWeight_zero, hfin] using hExp_tendsto
    · have hEventually :
          ∀ᶠ n : ℕ in atTop,
            brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n) ω = 0 := by
        exact Filter.Eventually.of_forall fun n ↦ by
          simp [brownianAffineBoundaryHittingTimeLaplaceWeight_def, hfin]
      refine Tendsto.congr' (hEventually.mono fun n hn ↦ hn.symm) ?_
      simpa [brownianAffineBoundaryHittingTimeLaplaceWeight_zero, hfin] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hIntegral_tendsto :
      Tendsto
        (fun n : ℕ ↦ ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n) ω ∂μ)
        atTop
        (𝓝 (∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 ω ∂μ)) := by
    -- Proof comment: dominated convergence handles the parameter limit once the finite-hit
    -- indicator is fixed at `λ = 0`.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0)
      hWeight_meas hWeight0_int hWeight_bound hWeight_tendsto
  have hClosedForm_tendsto :
      Tendsto
        (fun n : ℕ ↦
          Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lamSeq n)))
        atTop
        (𝓝 (Real.exp (-b * a - b * Real.sqrt (a ^ 2)))) := by
    have hCont :
        Continuous fun x : ℝ ↦ Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * x)) := by
      fun_prop
    simpa [lamSeq] using hCont.continuousAt.tendsto.comp hLamSeq_zero
  have hPositiveBranch :
      Tendsto
        (fun n : ℕ ↦ ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b (lamSeq n) ω ∂μ)
        atTop
        (𝓝 (Real.exp (-b * a - b * Real.sqrt (a ^ 2)))) := by
    refine Tendsto.congr' ?_ hClosedForm_tendsto
    exact Filter.Eventually.of_forall fun n ↦
      (brownianAffineBoundaryHittingTime_laplaceTransform_pos
        (μ := μ) (B := B) hB (a := a) (b := b) (lam := lamSeq n) hb (by
          dsimp [lamSeq]
          positivity)).symm
  exact tendsto_nhds_unique hIntegral_tendsto hPositiveBranch

-- Proof sketch: rewrite the finite-hit Laplace weight through the deterministic-horizon crossing
-- formula for the drifted path `t ↦ B t - a t`, identify the resulting density on `(0, ∞)`, and
-- evaluate the Laplace integral analytically.
/-- Exercise 21.2.6 (1): for Brownian motion `B`, if `b > 0` and `τ` is the first time with
`B_t = a t + b`, then the Laplace transform of `τ`, interpreted as `0` on the event `{τ = ∞}`,
is `exp (-b a - b sqrt (a^2 + 2 λ))`. -/
theorem brownianAffineBoundaryHittingTime_laplaceTransform
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) :
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam ω ∂μ =
      Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := by
  by_cases hlam_pos : 0 < lam
  · -- Route correction: the dead finite-hit-law endgame is gone; the positive branch is now the
    -- clipped optional-sampling calculation on the continuous Brownian version.
    exact brownianAffineBoundaryHittingTime_laplaceTransform_pos
      (μ := μ) (B := B) hB (a := a) (b := b) (lam := lam) hb hlam_pos
  · have hlam_zero : lam = 0 := by
      linarith
    -- Proof comment: the `λ = 0` branch is the limit of the already established positive branch.
    simpa [hlam_zero] using
      brownianAffineBoundaryHittingTime_laplaceTransform_zero
        (μ := μ) (B := B) hB (a := a) (b := b) hb

-- Proof sketch: specialize part (1) at `λ = 0`. Then the Laplace weight reduces to the indicator
-- of `{τ < ∞}`, and `sqrt (a ^ 2) = |a|`, so the right-hand side becomes `1` when `a ≤ 0` and
-- `exp (-2 * b * a)` when `a > 0`, equivalently `min 1 (exp (-2 * b * a))`.
/-- Exercise 21.2.6 (2): consequently, the probability that the affine boundary `t ↦ a t + b` is
ever hit is `min (1, exp (-2 b a))`. -/
theorem brownianAffineBoundaryHittingTime_lt_top_prob
    (hB : IsBrownianMotion μ B) {a b : ℝ} (hb : 0 < b) :
    μ {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤} =
      ENNReal.ofReal (min 1 (Real.exp (-2 * b * a))) := by
  let s : Set Ω := {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
  have hs_null : NullMeasurableSet s μ :=
    brownianAffineBoundaryFiniteHitEvent_nullMeasurable (μ := μ) (B := B) (a := a) (b := b) hB hb
  have hIndicatorIntegral :
      ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 ω ∂μ = μ.real s := by
    calc
      ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b 0 ω ∂μ
          = ∫ ω, Set.indicator s (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              -- Proof comment: at `λ = 0`, the Laplace weight is exactly the indicator of finite
              -- hitting.
              rw [brownianAffineBoundaryHittingTimeLaplaceWeight_zero]
      _ = ∫ ω in s, (1 : ℝ) ∂μ := by
            -- Proof comment: `integral_indicator₀` moves the indicator into a set integral for a
            -- null measurable event.
            simpa using
              (MeasureTheory.integral_indicator₀
                (μ := μ) (s := s) (f := fun _ : Ω ↦ (1 : ℝ)) hs_null)
      _ = μ.real s := by
            -- Proof comment: the set integral of the constant `1` is the real-valued mass.
            simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := s))
  have hLaplaceZero :=
    brownianAffineBoundaryHittingTime_laplaceTransform
      (μ := μ) (B := B) hB (a := a) (b := b) (lam := 0) hb (by positivity)
  rw [hIndicatorIntegral] at hLaplaceZero
  have hClosedForm : μ.real s = min 1 (Real.exp (-2 * b * a)) := by
    calc
      μ.real s = Real.exp (-b * a - b * Real.sqrt (a ^ 2)) := by
        simpa using hLaplaceZero
      _ = min 1 (Real.exp (-2 * b * a)) := by
        exact brownianAffineBoundaryHittingTime_zeroParameter_closedForm hb
  have hμs_ne_top : μ s ≠ ∞ := by
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    exact measure_ne_top μ s
  -- Proof comment: convert the real-valued mass back to the ambient `ENNReal` measure.
  calc
    μ s = ENNReal.ofReal (μ.real s) := by
      simpa using (ENNReal.ofReal_toReal hμs_ne_top).symm
    _ = ENNReal.ofReal (min 1 (Real.exp (-2 * b * a))) := by
      rw [hClosedForm]

end BrownianMotionExercise

end ProbabilityTheory
