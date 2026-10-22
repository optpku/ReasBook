/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : TimeFiltration}
variable {M A : NNReal → Ω → ℝ} {τ τ₀ : Ω → ENNReal}

-- Route correction: this file only needs the pre-21.64 stopping and square-variation API from
-- `Theorem_21_70`, so we internalize that stable layer here instead of importing the broken
-- `Items.Chap21.Theorem_21_70` module graph.
/-- A continuous square-variation process of a continuous local martingale `M` is an adapted
real-valued process `A` starting at `0`, with continuous increasing sample paths, such that
`M² - A` is a local martingale. -/
structure IsContinuousSquareVariationProcess
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (M A : NNReal → Ω → ℝ) : Prop where
  zero : A 0 = 0
  adapted : Adapted ℱ A
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ A t ω)
  monotone : ∀ ω : Ω, Monotone (fun t : NNReal ↦ A t ω)
  local_martingale_sq_sub :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω ^ 2 - A t ω)

/-- Helper for Theorem 21.75: deterministic pathwise boundedness upgrades to the bounded-in-time
almost-sure owner used by Remark 21.68. -/
lemma boundedInTimeAe_of_boundedProcess
    {X : NNReal → Ω → ℝ} (hbounded : IsBoundedProcess X) :
    BoundedInTimeAe μ X := by
  rcases hbounded with ⟨C, _, hC⟩
  exact ⟨C, Filter.Eventually.of_forall fun ω t ↦ hC t ω⟩

omit mΩ in
/-- Helper for Theorem 21.75: stopping preserves deterministic pathwise boundedness. -/
lemma isBoundedProcess_stoppedProcess
    {X : NNReal → Ω → ℝ} (hbounded : IsBoundedProcess X) {σ : Ω → ENNReal} :
    IsBoundedProcess (stoppedProcess X σ) := by
  rcases hbounded with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ω
  -- Proof comment: a stopped value is the original process at the clipped time
  -- `min t σ(ω)`.
  simpa [stoppedProcess] using hC ((min (t : ENNReal) (σ ω)).untopA) ω

/-- Helper for Theorem 21.75: stopping a continuous sample path keeps it continuous. -/
lemma continuous_stoppedProcess_of_continuous
    {X : NNReal → Ω → ℝ} (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → ENNReal} :
    ∀ ω : Ω, Continuous fun t : NNReal ↦ stoppedProcess X σ t ω := by
  intro ω
  have hfinite : ∀ t : NNReal, min (t : ENNReal) (σ ω) ≠ ∞ := fun t ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  let clipped : NNReal → {s : ENNReal | s ≠ ∞} := fun t ↦
    ⟨min (t : ENNReal) (σ ω), hfinite t⟩
  have hclipped : Continuous clipped := by
    -- Proof comment: the clipped time is the minimum of the identity path and the constant level
    -- `σ ω`, viewed inside the finite part of `ENNReal`.
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
  -- Proof comment: `stoppedProcess` is the original path precomposed with the clipped time.
  rw [hEq]
  exact (hX_cont ω).comp htime

/-- Helper for Theorem 21.75: deterministic boundedness gives uniform integrability for the whole
time-indexed family. -/
lemma uniformIntegrable_of_boundedProcess
    {X : NNReal → Ω → ℝ} (hX_meas : ∀ t : NNReal, AEStronglyMeasurable (X t) μ)
    (hbounded : IsBoundedProcess X) :
    UniformIntegrable X 1 μ := by
  rcases hbounded with ⟨C, hC_nonneg, hC⟩
  let g : Ω → ℝ := fun _ ↦ C + 1
  have hg : Integrable g μ := integrable_const (C + 1)
  have hdom : ∀ t : NNReal, ∀ᵐ ω ∂μ, |X t ω| ≤ g ω := by
    intro t
    exact Filter.Eventually.of_forall fun ω ↦ le_trans (hC t ω) (by simp [g])
  have hconst : UniformIntegrable (fun _ : NNReal ↦ g) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.2 hg)
  refine ⟨hX_meas, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδ_bound⟩ := hconst.2.1 hε
    refine ⟨δ, hδ, fun t s hs hμs ↦ ?_⟩
    refine (eLpNorm_mono_ae_real ?_).trans (hδ_bound t s hs hμs)
    filter_upwards [hdom t] with ω hω
    by_cases hmem : ω ∈ s
    · simpa [Set.indicator_of_mem, hmem] using hω
    · simp [Set.indicator_of_notMem, hmem]
  · rcases hconst.2.2 with ⟨K, hK⟩
    refine ⟨K, fun t ↦ ?_⟩
    exact (eLpNorm_mono_ae_real (hdom t)).trans (hK t)

/-- Helper for Theorem 21.75: clipping the bounded stop `σ ∧ t` again at the deterministic time
`s ≤ t` recovers the time-`s` marginal of `X^σ`. -/
lemma stoppedValue_min_const_min_eq_stoppedProcess
    {X : NNReal → Ω → ℝ} {σ : Ω → ENNReal} {s t : NNReal} (hst : s ≤ t) :
    stoppedValue X (fun ω ↦ min (s : ENNReal) (min (σ ω) (t : ENNReal))) =
      stoppedProcess X σ s := by
  ext ω
  rw [stoppedProcess_eq_stoppedValue_apply (u := X) (τ := σ) (i := s)]
  change X (min (s : ENNReal) (min (σ ω) (t : ENNReal))).untopA ω =
    X (min (s : ENNReal) (σ ω)).untopA ω
  have hst' : (s : ENNReal) ≤ (t : ENNReal) := by
    exact_mod_cast hst
  have hmin : min (s : ENNReal) (min (σ ω) (t : ENNReal)) = min (s : ENNReal) (σ ω) := by
    calc
      min (s : ENNReal) (min (σ ω) (t : ENNReal)) =
          min (min (s : ENNReal) (σ ω)) (t : ENNReal) := by
            rw [min_assoc]
      _ = min (s : ENNReal) (σ ω) := by
            rw [min_eq_left (le_trans (min_le_left _ _) hst')]
  -- Proof comment: after reducing the nested minimum to the canonical `s ∧ σ`, both sides are
  -- the same stopped value.
  simpa [hmin]

/-- Helper for Theorem 21.75: the bounded stop `σ ∧ t` is exactly the time-`t` slice of the
stopped process `X^σ`. -/
lemma stoppedValue_min_const_eq_stoppedProcess
    {X : NNReal → Ω → ℝ} {σ : Ω → ENNReal} {t : NNReal} :
    stoppedValue X (fun ω ↦ min (σ ω) (t : ENNReal)) =
      stoppedProcess X σ t := by
  ext ω
  change X (min (σ ω) (t : ENNReal)).untopA ω =
    X (min (t : ENNReal) (σ ω)).untopA ω
  -- Proof comment: both sides evaluate `X` at the same clipped time, up to commutativity of
  -- `min`.
  rw [min_comm]

/-- Helper for Theorem 21.75: dyadic ceiling approximation of a finite nonnegative random time. -/
def dyadicCeilApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

/-- Helper for Theorem 21.75: the dyadic ceiling event `{dyadicCeilApprox n τ ≤ t}` rewrites as
the original stopping event at the dyadic predecessor of `t`. -/
lemma dyadicCeilApprox_event_le_eq (n : ℕ) (τ : Ω → NNReal) (t : NNReal) :
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
      -- Proof comment: the dyadic mesh denominator is strictly positive.
      dsimp [c]
      positivity
    have h_div :
        dyadicCeilApprox n τ ω ≤ t ↔
          (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t := by
      -- Proof comment: multiply by the positive dyadic scale to remove the denominator.
      dsimp [dyadicCeilApprox, c]
      rw [div_le_iff₀ hc_pos]
      simpa [c, mul_comm]
    have h_ceil_floor :
        (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t ↔
          Nat.ceil (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
      constructor
      · intro h
        have hreal : ((Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℕ) : ℝ) ≤ (((c * t : NNReal) : ℝ)) := by
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
    have h_floor_div :
        Nat.ceil (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) ↔
          τ ω ≤ (Nat.floor (((c * t : NNReal) : ℝ)) : NNReal) / c := by
      constructor
      · intro h
        have hreal : (((c * τ ω : NNReal) : ℝ)) ≤ Nat.floor (((c * t : NNReal) : ℝ)) := by
          exact (Nat.ceil_le.mp h)
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
    -- Proof comment: the dyadic ceiling only asks whether `τ` already fell below the latest mesh
    -- point not exceeding `t`.
    exact h_div.trans (h_ceil_floor.trans h_floor_div)
  exact_mod_cast hbody

/-- Helper for Theorem 21.75: dyadic ceiling approximations of `NNReal`-valued stopping times are
still stopping times. -/
lemma dyadicCeilApprox_isStoppingTime {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal) := by
  intro t
  let q : NNReal :=
    ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) / ((2 : NNReal) ^ n))
  have hpow_pos : 0 < (2 : NNReal) ^ n := by
    -- Proof comment: the dyadic scale is positive, so dividing by it preserves order.
    positivity
  have hq_le_t : q ≤ t := by
    -- Proof comment: the dyadic predecessor never exceeds the original threshold.
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
  -- Proof comment: rewrite the dyadic event through the original stopping time and then move it
  -- down along the filtration monotonicity `q ≤ t`.
  simpa [dyadicCeilApprox_event_le_eq (n := n) (τ := τ) (t := t)] using
    (ℱ.mono hq_le_t) _ (hτ.measurableSet_le q)

/-- Helper for Theorem 21.75: every dyadic ceiling approximation has countable range. -/
lemma dyadicCeilApprox_countableRange (n : ℕ) (τ : Ω → NNReal) :
    (Set.range fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal)).Countable := by
  refine
    ((Set.countable_range
      fun k : ℕ ↦ ((((k : NNReal) / ((2 : NNReal) ^ n)) : NNReal) : ENNReal))).mono ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ), ?_⟩
  simp [dyadicCeilApprox]

/-- Helper for Theorem 21.75: a dyadic ceiling overshoots a deterministic upper bound by at most
one mesh size. -/
lemma dyadicCeilApprox_le_add_mesh
    (m : ℕ) {τ : Ω → NNReal} {T : NNReal} (hτ_le : ∀ ω, τ ω ≤ T) :
    ∀ ω, dyadicCeilApprox m τ ω ≤ T + ((2 : NNReal) ^ m)⁻¹ := by
  intro ω
  let c : NNReal := (2 : NNReal) ^ m
  have hc_pos : 0 < c := by
    -- Proof comment: the dyadic scale is strictly positive.
    dsimp [c]
    positivity
  have hceil : (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * τ ω + 1 := by
    -- Proof comment: the ceiling of a nonnegative real stays within one unit above it.
    simpa using (Nat.ceil_lt_add_one (show 0 ≤ (c * τ ω : NNReal) by positivity)).le
  -- Proof comment: divide by the positive dyadic scale and absorb the unit overshoot into the
  -- mesh size `c⁻¹`.
  dsimp [dyadicCeilApprox, c]
  rw [div_le_iff₀ hc_pos]
  refine hceil.trans ?_
  calc
    (2 : NNReal) ^ m * τ ω + 1 ≤ (2 : NNReal) ^ m * T + 1 := by
      gcongr
      exact hτ_le ω
    _ = T * (2 : NNReal) ^ m + 1 := by rw [mul_comm]
    _ = T * (2 : NNReal) ^ m + ((2 : NNReal) ^ m)⁻¹ * ((2 : NNReal) ^ m) := by
      rw [inv_mul_cancel₀]
      positivity
    _ = (T + ((2 : NNReal) ^ m)⁻¹) * (2 : NNReal) ^ m := by
      rw [add_mul]

/-- Helper for Theorem 21.75: dyadic ceiling approximations converge pointwise to the underlying
finite stopping time. -/
lemma dyadicCeilApprox_tendsto
    (ρ : Ω → NNReal) :
    ∀ ω, Tendsto (fun m ↦ dyadicCeilApprox m ρ ω) atTop (𝓝 (ρ ω)) := by
  intro ω
  have hEq :
      (fun m ↦ dyadicCeilApprox m ρ ω) =
        fun m ↦ (((Nat.ceil ((ρ ω : ℝ) * (2 : ℝ) ^ m) : ℕ) : NNReal) / (2 : NNReal) ^ m) := by
    funext m
    unfold dyadicCeilApprox
    congr 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (congrArg (fun x : NNReal ↦ (x : ℝ)) (mul_comm ((2 : NNReal) ^ m) (ρ ω)))
  -- Proof comment: this is the standard dyadic approximation
  -- `⌈ρ(ω) 2^m⌉ / 2^m → ρ(ω)`.
  rw [hEq]
  refine (NNReal.tendsto_coe).mp ?_
  simpa using
    (tendsto_nat_ceil_mul_div_atTop (a := (ρ ω : ℝ))
      (show 0 ≤ (ρ ω : ℝ) from (ρ ω).2)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Theorem 21.75: continuity of a sample path turns pointwise convergence of finite
stopping times into convergence of the corresponding stopped values. -/
lemma stoppedValue_tendsto_of_timeApprox
    {X : NNReal → Ω → ℝ}
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {ρm : ℕ → Ω → NNReal} {ρ : Ω → NNReal}
    (hρ : ∀ ω, Tendsto (fun m ↦ ρm m ω) atTop (𝓝 (ρ ω))) :
    ∀ ω,
      Tendsto
        (fun m ↦ stoppedValue X (fun ω' ↦ ((ρm m ω' : NNReal) : ENNReal)) ω)
        atTop
        (𝓝 (stoppedValue X (fun ω' ↦ ((ρ ω' : NNReal) : ENNReal)) ω)) := by
  intro ω
  -- Proof comment: for `NNReal`-valued stopping times, `stoppedValue` is evaluation at that
  -- finite time, so continuity of the sample path gives the limit immediately.
  simpa [stoppedValue] using ((hX_cont ω).tendsto (ρ ω)).comp (hρ ω)

/-- Helper for Theorem 21.75: global `L¹` convergence controls the integrals over every restricted
measure `μ.restrict s`. -/
lemma tendsto_restrictedIntegral_of_tendsto_L1
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {s : Set Ω}
    (hg : Integrable g μ) (hfi : ∀ n, Integrable (f n) μ)
    (hL1 : Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω in s, f n ω ∂μ) atTop (𝓝 (∫ ω in s, g ω ∂μ)) := by
  have hL1_restrict :
      Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 (μ.restrict s)) atTop (𝓝 0) := by
    -- Proof comment: restricting the measure can only decrease the `L¹` seminorm of the
    -- difference, so the restricted seminorm still tends to zero.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 ?_ ?_
    · intro n
      exact bot_le
    · intro n
      exact eLpNorm_mono_measure (fun ω ↦ f n ω - g ω) Measure.restrict_le_self
  -- Proof comment: after transferring the `L¹` convergence to `μ.restrict s`, continuity of the
  -- integral on `L¹` yields convergence of the restricted integrals.
  exact tendsto_integral_of_L1' g hg.restrict
    (Filter.Eventually.of_forall fun n ↦ (hfi n).restrict) hL1_restrict

/-- Helper for Theorem 21.75: the dyadic stopped slices at a fixed deterministic time converge in
`L¹` to the exact finite-stop slice, and the limit slice is integrable. -/
private lemma stoppedProcess_dyadicCeilApprox_limitData
    {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (r : NNReal) :
    Integrable (stoppedProcess X (fun ω ↦ (σ ω : ENNReal)) r) μ ∧
      Tendsto
        (fun m ↦
          eLpNorm
            (fun ω ↦
              stoppedProcess X (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω -
                stoppedProcess X (fun ω' ↦ (σ ω' : ENNReal)) r ω)
            1 μ)
        atTop (𝓝 0) := by
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
      ∀ m, stoppedValue X (τm m) =ᵐ[μ] μ[X r | (hτm_stop m).measurableSpace] := by
    intro m
    -- Proof comment: each clipped dyadic stop is bounded by `r` and has countable range, so the
    -- countable-range optional sampling theorem identifies it with a conditional expectation.
    exact hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hτm_stop m) (hτm_le m) (hτm_count m)
  have hUIcond :
      UniformIntegrable
        (fun m : ℕ ↦ μ[X r | (hτm_stop m).measurableSpace]) 1 μ :=
    (hX.integrable r).uniformIntegrable_condExp fun m ↦ (hτm_stop m).measurableSpace_le
  have hUIstopped : UniformIntegrable (fun m : ℕ ↦ stoppedValue X (τm m)) 1 μ :=
    hUIcond.ae_eq fun m ↦ (hCond m).symm
  have hApprox :
      ∀ ω,
        Tendsto (fun m ↦ min (dyadicCeilApprox m σ ω) r) atTop (𝓝 (min (σ ω) r)) := by
    intro ω
    -- Proof comment: the dyadic times converge pointwise to `σ(ω)`, and the deterministic clip
    -- `x ↦ min x r` is continuous.
    exact ((continuous_id.min continuous_const).tendsto (σ ω)).comp
      (dyadicCeilApprox_tendsto σ ω)
  have hAeTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m ↦ stoppedValue X (τm m) ω) atTop (𝓝 (stoppedValue X τ ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    -- Proof comment: continuity of the sample path turns convergence of the clipped dyadic times
    -- into convergence of the corresponding stopped values.
    simpa [τm, τ] using
      stoppedValue_tendsto_of_timeApprox
        (X := X) hX_cont
        (ρm := fun m ω' ↦ min (dyadicCeilApprox m σ ω') r)
        (ρ := fun ω' ↦ min (σ ω') r) hApprox ω
  have hInt : Integrable (stoppedValue X τ) μ :=
    hUIstopped.integrable_of_ae_tendsto hAeTendsto
  have hL1 :
      Tendsto
        (fun m ↦ eLpNorm (fun ω ↦ stoppedValue X (τm m) ω - stoppedValue X τ ω) 1 μ)
        atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun m ↦ hUIstopped.aestronglyMeasurable m)
      (memLp_one_iff_integrable.2 hInt) hUIstopped.unifIntegrable hAeTendsto
  have hτ_eq :
      stoppedValue X τ = stoppedProcess X (fun ω ↦ (σ ω : ENNReal)) r := by
    simpa [τ] using
      (stoppedValue_min_const_eq_stoppedProcess
        (X := X) (σ := fun ω ↦ (σ ω : ENNReal)) (t := r))
  have hτm_eq :
      ∀ m, stoppedValue X (τm m) =
        stoppedProcess X (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) r := by
    intro m
    simpa [τm] using
      (stoppedValue_min_const_eq_stoppedProcess
        (X := X) (σ := fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) (t := r))
  constructor
  · -- Proof comment: the exact bounded-time slice is the integrable limit of the uniformly
    -- integrable dyadic stopped slices.
    simpa [hτ_eq] using hInt
  · -- Proof comment: rewrite the stopped-value convergence back into the stopped-process normal
    -- form at time `r`.
    simpa [hτ_eq, hτm_eq] using hL1

/-- Helper for Theorem 21.75: a finite stopping time yields an integrable stopped slice at every
deterministic time. -/
lemma integrable_stoppedProcess_of_finiteStoppingTime
    {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (r : NNReal) :
    Integrable (stoppedProcess X (fun ω ↦ (σ ω : ENNReal)) r) μ := by
  -- Proof comment: this is the integrability component of the dyadic `L¹` approximation package.
  exact (stoppedProcess_dyadicCeilApprox_limitData
    (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hσ r).1

/-- Helper for Theorem 21.75: dyadic ceiling approximations of a finite stopping time converge in
`L¹` to the exact stopped slice at each deterministic time. -/
lemma stoppedProcess_dyadicCeilApprox_tendsto_L1
    {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (r : NNReal) :
    Tendsto
      (fun m ↦
        eLpNorm
          (fun ω ↦
            stoppedProcess X (fun ω' ↦ (dyadicCeilApprox m σ ω' : ENNReal)) r ω -
              stoppedProcess X (fun ω' ↦ (σ ω' : ENNReal)) r ω)
          1 μ)
      atTop (𝓝 0) := by
  -- Proof comment: this is the `L¹` convergence component of the fixed-time dyadic approximation
  -- package.
  exact (stoppedProcess_dyadicCeilApprox_limitData
    (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hσ r).2

/-- Helper for Theorem 21.75: a continuous martingale stays a martingale after stopping at a
countable-range stopping time. -/
lemma martingale_stoppedProcess_of_martingale_of_countableRangeStoppingTime
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    (hσ_count : (Set.range σ).Countable) :
    Martingale (stoppedProcess X σ) ℱ μ := by
  refine ⟨hX.stronglyAdapted.stoppedProcess hX_cont hσ, ?_⟩
  intro s t hst
  let τs : Ω → ENNReal := fun ω ↦ min (σ ω) (s : ENNReal)
  let τt : Ω → ENNReal := fun ω ↦ min (σ ω) (t : ENNReal)
  have hst' : (s : ENNReal) ≤ (t : ENNReal) := by
    exact_mod_cast hst
  have hτs_stop : IsStoppingTime ℱ τs := hσ.min_const s
  have hτt_stop : IsStoppingTime ℱ τt := hσ.min_const t
  have hτs_le : ∀ ω, τs ω ≤ (s : ENNReal) := fun ω ↦ min_le_right _ _
  have hτt_le : ∀ ω, τt ω ≤ (t : ENNReal) := fun ω ↦ min_le_right _ _
  have hτs_le_τt : τs ≤ τt := fun ω ↦ min_le_min_left _ hst'
  have hτs_count : (Set.range τs).Countable := by
    refine ((hσ_count.image fun u : ENNReal ↦ min u (s : ENNReal))).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  have hτt_count : (Set.range τt).Countable := by
    refine ((hσ_count.image fun u : ENNReal ↦ min u (t : ENNReal))).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  have hStoppedCond := hX.stoppedValue_ae_eq_condExp_of_le_of_countable_range
    hτt_stop hτs_stop hτs_le_τt hτt_le hτt_count hτs_count
  have hCover : Set.univ = ⋃ i ∈ Set.range τs, {ω : Ω | τs ω = i} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_iUnion, Set.mem_setOf_eq, exists_apply_eq_apply']
  have hStoppedEq :
      μ[stoppedValue X τt | ℱ s] =ᵐ[μ] stoppedValue X τs := by
    -- Proof comment: instead of rewriting the stopping-time sigma-algebra globally, split
    -- over the atoms `{τ ∧ s = i}` where the conditional expectations have the same owner.
    nth_rw 1 [← @Measure.restrict_univ Ω _ μ]
    rw [hCover, ae_eq_restrict_biUnion_iff _ hτs_count]
    intro i hi
    by_cases his : i = (s : ENNReal)
    · subst his
      have hRestrict :
          μ[stoppedValue X τt | hτs_stop.measurableSpace] =ᵐ[μ.restrict {ω : Ω | τs ω = (s : ENNReal)}]
            μ[stoppedValue X τt | ℱ s] := by
        simpa [τs] using
          (MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
            (μ := μ) (ℱ := ℱ) (f := stoppedValue X τt) (τ := τs) hτs_stop hτs_count s)
      exact hRestrict.symm.trans (ae_restrict_of_ae hStoppedCond.symm)
    · have hi_le_s : i ≤ (s : ENNReal) := by
        rcases hi with ⟨ω, rfl⟩
        exact min_le_right _ _
      have hi_le_t : i ≤ (t : ENNReal) := hi_le_s.trans hst'
      have hi_fin : i ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hi_le_s
      have hi_untop_le_s : i.untopA ≤ s :=
        (WithTop.untopA_le_iff (x := i) (hx := hi_fin)).2 hi_le_s
      let slice : Set Ω := {ω : Ω | τs ω = i}
      have hslice_meas_i :
          MeasurableSet[ℱ i.untopA] slice := by
        have hslice_hτs :
            MeasurableSet[hτs_stop.measurableSpace] (Set.univ ∩ {ω : Ω | τs ω = (i.untopA : ENNReal)}) := by
          simpa using hτs_stop.measurableSet_eq' i.untopA
        have hslice_eq :
            slice = {ω : Ω | τs ω = (i.untopA : ENNReal)} := by
          have hcoei : ((i.untopA : NNReal) : ENNReal) = i := by
            rw [WithTop.untopA_eq_untop hi_fin]
            exact WithTop.coe_untop i hi_fin
          ext ω
          constructor
          · intro hω
            have hτs_eq : τs ω = i := by simpa [slice] using hω
            simpa [hcoei] using hτs_eq
          · intro hω
            have hτs_eq : τs ω = (i.untopA : ENNReal) := hω
            have : τs ω = i := by simpa [hcoei] using hτs_eq
            simpa [slice] using this
        rw [hslice_eq]
        simpa [Set.inter_comm] using
          (hτs_stop.measurableSet_inter_eq_iff Set.univ i.untopA).mp hslice_hτs
      have hslice_meas_s :
          MeasurableSet[ℱ s] slice := by
        exact (ℱ.mono hi_untop_le_s) _ hslice_meas_i
      have hslice_ambient : MeasurableSet slice := by
        exact (ℱ.le s) _ hslice_meas_s
      have hXi_meas : StronglyMeasurable[ℱ s] (fun ω ↦ X i.untopA ω) :=
        (hX.stronglyMeasurable i.untopA).mono (ℱ.mono hi_untop_le_s)
      have hXi_cond :
          μ[(fun ω ↦ X i.untopA ω) | ℱ s] =ᵐ[μ] fun ω ↦ X i.untopA ω := by
        rw [condExp_of_stronglyMeasurable (ℱ.le s) hXi_meas (hX.integrable i.untopA)]
      have hLeftAtom :
          stoppedValue X τt =ᵐ[μ.restrict slice] fun ω ↦ X i.untopA ω := by
        exact (ae_restrict_iff' hslice_ambient).2 <| Filter.Eventually.of_forall fun ω hω ↦ by
          have hτs_eq : τs ω = i := by simpa [slice] using hω
          have hσ_eq : σ ω = i := by
            by_cases hσ_le_s : σ ω ≤ (s : ENNReal)
            · simpa [τs, min_eq_left hσ_le_s] using hτs_eq
            · have hs_le_σ : (s : ENNReal) ≤ σ ω := le_of_not_ge hσ_le_s
              have : (s : ENNReal) = i := by
                calc
                  (s : ENNReal) = min (σ ω) (s : ENNReal) := by
                    symm
                    exact min_eq_right hs_le_σ
                  _ = i := hτs_eq
              exact False.elim (his this.symm)
          have hτt_eq : τt ω = i := by
            calc
              τt ω = min (σ ω) (t : ENNReal) := rfl
              _ = min i (t : ENNReal) := by rw [hσ_eq]
              _ = i := min_eq_left hi_le_t
          simp [stoppedValue, hτt_eq, hi_fin]
      have hRightAtom :
          stoppedValue X τs =ᵐ[μ.restrict slice] fun ω ↦ X i.untopA ω := by
        exact (ae_restrict_iff' hslice_ambient).2 <| Filter.Eventually.of_forall fun ω hω ↦ by
          have hτs_eq : τs ω = i := by simpa [slice] using hω
          simp [stoppedValue, hτs_eq, hi_fin]
      have hIndicatorInput :
          slice.indicator (stoppedValue X τt) =ᵐ[μ]
            slice.indicator (fun ω ↦ X i.untopA ω) := by
        exact (ae_eq_restrict_iff_indicator_ae_eq hslice_ambient).1 hLeftAtom
      have hIndicatorInt :
          Integrable (slice.indicator (stoppedValue X τt)) μ := by
        exact ((hX.integrable i.untopA).indicator hslice_ambient).congr hIndicatorInput.symm
      have hStoppedIndicator :
          μ[slice.indicator (stoppedValue X τt) | ℱ s] =ᵐ[μ]
            slice.indicator (μ[stoppedValue X τt | ℱ s]) := by
        exact MeasureTheory.condExp_indicator (μ := μ) (m := ℱ s)
          hIndicatorInt hslice_meas_s
      have hFixedIndicator :
          μ[slice.indicator (fun ω ↦ X i.untopA ω) | ℱ s] =ᵐ[μ]
            slice.indicator (fun ω ↦ X i.untopA ω) := by
        rw [condExp_of_stronglyMeasurable (ℱ.le s)]
        · exact hXi_meas.indicator hslice_meas_s
        · exact Integrable.indicator hslice_ambient (hX.integrable i.untopA)
      have hIndicatorEq :
          slice.indicator (μ[stoppedValue X τt | ℱ s]) =ᵐ[μ]
            slice.indicator (fun ω ↦ X i.untopA ω) := by
        exact hStoppedIndicator.symm.trans ((condExp_congr_ae hIndicatorInput).trans hFixedIndicator)
      have hRightIndicator :
          slice.indicator (stoppedValue X τs) =ᵐ[μ]
            slice.indicator (fun ω ↦ X i.untopA ω) := by
        exact (ae_eq_restrict_iff_indicator_ae_eq hslice_ambient).1 hRightAtom
      exact (ae_eq_restrict_iff_indicator_ae_eq hslice_ambient).2
        (hIndicatorEq.trans hRightIndicator.symm)
  have hLeftRewrite :
      μ[stoppedProcess X σ t | ℱ s] =ᵐ[μ] μ[stoppedValue X τt | ℱ s] := by
    -- Proof comment: rewrite the time-`t` stopped process as the stopped value at `τ ∧ t`
    -- before comparing conditional expectations.
    refine condExp_congr_ae ?_
    exact Filter.EventuallyEq.of_eq <| by
      simpa [τt] using
        (stoppedValue_min_const_eq_stoppedProcess (X := X) (σ := σ) (t := t)).symm
  have hRightRewrite :
      stoppedValue X τs =ᵐ[μ] stoppedProcess X σ s := by
    -- Proof comment: at time `s`, the stopped value at `τ ∧ s` is exactly the stopped process.
    exact Filter.EventuallyEq.of_eq <| by
      simpa [τs] using
        (stoppedValue_min_const_eq_stoppedProcess (X := X) (σ := σ) (t := s))
  -- Proof comment: transport the stopped-value martingale identity through the two explicit
  -- normalization rewrites.
  exact hLeftRewrite.trans (hStoppedEq.trans hRightRewrite)

/-- Helper for Theorem 21.75: a bounded continuous martingale remains a martingale after stopping
at a deterministically bounded stopping time. -/
lemma martingale_stoppedProcess_of_martingale_of_boundedStoppingTime
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T) :
    Martingale (stoppedProcess X σ) ℱ μ := by
  rcases hσ_bdd with ⟨T, hσ_le⟩
  have hσ_fin : ∀ ω, σ ω ≠ ∞ := fun ω ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hσ_le ω)
  let σNN : Ω → NNReal := fun ω ↦ ENNReal.toNNReal (σ ω)
  have hσ_eq : (fun ω ↦ (σNN ω : ENNReal)) = σ := by
    funext ω
    simp [σNN, ENNReal.coe_toNNReal, hσ_fin ω]
  have hσNN : IsStoppingTime ℱ (fun ω ↦ (σNN ω : ENNReal)) := by
    rw [hσ_eq]
    exact hσ
  -- Route correction: the direct `stoppedValue_min_ae_eq_condExp` route still dead-ends on
  -- `LocallyFiniteOrder NNReal`. The repaired route now has the countable-range owner above, so
  -- the remaining work is only the dyadic lift from the finite representative of `σ`.
  let σm : ℕ → Ω → ENNReal := fun m ω ↦ (dyadicCeilApprox m σNN ω : ENNReal)
  have hDyadicOwner (m : ℕ) := by
    have hDyadicStop :
        IsStoppingTime ℱ (σm m) := by
      -- Proof comment: each dyadic ceiling of the finite representative remains a stopping time.
      simpa [σm] using dyadicCeilApprox_isStoppingTime (ℱ := ℱ) hσNN m
    exact martingale_stoppedProcess_of_martingale_of_countableRangeStoppingTime
      (ℱ := ℱ) (μ := μ) (X := X) (σ := σm m) hX hX_cont hDyadicStop
      (dyadicCeilApprox_countableRange m σNN)
  refine ⟨hX.stronglyAdapted.stoppedProcess hX_cont hσ, ?_⟩
  intro s t hst
  have hInt_s := by
    -- Proof comment: the exact time-`s` slice is integrable because it is the `L¹` limit of the
    -- dyadic stopped slices.
    simpa [hσ_eq] using
      integrable_stoppedProcess_of_finiteStoppingTime
        (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hσNN s
  have hInt_t := by
    -- Proof comment: the same dyadic approximation argument applies to the time-`t` slice.
    simpa [hσ_eq] using
      integrable_stoppedProcess_of_finiteStoppingTime
        (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hσNN t
  have hL1_s := by
    -- Proof comment: the dyadic stopped slices converge in `L¹` to the exact time-`s` slice.
    simpa [σm, hσ_eq] using
      stoppedProcess_dyadicCeilApprox_tendsto_L1
        (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hσNN s
  have hL1_t := by
    -- Proof comment: the same fixed-time `L¹` bridge holds at time `t`.
    simpa [σm, hσ_eq] using
      stoppedProcess_dyadicCeilApprox_tendsto_L1
        (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hσNN t
  have hStrongStopped : StronglyAdapted ℱ (stoppedProcess X σ) :=
    hX.stronglyAdapted.stoppedProcess hX_cont hσ
  -- Proof comment: characterize the conditional expectation at time `s` by equality of its set
  -- integrals on all `ℱ s`-measurable sets, passing the dyadic martingale identities to the limit.
  exact (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hInt_t
    (fun u _ _ ↦ hInt_s.integrableOn)
    (fun u hu _ ↦ by
      have hLimit_s :
          Tendsto (fun m ↦ ∫ ω in u, stoppedProcess X (σm m) s ω ∂μ) atTop
            (𝓝 (∫ ω in u, stoppedProcess X σ s ω ∂μ)) :=
        tendsto_restrictedIntegral_of_tendsto_L1
          (μ := μ) (s := u) hInt_s (fun m ↦ (hDyadicOwner m).integrable s) hL1_s
      have hLimit_t :
          Tendsto (fun m ↦ ∫ ω in u, stoppedProcess X (σm m) t ω ∂μ) atTop
            (𝓝 (∫ ω in u, stoppedProcess X σ t ω ∂μ)) :=
        tendsto_restrictedIntegral_of_tendsto_L1
          (μ := μ) (s := u) hInt_t (fun m ↦ (hDyadicOwner m).integrable t) hL1_t
      have hEqSeq :
          ∀ m, ∫ ω in u, stoppedProcess X (σm m) s ω ∂μ =
            ∫ ω in u, stoppedProcess X (σm m) t ω ∂μ := by
        intro m
        simpa using (hDyadicOwner m).setIntegral_eq hst hu
      have hLimit_t' :
          Tendsto (fun m ↦ ∫ ω in u, stoppedProcess X (σm m) s ω ∂μ) atTop
            (𝓝 (∫ ω in u, stoppedProcess X σ t ω ∂μ)) := by
        refine Tendsto.congr' ?_ hLimit_t
        exact Filter.Eventually.of_forall fun m ↦ (hEqSeq m).symm
      exact tendsto_nhds_unique hLimit_s hLimit_t')
    ((hStrongStopped s).aestronglyMeasurable)).symm

/-- Helper for Theorem 21.75: a bounded continuous martingale remains a martingale after stopping
at a bounded stopping time. -/
lemma martingale_stoppedProcess_of_bounded_of_boundedStoppingTime
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    (_hbounded : IsBoundedProcess X) {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T) :
    Martingale (stoppedProcess X σ) ℱ μ := by
  -- Proof comment: the extra deterministic boundedness hypothesis is not used; this lemma is just
  -- the bounded-process specialization of the central bounded-stop martingale bridge above.
  exact martingale_stoppedProcess_of_martingale_of_boundedStoppingTime
    (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hσ hσ_bdd

/-- Helper for Theorem 21.75: a bounded continuous martingale remains a martingale after stopping.
-/
lemma martingale_stoppedProcess_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    (hbounded : IsBoundedProcess X) {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ) :
    Martingale (stoppedProcess X σ) ℱ μ := by
  have hLocal : IsLocalMartingale ℱ μ (stoppedProcess X σ) :=
    (isLocalMartingale_iff (ℱ := ℱ) (μ := μ) (M := stoppedProcess X σ)).2
      ⟨(hX.stronglyAdapted.stoppedProcess hX_cont hσ).adapted,
        fun n _ ↦ (n : ENNReal),
        by
          refine (isLocalizingSequence_iff (ℱ := ℱ) (μ := μ)
              (M := stoppedProcess X σ) (τs := fun n _ ↦ (n : ENNReal))).2
            ⟨?_, ?_, ?_⟩
          · intro n
            -- Proof comment: deterministic horizons are stopping times.
            simpa using (isStoppingTime_const ℱ (n : NNReal))
          · refine Filter.Eventually.of_forall fun ω ↦ ?_
            refine ⟨fun a b hab ↦ by simpa using hab, ?_⟩
            -- Proof comment: the deterministic horizons increase pointwise to `∞`.
            simpa using ENNReal.tendsto_nat_nhds_top
          · intro n
            have hDoubleStop :
                stoppedProcess (stoppedProcess X σ) (fun _ ↦ (n : ENNReal)) =
                  stoppedProcess X (fun ω ↦ min (σ ω) (n : ENNReal)) := by
              simpa [min_comm] using
                (stoppedProcess_stoppedProcess' :
                  stoppedProcess (stoppedProcess X σ) (fun _ ↦ (n : ENNReal)) =
                    stoppedProcess X (fun ω ↦ min ((fun _ ↦ (n : ENNReal)) ω) (σ ω)))
            have hStoppedMart :
                Martingale (stoppedProcess X (fun ω ↦ min (σ ω) (n : ENNReal))) ℱ μ :=
              martingale_stoppedProcess_of_bounded_of_boundedStoppingTime
                (ℱ := ℱ) (X := X) hX hX_cont hbounded (hσ.min_const (n : NNReal))
                ⟨n, fun ω ↦ min_le_right _ _⟩
            have hStoppedBdd :
                IsBoundedProcess (stoppedProcess X (fun ω ↦ min (σ ω) (n : ENNReal))) :=
              isBoundedProcess_stoppedProcess hbounded
            refine ⟨hDoubleStop ▸ hStoppedMart, ?_⟩
            -- Proof comment: deterministic boundedness upgrades the whole doubly stopped family to
            -- uniform integrability.
            exact hDoubleStop ▸
              uniformIntegrable_of_boundedProcess
                (fun t ↦ (hStoppedMart.integrable t).aestronglyMeasurable) hStoppedBdd⟩
  -- Proof comment: bounded local martingales are genuine martingales by Remark 21.68.
  exact martingale_of_bounded_local_martingale hLocal
    (boundedInTimeAe_of_boundedProcess (isBoundedProcess_stoppedProcess hbounded))

/-- Helper for Theorem 21.75: stopping a continuous local martingale yields a local martingale. -/
lemma isLocalMartingale_stoppedProcess
    (hX : IsLocalMartingale ℱ μ M)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ) :
    IsLocalMartingale ℱ μ (stoppedProcess M σ) := by
  have hX_upToInfinity : IsLocalMartingaleUpTo ℱ μ (fun _ ↦ (∞ : ENNReal)) M := by
    -- Proof comment: a local martingale is the special case of a local martingale up to `∞`.
    exact (isLocalMartingaleUpTo_iff ℱ μ (fun _ ↦ (∞ : ENNReal)) M).2
      ((isLocalMartingale_iff ℱ μ M).1 hX)
  rcases
      (isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
        (ℱ := ℱ) (μ := μ) (τ := fun _ ↦ (∞ : ENNReal)) (M := M)
        ((isLocalMartingale_iff ℱ μ M).1 hX).1 hX_cont).1 hX_upToInfinity with
    ⟨τSeq, hApprox, hMart, hBound⟩
  refine (isLocalMartingale_iff ℱ μ (stoppedProcess M σ)).2 ⟨?_, τSeq, ?_⟩
  · -- Proof comment: stopping preserves adaptedness for continuous paths.
    exact ((((isLocalMartingale_iff ℱ μ M).1 hX).1).stronglyAdapted.stoppedProcess
      hX_cont hσ).adapted
  · refine (isLocalizingSequence_iff ℱ μ (stoppedProcess M σ) τSeq).2
      ⟨hApprox.2.1, hApprox.2.2, ?_⟩
    intro n
    have hDoubleStop :
        stoppedProcess (stoppedProcess M σ) (τSeq n) =
          stoppedProcess (stoppedProcess M (τSeq n)) σ := by
      rw [stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
      congr
      funext ω
      exact min_comm _ _
    have hStoppedMart :
        Martingale (stoppedProcess (stoppedProcess M (τSeq n)) σ) ℱ μ :=
      martingale_stoppedProcess_of_bounded
        (ℱ := ℱ) (X := stoppedProcess M (τSeq n)) (hMart n)
        (continuous_stoppedProcess_of_continuous hX_cont) (hBound n) hσ
    have hStoppedBdd :
        IsBoundedProcess (stoppedProcess (stoppedProcess M (τSeq n)) σ) :=
      isBoundedProcess_stoppedProcess (hBound n)
    refine ⟨hDoubleStop.symm ▸ hStoppedMart, ?_⟩
    -- Proof comment: deterministic boundedness of each doubly stopped approximant gives the
    -- uniform-integrability clause required by the localizing sequence API.
    exact hDoubleStop.symm ▸
      uniformIntegrable_of_boundedProcess
        (fun t ↦ (hStoppedMart.integrable t).aestronglyMeasurable) hStoppedBdd

/-- Helper for Theorem 21.75: stopping the square-minus-bracket process rewrites to the square of
the stopped martingale minus the stopped bracket. -/
lemma stoppedProcess_sq_sub
    {σ : Ω → ENNReal} :
    stoppedProcess (fun t ω ↦ M t ω ^ 2 - A t ω) σ =
      fun t ω ↦ (stoppedProcess M σ t ω) ^ 2 - stoppedProcess A σ t ω := by
  ext t ω
  -- Proof comment: all three terms evaluate the underlying processes at the same clipped time
  -- `min t σ(ω)`, so this is a direct unfolding computation.
  simp [stoppedProcess]

/-- Helper for Theorem 21.75: the square-variation structure is stable under stopping. -/
lemma stoppedSquareVariationProcess
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ) :
    IsContinuousSquareVariationProcess ℱ μ (stoppedProcess M σ) (stoppedProcess A σ) := by
  have hZero : stoppedProcess A σ 0 = 0 := by
    -- Proof comment: stopping at time `0` leaves the bracket at its initial value `A 0 = 0`.
    ext ω
    simp [stoppedProcess, hA.zero]
  have hAdapted : Adapted ℱ (stoppedProcess A σ) :=
    -- Proof comment: adaptedness is preserved because stopping only composes with the clipped
    -- time.
    (hA.adapted.stronglyAdapted.stoppedProcess hA.continuous hσ).adapted
  have hContinuous : ∀ ω : Ω, Continuous fun t : NNReal ↦ stoppedProcess A σ t ω :=
    -- Proof comment: continuity of each bracket path is preserved by the time-clipping map.
    continuous_stoppedProcess_of_continuous hA.continuous
  have hMonotone : ∀ ω : Ω, Monotone (fun t : NNReal ↦ stoppedProcess A σ t ω) := by
    intro ω s t hst
    -- Proof comment: once the stopping time has occurred the stopped path is constant, and before
    -- that time the claim is just monotonicity of `A`.
    by_cases hσs : σ ω ≤ s
    · have hσt : σ ω ≤ t := hσs.trans (by exact_mod_cast hst)
      rw [stoppedProcess_eq_of_ge hσs, stoppedProcess_eq_of_ge hσt]
    · have hsσ : (s : ENNReal) ≤ σ ω := le_of_not_ge hσs
      by_cases hσt : σ ω ≤ t
      · rw [stoppedProcess_eq_of_le hsσ, stoppedProcess_eq_of_ge hσt]
        exact hA.monotone ω (by exact_mod_cast hsσ)
      · have htσ : (t : ENNReal) ≤ σ ω := le_of_not_ge hσt
        rw [stoppedProcess_eq_of_le hsσ, stoppedProcess_eq_of_le htσ]
        exact hA.monotone ω hst
  have hLocalMartingale :
      IsContinuousLocalMartingale ℱ μ
        (fun t ω ↦ (stoppedProcess M σ t ω) ^ 2 - stoppedProcess A σ t ω) := by
    -- Proof comment: stop the local martingale `M² - A` and then rewrite it into the canonical
    -- square-minus-stopped-bracket normal form.
    have hLocal :
        IsLocalMartingale ℱ μ
          (fun t ω ↦ (stoppedProcess M σ t ω) ^ 2 - stoppedProcess A σ t ω) := by
      simpa [stoppedProcess_sq_sub] using
        isLocalMartingale_stoppedProcess
          (ℱ := ℱ) (M := fun t ω ↦ M t ω ^ 2 - A t ω)
          hA.local_martingale_sq_sub.local_martingale hA.local_martingale_sq_sub.continuous hσ
    have hLocalCont :
        ∀ ω : Ω, Continuous fun t : NNReal ↦
          (stoppedProcess M σ t ω) ^ 2 - stoppedProcess A σ t ω := by
      simpa [stoppedProcess_sq_sub] using
        continuous_stoppedProcess_of_continuous
          (X := fun t ω ↦ M t ω ^ 2 - A t ω) hA.local_martingale_sq_sub.continuous
    exact ⟨hLocal, hLocalCont⟩
  exact ⟨hZero, hAdapted, hContinuous, hMonotone, hLocalMartingale⟩

/-- Helper for Theorem 21.75: the square-variation hypothesis already forces `M 0 ∈ L²(μ)`. -/
lemma integrable_initialSquare_of_continuousSquareVariationProcess
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) :
    Integrable (fun ω ↦ (M 0 ω) ^ 2) μ := by
  rcases (isLocalMartingale_iff ℱ μ (fun t ω ↦ M t ω ^ 2 - A t ω)).1
      hA.local_martingale_sq_sub.local_martingale with ⟨_, τSeq, hτSeq⟩
  have hInt :
      Integrable (stoppedProcess (fun t ω ↦ M t ω ^ 2 - A t ω) (τSeq 0) 0) μ :=
    ((hτSeq.2.2.2 0).1.integrable 0)
  -- Proof comment: at time `0` the stopped square-minus-bracket process is exactly `M 0 ^ 2`
  -- because the bracket starts at `0`.
  simpa [stoppedProcess, hA.zero] using hInt

/-- Helper for Theorem 21.75: if a stopping time `σ` is bounded by the deterministic horizon `T`,
then its stopped value is exactly the time-`T` slice of the stopped process. -/
lemma stoppedValue_eq_stoppedProcess_of_le_const
    {X : NNReal → Ω → ℝ} {σ : Ω → ENNReal} {T : NNReal}
    (hσ_le : ∀ ω, σ ω ≤ T) :
    stoppedValue X σ = stoppedProcess X σ T := by
  funext ω
  -- Proof comment: once the deterministic horizon dominates `σ(ω)`, the stopped process has
  -- already frozen at the terminal stopped value.
  exact (stoppedProcess_eq_of_ge (ω := ω) (τ := σ) (i := T) (hσ_le ω)).symm

/-- Helper for Theorem 21.75: if a stopping time `ρ` stays below the deterministic horizon `T`,
then stopping the deterministically clipped process `X^T` at `ρ` recovers the original stopped
value `X_ρ`. -/
lemma stoppedValue_stoppedProcess_const_eq_stoppedValue
    {X : NNReal → Ω → ℝ} {ρ : Ω → ENNReal} {T : NNReal}
    (hρ_le : ∀ ω, ρ ω ≤ T) :
    stoppedValue (stoppedProcess X (fun _ ↦ (T : ENNReal))) ρ = stoppedValue X ρ := by
  funext ω
  have hρ_ne_top : ρ ω ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hρ_le ω)
  -- Proof comment: after the outer stop at the deterministic horizon `T`, the additional stop at
  -- `ρ` only sees the minimum `ρ(ω) ∧ T`, which equals `ρ(ω)` under the bound hypothesis.
  rw [stoppedValue_stoppedProcess_apply
    (u := X) (τ := fun _ ↦ (T : ENNReal)) (σ := ρ) (ω := ω) hρ_ne_top]
  change X (min (ρ ω) (T : ENNReal)).untopA ω = X (ρ ω).untopA ω
  rw [min_eq_left (hρ_le ω)]

/-- Helper for Theorem 21.75: the bounded clipped stop `ρ := σ ∧ t` of the deterministically
stopped process `X^T` is the same as the time-`t` slice of `X^σ`. -/
lemma stoppedValue_stoppedProcess_const_eq_stoppedProcess
    {X : NNReal → Ω → ℝ} {σ : Ω → ENNReal} {T t : NNReal}
    (hσ_le : ∀ ω, σ ω ≤ T) :
    stoppedValue (stoppedProcess X (fun _ ↦ (T : ENNReal)))
        (fun ω ↦ min (σ ω) (t : ENNReal)) =
      stoppedProcess X σ t := by
  calc
    stoppedValue (stoppedProcess X (fun _ ↦ (T : ENNReal)))
        (fun ω ↦ min (σ ω) (t : ENNReal)) =
      stoppedValue X (fun ω ↦ min (σ ω) (t : ENNReal)) := by
        -- Proof comment: `σ ∧ t` is still bounded by `T`, so the previous normalization applies.
        refine stoppedValue_stoppedProcess_const_eq_stoppedValue ?_
        intro ω
        exact (min_le_left _ _).trans (hσ_le ω)
    _ = stoppedProcess X σ t := by
      -- Proof comment: a deterministic-time slice of the stopped process is the stopped value at
      -- the clipped stopping time `σ ∧ t`.
      funext ω
      simpa [min_comm] using
        (stoppedProcess_eq_stoppedValue_apply (u := X) (τ := σ) (i := t) ω).symm

/-- Helper for Theorem 21.75: if the finite stop `σ` lies below `τ`, then stopping `X^τ` once
more at `σ` recovers the original stopped value `X_σ`. -/
lemma stoppedValue_stoppedProcess_eq_stoppedValue_of_le
    {X : NNReal → Ω → ℝ} {σ τ : Ω → ENNReal}
    (hσ_le_τ : ∀ ω, σ ω ≤ τ ω) (hσ_fin : ∀ ω, σ ω ≠ ∞) :
    stoppedValue (stoppedProcess X τ) σ = stoppedValue X σ := by
  funext ω
  -- Proof comment: the second stop evaluates `X` at `σ(ω) ∧ τ(ω)`, which is just `σ(ω)` under
  -- the order hypothesis.
  rw [stoppedValue_stoppedProcess_apply
    (u := X) (τ := τ) (σ := σ) (ω := ω) (hσ_fin ω)]
  change X ((min (σ ω) (τ ω)).untopA) ω = X ((σ ω).untopA) ω
  rw [min_eq_left (hσ_le_τ ω)]

/-- Helper for Theorem 21.75: a bounded continuous martingale has the same expectation at every
finite stopping time. -/
lemma expected_stoppedValue_eq_initial_of_bounded_of_finiteStoppingTime_aux
    {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    (hbounded : IsBoundedProcess X)
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ) (hσ_fin : ∀ ω, σ ω ≠ ∞) :
    μ[stoppedValue X σ] = μ[X 0] := by
  -- Proof comment: first upgrade the stopped process `X^σ` to a genuine martingale using the
  -- bounded-stop owner from the previous lemma.
  have hStoppedMart :
      Martingale (stoppedProcess X σ) ℱ μ :=
    martingale_stoppedProcess_of_bounded
      (ℱ := ℱ) (μ := μ) (X := X) hX hX_cont hbounded hσ
  have hStoppedBdd : IsBoundedProcess (stoppedProcess X σ) :=
    isBoundedProcess_stoppedProcess hbounded
  have hUIAll :
      UniformIntegrable (stoppedProcess X σ) 1 μ :=
    uniformIntegrable_of_boundedProcess
      (fun t ↦ (hStoppedMart.integrable t).aestronglyMeasurable) hStoppedBdd
  have hUINat :
      UniformIntegrable (fun n : ℕ ↦ stoppedProcess X σ n) 1 μ := by
    -- Proof comment: uniform integrability of the full continuous-time family restricts directly
    -- to the integer-time subsequence.
    refine ⟨fun n ↦ hUIAll.1 n, ?_, ?_⟩
    · intro ε hε
      rcases hUIAll.2.1 hε with ⟨δ, hδ, hδ_bound⟩
      exact ⟨δ, hδ, fun n s hs hμs ↦ hδ_bound n s hs hμs⟩
    · rcases hUIAll.2.2 with ⟨C, hC⟩
      exact ⟨C, fun n ↦ hC n⟩
  have hNatTendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ stoppedProcess X σ n ω) atTop
        (𝓝 (stoppedValue X σ ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hEventuallyEq :
        (fun n : ℕ ↦ stoppedProcess X σ n ω) =ᶠ[atTop] fun _ ↦ stoppedValue X σ ω := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ((σ ω).untopA)] with n hn
      have hσn : σ ω ≤ (n : ENNReal) :=
        (WithTop.untopA_le_iff (x := σ ω) (hx := hσ_fin ω)).1 hn
      -- Proof comment: once the integer horizon dominates the finite stop `σ(ω)`, the stopped
      -- process has already frozen at the terminal stopped value.
      simpa [stoppedValue] using
        (stoppedProcess_eq_of_ge (u := X) (τ := σ) (ω := ω) (i := (n : NNReal)) hσn)
    exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have hStoppedValueInt : Integrable (stoppedValue X σ) μ :=
    hUINat.integrable_of_ae_tendsto hNatTendsto
  have hL1 :
      Tendsto
        (fun n : ℕ ↦ eLpNorm (fun ω ↦ stoppedProcess X σ n ω - stoppedValue X σ ω) 1 μ)
        atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun n ↦ (hStoppedMart.integrable n).aestronglyMeasurable)
      (memLp_one_iff_integrable.2 hStoppedValueInt) hUINat.2.1 hNatTendsto
  have hIntegralTendsto :
      Tendsto (fun n : ℕ ↦ μ[stoppedProcess X σ n]) atTop
        (𝓝 μ[stoppedValue X σ]) := by
    -- Proof comment: `L¹` convergence of the integer-time stopped marginals gives convergence of
    -- their expectations to the terminal stopped expectation.
    exact tendsto_integral_of_L1' (stoppedValue X σ) hStoppedValueInt
      (Filter.Eventually.of_forall fun n ↦ (hUINat.memLp n).integrable le_rfl) hL1
  have hIntegralEq :
      ∀ n : ℕ, μ[stoppedProcess X σ n] = μ[X 0] := by
    intro n
    -- Proof comment: every deterministic time marginal of the stopped martingale has the same
    -- expectation as its initial value.
    simpa [setIntegral_univ] using
      (hStoppedMart.setIntegral_eq (show (0 : NNReal) ≤ n by exact zero_le _)
        (s := Set.univ) MeasurableSet.univ).symm
  have hConstTendsto :
      Tendsto (fun n : ℕ ↦ μ[stoppedProcess X σ n]) atTop (𝓝 μ[X 0]) := by
    have hSeqEq : (fun n : ℕ ↦ μ[stoppedProcess X σ n]) = fun _ ↦ μ[X 0] := by
      funext n
      exact hIntegralEq n
    simpa [hSeqEq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ μ[X 0]) atTop (𝓝 μ[X 0]))
  -- Proof comment: the integer-time expectations converge both to the terminal stopped
  -- expectation and to the constant initial expectation, so the two limits coincide.
  exact tendsto_nhds_unique hIntegralTendsto hConstTendsto

/-- Helper for Theorem 21.75: bounded stopping preserves the initial expectation of a continuous
martingale. -/
lemma expected_stoppedValue_eq_initial_of_martingale_of_boundedStoppingTime
    {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ)
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ)
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T) :
    μ[stoppedValue X σ] = μ[X 0] := by
  rcases hσ_bdd with ⟨T, hσ_bdd⟩
  have hStoppedMart :
      Martingale (stoppedProcess X σ) ℱ μ :=
    martingale_stoppedProcess_of_martingale_of_boundedStoppingTime
      (ℱ := ℱ) (μ := μ) hX hX_cont hσ ⟨T, hσ_bdd⟩
  -- Proof comment: evaluate the stopped martingale at the bounding horizon `T`, where it has
  -- already reached the terminal stopped value.
  calc
    μ[stoppedValue X σ] = μ[stoppedProcess X σ T] := by
      simp [stoppedValue_eq_stoppedProcess_of_le_const (X := X) (σ := σ) (T := T) hσ_bdd]
    _ = μ[stoppedProcess X σ 0] := by
      simpa [setIntegral_univ] using
        (hStoppedMart.setIntegral_eq (show (0 : NNReal) ≤ T by exact zero_le T)
          (s := Set.univ) MeasurableSet.univ).symm
    _ = μ[X 0] := by
      simp [stoppedProcess]

-- Proof sketch: localize `M` before `τ` by the bounded martingale sequence from Remark 21.67,
-- stop again at `τ₀`, and use the integrability of the square-variation witness `A` at `τ₀` to
-- obtain uniform integrability of the doubly stopped martingales. Optional sampling then passes
-- to the limit and identifies the stopped expectation with the initial one.
/-- Helper for Theorem 21.75: once `τSeq` approximates `τ` and `τ₀ < τ`, the extra localization
eventually releases above `τ₀` almost surely. -/
lemma ae_eventually_le_localizingApprox_of_lt
    {τSeq : ℕ → Ω → ENNReal}
    (hApprox : IsStoppingTimeApproximationUpTo ℱ μ τSeq τ)
    (hτ₀_lt : τ₀ < τ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, τ₀ ω ≤ τSeq n ω := by
  rcases hApprox with ⟨_, _, hlim⟩
  filter_upwards [hlim] with ω hω
  rcases hω with ⟨_, hωtendsto⟩
  -- Proof comment: since `τSeq n ω → τ ω` and `τ₀ ω < τ ω`, the tail of the approximation stays
  -- above `τ₀ ω`.
  exact (hωtendsto <| Set.Ioi_mem_nhds (hτ₀_lt ω)).mono fun _ hn ↦ le_of_lt hn

/-- Helper for Theorem 21.75: on a probability space, a family with uniformly bounded `L^p`
norms for some exponent `p > 1` is uniformly integrable in `L¹`. -/
private theorem uniformIntegrable_of_boundedMemLpFamily_of_one_lt
    {ι : Type*} {p : ℝ} (hp : 1 < p) {f : ι → Ω → ℝ}
    (hf_memLp : ∀ i, MemLp (f i) (ENNReal.ofReal p) μ)
    (hf_bdd : ∃ C : NNReal, ∀ i, eLpNorm (f i) (ENNReal.ofReal p) μ ≤ C) :
    UniformIntegrable f 1 μ := by
  rcases hf_bdd with ⟨C, hC⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have h1_le_q : (1 : ℝ≥0∞) ≤ q := by
    simpa [q, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  let B : NNReal := max C 1
  have hB : ∀ i, eLpNorm (f i) q μ ≤ (B : ℝ≥0∞) := by
    intro i
    exact le_trans (hC i) (by exact_mod_cast le_max_left C (1 : NNReal))
  have hBpos : 0 < (B : ℝ) := by
    exact NNReal.coe_pos.2 (lt_of_lt_of_le zero_lt_one (le_max_right C 1))
  let r : ℝ := 1 - 1 / p
  have hr_pos : 0 < r := by
    dsimp [r]
    have hp_inv_lt : 1 / p < 1 / 1 := one_div_lt_one_div_of_lt zero_lt_one hp
    linarith
  have hbound1 : ∀ i, eLpNorm (f i) 1 μ ≤ (B : ℝ≥0∞) * μ Set.univ ^ r := by
    intro i
    -- Proof comment: compare the `L¹` and `L^p` seminorms on the whole finite measure space.
    calc
      eLpNorm (f i) 1 μ ≤ eLpNorm (f i) q μ * μ Set.univ ^ r := by
        simpa [q, r, hp0.ne', ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le, one_div] using
          (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1_le_q
            ((hf_memLp i).aestronglyMeasurable))
      _ ≤ (B : ℝ≥0∞) * μ Set.univ ^ r := by
        gcongr
        exact hB i
  refine ⟨fun i ↦ (hf_memLp i).aestronglyMeasurable, ?_, ?_⟩
  · intro ε hε
    let δ : ℝ := (ε / B) ^ (1 / r)
    have hδpos : 0 < δ := by
      -- Proof comment: `δ` is positive because both `ε` and the uniform `L^p` bound are positive.
      dsimp [δ]
      exact Real.rpow_pos_of_pos (div_pos hε hBpos) _
    refine ⟨δ, hδpos, ?_⟩
    intro i s hs hμs
    have hmeas_restrict : AEStronglyMeasurable (f i) (μ.restrict s) :=
      ((hf_memLp i).aestronglyMeasurable).mono_measure Measure.restrict_le_self
    have hcomp :
        eLpNorm (s.indicator (f i)) 1 μ ≤
          eLpNorm (f i) q (μ.restrict s) * μ s ^ r := by
      -- Proof comment: move to the restricted measure on `s` and compare exponents there.
      simpa [q, eLpNorm_indicator_eq_eLpNorm_restrict hs, r, hp0.ne', ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le, one_div, Measure.restrict_apply' hs, Set.univ_inter] using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1_le_q hmeas_restrict)
    have hrestrict : eLpNorm (f i) q (μ.restrict s) ≤ (B : ℝ≥0∞) := by
      exact le_trans
        (eLpNorm_mono_measure (f i) Measure.restrict_le_self)
        (hB i)
    have hδr_real : δ ^ r = ε / B := by
      simpa [δ] using Real.rpow_inv_rpow (div_nonneg hε.le hBpos.le) hr_pos.ne'
    have hδr : ENNReal.ofReal δ ^ r = ENNReal.ofReal (ε / B) := by
      simpa [ENNReal.ofReal_rpow_of_nonneg hδpos.le hr_pos.le] using
        congrArg ENNReal.ofReal hδr_real
    have hμsr : μ s ^ r ≤ ENNReal.ofReal ε / (B : ℝ≥0∞) := by
      -- Proof comment: the choice of `δ` makes the measure factor `μ s ^ r` small enough.
      calc
        μ s ^ r ≤ ENNReal.ofReal δ ^ r := ENNReal.rpow_le_rpow hμs hr_pos.le
        _ = ENNReal.ofReal (ε / B) := hδr
        _ = ENNReal.ofReal ε / (B : ℝ≥0∞) := by
          simpa using (ENNReal.ofReal_div_of_pos hBpos)
    calc
      eLpNorm (s.indicator (f i)) 1 μ
          ≤ eLpNorm (f i) q (μ.restrict s) * μ s ^ r := hcomp
      _ ≤ (B : ℝ≥0∞) * μ s ^ r := by
        gcongr
      _ ≤ (B : ℝ≥0∞) * (ENNReal.ofReal ε / (B : ℝ≥0∞)) := by
        gcongr
      _ = ENNReal.ofReal ε := by
        rw [mul_comm, ENNReal.div_mul_cancel (by exact_mod_cast hBpos.ne') ENNReal.coe_ne_top]
  · refine ⟨(((B : ℝ≥0∞) * μ Set.univ ^ r).toNNReal), ?_⟩
    intro i
    -- Proof comment: the same exponent comparison gives a uniform `L¹` bound on the whole
    -- family, which is the boundedness component of `UniformIntegrable`.
    rw [ENNReal.coe_toNNReal]
    · exact hbound1 i
    · exact (ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)).ne

/-- Helper for Theorem 21.75: a common `L²` bound makes a real-valued family uniformly
integrable in `L¹`. -/
lemma uniformIntegrable_one_of_integrable_sq_bdd
    {ι : Type*} {f : ι → Ω → ℝ}
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf_sq : ∀ i, Integrable (fun ω ↦ (f i ω) ^ 2) μ)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ i, ∫ ω, (f i ω) ^ 2 ∂μ ≤ B) :
    UniformIntegrable f 1 μ := by
  let q : ℝ≥0∞ := ENNReal.ofReal (2 : ℝ)
  have hq_ne_zero : q ≠ 0 := by
    norm_num [q]
  have hq_ne_top : q ≠ ∞ := by
    simp [q]
  have hf_memLp : ∀ i, MemLp (f i) q μ := by
    intro i
    -- Proof comment: finite second moments are exactly the `L²` membership condition.
    refine (integrable_norm_rpow_iff (hf_meas i) hq_ne_zero hq_ne_top).1 ?_
    simpa [q, Real.norm_eq_abs, sq_abs] using hf_sq i
  let C : NNReal := ⟨B ^ (1 / 2 : ℝ), Real.rpow_nonneg hB_nonneg _⟩
  have hC : ∀ i, eLpNorm (f i) q μ ≤ C := by
    intro i
    have hsq_nonneg : 0 ≤ ∫ ω, (f i ω) ^ 2 ∂μ := by
      exact integral_nonneg fun _ ↦ sq_nonneg _
    have hNorm :
        eLpNorm (f i) q μ =
          ENNReal.ofReal ((∫ ω, (f i ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
      -- Proof comment: for `p = 2`, the `L²` seminorm is the square-root of the second moment.
      simpa [q, Real.norm_eq_abs, sq_abs] using
        (MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm
          (f := f i) (p := q) (μ := μ) hq_ne_zero hq_ne_top (hf_memLp i))
    have hpow :
        (∫ ω, (f i ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hsq_nonneg (hB i) (by norm_num)
    calc
      eLpNorm (f i) q μ =
          ENNReal.ofReal ((∫ ω, (f i ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := hNorm
      _ ≤ ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := ENNReal.ofReal_le_ofReal hpow
      _ ≤ C := by simp [C]
  -- Proof comment: once the family is uniformly bounded in `L²`, the general `p > 1` criterion
  -- upgrades it to uniform integrability in `L¹`.
  exact uniformIntegrable_of_boundedMemLpFamily_of_one_lt
    (p := 2) (by norm_num) hf_memLp ⟨C, hC⟩

/-- Helper for Theorem 21.75: uniform integrability plus almost-sure convergence gives
convergence of expectations. -/
lemma tendsto_integral_of_uniformIntegrable_of_tendsto_ae
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hUI : UniformIntegrable f 1 μ)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n ↦ μ[f n]) atTop (𝓝 μ[g]) := by
  have hg_int : Integrable g μ := hUI.integrable_of_ae_tendsto hfg
  have hL1 :
      Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hf_meas
      (memLp_one_iff_integrable.2 hg_int) hUI.2.1 hfg
  -- Proof comment: once the difference tends to zero in `L¹`, continuity of the Bochner integral
  -- gives convergence of expectations.
  exact tendsto_integral_of_L1' g hg_int
    (Filter.Eventually.of_forall fun n ↦ (hUI.memLp n).integrable le_rfl) hL1

/-- Helper for Theorem 21.75: once a stopping time is finite, large deterministic times leave the
stopped process frozen at the terminal stopped value. -/
lemma tendsto_stoppedProcess_atTop_to_stoppedValue
    {X : NNReal → Ω → ℝ} {σ : Ω → ENNReal}
    (hσ_fin : ∀ ω : Ω, σ ω ≠ ∞) :
    ∀ ω, Tendsto (fun t : NNReal ↦ stoppedProcess X σ t ω) atTop (𝓝 (stoppedValue X σ ω)) := by
  intro ω
  have hEventuallyEq :
      (fun t : NNReal ↦ stoppedProcess X σ t ω) =ᶠ[atTop] fun _ ↦ stoppedValue X σ ω := by
    filter_upwards [eventually_ge_atTop ((σ ω).untopA)] with t ht
    have hστ : σ ω ≤ (t : ENNReal) :=
      (WithTop.untopA_le_iff (x := σ ω) (hx := hσ_fin ω)).1 ht
    -- Proof comment: once `t` dominates the finite stop `σ(ω)`, the process is already frozen.
    simpa [stoppedValue] using
      (stoppedProcess_eq_of_ge (u := X) (τ := σ) (ω := ω) (i := t) hστ)
  exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds

/-- Helper for Theorem 21.75: a monotone path preserves the order of finite stopping times under
stopped evaluation. -/
lemma stoppedValue_le_stoppedValue_of_monotone
    {X : NNReal → Ω → ℝ}
    (hX_mono : ∀ ω : Ω, Monotone (fun t : NNReal ↦ X t ω))
    {σ ρ : Ω → ENNReal} (hσρ : ∀ ω, σ ω ≤ ρ ω) (hρ_fin : ∀ ω : Ω, ρ ω ≠ ∞) :
    ∀ ω, stoppedValue X σ ω ≤ stoppedValue X ρ ω := by
  intro ω
  have hσ_idx_le_ρ_idx : (σ ω).untopA ≤ (ρ ω).untopA :=
    WithTop.untopA_mono (hρ_fin ω) (hσρ ω)
  -- Proof comment: finite stopping times evaluate the monotone path at ordered deterministic
  -- indices.
  simpa [stoppedValue] using hX_mono ω hσ_idx_le_ρ_idx

/-- Helper for Theorem 21.75: a monotone process starting at `0` has nonnegative stopped values.
-/
lemma stoppedValue_nonneg_of_monotone_zero
    {X : NNReal → Ω → ℝ}
    (hX_zero : X 0 = 0)
    (hX_mono : ∀ ω : Ω, Monotone (fun t : NNReal ↦ X t ω))
    {σ : Ω → ENNReal} :
    ∀ ω, 0 ≤ stoppedValue X σ ω := by
  intro ω
  -- Proof comment: the stopped value is the path evaluated at the finite index `σ(ω).untopA`,
  -- which is above time `0`.
  simpa [stoppedValue, hX_zero] using
    hX_mono ω (show (0 : NNReal) ≤ (σ ω).untopA by exact zero_le _)

/-- Helper for Theorem 21.75: an increasing process started at `0` stays integrable when the stop
is moved down below an integrable finite terminal stop.
-/
lemma integrable_stoppedValue_of_monotone_of_le
    {X : NNReal → Ω → ℝ} (hX_adapted : Adapted ℱ X)
    (hX_zero : X 0 = 0)
    (hX_mono : ∀ ω : Ω, Monotone (fun t : NNReal ↦ X t ω))
    (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ ρ : Ω → ENNReal} (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ)
    (hσρ : ∀ ω, σ ω ≤ ρ ω) (hρ_fin : ∀ ω : Ω, ρ ω ≠ ∞)
    (hρ_int : Integrable (stoppedValue X ρ) μ) :
    Integrable (stoppedValue X σ) μ := by
  have hσ_meas :
      AEStronglyMeasurable (stoppedValue X σ) μ := by
    exact
      (measurable_stoppedValue
        (hX_adapted.stronglyAdapted.progMeasurable_of_continuous hX_cont)
        hσ).aestronglyMeasurable
  refine Integrable.mono' hρ_int hσ_meas ?_
  filter_upwards [
    Filter.Eventually.of_forall
      (stoppedValue_nonneg_of_monotone_zero
        (X := X) hX_zero hX_mono (σ := σ)),
    Filter.Eventually.of_forall
      (stoppedValue_le_stoppedValue_of_monotone
        (X := X) hX_mono (σ := σ) (ρ := ρ) hσρ hρ_fin)
  ] with ω hσ_nonneg hσ_le_ρ
  -- Proof comment: nonnegativity removes the absolute value, so pointwise domination by the
  -- terminal stopped value yields the integrability transfer.
  rw [Real.norm_of_nonneg hσ_nonneg]
  exact hσ_le_ρ

/-- Helper for Theorem 21.75: monotonicity of the path transfers directly to the expectations of
two finite stopped values ordered by their stopping times.
-/
lemma integral_stoppedValue_le_of_monotone_of_le
    {X : NNReal → Ω → ℝ}
    (hX_mono : ∀ ω : Ω, Monotone (fun t : NNReal ↦ X t ω))
    {σ ρ : Ω → ENNReal} (hσρ : ∀ ω, σ ω ≤ ρ ω) (hρ_fin : ∀ ω : Ω, ρ ω ≠ ∞)
    (hσ_int : Integrable (stoppedValue X σ) μ)
    (hρ_int : Integrable (stoppedValue X ρ) μ) :
    μ[stoppedValue X σ] ≤ μ[stoppedValue X ρ] := by
  -- Proof comment: after proving the pointwise order for stopped values, monotonicity of the
  -- integral gives the expectation bound.
  refine integral_mono_ae hσ_int hρ_int ?_
  exact Filter.Eventually.of_forall
    (stoppedValue_le_stoppedValue_of_monotone
      (X := X) hX_mono (σ := σ) (ρ := ρ) hσρ hρ_fin)

/-- Helper for Theorem 21.75: evaluating a square-minus-process at a finite stop rewrites to the
square of the stopped value minus the stopped compensator. -/
lemma stoppedValue_sq_sub_of_finiteStop
    {X B : NNReal → Ω → ℝ} {σ : Ω → ENNReal} (hσ_fin : ∀ ω, σ ω ≠ ∞) :
    stoppedValue (fun t ω ↦ X t ω ^ 2 - B t ω) σ =
      fun ω ↦ (stoppedValue X σ ω) ^ 2 - stoppedValue B σ ω := by
  funext ω
  -- Proof comment: at a finite stop, every term is evaluated at the same clipped deterministic
  -- time `σ(ω).untopA`.
  simp [stoppedValue, hσ_fin ω]

/-- Helper for Theorem 21.75: if a stopping-time approximation tends almost surely to `∞`, then it
eventually dominates every fixed finite stopping time. -/
lemma ae_eventually_le_stoppingApprox_top_of_finite
    {τSeq : ℕ → Ω → ENNReal}
    (hApprox : IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ (∞ : ENNReal)))
    {σ : Ω → ENNReal} (hσ_fin : ∀ ω : Ω, σ ω ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, σ ω ≤ τSeq n ω := by
  rcases hApprox with ⟨_, _, hlim⟩
  filter_upwards [hlim] with ω hω
  rcases hω with ⟨_, hωtendsto⟩
  have hTail :
      ∀ᶠ n in atTop, ((σ ω).untopA : ENNReal) < τSeq n ω :=
    ENNReal.tendsto_nhds_top_iff_nnreal.1 hωtendsto (σ ω).untopA
  filter_upwards [hTail] with n hn
  have hσ_eq : (((σ ω).untopA : NNReal) : ENNReal) = σ ω := by
    simpa using (WithTop.coe_untop (σ ω) (hσ_fin ω))
  exact hσ_eq ▸ le_of_lt hn

/-- Helper for Theorem 21.75: once a bounded stopped martingale owner is available above a finite
stop `σ`, the compensated-square identity gives the second moment of `M_σ`. -/
lemma stoppedValue_sq_integrable_and_integral_eq_initial_add_variation_of_boundedOwner
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    {σ τ' : Ω → ENNReal}
    (hτ' : IsStoppingTime ℱ τ') (hσ : IsStoppingTime ℱ σ)
    (hσ_fin : ∀ ω : Ω, σ ω ≠ ∞) (hσ_le : ∀ ω, σ ω ≤ τ' ω)
    (hOwner : Martingale (stoppedProcess M τ') ℱ μ)
    (hOwner_bdd : IsBoundedProcess (stoppedProcess M τ'))
    (hAσ : Integrable (stoppedValue A σ) μ) :
    Integrable (fun ω ↦ (stoppedValue M σ ω) ^ 2) μ ∧
      μ[fun ω ↦ (stoppedValue M σ ω) ^ 2] =
        μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A σ] := by
  let Y : NNReal → Ω → ℝ := fun t ω ↦
    (stoppedProcess M τ' t ω) ^ 2 - stoppedProcess A τ' t ω
  have hSquareStopped :
      IsContinuousSquareVariationProcess ℱ μ (stoppedProcess M τ') (stoppedProcess A τ') :=
    by
      have hZero : stoppedProcess A τ' 0 = 0 := by
        ext ω
        simp [stoppedProcess, hA.zero]
      have hAdapted : Adapted ℱ (stoppedProcess A τ') :=
        (hA.adapted.stronglyAdapted.stoppedProcess hA.continuous hτ').adapted
      have hContinuous : ∀ ω : Ω, Continuous fun t : NNReal ↦ stoppedProcess A τ' t ω :=
        continuous_stoppedProcess_of_continuous hA.continuous
      have hMonotone : ∀ ω : Ω, Monotone (fun t : NNReal ↦ stoppedProcess A τ' t ω) := by
        intro ω s t hst
        by_cases hτs : τ' ω ≤ s
        · have hτt : τ' ω ≤ t := hτs.trans (by exact_mod_cast hst)
          rw [stoppedProcess_eq_of_ge hτs, stoppedProcess_eq_of_ge hτt]
        · have hsτ : (s : ENNReal) ≤ τ' ω := le_of_not_ge hτs
          by_cases hτt : τ' ω ≤ t
          · rw [stoppedProcess_eq_of_le hsτ, stoppedProcess_eq_of_ge hτt]
            exact hA.monotone ω (by exact_mod_cast hsτ)
          · have htτ : (t : ENNReal) ≤ τ' ω := le_of_not_ge hτt
            rw [stoppedProcess_eq_of_le hsτ, stoppedProcess_eq_of_le htτ]
            exact hA.monotone ω hst
      have hLocalMartingale :
          IsContinuousLocalMartingale ℱ μ
            (fun t ω ↦ (stoppedProcess M τ' t ω) ^ 2 - stoppedProcess A τ' t ω) := by
        have hLocal :
            IsLocalMartingale ℱ μ
              (fun t ω ↦ (stoppedProcess M τ' t ω) ^ 2 - stoppedProcess A τ' t ω) := by
          simpa [stoppedProcess_sq_sub] using
            isLocalMartingale_stoppedProcess
              (ℱ := ℱ) (M := fun t ω ↦ M t ω ^ 2 - A t ω)
              hA.local_martingale_sq_sub.local_martingale
              hA.local_martingale_sq_sub.continuous hτ'
        have hLocalCont :
            ∀ ω : Ω, Continuous fun t : NNReal ↦
              (stoppedProcess M τ' t ω) ^ 2 - stoppedProcess A τ' t ω := by
          simpa [stoppedProcess_sq_sub] using
            continuous_stoppedProcess_of_continuous
              (X := fun t ω ↦ M t ω ^ 2 - A t ω) hA.local_martingale_sq_sub.continuous
        exact ⟨hLocal, hLocalCont⟩
      exact ⟨hZero, hAdapted, hContinuous, hMonotone, hLocalMartingale⟩
  have hY : IsContinuousLocalMartingale ℱ μ Y := by
    -- Proof comment: the compensated square of the stopped process is exactly the local martingale
    -- field carried by the stopped square-variation witness.
    simpa [Y] using hSquareStopped.local_martingale_sq_sub
  have hY_upToInfinity : IsLocalMartingaleUpTo ℱ μ (fun _ ↦ (∞ : ENNReal)) Y := by
    -- Proof comment: a local martingale is the special case of a local martingale up to `∞`.
    exact (isLocalMartingaleUpTo_iff ℱ μ (fun _ ↦ (∞ : ENNReal)) Y).2
      ((isLocalMartingale_iff ℱ μ Y).1 hY.local_martingale)
  have hY_boundedApprox :
      HasBoundedStoppedMartingaleApproximationUpTo ℱ μ (fun _ ↦ (∞ : ENNReal)) Y :=
    (isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
      (ℱ := ℱ) (μ := μ) (τ := fun _ ↦ (∞ : ENNReal)) (M := Y)
      hY.adapted hY.continuous).1 hY_upToInfinity
  rcases hY_boundedApprox with ⟨κSeq, hκApprox, hκBounded⟩
  let σκ : ℕ → Ω → ENNReal := fun k ω ↦ min (σ ω) (κSeq k ω)
  have hσκ_stop : ∀ k : ℕ, IsStoppingTime ℱ (σκ k) := by
    intro k
    exact hσ.min (hκApprox.2.1 k)
  have hσκ_fin : ∀ k : ℕ, ∀ ω : Ω, σκ k ω ≠ ∞ := by
    intro k ω
    exact ne_top_of_le_ne_top (hσ_fin ω) (min_le_left _ _)
  have hσκ_le_κ : ∀ k : ℕ, ∀ ω : Ω, σκ k ω ≤ κSeq k ω := by
    intro k ω
    exact min_le_right _ _
  have hσκ_le_σ : ∀ k : ℕ, ∀ ω : Ω, σκ k ω ≤ σ ω := by
    intro k ω
    exact min_le_left _ _
  have hExpectedApprox :
      ∀ k : ℕ, μ[stoppedValue Y (σκ k)] = μ[Y 0] := by
    intro k
    have hRewrite :
        stoppedValue (stoppedProcess Y (κSeq k)) (σκ k) = stoppedValue Y (σκ k) :=
      stoppedValue_stoppedProcess_eq_stoppedValue_of_le
        (X := Y) (σ := σκ k) (τ := κSeq k) (hσκ_le_κ k) (hσκ_fin k)
    have hStoppedExpected :
        μ[stoppedValue (stoppedProcess Y (κSeq k)) (σκ k)] =
          μ[(stoppedProcess Y (κSeq k)) 0] :=
      expected_stoppedValue_eq_initial_of_bounded_of_finiteStoppingTime_aux
        (ℱ := ℱ) (μ := μ) (X := stoppedProcess Y (κSeq k)) (hκBounded k).1
        (continuous_stoppedProcess_of_continuous hY.continuous) (hκBounded k).2
        (hσκ_stop k) (hσκ_fin k)
    -- Proof comment: the auxiliary localizer `κ_k` turns the compensated-square process into a
    -- bounded martingale, so optional sampling applies at `σ ∧ κ_k`.
    calc
      μ[stoppedValue Y (σκ k)]
          = μ[stoppedValue (stoppedProcess Y (κSeq k)) (σκ k)] := by
              simp [hRewrite]
      _ = μ[(stoppedProcess Y (κSeq k)) 0] := hStoppedExpected
      _ = μ[Y 0] := by simp [stoppedProcess]
  rcases hOwner_bdd with ⟨C, hC_nonneg, hC⟩
  let G : Ω → ℝ := fun ω ↦ C ^ 2 + stoppedValue A σ ω
  have hG_int : Integrable G μ := by
    -- Proof comment: the only nonconstant part of the dominating function is the integrable
    -- terminal bracket term.
    simpa [G] using (integrable_const (C ^ 2)).add hAσ
  have hAσ_nonneg :
      ∀ᵐ ω ∂μ, 0 ≤ stoppedValue A σ ω := by
    exact Filter.Eventually.of_forall <|
      stoppedValue_nonneg_of_monotone_zero
        (X := A) hA.zero hA.monotone (σ := σ)
  have hApprox_meas :
      ∀ k : ℕ, AEStronglyMeasurable (stoppedValue Y (σκ k)) μ := by
    intro k
    exact
      (measurable_stoppedValue
        (hY.adapted.stronglyAdapted.progMeasurable_of_continuous hY.continuous)
        (hσκ_stop k)).aestronglyMeasurable
  have hApprox_dom :
      ∀ k : ℕ, ∀ᵐ ω ∂μ, ‖stoppedValue Y (σκ k) ω‖ ≤ G ω := by
    intro k
    filter_upwards [hAσ_nonneg] with ω hAσ_nonneg_ω
    have hStoppedBound :
        |stoppedValue (stoppedProcess M τ') (σκ k) ω| ≤ C := by
      -- Proof comment: the bounded owner controls the stopped value because it controls every
      -- deterministic-time slice of the owner process.
      simpa [stoppedValue, Real.norm_eq_abs] using hC ((σκ k ω).untopA) ω
    have hVariation_nonneg :
        0 ≤ stoppedValue (stoppedProcess A τ') (σκ k) ω := by
      exact
        stoppedValue_nonneg_of_monotone_zero
          (X := stoppedProcess A τ') hSquareStopped.zero hSquareStopped.monotone
          (σ := σκ k) ω
    have hVariation_le :
        stoppedValue (stoppedProcess A τ') (σκ k) ω ≤ stoppedValue A σ ω := by
      have hMono :
          stoppedValue (stoppedProcess A τ') (σκ k) ω ≤
            stoppedValue (stoppedProcess A τ') σ ω :=
        stoppedValue_le_stoppedValue_of_monotone
          (X := stoppedProcess A τ') hSquareStopped.monotone
          (σ := σκ k) (ρ := σ) (hσκ_le_σ k) hσ_fin ω
      have hRewriteA :
          stoppedValue (stoppedProcess A τ') σ = stoppedValue A σ :=
        stoppedValue_stoppedProcess_eq_stoppedValue_of_le
          (X := A) (σ := σ) (τ := τ') hσ_le hσ_fin
      simpa [hRewriteA] using hMono
    have hStoppedSqLe : (stoppedValue (stoppedProcess M τ') (σκ k) ω) ^ 2 ≤ C ^ 2 := by
      nlinarith [hStoppedBound, hC_nonneg]
    have hRewriteYω :
        stoppedValue Y (σκ k) ω =
          (stoppedValue (stoppedProcess M τ') (σκ k) ω) ^ 2 -
            stoppedValue (stoppedProcess A τ') (σκ k) ω := by
      simpa [Y] using
        congrFun
          (stoppedValue_sq_sub_of_finiteStop
            (X := stoppedProcess M τ') (B := stoppedProcess A τ') (σ := σκ k) (hσκ_fin k))
          ω
    rw [hRewriteYω]
    calc
      ‖(stoppedValue (stoppedProcess M τ') (σκ k) ω) ^ 2 -
            stoppedValue (stoppedProcess A τ') (σκ k) ω‖
          ≤ ‖(stoppedValue (stoppedProcess M τ') (σκ k) ω) ^ 2‖ +
              ‖stoppedValue (stoppedProcess A τ') (σκ k) ω‖ := by
                exact norm_sub_le _ _
      _ = (stoppedValue (stoppedProcess M τ') (σκ k) ω) ^ 2 +
            stoppedValue (stoppedProcess A τ') (σκ k) ω := by
              rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hVariation_nonneg]
      _ ≤ C ^ 2 + stoppedValue A σ ω := by
            linarith
  have hEventually :
      ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, σ ω ≤ κSeq k ω :=
    ae_eventually_le_stoppingApprox_top_of_finite
      (ℱ := ℱ) (μ := μ) (τSeq := κSeq) hκApprox hσ_fin
  have hApprox_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun k ↦ stoppedValue Y (σκ k) ω) atTop (𝓝 (stoppedValue Y σ ω)) := by
    filter_upwards [hEventually] with ω hω
    have hEventuallyEq :
        (fun k ↦ stoppedValue Y (σκ k) ω) =ᶠ[atTop] fun _ ↦ stoppedValue Y σ ω := by
      filter_upwards [hω] with k hk
      have hσk_eq : σκ k ω = σ ω := by
        simp [σκ, min_eq_left hk]
      simp [hσk_eq]
    -- Proof comment: once the auxiliary localizer has moved past the finite stop `σ(ω)`, the
    -- extra localization disappears.
    exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have hApproxIntegral_tendsto :
      Tendsto (fun k : ℕ ↦ μ[stoppedValue Y (σκ k)]) atTop (𝓝 μ[stoppedValue Y σ]) :=
    tendsto_integral_of_dominated_convergence G hApprox_meas hG_int hApprox_dom hApprox_tendsto
  have hApproxConst_tendsto :
      Tendsto (fun k : ℕ ↦ μ[stoppedValue Y (σκ k)]) atTop (𝓝 μ[Y 0]) := by
    have hSeqEq : (fun k : ℕ ↦ μ[stoppedValue Y (σκ k)]) = fun _ : ℕ ↦ μ[Y 0] := by
      funext k
      exact hExpectedApprox k
    simpa [hSeqEq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ μ[Y 0]) atTop (𝓝 μ[Y 0]))
  have hCompensatedEq :
      μ[stoppedValue Y σ] = μ[Y 0] :=
    tendsto_nhds_unique hApproxIntegral_tendsto hApproxConst_tendsto
  have hStoppedBound :
      ∀ ω : Ω, |stoppedValue M σ ω| ≤ C := by
    intro ω
    have hRewriteM :
        stoppedValue (stoppedProcess M τ') σ = stoppedValue M σ :=
      stoppedValue_stoppedProcess_eq_stoppedValue_of_le
        (X := M) (σ := σ) (τ := τ') hσ_le hσ_fin
    simpa [hRewriteM, stoppedValue, Real.norm_eq_abs] using hC ((σ ω).untopA) ω
  have hSq_meas :
      AEStronglyMeasurable (fun ω ↦ (stoppedValue M σ ω) ^ 2) μ :=
    ((measurable_stoppedValue
      (hA.local_martingale_sq_sub.adapted.stronglyAdapted.progMeasurable_of_continuous
        hA.local_martingale_sq_sub.continuous) hσ)
      .aestronglyMeasurable).pow 2
  have hSq_int : Integrable (fun ω ↦ (stoppedValue M σ ω) ^ 2) μ := by
    refine Integrable.mono' (integrable_const (C ^ 2)) hSq_meas ?_
    filter_upwards with ω
    have hSqLe : (stoppedValue M σ ω) ^ 2 ≤ C ^ 2 := by
      nlinarith [hStoppedBound ω, hC_nonneg]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hSqLe
  have hRewriteYσ :
      stoppedValue Y σ = fun ω ↦ (stoppedValue M σ ω) ^ 2 - stoppedValue A σ ω := by
    funext ω
    have hRewriteSq :=
      congrFun
        (stoppedValue_sq_sub_of_finiteStop
          (X := stoppedProcess M τ') (B := stoppedProcess A τ') (σ := σ) hσ_fin) ω
    have hRewriteM :
        stoppedValue (stoppedProcess M τ') σ = stoppedValue M σ :=
      stoppedValue_stoppedProcess_eq_stoppedValue_of_le
        (X := M) (σ := σ) (τ := τ') hσ_le hσ_fin
    have hRewriteA :
        stoppedValue (stoppedProcess A τ') σ = stoppedValue A σ :=
      stoppedValue_stoppedProcess_eq_stoppedValue_of_le
        (X := A) (σ := σ) (τ := τ') hσ_le hσ_fin
    simpa [Y, hRewriteM, hRewriteA] using hRewriteSq
  have hY0 :
      Y 0 = fun ω ↦ (M 0 ω) ^ 2 := by
    funext ω
    -- Proof comment: at time `0`, both stopped processes are unchanged and the bracket starts at
    -- `0`.
    simp [Y, hA.zero]
  have hDiffEq :
      μ[fun ω ↦ (stoppedValue M σ ω) ^ 2 - stoppedValue A σ ω] =
        μ[fun ω ↦ (M 0 ω) ^ 2] := by
    calc
      μ[fun ω ↦ (stoppedValue M σ ω) ^ 2 - stoppedValue A σ ω]
          = μ[stoppedValue Y σ] := by simp [hRewriteYσ]
      _ = μ[Y 0] := hCompensatedEq
      _ = μ[fun ω ↦ (M 0 ω) ^ 2] := by simp [hY0]
  have hSubEq :
      μ[fun ω ↦ (stoppedValue M σ ω) ^ 2] - μ[stoppedValue A σ] =
        μ[fun ω ↦ (M 0 ω) ^ 2] := by
    calc
      μ[fun ω ↦ (stoppedValue M σ ω) ^ 2] - μ[stoppedValue A σ]
          = μ[fun ω ↦ (stoppedValue M σ ω) ^ 2 - stoppedValue A σ ω] := by
              symm
              exact integral_sub' hSq_int hAσ
      _ = μ[fun ω ↦ (M 0 ω) ^ 2] := hDiffEq
  constructor
  · exact hSq_int
  · linarith

/-- First clause of Theorem 21.75: if `M` is a continuous local martingale up to the stopping
time `τ`, if `τ₀ < τ` is a stopping time, and if `A` is a continuous square-variation process
playing the role of the bracket `⟨M⟩` with `A_{τ₀}` integrable, then `E[M_{τ₀}] = E[M_0]`. -/
theorem expected_stoppedValue_eq_initial_of_localMartingaleUpTo_of_squareVariation_integrable
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) (hτ₀ : IsStoppingTime ℱ τ₀) (hτ₀_lt : τ₀ < τ)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAτ₀ : Integrable (stoppedValue A τ₀) μ) :
    μ[stoppedValue M τ₀] = μ[M 0] := by
  have hM_boundedApprox :
      HasBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M :=
    (isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
      (ℱ := ℱ) (μ := μ) (τ := τ) (M := M) hM.adapted hM.continuous).1
      hM.local_martingale_upTo
  rcases hM_boundedApprox with ⟨τSeq, hApprox, hBoundedSeq⟩
  let ρ : ℕ → Ω → ENNReal := fun n ω ↦ min (τ₀ ω) (τSeq n ω)
  have hτ₀_fin : ∀ ω : Ω, τ₀ ω ≠ ∞ := fun ω ↦ ne_top_of_lt (hτ₀_lt ω)
  have hρ_fin : ∀ n : ℕ, ∀ ω : Ω, ρ n ω ≠ ∞ := by
    intro n ω
    exact ne_top_of_le_ne_top (hτ₀_fin ω) (min_le_left _ _)
  have hEventually :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, τ₀ ω ≤ τSeq n ω :=
    ae_eventually_le_localizingApprox_of_lt
      (τ := τ) (τ₀ := τ₀) (τSeq := τSeq) hApprox hτ₀_lt
  have hExpectedApprox :
      ∀ n : ℕ, μ[stoppedValue M (ρ n)] = μ[M 0] := by
    intro n
    have hρ_stop : IsStoppingTime ℱ (ρ n) :=
      hτ₀.min (hApprox.2.1 n)
    have hρ_le : ∀ ω, ρ n ω ≤ τSeq n ω := fun ω ↦ min_le_right _ _
    have hExpectedStopped :
        μ[stoppedValue (stoppedProcess M (τSeq n)) (ρ n)] =
          μ[(stoppedProcess M (τSeq n)) 0] :=
      expected_stoppedValue_eq_initial_of_bounded_of_finiteStoppingTime_aux
        (ℱ := ℱ) (X := stoppedProcess M (τSeq n)) (hBoundedSeq n).1
        (continuous_stoppedProcess_of_continuous hM.continuous) (hBoundedSeq n).2
        hρ_stop (hρ_fin n)
    have hRewrite :
        stoppedValue (stoppedProcess M (τSeq n)) (ρ n) = stoppedValue M (ρ n) :=
      stoppedValue_stoppedProcess_eq_stoppedValue_of_le
        (X := M) (σ := ρ n) (τ := τSeq n) hρ_le (hρ_fin n)
    -- Proof comment: each bounded martingale localizer can itself be stopped at `τ₀ ∧ τₙ`, and
    -- the resulting stopped expectation is still the initial expectation.
    calc
      μ[stoppedValue M (ρ n)]
          = μ[stoppedValue (stoppedProcess M (τSeq n)) (ρ n)] := by
              simp [hRewrite]
      _ = μ[(stoppedProcess M (τSeq n)) 0] := hExpectedStopped
      _ = μ[M 0] := by simp [stoppedProcess]
  let approxValue : ℕ → Ω → ℝ := fun n ω ↦
    stoppedValue M (ρ n) ω
  have hApproxValue_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ approxValue n ω) atTop (𝓝 (stoppedValue M τ₀ ω)) := by
    filter_upwards [hEventually] with ω hω
    have hEventuallyEq :
        (fun n ↦ approxValue n ω) =ᶠ[atTop] fun _ ↦ stoppedValue M τ₀ ω := by
      filter_upwards [hω] with n hn
      simp [approxValue, ρ, min_eq_left hn]
    -- Proof comment: once the localizing sequence lies above `τ₀(ω)`, the clipped stop is
    -- exactly `τ₀(ω)`, so the approximants are eventually constant.
    exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have _hInitialSquareInt :
      Integrable (fun ω ↦ (M 0 ω) ^ 2) μ :=
    integrable_initialSquare_of_continuousSquareVariationProcess
      (ℱ := ℱ) (μ := μ) (M := M) (A := A) hA
  have _hVariationBound :
      ∀ n ω, stoppedValue A (ρ n) ω ≤ stoppedValue A τ₀ ω := by
    intro n ω
    exact stoppedValue_le_stoppedValue_of_monotone
      (X := A) hA.monotone (σ := ρ n) (ρ := τ₀)
      (fun ω' ↦ min_le_left _ _) hτ₀_fin ω
  have hVariationInt :
      ∀ n : ℕ, Integrable (stoppedValue A (ρ n)) μ := by
    intro n
    have hρ_stop : IsStoppingTime ℱ (ρ n) :=
      hτ₀.min (hApprox.2.1 n)
    -- Proof comment: the increasing bracket process is dominated by its terminal stopped value at
    -- `τ₀`, so integrability descends from `A_{τ₀}` to every `A_{ρ n}`.
    exact integrable_stoppedValue_of_monotone_of_le
      (ℱ := ℱ) (μ := μ) (X := A) hA.adapted hA.zero hA.monotone
      hA.continuous hρ_stop hτ₀ (fun ω ↦ min_le_left _ _) hτ₀_fin hAτ₀
  have hVariationIntegral_le :
      ∀ n : ℕ, μ[stoppedValue A (ρ n)] ≤ μ[stoppedValue A τ₀] := by
    intro n
    -- Proof comment: once `A_{ρ n}` is known integrable, the same monotonicity argument gives
    -- the integral bound needed for the second-moment estimate.
    exact integral_stoppedValue_le_of_monotone_of_le
      (μ := μ) (X := A) hA.monotone
      (σ := ρ n) (ρ := τ₀) (fun ω ↦ min_le_left _ _) hτ₀_fin
      (hVariationInt n) hAτ₀
  have _hStoppedLimit :
      ∀ᵐ ω ∂μ, Tendsto (fun t : NNReal ↦ stoppedProcess M τ₀ t ω) atTop
        (𝓝 (stoppedValue M τ₀ ω)) :=
    Filter.Eventually.of_forall <|
      tendsto_stoppedProcess_atTop_to_stoppedValue (X := M) (σ := τ₀) hτ₀_fin
  have hApproxValue_meas : ∀ n : ℕ, AEStronglyMeasurable (approxValue n) μ := by
    intro n
    have hρ_stop : IsStoppingTime ℱ (ρ n) :=
      hτ₀.min (hApprox.2.1 n)
    exact
      (measurable_stoppedValue
        (hM.adapted.stronglyAdapted.progMeasurable_of_continuous hM.continuous)
        hρ_stop).aestronglyMeasurable
  have hAτ₀_nonneg : 0 ≤ μ[stoppedValue A τ₀] := by
    have hAτ₀_nonneg_ae : ∀ᵐ ω ∂μ, 0 ≤ stoppedValue A τ₀ ω := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      -- Proof comment: monotonicity of the square-variation path and `A 0 = 0` force
      -- `A_{τ₀(ω)} ≥ 0`.
      simpa [stoppedValue, hA.zero] using
        (hA.monotone ω (show (0 : NNReal) ≤ (τ₀ ω).untopA by exact zero_le _))
    exact integral_nonneg_ae hAτ₀_nonneg_ae
  have hApprox_sq :
      ∀ n : ℕ,
        Integrable (fun ω ↦ (approxValue n ω) ^ 2) μ ∧
          ∫ ω, (approxValue n ω) ^ 2 ∂μ ≤
            μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀] := by
    intro n
    have hρ_stop : IsStoppingTime ℱ (ρ n) :=
      hτ₀.min (hApprox.2.1 n)
    have hApproxVariationInt :
        Integrable (stoppedValue A (ρ n)) μ :=
      hVariationInt n
    have hApproxVariation_le :
        μ[stoppedValue A (ρ n)] ≤ μ[stoppedValue A τ₀] :=
      hVariationIntegral_le n
    rcases
        stoppedValue_sq_integrable_and_integral_eq_initial_add_variation_of_boundedOwner
          (ℱ := ℱ) (μ := μ) (M := M) (A := A) hA
          (hτ' := hApprox.2.1 n) (hσ := hρ_stop) (hσ_fin := hρ_fin n)
          (hσ_le := fun ω ↦ min_le_right _ _) (hOwner := (hBoundedSeq n).1)
          (hOwner_bdd := (hBoundedSeq n).2) hApproxVariationInt with
      ⟨hSqInt, hSqEq⟩
    constructor
    · simpa [approxValue] using hSqInt
    · -- Proof comment: the compensated-square identity at `ρ n` reduces the bound to the
      -- monotone bracket estimate already established above.
      calc
        ∫ ω, (approxValue n ω) ^ 2 ∂μ =
            μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A (ρ n)] := by
              simpa [approxValue] using hSqEq
        _ ≤ μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀] := by
              gcongr
  have hInitialSquare_nonneg : 0 ≤ μ[fun ω ↦ (M 0 ω) ^ 2] := by
    exact integral_nonneg fun ω ↦ sq_nonneg (M 0 ω)
  have hUIApprox :
      UniformIntegrable approxValue 1 μ :=
    uniformIntegrable_one_of_integrable_sq_bdd
      (μ := μ) (f := approxValue) hApproxValue_meas
      (fun n ↦ (hApprox_sq n).1)
      (hB_nonneg := add_nonneg hInitialSquare_nonneg hAτ₀_nonneg)
      (fun n ↦ (hApprox_sq n).2)
  have hApproxIntegralTendsto :
      Tendsto (fun n : ℕ ↦ μ[approxValue n]) atTop (𝓝 μ[stoppedValue M τ₀]) :=
    tendsto_integral_of_uniformIntegrable_of_tendsto_ae
      (μ := μ) (f := approxValue) (g := stoppedValue M τ₀)
      hApproxValue_meas hUIApprox hApproxValue_tendsto
  have hApproxConstTendsto :
      Tendsto (fun n : ℕ ↦ μ[approxValue n]) atTop (𝓝 μ[M 0]) := by
    have hSeqEq : (fun n : ℕ ↦ μ[approxValue n]) = fun _ : ℕ ↦ μ[M 0] := by
      funext n
      exact hExpectedApprox n
    simpa [hSeqEq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ μ[M 0]) atTop (𝓝 μ[M 0]))
  -- Proof comment: the stopped expectations along `ρ n` converge to both the exact stopped
  -- expectation and the constant initial expectation, so the limits must agree.
  exact tendsto_nhds_unique hApproxIntegralTendsto hApproxConstTendsto

-- Proof sketch: use clause (1) and the square-variation identity for the stopped bounded
-- localizing martingales to obtain a uniform `L²` estimate
-- `E[(M_{t ∧ τ₀})²] ≤ E[M_0²] + E[A_{τ₀}]`. This gives a common `L²` bound in time and, together
-- with the stopped-martingale property, yields that `M^{τ₀}` is an `L²`-bounded martingale.
/-- Theorem 21.75 (2): under the same hypotheses, if `M_0 ∈ L²(μ)`, then the stopped process
`M^{τ₀}` is a martingale and is uniformly bounded in `L²`. -/
theorem stoppedProcess_martingale_and_l2_bounded_of_localMartingaleUpTo_of_memLp_two
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) (hτ₀ : IsStoppingTime ℱ τ₀) (hτ₀_lt : τ₀ < τ)
    (hA : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAτ₀ : Integrable (stoppedValue A τ₀) μ)
    (hM0_sq : MemLp (M 0) 2 μ) :
    Martingale (stoppedProcess M τ₀) ℱ μ ∧
      ∃ C : NNReal, ∀ t : NNReal, eLpNorm (stoppedProcess M τ₀ t) 2 μ ≤ C := by
  have hτ₀_fin : ∀ ω : Ω, τ₀ ω ≠ ∞ := fun ω ↦ ne_top_of_lt (hτ₀_lt ω)
  have _hSliceVariationBound :
      ∀ t ω, stoppedValue A (fun ω' ↦ min (τ₀ ω') (t : ENNReal)) ω ≤ stoppedValue A τ₀ ω := by
    intro t ω
    exact stoppedValue_le_stoppedValue_of_monotone
      (X := A) hA.monotone (σ := fun ω' ↦ min (τ₀ ω') (t : ENNReal)) (ρ := τ₀)
      (fun ω' ↦ min_le_left _ _) hτ₀_fin ω
  have hM_boundedApprox :
      HasBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M :=
    (isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
      (ℱ := ℱ) (μ := μ) (τ := τ) (M := M) hM.adapted hM.continuous).1
      hM.local_martingale_upTo
  rcases hM_boundedApprox with ⟨τSeq, hApprox, hBoundedSeq⟩
  let ρ : ℕ → Ω → ENNReal := fun n ω ↦ min (τ₀ ω) (τSeq n ω)
  have hρ_fin : ∀ n : ℕ, ∀ ω : Ω, ρ n ω ≠ ∞ := by
    intro n ω
    exact ne_top_of_le_ne_top (hτ₀_fin ω) (min_le_left _ _)
  have hEventually :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, τ₀ ω ≤ τSeq n ω :=
    ae_eventually_le_localizingApprox_of_lt
      (τ := τ) (τ₀ := τ₀) (τSeq := τSeq) hApprox hτ₀_lt
  have hApproxMart :
      ∀ n : ℕ, Martingale (stoppedProcess M (ρ n)) ℱ μ := by
    intro n
    have hDoubleStop :
        stoppedProcess (stoppedProcess M (τSeq n)) τ₀ = stoppedProcess M (ρ n) := by
      simpa [ρ, min_comm] using
        (stoppedProcess_stoppedProcess' :
          stoppedProcess (stoppedProcess M (τSeq n)) τ₀ =
            stoppedProcess M (fun ω ↦ min (τ₀ ω) (τSeq n ω)))
    have hStoppedMart :
        Martingale (stoppedProcess (stoppedProcess M (τSeq n)) τ₀) ℱ μ :=
      martingale_stoppedProcess_of_bounded
        (ℱ := ℱ) (μ := μ) (X := stoppedProcess M (τSeq n)) (hBoundedSeq n).1
        (continuous_stoppedProcess_of_continuous hM.continuous) (hBoundedSeq n).2 hτ₀
    -- Proof comment: each bounded owner `M^(τ_n)` stays a martingale after the extra stop at
    -- `τ₀`, and the double stop is exactly `M^(τ₀ ∧ τ_n)`.
    exact hDoubleStop ▸ hStoppedMart
  have hApproxSlice_tendsto :
      ∀ t : NNReal,
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ stoppedProcess M (ρ n) t ω) atTop
            (𝓝 (stoppedProcess M τ₀ t ω)) := by
    intro t
    filter_upwards [hEventually] with ω hω
    have hEventuallyEq :
        (fun n ↦ stoppedProcess M (ρ n) t ω) =ᶠ[atTop] fun _ ↦ stoppedProcess M τ₀ t ω := by
      filter_upwards [hω] with n hn
      have hρ_eq : ρ n ω = τ₀ ω := by
        simp [ρ, min_eq_left hn]
      simp [hρ_eq]
    -- Proof comment: once `τ_n(ω)` lies above `τ₀(ω)`, the approximate stopped process is
    -- literally the exact stopped process at time `t`.
    exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have hApproxSlice_meas :
      ∀ n : ℕ, ∀ t : NNReal, AEStronglyMeasurable (stoppedProcess M (ρ n) t) μ := by
    intro n t
    exact (hApproxMart n).integrable t |>.aestronglyMeasurable
  have hApproxSlice_sq :
      ∀ n : ℕ, ∀ t : NNReal,
        Integrable (fun ω ↦ (stoppedProcess M (ρ n) t ω) ^ 2) μ ∧
          ∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ ≤
            μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀] := by
    intro n t
    let σt : Ω → ENNReal := fun ω ↦ min (ρ n ω) (t : ENNReal)
    have hσt_stop : IsStoppingTime ℱ σt := (hτ₀.min (hApprox.2.1 n)).min_const t
    have hσt_fin : ∀ ω : Ω, σt ω ≠ ∞ := by
      intro ω
      exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    have hσt_le_τSeq : ∀ ω, σt ω ≤ τSeq n ω := by
      intro ω
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hσt_le_τ₀ : ∀ ω, σt ω ≤ τ₀ ω := by
      intro ω
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hVariationInt :
        Integrable (stoppedValue A σt) μ := by
      exact integrable_stoppedValue_of_monotone_of_le
        (ℱ := ℱ) (μ := μ) (X := A) hA.adapted hA.zero hA.monotone
        hA.continuous hσt_stop hτ₀ hσt_le_τ₀ hτ₀_fin hAτ₀
    have hVariationIntegral_le :
        μ[stoppedValue A σt] ≤ μ[stoppedValue A τ₀] := by
      exact integral_stoppedValue_le_of_monotone_of_le
        (μ := μ) (X := A) hA.monotone
        (σ := σt) (ρ := τ₀) hσt_le_τ₀ hτ₀_fin hVariationInt hAτ₀
    rcases
        stoppedValue_sq_integrable_and_integral_eq_initial_add_variation_of_boundedOwner
          (ℱ := ℱ) (μ := μ) (M := M) (A := A) hA
          (hτ' := hApprox.2.1 n) (hσ := hσt_stop) (hσ_fin := hσt_fin)
          (hσ_le := hσt_le_τSeq) (hOwner := (hBoundedSeq n).1)
          (hOwner_bdd := (hBoundedSeq n).2) hVariationInt with
      ⟨hSqInt, hSqEq⟩
    constructor
    · simpa [σt, ρ, stoppedValue_min_const_eq_stoppedProcess] using hSqInt
    · -- Proof comment: the fixed-time triple stop `τ₀ ∧ τ_n ∧ t` fits the same compensated-square
      -- owner, and the remaining bracket term is again bounded by `A_{τ₀}`.
      calc
        ∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ =
            μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A σt] := by
              simpa [σt, ρ, stoppedValue_min_const_eq_stoppedProcess] using hSqEq
        _ ≤ μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀] := by
              gcongr
  -- Route correction: the bounded approximants `M^(τ₀ ∧ τ_n)` and their fixed-time `L²` bounds
  -- are now in place. The remaining work is only the final `n → ∞` transfer of the martingale
  -- set-integral identities and the exact `eLpNorm` bound for the stopped process.
  let B : ℝ := μ[fun ω ↦ (M 0 ω) ^ 2] + μ[stoppedValue A τ₀]
  have hInitialSquare_nonneg : 0 ≤ μ[fun ω ↦ (M 0 ω) ^ 2] := by
    exact integral_nonneg fun ω ↦ sq_nonneg (M 0 ω)
  have hAτ₀_nonneg : 0 ≤ μ[stoppedValue A τ₀] := by
    have hAτ₀_nonneg_ae : ∀ᵐ ω ∂μ, 0 ≤ stoppedValue A τ₀ ω := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      -- Proof comment: monotonicity of the square-variation path and `A 0 = 0` force
      -- `A_{τ₀(ω)} ≥ 0`.
      simpa [stoppedValue, hA.zero] using
        (hA.monotone ω (show (0 : NNReal) ≤ (τ₀ ω).untopA by exact zero_le _))
    exact integral_nonneg_ae hAτ₀_nonneg_ae
  have hB_nonneg : 0 ≤ B := add_nonneg hInitialSquare_nonneg hAτ₀_nonneg
  have hApproxSlice_UI :
      ∀ t : NNReal, UniformIntegrable (fun n : ℕ ↦ stoppedProcess M (ρ n) t) 1 μ := by
    intro t
    -- Proof comment: the common second-moment estimate for the localized slices upgrades to
    -- uniform integrability in `L¹`.
    exact uniformIntegrable_one_of_integrable_sq_bdd
      (μ := μ) (f := fun n : ℕ ↦ stoppedProcess M (ρ n) t)
      (fun n ↦ hApproxSlice_meas n t) (fun n ↦ (hApproxSlice_sq n t).1)
      hB_nonneg (fun n ↦ by simpa [B] using (hApproxSlice_sq n t).2)
  have hStoppedSlice_integrable :
      ∀ t : NNReal, Integrable (stoppedProcess M τ₀ t) μ := by
    intro t
    -- Proof comment: the exact slice is the almost-sure limit of a uniformly integrable family.
    exact (hApproxSlice_UI t).integrable_of_ae_tendsto (hApproxSlice_tendsto t)
  have hApproxSlice_tendsto_L1 :
      ∀ t : NNReal,
        Tendsto
          (fun n ↦
            eLpNorm
              (fun ω ↦ stoppedProcess M (ρ n) t ω - stoppedProcess M τ₀ t ω)
              1 μ)
          atTop (𝓝 0) := by
    intro t
    -- Proof comment: fixed-time almost-sure convergence plus uniform integrability gives `L¹`
    -- convergence of the localized slices to the exact stopped slice.
    exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun n ↦ hApproxSlice_meas n t)
      (memLp_one_iff_integrable.2 (hStoppedSlice_integrable t))
      (hApproxSlice_UI t).unifIntegrable (hApproxSlice_tendsto t)
  have hStoppedSetIntegralEq :
      ∀ ⦃s t : NNReal⦄, s ≤ t → ∀ ⦃u : Set Ω⦄, u ∈ ℱ s →
        ∫ ω in u, stoppedProcess M τ₀ s ω ∂μ =
          ∫ ω in u, stoppedProcess M τ₀ t ω ∂μ := by
    intro s t hst u hu
    have hLimit_s :
        Tendsto (fun n ↦ ∫ ω in u, stoppedProcess M (ρ n) s ω ∂μ) atTop
          (𝓝 (∫ ω in u, stoppedProcess M τ₀ s ω ∂μ)) :=
      tendsto_restrictedIntegral_of_tendsto_L1
        (μ := μ) (s := u) (hStoppedSlice_integrable s)
        (fun n ↦ (hApproxMart n).integrable s) (hApproxSlice_tendsto_L1 s)
    have hLimit_t :
        Tendsto (fun n ↦ ∫ ω in u, stoppedProcess M (ρ n) t ω ∂μ) atTop
          (𝓝 (∫ ω in u, stoppedProcess M τ₀ t ω ∂μ)) :=
      tendsto_restrictedIntegral_of_tendsto_L1
        (μ := μ) (s := u) (hStoppedSlice_integrable t)
        (fun n ↦ (hApproxMart n).integrable t) (hApproxSlice_tendsto_L1 t)
    have hEqSeq :
        ∀ n, ∫ ω in u, stoppedProcess M (ρ n) s ω ∂μ =
          ∫ ω in u, stoppedProcess M (ρ n) t ω ∂μ := by
      intro n
      simpa using (hApproxMart n).setIntegral_eq hst hu
    have hLimit_t' :
        Tendsto (fun n ↦ ∫ ω in u, stoppedProcess M (ρ n) s ω ∂μ) atTop
          (𝓝 (∫ ω in u, stoppedProcess M τ₀ t ω ∂μ)) := by
      refine Tendsto.congr' ?_ hLimit_t
      exact Filter.Eventually.of_forall hEqSeq
    -- Proof comment: the restricted-integral martingale identity for each localized owner passes
    -- to the limit because both fixed-time slice families converge in `L¹`.
    exact tendsto_nhds_unique hLimit_s hLimit_t'
  have hStrongStopped : StronglyAdapted ℱ (stoppedProcess M τ₀) :=
    hM.adapted.stronglyAdapted.stoppedProcess hM.continuous hτ₀
  have hStoppedMart : Martingale (stoppedProcess M τ₀) ℱ μ := by
    refine ⟨hStrongStopped, ?_⟩
    intro s t hst
    -- Proof comment: identify the conditional expectation at time `s` by the equality of all
    -- restricted integrals over `ℱ s`.
    exact ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hStoppedSlice_integrable t)
      (fun u _ _ ↦ (hStoppedSlice_integrable s).integrableOn)
      (fun u hu _ ↦ hStoppedSetIntegralEq hst hu)
      ((hStrongStopped s).aestronglyMeasurable)
  let q : ℝ≥0∞ := ENNReal.ofReal (2 : ℝ)
  let C : NNReal := ⟨B ^ (1 / 2 : ℝ), Real.rpow_nonneg hB_nonneg _⟩
  have hApproxSlice_eLpNorm_two_le :
      ∀ n : ℕ, ∀ t : NNReal, eLpNorm (stoppedProcess M (ρ n) t) q μ ≤ C := by
    intro n t
    have hMemLp : MemLp (stoppedProcess M (ρ n) t) q μ := by
      refine (integrable_norm_rpow_iff (hApproxSlice_meas n t) ?_ ?_).1 ?_
      · norm_num [q]
      · simp [q]
      · simpa [q, Real.norm_eq_abs, sq_abs] using (hApproxSlice_sq n t).1
    have hNorm :
        eLpNorm (stoppedProcess M (ρ n) t) q μ =
          ENNReal.ofReal
            ((∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
      -- Proof comment: for `p = 2`, the `eLpNorm` is the square root of the second moment.
      simpa [q, Real.norm_eq_abs, sq_abs] using
        (MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm
          (f := stoppedProcess M (ρ n) t) (p := q) (μ := μ)
          (by norm_num [q]) (by simp [q]) hMemLp)
    have hSq_nonneg : 0 ≤ ∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ := by
      exact integral_nonneg fun ω ↦ sq_nonneg _
    have hPow :
        (∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hSq_nonneg (by simpa [B] using (hApproxSlice_sq n t).2) (by norm_num)
    calc
      eLpNorm (stoppedProcess M (ρ n) t) q μ =
          ENNReal.ofReal
            ((∫ ω, (stoppedProcess M (ρ n) t ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := hNorm
      _ ≤ ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := ENNReal.ofReal_le_ofReal hPow
      _ ≤ C := by simp [C]
  have hStopped_eLpNorm_two_le :
      ∀ t : NNReal, eLpNorm (stoppedProcess M τ₀ t) q μ ≤ C := by
    intro t
    -- Proof comment: lower semicontinuity of `eLpNorm` under almost-sure convergence transfers
    -- the common `L²` bound from the localized slices to the exact stopped slice.
    exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
      (u := atTop) (f := fun n : ℕ ↦ stoppedProcess M (ρ n) t)
      (g := stoppedProcess M τ₀ t) (C := C)
      (Filter.Eventually.of_forall fun n ↦ hApproxSlice_eLpNorm_two_le n t)
      (fun n ↦ hApproxSlice_meas n t) (hApproxSlice_tendsto t)
  exact ⟨hStoppedMart, ⟨C, fun t ↦ by simpa [q] using hStopped_eLpNorm_two_le t⟩⟩

end ProbabilityTheory
