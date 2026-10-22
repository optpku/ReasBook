/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Martingale.Centering

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u}
variable {E : Type v} [TopologicalSpace E]

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration NNReal mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X Y : NNReal → Ω → ℝ}

/-- The dyadic ceiling approximation `t ↦ 2^{-n} ⌈2^n t⌉` applied pointwise to a nonnegative random
time. -/
def dyadicCeilApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

/-- Helper: the event `{dyadicCeilApprox n τ ≤ t}` is the deterministic
threshold event for `τ` obtained by taking the dyadic predecessor of `t` on the mesh `2^{-n}`. -/
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
      -- Proof comment: the dyadic scale is strictly positive.
      dsimp [c]
      positivity
    have hDiv :
        dyadicCeilApprox n τ ω ≤ t ↔
          (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * t := by
      -- Proof comment: multiply by the positive mesh denominator to remove the quotient.
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
    -- Proof comment: the dyadic ceiling only records whether `τ` is below the last mesh point
    -- not exceeding `t`.
    exact hDiv.trans (hCeilFloor.trans hFloorDiv)
  exact_mod_cast hbody

-- Proof sketch: for each deterministic time `t`, the event
-- `{dyadicCeilApprox n τ ≤ t}` can be rewritten as `{τ ≤ k / 2^n}` for the appropriate dyadic
-- predecessor of `t`; this is measurable because `τ` is a stopping time.
/-- The dyadic ceiling approximation of a finite nonnegative stopping time is again a stopping
time. -/
theorem dyadicCeilApprox_isStoppingTime {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal) := by
  intro t
  let q : NNReal :=
    ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal) / ((2 : NNReal) ^ n))
  have hpow_pos : 0 < (2 : NNReal) ^ n := by
    -- Proof comment: the dyadic mesh denominator is positive.
    positivity
  have hq_le_t : q ≤ t := by
    -- Proof comment: the dyadic predecessor of `t` never exceeds `t`.
    dsimp [q]
    refine (div_le_iff₀ hpow_pos).2 ?_
    have hfloor :
        ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : NNReal)) ≤
          ((2 : NNReal) ^ n) * t := by
      have hfloorReal :
          (((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : ℕ) : ℝ)) ≤
            ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) := by
        exact Nat.floor_le (show 0 ≤ ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) by positivity)
      exact_mod_cast hfloorReal
    simpa [mul_comm] using hfloor
  -- Proof comment: rewrite the dyadic event to an original stopping event at time `q`, then move
  -- it forward along the filtration monotonicity `q ≤ t`.
  change MeasurableSet[ℱ t] {ω | (dyadicCeilApprox n τ ω : ENNReal) ≤ t}
  rw [dyadicCeilApprox_event_le_eq n τ t]
  simpa [q] using (ℱ.mono hq_le_t _ (hτ.measurableSet_le q))

/-- Helper: a dyadic ceiling overshoots a deterministic upper bound by at
most one mesh size. -/
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
    -- Proof comment: the ceiling of a nonnegative real lies at most one unit above the input.
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

/-- Helper: a dyadic ceiling overshoots the underlying time by at most one
mesh size. -/
lemma dyadicCeilApprox_le_self_add_mesh
    (m : ℕ) (τ : Ω → NNReal) :
    ∀ ω, dyadicCeilApprox m τ ω ≤ τ ω + ((2 : NNReal) ^ m)⁻¹ := by
  intro ω
  let c : NNReal := (2 : NNReal) ^ m
  have hc_pos : 0 < c := by
    -- Proof comment: the dyadic scale is strictly positive.
    dsimp [c]
    positivity
  have hceil : (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤ c * τ ω + 1 := by
    -- Proof comment: the ceiling of a nonnegative real lies at most one unit above the input.
    simpa using (Nat.ceil_lt_add_one (show 0 ≤ (c * τ ω : NNReal) by positivity)).le
  -- Proof comment: divide by the positive dyadic scale and rewrite the one-unit overshoot as one
  -- dyadic mesh width.
  dsimp [dyadicCeilApprox, c]
  rw [div_le_iff₀ hc_pos]
  have haux_eq : c * τ ω + 1 = (τ ω + c⁻¹) * c := by
    calc
      c * τ ω + 1 = c * τ ω + c⁻¹ * c := by
        rw [inv_mul_cancel₀]
        positivity
      _ = τ ω * c + c⁻¹ * c := by
        rw [mul_comm c (τ ω)]
      _ = (τ ω + c⁻¹) * c := by
        rw [add_mul]
  simpa [c] using hceil.trans haux_eq.le

/-- Helper: the dyadic mesh `2^{-n}` is dominated by the reciprocal mesh
`(n + 1)⁻¹`. -/
lemma dyadicMesh_le_inv_succ (n : ℕ) :
    ((2 : NNReal) ^ n)⁻¹ ≤ ((n + 1 : ℕ) : NNReal)⁻¹ := by
  have hnat : n + 1 ≤ 2 ^ n := by
    simpa using (Nat.choose_succ_le_two_pow n 1)
  have hnat' : ((n + 1 : ℕ) : NNReal) ≤ (2 : NNReal) ^ n := by
    exact_mod_cast hnat
  simpa [one_div] using
    (one_div_le_one_div_of_le (show (0 : NNReal) < ((n + 1 : ℕ) : NNReal) by positivity) hnat')

/-- Helper: dyadic ceiling approximations converge pointwise to the underlying
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
    (tendsto_nat_ceil_mul_div_atTop
      (show 0 ≤ (ρ ω : ℝ) from (ρ ω).2)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper: dyadic ceilings always stay to the right of the original time. -/
lemma self_le_dyadicCeilApprox
    (n : ℕ) (τ : Ω → NNReal) :
    ∀ ω, τ ω ≤ dyadicCeilApprox n τ ω := by
  intro ω
  let c : NNReal := (2 : NNReal) ^ n
  have hc_pos : 0 < c := by
    -- Proof comment: the dyadic scale is strictly positive.
    dsimp [c]
    positivity
  have hceil : c * τ ω ≤ (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) := by
    have hreal : (((c * τ ω : NNReal) : ℝ)) ≤ Nat.ceil (((c * τ ω : NNReal) : ℝ)) := Nat.le_ceil _
    exact_mod_cast hreal
  -- Proof comment: dividing the basic ceiling inequality by the positive scale gives the desired
  -- one-sided approximation.
  dsimp [dyadicCeilApprox, c]
  rw [le_div_iff₀ hc_pos]
  simpa [mul_comm] using hceil

/-- Helper: the dyadic ceiling approximation is monotone in the underlying
time. -/
lemma dyadicCeilApprox_mono
    (n : ℕ) {τ η : Ω → NNReal} (hτη : τ ≤ η) :
    dyadicCeilApprox n τ ≤ dyadicCeilApprox n η := by
  intro ω
  let c : NNReal := (2 : NNReal) ^ n
  have hc_pos : 0 < c := by
    -- Proof comment: the common dyadic scale is strictly positive, so the order comparison
    -- reduces to monotonicity of multiplication and of the ceiling map.
    dsimp [c]
    positivity
  have hmul :
      (((c * τ ω : NNReal) : ℝ)) ≤ (((c * η ω : NNReal) : ℝ)) := by
    exact_mod_cast (mul_le_mul_left' (hτη ω) c)
  have hceil :
      (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) ≤
        (Nat.ceil (((c * η ω : NNReal) : ℝ)) : NNReal) := by
    exact_mod_cast (Nat.ceil_le_ceil hmul)
  -- Proof comment: dividing the two ordered ceilings by the same positive dyadic scale preserves
  -- the inequality.
  change
    (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : NNReal) / c ≤
      (Nat.ceil (((c * η ω : NNReal) : ℝ)) : NNReal) / c
  refine NNReal.div_le_of_le_mul ?_
  rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc_pos.ne', mul_one]
  exact hceil

/-- Helper: refining the dyadic mesh can only decrease the ceiling
approximation. -/
lemma dyadicCeilApprox_succ_le
    (n : ℕ) (τ : Ω → NNReal) :
    ∀ ω, dyadicCeilApprox (n + 1) τ ω ≤ dyadicCeilApprox n τ ω := by
  intro ω
  let c : NNReal := (2 : NNReal) ^ n
  have hc_pos : 0 < c := by
    -- Proof comment: the dyadic scale at level `n` is strictly positive.
    dsimp [c]
    positivity
  have hpow : (2 : NNReal) ^ (n + 1) = (2 : NNReal) * c := by
    -- Proof comment: rewrite the finer dyadic denominator as `2 * 2^n`.
    simp [c, pow_succ, mul_comm, mul_left_comm, mul_assoc]
  have hceil :
      Nat.ceil ((((2 : NNReal) * c * τ ω : NNReal) : ℝ)) ≤
        2 * Nat.ceil (((c * τ ω : NNReal) : ℝ)) := by
    have hx :
        ((((2 : NNReal) * c * τ ω : NNReal) : ℝ)) =
          2 * (((c * τ ω : NNReal) : ℝ)) := by
      norm_num [mul_assoc]
    rw [hx]
    have hxceil :
        2 * (((c * τ ω : NNReal) : ℝ)) ≤
          ((2 * Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℕ) : ℝ) := by
      have hxceil' :
          2 * (((c * τ ω : NNReal) : ℝ)) ≤
            2 * (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℝ) := by
        gcongr
        exact Nat.le_ceil (((c * τ ω : NNReal) : ℝ))
      simpa using hxceil'
    exact Nat.ceil_le.2 hxceil
  let a : ℝ := (Nat.ceil ((((2 : NNReal) * c * τ ω : NNReal) : ℝ)) : ℕ)
  let b : ℝ := (Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℕ)
  have hreal : a / (2 * (c : ℝ)) ≤ b / (c : ℝ) := by
    have hc_real_pos : 0 < (c : ℝ) := by
      exact_mod_cast hc_pos
    have hceil_real :
        a ≤ 2 * b := by
      change (((Nat.ceil ((((2 : NNReal) * c * τ ω : NNReal) : ℝ)) : ℕ) : ℝ)) ≤
        2 * (((Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℕ) : ℝ))
      exact_mod_cast hceil
    have hc_real_ne : (c : ℝ) ≠ 0 := by
      exact_mod_cast hc_pos.ne'
    -- Proof comment: clear the positive denominator `2 * c` and reduce to the ceiling estimate
    -- already proved above.
    field_simp [hc_real_ne]
    nlinarith
  exact_mod_cast (by simpa [dyadicCeilApprox, hpow, c, a, b, mul_assoc] using hreal)

/-- Helper: the dyadic ceiling approximations form a decreasing family of
stopping times. -/
lemma dyadicCeilApprox_antitone
    (τ : Ω → NNReal) :
    Antitone fun n ↦ dyadicCeilApprox n τ := by
  intro n m hnm ω
  induction hnm with
  | refl =>
      exact le_rfl
  | @step k hnk ih =>
      exact le_trans (dyadicCeilApprox_succ_le k τ ω) ih

/-- Helper: every dyadic ceiling approximation has countable range. -/
lemma dyadicCeilApprox_countableRange (n : ℕ) (τ : Ω → NNReal) :
    (Set.range fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal)).Countable := by
  refine
    ((Set.countable_range
      fun k : ℕ ↦ ((((k : NNReal) / ((2 : NNReal) ^ n)) : NNReal) : ENNReal))).mono ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ), ?_⟩
  simp [dyadicCeilApprox]

/-- Helper: right continuity of the filtration can be tested along the
deterministic sequence `t + (n + 1)⁻¹`. -/
lemma filtration_iInf_add_inv_succ_eq
    [Filtration.IsRightContinuous ℱ] (t : NNReal) :
    (⨅ n : ℕ, ℱ (t + ((n + 1 : ℕ) : NNReal)⁻¹)) = ℱ t := by
  let hrc : Filtration.rightCont ℱ = ℱ := Filtration.IsRightContinuous.eq
  have hrc_t : Filtration.rightCont ℱ t = ℱ t := by
    simpa using congrArg (fun 𝓖 : Filtration NNReal mΩ ↦ 𝓖 t) hrc
  rw [← hrc_t, Filtration.rightCont_eq ℱ t]
  refine le_antisymm ?_ ?_
  · -- Proof comment: the reciprocal sequence is cofinal in the right-neighborhood filter of `t`,
    -- so every future stage dominates some term of the sequence.
    refine le_iInf₂ fun u hu ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hu)
    have hseq_le : t + ((n + 1 : ℕ) : NNReal)⁻¹ ≤ u := by
      simpa [add_comm, add_left_comm, add_assoc, add_tsub_cancel_of_le hu.le] using
        (add_lt_add_left hn t).le
    exact (iInf_le _ n).trans (ℱ.mono hseq_le)
  · -- Proof comment: every stage in the sequence lies strictly to the right of `t`, so the
    -- right-limit infimum is below each term of the sequence.
    refine le_iInf fun n ↦ ?_
    refine iInf₂_le_of_le (t + ((n + 1 : ℕ) : NNReal)⁻¹) ?_ le_rfl
    simp

/-- Helper: on the event `{σ ≤ t}`, the buffered dyadic event
`{σⁿ ≤ t + (n + 1)⁻¹}` is automatic. -/
lemma dyadicEvent_inter_le_buffer_eq
    (n : ℕ) (σ : Ω → NNReal) (s : Set Ω) (t : NNReal) :
    s ∩ {ω | (σ ω : ENNReal) ≤ t} =
      (s ∩ {ω | (σ ω : ENNReal) ≤ t}) ∩
        {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ t + ((n + 1 : ℕ) : NNReal)⁻¹} := by
  ext ω
  constructor
  · intro hω
    refine ⟨hω, ?_⟩
    have hσ_le_t : σ ω ≤ t := by
      exact_mod_cast hω.2
    -- Proof comment: the dyadic ceiling stays within one mesh of `σ`, and that mesh is at most
    -- `(n + 1)⁻¹`.
    have hbuffer :
        dyadicCeilApprox n σ ω ≤ t + ((n + 1 : ℕ) : NNReal)⁻¹ := by
      calc
        dyadicCeilApprox n σ ω ≤ σ ω + ((2 : NNReal) ^ n)⁻¹ :=
          dyadicCeilApprox_le_self_add_mesh n σ ω
        _ ≤ t + ((2 : NNReal) ^ n)⁻¹ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hσ_le_t (((2 : NNReal) ^ n)⁻¹)
        _ ≤ t + ((n + 1 : ℕ) : NNReal)⁻¹ :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left (dyadicMesh_le_inv_succ n) t
    exact_mod_cast hbuffer
  · intro hω
    exact hω.1

/-- Helper: a set measurable in every dyadic stopping-time σ-algebra
already satisfies the event tests for `𝓕_σ`. -/
lemma dyadicStoppingTimeMeasurableSpace_reverseInclusion
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    [Filtration.IsRightContinuous ℱ]
    {s : Set Ω}
    (hs : ∀ n, MeasurableSet[(dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] s)
    (t : NNReal) :
    MeasurableSet[ℱ t] (s ∩ {ω | (σ ω : ENNReal) ≤ t}) := by
  let A : Set Ω := s ∩ {ω | (σ ω : ENNReal) ≤ t}
  have hA_meas_stage :
      ∀ n, MeasurableSet[ℱ (t + ((n + 1 : ℕ) : NNReal)⁻¹)] A := by
    intro n
    let hσn : IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal) :=
      dyadicCeilApprox_isStoppingTime hσ n
    let c : NNReal := t + ((n + 1 : ℕ) : NNReal)⁻¹
    have hσ_le_σn :
        (fun ω ↦ (σ ω : ENNReal)) ≤ fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal) := by
      intro ω
      change (σ ω : ENNReal) ≤ (dyadicCeilApprox n σ ω : ENNReal)
      exact_mod_cast self_le_dyadicCeilApprox n σ ω
    have hσ_event : MeasurableSet[hσn.measurableSpace] {ω | (σ ω : ENNReal) ≤ t} := by
      -- Proof comment: `{σ ≤ t}` is measurable already in `𝓕_σ`, hence also in every larger
      -- dyadic stopping-time σ-algebra `𝓕_{σⁿ}`.
      exact
        (hσ.measurableSpace_mono hσn hσ_le_σn) _
          (hσ.measurableSet_le' t)
    have hA_meas_sigma : MeasurableSet[hσn.measurableSpace] A := by
      -- Proof comment: combine the stagewise measurability of `s` with the stopping event
      -- `{σ ≤ t}`.
      exact (hs n).inter hσ_event
    have hA_eq :
        A = A ∩ {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ c} := by
      -- Proof comment: rewrite the fixed event into the normal form expected by
      -- `measurableSet_inter_le_const_iff`.
      simpa [A, c] using dyadicEvent_inter_le_buffer_eq n σ s t
    have hA_meas_min :
        MeasurableSet[(hσn.min_const c).measurableSpace]
          (A ∩ {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ c}) := by
      have hA_meas_buffer :
          MeasurableSet[hσn.measurableSpace]
            (A ∩ {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ c}) := by
        exact hA_eq ▸ hA_meas_sigma
      exact (hσn.measurableSet_inter_le_const_iff A c).1 hA_meas_buffer
    have hA_meas_det :
        MeasurableSet[ℱ c] (A ∩ {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ c}) := by
      -- Proof comment: the bounded stopping time `σⁿ ∧ c` takes values below the deterministic
      -- horizon `c`, so its σ-algebra sits inside `𝓕_c`.
      exact
        ((hσn.min_const c).measurableSpace_le_of_le_const fun _ ↦ min_le_right _ _) _
          hA_meas_min
    -- Proof comment: after transport to `𝓕_c`, remove the redundant buffered event.
    rw [hA_eq]
    exact hA_meas_det
  have hA_meas_iInf :
      MeasurableSet[(⨅ n : ℕ, ℱ (t + ((n + 1 : ℕ) : NNReal)⁻¹))] A := by
    rw [MeasurableSpace.measurableSet_iInf]
    exact hA_meas_stage
  -- Proof comment: right continuity identifies the deterministic infimum with `𝓕_t`.
  rw [filtration_iInf_add_inv_succ_eq t] at hA_meas_iInf
  exact hA_meas_iInf

/-- Helper: the dyadic stopping-time σ-algebras decrease to `𝓕_σ` along a
right-continuous filtration. -/
lemma dyadicCeilApprox_measurableSpace_iInf_eq
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    [Filtration.IsRightContinuous ℱ] :
    (⨅ n : ℕ, (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace) = hσ.measurableSpace := by
  refine le_antisymm ?_ ?_
  · intro s hs
    rw [MeasurableSpace.measurableSet_iInf] at hs
    rw [hσ.measurableSet]
    refine ⟨(hs 0).1, ?_⟩
    intro t
    -- Route correction: instead of trying to make one global `⋂ n` object measurable in each
    -- dyadic stage, test the fixed event `s ∩ {σ ≤ t}` and transport it stage by stage.
    exact dyadicStoppingTimeMeasurableSpace_reverseInclusion hσ hs t
  · -- Proof comment: each dyadic ceiling dominates `σ`, so `𝓕_σ` is contained in every
    -- dyadic stopping-time σ-algebra `𝓕_{σⁿ}`.
    refine le_iInf fun n ↦ ?_
    have hσ_le_σn :
        (fun ω ↦ (σ ω : ENNReal)) ≤ fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal) := by
      intro ω
      change (σ ω : ENNReal) ≤ (dyadicCeilApprox n σ ω : ENNReal)
      exact_mod_cast self_le_dyadicCeilApprox n σ ω
    exact hσ.measurableSpace_mono (dyadicCeilApprox_isStoppingTime hσ n) hσ_le_σn

/-- Helper: the stopping-time `σ`-algebras of the dyadic ceiling approximations form a decreasing
family. -/
lemma dyadicCeilApprox_measurableSpace_antitone
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal)) :
    Antitone fun n ↦ (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace := by
  intro n m hnm
  have hmn' :
      (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) ≤
        fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal) := by
    intro ω
    exact
      show (dyadicCeilApprox m σ ω : ENNReal) ≤ (dyadicCeilApprox n σ ω : ENNReal) by
        exact_mod_cast (dyadicCeilApprox_antitone σ hnm ω)
  -- Proof comment: finer dyadic ceilings are smaller stopping times, hence generate smaller
  -- stopping-time `σ`-algebras.
  exact
    (dyadicCeilApprox_isStoppingTime hσ m).measurableSpace_mono
      (dyadicCeilApprox_isStoppingTime hσ n)
      hmn'

end ProbabilityTheory
