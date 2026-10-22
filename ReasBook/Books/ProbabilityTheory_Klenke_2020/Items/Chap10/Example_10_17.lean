/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- Helper for Example 10.17: the bounded truncation `τ ∧ n` of an `ℕ`-valued stopping time,
viewed as an `ℕ∞`-valued stopping time. -/
noncomputable def truncatedStoppingTime (τ : Ω → ℕ) (n : ℕ) : Ω → ℕ∞ :=
  fun ω ↦ min (τ ω : ℕ∞) n

/- Example 10.17 is `source-facing`: its public content is the expected-value identity for the
two-sided hitting time `τ_{a,b}` and the divergence of the one-sided hitting time `τ_a`. In this
workspace the executable owner route is the measurable modification of the walk already developed
in Example 10.16, together with the canonical hitting-time API `MeasureTheory.hittingAfter` and
the partial-sum martingale API from Example 10.6. -/
section SymmetricSimpleRandomWalk

variable {P : Measure Ω} {X : ℕ → Ω → ℤ}
variable (hX_zero : X 0 = 0)
variable (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
variable (hX_law : ∀ n,
  HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)

local instance : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure

omit mΩ in
/-- Helper for Example 10.17: enlarging the target set can only decrease the first hitting time
after `0`. -/
lemma hittingAfter_le_of_subset
    {β : Type*} {u : ℕ → Ω → β} {s t : Set β} {ω : Ω}
    (hst : s ⊆ t) :
    hittingAfter u t 0 ω ≤ hittingAfter u s 0 ω := by
  -- Proof comment: use the antitonicity of `hittingAfter` in the target set.
  exact hittingAfter_apply_anti (u := u) (n := 0) (ω := ω) hst

/-- Helper for Example 10.17: a measurable fair-sign increment family has unit square after
casting to `ℝ`. -/
lemma fairStepReal_sq_ae_eq_one
    {Y : ℕ → Ω → ℤ}
    [IsProbabilityMeasure P]
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_neg : ∀ n : ℕ, P ((Y n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hY_pos : ∀ n : ℕ, P ((Y n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    ∀ n, (fun ω ↦ ((Y n ω : ℝ) ^ 2)) =ᵐ[P] fun _ ↦ (1 : ℝ) := by
  intro n
  -- Proof comment: the fair-sign hypothesis forces every increment to be `±1` almost surely.
  filter_upwards [ae_eq_negOne_or_eq_one_of_fairSigns P Y hY_meas hY_neg hY_pos n] with ω hω
  rcases hω with hω | hω <;> simp [hω]

/-- Helper for Example 10.17: the real partial sums of a measurable fair-sign family have
compensated square martingale `Sₙ^2 - n`. -/
lemma fairStepPartialSums_squareMinusTime_martingale
    {Y : ℕ → Ω → ℤ}
    [IsProbabilityMeasure P]
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P)
    (hY_neg : ∀ n : ℕ, P ((Y n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hY_pos : ∀ n : ℕ, P ((Y n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹) :
    let stepReal : ℕ → Ω → ℝ := fun n ω ↦ (Y n ω : ℝ)
    let S : ℕ → Ω → ℝ := partialSum stepReal
    let hS_strMeas :
        ∀ n, StronglyMeasurable (S n) :=
      fun n ↦ (partialSum_measurable stepReal
        (fun k ↦ measurable_stepReal Y hY_meas k) n).stronglyMeasurable
    let ℱS : Filtration ℕ mΩ := Filtration.natural S hS_strMeas
    Martingale (fun n ω ↦ (S n ω) ^ 2 - n) ℱS P := by
  let stepReal : ℕ → Ω → ℝ := fun n ω ↦ (Y n ω : ℝ)
  let S : ℕ → Ω → ℝ := partialSum stepReal
  let hS_strMeas :
      ∀ n, StronglyMeasurable (S n) :=
    fun n ↦ (partialSum_measurable stepReal
      (fun k ↦ measurable_stepReal Y hY_meas k) n).stronglyMeasurable
  let ℱS : Filtration ℕ mΩ := Filtration.natural S hS_strMeas
  have hcast_meas : Measurable (fun z : ℤ ↦ (z : ℝ)) := measurable_of_countable _
  have hstepReal_indep : iIndepFun stepReal P := by
    -- Proof comment: independence survives composition with the measurable cast `ℤ → ℝ`.
    simpa [stepReal] using hY_indep.comp (fun _ z ↦ (z : ℝ)) (fun _ ↦ hcast_meas)
  have hstepReal_int : ∀ n, Integrable (stepReal n) P := by
    intro n
    -- Proof comment: a fair sign is bounded by `1` in absolute value, hence integrable.
    simpa [stepReal] using
      integrable_stepReal_of_fairSigns P Y hY_meas hY_neg hY_pos n
  have hstepReal_mean_zero : ∀ n, P[stepReal n] = 0 := by
    intro n
    -- Proof comment: the symmetric law makes the real-cast increment centered.
    simpa [stepReal] using
      integral_stepReal_eq_zero_of_fairSigns P Y hY_meas hY_neg hY_pos n
  have hstepReal_sq_int : ∀ n, Integrable (fun ω ↦ (stepReal n ω) ^ 2) P := by
    intro n
    -- Proof comment: after the `±1` normalization, the square is the constant function `1`.
    exact (integrable_const (1 : ℝ)).congr
      ((fairStepReal_sq_ae_eq_one (P := P) (Y := Y) hY_meas hY_neg hY_pos n).symm)
  have hstepReal_sq_mean_one : ∀ n, P[fun ω ↦ (stepReal n ω) ^ 2] = 1 := by
    intro n
    -- Proof comment: integrate the almost-sure square identity to collapse the deterministic
    -- square-variation compensator to the time index.
    calc
      P[fun ω ↦ (stepReal n ω) ^ 2] = ∫ ω, (1 : ℝ) ∂P := by
        exact integral_congr_ae
          (fairStepReal_sq_ae_eq_one (P := P) (Y := Y) hY_meas hY_neg hY_pos n)
      _ = 1 := by simp
  -- Proof comment: Example 10.6 already gives the compensated-square martingale with the
  -- deterministic second-moment sum; here that sum is exactly `n`.
  simpa [stepReal, S, ℱS, hS_strMeas, hstepReal_sq_mean_one] using
    (independentCenteredPartialSums_squareMinusDeterministicSquareVariation_martingale
      (Y := stepReal) (μ := P) (hY_meas := fun k ↦ measurable_stepReal Y hY_meas k)
      hstepReal_sq_int hstepReal_mean_zero hstepReal_indep)

include hX_zero hX_indep hX_law

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.17: if a measurable modification `W` agrees almost surely with the
original walk `X`, then the event "the two-sided hitting time equals the left hitting time"
agrees almost surely for `W` and `X`. -/
lemma twoSidedHitLeftEvent_ae_eq_original
    {W : ℕ → Ω → ℤ} {a : ℤ} {b : ℕ}
    (hW_eq_X : ∀ᵐ ω ∂P, ∀ n, W n ω = X n ω) :
    {ω | hittingAfter W ({a, (b : ℤ)} : Set ℤ) 0 ω = hittingAfter W ({a} : Set ℤ) 0 ω} =ᵐ[P]
      {ω | hittingAfter X ({a, (b : ℤ)} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω} := by
  -- Proof comment: pathwise equality of the two walks identifies both relevant hitting times.
  filter_upwards [hW_eq_X] with ω hω
  have hab :
      hittingAfter W ({a, (b : ℤ)} : Set ℤ) 0 ω =
        hittingAfter X ({a, (b : ℤ)} : Set ℤ) 0 ω :=
    hittingAfter_zero_eq_of_forall_eq (u := W) (v := X)
      (s := ({a, (b : ℤ)} : Set ℤ)) (ω := ω) hω
  have ha :
      hittingAfter W ({a} : Set ℤ) 0 ω =
        hittingAfter X ({a} : Set ℤ) 0 ω :=
    hittingAfter_zero_eq_of_forall_eq (u := W) (v := X)
      (s := ({a} : Set ℤ)) (ω := ω) hω
  simpa using
    (by rw [hab, ha] :
      (hittingAfter W ({a, (b : ℤ)} : Set ℤ) 0 ω = hittingAfter W ({a} : Set ℤ) 0 ω) =
        (hittingAfter X ({a, (b : ℤ)} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω))

omit hX_zero in
/-- Helper for Example 10.17: the canonical measurable modification of the symmetric simple
random walk hits the two-sided boundary `{a, (b : ℤ)}` almost surely. -/
lemma twoSidedHittingAfter_ae_ne_top
    {a : ℤ} {b : ℕ} (ha : a < 0) (hb : 0 < b) :
    let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
    let Ym : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
    let W : ℕ → Ω → ℤ := randomWalkProcess Ym
    ∀ᵐ ω ∂P, hittingAfter W ({a, (b : ℤ)} : Set ℤ) 0 ω ≠ ⊤ := by
  dsimp
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Ym : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  let W : ℕ → Ω → ℤ := randomWalkProcess Ym
  have hYm_eq : ∀ n, Δ n =ᵐ[P] Ym n := by
    intro n
    simpa [Δ, Ym] using (hX_law n).aemeasurable.ae_eq_mk
  have hYm_meas : ∀ n, Measurable (Ym n) := by
    intro n
    simpa [Ym] using (hX_law n).aemeasurable.measurable_mk
  have hYm_indep : iIndepFun Ym P := hX_indep.congr hYm_eq
  have hYm_law : ∀ n, HasLaw (Ym n) symmetricRademacherLaw P := by
    intro n
    exact (hX_law n).congr (hYm_eq n).symm
  have hYm_neg : ∀ n : ℕ, P ((Ym n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Ym n) (hYm_law n)).1
  have hYm_pos : ∀ n : ℕ, P ((Ym n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Ym n) (hYm_law n)).2
  have hYm_signs : ∀ᵐ ω ∂P, ∀ n, Ym n ω = (-1 : ℤ) ∨ Ym n ω = 1 := by
    exact ae_all_iff.2 fun n ↦
      ae_eq_negOne_or_eq_one_of_fairSigns P Ym hYm_meas hYm_neg hYm_pos n
  have hτa_lt_top : ∀ᵐ ω ∂P, hittingAfter W ({a} : Set ℤ) 0 ω < ⊤ := by
    have hNegYm_meas : ∀ n, Measurable (fun ω ↦ -Ym n ω) := by
      intro n
      exact measurable_neg.comp (hYm_meas n)
    have hNegYm_indep : iIndepFun (fun n ω ↦ -Ym n ω) P := by
      simpa using hYm_indep.comp (fun _ z ↦ (-z : ℤ)) (fun _ ↦ measurable_neg)
    have hNegYm_neg : ∀ n : ℕ, P ((fun ω ↦ -Ym n ω) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
      intro n
      have hset : (fun ω ↦ -Ym n ω) ⁻¹' {(-1 : ℤ)} = (Ym n) ⁻¹' {(1 : ℤ)} := by
        ext ω
        simp
      rw [hset]
      exact hYm_pos n
    have hNegYm_pos : ∀ n : ℕ, P ((fun ω ↦ -Ym n ω) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
      intro n
      have hset : (fun ω ↦ -Ym n ω) ⁻¹' {(1 : ℤ)} = (Ym n) ⁻¹' {(-1 : ℤ)} := by
        ext ω
        constructor <;> intro h <;> simp at h ⊢ <;> omega
      rw [hset]
      exact hYm_neg n
    filter_upwards
      [ae_infinite_partial_sum_ge_of_independent_fair_signs
          P (fun n ω ↦ -Ym n ω) hNegYm_meas hNegYm_indep hNegYm_neg hNegYm_pos,
        hYm_signs] with ω hωInf hωSigns
    have hne : hittingAfter W ({a} : Set ℤ) 0 ω ≠ ⊤ := by
      intro htop
      have hW_zero : W 0 ω = 0 := by
        simpa [W] using congrFun (randomWalkProcess_zero Ym) ω
      have hW_step :
          ∀ n, W (n + 1) ω - W n ω = (-1 : ℤ) ∨ W (n + 1) ω - W n ω = 1 := by
        intro n
        have hinc : W (n + 1) ω - W n ω = Ym n ω := by
          simpa [W] using randomWalkProcess_increment Ym n ω
        simpa [hinc] using hωSigns n
      have hstrict :=
        strictLeftBoundary_of_hittingAfter_eq_top
          (fun n ↦ W n ω) hW_zero hW_step ha htop
      rcases (hωInf (-a)).nonempty with ⟨n, hn⟩
      have hle : W n ω ≤ a := by
        have hneg_ge : -a ≤ -W n ω := by
          simpa [W, random_walk_partial_sum, randomWalkProcess_apply, Finset.sum_neg_distrib] using
            hn
        omega
      exact not_le_of_gt (hstrict n) hle
    simpa [lt_top_iff_ne_top] using hne
  -- Proof comment: hitting the left boundary at a finite time already forces the two-sided
  -- hitting time to be finite.
  filter_upwards [hτa_lt_top] with ω hωa
  have hτa_ne : hittingAfter W ({a} : Set ℤ) 0 ω ≠ ⊤ := ne_of_lt hωa
  let ia : ℕ := (hittingAfter W ({a} : Set ℤ) 0 ω).untop hτa_ne
  have hia : ia = (hittingAfter W ({a} : Set ℤ) 0 ω).untopA := by
    dsimp [ia]
    rw [WithTop.untopA_eq_untop hτa_ne]
  have hmem_a : W ia ω ∈ ({a} : Set ℤ) := by
    simpa [Set.mem_singleton_iff, hia] using
      hittingAfter_mem_set_of_ne_top
        (u := W) (s := ({a} : Set ℤ)) (n := 0) (ω := ω) hτa_ne
  have hmem_ab : W ia ω ∈ ({a, (b : ℤ)} : Set ℤ) := by
    have hEq : W ia ω = a := by
      simpa [Set.mem_singleton_iff] using hmem_a
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, hEq]
  have hle_ab : hittingAfter W ({a, (b : ℤ)} : Set ℤ) 0 ω ≤ ia := by
    exact hittingAfter_le_of_mem
      (u := W) (s := ({a, (b : ℤ)} : Set ℤ)) (n := 0) (ω := ω)
      (i := ia) (by simp [ia]) hmem_ab
  exact ne_of_lt (lt_of_le_of_lt hle_ab (by simp [ia]))

omit mΩ hX_zero hX_indep hX_law in
/-- Helper for Example 10.17: coercing the finite truncation
`σₙ ω := (min (τ ω) n).untopA` back to `ℕ∞` recovers the original minimum. -/
lemma twoSidedTruncation_coe_eq_min
    {τ : Ω → ℕ∞} (n : ℕ) :
    let σn : Ω → ℕ := fun ω ↦ (min (τ ω) (n : ℕ∞)).untopA
    (fun ω ↦ ((σn ω : ℕ) : ℕ∞)) = fun ω ↦ min (τ ω) (n : ℕ∞) := by
  dsimp
  funext ω
  have hmin : min (τ ω) (n : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  rw [WithTop.untopA_eq_untop hmin]
  exact WithTop.coe_untop _ _

omit mΩ hX_zero hX_indep hX_law in
/-- Helper for Example 10.17: stopping at the `ℕ∞` truncation `min (τ,n)` agrees with stopping at
the coerced finite truncation `σₙ`. -/
lemma stoppedValue_twoSidedTruncation_eq_coe
    {β : Type*} (u : ℕ → Ω → β) {τ : Ω → ℕ∞} (n : ℕ) :
    let σn : Ω → ℕ := fun ω ↦ (min (τ ω) (n : ℕ∞)).untopA
    stoppedValue u (fun ω ↦ min (τ ω) (n : ℕ∞)) =
      stoppedValue u (fun ω ↦ ((σn ω : ℕ) : ℕ∞)) := by
  dsimp
  funext ω
  have hmin : min (τ ω) (n : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  change
    u ((min (τ ω) (n : ℕ∞)).untopA) ω =
      u (((((min (τ ω) (n : ℕ∞)).untopA : ℕ) : ℕ∞)).untopA) ω
  simp

omit mΩ hX_zero hX_indep hX_law in
/-- Helper for Example 10.17: a finite stopping time bounded by `n` is unchanged by truncation at
`n` when viewed as an `ℕ∞`-valued stopping time. -/
lemma truncatedStoppingTime_eq_coe_of_le
    {τ : Ω → ℕ} {n : ℕ} (hτ_le : ∀ ω, τ ω ≤ n) :
    truncatedStoppingTime τ n = fun ω ↦ ((τ ω : ℕ) : ℕ∞) := by
  -- Proof comment: once `τ ω ≤ n`, the truncation `min (τ ω) n` is exactly `τ ω`.
  funext ω
  simpa [truncatedStoppingTime] using
    (min_eq_left (show (τ ω : ℕ∞) ≤ n by exact_mod_cast hτ_le ω))

/- API note: keep the two-sided boundary on the integer owner surface
`hittingAfter X ({a, b} : Set ℤ) 0`, matching Example 10.16 and the source statement. -/
/-- Example 10.17: for a symmetric simple random walk started at `0`, the expected first time
to hit either `a < 0` or the positive right boundary `b : ℤ` is `|a| b`. The one-sided
hitting-time divergence and the real-valued expectation corollary are stated separately below. -/
theorem symmetricSimpleRandomWalk_lintegral_hittingTimeFormulas
    {a b : ℤ} (ha : a < 0) (hb : 0 < b) :
    lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, b} : Set ℤ) 0 ω)) =
      ENNReal.ofReal ((Int.natAbs a : ℝ) * b) := by
  -- Route correction: keep the truncation on the owner `ℕ∞` surface `τtrunc n = min τab n`.
  -- This avoids the older `σn : Ω → ℕ` transport churn and lets optional stopping, DCT, and MCT
  -- run directly against the canonical stopping-time API.
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Ym : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  let W : ℕ → Ω → ℤ := randomWalkProcess Ym
  have hYm_eq : ∀ n, Δ n =ᵐ[P] Ym n := by
    intro n
    -- Proof comment: replace each increment by the measurable representative supplied by `HasLaw`.
    simpa [Δ, Ym] using (hX_law n).aemeasurable.ae_eq_mk
  have hYm_meas : ∀ n, Measurable (Ym n) := by
    intro n
    -- Proof comment: the measurable representative is measurable by construction.
    simpa [Ym] using (hX_law n).aemeasurable.measurable_mk
  have hYm_indep : iIndepFun Ym P := hX_indep.congr hYm_eq
  have hYm_law : ∀ n, HasLaw (Ym n) symmetricRademacherLaw P := by
    intro n
    exact (hX_law n).congr (hYm_eq n).symm
  have hYm_neg : ∀ n : ℕ, P ((Ym n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Ym n) (hYm_law n)).1
  have hYm_pos : ∀ n : ℕ, P ((Ym n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Ym n) (hYm_law n)).2
  have hYm_signs : ∀ᵐ ω ∂P, ∀ n, Ym n ω = (-1 : ℤ) ∨ Ym n ω = 1 := by
    exact ae_all_iff.2 fun n ↦
      ae_eq_negOne_or_eq_one_of_fairSigns P Ym hYm_meas hYm_neg hYm_pos n
  have hW_eq_X : ∀ᵐ ω ∂P, ∀ n, W n ω = X n ω := by
    have h_all : ∀ᵐ ω ∂P, ∀ n, Δ n ω = Ym n ω := by
      simpa [Filter.EventuallyEq] using (ae_all_iff.2 hYm_eq)
    filter_upwards [h_all] with ω hω n
    calc
      W n ω = random_walk_partial_sum Ym n ω := by
        simpa [W] using randomWalkProcess_apply Ym n ω
      _ = random_walk_partial_sum Δ n ω := by
        unfold random_walk_partial_sum
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact (hω j).symm
      _ = X n ω := by
        simpa [Δ] using symmetricSimpleRandomWalk_position_eq_partialSum hX_zero n ω
  have hτW_eq_X :
      ∀ᵐ ω ∂P, hittingAfter W ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a, b} : Set ℤ) 0 ω := by
    -- Proof comment: pathwise equality of the measurable modification identifies the hitting time.
    filter_upwards [hW_eq_X] with ω hω
    exact hittingAfter_zero_eq_of_forall_eq
      (u := W) (v := X) (s := ({a, b} : Set ℤ)) (ω := ω) hω
  let stepReal : ℕ → Ω → ℝ := fun n ω ↦ (Ym n ω : ℝ)
  let Wℝ : ℕ → Ω → ℝ := partialSum stepReal
  have hWℝ_eq : ∀ n ω, Wℝ n ω = (W n ω : ℝ) := by
    intro n ω
    -- Proof comment: the real partial sums are just the integer walk cast into `ℝ`.
    simpa [Wℝ, stepReal, W] using partialSum_intCast_eq_randomWalkProcess Ym n ω
  have hWℝ_strMeas :
      ∀ n, StronglyMeasurable (Wℝ n) := by
    intro n
    -- Proof comment: finite partial sums of measurable real increments remain measurable.
    exact (partialSum_measurable stepReal
      (fun k ↦ measurable_stepReal Ym hYm_meas k) n).stronglyMeasurable
  let ℱW : Filtration ℕ mΩ := Filtration.natural Wℝ hWℝ_strMeas
  let τab : Ω → ℕ∞ := hittingAfter W ({a, b} : Set ℤ) 0
  let τa : Ω → ℕ∞ := hittingAfter W ({a} : Set ℤ) 0
  let τtrunc : ℕ → Ω → ℕ∞ := fun n ω ↦ min (τab ω) (n : ℕ∞)
  let F : ℕ → Ω → ℝ := fun n ω ↦ (stoppedValue Wℝ (τtrunc n) ω) ^ 2
  let G : ℕ → Ω → ℝ := fun n ω ↦ ((τtrunc n ω).untopA : ℝ)
  let H : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ENat.toENNReal (τtrunc n ω)
  have hτab_eq :
      hittingAfter Wℝ ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 = τab := by
    funext ω
    calc
      hittingAfter Wℝ ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 ω =
          hittingAfter (fun n ω' ↦ (W n ω' : ℝ))
            ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 ω := by
              exact hittingAfter_zero_eq_of_forall_eq
                (u := Wℝ) (v := fun n ω' ↦ (W n ω' : ℝ))
                (s := ({(a : ℝ), (b : ℝ)} : Set ℝ))
                (ω := ω) (fun n ↦ hWℝ_eq n ω)
      _ = τab ω := by
        simpa [τab] using hittingAfter_intCast_pair_eq (u := W) (ω := ω) (a := a) (b := b)
  have hτa_eq :
      hittingAfter Wℝ ({(a : ℝ)} : Set ℝ) 0 = τa := by
    funext ω
    calc
      hittingAfter Wℝ ({(a : ℝ)} : Set ℝ) 0 ω =
          hittingAfter (fun n ω' ↦ (W n ω' : ℝ))
            ({(a : ℝ)} : Set ℝ) 0 ω := by
              exact hittingAfter_zero_eq_of_forall_eq
                (u := Wℝ) (v := fun n ω' ↦ (W n ω' : ℝ))
                (s := ({(a : ℝ)} : Set ℝ))
                (ω := ω) (fun n ↦ hWℝ_eq n ω)
      _ = τa ω := by
        simpa [τa] using hittingAfter_intCast_singleton_eq (u := W) (ω := ω) (a := a)
  have hτab_stop : IsStoppingTime ℱW τab := by
    -- Proof comment: rewrite the integer hitting time as a real hitting time of the adapted walk.
    rw [← hτab_eq]
    simpa [Set.insert_comm] using
      Adapted.isStoppingTime_hittingAfter
        (u := Wℝ) (s := ({(a : ℝ), (b : ℝ)} : Set ℝ)) (n := 0)
        (Filtration.stronglyAdapted_natural hWℝ_strMeas).adapted
        ((measurableSet_singleton (b : ℝ)).insert (a : ℝ))
  have hτa_stop : IsStoppingTime ℱW τa := by
    -- Proof comment: the same real-cast identification gives the left-boundary stopping time.
    rw [← hτa_eq]
    simpa using
      Adapted.isStoppingTime_hittingAfter
        (u := Wℝ) (s := ({(a : ℝ)} : Set ℝ)) (n := 0)
        (Filtration.stronglyAdapted_natural hWℝ_strMeas).adapted
        (measurableSet_singleton (a : ℝ))
  have hbNat : 0 < Int.toNat b := by
    have hbNatZ : (0 : ℤ) < Int.toNat b := by
      simpa [Int.toNat_of_nonneg hb.le] using hb
    exact_mod_cast hbNatZ
  have hbCast : ((Int.toNat b : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb.le
  have hτab_ae_ne_top : ∀ᵐ ω ∂P, τab ω ≠ ⊤ := by
    -- Proof comment: the measurable modification inherits two-sided recurrence from the walk.
    simpa [τab, hbCast] using
      (twoSidedHittingAfter_ae_ne_top
        (P := P) (X := X) hX_indep hX_law (a := a) (b := Int.toNat b) ha hbNat)
  have hτab_le_τa : ∀ ω, τab ω ≤ τa ω := by
    intro ω
    exact hittingAfter_le_of_subset
      (u := W) (s := ({a} : Set ℤ)) (t := ({a, b} : Set ℤ)) (ω := ω)
      (by intro x hx; left; simpa [Set.mem_singleton_iff] using hx)
  have hτab_le_τb : ∀ ω, τab ω ≤ hittingAfter W ({b} : Set ℤ) 0 ω := by
    intro ω
    exact hittingAfter_le_of_subset
      (u := W) (s := ({b} : Set ℤ)) (t := ({a, b} : Set ℤ)) (ω := ω)
      (by intro x hx; right; simpa [Set.mem_singleton_iff] using hx)
  have hτtrunc_stop : ∀ n, IsStoppingTime ℱW (τtrunc n) := by
    intro n
    exact hτab_stop.min_const n
  have hWℝ_martingale :
      Martingale (fun n ω ↦ (Wℝ n ω) ^ 2 - n) ℱW P := by
    -- Proof comment: the fair-sign square-minus-time martingale is the owner process for OST.
    simpa [stepReal, Wℝ, ℱW] using
      (fairStepPartialSums_squareMinusTime_martingale
        (P := P) (Y := Ym) hYm_meas hYm_indep hYm_neg hYm_pos)
  have hStopped_meas :
      ∀ n, Measurable (stoppedValue Wℝ (τtrunc n)) := by
    intro n
    -- Proof comment: bounded stopped values are measurable on the natural filtration.
    have hStopped_meas_h := measurable_stoppedValue
        (Filtration.stronglyAdapted_natural hWℝ_strMeas).progMeasurable_of_discrete
        (hτtrunc_stop n)
    intro s hs
    exact (hτtrunc_stop n).measurableSpace_le _ (hStopped_meas_h hs)
  have hG_meas : ∀ n, Measurable (G n) := by
    intro n
    -- Proof comment: `G n` is a countable-valued measurable transform of the truncation.
    let τn : Ω → WithTop ℕ := fun ω ↦ τtrunc n ω
    have hτn_meas_h : Measurable[(hτtrunc_stop n).measurableSpace] τn :=
      (hτtrunc_stop n).measurable
    have hτn_meas : Measurable τn := by
      intro s hs
      exact (hτtrunc_stop n).measurableSpace_le _ (hτn_meas_h hs)
    simpa [τn, G] using
      (measurable_of_countable fun t : WithTop ℕ ↦ ((t.untopA : ℕ) : ℝ)).comp hτn_meas
  have hStopped_bound :
      ∀ n, ∀ᵐ ω ∂P, ‖stoppedValue Wℝ (τtrunc n) ω‖ ≤ (b - a : ℝ) := by
    intro n
    -- Route correction: keep the truncation on the `ℕ∞` owner surface and compare it directly to
    -- the stopped process from Example 10.16, instead of coercing to an auxiliary `ℕ` surface.
    filter_upwards [hYm_signs] with ω hωSigns
    have hW_zero : W 0 ω = 0 := by
      simpa [W] using congrFun (randomWalkProcess_zero Ym) ω
    have hW_step :
        ∀ k, W (k + 1) ω - W k ω = (-1 : ℤ) ∨ W (k + 1) ω - W k ω = 1 := by
      intro k
      have hinc : W (k + 1) ω - W k ω = Ym k ω := by
        simpa [W] using randomWalkProcess_increment Ym k ω
      simpa [hinc] using hωSigns k
    have hstopEq :
        stoppedValue Wℝ (τtrunc n) ω = stoppedProcess Wℝ τab n ω := by
      simpa [τtrunc, min_comm] using
        (stoppedProcess_eq_stoppedValue_apply (u := Wℝ) (τ := τab) n ω).symm
    by_cases hτ : τab ω ≤ n
    · have hτ_ne : τab ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) hτ
      have hmem : W (τab ω).untopA ω ∈ ({a, b} : Set ℤ) := by
        simpa [τab] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({a, b} : Set ℤ)) (n := 0) (ω := ω) hτ_ne)
      have hcast : Wℝ (τab ω).untopA ω = (W (τab ω).untopA ω : ℝ) := hWℝ_eq _ _
      have hproc : stoppedProcess Wℝ τab n ω = Wℝ (τab ω).untopA ω := by
        exact stoppedProcess_eq_of_ge hτ
      rw [hstopEq, hproc, hcast]
      rcases (by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem :
          W (τab ω).untopA ω = a ∨ W (τab ω).untopA ω = b) with hval | hval
      · rw [hval, Real.norm_eq_abs, abs_of_nonpos (show (a : ℝ) ≤ 0 by exact_mod_cast ha.le)]
        nlinarith [show (a : ℝ) < 0 by exact_mod_cast ha, show (0 : ℝ) < b by exact_mod_cast hb]
      · rw [hval, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ b by exact_mod_cast hb.le)]
        nlinarith [show (a : ℝ) < 0 by exact_mod_cast ha, show (0 : ℝ) < b by exact_mod_cast hb]
    · have hlt : (n : ℕ∞) < τab ω := lt_of_not_ge hτ
      have hlt_a : (n : ℕ∞) < τa ω := lt_of_lt_of_le hlt (hτab_le_τa ω)
      have hlt_b : (n : ℕ∞) < hittingAfter W ({b} : Set ℤ) 0 ω :=
        lt_of_lt_of_le hlt (hτab_le_τb ω)
      have ha_lt : a < W n ω := by
        exact strictLeftBoundary_before_hitting
          (fun k ↦ W k ω) hW_zero hW_step ha n hlt_a
      have hb_gt : W n ω < b := by
        exact strictRightBoundary_before_hitting
          (fun k ↦ W k ω) hW_zero hW_step hb n hlt_b
      have hcast : Wℝ n ω = (W n ω : ℝ) := hWℝ_eq n ω
      have hproc : stoppedProcess Wℝ τab n ω = Wℝ n ω := by
        exact stoppedProcess_eq_of_le (le_of_lt hlt)
      have ha_lt_real : (a : ℝ) < (W n ω : ℝ) := by exact_mod_cast ha_lt
      have hb_gt_real : (W n ω : ℝ) < (b : ℝ) := by exact_mod_cast hb_gt
      rw [hstopEq, hproc, hcast, Real.norm_eq_abs]
      refine abs_le.2 ?_
      constructor <;> nlinarith [ha_lt_real, hb_gt_real,
        show (a : ℝ) < 0 by exact_mod_cast ha,
        show (0 : ℝ) < b by exact_mod_cast hb]
  have hF_bound :
      ∀ n, ∀ᵐ ω ∂P, F n ω ≤ (b - a : ℝ) ^ 2 := by
    intro n
    filter_upwards [hStopped_bound n] with ω hω
    have habs : |stoppedValue Wℝ (τtrunc n) ω| ≤ (b - a : ℝ) := by
      simpa [Real.norm_eq_abs] using hω
    have hbound :
        (stoppedValue Wℝ (τtrunc n) ω) ^ 2 ≤ (b - a : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ (b - a : ℝ) := by
        nlinarith [show (a : ℝ) < 0 by exact_mod_cast ha, show (0 : ℝ) < b by exact_mod_cast hb]
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hnonneg] using habs)
    simpa [F] using hbound
  have hG_nonneg : ∀ n, 0 ≤ᵐ[P] G n := by
    intro n
    refine Filter.Eventually.of_forall ?_
    intro ω
    simp [G, τtrunc]
  have hG_bound :
      ∀ n, ∀ᵐ ω ∂P, |G n ω| ≤ n := by
    intro n
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hne : τtrunc n ω ≠ ⊤ := by
      exact ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    have hcoetop : (((τtrunc n ω).untopA : ℕ) : ℕ∞) = τtrunc n ω := by
      rw [WithTop.untopA_eq_untop hne]
      exact WithTop.coe_untop _ _
    have hle_nat : (τtrunc n ω).untopA ≤ n := by
      exact_mod_cast (show (((τtrunc n ω).untopA : ℕ) : ℕ∞) ≤ n by
        rw [hcoetop]
        exact min_le_right _ _)
    have hnonneg : 0 ≤ G n ω := by
      simp [G, τtrunc]
    have hle_real : (((τtrunc n ω).untopA : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hle_nat
    simpa [Real.norm_eq_abs, G, abs_of_nonneg hnonneg] using hle_real
  have hF_int : ∀ n, Integrable (F n) P := by
    intro n
    have hboundnorm : ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (b - a : ℝ) ^ 2 := by
      filter_upwards [hF_bound n] with ω hω
      have hnonneg : 0 ≤ F n ω := sq_nonneg _
      rwa [Real.norm_of_nonneg hnonneg]
    exact Integrable.mono' (integrable_const ((b - a : ℝ) ^ 2))
      (((hStopped_meas n).stronglyMeasurable.pow 2).aestronglyMeasurable) hboundnorm
  have hG_int : ∀ n, Integrable (G n) P := by
    intro n
    have hboundnorm : ∀ᵐ ω ∂P, ‖G n ω‖ ≤ n := by
      simpa [Real.norm_eq_abs] using hG_bound n
    exact Integrable.mono' (integrable_const (n : ℝ))
      ((hG_meas n).stronglyMeasurable.aestronglyMeasurable) hboundnorm
  have hSquare_eq_time :
      ∀ n, ∫ ω, F n ω ∂P = ∫ ω, G n ω ∂P := by
    intro n
    have hzero_le : ∀ ω, (0 : ℕ∞) ≤ τtrunc n ω := by
      intro ω
      simp [τtrunc]
    have hEq :
        P[stoppedValue (fun k ω ↦ (Wℝ k ω) ^ 2 - k) (τtrunc n)] =
          P[stoppedValue (fun k ω ↦ (Wℝ k ω) ^ 2 - k) (fun _ ↦ (0 : ℕ∞))] := by
      exact martingale_expected_stoppedValue_eq_of_le_of_bounded
        (X := fun k ω ↦ (Wℝ k ω) ^ 2 - k) (μ := P) (ℱ := ℱW)
        hWℝ_martingale (isStoppingTime_const ℱW 0) (hτtrunc_stop n)
        hzero_le (fun ω ↦ min_le_right _ _)
    have hEq_zero :
        ∫ ω, (F n ω - G n ω) ∂P = 0 := by
      calc
        ∫ ω, (F n ω - G n ω) ∂P =
            P[stoppedValue (fun k ω ↦ (Wℝ k ω) ^ 2 - k) (τtrunc n)] := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro ω
              simp [F, G, τtrunc, stoppedValue]
        _ = P[stoppedValue (fun k ω ↦ (Wℝ k ω) ^ 2 - k) (fun _ ↦ (0 : ℕ∞))] := hEq
        _ = ∫ ω, ((Wℝ 0 ω) ^ 2 - 0) ∂P := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro ω
          have hzero : ((0 : ℕ∞).untopA : ℕ) = 0 := by rfl
          simp [stoppedValue, hzero]
        _ = 0 := by
          simp [Wℝ, partialSum_apply]
    have hSub :
        ∫ ω, (F n ω - G n ω) ∂P = ∫ ω, F n ω ∂P - ∫ ω, G n ω ∂P := by
      simpa using integral_sub' (hF_int n) (hG_int n)
    rw [hSub] at hEq_zero
    linarith
  have hF_tendsto :
      ∀ᵐ ω ∂P, Filter.Tendsto (fun n ↦ F n ω) Filter.atTop
        (nhds ((stoppedValue Wℝ τab ω) ^ 2)) := by
    -- Proof comment: on every path where `τab` is finite, the truncations eventually stop at `τab`.
    filter_upwards
      [stoppedValue_truncation_ae_eventuallyEq
        (X := Wℝ) (μ := P) (τ := τab) hτab_ae_ne_top] with ω hω
    have hEq :
        (fun n ↦ F n ω) =ᶠ[Filter.atTop] fun _ ↦ (stoppedValue Wℝ τab ω) ^ 2 := by
      filter_upwards [hω] with n hn
      simpa [F] using congrArg (fun x : ℝ ↦ x ^ 2) hn
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
  have hF_norm_bound :
      ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (b - a : ℝ) ^ 2 := by
    intro n
    filter_upwards [hF_bound n] with ω hω
    have hnonneg : 0 ≤ F n ω := sq_nonneg _
    rwa [Real.norm_of_nonneg hnonneg]
  have hF_integral_tendsto :
      Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂P) Filter.atTop
        (nhds (∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ ↦ (b - a : ℝ) ^ 2)
      (fun n ↦ (hF_int n).aestronglyMeasurable)
      (integrable_const ((b - a : ℝ) ^ 2))
      hF_norm_bound hF_tendsto
  have hH_lintegral_tendsto :
      Filter.Tendsto (fun n ↦ ∫⁻ ω, H n ω ∂P) Filter.atTop
        (nhds (∫⁻ ω, ENat.toENNReal (τab ω) ∂P)) := by
    -- Proof comment: `τab ∧ n` is monotone in `n` and eventually constant on each finite path.
    refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro n
      let τn : Ω → WithTop ℕ := fun ω ↦ τtrunc n ω
      have hτn_meas_h : Measurable[(hτtrunc_stop n).measurableSpace] τn :=
        (hτtrunc_stop n).measurable
      have hτn_meas : Measurable τn := by
        intro s hs
        exact (hτtrunc_stop n).measurableSpace_le _ (hτn_meas_h hs)
      simpa [τn, H] using
        ((measurable_of_countable fun t : WithTop ℕ ↦ ENat.toENNReal t).comp
          hτn_meas).aemeasurable
    · filter_upwards with ω
      intro m n hmn
      exact ENat.toENNReal_mono
        (min_le_min_left _ (show (m : ℕ∞) ≤ n by exact_mod_cast hmn))
    · filter_upwards [hτab_ae_ne_top] with ω hω
      have hEq :
          (fun _ : ℕ ↦ ENat.toENNReal (τab ω)) =ᶠ[Filter.atTop] fun n ↦ H n ω := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨(τab ω).untop hω, ?_⟩
        intro n hn
        have hle : τab ω ≤ (n : ℕ∞) := by
          rw [← WithTop.coe_untop (τab ω) hω]
          exact WithTop.coe_le_coe.2 (show (τab ω).untop hω ≤ n by
            simpa [ge_iff_le] using hn)
        have hτn : H n ω = ENat.toENNReal (τab ω) := by
          change ENat.toENNReal (min (τab ω) (n : ℕ∞)) = ENat.toENNReal (τab ω)
          rw [min_eq_left hle]
        simpa [hτn]
      exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hTrunc_eq :
      ∀ n, ENNReal.ofReal (∫ ω, F n ω ∂P) = ∫⁻ ω, H n ω ∂P := by
    intro n
    calc
      ENNReal.ofReal (∫ ω, F n ω ∂P) = ENNReal.ofReal (∫ ω, G n ω ∂P) := by
        rw [hSquare_eq_time n]
      _ = ∫⁻ ω, ENNReal.ofReal (G n ω) ∂P := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hG_int n) (hG_nonneg n)]
      _ = ∫⁻ ω, H n ω ∂P := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
        intro ω
        have hne : τtrunc n ω ≠ ⊤ := by
          exact ne_top_of_le_ne_top (by simp) (min_le_right _ _)
        have hGω : G n ω = (((τtrunc n ω).untopA : ℕ) : ℝ) := by
          rfl
        calc
          ENNReal.ofReal (G n ω) =
              (((τtrunc n ω).untop hne : ℕ) : ℝ≥0∞) := by
                rw [hGω, WithTop.untopA_eq_untop hne, ENNReal.ofReal_natCast]
          _ = ENat.toENNReal ((((τtrunc n ω).untop hne : ℕ) : ℕ∞)) := by
                simp [ENat.toENNReal_coe]
          _ = ENat.toENNReal (τtrunc n ω) := by
                exact congrArg ENat.toENNReal (WithTop.coe_untop (τtrunc n ω) hne)
          _ = H n ω := by
                rfl
  have hTerminal_time :
      ∫⁻ ω, ENat.toENNReal (τab ω) ∂P =
        ENNReal.ofReal (∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P) := by
    have hLeft :
        Filter.Tendsto (fun n ↦ ENNReal.ofReal (∫ ω, F n ω ∂P)) Filter.atTop
          (nhds (ENNReal.ofReal (∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P))) := by
      exact (ENNReal.continuous_ofReal.tendsto _).comp hF_integral_tendsto
    have hRight :
        Filter.Tendsto (fun n ↦ ENNReal.ofReal (∫ ω, F n ω ∂P)) Filter.atTop
          (nhds (∫⁻ ω, ENat.toENNReal (τab ω) ∂P)) := by
      have hEqSeq :
          (fun n ↦ ENNReal.ofReal (∫ ω, F n ω ∂P)) = fun n ↦ ∫⁻ ω, H n ω ∂P := by
        funext n
        exact hTrunc_eq n
      simp [hEqSeq]
      exact hH_lintegral_tendsto
    exact tendsto_nhds_unique hRight hLeft
  let A : Set Ω := {ω | τab ω = τa ω}
  have hA_meas : MeasurableSet A := by
    -- Proof comment: the left-hit event is measurable because both stopping times are measurable.
    have hτab_eq_meas : ∀ n : ℕ, MeasurableSet {ω | τab ω = n} := by
      intro n
      exact ℱW.le n _ (hτab_stop.measurableSet_eq n)
    have hτa_eq_meas : ∀ n : ℕ, MeasurableSet {ω | τa ω = n} := by
      intro n
      exact ℱW.le n _ (hτa_stop.measurableSet_eq n)
    have hτab_top_meas : MeasurableSet {ω | τab ω = ⊤} := by
      have hEq : {ω | τab ω = ⊤} = (⋃ n : ℕ, {ω | τab ω = n})ᶜ := by
        ext ω
        cases hτ : τab ω with
        | top =>
            simpa [hτ]
        | coe n =>
            simpa [hτ]
      rw [hEq]
      exact (MeasurableSet.iUnion hτab_eq_meas).compl
    have hτa_top_meas : MeasurableSet {ω | τa ω = ⊤} := by
      have hEq : {ω | τa ω = ⊤} = (⋃ n : ℕ, {ω | τa ω = n})ᶜ := by
        ext ω
        cases hτ : τa ω with
        | top =>
            simpa [hτ]
        | coe n =>
            simpa [hτ]
      rw [hEq]
      exact (MeasurableSet.iUnion hτa_eq_meas).compl
    have hEq :
        A =
          (⋃ n : ℕ, {ω | τab ω = n} ∩ {ω | τa ω = n}) ∪
            ({ω | τab ω = ⊤} ∩ {ω | τa ω = ⊤}) := by
      ext ω
      cases hτabω : τab ω with
      | top =>
          cases hτaω : τa ω with
          | top =>
              simpa [A, hτabω, hτaω]
          | coe m =>
              simpa [A, hτabω, hτaω]
      | coe n =>
          cases hτaω : τa ω with
          | top =>
              simpa [A, hτabω, hτaω]
          | coe m =>
              simpa [A, hτabω, hτaω, eq_comm]
    rw [hEq]
    exact
      (MeasurableSet.iUnion fun n ↦ (hτab_eq_meas n).inter (hτa_eq_meas n)).union
        (hτab_top_meas.inter hτa_top_meas)
  have hTerminal_square_repr :
      (fun ω ↦ (stoppedValue Wℝ τab ω) ^ 2) =ᵐ[P]
        fun ω ↦ A.indicator (fun _ ↦ ((a : ℝ) ^ 2)) ω +
          Aᶜ.indicator (fun _ ↦ ((b : ℝ) ^ 2)) ω := by
    -- Proof comment: on the finite-hit event, the stopped walk lands at `a` or `b`, and `A`
    -- records exactly the left-boundary alternative.
    filter_upwards [hτab_ae_ne_top] with ω hω
    by_cases hAω : ω ∈ A
    · have hEqτ : τab ω = τa ω := by simpa [A] using hAω
      have hτa_ne : τa ω ≠ ⊤ := by simpa [hEqτ] using hω
      have hval : W (τab ω).untopA ω = a := by
        simpa [τa, hEqτ, Set.mem_singleton_iff] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({a} : Set ℤ)) (n := 0) (ω := ω) hτa_ne)
      have hcast : Wℝ (τab ω).untopA ω = (W (τab ω).untopA ω : ℝ) := hWℝ_eq _ _
      have hterm : (stoppedValue Wℝ τab ω) ^ 2 = (a : ℝ) ^ 2 := by
        rw [stoppedValue, hcast, hval]
      simp [A, hAω, hterm]
    · have hmem : W (τab ω).untopA ω ∈ ({a, b} : Set ℤ) := by
        simpa [τab] using
          (hittingAfter_mem_set_of_ne_top
            (u := W) (s := ({a, b} : Set ℤ)) (n := 0) (ω := ω) hω)
      have hcast : Wℝ (τab ω).untopA ω = (W (τab ω).untopA ω : ℝ) := hWℝ_eq _ _
      have hval_b : W (τab ω).untopA ω = b := by
        rcases (by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem :
            W (τab ω).untopA ω = a ∨ W (τab ω).untopA ω = b) with hval_a | hval_b
        · have hidx_eq : (((τab ω).untopA : ℕ) : ℕ∞) = τab ω := by
            rw [WithTop.untopA_eq_untop hω]
            exact WithTop.coe_untop _ _
          have hτa_le : τa ω ≤ τab ω := by
            have hmem_a : W (τab ω).untopA ω ∈ ({a} : Set ℤ) := by
              simpa [Set.mem_singleton_iff, hval_a] using hmem
            calc
              τa ω ≤ (τab ω).untopA := by
                exact hittingAfter_le_of_mem
                  (u := W) (s := ({a} : Set ℤ)) (n := 0) (ω := ω)
                  (i := (τab ω).untopA) (by simp) hmem_a
              _ = τab ω := hidx_eq
          have hEqτ : τab ω = τa ω := le_antisymm (hτab_le_τa ω) hτa_le
          exact False.elim (hAω (by simpa [A] using hEqτ))
        · exact hval_b
      have hterm : (stoppedValue Wℝ τab ω) ^ 2 = (b : ℝ) ^ 2 := by
        rw [stoppedValue, hcast, hval_b]
      simp [A, hAω, hterm]
  have hTerminal_square_integral :
      ∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P =
        P.real A * ((a : ℝ) ^ 2) + P.real Aᶜ * ((b : ℝ) ^ 2) := by
    calc
      ∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P =
          ∫ ω,
            (A.indicator (fun _ ↦ ((a : ℝ) ^ 2)) ω +
              Aᶜ.indicator (fun _ ↦ ((b : ℝ) ^ 2)) ω) ∂P := by
                exact integral_congr_ae hTerminal_square_repr
      _ = ∫ ω, A.indicator (fun _ ↦ ((a : ℝ) ^ 2)) ω ∂P
            + ∫ ω, Aᶜ.indicator (fun _ ↦ ((b : ℝ) ^ 2)) ω ∂P := by
              rw [integral_add]
              · exact (integrable_const ((a : ℝ) ^ 2)).indicator hA_meas
              · exact (integrable_const ((b : ℝ) ^ 2)).indicator hA_meas.compl
      _ = P.real A * ((a : ℝ) ^ 2) + P.real Aᶜ * ((b : ℝ) ^ 2) := by
        rw [integral_indicator_const (((a : ℝ) ^ 2)) hA_meas,
          integral_indicator_const (((b : ℝ) ^ 2)) hA_meas.compl]
        simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hAeq_X :
      A =ᵐ[P]
        {ω | hittingAfter X ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω} := by
    -- Proof comment: transport the left-hit event back to the original walk only at the end.
    simpa [A, τab, τa, hbCast] using
      (twoSidedHitLeftEvent_ae_eq_original
        (P := P) (X := X) (W := W) (a := a) (b := Int.toNat b) hW_eq_X)
  have hA_measure :
      P A = ENNReal.ofReal ((b : ℝ) / (b - a : ℝ)) := by
    calc
      P A = P {ω | hittingAfter X ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a} : Set ℤ) 0 ω} := by
        exact measure_congr hAeq_X
      _ = ENNReal.ofReal ((b : ℝ) / (b - a : ℝ)) := by
        exact symmetricSimpleRandomWalk_prob_hitLeftBeforeRight
          P X hX_zero hX_indep hX_law ha hb
  have hA_le_one : P A ≤ 1 := by
    calc
      P A ≤ P Set.univ := measure_mono (Set.subset_univ A)
      _ = 1 := by simp
  have hA_ne_top : P A ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hA_le_one (by simp))
  have hA_real : P.real A = (b : ℝ) / (b - a : ℝ) := by
    have ha_real : (a : ℝ) < 0 := by exact_mod_cast ha
    have hb_real : (0 : ℝ) < b := by exact_mod_cast hb
    have hfrac_nonneg : 0 ≤ (b : ℝ) / (b - a : ℝ) := by
      exact div_nonneg hb_real.le (by nlinarith)
    rw [Measure.real_def, hA_measure, ENNReal.toReal_ofReal hfrac_nonneg]
  have hA_compl_real : P.real Aᶜ = 1 - P.real A := by
    rw [Measure.real_def, measure_compl hA_meas hA_ne_top, measure_univ]
    rw [ENNReal.toReal_sub_of_le hA_le_one (by simp)]
    simp [Measure.real_def]
  have hnatAbs_int : ((Int.natAbs a : ℕ) : ℤ) = -a := by
    simpa using Int.ofNat_natAbs_of_nonpos (show a ≤ 0 by omega)
  have hnatAbs_real : (Int.natAbs a : ℝ) = -(a : ℝ) := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ℝ)) hnatAbs_int
    simpa using hcast
  have hTerminal_value :
      ∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P = (Int.natAbs a : ℝ) * b := by
    have ha_real : (a : ℝ) < 0 := by exact_mod_cast ha
    have hb_real : (0 : ℝ) < b := by exact_mod_cast hb
    calc
      ∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P =
          P.real A * ((a : ℝ) ^ 2) + P.real Aᶜ * ((b : ℝ) ^ 2) := hTerminal_square_integral
      _ = ((b : ℝ) / (b - a : ℝ)) * ((a : ℝ) ^ 2) +
            (1 - (b : ℝ) / (b - a : ℝ)) * ((b : ℝ) ^ 2) := by
              rw [hA_compl_real, hA_real]
      _ = (Int.natAbs a : ℝ) * b := by
        have hden : (b : ℝ) - a ≠ 0 := by
          nlinarith
        rw [hnatAbs_real]
        field_simp [hden]
        nlinarith
  have hW_target :
      ∫⁻ ω, ENat.toENNReal (τab ω) ∂P = ENNReal.ofReal ((Int.natAbs a : ℝ) * b) := by
    calc
      ∫⁻ ω, ENat.toENNReal (τab ω) ∂P =
          ENNReal.ofReal (∫ ω, (stoppedValue Wℝ τab ω) ^ 2 ∂P) := hTerminal_time
      _ = ENNReal.ofReal ((Int.natAbs a : ℝ) * b) := by rw [hTerminal_value]
  -- Proof comment: finish by transporting the measurable-modification result back to `X`.
  calc
    lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, b} : Set ℤ) 0 ω)) =
        ∫⁻ ω, ENat.toENNReal (τab ω) ∂P := by
          refine (lintegral_congr_ae ?_).symm
          filter_upwards [hτW_eq_X] with ω hω
          simp [τab, hω]
    _ = ENNReal.ofReal ((Int.natAbs a : ℝ) * b) := hW_target

/-- Companion theorem: the two-sided hitting time is almost surely finite. -/
theorem symmetricSimpleRandomWalk_twoSidedHittingTime_ae_ne_top
    {a b : ℤ} (ha : a < 0) (hb : 0 < b) :
    ∀ᵐ ω ∂P, hittingAfter X ({a, b} : Set ℤ) 0 ω ≠ ⊤ := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Ym : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  let W : ℕ → Ω → ℤ := randomWalkProcess Ym
  have hYm_eq : ∀ n, Δ n =ᵐ[P] Ym n := by
    intro n
    simpa [Δ, Ym] using (hX_law n).aemeasurable.ae_eq_mk
  have hW_eq_X : ∀ᵐ ω ∂P, ∀ n, W n ω = X n ω := by
    have h_all : ∀ᵐ ω ∂P, ∀ n, Δ n ω = Ym n ω := by
      simpa [Filter.EventuallyEq] using (ae_all_iff.2 hYm_eq)
    filter_upwards [h_all] with ω hω n
    calc
      W n ω = random_walk_partial_sum Ym n ω := by
        simpa [W] using randomWalkProcess_apply Ym n ω
      _ = random_walk_partial_sum Δ n ω := by
        unfold random_walk_partial_sum
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact (hω j).symm
      _ = X n ω := by
        simpa [Δ] using symmetricSimpleRandomWalk_position_eq_partialSum hX_zero n ω
  have hτW_eq_X :
      ∀ᵐ ω ∂P, hittingAfter W ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a, b} : Set ℤ) 0 ω := by
    filter_upwards [hW_eq_X] with ω hω
    exact hittingAfter_zero_eq_of_forall_eq
      (u := W) (v := X) (s := ({a, b} : Set ℤ)) (ω := ω) hω
  have hτW_ne_top :
      ∀ᵐ ω ∂P, hittingAfter W ({a, b} : Set ℤ) 0 ω ≠ ⊤ := by
    have hbNat : 0 < Int.toNat b := by
      have : (0 : ℤ) < Int.toNat b := by
        simpa [Int.toNat_of_nonneg hb.le] using hb
      exact_mod_cast this
    have hbCast : ((Int.toNat b : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb.le
    simpa [hbCast] using
      (twoSidedHittingAfter_ae_ne_top
        (P := P) (X := X) hX_indep hX_law (a := a) (b := Int.toNat b) ha hbNat)
  -- Proof comment: transport the almost-sure finiteness from the measurable modification back
  -- to the original walk using the pathwise almost-sure equality of hitting times.
  filter_upwards [hτW_ne_top, hτW_eq_X] with ω hω hEq
  simpa [hEq] using hω

/-- Companion corollary: after the almost-sure finiteness bridge, the two-sided expectation can
be read on the real-valued integral surface. -/
theorem symmetricSimpleRandomWalk_lintegral_twoSidedHittingTime
    {a b : ℤ} (ha : a < 0) (hb : 0 < b) :
    ∫ ω, ENNReal.toReal (ENat.toENNReal (hittingAfter X ({a, b} : Set ℤ) 0 ω)) ∂P =
      (Int.natAbs a : ℝ) * b := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Ym : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  let W : ℕ → Ω → ℤ := randomWalkProcess Ym
  have hYm_eq : ∀ n, Δ n =ᵐ[P] Ym n := by
    intro n
    -- Proof comment: replace each increment by its measurable modification supplied by `HasLaw`.
    simpa [Δ, Ym] using (hX_law n).aemeasurable.ae_eq_mk
  have hYm_meas : ∀ n, Measurable (Ym n) := by
    intro n
    -- Proof comment: the measurable representative is measurable by construction.
    simpa [Ym] using (hX_law n).aemeasurable.measurable_mk
  have hW_eq_X : ∀ᵐ ω ∂P, ∀ n, W n ω = X n ω := by
    have h_all : ∀ᵐ ω ∂P, ∀ n, Δ n ω = Ym n ω := by
      simpa [Filter.EventuallyEq] using (ae_all_iff.2 hYm_eq)
    filter_upwards [h_all] with ω hω n
    calc
      W n ω = random_walk_partial_sum Ym n ω := by
        simpa [W] using randomWalkProcess_apply Ym n ω
      _ = random_walk_partial_sum Δ n ω := by
        unfold random_walk_partial_sum
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact (hω j).symm
      _ = X n ω := by
        simpa [Δ] using symmetricSimpleRandomWalk_position_eq_partialSum hX_zero n ω
  have hτW_eq_X :
      ∀ᵐ ω ∂P, hittingAfter W ({a, b} : Set ℤ) 0 ω = hittingAfter X ({a, b} : Set ℤ) 0 ω := by
    -- Proof comment: once the measurable modification agrees pathwise with `X`, the two-sided
    -- hitting times are identical on that full-measure set.
    filter_upwards [hW_eq_X] with ω hω
    exact hittingAfter_zero_eq_of_forall_eq
      (u := W) (v := X) (s := ({a, b} : Set ℤ)) (ω := ω) hω
  let stepReal : ℕ → Ω → ℝ := fun n ω ↦ (Ym n ω : ℝ)
  let Wℝ : ℕ → Ω → ℝ := partialSum stepReal
  have hWℝ_eq : ∀ n ω, Wℝ n ω = (W n ω : ℝ) := by
    intro n ω
    -- Proof comment: the real partial sums are just the integer random walk cast into `ℝ`.
    simpa [Wℝ, stepReal, W] using partialSum_intCast_eq_randomWalkProcess Ym n ω
  have hWℝ_strMeas :
      ∀ n, StronglyMeasurable (Wℝ n) := by
    intro n
    -- Proof comment: finite partial sums of measurable real increments stay measurable.
    exact (partialSum_measurable stepReal
      (fun k ↦ measurable_stepReal Ym hYm_meas k) n).stronglyMeasurable
  let ℱW : Filtration ℕ mΩ := Filtration.natural Wℝ hWℝ_strMeas
  let τab : Ω → ℕ∞ := hittingAfter W ({a, b} : Set ℤ) 0
  have hτab_eq :
      hittingAfter Wℝ ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 = τab := by
    funext ω
    calc
      hittingAfter Wℝ ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 ω =
          hittingAfter (fun n ω' ↦ (W n ω' : ℝ))
            ({(a : ℝ), (b : ℝ)} : Set ℝ) 0 ω := by
              exact hittingAfter_zero_eq_of_forall_eq
                (u := Wℝ) (v := fun n ω' ↦ (W n ω' : ℝ))
                (s := ({(a : ℝ), (b : ℝ)} : Set ℝ))
                (ω := ω) (fun n ↦ hWℝ_eq n ω)
      _ = τab ω := by
        simpa [τab] using hittingAfter_intCast_pair_eq (u := W) (ω := ω) (a := a) (b := b)
  have hτab_stop : IsStoppingTime ℱW τab := by
    -- Proof comment: rewrite the integer hitting time as a real hitting time of the adapted
    -- measurable modification `Wℝ`.
    rw [← hτab_eq]
    simpa [Set.insert_comm] using
      Adapted.isStoppingTime_hittingAfter
        (u := Wℝ) (s := ({(a : ℝ), (b : ℝ)} : Set ℝ)) (n := 0)
        (Filtration.stronglyAdapted_natural hWℝ_strMeas).adapted
        ((measurableSet_singleton (b : ℝ)).insert (a : ℝ))
  let fW : Ω → ℝ≥0∞ := fun ω ↦ ENat.toENNReal (τab ω)
  have hfW_meas : Measurable fW := by
    -- Proof comment: the measurable stopping time `τab` lands in the countable space `ℕ∞`,
    -- and `ENat.toENNReal` is measurable on that countable domain.
    let τW : Ω → WithTop ℕ := τab
    have hτab_meas_h := hτab_stop.measurable
    have hτab_meas : Measurable τW := by
      intro s hs
      exact hτab_stop.measurableSpace_le _ (hτab_meas_h (by simpa using hs))
    simpa [fW, τW] using
      ((measurable_of_countable fun t : WithTop ℕ ↦ ENat.toENNReal t).comp hτab_meas)
  have hlintegral_ne_top :
      lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, b} : Set ℤ) 0 ω)) ≠ ⊤ := by
    rw [symmetricSimpleRandomWalk_lintegral_hittingTimeFormulas
      (P := P) (X := X) hX_zero hX_indep hX_law ha hb]
    exact ENNReal.ofReal_ne_top
  have hlintegralW_eq :
      lintegral P fW =
        lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, b} : Set ℤ) 0 ω)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hτW_eq_X] with ω hω
    simp [fW, τab, hω]
  have hlintegralW_ne_top : lintegral P fW ≠ ⊤ := by
    rw [hlintegralW_eq]
    exact hlintegral_ne_top
  have hfW_lt_top : ∀ᵐ ω ∂P, fW ω < ⊤ := by
    exact ae_lt_top hfW_meas hlintegralW_ne_top
  -- Proof comment: convert the real-valued expectation to the `ENNReal` lintegral on the
  -- measurable modification, then transport the result back to `X`.
  calc
    ∫ ω, ENNReal.toReal (ENat.toENNReal (hittingAfter X ({a, b} : Set ℤ) 0 ω)) ∂P
        = ∫ ω, (fW ω).toReal ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hτW_eq_X] with ω hω
            simp [fW, τab, hω]
    _ = (lintegral P fW).toReal := by
      exact integral_toReal hfW_meas.aemeasurable hfW_lt_top
    _ =
        (lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, b} : Set ℤ) 0 ω))).toReal := by
          rw [hlintegralW_eq]
    _ = (ENNReal.ofReal ((Int.natAbs a : ℝ) * b)).toReal := by
      rw [symmetricSimpleRandomWalk_lintegral_hittingTimeFormulas
        (P := P) (X := X) hX_zero hX_indep hX_law ha hb]
    _ = (Int.natAbs a : ℝ) * b := by
      refine ENNReal.toReal_ofReal ?_
      positivity

/-- Companion theorem: the one-sided hitting-time expectation is infinite. -/
theorem symmetricSimpleRandomWalk_lintegral_levelHittingTime_eq_top
    {a : ℤ} (ha : a < 0) :
    lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a} : Set ℤ) 0 ω)) = ∞ := by
  let τa : Ω → ℕ∞ := hittingAfter X ({a} : Set ℤ) 0
  have ha_ne_zero : a ≠ 0 := by omega
  have hnatAbs_pos : 0 < Int.natAbs a := Int.natAbs_pos.2 ha_ne_zero
  have hnatAbs_one : 1 ≤ Int.natAbs a := Nat.succ_le_of_lt hnatAbs_pos
  have hlower :
      ∀ N : ℕ,
        ((N : ℕ) : ℝ≥0∞) ≤ lintegral P (fun ω ↦ ENat.toENNReal (τa ω)) := by
    intro N
    have hb : 0 < (N + 1 : ℤ) := by exact_mod_cast Nat.succ_pos N
    have hsubset : ({a} : Set ℤ) ⊆ ({a, (N + 1 : ℤ)} : Set ℤ) := by
      intro x hx
      left
      simpa [Set.mem_singleton_iff] using hx
    have hmono :
        lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, (N + 1 : ℤ)} : Set ℤ) 0 ω)) ≤
          lintegral P (fun ω ↦ ENat.toENNReal (τa ω)) := by
      refine lintegral_mono ?_
      intro ω
      -- Proof comment: enlarging the target set from `{a}` to `{a, N + 1}` can only make the
      -- hitting time smaller.
      simpa [τa] using
        ENat.toENNReal_mono
          (hittingAfter_le_of_subset
            (u := X) (s := ({a} : Set ℤ)) (t := ({a, (N + 1 : ℤ)} : Set ℤ))
            (ω := ω) hsubset)
    have htwo :=
      symmetricSimpleRandomWalk_lintegral_hittingTimeFormulas
        (P := P) (X := X) hX_zero hX_indep hX_law (a := a) (b := (N + 1 : ℤ)) ha hb
    have htwo_nat :
        lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, (N + 1 : ℤ)} : Set ℤ) 0 ω)) =
          ((Int.natAbs a * (N + 1) : ℕ) : ℝ≥0∞) := by
      calc
        lintegral P (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, (N + 1 : ℤ)} : Set ℤ) 0 ω)) =
            ENNReal.ofReal ((Int.natAbs a : ℝ) * ((N + 1 : ℤ) : ℝ)) := htwo
        _ = ((Int.natAbs a * (N + 1) : ℕ) : ℝ≥0∞) := by
          have hbCast : (((N + 1 : ℤ) : ℝ)) = (N + 1 : ℝ) := by norm_num
          rw [hbCast, ← ENNReal.ofReal_natCast (Int.natAbs a * (N + 1))]
          congr 1
          norm_num [Nat.cast_mul]
    have hsucc_le :
        ((N + 1 : ℕ) : ℝ≥0∞) ≤ lintegral P (fun ω ↦ ENat.toENNReal (τa ω)) := by
      have hNat :
          N + 1 ≤ Int.natAbs a * (N + 1) := by
        calc
          N + 1 = 1 * (N + 1) := by simp
          _ ≤ Int.natAbs a * (N + 1) := Nat.mul_le_mul_right (N + 1) hnatAbs_one
      calc
        ((N + 1 : ℕ) : ℝ≥0∞) ≤ ((Int.natAbs a * (N + 1) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast hNat
        _ =
            lintegral P
              (fun ω ↦ ENat.toENNReal (hittingAfter X ({a, (N + 1 : ℤ)} : Set ℤ) 0 ω)) := by
                exact htwo_nat.symm
        _ ≤ lintegral P (fun ω ↦ ENat.toENNReal (τa ω)) := hmono
    exact le_trans (by exact_mod_cast Nat.le_succ N) hsucc_le
  -- Proof comment: the expectation dominates every finite natural number, so it must be `∞`.
  refine top_unique ?_
  exact le_of_tendsto' ENNReal.tendsto_nat_nhds_top hlower

end SymmetricSimpleRandomWalk
