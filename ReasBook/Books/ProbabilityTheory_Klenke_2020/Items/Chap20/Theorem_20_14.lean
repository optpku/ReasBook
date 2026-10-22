/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Lemma_20_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Lemma_20_7

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {τ : Ω → Ω} {f g : Ω → ℝ}

/-- Helper for Theorem 20.14: ergodicity forces the invariant conditional expectation
`P[f | MeasurableSpace.invariants τ]` to be almost surely constant. -/
theorem condExpInvariantsAeEqConstOfErgodic
    (hτ : Ergodic τ P) :
    ∃ c : ℝ, P[f | MeasurableSpace.invariants τ] =ᵐ[P] fun _ ↦ c := by
  -- Proof comment: apply Lemma 20.7 to the conditional expectation itself, which is
  -- measurable with respect to the invariant σ-algebra by construction.
  have hmeas : Measurable[MeasurableSpace.invariants τ] P[f | MeasurableSpace.invariants τ] :=
    StronglyMeasurable.measurable stronglyMeasurable_condExp
  exact
    (ergodic_iff_ae_eq_const_of_measurable_invariants_real P hτ.toMeasurePreserving).mp hτ hmeas

/-- Helper for Theorem 20.14: if the invariant conditional expectation is almost surely the
constant `c`, then `c = ∫ ω, f ω ∂P`. -/
theorem condExpInvariantsConstEqExpectation
    (_hf : Integrable f P)
    (hc : P[f | MeasurableSpace.invariants τ] =ᵐ[P] fun _ ↦ c) :
    c = ∫ ω, f ω ∂P := by
  -- Proof comment: integrate the almost-sure constant identification and then use the
  -- conditional-expectation integral identity on the invariant σ-algebra.
  calc
    c = ∫ ω, (fun _ : Ω ↦ c) ω ∂P := by
      simp
    _ = ∫ ω, P[f | MeasurableSpace.invariants τ] ω ∂P := by
      symm
      exact integral_congr_ae hc
    _ = ∫ ω, f ω ∂P := by
      simpa using integral_condExp (μ := P) (m := MeasurableSpace.invariants τ)
        (hm := MeasurableSpace.invariants_le τ) (f := f)

/-- Helper for Theorem 20.14: under ergodicity, the invariant conditional expectation
`P[f | MeasurableSpace.invariants τ]` is almost surely the expectation of `f`. -/
theorem condExpInvariantsAeEqExpectationOfErgodic
    (hτ : Ergodic τ P) (hf : Integrable f P) :
    P[f | MeasurableSpace.invariants τ] =ᵐ[P] fun _ ↦ ∫ ω, f ω ∂P := by
  -- Proof comment: combine the almost-sure constancy from ergodicity with the integral
  -- characterization of that constant.
  rcases condExpInvariantsAeEqConstOfErgodic (P := P) (τ := τ) (f := f) hτ with ⟨c, hc⟩
  have hc' : c = ∫ ω, f ω ∂P :=
    condExpInvariantsConstEqExpectation (P := P) (τ := τ) (f := f) hf hc
  filter_upwards [hc] with ω hω
  simpa [hc'] using hω

/-- Helper for Theorem 20.14: the conditional expectation onto
`MeasurableSpace.invariants τ` is exactly `τ`-invariant. -/
theorem condExpInvariants_comp_eq
    (τ : Ω → Ω) (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) :
    P[f | MeasurableSpace.invariants τ] ∘ τ = P[f | MeasurableSpace.invariants τ] := by
  -- Proof comment: Lemma 20.7 rewrites invariant-σ-algebra measurability as pointwise
  -- invariance under the transformation.
  have hInv : Measurable[MeasurableSpace.invariants τ] P[f | MeasurableSpace.invariants τ] :=
    StronglyMeasurable.measurable stronglyMeasurable_condExp
  have hMeas : Measurable P[f | MeasurableSpace.invariants τ] :=
    (MeasurableSpace.measurable_invariants_dom.mp hInv).1
  exact (measurable_invariants_real_iff_comp_eq hMeas).mp hInv

/-- Helper for Theorem 20.14: after centering by `P[f | MeasurableSpace.invariants τ]`,
the invariant conditional expectation vanishes almost surely. -/
theorem condExp_sub_condExpInvariants_ae_eq_zero
    (hf : Integrable f P) :
    P[fun ω ↦ f ω - P[f | MeasurableSpace.invariants τ] ω
      | MeasurableSpace.invariants τ] =ᵐ[P] 0 := by
  -- Proof comment: subtract the conditional expectation from itself after applying
  -- `condExp_sub` and the idempotence of conditional expectation.
  have hcondInt : Integrable P[f | MeasurableSpace.invariants τ] P := integrable_condExp
  have hself :
      P[P[f | MeasurableSpace.invariants τ] | MeasurableSpace.invariants τ] =ᵐ[P]
        P[f | MeasurableSpace.invariants τ] :=
    condExp_of_aestronglyMeasurable' (MeasurableSpace.invariants_le τ)
      (StronglyMeasurable.aestronglyMeasurable stronglyMeasurable_condExp) hcondInt
  refine (condExp_sub hf hcondInt (MeasurableSpace.invariants τ)).trans ?_
  refine (EventuallyEq.sub EventuallyEq.rfl hself).trans ?_
  filter_upwards with ω
  simp

/-- Helper for Theorem 20.14: on every measurable event, a centered observable with vanishing
invariant conditional expectation has integral `0`. -/
theorem setIntegral_eq_zero_of_condExpInvariants_aeZero
    (hg : Integrable g P)
    (hzero : P[g | MeasurableSpace.invariants τ] =ᵐ[P] 0)
    {s : Set Ω} (hs : MeasurableSet[MeasurableSpace.invariants τ] s) :
    ∫ ω in s, g ω ∂P = 0 := by
  -- Proof comment: move the set integral to the conditional expectation and then use the
  -- almost-sure zero hypothesis.
  calc
    ∫ ω in s, g ω ∂P = ∫ ω in s, P[g | MeasurableSpace.invariants τ] ω ∂P := by
      symm
      exact setIntegral_condExp (hm := MeasurableSpace.invariants_le τ) hg hs
    _ = 0 := by
      exact setIntegral_eq_zero_of_ae_eq_zero <| hzero.mono fun _ hx _ ↦ hx

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 20.14: reuse Lemma 20.13's maximal-orbit inequality through a theorem-local
wrapper. -/
theorem integral_nonneg_on_maxOrbitPartialSumPosLocal
    (hτ : MeasurePreserving τ P P) {X0 : Ω → ℝ} (hX0 : Integrable X0 P)
    (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < max_orbit_partial_sum τ X0 n ω}, X0 ω ∂P := by
  -- Proof comment: the centered maximal-ergodic step needs exactly the final inequality from
  -- Lemma 20.13, so reuse that earlier owner through a local companion name.
  simpa using integral_nonneg_on_max_orbit_partial_sum_pos (P := P) (τ := τ) hτ hX0 n

/-- Helper for Theorem 20.14: along almost every orbit of an integrable observable, the single
orbit term divided by time tends to `0`. -/
theorem ae_orbitTermDiv_tendsto_zero_of_integrable
    (hτ : MeasurePreserving τ P P) (hg : Integrable g P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ g ((τ^[n]) ω) / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have hnorm : Integrable (fun ω ↦ ‖g ω‖) P := hg.norm
  have hEventuallyBound :
      ∀ m : ℕ, ∀ᵐ ω ∂P,
        ∀ᶠ n : ℕ in atTop, ‖g ((τ^[n]) ω) / (n + 1 : ℝ)‖ ≤ 1 / (m + 1 : ℝ) := by
    intro m
    let X : Ω → ℝ := fun ω ↦ (m + 1 : ℝ) * ‖g ω‖
    have hXint : Integrable X P := by
      simpa [X] using hnorm.const_mul (m + 1 : ℝ)
    have hXnonneg : 0 ≤ X := by
      intro ω
      exact mul_nonneg (by positivity) (norm_nonneg _)
    let s : ℕ → Set Ω := fun n ↦ {ω | X ((τ^[n]) ω) ∈ Set.Ioi (n : ℝ)}
    have hs_eq : ∀ n : ℕ, P (s n) = P {ω | X ω ∈ Set.Ioi (n : ℝ)} := by
      intro n
      have hs_pre : s n = (τ^[n]) ⁻¹' {ω | X ω ∈ Set.Ioi (n : ℝ)} := by
        ext ω
        simp [s]
      have hs_null :
          NullMeasurableSet {ω | X ω ∈ Set.Ioi (n : ℝ)} P := by
        simpa [Set.preimage] using
          hXint.aestronglyMeasurable.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
      rw [hs_pre, (hτ.iterate n).measure_preimage hs_null]
    have hs_tsum : (∑' n : ℕ, P (s n)) < ∞ := by
      letI : MeasureSpace Ω := ⟨P⟩
      have hXint' : Integrable X := by
        simpa using hXint
      have hXnonneg' : 0 ≤ X := hXnonneg
      have htail :
          (∑' n : ℕ, P {ω | X ω ∈ Set.Ioi (n : ℝ)}) < ∞ :=
        by simpa using ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hXint' hXnonneg'
      rw [tsum_congr hs_eq]
      exact htail
    filter_upwards [ae_eventually_notMem hs_tsum.ne] with ω hω
    filter_upwards [hω] with n hn
    have hn_scaled : X ((τ^[n]) ω) ≤ n := by
      simpa [s, Set.mem_Ioi, not_lt] using hn
    have hn_scaled' : X ((τ^[n]) ω) ≤ n + 1 := by
      exact hn_scaled.trans <| by exact_mod_cast Nat.le_succ n
    have hmpos : 0 < (m + 1 : ℝ) := by positivity
    have hn1pos : 0 < (n + 1 : ℝ) := by positivity
    have hnorm_le : ‖g ((τ^[n]) ω)‖ ≤ (n + 1 : ℝ) / (m + 1 : ℝ) := by
      have : (m + 1 : ℝ) * ‖g ((τ^[n]) ω)‖ ≤ n + 1 := by
        simpa [X] using hn_scaled'
      exact (le_div_iff₀ hmpos).2 <| by simpa [mul_comm] using this
    have hdiv_le :
        ‖g ((τ^[n]) ω)‖ / (n + 1 : ℝ) ≤ ((n + 1 : ℝ) / (m + 1 : ℝ)) / (n + 1 : ℝ) :=
      div_le_div_of_nonneg_right hnorm_le hn1pos.le
    have hrhs : ((n + 1 : ℝ) / (m + 1 : ℝ)) / (n + 1 : ℝ) = 1 / (m + 1 : ℝ) := by
      field_simp [ne_of_gt hmpos, ne_of_gt hn1pos]
    simpa [norm_div, hrhs, abs_of_pos hn1pos] using hdiv_le
  filter_upwards [ae_all_iff.2 hEventuallyBound] with ω hω
  -- Proof comment: the countable bounds `1 / (m + 1)` recover the metric definition of
  -- convergence to `0`.
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  rcases Filter.eventually_atTop.1 (hω m) with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa [dist_eq_norm] using lt_of_le_of_lt (hN n hn) hm

/-- Helper for Theorem 20.14: shifting the base point of the `(n + 1)`-st Birkhoff average along
`τ` changes the average by an endpoint term, and that endpoint term tends to `0` almost surely for
integrable observables. -/
theorem birkhoffAverage_shiftDiff_tendsto_zero_ae
    (hτ : MeasurePreserving τ P P) (hg : Integrable g P) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦ birkhoffAverage ℝ τ g (n + 1) (τ ω) - birkhoffAverage ℝ τ g (n + 1) ω)
        atTop (𝓝 0) := by
  have horbit :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ g ((τ^[n]) ω) / (n + 1 : ℝ)) atTop (𝓝 0) :=
    ae_orbitTermDiv_tendsto_zero_of_integrable (P := P) (τ := τ) (g := g) hτ hg
  have horbitShift :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ g ((τ^[n]) (τ ω)) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    -- Proof comment: pull the almost-sure orbit decay through `τ`; the iterate index then shifts
    -- from `n` to `n + 1`.
    filter_upwards [hτ.quasiMeasurePreserving.ae horbit] with ω hω
    simpa [Function.comp] using hω
  have hconst :
      ∀ ω : Ω, Tendsto (fun n : ℕ ↦ g ω / (n + 1 : ℝ)) atTop (𝓝 0) := by
    intro ω
    -- Proof comment: for a fixed sample point, dividing a constant by `n + 1` tends to `0`.
    convert (tendsto_const_div_atTop_nhds_zero_nat (g ω)).comp (tendsto_add_atTop_nat 1) using 1
    ext n
    simp [Function.comp, Nat.cast_add]
  have hrewrite :
      ∀ ω : Ω,
        (fun n : ℕ ↦ birkhoffAverage ℝ τ g (n + 1) (τ ω) - birkhoffAverage ℝ τ g (n + 1) ω) =
          fun n : ℕ ↦ g ((τ^[n]) (τ ω)) / (n + 1 : ℝ) - g ω / (n + 1 : ℝ) := by
    intro ω
    funext n
    -- Proof comment: `birkhoffAverage_apply_sub_birkhoffAverage` rewrites the shift difference as
    -- the difference of the orbit endpoints divided by the averaging time.
    simpa [div_eq_mul_inv, sub_mul, mul_comm, mul_left_comm, mul_assoc] using
      (birkhoffAverage_apply_sub_birkhoffAverage (R := ℝ) τ g (n + 1) ω)
  filter_upwards [horbitShift] with ω hω
  -- Proof comment: subtract the vanishing constant-endpoint term from the shifted orbit-endpoint
  -- term, then rewrite back to the Birkhoff-average difference.
  rw [hrewrite ω]
  simpa using hω.sub (hconst ω)

/-- Helper for Theorem 20.14: an almost invariant event is orbitwise stable on a full-measure set.
-/
theorem orbitMembershipStable_ae_of_preimage_ae_eq
    (hτ : MeasurePreserving τ P P) {s : Set Ω} (hs : τ ⁻¹' s =ᵐ[P] s) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ((τ^[k]) ω ∈ s ↔ ω ∈ s) := by
  have hiter :
      ∀ k : ℕ, ∀ᵐ ω ∂P, ((τ^[k]) ω ∈ s ↔ ω ∈ s) := by
    intro k
    -- Proof comment: iterate the almost-invariance once and then read the resulting a.e. set
    -- equality pointwise as orbit-membership equivalence.
    filter_upwards [hτ.quasiMeasurePreserving.preimage_iterate_ae_eq (k := k) hs] with ω hω
    change ω ∈ (τ^[k]) ⁻¹' s ↔ ω ∈ s
    simpa [Set.preimage_iterate_eq] using hω
  -- Proof comment: intersect the countably many iterate-stability events into one full-measure set.
  exact ae_all_iff.2 hiter

/-- Helper for Theorem 20.14: the slackened upper-threshold event for the `(n + 1)`-st Birkhoff
average. -/
def strictUpperSlice (τ : Ω → Ω) (g : Ω → ℝ) (ε : ℝ) (m n : ℕ) : Set Ω :=
  {ω | ε + 1 / (m + 1 : ℝ) < birkhoffAverage ℝ τ g (n + 1) ω}

/-- Helper for Theorem 20.14: the raw strict-upper-limit event `limsup averages > ε`, written as a
countable union of slackened limsup slices. -/
def strictUpperLimitEvent (τ : Ω → Ω) (g : Ω → ℝ) (ε : ℝ) : Set Ω :=
  ⋃ m : ℕ, limsup (α := Set Ω) (fun n : ℕ ↦ strictUpperSlice τ g ε m n) atTop

/-- Helper for Theorem 20.14: on an orbit where membership in the raw strict-upper-limit event is
stable, that raw event is equivalent to positivity of a supported maximal orbit partial sum. -/
theorem strictUpperLimitEvent_supportedMaxOrbit_pointwise
    (ε : ℝ) {ω : Ω}
    (hstable : ∀ k : ℕ,
      ((τ^[k]) ω ∈ strictUpperLimitEvent τ g ε ↔ ω ∈ strictUpperLimitEvent τ g ε)) :
    ω ∈ strictUpperLimitEvent τ g ε ↔
      ∃ n : ℕ,
        0 <
          max_orbit_partial_sum τ
            ((strictUpperLimitEvent τ g ε).indicator (fun ξ ↦ g ξ - ε)) n ω := by
  let bad : Set Ω := strictUpperLimitEvent τ g ε
  let gε : Ω → ℝ := bad.indicator (fun ξ ↦ g ξ - ε)
  constructor
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
    rw [Filter.mem_limsup_iff_frequently_mem] at hm
    rcases hm.exists with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    have horbit_mem : ∀ k ∈ Finset.range (n + 1), (τ^[k]) ω ∈ bad := by
      intro k hk
      exact (hstable k).2 hω
    have hsum_indicator :
        birkhoffSum τ gε (n + 1) ω = birkhoffSum τ (fun ξ ↦ g ξ - ε) (n + 1) ω := by
      -- Proof comment: on the stable orbit segment, the indicator never switches off.
      unfold birkhoffSum gε
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [horbit_mem k hk]
    have havg :
        ε + 1 / (m + 1 : ℝ) < birkhoffSum τ g (n + 1) ω / (n + 1 : ℝ) := by
      -- Proof comment: rewrite the slice membership as a statement about the normalized Birkhoff
      -- sum at time `n + 1`.
      simpa [strictUpperSlice, birkhoffAverage, div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm,
        mul_assoc] using hn
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hm1_pos : (0 : ℝ) < m + 1 := by positivity
    have hsum_gt :
        (n + 1 : ℝ) * (ε + 1 / (m + 1 : ℝ)) < birkhoffSum τ g (n + 1) ω := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (lt_div_iff₀ hn1_pos).1 havg
    have hconst :
        birkhoffSum τ (fun _ : Ω ↦ ε) (n + 1) ω = (n + 1 : ℝ) * ε := by
      -- Proof comment: the Birkhoff sum of a constant observable is the scalar multiple by the
      -- orbit length.
      simpa [nsmul_eq_mul] using
        congrFun (birkhoffSum_of_comp_eq (f := τ) (φ := fun _ : Ω ↦ ε) rfl (n + 1)) ω
    have hsum_sub :
        birkhoffSum τ (fun ξ ↦ g ξ - ε) (n + 1) ω =
          birkhoffSum τ g (n + 1) ω - (n + 1 : ℝ) * ε := by
      -- Proof comment: split the centered Birkhoff sum into the original sum minus the constant
      -- drift term.
      simpa [hconst] using
        (birkhoffSum_sub τ g (fun _ : Ω ↦ ε) (n + 1) ω)
    have hfrac_pos : 0 < (n + 1 : ℝ) / (m + 1 : ℝ) := by positivity
    have hsum_pos : 0 < birkhoffSum τ (fun ξ ↦ g ξ - ε) (n + 1) ω := by
      -- Proof comment: the strict slack `1 / (m + 1)` yields a genuinely positive centered sum.
      have hsum_gt' :
          (n + 1 : ℝ) * ε + (n + 1 : ℝ) / (m + 1 : ℝ) < birkhoffSum τ g (n + 1) ω := by
        have hrewrite :
            (n + 1 : ℝ) * (ε + 1 / (m + 1 : ℝ)) =
              (n + 1 : ℝ) * ε + (n + 1 : ℝ) / (m + 1 : ℝ) := by
          ring
        rw [hrewrite] at hsum_gt
        exact hsum_gt
      have hslack_lt :
          (n + 1 : ℝ) / (m + 1 : ℝ) < birkhoffSum τ (fun ξ ↦ g ξ - ε) (n + 1) ω := by
        rw [hsum_sub]
        linarith
      exact lt_trans hfrac_pos hslack_lt
    have hle :
        birkhoffSum τ gε (n + 1) ω ≤ max_orbit_partial_sum τ gε (n + 1) ω :=
      birkhoffSum_le_max_orbit_partial_sum (τ := τ) (X0 := gε) (k := n + 1) (n := n + 1)
        (le_rfl) ω
    exact lt_of_lt_of_le (hsum_indicator ▸ hsum_pos) hle
  · rintro ⟨n, hn⟩
    by_contra hω
    have horbit_not_mem : ∀ k : ℕ, (τ^[k]) ω ∉ bad := by
      intro k hk
      exact hω ((hstable k).1 hk)
    have hmax_zero : ∀ j : ℕ, max_orbit_partial_sum τ gε j ω = 0 := by
      intro j
      induction j with
      | zero =>
          simp [max_orbit_partial_sum]
      | succ j ih =>
          have hsum_zero : birkhoffSum τ gε (j + 1) ω = 0 := by
            -- Proof comment: if the raw bad event never occurs along the orbit, the supported
            -- observable vanishes on every orbit point.
            simp [gε, birkhoffSum, horbit_not_mem]
          simpa [max_orbit_partial_sum_succ, ih, hsum_zero]
    have hmax_zero' :
        max_orbit_partial_sum τ
            ((strictUpperLimitEvent τ g ε).indicator (fun ξ ↦ g ξ - ε)) n ω = 0 := by
      simpa [gε, bad] using hmax_zero n
    rw [hmax_zero'] at hn
    exact (lt_irrefl (0 : ℝ)) hn

/-- Helper for Theorem 20.14: once the raw strict-upper-limit event is known to be almost
invariant, the deterministic supported-max-orbit witness packages into an almost-everywhere set
equality. -/
theorem strictUpperLimitEvent_supportedMaxOrbit_ae_eq
    (hτ : MeasurePreserving τ P P) (ε : ℝ)
    (hs : τ ⁻¹' strictUpperLimitEvent τ g ε =ᵐ[P] strictUpperLimitEvent τ g ε) :
    (⋃ n : ℕ,
        {ω |
          0 <
            max_orbit_partial_sum τ
              ((strictUpperLimitEvent τ g ε).indicator (fun ξ ↦ g ξ - ε)) n ω}) =ᵐ[P]
      strictUpperLimitEvent τ g ε := by
  have hstable :
      ∀ᵐ ω ∂P, ∀ k : ℕ,
        ((τ^[k]) ω ∈ strictUpperLimitEvent τ g ε ↔ ω ∈ strictUpperLimitEvent τ g ε) :=
    orbitMembershipStable_ae_of_preimage_ae_eq (P := P) (τ := τ) hτ hs
  filter_upwards [hstable] with ω hω
  exact propext <| by
    constructor
    · intro hω_union
      rcases Set.mem_iUnion.1 hω_union with ⟨n, hn⟩
      exact
        (strictUpperLimitEvent_supportedMaxOrbit_pointwise
          (τ := τ) (g := g) (ε := ε) (ω := ω) hω).2 ⟨n, hn⟩
    · intro hω_bad
      rcases
          (strictUpperLimitEvent_supportedMaxOrbit_pointwise
            (τ := τ) (g := g) (ε := ε) (ω := ω) hω).1 hω_bad with
        ⟨n, hn⟩
      exact Set.mem_iUnion.2 ⟨n, hn⟩

/-- Helper for Theorem 20.14: the raw strict-upper-limit event is null measurable. -/
theorem strictUpperLimitEvent_nullMeasurable
    (hτ : MeasurePreserving τ P P) (hg : Integrable g P) (ε : ℝ) :
    NullMeasurableSet (strictUpperLimitEvent τ g ε) P := by
  -- Proof comment: each slack slice is null measurable, so replace it by a measurable hull on a
  -- full-measure set and then take limsups and the outer countable union.
  refine NullMeasurableSet.iUnion fun m ↦ ?_
  let s : ℕ → Set Ω := fun n ↦ strictUpperSlice τ g ε m n
  have hs_null : ∀ n : ℕ, NullMeasurableSet (s n) P := by
    intro n
    have hsum : Integrable (fun ω ↦ birkhoffSum τ g (n + 1) ω) P :=
      integrable_birkhoffSum P hτ hg (n + 1)
    have havg :
        AEStronglyMeasurable (fun ω ↦ birkhoffAverage ℝ τ g (n + 1) ω) P := by
      simpa [birkhoffAverage] using hsum.aestronglyMeasurable.const_smul ((n + 1 : ℝ)⁻¹)
    simpa [s, strictUpperSlice] using
      nullMeasurableSet_lt aemeasurable_const havg.aemeasurable
  let t : ℕ → Set Ω := fun n ↦ toMeasurable P (s n)
  have hs_ae : ∀ n : ℕ, t n =ᵐ[P] s n := by
    intro n
    exact (hs_null n).toMeasurable_ae_eq
  have hlimsup_ae :
      limsup (α := Set Ω) t atTop =ᵐ[P] limsup (α := Set Ω) s atTop := by
    -- Proof comment: on the countable full-measure set where every slice agrees with its
    -- measurable hull, limsup membership is unchanged.
    filter_upwards [ae_all_iff.2 fun n ↦ by simpa [Filter.EventuallyEq] using hs_ae n] with ω hω
    exact propext <| by
      change ω ∈ Filter.limsup t Filter.atTop ↔ ω ∈ Filter.limsup s Filter.atTop
      rw [mem_limsup_iff_frequently_mem, mem_limsup_iff_frequently_mem]
      simpa using
        (frequently_congr (f := atTop) (h := Filter.Eventually.of_forall hω))
  refine (show NullMeasurableSet (Filter.limsup t Filter.atTop) P from
      (show MeasurableSet (Filter.limsup t Filter.atTop) from
        by
          measurability).nullMeasurableSet).congr ?_
  simpa [s, t] using hlimsup_ae

/-- Helper for Theorem 20.14: the raw strict-upper-limit event is almost invariant under `τ`. -/
theorem strictUpperLimitEvent_preimage_ae_eq
    (hτ : MeasurePreserving τ P P) (hg : Integrable g P) (ε : ℝ) :
    τ ⁻¹' strictUpperLimitEvent τ g ε =ᵐ[P] strictUpperLimitEvent τ g ε := by
  have hshift :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n : ℕ ↦
            birkhoffAverage ℝ τ g (n + 1) (τ ω) - birkhoffAverage ℝ τ g (n + 1) ω)
          atTop (𝓝 0) :=
    birkhoffAverage_shiftDiff_tendsto_zero_ae (P := P) (τ := τ) (g := g) hτ hg
  filter_upwards [hshift] with ω hω
  apply propext
  constructor
  · intro hτω
    have hτω' : τ ω ∈ strictUpperLimitEvent τ g ε := by
      simpa [Set.preimage] using hτω
    rcases Set.mem_iUnion.1 hτω' with ⟨m, hm⟩
    rw [mem_limsup_iff_frequently_mem] at hm
    have hhalf_pos : 0 < (1 / (m + 1 : ℝ)) / 2 := by positivity
    obtain ⟨m', hm'⟩ := exists_nat_one_div_lt hhalf_pos
    have hsmall :
        ∀ᶠ n : ℕ in atTop,
          |birkhoffAverage ℝ τ g (n + 1) (τ ω) - birkhoffAverage ℝ τ g (n + 1) ω| <
            (1 / (m + 1 : ℝ)) / 2 := by
      simpa [Real.dist_eq] using Metric.tendsto_atTop.1 hω ((1 / (m + 1 : ℝ)) / 2) hhalf_pos
    refine Set.mem_iUnion.2 ⟨m', ?_⟩
    rw [mem_limsup_iff_frequently_mem]
    refine (hm.and_eventually hsmall).mono ?_
    intro n hn
    rcases hn with ⟨hnBad, hnSmall⟩
    have hnBad' :
        ε + 1 / (m + 1 : ℝ) < birkhoffAverage ℝ τ g (n + 1) (τ ω) := by
      simpa [strictUpperSlice] using hnBad
    have hdiff_upper :
        birkhoffAverage ℝ τ g (n + 1) (τ ω) - birkhoffAverage ℝ τ g (n + 1) ω <
          (1 / (m + 1 : ℝ)) / 2 :=
      (abs_lt.mp hnSmall).2
    -- Proof comment: the witness for `τ ω` survives after shrinking the slack by more than the
    -- eventual shift error.
    have : ε + 1 / (m' + 1 : ℝ) < birkhoffAverage ℝ τ g (n + 1) ω := by
      linarith [hnBad']
    exact this
  · intro hωbad
    rcases Set.mem_iUnion.1 hωbad with ⟨m, hm⟩
    rw [mem_limsup_iff_frequently_mem] at hm
    have hhalf_pos : 0 < (1 / (m + 1 : ℝ)) / 2 := by positivity
    obtain ⟨m', hm'⟩ := exists_nat_one_div_lt hhalf_pos
    have hsmall :
        ∀ᶠ n : ℕ in atTop,
          |birkhoffAverage ℝ τ g (n + 1) (τ ω) - birkhoffAverage ℝ τ g (n + 1) ω| <
            (1 / (m + 1 : ℝ)) / 2 := by
      simpa [Real.dist_eq] using Metric.tendsto_atTop.1 hω ((1 / (m + 1 : ℝ)) / 2) hhalf_pos
    show τ ω ∈ strictUpperLimitEvent τ g ε
    refine Set.mem_iUnion.2 ⟨m', ?_⟩
    rw [mem_limsup_iff_frequently_mem]
    refine (hm.and_eventually hsmall).mono ?_
    intro n hn
    rcases hn with ⟨hnBad, hnSmall⟩
    have hnBad' :
        ε + 1 / (m + 1 : ℝ) < birkhoffAverage ℝ τ g (n + 1) ω := by
      simpa [strictUpperSlice] using hnBad
    have hdiff_lower :
        -(1 / (m + 1 : ℝ) / 2) <
          birkhoffAverage ℝ τ g (n + 1) (τ ω) - birkhoffAverage ℝ τ g (n + 1) ω :=
      (abs_lt.mp hnSmall).1
    -- Proof comment: the reverse implication uses the same slack-shrinking argument with the
    -- opposite sign of the shift error.
    have : ε + 1 / (m' + 1 : ℝ) < birkhoffAverage ℝ τ g (n + 1) (τ ω) := by
      linarith [hnBad']
    exact this

/-- Helper for Theorem 20.14: the raw strict-upper-limit event has measure zero once the centered
conditional expectation vanishes. -/
theorem strictUpperLimitEvent_measure_zero
    (hτ : MeasurePreserving τ P P) (hg : Integrable g P)
    (hzero : P[g | MeasurableSpace.invariants τ] =ᵐ[P] 0)
    {ε : ℝ} (hε : 0 < ε) :
    P (strictUpperLimitEvent τ g ε) = 0 := by
  let bad : Set Ω := strictUpperLimitEvent τ g ε
  let gε : Ω → ℝ := bad.indicator (fun ω ↦ g ω - ε)
  have hbad_null : NullMeasurableSet bad P :=
    strictUpperLimitEvent_nullMeasurable (P := P) (τ := τ) (g := g) hτ hg ε
  have hbad_pre :
      τ ⁻¹' bad =ᵐ[P] bad := by
    simpa [bad] using
      strictUpperLimitEvent_preimage_ae_eq (P := P) (τ := τ) (g := g) hτ hg ε
  have hgε : Integrable gε P := by
    -- Proof comment: the supported centered observable is integrable because it is an indicator of
    -- an integrable function on a null measurable set.
    simpa [gε] using (hg.sub (integrable_const ε)).indicator₀ hbad_null
  let Fn : ℕ → Set Ω := fun n ↦ {ω | 0 < max_orbit_partial_sum τ gε n ω}
  have hFn_null : ∀ n : ℕ, NullMeasurableSet (Fn n) P := by
    intro n
    have hmax_int : Integrable (fun ω ↦ max_orbit_partial_sum τ gε n ω) P := by
      induction n with
      | zero =>
          simpa [max_orbit_partial_sum]
      | succ n ih =>
          have hsum : Integrable (fun ω ↦ birkhoffSum τ gε (n + 1) ω) P :=
            integrable_birkhoffSum P hτ hgε (n + 1)
          have hsup :
              Integrable
                (fun ω ↦ max (max_orbit_partial_sum τ gε n ω) (birkhoffSum τ gε (n + 1) ω)) P :=
            ih.sup hsum
          simpa [max_orbit_partial_sum_succ] using hsup
    simpa [Fn] using
      nullMeasurableSet_lt aemeasurable_const hmax_int.aestronglyMeasurable.aemeasurable
  have hFn_mono : Monotone Fn := by
    -- Proof comment: the maximal orbit partial sums are increasing in the time index.
    refine monotone_nat_of_le_succ fun n ω hω ↦ ?_
    have hle : max_orbit_partial_sum τ gε n ω ≤ max_orbit_partial_sum τ gε (n + 1) ω := by
      rw [max_orbit_partial_sum_succ]
      exact le_max_left _ _
    exact lt_of_lt_of_le hω hle
  have hFn_nonneg : ∀ n : ℕ, 0 ≤ ∫ ω in Fn n, gε ω ∂P := by
    intro n
    simpa [Fn] using
      integral_nonneg_on_maxOrbitPartialSumPosLocal
        (P := P) (τ := τ) (X0 := gε) hτ hgε n
  have hFn_union :
      (⋃ n : ℕ, Fn n) =ᵐ[P] bad := by
    simpa [Fn, bad, gε] using
      strictUpperLimitEvent_supportedMaxOrbit_ae_eq
        (P := P) (τ := τ) (g := g) hτ ε hbad_pre
  have hFn_tendsto :
      Tendsto (fun n : ℕ ↦ ∫ ω in Fn n, gε ω ∂P) atTop
        (𝓝 (∫ ω in ⋃ n, Fn n, gε ω ∂P)) := by
    exact tendsto_setIntegral_of_monotone₀ hFn_null hFn_mono hgε.integrableOn
  have hunion_nonneg : 0 ≤ ∫ ω in ⋃ n, Fn n, gε ω ∂P := by
    exact ge_of_tendsto' hFn_tendsto fun n ↦ hFn_nonneg n
  have hbad_nonneg : 0 ≤ ∫ ω in bad, gε ω ∂P := by
    calc
      0 ≤ ∫ ω in ⋃ n, Fn n, gε ω ∂P := hunion_nonneg
      _ = ∫ ω in bad, gε ω ∂P := setIntegral_congr_set hFn_union
  rcases
      hτ.quasiMeasurePreserving.exists_preimage_eq_of_preimage_ae
        (s := bad) hbad_null hbad_pre with
    ⟨t, ht_meas, ht_ae, ht_pre⟩
  have ht_inv : MeasurableSet[MeasurableSpace.invariants τ] t := by
    exact MeasurableSpace.measurableSet_invariants.mpr ⟨ht_meas, ht_pre⟩
  have hbad_g_zero : ∫ ω in bad, g ω ∂P = 0 := by
    -- Proof comment: replace the raw bad event by an exactly invariant measurable representative
    -- before applying the centered conditional-expectation identity.
    calc
      ∫ ω in bad, g ω ∂P = ∫ ω in t, g ω ∂P := by
        symm
        exact setIntegral_congr_set ht_ae
      _ = 0 := by
        exact
          setIntegral_eq_zero_of_condExpInvariants_aeZero
            (P := P) (τ := τ) (g := g) hg hzero ht_inv
  have hbad_gε :
      ∫ ω in bad, gε ω ∂P = ∫ ω in bad, (g ω - ε) ∂P := by
    -- Proof comment: on the raw bad event itself, the indicator in `gε` is identically `1`.
    refine setIntegral_congr_fun₀ hbad_null ?_
    intro ω hω
    simp [gε, hω]
  have hbad_centered :
      ∫ ω in bad, (g ω - ε) ∂P = -ε * P.real bad := by
    calc
      ∫ ω in bad, (g ω - ε) ∂P = ∫ ω in bad, g ω ∂P - ∫ ω in bad, ε ∂P := by
        rw [integral_sub hg.integrableOn (integrable_const ε).integrableOn]
      _ = 0 - ∫ ω in bad, ε ∂P := by simp [hbad_g_zero]
      _ = 0 - P.real bad * ε := by simp [setIntegral_const]
      _ = -ε * P.real bad := by ring
  have hineq : 0 ≤ -ε * P.real bad := by
    calc
      0 ≤ ∫ ω in bad, gε ω ∂P := hbad_nonneg
      _ = ∫ ω in bad, (g ω - ε) ∂P := hbad_gε
      _ = -ε * P.real bad := hbad_centered
  have hreal_nonneg : 0 ≤ P.real bad := by positivity
  have hreal_nonpos : P.real bad ≤ 0 := by
    by_contra hpos
    have hxpos : 0 < P.real bad := lt_of_not_ge hpos
    have hneg : -ε * P.real bad < 0 := by
      nlinarith
    exact (not_lt_of_ge hineq) hneg
  have hreal_zero : P.real bad = 0 := le_antisymm hreal_nonpos hreal_nonneg
  exact (measureReal_eq_zero_iff (μ := P) (s := bad)).1 hreal_zero

/-- Helper for Theorem 20.14: outside the raw strict-upper-limit event, every slack level gives an
eventual upper bound on the shifted Birkhoff averages. -/
theorem not_mem_strictUpperLimitEvent_iff
    (ε : ℝ) (ω : Ω) :
    ω ∉ strictUpperLimitEvent τ g ε ↔
      ∀ m : ℕ,
        ∀ᶠ n : ℕ in atTop, birkhoffAverage ℝ τ g (n + 1) ω ≤ ε + 1 / (m + 1 : ℝ) := by
  constructor
  · intro hω m
    have hm : ω ∉ limsup (α := Set Ω) (fun n : ℕ ↦ strictUpperSlice τ g ε m n) atTop := by
      intro hm
      exact hω (Set.mem_iUnion.2 ⟨m, hm⟩)
    rw [mem_limsup_iff_frequently_mem, not_frequently] at hm
    simpa [strictUpperSlice, not_lt] using hm
  · intro hω hbad
    rcases Set.mem_iUnion.1 hbad with ⟨m, hm⟩
    rw [mem_limsup_iff_frequently_mem] at hm
    have hnot :
        ∀ᶠ n : ℕ in atTop, ω ∉ strictUpperSlice τ g ε m n := by
      simpa [strictUpperSlice, not_lt] using hω m
    exact ((not_frequently).2 hnot) hm

/-- Helper for Theorem 20.14: once the centered maximal-ergodic core is restored, the centered
Birkhoff averages converge almost surely to `0`. -/
theorem centered_birkhoffAverage_tendsto_zero_ae
    (hτ : MeasurePreserving τ P P) (hg : Integrable g P)
    (hzero : P[g | MeasurableSpace.invariants τ] =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ τ g n ω) atTop (𝓝 0) := by
  have hzero_neg : P[-g | MeasurableSpace.invariants τ] =ᵐ[P] 0 := by
    -- Proof comment: conditional expectation commutes with negation, so the centered hypothesis
    -- propagates to `-g`.
    refine (condExp_neg (μ := P) (f := g) (m := MeasurableSpace.invariants τ)).trans ?_
    filter_upwards [hzero] with ω hω
    simp [hω]
  have havoid :
      ∀ m : ℕ,
        ∀ᵐ ω ∂P,
          ω ∉ strictUpperLimitEvent τ g (1 / (m + 1 : ℝ)) ∧
            ω ∉ strictUpperLimitEvent τ (-g) (1 / (m + 1 : ℝ)) := by
    intro m
    have hμg :
        P (strictUpperLimitEvent τ g (1 / (m + 1 : ℝ))) = 0 :=
      strictUpperLimitEvent_measure_zero
        (P := P) (τ := τ) (g := g) hτ hg hzero (by positivity)
    have hμneg :
        P (strictUpperLimitEvent τ (-g) (1 / (m + 1 : ℝ))) = 0 :=
      strictUpperLimitEvent_measure_zero
        (P := P) (τ := τ) (g := -g) hτ hg.neg hzero_neg (by positivity)
    have hmem_g : ∀ᵐ ω ∂P, ω ∉ strictUpperLimitEvent τ g (1 / (m + 1 : ℝ)) := by
      rw [ae_iff]
      simpa using hμg
    have hmem_neg : ∀ᵐ ω ∂P, ω ∉ strictUpperLimitEvent τ (-g) (1 / (m + 1 : ℝ)) := by
      rw [ae_iff]
      simpa using hμneg
    filter_upwards [hmem_g, hmem_neg] with ω hωg hωneg
    exact ⟨hωg, hωneg⟩
  filter_upwards [ae_all_iff.2 havoid] with ω hω
  -- Proof comment: avoid all strict-upper events for `g` and `-g`, then convert those countably
  -- many exclusions into eventual two-sided bounds and hence convergence to `0`.
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  let δ : ℝ := 1 / (m + 1 : ℝ)
  have hupper :
      ∀ᶠ n : ℕ in atTop, birkhoffAverage ℝ τ g (n + 1) ω ≤ δ + 1 / (m + 1 : ℝ) := by
    simpa [δ] using
      (not_mem_strictUpperLimitEvent_iff (τ := τ) (g := g) (ε := δ) (ω := ω)).1 (hω m).1 m
  have hlower :
      ∀ᶠ n : ℕ in atTop, -birkhoffAverage ℝ τ g (n + 1) ω ≤ δ + 1 / (m + 1 : ℝ) := by
    have hnegUpper :
        ∀ᶠ n : ℕ in atTop, birkhoffAverage ℝ τ (-g) (n + 1) ω ≤ δ + 1 / (m + 1 : ℝ) := by
      simpa [δ] using
        (not_mem_strictUpperLimitEvent_iff (τ := τ) (g := -g) (ε := δ) (ω := ω)).1 (hω m).2 m
    filter_upwards [hnegUpper] with n hn
    simpa [birkhoffAverage_neg] using hn
  rcases Filter.eventually_atTop.1 (hupper.and hlower) with ⟨N, hN⟩
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  have hpred : N ≤ n - 1 := by
    omega
  have hbounds := hN (n - 1) hpred
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ N) hn
  have hupper_n : birkhoffAverage ℝ τ g n ω ≤ δ + 1 / (m + 1 : ℝ) := by
    have hn_eq : (n - 1) + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
    simpa [hn_eq] using hbounds.1
  have hlower_n : -birkhoffAverage ℝ τ g n ω ≤ δ + 1 / (m + 1 : ℝ) := by
    have hn_eq : (n - 1) + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
    simpa [hn_eq] using hbounds.2
  have hdist :
      dist (birkhoffAverage ℝ τ g n ω) 0 < ε := by
    have habs :
        |birkhoffAverage ℝ τ g n ω| ≤ δ + 1 / (m + 1 : ℝ) := by
      refine abs_le.2 ?_
      constructor
      · linarith
      · exact hupper_n
    have hlt : δ + 1 / (m + 1 : ℝ) < ε := by
      linarith
    simpa [Real.dist_eq] using lt_of_le_of_lt habs hlt
  simpa using hdist

/-- Theorem 20.14: for an integrable observable on a probability space with a
measure-preserving transformation `τ`, the Birkhoff averages converge almost surely to the
conditional expectation onto the invariant σ-algebra `MeasurableSpace.invariants τ`. -/
theorem birkhoffAverage_tendsto_ae_condExp_invariants
    (hτ : MeasurePreserving τ P P) (hf : Integrable f P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ τ f n ω) atTop
        (𝓝 (P[f | MeasurableSpace.invariants τ] ω)) := by
  -- Route correction: the source owner file was blanked, so the recovered frontier here is the
  -- de-centering shell. The remaining centered maximal-ergodic core still has to be restored.
  let g : Ω → ℝ := fun ω ↦ f ω - P[f | MeasurableSpace.invariants τ] ω
  have hg : Integrable g P := hf.sub integrable_condExp
  have hzero :
      P[g | MeasurableSpace.invariants τ] =ᵐ[P] 0 := by
    simpa [g] using condExp_sub_condExpInvariants_ae_eq_zero (P := P) (τ := τ) (f := f) hf
  have hcondComp : P[f | MeasurableSpace.invariants τ] ∘ τ = P[f | MeasurableSpace.invariants τ] :=
    condExpInvariants_comp_eq τ P f
  have hcentered :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ τ g n ω) atTop (𝓝 0) :=
    centered_birkhoffAverage_tendsto_zero_ae (P := P) (τ := τ) (g := g) hτ hg hzero
  filter_upwards [hcentered] with ω hω
  have hcondAvg :
      Tendsto
        (fun n : ℕ ↦ birkhoffAverage ℝ τ (P[f | MeasurableSpace.invariants τ]) n ω)
        atTop (𝓝 (P[f | MeasurableSpace.invariants τ] ω)) := by
    have hEventuallyConst :
        ∀ᶠ n : ℕ in atTop,
          birkhoffAverage ℝ τ (P[f | MeasurableSpace.invariants τ]) n ω =
            P[f | MeasurableSpace.invariants τ] ω := by
      -- Proof comment: away from the initial index `0`, the Birkhoff averages of an invariant
      -- function are exactly constant.
      refine Filter.eventually_atTop.2 ?_
      refine ⟨1, fun n hn ↦ ?_⟩
      have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
      exact congrFun
        (birkhoffAverage_of_comp_eq (R := ℝ) hcondComp
          (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos))) ω
    have hEventuallyConst' :
        (fun _ : ℕ ↦ P[f | MeasurableSpace.invariants τ] ω) =ᶠ[atTop]
          fun n : ℕ ↦ birkhoffAverage ℝ τ (P[f | MeasurableSpace.invariants τ]) n ω := by
      filter_upwards [hEventuallyConst] with n hn
      simp [hn]
    -- Proof comment: replace the sequence by the eventually constant one and use the constant
    -- limit.
    exact
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ P[f | MeasurableSpace.invariants τ] ω)
        atTop (𝓝 (P[f | MeasurableSpace.invariants τ] ω))).congr' hEventuallyConst'
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          birkhoffAverage ℝ τ g n ω +
            birkhoffAverage ℝ τ (P[f | MeasurableSpace.invariants τ]) n ω)
        atTop (𝓝 (P[f | MeasurableSpace.invariants τ] ω)) := by
    -- Proof comment: add the centered limit `0` to the invariant part.
    simpa using hω.add hcondAvg
  have hdecomp :
      (fun n : ℕ ↦ birkhoffAverage ℝ τ f n ω) =
        fun n : ℕ ↦
          birkhoffAverage ℝ τ g n ω +
            birkhoffAverage ℝ τ (P[f | MeasurableSpace.invariants τ]) n ω := by
    funext n
    -- Proof comment: the Birkhoff average is linear, so the original observable splits into the
    -- centered part plus its invariant conditional expectation.
    have hsub :=
      congrFun
        (congrFun
          (birkhoffAverage_sub (R := ℝ) (f := τ) (g := f)
            (g' := P[f | MeasurableSpace.invariants τ])) n) ω
    linarith [show birkhoffAverage ℝ τ g n ω =
      birkhoffAverage ℝ τ f n ω -
        birkhoffAverage ℝ τ (P[f | MeasurableSpace.invariants τ]) n ω by
      simpa [g] using hsub]
  rw [hdecomp]
  exact hsum

/-- Helper for Theorem 20.14: under ergodicity, the Birkhoff averages converge almost surely
to the expectation of `f`. -/
theorem birkhoffAverage_tendsto_ae_expectation_of_ergodic
    (hτ : Ergodic τ P) (hf : Integrable f P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ τ f n ω) atTop (𝓝 (∫ ω, f ω ∂P)) := by
  -- Proof comment: combine the general almost-sure Birkhoff theorem with the ergodic
  -- identification of the invariant conditional expectation.
  filter_upwards
    [ birkhoffAverage_tendsto_ae_condExp_invariants
        (P := P) (τ := τ) (f := f) hτ.toMeasurePreserving hf
    , condExpInvariantsAeEqExpectationOfErgodic (P := P) (τ := τ) (f := f) hτ hf
    ] with ω hω hμ
  simpa [hμ] using hω
