/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MeasureTheory
open MeasureTheory

universe u

variable {Ω : Type u}

/-- The maximal orbit partial sum `M_n = max {0, S₁, ..., Sₙ}`, where
`S_k(ω) = birkhoffSum τ X0 k ω`. -/
def max_orbit_partial_sum (τ : Ω → Ω) (X0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | n + 1 => fun ω ↦ max (max_orbit_partial_sum τ X0 n ω) (birkhoffSum τ X0 (n + 1) ω)

/-- The maximal orbit partial sum vanishes at time `0`. -/
theorem max_orbit_partial_sum_zero (τ : Ω → Ω) (X0 : Ω → ℝ) :
    max_orbit_partial_sum τ X0 0 = 0 := rfl

/-- The maximal orbit partial sums satisfy the expected recursion by adjoining the next partial
sum to the running maximum. -/
theorem max_orbit_partial_sum_succ (τ : Ω → Ω) (X0 : Ω → ℝ) (n : ℕ) :
    max_orbit_partial_sum τ X0 (n + 1) =
      fun ω ↦ max (max_orbit_partial_sum τ X0 n ω) (birkhoffSum τ X0 (n + 1) ω) := rfl

variable [MeasurableSpace Ω]

/-- Helper for Lemma 20.13: every Birkhoff sum of an integrable observable remains integrable under
an invariant measure. -/
lemma integrable_birkhoffSum (P : Measure Ω) {τ : Ω → Ω} (hτ : MeasurePreserving τ P P)
    {X0 : Ω → ℝ} (hX0 : Integrable X0 P) (n : ℕ) :
    Integrable (fun ω ↦ birkhoffSum τ X0 n ω) P := by
  -- Proof step: unfold the successor recursion `S_{n+1} = X0 + S_n ∘ τ` and use measure
  -- preservation to transport integrability across the shift.
  induction n with
  | zero =>
      simp [birkhoffSum]
  | succ n ih =>
      rw [show (fun ω ↦ birkhoffSum τ X0 (n + 1) ω) =
          fun ω ↦ X0 ω + birkhoffSum τ X0 n (τ ω) by
            funext ω
            rw [birkhoffSum_succ']]
      exact hX0.add (hτ.integrable_comp_of_integrable ih)

omit [MeasurableSpace Ω] in
/-- Helper for Lemma 20.13: each partial sum is dominated by the running maximum of the orbit
partial sums. -/
lemma birkhoffSum_le_max_orbit_partial_sum {τ : Ω → Ω} {X0 : Ω → ℝ} {k n : ℕ}
    (hk : k ≤ n) (ω : Ω) :
    birkhoffSum τ X0 k ω ≤ max_orbit_partial_sum τ X0 n ω := by
  -- Proof step: at time `n + 1`, either `k = n + 1`, when the new partial sum is one branch of
  -- the max, or `k ≤ n`, when the induction hypothesis survives through `le_max_left`.
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [max_orbit_partial_sum]
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hk with rfl | hklt
      · rw [max_orbit_partial_sum_succ]
        exact le_max_right _ _
      · have hkn : k ≤ n := Nat.le_of_lt_succ hklt
        exact (ih hkn).trans (le_max_left _ _)

omit [MeasurableSpace Ω] in
/-- Helper for Lemma 20.13: the maximal orbit partial sum is always nonnegative because `0` is one
of the admissible partial sums. -/
lemma max_orbit_partial_sum_nonneg {τ : Ω → Ω} {X0 : Ω → ℝ} (n : ℕ) (ω : Ω) :
    0 ≤ max_orbit_partial_sum τ X0 n ω := by
  -- Proof step: apply the comparison lemma to the zeroth Birkhoff sum, which is identically `0`.
  simpa using (birkhoffSum_le_max_orbit_partial_sum (τ := τ) (X0 := X0) (k := 0) (n := n)
    (Nat.zero_le n) ω)

omit [MeasurableSpace Ω] in
/-- Helper for Lemma 20.13: on the positivity set of `M_n`, the source inequality
`M_n ≤ X0 + M_n ∘ τ` holds pointwise. -/
lemma max_orbit_partial_sum_le_base_add_shift_on_pos {τ : Ω → Ω} {X0 : Ω → ℝ} {n : ℕ}
    {ω : Ω} (hω : 0 < max_orbit_partial_sum τ X0 n ω) :
    max_orbit_partial_sum τ X0 n ω ≤ X0 ω + max_orbit_partial_sum τ X0 n (τ ω) := by
  -- Proof step: split the recursive max defining `M_{n+1}`. The new Birkhoff-sum branch is
  -- controlled by `birkhoffSum_succ'`, while the old-max branch uses the induction hypothesis when
  -- it is positive and otherwise is below the positive new branch.
  induction n generalizing ω with
  | zero =>
      simp [max_orbit_partial_sum] at hω
  | succ n ih =>
      rw [max_orbit_partial_sum_succ] at hω ⊢
      have hsum :
          birkhoffSum τ X0 (n + 1) ω ≤
            X0 ω + max_orbit_partial_sum τ X0 (n + 1) (τ ω) := by
        calc
          birkhoffSum τ X0 (n + 1) ω = X0 ω + birkhoffSum τ X0 n (τ ω) := by
            rw [birkhoffSum_succ']
          _ ≤ X0 ω + max_orbit_partial_sum τ X0 n (τ ω) := by
            gcongr
            exact birkhoffSum_le_max_orbit_partial_sum (τ := τ) (X0 := X0) (k := n)
              (n := n) (le_rfl) (τ ω)
          _ ≤ X0 ω + max_orbit_partial_sum τ X0 (n + 1) (τ ω) := by
            gcongr
            exact le_max_left _ _
      by_cases hprev : 0 < max_orbit_partial_sum τ X0 n ω
      · have hprev' :
            max_orbit_partial_sum τ X0 n ω ≤
              X0 ω + max_orbit_partial_sum τ X0 (n + 1) (τ ω) := by
          calc
            max_orbit_partial_sum τ X0 n ω ≤ X0 ω + max_orbit_partial_sum τ X0 n (τ ω) :=
              ih hprev
            _ ≤ X0 ω + max_orbit_partial_sum τ X0 (n + 1) (τ ω) := by
              gcongr
              exact le_max_left _ _
        exact max_le hprev' hsum
      · have hprev_nonpos : max_orbit_partial_sum τ X0 n ω ≤ 0 := le_of_not_gt hprev
        have hsum_pos : 0 < birkhoffSum τ X0 (n + 1) ω := by
          by_contra hsum_not_pos
          have hsum_nonpos : birkhoffSum τ X0 (n + 1) ω ≤ 0 := le_of_not_gt hsum_not_pos
          have hmax_nonpos :
              max (max_orbit_partial_sum τ X0 n ω) (birkhoffSum τ X0 (n + 1) ω) ≤ 0 :=
            max_le hprev_nonpos hsum_nonpos
          exact (not_lt_of_ge hmax_nonpos) hω
        have hprev_le_sum : max_orbit_partial_sum τ X0 n ω ≤ birkhoffSum τ X0 (n + 1) ω := by
          linarith
        exact max_le (hprev_le_sum.trans hsum) hsum

/-- Lemma 20.13: in a measure-preserving dynamical system, if `X0` is integrable and
`M_n = max {0, S₁, ..., Sₙ}` with `S_k = birkhoffSum τ X0 k` is the maximal orbit partial sum of
`X0`, then the integral of
`X0` over the event `{M_n > 0}` is nonnegative. -/
-- Proof sketch: compare `X0` with `max {S_1, ..., S_n} - M_n ∘ τ` using the recursion
-- `S_{k+1} = X0 + S_k ∘ τ`; on `{M_n ≤ 0}` one has `M_n - M_n ∘ τ ≤ 0`, so restricting to
-- `{M_n > 0}` yields a lower bound by `M_n - M_n ∘ τ`, and measure preservation cancels the two
-- integrals of `M_n`.
theorem integral_nonneg_on_max_orbit_partial_sum_pos
    (P : Measure Ω) {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) {X0 : Ω → ℝ} (hX0 : Integrable X0 P)
    (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < max_orbit_partial_sum τ X0 n ω}, X0 ω ∂P := by
  let A : Set Ω := {ω | 0 < max_orbit_partial_sum τ X0 n ω}
  let M : Ω → ℝ := fun ω ↦ max_orbit_partial_sum τ X0 n ω
  let Δ : Ω → ℝ := fun ω ↦ M ω - M (τ ω)
  have hMint : Integrable M P := by
    -- Proof step: the recursive definition of `M_n` preserves integrability because it is built
    -- from Birkhoff sums by repeatedly taking pointwise maxima.
    induction n with
    | zero =>
        dsimp [M, max_orbit_partial_sum]
        exact integrable_zero Ω ℝ P
    | succ n ih =>
        have hsup :
            Integrable
              (fun ω ↦ max (max_orbit_partial_sum τ X0 n ω) (birkhoffSum τ X0 (n + 1) ω)) P :=
          ih.sup (integrable_birkhoffSum P hτ hX0 (n + 1))
        refine hsup.congr ?_
        filter_upwards with ω
        simp [M, max_orbit_partial_sum]
  have hA : NullMeasurableSet A P := by
    -- Proof step: integrability of `M_n` gives enough almost-everywhere measurability to treat
    -- the positivity event with the null-measurable set-integral lemmas.
    simpa [A, M] using
      nullMeasurableSet_lt
        (aemeasurable_const : AEMeasurable (fun _ : Ω ↦ (0 : ℝ)) P)
        hMint.aestronglyMeasurable.aemeasurable
  have hMshift : Integrable (fun ω ↦ M (τ ω)) P :=
    hτ.integrable_comp_of_integrable hMint
  have hΔint : Integrable Δ P := hMint.sub hMshift
  have hΔindicator : Integrable (A.indicator Δ) P := hΔint.indicator₀ hA
  have hmap_M :
      ∫ ω, M (τ ω) ∂P = ∫ ω, M ω ∂P := by
    -- Proof step: push forward `P` by `τ` and rewrite with `hτ.map_eq`.
    have hM_map : AEStronglyMeasurable M (Measure.map τ P) := by
      simpa [hτ.map_eq] using hMint.aestronglyMeasurable
    calc
      ∫ ω, M (τ ω) ∂P = ∫ ω, M ω ∂Measure.map τ P := by
        symm
        exact integral_map hτ.aemeasurable hM_map
      _ = ∫ ω, M ω ∂P := by
        simp [hτ.map_eq]
  have hΔzero : ∫ ω, Δ ω ∂P = 0 := by
    -- Proof step: the two integrals in `Δ = M_n - M_n ∘ τ` cancel by measure preservation.
    dsimp [Δ]
    rw [integral_sub hMint hMshift, hmap_M, sub_self]
  have hΔ_le_indicator : ∀ᵐ ω ∂P, Δ ω ≤ A.indicator Δ ω := by
    -- Proof step: on `A` the indicator leaves `Δ` unchanged, while on `Aᶜ` the nonnegativity of
    -- `M_n ∘ τ` forces `Δ ≤ 0`.
    filter_upwards with ω
    by_cases hω : 0 < M ω
    · have hωA : ω ∈ A := by
        simpa [A, M] using hω
      simp [Set.indicator_of_mem hωA]
    · have hω_nonpos : M ω ≤ 0 := le_of_not_gt hω
      have hτω_nonneg : 0 ≤ M (τ ω) := by
        simpa [M] using max_orbit_partial_sum_nonneg (τ := τ) (X0 := X0) n (τ ω)
      have hΔ_nonpos : Δ ω ≤ 0 := by
        dsimp [Δ]
        linarith
      have hωA : ω ∉ A := by
        simpa [A, M] using hω
      simpa [Set.indicator_of_notMem hωA] using hΔ_nonpos
  have hΔ_le_X0_on_A : ∀ ω ∈ A, Δ ω ≤ X0 ω := by
    -- Proof step: rearrange the source inequality `M_n ≤ X0 + M_n ∘ τ` on the positivity set.
    intro ω hω
    have hpoint :
        max_orbit_partial_sum τ X0 n ω ≤ X0 ω + max_orbit_partial_sum τ X0 n (τ ω) :=
      max_orbit_partial_sum_le_base_add_shift_on_pos (τ := τ) (X0 := X0) hω
    dsimp [Δ, M]
    linarith
  have hset_le :
      ∫ ω in A, Δ ω ∂P ≤ ∫ ω in A, X0 ω ∂P := by
    exact setIntegral_mono_on₀ (hf := hΔint.integrableOn) (hg := hX0.integrableOn) hA hΔ_le_X0_on_A
  -- Proof step: compare the full-space integral of `Δ` with its restriction to `A`, then bound
  -- that restricted integral by the target set integral of `X0`.
  calc
    0 = ∫ ω, Δ ω ∂P := hΔzero.symm
    _ ≤ ∫ ω, A.indicator Δ ω ∂P := integral_mono_ae hΔint hΔindicator hΔ_le_indicator
    _ = ∫ ω in A, Δ ω ∂P := integral_indicator₀ hA
    _ ≤ ∫ ω in A, X0 ω ∂P := hset_le
    _ = ∫ ω in {ω | 0 < max_orbit_partial_sum τ X0 n ω}, X0 ω ∂P := by simp [A]
