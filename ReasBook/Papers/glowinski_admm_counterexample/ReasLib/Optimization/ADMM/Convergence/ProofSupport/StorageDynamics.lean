module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

open scoped BigOperators
open Filter

namespace ADMM.ConvergenceProof

/-- Summing a one-step storage inequality bounds all accumulated dissipation.
The initial storage is arbitrary; no positivity of its quadratic part is used. -/
theorem storage_partialSum_le {U D : ℕ → ℝ}
    (hstep : ∀ k, U (k + 1) + D k ≤ U k) (N : ℕ) :
    U N + ∑ k ∈ Finset.range N, D k ≤ U 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]

/-- Nonnegative storage and nonnegative dissipation make dissipation summable. -/
theorem storage_dissipation_summable {U D : ℕ → ℝ}
    (hU : ∀ k, 0 ≤ U k) (hD : ∀ k, 0 ≤ D k)
    (hstep : ∀ k, U (k + 1) + D k ≤ U k) : Summable D := by
  apply summable_of_sum_range_le hD
  intro N
  linarith [storage_partialSum_le hstep N, hU N]

/-- A nonnegative merit term and residual square controlled by storage descent
are separately summable. -/
theorem storage_two_dissipations_summable {U F R : ℕ → ℝ} {ω ε : ℝ}
    (hω : 0 < ω) (hε : 0 < ε)
    (hU : ∀ k, 0 ≤ U k) (hF : ∀ k, 0 ≤ F k) (hR : ∀ k, 0 ≤ R k)
    (hstep : ∀ k, U (k + 1) + ω * F k + ε * R k ≤ U k) :
    Summable F ∧ Summable R := by
  have hFstep : ∀ k, U (k + 1) + ω * F k ≤ U k := by
    intro k
    linarith [hstep k, mul_nonneg hε.le (hR k)]
  have hRstep : ∀ k, U (k + 1) + ε * R k ≤ U k := by
    intro k
    linarith [hstep k, mul_nonneg hω.le (hF k)]
  have hFs := storage_dissipation_summable hU
    (fun k ↦ mul_nonneg hω.le (hF k)) hFstep
  have hRs := storage_dissipation_summable hU
    (fun k ↦ mul_nonneg hε.le (hR k)) hRstep
  constructor
  · simpa only [← mul_assoc, inv_mul_cancel₀ hω.ne', one_mul] using hFs.mul_left ω⁻¹
  · simpa only [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] using hRs.mul_left ε⁻¹

/-- Storage descent with nonnegative dissipation makes storage nonincreasing. -/
theorem storage_antitone {U D : ℕ → ℝ} (hD : ∀ k, 0 ≤ D k)
    (hstep : ∀ k, U (k + 1) + D k ≤ U k) : Antitone U := by
  apply antitone_nat_of_succ_le
  intro k
  linarith [hstep k, hD k]

/-- The coercive lower bound and descent control every state square uniformly. -/
theorem storage_coercive_bound {U S : ℕ → ℝ} {ζ : ℝ} (hζ : 0 < ζ)
    (hlower : ∀ k, ζ * S k ≤ U k) (hU : Antitone U) (k : ℕ) :
    S k ≤ U 0 / ζ := by
  apply (le_div_iff₀ hζ).2
  simpa only [mul_comm] using (hlower k).trans (hU (Nat.zero_le k))

/-- A nonincreasing storage with a subsequence converging to zero converges to
zero on the entire sequence. This is the recentering step of the orbit proof. -/
theorem storage_tendsto_zero_of_subsequence {U : ℕ → ℝ}
    (hU : Antitone U) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hsub : Tendsto (U ∘ σ) atTop (nhds 0)) : Tendsto U atTop (nhds 0) := by
  exact (tendsto_iff_tendsto_subseq_of_antitone hU hσ.tendsto_atTop).2 hsub

/-- Coercivity turns vanishing storage into vanishing nonnegative state square. -/
theorem storage_coercive_tendsto_zero {U S : ℕ → ℝ} {ζ : ℝ}
    (hζ : 0 < ζ) (hS : ∀ k, 0 ≤ S k) (hlower : ∀ k, ζ * S k ≤ U k)
    (hU : Tendsto U atTop (nhds 0)) : Tendsto S atTop (nhds 0) := by
  apply squeeze_zero hS
  · intro k
    exact (le_div_iff₀ hζ).2 (by simpa only [mul_comm] using hlower k)
  · simpa only [zero_div] using hU.div_const ζ

/-- A vector whose norm square tends to zero tends to zero. -/
theorem tendsto_zero_of_norm_sq {E : Type*} [SeminormedAddCommGroup E]
    {x : ℕ → E} (h : Tendsto (fun k ↦ ‖x k‖ ^ 2) atTop (nhds 0)) :
    Tendsto x atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h.sqrt

/-- Coercive storage tending to zero forces the whole recentered vector state
to converge, without any positivity assumption on individual storage terms. -/
theorem storage_norm_tendsto_zero {E : Type*} [SeminormedAddCommGroup E]
    {U : ℕ → ℝ} {x : ℕ → E} {ζ : ℝ} (hζ : 0 < ζ)
    (hlower : ∀ k, ζ * ‖x k‖ ^ 2 ≤ U k)
    (hU : Tendsto U atTop (nhds 0)) : Tendsto x atTop (nhds 0) := by
  apply tendsto_zero_of_norm_sq
  exact storage_coercive_tendsto_zero hζ (fun k ↦ sq_nonneg _) hlower hU

/-- A summable forcing term allows summation of an auxiliary energy estimate.
This yields summability of second-image increments from summable residuals. -/
theorem energy_forced_dissipation_summable {L D R : ℕ → ℝ}
    (hL : ∀ k, 0 ≤ L k) (hD : ∀ k, 0 ≤ D k) (hR : ∀ k, 0 ≤ R k)
    (hRs : Summable R) (hstep : ∀ k, L (k + 1) + D k ≤ L k + R k) :
    Summable D := by
  have hsum : ∀ N, L N + ∑ k ∈ Finset.range N, D k ≤
      L 0 + ∑ k ∈ Finset.range N, R k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linarith [hstep N]
  apply summable_of_sum_range_le hD (c := L 0 + ∑' k, R k)
  intro N
  have hRbound := hRs.sum_le_tsum (Finset.range N) (fun k _ ↦ hR k)
  linarith [hsum N, hL N]

/-- An energy with summable nonnegative errors has a finite limit. Subtracting
accumulated errors produces an ordinary nonincreasing, bounded-below sequence. -/
theorem energy_exists_limit {L R : ℕ → ℝ}
    (hL : ∀ k, 0 ≤ L k) (hR : ∀ k, 0 ≤ R k) (hRs : Summable R)
    (hstep : ∀ k, L (k + 1) ≤ L k + R k) :
    ∃ l : ℝ, Tendsto L atTop (nhds l) := by
  let V : ℕ → ℝ := fun k ↦ L k - ∑ j ∈ Finset.range k, R j
  have hV : Antitone V := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp only [V]
    rw [Finset.sum_range_succ]
    linarith [hstep k]
  have hbdd : BddBelow (Set.range V) := by
    refine ⟨-(∑' k, R k), ?_⟩
    rintro _ ⟨k, rfl⟩
    have hsum := hRs.sum_le_tsum (Finset.range k) (fun j _ ↦ hR j)
    dsimp only [V]
    linarith [hL k]
  have hlim := (tendsto_atTop_ciInf hV hbdd).add hRs.hasSum.tendsto_sum_nat
  refine ⟨iInf V + ∑' k, R k, ?_⟩
  simpa only [V, sub_add_cancel] using hlim

/-- A summably perturbed nonincreasing energy vanishes on the entire orbit
as soon as it vanishes along one cofinal subsequence. -/
theorem energy_tendsto_zero_of_subsequence {L R : ℕ → ℝ}
    (hL : ∀ k, 0 ≤ L k) (hR : ∀ k, 0 ≤ R k) (hRs : Summable R)
    (hstep : ∀ k, L (k + 1) ≤ L k + R k)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hsub : Tendsto (L ∘ σ) atTop (nhds 0)) : Tendsto L atTop (nhds 0) := by
  obtain ⟨l, hl⟩ := energy_exists_limit hL hR hRs hstep
  have heq : l = 0 := tendsto_nhds_unique (hl.comp hσ.tendsto_atTop) hsub
  rwa [heq] at hl

end ADMM.ConvergenceProof
