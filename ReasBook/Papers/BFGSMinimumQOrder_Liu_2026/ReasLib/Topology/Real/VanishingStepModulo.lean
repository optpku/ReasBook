module

public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Sequences

public section

open Filter
open scoped Topology

namespace Real

/-- First crossings of levels separated by more than every relevant step occur at
strictly increasing indices. -/
private lemma strictMono_of_firstCrossing {p : ℝ} (hp : 0 < p) {φ a : ℕ → ℝ}
    {j : ℕ → ℕ} {K : ℕ} (hgap : ∀ i, a i - a (i + 1) = p)
    (hdrop : ∀ n, K ≤ n → φ n - φ (n + 1) < p) (hafter : ∀ i, K < j i)
    (hcross : ∀ i, φ (j i) ≤ a i) (hbefore : ∀ i k, k < j i → a i < φ k) :
    StrictMono j := by
  -- Adjacent crossing indices suffice to establish strict monotonicity.
  refine strictMono_nat_of_lt_succ ?_
  intro i
  by_contra hnot
  have hle : j (i + 1) ≤ j i := Nat.le_of_not_gt hnot
  rcases hle.lt_or_eq with hlt | heq
  · -- An earlier crossing of the lower level contradicts minimality for the upper level.
    have hupper := hbefore i (j (i + 1)) hlt
    have hlower := hcross (i + 1)
    linarith [hgap i]
  · -- A common crossing would force its preceding step to be at least one full level gap.
    have hpositive : 0 < j i := lt_of_le_of_lt (Nat.zero_le K) (hafter i)
    have hpred_lt : j i - 1 < j i := by omega
    have hKpred : K ≤ j i - 1 := Nat.le_sub_one_of_lt (hafter i)
    have hupper := hbefore i (j i - 1) hpred_lt
    have hlower := hcross (i + 1)
    have hsmall := hdrop (j i - 1) hKpred
    have hpred_succ : j i - 1 + 1 = j i := by omega
    rw [heq] at hlower
    rw [hpred_succ] at hsmall
    linarith [hgap i]

/-- The overshoot at a positive first crossing is bounded by the preceding step. -/
private lemma firstCrossingError_le_drop {φ : ℕ → ℝ} {a : ℝ} {j : ℕ} (hj : 0 < j)
    (hcross : φ j ≤ a) (hbefore : ∀ k, k < j → a < φ k) :
    0 ≤ a - φ j ∧ a - φ j ≤ φ (j - 1) - φ j := by
  -- Nonnegativity follows at the crossing, while minimality controls the overshoot.
  constructor
  · linarith
  · have hpred_lt : j - 1 < j := by omega
    exact sub_le_sub_right (hbefore (j - 1) hpred_lt).le (φ j)

/-- Overshoots at strictly increasing positive first crossings tend to zero when the
successive steps tend to zero. -/
private lemma tendsto_firstCrossingError {φ a : ℕ → ℝ} {j : ℕ → ℕ}
    (hmono : StrictMono j) (hpositive : ∀ i, 0 < j i) (hcross : ∀ i, φ (j i) ≤ a i)
    (hbefore : ∀ i k, k < j i → a i < φ k)
    (hstep : Tendsto (fun n : ℕ ↦ φ n - φ (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ a i - φ (j i)) atTop (𝓝 0) := by
  -- The predecessor indices still tend to infinity along the crossing subsequence.
  have hpred : Tendsto (fun i ↦ j i - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hmono.tendsto_atTop
  have hdrop_limit :
      Tendsto (fun i ↦ φ (j i - 1) - φ (j i - 1 + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hstep.comp hpred
  have hdrop_normalize :
      (fun i ↦ φ (j i - 1) - φ (j i - 1 + 1)) =
        fun i ↦ φ (j i - 1) - φ (j i) := by
    funext i
    rw [Nat.sub_add_cancel (hpositive i)]
  rw [hdrop_normalize] at hdrop_limit
  -- Squeezing by the preceding vanishing step closes the overshoot limit.
  refine squeeze_zero (fun i ↦ (firstCrossingError_le_drop (hpositive i)
    (hcross i) (hbefore i)).1) (fun i ↦ (firstCrossingError_le_drop (hpositive i)
      (hcross i) (hbefore i)).2) hdrop_limit

/-- Given a strictly decreasing real sequence tending to negative infinity whose successive
drops tend to zero, every target is approached along a subsequence after adding integer
multiples of any fixed positive period. -/
theorem existsSubseqAddIntMulTendsto (p : ℝ) (hp : 0 < p) {φ : ℕ → ℝ}
    (hstrict : StrictAnti φ) (hbot : Tendsto φ atTop atBot)
    (hstep : Tendsto (fun j : ℕ ↦ φ j - φ (j + 1)) atTop (𝓝 0)) (θ : ℝ) :
    ∃ j : ℕ → ℕ, ∃ m : ℕ → ℤ, StrictMono j ∧
      Tendsto (fun i ↦ φ (j i) + m i * p) atTop (𝓝 θ) := by
  -- First choose a tail on which every step is shorter than one period.
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hstep.eventually_lt_const hp)
  obtain ⟨N, hN⟩ := exists_nat_gt ((θ - φ K) / p)
  have hlevel : θ - (N : ℝ) * p < φ K := by
    have hscaled : θ - φ K < (N : ℝ) * p := (div_lt_iff₀ hp).mp hN
    linarith
  let a : ℕ → ℝ := fun i ↦ θ - ((N + i : ℕ) : ℝ) * p
  -- Tending to negative infinity supplies a crossing of every chosen level.
  have hcross_exists : ∀ i, ∃ n, φ n ≤ a i := by
    intro i
    obtain ⟨n, hn⟩ := (tendsto_atTop_atBot.mp hbot) (a i)
    exact ⟨n, hn n le_rfl⟩
  let j : ℕ → ℕ := fun i ↦ Nat.find (hcross_exists i)
  have hcross (i) : φ (j i) ≤ a i := by
    exact Nat.find_spec (hcross_exists i)
  have hbefore (i k) (hk : k < j i) : a i < φ k := by
    exact lt_of_not_ge (Nat.find_min (hcross_exists i) hk)
  -- Every selected level is already below the value at the small-step cutoff.
  have hlevel_below (i) : a i < φ K := by
    have hcast : (N : ℝ) ≤ ((N + i : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right N i
    have hmul := mul_le_mul_of_nonneg_right hcast hp.le
    dsimp only [a]
    linarith
  have hafter (i) : K < j i := by
    by_contra hnot
    have hle : j i ≤ K := Nat.le_of_not_gt hnot
    have hφ := hstrict.antitone hle
    linarith [hcross i, hlevel_below i]
  have hgap (i) : a i - a (i + 1) = p := by
    dsimp only [a]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hjmono : StrictMono j :=
    strictMono_of_firstCrossing hp hgap hK hafter hcross hbefore
  -- The first-crossing overshoot vanishes along these strictly increasing indices.
  have herror : Tendsto (fun i ↦ a i - φ (j i)) atTop (𝓝 0) :=
    tendsto_firstCrossingError hjmono
      (fun i ↦ lt_of_le_of_lt (Nat.zero_le K) (hafter i))
      hcross hbefore hstep
  let m : ℕ → ℤ := fun i ↦ ((N + i : ℕ) : ℤ)
  have hnormalize (i) : φ (j i) + m i * p = θ - (a i - φ (j i)) := by
    dsimp only [m, a]
    simp only [Int.cast_add, Int.cast_natCast, Nat.cast_add]
    ring
  -- Adding the winding number is exactly subtraction of the vanishing overshoot.
  refine ⟨j, m, hjmono, ?_⟩
  simpa only [hnormalize, sub_zero] using tendsto_const_nhds.sub herror

end Real
