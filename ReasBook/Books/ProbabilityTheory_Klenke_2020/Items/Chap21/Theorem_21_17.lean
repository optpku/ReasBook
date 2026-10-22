/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_17.ProbabilisticCore

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped NNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

/-- Helper for Theorem 21.17: if `γ > 1 / 2`, one can choose a block length `k` so that the
probability exponent `1 + k * ((1 / 2 : ℝ) - γ)` is strictly less than `-1`. -/
lemma exists_blockDecayExponent_lt_neg_one
    (γ : Set.Ioc (0 : ℝ≥0) 1) (hγ : (1 / 2 : ℝ≥0) < γ) :
    ∃ k : ℕ, 1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ)) < -1 := by
  have hγ' : (1 / 2 : ℝ) < (γ : ℝ) := by
    exact_mod_cast hγ
  have hdiff_pos : 0 < (γ : ℝ) - (1 / 2 : ℝ) := by
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ((γ : ℝ) - (1 / 2 : ℝ)))
  have hk' : 2 < (k : ℝ) * ((γ : ℝ) - (1 / 2 : ℝ)) := by
    -- Multiply the lower bound for `k` by the positive gap `γ - 1 / 2`.
    rw [div_lt_iff₀ hdiff_pos] at hk
    simpa [mul_comm, mul_left_comm, mul_assoc] using hk
  -- Rewrite the exponent in terms of the positive gap and finish by arithmetic.
  refine ⟨k, ?_⟩
  nlinarith

/-- Helper for Theorem 21.17: differentiability of a real function on `Set.Ici 0` at `t`
gives a local order-`1` Hölder estimate after restricting the variable to `NNReal`. -/
lemma holderContinuousAtOne_of_differentiableWithinAtIci
    {f : ℝ → ℝ} {t : NNReal}
    (hf : DifferentiableWithinAt ℝ f (Set.Ici (0 : ℝ)) (t : ℝ)) :
    HolderContinuousAt (⟨1, by simp⟩ : Set.Ioc (0 : ℝ≥0) 1) (fun s : NNReal ↦ f s) t := by
  let f' : ℝ := derivWithin f (Set.Ici (0 : ℝ)) (t : ℝ)
  have hf' : HasDerivWithinAt f f' (Set.Ici (0 : ℝ)) (t : ℝ) := hf.hasDerivWithinAt
  let K : ℝ := ‖f'‖ + 1
  have hK : ‖f'‖ < K := by
    -- Take a slope bound strictly larger than the derivative norm.
    dsimp [K]
    linarith
  let good : Set ℝ := {z | ‖z - (t : ℝ)‖⁻¹ * ‖f z - f t‖ < K}
  have hgood : good ∈ 𝓝[Set.Ici (0 : ℝ)] (t : ℝ) := by
    -- The derivative controls the local slope ratio along the half-line.
    simpa [good] using hf'.limsup_norm_slope_le hK
  rcases Metric.mem_nhdsWithin_iff.mp hgood with ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, Real.toNNReal K, ?_⟩
  intro y hy
  have hy' : (y : ℝ) ∈ Metric.ball (t : ℝ) ε ∩ Set.Ici (0 : ℝ) := by
    constructor
    · simpa [Metric.ball, NNReal.dist_eq] using hy
    · exact y.2
  have hratio : ‖(y : ℝ) - (t : ℝ)‖⁻¹ * ‖f y - f t‖ < K := hε hy'
  by_cases hyt : y = t
  · -- At the center point the Hölder bound is trivial.
    subst hyt
    simp
  · have hdistpos : 0 < ‖(y : ℝ) - (t : ℝ)‖ := by
      have hytreal : (y : ℝ) ≠ (t : ℝ) := by
        exact_mod_cast hyt
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hytreal)
    have hbound : ‖f y - f t‖ < ‖(y : ℝ) - (t : ℝ)‖ * K := by
      exact (inv_mul_lt_iff₀ hdistpos).mp hratio
    have hKnonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    -- Repackage the real-valued slope estimate as the project's `HolderContinuousAt` bound.
    exact le_of_lt <| by
      simpa [dist_eq_norm, NNReal.dist_eq, Real.rpow_one, Real.toNNReal_of_nonneg hKnonneg,
        norm_sub_rev, abs_sub_comm, mul_comm, mul_left_comm, mul_assoc] using hbound

/-- Helper for Theorem 21.17: the floor-chosen mesh index inside the unit window of `t` stays in
`Finset.range (n + 1)`, and every later mesh point is within `(j + 1) / (n + 1)` of `t`. -/
lemma floorBlockIndex_meshPoint_dist_le
    (t : NNReal) (n : ℕ) :
    let m : ℕ := Nat.floor (t : ℝ)
    let i : ℕ := Nat.floor (((t : ℝ) - m) * (n + 1))
    i < n + 1 ∧
      ∀ j : ℕ,
        dist ((m : NNReal) + ((i + j : ℕ) : NNReal) / (n + 1)) t ≤
          ((j + 1 : ℝ) / (n + 1)) := by
  let m : ℕ := Nat.floor (t : ℝ)
  let r : ℝ := (t : ℝ) - m
  let i : ℕ := Nat.floor (r * (n + 1))
  have hm_le : (m : ℝ) ≤ (t : ℝ) := by
    simpa [m] using Nat.floor_le t.2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact sub_nonneg.mpr hm_le
  have hr_lt_one : r < 1 := by
    have ht_lt : (t : ℝ) < m + 1 := by
      simpa [m] using (Nat.lt_floor_add_one (t : ℝ))
    dsimp [r]
    linarith
  have hi_lt : i < n + 1 := by
    have hmul_lt : r * (n + 1 : ℝ) < n + 1 := by
      have hn_pos : 0 < (n + 1 : ℝ) := by
        positivity
      nlinarith
    have hmul_nonneg : 0 ≤ r * (n + 1 : ℝ) := by
      positivity
    have hmul_lt' : r * (n + 1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      simpa using hmul_lt
    simpa [i] using
      (Nat.floor_lt hmul_nonneg).2
        hmul_lt'
  refine ⟨hi_lt, ?_⟩
  intro j
  have hn_pos : 0 < (n + 1 : ℝ) := by
    positivity
  have hi_le : (i : ℝ) ≤ r * (n + 1) := by
    simpa [i] using Nat.floor_le (mul_nonneg hr_nonneg hn_pos.le)
  have hi_succ : r * (n + 1) < i + 1 := by
    simpa [i] using (Nat.lt_floor_add_one (r * (n + 1)))
  have hbase_le : (i : ℝ) / (n + 1) ≤ r := by
    have hden_ne : (n + 1 : ℝ) ≠ 0 := by
      linarith
    field_simp [hden_ne]
    linarith
  have hbase_lt :
      r < (i + 1 : ℝ) / (n + 1) := by
    have hden_ne : (n + 1 : ℝ) ≠ 0 := by
      linarith
    field_simp [hden_ne]
    linarith
  have hbase_lt' :
      r < (i : ℝ) / (n + 1) + (1 : ℝ) / (n + 1) := by
    simpa [add_div, add_comm, add_left_comm, add_assoc] using hbase_lt
  have hbase_abs :
      |(i : ℝ) / (n + 1) - r| ≤ (1 : ℝ) / (n + 1) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hbase_le)]
    linarith
  have hcast_t : (t : ℝ) = m + r := by
    dsimp [r]
    ring
  have hsub :
      (((m : NNReal) + ((i + j : ℕ) : NNReal) / (n + 1) : NNReal) : ℝ) - t =
        (((i + j : ℕ) : ℝ) / (n + 1) - r) := by
    change (m : ℝ) + (((i + j : ℕ) : ℝ) / (n + 1)) - t =
      (((i + j : ℕ) : ℝ) / (n + 1) - r)
    rw [hcast_t]
    ring
  have hdist_eq :
      dist ((m : NNReal) + ((i + j : ℕ) : NNReal) / (n + 1)) t =
        |((i + j : ℕ) : ℝ) / (n + 1) - r| := by
    rw [NNReal.dist_eq, hsub]
  have hj_abs :
      |(j : ℝ) / (n + 1)| = (j : ℝ) / (n + 1) := by
    rw [abs_of_nonneg]
    positivity
  -- Proof comment: the fractional part of `t` is within one mesh step of the floor-selected start
  -- index, and shifting by `j` adds at most `j / (n + 1)` to that error.
  rw [hdist_eq]
  calc
    |((i + j : ℕ) : ℝ) / (n + 1) - r|
      = |((i : ℝ) / (n + 1) - r) + (j : ℝ) / (n + 1)| := by
          congr 1
          rw [Nat.cast_add, add_div]
          ring_nf
    _ ≤ |(i : ℝ) / (n + 1) - r| + |(j : ℝ) / (n + 1)| := by
          simpa using abs_add_le ((i : ℝ) / (n + 1) - r) ((j : ℝ) / (n + 1))
    _ = |(i : ℝ) / (n + 1) - r| + (j : ℝ) / (n + 1) := by rw [hj_abs]
    _ ≤ (1 : ℝ) / (n + 1) + (j : ℝ) / (n + 1) := by
          gcongr
    _ = ((j : ℝ) + 1) / (n + 1) := by
          rw [← add_div]
          ring_nf

/-- Helper for Theorem 21.17: the mesh radius from the source proof factors into a `k`-part and
an `(n + 1)⁻¹`-part after taking the `γ`th power. -/
lemma meshRadius_rpow_eq
    (γ : Set.Ioc (0 : ℝ≥0) 1) (k n : ℕ) :
    (((k + 1 : ℝ) / (n + 1)) ^ (γ : ℝ)) =
      (k + 1 : ℝ) ^ (γ : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) := by
  -- Proof comment: normalize the single Hölder radius once so all later bounds use the same
  -- `((n + 1)⁻¹)^γ` threshold appearing in `smallIncrementBlockEvent`.
  have hleft_nonneg : 0 ≤ (k + 1 : ℝ) := by positivity
  have hright_nonneg : 0 ≤ ((n + 1 : ℝ)⁻¹) := by positivity
  rw [div_eq_mul_inv, Real.mul_rpow hleft_nonneg hright_nonneg]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.17: a local `γ`-Hölder bound at `t` forces eventual membership in the
countable family of small-increment block events on the unit window starting at `Nat.floor t`. -/
lemma holderContinuousAt_eventually_mem_smallIncrementBlockEvent
    {B : NNReal → Ω → ℝ} {ω : Ω} {γ : Set.Ioc (0 : ℝ≥0) 1} {k : ℕ} {t : NNReal}
    (ht : HolderContinuousAt γ (fun s : NNReal ↦ B s ω) t) :
    ∃ N n₀ : ℕ, ∀ ⦃n : ℕ⦄, n₀ ≤ n →
      ω ∈ smallIncrementBlockEvent B γ k N (Nat.floor (t : ℝ)) n := by
  rcases ht.exists_dist_le_mul_rpow with ⟨ε, hεpos, C, hC⟩
  let N : ℕ := Nat.ceil (2 * (C : ℝ) * (k + 1 : ℝ) ^ (γ : ℝ))
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((k + 1 : ℝ) / ε)
  refine ⟨N, n₀, ?_⟩
  intro n hn
  let m : ℕ := Nat.floor (t : ℝ)
  let i : ℕ := Nat.floor (((t : ℝ) - m) * (n + 1))
  let radius : ℝ := (k + 1 : ℝ) / (n + 1)
  have hn_pos : 0 < (n + 1 : ℝ) := by
    positivity
  have hγ_nonneg : 0 ≤ (γ : ℝ) := by
    exact_mod_cast γ.2.1.le
  have hRadius_lt :
      radius < ε := by
    have hn₀_lt : (n₀ : ℝ) < (n + 1 : ℝ) := by
      exact_mod_cast Nat.lt_succ_of_le hn
    have hquot_lt : ((k + 1 : ℝ) / ε) < (n + 1 : ℝ) := lt_trans hn₀ hn₀_lt
    have hmul_lt : (k + 1 : ℝ) < ε * (n + 1 : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hεpos).1 hquot_lt
    exact (div_lt_iff₀ hn_pos).2 <| by
      simpa [radius, mul_comm, mul_left_comm, mul_assoc] using hmul_lt
  have hgeom := floorBlockIndex_meshPoint_dist_le t n
  have hi_lt : i < n + 1 := by
    simpa [m, i] using hgeom.1
  have hdist (j : ℕ) :
      dist ((m : NNReal) + ((i + j : ℕ) : NNReal) / (n + 1)) t ≤ ((j + 1 : ℝ) / (n + 1)) := by
    simpa [m, i] using hgeom.2 j
  have hi_mem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr hi_lt
  -- Proof comment: use the floor-selected start index `i` as the union witness in the block event.
  rw [smallIncrementBlockEvent]
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  refine Set.mem_iUnion.2 ⟨hi_mem, ?_⟩
  rw [smallIncrementBlockSlice]
  refine Set.mem_iInter.2 ?_
  intro l
  refine Set.mem_iInter.2 ?_
  intro hl
  let x₀ : NNReal := (m : NNReal) + ((i + l : ℕ) : NNReal) / (n + 1)
  let x₁ : NNReal := (m : NNReal) + ((i + l + 1 : ℕ) : NNReal) / (n + 1)
  have hl_lt : l < k := Finset.mem_range.mp hl
  have hstep₀_le : ((l + 1 : ℕ) : ℝ) / (n + 1) ≤ radius := by
    have hnum : ((l + 1 : ℕ) : ℝ) ≤ (k + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hl_lt)
    have hden_ne : (n + 1 : ℝ) ≠ 0 := by
      linarith
    dsimp [radius]
    field_simp [hden_ne]
    linarith
  have hstep₁_le : ((l + 2 : ℕ) : ℝ) / (n + 1) ≤ radius := by
    have hnum : ((l + 2 : ℕ) : ℝ) ≤ (k + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.succ_le_of_lt hl_lt)
    have hden_ne : (n + 1 : ℝ) ≠ 0 := by
      linarith
    dsimp [radius]
    field_simp [hden_ne]
    linarith
  have hx₀_le : dist x₀ t ≤ radius := by
    exact le_trans (by simpa [x₀] using hdist l) hstep₀_le
  have hx₁_le : dist x₁ t ≤ radius := by
    have hdist_succ' :
        dist x₁ t ≤ ((l : ℝ) + (1 + 1)) / (n + 1) := by
      simpa [x₁, add_assoc, Nat.cast_add, add_comm, add_left_comm] using hdist (l + 1)
    have hdist_succ :
        dist x₁ t ≤ ((l + 2 : ℕ) : ℝ) / (n + 1) := by
      have hrhs :
          ((l : ℝ) + (1 + 1)) / (n + 1) = ((l + 2 : ℕ) : ℝ) / (n + 1) := by
        norm_num [Nat.cast_add, add_assoc]
      exact hrhs.symm ▸ hdist_succ'
    exact le_trans hdist_succ hstep₁_le
  have hx₀_lt : dist x₀ t < ε := lt_of_le_of_lt hx₀_le hRadius_lt
  have hx₁_lt : dist x₁ t < ε := lt_of_le_of_lt hx₁_le hRadius_lt
  have hpow₀ : dist t x₀ ^ (γ : ℝ) ≤ radius ^ (γ : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) (by simpa [dist_comm] using hx₀_le) hγ_nonneg
  have hpow₁ : dist t x₁ ^ (γ : ℝ) ≤ radius ^ (γ : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) (by simpa [dist_comm] using hx₁_le) hγ_nonneg
  have hholder₀ :
      dist (B x₀ ω) (B t ω) ≤ (C : ℝ) * radius ^ (γ : ℝ) := by
    have hlocal : dist (B x₀ ω) (B t ω) ≤ (C : ℝ) * dist t x₀ ^ (γ : ℝ) := by
      simpa [x₀, dist_comm] using hC x₀ hx₀_lt
    exact le_trans hlocal (mul_le_mul_of_nonneg_left hpow₀ C.2)
  have hholder₁ :
      dist (B x₁ ω) (B t ω) ≤ (C : ℝ) * radius ^ (γ : ℝ) := by
    have hlocal : dist (B x₁ ω) (B t ω) ≤ (C : ℝ) * dist t x₁ ^ (γ : ℝ) := by
      simpa [x₁, dist_comm] using hC x₁ hx₁_lt
    exact le_trans hlocal (mul_le_mul_of_nonneg_left hpow₁ C.2)
  have hN_le : 2 * (C : ℝ) * (k + 1 : ℝ) ^ (γ : ℝ) ≤ N := by
    exact Nat.le_ceil _
  have hmesh_nonneg : 0 ≤ ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) := by
    exact Real.rpow_nonneg (inv_nonneg.mpr (by positivity)) _
  -- Proof comment: each increment is controlled by two Hölder estimates through `t`, and the
  -- normalized radius from `meshRadius_rpow_eq` matches the event threshold exactly.
  simpa [Set.mem_setOf_eq, x₀, x₁] using
    (calc
      |B x₁ ω - B x₀ ω|
        = dist (B x₁ ω) (B x₀ ω) := by rw [Real.dist_eq]
      _ ≤ dist (B x₁ ω) (B t ω) + dist (B x₀ ω) (B t ω) := by
            simpa [dist_comm] using dist_triangle_right (B x₁ ω) (B x₀ ω) (B t ω)
      _ ≤ (C : ℝ) * radius ^ (γ : ℝ) + (C : ℝ) * radius ^ (γ : ℝ) := add_le_add hholder₁ hholder₀
      _ = (2 * (C : ℝ)) * radius ^ (γ : ℝ) := by ring
      _ = (2 * (C : ℝ) * (k + 1 : ℝ) ^ (γ : ℝ)) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) := by
            rw [meshRadius_rpow_eq γ k n]
            ring
      _ ≤ (N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) := by
            exact mul_le_mul_of_nonneg_right hN_le hmesh_nonneg)

-- Proof sketch: follow the Paley--Wiener--Zygmund dyadic-block argument from the text. For a
-- fixed exponent `γ > 1 / 2`, estimate the probability that `k` consecutive increments of size
-- `1 / n` are all `O(n^{-γ})`, use independence and the Gaussian scaling law to obtain a summable
-- bound, and conclude by Borel--Cantelli that almost no sample path is `γ`-Hölder at any point.
/-- Theorem 21.17: for every exponent `γ ∈ (0,1]` with `γ > 1 / 2`, almost every Brownian sample
path fails to be Hölder-continuous of order `γ` at every time `t ≥ 0`. -/
theorem ae_forall_not_holderContinuousAt_path
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (γ : Set.Ioc (0 : ℝ≥0) 1) (hγ : (1 / 2 : ℝ≥0) < γ) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, ¬ HolderContinuousAt γ (fun s : NNReal ↦ B s ω) t := by
  -- Route correction: keep the final contradiction proof here, but import the probabilistic and
  -- deterministic helper chains so the target file only assembles the two stable endpoints.
  obtain ⟨k, hk⟩ := exists_blockDecayExponent_lt_neg_one γ hγ
  -- Proof comment: after the summability lemma and the pathwise Hölder-to-block-event lemma are
  -- in place, apply Borel-Cantelli to every fixed `(m, N)` and then contradict the eventual
  -- non-membership event with the deterministic eventual membership forced by any Hölder point.
  have hAvoid :
      ∀ᵐ ω ∂μ, ∀ m N : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
        ω ∉ smallIncrementBlockEvent B γ k N m n :=
    ae_eventually_notMem_smallIncrementBlockEvent hB γ hk
  filter_upwards [hAvoid] with ω hω
  intro t ht
  rcases
      holderContinuousAt_eventually_mem_smallIncrementBlockEvent
        (B := B) (ω := ω) (γ := γ) (k := k) (t := t) ht with
    ⟨N, n₀, hmem⟩
  have hnot :
      ∀ᶠ n : ℕ in Filter.atTop,
        ω ∉ smallIncrementBlockEvent B γ k N (Nat.floor (t : ℝ)) n :=
    hω (Nat.floor (t : ℝ)) N
  have hmem_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        ω ∈ smallIncrementBlockEvent B γ k N (Nat.floor (t : ℝ)) n := by
    exact Filter.eventually_atTop.2 ⟨n₀, fun n hn ↦ hmem hn⟩
  rcases Filter.eventually_atTop.1 (hnot.and hmem_eventually) with ⟨n, hn⟩
  exact (hn n le_rfl).1 (hn n le_rfl).2

-- Proof sketch: apply `ae_forall_not_holderContinuousAt_path` with any exponent
-- `γ ∈ (1 / 2, 1]`; differentiability of a path at a point on `[0, ∞)` would imply a local
-- Lipschitz estimate there, hence Hölder continuity of every order at most `1`, contradicting the
-- previous theorem.
/-- Brownian sample paths are almost surely nowhere differentiable on the half-line `[0, ∞)`. -/
theorem ae_nowhere_differentiable_path
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      ¬ DifferentiableWithinAt ℝ (fun s : ℝ ↦ B (Real.toNNReal s) ω) (Set.Ici (0 : ℝ))
        (t : ℝ) := by
  let γOne : Set.Ioc (0 : ℝ≥0) 1 := ⟨1, by simp⟩
  have hHolder :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, ¬ HolderContinuousAt γOne (fun s : NNReal ↦ B s ω) t :=
    hB.ae_forall_not_holderContinuousAt_path γOne (by norm_num)
  filter_upwards [hHolder] with ω hω t
  intro hdiff
  -- Proof comment: differentiability on `Set.Ici 0` yields a local Lipschitz bound, hence
  -- `1`-Hölder continuity at the same point.
  have hholderAt :
      HolderContinuousAt γOne (fun s : NNReal ↦ B s ω) t := by
    simpa using
      holderContinuousAtOne_of_differentiableWithinAtIci
        (f := fun s : ℝ ↦ B (Real.toNNReal s) ω) (t := t) hdiff
  exact hω t hholderAt

end IsBrownianMotion

end ProbabilityTheory
