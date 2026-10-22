/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

section

variable {X : Type u} [PseudoMetricSpace X] [CompleteSpace X]
variable {C : Set X} {xₙ : ℕ → X} {κ : ℝ}

namespace FejerMonotone

omit [CompleteSpace X] in
/-- Helper for Theorem 5.12: a one-step contraction of `Metric.infDist` propagates to the explicit
geometric estimate at every index. -/
lemma infDist_le_geometric_of_infDist_contracts
    (hκ_nonneg : 0 ≤ κ)
    (hdist : ∀ n, Metric.infDist (xₙ (n + 1)) C ≤ κ * Metric.infDist (xₙ n) C) :
    ∀ n, Metric.infDist (xₙ n) C ≤ κ ^ n * Metric.infDist (xₙ 0) C := by
  intro n
  induction n with
  | zero =>
      -- At the initial index the geometric factor is `1`, so the claim is immediate.
      simp
  | succ n ihn =>
      -- Multiply the previous-step estimate by `κ` and use the contractive hypothesis.
      calc
        Metric.infDist (xₙ (n + 1)) C ≤ κ * Metric.infDist (xₙ n) C := hdist n
        _ ≤ κ * (κ ^ n * Metric.infDist (xₙ 0) C) := by
          gcongr
        _ = κ ^ (n + 1) * Metric.infDist (xₙ 0) C := by
          rw [pow_succ']
          ring

omit [CompleteSpace X] in
/-- Helper for Theorem 5.12: geometric decay with ratio `κ ∈ [0, 1)` forces the distance-to-`C`
sequence to converge to `0`. -/
lemma infDist_tendsto_zero_of_infDist_contracts
    (hκ_nonneg : 0 ≤ κ) (hκ_lt_one : κ < 1)
    (hdist : ∀ n, Metric.infDist (xₙ (n + 1)) C ≤ κ * Metric.infDist (xₙ n) C) :
    Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 0) := by
  have hgeom := infDist_le_geometric_of_infDist_contracts hκ_nonneg hdist
  have hgeom_tendsto :
      Tendsto (fun n ↦ κ ^ n * Metric.infDist (xₙ 0) C) atTop (𝓝 0) := by
    -- The geometric majorant tends to `0` because `κ ^ n → 0`.
    simpa [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hκ_nonneg hκ_lt_one).mul_const
        (Metric.infDist (xₙ 0) C)
  -- Squeeze the nonnegative distance sequence between `0` and its geometric majorant.
  refine squeeze_zero (fun n ↦ Metric.infDist_nonneg) (fun n ↦ hgeom n) hgeom_tendsto

omit [CompleteSpace X] in
/-- Helper for Theorem 5.12: passing Proposition 5.4(v) to the limit bounds the distance to the
strong limit by twice the distance to `C`. -/
lemma dist_le_two_mul_infDist_of_tendsto
    (hxₙ : FejerMonotone C xₙ) (hC_nonempty : C.Nonempty) {x : X}
    (hxlim : Tendsto xₙ atTop (𝓝 x)) :
    ∀ n, dist (xₙ n) x ≤ 2 * Metric.infDist (xₙ n) C := by
  intro n
  have htail : Tendsto (fun m ↦ xₙ (n + m)) atTop (𝓝 x) := by
    -- Convergence of the full sequence implies convergence of every tail.
    simpa [Nat.add_comm] using hxlim.comp (tendsto_add_atTop_nat n)
  have hdist_tendsto :
      Tendsto (fun m ↦ dist (xₙ n) (xₙ (n + m))) atTop (𝓝 (dist (xₙ n) x)) := by
    -- Continuity of the distance function transports the tail convergence.
    exact ((continuous_const.dist continuous_id).tendsto x).comp htail
  have hbound :
      ∀ᶠ m in atTop, dist (xₙ n) (xₙ (n + m)) ∈ Set.Iic (2 * Metric.infDist (xₙ n) C) := by
    refine Filter.Eventually.of_forall (fun m ↦ ?_)
    simpa [Set.mem_Iic, dist_comm] using hxₙ.dist_le_two_mul_infDist hC_nonempty m n
  -- The upper bound is closed, so it survives under the limit `m → ∞`.
  simpa [Set.mem_Iic] using isClosed_Iic.mem_of_tendsto hdist_tendsto hbound

-- Proof sketch: Theorem 5.11 gives strong convergence of `xₙ` to some `x ∈ C` from the Fejér
-- monotonicity hypothesis together with the geometric decay of `Metric.infDist (xₙ n) C`. Then
-- apply `FejerMonotone.dist_le_two_mul_infDist` with `m → ∞` to obtain
-- `dist (xₙ n) x ≤ 2 * Metric.infDist (xₙ n) C`, and combine this with the hypothesis
-- `Metric.infDist (xₙ (n + 1)) C ≤ κ * Metric.infDist (xₙ n) C` to derive the bound
-- `dist (xₙ n) x ≤ 2 * κ ^ n * Metric.infDist (xₙ 0) C` for every `n`.
/-- Theorem 5.12: if `C` is a nonempty closed subset of a complete pseudometric space, `xₙ`
is Fejér monotone with respect to `C`, and the distances `Metric.infDist (xₙ n) C` decay
geometrically with ratio `κ` satisfying `0 ≤ κ < 1`, then `xₙ` converges strongly to some `x ∈ C`;
more precisely, for every `n`, one has
`dist (xₙ n) x ≤ 2 * κ ^ n * Metric.infDist (xₙ 0) C`. -/
theorem exists_tendsto_with_dist_le_of_infDist_contracts
    (hxₙ : FejerMonotone C xₙ) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hκ_nonneg : 0 ≤ κ) (hκ_lt_one : κ < 1)
    (hdist : ∀ n, Metric.infDist (xₙ (n + 1)) C ≤ κ * Metric.infDist (xₙ n) C) :
    ∃ x ∈ C,
      Tendsto xₙ atTop (𝓝 x) ∧
      ∀ n, dist (xₙ n) x ≤ 2 * κ ^ n * Metric.infDist (xₙ 0) C := by
  have hgeom := infDist_le_geometric_of_infDist_contracts hκ_nonneg hdist
  have hzero :
      Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 0) :=
    infDist_tendsto_zero_of_infDist_contracts hκ_nonneg hκ_lt_one hdist
  have hzero_ereal :
      Tendsto (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop (𝓝 (0 : EReal)) := by
    -- Convert the real convergence of the distance sequence to the `EReal` liminf statement
    -- required by Theorem 5.11.
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp hzero
  have hliminf :
      liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop = 0 := by
    simpa using hzero_ereal.liminf_eq
  have htfae :=
    strongConvergent_seqClusterPt_liminf_infDist_eq_zero_tfae hxₙ hC_nonempty hC_closed
  rcases (List.TFAE.out htfae 2 0).mp hliminf with ⟨x, hxC, hxlim⟩
  refine ⟨x, hxC, hxlim, ?_⟩
  intro n
  have hlimit_bound :
      dist (xₙ n) x ≤ 2 * Metric.infDist (xₙ n) C :=
    dist_le_two_mul_infDist_of_tendsto hxₙ hC_nonempty hxlim n
  -- First compare `dist (xₙ n) x` to `Metric.infDist (xₙ n) C`, then insert the geometric decay.
  calc
    dist (xₙ n) x ≤ 2 * Metric.infDist (xₙ n) C := hlimit_bound
    _ ≤ 2 * (κ ^ n * Metric.infDist (xₙ 0) C) := by
      gcongr
      exact hgeom n
    _ = 2 * κ ^ n * Metric.infDist (xₙ 0) C := by ring

end FejerMonotone

end
