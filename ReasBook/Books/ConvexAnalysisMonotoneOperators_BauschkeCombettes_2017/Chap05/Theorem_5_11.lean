/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

section

variable {X : Type u} [PseudoMetricSpace X] [CompleteSpace X]
variable {C : Set X} {xₙ : ℕ → X}

namespace FejerMonotone

/-- Helper for Theorem 5.11: a strong sequential cluster point in `C` forces the `EReal` liminf of
the distance-to-`C` sequence to vanish. -/
lemma strong_cluster_point_implies_liminf_infDist_eq_zero
    {z : X} (hz : z ∈ C) (hcluster : IsSequentialClusterPt xₙ z) :
    liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop = 0 := by
  rcases hcluster.exists_subseq_tendsto with ⟨φ, hφmono, hφtendsto⟩
  -- The subsequence converging to `z` makes its pointwise distances to `C` converge to `0`.
  have hdist_tendsto : Tendsto (fun n ↦ dist (xₙ (φ n)) z) atTop (𝓝 0) := by
    simpa [Function.comp] using (tendsto_iff_dist_tendsto_zero.1 hφtendsto)
  have hinf_tendsto : Tendsto (fun n ↦ Metric.infDist (xₙ (φ n)) C) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ Metric.infDist_nonneg) ?_ hdist_tendsto
    intro n
    exact Metric.infDist_le_dist_of_mem hz
  have hsub_liminf :
      liminf (fun n ↦ (Metric.infDist (xₙ (φ n)) C : EReal)) atTop = 0 := by
    have hsub_ereal :
        Tendsto (fun n ↦ (Metric.infDist (xₙ (φ n)) C : EReal)) atTop (𝓝 (0 : EReal)) := by
      exact (continuous_coe_real_ereal.tendsto 0).comp hinf_tendsto
    simpa using hsub_ereal.liminf_eq
  have hnonneg :
      (0 : EReal) ≤ liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop := by
    exact
      Filter.le_liminf_of_le (f := atTop)
        (u := fun n ↦ (Metric.infDist (xₙ n) C : EReal)) (a := (0 : EReal))
        (hf := by isBoundedDefault)
        (h := Filter.Eventually.of_forall fun n ↦ by
          simpa using
            (show (0 : ℝ) ≤ Metric.infDist (xₙ n) C from Metric.infDist_nonneg))
  have hle_subseq :
      liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop ≤
        liminf (fun n ↦ (Metric.infDist (xₙ (φ n)) C : EReal)) atTop := by
    have hmap :
        liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop ≤
          liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) (Filter.map φ atTop) := by
      exact Filter.liminf_le_liminf_of_le hφmono.tendsto_atTop
    simpa [Filter.liminf_comp, Function.comp] using hmap
  -- The full liminf is squeezed between the nonnegativity lower bound and the zero subsequence
  -- limit.
  refine le_antisymm ?_ hnonneg
  simpa [hsub_liminf] using hle_subseq

/-- Helper for Theorem 5.11: Proposition 5.4 upgrades vanishing `EReal` liminf of the distance
sequence to actual convergence `Metric.infDist (xₙ n) C → 0`. -/
lemma tendsto_zero_of_antitone_liminf_infDist_eq_zero
    (hxₙ : FejerMonotone C xₙ)
    (hliminf : liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop = 0) :
    Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 0) := by
  rcases hxₙ.infDist_tendsto with ⟨l, hl⟩
  -- Proposition 5.4 already gives convergence of the real distance sequence; the liminf
  -- hypothesis identifies its limit as `0`.
  have hereal :
      Tendsto (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop (𝓝 (l : EReal)) := by
    exact (continuous_coe_real_ereal.tendsto l).comp hl
  have hliminf_real :
      liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop = (l : EReal) := by
    simpa using hereal.liminf_eq
  have hl_zero_ereal : (l : EReal) = 0 := by
    simpa [hliminf_real] using hliminf
  have hl_zero : l = 0 := by
    exact_mod_cast hl_zero_ereal
  simpa [hl_zero] using hl

/-- Helper for Theorem 5.11: if the distances to `C` tend to `0`, the Fejér estimate from
Proposition 5.4 forces the sequence itself to be Cauchy. -/
lemma cauchySeq_of_infDist_tendsto_zero
    (hxₙ : FejerMonotone C xₙ) (hC_nonempty : C.Nonempty)
    (hzero : Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 0)) :
    CauchySeq xₙ := by
  have htail :
      ∀ n m : ℕ, n ≤ m → dist (xₙ n) (xₙ m) ≤ 2 * Metric.infDist (xₙ n) C := by
    intro n m hnm
    rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
    -- Rewrite the tail index as `n + k` so Proposition 5.4 applies directly.
    calc
      dist (xₙ n) (xₙ (n + k)) = dist (xₙ (n + k)) (xₙ n) := dist_comm _ _
      _ ≤ 2 * Metric.infDist (xₙ n) C := hxₙ.dist_le_two_mul_infDist hC_nonempty k n
  have htwo_zero : Tendsto (fun n ↦ 2 * Metric.infDist (xₙ n) C) atTop (𝓝 0) := by
    -- The Cauchy bound uses the doubled distance sequence.
    simpa [two_mul] using hzero.add hzero
  exact cauchySeq_of_le_tendsto_0' (fun n ↦ 2 * Metric.infDist (xₙ n) C) htail htwo_zero

/-- Helper for Theorem 5.11: if a sequence converges and its distances to a nonempty closed set
vanish, then its limit belongs to that set. -/
lemma limit_mem_of_closed_of_infDist_tendsto_zero
    {z : X} (hz : Tendsto xₙ atTop (𝓝 z))
    (hzero : Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 0))
    (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    z ∈ C := by
  -- Continuity of `Metric.infDist` transports the sequence limit to the limit distance.
  have hz_infDist :
      Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 (Metric.infDist z C)) := by
    exact (Metric.continuous_infDist_pt C).tendsto z |>.comp hz
  have hz_zero : Metric.infDist z C = 0 := tendsto_nhds_unique hz_infDist hzero
  exact (hC_closed.mem_iff_infDist_zero hC_nonempty).2 hz_zero

-- Proof sketch: `(i) → (ii)` is immediate. For `(ii) → (iii)`, a strongly convergent subsequence
-- to some `z ∈ C` forces the corresponding distance subsequence `n ↦ Metric.infDist (xₙ n) C` to
-- converge to `0`, so the `EReal` liminf is `0`. For `(iii) → (i)`, Proposition 5.4 gives that
-- `n ↦ Metric.infDist (xₙ n) C` is decreasing and convergent, so the liminf hypothesis upgrades to
-- `Metric.infDist (xₙ n) C → 0`; then `FejerMonotone.dist_le_two_mul_infDist` makes `(xₙ n)`
-- Cauchy, completeness yields a limit `z`, and closedness of `C` puts `z` back in `C`.
/-- Theorem 5.11: for a Fejér-monotone sequence with respect to a nonempty closed set `C` in a
complete pseudometric space, strong convergence to a point of `C`, existence of a strong sequential
cluster point in `C`, and vanishing lower limit of the distance sequence
`n ↦ Metric.infDist (xₙ n) C` are equivalent. -/
theorem strongConvergent_seqClusterPt_liminf_infDist_eq_zero_tfae
    (hxₙ : FejerMonotone C xₙ) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) :
    List.TFAE [
      ∃ z ∈ C, Tendsto xₙ atTop (𝓝 z),
      ∃ z ∈ C, IsSequentialClusterPt xₙ z,
      liminf (fun n ↦ (Metric.infDist (xₙ n) C : EReal)) atTop = 0
    ] := by
  -- Route correction: this theorem lives in a complete pseudometric space, so the closing route is
  -- Proposition 5.4 plus completeness and closedness, not the Hilbert projection theorem.
  tfae_have 1 → 2 := by
    rintro ⟨z, hzC, hz⟩
    -- A convergent sequence has its limit as a sequential cluster point via the identity
    -- subsequence.
    exact ⟨z, hzC, ⟨fun n ↦ n, strictMono_id, by simpa using hz⟩⟩
  tfae_have 2 → 3 := by
    rintro ⟨z, hzC, hcluster⟩
    -- The cluster-point subsequence forces the distance liminf to be `0`.
    exact strong_cluster_point_implies_liminf_infDist_eq_zero hzC hcluster
  tfae_have 3 → 1 := by
    intro hliminf
    -- First upgrade the liminf information to pointwise distance convergence.
    have hinf_zero :
        Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 0) :=
      tendsto_zero_of_antitone_liminf_infDist_eq_zero hxₙ hliminf
    -- Then the Fejér two-point estimate gives a Cauchy sequence.
    have hcauchy : CauchySeq xₙ :=
      cauchySeq_of_infDist_tendsto_zero hxₙ hC_nonempty hinf_zero
    rcases cauchySeq_tendsto_of_complete hcauchy with ⟨z, hz⟩
    -- Vanishing distance to the closed set identifies the limit point as belonging to `C`.
    have hzC : z ∈ C :=
      limit_mem_of_closed_of_infDist_tendsto_zero hz hinf_zero hC_closed hC_nonempty
    exact ⟨z, hzC, hz⟩
  tfae_finish

end FejerMonotone

end
