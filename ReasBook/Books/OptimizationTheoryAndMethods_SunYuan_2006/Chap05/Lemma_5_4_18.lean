/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Order.MonotoneConvergence

open Filter

-- Semantic recall: `lean_leansearch` did not expose a canonical ready-made mathlib theorem for
-- this perturbed scalar recurrence, so the source-faithful convergence statement is recorded
-- directly on real sequences indexed by `ℕ`.

/-- Chapter05 Lemma 5.4.18: if nonnegative real sequences `φ` and `δ` satisfy
`φ (k + 1) ≤ (1 + δ k) * φ k + δ k` for every `k`, and `δ` is summable, then `φ` converges.
This is the standard `ℕ`-indexed reindexing of the textbook sequence starting at `k = 1`. -/
theorem exists_tendsto_of_nonneg_recurrence_of_summable
    {φ δ : ℕ → ℝ}
    (hφ_nonneg : ∀ k, 0 ≤ φ k)
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hrec : ∀ k, φ (k + 1) ≤ (1 + δ k) * φ k + δ k)
    (hδ_summable : Summable δ) :
    ∃ l : ℝ, Tendsto φ atTop (nhds l) := by
  let P : ℕ → ℝ := fun k ↦ ∏ i ∈ Finset.range k, (1 + δ i)
  let ψ : ℕ → ℝ := fun k ↦ (φ k + 1) / P k
  have hP_pos : ∀ k, 0 < P k := by
    intro k
    dsimp [P]
    refine Finset.prod_pos fun i _ ↦ ?_
    linarith [hδ_nonneg i]
  have hψ_step : ∀ k, ψ (k + 1) ≤ ψ k := by
    intro k
    have hPk_pos : 0 < P k := hP_pos k
    have hδk_pos : 0 < 1 + δ k := by
      linarith [hδ_nonneg k]
    have hdenom_pos : 0 < P k * (1 + δ k) := mul_pos hPk_pos hδk_pos
    dsimp [ψ]
    rw [show P (k + 1) = P k * (1 + δ k) by
      simp [P, Finset.prod_range_succ]]
    rw [div_le_iff₀ hdenom_pos]
    have hψ_mul : ψ k * P k = φ k + 1 := by
      dsimp [ψ]
      field_simp [hPk_pos.ne']
    calc
      φ (k + 1) + 1 ≤ (1 + δ k) * φ k + δ k + 1 := by
        linarith [hrec k]
      _ = (1 + δ k) * (φ k + 1) := by
        ring
      _ = (1 + δ k) * (ψ k * P k) := by
        rw [hψ_mul]
      _ = ψ k * (P k * (1 + δ k)) := by
        ring
  have hψ_anti : Antitone ψ := antitone_nat_of_succ_le hψ_step
  have hψ_nonneg : ∀ k, 0 ≤ ψ k := by
    intro k
    have hPk_pos : 0 < P k := hP_pos k
    dsimp [ψ]
    exact div_nonneg (by linarith [hφ_nonneg k]) hPk_pos.le
  have hψ_bddBelow : BddBelow (Set.range ψ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hψ_nonneg k
  have hψ_tendsto : Tendsto ψ atTop (nhds (⨅ k, ψ k)) :=
    tendsto_atTop_ciInf hψ_anti hψ_bddBelow
  have hP_tendsto : Tendsto P atTop (nhds (∏' i, (1 + δ i))) := by
    have hmult : Multipliable (fun i ↦ 1 + δ i) :=
      Real.multipliable_one_add_of_summable hδ_summable
    simpa [P] using (hmult.hasProd_iff_tendsto_nat).mp hmult.hasProd
  have hφ_add_one :
      Tendsto (fun k ↦ φ k + 1) atTop (nhds ((⨅ k, ψ k) * ∏' i, (1 + δ i))) := by
    have hmul :
        Tendsto (fun k ↦ ψ k * P k) atTop (nhds ((⨅ k, ψ k) * ∏' i, (1 + δ i))) :=
      hψ_tendsto.mul hP_tendsto
    refine hmul.congr' <| Filter.Eventually.of_forall fun k ↦ ?_
    have hPk_pos : 0 < P k := hP_pos k
    dsimp [ψ]
    field_simp [hPk_pos.ne']
  refine ⟨((⨅ k, ψ k) * ∏' i, (1 + δ i)) - 1, ?_⟩
  simpa using hφ_add_one.sub_const 1
