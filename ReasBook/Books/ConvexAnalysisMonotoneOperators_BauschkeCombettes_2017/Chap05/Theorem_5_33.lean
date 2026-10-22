/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Lemma_5_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology BigOperators

universe u

section

variable {H : Type u} [SeminormedAddCommGroup H]
variable {C : Set H} {x : ℕ → H}

/-- A sequence is quasi-Fejér monotone with respect to `C` if its squared distance to each point
of `C` is controlled by a summable nonnegative error sequence. -/
def UniformQuasiFejerMonotone (C : Set H) (x : ℕ → H) : Prop :=
  ∃ ε : ℕ → ℝ,
    Summable ε ∧
      (∀ n : ℕ, 0 ≤ ε n) ∧
        ∀ c ∈ C, ∀ n : ℕ, ‖x (n + 1) - c‖ ^ 2 ≤ ‖x n - c‖ ^ 2 + ε n

-- Proof sketch: unfold `UniformQuasiFejerMonotone` and retain the summable nonnegative error sequence
-- together with its one-step squared-distance estimate.
/-- A quasi-Fejér monotone sequence admits a summable nonnegative error sequence controlling each
one-step squared-distance increment. -/
theorem UniformQuasiFejerMonotone.exists_summable_sq_error
    (h : UniformQuasiFejerMonotone C x) :
    ∃ ε : ℕ → ℝ,
      Summable ε ∧
        (∀ n : ℕ, 0 ≤ ε n) ∧
          ∀ c ∈ C, ∀ n : ℕ, ‖x (n + 1) - c‖ ^ 2 ≤ ‖x n - c‖ ^ 2 + ε n := by
  -- Unpack the definition to expose the single summable error sequence used throughout the proof.
  exact h

-- Proof sketch: subtract the partial sums of the summable error sequence to obtain a corrected
-- sequence that is antitone and bounded below, hence convergent; then add back the convergent
-- partial sums of the errors.
/-- Helper for Theorem 5.33: a nonnegative real sequence whose one-step growth is controlled by a
summable nonnegative error sequence converges. -/
theorem tendsto_of_nonneg_summable_perturbation
    {α ε : ℕ → ℝ} (hεsumm : Summable ε) (hεnonneg : ∀ n : ℕ, 0 ≤ ε n)
    (hαnonneg : ∀ n : ℕ, 0 ≤ α n) (hstep : ∀ n : ℕ, α (n + 1) ≤ α n + ε n) :
    ∃ l : ℝ, Tendsto α atTop (𝓝 l) := by
  -- Route correction: package the scalar recursion in `ℝ≥0` and reuse Lemma 5.31 directly,
  -- rather than rebuilding the corrected-sequence convergence argument in this file.
  let αNN : ℕ → NNReal := fun n ↦ ⟨α n, hαnonneg n⟩
  let εNN : ℕ → NNReal := fun n ↦ ⟨ε n, hεnonneg n⟩
  have hεNN : Summable εNN := by
    have hεreal : Summable (fun n ↦ ((εNN n : NNReal) : ℝ)) := by
      simpa [εNN] using hεsumm
    exact (NNReal.summable_coe).1 hεreal
  have hrec : ∀ n : ℕ, αNN (n + 1) + 0 ≤ (1 + 0) * αNN n + εNN n := by
    intro n
    -- The given one-step estimate already matches the perturbed-descent hypothesis.
    simpa [αNN, εNN] using hstep n
  rcases
      tendsto_and_summable_of_summable_perturbed_descent
        (α := αNN) (β := fun _ ↦ 0) (γ := fun _ ↦ 0) (ε := εNN)
        summable_zero hεNN hrec with
    ⟨⟨l, hαNN⟩, _⟩
  refine ⟨l, ?_⟩
  have hαreal :
      Tendsto (fun n ↦ ((αNN n : NNReal) : ℝ)) atTop (𝓝 (l : ℝ)) :=
    (NNReal.tendsto_coe').2 ⟨l.2, hαNN⟩
  -- Coercing back to `ℝ` recovers the original scalar sequence.
  change Tendsto (fun n ↦ ((αNN n : NNReal) : ℝ)) atTop (𝓝 (l : ℝ))
  exact hαreal

-- Proof sketch: rewrite `Metric.infDist x C` as the infimum of `dist x z`, apply the monotone
-- continuous map `r ↦ max r 0 ^ 2` to move the square inside the infimum, and then note that all
-- distances are already nonnegative.
/-- Helper for Theorem 5.33: for a nonempty set, the square of the distance to the set is the
infimum of the squared distances to its points. -/
theorem sq_infDist_eq_iInf_sq_dist_nonempty (x : H) (C : Set H) (hC : C.Nonempty) :
    Metric.infDist x C ^ 2 = ⨅ z : C, dist x z ^ 2 := by
  let f : ℝ → ℝ := fun r ↦ max r 0 ^ 2
  letI : Nonempty C := hC.to_subtype
  rw [Metric.infDist_eq_iInf]
  have hinf_nonneg : 0 ≤ ⨅ z : C, dist x z := by
    refine le_ciInf fun z ↦ ?_
    exact dist_nonneg
  have hf_cont : ContinuousAt f (⨅ z : C, dist x z) := by
    dsimp [f]
    exact ((continuousAt_id.max continuousAt_const).pow 2)
  have hf_mono : Monotone f := by
    intro a b hab
    dsimp [f]
    have hmax : max a 0 ≤ max b 0 := max_le_max hab le_rfl
    nlinarith [hmax, le_max_right a 0, le_max_right b 0]
  have hmap :
      f (⨅ z : C, dist x z) = ⨅ z : C, f (dist x z) := by
    refine Monotone.map_ciInf_of_continuousAt hf_cont hf_mono ?_
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact dist_nonneg
  -- The cutoff inside `max` is inactive because each distance term is nonnegative.
  simpa [f, hinf_nonneg, dist_nonneg] using hmap

-- Proof sketch: apply the quasi-monotone convergence lemma to the real sequence
-- `n ↦ ‖x n - z‖ ^ 2`, then pass from convergence of squared norms to convergence of norms.
/-- Theorem 5.33 (1): clause (i). For every `z ∈ C`, the distance sequence
`n ↦ ‖x n - z‖` converges. -/
theorem quasiFejerMonotone_norm_tendsto {z : H}
    (hquasi : UniformQuasiFejerMonotone C x) (hz : z ∈ C) :
    ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - z‖) atTop (𝓝 l) := by
  rcases hquasi.exists_summable_sq_error with ⟨ε, hεsumm, hεnonneg, hstep⟩
  let α : ℕ → ℝ := fun n ↦ ‖x n - z‖ ^ 2
  have hαnonneg : ∀ n : ℕ, 0 ≤ α n := by
    intro n
    exact sq_nonneg _
  have hαstep : ∀ n : ℕ, α (n + 1) ≤ α n + ε n := by
    intro n
    -- The quasi-Fejér estimate already has the required perturbed-descent form.
    simpa [α] using hstep z hz n
  rcases tendsto_of_nonneg_summable_perturbation hεsumm hεnonneg hαnonneg hαstep with ⟨l, hα⟩
  refine ⟨Real.sqrt l, ?_⟩
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (α n)) atTop (𝓝 (Real.sqrt l)) :=
    (Real.continuous_sqrt.tendsto _).comp hα
  -- Taking square roots turns convergence of squared norms back into convergence of norms.
  simpa [α, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

-- Proof sketch: choose `z ∈ C`, use clause (i) to obtain convergence and hence boundedness of the
-- distance sequence to `z`, and then bound the range of `x` by translating that bounded real
-- sequence back to the ambient space.
/-- Theorem 5.33 (2): clause (ii). A quasi-Fejér monotone sequence with respect to a nonempty set
is bounded. -/
theorem quasiFejerMonotone_bounded
    (hC : C.Nonempty) (hquasi : UniformQuasiFejerMonotone C x) :
    Bornology.IsBounded (Set.range x) := by
  rcases hC with ⟨z, hz⟩
  rcases quasiFejerMonotone_norm_tendsto hquasi hz with ⟨l, hl⟩
  have hdist_bounded :
      Bornology.IsBounded (Set.range fun n ↦ ‖x n - z‖) :=
    Metric.isBounded_range_of_tendsto _ hl
  rcases isBounded_iff_forall_norm_le.mp hdist_bounded with ⟨R, hR⟩
  -- Bounding `‖x n - z‖` uniformly bounds `‖x n‖` by the triangle inequality.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R + ‖z‖, ?_⟩
  rintro y ⟨n, rfl⟩
  have hRn : ‖x n - z‖ ≤ R := by
    simpa using hR _ (Set.mem_range_self n)
  calc
    ‖x n‖ = ‖(x n - z) + z‖ := by abel_nf
    _ ≤ ‖x n - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ R + ‖z‖ := by simpa [add_comm] using add_le_add_right hRn ‖z‖

-- Proof sketch: use the common quasi-Fejér error sequence, compare `Metric.infDist` with each
-- pointwise distance, and push the infimum through addition by a constant to obtain the squared
-- distance-to-set recursion needed for Lemma 5.31.
/-- Helper for Theorem 5.33: when `C` is nonempty, the squared distance-to-set sequence satisfies
the same summable perturbed-descent inequality as the squared distances to points of `C`. -/
theorem quasiFejerMonotone_infDist_sq_step
    (hC : C.Nonempty) (hquasi : UniformQuasiFejerMonotone C x) :
    ∃ ε : ℕ → ℝ,
      Summable ε ∧
        (∀ n : ℕ, 0 ≤ ε n) ∧
          ∀ n : ℕ, Metric.infDist (x (n + 1)) C ^ 2 ≤ Metric.infDist (x n) C ^ 2 + ε n := by
  rcases hquasi.exists_summable_sq_error with ⟨ε, hεsumm, hεnonneg, hstep⟩
  refine ⟨ε, hεsumm, hεnonneg, ?_⟩
  intro n
  letI : Nonempty C := hC.to_subtype
  have hpoint :
      ∀ z : C, Metric.infDist (x (n + 1)) C ^ 2 ≤ dist (x n) z ^ 2 + ε n := by
    intro z
    have hdist : Metric.infDist (x (n + 1)) C ≤ dist (x (n + 1)) z :=
      Metric.infDist_le_dist_of_mem z.property
    have hsq :
        Metric.infDist (x (n + 1)) C ^ 2 ≤ dist (x (n + 1)) z ^ 2 := by
      exact (sq_le_sq₀ Metric.infDist_nonneg dist_nonneg).2 hdist
    -- First compare with a fixed point of `C`, then invoke the pointwise quasi-Fejér estimate.
    exact hsq.trans (by simpa [dist_eq_norm] using hstep z z.property n)
  have hinf :
      Metric.infDist (x (n + 1)) C ^ 2 ≤ ⨅ z : C, dist (x n) z ^ 2 + ε n := by
    -- The left-hand side is below every candidate upper bound, hence below their infimum.
    refine le_ciInf ?_
    intro z
    exact hpoint z
  have hmap :
      (⨅ z : C, dist (x n) z ^ 2) + ε n = ⨅ z : C, dist (x n) z ^ 2 + ε n := by
    let f : ℝ → ℝ := fun r ↦ r + ε n
    have hf_cont : ContinuousAt f (⨅ z : C, dist (x n) z ^ 2) := by
      simpa [f] using (continuousAt_id.add continuousAt_const)
    have hf_mono : Monotone f := by
      intro a b hab
      simpa [f] using add_le_add_right hab (ε n)
    have hbdd : BddBelow (Set.range fun z : C ↦ dist (x n) z ^ 2) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact sq_nonneg _
    -- Addition by the constant error term commutes with the infimum over `C`.
    simpa [f] using
      (Monotone.map_ciInf_of_continuousAt
        (g := fun z : C ↦ dist (x n) z ^ 2) hf_cont hf_mono hbdd)
  have hinf' :
      (⨅ z : C, dist (x (n + 1)) z ^ 2) ≤ ⨅ z : C, dist (x n) z ^ 2 + ε n := by
    simpa [sq_infDist_eq_iInf_sq_dist_nonempty (x (n + 1)) C hC] using hinf
  -- Rewrite the set distances as infima of squared pointwise distances on both sides.
  calc
    Metric.infDist (x (n + 1)) C ^ 2 = ⨅ z : C, dist (x (n + 1)) z ^ 2 := by
      exact sq_infDist_eq_iInf_sq_dist_nonempty (x (n + 1)) C hC
    _ ≤ ⨅ z : C, dist (x n) z ^ 2 + ε n := hinf'
    _ = (⨅ z : C, dist (x n) z ^ 2) + ε n := by
      symm
      exact hmap
    _ = Metric.infDist (x n) C ^ 2 + ε n := by
      rw [← sq_infDist_eq_iInf_sq_dist_nonempty (x n) C hC]

-- Proof sketch: take the infimum over `z ∈ C` in the defining squared-distance estimate to get a
-- quasi-monotone inequality for `n ↦ Metric.infDist (x n) C ^ 2`, then apply the same real
-- convergence lemma and pass from squared distances to distances.
/-- Theorem 5.33 (3): clause (iii). The distance sequence
`n ↦ Metric.infDist (x n) C` converges. -/
theorem quasiFejerMonotone_infDist_tendsto
    (hquasi : UniformQuasiFejerMonotone C x) :
    ∃ l : ℝ, Tendsto (fun n ↦ Metric.infDist (x n) C) atTop (𝓝 l) := by
  by_cases hC : C.Nonempty
  · rcases quasiFejerMonotone_infDist_sq_step hC hquasi with ⟨ε, hεsumm, hεnonneg, hstep⟩
    let α : ℕ → ℝ := fun n ↦ Metric.infDist (x n) C ^ 2
    have hαnonneg : ∀ n : ℕ, 0 ≤ α n := by
      intro n
      exact sq_nonneg _
    have hαstep : ∀ n : ℕ, α (n + 1) ≤ α n + ε n := by
      intro n
      -- The helper lemma has already distilled the set-distance recursion we need.
      simpa [α] using hstep n
    rcases tendsto_of_nonneg_summable_perturbation hεsumm hεnonneg hαnonneg hαstep with
      ⟨l, hα⟩
    refine ⟨Real.sqrt l, ?_⟩
    have hsqrt : Tendsto (fun n ↦ Real.sqrt (α n)) atTop (𝓝 (Real.sqrt l)) :=
      (Real.continuous_sqrt.tendsto _).comp hα
    -- As in clause (i), taking square roots recovers convergence of the unsquared distances.
    simpa [α, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Metric.infDist_nonneg : 0 ≤ Metric.infDist (x _) C)] using hsqrt
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    refine ⟨0, ?_⟩
    -- For the empty set the infimum distance is constantly zero.
    simpa [hCempty, Metric.infDist_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H} {x : ℕ → H}

-- Proof sketch: clause (i) supplies convergence of `n ↦ ‖x n - z‖` for every `z ∈ C`, and then
-- the weak cluster-point hypothesis lets one apply the chapter's Opial lemma to conclude weak
-- convergence to a point of `C`.
/-- Theorem 5.33 (4): clause (iv). If every weak sequential cluster point of a quasi-Fejér
monotone sequence belongs to `C`, then the sequence converges weakly to a point of `C`. -/
theorem tendsto_weakly_of_quasiFejerMonotone_of_weakSequentialClusterPts_mem
    (hC : C.Nonempty) (hquasi : UniformQuasiFejerMonotone C x)
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) → z ∈ C) :
    ∃ z ∈ C, Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H z)) := by
  -- Clause (i) supplies exactly the distance-convergence hypothesis required by Opial's lemma.
  refine opial_lemma hC x ?_ hcluster
  intro z hz
  exact quasiFejerMonotone_norm_tendsto hquasi hz

end
