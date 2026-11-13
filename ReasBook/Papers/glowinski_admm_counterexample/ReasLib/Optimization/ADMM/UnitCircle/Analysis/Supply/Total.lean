/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Discounted

@[expose] public section

open scoped BigOperators Topology
open ADMM.ConvergenceProof Filter

namespace ADMM.UnitCircle.Supply

/-- The actual convex supply in one graph block, excluding the residual square. -/
noncomputable def blockSupply {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    (x g : ℕ → Fin m → ℝ) (k : ℕ) : ℝ :=
  c.omega * dotProduct (g k) (x k) + ∑ i : Fin ℓ,
    lagSupply x g (c.backward b i) (c.forward b i) (i.val + 1) k

/-- The coefficient of the graph height remaining after summing lag differences. -/
noncomputable def discountCorrection {ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    (α : ℝ) : ℝ :=
  ∑ i : Fin ℓ, (c.backward b i - c.forward b i) * (1 - timeWeight α (i.val + 1))

/-- Discounting makes the complete finite supply absolutely summable. -/
theorem summable_weighted_blockSupply {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    {x g : ℕ → Fin m → ℝ} {α : ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k))) :
    Summable (fun k ↦ timeWeight α k * blockSupply c b x g k) := by
  have hsum := summable_sum (s := Finset.univ) (fun i _ ↦
    summable_weighted_lagSupply hx hg (c.backward b i) (c.forward b i) (i.val + 1))
  apply (((summable_weighted_dot hg hx).mul_left c.omega).add hsum).congr
  intro k
  simp only [blockSupply, mul_add, Finset.mul_sum]
  ring

/-- The weighted convex supply dominates its exact graph-potential lower bound. -/
theorem weighted_blockSupply_lower {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    {f : (Fin m → ℝ) → EReal} {x g : ℕ → Fin m → ℝ} {α : ℝ}
    (hzero : IsSubgradientAt f 0 0)
    (hgraph : ∀ k, IsSubgradientAt f (g k) (x k))
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k))) :
    c.omega * (∑' k, timeWeight α k * dotProduct (g k) (x k)) +
      discountCorrection c b α * (∑' k, timeWeight α k * graphValue f (x k)) ≤
      ∑' k, timeWeight α k * blockSupply c b x g k := by
  have hp := summable_weighted_dot hg hx
  have hl : ∀ i : Fin ℓ, Summable (fun k ↦ timeWeight α k *
      lagSupply x g (c.backward b i) (c.forward b i) (i.val + 1) k) :=
    fun i ↦ summable_weighted_lagSupply hx hg _ _ _
  have hsum := summable_sum (s := Finset.univ) (fun i _ ↦ hl i)
  have heq : (∑' k, timeWeight α k * blockSupply c b x g k) =
      c.omega * (∑' k, timeWeight α k * dotProduct (g k) (x k)) +
      ∑ i : Fin ℓ, ∑' k, timeWeight α k *
        lagSupply x g (c.backward b i) (c.forward b i) (i.val + 1) k := by
    calc
      _ = ∑' k, (c.omega * (timeWeight α k * dotProduct (g k) (x k)) +
          ∑ i : Fin ℓ, timeWeight α k *
            lagSupply x g (c.backward b i) (c.forward b i) (i.val + 1) k) := by
        apply tsum_congr
        intro k
        simp only [blockSupply, mul_add, Finset.mul_sum]
        ring
      _ = _ := by
        rw [(hp.mul_left c.omega).tsum_add hsum, tsum_mul_left,
          Summable.tsum_finsetSum (fun i _ ↦ hl i)]
  rw [heq]
  apply add_le_add le_rfl
  rw [discountCorrection, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact weighted_lag_lower hzero hgraph hx hg (c.backward_nonneg b i)
    (c.forward_nonneg b i) (i.val + 1)

/-- A small discount correction can lose at most half of the origin merit. -/
theorem half_origin_merit_le {ω σ ψ M : ℝ} (hω : 0 ≤ ω)
    (hσ : |σ| ≤ ω / 2) (hψ : 0 ≤ ψ) (hψM : ψ ≤ M) :
    (ω / 2) * M ≤ ω * M + σ * ψ := by
  have hM : 0 ≤ M := hψ.trans hψM
  have hs : -(ω / 2) ≤ σ := (abs_le.mp hσ).1
  have h₁ := mul_le_mul_of_nonneg_right hs hψ
  have h₂ := mul_le_mul_of_nonneg_left hψM (show 0 ≤ ω / 2 by positivity)
  nlinarith

/-- The actual discounted convex supply is nonnegative, with the stronger
half-origin-pairing lower bound from Appendix C.1. -/
theorem discounted_convex_supply {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    {f : (Fin m → ℝ) → EReal} {x g : ℕ → Fin m → ℝ} {α : ℝ}
    (hzero : IsSubgradientAt f 0 0)
    (hgraph : ∀ k, IsSubgradientAt f (g k) (x k))
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (hcorrection : |discountCorrection c b α| ≤ c.omega / 2) :
    0 ≤ (c.omega / 2) * (∑' k, timeWeight α k * dotProduct (g k) (x k)) ∧
      (c.omega / 2) * (∑' k, timeWeight α k * dotProduct (g k) (x k)) ≤
        ∑' k, timeWeight α k * blockSupply c b x g k := by
  have hb := fun k ↦ graphValue_bounds hzero (hgraph k)
  have hM : ∀ k, 0 ≤ dotProduct (g k) (x k) := fun k ↦ (hb k).1.trans (hb k).2
  have htotalM : 0 ≤ ∑' k, timeWeight α k * dotProduct (g k) (x k) :=
    tsum_nonneg (fun k ↦ mul_nonneg (timeWeight_nonneg α k) (hM k))
  refine ⟨mul_nonneg (div_nonneg c.omega_pos.le (by norm_num)) htotalM, ?_⟩
  have hv := summable_weighted_graphValue hzero hgraph hx hg
  have hp := summable_weighted_dot hg hx
  have hv0 : 0 ≤ ∑' k, timeWeight α k * graphValue f (x k) :=
    tsum_nonneg (fun k ↦ mul_nonneg (timeWeight_nonneg α k) (hb k).1)
  have hvM : (∑' k, timeWeight α k * graphValue f (x k)) ≤
      ∑' k, timeWeight α k * dotProduct (g k) (x k) :=
    hv.tsum_le_tsum (fun k ↦ mul_le_mul_of_nonneg_left (hb k).2
      (timeWeight_nonneg α k)) hp
  exact (half_origin_merit_le c.omega_pos.le hcorrection hv0 hvM).trans
    (weighted_blockSupply_lower c b hzero hgraph hx hg)

/-- Every finite set of lag weights has a vanishing discount correction at
one, so the half-origin estimate holds throughout a neighborhood of one. -/
theorem discountCorrection_tendsto {ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2) :
    Tendsto (discountCorrection c b) (𝓝 (1 : ℝ)) (𝓝 0) := by
  have hId : Tendsto (fun α : ℝ ↦ α) (𝓝 (1 : ℝ)) (𝓝 1) := tendsto_id
  have hOne : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝 (1 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have h : Tendsto
      (fun α : ℝ ↦ ∑ i : Fin ℓ, (c.backward b i - c.forward b i) *
        (1 - α ^ (2 * (i.val + 1)))) (𝓝 1)
      (𝓝 (∑ i : Fin ℓ, (c.backward b i - c.forward b i) *
        (1 - (1 : ℝ) ^ (2 * (i.val + 1))))) :=
    tendsto_finsetSum Finset.univ (fun i _ ↦
      (hOne.sub (hId.pow (2 * (i.val + 1)))).const_mul
        (c.backward b i - c.forward b i))
  change Tendsto (fun α : ℝ ↦ ∑ i : Fin ℓ,
    (c.backward b i - c.forward b i) * (1 - α ^ (2 * (i.val + 1)))) _ _
  simpa only [one_pow, sub_self, mul_zero, Finset.sum_const_zero] using h

/-- The two blocks simultaneously have sufficiently small discount errors. -/
theorem eventually_discountCorrection_small {ℓ : ℕ} (c : LagWeights ℓ) :
    ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), ∀ b : Fin 2,
      |discountCorrection c b α| ≤ c.omega / 2 := by
  apply Filter.eventually_all.mpr
  intro b
  have h := (discountCorrection_tendsto c b).abs
  have hsmall : ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), |discountCorrection c b α| < c.omega / 2 :=
    (tendsto_order.1 h).2 _ (by simpa using (show 0 < c.omega / 2 from div_pos c.omega_pos (by norm_num)))
  exact hsmall.mono (fun _ hα ↦ hα.le)

end ADMM.UnitCircle.Supply
