/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitConvergence

@[expose] public section

open scoped BigOperators
open ADMM.ConvergenceProof ADMM.FiniteMemory

namespace ADMM.UnitCircle.Recovery

/-- Square summability of the true multiplier differences bounds the entire
normalized state. This uses only the exact reduced energy identity and graph
monotonicity at the KKT origin, independently of a finite-memory certificate. -/
theorem state_bounded_of_residual_summable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k))
    (hres : Summable (fun k ↦ coordinateSquare (w (k + 1) - w k))) :
    ∃ C : ℝ, ∀ k, coordinateSquare (η k) + coordinateSquare (w k) ≤ C := by
  let E : ℕ → ℝ := fun k ↦ γ ^ 2 * coordinateSquare (w k) + γ * coordinateSquare (η k)
  let R : ℕ → ℝ := fun k ↦ γ ^ 2 * coordinateSquare (w (k + 1) - w k)
  have hE : ∀ k, 0 ≤ E k := fun k ↦ add_nonneg
    (mul_nonneg (sq_nonneg _) (coordinateSquare_nonneg _))
    (mul_nonneg hγ.le (coordinateSquare_nonneg _))
  have hR : ∀ k, 0 ≤ R k := fun k ↦
    mul_nonneg (sq_nonneg _) (coordinateSquare_nonneg _)
  have hsR : Summable R := hres.mul_left (γ ^ 2)
  have hpair := generated_pairing_nonneg f η w hzero hgraph
  have hstep : ∀ k, E (k + 1) ≤ E k + R k := by
    intro k
    have he := reduced_energy_descent hγ.le (η k) (η (k + 1)) (w k) (w (k + 1))
    have hp := mul_nonneg (show 0 ≤ 2 * γ by positivity) (hpair k)
    have hd := mul_nonneg (show 0 ≤ γ / 2 by positivity)
      (coordinateSquare_nonneg (η (k + 1) - η k))
    dsimp only [generatedNormal, generatedPosition] at hp
    dsimp only [E, R]
    linarith
  have hfinite : ∀ k, E k ≤ E 0 + ∑ j ∈ Finset.range k, R j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep k]
  let C : ℝ := E 0 + ∑' k, R k
  have hbound : ∀ k, E k ≤ C := by
    intro k
    exact (hfinite k).trans (add_le_add le_rfl
      (hsR.sum_le_tsum (Finset.range k) (fun i _ ↦ hR i)))
  refine ⟨C / γ + C / γ ^ 2, ?_⟩
  intro k
  have hη : coordinateSquare (η k) ≤ C / γ := by
    apply (le_div_iff₀ hγ).mpr
    have hw := mul_nonneg (sq_nonneg γ) (coordinateSquare_nonneg (w k))
    have hb := hbound k
    dsimp only [E] at hb
    nlinarith
  have hw : coordinateSquare (w k) ≤ C / γ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
    have hη := mul_nonneg hγ.le (coordinateSquare_nonneg (η k))
    have hb := hbound k
    dsimp only [E] at hb
    nlinarith
  exact add_le_add hη hw

/-- The normalized orbit converges from residual summability alone. Compactness,
closed graph limits, and the existing summable-error energy argument identify
one stationary limit; no convergence of the objective on its domain is assumed. -/
theorem normalized_converges_of_residual_summable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hf : ∀ b, IsClosedProperConvex (f b))
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k))
    (hres : Summable (fun k ↦ coordinateSquare (w (k + 1) - w k))) :
    ∃ ηBar wBar, Filter.Tendsto η Filter.atTop (nhds ηBar) ∧
      Filter.Tendsto w Filter.atTop (nhds wBar) ∧
      (∀ b, IsSubgradientAt (f b) (stationaryNormal γ wBar b) ηBar) :=
  reduced_converges_of_bounded_summable hγ f η w hf hzero hgraph
    (state_bounded_of_residual_summable hγ f η w hzero hgraph hres) hres

end ADMM.UnitCircle.Recovery
