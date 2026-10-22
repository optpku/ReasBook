/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GeneratedCertificate
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitEnergy

@[expose] public section

open scoped BigOperators
open ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- A finite-memory certificate gives the actual multiplier residual square
summability, after restoring the harmless finite generated prefix. -/
theorem finiteMemory_residual_summable {m ℓ : ℕ} {γ : ℝ}
    (c : Certificate ℓ γ) (f : Block → (Fin m → ℝ) → EReal)
    (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) :
    Summable (fun k ↦ coordinateSquare (w (k + 1) - w k)) := by
  have hs := (generated_certificate_summable c f η w hzero hgraph).2
  apply (summable_nat_add_iff ℓ).1
  simpa only [residual_coordinate, generatedHistory_residual, Fin.rev_zero,
    Fin.val_last, coordinateSquare, dotProduct, Pi.sub_apply, pow_two] using hs

/-- The certificate lower bound and nonincreasing storage uniformly bound the
entire reduced state, including its finite initial prefix. -/
theorem finiteMemory_state_bounded {m ℓ : ℕ} {γ : ℝ}
    (c : Certificate ℓ γ) (f : Block → (Fin m → ℝ) → EReal)
    (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) :
    ∃ C : ℝ, ∀ k, coordinateSquare (η k) + coordinateSquare (w k) ≤ C := by
  let Z := generatedHistory (ℓ := ℓ) η w
  let Φ := generatedValues (ℓ := ℓ) f η w
  let U := certificateSequenceStorage c Z Φ
  let S : ℕ → ℝ := fun k ↦ coordinateSquare (η k) + coordinateSquare (w k)
  have hS : ∀ k, 0 ≤ S k := fun k ↦ add_nonneg
    (coordinateSquare_nonneg _) (coordinateSquare_nonneg _)
  have hlower : ∀ k, c.zeta * S (k + ℓ) ≤ U k := by
    intro k
    have h := certificateSequence_lower c Z Φ (generatedValues_gap f η w hzero hgraph) k
    simpa [Z, Φ, U, S, generatedHistory, Fin.rev, coordinateSquare,
      dotProduct, pow_two, Finset.sum_add_distrib] using h
  have hmono : Antitone U := by
    apply antitone_nat_of_succ_le
    intro k
    have h := certificateSequence_descent c Z Φ (generatedHistory_shift η w)
      (generatedValues_shift f η w) (generatedValues_current f η w hzero hgraph)
      (generatedValues_support f η w hgraph) k
    have hm := mul_nonneg c.omega_pos.le (add_nonneg
      (generatedValues_nonneg (ℓ := ℓ) f η w hzero hgraph k .F 0)
      (generatedValues_nonneg (ℓ := ℓ) f η w hzero hgraph k .J 0))
    have hr : 0 ≤ c.epsilon * ∑ a : Fin m,
        FiniteMemory.residual (fun i ↦ Z k i a) 0 ^ 2 :=
      mul_nonneg c.epsilon_pos.le (Finset.sum_nonneg fun a _ ↦ sq_nonneg _)
    change U (k + 1) ≤ U k
    dsimp only [U, Φ] at *
    linarith
  have htail : ∀ k, S (k + ℓ) ≤ U 0 / c.zeta := by
    intro k
    exact storage_coercive_bound c.zeta_pos hlower hmono k
  have hnonneg : 0 ≤ U 0 / c.zeta := (hS ℓ).trans (by simpa using htail 0)
  refine ⟨U 0 / c.zeta + ∑ j ∈ Finset.range ℓ, S j, ?_⟩
  intro k
  change S k ≤ _
  by_cases hk : k < ℓ
  · have hprefix : S k ≤ ∑ j ∈ Finset.range ℓ, S j :=
      Finset.single_le_sum (fun j _ ↦ hS j) (Finset.mem_range.mpr hk)
    linarith
  · have htail' : S k ≤ U 0 / c.zeta := by
      simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt hk)] using htail (k - ℓ)
    have hprefix : 0 ≤ ∑ j ∈ Finset.range ℓ, S j := Finset.sum_nonneg fun j _ ↦ hS j
    linarith

end ADMM.ConvergenceProof
