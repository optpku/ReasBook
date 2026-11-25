/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.RadialRemainder
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

open scoped ComplexOrder

namespace ADMM.UnitCircle

/-- Compactness bounds every entry of the actual constructed radial remainder
uniformly in a fixed terminal discount interval and on the whole unit circle. -/
theorem supplyRadialRemainder_entries_bounded {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, 1 / 2 ≤ α → α ≤ 1 →
      ∀ z : ℂ, ‖z‖ = 1 → ∀ i j : Fin 2,
        ‖supplyRadialRemainder c γ α z i j‖ ≤ B := by
  let K : Set (ℝ × ℂ) := Set.Icc (1 / 2 : ℝ) 1 ×ˢ Metric.sphere (0 : ℂ) 1
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_sphere (0 : ℂ) 1)
  let f : (ℝ × ℂ) → (Fin 2 → Fin 2 → ℂ) :=
    fun p ↦ supplyRadialRemainder c γ p.1 p.2
  have hf : ContinuousOn f K := by
    intro p hp
    apply (supplyRadialRemainder_continuousAt c γ p ?_).continuousWithinAt
    have hz : ‖p.2‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hp.2
    exact norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨max B 1, lt_of_lt_of_le (by norm_num) (le_max_right B 1), ?_⟩
  intro α ha0 ha1 z hz i j
  have hp : (α, z) ∈ K := by
    exact ⟨⟨ha0, ha1⟩, by simpa [Metric.mem_sphere, dist_zero_right] using hz⟩
  exact (norm_le_pi_norm (f (α, z) i) j).trans
    ((norm_le_pi_norm (f (α, z)) i).trans ((hB (α, z) hp).trans (le_max_left B 1)))

/-- A uniform bound on the entries of a Hermitian two-by-two matrix gives
a quantitative lower matrix bound. -/
theorem hermitian_add_scalar_posDef_of_entry_bound
    {A : Matrix (Fin 2) (Fin 2) ℂ} {B : ℝ} (hA : A.IsHermitian)
    (hB : 0 < B) (hentry : ∀ i j : Fin 2, ‖A i j‖ ≤ B) :
    (A + ((4 * B : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  have ha : -B ≤ (A 0 0).re :=
    (abs_le.mp ((Complex.abs_re_le_norm (A 0 0)).trans (hentry 0 0))).1
  have hd : -B ≤ (A 1 1).re :=
    (abs_le.mp ((Complex.abs_re_le_norm (A 1 1)).trans (hentry 1 1))).1
  have hb : Complex.normSq (A 0 1) ≤ B ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hentry 0 1, norm_nonneg (A 0 1)]
  have h00 : 0 < (A 0 0).re + 4 * B := by linarith
  have hp : (3 * B) * (3 * B) ≤
      ((A 0 0).re + 4 * B) * ((A 1 1).re + 4 * B) := by
    apply mul_le_mul <;> linarith
  have hdet : 0 < ((A 0 0).re + 4 * B) * ((A 1 1).re + 4 * B) -
      Complex.normSq (A 0 1) := by nlinarith [sq_pos_of_pos hB]
  have hform : A + ((4 * B : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      hermitianTwoByTwo ((A 0 0).re + 4 * B) ((A 1 1).re + 4 * B) (A 0 1) := by
    conv_lhs => rw [hermitian_eq_twoByTwo hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianTwoByTwo] <;> push_cast <;> ring
  rw [hform]
  exact hermitianTwoByTwo_posDef h00 hdet

/-- The actual radial remainder is bounded below uniformly on the circle.
This is the compactness input for the part away from zero frequency. -/
theorem supplyRadialRemainder_uniform_lower_bound {ℓ : ℕ}
    (c : LagWeights ℓ) (γ : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ α : ℝ, 1 / 2 ≤ α → α < 1 →
      ∀ z : ℂ, ‖z‖ = 1 →
        (supplyRadialRemainder c γ α z +
          (M : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  obtain ⟨B, hB, hbound⟩ := supplyRadialRemainder_entries_bounded c γ
  refine ⟨4 * B, by positivity, ?_⟩
  intro α ha0 ha1 z hz
  exact (hermitian_add_scalar_posDef_of_entry_bound
    (supplyRadialRemainder_isHermitian c γ α z ha1.ne) hB
    (hbound α ha0 ha1.le z hz)).posSemidef

end ADMM.UnitCircle
