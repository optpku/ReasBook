module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This file is the source-independent final algebra step for the normalized
center bracket.  The source proof supplies the bracket germ and the exact
transport identity; this module only performs the compact remainder and
zero-filled cubic cancellation.
-/

/-- Helper for Infrastructure I.16a: the zero-filled quotient associated with a
mixed scalar residual and its cubic weight. -/
def centerBracketZeroFilledQuotient
    (R : (ℝ × ℝ × ℝ) → ℝ → ℝ) (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  if θ.1 * r ^ (3 : ℕ) = 0 then 0 else
    R θ r / (θ.1 * r ^ (3 : ℕ))

/-- Helper for Infrastructure I.16a: the two-term truncated polynomial of a
bracket with zero constant coefficient is `κ θ * r`. -/
lemma centerBracket_linearPolynomial
    (κ : (ℝ × ℝ × ℝ) → ℝ) (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    (∑ n : Fin 2,
        (![0, κ θ] : Fin 2 → ℝ) n * r ^ (n : ℕ)) = κ θ * r := by
  simp [Fin.sum_univ_succ]

/-- Infrastructure I.16a: a compact quadratic bracket germ and its exact
`θ.1 * r` transport yield a uniform bound for the zero-filled cubic quotient. -/
theorem centerBracket_zeroFilledQuotient_uniformBound
    {R W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {κ : (ℝ × ℝ × ℝ) → ℝ}
    {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K)
    (hW : IndependentRadiusTruncatedGerm W K 2
      (fun n θ ↦ (![0, κ θ] : Fin 2 → ℝ) n))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (htransport : ∀ θ ∈ K, ∀ r : ℝ, |r| < δ₀ →
      R θ r = θ.1 * r * (W θ r - κ θ * r)) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖centerBracketZeroFilledQuotient R θ r‖ ≤ C := by
  have horder : 0 < (2 : ℕ) := by norm_num
  obtain ⟨C, hC, hRemainder⟩ :=
    uniformRemainderOn_of_independentRadiusTruncatedGerm
      (m := 2) horder hK hW
  have hC_nonneg : 0 ≤ C := le_of_lt hC
  obtain ⟨δW, hδW, hRemainder⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_bound hRemainder
  have hbracket : ∀ θ ∈ K, ∀ r : ℝ, |r| < δW →
      ‖W θ r - κ θ * r‖ ≤ C * |r| ^ (2 : ℝ) := by
    intro θ hθ r hr
    have hbound := hRemainder θ hθ r hr
    rw [centerBracket_linearPolynomial] at hbound
    exact hbound
  let δ : ℝ := min δ₀ δW
  have hδ : 0 < δ := lt_min hδ₀ hδW
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro θ hθ r hr
  have hr₀ : |r| < δ₀ := lt_of_lt_of_le hr (min_le_left δ₀ δW)
  have hrW : |r| < δW := lt_of_lt_of_le hr (min_le_right δ₀ δW)
  by_cases hweight : θ.1 * r ^ (3 : ℕ) = 0
  · simp [centerBracketZeroFilledQuotient, hweight, hC_nonneg]
  · have hθ_ne : θ.1 ≠ 0 := by
      intro hθzero
      apply hweight
      simp [hθzero]
    have hr_ne : r ≠ 0 := by
      intro hrzero
      apply hweight
      simp [hrzero]
    have htransport' := htransport θ hθ r hr₀
    have hscalar :
        (θ.1 * r * (W θ r - κ θ * r)) /
            (θ.1 * r ^ (3 : ℕ)) =
          (W θ r - κ θ * r) / r ^ (2 : ℕ) := by
      field_simp [hθ_ne, hr_ne]
    simp only [centerBracketZeroFilledQuotient, hweight, if_false,
      htransport']
    rw [hscalar]
    have hrpow_ne : r ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hr_ne
    have hnorm_rpow_pos : 0 < ‖r ^ (2 : ℕ)‖ := norm_pos_iff.mpr hrpow_ne
    rw [norm_div]
    apply (div_le_iff₀ hnorm_rpow_pos).2
    have hbracket' := hbracket θ hθ r hrW
    have hpow : |r| ^ (2 : ℝ) = |r| ^ (2 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [hpow] at hbracket'
    have hdenom : ‖r ^ (2 : ℕ)‖ = |r| ^ (2 : ℕ) := by
      rw [norm_pow, Real.norm_eq_abs]
    rw [hdenom]
    exact hbracket'

end DFP.TwoLeg.Mixed
