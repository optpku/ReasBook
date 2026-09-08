module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Analysis.Asymptotics.UniformRemainder

public section

namespace Asymptotics.IsUniformRemainderModulusOn

universe u v

/-- An order-`q + 1` bound gives a linear-in-`η` upper bound for the canonical
order-`q` remainder modulus. -/
theorem uniformRemainderModulus_le_mul
    {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Θ → ℝ → E} {s : Set Θ} {q η C : ℝ}
    (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hbound : ∀ θ ∈ s, ∀ ε : ℝ, 0 < |ε| → |ε| ≤ η →
      ‖R θ ε‖ ≤ C * |ε| ^ (q + 1)) :
    uniformRemainderModulus R s q η ≤ C * η := by
  let A : Set ℝ := insert 0 {c : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
    0 < |ε| ∧ |ε| ≤ η ∧ c = ‖R θ ε‖ / |ε| ^ q}
  have hupper : ∀ c ∈ A, c ≤ C * η := by
    intro c hc
    change c ∈ insert 0 {d : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
      0 < |ε| ∧ |ε| ≤ η ∧ d = ‖R θ ε‖ / |ε| ^ q} at hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact mul_nonneg hC hη
    · rcases hc with ⟨θ, hθ, ε, hε, hεη, rfl⟩
      have hpow : 0 < |ε| ^ q := Real.rpow_pos_of_pos hε q
      have hscaled : ‖R θ ε‖ / |ε| ^ q ≤ C * |ε| := by
        apply (div_le_iff₀ hpow).2
        calc
          ‖R θ ε‖ ≤ C * |ε| ^ (q + 1) := hbound θ hθ ε hε hεη
          _ = (C * |ε|) * |ε| ^ q := by
            rw [Real.rpow_add hε q 1, Real.rpow_one]
            ring
      exact hscaled.trans (mul_le_mul_of_nonneg_left hεη hC)
  have hnonempty : A.Nonempty := by
    exact ⟨0, Set.mem_insert 0 _⟩
  have hsup : sSup A ≤ C * η := csSup_le hnonempty hupper
  change sSup (insert 0 {c : ℝ | ∃ θ ∈ s, ∃ ε : ℝ,
    0 < |ε| ∧ |ε| ≤ η ∧ c = ‖R θ ε‖ / |ε| ^ q}) ≤ C * η
  exact hsup

/-- A natural-power bound of order `n + 1` gives a linear upper bound for the
canonical order-`n` remainder modulus. -/
theorem uniformRemainderModulus_natCast_le_mul
    {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Θ → ℝ → E} {s : Set Θ} {n : ℕ} {η C : ℝ}
    (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hbound : ∀ θ ∈ s, ∀ ε : ℝ, 0 < |ε| → |ε| ≤ η →
      ‖R θ ε‖ ≤ C * |ε| ^ (n + 1)) :
    uniformRemainderModulus R s (n : ℝ) η ≤ C * η := by
  apply uniformRemainderModulus_le_mul hη hC
  intro θ hθ ε hε hεη
  have hexponent : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by
    norm_num
  rw [hexponent, Real.rpow_natCast]
  exact hbound θ hθ ε hε hεη

/-- An order-`n + 1` uniform remainder estimate supplies a positive range on which
the canonical order-`n` modulus is bounded by `C * η`. -/
theorem exists_uniformRemainderModulus_natCast_le_mul
    {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Θ → ℝ → E} {s : Set Θ} {n : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hR : IsUniformRemainderOn R s C ((n + 1 : ℕ) : ℝ)) :
    ∃ η₀ > 0, ∀ η ∈ Set.Ioc 0 η₀,
      uniformRemainderModulus R s (n : ℝ) η ≤ C * η := by
  obtain ⟨δ, hδ, hbound⟩ := hR
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro η hη
  apply uniformRemainderModulus_natCast_le_mul hη.1.le hC
  intro θ hθ ε hε hεη
  have hεδ : |ε| < δ := hεη.trans_lt (hη.2.trans_lt (half_lt_self hδ))
  have h := hbound θ hθ ε hεδ
  simpa only [Real.rpow_natCast] using h

end Asymptotics.IsUniformRemainderModulusOn
