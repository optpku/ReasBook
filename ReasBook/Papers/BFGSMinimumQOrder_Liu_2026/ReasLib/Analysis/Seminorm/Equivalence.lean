module

public import Mathlib.Analysis.Seminorm

public section

universe u v

namespace Seminorm

variable {𝕜 : Type u} {E : Type v} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Two seminorms are equivalent when each bounds the other up to a positive constant. -/
def IsEquivalent (p q : Seminorm 𝕜 E) : Prop :=
  ∃ a b : NNReal, 0 < a ∧ 0 < b ∧ a • q ≤ p ∧ p ≤ b • q

/-- Seminorm.isEquivalent_iff: equivalence of seminorms expressed by pointwise
two-sided bounds. -/
theorem isEquivalent_iff {p q : Seminorm 𝕜 E} :
    p.IsEquivalent q ↔
      ∃ a b : NNReal, 0 < a ∧ 0 < b ∧
        ∀ x, (a : ℝ) * q x ≤ p x ∧ p x ≤ (b : ℝ) * q x := by
  -- Translate the two seminorm-order bounds to evaluations and combine their quantifiers.
  simp only [IsEquivalent, le_def, smul_apply, NNReal.smul_def, smul_eq_mul, forall_and]

namespace IsEquivalent

/-- Every seminorm is equivalent to itself. -/
theorem refl (p : Seminorm 𝕜 E) : p.IsEquivalent p := by
  -- The unit scalar supplies both comparison constants.
  rw [isEquivalent_iff]
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro x
  simp

/-- Equivalence of seminorms is symmetric. -/
theorem symm {p q : Seminorm 𝕜 E} (h : p.IsEquivalent q) :
    q.IsEquivalent p := by
  -- Reciprocal constants turn each original comparison into the reversed one.
  rw [isEquivalent_iff] at h ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := h
  refine ⟨b⁻¹, a⁻¹, inv_pos.mpr hb, inv_pos.mpr ha, ?_⟩
  have haReal : (0 : ℝ) < a := NNReal.coe_pos.mpr ha
  have hbReal : (0 : ℝ) < b := NNReal.coe_pos.mpr hb
  intro x
  constructor
  · rw [NNReal.coe_inv, inv_mul_le_iff₀ hbReal]
    exact (hab x).2
  · rw [NNReal.coe_inv, le_inv_mul_iff₀ haReal]
    exact (hab x).1

/-- Equivalence of seminorms is transitive. -/
theorem trans {p q r : Seminorm 𝕜 E} (hpq : p.IsEquivalent q)
    (hqr : q.IsEquivalent r) : p.IsEquivalent r := by
  -- Products compose the lower bounds and the upper bounds independently.
  rw [isEquivalent_iff] at hpq hqr ⊢
  obtain ⟨a, b, ha, hb, hpq⟩ := hpq
  obtain ⟨c, d, hc, hd, hqr⟩ := hqr
  refine ⟨a * c, b * d, mul_pos ha hc, mul_pos hb hd, ?_⟩
  intro x
  constructor
  · calc
      ((a * c : NNReal) : ℝ) * r x = (a : ℝ) * ((c : ℝ) * r x) := by
        rw [NNReal.coe_mul, mul_assoc]
      _ ≤ (a : ℝ) * q x := mul_le_mul_of_nonneg_left (hqr x).1 a.coe_nonneg
      _ ≤ p x := (hpq x).1
  · calc
      p x ≤ (b : ℝ) * q x := (hpq x).2
      _ ≤ (b : ℝ) * ((d : ℝ) * r x) :=
        mul_le_mul_of_nonneg_left (hqr x).2 b.coe_nonneg
      _ = ((b * d : NNReal) : ℝ) * r x := by
        rw [NNReal.coe_mul, mul_assoc]

end IsEquivalent

end Seminorm
