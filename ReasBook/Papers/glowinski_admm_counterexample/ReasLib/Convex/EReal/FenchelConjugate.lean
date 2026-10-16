module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.EReal.Basic

@[expose] public section

namespace ERealConvex

/-- The Fenchel conjugate of an extended-real function on a finite real
coordinate space. -/
noncomputable def fenchelConjugate {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (p : Fin n → ℝ) : EReal :=
  sSup {r | ∃ x : Fin n → ℝ, r = ((dotProduct x p : ℝ) : EReal) - φ x}

/-- Evaluation of the Fenchel conjugate as a supremum of affine differences. -/
theorem fenchelConjugate_apply {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (p : Fin n → ℝ) :
    fenchelConjugate φ p =
      sSup {r | ∃ x : Fin n → ℝ,
        r = ((dotProduct x p : ℝ) : EReal) - φ x} := by
  -- Unfolding the conjugate exposes exactly the stated supremum.
  rfl

/-- The Fenchel biconjugate of an extended-real function. -/
noncomputable def fenchelBiconjugate {n : ℕ} (φ : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fenchelConjugate (fenchelConjugate φ)

/-- Evaluation of the Fenchel biconjugate by two successive conjugations. -/
theorem fenchelBiconjugate_apply {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (x : Fin n → ℝ) :
    fenchelBiconjugate φ x = fenchelConjugate (fenchelConjugate φ) x := by
  -- Unfolding only the outer biconjugate gives the successive conjugations.
  rfl

end ERealConvex
