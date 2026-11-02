module

public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

universe u v

namespace Function

/-- An algorithm runtime `runtime : S → ℕ` is polynomially bounded by an input-size function
`encodingSize : S → ℕ` when some natural-coefficient polynomial dominates `runtime` pointwise
after evaluation on the encoding size. -/
def PolynomiallyBoundedByNat {S : Type u} (runtime encodingSize : S → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ s : S, runtime s ≤ p.eval (encodingSize s)

/-- Expanding `runtime.PolynomiallyBoundedByNat encodingSize` gives the witness polynomial and the
corresponding pointwise domination inequality. -/
theorem polynomiallyBoundedByNat_iff
    {S : Type u} {runtime encodingSize : S → ℕ} :
    runtime.PolynomiallyBoundedByNat encodingSize ↔
      ∃ p : Polynomial ℕ, ∀ s : S, runtime s ≤ p.eval (encodingSize s) :=
  Iff.rfl

namespace PolynomiallyBoundedByNat

/-- Precomposing the domain by `u` preserves polynomial boundedness by the transported encoding
size function. -/
theorem comp_right
    {S : Type u} {T : Type v} {runtime encodingSize : S → ℕ}
    (h : runtime.PolynomiallyBoundedByNat encodingSize) (u : T → S) :
    (runtime ∘ u).PolynomiallyBoundedByNat (encodingSize ∘ u) := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, fun t ↦ hp (u t)⟩

end PolynomiallyBoundedByNat

end Function

end
