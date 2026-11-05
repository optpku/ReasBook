/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

universe u v

namespace Function

/-- Definition 1.13. Let `S` be a type and let `f g : S → NNReal`. The function `f` is
polynomially bounded by `g` if there exists a real polynomial `φ` such that
`(f s : ℝ) ≤ φ.eval (g s : ℝ)` for all `s : S`. -/
def PolynomiallyBoundedBy {S : Type u} (f g : S → NNReal) : Prop :=
  ∃ φ : Polynomial ℝ, ∀ s : S, (f s : ℝ) ≤ φ.eval (g s : ℝ)

/-- Expanding `f.PolynomiallyBoundedBy g` gives the witness polynomial and the pointwise bound. -/
theorem polynomiallyBoundedBy_iff
    {S : Type u} {f g : S → NNReal} :
    f.PolynomiallyBoundedBy g ↔
      ∃ φ : Polynomial ℝ, ∀ s : S, (f s : ℝ) ≤ φ.eval (g s : ℝ) :=
  Iff.rfl

namespace PolynomiallyBoundedBy

/-- Precomposing the domain by `u` preserves polynomial boundedness by the transported control
function. -/
theorem comp_right
    {S : Type u} {T : Type v} {f g : S → NNReal}
    (hfg : f.PolynomiallyBoundedBy g) (u : T → S) :
    (f ∘ u).PolynomiallyBoundedBy (g ∘ u) := by
  rcases hfg with ⟨φ, hφ⟩
  exact ⟨φ, fun t ↦ hφ (u t)⟩

end PolynomiallyBoundedBy

end Function

end
