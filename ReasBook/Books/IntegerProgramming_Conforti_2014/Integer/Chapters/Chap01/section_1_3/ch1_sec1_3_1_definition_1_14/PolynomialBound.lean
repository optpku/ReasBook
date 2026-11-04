/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Real.Basic

@[expose] public section

universe u v

namespace Function

/-- Definition 1.14. Let `S` be a type, let `f : S → ℝ`, and let
`g : Fin t → S → ℝ` encode the finite family `g₁, ..., g_t : S → ℝ`. The function `f` is
polynomially bounded by `g` if there exists a real multivariate polynomial in `t` variables whose
pointwise evaluation dominates `f`. -/
def PolynomiallyBoundedByFamily {S : Type u} {t : ℕ} (f : S → ℝ) (g : Fin t → S → ℝ) : Prop :=
  ∃ φ : MvPolynomial (Fin t) ℝ, ∀ s, f s ≤ MvPolynomial.eval (fun i ↦ g i s) φ

/-- Expanding `f.PolynomiallyBoundedByFamily g` gives a witness polynomial and the corresponding
pointwise domination inequality. -/
theorem polynomiallyBoundedByFamily_iff {S : Type u} {t : ℕ} {f : S → ℝ} {g : Fin t → S → ℝ} :
    f.PolynomiallyBoundedByFamily g ↔
      ∃ φ : MvPolynomial (Fin t) ℝ, ∀ s, f s ≤ MvPolynomial.eval (fun i ↦ g i s) φ :=
  Iff.rfl

namespace PolynomiallyBoundedByFamily

/-- Precomposing the domain by `u` preserves polynomial boundedness by the transported family of
controlling functions. -/
theorem comp_right {S : Type u} {T : Type v} {t : ℕ} {f : S → ℝ} {g : Fin t → S → ℝ}
    (hfg : f.PolynomiallyBoundedByFamily g) (u : T → S) :
    (f ∘ u).PolynomiallyBoundedByFamily (fun i ↦ g i ∘ u) := by
  rcases hfg with ⟨φ, hφ⟩
  exact ⟨φ, fun s ↦ hφ (u s)⟩

end PolynomiallyBoundedByFamily

end Function

end
