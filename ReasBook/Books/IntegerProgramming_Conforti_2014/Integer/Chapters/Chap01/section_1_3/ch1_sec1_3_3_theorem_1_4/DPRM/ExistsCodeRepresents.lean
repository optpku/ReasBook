/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.ExistsCode
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.PolyBridge

/-!
# Coding a polynomial that represents a relation

Issue #11, compatibility half: the one statement that needs `RepresentsNat` from #5, kept
in its own module so that `Hilbert10.ExistsCode` genuinely does not depend on the
`Poly`/`MvPolynomial` bridge — a fact about the import graph, not a claim in prose. That
separation is why `ExistsCode` could be promoted (#50) while this module, which needs the
staged `PolyBridge`, could not.
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

open MvPolynomial

variable {n m : ℕ}

/-- If a polynomial represents a relation, some code has that relation as its natural-root
condition, with inputs in the first `n` slots and witnesses in the next `m`. -/
theorem exists_code_representsNat {R : (Fin n → ℕ) → Prop}
    {p : MvPolynomial (Fin n ⊕ Fin m) ℤ} (hp : RepresentsNat p R) :
    ∃ q : PolynomialCode, q.arity ≤ n + m ∧
      ∀ x : Fin n → ℕ, R x ↔ ∃ y : Fin m → ℕ, q.eval (List.ofFn x ++ List.ofFn y) = 0 := by
  obtain ⟨q, harity, hden⟩ := exists_code p
  refine ⟨q, harity, fun x => ?_⟩
  rw [hp x]
  exact exists_congr fun y => by rw [eval_exists_code hden x y]

end PolynomialCode

end Hilbert10
