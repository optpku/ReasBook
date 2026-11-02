module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_22

public section

variable {m n p : ℕ}

/-
Definition 1.29 [Mixed integer linear set]. The source notion
`{(x, y) ∈ ℤ_+^n × ℝ_+^p | A x + G y ≤ b}` with rational data `A`, `G`, and `b` is
formalized by the existing owner `rationalMixedIntegerLinearSet`. Its set-builder semantics are
exposed by the canonical membership theorem below.
-/

#check
  (rationalMixedIntegerLinearSet :
    Matrix (Fin m) (Fin n) ℚ →
      Matrix (Fin m) (Fin p) ℚ → (Fin m → ℚ) → Set (MixedRealPoint n p))
#check
  (mem_rationalMixedIntegerLinearSet_iff :
    ∀ {A : Matrix (Fin m) (Fin n) ℚ} {G : Matrix (Fin m) (Fin p) ℚ} {b : Fin m → ℚ}
      {xy : MixedRealPoint n p},
      xy ∈ rationalMixedIntegerLinearSet A G b ↔
        (Matrix.mulVec (A.map (Rat.castHom ℝ)) xy.1 +
            Matrix.mulVec (G.map (Rat.castHom ℝ)) xy.2 ≤
            fun i ↦ (b i : ℝ)) ∧
          0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ ∀ j : Fin n, ∃ z : ℤ, xy.1 j = (z : ℝ))

end
