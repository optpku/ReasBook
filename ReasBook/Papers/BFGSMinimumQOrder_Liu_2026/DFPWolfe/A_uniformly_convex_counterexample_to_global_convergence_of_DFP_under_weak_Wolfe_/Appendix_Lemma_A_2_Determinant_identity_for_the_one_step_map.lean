module

public import ReasLib.Optimization.DFP.InverseUpdate.Determinant

open scoped Matrix

universe u

/- Appendix Lemma A.2 (Determinant identity for the one-step map): the exact
inverse-form DFP update satisfies `det H₊ = det H * ((s ⬝ᵥ y) / (y ⬝ᵥ (H *ᵥ y)))`. -/
#check (Matrix.det_inverseDFPUpdate :
  ∀ {n : Type u} [Fintype n] [DecidableEq n] {H : Matrix n n ℝ} {s y : n → ℝ},
    H.PosDef → 0 < s ⬝ᵥ y →
      (Matrix.inverseDFPUpdate H s y).det =
        H.det * ((s ⬝ᵥ y) / (y ⬝ᵥ (H *ᵥ y))))
