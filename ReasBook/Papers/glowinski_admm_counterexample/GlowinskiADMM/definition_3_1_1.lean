module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ImageReduction

@[expose] public section

variable {n₁ n₂ m : ℕ}

/- Definition 3.1.1. Put `q = A.mulVec x`, `v = B.mulVec y - b`, and
`u = β⁻¹ • λ`.
The functions `ADMM.ImageReduction.fiberInf` and
`ADMM.ImageReduction.shiftedFiberInf` are the image objectives on the fibers
`A.mulVec x = q` and `B.mulVec y - b = v`, respectively. Their β-scaled Fenchel
biconjugates are `ADMM.ImageReduction.reducedFirst` and
`ADMM.ImageReduction.reducedSecond`; biconjugation is needed because an image
objective need not be closed. -/
#check (ADMM.ImageReduction.fiberInf :
  ((Fin n₁ → ℝ) → EReal) → Matrix (Fin m) (Fin n₁) ℝ →
    (Fin m → ℝ) → EReal)
#check (ADMM.ImageReduction.fiberInf_apply :
  ∀ (φ : (Fin n₁ → ℝ) → EReal) (L : Matrix (Fin m) (Fin n₁) ℝ)
      (q : Fin m → ℝ),
    ADMM.ImageReduction.fiberInf φ L q =
      sInf {r : EReal | ∃ x, L.mulVec x = q ∧ r = φ x})
#check (ADMM.ImageReduction.shiftedFiberInf :
  ((Fin n₂ → ℝ) → EReal) → Matrix (Fin m) (Fin n₂) ℝ →
    (Fin m → ℝ) → (Fin m → ℝ) → EReal)
#check (ADMM.ImageReduction.shiftedFiberInf_apply :
  ∀ (φ : (Fin n₂ → ℝ) → EReal) (L : Matrix (Fin m) (Fin n₂) ℝ)
      (b v : Fin m → ℝ),
    ADMM.ImageReduction.shiftedFiberInf φ L b v =
      sInf {r : EReal | ∃ y, L.mulVec y - b = v ∧ r = φ y})
#check (ADMM.ImageReduction.reducedFirst :
  ((Fin n₁ → ℝ) → EReal) → Matrix (Fin m) (Fin n₁) ℝ → ℝ →
    (Fin m → ℝ) → EReal)
#check (ADMM.ImageReduction.reducedFirst_apply :
  ∀ (f : (Fin n₁ → ℝ) → EReal) (A : Matrix (Fin m) (Fin n₁) ℝ)
      (β : ℝ) (q : Fin m → ℝ),
    ADMM.ImageReduction.reducedFirst f A β q =
      ERealConvex.fenchelBiconjugate (ADMM.ImageReduction.fiberInf f A) q /
        (β : EReal))
#check (ADMM.ImageReduction.reducedSecond :
  ((Fin n₂ → ℝ) → EReal) → Matrix (Fin m) (Fin n₂) ℝ →
    (Fin m → ℝ) → ℝ → (Fin m → ℝ) → EReal)
#check (ADMM.ImageReduction.reducedSecond_apply :
  ∀ (g : (Fin n₂ → ℝ) → EReal) (B : Matrix (Fin m) (Fin n₂) ℝ)
      (b : Fin m → ℝ) (β : ℝ) (v : Fin m → ℝ),
    ADMM.ImageReduction.reducedSecond g B b β v =
      ERealConvex.fenchelBiconjugate
          (ADMM.ImageReduction.shiftedFiberInf g B b) v /
        (β : EReal))
