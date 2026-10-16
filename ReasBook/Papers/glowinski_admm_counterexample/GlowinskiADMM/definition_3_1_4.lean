module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.Certificate

@[expose] public section

/-
Definition 3.1.4: An ADMM finite-memory certificate consists of its nonnegative
lag weights, positive parameters, signed-value storage, and the descent and lower
finite positive-semidefiniteness tests, including all directed origin gaps.
-/
#check (ADMM.FiniteMemory.Certificate : (ℓ : ℕ) → (γ : ℝ) → Type)
#check ADMM.FiniteMemory.supply
#check ADMM.FiniteMemory.storage
