module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix

public section

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_12.lean`: every linear
functional on a finite coordinate space is a dot product with a vector. -/
private lemma existsDotProductRepresentation
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (f : (ι → R) →ₗ[R] R) :
    ∃ u : ι → R, ∀ x : ι → R, u ⬝ᵥ x = f x := by
  classical
  -- Take the coordinates of the functional on the canonical coordinate vectors.
  refine ⟨fun i ↦ f (fun j ↦ if i = j then 1 else 0), ?_⟩
  intro x
  -- The canonical-coordinate expansion of `x` identifies the two finite sums.
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [dotProduct, smul_eq_mul, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_12.lean`: membership in the
range of `A.mulVecLin` is solvability of the corresponding matrix equation. -/
private lemma memRangeMulVecLin_iff
    {m n R : Type*} [Fintype n] [CommSemiring R]
    (A : Matrix m n R) (b : m → R) :
    b ∈ LinearMap.range A.mulVecLin ↔ ∃ x : n → R, A *ᵥ x = b := by
  constructor
  · rintro ⟨x, hx⟩
    -- Expose only the application rule for the bundled matrix linear map.
    have hx' : A *ᵥ x = b := by
      simpa only [Matrix.mulVecLin_apply] using hx
    exact ⟨x, hx'⟩
  · rintro ⟨x, hx⟩
    -- Package a solution as the corresponding witness for range membership.
    have hx' : A.mulVecLin x = b := by
      simpa only [Matrix.mulVecLin_apply] using hx
    exact ⟨x, hx'⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_12.lean`: if the dot
product of `u` with every matrix image vanishes, then `u ᵥ* A` is zero. -/
private lemma vecMulVanishesOfDotProductMulVecVanishes
    {m n R : Type*} [Fintype m] [Fintype n] [Semiring R]
    (A : Matrix m n R) (u : m → R)
    (h : ∀ x : n → R, u ⬝ᵥ (A *ᵥ x) = 0) :
    u ᵥ* A = 0 := by
  -- Test the row vector against every vector and reassociate matrix multiplication.
  apply dotProduct_eq_zero
  intro x
  rw [← Matrix.dotProduct_mulVec]
  exact h x

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_12.lean
Theorem 1.12 [Fredholm Alternative]. For a real matrix `A` and right-hand side `b`, the system
`A *ᵥ x = b` is infeasible exactly when there is a row witness `u` with `u ᵥ* A = 0` and
`u ⬝ᵥ b ≠ 0`. -/
theorem fredholmAlternative
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    (¬ ∃ x : Fin n → ℝ, A *ᵥ x = b) ↔
      ∃ u : Fin m → ℝ, u ᵥ* A = 0 ∧ u ⬝ᵥ b ≠ 0 := by
  constructor
  · intro hInfeasible
    -- Regard the infeasible right-hand side as lying outside the range subspace.
    have hbNotMem : b ∉ LinearMap.range A.mulVecLin := by
      intro hbMem
      exact hInfeasible ((memRangeMulVecLin_iff A b).mp hbMem)
    obtain ⟨f, hfb, hRangeKer⟩ := Submodule.exists_le_ker_of_notMem hbNotMem
    obtain ⟨u, hu⟩ := existsDotProductRepresentation f
    refine ⟨u, ?_, ?_⟩
    · -- The separating functional vanishes on every matrix image.
      apply vecMulVanishesOfDotProductMulVecVanishes A u
      intro x
      rw [hu]
      apply LinearMap.mem_ker.mp
      apply hRangeKer
      have hx : A *ᵥ x = A *ᵥ x := rfl
      exact (memRangeMulVecLin_iff A (A *ᵥ x)).mpr ⟨x, hx⟩
    · -- Its nonzero value at `b` becomes the required dot-product certificate.
      rwa [hu]
  · rintro ⟨u, huA, hub⟩ ⟨x, hx⟩
    -- Any alleged solution makes the certificate dot product vanish.
    apply hub
    have hzero : (u ᵥ* A) ⬝ᵥ x = 0 := by
      rw [huA, zero_dotProduct]
    calc
      u ⬝ᵥ b = u ⬝ᵥ (A *ᵥ x) := congrArg (fun y ↦ u ⬝ᵥ y) hx.symm
      _ = (u ᵥ* A) ⬝ᵥ x := Matrix.dotProduct_mulVec u A x
      _ = 0 := hzero

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_9b0734fa8d86c5b72666"
#print axioms _root_.fredholmAlternative
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_9b0734fa8d86c5b72666"
