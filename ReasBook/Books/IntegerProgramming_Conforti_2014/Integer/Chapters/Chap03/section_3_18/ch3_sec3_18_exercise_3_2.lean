import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_4

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

variable {𝕜 : Type*}

section

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Helper for Exercise 3.2: a coordinatewise strict solution of `A *ᵥ x` can be rescaled to
satisfy `A *ᵥ y ≤ -1` coordinatewise. -/
lemma exists_mulVec_le_neg_one_of_exists_mulVec_lt_zero
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜} :
    (∃ x : Fin n → 𝕜, ∀ i : Fin m, (A *ᵥ x) i < 0) →
      ∃ y : Fin n → 𝕜, A *ᵥ y ≤ (-1 : Fin m → 𝕜) := by
  rintro ⟨x, hx⟩
  let t : 𝕜 := ∑ i, 1 / (-(A *ᵥ x) i)
  refine ⟨t • x, ?_⟩
  intro i
  -- Each reciprocal term is dominated by the sum `t`.
  have hterm_le : 1 / (-(A *ᵥ x) i) ≤ t := by
    dsimp [t]
    exact Finset.single_le_sum
      (fun j _ ↦ one_div_nonneg.mpr <| neg_nonneg.mpr <| le_of_lt <| hx j)
      (Finset.mem_univ i)
  -- The strict negativity hypothesis makes the denominator positive.
  have hdenom_pos : 0 < -(A *ᵥ x) i := by
    linarith [hx i]
  have hmul :
      (1 / (-(A *ᵥ x) i)) * (-(A *ᵥ x) i) ≤ t * (-(A *ᵥ x) i) :=
    mul_le_mul_of_nonneg_right hterm_le hdenom_pos.le
  have hone : (1 / (-(A *ᵥ x) i)) * (-(A *ᵥ x) i) = 1 := by
    rw [one_div, inv_mul_cancel₀ hdenom_pos.ne']
  have hge : 1 ≤ t * (-(A *ᵥ x) i) := by
    rw [hone] at hmul
    exact hmul
  have hbound : t * (A *ᵥ x) i ≤ -1 := by
    nlinarith
  -- Rewriting the scaled matrix-vector product finishes the coordinatewise bound.
  calc
    (A *ᵥ (t • x)) i = t * (A *ᵥ x) i := by
      rw [Matrix.mulVec_smul]
      simp
    _ ≤ -1 := hbound

/-- Helper for Exercise 3.2: a Farkas certificate for right-hand side `-1` has positive mass on
the constant-one vector. -/
lemma farkas_certificate_neg_one_dot_one_pos
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜} {u : Fin m → 𝕜} :
    IsFarkasCertificate A (-1 : Fin m → 𝕜) u → 0 < u ⬝ᵥ (1 : Fin m → 𝕜) := by
  intro hcert
  -- Rewriting against the constant `-1` vector reduces the claim to the certificate inequality.
  have hdot : u ⬝ᵥ (-1 : Fin m → 𝕜) = -(u ⬝ᵥ (1 : Fin m → 𝕜)) := by
    simp
  nlinarith [hcert.negative_rhs, hdot]

/-- Helper for Exercise 3.2: a Farkas certificate for right-hand side `-1` normalizes to a
solution of the normalized nonnegative left-kernel system. -/
lemma exists_isFarkasCertificate_neg_one_iff_exists_normalized_nonnegative_left_kernel
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜} :
    (∃ u : Fin m → 𝕜, IsFarkasCertificate A (-1 : Fin m → 𝕜) u) ↔
      ∃ u : Fin m → 𝕜, u ᵥ* A = 0 ∧ 0 ≤ u ∧ u ⬝ᵥ (1 : Fin m → 𝕜) = 1 := by
  constructor
  · rintro ⟨u, hcert⟩
    let v : Fin m → 𝕜 := (u ⬝ᵥ (1 : Fin m → 𝕜))⁻¹ • u
    have hpos : 0 < u ⬝ᵥ (1 : Fin m → 𝕜) :=
      farkas_certificate_neg_one_dot_one_pos hcert
    have hkernel : v ᵥ* A = 0 := by
      -- Scaling preserves the left-kernel equation.
      dsimp [v]
      rw [Matrix.smul_vecMul, hcert.annihilates, smul_zero]
    have hnonneg : 0 ≤ v := by
      -- The normalization factor is nonnegative, so nonnegativity is preserved pointwise.
      intro i
      dsimp [v]
      exact smul_nonneg (inv_nonneg.mpr hpos.le) (hcert.nonneg i)
    have hnorm : v ⬝ᵥ (1 : Fin m → 𝕜) = 1 := by
      -- The normalization factor is chosen so that the dot product with `1` becomes exactly `1`.
      dsimp [v]
      rw [smul_dotProduct]
      simpa [smul_eq_mul] using inv_mul_cancel₀ hpos.ne'
    exact ⟨v, hkernel, hnonneg, hnorm⟩
  · rintro ⟨u, hkernel, hnonneg, hnorm⟩
    refine ⟨u, ⟨hnonneg, hkernel, ?_⟩⟩
    -- The normalization equation turns the dot product against `-1` into `-1`.
    have hdot : u ⬝ᵥ (-1 : Fin m → 𝕜) = -(u ⬝ᵥ (1 : Fin m → 𝕜)) := by
      simp
    rw [hdot, hnorm]
    norm_num

/-- Helper for Exercise 3.2: the coordinatewise strict system `A *ᵥ x < 0` is feasible exactly
when the scaled system `A *ᵥ y ≤ -1` is feasible. -/
lemma exists_mulVec_lt_zero_iff_exists_mulVec_le_neg_one
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜} :
    (∃ x : Fin n → 𝕜, ∀ i : Fin m, (A *ᵥ x) i < 0) ↔
      ∃ y : Fin n → 𝕜, A *ᵥ y ≤ (-1 : Fin m → 𝕜) := by
  constructor
  · exact exists_mulVec_le_neg_one_of_exists_mulVec_lt_zero
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    intro i
    exact lt_of_le_of_lt (hy i) (by norm_num)

/-- Exercise 3.2. For an `m × n` matrix `A`, the coordinatewise strict system
`∀ i, (A *ᵥ x) i < 0` is feasible if and only if the normalized nonnegative left-kernel system
`u ᵥ* A = 0`, `0 ≤ u`, and `u ⬝ᵥ (1 : Fin m → 𝕜) = 1` is infeasible. -/
theorem strict_linear_system_feasible_iff_normalized_nonnegative_left_kernel_infeasible
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    (∃ x : Fin n → 𝕜, ∀ i : Fin m, (A *ᵥ x) i < 0) ↔
      ¬ ∃ u : Fin m → 𝕜, u ᵥ* A = 0 ∧ 0 ≤ u ∧ u ⬝ᵥ (1 : Fin m → 𝕜) = 1 := by
  classical
  have hstrict :
      (∃ x : Fin n → 𝕜, ∀ i : Fin m, (A *ᵥ x) i < 0) ↔
        ¬ ∃ u : Fin m → 𝕜, IsFarkasCertificate A (-1 : Fin m → 𝕜) u := by
    rw [exists_mulVec_lt_zero_iff_exists_mulVec_le_neg_one]
    constructor
    · intro hy hcert
      exact (farkas_lemma_linear_inequalities A (-1 : Fin m → 𝕜)).mpr hcert hy
    · intro hcert
      by_contra hy
      exact hcert ((farkas_lemma_linear_inequalities A (-1 : Fin m → 𝕜)).mp hy)
  have hnormalized :
      (¬ ∃ u : Fin m → 𝕜, IsFarkasCertificate A (-1 : Fin m → 𝕜) u) ↔
        ¬ ∃ u : Fin m → 𝕜, u ᵥ* A = 0 ∧ 0 ≤ u ∧ u ⬝ᵥ (1 : Fin m → 𝕜) = 1 :=
    not_congr exists_isFarkasCertificate_neg_one_iff_exists_normalized_nonnegative_left_kernel
  exact hstrict.trans hnormalized

end
