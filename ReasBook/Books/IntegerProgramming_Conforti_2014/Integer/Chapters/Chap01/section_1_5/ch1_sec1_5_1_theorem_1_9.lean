/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_remark_5_1
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_1

public section

open scoped IntegerVectorNotation Matrix

namespace PureIntegerHalfspace

variable {n : ℕ}

/-- The pure-integer one-row halfspace
`{x ∈ ℤ^n | (fun i ↦ (a i : ℝ)) ⬝ᵥ x ≤ c}` attached to the integer row `a` and right-hand side
`c`. -/
def set
    (a : Fin n → ℤ)
    (c : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ ℤ^n ∧ (fun i ↦ (a i : ℝ)) ⬝ᵥ x ≤ c}

/-- Membership in `set a c` means belonging to `ℤ^n` and satisfying the defining one-row
inequality. -/
theorem mem_set_iff
    (a : Fin n → ℤ)
    (c : ℝ)
    (x : Fin n → ℝ) :
    x ∈ set a c ↔ x ∈ ℤ^n ∧ (fun i ↦ (a i : ℝ)) ⬝ᵥ x ≤ c := by
  -- Unfolding `set` exposes exactly the conjunction in the statement.
  rfl

/-- The gcd of the coordinate absolute values of the integer row `a`. -/
def coefficientGcd
    (a : Fin n → ℤ) : ℕ :=
  Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (a i))

/-- The gcd-normalized integer row `a' = a / coefficientGcd a`. -/
def normalizedCoefficients
    (a : Fin n → ℤ) : Fin n → ℤ :=
  fun i ↦ a i / coefficientGcd a

/-- The rounded halfspace
`{x ∈ ℝ^n | (fun i ↦ (normalizedCoefficients a i : ℝ)) ⬝ᵥ x ≤ ⌊c / coefficientGcd a⌋}`. -/
def roundedHalfspace
    (a : Fin n → ℤ)
    (c : ℝ) : Set (Fin n → ℝ) :=
  {x |
    (fun i ↦ (normalizedCoefficients a i : ℝ)) ⬝ᵥ x ≤
      (Int.floor (c / coefficientGcd a) : ℝ)}

/-- Membership in `roundedHalfspace a c` means satisfying the normalized rounded inequality. -/
theorem mem_roundedHalfspace_iff
    (a : Fin n → ℤ)
    (c : ℝ)
    (x : Fin n → ℝ) :
    x ∈ roundedHalfspace a c ↔
      (fun i ↦ (normalizedCoefficients a i : ℝ)) ⬝ᵥ x ≤
        (Int.floor (c / coefficientGcd a) : ℝ) := by
  -- Unfolding `roundedHalfspace` gives the defining normalized inequality.
  rfl

/-- Theorem 1.9 (1). If `a ∈ ℤ^n \ {0}` and `a' = a / g` with
`g = coefficientGcd a`, then `a'` still has integer coordinates, viewed inside `ℤ^n ⊆ ℝ^n`. -/
theorem normalizedCoefficients_mem_integerVectors
    (a : Fin n → ℤ)
    (ha_nonzero : a ≠ 0) :
    (fun i ↦ (normalizedCoefficients a i : ℝ)) ∈ ℤ^n := by
  -- The normalized coefficient vector is already integer-valued before casting to `ℝ`.
  exact (mem_integerVectors_iff).2 ⟨normalizedCoefficients a, rfl⟩

/-- Theorem 1.9 (2). Let `S = {x ∈ ℤ^n | (fun i ↦ (a i : ℝ)) ⬝ᵥ x ≤ c}` for
`a ∈ ℤ^n \ {0}` and `c ∈ ℝ`, let `g = coefficientGcd a`, and let `a' = a / g`. Then
`convexHull ℝ S` is the rounded halfspace cut out by `a'` with right-hand side `⌊c / g⌋`. -/
theorem convexHull_eq_roundedHalfspace
    (a : Fin n → ℤ)
    (c : ℝ)
    (ha_nonzero : a ≠ 0) :
    convexHull ℝ (set a c) = roundedHalfspace a c := by
  let g := coefficientGcd a
  -- The coordinate gcd is positive for a nonzero coefficient row.
  have hg_pos : 0 < g := by
    simpa [g, coefficientGcd] using coordinate_gcd_pos a ha_nonzero
  -- Normalizing by the gcd produces a primitive coefficient vector.
  have hprimitive :
      Finset.univ.gcd
          (fun j : Fin n ↦ Int.natAbs (normalizedCoefficients a j)) = 1 := by
    simpa [normalizedCoefficients, coefficientGcd] using
      normalized_split_vector_gcd_eq_one a ha_nonzero
  -- The normalized row cannot vanish, or its coordinate gcd would be zero instead of one.
  have hnormalized_nonzero : normalizedCoefficients a ≠ 0 := by
    intro hzero
    have hzero_gcd :
        Finset.univ.gcd
            (fun j : Fin n ↦ Int.natAbs (normalizedCoefficients a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [hzero]
    rw [hzero_gcd] at hprimitive
    exact Nat.zero_ne_one hprimitive
  -- The universal pure-integer case is the `I = Finset.univ` split with zero threshold.
  have hs_zero_on_continuous :
      ∀ j ∈ (Finset.univ : Finset (Fin n))ᶜ, normalizedCoefficients a j = 0 := by
    intro j hj
    simp at hj
  let s : Split Finset.univ :=
    { π := normalizedCoefficients a
      π0 := 0
      nonzero := hnormalized_nonzero
      zero_on_continuous := hs_zero_on_continuous }
  have hs_primitive : s.IsPrimitive := by
    simpa [Split.IsPrimitive, s] using hprimitive
  -- The original row is the gcd times the normalized split row.
  have hscale (x : Fin n → ℝ) :
      (fun i ↦ (a i : ℝ)) ⬝ᵥ x = (g : ℝ) * split_dot s x := by
    simpa [split_dot, dotProduct, g, s, coefficientGcd, normalizedCoefficients] using
      normalized_split_dot_eq_gcd_mul a ha_nonzero x
  -- Rewrite the source-facing set as the canonical primitive mixed-integer halfspace.
  have hleft :
      set a c =
        {x : Fin n → ℝ |
          (∀ j ∈ (Finset.univ : Finset (Fin n)), ∃ z : ℤ, x j = (z : ℝ)) ∧
            split_dot s x ≤ c / g} := by
    ext x
    constructor
    · intro hx
      rcases (mem_set_iff a c x).1 hx with ⟨hx_int, hx_le⟩
      refine ⟨?_, ?_⟩
      · rw [mem_integerVectors_iff_forall] at hx_int
        intro j hj
        rcases hx_int j with ⟨z, hz⟩
        exact ⟨z, hz.symm⟩
      · have hg_real_pos : (0 : ℝ) < g := by
          exact_mod_cast hg_pos
        rw [hscale x] at hx_le
        exact (le_div_iff₀ hg_real_pos).2 (by simpa [mul_comm] using hx_le)
    · intro hx
      rcases hx with ⟨hx_int, hx_le⟩
      refine (mem_set_iff a c x).2 ?_
      refine ⟨?_, ?_⟩
      · rw [mem_integerVectors_iff_forall]
        intro j
        rcases hx_int j (by simp) with ⟨z, hz⟩
        exact ⟨z, hz.symm⟩
      · have hg_real_pos : (0 : ℝ) < g := by
          exact_mod_cast hg_pos
        rw [hscale x]
        have hmul : split_dot s x * g ≤ c := (le_div_iff₀ hg_real_pos).1 hx_le
        simpa [mul_comm] using hmul
  -- Apply the canonical primitive rounded-halfspace hull theorem and unfold back to the target.
  calc
    convexHull ℝ (set a c)
        = convexHull ℝ {x : Fin n → ℝ |
            (∀ j ∈ (Finset.univ : Finset (Fin n)), ∃ z : ℤ, x j = (z : ℝ)) ∧
              split_dot s x ≤ c / g} := by
            rw [hleft]
    _ = {x : Fin n → ℝ | split_dot s x ≤ (Int.floor (c / g) : ℝ)} := by
      simpa using
        convexHull_mixed_integer_halfspace_eq_rounded_halfspace_of_relatively_prime_coefficients
          Finset.univ s (c / g) hs_primitive
    _ = roundedHalfspace a c := by
      ext x
      simp [roundedHalfspace, split_dot, dotProduct, g, s]

end PureIntegerHalfspace

end
