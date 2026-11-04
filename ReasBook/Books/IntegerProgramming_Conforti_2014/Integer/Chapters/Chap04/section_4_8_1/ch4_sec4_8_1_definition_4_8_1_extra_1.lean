/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_29
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tooling requested by the statement policy was unavailable in this environment:
-- `tool_search` exposed no Lean search tool such as `lean_leansearch`, so this file follows the
-- local Chapter 4 precedent of using `Fin (n + 1) → ℝ` together with `convexHull ℝ`.

section Definition481Extra1

variable {n : ℕ}

/-- Definition 4.8.1-extra-1 (1). The mixing set associated with rational data
`b₁, …, bₙ` is the mixed-integer subset of `ℝ^(n+1)` consisting of vectors
`(x₀, …, xₙ)` with `x₀ ≥ 0`, tail in `integerVectors n`, and
`x₀ + x_t ≥ b_t` for `t = 1, …, n`. -/
def mixingSet (b : Fin n → ℚ) : Set (Fin (n + 1) → ℝ) :=
  {x |
    0 ≤ x 0 ∧
      (fun t : Fin n ↦ x t.succ) ∈ integerVectors n ∧
      ∀ t : Fin n, (b t : ℝ) ≤ x 0 + x t.succ}

/-- Membership in `mixingSet b` is exactly nonnegativity of the zeroth coordinate, integrality of
the tail vector, and the mixing inequalities. -/
theorem mem_mixingSet_iff {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ} :
    x ∈ mixingSet b ↔
      0 ≤ x 0 ∧
        (fun t : Fin n ↦ x t.succ) ∈ integerVectors n ∧
        ∀ t : Fin n, (b t : ℝ) ≤ x 0 + x t.succ := by
  rfl

/-- Membership in `mixingSet b` is exactly the coordinatewise nonnegativity, integrality, and
mixing inequalities from the source definition. -/
theorem mem_mixingSet_iff_forall {b : Fin n → ℚ} {x : Fin (n + 1) → ℝ} :
    x ∈ mixingSet b ↔
      0 ≤ x 0 ∧
        (∀ t : Fin n, x t.succ ∈ Set.range (fun z : ℤ ↦ (z : ℝ))) ∧
        ∀ t : Fin n, (b t : ℝ) ≤ x 0 + x t.succ := by
  rw [mem_mixingSet_iff, mem_integerVectors_iff_forall]

/-- Definition 4.8.1-extra-1 (2). The fractional part data `f_t = b_t - ⌊b_t⌋` attached to the
mixing set. -/
noncomputable def mixingFractionalPart (b : Fin n → ℚ) (t : Fin n) : ℝ :=
  Int.fract (b t : ℝ)

/-- The `t`-th mixing fractional part is `Int.fract (b t)`. -/
@[simp] theorem mixingFractionalPart_eq_fract (b : Fin n → ℚ) (t : Fin n) :
    mixingFractionalPart b t = Int.fract (b t : ℝ) := rfl

/-- Definition 4.8.1-extra-1 (3). The extended fractional-part vector has `f₀ = 0` and
`f_t = b_t - ⌊b_t⌋` for `t = 1, …, n`. -/
noncomputable def extendedMixingFractionalPart (b : Fin n → ℚ) : Fin (n + 1) → ℝ :=
  Fin.cases 0 (mixingFractionalPart b)

/-- The zeroth coordinate of the extended fractional-part vector is `0`. -/
@[simp] theorem extendedMixingFractionalPart_zero (b : Fin n → ℚ) :
    extendedMixingFractionalPart b 0 = 0 := rfl

/-- The successor coordinates of the extended fractional-part vector recover the original
fractional parts. -/
@[simp] theorem extendedMixingFractionalPart_succ (b : Fin n → ℚ) (t : Fin n) :
    extendedMixingFractionalPart b t.succ = mixingFractionalPart b t := rfl

/-- Definition 4.8.1-extra-1 (4). The convex hull `P^mix` of the mixing set. -/
def mixingHull (b : Fin n → ℚ) : Set (Fin (n + 1) → ℝ) :=
  convexHull ℝ (mixingSet b)

/-
Definition 4.8.1-extra-1 (5), owner form: the linear relaxation
`P = {x ∈ ℝ^(n+1) | x₀ ≥ 0, x₀ + x_t ≥ b_t for t = 1, …, n}` is the Exercise 3.29 polyhedron
specialized to the real coercion of the rational data `b`.
-/
recall exercise_3_29_polyhedron
recall mem_exercise_3_29_polyhedron_iff

/-
Definition 4.8.1-extra-1 (6), owner form: the distinguished vectors `r⁰, …, rⁿ` used for the
extreme rays of the recession cone are the Exercise 3.29 generators `exercise_3_29_ray`.
-/
recall exercise_3_29_ray
recall exercise_3_29_ray_apply

/-- Helper for Definition 4.8.1-extra-1: the coordinate vector with zeroth entry `0` and
successor entries given by ceilings of `b` belongs to the mixing set. -/
lemma ceiling_witness_mem_mixingSet (b : Fin n → ℚ) :
    (fun i : Fin (n + 1) ↦ Fin.cases 0 (fun t : Fin n ↦ (⌈b t⌉ : ℝ)) i) ∈ mixingSet b := by
  rw [mem_mixingSet_iff]
  refine ⟨by simp, ?_, ?_⟩
  · rw [mem_integerVectors_iff_forall]
    intro t
    exact ⟨⌈b t⌉, by simp⟩
  · intro t
    have hceil : ((b t : ℚ) : ℝ) ≤ (⌈b t⌉ : ℝ) := by
      exact_mod_cast Int.le_ceil (b t)
    simpa using hceil

/-- Definition 4.8.1-extra-1 (7). The mixing set is nonempty. -/
theorem mixingSet_nonempty (b : Fin n → ℚ) :
    (mixingSet b).Nonempty := by
  exact ⟨fun i : Fin (n + 1) ↦ Fin.cases 0 (fun t : Fin n ↦ (⌈b t⌉ : ℝ)) i,
    ceiling_witness_mem_mixingSet b⟩

end Definition481Extra1
