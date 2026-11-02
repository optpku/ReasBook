import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_5.ch5_sec5_1_5_definition_5_1_5_extra_1

open scoped IntegerVectorNotation Matrix

-- Semantic recall note: the mixed-space owner layer is already established in Chapter 4 via
-- `MixedRealPoint`, `mixed_integer_points`, and `mixed_linear_objective`, and the MIR owner is
-- already established in Chapter 5.1.5. This file therefore keeps only the source-facing
-- Exercise 5.6 set and reuses those canonical owners directly.

section Exercise56

variable {n p : ℕ}

/-- The mixed-integer set
`S = {(x, y) ∈ ℤ^n × ℝ^p | c x + g y ≤ b + α x_k, c x + g y ≤ b + β (1 - x_k)}`
from Exercise 5.6, embedded in `ℝ^n × ℝ^p`. -/
def exercise_5_6_set
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n) : Set (MixedRealPoint n p) :=
  mixed_integer_points
    {xy | mixed_linear_objective c g xy ≤ b + alpha * xy.1 k ∧
      mixed_linear_objective c g xy ≤ b + beta * (1 - xy.1 k)}

/-- Membership in `exercise_5_6_set c g b alpha beta k` unfolds to integrality of the `x`
coordinates and the two defining linear inequalities. -/
theorem mem_exercise_5_6_set_iff
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_6_set c g b alpha beta k ↔
      xy.1 ∈ ℤ^n ∧
        mixed_linear_objective c g xy ≤ b + alpha * xy.1 k ∧
          mixed_linear_objective c g xy ≤ b + beta * (1 - xy.1 k) := by
  rw [exercise_5_6_set, mem_mixed_integer_points_iff, mem_mixed_integer_lattice_iff]
  simp [and_assoc, and_comm]

/-- The canonical flattened image of `exercise_5_6_set c g b alpha beta k` in `ℝ^(n + p)`,
used by the MIR owner `is_mixed_integer_rounding_inequality`. -/
def exercise_5_6_flat_set
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n) : Set (Fin (n + p) → ℝ) :=
  (Fin.appendEquiv n p) '' exercise_5_6_set c g b alpha beta k

/-- Membership in `exercise_5_6_flat_set c g b alpha beta k` is equivalent to membership of the
unflattened point in the source-facing mixed-space set from Exercise 5.6. -/
theorem mem_exercise_5_6_flat_set_iff
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (u : Fin (n + p) → ℝ) :
    u ∈ exercise_5_6_flat_set c g b alpha beta k ↔
      (Fin.appendEquiv n p).symm u ∈ exercise_5_6_set c g b alpha beta k := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    simpa using hxy
  · intro hu
    refine ⟨(Fin.appendEquiv n p).symm u, hu, ?_⟩
    simpa using (Fin.appendEquiv n p).apply_symm_apply u

/-- Helper for Exercise 5.6: evaluating the flattened objective `Fin.append c g` on the
flattening of a mixed point recovers the source-facing mixed linear objective. -/
lemma exercise_5_6_flat_objective_eq_mixed_linear_objective
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (xy : MixedRealPoint n p) :
    (Fin.append c g) ⬝ᵥ Fin.appendEquiv n p xy = mixed_linear_objective c g xy := by
  -- Flattening concatenates the integer and continuous blocks, so the dot product splits.
  simp [mixed_linear_objective_def, dotProduct, Fin.appendEquiv, Fin.append, Fin.sum_univ_add]

/-- Helper for Exercise 5.6: an integer-valued real lies either at or below `0`, or at least at
`1`. -/
lemma realInt_nonpos_or_one_le
    {r : ℝ}
    (hr : r ∈ Set.range (Int.cast : ℤ → ℝ)) :
    r ≤ 0 ∨ 1 ≤ r := by
  rcases hr with ⟨z, rfl⟩
  by_cases hz : z ≤ 0
  · -- Nonpositive integers stay nonpositive after coercion to `ℝ`.
    left
    exact_mod_cast hz
  · -- Any integer that is not `≤ 0` is at least `1`.
    right
    have hz' : 1 ≤ z := by
      omega
    exact_mod_cast hz'

/-- Helper for Exercise 5.6: every point of `exercise_5_6_set c g b alpha beta k` satisfies the
base inequality `c x + g y ≤ b` once the distinguished coordinate is integral. -/
lemma exercise_5_6_cut_valid_on_set
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    {xy : MixedRealPoint n p}
    (hxy : xy ∈ exercise_5_6_set c g b alpha beta k) :
    mixed_linear_objective c g xy ≤ b := by
  rcases (mem_exercise_5_6_set_iff c g b alpha beta k xy).mp hxy with
    ⟨hxInt, hleft, hright⟩
  rw [mem_integerVectors_iff_forall] at hxInt
  have hkInt : xy.1 k ∈ Set.range (Int.cast : ℤ → ℝ) := hxInt k
  rcases realInt_nonpos_or_one_le hkInt with hnonpos | hone
  · -- If `x_k ≤ 0`, the first branch inequality already dominates `b`.
    have halpha_term : alpha * xy.1 k ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos halpha.le hnonpos
    linarith
  · -- If `1 ≤ x_k`, then `1 - x_k ≤ 0`, so the second branch inequality dominates `b`.
    have hone_minus : 1 - xy.1 k ≤ 0 := by
      linarith
    have hbeta_term : beta * (1 - xy.1 k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hbeta.le hone_minus
    linarith

/-- Helper for Exercise 5.6: the flattened inequality `(Fin.append c g) ⬝ᵥ u ≤ b` is valid on
the canonical flat image of the Exercise 5.6 mixed set. -/
lemma exercise_5_6_cut_valid_on_flat_set
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta)
    {u : Fin (n + p) → ℝ}
    (hu : u ∈ exercise_5_6_flat_set c g b alpha beta k) :
    (Fin.append c g) ⬝ᵥ u ≤ b := by
  have hsource :
      mixed_linear_objective c g ((Fin.appendEquiv n p).symm u) ≤ b :=
    exercise_5_6_cut_valid_on_set c g b alpha beta k halpha hbeta <|
      (mem_exercise_5_6_flat_set_iff c g b alpha beta k u).mp hu
  have hrewrite :
      (Fin.append c g) ⬝ᵥ u =
        mixed_linear_objective c g ((Fin.appendEquiv n p).symm u) := by
    -- Rewrite the flat objective through the canonical unflattening map once.
    calc
      (Fin.append c g) ⬝ᵥ u =
          (Fin.append c g) ⬝ᵥ Fin.appendEquiv n p ((Fin.appendEquiv n p).symm u) := by
            rw [(Fin.appendEquiv n p).apply_symm_apply u]
      _ = mixed_linear_objective c g ((Fin.appendEquiv n p).symm u) :=
            exercise_5_6_flat_objective_eq_mixed_linear_objective
              c g ((Fin.appendEquiv n p).symm u)
  rw [hrewrite]
  exact hsource

/-- Exercise 5.6. Let `c ∈ ℝ^n`, `g ∈ ℝ^p`, `b ∈ ℝ`, and
`S = {(x, y) ∈ ℤ^n × ℝ^p | c x + g y ≤ b + α x_k, c x + g y ≤ b + β (1 - x_k)}`
with `k : Fin n` encoding the source condition `1 ≤ k ≤ n` and `α, β > 0`. Then the inequality
`c x + g y ≤ b` is a mixed integer rounding inequality for `S`. -/
theorem exercise_5_6_cut_is_mixed_integer_rounding
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta) :
    is_mixed_integer_rounding_inequality
      (Set.range (Fin.castAdd p))
      (exercise_5_6_flat_set c g b alpha beta k)
      (Fin.append c g)
      b := by
  refine ⟨fun _ ↦ 0, Fin.append c g, b, 0, ?_, ?_, ?_, ?_, ?_⟩
  · -- The zero split row is supported on every integer-coordinate set.
    intro j hj
    rfl
  · intro u hu
    have hvalid :
        (Fin.append c g) ⬝ᵥ u ≤ b :=
      exercise_5_6_cut_valid_on_flat_set c g b alpha beta k halpha hbeta hu
    -- Route correction: with `π = 0`, the first MIR witness inequality is just `c u ≤ b`.
    have hzeroDot : (fun i : Fin (n + p) ↦ ((0 : ℤ) : ℝ)) ⬝ᵥ u = 0 := by
      simp [dotProduct]
    rw [hzeroDot]
    linarith
  · intro u hu
    -- The second MIR witness inequality is the same flat validity statement.
    exact exercise_5_6_cut_valid_on_flat_set c g b alpha beta k halpha hbeta hu
  · -- The MIR coefficient formula collapses to the original flat objective vector.
    ext i
    simp
  · -- The MIR right-hand side formula collapses to `b`.
    simp

end Exercise56
