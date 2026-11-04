/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_remark_4_32
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_1

open scoped BigOperators IntegerVectorNotation

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so the exercise below reuses the existing Chapter 4 mixed-space
-- owners `MixedRealPoint`, `mixed_integer_points`, and `ℤ^n`, together with the canonical
-- Section 3.18 facet owner `IsFacetOf` for the mixed-space conclusion.

section Exercise510

variable {n p : ℕ}

/-- The index set `J⁻ = {j | g_j < 0}` from Exercise 5.10. -/
noncomputable def exercise_5_10_negative_index_set (g : Fin p → ℝ) : Finset (Fin p) :=
  Finset.univ.filter fun j : Fin p ↦ g j < 0

/-- Membership in `exercise_5_10_negative_index_set g` is exactly the inequality `g j < 0`. -/
theorem mem_exercise_5_10_negative_index_set_iff
    (g : Fin p → ℝ) (j : Fin p) :
    j ∈ exercise_5_10_negative_index_set g ↔ g j < 0 := by
  simp [exercise_5_10_negative_index_set]

/-- The mixed-integer set
`S = {(x, y) ∈ ℤ^n × ℝ_+^p | ∑ a_j x_j + ∑ g_j y_j ≤ b}`
from Exercise 5.10, embedded in `ℝ^n × ℝ^p`. -/
def exercise_5_10_mixed_integer_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  mixed_integer_points
    {xy |
      (∀ j : Fin p, 0 ≤ xy.2 j) ∧
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b}

/-- Membership in `exercise_5_10_mixed_integer_set a g b` expands to integer-valued first
coordinates, nonnegative continuous coordinates, and the defining linear inequality. -/
theorem mem_exercise_5_10_mixed_integer_set_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_10_mixed_integer_set a g b ↔
      xy.1 ∈ ℤ^n ∧
        (∀ j : Fin p, 0 ≤ xy.2 j) ∧
          mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b := by
  rw [exercise_5_10_mixed_integer_set, mem_mixed_integer_points_iff, mem_mixed_integer_lattice_iff]
  simp [and_left_comm, and_comm]

/-- The left-hand side of the inequality in Exercise 5.10:
`∑ ⌊a_j⌋ x_j + (1 / (1 - f)) * ∑_{j ∈ J⁻} g_j y_j`.
Since `a_j ∈ ℤ`, the coefficient term is written directly as `a_j`. -/
noncomputable def exercise_5_10_cut_value
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) : ℝ :=
  (∑ j, (a j : ℝ) * xy.1 j) +
    (1 / (1 - Int.fract b)) *
      Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)

/-- Expanding `exercise_5_10_cut_value` recovers the source inequality from Exercise 5.10. -/
theorem exercise_5_10_cut_value_eq
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    exercise_5_10_cut_value a g b xy =
      (∑ j, (a j : ℝ) * xy.1 j) +
        (1 / (1 - Int.fract b)) *
          Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) :=
  rfl

/-- The equality face of `conv(S)` cut out by the Exercise 5.10 inequality. -/
def exercise_5_10_cut_face
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p) :=
  {xy |
    xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
      exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ)}

/-- Membership in `exercise_5_10_cut_face a g b` means lying in `conv(S)` and saturating the
Exercise 5.10 cut inequality. -/
theorem mem_exercise_5_10_cut_face_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_10_cut_face a g b ↔
      xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
        exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) :=
  Iff.rfl

/-- Helper for Exercise 5.10: the negative continuous contribution is nonpositive on the mixed
integer set because every selected coefficient is negative while every continuous coordinate is
nonnegative. -/
lemma negativeContribution_nonpos
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p)
    (hxy : xy ∈ exercise_5_10_mixed_integer_set a g b) :
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) ≤ 0 := by
  rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with ⟨_, hy_nonneg, _⟩
  -- Each selected term has a negative coefficient and a nonnegative variable value.
  refine Finset.sum_nonpos ?_
  intro j hj
  have hj_neg : g j < 0 := (mem_exercise_5_10_negative_index_set_iff g j).1 hj
  exact mul_nonpos_of_nonpos_of_nonneg hj_neg.le (hy_nonneg j)

/-- Helper for Exercise 5.10: removing the nonnegative `g_j y_j` terms can only decrease the
continuous part of the original row inequality. -/
lemma negativeContribution_le_totalContribution
    (g : Fin p → ℝ)
    (xy : MixedRealPoint n p)
    (hy_nonneg : ∀ j : Fin p, 0 ≤ xy.2 j) :
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) ≤
      ∑ j, g j * xy.2 j := by
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ)
      (p := fun j : Fin p ↦ g j < 0)
      (f := fun j : Fin p ↦ g j * xy.2 j)
  let nonnegativeIndexSet : Finset (Fin p) :=
    Finset.univ.filter fun j : Fin p ↦ ¬ g j < 0
  have hrest_nonneg :
      0 ≤ Finset.sum nonnegativeIndexSet (fun j ↦ g j * xy.2 j) := by
    -- The complementary summands come from coefficients `g_j ≥ 0`.
    refine Finset.sum_nonneg ?_
    intro j hj
    have hj_nonneg : 0 ≤ g j := by
      exact le_of_not_gt (Finset.mem_filter.1 hj).2
    exact mul_nonneg hj_nonneg (hy_nonneg j)
  -- Splitting the full sum into the negative and nonnegative blocks isolates the desired bound.
  have hsplit' :
      ∑ j, g j * xy.2 j =
        Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) +
          Finset.sum nonnegativeIndexSet (fun j ↦ g j * xy.2 j) := by
    simpa [exercise_5_10_negative_index_set, nonnegativeIndexSet] using hsplit.symm
  linarith [hsplit', hrest_nonneg]

/-- Helper for Exercise 5.10: once the integer part of the row and the negative slack are
isolated, floor arithmetic turns the original row bound into the mixed cut bound. -/
lemma cutBound_of_integerRowAndNegativeSlack
    (b : ℝ)
    (z : ℤ)
    {s : ℝ}
    (hs_nonpos : s ≤ 0)
    (hsum : (z : ℝ) + s ≤ b) :
    (z : ℝ) + s / (1 - Int.fract b) ≤ (Int.floor b : ℝ) := by
  have hfract_nonneg : 0 ≤ Int.fract b := Int.fract_nonneg b
  have hden_pos : 0 < 1 - Int.fract b := by
    linarith [Int.fract_lt_one b]
  by_cases hzle : z ≤ Int.floor b
  · -- If the integer row is already at most `⌊b⌋`, the negative slack term only helps.
    have hsdiv_nonpos : s / (1 - Int.fract b) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hs_nonpos hden_pos.le
    have hz_real : (z : ℝ) ≤ (Int.floor b : ℝ) := by
      exact_mod_cast hzle
    linarith
  · -- Otherwise the original row bound forces enough negative slack to offset
    -- the excess integer part.
    have hzgt : Int.floor b < z := lt_of_not_ge hzle
    have hzge_real : ((Int.floor b : ℤ) : ℝ) + 1 ≤ (z : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hzgt)
    have hs_upper : s ≤ Int.fract b - ((z : ℝ) - (Int.floor b : ℝ)) := by
      linarith [hsum, Int.floor_add_fract b]
    have hs_scaled :
        s ≤ -((z : ℝ) - (Int.floor b : ℝ)) * (1 - Int.fract b) := by
      nlinarith
        [hs_upper, hfract_nonneg,
          show (0 : ℝ) ≤ (z : ℝ) - (Int.floor b : ℝ) - 1 by linarith]
    have hsdiv :
        s / (1 - Int.fract b) ≤ -((z : ℝ) - (Int.floor b : ℝ)) := by
      exact (div_le_iff₀ hden_pos).2
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hs_scaled)
    linarith

/-- Exercise 5.10 (1). Let
`S = {(x, y) ∈ ℤ^n × ℝ_+^p | ∑ a_j x_j + ∑ g_j y_j ≤ b}` where
`a₁, …, aₙ ∈ ℤ`, `g₁, …, g_p ∈ ℝ`, `f = b - ⌊b⌋`, and `J⁻ = {j | g_j < 0}`. Then
`∑ ⌊a_j⌋ x_j + (1 / (1 - f)) * ∑_{j ∈ J⁻} g_j y_j ≤ ⌊b⌋`
is valid for `S`. The source side condition `b ∉ ℤ` is redundant for validity, so it is omitted
from the Lean statement. -/
theorem exercise_5_10_valid_cut
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p)
    (hxy : xy ∈ exercise_5_10_mixed_integer_set a g b) :
    exercise_5_10_cut_value a g b xy ≤ (Int.floor b : ℝ) := by
  rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with
    ⟨hx_int, hy_nonneg, hrow_bound⟩
  rcases (mem_integerVectors_iff).1 hx_int with ⟨xInt, hx_cast⟩
  let z : ℤ := ∑ j, a j * xInt j
  let s : ℝ := Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
  have hz_row : (z : ℝ) = ∑ j, (a j : ℝ) * xy.1 j := by
    -- The integer block of `xy` is the real coercion of an integer vector.
    calc
      (z : ℝ) = ((∑ j, a j * xInt j : ℤ) : ℝ) := by rfl
      _ = ∑ j, ((a j * xInt j : ℤ) : ℝ) := by simp
      _ = ∑ j, (a j : ℝ) * xy.1 j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hx_cast, Int.cast_mul]
  have hs_nonpos : s ≤ 0 := by
    simpa [s] using negativeContribution_nonpos a g b xy hxy
  have hs_le_total : s ≤ ∑ j, g j * xy.2 j := by
    simpa [s] using negativeContribution_le_totalContribution g xy hy_nonneg
  have hrow_bound' : (∑ j, (a j : ℝ) * xy.1 j) + ∑ j, g j * xy.2 j ≤ b := by
    simpa [mixed_linear_objective, dotProduct] using hrow_bound
  have hreduced_row : (z : ℝ) + s ≤ b := by
    linarith [hrow_bound', hs_le_total, hz_row]
  -- The final step is the scalar floor lemma on the integer row value and the negative slack.
  have hcut :
      (z : ℝ) + s / (1 - Int.fract b) ≤ (Int.floor b : ℝ) :=
    cutBound_of_integerRowAndNegativeSlack b z hs_nonpos hreduced_row
  simpa [exercise_5_10_cut_value, z, s, hz_row, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hcut

/-- Helper for Exercise 5.10: the cut face is nonempty because the primitive integer row `a`
admits a lattice point at level `⌊b⌋`, and setting all continuous coordinates to `0` saturates
the cut. -/
lemma exercise_5_10_cut_face_nonempty
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1) :
    (exercise_5_10_cut_face a g b).Nonempty := by
  have ha_nonzero : a ≠ 0 := by
    intro ha_zero
    have hgcd_zero :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [ha_zero]
    rw [hgcd_zero] at ha_relatively_prime
    exact Nat.zero_ne_one ha_relatively_prime
  let splitRow : Split Finset.univ :=
    { π := a
      π0 := Int.floor b
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simp at hj }
  have hprimitive : splitRow.IsPrimitive := by
    simpa [Split.IsPrimitive, splitRow] using ha_relatively_prime
  obtain ⟨xInt, hxInt⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitRow hprimitive
  let xy : MixedRealPoint n p := (Int.cast ∘ xInt, fun _ : Fin p ↦ 0)
  have hrow_eq : ∑ j, (a j : ℝ) * xy.1 j = (Int.floor b : ℝ) := by
    -- The chosen integer point lies on the hyperplane `a · x = ⌊b⌋`.
    calc
      ∑ j, (a j : ℝ) * xy.1 j = ∑ j, ((a j * xInt j : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [xy, Int.cast_mul]
      _ = ((∑ j, a j * xInt j : ℤ) : ℝ) := by simp
      _ = (Int.floor b : ℝ) := by
            have hxIntReal :
                ((∑ j, splitRow.π j * xInt j : ℤ) : ℝ) = (splitRow.π0 : ℝ) := by
              exact_mod_cast hxInt
            simpa [splitRow] using hxIntReal
  have hrow_eq' : ∑ j, (a j : ℝ) * (xInt j : ℝ) = (Int.floor b : ℝ) := by
    simpa [xy] using hrow_eq
  have hxy_mem : xy ∈ exercise_5_10_mixed_integer_set a g b := by
    rw [mem_exercise_5_10_mixed_integer_set_iff]
    refine ⟨(mem_integerVectors_iff).2 ⟨xInt, rfl⟩, ?_, ?_⟩
    · intro j
      simp [xy]
    · -- With `y = 0`, the original row inequality reduces to `a · x = ⌊b⌋ ≤ b`.
      calc
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy
            = ∑ j, (a j : ℝ) * xy.1 j := by
                simp [mixed_linear_objective, dotProduct, xy]
        _ = (Int.floor b : ℝ) := hrow_eq
        _ ≤ b := Int.floor_le b
  refine ⟨xy, ?_⟩
  rw [mem_exercise_5_10_cut_face_iff]
  refine ⟨subset_convexHull ℝ _ hxy_mem, ?_⟩
  -- The same witness saturates the mixed cut because its continuous block is zero.
  simp [exercise_5_10_cut_value, xy, div_eq_mul_inv, hrow_eq']

/-- Helper for Exercise 5.10: the cut inequality can be viewed on the flattened ambient space
`Fin (n + p) → ℝ` by keeping the integer coefficients on the `x`-block and attaching the scaled
negative continuous coefficients on the `y`-block. -/
noncomputable def exercise_5_10_flat_cut_vector
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Fin (n + p) → ℝ :=
  Fin.append
    (fun i : Fin n ↦ (a i : ℝ))
    (fun j : Fin p ↦ if g j < 0 then g j / (1 - Int.fract b) else 0)

/-- Helper for Exercise 5.10: evaluating the flattened cut vector on `Fin.appendEquiv n p xy`
recovers `exercise_5_10_cut_value a g b xy`. -/
lemma exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy =
      exercise_5_10_cut_value a g b xy := by
  -- Split the flattened dot product into the integer and continuous blocks.
  have hcont :
      (∑ j : Fin p,
          (if g j < 0 then g j / (1 - Int.fract b) else 0) * xy.2 j) =
        (1 / (1 - Int.fract b)) *
          Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) := by
    calc
      (∑ j : Fin p, (if g j < 0 then g j / (1 - Int.fract b) else 0) * xy.2 j)
          = Finset.sum (exercise_5_10_negative_index_set g)
              (fun j ↦ (g j / (1 - Int.fract b)) * xy.2 j) := by
              simpa [exercise_5_10_negative_index_set] using
                (Finset.sum_filter
                  (s := Finset.univ)
                  (p := fun j : Fin p ↦ g j < 0)
                  (f := fun j ↦ (g j / (1 - Int.fract b)) * xy.2 j)).symm
      _ = Finset.sum (exercise_5_10_negative_index_set g)
            (fun j ↦ (1 / (1 - Int.fract b)) * (g j * xy.2 j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (1 / (1 - Int.fract b)) *
            Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) := by
              rw [Finset.mul_sum]
  -- After normalizing the continuous block, the flattened and mixed-space formulas coincide.
  have hdot :
      exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy =
        ∑ i, (a i : ℝ) * xy.1 i +
          ∑ j : Fin p, (if g j < 0 then g j / (1 - Int.fract b) else 0) * xy.2 j := by
    simp [exercise_5_10_flat_cut_vector, dotProduct, Fin.appendEquiv, Fin.append, Fin.sum_univ_add]
  rw [hdot, exercise_5_10_cut_value, hcont]

/-- Helper for Exercise 5.10: flattening commutes with the convex hull of the mixed-integer set. -/
lemma appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b) =
      convexHull ℝ (Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b) := by
  let eL : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  -- The flattening map is linear, so it carries convex hulls to convex hulls.
  simpa [eL] using
    (LinearMap.image_convexHull eL.toLinearMap (exercise_5_10_mixed_integer_set a g b))

/-- Helper for Exercise 5.10: after flattening, the cut face is the equality face cut out by the
flattened cut vector on the flattened mixed hull. -/
lemma appendEquiv_image_exercise_5_10_cut_face_eq_face_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' exercise_5_10_cut_face a g b =
      face_set
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (exercise_5_10_flat_cut_vector a g b)
        (Int.floor b : ℝ) := by
  ext u
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rw [mem_exercise_5_10_cut_face_iff] at hxy
    -- The image point stays in the flattened hull and satisfies the equality case of the cut.
    refine (mem_face_set_iff).2 ?_
    refine ⟨⟨xy, hxy.1, rfl⟩, ?_⟩
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hxy.2
  · intro hu
    rw [mem_face_set_iff] at hu
    rcases hu.1 with ⟨xy, hxyHull, rfl⟩
    -- Pull the equality slice back through the flattening equivalence.
    refine ⟨xy, ?_, rfl⟩
    rw [mem_exercise_5_10_cut_face_iff]
    refine ⟨hxyHull, ?_⟩
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hu.2

/-- Helper for Exercise 5.10: the cut face is an exposed face of the mixed hull because the cut
inequality is valid on every generator of the convex hull and is attained on the nonempty face. -/
lemma exercise_5_10_cut_face_isExposed
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    IsExposed ℝ
      (convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
      (exercise_5_10_cut_face a g b) := by
  let eL : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  let e : MixedRealPoint n p ≃L[ℝ] (Fin (n + p) → ℝ) :=
    eL.toContinuousLinearEquiv
  have he_symm_apply (u : Fin (n + p) → ℝ) :
      e.symm u = (Fin.appendEquiv n p).symm u := by
    rfl
  have hgen_valid :
      Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b ⊆
        {u : Fin (n + p) → ℝ |
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
    intro u hu
    rcases hu with ⟨xy, hxy, rfl⟩
    -- Validity on generators becomes validity of the flattened inequality after reindexing.
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using
      exercise_5_10_valid_cut a g b xy hxy
  have hcut_halfspace_convex :
      Convex ℝ {u : Fin (n + p) → ℝ |
        exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
    let L : (Fin (n + p) → ℝ) →ₗ[ℝ] ℝ :=
      (dotProductStrongDual (exercise_5_10_flat_cut_vector a g b)).toLinearMap
    have hset :
        {u : Fin (n + p) → ℝ |
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} =
          L ⁻¹' Set.Iic (Int.floor b : ℝ) := by
      ext u
      simp [L, dotProductStrongDual_apply]
    -- The cut halfspace is a linear preimage of the convex interval `(-∞, ⌊b⌋]`.
    rw [hset]
    exact (convex_Iic (Int.floor b : ℝ)).linear_preimage L
  have hflat_valid :
      is_valid_inequality
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (exercise_5_10_flat_cut_vector a g b)
        (Int.floor b : ℝ) := by
    have himage_subset :
        Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ⊆
          {u : Fin (n + p) → ℝ |
            exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
      calc
        Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)
            = convexHull ℝ (Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b) := by
                exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set a g b
        _ ⊆ {u : Fin (n + p) → ℝ |
              exercise_5_10_flat_cut_vector a g b ⬝ᵥ u ≤ (Int.floor b : ℝ)} := by
              exact convexHull_min hgen_valid hcut_halfspace_convex
    intro u hu
    exact himage_subset hu
  have hflat_exposed :
      IsExposed ℝ
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b) := by
    rw [appendEquiv_image_exercise_5_10_cut_face_eq_face_set]
    exact isExposed_face_set_of_valid_inequality hflat_valid
  have hback :
      IsExposed ℝ
        (e.symm '' (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)))
        (e.symm '' (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b)) := by
    exact isExposed_image_continuousLinearEquiv e.symm hflat_exposed
  have hsymm_hull :
      e.symm '' (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)) =
        convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
    ext xy
    constructor
    · rintro ⟨u, hu, hxy⟩
      rcases hu with ⟨z, hz, rfl⟩
      have hzxy : z = xy := by
        simpa [he_symm_apply] using hxy
      exact hzxy ▸ hz
    · intro hxy
      refine ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩, ?_⟩
      simp [he_symm_apply]
  have hsymm_face :
      e.symm '' (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b) =
        exercise_5_10_cut_face a g b := by
    ext xy
    constructor
    · rintro ⟨u, hu, hxy⟩
      rcases hu with ⟨z, hz, rfl⟩
      have hzxy : z = xy := by
        simpa [he_symm_apply] using hxy
      exact hzxy ▸ hz
    · intro hxy
      refine ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩, ?_⟩
      simp [he_symm_apply]
  -- Transport the exposed face back through the flattening equivalence.
  rw [hsymm_hull, hsymm_face] at hback
  exact hback

/-- Helper for Exercise 5.10: the cut is strict at a feasible mixed-integer point on the lower
integer level `a · x = ⌊b⌋ - 1`, so the cut face is a proper subset of the mixed hull. -/
lemma exercise_5_10_exists_strict_cut_point
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    ∃ xy : MixedRealPoint n p,
      xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
        exercise_5_10_cut_value a g b xy < (Int.floor b : ℝ) := by
  have ha_nonzero : a ≠ 0 := by
    intro ha_zero
    have hgcd_zero :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [ha_zero]
    rw [hgcd_zero] at ha_relatively_prime
    exact Nat.zero_ne_one ha_relatively_prime
  let splitRow : Split Finset.univ :=
    { π := a
      π0 := Int.floor b - 1
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simp at hj }
  have hprimitive : splitRow.IsPrimitive := by
    simpa [Split.IsPrimitive, splitRow] using ha_relatively_prime
  obtain ⟨xInt, hxInt⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitRow hprimitive
  let xy : MixedRealPoint n p := (Int.cast ∘ xInt, fun _ : Fin p ↦ 0)
  have hrow_eq : ∑ j, (a j : ℝ) * xy.1 j = ((Int.floor b : ℝ) - 1) := by
    -- The primitive witness is chosen on the lower integer level `⌊b⌋ - 1`.
    calc
      ∑ j, (a j : ℝ) * xy.1 j = ∑ j, ((a j * xInt j : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [xy, Int.cast_mul]
      _ = ((∑ j, a j * xInt j : ℤ) : ℝ) := by simp
      _ = ((Int.floor b - 1 : ℤ) : ℝ) := by
            have hxIntReal :
                ((∑ j, splitRow.π j * xInt j : ℤ) : ℝ) = (splitRow.π0 : ℝ) := by
              exact_mod_cast hxInt
            simpa [splitRow] using hxIntReal
      _ = (Int.floor b : ℝ) - 1 := by norm_num
  have hrow_eq' : ∑ j, (a j : ℝ) * (xInt j : ℝ) = (Int.floor b : ℝ) - 1 := by
    simpa [xy] using hrow_eq
  have hfract_pos : 0 < Int.fract b := by
    have hfloor_ne : b ≠ (Int.floor b : ℝ) := by
      intro hb_floor
      exact hb_nonint ⟨Int.floor b, hb_floor⟩
    exact (Int.fract_pos).2 hfloor_ne
  have hbelow_b : (Int.floor b : ℝ) - 1 ≤ b := by
    linarith [Int.floor_add_fract b, hfract_pos]
  have hxy_mem : xy ∈ exercise_5_10_mixed_integer_set a g b := by
    rw [mem_exercise_5_10_mixed_integer_set_iff]
    refine ⟨(mem_integerVectors_iff).2 ⟨xInt, rfl⟩, ?_, ?_⟩
    · intro j
      simp [xy]
    · -- With `y = 0`, the original row is exactly `a · x = ⌊b⌋ - 1 ≤ b`.
      calc
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy
            = ∑ j, (a j : ℝ) * xy.1 j := by
                simp [mixed_linear_objective, dotProduct, xy]
        _ = (Int.floor b : ℝ) - 1 := hrow_eq
        _ ≤ b := hbelow_b
  refine ⟨xy, subset_convexHull ℝ _ hxy_mem, ?_⟩
  -- The same lower-level witness makes the cut strict by exactly one unit.
  calc
    exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) - 1 := by
      simp [exercise_5_10_cut_value, xy, div_eq_mul_inv, hrow_eq']
    _ < (Int.floor b : ℝ) := by linarith

/-- Helper for Exercise 5.10: the integer block matrix of the one-row relaxation keeps the
original row in position `0` and has zero integer coefficients on the nonnegativity rows. -/
noncomputable def exercise_5_10_relaxationMatrixInt
    (a : Fin n → ℤ) : Matrix (Fin (p + 1)) (Fin n) ℝ :=
  fun i ↦ Fin.cases (fun j : Fin n ↦ (a j : ℝ)) (fun _j _k ↦ 0) i

/-- Helper for Exercise 5.10: the continuous block matrix of the one-row relaxation keeps the
original coefficient row in position `0` and uses the rows `-y_j ≤ 0` for nonnegativity. -/
noncomputable def exercise_5_10_relaxationMatrixCont
    (g : Fin p → ℝ) : Matrix (Fin (p + 1)) (Fin p) ℝ :=
  fun i ↦ Fin.cases g (fun j : Fin p ↦ -Pi.single j (1 : ℝ)) i

/-- Helper for Exercise 5.10: the right-hand side of the one-row relaxation is `b` on the
original row and `0` on the nonnegativity rows. -/
noncomputable def exercise_5_10_relaxationRhs
    (b : ℝ) : Fin (p + 1) → ℝ :=
  Fin.cases b (fun _j ↦ 0)

/-- Helper for Exercise 5.10: the basic multiplier `(1, g)` reproduces the split row `a` and
annihilates the continuous block of the one-row relaxation. -/
noncomputable def exercise_5_10_relaxationMultiplier
    (g : Fin p → ℝ) : Fin (p + 1) → ℝ :=
  Fin.cases 1 g

/-- Helper for Exercise 5.10: the real mixed polyhedron built from the explicit one-row
relaxation data is exactly the source-facing relaxation `y ≥ 0` and
`mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b`. -/
lemma mem_exercise_5_10_relaxation_polyhedron_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ real_mixed_polyhedron
        (exercise_5_10_relaxationMatrixInt (p := p) a)
        (exercise_5_10_relaxationMatrixCont g)
        (exercise_5_10_relaxationRhs (p := p) b) ↔
      (∀ j : Fin p, 0 ≤ xy.2 j) ∧
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b := by
  rw [mem_real_mixed_polyhedron_iff]
  constructor
  · intro hxy
    refine ⟨?_, ?_⟩
    · intro j
      have hj := hxy j.succ
      -- The nonnegativity rows are exactly the inequalities `-y_j ≤ 0`.
      have hj' : 0 ≤ ∑ x : Fin p, (if x = j then (1 : ℝ) else 0) * xy.2 x := by
        simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
          exercise_5_10_relaxationRhs, mixed_linear_objective, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, Pi.single_apply] using hj
      simpa [dotProduct] using hj'
    · have h0 := hxy 0
      -- Row `0` is the original mixed inequality.
      simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
        exercise_5_10_relaxationRhs, mixed_linear_objective, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using h0
  · rintro ⟨hy_nonneg, hrow⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · -- Row `0` restates the original mixed inequality.
      simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
        exercise_5_10_relaxationRhs, mixed_linear_objective, dotProduct] using hrow
    · intro j
      -- Each successor row is the nonnegativity constraint `-y_j ≤ 0`.
      have hj' : 0 ≤ ∑ x : Fin p, (if x = j then (1 : ℝ) else 0) * xy.2 x := by
        simpa [dotProduct] using hy_nonneg j
      simpa [exercise_5_10_relaxationMatrixInt, exercise_5_10_relaxationMatrixCont,
        exercise_5_10_relaxationRhs, mixed_linear_objective, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Pi.single_apply] using hj'

/-- Helper for Exercise 5.10: the multiplier `(1, g)` reproduces the integer split row `a` on
the explicit relaxation matrix. -/
lemma exercise_5_10_relaxationMultiplier_vecMul_matrixInt
    (a : Fin n → ℤ)
    (g : Fin p → ℝ) :
    Matrix.vecMul (exercise_5_10_relaxationMultiplier g)
        (exercise_5_10_relaxationMatrixInt (p := p) a) =
      fun j : Fin n ↦ (a j : ℝ) := by
  ext j
  -- Only the original row contributes to the integer block.
  simp [Matrix.vecMul, exercise_5_10_relaxationMultiplier,
    exercise_5_10_relaxationMatrixInt, dotProduct, Fin.sum_univ_succ]

/-- Helper for Exercise 5.10: the same multiplier annihilates the continuous block of the
explicit relaxation matrix. -/
lemma exercise_5_10_relaxationMultiplier_vecMul_matrixCont
    (g : Fin p → ℝ) :
    Matrix.vecMul (exercise_5_10_relaxationMultiplier g)
        (exercise_5_10_relaxationMatrixCont (p := p) g) = 0 := by
  ext j
  -- The original row contributes `g_j`, which is cancelled by the `j`th nonnegativity row.
  have hsum_single :
      ∑ x : Fin p, g x * (if x = j then (1 : ℝ) else 0) = g j := by
    simp
  calc
    Matrix.vecMul (exercise_5_10_relaxationMultiplier g)
        (exercise_5_10_relaxationMatrixCont (p := p) g) j
        = g j - ∑ x : Fin p, g x * (if x = j then (1 : ℝ) else 0) := by
            simp [Matrix.vecMul, exercise_5_10_relaxationMultiplier,
              exercise_5_10_relaxationMatrixCont, dotProduct, Fin.sum_univ_succ,
              Pi.single_apply]
    _ = g j - g j := by rw [hsum_single]
    _ = 0 := by ring

/-- Helper for Exercise 5.10: adjoining one nonnegative slack variable turns the original
mixed-integer inequality into an equality system without changing the `(x, y)` projection. -/
def exercise_5_10_augmentedSet
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p × ℝ) :=
  {xys |
    xys.1.1 ∈ ℤ^n ∧
      (∀ j : Fin p, 0 ≤ xys.1.2 j) ∧
        0 ≤ xys.2 ∧
          mixed_linear_objective (fun i ↦ (a i : ℝ)) g xys.1 + xys.2 = b}

/-- Membership in `exercise_5_10_augmentedSet a g b` means that the integer block is integral,
the original continuous block and the new slack are nonnegative, and the lifted row is exact. -/
theorem mem_exercise_5_10_augmentedSet_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xys : MixedRealPoint n p × ℝ) :
    xys ∈ exercise_5_10_augmentedSet a g b ↔
      xys.1.1 ∈ ℤ^n ∧
        (∀ j : Fin p, 0 ≤ xys.1.2 j) ∧
          0 ≤ xys.2 ∧
            mixed_linear_objective (fun i ↦ (a i : ℝ)) g xys.1 + xys.2 = b :=
  Iff.rfl

/-- Helper for Exercise 5.10: forgetting the slack coordinate identifies the lifted equality
system with the original mixed-integer set. -/
lemma exercise_5_10_augmentedProjection_eq_mixed_integer_set
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Prod.fst '' exercise_5_10_augmentedSet a g b =
      exercise_5_10_mixed_integer_set a g b := by
  ext xy
  constructor
  · rintro ⟨xys, hxys, rfl⟩
    rcases (mem_exercise_5_10_augmentedSet_iff a g b xys).1 hxys with
      ⟨hx_int, hy_nonneg, _hs_nonneg, hrow_eq⟩
    rw [mem_exercise_5_10_mixed_integer_set_iff]
    refine ⟨hx_int, hy_nonneg, ?_⟩
    -- Dropping the nonnegative slack recovers the original row inequality.
    linarith
  · intro hxy
    rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with
      ⟨hx_int, hy_nonneg, hrow_le⟩
    refine ⟨(xy, b - mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy), ?_, rfl⟩
    refine (mem_exercise_5_10_augmentedSet_iff a g b _).2 ?_
    constructor
    · exact hx_int
    constructor
    · exact hy_nonneg
    constructor
    · -- The slack is exactly the residual of the original feasible inequality.
      linarith
    · -- By construction the lifted row holds at equality.
      ring

/-- Helper for Exercise 5.10: linear projection commutes with the convex hull of the augmented
slack model, so the lifted owner projects back to `conv(S)`. -/
lemma exercise_5_10_augmentedProjection_image_convexHull
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Prod.fst '' convexHull ℝ (exercise_5_10_augmentedSet a g b) =
      convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
  let proj : (MixedRealPoint n p × ℝ) →ₗ[ℝ] MixedRealPoint n p :=
    LinearMap.fst ℝ (MixedRealPoint n p) ℝ
  have hproj_image :
      proj '' exercise_5_10_augmentedSet a g b =
        Prod.fst '' exercise_5_10_augmentedSet a g b := by
    rfl
  -- Push the convex hull through the linear projection, then simplify the projected owner.
  calc
    Prod.fst '' convexHull ℝ (exercise_5_10_augmentedSet a g b)
        = proj '' convexHull ℝ (exercise_5_10_augmentedSet a g b) := by
            rfl
    _ = convexHull ℝ (proj '' exercise_5_10_augmentedSet a g b) := by
          simpa [proj] using LinearMap.image_convexHull proj (exercise_5_10_augmentedSet a g b)
    _ = convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
          rw [hproj_image, exercise_5_10_augmentedProjection_eq_mixed_integer_set]

/-- Helper for Exercise 5.10: the lifted equality owner has the same cut face after forgetting
the slack coordinate, so the facet question can be moved to the augmented model. -/
def exercise_5_10_augmentedCutFace
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Set (MixedRealPoint n p × ℝ) :=
  {xys |
    xys ∈ convexHull ℝ (exercise_5_10_augmentedSet a g b) ∧
      exercise_5_10_cut_value a g b xys.1 = (Int.floor b : ℝ)}

/-- Forgetting the slack variable sends the lifted cut-equality face exactly to the source-facing
cut face `exercise_5_10_cut_face a g b`. -/
lemma exercise_5_10_augmentedProjection_eq_cut_face
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Prod.fst '' exercise_5_10_augmentedCutFace a g b =
      exercise_5_10_cut_face a g b := by
  ext xy
  constructor
  · rintro ⟨xys, hxys, rfl⟩
    rw [mem_exercise_5_10_cut_face_iff]
    refine ⟨?_, hxys.2⟩
    -- Projecting a lifted hull point lands in the original convex hull.
    rw [← exercise_5_10_augmentedProjection_image_convexHull]
    exact ⟨xys, hxys.1, rfl⟩
  · intro hxy
    rw [mem_exercise_5_10_cut_face_iff] at hxy
    rw [← exercise_5_10_augmentedProjection_image_convexHull] at hxy
    rcases hxy.1 with ⟨xys, hxys_hull, hproj⟩
    refine ⟨xys, ⟨hxys_hull, ?_⟩, hproj⟩
    -- The cut equation only depends on `(x, y)`, so it transfers across the projection equality.
    simpa [hproj] using hxy.2

/-- Helper for Exercise 5.10: the flat polyhedron used for the facet argument keeps row `0` as the
original relaxation inequality, row `1` as the cut inequality, and rows `2 + j` as the
nonnegativity inequalities `-y_j ≤ 0`. -/
noncomputable def exercise_5_10_facetMatrix
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) : Matrix (Fin (p + 2)) (Fin (n + p)) ℝ :=
  fun i ↦
    Fin.cases
      (Fin.append (fun j : Fin n ↦ (a j : ℝ)) g)
      (fun i' ↦
        Fin.cases
          (exercise_5_10_flat_cut_vector a g b)
          (fun j : Fin p ↦ Fin.append (fun _ : Fin n ↦ (0 : ℝ)) (-Pi.single j (1 : ℝ)))
          i')
      i

/-- Helper for Exercise 5.10: the flat right-hand side uses `b` on the original row,
`⌊b⌋` on the cut row, and `0` on the nonnegativity rows. -/
noncomputable def exercise_5_10_facetRhs
    (p : ℕ)
    (b : ℝ) : Fin (p + 2) → ℝ :=
  Fin.cases b (fun i' ↦ Fin.cases (Int.floor b : ℝ) (fun _ : Fin p ↦ 0) i')

/-- Helper for Exercise 5.10: each successor row after the cut row is the nonnegativity
constraint `-y_j ≤ 0` on a flattened mixed-space point. -/
lemma exercise_5_10_facetMatrix_nonneg_row_eval
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p)
    (j : Fin p) :
    Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) (Fin.succ (Fin.succ j))
      = -xy.2 j := by
  -- Only the `j`th nonnegativity row contributes on this successor coordinate.
  simp [exercise_5_10_facetMatrix, Matrix.mulVec, dotProduct, Fin.appendEquiv, Fin.append,
    Fin.sum_univ_add, Pi.single_apply]

/-- Helper for Exercise 5.10: membership in the explicit flat polyhedron is exactly the source
relaxation `y ≥ 0`, the original row inequality, and the Exercise 5.10 cut inequality. -/
lemma mem_exercise_5_10_facetPolyhedron_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    Fin.appendEquiv n p xy ∈
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) ↔
      (∀ j : Fin p, 0 ≤ xy.2 j) ∧
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b ∧
          exercise_5_10_cut_value a g b xy ≤ (Int.floor b : ℝ) := by
  rw [mem_polyhedron_le_set_iff]
  constructor
  · intro hxy
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hj := hxy (Fin.succ (Fin.succ j))
      have hj' : -xy.2 j ≤ 0 := by
        simpa [exercise_5_10_facetRhs, exercise_5_10_facetMatrix_nonneg_row_eval] using hj
      linarith
    · have h0 := hxy 0
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, mixed_linear_objective,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_add] using h0
    · have h1 := hxy 1
      have hcut :
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy ≤ (Int.floor b : ℝ) := by
        simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] using h1
      simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hcut
  · rintro ⟨hy_nonneg, hrow, hcut⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · -- Row `0` is the original one-row relaxation inequality.
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, mixed_linear_objective,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_add] using hrow
    · intro i'
      refine Fin.cases ?_ ?_ i'
      · -- Row `1` is the flat cut inequality.
        have hcut' :
            exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy ≤ (Int.floor b : ℝ) := by
          simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hcut
        simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] using hcut'
      · intro j
        -- Each successor row after the cut is exactly `-y_j ≤ 0`.
        have hj' : -xy.2 j ≤ 0 := by
          linarith [hy_nonneg j]
        simpa [exercise_5_10_facetRhs, exercise_5_10_facetMatrix_nonneg_row_eval] using hj'

/-- Helper for Exercise 5.10: the explicit flat facet owner is convex because it is a finite
system of linear inequalities. -/
lemma exercise_5_10_facetPolyhedron_convex
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Convex ℝ
      (polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b)) := by
  intro u hu v hv α β hα hβ hαβ i
  have hui :
      Matrix.mulVec (exercise_5_10_facetMatrix a g b) u i ≤ exercise_5_10_facetRhs p b i := hu i
  have hvi :
      Matrix.mulVec (exercise_5_10_facetMatrix a g b) v i ≤ exercise_5_10_facetRhs p b i := hv i
  calc
    Matrix.mulVec (exercise_5_10_facetMatrix a g b) (α • u + β • v) i
        = α * Matrix.mulVec (exercise_5_10_facetMatrix a g b) u i +
            β * Matrix.mulVec (exercise_5_10_facetMatrix a g b) v i := by
              calc
                ∑ j, exercise_5_10_facetMatrix a g b i j * (α * u j + β * v j)
                    = ∑ j, (α * (exercise_5_10_facetMatrix a g b i j * u j) +
                        β * (exercise_5_10_facetMatrix a g b i j * v j)) := by
                          refine Finset.sum_congr rfl ?_
                          intro j hj
                          ring
                _ = (∑ j, α * (exercise_5_10_facetMatrix a g b i j * u j)) +
                      ∑ j, β * (exercise_5_10_facetMatrix a g b i j * v j) := by
                        rw [Finset.sum_add_distrib]
                _ = α * Matrix.mulVec (exercise_5_10_facetMatrix a g b) u i +
                      β * Matrix.mulVec (exercise_5_10_facetMatrix a g b) v i := by
                        simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ α * exercise_5_10_facetRhs p b i + β * exercise_5_10_facetRhs p b i := by
          exact add_le_add (mul_le_mul_of_nonneg_left hui hα) (mul_le_mul_of_nonneg_left hvi hβ)
    _ = exercise_5_10_facetRhs p b i := by
          rw [← add_mul, hαβ, one_mul]

/-- Helper for Exercise 5.10: flattening sends `conv(S)` into the explicit facet owner `P'`
because the generators satisfy the relaxation rows and the cut is valid on `S`. -/
lemma appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_subset_facetPolyhedron
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ⊆
      polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
  have hgen :
      Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b ⊆
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
    intro u hu
    rcases hu with ⟨xy, hxy, rfl⟩
    rcases (mem_exercise_5_10_mixed_integer_set_iff a g b xy).1 hxy with
      ⟨_, hy_nonneg, hrow⟩
    refine (mem_exercise_5_10_facetPolyhedron_iff a g b xy).2 ?_
    exact ⟨hy_nonneg, hrow, exercise_5_10_valid_cut a g b xy hxy⟩
  calc
    Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)
        = convexHull ℝ (Fin.appendEquiv n p '' exercise_5_10_mixed_integer_set a g b) := by
            exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set a g b
    _ ⊆ polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
          exact convexHull_min hgen (exercise_5_10_facetPolyhedron_convex a g b)

/-- Helper for Exercise 5.10: every point of the source cut face maps into the singleton active
face of row `1` on the explicit flat owner `P'`. -/
lemma appendEquiv_image_exercise_5_10_cut_face_subset_activeConstraintFace
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ) :
    Fin.appendEquiv n p '' exercise_5_10_cut_face a g b ⊆
      active_constraint_face
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        ({1} : Set (Fin (p + 2))) := by
  intro u hu
  rcases hu with ⟨xy, hxy, rfl⟩
  rw [mem_exercise_5_10_cut_face_iff] at hxy
  have hxP :
      Fin.appendEquiv n p xy ∈
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
    exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_subset_facetPolyhedron
      a g b ⟨xy, hxy.1, rfl⟩
  refine (mem_active_constraint_face_iff).2 ?_
  constructor
  · intro i hi
    have hi1 : i = 1 := by simpa using hi
    have hcut :
        exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy = (Int.floor b : ℝ) := by
      simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hxy.2
    simpa [hi1, exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hcut
  · intro i hi
    exact hxP i

/-- Helper for Exercise 5.10: the strict-cut point already built inside `conv(S)` witnesses that
the cut row is not an implicit equality of the explicit flat owner `P'`. -/
lemma exercise_5_10_cutRow_irredundant
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    is_irredundant_row
      (exercise_5_10_facetMatrix a g b)
      (exercise_5_10_facetRhs p b)
      1 := by
  have ha_nonzero : a ≠ 0 := by
    intro ha_zero
    have hgcd_zero :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 0 := by
      apply Finset.gcd_eq_zero_iff.mpr
      intro j hj
      simp [ha_zero]
    rw [hgcd_zero] at ha_relatively_prime
    exact Nat.zero_ne_one ha_relatively_prime
  have hfract_pos : 0 < Int.fract b := by
    have hfloor_ne : b ≠ (Int.floor b : ℝ) := by
      intro hb_floor
      exact hb_nonint ⟨Int.floor b, hb_floor⟩
    exact (Int.fract_pos).2 hfloor_ne
  let splitFloor : Split Finset.univ :=
    { π := a
      π0 := Int.floor b
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simp at hj }
  have hprimitiveFloor : splitFloor.IsPrimitive := by
    simpa [Split.IsPrimitive, splitFloor] using ha_relatively_prime
  obtain ⟨xFloor, hxFloor⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitFloor hprimitiveFloor
  let splitDir : Split Finset.univ :=
    { π := a
      π0 := 1
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simp at hj }
  have hprimitiveDir : splitDir.IsPrimitive := by
    simpa [Split.IsPrimitive, splitDir] using ha_relatively_prime
  obtain ⟨d, hd⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitDir hprimitiveDir
  let xWitness : Fin n → ℝ := fun j ↦ (xFloor j : ℝ) + Int.fract b * (d j : ℝ)
  let xy : MixedRealPoint n p := (xWitness, fun _ : Fin p ↦ 0)
  have hxFloor_row : ∑ j, (a j : ℝ) * (xFloor j : ℝ) = (Int.floor b : ℝ) := by
    -- The first lattice witness lies on the integer hyperplane `a · x = floor b`.
    have hxFloor_real :
        ((∑ j, splitFloor.π j * xFloor j : ℤ) : ℝ) = (splitFloor.π0 : ℝ) := by
      exact_mod_cast hxFloor
    simpa [splitFloor, Int.cast_mul] using hxFloor_real
  have hd_row : ∑ j, (a j : ℝ) * (d j : ℝ) = (1 : ℝ) := by
    -- The primitive direction changes the integer row value by exactly one.
    have hd_real :
        ((∑ j, splitDir.π j * d j : ℤ) : ℝ) = (splitDir.π0 : ℝ) := by
      exact_mod_cast hd
    simpa [splitDir, Int.cast_mul] using hd_real
  have hxWitness_row :
      ∑ j, (a j : ℝ) * xWitness j = b := by
    -- Expanding `xFloor + fract(b) • d` gives `floor b + fract b = b`.
    calc
      ∑ j, (a j : ℝ) * xWitness j
          = ∑ j, ((a j : ℝ) * (xFloor j : ℝ) + Int.fract b * ((a j : ℝ) * (d j : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ j, (a j : ℝ) * (xFloor j : ℝ) +
            Int.fract b * ∑ j, (a j : ℝ) * (d j : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (Int.floor b : ℝ) + Int.fract b * (1 : ℝ) := by rw [hxFloor_row, hd_row]
      _ = b := by simp
  refine ⟨Fin.appendEquiv n p xy, ?_, ?_⟩
  · intro i hi
    revert hi
    -- All rows except the cut row are satisfied by the explicit witness.
    refine Fin.cases ?_ ?_ i
    · intro _hi
      have hrow0 :
        mixed_linear_objective (fun j ↦ (a j : ℝ)) g xy = b := by
        simpa [mixed_linear_objective, dotProduct, xy, xWitness] using hxWitness_row
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
        mixed_linear_objective, Fin.sum_univ_succ, Fin.sum_univ_add, xy, xWitness]
        using hrow0.le
    · intro i' hi
      by_cases hi0 : i' = 0
      · subst hi0
        exact (hi rfl).elim
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
        simp [exercise_5_10_facetRhs, exercise_5_10_facetMatrix_nonneg_row_eval, xy]
  · -- The cut row is violated strictly because the same witness attains value `b > floor b`.
    have hcut_eq : exercise_5_10_cut_value a g b xy = b := by
      simpa [exercise_5_10_cut_value, mixed_linear_objective, dotProduct, xy, xWitness]
        using hxWitness_row
    have hcut_gt : (Int.floor b : ℝ) < exercise_5_10_cut_value a g b xy := by
      rw [hcut_eq]
      linarith [Int.floor_add_fract b, hfract_pos]
    have hrow1 :
        (Int.floor b : ℝ) <
          Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) 1 := by
      have hflat :
          (Int.floor b : ℝ) <
            exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy := by
        simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hcut_gt
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using hflat
    simpa using hrow1

/-- Helper for Exercise 5.10: the strict-cut point already built inside `conv(S)` witnesses that
the cut row is not an implicit equality of the explicit flat owner `P'`. -/
lemma exercise_5_10_cutRow_not_implicit
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    ¬ is_implicit_equality
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        1 := by
  rcases exercise_5_10_exists_strict_cut_point a g b ha_relatively_prime hb_nonint with
    ⟨xy, hxy_hull, hxy_strict⟩
  intro himplicit
  have hxP :
      Fin.appendEquiv n p xy ∈
        polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
    exact appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_subset_facetPolyhedron
      a g b ⟨xy, hxy_hull, rfl⟩
  have hrow_eq :
      Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) 1 =
        exercise_5_10_facetRhs p b 1 := himplicit hxP
  have hcut_eq : exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) := by
    have hflat :
        exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy = (Int.floor b : ℝ) := by
      simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using hrow_eq
    simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hflat
  exact (ne_of_lt hxy_strict) hcut_eq

/-- Helper for Exercise 5.10: membership in the singleton active face of row `1` rewrites to the
source-facing nonnegativity constraints, the original row inequality, and equality in the cut. -/
lemma mem_appendEquiv_rowOneActiveConstraintFace_iff
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p) :
    Fin.appendEquiv n p xy ∈
        active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2))) ↔
      (∀ j : Fin p, 0 ≤ xy.2 j) ∧
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g xy ≤ b ∧
          exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) := by
  constructor
  · intro hxy
    have hxP :
        Fin.appendEquiv n p xy ∈
          polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
      -- The active face sits inside the ambient flat polyhedron.
      exact mem_polyhedron_of_mem_active_constraint_face hxy
    rcases (mem_exercise_5_10_facetPolyhedron_iff a g b xy).1 hxP with
      ⟨hy_nonneg, hrow, hcut_le⟩
    have hrow1 :
        Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) 1 =
          exercise_5_10_facetRhs p b 1 :=
      (mem_active_constraint_face_iff.mp hxy).1 1 (by simp)
    have hcut_eq :
        exercise_5_10_cut_value a g b xy = (Int.floor b : ℝ) := by
      -- Row `1` is exactly the flattened cut equation.
      have hflat :
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy = (Int.floor b : ℝ) := by
        simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] using hrow1
      simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hflat
    exact ⟨hy_nonneg, hrow, hcut_eq⟩
  · rintro ⟨hy_nonneg, hrow, hcut_eq⟩
    have hxP :
        Fin.appendEquiv n p xy ∈
          polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b) := by
      -- The source-facing conditions are exactly the flat polyhedron inequalities.
      refine (mem_exercise_5_10_facetPolyhedron_iff a g b xy).2 ?_
      exact ⟨hy_nonneg, hrow, by simpa using hcut_eq.le⟩
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      have hi1 : i = 1 := by simpa using hi
      -- Row `1` becomes the cut equality after reflattening.
      have hflat :
          exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy = (Int.floor b : ℝ) := by
        simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hcut_eq
      simpa [hi1, exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using hflat
    · intro i hi
      exact hxP i

/-- Helper for Exercise 5.10: when `b ∉ ℤ`, a row-`1` active point lies either on the lower
split branch, on the upper boundary `split_dot a x = ⌊b⌋ + 1`, or in the open split strip. -/
lemma exercise_5_10_activeFaceRow_branchCases
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ))
    (xy : MixedRealPoint n p)
    (hxy :
      Fin.appendEquiv n p xy ∈
        active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2)))) :
    split_dot a xy.1 ≤ (Int.floor b : ℝ) ∨
      split_dot a xy.1 = (Int.floor b : ℝ) + 1 ∨
        xy.1 ∈ split_strip a (Int.floor b) := by
  rcases (mem_appendEquiv_rowOneActiveConstraintFace_iff a g b xy).1 hxy with
    ⟨hy_nonneg, hrow, hcut_eq⟩
  let c : ℝ := split_dot a xy.1
  let neg : ℝ :=
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
  let total : ℝ := ∑ j, g j * xy.2 j
  have hfract_pos : 0 < Int.fract b := by
    have hfloor_ne : b ≠ (Int.floor b : ℝ) := by
      intro hb_floor
      exact hb_nonint ⟨Int.floor b, hb_floor⟩
    exact (Int.fract_pos).2 hfloor_ne
  have hneg_le_total : neg ≤ total := by
    -- Removing the nonnegative continuous block can only decrease the total row contribution.
    simpa [neg, total] using negativeContribution_le_totalContribution g xy hy_nonneg
  have hrow_sum : c + total ≤ b := by
    -- The source row inequality is exactly `split_dot a x + ∑ g_j y_j ≤ b`.
    simpa [c, total, split_dot_eq_sum, mixed_linear_objective, dotProduct] using hrow
  have hrow_neg : c + neg ≤ b := by
    linarith
  have hcut_scaled :
      c * (1 - Int.fract b) + neg = (Int.floor b : ℝ) * (1 - Int.fract b) := by
    have hden_ne : 1 - Int.fract b ≠ 0 := by
      linarith [Int.fract_lt_one b]
    have hcut_eq_div :
        c + neg / (1 - Int.fract b) = (Int.floor b : ℝ) := by
      simpa [c, neg, exercise_5_10_cut_value, split_dot_eq_sum, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc] using hcut_eq
    have hmul :
        (c + neg / (1 - Int.fract b)) * (1 - Int.fract b) =
          c * (1 - Int.fract b) + neg := by
      field_simp [hden_ne]
    -- Clear the denominator in the cut equality once, then keep the rest propositional.
    calc
      c * (1 - Int.fract b) + neg
          = (c + neg / (1 - Int.fract b)) * (1 - Int.fract b) := by
              simpa using hmul.symm
      _ = (Int.floor b : ℝ) * (1 - Int.fract b) := by
            rw [hcut_eq_div]
  by_cases hlow : c ≤ (Int.floor b : ℝ)
  · exact Or.inl hlow
  · have hgt : (Int.floor b : ℝ) < c := lt_of_not_ge hlow
    have hupper : c ≤ (Int.floor b : ℝ) + 1 := by
      have hdelta_mul :
          (c - (Int.floor b : ℝ)) * Int.fract b ≤ Int.fract b := by
        linarith [hrow_neg, hcut_scaled, Int.floor_add_fract b]
      have hdelta_le : c - (Int.floor b : ℝ) ≤ 1 := by
        nlinarith [hdelta_mul, hfract_pos]
      linarith
    by_cases hboundary : c = (Int.floor b : ℝ) + 1
    · exact Or.inr (Or.inl hboundary)
    · have hlt : c < (Int.floor b : ℝ) + 1 := lt_of_le_of_ne hupper hboundary
      -- The remaining case is the genuine strip case.
      exact Or.inr (Or.inr ((mem_split_strip_iff).2 (by simpa [c] using ⟨hgt, hlt⟩)))

/-- Helper for Exercise 5.10: relative primality of the integer row coefficients forces the row
vector `a` to be nonzero. -/
lemma exercise_5_10_row_nonzero_of_relatively_prime
    (a : Fin n → ℤ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1) :
    a ≠ 0 := by
  intro ha_zero
  have hgcd_zero :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 0 := by
    apply Finset.gcd_eq_zero_iff.mpr
    intro j hj
    simp [ha_zero]
  rw [hgcd_zero] at ha_relatively_prime
  exact Nat.zero_ne_one ha_relatively_prime

/-- Helper for Exercise 5.10: if the fixed-`y` slice lies in the rounded one-row halfspace for
`b - g ⋅ y`, then freezing `y` lifts that slice hull into `conv(S)`. -/
lemma exercise_5_10_mem_convexHull_of_fixedYSliceRounded
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (xy : MixedRealPoint n p)
    (hy_nonneg : ∀ j : Fin p, 0 ≤ xy.2 j)
    (hrounded :
      split_dot a xy.1 ≤
        (Int.floor (b - ∑ j, g j * xy.2 j) : ℝ)) :
    xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
  let total : ℝ := ∑ j, g j * xy.2 j
  let X : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ |
      (∀ j ∈ (Finset.univ : Finset (Fin n)), ∃ z : ℤ, x j = (z : ℝ)) ∧
        split_dot a x ≤ b - total}
  have ha_nonzero : a ≠ 0 :=
    exercise_5_10_row_nonzero_of_relatively_prime a ha_relatively_prime
  let splitRow : Split Finset.univ :=
    { π := a
      π0 := 0
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simp at hj }
  have hprimitive : splitRow.IsPrimitive := by
    -- The split owner only repackages the same primitive row.
    simpa [Split.IsPrimitive, splitRow] using ha_relatively_prime
  have hx_hull :
      xy.1 ∈ convexHull ℝ X := by
    -- Apply the one-row primitive halfspace theorem at the frozen right-hand side `b - g ⋅ y`.
    rw [convexHull_mixed_integer_halfspace_eq_rounded_halfspace_of_relatively_prime_coefficients
      Finset.univ splitRow (b - total) hprimitive]
    simpa [X, splitRow, total] using hrounded
  have hxy_hull :
      xy ∈ convexHull ℝ {uv : MixedRealPoint n p | uv.1 ∈ X ∧ uv.2 = xy.2} := by
    -- Keep the continuous block fixed while transporting the `x`-slice convex combination.
    rcases (mem_convexHull_iff_exists_fintype).1 hx_hull with
      ⟨ι, _, w, z, hw₀, hw₁, hz, hxsum⟩
    refine mem_convexHull_of_exists_fintype w (fun i ↦ (z i, xy.2)) hw₀ hw₁ ?_ ?_
    · intro i
      exact ⟨hz i, rfl⟩
    · refine Prod.ext ?_ ?_
      · simpa [Prod.fst_sum] using hxsum
      · calc
          (∑ i, w i • (z i, xy.2)).2 = ∑ i, w i • xy.2 := by
                simp [Prod.snd_sum]
          _ = (∑ i, w i) • xy.2 := by
                rw [Finset.sum_smul]
          _ = xy.2 := by
                simp [hw₁]
  have hlift :
      {uv : MixedRealPoint n p | uv.1 ∈ X ∧ uv.2 = xy.2} ⊆
        exercise_5_10_mixed_integer_set a g b := by
    intro uv huv
    rcases huv with ⟨huX, huY⟩
    rcases huX with ⟨hu_int, hu_row⟩
    rw [mem_exercise_5_10_mixed_integer_set_iff]
    refine ⟨(mem_integerVectors_iff_forall).2 ?_, ?_, ?_⟩
    · intro j
      rcases hu_int j (by simp) with ⟨z, hz⟩
      exact ⟨z, hz.symm⟩
    · simpa [huY] using hy_nonneg
    · -- The fixed-`y` slice inequality is exactly the original row bound with `y` frozen.
      calc
        mixed_linear_objective (fun i ↦ (a i : ℝ)) g uv
            = split_dot a uv.1 + total := by
                simp [mixed_linear_objective, split_dot_eq_sum, dotProduct, total, huY]
        _ ≤ (b - total) + total := by
              linarith
        _ = b := by
              simp [total]
  exact (convexHull_mono hlift) hxy_hull

/-- Helper for Exercise 5.10: on the lower branch, the cut equality forces `a ⋅ x = ⌊b⌋`, so the
fixed-`y` residual halfspace already rounds to the source hull. -/
lemma exercise_5_10_mem_cut_face_of_lowerActiveFacePoint
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (xy : MixedRealPoint n p)
    (hactive :
      Fin.appendEquiv n p xy ∈
        active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2))))
    (hlow : split_dot a xy.1 ≤ (Int.floor b : ℝ)) :
    xy ∈ exercise_5_10_cut_face a g b := by
  rcases (mem_appendEquiv_rowOneActiveConstraintFace_iff a g b xy).1 hactive with
    ⟨hy_nonneg, hrow, hcut_eq⟩
  let c : ℝ := split_dot a xy.1
  let neg : ℝ :=
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
  let total : ℝ := ∑ j, g j * xy.2 j
  have hden_pos : 0 < 1 - Int.fract b := by
    linarith [Int.fract_lt_one b]
  have hden_ne : 1 - Int.fract b ≠ 0 := ne_of_gt hden_pos
  have hneg_nonpos : neg ≤ 0 := by
    -- The negative-index contribution is a sum of nonpositive terms.
    refine Finset.sum_nonpos ?_
    intro j hj
    have hj_neg : g j < 0 := (mem_exercise_5_10_negative_index_set_iff g j).1 hj
    exact mul_nonpos_of_nonpos_of_nonneg hj_neg.le (hy_nonneg j)
  have hneg_le_total : neg ≤ total := by
    simpa [neg, total] using negativeContribution_le_totalContribution g xy hy_nonneg
  have hrow_sum : c + total ≤ b := by
    -- Rewrite the source row to the scalar form used by the floor argument.
    simpa [c, total, split_dot_eq_sum, mixed_linear_objective, dotProduct] using hrow
  have hcut_scaled :
      c + neg / (1 - Int.fract b) = (Int.floor b : ℝ) := by
    simpa [c, neg, exercise_5_10_cut_value, split_dot_eq_sum, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hcut_eq
  have hc_ge : (Int.floor b : ℝ) ≤ c := by
    have hdiv_nonpos : neg / (1 - Int.fract b) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hneg_nonpos hden_pos.le
    linarith
  have hc_eq : c = (Int.floor b : ℝ) := by
    exact le_antisymm hlow hc_ge
  have hdiv_eq : neg / (1 - Int.fract b) = 0 := by
    linarith [hcut_scaled, hc_eq]
  have hneg_eq : neg = 0 := by
    rcases (div_eq_zero_iff).1 hdiv_eq with hneg_eq | hzero
    · exact hneg_eq
    · exact (hden_ne hzero).elim
  have htotal_nonneg : 0 ≤ total := by
    linarith [hneg_le_total, hneg_eq]
  have htotal_le_fract : total ≤ Int.fract b := by
    linarith [hrow_sum, hc_eq, Int.floor_add_fract b]
  have hfloor_le_residual :
      (Int.floor b : ℝ) ≤ b - total := by
    linarith [htotal_le_fract, Int.floor_add_fract b]
  have hrounded_int : Int.floor b ≤ Int.floor (b - total) := by
    exact Int.le_floor.mpr hfloor_le_residual
  have hrounded :
      split_dot a xy.1 ≤ (Int.floor (b - total) : ℝ) := by
    calc
      split_dot a xy.1 = (Int.floor b : ℝ) := by simpa [c] using hc_eq
      _ ≤ (Int.floor (b - total) : ℝ) := by exact_mod_cast hrounded_int
  refine (mem_exercise_5_10_cut_face_iff a g b xy).2 ?_
  constructor
  · -- Freeze `y` and lift the rounded slice hull back to `conv(S)`.
    simpa [total] using
      exercise_5_10_mem_convexHull_of_fixedYSliceRounded a g b ha_relatively_prime xy hy_nonneg
        hrounded
  · exact hcut_eq

/-- Helper for Exercise 5.10: on the upper split boundary, the cut equality forces the residual
right-hand side to round exactly to `⌊b⌋ + 1`. -/
lemma exercise_5_10_mem_cut_face_of_upperBoundaryActiveFacePoint
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (xy : MixedRealPoint n p)
    (hactive :
      Fin.appendEquiv n p xy ∈
        active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2))))
    (hupper : split_dot a xy.1 = (Int.floor b : ℝ) + 1) :
    xy ∈ exercise_5_10_cut_face a g b := by
  rcases (mem_appendEquiv_rowOneActiveConstraintFace_iff a g b xy).1 hactive with
    ⟨hy_nonneg, hrow, hcut_eq⟩
  let c : ℝ := split_dot a xy.1
  let neg : ℝ :=
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
  let total : ℝ := ∑ j, g j * xy.2 j
  have hneg_le_total : neg ≤ total := by
    simpa [neg, total] using negativeContribution_le_totalContribution g xy hy_nonneg
  have hrow_sum : c + total ≤ b := by
    -- Rewrite the source row to the scalar form used by the floor argument.
    simpa [c, total, split_dot_eq_sum, mixed_linear_objective, dotProduct] using hrow
  have hcut_scaled :
      c + neg / (1 - Int.fract b) = (Int.floor b : ℝ) := by
    simpa [c, neg, exercise_5_10_cut_value, split_dot_eq_sum, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hcut_eq
  have hc_eq : c = (Int.floor b : ℝ) + 1 := by
    simpa [c] using hupper
  have hdiv_eq : neg / (1 - Int.fract b) = -1 := by
    linarith [hcut_scaled, hc_eq]
  have hden_ne : 1 - Int.fract b ≠ 0 := by
    linarith [Int.fract_lt_one b]
  have hneg_eq : neg = Int.fract b - 1 := by
    have hneg_mul : neg = (-1 : ℝ) * (1 - Int.fract b) := by
      exact (div_eq_iff hden_ne).1 hdiv_eq
    linarith
  have htotal_le : total ≤ Int.fract b - 1 := by
    linarith [hrow_sum, hc_eq, Int.floor_add_fract b]
  have htotal_eq : total = Int.fract b - 1 := by
    linarith [hneg_le_total, hneg_eq, htotal_le]
  have hb_residual : b - total = (Int.floor b : ℝ) + 1 := by
    linarith [htotal_eq, Int.floor_add_fract b]
  have hrounded :
      split_dot a xy.1 ≤ (Int.floor (b - total) : ℝ) := by
    have hfloor_eq : (Int.floor (b - total) : ℝ) = (Int.floor b : ℝ) + 1 := by
      simp [hb_residual]
    calc
      split_dot a xy.1 = (Int.floor b : ℝ) + 1 := by simpa [c] using hc_eq
      _ = (Int.floor (b - total) : ℝ) := by simpa using hfloor_eq.symm
      _ ≤ (Int.floor (b - total) : ℝ) := le_rfl
  refine (mem_exercise_5_10_cut_face_iff a g b xy).2 ?_
  constructor
  · -- The upper-boundary residual is already integral after freezing `y`.
    simpa [total] using
      exercise_5_10_mem_convexHull_of_fixedYSliceRounded a g b ha_relatively_prime xy hy_nonneg
        hrounded
  · exact hcut_eq

/-- Helper for Exercise 5.10: on the genuine strip branch, the active-face equalities determine
the strip parameter, the negative contribution, and the remaining positive mass. -/
lemma exercise_5_10_stripActiveFaceMassBounds
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (xy : MixedRealPoint n p)
    (hactive :
      Fin.appendEquiv n p xy ∈
        active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2))))
    (hstrip : xy.1 ∈ split_strip a (Int.floor b)) :
    let θ : ℝ := split_dot a xy.1 - (Int.floor b : ℝ)
    let neg : ℝ :=
      Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
    let pos : ℝ :=
      Finset.sum (Finset.univ.filter fun j : Fin p ↦ ¬ g j < 0) (fun j ↦ g j * xy.2 j)
    0 < θ ∧ θ < 1 ∧ neg = θ * (Int.fract b - 1) ∧ pos ≤ Int.fract b * (1 - θ) := by
  rcases (mem_appendEquiv_rowOneActiveConstraintFace_iff a g b xy).1 hactive with
    ⟨hy_nonneg, hrow, hcut_eq⟩
  let θ : ℝ := split_dot a xy.1 - (Int.floor b : ℝ)
  let neg : ℝ :=
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
  let pos : ℝ :=
    Finset.sum (Finset.univ.filter fun j : Fin p ↦ ¬ g j < 0) (fun j ↦ g j * xy.2 j)
  have hθ_pos : 0 < θ := by
    -- Membership in the split strip gives the lower strict inequality for `θ`.
    rcases (mem_split_strip_iff).1 hstrip with ⟨hgt, _⟩
    simpa [θ] using hgt
  have hθ_lt : θ < 1 := by
    -- The upper strict strip inequality becomes the normalization `θ < 1`.
    rcases (mem_split_strip_iff).1 hstrip with ⟨_, hlt⟩
    dsimp [θ]
    linarith
  have hsplit :
      neg + pos = ∑ j, g j * xy.2 j := by
    -- Split the continuous contribution into its negative and nonnegative coefficient blocks.
    simpa [neg, pos, exercise_5_10_negative_index_set] using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ)
        (p := fun j : Fin p ↦ g j < 0)
        (f := fun j ↦ g j * xy.2 j))
  have hcut_scaled :
      split_dot a xy.1 + neg / (1 - Int.fract b) = (Int.floor b : ℝ) := by
    -- Row `1` of the active face is exactly the cut equation.
    simpa [neg, exercise_5_10_cut_value, split_dot_eq_sum, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hcut_eq
  have hden_pos : 0 < 1 - Int.fract b := by
    linarith [Int.fract_lt_one b]
  have hden_ne : 1 - Int.fract b ≠ 0 := ne_of_gt hden_pos
  have hneg_div : neg / (1 - Int.fract b) = -θ := by
    dsimp [θ] at hcut_scaled ⊢
    linarith
  have hneg_eq : neg = θ * (Int.fract b - 1) := by
    have hneg_mul : neg = (-θ) * (1 - Int.fract b) := by
      exact (div_eq_iff hden_ne).1 hneg_div
    linarith
  have hrow_sum : split_dot a xy.1 + ∑ j, g j * xy.2 j ≤ b := by
    -- The original mixed row inequality is the source row bound.
    simpa [mixed_linear_objective, dotProduct, split_dot_eq_sum] using hrow
  have hpos_le : pos ≤ Int.fract b * (1 - θ) := by
    have hrow_sum' :
        ((Int.floor b : ℝ) + θ) + (neg + pos) ≤ b := by
      simpa [θ, hsplit, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrow_sum
    linarith [hrow_sum', hneg_eq, Int.floor_add_fract b]
  exact ⟨hθ_pos, hθ_lt, hneg_eq, hpos_le⟩

/-- Helper for Exercise 5.10: a genuine strip active point lies in the source cut face after
splitting its continuous mass into lower and upper endpoint slices. -/
lemma exercise_5_10_mem_cut_face_of_stripActiveFacePoint
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (xy : MixedRealPoint n p)
    (hactive :
      Fin.appendEquiv n p xy ∈
        active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2))))
    (hstrip : xy.1 ∈ split_strip a (Int.floor b)) :
    xy ∈ exercise_5_10_cut_face a g b := by
  rcases (mem_appendEquiv_rowOneActiveConstraintFace_iff a g b xy).1 hactive with
    ⟨hy_nonneg, hrow, hcut_eq⟩
  let θ : ℝ := split_dot a xy.1 - (Int.floor b : ℝ)
  let neg : ℝ :=
    Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j)
  let Jpos : Finset (Fin p) := Finset.univ.filter fun j : Fin p ↦ ¬ g j < 0
  let pos : ℝ := Finset.sum Jpos (fun j ↦ g j * xy.2 j)
  have hmass := exercise_5_10_stripActiveFaceMassBounds a g b xy hactive hstrip
  have hmass' : 0 < θ ∧ θ < 1 ∧ neg = θ * (Int.fract b - 1) ∧ pos ≤ Int.fract b * (1 - θ) := by
    simpa [θ, neg, Jpos, pos] using hmass
  rcases hmass' with ⟨hθ_pos, hθ_lt, hneg_eq, hpos_le⟩
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ_pos
  have hone_subθ_pos : 0 < 1 - θ := by
    linarith
  have hone_subθ_ne : 1 - θ ≠ 0 := ne_of_gt hone_subθ_pos
  have ha_nonzero : a ≠ 0 :=
    exercise_5_10_row_nonzero_of_relatively_prime a ha_relatively_prime
  let splitDir : Split Finset.univ :=
    { π := a
      π0 := 1
      nonzero := ha_nonzero
      zero_on_continuous := by
        intro j hj
        simp at hj }
  have hprimitiveDir : splitDir.IsPrimitive := by
    simpa [Split.IsPrimitive, splitDir] using ha_relatively_prime
  obtain ⟨d, hd⟩ :=
    exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
      Finset.univ splitDir hprimitiveDir
  let dReal : Fin n → ℝ := fun j ↦ (d j : ℝ)
  have hd_row : split_dot a dReal = (1 : ℝ) := by
    -- The primitive direction changes the split row by exactly one.
    have hd_real :
        ((∑ j, splitDir.π j * d j : ℤ) : ℝ) = (splitDir.π0 : ℝ) := by
      exact_mod_cast hd
    simpa [splitDir, dReal, Int.cast_mul, split_dot_eq_sum] using hd_real
  let xLower : Fin n → ℝ := xy.1 + (-θ) • dReal
  let xUpper : Fin n → ℝ := xy.1 + (1 - θ) • dReal
  let yLower : Fin p → ℝ := fun j ↦ if g j < 0 then 0 else xy.2 j / (1 - θ)
  let yUpper : Fin p → ℝ := fun j ↦ if g j < 0 then xy.2 j / θ else 0
  let xyLower : MixedRealPoint n p := (xLower, yLower)
  let xyUpper : MixedRealPoint n p := (xUpper, yUpper)
  have hxLower_row : split_dot a xLower = (Int.floor b : ℝ) := by
    -- Shifting by `-θ d` lands on the lower integer split boundary.
    calc
      split_dot a xLower = split_dot a xy.1 + (-θ) * split_dot a dReal := by
        simpa [xLower] using integerDot_add_smul a xy.1 dReal (-θ)
      _ = split_dot a xy.1 - θ := by rw [hd_row]; ring
      _ = (Int.floor b : ℝ) := by
        dsimp [θ]
        ring
  have hxUpper_row : split_dot a xUpper = (Int.floor b : ℝ) + 1 := by
    -- Shifting by `(1 - θ) d` reaches the upper split boundary.
    calc
      split_dot a xUpper = split_dot a xy.1 + (1 - θ) * split_dot a dReal := by
        simpa [xUpper] using integerDot_add_smul a xy.1 dReal (1 - θ)
      _ = split_dot a xy.1 + (1 - θ) := by simp [hd_row]
      _ = (Int.floor b : ℝ) + 1 := by
        dsimp [θ]
        ring
  have hyLower_nonneg : ∀ j : Fin p, 0 ≤ yLower j := by
    intro j
    by_cases hgj : g j < 0
    · simp [yLower, hgj]
    · simpa [yLower, hgj] using div_nonneg (hy_nonneg j) hone_subθ_pos.le
  have hyUpper_nonneg : ∀ j : Fin p, 0 ≤ yUpper j := by
    intro j
    by_cases hgj : g j < 0
    · simpa [yUpper, hgj] using div_nonneg (hy_nonneg j) hθ_pos.le
    · simp [yUpper, hgj]
  have hlower_neg_zero :
      Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * yLower j) = 0 := by
    -- The lower endpoint keeps only the nonnegative coefficient block.
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hgj : g j < 0 := (mem_exercise_5_10_negative_index_set_iff g j).1 hj
    simp [yLower, hgj]
  have hlower_pos :
      Finset.sum Jpos (fun j ↦ g j * yLower j) = pos / (1 - θ) := by
    -- Scaling the nonnegative block by `1 / (1 - θ)` preserves its total up to the same factor.
    calc
      Finset.sum Jpos (fun j ↦ g j * yLower j)
          = Finset.sum Jpos (fun j ↦ (1 / (1 - θ)) * (g j * xy.2 j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hgj : ¬ g j < 0 := (Finset.mem_filter.1 hj).2
              simp [yLower, hgj, div_eq_mul_inv]
              ring
      _ = (1 / (1 - θ)) * Finset.sum Jpos (fun j ↦ g j * xy.2 j) := by
            rw [Finset.mul_sum]
      _ = pos / (1 - θ) := by
            simp [pos, div_eq_mul_inv, mul_comm]
  have htotalLower :
      ∑ j, g j * yLower j = pos / (1 - θ) := by
    have hsplitLower :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ)
        (p := fun j : Fin p ↦ g j < 0)
        (f := fun j ↦ g j * yLower j)
    calc
      ∑ j, g j * yLower j
          = Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * yLower j) +
              Finset.sum Jpos (fun j ↦ g j * yLower j) := by
                simpa [exercise_5_10_negative_index_set, Jpos] using hsplitLower.symm
      _ = pos / (1 - θ) := by rw [hlower_neg_zero, hlower_pos, zero_add]
  have htotalLower_le_fract : ∑ j, g j * yLower j ≤ Int.fract b := by
    rw [htotalLower]
    exact (div_le_iff₀ hone_subθ_pos).2
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpos_le)
  have hroundedLower :
      split_dot a xLower ≤ (Int.floor (b - ∑ j, g j * yLower j) : ℝ) := by
    -- The lower endpoint lies in the rounded lower slice because its continuous mass is at most
    -- the fractional right-hand-side slack.
    have hfloor_le :
        (Int.floor b : ℝ) ≤ b - ∑ j, g j * yLower j := by
      linarith [htotalLower_le_fract, Int.floor_add_fract b]
    have hfloor_int : Int.floor b ≤ Int.floor (b - ∑ j, g j * yLower j) := by
      exact Int.le_floor.mpr hfloor_le
    rw [hxLower_row]
    exact_mod_cast hfloor_int
  have hupper_pos_zero :
      Finset.sum Jpos (fun j ↦ g j * yUpper j) = 0 := by
    -- The upper endpoint keeps only the negative coefficient block.
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hgj : ¬ g j < 0 := (Finset.mem_filter.1 hj).2
    simp [yUpper, hgj]
  have hupper_neg :
      Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * yUpper j) = neg / θ := by
    -- Scaling the negative block by `1 / θ` preserves its total up to that factor.
    calc
      Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * yUpper j)
          = Finset.sum (exercise_5_10_negative_index_set g)
              (fun j ↦ (1 / θ) * (g j * xy.2 j)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                have hgj : g j < 0 := (mem_exercise_5_10_negative_index_set_iff g j).1 hj
                simp [yUpper, hgj, div_eq_mul_inv]
                ring
      _ = (1 / θ) *
            Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * xy.2 j) := by
            rw [Finset.mul_sum]
      _ = neg / θ := by
            simp [neg, div_eq_mul_inv, mul_comm]
  have htotalUpper :
      ∑ j, g j * yUpper j = neg / θ := by
    have hsplitUpper :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ)
        (p := fun j : Fin p ↦ g j < 0)
        (f := fun j ↦ g j * yUpper j)
    calc
      ∑ j, g j * yUpper j
          = Finset.sum (exercise_5_10_negative_index_set g) (fun j ↦ g j * yUpper j) +
              Finset.sum Jpos (fun j ↦ g j * yUpper j) := by
                simpa [exercise_5_10_negative_index_set, Jpos] using hsplitUpper.symm
      _ = neg / θ := by rw [hupper_neg, hupper_pos_zero, add_zero]
  have htotalUpper_eq : ∑ j, g j * yUpper j = Int.fract b - 1 := by
    rw [htotalUpper]
    refine (div_eq_iff hθ_ne).2 ?_
    calc
      neg = θ * (Int.fract b - 1) := hneg_eq
      _ = (Int.fract b - 1) * θ := by ring
  have hroundedUpper :
      split_dot a xUpper ≤ (Int.floor (b - ∑ j, g j * yUpper j) : ℝ) := by
    -- The upper endpoint attains the integral residual `⌊b⌋ + 1` exactly.
    have hb_residual : b - ∑ j, g j * yUpper j = (Int.floor b : ℝ) + 1 := by
      linarith [htotalUpper_eq, Int.floor_add_fract b]
    rw [hxUpper_row]
    have hfloor_eq : (Int.floor (b - ∑ j, g j * yUpper j) : ℝ) = (Int.floor b : ℝ) + 1 := by
      simp [hb_residual]
    exact hfloor_eq.ge
  have hxyLower_hull :
      xyLower ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
    -- The lower endpoint lies in the rounded lower slice with the rescaled nonnegative block.
    exact exercise_5_10_mem_convexHull_of_fixedYSliceRounded
      a g b ha_relatively_prime xyLower hyLower_nonneg hroundedLower
  have hxyUpper_hull :
      xyUpper ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
    -- The upper endpoint lies in the rounded upper slice with the rescaled negative block.
    exact exercise_5_10_mem_convexHull_of_fixedYSliceRounded
      a g b ha_relatively_prime xyUpper hyUpper_nonneg hroundedUpper
  have hxy_line : xy = AffineMap.lineMap xyLower xyUpper θ := by
    -- Recombine the lower and upper endpoints with the strip parameter `θ`.
    refine Prod.ext ?_ ?_
    · funext j
      simp [xyLower, xyUpper, xLower, xUpper, dReal, AffineMap.lineMap_apply_module]
      ring
    · funext j
      by_cases hgj : g j < 0
      · simp [xyLower, xyUpper, yLower, yUpper, hgj, AffineMap.lineMap_apply_module]
        field_simp [hθ_ne]
      · simp [xyLower, xyUpper, yLower, yUpper, hgj, AffineMap.lineMap_apply_module]
        field_simp [hone_subθ_ne]
  have hxy_segment : xy ∈ segment ℝ xyLower xyUpper := by
    -- The strip point lies on the segment joining the two rounded endpoint witnesses.
    rw [segment_eq_image_lineMap]
    exact ⟨θ, ⟨hθ_pos.le, hθ_lt.le⟩, hxy_line.symm⟩
  have hxy_hull : xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) := by
    -- Convexity of `conv(S)` now lifts the endpoint segment back to the source hull.
    exact (convex_convexHull ℝ
      (exercise_5_10_mixed_integer_set a g b)).segment_subset
        hxyLower_hull hxyUpper_hull hxy_segment
  exact (mem_exercise_5_10_cut_face_iff a g b xy).2 ⟨hxy_hull, hcut_eq⟩

/-- Helper for Exercise 5.10: every point of the singleton active face of row `1` on the explicit
flat owner `P'` should come from the source-facing cut face after flattening. -/
lemma activeConstraintFace_subset_appendEquiv_image_exercise_5_10_cut_face
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    active_constraint_face
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        ({1} : Set (Fin (p + 2))) ⊆
      Fin.appendEquiv n p '' exercise_5_10_cut_face a g b := by
  -- Route correction: the remaining blocker is the reverse face inclusion from the canonical
  -- singleton active face of `P'` back to the flattened source face.
  intro u hu
  let xy : MixedRealPoint n p := (Fin.appendEquiv n p).symm u
  have hxy_eq : Fin.appendEquiv n p xy = u := by
    simpa [xy] using (Fin.appendEquiv n p).apply_symm_apply u
  have hactive :
      Fin.appendEquiv n p xy ∈
        active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2))) := by
    simpa [hxy_eq] using hu
  refine ⟨xy, ?_, hxy_eq⟩
  rcases exercise_5_10_activeFaceRow_branchCases a g b hb_nonint xy hactive with
    hlow | hupper | hstrip
  · -- The lower branch collapses to the integer hyperplane `a ⋅ x = ⌊b⌋`.
    exact exercise_5_10_mem_cut_face_of_lowerActiveFacePoint
      a g b ha_relatively_prime xy hactive hlow
  · -- The upper boundary also rounds exactly after freezing the continuous block.
    exact exercise_5_10_mem_cut_face_of_upperBoundaryActiveFacePoint
      a g b ha_relatively_prime xy hactive hupper
  · -- The genuine strip case is handled by the lower/upper endpoint convex decomposition.
    exact exercise_5_10_mem_cut_face_of_stripActiveFacePoint
      a g b ha_relatively_prime xy hactive hstrip

/-- Helper for Exercise 5.10: after flattening, the source cut face is exactly the singleton
active face of row `1` on the explicit flat owner `P'`. -/
lemma appendEquiv_image_exercise_5_10_cut_face_eq_activeConstraintFace
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    Fin.appendEquiv n p '' exercise_5_10_cut_face a g b =
      active_constraint_face
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        ({1} : Set (Fin (p + 2))) := by
  apply Set.Subset.antisymm
  · -- The forward inclusion was already established from the validity proof.
    exact appendEquiv_image_exercise_5_10_cut_face_subset_activeConstraintFace a g b
  · -- The reverse inclusion is the only remaining structural bridge.
    exact activeConstraintFace_subset_appendEquiv_image_exercise_5_10_cut_face
      a g b ha_relatively_prime hb_nonint

/-- Helper for Exercise 5.10: once the flattened cut face is identified with the singleton active
face of row `1`, the Chapter 3 singleton-row criterion upgrades it to a facet of `P'`. -/
lemma exercise_5_10_flat_cut_face_isFacet
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    is_facet
      (polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b))
      (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b) := by
  have hrow_not_implicit :
      ¬ is_implicit_equality
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          1 :=
    exercise_5_10_cutRow_not_implicit a g b ha_relatively_prime hb_nonint
  have hrow_remaining :
      1 ∈ remaining_inequality_indices
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b) :=
    (mem_remaining_inequality_indices_iff
      (exercise_5_10_facetMatrix a g b)
      (exercise_5_10_facetRhs p b)
      1).2 hrow_not_implicit
  have hrow_irredundant :
      is_irredundant_row
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        1 :=
    exercise_5_10_cutRow_irredundant a g b ha_relatively_prime hb_nonint
  have hcut_face_nonempty :
      (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b).Nonempty := by
    rcases exercise_5_10_cut_face_nonempty a g b ha_relatively_prime with ⟨xy, hxy⟩
    exact ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩⟩
  have hactive_nonempty :
      (active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2)))).Nonempty := by
    simpa [appendEquiv_image_exercise_5_10_cut_face_eq_activeConstraintFace
      a g b ha_relatively_prime hb_nonint] using hcut_face_nonempty
  have hactive_codim :
      Module.finrank ℝ
          (affineSpan ℝ
            (active_constraint_face
              (exercise_5_10_facetMatrix a g b)
              (exercise_5_10_facetRhs p b)
              ({1} : Set (Fin (p + 2))))).direction + 1 =
        Module.finrank ℝ
          (affineSpan ℝ
            (polyhedron_le_set
              (exercise_5_10_facetMatrix a g b)
              (exercise_5_10_facetRhs p b))).direction := by
    simpa [appendEquiv_image_exercise_5_10_cut_face_eq_activeConstraintFace
      a g b ha_relatively_prime hb_nonint] using
      (finrank_direction_affineSpan_add_one_eq_of_irredundant_singleton
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        1
        hrow_remaining
        hrow_irredundant)
  have hfacet_active :
      is_facet
        (polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b))
        (active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2)))) :=
    isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
      (exercise_5_10_facetMatrix a g b)
      (exercise_5_10_facetRhs p b)
      (active_constraint_face
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        ({1} : Set (Fin (p + 2))))
      (active_constraint_face_isExposed
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        ({1} : Set (Fin (p + 2))))
      hactive_nonempty
      hactive_codim
  simpa [appendEquiv_image_exercise_5_10_cut_face_eq_activeConstraintFace
    a g b ha_relatively_prime hb_nonint] using hfacet_active

/-- Helper for Exercise 5.10: the ambient affine spans of the flattened mixed-integer hull and the
explicit flat owner `P'` coincide once they are tied together by one strict cut point and the
common singleton facet. -/
lemma appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_affineSpan_eq_facetPolyhedron
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    affineSpan ℝ (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)) =
      affineSpan ℝ
        (polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b)) := by
  let Q : Set (Fin (n + p) → ℝ) :=
    Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b)
  let P' : Set (Fin (n + p) → ℝ) :=
    polyhedron_le_set (exercise_5_10_facetMatrix a g b) (exercise_5_10_facetRhs p b)
  rcases exercise_5_10_exists_strict_cut_point a g b ha_relatively_prime hb_nonint with
    ⟨xy, hxy_hull, hxy_strict⟩
  have hsubset : Q ⊆ P' := by
    simpa [Q, P'] using
      appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_subset_facetPolyhedron a g b
  have hflat_strict_mem : Fin.appendEquiv n p xy ∈ P' := by
    exact hsubset ⟨xy, hxy_hull, rfl⟩
  have hflat_strict_lt :
      Matrix.mulVec (exercise_5_10_facetMatrix a g b) (Fin.appendEquiv n p xy) 1 <
        exercise_5_10_facetRhs p b 1 := by
    have hflat :
        exercise_5_10_flat_cut_vector a g b ⬝ᵥ Fin.appendEquiv n p xy < (Int.floor b : ℝ) := by
      simpa [exercise_5_10_flat_cut_vector_dot_appendEquiv_eq_cut_value] using hxy_strict
    simpa [exercise_5_10_facetMatrix, exercise_5_10_facetRhs, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hflat
  have hfacet_flat :
      is_facet P'
        (active_constraint_face
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          ({1} : Set (Fin (p + 2)))) := by
    simpa [P',
      appendEquiv_image_exercise_5_10_cut_face_eq_activeConstraintFace
        a g b ha_relatively_prime hb_nonint]
      using exercise_5_10_flat_cut_face_isFacet a g b ha_relatively_prime hb_nonint
  have hambient :
      affineSpan ℝ P' =
        affineSpan ℝ
          ({Fin.appendEquiv n p xy} ∪
            active_constraint_face
              (exercise_5_10_facetMatrix a g b)
              (exercise_5_10_facetRhs p b)
              ({1} : Set (Fin (p + 2)))) := by
    simpa [P'] using
      ambientAffineHull_eq_affineSpan_strictPoint_union_singletonFacet
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        1
        hfacet_flat
        hflat_strict_mem
        hflat_strict_lt
  have hunion_subset : ({Fin.appendEquiv n p xy} ∪
      active_constraint_face
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        ({1} : Set (Fin (p + 2)))) ⊆ Q := by
    intro u hu
    rcases hu with rfl | huFace
    · exact ⟨xy, hxy_hull, rfl⟩
    · rcases
        activeConstraintFace_subset_appendEquiv_image_exercise_5_10_cut_face
          a g b ha_relatively_prime hb_nonint huFace with
        ⟨xyFace, hxyFace, rfl⟩
      exact ⟨xyFace, hxyFace.1, rfl⟩
  apply le_antisymm
  · exact affineSpan_mono ℝ hsubset
  · rw [hambient]
    exact affineSpan_mono ℝ hunion_subset

/-- Exercise 5.10 (2). Under the same hypotheses, the inequality from Exercise 5.10 (1) defines
a facet of `conv(S)`. The relative-primality assumption already excludes the zero row. -/
theorem exercise_5_10_cut_defines_facet
    (a : Fin n → ℤ)
    (g : Fin p → ℝ)
    (b : ℝ)
    (ha_relatively_prime : Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (a j)) = 1)
    (hb_nonint : ¬ ∃ z : ℤ, b = (z : ℝ)) :
    IsFacetOf
      (convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
      (exercise_5_10_cut_face a g b) := by
  have hface_nonempty :
      (exercise_5_10_cut_face a g b).Nonempty :=
    exercise_5_10_cut_face_nonempty a g b ha_relatively_prime
  have hface_exposed :
      IsExposed ℝ
        (convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (exercise_5_10_cut_face a g b) :=
    exercise_5_10_cut_face_isExposed a g b
  have hstrict_cut :
      ∃ xy : MixedRealPoint n p,
        xy ∈ convexHull ℝ (exercise_5_10_mixed_integer_set a g b) ∧
          exercise_5_10_cut_value a g b xy < (Int.floor b : ℝ) :=
    exercise_5_10_exists_strict_cut_point a g b ha_relatively_prime hb_nonint
  have hcut_row_irredundant :
      is_irredundant_row
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b)
        1 :=
    exercise_5_10_cutRow_irredundant a g b ha_relatively_prime hb_nonint
  let eL : MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  let e : MixedRealPoint n p ≃L[ℝ] (Fin (n + p) → ℝ) := eL.toContinuousLinearEquiv
  have hflat_nonempty :
      (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b).Nonempty := by
    rcases hface_nonempty with ⟨xy, hxy⟩
    exact ⟨Fin.appendEquiv n p xy, ⟨xy, hxy, rfl⟩⟩
  have hflat_exposed :
      IsExposed ℝ
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b) := by
    -- Transport the exposed-face structure along the flattening equivalence.
    simpa [e] using isExposed_image_continuousLinearEquiv e hface_exposed
  have hrow_not_implicit :
      ¬ is_implicit_equality
          (exercise_5_10_facetMatrix a g b)
          (exercise_5_10_facetRhs p b)
          1 :=
    exercise_5_10_cutRow_not_implicit a g b ha_relatively_prime hb_nonint
  have hrow_remaining :
      1 ∈ remaining_inequality_indices
        (exercise_5_10_facetMatrix a g b)
        (exercise_5_10_facetRhs p b) :=
    (mem_remaining_inequality_indices_iff
      (exercise_5_10_facetMatrix a g b)
      (exercise_5_10_facetRhs p b)
      1).2 hrow_not_implicit
  have hflat_codim :
      Module.finrank ℝ
          (affineSpan ℝ (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b)).direction + 1 =
        Module.finrank ℝ
          (affineSpan ℝ
            (Fin.appendEquiv n p '' convexHull ℝ
              (exercise_5_10_mixed_integer_set a g b))).direction := by
    -- Rewrite both the face and the ambient owner to the singleton active face inside `P'`.
    rw [appendEquiv_image_exercise_5_10_cut_face_eq_activeConstraintFace
      a g b ha_relatively_prime hb_nonint]
    rw [appendEquiv_image_convexHull_exercise_5_10_mixed_integer_set_affineSpan_eq_facetPolyhedron
      a g b ha_relatively_prime hb_nonint]
    exact finrank_direction_affineSpan_add_one_eq_of_irredundant_singleton
      (exercise_5_10_facetMatrix a g b)
      (exercise_5_10_facetRhs p b)
      1
      hrow_remaining
      hcut_row_irredundant
  have hflat_facet :
      IsFacetOf
        (Fin.appendEquiv n p '' convexHull ℝ (exercise_5_10_mixed_integer_set a g b))
        (Fin.appendEquiv n p '' exercise_5_10_cut_face a g b) :=
    (isFacetOf_iff).2 ⟨hflat_nonempty, hflat_exposed, hflat_codim⟩
  -- Pull the flat facet statement back through `Fin.appendEquiv`.
  simpa [e] using (isFacetOf_image_continuousLinearEquiv e).2 hflat_facet

end Exercise510
