/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_5.ch5_sec5_1_5_theorem_5_12

open scoped Matrix

-- This example reuses the Chapter 3/5 owners `polyhedron_le_set`,
-- `mixed_integer_feasible_set`, and `mixed_split_closure`.

section Example511

/- Source-facing layer: the concrete simplex and mixed-integer set from Example 5.11 are kept in
`Fin 3 → ℝ` coordinates. Core/canonical layer: the simplex is presented through its matrix owner,
and the mixed-integer set is presented through the Chapter 5 owner
`mixed_integer_feasible_set`. -/

/-- A matrix presentation of the simplex from Example 5.11 in the coordinate order
`(x₁, x₂, y)`. -/
def example_5_11_matrix : Matrix (Fin 4) (Fin 3) ℝ :=
  ![![-1, 0, 1],
    ![0, -1, 1],
    ![1, 1, 2],
    ![0, 0, -1]]

/-- The right-hand side vector for `example_5_11_matrix`. -/
def example_5_11_rhs : Fin 4 → ℝ :=
  ![0, 0, 2, 0]

/-- The integer-variable index set `I = {x₁, x₂}` from Example 5.11. -/
def example_5_11_integer_indices : Finset (Fin 3) :=
  {0, 1}

/-- The simplex `P = {(x₁, x₂, y) ∈ ℝ³_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}` from
Example 5.11, written in `Fin 3 → ℝ` coordinates. -/
def example_5_11_polyhedron : Set (Fin 3 → ℝ) :=
  polyhedron_le_set example_5_11_matrix example_5_11_rhs

/-- Membership in `example_5_11_polyhedron` is exactly the explicit nonnegativity and simplex
inequality system from Example 5.11. -/
theorem mem_example_5_11_polyhedron_iff
    {v : Fin 3 → ℝ} :
    v ∈ example_5_11_polyhedron ↔
      0 ≤ v 0 ∧
        0 ≤ v 1 ∧
          0 ≤ v 2 ∧
            v 2 ≤ v 0 ∧
              v 2 ≤ v 1 ∧
                v 0 + v 1 + 2 * v 2 ≤ 2 := by
  rw [example_5_11_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hv
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    have h3 := hv 3
    norm_num [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      at h0 h1 h2 h3
    have hyx0 : v 2 ≤ v 0 := by
      simpa using h0
    have hyx1 : v 2 ≤ v 1 := by
      simpa using h1
    have hineq : v 0 + v 1 + 2 * v 2 ≤ 2 := by
      simpa using h2
    have hy : 0 ≤ v 2 := by
      have h3' : -v 2 ≤ 0 := by
        simpa using h3
      linarith
    have hx0 : 0 ≤ v 0 := by
      linarith
    have hx1 : 0 ≤ v 1 := by
      linarith
    exact ⟨hx0, hx1, hy, hyx0, hyx1, hineq⟩
  · rintro ⟨hx0, hx1, hy, hyx0, hyx1, hineq⟩ i
    fin_cases i
    · simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hyx0
    · simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hyx1
    · simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hineq
    · have h3 : -v 2 ≤ 0 := by
        linarith
      simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using h3

/-- The mixed-integer set
`S = {(x₁, x₂, y) ∈ ℤ²_+ × ℝ_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}` from Example 5.11. -/
def example_5_11_mixed_integer_set : Set (Fin 3 → ℝ) :=
  mixed_integer_feasible_set
    example_5_11_matrix
    example_5_11_rhs
    example_5_11_integer_indices

/-- Membership in `example_5_11_mixed_integer_set` means feasibility in
`example_5_11_polyhedron` together with integrality of the first two coordinates. -/
theorem mem_example_5_11_mixed_integer_set_iff
    {v : Fin 3 → ℝ} :
    v ∈ example_5_11_mixed_integer_set ↔
      v ∈ example_5_11_polyhedron ∧
        (∃ z : ℤ, v 0 = (z : ℝ)) ∧
          ∃ z : ℤ, v 1 = (z : ℝ) := by
  rw [example_5_11_mixed_integer_set, mem_mixed_integer_feasible_set_iff]
  constructor
  · rintro ⟨hv, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · change v ∈ polyhedron_le_set example_5_11_matrix example_5_11_rhs
      exact (mem_polyhedron_le_set_iff).2 hv
    · exact hint 0 (by simp [example_5_11_integer_indices])
    · exact hint 1 (by simp [example_5_11_integer_indices])
  · rintro ⟨hv, hz0, hz1⟩
    refine ⟨?_, ?_⟩
    · have hv' : v ∈ polyhedron_le_set example_5_11_matrix example_5_11_rhs := by
        simpa [example_5_11_polyhedron] using hv
      exact (mem_polyhedron_le_set_iff).1 hv'
    · intro j hj
      fin_cases j
      · simpa [example_5_11_integer_indices] using hz0
      · simpa [example_5_11_integer_indices] using hz1
      · simp [example_5_11_integer_indices] at hj

/-- The `k`-fold mixed split closure `P^k` of the Example 5.11 simplex relative to the integer
coordinates `I = {x₁, x₂}`. -/
def example_5_11_iterated_split_closure (k : ℕ) : Set (Fin 3 → ℝ) :=
  (mixed_split_closure example_5_11_integer_indices)^[k] example_5_11_polyhedron

/-- The zeroth mixed split closure `P⁰` of Example 5.11 is the original simplex `P`. -/
theorem example_5_11_iterated_split_closure_zero :
    example_5_11_iterated_split_closure 0 = example_5_11_polyhedron :=
  rfl

/-- The recursive step `P^(k + 1) = (P^k)^split` for the Example 5.11 mixed split-closure
sequence relative to `I = {x₁, x₂}`. -/
theorem example_5_11_iterated_split_closure_succ
    (k : ℕ) :
    example_5_11_iterated_split_closure (k + 1) =
      mixed_split_closure example_5_11_integer_indices
        (example_5_11_iterated_split_closure k) := by
  simp [example_5_11_iterated_split_closure, Function.iterate_succ_apply']

/-- Helper for Example 5.11: supported splits on `I = {x₁, x₂}` ignore the continuous
coordinate `y`. -/
private lemma example511_splitDot_eq
    (s : Split ((↑example_5_11_integer_indices : Set (Fin 3)).toFinite.toFinset))
    (v : Fin 3 → ℝ) :
    split_dot s v = (s 0 : ℝ) * v 0 + (s 1 : ℝ) * v 1 := by
  -- Rewrite the supported split sum so only the two integer coordinates remain.
  rw [splitDot_eq_sum_filterIntegerIndices]
  simp [example_5_11_integer_indices]

/-- Helper for Example 5.11: any ambient point with integral first two coordinates already lies
in the split hull of the current ambient set. -/
private lemma example511_memSplitHull_of_integralFirstTwo
    {Q : Set (Fin 3 → ℝ)}
    {v : Fin 3 → ℝ}
    (hvQ : v ∈ Q)
    (hz0 : ∃ z : ℤ, v 0 = (z : ℝ))
    (hz1 : ∃ z : ℤ, v 1 = (z : ℝ))
    (s : Split ((↑example_5_11_integer_indices : Set (Fin 3)).toFinite.toFinset)) :
    v ∈ split_hull Q s s.π0 := by
  have hInt :
      ∀ j ∈ ((↑example_5_11_integer_indices : Set (Fin 3)).toFinite.toFinset),
        ∃ z : ℤ, v j = (z : ℝ) := by
    intro j hj
    fin_cases j
    · simpa [example_5_11_integer_indices] using hz0
    · simpa [example_5_11_integer_indices] using hz1
    · simp [example_5_11_integer_indices] at hj
  -- The split value is integral, so the point lies on one side of the disjunction.
  rcases split_dot_integral_of_integral_coordinates
      ((↑example_5_11_integer_indices : Set (Fin 3)).toFinite.toFinset) s hInt with
    ⟨z, hz⟩
  have hz' : split_dot s.π v = (z : ℝ) := by
    simpa using hz
  by_cases hle : z ≤ s.π0
  · have hvLower : v ∈ split_branch_lower Q s s.π0 := by
      refine (mem_split_branch_lower_iff).2 ⟨hvQ, ?_⟩
      have hleR : (z : ℝ) ≤ (s.π0 : ℝ) := by
        exact_mod_cast hle
      simpa [hz'] using hleR
    simpa [split_hull] using
      (subset_convexHull ℝ
        (split_branch_lower Q s s.π0 ∪ split_branch_upper Q s s.π0)
        (Or.inl hvLower))
  · have hge : s.π0 + 1 ≤ z := by
      omega
    have hvUpper : v ∈ split_branch_upper Q s s.π0 := by
      refine (mem_split_branch_upper_iff).2 ⟨hvQ, ?_⟩
      have hgeR : (s.π0 : ℝ) + 1 ≤ (z : ℝ) := by
        exact_mod_cast hge
      simpa [hz'] using hgeR
    simpa [split_hull] using
      (subset_convexHull ℝ
        (split_branch_lower Q s s.π0 ∪ split_branch_upper Q s s.π0)
        (Or.inr hvUpper))

/-- Helper for Example 5.11: any ambient point with integral first two coordinates survives one
mixed split closure step. -/
private lemma memMixedSplitClosure_of_integralFirstTwo
    {Q : Set (Fin 3 → ℝ)}
    {v : Fin 3 → ℝ}
    (hvQ : v ∈ Q)
    (hz0 : ∃ z : ℤ, v 0 = (z : ℝ))
    (hz1 : ∃ z : ℤ, v 1 = (z : ℝ)) :
    v ∈ mixed_split_closure example_5_11_integer_indices Q := by
  -- Membership in the mixed split closure is ambient membership plus membership in every split hull.
  rw [mem_mixed_split_closure_iff]
  refine ⟨hvQ, ?_⟩
  intro s
  exact example511_memSplitHull_of_integralFirstTwo hvQ hz0 hz1 s

/-- Helper for Example 5.11: every iterated mixed split closure remains convex. -/
private theorem example511_iteratedSplitClosureConvex
    (k : ℕ) :
    Convex ℝ (example_5_11_iterated_split_closure k) := by
  induction k with
  | zero =>
      -- The base iterate is the original simplex `P`.
      simpa [example_5_11_iterated_split_closure_zero] using
        polyhedron_le_set_convex example_5_11_matrix example_5_11_rhs
  | succ k ih =>
      -- The successor iterate is the ambient convex set intersected with every convex split hull.
      rw [example_5_11_iterated_split_closure_succ, mixed_split_closure]
      refine ih.inter ?_
      refine convex_iInter ?_
      intro s
      simpa [split_hull] using
        (convex_convexHull ℝ
          (split_branch_lower (example_5_11_iterated_split_closure k) s s.π0 ∪
            split_branch_upper (example_5_11_iterated_split_closure k) s s.π0))

/-- Helper for Example 5.11: every integral point of the base mixed-integer set survives every
iterated mixed split closure. -/
private theorem example511_mixedIntegerPoint_mem_iteratedSplitClosure
    {v : Fin 3 → ℝ}
    (hv : v ∈ example_5_11_mixed_integer_set) :
    ∀ k : ℕ, v ∈ example_5_11_iterated_split_closure k := by
  intro k
  induction k with
  | zero =>
      -- At level zero the mixed-integer point is already in the original simplex `P`.
      rcases (mem_example_5_11_mixed_integer_set_iff.mp hv) with ⟨hvP, _, _⟩
      simpa [example_5_11_iterated_split_closure_zero] using hvP
  | succ k ih =>
      -- One more mixed split closure step preserves the point because every split value is integral.
      rcases (mem_example_5_11_mixed_integer_set_iff.mp hv) with ⟨_, hz0, hz1⟩
      rw [example_5_11_iterated_split_closure_succ]
      exact memMixedSplitClosure_of_integralFirstTwo ih hz0 hz1

/-- Helper for Example 5.11: every integral base point `(x₁, x₂, 0)` with `x₁ + x₂ ≤ 2`
belongs to the mixed-integer set `S`. -/
private lemma example511_planePoint_memMixedIntegerSet
    {x1 x2 : ℤ}
    (hx1 : 0 ≤ x1)
    (hx2 : 0 ≤ x2)
    (hsum : x1 + x2 ≤ 2) :
    ![(x1 : ℝ), (x2 : ℝ), 0] ∈ example_5_11_mixed_integer_set := by
  rw [mem_example_5_11_mixed_integer_set_iff]
  refine ⟨?_, ⟨x1, by simp⟩, ⟨x2, by simp⟩⟩
  -- The explicit point lies in the simplex because its third coordinate is zero.
  rw [mem_example_5_11_polyhedron_iff]
  have hx1R : 0 ≤ (x1 : ℝ) := by
    exact_mod_cast hx1
  have hx2R : 0 ≤ (x2 : ℝ) := by
    exact_mod_cast hx2
  have hsumR : (x1 : ℝ) + (x2 : ℝ) ≤ 2 := by
    exact_mod_cast hsum
  refine ⟨hx1R, hx2R, by simp, by simpa using hx1R, by simpa using hx2R, ?_⟩
  simpa using hsumR

/-- Helper for Example 5.11: every point of the mixed-integer set lies in the plane `y = 0`. -/
private lemma example511_y_eq_zero_of_memMixedIntegerSet
    {v : Fin 3 → ℝ}
    (hv : v ∈ example_5_11_mixed_integer_set) :
    v 2 = 0 := by
  rcases (mem_example_5_11_mixed_integer_set_iff.mp hv) with ⟨hvP, hz0, hz1⟩
  rcases (mem_example_5_11_polyhedron_iff.mp hvP) with
    ⟨hx0, hx1, hy, hyx0, hyx1, hineq⟩
  by_contra hne
  -- A positive `y` would force both integer coordinates to be at least `1`, contradicting the sum bound.
  have hne0 : (0 : ℝ) ≠ v 2 := by
    intro h
    exact hne h.symm
  have hyPos : 0 < v 2 := lt_of_le_of_ne hy hne0
  have hv0Pos : 0 < v 0 := lt_of_lt_of_le hyPos hyx0
  have hv1Pos : 0 < v 1 := lt_of_lt_of_le hyPos hyx1
  rcases hz0 with ⟨z0, hz0⟩
  rcases hz1 with ⟨z1, hz1⟩
  have hz0PosR : 0 < (z0 : ℝ) := by
    simpa [hz0] using hv0Pos
  have hz1PosR : 0 < (z1 : ℝ) := by
    simpa [hz1] using hv1Pos
  have hz0Pos : 0 < z0 := by
    exact_mod_cast hz0PosR
  have hz1Pos : 0 < z1 := by
    exact_mod_cast hz1PosR
  have hz0One : (1 : ℤ) ≤ z0 := by
    omega
  have hz1One : (1 : ℤ) ≤ z1 := by
    omega
  have hz0OneR : (1 : ℝ) ≤ (z0 : ℝ) := by
    exact_mod_cast hz0One
  have hz1OneR : (1 : ℝ) ≤ (z1 : ℝ) := by
    exact_mod_cast hz1One
  linarith

/-- The witness point `((1 / 2), (1 / 2), (1 / 2) / 3^k)` remains in the `k`-fold mixed split
closure of the Example 5.11 simplex relative to `I = {x₁, x₂}`. -/
theorem example_5_11_witness_mem_iterated_split_closure
    (k : ℕ) :
    ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ) / (3 : ℝ) ^ k] ∈
      example_5_11_iterated_split_closure k := by
  let w : ℕ → Fin 3 → ℝ :=
    fun n ↦ ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ) / (3 : ℝ) ^ n]
  suffices hw : ∀ n : ℕ, w n ∈ example_5_11_iterated_split_closure n by
    simpa [w] using hw k
  intro n
  induction n with
  | zero =>
      -- The initial witness is the top vertex `C` of the simplex `P`.
      rw [example_5_11_iterated_split_closure_zero]
      refine (mem_example_5_11_polyhedron_iff).2 ?_
      refine ⟨by norm_num [w], by norm_num [w],
        by simpa [w] using (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num),
        by simpa [w] using (show (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) by norm_num),
        by simpa [w] using (show (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) by norm_num),
        by simpa [w] using
          (show (1 / 2 : ℝ) + (1 / 2 : ℝ) + 2 * (1 / 2 : ℝ) ≤ 2 by norm_num)⟩
  | succ n ih =>
      let mid : Fin 3 → ℝ := ![(1 / 2 : ℝ), (1 / 2 : ℝ), 0]
      let o : Fin 3 → ℝ := ![0, 0, 0]
      let e1 : Fin 3 → ℝ := ![1, 0, 0]
      let e2 : Fin 3 → ℝ := ![0, 1, 0]
      let a : Fin 3 → ℝ := ![2, 0, 0]
      let b : Fin 3 → ℝ := ![0, 2, 0]
      let t : ℝ := (1 / 2 : ℝ) / (3 : ℝ) ^ n
      let cA : Fin 3 → ℝ := ![(1 : ℝ), (1 / 3 : ℝ), (2 / 3 : ℝ) * t]
      let cB : Fin 3 → ℝ := ![(1 / 3 : ℝ), (1 : ℝ), (2 / 3 : ℝ) * t]
      let dA : Fin 3 → ℝ := ![0, (2 / 3 : ℝ), 0]
      let dB : Fin 3 → ℝ := ![(2 / 3 : ℝ), 0, 0]
      have hConvex : Convex ℝ (example_5_11_iterated_split_closure n) :=
        example511_iteratedSplitClosureConvex n
      have he1Mixed : e1 ∈ example_5_11_mixed_integer_set := by
        simpa [e1] using
          example511_planePoint_memMixedIntegerSet (x1 := 1) (x2 := 0) (by omega) (by omega)
            (by omega)
      have he2Mixed : e2 ∈ example_5_11_mixed_integer_set := by
        simpa [e2] using
          example511_planePoint_memMixedIntegerSet (x1 := 0) (x2 := 1) (by omega) (by omega)
            (by omega)
      have hoMixed : o ∈ example_5_11_mixed_integer_set := by
        simpa [o] using
          example511_planePoint_memMixedIntegerSet (x1 := 0) (x2 := 0) (by omega) (by omega)
            (by omega)
      have haMixed : a ∈ example_5_11_mixed_integer_set := by
        simpa [a] using
          example511_planePoint_memMixedIntegerSet (x1 := 2) (x2 := 0) (by omega) (by omega)
            (by omega)
      have hbMixed : b ∈ example_5_11_mixed_integer_set := by
        simpa [b] using
          example511_planePoint_memMixedIntegerSet (x1 := 0) (x2 := 2) (by omega) (by omega)
            (by omega)
      have huMixed : ![(1 : ℝ), (1 : ℝ), 0] ∈ example_5_11_mixed_integer_set := by
        simpa using
          example511_planePoint_memMixedIntegerSet (x1 := 1) (x2 := 1) (by omega) (by omega)
            (by omega)
      have he1 : e1 ∈ example_5_11_iterated_split_closure n :=
        example511_mixedIntegerPoint_mem_iteratedSplitClosure he1Mixed n
      have he2 : e2 ∈ example_5_11_iterated_split_closure n :=
        example511_mixedIntegerPoint_mem_iteratedSplitClosure he2Mixed n
      have ho : o ∈ example_5_11_iterated_split_closure n :=
        example511_mixedIntegerPoint_mem_iteratedSplitClosure hoMixed n
      have ha : a ∈ example_5_11_iterated_split_closure n :=
        example511_mixedIntegerPoint_mem_iteratedSplitClosure haMixed n
      have hb : b ∈ example_5_11_iterated_split_closure n :=
        example511_mixedIntegerPoint_mem_iteratedSplitClosure hbMixed n
      have hpow : (3 : ℝ) ^ n ≠ 0 := by
        positivity
      have hwt : w n = ![(1 / 2 : ℝ), (1 / 2 : ℝ), t] := by
        simp [w, t]
      have hwsuccZ : (1 / 2 : ℝ) / (3 : ℝ) ^ (n + 1) = t / 3 := by
        dsimp [t]
        rw [pow_succ]
        field_simp [hpow]
      have hwsucc : w (n + 1) = ![(1 / 2 : ℝ), (1 / 2 : ℝ), t / 3] := by
        ext i <;> fin_cases i
        · simp [w]
        · simp [w]
        · simpa [w] using hwsuccZ
      have hmid_eq : mid = midpoint ℝ e1 e2 := by
        ext i <;> fin_cases i <;> simp [mid, e1, e2, midpoint_eq_smul_add]
      have hw_line : w (n + 1) = AffineMap.lineMap mid (w n) (1 / 3 : ℝ) := by
        ext i <;> fin_cases i
        · norm_num [mid, hwt, hwsucc, AffineMap.lineMap_apply_module]
        · norm_num [mid, hwt, hwsucc, AffineMap.lineMap_apply_module]
        · have hthird : t / 3 = (1 / 3 : ℝ) * t := by ring
          simpa [mid, hwt, hwsucc, AffineMap.lineMap_apply_module] using hthird
      have hcA_line : cA = AffineMap.lineMap (w n) a (1 / 3 : ℝ) := by
        ext i <;> fin_cases i
        · norm_num [cA, a, hwt, AffineMap.lineMap_apply_module]
        · norm_num [cA, a, hwt, AffineMap.lineMap_apply_module]
        · have hthird : (2 / 3 : ℝ) * t = (1 - (1 / 3 : ℝ)) * t + (1 / 3 : ℝ) * 0 := by
            ring
          simpa [cA, a, hwt, AffineMap.lineMap_apply_module] using hthird
      have hcB_line : cB = AffineMap.lineMap (w n) b (1 / 3 : ℝ) := by
        ext i <;> fin_cases i
        · norm_num [cB, b, hwt, AffineMap.lineMap_apply_module]
        · norm_num [cB, b, hwt, AffineMap.lineMap_apply_module]
        · have hthird : (2 / 3 : ℝ) * t = (1 - (1 / 3 : ℝ)) * t + (1 / 3 : ℝ) * 0 := by
            ring
          simpa [cB, b, hwt, AffineMap.lineMap_apply_module] using hthird
      have hdA_line : dA = AffineMap.lineMap o b (1 / 3 : ℝ) := by
        ext i <;> fin_cases i
        · norm_num [dA, o, b, AffineMap.lineMap_apply_module]
        · norm_num [dA, o, b, AffineMap.lineMap_apply_module]
        · simp [dA, o, b, AffineMap.lineMap_apply_module]
      have hdB_line : dB = AffineMap.lineMap o a (1 / 3 : ℝ) := by
        ext i <;> fin_cases i
        · norm_num [dB, o, a, AffineMap.lineMap_apply_module]
        · norm_num [dB, o, a, AffineMap.lineMap_apply_module]
        · simp [dB, o, a, AffineMap.lineMap_apply_module]
      have hw_mid_cA : w (n + 1) = midpoint ℝ dA cA := by
        ext i <;> fin_cases i
        · norm_num [dA, cA, hwsucc, midpoint_eq_smul_add]
        · norm_num [dA, cA, hwsucc, midpoint_eq_smul_add]
        · have hthird : t / 3 = (1 / 2 : ℝ) * ((2 / 3 : ℝ) * t) := by ring
          simpa [dA, cA, hwsucc, midpoint_eq_smul_add] using hthird
      have hw_mid_cB : w (n + 1) = midpoint ℝ dB cB := by
        ext i <;> fin_cases i
        · norm_num [dB, cB, hwsucc, midpoint_eq_smul_add]
        · norm_num [dB, cB, hwsucc, midpoint_eq_smul_add]
        · have hthird : t / 3 = (1 / 2 : ℝ) * ((2 / 3 : ℝ) * t) := by ring
          simpa [dB, cB, hwsucc, midpoint_eq_smul_add] using hthird
      rw [example_5_11_iterated_split_closure_succ, mem_mixed_split_closure_iff]
      refine ⟨?_, ?_⟩
      · -- First keep the next witness inside the ambient iterate `P^n`.
        have hmid_mem : mid ∈ example_5_11_iterated_split_closure n := by
          rw [hmid_eq]
          exact hConvex.midpoint_mem he1 he2
        simpa [hw_line, AffineMap.lineMap_apply_module] using
          (hConvex hmid_mem ih (by positivity) (by positivity)
            (by norm_num : (1 - (1 / 3 : ℝ)) + (1 / 3 : ℝ) = 1))
      · intro s
        have hSplitConvex :
            Convex ℝ (split_hull (example_5_11_iterated_split_closure n) s s.π0) := by
          simpa [split_hull] using
            (convex_convexHull ℝ
              (split_branch_lower (example_5_11_iterated_split_closure n) s s.π0 ∪
                split_branch_upper (example_5_11_iterated_split_closure n) s s.π0))
        have he1Hull :
            e1 ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 :=
          example511_memSplitHull_of_integralFirstTwo he1 ⟨1, by simp [e1]⟩ ⟨0, by simp [e1]⟩ s
        have he2Hull :
            e2 ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 :=
          example511_memSplitHull_of_integralFirstTwo he2 ⟨0, by simp [e2]⟩ ⟨1, by simp [e2]⟩ s
        have hoHull :
            o ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 :=
          example511_memSplitHull_of_integralFirstTwo ho ⟨0, by simp [o]⟩ ⟨0, by simp [o]⟩ s
        have haHull :
            a ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 :=
          example511_memSplitHull_of_integralFirstTwo ha ⟨2, by simp [a]⟩ ⟨0, by simp [a]⟩ s
        have hbHull :
            b ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 :=
          example511_memSplitHull_of_integralFirstTwo hb ⟨0, by simp [b]⟩ ⟨2, by simp [b]⟩ s
        have hmidHull : mid ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
          rw [hmid_eq]
          exact hSplitConvex.midpoint_mem he1Hull he2Hull
        have hdAHull : dA ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
          simpa [hdA_line, AffineMap.lineMap_apply_module] using
            (hSplitConvex hoHull hbHull (by positivity) (by positivity)
              (by norm_num : (1 - (1 / 3 : ℝ)) + (1 / 3 : ℝ) = 1))
        have hdBHull : dB ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
          simpa [hdB_line, AffineMap.lineMap_apply_module] using
            (hSplitConvex hoHull haHull (by positivity) (by positivity)
              (by norm_num : (1 - (1 / 3 : ℝ)) + (1 / 3 : ℝ) = 1))
        have hsplitW : split_dot s (w n) = ((s 0 : ℝ) + (s 1 : ℝ)) / 2 := by
          rw [example511_splitDot_eq (s := s)]
          simp [hwt]
          ring
        by_cases hLower : split_dot s (w n) ≤ (s.π0 : ℝ)
        · -- If the current witness already lies on the lower side, the segment to the base midpoint
          -- keeps the next witness inside the split hull.
          have hwHull :
              w n ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
            simpa [split_hull] using
              (subset_convexHull ℝ
                (split_branch_lower (example_5_11_iterated_split_closure n) s s.π0 ∪
                  split_branch_upper (example_5_11_iterated_split_closure n) s s.π0)
                (Or.inl ((mem_split_branch_lower_iff).2 ⟨ih, hLower⟩)))
          simpa [hw_line, AffineMap.lineMap_apply_module] using
            (hSplitConvex hmidHull hwHull (by positivity) (by positivity)
              (by norm_num : (1 - (1 / 3 : ℝ)) + (1 / 3 : ℝ) = 1))
        · by_cases hUpper : (s.π0 : ℝ) + 1 ≤ split_dot s (w n)
          · -- The upper-side case is symmetric to the lower-side case.
            have hwHull :
                w n ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
              simpa [split_hull] using
                (subset_convexHull ℝ
                  (split_branch_lower (example_5_11_iterated_split_closure n) s s.π0 ∪
                    split_branch_upper (example_5_11_iterated_split_closure n) s s.π0)
                  (Or.inr ((mem_split_branch_upper_iff).2 ⟨ih, hUpper⟩)))
            simpa [hw_line, AffineMap.lineMap_apply_module] using
              (hSplitConvex hmidHull hwHull (by positivity) (by positivity)
                (by norm_num : (1 - (1 / 3 : ℝ)) + (1 / 3 : ℝ) = 1))
          · -- In the strip case, one of the two edge points `cA` or `cB` survives the split.
            have hgt : (s.π0 : ℝ) < split_dot s (w n) := lt_of_not_ge hLower
            have hlt : split_dot s (w n) < (s.π0 : ℝ) + 1 := lt_of_not_ge hUpper
            have hsumLowerR : (2 * s.π0 : ℝ) < (s 0 : ℝ) + (s 1 : ℝ) := by
              nlinarith [hgt, hsplitW]
            have hsumUpperR : (s 0 : ℝ) + (s 1 : ℝ) < (2 * s.π0 + 2 : ℝ) := by
              nlinarith [hlt, hsplitW]
            have hsumLower : 2 * s.π0 < s 0 + s 1 := by
              exact_mod_cast hsumLowerR
            have hsumUpper : s 0 + s 1 < 2 * s.π0 + 2 := by
              exact_mod_cast hsumUpperR
            have hsum : s 0 + s 1 = 2 * s.π0 + 1 := by
              omega
            have hcA_mem : cA ∈ example_5_11_iterated_split_closure n := by
              simpa [hcA_line, AffineMap.lineMap_apply_module] using
                (hConvex ih ha (by positivity) (by positivity)
                  (by norm_num : (1 - (1 / 3 : ℝ)) + (1 / 3 : ℝ) = 1))
            have hcB_mem : cB ∈ example_5_11_iterated_split_closure n := by
              simpa [hcB_line, AffineMap.lineMap_apply_module] using
                (hConvex ih hb (by positivity) (by positivity)
                  (by norm_num : (1 - (1 / 3 : ℝ)) + (1 / 3 : ℝ) = 1))
            have hsplitCA : split_dot s cA = (s 0 : ℝ) + (s 1 : ℝ) / 3 := by
              rw [example511_splitDot_eq (s := s)]
              simp [cA]
              ring
            have hsplitCB : split_dot s cB = (s 0 : ℝ) / 3 + (s 1 : ℝ) := by
              rw [example511_splitDot_eq (s := s)]
              simp [cB]
              ring
            by_cases haLower : s 0 ≤ s.π0
            · have hbUpper : s.π0 + 1 ≤ s 1 := by
                omega
              by_cases hpi0Nonneg : 0 ≤ s.π0
              · have hrUpper : s.π0 + 1 ≤ s 0 + s 1 := by
                  omega
                have hbUpperR : (s.π0 : ℝ) + 1 ≤ (s 1 : ℝ) := by
                  exact_mod_cast hbUpper
                have hrUpperR : (s.π0 : ℝ) + 1 ≤ ((s 0 + s 1 : ℤ) : ℝ) := by
                  exact_mod_cast hrUpper
                rw [Int.cast_add] at hrUpperR
                have hcBUpper :
                    (s.π0 : ℝ) + 1 ≤ split_dot s cB := by
                  rw [hsplitCB]
                  nlinarith [hbUpperR, hrUpperR]
                have hcBHull :
                    cB ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
                  simpa [split_hull] using
                    (subset_convexHull ℝ
                      (split_branch_lower (example_5_11_iterated_split_closure n) s s.π0 ∪
                        split_branch_upper (example_5_11_iterated_split_closure n) s s.π0)
                      (Or.inr ((mem_split_branch_upper_iff).2 ⟨hcB_mem, hcBUpper⟩)))
                rw [hw_mid_cB]
                exact hSplitConvex.midpoint_mem hdBHull hcBHull
              · have hrLower : s 0 + s 1 ≤ s.π0 := by
                  omega
                have haLowerR : (s 0 : ℝ) ≤ (s.π0 : ℝ) := by
                  exact_mod_cast haLower
                have hrLowerR : ((s 0 + s 1 : ℤ) : ℝ) ≤ (s.π0 : ℝ) := by
                  exact_mod_cast hrLower
                rw [Int.cast_add] at hrLowerR
                have hcALower :
                    split_dot s cA ≤ (s.π0 : ℝ) := by
                  rw [hsplitCA]
                  nlinarith [haLowerR, hrLowerR]
                have hcAHull :
                    cA ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
                  simpa [split_hull] using
                    (subset_convexHull ℝ
                      (split_branch_lower (example_5_11_iterated_split_closure n) s s.π0 ∪
                        split_branch_upper (example_5_11_iterated_split_closure n) s s.π0)
                      (Or.inl ((mem_split_branch_lower_iff).2 ⟨hcA_mem, hcALower⟩)))
                rw [hw_mid_cA]
                exact hSplitConvex.midpoint_mem hdAHull hcAHull
            · have haUpper : s.π0 + 1 ≤ s 0 := by
                omega
              have hbLower : s 1 ≤ s.π0 := by
                omega
              by_cases hpi0Nonneg : 0 ≤ s.π0
              · have hrUpper : s.π0 + 1 ≤ s 0 + s 1 := by
                  omega
                have haUpperR : (s.π0 : ℝ) + 1 ≤ (s 0 : ℝ) := by
                  exact_mod_cast haUpper
                have hrUpperR : (s.π0 : ℝ) + 1 ≤ ((s 0 + s 1 : ℤ) : ℝ) := by
                  exact_mod_cast hrUpper
                rw [Int.cast_add] at hrUpperR
                have hcAUpper :
                    (s.π0 : ℝ) + 1 ≤ split_dot s cA := by
                  rw [hsplitCA]
                  nlinarith [haUpperR, hrUpperR]
                have hcAHull :
                    cA ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
                  simpa [split_hull] using
                    (subset_convexHull ℝ
                      (split_branch_lower (example_5_11_iterated_split_closure n) s s.π0 ∪
                        split_branch_upper (example_5_11_iterated_split_closure n) s s.π0)
                      (Or.inr ((mem_split_branch_upper_iff).2 ⟨hcA_mem, hcAUpper⟩)))
                rw [hw_mid_cA]
                exact hSplitConvex.midpoint_mem hdAHull hcAHull
              · have hrLower : s 0 + s 1 ≤ s.π0 := by
                  omega
                have hbLowerR : (s 1 : ℝ) ≤ (s.π0 : ℝ) := by
                  exact_mod_cast hbLower
                have hrLowerR : ((s 0 + s 1 : ℤ) : ℝ) ≤ (s.π0 : ℝ) := by
                  exact_mod_cast hrLower
                rw [Int.cast_add] at hrLowerR
                have hcBLower :
                    split_dot s cB ≤ (s.π0 : ℝ) := by
                  rw [hsplitCB]
                  nlinarith [hbLowerR, hrLowerR]
                have hcBHull :
                    cB ∈ split_hull (example_5_11_iterated_split_closure n) s s.π0 := by
                  simpa [split_hull] using
                    (subset_convexHull ℝ
                      (split_branch_lower (example_5_11_iterated_split_closure n) s s.π0 ∪
                        split_branch_upper (example_5_11_iterated_split_closure n) s s.π0)
                      (Or.inl ((mem_split_branch_lower_iff).2 ⟨hcB_mem, hcBLower⟩)))
                rw [hw_mid_cB]
                exact hSplitConvex.midpoint_mem hdBHull hcBHull

/-- The mixed-integer hull of the Example 5.11 set lies in the plane `y = 0`. -/
theorem example_5_11_mixed_integer_hull_subset_y_eq_zero :
    convexHull ℝ example_5_11_mixed_integer_set ⊆
      {v : Fin 3 → ℝ | v 2 = 0} := by
  -- Every generator of the mixed-integer hull already lies in the plane `y = 0`.
  refine convexHull_min ?_ ?_
  · intro v hv
    simpa using example511_y_eq_zero_of_memMixedIntegerSet hv
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    -- The third coordinate of a convex combination depends only on the third coordinates.
    simp [Pi.add_apply, Pi.smul_apply, hx, hy]

/-- Example 5.11. For the simplex
`P = {(x₁, x₂, y) ∈ ℝ³_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}` and the mixed-integer set
`S = {(x₁, x₂, y) ∈ ℤ²_+ × ℝ_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}`, every positive iterated
mixed split closure `P^k` relative to `I = {x₁, x₂}` is still strictly larger than `conv(S)`. -/
theorem example_5_11_iterated_split_closure_ne_convexHull_mixed_integer_set
    (k : ℕ)
    (hk : 0 < k) :
    example_5_11_iterated_split_closure k ≠ convexHull ℝ example_5_11_mixed_integer_set :=
  by
  have _ := hk
  intro hEq
  let w : Fin 3 → ℝ :=
    ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ) / (3 : ℝ) ^ k]
  have hwClosure : w ∈ example_5_11_iterated_split_closure k := by
    simpa [w] using example_5_11_witness_mem_iterated_split_closure k
  have hwHull : w ∈ convexHull ℝ example_5_11_mixed_integer_set := by
    simpa [hEq] using hwClosure
  have hwZero : w 2 = 0 := example_5_11_mixed_integer_hull_subset_y_eq_zero hwHull
  -- The witness always has positive `y`-coordinate, so it cannot lie in the mixed-integer hull.
  have hwPos : 0 < w 2 := by
    change 0 < (1 / 2 : ℝ) / (3 : ℝ) ^ k
    positivity
  exact hwPos.ne' hwZero

end Example511
