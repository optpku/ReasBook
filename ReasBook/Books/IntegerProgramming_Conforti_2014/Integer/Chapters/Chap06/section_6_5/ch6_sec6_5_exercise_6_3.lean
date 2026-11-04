/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_example_6_3

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no deferred semantic search tool such as `lean_leansearch` was available
-- in this environment, so this file follows the local Chapter 6 `Fin 3 → ℝ` / `convexHull ℝ`
-- precedent by direct repository inspection.

noncomputable section

section Exercise63

/-- The simplex `S_k` from Exercise 6.3 in the modular-variable space `(x₆,x₇,x₈)`. -/
def exercise_6_3_simplex (k : ℕ) : Set (Fin 3 → ℝ) :=
  {x | (∀ i : Fin 3, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = (2 * k : ℝ)}

/-- Membership in `exercise_6_3_simplex k` is exactly the nonnegativity and fixed-sum condition
defining the simplex `S_k`. -/
theorem mem_exercise_6_3_simplex_iff (k : ℕ) (x : Fin 3 → ℝ) :
    x ∈ exercise_6_3_simplex k ↔
      (∀ i : Fin 3, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = (2 * k : ℝ) :=
  Iff.rfl

/-- The corner polyhedron deduced in Exercise 6.3 in the modular-variable space `(x₆,x₇,x₈)`. -/
def exercise_6_3_modular_corner : Set (Fin 3 → ℝ) :=
  {x | (∀ i : Fin 3, 0 ≤ x i) ∧ (2 : ℝ) ≤ x 0 + x 1 + x 2}

/-- Membership in `exercise_6_3_modular_corner` is exactly the displayed inequality description
of the modular-space corner polyhedron. -/
theorem mem_exercise_6_3_modular_corner_iff (x : Fin 3 → ℝ) :
    x ∈ exercise_6_3_modular_corner ↔
      (∀ i : Fin 3, 0 ≤ x i) ∧ (2 : ℝ) ≤ x 0 + x 1 + x 2 :=
  Iff.rfl

/-- Helper for Exercise 6.3: every point of `exercise_6_3_simplex k` is a convex combination of
the three axis points at level `2 * k`. -/
lemma exercise_6_3_mem_convexHull_of_mem_simplex
    {M : Set (Fin 3 → ℝ)}
    {k : ℕ}
    (hk : 0 < k)
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_6_3_simplex k)
    (haxis₁ : ∀ k : ℕ, 0 < k → ![(2 * k : ℝ), 0, 0] ∈ M)
    (haxis₂ : ∀ k : ℕ, 0 < k → ![0, (2 * k : ℝ), 0] ∈ M)
    (haxis₃ : ∀ k : ℕ, 0 < k → ![0, 0, (2 * k : ℝ)] ∈ M) :
    x ∈ convexHull ℝ M := by
  rw [mem_exercise_6_3_simplex_iff] at hx
  let w : Fin 3 → ℝ := fun i ↦ x i / (2 * k : ℝ)
  let axis : Fin 3 → Fin 3 → ℝ := fun i ↦ (2 * k : ℝ) • Pi.single i (1 : ℝ)
  have hkR_pos : (0 : ℝ) < (2 * k : ℝ) := by
    nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast Nat.succ_le_of_lt hk]
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    -- The simplex inequalities make the barycentric weights nonnegative.
    intro i
    exact div_nonneg (hx.1 i) hkR_pos.le
  have hw_sum : ∑ i, w i = 1 := by
    -- The fixed-sum equation says the barycentric weights add up to `1`.
    rw [Fin.sum_univ_three]
    dsimp [w]
    field_simp [hkR_pos.ne']
    linarith [hx.2]
  have haxis0 : axis 0 = ![(2 * k : ℝ), 0, 0] := by
    ext j
    fin_cases j <;> simp [axis]
  have haxis1 : axis 1 = ![0, (2 * k : ℝ), 0] := by
    ext j
    fin_cases j <;> simp [axis]
  have haxis2 : axis 2 = ![0, 0, (2 * k : ℝ)] := by
    ext j
    fin_cases j <;> simp [axis]
  have haxis_mem : ∀ i, axis i ∈ M := by
    -- The three support points are exactly the assumed axis points.
    intro i
    fin_cases i
    · exact haxis0.symm ▸ haxis₁ k hk
    · exact haxis1.symm ▸ haxis₂ k hk
    · exact haxis2.symm ▸ haxis₃ k hk
  have hweight_mul : ∀ i, w i * (2 * k : ℝ) = x i := by
    -- Each barycentric weight rescales the corresponding axis point back to `x i`.
    intro i
    dsimp [w]
    field_simp [hkR_pos.ne']
  have hrepr : ∑ i, w i • axis i = x := by
    -- Summing the rescaled coordinate basis vectors reconstructs `x`.
    calc
      ∑ i, w i • axis i = ∑ i, x i • Pi.single i (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        calc
          w i • axis i = (w i * (2 * k : ℝ)) • Pi.single i (1 : ℝ) := by
              simp [axis, smul_smul]
          _ = x i • Pi.single i (1 : ℝ) := by
              rw [hweight_mul i]
      _ = x := by
        simpa using (pi_eq_sum_univ' x).symm
  exact mem_convexHull_of_exists_fintype w axis hw_nonneg hw_sum haxis_mem hrepr

/-- Helper for Exercise 6.3: every `σ ≥ 2` lies between two adjacent even levels `2n` and
`2(n + 1)` with `n > 0`. -/
lemma exercise_6_3_exists_adjacentEvenLevels
    {σ : ℝ} (hσ : (2 : ℝ) ≤ σ) :
    ∃ n : ℕ, 0 < n ∧ (2 * n : ℝ) ≤ σ ∧ σ ≤ (2 * (n + 1) : ℝ) := by
  let n : ℕ := ⌊σ / 2⌋₊
  refine ⟨n, ?_, ?_, ?_⟩
  · -- The lower bound `σ ≥ 2` guarantees that the lower even level is positive.
    have hσhalf_one : (1 : ℝ) ≤ σ / 2 := by
      linarith
    simpa [n] using (Nat.floor_pos.mpr hσhalf_one)
  · -- The floor gives the lower adjacent level.
    have hσhalf_nonneg : 0 ≤ σ / 2 := by
      linarith
    have hfloor : (n : ℝ) ≤ σ / 2 := by
      simpa [n] using (Nat.floor_le hσhalf_nonneg : ((⌊σ / 2⌋₊ : ℕ) : ℝ) ≤ σ / 2)
    nlinarith
  · -- The strict upper floor bound gives the next adjacent even level.
    have hfloor : σ / 2 < (n : ℝ) + 1 := by
      simpa [n] using (Nat.lt_floor_add_one (σ / 2))
    nlinarith

/-- Helper for Exercise 6.3: a nonnegative point whose coordinate sum lies in one adjacent-even
strip belongs to the convex hull generated by the modular axis points. -/
lemma exercise_6_3_mem_convexHull_of_sumStrip
    {M : Set (Fin 3 → ℝ)}
    {x : Fin 3 → ℝ}
    {n : ℕ}
    (hx_nonneg : ∀ i : Fin 3, 0 ≤ x i)
    (hn : 0 < n)
    (hleft : (2 * n : ℝ) ≤ x 0 + x 1 + x 2)
    (hright : x 0 + x 1 + x 2 ≤ (2 * (n + 1) : ℝ))
    (haxis₁ : ∀ k : ℕ, 0 < k → ![(2 * k : ℝ), 0, 0] ∈ M)
    (haxis₂ : ∀ k : ℕ, 0 < k → ![0, (2 * k : ℝ), 0] ∈ M)
    (haxis₃ : ∀ k : ℕ, 0 < k → ![0, 0, (2 * k : ℝ)] ∈ M) :
    x ∈ convexHull ℝ M := by
  let σ : ℝ := x 0 + x 1 + x 2
  have hσ_pos : 0 < σ := by
    -- The strip starts above the first even level, so the normalization denominator is positive.
    have hn_one : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt hn
    dsimp [σ]
    nlinarith
  have hσ_ne : σ ≠ 0 := hσ_pos.ne'
  let lower : Fin 3 → ℝ := ((2 * n : ℝ) / σ) • x
  let upper : Fin 3 → ℝ := ((2 * (n + 1) : ℝ) / σ) • x
  have hsum_one :
      x 0 * (x 0 + x 1 + x 2)⁻¹ +
        x 1 * (x 0 + x 1 + x 2)⁻¹ +
        x 2 * (x 0 + x 1 + x 2)⁻¹ = 1 := by
    -- The coordinate sum becomes `1` after multiplying by its reciprocal.
    have hmul_inv :
        (x 0 + x 1 + x 2) * (x 0 + x 1 + x 2)⁻¹ = (1 : ℝ) := by
      simpa [div_eq_mul_inv] using
        (div_self hσ_ne : (x 0 + x 1 + x 2) / (x 0 + x 1 + x 2) = (1 : ℝ))
    simpa [add_mul, mul_add, add_assoc, add_left_comm, add_comm] using hmul_inv
  have hlower_mem_simplex : lower ∈ exercise_6_3_simplex n := by
    rw [mem_exercise_6_3_simplex_iff]
    refine ⟨?_, ?_⟩
    · -- Scaling by the lower adjacent-even level preserves nonnegativity.
      intro i
      have hcoeff_nonneg : 0 ≤ (2 * n : ℝ) / σ := by
        exact div_nonneg (by positivity) hσ_pos.le
      simpa [lower] using mul_nonneg hcoeff_nonneg (hx_nonneg i)
    · -- The coordinate sum is normalized to the lower even level `2n`.
      dsimp [lower, σ]
      calc
        (2 * n : ℝ) / (x 0 + x 1 + x 2) * x 0 +
            (2 * n : ℝ) / (x 0 + x 1 + x 2) * x 1 +
            (2 * n : ℝ) / (x 0 + x 1 + x 2) * x 2
            = (2 * n : ℝ) *
                (x 0 * (x 0 + x 1 + x 2)⁻¹ +
                  x 1 * (x 0 + x 1 + x 2)⁻¹ +
                  x 2 * (x 0 + x 1 + x 2)⁻¹) := by
                ring
        _ = (2 * n : ℝ) := by
              rw [hsum_one, mul_one]
  have hupper_mem_simplex : upper ∈ exercise_6_3_simplex (n + 1) := by
    rw [mem_exercise_6_3_simplex_iff]
    refine ⟨?_, ?_⟩
    · -- Scaling by the upper adjacent-even level preserves nonnegativity.
      intro i
      have hcoeff_nonneg : 0 ≤ (2 * (n + 1) : ℝ) / σ := by
        exact div_nonneg (by positivity) hσ_pos.le
      simpa [upper] using mul_nonneg hcoeff_nonneg (hx_nonneg i)
    · -- The coordinate sum is normalized to the upper even level `2(n + 1)`.
      dsimp [upper, σ]
      calc
        (2 * (n + 1) : ℝ) / (x 0 + x 1 + x 2) * x 0 +
            (2 * (n + 1) : ℝ) / (x 0 + x 1 + x 2) * x 1 +
            (2 * (n + 1) : ℝ) / (x 0 + x 1 + x 2) * x 2
            = (2 * (n + 1) : ℝ) *
                (x 0 * (x 0 + x 1 + x 2)⁻¹ +
                  x 1 * (x 0 + x 1 + x 2)⁻¹ +
                  x 2 * (x 0 + x 1 + x 2)⁻¹) := by
                ring
        _ = (2 * ↑(n + 1) : ℝ) := by
              rw [hsum_one]
              norm_num
  have hlower_mem_hull : lower ∈ convexHull ℝ M := by
    exact
      exercise_6_3_mem_convexHull_of_mem_simplex hn hlower_mem_simplex
        haxis₁ haxis₂ haxis₃
  have hupper_mem_hull : upper ∈ convexHull ℝ M := by
    exact
      exercise_6_3_mem_convexHull_of_mem_simplex (Nat.succ_pos n) hupper_mem_simplex
        haxis₁ haxis₂ haxis₃
  let a : ℝ := ((2 * (n + 1) : ℝ) - σ) / 2
  let b : ℝ := (σ - (2 * n : ℝ)) / 2
  have ha_nonneg : 0 ≤ a := by
    -- The strip bounds make the lower-level coefficient nonnegative.
    dsimp [a, σ]
    linarith
  have hb_nonneg : 0 ≤ b := by
    -- The strip bounds make the upper-level coefficient nonnegative.
    dsimp [b, σ]
    linarith
  have hab : a + b = 1 := by
    -- The strip coefficients form a convex pair.
    dsimp [a, b]
    ring
  have hcoeff :
      a * ((2 * n : ℝ) / σ) + b * ((2 * (n + 1) : ℝ) / σ) = 1 := by
    -- These coefficients reconstruct the original point from the two normalized simplex points.
    dsimp [a, b]
    field_simp [hσ_ne]
    ring
  have hrepr : a • lower + b • upper = x := by
    calc
      a • lower + b • upper
          = (a * ((2 * n : ℝ) / σ)) • x + (b * ((2 * (n + 1) : ℝ) / σ)) • x := by
              simp [lower, upper, smul_smul]
      _ = (a * ((2 * n : ℝ) / σ) + b * ((2 * (n + 1) : ℝ) / σ)) • x := by
            rw [add_smul]
      _ = x := by
            rw [hcoeff, one_smul]
  have hcombo : a • lower + b • upper ∈ convexHull ℝ M := by
    -- Convexity of the hull closes the argument once both normalized points lie in it.
    exact
      (convex_iff_add_mem.mp (convex_convexHull ℝ M))
        hlower_mem_hull hupper_mem_hull ha_nonneg hb_nonneg hab
  simpa [hrepr] using hcombo

/-- The affine change of variables sending `(x₁,x₂,x₃)` to the three modular-space coordinates
used to describe the corner polyhedron in Exercise 6.3. -/
def exercise_6_3_original_to_modular : (Fin 3 → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin'
      ![
        ![(0 : ℝ), 1, -(1 / 2 : ℝ)],
        ![-1, 0, -(1 / 2 : ℝ)],
        ![1, -1, -1]
      ]).toAffineMap +ᵥ
    AffineMap.const ℝ (Fin 3 → ℝ) ![(0 : ℝ), 1, 1]

@[simp] theorem exercise_6_3_original_to_modular_apply (x : Fin 3 → ℝ) :
    exercise_6_3_original_to_modular x =
      ![
        x 1 - x 2 / 2,
        1 - x 0 - x 2 / 2,
        1 + x 0 - x 1 - x 2
      ] :=
  by
    ext i
    fin_cases i <;>
      simp [exercise_6_3_original_to_modular, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] <;>
      ring_nf

/-- The modular-space corner inequalities pulled back along
`exercise_6_3_original_to_modular` are exactly the four displayed inequalities in the original
variables `(x₁,x₂,x₃)`. -/
theorem exercise_6_3_original_to_modular_mem_modular_corner_iff (x : Fin 3 → ℝ) :
    exercise_6_3_original_to_modular x ∈ exercise_6_3_modular_corner ↔
      x 2 ≤ 0 ∧
      x 2 ≤ 2 * x 1 ∧
      2 * x 0 + x 2 ≤ 2 ∧
      -x 0 + x 1 + x 2 ≤ 1 := by
  rw [mem_exercise_6_3_modular_corner_iff, exercise_6_3_original_to_modular_apply]
  constructor
  · rintro ⟨hx_nonneg, hsum⟩
    have hx0 : 0 ≤ x 1 - x 2 / 2 := by simpa using hx_nonneg 0
    have hx1 : 0 ≤ 1 - x 0 - x 2 / 2 := by simpa using hx_nonneg 1
    have hx2 : 0 ≤ 1 + x 0 - x 1 - x 2 := by simpa using hx_nonneg 2
    have hsum' :
        2 ≤
          (x 1 - x 2 / 2) + (1 - x 0 - x 2 / 2) + (1 + x 0 - x 1 - x 2) := by
      simpa using hsum
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hx₂_nonpos, hx₁, hx₀, hmix⟩
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · change 0 ≤ x 1 - x 2 / 2
        linarith
      · change 0 ≤ 1 - x 0 - x 2 / 2
        linarith
      · change 0 ≤ 1 + x 0 - x 1 - x 2
        linarith
    · change 2 ≤
        ![x 1 - x 2 / 2, 1 - x 0 - x 2 / 2, 1 + x 0 - x 1 - x 2] 0 +
          ![x 1 - x 2 / 2, 1 - x 0 - x 2 / 2, 1 + x 0 - x 1 - x 2] 1 +
            ![x 1 - x 2 / 2, 1 - x 0 - x 2 / 2, 1 + x 0 - x 1 - x 2] 2
      simp
      linarith

/-- Exercise 6.3 (1). If the solution set `M` of the modular reformulation of `(6.6)` is contained
in the union of the simplices `S_k` with `k > 0` and contains the axis points
`(2k,0,0)`, `(0,2k,0)`, and `(0,0,2k)` for every positive integer `k`, then the corner
polyhedron `corner(B)` in the variables `(x₆,x₇,x₈)` is exactly
`{x ∈ ℝ_+^3 | 2 ≤ x₆ + x₇ + x₈}`. -/
theorem exercise_6_3_modular_corner_eq_convexHull
    (M : Set (Fin 3 → ℝ))
    (hsubset : ∀ ⦃x : Fin 3 → ℝ⦄, x ∈ M → ∃ k : ℕ, 0 < k ∧ x ∈ exercise_6_3_simplex k)
    (haxis₁ : ∀ k : ℕ, 0 < k → ![(2 * k : ℝ), 0, 0] ∈ M)
    (haxis₂ : ∀ k : ℕ, 0 < k → ![0, (2 * k : ℝ), 0] ∈ M)
    (haxis₃ : ∀ k : ℕ, 0 < k → ![0, 0, (2 * k : ℝ)] ∈ M) :
    exercise_6_3_modular_corner = convexHull ℝ M := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_exercise_6_3_modular_corner_iff] at hx
    obtain ⟨n, hn, hleft, hright⟩ := exercise_6_3_exists_adjacentEvenLevels hx.2
    -- A modular-corner point lies in one adjacent-even strip, hence in the hull.
    exact exercise_6_3_mem_convexHull_of_sumStrip hx.1 hn hleft hright haxis₁ haxis₂ haxis₃
  · -- Route correction: prove the easy inclusion abstractly via `convexHull_min`.
    refine convexHull_min ?_ ?_
    · intro x hxM
      rcases hsubset hxM with ⟨k, hk, hkx⟩
      rw [mem_exercise_6_3_simplex_iff] at hkx
      rw [mem_exercise_6_3_modular_corner_iff]
      refine ⟨hkx.1, ?_⟩
      have hk_one : (1 : ℝ) ≤ k := by
        exact_mod_cast Nat.succ_le_of_lt hk
      nlinarith [hkx.2]
    · intro x hx y hy a b ha hb hab
      rw [mem_exercise_6_3_modular_corner_iff] at hx hy ⊢
      refine ⟨?_, ?_⟩
      · -- Coordinatewise nonnegativity is preserved by convex combinations.
        intro i
        exact add_nonneg (smul_nonneg ha (hx.1 i)) (smul_nonneg hb (hy.1 i))
      · -- The lower bound on the coordinate sum is linear as well.
        have hsum :
            (a • x + b • y) 0 + (a • x + b • y) 1 + (a • x + b • y) 2 =
              a * (x 0 + x 1 + x 2) + b * (y 0 + y 1 + y 2) := by
          simp
          ring
        rw [hsum]
        nlinarith [hx.2, hy.2]

/-- Exercise 6.3 (2). Under the affine change of variables from `(x₁,x₂,x₃)` to the modular
coordinates, the corner polyhedron `corner(B)` in the original-variable space is the preimage of
the modular-space corner polyhedron. Equivalently, it is cut out by
`x₃ ≤ 0`, `x₂ - 1/2 x₃ ≥ 0`, `x₁ + 1/2 x₃ ≤ 1`, and `-x₁ + x₂ + x₃ ≤ 1`. -/
theorem exercise_6_3_original_corner_eq_preimage_modular_corner :
    example_6_3_corner =
      exercise_6_3_original_to_modular ⁻¹' exercise_6_3_modular_corner := by
  ext x
  -- Both sides are the same four inequalities after rewriting the preimage membership.
  rw [Set.mem_preimage, mem_example_6_3_corner_iff,
    exercise_6_3_original_to_modular_mem_modular_corner_iff]

end Exercise63
