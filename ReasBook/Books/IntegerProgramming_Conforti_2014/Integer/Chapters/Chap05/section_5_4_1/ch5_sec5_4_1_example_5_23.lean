/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22

open scoped BigOperators SplitHullNotation

-- Semantic recall note: this example reuses the Chapter 5 split-closure and binary-point owners
-- exposed by Theorem 5.22 and adds only the example-specific polytope, fractional layers, and
-- iterated split-closure sequence.

section Example523

variable {n : ℕ}

/-- The polytope `P` from Example 5.23, cut out by the box constraints `0 ≤ x_j ≤ 1` and the
family of inequalities
`∑_{j ∈ J} x_j + ∑_{j ∉ J} (1 - x_j) ≥ 1 / 2` for every `J ⊆ {1, …, n}`. -/
def example_5_23_polytope (n : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
      ∀ J : Finset (Fin n),
        J.sum (fun j ↦ x j) + (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - x j) ≥ (1 / 2 : ℝ)}

/-- Membership in `example_5_23_polytope n` is exactly the conjunction of the box constraints and
the family of parity-type inequalities from Example 5.23. -/
theorem mem_example_5_23_polytope_iff
    {n : ℕ}
    {x : Fin n → ℝ} :
    x ∈ example_5_23_polytope n ↔
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        ∀ J : Finset (Fin n),
          J.sum (fun j ↦ x j) + (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - x j) ≥
            (1 / 2 : ℝ) :=
  Iff.rfl

/-- The binary points `P ∩ {0, 1}ⁿ` of the Example 5.23 polytope. -/
def example_5_23_zero_one_points (n : ℕ) : Set (Fin n → ℝ) :=
  zero_one_points (Nat.le_refl n) (example_5_23_polytope n)

/-- Membership in the Example 5.23 binary-point set means belonging to the polytope and having
every coordinate in `{0, 1}`. -/
theorem mem_example_5_23_zero_one_points_iff
    {n : ℕ}
    {x : Fin n → ℝ} :
    x ∈ example_5_23_zero_one_points n ↔
      x ∈ example_5_23_polytope n ∧ ∀ j : Fin n, x j = 0 ∨ x j = 1 := by
  simpa using
    (mem_zero_one_points_iff (Nat.le_refl n) (example_5_23_polytope n) x)

/-- The set `F_j` from Example 5.23: exactly `j` coordinates are equal to `1 / 2`, and every
remaining coordinate belongs to `{0, 1}`. -/
def example_5_23_fractional_layer (n j : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (Finset.univ.filter (fun i : Fin n ↦ x i = (1 / 2 : ℝ))).card = j ∧
      ∀ i, x i = (1 / 2 : ℝ) ∨ x i = 0 ∨ x i = 1}

/-- Membership in `example_5_23_fractional_layer n j` means that exactly `j` coordinates are
equal to `1 / 2` and every coordinate belongs to `{0, 1 / 2, 1}`. -/
theorem mem_example_5_23_fractional_layer_iff
    {n j : ℕ}
    {x : Fin n → ℝ} :
    x ∈ example_5_23_fractional_layer n j ↔
      (Finset.univ.filter (fun i : Fin n ↦ x i = (1 / 2 : ℝ))).card = j ∧
        ∀ i, x i = (1 / 2 : ℝ) ∨ x i = 0 ∨ x i = 1 :=
  Iff.rfl

/-- The `k`-fold split closure `P^k` of the Example 5.23 polytope. -/
def example_5_23_iterated_split_closure (n k : ℕ) : Set (Fin n → ℝ) :=
  (split_closure^[k]) (example_5_23_polytope n)

/-- The zeroth canonical iterated split closure of the Example 5.23 polytope is the polytope
itself. -/
theorem example_5_23_iterated_split_closure_zero
    (n : ℕ) :
    example_5_23_iterated_split_closure n 0 = example_5_23_polytope n :=
  rfl

/-- The successor step in the canonical split-closure iterate sequence for Example 5.23. -/
theorem example_5_23_iterated_split_closure_succ
    (n k : ℕ) :
    example_5_23_iterated_split_closure n (k + 1) =
      (example_5_23_iterated_split_closure n k)^split := by
  simp [example_5_23_iterated_split_closure, Function.iterate_succ_apply']

/-- The all-half vector belongs to `F_n`. -/
theorem example_5_23_all_half_mem_fractional_layer
    (n : ℕ) :
    (fun _ : Fin n ↦ (1 / 2 : ℝ)) ∈ example_5_23_fractional_layer n n := by
  simp [example_5_23_fractional_layer]

/-- Helper for Example 5.23: the defining inequalities of `P` are preserved by convex
combinations, so `example_5_23_polytope n` is convex. -/
private theorem example_5_23_polytope_convex
    (n : ℕ) :
    Convex ℝ (example_5_23_polytope n) := by
  intro x hx y hy a b ha hb hab
  rw [mem_example_5_23_polytope_iff] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · -- The box constraints are coordinatewise stable under convex combinations.
    intro i
    have hx0 := (hx.1 i).1
    have hx1 := (hx.1 i).2
    have hy0 := (hy.1 i).1
    have hy1 := (hy.1 i).2
    constructor
    · simpa [Pi.smul_apply] using
        add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
    · change a * x i + b * y i ≤ 1
      nlinarith
  · -- Each parity inequality is affine in `x`, so the lower bound is preserved as well.
    intro J
    have hxJ := hx.2 J
    have hyJ := hy.2 J
    have hsumJ :
        J.sum (fun j ↦ (a • x + b • y) j) =
          a * J.sum (fun j ↦ x j) + b * J.sum (fun j ↦ y j) := by
      simp [Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
    have hcoord :
        ∀ j : Fin n,
          (1 : ℝ) - (a • x + b • y) j =
            a * ((1 : ℝ) - x j) + b * ((1 : ℝ) - y j) := by
      intro j
      simp [Pi.smul_apply]
      nlinarith
    have hsumCompl :
        (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - (a • x + b • y) j) =
          a * (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - x j) +
            b * (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - y j) := by
      simp_rw [hcoord]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [hsumJ, hsumCompl]
    nlinarith

/-- Helper for Example 5.23: every iterated split closure is convex because each split hull is a
convex hull and the closure is an intersection of such hulls. -/
private theorem example_5_23_iterated_split_closure_convex
    (n k : ℕ) :
    Convex ℝ (example_5_23_iterated_split_closure n k) := by
  induction k with
  | zero =>
      simpa [example_5_23_iterated_split_closure_zero] using example_5_23_polytope_convex n
  | succ k ih =>
      -- The successor iterate is an intersection of split hulls of the previous iterate.
      rw [example_5_23_iterated_split_closure_succ, split_closure]
      refine convex_iInter₂ ?_
      intro π π0
      simpa [split_hull] using
        (convex_convexHull ℝ
          (split_branch_lower (example_5_23_iterated_split_closure n k) π.1 π0 ∪
            split_branch_upper (example_5_23_iterated_split_closure n k) π.1 π0))

/-- Helper for Example 5.23: a `{0, 1 / 2, 1}`-valued point with at least one `1 / 2` coordinate
already satisfies every defining inequality of `P`. -/
private lemma example_5_23_mem_polytope_of_exists_half
    {n : ℕ}
    {x : Fin n → ℝ}
    (hvals : ∀ i, x i = (1 / 2 : ℝ) ∨ x i = 0 ∨ x i = 1)
    (hex : ∃ i, x i = (1 / 2 : ℝ)) :
    x ∈ example_5_23_polytope n := by
  rw [mem_example_5_23_polytope_iff]
  refine ⟨?_, ?_⟩
  · -- The three allowed coordinate values all lie in `[0, 1]`.
    intro i
    rcases hvals i with hhalf | hzero | hone
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
  · -- A half-coordinate contributes `1 / 2` to one side of every parity inequality.
    intro J
    rcases hex with ⟨i, hi⟩
    have hbox : ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
      intro j
      rcases hvals j with hhalf | hzero | hone
      · constructor <;> linarith
      · constructor <;> linarith
      · constructor <;> linarith
    have hJnonneg : 0 ≤ J.sum (fun j ↦ x j) := by
      exact Finset.sum_nonneg fun j _ ↦ (hbox j).1
    have hComplNonneg : 0 ≤ (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - x j) := by
      exact Finset.sum_nonneg fun j _ ↦ sub_nonneg.mpr (hbox j).2
    by_cases hiJ : i ∈ J
    · -- If the half-coordinate lies in `J`, it contributes directly to the first sum.
      have hJtailNonneg : 0 ≤ (J.erase i).sum (fun j ↦ x j) := by
        exact Finset.sum_nonneg fun j _ ↦ (hbox j).1
      have hJhalf : (1 / 2 : ℝ) ≤ J.sum (fun j ↦ x j) := by
        have haux : (1 / 2 : ℝ) ≤ (J.erase i).sum (fun j ↦ x j) + x i := by
          nlinarith [hJtailNonneg, hi]
        calc
          (1 / 2 : ℝ) ≤ (J.erase i).sum (fun j ↦ x j) + x i := haux
          _ = J.sum (fun j ↦ x j) := by
                simpa [hi] using (Finset.sum_erase_add J (fun j : Fin n ↦ x j) hiJ)
      linarith
    · -- Otherwise the same half-coordinate appears in the complementary sum as `1 - 1 / 2`.
      have hiCompl : i ∈ Finset.univ \ J := by
        simp [hiJ]
      have hComplTailNonneg : 0 ≤ ((Finset.univ \ J).erase i).sum (fun j ↦ (1 : ℝ) - x j) := by
        exact Finset.sum_nonneg fun j _ ↦ sub_nonneg.mpr (hbox j).2
      have hComplHalf : (1 / 2 : ℝ) ≤ (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - x j) := by
        have haux :
            (1 / 2 : ℝ) ≤
              ((Finset.univ \ J).erase i).sum (fun j ↦ (1 : ℝ) - x j) + ((1 : ℝ) - x i) := by
          nlinarith [hComplTailNonneg, hi]
        calc
          (1 / 2 : ℝ) ≤ ((Finset.univ \ J).erase i).sum (fun j ↦ (1 : ℝ) - x j) + ((1 : ℝ) - x i) :=
              haux
          _ = (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - x j) := by
                simpa [hi] using
                  (Finset.sum_erase_add (Finset.univ \ J) (fun j : Fin n ↦ (1 : ℝ) - x j) hiCompl)
      linarith

/-- Helper for Example 5.23: replacing one half-coordinate by `0` lowers the fractional-layer
count by exactly one. -/
private lemma example_5_23_fractional_layer_update_zero_mem
    {n j : ℕ}
    {x : Fin n → ℝ}
    {i : Fin n}
    (hx : x ∈ example_5_23_fractional_layer n (j + 1))
    (hi : x i = (1 / 2 : ℝ)) :
    Function.update x i 0 ∈ example_5_23_fractional_layer n j := by
  rw [mem_example_5_23_fractional_layer_iff] at hx ⊢
  refine ⟨?_, ?_⟩
  · -- The new half-coordinate set is the old one with `i` erased.
    have hfilter :
        Finset.univ.filter
            (fun k : Fin n ↦ Function.update x i 0 k = (1 / 2 : ℝ)) =
          (Finset.univ.filter (fun k : Fin n ↦ x k = (1 / 2 : ℝ))).erase i := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [Function.update, hi]
      · simp [hk]
    rw [hfilter, Finset.card_erase_of_mem]
    · rw [hx.1]
      simp
    · simp [hi]
  · -- Away from `i`, the allowed values are unchanged; at `i` the value is now `0`.
    intro k
    by_cases hk : k = i
    · subst hk
      simp [Function.update]
    · simpa [hk] using hx.2 k

/-- Helper for Example 5.23: replacing one half-coordinate by `1` lowers the fractional-layer
count by exactly one. -/
private lemma example_5_23_fractional_layer_update_one_mem
    {n j : ℕ}
    {x : Fin n → ℝ}
    {i : Fin n}
    (hx : x ∈ example_5_23_fractional_layer n (j + 1))
    (hi : x i = (1 / 2 : ℝ)) :
    Function.update x i 1 ∈ example_5_23_fractional_layer n j := by
  rw [mem_example_5_23_fractional_layer_iff] at hx ⊢
  refine ⟨?_, ?_⟩
  · -- Changing a half-coordinate to `1` removes exactly that half-coordinate from the filter.
    have hfilter :
        Finset.univ.filter
            (fun k : Fin n ↦ Function.update x i 1 k = (1 / 2 : ℝ)) =
          (Finset.univ.filter (fun k : Fin n ↦ x k = (1 / 2 : ℝ))).erase i := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [Function.update, hi]
      · simp [hk]
    rw [hfilter, Finset.card_erase_of_mem]
    · rw [hx.1]
      simp
    · simp [hi]
  · -- The updated point stays `{0, 1 / 2, 1}`-valued coordinatewise.
    intro k
    by_cases hk : k = i
    · subst hk
      simp [Function.update]
    · simpa [hk] using hx.2 k

/-- Helper for Example 5.23: a point in `F_{j+1}` is the midpoint of the two points obtained by
changing one half-coordinate to `0` and `1`. -/
private lemma example_5_23_midpoint_updates_eq
    {n : ℕ}
    {x : Fin n → ℝ}
    {i : Fin n}
    (hi : x i = (1 / 2 : ℝ)) :
    midpoint ℝ (Function.update x i 0) (Function.update x i 1) = x := by
  ext k
  by_cases hk : k = i
  · subst hk
    simp [midpoint_eq_smul_add, hi]
  · simp [hk]

/-- Helper for Example 5.23: any convex set containing `F_j` also contains `F_{j+1}` by the
midpoint construction from the source proof. -/
private lemma example_5_23_fractional_layer_succ_subset_of_convex
    {n j : ℕ}
    {Q : Set (Fin n → ℝ)}
    (hQ : Convex ℝ Q)
    (hprev : example_5_23_fractional_layer n j ⊆ Q) :
    example_5_23_fractional_layer n (j + 1) ⊆ Q := by
  intro x hx
  rw [mem_example_5_23_fractional_layer_iff] at hx
  have hpos : 0 < (Finset.univ.filter (fun i : Fin n ↦ x i = (1 / 2 : ℝ))).card := by
    rw [hx.1]
    exact Nat.succ_pos j
  rcases Finset.card_pos.mp hpos with ⟨i, hiMem⟩
  have hi : x i = (1 / 2 : ℝ) := (Finset.mem_filter.mp hiMem).2
  have hx0 : Function.update x i 0 ∈ example_5_23_fractional_layer n j :=
    example_5_23_fractional_layer_update_zero_mem
      (by simpa [mem_example_5_23_fractional_layer_iff] using hx) hi
  have hx1 : Function.update x i 1 ∈ example_5_23_fractional_layer n j :=
    example_5_23_fractional_layer_update_one_mem
      (by simpa [mem_example_5_23_fractional_layer_iff] using hx) hi
  -- The midpoint route matches the source proof and keeps the main theorem flat.
  have hmid :
      midpoint ℝ (Function.update x i 0) (Function.update x i 1) ∈ Q := by
    exact hQ.midpoint_mem (hprev hx0) (hprev hx1)
  simpa [example_5_23_midpoint_updates_eq hi] using hmid

/-- Helper for Example 5.23: the split value of a fractional-layer point is always a half-integer.
-/
private lemma example_5_23_split_dot_eq_int_half_of_mem_fractional_layer
    {n j : ℕ}
    {π : Fin n → ℤ}
    {x : Fin n → ℝ}
    (hx : x ∈ example_5_23_fractional_layer n j) :
    ∃ z : ℤ, split_dot π x = (z : ℝ) / 2 := by
  rw [mem_example_5_23_fractional_layer_iff] at hx
  let coeff : Fin n → ℤ :=
    fun i ↦ if x i = (1 / 2 : ℝ) then π i else if x i = 1 then 2 * π i else 0
  refine ⟨∑ i : Fin n, coeff i, ?_⟩
  -- Each coordinate contributes either `0`, `π i / 2`, or `π i`.
  rw [split_dot_eq_sum]
  calc
    ∑ i : Fin n, (π i : ℝ) * x i = ∑ i : Fin n, ((coeff i : ℝ) / 2) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hhalf : x i = (1 / 2 : ℝ)
      · have hcoeff : ((coeff i : ℤ) : ℝ) = (π i : ℝ) := by
          simp [coeff, hhalf]
        calc
          (π i : ℝ) * x i = (π i : ℝ) * (1 / 2 : ℝ) := by rw [hhalf]
          _ = ((coeff i : ℝ) / 2) := by
                rw [hcoeff]
                ring
      · rcases hx.2 i with hhalf' | hzero | hone
        · exact (hhalf hhalf').elim
        · have hcoeff : ((coeff i : ℤ) : ℝ) = 0 := by
            simp [coeff, hzero]
          calc
            (π i : ℝ) * x i = 0 := by rw [hzero]; ring
            _ = ((coeff i : ℝ) / 2) := by
                  rw [hcoeff]
                  ring
        · have hcoeff : ((coeff i : ℤ) : ℝ) = 2 * (π i : ℝ) := by
            simp [coeff, hone]
          calc
            (π i : ℝ) * x i = (π i : ℝ) := by rw [hone]; ring
            _ = ((coeff i : ℝ) / 2) := by
                  rw [hcoeff]
                  ring
    _ = (∑ i : Fin n, (coeff i : ℝ)) / 2 := by
      rw [Finset.sum_div]
    _ = ((∑ i : Fin n, coeff i : ℤ) : ℝ) / 2 := by
      simp

/-- Helper for Example 5.23: a strip point in a fractional layer has the exact split value
`π0 + 1 / 2`. -/
private lemma example_5_23_split_dot_eq_pi0_add_half_of_mem_strip
    {n j : ℕ}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x : Fin n → ℝ}
    (hx : x ∈ example_5_23_fractional_layer n j)
    (hxStrip : x ∈ split_strip π π0) :
    split_dot π x = (π0 : ℝ) + (1 / 2 : ℝ) := by
  rcases example_5_23_split_dot_eq_int_half_of_mem_fractional_layer (π := π) hx with ⟨z, hz⟩
  rw [mem_split_strip_iff] at hxStrip
  -- Multiplying the strip inequalities by `2` pins down the unique odd integer in the strip.
  have hzLowerReal : (((2 * π0 : ℤ) : ℝ)) < (z : ℝ) := by
    rw [hz] at hxStrip
    have hmul :
        (2 : ℝ) * (π0 : ℝ) < (2 : ℝ) * ((z : ℝ) / 2) :=
      mul_lt_mul_of_pos_left hxStrip.1 (by norm_num)
    simpa [two_mul] using hmul
  have hzUpperReal : (z : ℝ) < (((2 * π0 + 2 : ℤ) : ℝ)) := by
    rw [hz] at hxStrip
    have hmul :
        (2 : ℝ) * ((z : ℝ) / 2) < (2 : ℝ) * ((π0 : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hxStrip.2 (by norm_num)
    calc
      (z : ℝ) = (2 : ℝ) * ((z : ℝ) / 2) := by ring
      _ < (2 : ℝ) * ((π0 : ℝ) + 1) := hmul
      _ = (((2 * π0 + 2 : ℤ) : ℝ)) := by
            norm_num
            ring
  have hzLower : 2 * π0 < z := by
    exact_mod_cast hzLowerReal
  have hzUpper : z < 2 * π0 + 2 := by
    exact_mod_cast hzUpperReal
  have hzEq : z = 2 * π0 + 1 := by
    omega
  calc
    split_dot π x = (z : ℝ) / 2 := hz
    _ = (((2 * π0 + 1 : ℤ) : ℝ) / 2) := by rw [hzEq]
    _ = (π0 : ℝ) + (1 / 2 : ℝ) := by
          calc
            (((2 * π0 + 1 : ℤ) : ℝ) / 2)
                = ((((2 * π0 : ℤ) : ℝ) + 1) / 2) := by
                    norm_num
            _ = ((((2 * π0 : ℤ) : ℝ) / 2)) + (1 / 2 : ℝ) := by
                  ring
            _ = (π0 : ℝ) + (1 / 2 : ℝ) := by
                  norm_num

/-- Helper for Example 5.23: if every half-coordinate has zero split coefficient, then the split
value is integral. -/
private lemma example_5_23_split_dot_eq_int_of_half_coeff_zero
    {n j : ℕ}
    {π : Fin n → ℤ}
    {x : Fin n → ℝ}
    (hx : x ∈ example_5_23_fractional_layer n j)
    (hhalfZero : ∀ i : Fin n, x i = (1 / 2 : ℝ) → π i = 0) :
    ∃ z : ℤ, split_dot π x = z := by
  rw [mem_example_5_23_fractional_layer_iff] at hx
  let coeff : Fin n → ℤ := fun i ↦ if x i = 1 then π i else 0
  refine ⟨∑ i : Fin n, coeff i, ?_⟩
  -- Once the half-contributions vanish, only the `1`-coordinates remain in the sum.
  rw [split_dot_eq_sum]
  calc
    ∑ i : Fin n, (π i : ℝ) * x i = ∑ i : Fin n, (coeff i : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hhalf : x i = (1 / 2 : ℝ)
      · have hpi0 : π i = 0 := hhalfZero i hhalf
        have hcoeff : ((coeff i : ℤ) : ℝ) = 0 := by
          simp [coeff, hhalf]
        calc
          (π i : ℝ) * x i = 0 := by rw [hhalf, hpi0]; norm_num
          _ = (coeff i : ℝ) := by rw [hcoeff]
      · rcases hx.2 i with hhalf' | hzero | hone
        · exact (hhalf hhalf').elim
        · have hcoeff : ((coeff i : ℤ) : ℝ) = 0 := by
            simp [coeff, hzero]
          calc
            (π i : ℝ) * x i = 0 := by rw [hzero]; ring
            _ = (coeff i : ℝ) := by rw [hcoeff]
        · have hcoeff : ((coeff i : ℤ) : ℝ) = (π i : ℝ) := by
            simp [coeff, hone]
          calc
            (π i : ℝ) * x i = (π i : ℝ) := by rw [hone]; ring
            _ = (coeff i : ℝ) := by rw [hcoeff]
    _ = ((∑ i : Fin n, coeff i : ℤ) : ℝ) := by
      simp

/-- Helper for Example 5.23: the normalized strip value forces some half-coordinate to have a
nonzero split coefficient. -/
private lemma example_5_23_exists_half_coordinate_nonzero_of_split_dot_eq_pi0_add_half
    {n j : ℕ}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x : Fin n → ℝ}
    (hx : x ∈ example_5_23_fractional_layer n (j + 1))
    (hsplit : split_dot π x = (π0 : ℝ) + (1 / 2 : ℝ)) :
    ∃ i : Fin n, x i = (1 / 2 : ℝ) ∧ π i ≠ 0 := by
  by_contra hnone
  have hhalfZero : ∀ i : Fin n, x i = (1 / 2 : ℝ) → π i = 0 := by
    intro i hi
    by_contra hpi
    exact hnone ⟨i, hi, hpi⟩
  rcases example_5_23_split_dot_eq_int_of_half_coeff_zero (π := π) hx hhalfZero with ⟨z, hz⟩
  have hzEq : (z : ℝ) = (π0 : ℝ) + (1 / 2 : ℝ) := by
    simpa [hz] using hsplit
  have hzParityReal : (((2 * z : ℤ) : ℝ)) = (((2 * π0 + 1 : ℤ) : ℝ)) := by
    calc
      (((2 * z : ℤ) : ℝ)) = 2 * (z : ℝ) := by norm_num
      _ = 2 * ((π0 : ℝ) + (1 / 2 : ℝ)) := by rw [hzEq]
      _ = (((2 * π0 + 1 : ℤ) : ℝ)) := by
            norm_num
            ring
  have hzParity : 2 * z = 2 * π0 + 1 := by
    exact_mod_cast hzParityReal
  omega

/-- Helper for Example 5.23: changing a half-coordinate to `0` or `1` shifts the split value by
`∓ π_j / 2`. -/
private lemma example_5_23_split_dot_update_zero_one_of_eq_half
    {n : ℕ}
    {π : Fin n → ℤ}
    {x : Fin n → ℝ}
    {j : Fin n}
    (hj : x j = (1 / 2 : ℝ)) :
    split_dot π (Function.update x j 0) = split_dot π x - (π j : ℝ) / 2 ∧
      split_dot π (Function.update x j 1) = split_dot π x + (π j : ℝ) / 2 := by
  -- Isolate the `j`th summand once and reuse it for both updates.
  rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
  have hxSum :
      ∑ k : Fin n, (π k : ℝ) * x k =
        (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) * x j := by
    exact
      (Finset.sum_erase_add (Finset.univ) (fun k : Fin n ↦ (π k : ℝ) * x k)
        (Finset.mem_univ j)).symm
  have hzeroSum :
      ∑ k : Fin n, (π k : ℝ) * Function.update x j 0 k =
        (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) := by
    calc
      ∑ k : Fin n, (π k : ℝ) * Function.update x j 0 k
          = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * Function.update x j 0 k) +
              (π j : ℝ) * Function.update x j 0 j := by
                exact
                  (Finset.sum_erase_add (Finset.univ)
                    (fun k : Fin n ↦ (π k : ℝ) * Function.update x j 0 k)
                    (Finset.mem_univ j)).symm
      _ = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) * 0 := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro k hk
              have hkne : k ≠ j := (Finset.mem_erase.mp hk).1
              simp [Function.update_of_ne hkne]
            · simp [Function.update]
      _ = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) := by
            ring
  have honeSum :
      ∑ k : Fin n, (π k : ℝ) * Function.update x j 1 k =
        (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) := by
    calc
      ∑ k : Fin n, (π k : ℝ) * Function.update x j 1 k
          = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * Function.update x j 1 k) +
              (π j : ℝ) * Function.update x j 1 j := by
                exact
                  (Finset.sum_erase_add (Finset.univ)
                    (fun k : Fin n ↦ (π k : ℝ) * Function.update x j 1 k)
                    (Finset.mem_univ j)).symm
      _ = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) * 1 := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro k hk
              have hkne : k ≠ j := (Finset.mem_erase.mp hk).1
              simp [Function.update_of_ne hkne]
            · simp [Function.update]
      _ = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) := by
            ring
  constructor
  · calc
      ∑ k : Fin n, (π k : ℝ) * Function.update x j 0 k
          = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) := hzeroSum
      _ = ((Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) * x j) -
            (π j : ℝ) / 2 := by
              rw [hj]
              ring
      _ = ∑ k : Fin n, (π k : ℝ) * x k - (π j : ℝ) / 2 := by
            rw [← hxSum]
  · calc
      ∑ k : Fin n, (π k : ℝ) * Function.update x j 1 k
          = (Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) := honeSum
      _ = ((Finset.univ.erase j).sum (fun k ↦ (π k : ℝ) * x k) + (π j : ℝ) * x j) +
            (π j : ℝ) / 2 := by
              rw [hj]
              ring
      _ = ∑ k : Fin n, (π k : ℝ) * x k + (π j : ℝ) / 2 := by
            rw [← hxSum]

/-- Helper for Example 5.23: a strip point in `F_{j+1}` lies in the split hull of any ambient
set containing `F_j`. -/
private lemma example_5_23_mem_split_hull_of_fractional_layer_mem_strip
    {n j : ℕ}
    {Q : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x : Fin n → ℝ}
    (hQ : example_5_23_fractional_layer n j ⊆ Q)
    (hx : x ∈ example_5_23_fractional_layer n (j + 1))
    (hxStrip : x ∈ split_strip π π0) :
    x ∈ Q^(π, π0) := by
  -- Route correction: normalize the strip value first, then place the two updates
  -- in opposite branches.
  have hsplit :
      split_dot π x = (π0 : ℝ) + (1 / 2 : ℝ) :=
    example_5_23_split_dot_eq_pi0_add_half_of_mem_strip (π := π) hx hxStrip
  rcases example_5_23_exists_half_coordinate_nonzero_of_split_dot_eq_pi0_add_half
      (π := π) (π0 := π0) hx hsplit with ⟨i, hi, hpi_ne_zero⟩
  have hx0Layer :
      Function.update x i 0 ∈ example_5_23_fractional_layer n j :=
    example_5_23_fractional_layer_update_zero_mem hx hi
  have hx1Layer :
      Function.update x i 1 ∈ example_5_23_fractional_layer n j :=
    example_5_23_fractional_layer_update_one_mem hx hi
  have hx0Q : Function.update x i 0 ∈ Q := hQ hx0Layer
  have hx1Q : Function.update x i 1 ∈ Q := hQ hx1Layer
  have hupdate :=
    example_5_23_split_dot_update_zero_one_of_eq_half (π := π) hi
  -- The sign of `π i` determines which updated point lands in which split branch.
  have hmid :
      midpoint ℝ (Function.update x i 0) (Function.update x i 1) ∈
        convexHull ℝ (split_branch_lower Q π π0 ∪ split_branch_upper Q π π0) := by
    have hsign : 1 ≤ π i ∨ π i ≤ -1 := by
      omega
    rcases hsign with hpos | hneg
    · have hx0Lower : Function.update x i 0 ∈ split_branch_lower Q π π0 := by
        rw [mem_split_branch_lower_iff]
        refine ⟨hx0Q, ?_⟩
        have hpiReal : (1 : ℝ) ≤ (π i : ℝ) := by
          exact_mod_cast hpos
        have hpiHalf : (1 / 2 : ℝ) ≤ (π i : ℝ) / 2 := by
          nlinarith
        calc
          split_dot π (Function.update x i 0)
              = (π0 : ℝ) + (1 / 2 : ℝ) - (π i : ℝ) / 2 := by
                  rw [hupdate.1, hsplit]
          _ ≤ (π0 : ℝ) := by
                nlinarith
      have hx1Upper : Function.update x i 1 ∈ split_branch_upper Q π π0 := by
        rw [mem_split_branch_upper_iff]
        refine ⟨hx1Q, ?_⟩
        have hpiReal : (1 : ℝ) ≤ (π i : ℝ) := by
          exact_mod_cast hpos
        have hpiHalf : (1 / 2 : ℝ) ≤ (π i : ℝ) / 2 := by
          nlinarith
        calc
          (π0 : ℝ) + 1
              = (π0 : ℝ) + (1 / 2 : ℝ) + (1 / 2 : ℝ) := by ring
          _ ≤ (π0 : ℝ) + (1 / 2 : ℝ) + (π i : ℝ) / 2 := by
                gcongr
          _ = split_dot π (Function.update x i 1) := by
                rw [hupdate.2, hsplit]
      have hx0Hull :
          Function.update x i 0 ∈
            convexHull ℝ (split_branch_lower Q π π0 ∪ split_branch_upper Q π π0) := by
        exact subset_convexHull ℝ _ (Or.inl hx0Lower)
      have hx1Hull :
          Function.update x i 1 ∈
            convexHull ℝ (split_branch_lower Q π π0 ∪ split_branch_upper Q π π0) := by
        exact subset_convexHull ℝ _ (Or.inr hx1Upper)
      exact (convex_convexHull ℝ _).midpoint_mem hx0Hull hx1Hull
    · have hx0Upper : Function.update x i 0 ∈ split_branch_upper Q π π0 := by
        rw [mem_split_branch_upper_iff]
        refine ⟨hx0Q, ?_⟩
        have hpiReal : (π i : ℝ) ≤ -1 := by
          exact_mod_cast hneg
        have hpiHalf : (π i : ℝ) / 2 ≤ -(1 / 2 : ℝ) := by
          nlinarith
        calc
          (π0 : ℝ) + 1
              = (π0 : ℝ) + (1 / 2 : ℝ) - (-(1 / 2 : ℝ)) := by ring
          _ ≤ (π0 : ℝ) + (1 / 2 : ℝ) - (π i : ℝ) / 2 := by
                nlinarith
          _ = split_dot π (Function.update x i 0) := by
                rw [hupdate.1, hsplit]
      have hx1Lower : Function.update x i 1 ∈ split_branch_lower Q π π0 := by
        rw [mem_split_branch_lower_iff]
        refine ⟨hx1Q, ?_⟩
        have hpiReal : (π i : ℝ) ≤ -1 := by
          exact_mod_cast hneg
        have hpiHalf : (π i : ℝ) / 2 ≤ -(1 / 2 : ℝ) := by
          nlinarith
        calc
          split_dot π (Function.update x i 1)
              = (π0 : ℝ) + (1 / 2 : ℝ) + (π i : ℝ) / 2 := by
                  rw [hupdate.2, hsplit]
          _ ≤ (π0 : ℝ) := by
                nlinarith
      have hx0Hull :
          Function.update x i 0 ∈
            convexHull ℝ (split_branch_lower Q π π0 ∪ split_branch_upper Q π π0) := by
        exact subset_convexHull ℝ _ (Or.inr hx0Upper)
      have hx1Hull :
          Function.update x i 1 ∈
            convexHull ℝ (split_branch_lower Q π π0 ∪ split_branch_upper Q π π0) := by
        exact subset_convexHull ℝ _ (Or.inl hx1Lower)
      exact (convex_convexHull ℝ _).midpoint_mem hx0Hull hx1Hull
  simpa [split_hull, example_5_23_midpoint_updates_eq hi] using hmid

/-- A preliminary fact for Example 5.23: the polytope `P` has no binary point, so its Chapter 5
binary-point set is empty. -/
theorem example_5_23_polytope_zero_one_points_eq_empty
    (n : ℕ) :
    example_5_23_zero_one_points n = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  rcases (mem_example_5_23_zero_one_points_iff.mp hx) with ⟨hxP, hx01⟩
  let J : Finset (Fin n) := Finset.univ.filter (fun j : Fin n ↦ x j = 0)
  have hineq := (mem_example_5_23_polytope_iff.mp hxP).2 J
  have hJsum : J.sum (fun j ↦ x j) = 0 := by
    -- By construction every coordinate indexed by `J` is zero.
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj' : j ∈ Finset.univ.filter (fun i : Fin n ↦ x i = 0) := by
      simpa [J] using hj
    exact (Finset.mem_filter.mp hj').2
  have hComplSum : (Finset.univ \ J).sum (fun j ↦ (1 : ℝ) - x j) = 0 := by
    -- A complementary coordinate cannot be zero, so the binary condition forces it to be `1`.
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_not_mem : j ∉ J := (Finset.mem_sdiff.mp hj).2
    have hj_ne_zero : x j ≠ 0 := by
      intro hj0
      exact hj_not_mem (by simp [J, hj0])
    rcases hx01 j with hj0 | hj1
    · exact False.elim (hj_ne_zero hj0)
    · simp [hj1]
  rw [hJsum, hComplSum] at hineq
  linarith

/-- Example 5.23 (2). For every `k = 0, …, n - 1`, the set `F_{k+1}` is contained in the `k`th
split closure `P^k`. -/
theorem example_5_23_fractional_layer_subset_iterated_split_closure
    (n k : ℕ)
    (hk : k < n) :
    example_5_23_fractional_layer n (k + 1) ⊆
      example_5_23_iterated_split_closure n k := by
  induction k generalizing n with
  | zero =>
      intro x hx
      rw [example_5_23_iterated_split_closure_zero]
      rw [mem_example_5_23_fractional_layer_iff] at hx
      -- The base layer `F₁` is already contained in `P`.
      have hhalfPos :
          0 < (Finset.univ.filter (fun i : Fin n ↦ x i = (1 / 2 : ℝ))).card := by
        rw [hx.1]
        simp
      rcases Finset.card_pos.mp hhalfPos with ⟨i, hi⟩
      exact example_5_23_mem_polytope_of_exists_half hx.2 ⟨i, (Finset.mem_filter.mp hi).2⟩
  | succ k ih =>
      intro x hx
      rw [example_5_23_iterated_split_closure_succ, mem_split_closure_iff]
      intro π π0
      -- Route correction: first descend from `F_{k+2}` to ambient membership in `P^k`,
      -- then split into the easy outside-strip case and the normalized strip case.
      have hkPrev : k < n := Nat.lt_of_succ_lt hk
      have hPrevLayer :
          example_5_23_fractional_layer n (k + 1) ⊆
            example_5_23_iterated_split_closure n k := by
        exact ih n hkPrev
      have hCurrLayer :
          example_5_23_fractional_layer n (k + 2) ⊆
            example_5_23_iterated_split_closure n k := by
        simpa [Nat.add_assoc] using
          example_5_23_fractional_layer_succ_subset_of_convex
            (example_5_23_iterated_split_closure_convex n k)
            hPrevLayer
      by_cases hxStrip : x ∈ split_strip π.1 π0
      · exact
          example_5_23_mem_split_hull_of_fractional_layer_mem_strip
            (Q := example_5_23_iterated_split_closure n k)
            (π := π.1) (π0 := π0) hPrevLayer hx hxStrip
      · have hxPrev : x ∈ example_5_23_iterated_split_closure n k := hCurrLayer hx
        by_cases hLower : split_dot π.1 x ≤ (π0 : ℝ)
        · exact subset_convexHull ℝ _
            (Or.inl ((mem_split_branch_lower_iff).2 ⟨hxPrev, hLower⟩))
        · have hgt : (π0 : ℝ) < split_dot π.1 x := by
            exact lt_of_not_ge hLower
          have hnotUpperLt : ¬ split_dot π.1 x < (π0 : ℝ) + 1 := by
            intro hlt
            exact hxStrip ((mem_split_strip_iff).2 ⟨hgt, hlt⟩)
          have hUpper : (π0 : ℝ) + 1 ≤ split_dot π.1 x := not_lt.mp hnotUpperLt
          exact subset_convexHull ℝ _
            (Or.inr ((mem_split_branch_upper_iff).2 ⟨hxPrev, hUpper⟩))

/-- A consequence of Example 5.23: the `(n - 1)`st split closure of `P` is nonempty. -/
theorem example_5_23_penultimate_iterated_split_closure_nonempty
    (n : ℕ)
    (hn : 0 < n) :
    (example_5_23_iterated_split_closure n (n - 1)).Nonempty := by
  have hhalf : (fun _ : Fin n ↦ (1 / 2 : ℝ)) ∈ example_5_23_fractional_layer n ((n - 1) + 1) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using
      example_5_23_all_half_mem_fractional_layer n
  refine ⟨fun _ : Fin n ↦ (1 / 2 : ℝ), ?_⟩
  -- The all-half vector lies in `F_n`, and the main inclusion theorem places `F_n` in `P^(n-1)`.
  exact
    example_5_23_fractional_layer_subset_iterated_split_closure n (n - 1)
      (Nat.sub_lt hn (Nat.succ_pos 0))
      hhalf

end Example523
