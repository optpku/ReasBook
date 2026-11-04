/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_theorem_3_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_theorem_4_30
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_corollary_4_37
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_3_theorem_9_10.PrimitiveHyperplane

open IsLocalization
open scoped BigOperators Matrix

section Theorem910

variable {m n : ℕ}

/-- The encoding size of a rational number is always positive. -/
theorem EncodingSize.rational_pos (q : ℚ) :
    0 < EncodingSize.rational q := by
  rw [EncodingSize.rational_eq, Nat.add_assoc]
  exact Nat.succ_pos (Nat.size q.num.natAbs + Nat.size q.den)

/-- The bounded truncation `P' = {x ∈ P | -R ≤ x ≤ R}` of the rational polyhedron
`P = rational_matrix_polyhedron A b`. -/
def bounded_rational_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (R : ℤ) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | x ∈ rational_matrix_polyhedron A b ∧
      ∀ i : Fin n, -(R : ℝ) ≤ x i ∧ x i ≤ (R : ℝ)}

/-- Membership in `bounded_rational_polyhedron A b R` means satisfying `A x ≤ b` together with
the coordinate box bounds `-R ≤ x_i ≤ R`. -/
theorem mem_bounded_rational_polyhedron_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (R : ℤ)
    (x : Fin n → ℝ) :
    x ∈ bounded_rational_polyhedron A b R ↔
      x ∈ rational_matrix_polyhedron A b ∧
        ∀ i : Fin n, -(R : ℝ) ≤ x i ∧ x i ≤ (R : ℝ) :=
  Iff.rfl

/-- A polynomially bounded box-reduction datum for integer feasibility in rational polyhedra. -/
structure PolynomiallyBoundedBoxReduction
    (pi : Polynomial ℕ)
    (f : ℕ → ℕ → ℤ) : Prop where
  /-- The radius function takes nonnegative values. -/
  nonneg : ∀ n L : ℕ, 0 ≤ f n L
  /-- The encoding size of the radius function is polynomially bounded. -/
  encoding_bound : ∀ n L : ℕ,
    (Nat.log2 ((f n L).natAbs + 1) + 1) ≤ pi.eval (n + L)
  /-- Integer feasibility is preserved after truncating by the radius function. -/
  feasibility_iff {m n : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ)
      (L : ℕ)
      (hA : ∀ i : Fin m, ∀ j : Fin n, EncodingSize.rational (A i j) ≤ L)
      (hb : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L) :
      contains_integral_point (rational_matrix_polyhedron A b) ↔
        contains_integral_point (bounded_rational_polyhedron A b (f n L))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_theorem_9_10.lean`: an encoding-size bound on an
integer vector bounds each coordinate by the corresponding power of two. -/
lemma natAbs_lt_twoPow_of_integerVectorEncoding_le
    {x : Fin n → ℤ}
    {B : ℕ}
    (hB : EncodingSize.integerVector x ≤ B) :
    ∀ i : Fin n, (x i).natAbs < 2 ^ B := by
  intro i
  -- First isolate the encoding size of the chosen coordinate from the whole vector bound.
  have hcoord : EncodingSize.integer (x i) ≤ EncodingSize.integerVector x := by
    rw [EncodingSize.integerVector_eq_sum]
    simpa using
      (Finset.single_le_sum
        (f := fun j : Fin n ↦ EncodingSize.integer (x j))
        (fun j _ ↦ Nat.zero_le _)
        (by simp : i ∈ Finset.univ))
  have hsize : Nat.size (x i).natAbs ≤ B := by
    have hcoordBound : EncodingSize.integer (x i) ≤ B := le_trans hcoord hB
    rw [EncodingSize.integer_eq] at hcoordBound
    exact le_trans (Nat.le_succ _) hcoordBound
  exact Nat.lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by decide) hsize)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_theorem_9_10.lean`: the explicit power-of-two
radius has encoding size at most two larger than its exponent. -/
lemma powRadius_log2_bound (B : ℕ) :
    Nat.log2 (2 ^ B + 1) + 1 ≤ B + 2 := by
  let x := 2 ^ B + 1
  have hxne : x ≠ 0 := by
    simp [x]
  have hlog_lt_size : Nat.log2 x < Nat.size x := by
    have hpow : 2 ^ Nat.log2 x ≤ x := by
      simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hxne
    exact Nat.lt_size.mpr hpow
  have hsize : Nat.size x ≤ B + 2 := by
    apply Nat.size_le.mpr
    have hpow_pos : 1 ≤ 2 ^ B := by
      exact Nat.succ_le_of_lt (pow_pos (by decide) _)
    calc
      x = 2 ^ B + 1 := rfl
      _ ≤ 2 ^ B + 2 ^ B := Nat.add_le_add_left hpow_pos _
      _ = 2 ^ (B + 1) := by
        rw [pow_succ']
        ring
      _ < 2 ^ (B + 2) := by
        have hpow_pos' : 0 < 2 ^ (B + 1) := pow_pos (by decide) _
        calc
          2 ^ (B + 1) < 2 ^ (B + 1) + 2 ^ (B + 1) := Nat.lt_add_of_pos_right hpow_pos'
          _ = 2 ^ (B + 2) := by
            rw [show B + 2 = (B + 1) + 1 by omega, pow_succ']
            ring
  exact le_trans (Nat.succ_le_of_lt hlog_lt_size) hsize

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_theorem_9_10.lean`: if the affine span of a
nonempty rational polyhedron is not all of `ℝ^n`, then the implicit-equality subsystem contains a
nonzero row. -/
lemma existsRationalEqualityRow_of_notFullAffineSpan
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (h_nonempty : (rational_matrix_polyhedron A b).Nonempty)
    (h_not_full : affineSpan ℝ (rational_matrix_polyhedron A b) ≠ ⊤) :
    ∃ i :
        {i // i ∈ implicit_equality_indices (A.map (Rat.castHom ℝ)) (fun j ↦ (b j : ℝ))},
      implicit_equality_matrix (A.map (Rat.castHom ℝ)) (fun j ↦ (b j : ℝ)) i ≠ 0 := by
  let A' : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let b' : Fin m → ℝ := fun j ↦ (b j : ℝ)
  have hspan :
      (affineSpan ℝ (rational_matrix_polyhedron A b) : Set (Fin n → ℝ)) =
        {x : Fin n → ℝ | implicit_equality_matrix A' b' *ᵥ x = implicit_equality_rhs A' b'} := by
    simpa [A', b', rational_matrix_polyhedron] using
      affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set
        (A := A') (b := b')
  -- If every implicit row vanished, then the implicit-equality solution set would be all of `ℝ^n`.
  by_contra hnone
  have hzeroRows :
      ∀ i :
          {i // i ∈ implicit_equality_indices (A.map (Rat.castHom ℝ)) (fun j ↦ (b j : ℝ))},
        implicit_equality_matrix A' b' i = 0 := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  rcases h_nonempty with ⟨x0, hx0⟩
  have hx0_aff : x0 ∈ (affineSpan ℝ (rational_matrix_polyhedron A b) : Set (Fin n → ℝ)) :=
    subset_affineSpan ℝ _ hx0
  have hx0_eq : implicit_equality_matrix A' b' *ᵥ x0 = implicit_equality_rhs A' b' := by
    rwa [hspan] at hx0_aff
  have hrhsZero : implicit_equality_rhs A' b' = 0 := by
    ext i
    have hiEq := congrArg (fun f ↦ f i) hx0_eq
    have hleftZero : (implicit_equality_matrix A' b' *ᵥ x0) i = 0 := by
      change implicit_equality_matrix A' b' i ⬝ᵥ x0 = 0
      rw [hzeroRows i]
      simp
    simpa [hleftZero] using hiEq.symm
  have htop :
      affineSpan ℝ (rational_matrix_polyhedron A b) = ⊤ := by
    ext x
    change
      x ∈ ((affineSpan ℝ (rational_matrix_polyhedron A b) :
        AffineSubspace ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) ↔
        x ∈ ((⊤ : AffineSubspace ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))
    rw [hspan]
    constructor
    · intro hx
      trivial
    · intro _
      rw [hrhsZero]
      ext i
      change implicit_equality_matrix A' b' i ⬝ᵥ x = 0
      rw [hzeroRows i]
      simp
  exact h_not_full htop

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_theorem_9_10.lean`: clearing denominators and
dividing by the common coordinate gcd turns a nonzero rational equality row into a primitive
integer hyperplane. -/
lemma primitiveIntegerHyperplane_of_rationalRowEquality
    {P : Set (Fin n → ℝ)}
    {a : Fin n → ℚ}
    {β : ℚ}
    (ha : a ≠ 0)
    (hP : P ⊆ {x : Fin n → ℝ | (fun j ↦ (a j : ℝ)) ⬝ᵥ x = (β : ℝ)}) :
    ∃ v : Fin n → ℤ,
      ∃ rhs : ℚ,
        is_primitive_integer_vector v ∧ P ⊆ integer_hyperplane v rhs := by
  let d : ℕ := rational_vector_common_denominator a
  let w : Fin n → ℤ := common_denominator_scaled_vector a
  have hd_ne_zero : d ≠ 0 := rational_vector_common_denominator_ne_zero a
  -- Choose a nonzero coordinate so that the denominator-cleared row is genuinely nonzero.
  have ha_coord : ∃ k : Fin n, a k ≠ 0 := by
    by_contra hcoord
    apply ha
    ext j
    by_contra hj
    exact hcoord ⟨j, hj⟩
  rcases ha_coord with ⟨k, hk⟩
  have hwk_ne_zero : w k ≠ 0 := by
    have hkScaled : (w k : ℚ) = (d : ℚ) * a k := by
      simpa [w] using congrFun (common_denominator_scaled_vector_eq_smul a) k
    intro hwk
    have hdQ_ne_zero : (d : ℚ) ≠ 0 := by
      exact_mod_cast hd_ne_zero
    have hmul : (d : ℚ) * a k = 0 := by
      simpa [w, hwk] using hkScaled.symm
    exact hk ((mul_eq_zero.mp hmul).resolve_left hdQ_ne_zero)
  let g : ℕ := Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (w j))
  have hg_ne_zero : g ≠ 0 := by
    intro hg
    have hg_zero :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (w j)) = 0 := hg
    have hzero := (Finset.gcd_eq_zero_iff (s := Finset.univ) (f := fun j : Fin n ↦ Int.natAbs (w j))).1 hg_zero
    exact hwk_ne_zero (Int.natAbs_eq_zero.mp (hzero k (by simp)))
  let v : Fin n → ℤ := fun j ↦ w j / g
  let rhs : ℚ := ((d : ℚ) * β) / g
  have hv_nonzero : v ≠ 0 := by
    intro hv
    have hdivkNat : g ∣ Int.natAbs (w k) := Finset.gcd_dvd (by simp : k ∈ Finset.univ)
    have hdivkInt : (g : ℤ) ∣ w k := by
      apply Int.dvd_natAbs.1
      exact Int.natCast_dvd_natCast.mpr hdivkNat
    have hwk : w k = 0 := by
      calc
        w k = (v k) * g := by
          symm
          simpa [v, mul_comm] using Int.ediv_mul_cancel hdivkInt
        _ = 0 := by simp [hv]
    exact hwk_ne_zero hwk
  have hgcd_one :
      Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (v j)) = 1 := by
    have hkNatAbs_ne_zero : Int.natAbs (w k) ≠ 0 := by
      simpa using Int.natAbs_ne_zero.mpr hwk_ne_zero
    have hgcdDiv :
        Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (w j) / g) = 1 :=
      Finset.gcd_div_eq_one (s := Finset.univ) (f := fun j : Fin n ↦ Int.natAbs (w j))
        (his := by simp) hkNatAbs_ne_zero
    refine (Finset.gcd_congr rfl ?_).trans hgcdDiv
    intro j hj
    have hdivNat : g ∣ Int.natAbs (w j) := Finset.gcd_dvd hj
    have hdivInt : (g : ℤ) ∣ w j := by
      apply Int.dvd_natAbs.1
      exact Int.natCast_dvd_natCast.mpr hdivNat
    simp [v, Int.natAbs_ediv_of_dvd hdivInt]
  refine ⟨v, rhs, ⟨hv_nonzero, hgcd_one⟩, ?_⟩
  intro x hx
  rw [mem_linear_hyperplane_iff]
  have hxEq : (fun j ↦ (a j : ℝ)) ⬝ᵥ x = (β : ℝ) := hP hx
  have hwEq :
      (fun j ↦ (w j : ℝ)) ⬝ᵥ x = (d : ℝ) * (β : ℝ) := by
    -- Rewrite the cleared row as a scalar multiple of the rational row.
    calc
      (fun j ↦ (w j : ℝ)) ⬝ᵥ x =
          ((d : ℝ) • (fun j ↦ (a j : ℝ))) ⬝ᵥ x := by
            rw [common_denominator_scaled_vector_eq_smul_real (v := a)]
      _ = (d : ℝ) * ((fun j ↦ (a j : ℝ)) ⬝ᵥ x) := by
            simpa [smul_eq_mul] using
              (smul_dotProduct (d : ℝ) (fun j ↦ (a j : ℝ)) x)
      _ = (d : ℝ) * (β : ℝ) := by rw [hxEq]
  have hw_as_gv : (fun j ↦ (w j : ℝ)) = (g : ℝ) • (Int.cast ∘ v) := by
    ext j
    have hdivNat : g ∣ Int.natAbs (w j) := Finset.gcd_dvd (by simp : j ∈ Finset.univ)
    have hdivInt : (g : ℤ) ∣ w j := by
      apply Int.dvd_natAbs.1
      exact Int.natCast_dvd_natCast.mpr hdivNat
    have hwj : w j = (v j) * g := by
      symm
      simpa [v, mul_comm] using Int.ediv_mul_cancel hdivInt
    have hwj' : w j = g * v j := by
      simpa [mul_comm] using hwj
    change (w j : ℝ) = (g : ℝ) * (v j : ℝ)
    exact_mod_cast hwj'
  have hrhsMul :
      (g : ℝ) * (rhs : ℝ) = (d : ℝ) * (β : ℝ) := by
    have hrhsQ : (g : ℚ) * rhs = (d : ℚ) * β := by
      dsimp [rhs]
      field_simp [hg_ne_zero]
    exact_mod_cast hrhsQ
  -- Compare the cleared equation with the normalized one and cancel the nonzero gcd factor.
  apply mul_left_cancel₀ (show (g : ℝ) ≠ 0 by exact_mod_cast hg_ne_zero)
  calc
    (g : ℝ) * ((Int.cast ∘ v : Fin n → ℝ) ⬝ᵥ x) =
        (((g : ℝ) • (Int.cast ∘ v : Fin n → ℝ)) ⬝ᵥ x) := by
          simpa [smul_eq_mul] using
            (smul_dotProduct (g : ℝ) (Int.cast ∘ v : Fin n → ℝ) x).symm
    _ = (fun j ↦ (w j : ℝ)) ⬝ᵥ x := by rw [hw_as_gv]
    _ = (d : ℝ) * (β : ℝ) := hwEq
    _ = (g : ℝ) * (rhs : ℝ) := hrhsMul.symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_theorem_9_10.lean`: the dot product of two
integer vectors, after coercion to `ℝ`, is itself an integer. -/
lemma integerDotProduct_eq_intCast
    (v z : Fin n → ℤ) :
    ∃ k : ℤ, (Int.cast ∘ v : Fin n → ℝ) ⬝ᵥ (Int.cast ∘ z) = (k : ℝ) := by
  -- Expand the dot product and package the finite sum as an explicit integer witness.
  refine ⟨∑ i, v i * z i, ?_⟩
  simp [dotProduct]

/-- Theorem 9.10 (1). There exists an integer-valued radius function `f(n, L)` whose encoding size
is polynomially bounded in `n + L` such that, for every rational system `A x ≤ b` in `n`
variables whose coefficients have encoding size at most `L`, the rational polyhedron
`P = {x ∈ ℝ^n | A x ≤ b}` contains an integral point if and only if its truncation
`P' = {x ∈ P | -f(n, L) ≤ x ≤ f(n, L)}` contains an integral point. -/
theorem exists_polynomially_bounded_box_reduction_for_integer_feasibility :
    ∃ pi : Polynomial ℕ,
      ∃ f : ℕ → ℕ → ℤ,
        PolynomiallyBoundedBoxReduction pi f := by
  obtain ⟨π₀, hπ₀⟩ := rational_linear_inequality_system_has_small_integral_solution
  let pi : Polynomial ℕ := π₀ + Polynomial.C 2
  let f : ℕ → ℕ → ℤ := fun n L ↦ Int.ofNat (2 ^ (π₀.eval (n + L)))
  refine ⟨pi, f, ?_⟩
  refine
    { nonneg := ?_
      encoding_bound := ?_
      feasibility_iff := ?_ }
  · -- The chosen radius is a nonnegative integer because it is a positive power of two.
    intro n L
    simp [f]
  · -- The logarithmic encoding size of `2^B` is bounded by `B + 2`.
    intro n L
    simpa [pi, f, Polynomial.eval_add, Nat.succ_eq_add_one] using
      (Nat.lt_of_succ_le (powRadius_log2_bound (π₀.eval (n + L))))
  · intro m n A b L hA hb
    constructor
    · intro hfeas
      rcases contains_integral_point_iff.mp hfeas with ⟨x, hx⟩
      obtain ⟨xbar, hxbar, hxbarBound⟩ := hπ₀ A b L hA hb ⟨x, hx⟩
      refine contains_integral_point_iff.mpr ⟨xbar, ?_⟩
      constructor
      · exact hxbar
      · intro i
        have hlt := natAbs_lt_twoPow_of_integerVectorEncoding_le hxbarBound i
        have hnat : (xbar i).natAbs ≤ 2 ^ (π₀.eval (n + L)) := Nat.le_of_lt hlt
        have hnatInt :
            Int.ofNat (xbar i).natAbs ≤ Int.ofNat (2 ^ (π₀.eval (n + L))) := by
          exact Int.ofNat_le.mpr hnat
        have hAbsInt : |xbar i| ≤ Int.ofNat (2 ^ (π₀.eval (n + L))) := by
          simpa using hnatInt
        have hAbsReal : |((xbar i : ℤ) : ℝ)| ≤ (2 ^ (π₀.eval (n + L)) : ℝ) := by
          exact_mod_cast hAbsInt
        have hbox := abs_le.mp hAbsReal
        constructor
        · simpa [f, Function.comp_apply] using hbox.1
        · simpa [f, Function.comp_apply] using hbox.2
    · -- The bounded truncation is contained in the original polyhedron, so feasibility only gets easier.
      exact contains_integral_point_mono fun _ hx ↦ hx.1

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_3_theorem_9_10.lean
Theorem 9.10 (2). If the nonempty rational polyhedron `P = {x ∈ ℝ^n | A x ≤ b}` is not
full-dimensional, then `P` is contained in a rational hyperplane `v^T x = rhs` whose normal
vector `v ∈ ℤ^n` is primitive. -/
theorem non_full_dimensional_rational_polyhedron_subset_integer_hyperplane
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (h_nonempty : (rational_matrix_polyhedron A b).Nonempty)
    (h_not_full : affineSpan ℝ (rational_matrix_polyhedron A b) ≠ ⊤) :
    ∃ v : Fin n → ℤ,
      ∃ rhs : ℚ,
        is_primitive_integer_vector v ∧
          rational_matrix_polyhedron A b ⊆ integer_hyperplane v rhs := by
  let A' : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let b' : Fin m → ℝ := fun j ↦ (b j : ℝ)
  obtain ⟨i, hi_nonzero⟩ :=
    existsRationalEqualityRow_of_notFullAffineSpan A b h_nonempty h_not_full
  have hi_subset :
      rational_matrix_polyhedron A b ⊆ {x : Fin n → ℝ | (A' *ᵥ x) i.1 = b' i} := by
    exact
      (is_implicit_equality_iff_matrix_polyhedron_subset_hyperplane A' b' i.1).mp i.2
  have hrow_nonzero : A i.1 ≠ 0 := by
    intro hrow
    apply hi_nonzero
    ext j
    simp [A', implicit_equality_matrix, hrow]
  have hi_subset_dot :
      rational_matrix_polyhedron A b ⊆
        {x : Fin n → ℝ | (fun j ↦ (A i.1 j : ℝ)) ⬝ᵥ x = (b i.1 : ℝ)} := by
    intro x hx
    simpa [A', b', Matrix.mulVec, dotProduct] using hi_subset hx
  -- Normalize the rational equality row to a primitive integral normal vector.
  exact primitiveIntegerHyperplane_of_rationalRowEquality hrow_nonzero hi_subset_dot

namespace RationalMatrixPolyhedron

/-- Theorem 9.10 (3). If the rational polyhedron `P = {x ∈ ℝ^n | A x ≤ b}` is contained in an
integral hyperplane `v^T x = rhs` with nonintegral right-hand side `rhs`, then `P` has no
integral point. -/
theorem no_integral_point_of_subset_integer_hyperplane
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (v : Fin n → ℤ)
    (rhs : ℚ)
    (h_subset : rational_matrix_polyhedron A b ⊆ integer_hyperplane v rhs)
    (h_rhs : ¬ IsInteger ℤ rhs) :
    ¬ contains_integral_point (rational_matrix_polyhedron A b) := by
  intro hpoint
  rcases contains_integral_point_iff.mp hpoint with ⟨z, hz⟩
  have hzHyperplane : Int.cast ∘ z ∈ integer_hyperplane v rhs := h_subset hz
  rw [mem_linear_hyperplane_iff] at hzHyperplane
  rcases integerDotProduct_eq_intCast v z with ⟨k, hk⟩
  have hrhsReal : (rhs : ℝ) = (k : ℝ) := by
    calc
      (rhs : ℝ) = (Int.cast ∘ v : Fin n → ℝ) ⬝ᵥ (Int.cast ∘ z) := by
        exact hzHyperplane.symm
      _ = (k : ℝ) := hk
  have hrhsRat : rhs = (k : ℚ) := by
    exact_mod_cast hrhsReal
  have hrhsInteger : IsInteger ℤ rhs := by
    exact (Rat.isLocalizationIsInteger_iff rhs).2 ⟨k, hrhsRat.symm⟩
  exact h_rhs hrhsInteger

end RationalMatrixPolyhedron

end Theorem910
