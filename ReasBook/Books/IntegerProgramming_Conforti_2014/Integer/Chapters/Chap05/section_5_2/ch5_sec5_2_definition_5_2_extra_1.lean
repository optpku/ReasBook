/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped BigOperators Matrix IntegerVectorNotation

section Definition52Extra1

variable {m n : ℕ}

namespace Split

/-- The coefficients of a split are relatively prime on the integer-variable indices,
equivalently on all coordinates because they vanish on the continuous-variable indices. -/
def IsPrimitive {I : Finset (Fin n)} (s : Split I) : Prop :=
  Finset.univ.gcd (fun j : Fin n ↦ Int.natAbs (s.π j)) = 1

end Split

/-- Helper for Definition 5.2-extra-1: the lower Chvátal halfspace of a split is convex because
it is the inverse image of a real half-line under the linear functional `split_dot s`. -/
lemma chvatal_halfspace_convex
    {I : Finset (Fin n)}
    (s : Split I) :
    Convex ℝ {x : Fin n → ℝ | split_dot s x ≤ (s.π0 : ℝ)} := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := split_dot s
      map_add' := by
        intro x y
        -- `split_dot` is the dot product with a fixed coefficient vector, hence additive.
        rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        -- The same dot-product description shows homogeneity.
        rw [split_dot_eq_sum, split_dot_eq_sum]
        calc
          ∑ i : Fin n, (s.π i : ℝ) * (a • x) i
              = ∑ i : Fin n, a * ((s.π i : ℝ) * x i) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simp [Pi.smul_apply, mul_assoc, mul_comm]
          _ = a * ∑ i : Fin n, (s.π i : ℝ) * x i := by
                rw [Finset.mul_sum] }
  have hconv : Convex ℝ (Set.Iic (s.π0 : ℝ)) := convex_Iic _
  -- Pull the convex interval `(-∞, π₀]` back along the linear map `L`.
  simpa [L] using hconv.linear_preimage L

/-- Helper for Definition 5.2-extra-1: every real halfspace cut out by `split_dot s` is convex. -/
lemma split_halfspace_convex
    {I : Finset (Fin n)}
    (s : Split I)
    (β : ℝ) :
    Convex ℝ {x : Fin n → ℝ | split_dot s x ≤ β} := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := split_dot s
      map_add' := by
        intro x y
        -- `split_dot` is the dot product with a fixed coefficient vector, so it is additive.
        rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        -- The same finite-sum formula gives homogeneity.
        rw [split_dot_eq_sum, split_dot_eq_sum]
        calc
          ∑ i : Fin n, (s.π i : ℝ) * (a • x) i
              = ∑ i : Fin n, a * ((s.π i : ℝ) * x i) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simp [Pi.smul_apply, mul_assoc, mul_comm]
          _ = a * ∑ i : Fin n, (s.π i : ℝ) * x i := by
                rw [Finset.mul_sum] }
  have hconv : Convex ℝ (Set.Iic β) := convex_Iic _
  -- Pull the convex interval `(-∞, β]` back along the linear map `L`.
  simpa [L] using hconv.linear_preimage L

/-- Helper for Definition 5.2-extra-1: `split_dot s` is linear on affine rays. -/
lemma split_dot_add_smul
    {I : Finset (Fin n)}
    (s : Split I)
    (x y : Fin n → ℝ)
    (a : ℝ) :
    split_dot s (x + a • y) = split_dot s x + a * split_dot s y := by
  rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
  calc
    ∑ i : Fin n, (s.π i : ℝ) * (x + a • y) i
        = ∑ i : Fin n, ((s.π i : ℝ) * x i + a * ((s.π i : ℝ) * y i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            change (s.π i : ℝ) * (x i + a * y i) =
              (s.π i : ℝ) * x i + a * ((s.π i : ℝ) * y i)
            ring
    _ = ∑ i : Fin n, (s.π i : ℝ) * x i + ∑ i : Fin n, a * ((s.π i : ℝ) * y i) := by
          rw [Finset.sum_add_distrib]
    _ = split_dot s x + a * split_dot s y := by
          rw [← split_dot_eq_sum]
          congr 1
          rw [split_dot_eq_sum, Finset.mul_sum]

/-- Helper for Definition 5.2-extra-1: `split_dot π` is linear on affine rays for any integer
coefficient vector `π`. -/
lemma integerDot_add_smul
    (π : Fin n → ℤ)
    (x y : Fin n → ℝ)
    (a : ℝ) :
    split_dot π (x + a • y) = split_dot π x + a * split_dot π y := by
  rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
  calc
    ∑ i : Fin n, (π i : ℝ) * (x + a • y) i
        = ∑ i : Fin n, ((π i : ℝ) * x i + a * ((π i : ℝ) * y i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            change (π i : ℝ) * (x i + a * y i) =
              (π i : ℝ) * x i + a * ((π i : ℝ) * y i)
            ring
    _ = ∑ i : Fin n, (π i : ℝ) * x i + ∑ i : Fin n, a * ((π i : ℝ) * y i) := by
          rw [Finset.sum_add_distrib]
    _ = split_dot π x + a * split_dot π y := by
          rw [← split_dot_eq_sum]
          congr 1
          rw [split_dot_eq_sum, Finset.mul_sum]

/-- Helper for Definition 5.2-extra-1: evaluating an integer row on a single supported coordinate
vector extracts the matching coefficient. -/
lemma integerDot_single
    (π : Fin n → ℤ)
    (j : Fin n)
    (a : ℝ) :
    split_dot π (Pi.single j a) = (π j : ℝ) * a := by
  rw [split_dot_eq_sum]
  simp [Pi.single_apply]

/-- Helper for Definition 5.2-extra-1: if `c = t • π` at the integer level, then `split_dot c`
is the real scalar multiple `(t : ℝ) * split_dot π`. -/
lemma integerDot_eq_intMul_splitDot
    (π c : Fin n → ℤ)
    (t : ℤ)
    (hc : c = fun j ↦ t * π j)
    (x : Fin n → ℝ) :
    split_dot c x = (t : ℝ) * split_dot π x := by
  rw [hc, split_dot_eq_sum, split_dot_eq_sum]
  calc
    ∑ i : Fin n, ((t * π i : ℤ) : ℝ) * x i
        = ∑ i : Fin n, (t : ℝ) * ((π i : ℝ) * x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [Int.cast_mul]
            ring
    _ = (t : ℝ) * ∑ i : Fin n, (π i : ℝ) * x i := by
          rw [Finset.mul_sum]

/-- Helper for Definition 5.2-extra-1: the split value of the `j`th coordinate basis vector is the
`j`th coefficient of the split. -/
lemma split_dot_single_one
    {I : Finset (Fin n)}
    (s : Split I)
    (j : Fin n) :
    split_dot s (Pi.single j (1 : ℝ)) = (s.π j : ℝ) := by
  rw [split_dot_eq_sum]
  simp [Pi.single_apply]

/-- Helper for Definition 5.2-extra-1: primitive split coefficients admit an integer Bézout
combination equal to `1`. -/
lemma split_isPrimitive_has_bezout_coefficients
    (I : Finset (Fin n))
    (s : Split I)
    (hprimitive : s.IsPrimitive) :
    ∃ u : Fin n → ℤ, ∑ j : Fin n, s.π j * u j = 1 := by
  obtain ⟨v, hv⟩ := Finset.gcd_eq_sum_mul Finset.univ s.π
  have hgcd_unit :
      IsUnit (Finset.univ.gcd fun j : Fin n ↦ s.π j) := by
    apply Int.isUnit_iff_natAbs_eq.mpr
    apply Nat.dvd_one.mp
    rw [← hprimitive]
    exact Finset.dvd_gcd fun j hj ↦
      Int.natAbs_dvd_natAbs.mpr (Finset.gcd_dvd hj)
  rcases hgcd_unit with ⟨u, hu⟩
  refine ⟨fun j ↦ (↑(u⁻¹) : ℤ) * v j, ?_⟩
  have hv' : (Finset.univ.gcd fun j : Fin n ↦ s.π j : ℤ) = ∑ j : Fin n, s.π j * v j := by
    simpa using hv
  calc
    ∑ j : Fin n, s.π j * ((↑(u⁻¹) : ℤ) * v j)
        = (↑(u⁻¹) : ℤ) * ∑ j : Fin n, s.π j * v j := by
            calc
              ∑ j : Fin n, s.π j * ((↑(u⁻¹) : ℤ) * v j)
                  = ∑ j : Fin n, (↑(u⁻¹) : ℤ) * (s.π j * v j) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      ring
              _ = (↑(u⁻¹) : ℤ) * ∑ j : Fin n, s.π j * v j := by
                    rw [Finset.mul_sum]
    _ = (↑(u⁻¹) : ℤ) * (Finset.univ.gcd fun j : Fin n ↦ s.π j) := by rw [hv']
    _ = 1 := by
          rw [← hu]
          simp

/-- A first clause of Definition 5.2-extra-1: for a split `s = (π, π₀)` over the
mixed-integer index set `I`,
the inequality `π x ≤ π₀` is a Chvátal inequality for `P = {x : ℝ^n | A x ≤ b}` if
`P ∩ {x : ℝ^n | π x ≥ π₀ + 1} = ∅`, equivalently, if the upper split branch is empty. -/
def IsChvatalInequality
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {I : Finset (Fin n)}
    (s : Split I) : Prop :=
  split_branch_upper (polyhedron_le_set A b) s s.π0 = ∅

/-- Unfolding characterization of `IsChvatalInequality`. -/
theorem isChvatalInequality_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {I : Finset (Fin n)}
    (s : Split I) :
    IsChvatalInequality A b s ↔
      ∀ x : Fin n → ℝ, A *ᵥ x ≤ b → split_dot s x < (s.π0 : ℝ) + 1 := by
  constructor
  · intro hch x hx
    -- If `x` satisfied the opposite inequality, it would lie in the forbidden upper branch.
    by_contra hlt
    have hupper_empty : split_branch_upper (polyhedron_le_set A b) s s.π0 = ∅ := by
      simpa [IsChvatalInequality] using hch
    have hx_upper : x ∈ split_branch_upper (polyhedron_le_set A b) s s.π0 := by
      rw [mem_split_branch_upper_iff]
      exact ⟨by simpa [mem_polyhedron_le_set_iff] using hx, not_lt.mp hlt⟩
    have : False := by
      simp [hupper_empty] at hx_upper
    exact this.elim
  · intro hvalid
    ext x
    constructor
    · intro hx_upper
      rw [mem_split_branch_upper_iff] at hx_upper
      have hx_lt : split_dot s x < (s.π0 : ℝ) + 1 := by
        simpa [mem_polyhedron_le_set_iff] using hvalid x hx_upper.1
      exact (not_lt_of_ge hx_upper.2 hx_lt).elim
    · intro hx_empty
      simp at hx_empty

/-- A second clause of Definition 5.2-extra-1: every Chvátal inequality is valid for the convex
hull of the
mixed-integer feasible set `S = {x ∈ P | x_j ∈ ℤ for j ∈ I}`. -/
theorem convexHull_mixed_integer_feasible_set_subset_chvatal_halfspace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (s : Split I)
    (hch : IsChvatalInequality A b s) :
    convexHull ℝ (mixed_integer_feasible_set A b I) ⊆
      {x : Fin n → ℝ | split_dot s x ≤ (s.π0 : ℝ)} := by
  refine convexHull_min ?_ (chvatal_halfspace_convex s)
  intro x hx
  rw [mem_mixed_integer_feasible_set_iff] at hx
  have hx_lt := (isChvatalInequality_iff A b s).mp hch x hx.1
  obtain ⟨z, hz⟩ := split_dot_integral_of_integral_coordinates I s hx.2
  have hz_lt_real : (z : ℝ) < (s.π0 : ℝ) + 1 := by
    simpa [hz] using hx_lt
  have hz_lt : z < s.π0 + 1 := by
    exact_mod_cast hz_lt_real
  have hz_le : z ≤ s.π0 := Int.lt_add_one_iff.mp hz_lt
  -- Integrality of `split_dot s x` converts the strict branch exclusion
  -- into the desired inequality.
  have hz_le_real : (z : ℝ) ≤ (s.π0 : ℝ) := by
    exact_mod_cast hz_le
  simpa [hz] using hz_le_real

/-- A third clause of Definition 5.2-extra-1: every Chvátal inequality is a split inequality
relative to the
same split `s = (π, π₀)`. -/
theorem isSplitInequality_of_isChvatalInequality
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (s : Split I)
    (hch : IsChvatalInequality A b s) :
    IsSplitInequality A b I (Int.cast ∘ s.π) (s.π0 : ℝ) := by
  refine ⟨s, ?_⟩
  intro x hx
  rcases hx with hx_lower | hx_upper
  · rw [mem_split_branch_lower_iff] at hx_lower
    -- On the lower branch the inequality is exactly the defining branch inequality.
    simpa [split_dot] using hx_lower.2
  · have : False := by
      have hupper_empty : split_branch_upper (polyhedron_le_set A b) s s.π0 = ∅ := by
        simpa [IsChvatalInequality] using hch
      simp [hupper_empty] at hx_upper
    exact this.elim

/-- A fourth clause of Definition 5.2-extra-1: for `δ = max {π x | A x ≤ b}` and `π₀ = ⌊δ⌋`,
the rounded
inequality `π x ≤ π₀` cuts off a proper part of `P = {x : ℝ^n | A x ≤ b}` if and only if `δ` is
not an integer. -/
theorem chvatal_floor_cut_strict_subset_iff_nonintegral_max
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (δ : ℝ)
    (hδ : IsGreatest (split_dot π '' {x : Fin n → ℝ | A *ᵥ x ≤ b}) δ) :
    {x : Fin n → ℝ | A *ᵥ x ≤ b ∧ split_dot π x ≤ (Int.floor δ : ℝ)} ⊂
      {x : Fin n → ℝ | A *ᵥ x ≤ b} ↔
      δ ∉ Set.range (Int.cast : ℤ → ℝ) := by
  obtain ⟨xδ, hxδ_mem, hxδ_eq⟩ := hδ.1
  constructor
  · intro hstrict hδ_int
    rcases hδ_int with ⟨z, rfl⟩
    have hsubset_back :
        {x : Fin n → ℝ | A *ᵥ x ≤ b} ⊆
          {x : Fin n → ℝ | A *ᵥ x ≤ b ∧ split_dot π x ≤ (Int.floor (z : ℝ) : ℝ)} := by
      intro x hx
      have hx_image : split_dot π x ∈ split_dot π '' {x : Fin n → ℝ | A *ᵥ x ≤ b} :=
        ⟨x, hx, rfl⟩
      refine ⟨hx, ?_⟩
      simpa using (show split_dot π x ≤ (z : ℝ) from hδ.2 hx_image)
    exact hstrict.2 hsubset_back
  · intro hδ_nonint
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hx.1
    · intro hsubset_back
      have hfloor_lt : (Int.floor δ : ℝ) < δ := by
        simpa using (Int.floor_lt_self_iff.2 hδ_nonint)
      have hxδ_cut : xδ ∈ {x : Fin n → ℝ | A *ᵥ x ≤ b ∧ split_dot π x ≤ (Int.floor δ : ℝ)} :=
        hsubset_back hxδ_mem
      have : δ ≤ (Int.floor δ : ℝ) := by
        simpa [hxδ_eq] using hxδ_cut.2
      exact (not_le_of_gt hfloor_lt this).elim

/-- A fifth clause of Definition 5.2-extra-1: if the coefficients of the split vector are
relatively prime on
the integer-variable indices, then the equation `π x = π₀` admits an integral solution. -/
theorem exists_integral_solution_on_split_hyperplane_of_relatively_prime_coefficients
    (I : Finset (Fin n))
    (s : Split I)
    (hprimitive : s.IsPrimitive) :
    ∃ x : Fin n → ℤ, ∑ j : Fin n, s.π j * x j = s.π0 := by
  obtain ⟨u, hu⟩ := split_isPrimitive_has_bezout_coefficients I s hprimitive
  refine ⟨fun j ↦ s.π0 * u j, ?_⟩
  -- Scale the Bézout relation by `π₀` to land on the target split hyperplane.
  calc
    ∑ j : Fin n, s.π j * (s.π0 * u j)
        = ∑ j : Fin n, s.π0 * (s.π j * u j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
    _ = s.π0 * ∑ j : Fin n, s.π j * u j := by
          rw [← Finset.mul_sum]
    _ = s.π0 := by rw [hu, mul_one]

/-- Helper for Definition 5.2-extra-1: if the split coefficients are primitive, then every
integral right-hand side occurs on a lattice point of the split hyperplane. -/
lemma exists_integral_point_on_primitive_split_hyperplane
    (I : Finset (Fin n))
    (s : Split I)
    (hprimitive : s.IsPrimitive)
    (rhs : ℤ) :
    ∃ x : Fin n → ℤ, ∑ j : Fin n, s.π j * x j = rhs := by
  obtain ⟨u, hu⟩ := split_isPrimitive_has_bezout_coefficients I s hprimitive
  -- The Chapter 1 Bézout hyperplane theorem produces an integral point at any level `rhs`.
  exact integer_points_on_hyperplane_of_bezout s.π ⟨u, hu⟩ rhs

/-- Helper for Definition 5.2-extra-1: an integral mixed-integer point of the one-row halfspace
already satisfies the rounded inequality because its split value is an integer. -/
lemma split_dot_le_floor_of_integral_coordinates
    (I : Finset (Fin n))
    (s : Split I)
    (δ : ℝ)
    {x : Fin n → ℝ}
    (hx_int : ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ))
    (hxδ : split_dot s x ≤ δ) :
    split_dot s x ≤ (Int.floor δ : ℝ) := by
  obtain ⟨z, hz⟩ := split_dot_integral_of_integral_coordinates I s hx_int
  have hz_real : (z : ℝ) ≤ δ := by
    simpa [hz] using hxδ
  have hz_int : z ≤ Int.floor δ := (Int.le_floor).2 hz_real
  -- After identifying the split value with an integer, the floor bound is immediate.
  have hz_floor_real : (z : ℝ) ≤ (Int.floor δ : ℝ) := by
    exact_mod_cast hz_int
  simpa [hz] using hz_floor_real

/-- Helper for Definition 5.2-extra-1: for any fixed continuous coordinates, a primitive split has
an integral point on the rounded boundary hyperplane with those continuous coordinates unchanged. -/
lemma exists_mixed_integer_point_on_rounded_split_hyperplane
    (I : Finset (Fin n))
    (s : Split I)
    (δ : ℝ)
    (hprimitive : s.IsPrimitive)
    (x : Fin n → ℝ) :
    ∃ y : Fin n → ℝ,
      (∀ j ∈ I, ∃ z : ℤ, y j = (z : ℝ)) ∧
      (∀ j ∈ Iᶜ, y j = x j) ∧
      split_dot s y = (Int.floor δ : ℝ) := by
  obtain ⟨z, hz⟩ :=
    exists_integral_point_on_primitive_split_hyperplane I s hprimitive (Int.floor δ)
  let y : Fin n → ℝ := fun j ↦ if hj : j ∈ I then (z j : ℝ) else x j
  refine ⟨y, ?_, ?_, ?_⟩
  · intro j hj
    refine ⟨z j, ?_⟩
    simp [y, hj]
  · intro j hj
    simp [y, show ¬ j ∈ I by simpa using hj]
  · have hz_real : ∑ j : Fin n, (s.π j : ℝ) * (z j : ℝ) = (Int.floor δ : ℝ) := by
      exact_mod_cast hz
    -- The split ignores the continuous coordinates because its coefficients vanish there.
    calc
      split_dot s y = ∑ j : Fin n, (s.π j : ℝ) * y j := by
        rw [split_dot_eq_sum]
      _ = ∑ j : Fin n, (s.π j : ℝ) * (z j : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        by_cases hjI : j ∈ I
        · simp [y, hjI]
        · have hzero : s.π j = 0 := by
            exact s.zero_on_continuous j (by simpa using hjI)
          simp [y, hjI, hzero]
      _ = (Int.floor δ : ℝ) := hz_real

/-- Helper for Definition 5.2-extra-1: if an integral objective has a finite maximum on the
rounded split halfspace, then its coefficients are a nonnegative integer multiple of `s.π`. -/
lemma integralObjectiveProportionalToSplitOnRoundedHalfspace
    (I : Finset (Fin n))
    (s : Split I)
    (δ : ℝ)
    (hprimitive : s.IsPrimitive)
    (c : Fin n → ℤ)
    (z : ℝ)
    (hz : IsGreatest
      (((Int.cast ∘ c) ⬝ᵥ ·) '' {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)}) z) :
    ∃ t : ℤ, 0 ≤ t ∧ c = fun j ↦ t * s.π j := by
  obtain ⟨y, hy_int, hy_cont, hy_eq⟩ :=
    exists_mixed_integer_point_on_rounded_split_hyperplane I s δ hprimitive (fun _ ↦ 0)
  have hy_mem : y ∈ {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)} := by
    simp [hy_eq]
  have hkernel :
      ∀ i j : Fin n, c i * s.π j = c j * s.π i := by
    intro i j
    let d : Fin n → ℝ :=
      Pi.single i (s.π j : ℝ) - Pi.single j (s.π i : ℝ)
    have hd_split : split_dot s d = 0 := by
      -- The chosen direction lies in the kernel of the defining split functional.
      rw [show d = Pi.single i (s.π j : ℝ) + (-1 : ℝ) • Pi.single j (s.π i : ℝ) by
        ext k
        simp [d, sub_eq_add_neg]]
      rw [integerDot_add_smul]
      rw [integerDot_single, integerDot_single]
      ring
    have hshift_mem :
        ∀ a : ℝ, y + a • d ∈ {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)} := by
      intro a
      -- Kernel directions preserve the rounded halfspace.
      change split_dot s (y + a • d) ≤ (Int.floor δ : ℝ)
      calc
        split_dot s (y + a • d) = split_dot s y + a * split_dot s d := by
          simpa using integerDot_add_smul s.π y d a
        _ = split_dot s y := by rw [hd_split]; ring
        _ = (Int.floor δ : ℝ) := hy_eq
        _ ≤ (Int.floor δ : ℝ) := le_rfl
    have hbound :
        ∀ a : ℝ, split_dot c (y + a • d) ≤ z := by
      intro a
      exact hz.2 ⟨y + a • d, hshift_mem a, rfl⟩
    let v : ℝ := split_dot c y
    let m : ℝ := split_dot c d
    have h1 : v + m ≤ z := by
      have h1raw : split_dot c (y + (1 : ℝ) • d) ≤ z := hbound 1
      calc
        v + m = split_dot c (y + (1 : ℝ) • d) := by
          dsimp [v, m]
          rw [integerDot_add_smul]
          ring
        _ ≤ z := h1raw
    have h2 : v + (2 : ℝ) * m ≤ z := by
      have h2raw : split_dot c (y + (2 : ℝ) • d) ≤ z := hbound 2
      calc
        v + (2 : ℝ) * m = split_dot c (y + (2 : ℝ) • d) := by
          dsimp [v, m]
          rw [integerDot_add_smul]
        _ ≤ z := h2raw
    have hneg1 : v + (-1 : ℝ) * m ≤ z := by
      have hneg1raw : split_dot c (y + (-1 : ℝ) • d) ≤ z := hbound (-1)
      calc
        v + (-1 : ℝ) * m = split_dot c (y + (-1 : ℝ) • d) := by
          dsimp [v, m]
          rw [integerDot_add_smul]
        _ ≤ z := hneg1raw
    have hneg2 : v + (-2 : ℝ) * m ≤ z := by
      have hneg2raw : split_dot c (y + (-2 : ℝ) • d) ≤ z := hbound (-2)
      calc
        v + (-2 : ℝ) * m = split_dot c (y + (-2 : ℝ) • d) := by
          dsimp [v, m]
          rw [integerDot_add_smul]
        _ ≤ z := hneg2raw
    have hm_nonpos : m ≤ 0 := by
      by_contra hm_pos
      have hm_pos' : 0 < m := lt_of_not_ge hm_pos
      obtain ⟨N, hN⟩ := exists_nat_gt ((z - v) / m)
      have hN' : z - v < (N : ℝ) * m := by
        exact (div_lt_iff₀ hm_pos').mp hN
      have hNbound : split_dot c (y + (N : ℝ) • d) ≤ z := hbound N
      have hNlarge : z < split_dot c (y + (N : ℝ) • d) := by
        calc
          z < v + (N : ℝ) * m := by linarith
          _ = split_dot c (y + (N : ℝ) • d) := by
                dsimp [v, m]
                rw [integerDot_add_smul]
      exact (not_lt_of_ge hNbound hNlarge).elim
    have hm_nonneg : 0 ≤ m := by
      by_contra hm_neg
      have hm_neg' : m < 0 := lt_of_not_ge hm_neg
      have hminus_pos : 0 < -m := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt ((z - v) / (-m))
      have hN' : z - v < (N : ℝ) * (-m) := by
        exact (div_lt_iff₀ hminus_pos).mp hN
      have hNbound : split_dot c (y + (-(N : ℝ)) • d) ≤ z := hbound (-(N : ℝ))
      have hNlarge : z < split_dot c (y + (-(N : ℝ)) • d) := by
        calc
          z < v + (N : ℝ) * (-m) := by linarith
          _ = split_dot c (y + (-(N : ℝ)) • d) := by
                dsimp [v, m]
                rw [integerDot_add_smul]
                ring
      exact (not_lt_of_ge hNbound hNlarge).elim
    have hm : m = 0 := by
      linarith
    have hm_eval : m = ((c i * s.π j - c j * s.π i : ℤ) : ℝ) := by
      -- Evaluating the objective on `d` produces the 2x2 determinant relation.
      dsimp [m]
      rw [show d = Pi.single i (s.π j : ℝ) + (-1 : ℝ) • Pi.single j (s.π i : ℝ) by
        ext k
        simp [d, sub_eq_add_neg]]
      rw [integerDot_add_smul, integerDot_single, integerDot_single]
      norm_num
      ring
    have hint_zero : c i * s.π j - c j * s.π i = 0 := by
      have hreal : ((c i * s.π j - c j * s.π i : ℤ) : ℝ) = 0 := by
        simpa [m, hm_eval] using hm
      exact_mod_cast hreal
    exact sub_eq_zero.mp hint_zero
  obtain ⟨u, hu⟩ := split_isPrimitive_has_bezout_coefficients I s hprimitive
  let t : ℤ := ∑ j : Fin n, c j * u j
  have hc : c = fun j ↦ t * s.π j := by
    funext i
    -- Bézout coefficients reconstruct the whole objective from its value on the primitive row.
    calc
      c i = c i * 1 := by ring
      _ = c i * ∑ j : Fin n, s.π j * u j := by rw [hu]
      _ = ∑ j : Fin n, c i * (s.π j * u j) := by rw [Finset.mul_sum]
      _ = ∑ j : Fin n, (c j * s.π i) * u j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            calc
              c i * (s.π j * u j) = (c i * s.π j) * u j := by ring
              _ = (c j * s.π i) * u j := by rw [hkernel i j]
      _ = s.π i * ∑ j : Fin n, c j * u j := by
            calc
              ∑ j : Fin n, (c j * s.π i) * u j
                  = ∑ j : Fin n, s.π i * (c j * u j) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      ring
              _ = s.π i * ∑ j : Fin n, c j * u j := by
                    rw [Finset.mul_sum]
      _ = t * s.π i := by
            ring
  obtain ⟨xmax, hxmax_mem, hxmax_eq⟩ := hz.1
  obtain ⟨wz, hwz⟩ := exists_integral_point_on_primitive_split_hyperplane I s hprimitive 1
  let w : Fin n → ℝ := Int.cast ∘ wz
  have hw_split : split_dot s w = 1 := by
    have hw_split_sum : ∑ j : Fin n, (s.π j : ℝ) * (wz j : ℝ) = 1 := by
      exact_mod_cast hwz
    simpa [w, split_dot_eq_sum] using hw_split_sum
  have hw_obj : split_dot c w = (t : ℝ) := by
    -- The proportionality description reduces the objective on `w` to the split value `1`.
    simpa [hw_split] using integerDot_eq_intMul_splitDot s.π c t hc w
  have ht_nonneg : 0 ≤ t := by
    by_contra ht_neg
    have hxmax_le : split_dot s xmax ≤ (Int.floor δ : ℝ) := hxmax_mem
    have hxshift_mem : xmax - w ∈ {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)} := by
      -- Moving one unit in the negative split direction preserves feasibility.
      change split_dot s (xmax - w) ≤ (Int.floor δ : ℝ)
      calc
        split_dot s (xmax - w) = split_dot s xmax + (-1 : ℝ) * split_dot s w := by
          simpa [sub_eq_add_neg] using
            (show split_dot s.π (xmax + (-1 : ℝ) • w) =
                split_dot s.π xmax + (-1 : ℝ) * split_dot s.π w by
              rw [integerDot_add_smul])
        _ = split_dot s xmax - 1 := by rw [hw_split]; ring
        _ ≤ (Int.floor δ : ℝ) := by linarith [hxmax_le]
    have hxshift_val : split_dot c (xmax - w) = z - (t : ℝ) := by
      -- The shifted point improves the objective by `-t`.
      have hxmax_split : split_dot c xmax = z := by
        simpa [split_dot] using hxmax_eq
      calc
        split_dot c (xmax - w) = split_dot c xmax + (-1 : ℝ) * split_dot c w := by
          simpa [sub_eq_add_neg] using
            (show split_dot c (xmax + (-1 : ℝ) • w) =
                split_dot c xmax + (-1 : ℝ) * split_dot c w by
              rw [integerDot_add_smul])
        _ = z - (t : ℝ) := by rw [hxmax_split, hw_obj]; ring
    have hcontra : z < split_dot c (xmax - w) := by
      rw [hxshift_val]
      have ht_neg_real : (t : ℝ) < 0 := by
        exact_mod_cast (lt_of_not_ge ht_neg : t < 0)
      linarith
    exact (not_lt_of_ge (hz.2 ⟨xmax - w, hxshift_mem, rfl⟩) hcontra).elim
  exact ⟨t, ht_nonneg, hc⟩

/-- Helper for Definition 5.2-extra-1: every finite maximum of an integral objective on the
rounded split halfspace is an integer. -/
lemma integralObjectiveMaximum_isInteger_onRoundedHalfspace
    (I : Finset (Fin n))
    (s : Split I)
    (δ : ℝ)
    (hprimitive : s.IsPrimitive)
    (c : Fin n → ℤ)
    (z : ℝ)
    (hz : IsGreatest
      (((Int.cast ∘ c) ⬝ᵥ ·) '' {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)}) z) :
    ∃ k : ℤ, z = k := by
  obtain ⟨t, ht_nonneg, hc⟩ :=
    integralObjectiveProportionalToSplitOnRoundedHalfspace I s δ hprimitive c z hz
  obtain ⟨wz, hwz⟩ :=
    exists_integral_point_on_primitive_split_hyperplane I s hprimitive (Int.floor δ)
  let w : Fin n → ℝ := Int.cast ∘ wz
  have hw_split : split_dot s w = (Int.floor δ : ℝ) := by
    have hw_split_sum : ∑ j : Fin n, (s.π j : ℝ) * (wz j : ℝ) = (Int.floor δ : ℝ) := by
      exact_mod_cast hwz
    simpa [w, split_dot_eq_sum] using hw_split_sum
  have hw_mem : w ∈ {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)} := by
    simp [hw_split]
  have hw_obj : split_dot c w = ((t * Int.floor δ : ℤ) : ℝ) := by
    -- On the rounded boundary, the proportional objective evaluates to the corresponding integer.
    calc
      split_dot c w = (t : ℝ) * split_dot s w := by
        simpa using integerDot_eq_intMul_splitDot s.π c t hc w
      _ = (t : ℝ) * (Int.floor δ : ℝ) := by rw [hw_split]
      _ = ((t * Int.floor δ : ℤ) : ℝ) := by exact_mod_cast rfl
  obtain ⟨xmax, hxmax_mem, hxmax_eq⟩ := hz.1
  have hxmax_split : split_dot c xmax = z := by
    simpa [split_dot] using hxmax_eq
  have hz_le : z ≤ ((t * Int.floor δ : ℤ) : ℝ) := by
    -- Nonnegative proportional objectives are maximized on the boundary `split_dot s x = ⌊δ⌋`.
    calc
      z = split_dot c xmax := hxmax_split.symm
      _ = (t : ℝ) * split_dot s xmax := by
            simpa using integerDot_eq_intMul_splitDot s.π c t hc xmax
      _ ≤ (t : ℝ) * (Int.floor δ : ℝ) := by
            have ht_nonneg_real : 0 ≤ (t : ℝ) := by exact_mod_cast ht_nonneg
            exact mul_le_mul_of_nonneg_left hxmax_mem ht_nonneg_real
      _ = ((t * Int.floor δ : ℤ) : ℝ) := by exact_mod_cast rfl
  have hz_ge : ((t * Int.floor δ : ℤ) : ℝ) ≤ z := by
    -- The boundary lattice point attains that upper bound.
    have hw_bound : split_dot c w ≤ z := hz.2 ⟨w, hw_mem, rfl⟩
    simpa [hw_obj] using hw_bound
  refine ⟨t * Int.floor δ, ?_⟩
  exact le_antisymm hz_le hz_ge

/-- Helper for Definition 5.2-extra-1: the rounded split halfspace is a rational polyhedron. -/
lemma roundedSplitHalfspace_isRationalPolyhedron
    (I : Finset (Fin n))
    (s : Split I)
    (δ : ℝ) :
    is_rational_polyhedron {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)} := by
  let A : Matrix (Fin 1) (Fin n) ℚ := fun _ j ↦ s.π j
  let b : Fin 1 → ℚ := fun _ ↦ Int.floor δ
  refine ⟨1, A, b, ?_⟩
  ext x
  constructor
  · intro hx
    change (A.map (Rat.castHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ)
    intro i
    fin_cases i
    simpa [A, b, split_dot_eq_sum, dotProduct]
      using hx
  · intro hx
    change split_dot s x ≤ (Int.floor δ : ℝ)
    have hx0 := hx 0
    simpa [A, b, split_dot_eq_sum, dotProduct]
      using hx0

/-- Helper for Definition 5.2-extra-1: every integer point of the rounded split halfspace is a
mixed-integer point of the original split halfspace. -/
lemma integerPoints_roundedSplitHalfspace_subset_mixedIntegerHalfspace
    (I : Finset (Fin n))
    (s : Split I)
    (δ : ℝ) :
    ({x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)} ∩ ℤ^n) ⊆
      {x : Fin n → ℝ |
        (∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)) ∧ split_dot s x ≤ δ} := by
  intro x hx
  rcases (mem_integerVectors_iff_forall).mp hx.2 with hx_int
  refine ⟨?_, le_trans hx.1 (Int.floor_le δ)⟩
  intro j hj
  rcases hx_int j with ⟨z, hz⟩
  exact ⟨z, hz.symm⟩

/-- Definition 5.2-extra-1 (6). If the coefficients of the split vector are relatively prime on
the integer-variable indices, then the mixed-integer halfspace
`{x ∈ ℤ^I × ℝ^C | π x ≤ δ}` has convex hull equal to the rounded real halfspace
`{x ∈ ℝ^n | π x ≤ ⌊δ⌋}`. -/
theorem convexHull_mixed_integer_halfspace_eq_rounded_halfspace_of_relatively_prime_coefficients
    (I : Finset (Fin n))
    (s : Split I)
    (δ : ℝ)
    (hprimitive : s.IsPrimitive) :
    convexHull ℝ
      {x : Fin n → ℝ |
        (∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)) ∧ split_dot s x ≤ δ} =
      {x : Fin n → ℝ | split_dot s x ≤ (Int.floor δ : ℝ)} := by
  apply Set.Subset.antisymm
  · -- Every generator satisfies the rounded inequality, and convexity preserves that inclusion.
    refine convexHull_min ?_ (split_halfspace_convex s (Int.floor δ : ℝ))
    intro x hx
    exact split_dot_le_floor_of_integral_coordinates I s δ hx.1 hx.2
  · intro x hx
    let roundedHalfspace : Set (Fin n → ℝ) :=
      {y : Fin n → ℝ | split_dot s y ≤ (Int.floor δ : ℝ)}
    let mixedHalfspace : Set (Fin n → ℝ) :=
      {y : Fin n → ℝ |
        (∀ j ∈ I, ∃ z : ℤ, y j = (z : ℝ)) ∧ split_dot s y ≤ δ}
    have hrounded_rational :
        is_rational_polyhedron roundedHalfspace :=
      roundedSplitHalfspace_isRationalPolyhedron I s δ
    have hrounded_integral : is_integral roundedHalfspace := by
      -- Route correction: rather than transport through `Fin n ≃ I ⊕ Iᶜ`, prove the rounded
      -- one-row halfspace is integral by Theorem 4.1(3).
      refine
        (rational_polyhedron_is_integral_iff_integral_linear_maxima_are_integer
          roundedHalfspace hrounded_rational).2 ?_
      intro c z hz
      exact integralObjectiveMaximum_isInteger_onRoundedHalfspace I s δ hprimitive c z hz
    have hrounded_eq_hull :
        roundedHalfspace = convexHull ℝ (roundedHalfspace ∩ ℤ^n) := by
      exact (is_integral_iff).mp hrounded_integral
    have hinteger_subset : roundedHalfspace ∩ ℤ^n ⊆ mixedHalfspace := by
      exact integerPoints_roundedSplitHalfspace_subset_mixedIntegerHalfspace I s δ
    -- Rewrite the rounded halfspace as the hull of its integer points, then enlarge generators to
    -- the mixed-integer halfspace by monotonicity.
    have hx_hull : x ∈ convexHull ℝ (roundedHalfspace ∩ ℤ^n) := by
      rw [← hrounded_eq_hull]
      exact hx
    exact (convexHull_mono hinteger_subset) hx_hull

end Definition52Extra1
