import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_6.ch4_sec4_6_definition_4_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_40

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: totally dual integral descriptions of rational polyhedra
-- * sampled owner declarations: Chapter 4.1 `rational_matrix_polyhedron` and `is_integral`,
--   Chapter 4.6 `totally_dual_integral`, and Theorem 4.26
-- * owner abstraction: the Chapter 4.6 owner `totally_dual_integral A b` on the Chapter 4.1
--   rational-system owner `rational_matrix_polyhedron A b`
-- * source/core/bridge triage: Theorem 4.27 is source-facing existential content stated directly
--   in terms of the Chapter 4 owners, so no extra wrapper around "integral TDI presentations" is
--   introduced
-- * primitive data: a finite row index `m : ℕ`, an integral matrix presentation, and, in part
--   `(2)`, an integral right-hand side witness
-- * derived API: equality with the target polyhedron and the TDI property of that presentation

section Theorem427

variable {n : ℕ} (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: a rational polyhedron
comes with a finite rational matrix presentation in the canonical polyhedron owner. -/
private lemma existsRationalMatrixPresentation
    (hP : is_rational_polyhedron P) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℚ, ∃ b : Fin m → ℚ,
      P = rational_matrix_polyhedron A b := by
  -- The rational-polyhedron owner already exposes exactly the required finite presentation.
  rcases (is_rational_polyhedron_iff.mp hP) with ⟨m, A, b, hEq⟩
  have hCanonical : P = rational_matrix_polyhedron A b := by
    simpa [rational_matrix_polyhedron] using hEq
  exact ⟨m, A, b, hCanonical⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: the common
denominator of a finite rational vector is nonzero. -/
private lemma rationalVectorCommonDenominator_ne_zero
    {q : ℕ} (v : Fin q → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  -- Positivity of every rational denominator survives the finite least common multiple.
  simp [rational_vector_common_denominator]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: every rational
polyhedron has an equivalent presentation whose coefficient matrix is integral. -/
private lemma existsIntegralMatrixPresentation
    (hP : is_rational_polyhedron P) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℚ,
      P = rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b := by
  obtain ⟨m, A, b, hP_eq⟩ := existsRationalMatrixPresentation P hP
  let d : Fin m → ℕ := fun i ↦ rational_vector_common_denominator (A i)
  let C : Matrix (Fin m) (Fin n) ℤ :=
    fun i ↦ common_denominator_scaled_vector (A i)
  let e : Fin m → ℚ := fun i ↦ (d i : ℚ) * b i
  refine ⟨m, C, e, hP_eq.trans ?_⟩
  ext x
  rw [mem_rational_matrix_polyhedron, mem_rational_matrix_polyhedron]
  have hrow : ∀ i : Fin m,
      (((C.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ x) i =
        (d i : ℝ) * ((A.map (Rat.castHom ℝ) *ᵥ x) i) := by
    intro i
    have hscaled := common_denominator_scaled_vector_eq_smul (A i)
    -- Cast the rowwise common-denominator identity once, then evaluate the matrix product.
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hcoord := congrFun hscaled j
    norm_num [C, d, Pi.smul_apply] at hcoord
    have hcoordReal :
        (common_denominator_scaled_vector (A i) j : ℝ) =
          (rational_vector_common_denominator (A i) : ℝ) * (A i j : ℝ) := by
      exact_mod_cast hcoord
    norm_num [C, d]
    rw [hcoordReal]
    ring
  constructor
  · intro hx i
    have hdi_pos : (0 : ℝ) < d i := by
      exact_mod_cast Nat.pos_of_ne_zero (rationalVectorCommonDenominator_ne_zero (A i))
    have hxi := hx i
    rw [hrow i]
    change (d i : ℝ) * ((A.map (Rat.castHom ℝ) *ᵥ x) i) ≤ (e i : ℝ)
    have he : (e i : ℝ) = (d i : ℝ) * (b i : ℝ) := by
      simp [e, d]
    rw [he]
    exact mul_le_mul_of_nonneg_left hxi hdi_pos.le
  · intro hx i
    have hdi_pos : (0 : ℝ) < d i := by
      exact_mod_cast Nat.pos_of_ne_zero (rationalVectorCommonDenominator_ne_zero (A i))
    have hxi := hx i
    rw [hrow i] at hxi
    simp only at hxi
    have he : (e i : ℝ) = (d i : ℝ) * (b i : ℝ) := by
      simp [e, d]
    rw [he] at hxi
    exact le_of_mul_le_mul_left hxi hdi_pos

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: membership in a
finite rational cone can be expressed using coefficients on the original finite index type. -/
private lemma existsNonnegativeCoefficientFunctionOfMemHull
    {q : ℕ} (r : Fin q → Fin n → ℚ) {v : Fin n → ℚ}
    (hv : v ∈ (PointedCone.hull ℚ (Set.range r) : Set (Fin n → ℚ))) :
    ∃ coeff : Fin q → ℚ, (∀ i, 0 ≤ coeff i) ∧ v = ∑ i, coeff i • r i := by
  classical
  rcases (mem_hull_iff.mp hv) with ⟨s, r', hr_mem, coeff, hcoeff_nonneg, hv_eq⟩
  let idx : Fin s → Fin q := fun k ↦ Classical.choose (hr_mem k)
  have hidx : ∀ k : Fin s, r (idx k) = r' k := by
    intro k
    exact Classical.choose_spec (hr_mem k)
  let coeff' : Fin q → ℚ := fun i ↦ ∑ k : Fin s, if idx k = i then coeff k else 0
  refine ⟨coeff', ?_, ?_⟩
  · intro i
    refine Finset.sum_nonneg ?_
    intro k hk
    by_cases hki : idx k = i
    · simp [hki, hcoeff_nonneg k]
    · simp [hki]
  · ext j
    -- Aggregate repeated selected generators back onto the original finite family.
    symm
    calc
      (∑ i : Fin q, coeff' i • r i) j =
          ∑ i : Fin q, (∑ k : Fin s, if idx k = i then coeff k else 0) * r i j := by
            simp [coeff', Pi.smul_apply]
      _ = ∑ i : Fin q, ∑ k : Fin s,
          (if idx k = i then coeff k else 0) * r i j := by simp_rw [Finset.sum_mul]
      _ = ∑ k : Fin s, ∑ i : Fin q,
          (if idx k = i then coeff k else 0) * r i j := by rw [Finset.sum_comm]
      _ = ∑ k : Fin s, coeff k * r' k j := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [hidx k]
      _ = (∑ k : Fin s, coeff k • r' k) j := by simp [Pi.smul_apply]
      _ = v j := by simpa using (congrFun hv_eq j).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: removing the
integer parts of cone coefficients leaves an integral remainder in the half-open coefficient box. -/
private lemma existsHalfOpenBoxRemainderOfIntegralConePoint
    {q : ℕ} (a : Fin q → Fin n → ℤ) {z : Fin n → ℤ}
    (hz : (fun t ↦ (z t : ℚ)) ∈
      (PointedCone.hull ℚ (Set.range fun j : Fin q ↦ fun t ↦ (a j t : ℚ)) :
        Set (Fin n → ℚ))) :
    ∃ coeff : Fin q → ℚ, ∃ μ₀ : Fin q →₀ ℕ, ∃ ρ : Fin n → ℤ,
      (∀ j, 0 ≤ coeff j) ∧
      z = μ₀.sum (fun j c ↦ c • a j) + ρ ∧
      (fun t ↦ (ρ t : ℚ)) =
        ∑ j : Fin q, Int.fract (coeff j) • (fun t ↦ (a j t : ℚ)) ∧
      (∀ j, 0 ≤ Int.fract (coeff j)) ∧
      (∀ j, Int.fract (coeff j) < 1) := by
  obtain ⟨coeff, hcoeff_nonneg, hz_eq⟩ :=
    existsNonnegativeCoefficientFunctionOfMemHull
      (fun j : Fin q ↦ fun t ↦ (a j t : ℚ)) hz
  let μNat : Fin q → ℕ := fun j ↦ Int.toNat (Int.floor (coeff j))
  let μ₀ : Fin q →₀ ℕ := Finsupp.equivFunOnFinite.symm μNat
  have hμCast : ∀ j : Fin q, ((μ₀ j : ℕ) : ℚ) = (Int.floor (coeff j) : ℚ) := by
    intro j
    have hfloor_nonneg : 0 ≤ Int.floor (coeff j) := Int.floor_nonneg.mpr (hcoeff_nonneg j)
    calc
      ((μ₀ j : ℕ) : ℚ) = (Int.toNat (Int.floor (coeff j)) : ℚ) := by simp [μ₀, μNat]
      _ = (Int.floor (coeff j) : ℚ) := by
        exact_mod_cast (Int.toNat_of_nonneg hfloor_nonneg)
  have hμ₀Q_eq :
      (fun t ↦ ((μ₀.sum (fun j c ↦ c • a j)) t : ℚ)) =
        ∑ j : Fin q, (Int.floor (coeff j) : ℚ) • (fun t ↦ (a j t : ℚ)) := by
    ext t
    have hzeroSum : ∀ j : Fin q, (0 : ℕ) • a j = 0 := by
      intro j
      simp
    -- Normalize both sides to the same coordinatewise finite sum before replacing coefficients.
    calc
      ((μ₀.sum (fun j c ↦ c • a j)) t : ℚ) =
          ∑ j : Fin q, ((μ₀ j : ℕ) : ℚ) * (a j t : ℚ) := by
            rw [Finsupp.sum_fintype _ _ hzeroSum, Finset.sum_apply]
            simp
      _ = ∑ j : Fin q, (Int.floor (coeff j) : ℚ) * (a j t : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hμCast j]
      _ = (∑ j : Fin q, (Int.floor (coeff j) : ℚ) • (fun s ↦ (a j s : ℚ))) t := by
            simp [Pi.smul_apply]
  let ρ : Fin n → ℤ := z - μ₀.sum (fun j c ↦ c • a j)
  refine ⟨coeff, μ₀, ρ, hcoeff_nonneg, ?_, ?_, ?_, ?_⟩
  · ext t
    simp [ρ, sub_eq_add_neg, add_left_comm]
  · ext t
    calc
      (ρ t : ℚ) = (z t : ℚ) - ((μ₀.sum (fun j c ↦ c • a j)) t : ℚ) := by simp [ρ]
      _ = (∑ j : Fin q, coeff j * (a j t : ℚ)) -
          ∑ j : Fin q, (Int.floor (coeff j) : ℚ) * (a j t : ℚ) := by
            rw [congrFun hz_eq t, congrFun hμ₀Q_eq t]
            simp [Pi.smul_apply]
      _ = ∑ j : Fin q, (coeff j - (Int.floor (coeff j) : ℚ)) * (a j t : ℚ) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = ∑ j : Fin q, Int.fract (coeff j) * (a j t : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hdecomp : coeff j - (Int.floor (coeff j) : ℚ) = Int.fract (coeff j) := by
              linarith [Int.floor_add_fract (coeff j)]
            rw [hdecomp]
      _ = (∑ j : Fin q, Int.fract (coeff j) • (fun s ↦ (a j s : ℚ))) t := by
            simp [Pi.smul_apply]
  · intro j
    exact Int.fract_nonneg (coeff j)
  · intro j
    exact Int.fract_lt_one (coeff j)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: a combination
with coefficients in `[0,1]` lies in the coordinate box determined by the integral generators. -/
private lemma weightedIntegralCombination_mem_coordinateBox
    {q : ℕ} (a : Fin q → ℤ) (coeff : Fin q → ℚ)
    (hcoeff_nonneg : ∀ j, 0 ≤ coeff j) (hcoeff_le_one : ∀ j, coeff j ≤ 1) :
    (∑ j : Fin q, coeff j * (a j : ℚ)) ∈
      Set.Icc (∑ j : Fin q, ((min (a j) 0 : ℤ) : ℚ))
        (∑ j : Fin q, ((max (a j) 0 : ℤ) : ℚ)) := by
  constructor
  · refine Finset.sum_le_sum fun j _ ↦ ?_
    by_cases haj : a j ≤ 0
    · have hajQ : (a j : ℚ) ≤ 0 := by exact_mod_cast haj
      have hmul : (a j : ℚ) ≤ coeff j * (a j : ℚ) := by
        nlinarith [hcoeff_le_one j, hajQ]
      simpa [min_eq_left haj] using hmul
    · have h0aj : 0 ≤ a j := le_of_lt (lt_of_not_ge haj)
      have h0ajQ : (0 : ℚ) ≤ (a j : ℚ) := by exact_mod_cast h0aj
      have hmul : (0 : ℚ) ≤ coeff j * (a j : ℚ) :=
        mul_nonneg (hcoeff_nonneg j) h0ajQ
      simpa [min_eq_right h0aj] using hmul
  · refine Finset.sum_le_sum fun j _ ↦ ?_
    by_cases haj : 0 ≤ a j
    · have hajQ : (0 : ℚ) ≤ (a j : ℚ) := by exact_mod_cast haj
      have hmul : coeff j * (a j : ℚ) ≤ (a j : ℚ) := by
        nlinarith [hcoeff_nonneg j, hcoeff_le_one j, hajQ]
      simpa [max_eq_left haj] using hmul
    · have hajNonpos : a j ≤ 0 := le_of_lt (lt_of_not_ge haj)
      have hajQ : (a j : ℚ) ≤ 0 := by exact_mod_cast hajNonpos
      have hmul : coeff j * (a j : ℚ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hcoeff_nonneg j) hajQ
      simpa [max_eq_right hajNonpos] using hmul

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: the integral
points of a finite coordinate box admit a finite enumeration. -/
private lemma existsFiniteIntegralPointsOfCoordinateBox
    (lower upper : Fin n → ℤ) :
    ∃ t : ℕ, ∃ s : Fin t → Fin n → ℤ,
      (∀ j i, s j i ∈ Set.Icc (lower i) (upper i)) ∧
      ∀ ρ : Fin n → ℤ, (∀ i, ρ i ∈ Set.Icc (lower i) (upper i)) →
        ∃ j : Fin t, s j = ρ := by
  classical
  let box : Set (Fin n → ℤ) := {ρ | ∀ i, ρ i ∈ Set.Icc (lower i) (upper i)}
  have hboxFinite : box.Finite := by
    simpa [box, Set.pi] using
      (Set.Finite.pi (t := fun i : Fin n ↦ Set.Icc (lower i) (upper i))
        fun i ↦ Set.finite_Icc (lower i) (upper i))
  obtain ⟨t, s, hs_inj, hs_range⟩ := hboxFinite.fin_param
  refine ⟨t, s, ?_, ?_⟩
  · intro j i
    have hs_mem : s j ∈ box := by
      rw [← hs_range]
      exact ⟨j, rfl⟩
    exact hs_mem i
  · intro ρ hρ
    have hρ_mem : ρ ∈ box := hρ
    rw [← hs_range] at hρ_mem
    exact hρ_mem

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: finitely many
integral cone remainders cover every integral cone point modulo the original generators. -/
private lemma existsFiniteIntegralRemainderFamilyOfIntegralCone
    {q : ℕ} (a : Fin q → Fin n → ℤ) :
    ∃ t : ℕ, ∃ s : Fin t → Fin n → ℤ,
      (∀ j : Fin t, (fun i ↦ (s j i : ℚ)) ∈
        (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
          Set (Fin n → ℚ))) ∧
      ∀ z : Fin n → ℤ,
        (fun i ↦ (z i : ℚ)) ∈
          (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
            Set (Fin n → ℚ)) →
        ∃ j : Fin t, ∃ μ : Fin q →₀ ℕ,
          z = s j + μ.sum (fun l c ↦ c • a l) := by
  classical
  let lower : Fin n → ℤ := fun i ↦ ∑ l : Fin q, min (a l i) 0
  let upper : Fin n → ℤ := fun i ↦ ∑ l : Fin q, max (a l i) 0
  obtain ⟨tBox, sBox, hsBox_mem, hsBox_cover⟩ :=
    existsFiniteIntegralPointsOfCoordinateBox lower upper
  let remainderIndex : Set (Fin tBox) :=
    {j | (fun i ↦ (sBox j i : ℚ)) ∈
      (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
        Set (Fin n → ℚ))}
  obtain ⟨t, e, he_inj, he_range⟩ := (Set.toFinite remainderIndex).fin_param
  let s : Fin t → Fin n → ℤ := fun j ↦ sBox (e j)
  refine ⟨t, s, ?_, ?_⟩
  · intro j
    have hej : e j ∈ remainderIndex := by
      rw [← he_range]
      exact ⟨j, rfl⟩
    exact hej
  · intro z hz
    obtain ⟨coeff, μ₀, ρ, hcoeff_nonneg, hz_split, hρ_eq, hfract_nonneg, hfract_lt_one⟩ :=
      existsHalfOpenBoxRemainderOfIntegralConePoint a hz
    have hρ_mem : (fun i ↦ (ρ i : ℚ)) ∈
        (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
          Set (Fin n → ℚ)) := by
      -- The fractional remainder is still a nonnegative conic combination.
      refine (mem_hull_iff).2 ?_
      refine ⟨q, (fun l : Fin q ↦ fun u ↦ (a l u : ℚ)), ?_,
        (fun l ↦ Int.fract (coeff l)), hfract_nonneg, hρ_eq⟩
      intro l
      exact ⟨l, rfl⟩
    have hρ_box : ∀ i : Fin n, ρ i ∈ Set.Icc (lower i) (upper i) := by
      intro i
      have hcoordBox := weightedIntegralCombination_mem_coordinateBox
        (fun l : Fin q ↦ a l i) (fun l ↦ Int.fract (coeff l)) hfract_nonneg
        (fun l ↦ (hfract_lt_one l).le)
      have hcoordEq : (ρ i : ℚ) = ∑ l : Fin q, Int.fract (coeff l) * (a l i : ℚ) := by
        simpa [Pi.smul_apply] using congrFun hρ_eq i
      rw [← hcoordEq] at hcoordBox
      have hLower : lower i ≤ ρ i := by
        exact_mod_cast hcoordBox.1
      have hUpper : ρ i ≤ upper i := by
        exact_mod_cast hcoordBox.2
      exact ⟨hLower, hUpper⟩
    rcases hsBox_cover ρ hρ_box with ⟨jBox, hjBox⟩
    have hjBox_mem : jBox ∈ remainderIndex := by
      change (fun i ↦ (sBox jBox i : ℚ)) ∈
        (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
          Set (Fin n → ℚ))
      simpa [hjBox] using hρ_mem
    have hjBox_range : jBox ∈ Set.range e := by
      rw [he_range]
      exact hjBox_mem
    rcases hjBox_range with ⟨j, rfl⟩
    refine ⟨j, μ₀, ?_⟩
    simpa [s, hjBox, add_comm, add_left_comm, add_assoc] using hz_split

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: every cone
generated by a finite integral family has a finite integral Hilbert basis inside that cone. -/
private lemma existsFiniteIntegralHilbertBasisOfIntegralCone
    {q : ℕ} (a : Fin q → Fin n → ℤ) :
    ∃ t : ℕ, ∃ h : Fin t → Fin n → ℤ,
      (∀ j : Fin t, (fun i ↦ (h j i : ℚ)) ∈
        (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
          Set (Fin n → ℚ))) ∧
      ∀ z : Fin n → ℤ,
        (fun i ↦ (z i : ℚ)) ∈
          (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
            Set (Fin n → ℚ)) →
        ∃ μ : Fin t →₀ ℕ, z = μ.sum (fun j c ↦ c • h j) := by
  classical
  obtain ⟨t, s, hs_mem, hs_cover⟩ := existsFiniteIntegralRemainderFamilyOfIntegralCone a
  let h : Fin (t + q) → Fin n → ℤ := Fin.append s a
  refine ⟨t + q, h, ?_, ?_⟩
  · intro j
    -- Each new basis vector is either a cone remainder or an original generator.
    refine Fin.addCases ?_ ?_ j
    · intro k
      simpa [h] using hs_mem k
    · intro k
      simpa [h] using
        (PointedCone.subset_hull
          (s := Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) ⟨k, rfl⟩)
  · intro z hz
    obtain ⟨j, μ, hz_split⟩ := hs_cover z hz
    let coeff : Fin (t + q) → ℕ := Fin.append (Pi.single j 1) (fun k ↦ μ k)
    let ν : Fin (t + q) →₀ ℕ := Finsupp.equivFunOnFinite.symm coeff
    refine ⟨ν, ?_⟩
    -- Splitting the final finite sum recovers the selected remainder and the old generators.
    ext i
    have hzeroH : ∀ j : Fin (t + q), (0 : ℕ) • h j = 0 := by
      intro j
      simp
    have hzeroA : ∀ j : Fin q, (0 : ℕ) • a j = 0 := by
      intro j
      simp
    have hμCoord :
        (μ.sum (fun j c ↦ c • a j)) i = ∑ j : Fin q, μ j * a j i := by
      rw [Finsupp.sum_fintype _ _ hzeroA, Finset.sum_apply]
      simp
    have hzCoord := congrFun hz_split i
    simp only [Pi.add_apply] at hzCoord
    rw [hμCoord] at hzCoord
    rw [Finsupp.sum_fintype _ _ hzeroH, Fin.sum_univ_add]
    simp only [nsmul_eq_mul, Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
    simpa [ν, coeff, h, Pi.single_apply] using hzCoord

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: a real
nonnegative solution of a rational linear system can be replaced by a rational one. -/
private lemma existsRationalNonnegativeSolutionOfRealCastFeasible
    {ι : Type*} [Fintype ι]
    (M : Matrix ι (Fin n) ℚ)
    (d : Fin n → ℚ)
    (hreal :
      ∃ xR : ι → ℝ,
        xR ᵥ* M.map (Rat.castHom ℝ) = (fun j ↦ (d j : ℝ)) ∧ 0 ≤ xR) :
    ∃ xQ : ι → ℚ, xQ ᵥ* M = d ∧ 0 ≤ xQ := by
  rcases hreal with ⟨xR, hxR_row, hxR_nonneg⟩
  have hrealTranspose :
      ∃ xR : ι → ℝ,
        M.transpose.map (Rat.castHom ℝ) *ᵥ xR = (fun j ↦ (d j : ℝ)) ∧ 0 ≤ xR := by
    refine ⟨xR, ?_, hxR_nonneg⟩
    -- Transposition puts the row-vector equation into the Farkas interface.
    simpa [Matrix.transpose_map] using
      (Matrix.mulVec_transpose (M.map (Rat.castHom ℝ)) xR).trans hxR_row
  have hrealMultipliers :
      ∀ u : Fin n → ℝ,
        u ᵥ* M.transpose.map (Rat.castHom ℝ) ≤ 0 →
          u ⬝ᵥ (fun j ↦ (d j : ℝ)) ≤ 0 :=
    (feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers
      (M.transpose.map (Rat.castHom ℝ)) (fun j ↦ (d j : ℝ))).mp hrealTranspose
  have hrationalMultipliers :
      ∀ u : Fin n → ℚ, u ᵥ* M.transpose ≤ 0 → u ⬝ᵥ d ≤ 0 := by
    intro u hu
    let uR : Fin n → ℝ := fun j ↦ (u j : ℝ)
    have huR : uR ᵥ* M.transpose.map (Rat.castHom ℝ) ≤ 0 := by
      intro i
      have hi : (u ᵥ* M.transpose) i ≤ 0 := hu i
      have hiR : ((u ᵥ* M.transpose) i : ℝ) ≤ 0 := by
        exact_mod_cast hi
      simpa [uR, Matrix.vecMul, dotProduct] using hiR
    have huRDot := hrealMultipliers uR huR
    have huDotCast : (((u ⬝ᵥ d : ℚ) : ℝ)) ≤ 0 := by
      simpa [uR, dotProduct] using huRDot
    exact_mod_cast huDotCast
  obtain ⟨xQ, hxQ, hxQ_nonneg⟩ :=
    (feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers M.transpose d).mpr
      hrationalMultipliers
  refine ⟨xQ, ?_, hxQ_nonneg⟩
  -- Transpose back to the original row-vector equation.
  simpa [Matrix.mulVec_transpose] using hxQ

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: an attained
integral objective belongs to the rational cone generated by the rows active at an optimizer. -/
private lemma integralObjective_mem_activeRowConeOfIsGreatest
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (c : Fin n → ℤ) (xStar : Fin n → ℝ)
    (hxStar : xStar ∈ rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b)
    (hopt :
      IsGreatest
        ((fun x : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) ''
          rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b)
        ((fun j ↦ (c j : ℝ)) ⬝ᵥ xStar)) :
    ∃ S : Finset (Fin m),
      (∀ i, i ∈ S ↔
        (((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ xStar) i = (b i : ℝ)) ∧
      (fun j ↦ (c j : ℚ)) ∈
        (PointedCone.hull ℚ
          (Set.range fun k : Fin S.card ↦
            fun j ↦ (A (((Finset.equivFin S).symm k : S) : Fin m) j : ℚ)) :
          Set (Fin n → ℚ)) := by
  classical
  let AQ : Matrix (Fin m) (Fin n) ℚ := A.map (Int.castRingHom ℚ)
  let AR : Matrix (Fin m) (Fin n) ℝ := AQ.map (Rat.castHom ℝ)
  let bR : Fin m → ℝ := fun i ↦ (b i : ℝ)
  let cR : Fin n → ℝ := fun j ↦ (c j : ℝ)
  let δ : ℝ := cR ⬝ᵥ xStar
  have hxStarReal : xStar ∈ polyhedron_le_set AR bR := by
    simpa [AQ, AR, bR, rational_matrix_polyhedron] using hxStar
  have hvalid : is_valid_inequality (polyhedron_le_set AR bR) cR δ := by
    intro x hx
    have hxQ : x ∈ rational_matrix_polyhedron AQ b := by
      simpa [AQ, AR, bR, rational_matrix_polyhedron] using hx
    exact hopt.2 ⟨x, hxQ, rfl⟩
  have hattained : (face_set (polyhedron_le_set AR bR) cR δ).Nonempty := by
    refine ⟨xStar, (mem_face_set_iff).2 ⟨hxStarReal, rfl⟩⟩
  obtain ⟨y, hyNonneg, hyRow, hyValue⟩ :=
    exists_nonneg_multiplier_of_attained_valid_inequality AR bR cR δ hvalid hattained
  let S : Finset (Fin m) := Finset.univ.filter fun i ↦ (AR *ᵥ xStar) i = bR i
  have hS : ∀ i, i ∈ S ↔ (AR *ᵥ xStar) i = bR i := by
    intro i
    simp [S]
  have hxFace : xStar ∈ face_set (polyhedron_le_set AR bR) cR δ :=
    (mem_face_set_iff).2 ⟨hxStarReal, rfl⟩
  have hxSupported :
      xStar ∈ active_constraint_face AR bR {i : Fin m | 0 < y i} :=
    (mem_face_set_iff_mem_active_constraint_face_of_support hyNonneg hyRow hyValue).mp hxFace
  have hyZero : ∀ i : Fin m, i ∉ S → y i = 0 := by
    intro i hi
    have hnotPos : ¬ 0 < y i := by
      intro hpos
      exact hi ((hS i).2 ((mem_active_constraint_face_iff.mp hxSupported).1 i hpos))
    exact le_antisymm (le_of_not_gt hnotPos) (hyNonneg i)
  let e : Fin S.card ≃ S := (Finset.equivFin S).symm
  let M : Matrix (Fin S.card) (Fin n) ℚ :=
    fun k j ↦ (A ((e k : S) : Fin m) j : ℚ)
  let yS : Fin S.card → ℝ := fun k ↦ y ((e k : S) : Fin m)
  have hySRow : yS ᵥ* M.map (Rat.castHom ℝ) = cR := by
    ext j
    have hfiltered :
        Finset.sum S (fun i ↦ y i * AR i j) = ∑ i : Fin m, y i * AR i j := by
      refine Finset.sum_subset (Finset.subset_univ S) ?_
      intro i hiUniv hiS
      simp [hyZero i hiS]
    calc
      (yS ᵥ* M.map (Rat.castHom ℝ)) j =
          ∑ k : Fin S.card, y ((e k : S) : Fin m) * AR ((e k : S) : Fin m) j := by
            simp [yS, M, AR, AQ, Matrix.vecMul, dotProduct]
      _ = ∑ i : S, y i.1 * AR i.1 j := by
            exact Fintype.sum_equiv e
              (fun k : Fin S.card ↦ y ((e k : S) : Fin m) * AR ((e k : S) : Fin m) j)
              (fun i : S ↦ y i.1 * AR i.1 j) (fun k ↦ rfl)
      _ = Finset.sum S (fun i ↦ y i * AR i j) := by
            simpa using (Finset.sum_attach S (fun i ↦ y i * AR i j))
      _ = ∑ i : Fin m, y i * AR i j := hfiltered
      _ = (y ᵥ* AR) j := rfl
      _ = cR j := congrFun hyRow j
  have hySNonneg : 0 ≤ yS := by
    intro k
    exact hyNonneg _
  have hySRowCast :
      yS ᵥ* M.map (Rat.castHom ℝ) = (fun j ↦ (c j : ℝ)) := by
    simpa [cR] using hySRow
  obtain ⟨q, hqRow, hqNonneg⟩ :=
    existsRationalNonnegativeSolutionOfRealCastFeasible M (fun j ↦ (c j : ℚ))
      ⟨yS, hySRowCast, hySNonneg⟩
  refine ⟨S, ?_, ?_⟩
  · intro i
    simpa [AQ, AR, bR] using hS i
  · refine (mem_hull_iff).2 ⟨S.card, M, ?_, q, hqNonneg, ?_⟩
    · intro k
      refine ⟨k, ?_⟩
      simp [M, e]
    · ext j
      have hj := congrFun hqRow j
      simpa [M, e, Matrix.vecMul, dotProduct, Pi.smul_apply] using hj.symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: a nonnegative
rational combination of valid integral rows is again a valid inequality. -/
private lemma nonnegativeIntegralRowCombination_valid
    {m q : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (idx : Fin q → Fin m) (qCoeff : Fin q → ℚ) (h : Fin n → ℤ)
    (hqNonneg : ∀ k, 0 ≤ qCoeff k)
    (hrow : (fun j ↦ (h j : ℚ)) =
      ∑ k : Fin q, qCoeff k • (fun j ↦ (A (idx k) j : ℚ)))
    {x : Fin n → ℝ}
    (hx : x ∈ rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b) :
    (fun j ↦ (h j : ℝ)) ⬝ᵥ x ≤ ∑ k : Fin q, (qCoeff k : ℝ) * (b (idx k) : ℝ) := by
  have hxRows : ∀ i, (((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ x) i ≤
      (b i : ℝ) := by
    simpa [rational_matrix_polyhedron] using hx
  have hrowReal : (fun j ↦ (h j : ℝ)) =
      ∑ k : Fin q, (qCoeff k : ℝ) • (fun j ↦ (A (idx k) j : ℝ)) := by
    ext j
    have hj := congrFun hrow j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    exact_mod_cast hj
  calc
    (fun j ↦ (h j : ℝ)) ⬝ᵥ x =
        (∑ k : Fin q, (qCoeff k : ℝ) • (fun j ↦ (A (idx k) j : ℝ))) ⬝ᵥ x := by
          rw [hrowReal]
    _ = ∑ k : Fin q, (qCoeff k : ℝ) *
        ((((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ x) (idx k)) := by
          simp [sum_dotProduct, smul_dotProduct, Matrix.mulVec]
    _ ≤ ∑ k : Fin q, (qCoeff k : ℝ) * (b (idx k) : ℝ) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          have hqNonnegReal : (0 : ℝ) ≤ qCoeff k := by
            exact_mod_cast hqNonneg k
          exact mul_le_mul_of_nonneg_left (hxRows (idx k)) hqNonnegReal

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: a feasible integral
dual certificate whose value equals an attained primal value is dual-optimal. -/
private lemma integralDualCertificateOfPrimalEquality
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ)
    (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : x ∈ rational_matrix_polyhedron A b)
    (hy : y ∈ rational_dual_feasible_region A c)
    (hyIntegral : y ∈ integerVectors m)
    (hvalue : y ⬝ᵥ (fun i ↦ (b i : ℝ)) = (fun j ↦ (c j : ℝ)) ⬝ᵥ x) :
    rational_dual_has_integral_optimal_solution A b c := by
  rw [rational_dual_has_integral_optimal_solution_iff]
  refine ⟨y, hy, hyIntegral, ?_⟩
  refine ⟨⟨y, hy, rfl⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hxReal :
      x ∈ primal_feasible_region (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
    -- Normalize the rational primal presentation to the real weak-duality interface.
    simpa [rational_matrix_polyhedron, primal_feasible_region] using hx
  have huReal :
      u ∈ dual_feasible_region (A.map (Rat.castHom ℝ)) (fun j ↦ (c j : ℝ)) := by
    -- The rational dual owner has the same real feasible set after unfolding.
    simpa [rational_dual_feasible_region, dual_feasible_region] using hu
  calc
    y ⬝ᵥ (fun i ↦ (b i : ℝ)) = (fun j ↦ (c j : ℝ)) ⬝ᵥ x := hvalue
    _ ≤ u ⬝ᵥ (fun i ↦ (b i : ℝ)) :=
      weak_duality_feasible_pair (A.map (Rat.castHom ℝ))
        (fun i ↦ (b i : ℝ)) (fun j ↦ (c j : ℝ)) hxReal huReal

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: choose a finite
integral Hilbert basis simultaneously for every subset of an integral row family. -/
private lemma existsHilbertBasesForAllRowSubsets
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ t : Finset (Fin m) → ℕ,
      ∃ h : ∀ S : Finset (Fin m), Fin (t S) → Fin n → ℤ,
        (∀ (S : Finset (Fin m)) (j : Fin (t S)), (fun u ↦ (h S j u : ℚ)) ∈
          (PointedCone.hull ℚ
            (Set.range fun k : Fin S.card ↦
              fun u ↦ (A (((Finset.equivFin S).symm k : S) : Fin m) u : ℚ)) :
            Set (Fin n → ℚ))) ∧
        ∀ (S : Finset (Fin m)) (z : Fin n → ℤ), (fun u ↦ (z u : ℚ)) ∈
            (PointedCone.hull ℚ
              (Set.range fun k : Fin S.card ↦
                fun u ↦ (A (((Finset.equivFin S).symm k : S) : Fin m) u : ℚ)) :
              Set (Fin n → ℚ)) →
          ∃ μ : Fin (t S) →₀ ℕ, z = μ.sum (fun j c ↦ c • h S j) := by
  classical
  have hEach : ∀ S : Finset (Fin m),
      ∃ q : ℕ, ∃ basis : Fin q → Fin n → ℤ,
        (∀ j, (fun u ↦ (basis j u : ℚ)) ∈
          (PointedCone.hull ℚ
            (Set.range fun k : Fin S.card ↦
              fun u ↦ (A (((Finset.equivFin S).symm k : S) : Fin m) u : ℚ)) :
            Set (Fin n → ℚ))) ∧
        ∀ z, (fun u ↦ (z u : ℚ)) ∈
            (PointedCone.hull ℚ
              (Set.range fun k : Fin S.card ↦
                fun u ↦ (A (((Finset.equivFin S).symm k : S) : Fin m) u : ℚ)) :
              Set (Fin n → ℚ)) →
          ∃ μ : Fin q →₀ ℕ, z = μ.sum (fun j c ↦ c • basis j) := by
    intro S
    -- Apply the finite-cone Hilbert-basis lemma to the rows enumerated by this subset.
    exact existsFiniteIntegralHilbertBasisOfIntegralCone
      (fun k : Fin S.card ↦ A (((Finset.equivFin S).symm k : S) : Fin m))
  choose t h hmem hgenerate using hEach
  exact ⟨t, h, hmem, hgenerate⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: a represented
row has the induced right-hand-side value at a point where all representing rows are tight. -/
private lemma integralRowCombination_value_of_tight
    {m q : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (idx : Fin q → Fin m) (qCoeff : Fin q → ℚ) (h : Fin n → ℤ)
    (hrow : (fun j ↦ (h j : ℚ)) =
      ∑ k : Fin q, qCoeff k • (fun j ↦ (A (idx k) j : ℚ)))
    (x : Fin n → ℝ)
    (htight : ∀ k, (((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ x) (idx k) =
      (b (idx k) : ℝ)) :
    (fun j ↦ (h j : ℝ)) ⬝ᵥ x =
      ∑ k : Fin q, (qCoeff k : ℝ) * (b (idx k) : ℝ) := by
  have hrowReal : (fun j ↦ (h j : ℝ)) =
      ∑ k : Fin q, (qCoeff k : ℝ) • (fun j ↦ (A (idx k) j : ℝ)) := by
    ext j
    have hj := congrFun hrow j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    exact_mod_cast hj
  calc
    (fun j ↦ (h j : ℝ)) ⬝ᵥ x =
        (∑ k : Fin q, (qCoeff k : ℝ) • (fun j ↦ (A (idx k) j : ℝ))) ⬝ᵥ x := by
          rw [hrowReal]
    _ = ∑ k : Fin q, (qCoeff k : ℝ) *
        ((((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ x) (idx k)) := by
          simp [sum_dotProduct, smul_dotProduct, Matrix.mulVec]
    _ = ∑ k : Fin q, (qCoeff k : ℝ) * (b (idx k) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [htight k]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: augment an
integral presentation by all active-row Hilbert bases, obtaining exact integral dual
certificates for every attained integral objective. -/
private lemma existsIntegralHilbertAugmentationWithOptimalCertificates
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) :
    ∃ k : ℕ, ∃ C : Matrix (Fin k) (Fin n) ℤ, ∃ d : Fin k → ℚ,
      rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b =
          rational_matrix_polyhedron (C.map (Int.castRingHom ℚ)) d ∧
        ∀ (c : Fin n → ℤ) (xStar : Fin n → ℝ),
          xStar ∈ rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b →
          IsGreatest
            ((fun x : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) ''
              rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b)
            ((fun j ↦ (c j : ℝ)) ⬝ᵥ xStar) →
          ∃ y : Fin k → ℝ,
            y ∈ rational_dual_feasible_region (C.map (Int.castRingHom ℚ)) c ∧
            y ∈ integerVectors k ∧
            y ⬝ᵥ (fun i ↦ (d i : ℝ)) = (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := by
  classical
  obtain ⟨t, h, hmem, hgenerate⟩ := existsHilbertBasesForAllRowSubsets A
  have hRepresent : ∀ (S : Finset (Fin m)) (j : Fin (t S)),
      ∃ coeff : Fin S.card → ℚ, (∀ l, 0 ≤ coeff l) ∧
        (fun u ↦ (h S j u : ℚ)) =
          ∑ l : Fin S.card, coeff l •
            (fun u ↦ (A (((Finset.equivFin S).symm l : S) : Fin m) u : ℚ)) := by
    intro S j
    -- Every chosen Hilbert vector lies in its row cone, so choose explicit rational coefficients.
    exact existsNonnegativeCoefficientFunctionOfMemHull
      (fun l : Fin S.card ↦
        fun u ↦ (A (((Finset.equivFin S).symm l : S) : Fin m) u : ℚ))
      (hmem S j)
  choose qCoeff hqNonneg hqRow using hRepresent
  let Row := Sum (Fin m) (Sigma fun S : Finset (Fin m) ↦ Fin (t S))
  let k : ℕ := Fintype.card Row
  let e : Fin k ≃ Row := (Fintype.equivFin Row).symm
  let C : Matrix (Fin k) (Fin n) ℤ := fun r u ↦
    match e r with
    | Sum.inl i => A i u
    | Sum.inr p => h p.1 p.2 u
  let d : Fin k → ℚ := fun r ↦
    match e r with
    | Sum.inl i => b i
    | Sum.inr p =>
        ∑ l : Fin p.1.card, qCoeff p.1 p.2 l *
          b (((Finset.equivFin p.1).symm l : p.1) : Fin m)
  have hPolyhedron :
      rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b =
        rational_matrix_polyhedron (C.map (Int.castRingHom ℚ)) d := by
    ext x
    rw [mem_rational_matrix_polyhedron, mem_rational_matrix_polyhedron]
    constructor
    · intro hx r
      generalize her : e r = row
      cases row with
      | inl i =>
          -- The original rows occur unchanged in the left summand.
          simpa [C, d, her, Matrix.mulVec, dotProduct] using hx i
      | inr p =>
          rcases p with ⟨S, j⟩
          have hvalid := nonnegativeIntegralRowCombination_valid A b
            (fun l : Fin S.card ↦ ((Finset.equivFin S).symm l : S))
            (qCoeff S j) (h S j) (hqNonneg S j) (hqRow S j) hx
          simpa [C, d, her, Matrix.mulVec, dotProduct] using hvalid
    · intro hx i
      -- Pull the original inequality back along the left-summand row embedding.
      have hi := hx (e.symm (Sum.inl i))
      simpa [C, d, Matrix.mulVec, dotProduct] using hi
  refine ⟨k, C, d, hPolyhedron, ?_⟩
  intro c xStar hxStar hopt
  obtain ⟨S, hactive, hcCone⟩ :=
    integralObjective_mem_activeRowConeOfIsGreatest A b c xStar hxStar hopt
  obtain ⟨μ, hμ⟩ := hgenerate S c hcCone
  let inj : Fin (t S) → Fin k := fun j ↦ e.symm (Sum.inr ⟨S, j⟩)
  let y : Fin k → ℝ := fun r ↦
    ∑ j : Fin (t S), if inj j = r then (μ j : ℝ) else 0
  have hyAggregate (f : Fin k → ℝ) :
      ∑ r : Fin k, y r * f r = ∑ j : Fin (t S), (μ j : ℝ) * f (inj j) := by
    -- Swap the two finite sums; each embedded Hilbert row contributes at one index only.
    calc
      ∑ r : Fin k, y r * f r =
          ∑ r : Fin k, ∑ j : Fin (t S),
            (if inj j = r then (μ j : ℝ) else 0) * f r := by
              simp_rw [y, Finset.sum_mul]
      _ = ∑ j : Fin (t S), ∑ r : Fin k,
          (if inj j = r then (μ j : ℝ) else 0) * f r := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin (t S), (μ j : ℝ) * f (inj j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp
  have hμReal : (fun u ↦ (c u : ℝ)) =
      ∑ j : Fin (t S), (μ j : ℝ) • (fun u ↦ (h S j u : ℝ)) := by
    ext u
    have huZ : c u = ∑ j : Fin (t S), (μ j : ℤ) * h S j u := by
      have hu := congrFun hμ u
      have hzeroH : ∀ j : Fin (t S), (0 : ℕ) • h S j = 0 := by
        intro j
        simp
      rw [Finsupp.sum_fintype _ _ hzeroH] at hu
      simpa [nsmul_eq_mul] using hu
    calc
      (c u : ℝ) = ((∑ j : Fin (t S), (μ j : ℤ) * h S j u : ℤ) : ℝ) := by
        exact_mod_cast huZ
      _ = ∑ j : Fin (t S), (μ j : ℝ) * (h S j u : ℝ) := by simp
      _ = (∑ j : Fin (t S), (μ j : ℝ) • (fun v ↦ (h S j v : ℝ))) u := by
        simp [Pi.smul_apply]
  have hyRow :
      y ᵥ* ((C.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) =
        (fun u ↦ (c u : ℝ)) := by
    ext u
    calc
      (y ᵥ* ((C.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ))) u =
          ∑ r : Fin k, y r * (C r u : ℝ) := by
            simp [Matrix.vecMul, dotProduct]
      _ = ∑ j : Fin (t S), (μ j : ℝ) * (C (inj j) u : ℝ) :=
        hyAggregate (fun r ↦ (C r u : ℝ))
      _ = ∑ j : Fin (t S), (μ j : ℝ) * (h S j u : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [C, inj]
      _ = (c u : ℝ) := by
            simpa [Pi.smul_apply] using (congrFun hμReal u).symm
  have hyNonneg : 0 ≤ y := by
    intro r
    refine Finset.sum_nonneg fun j hj ↦ ?_
    by_cases hjr : inj j = r
    · simp [hjr]
    · simp [hjr]
  have hyIntegral : y ∈ integerVectors k := by
    rw [mem_integerVectors_iff]
    refine ⟨fun r ↦ ∑ j : Fin (t S), if inj j = r then (μ j : ℤ) else 0, ?_⟩
    funext r
    simp [y]
  have hyFeasible :
      y ∈ rational_dual_feasible_region (C.map (Int.castRingHom ℚ)) c := by
    rw [mem_rational_dual_feasible_region_iff]
    exact ⟨hyRow, hyNonneg⟩
  have hdActive : ∀ j : Fin (t S),
      (d (inj j) : ℝ) = (fun u ↦ (h S j u : ℝ)) ⬝ᵥ xStar := by
    intro j
    have htight : ∀ l : Fin S.card,
        (((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ xStar)
            (((Finset.equivFin S).symm l : S) : Fin m) =
          (b (((Finset.equivFin S).symm l : S) : Fin m) : ℝ) := by
      intro l
      exact (hactive _).mp ((Finset.equivFin S).symm l).property
    have hvalue := integralRowCombination_value_of_tight A b
      (fun l : Fin S.card ↦ ((Finset.equivFin S).symm l : S))
      (qCoeff S j) (h S j) (hqRow S j) xStar htight
    calc
      (d (inj j) : ℝ) =
          ∑ l : Fin S.card, (qCoeff S j l : ℝ) *
            (b (((Finset.equivFin S).symm l : S) : Fin m) : ℝ) := by
              simp [d, inj]
      _ = (fun u ↦ (h S j u : ℝ)) ⬝ᵥ xStar := hvalue.symm
  have hyValue :
      y ⬝ᵥ (fun r ↦ (d r : ℝ)) = (fun u ↦ (c u : ℝ)) ⬝ᵥ xStar := by
    calc
      y ⬝ᵥ (fun r ↦ (d r : ℝ)) =
          ∑ j : Fin (t S), (μ j : ℝ) * (d (inj j) : ℝ) :=
        hyAggregate (fun r ↦ (d r : ℝ))
      _ = ∑ j : Fin (t S), (μ j : ℝ) *
          ((fun u ↦ (h S j u : ℝ)) ⬝ᵥ xStar) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hdActive j]
      _ = (∑ j : Fin (t S), (μ j : ℝ) • (fun u ↦ (h S j u : ℝ))) ⬝ᵥ xStar := by
            simp [sum_dotProduct, smul_dotProduct]
      _ = (fun u ↦ (c u : ℝ)) ⬝ᵥ xStar := by rw [hμReal]
  exact ⟨y, hyFeasible, hyIntegral, hyValue⟩

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean

Theorem 4.27 (1). Every rational polyhedron admits a totally dual integral description
`A x ≤ b` in which the coefficient matrix `A` is integral. -/
theorem rational_polyhedron_has_tdi_system_with_integral_matrix
    (hP : is_rational_polyhedron P)
    :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℚ,
      P = rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b ∧
        totally_dual_integral (A.map (Int.castRingHom ℚ)) b := by
  -- The statement now carries the rational-polyhedron premise required by the source.
  obtain ⟨m, A, b, hPresentation⟩ := existsIntegralMatrixPresentation P hP
  obtain ⟨k, C, d, hAugmentation, hCertificates⟩ :=
    existsIntegralHilbertAugmentationWithOptimalCertificates A b
  refine ⟨k, C, d, hPresentation.trans hAugmentation, ?_⟩
  rw [totally_dual_integral_iff]
  intro c hFinite
  rw [rational_primal_has_finite_optimum_iff] at hFinite
  rcases hFinite with ⟨xStar, hxStar, hOptimal⟩
  have hxOriginal :
      xStar ∈ rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b := by
    rw [hAugmentation]
    exact hxStar
  have hOptimalOriginal :
      IsGreatest
        ((fun x : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) ''
          rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b)
        ((fun j ↦ (c j : ℝ)) ⬝ᵥ xStar) := by
    simpa only [hAugmentation] using hOptimal
  obtain ⟨y, hyFeasible, hyIntegral, hyValue⟩ :=
    hCertificates c xStar hxOriginal hOptimalOriginal
  -- Equality with the attained primal value turns the certificate into a dual optimum.
  exact integralDualCertificateOfPrimalEquality
    (C.map (Int.castRingHom ℚ)) d c xStar y hxStar hyFeasible hyIntegral hyValue

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: evaluating an
integral matrix row at an integer vector gives an integer-valued real number. -/
private lemma integerMatrixRowValueIsInteger
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {x : Fin n → ℝ}
    (hx : x ∈ integerVectors n) (i : Fin m) :
    ∃ z : ℤ,
      (((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *ᵥ x) i = (z : ℝ) := by
  -- Choose integral coordinates and collect the finite row sum in `ℤ`.
  rcases mem_integerVectors_iff.mp hx with ⟨u, rfl⟩
  refine ⟨∑ j : Fin n, A i j * u j, ?_⟩
  simp [Matrix.mulVec, dotProduct, Function.comp_apply]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: every rational
matrix polyhedron is convex. -/
private lemma rationalMatrixPolyhedronConvex
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    Convex ℝ (rational_matrix_polyhedron A b) := by
  intro x hx y hy a₁ a₂ ha₁ ha₂ haSum i
  -- Each row inequality is preserved by a convex combination.
  calc
    ((A.map (Rat.castHom ℝ)) *ᵥ (a₁ • x + a₂ • y)) i =
          a₁ * ((A.map (Rat.castHom ℝ)) *ᵥ x) i +
          a₂ * ((A.map (Rat.castHom ℝ)) *ᵥ y) i := by
      simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        ∑ j, A.map (Rat.castHom ℝ) i j * (a₁ * x j + a₂ * y j) =
            ∑ j, (a₁ * (A.map (Rat.castHom ℝ) i j * x j) +
              a₂ * (A.map (Rat.castHom ℝ) i j * y j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        _ = a₁ * ∑ j, A.map (Rat.castHom ℝ) i j * x j +
            a₂ * ∑ j, A.map (Rat.castHom ℝ) i j * y j := by
          simp [Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ a₁ * (b i : ℝ) + a₂ * (b i : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hx i) ha₁)
        (mul_le_mul_of_nonneg_left (hy i) ha₂)
    _ = (b i : ℝ) := by
      rw [← add_mul, haSum, one_mul]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: an integral
polyhedron with integral coefficient matrix is unchanged after flooring its rational right-hand
side. -/
private lemma integralPolyhedronEqFloorRhs
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hIntegral : is_integral
      (rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b)) :
    rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b =
      rational_matrix_polyhedron (A.map (Int.castRingHom ℚ))
        (Int.cast ∘ fun i ↦ Int.floor (b i)) := by
  ext x
  constructor
  · intro hx
    rw [is_integral_iff] at hIntegral
    rw [hIntegral] at hx
    -- It suffices to check the floored inequalities on the integral generators.
    refine convexHull_min ?_ ?_ hx
    · rintro y ⟨hyFeasible, hyIntegral⟩
      rw [mem_rational_matrix_polyhedron]
      intro i
      obtain ⟨z, hz⟩ := integerMatrixRowValueIsInteger A hyIntegral i
      have hzRat : (z : ℚ) ≤ b i := by
        have hzReal := hyFeasible i
        rw [hz] at hzReal
        norm_num at hzReal
        exact hzReal
      have hzFloor : z ≤ Int.floor (b i) := Int.le_floor.mpr hzRat
      rw [hz]
      have hzFloorReal : (z : ℝ) ≤ (Int.floor (b i) : ℝ) := by
        exact_mod_cast hzFloor
      simpa using hzFloorReal
    · exact rationalMatrixPolyhedronConvex
        (A.map (Int.castRingHom ℚ)) (Int.cast ∘ fun i ↦ Int.floor (b i))
  · intro hx
    rw [mem_rational_matrix_polyhedron] at hx ⊢
    intro i
    have hFloorLe : (((Int.floor (b i) : ℤ) : ℚ) : ℝ) ≤ (b i : ℝ) := by
      exact (Rat.cast_le).mpr (Int.floor_le (b i))
    exact (hx i).trans hFloorLe

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: attained
primal and dual optima of a rational linear program have equal objective values. -/
private lemma rationalPrimalDualOptimalValuesEq
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : x ∈ rational_matrix_polyhedron A b)
    (hy : y ∈ rational_dual_feasible_region A c)
    (hPrimal : IsGreatest
      ((fun w : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ w) ''
        rational_matrix_polyhedron A b)
      ((fun j ↦ (c j : ℝ)) ⬝ᵥ x))
    (hDual : IsLeast
      ((fun u : Fin m → ℝ ↦ u ⬝ᵥ fun i ↦ (b i : ℝ)) ''
        rational_dual_feasible_region A c)
      (y ⬝ᵥ fun i ↦ (b i : ℝ))) :
    (fun j ↦ (c j : ℝ)) ⬝ᵥ x = y ⬝ᵥ fun i ↦ (b i : ℝ) := by
  let AR : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let bR : Fin m → ℝ := fun i ↦ (b i : ℝ)
  let cR : Fin n → ℝ := fun j ↦ (c j : ℝ)
  have hPrimalCanonical :
      IsGreatest (primal_objective_values AR bR cR) (cR ⬝ᵥ x) := by
    simpa [AR, bR, cR, primal_objective_values, primal_feasible_region,
      rational_matrix_polyhedron, polyhedron_le_set] using hPrimal
  have hDualCanonical : IsLeast (dual_objective_values AR bR cR) (y ⬝ᵥ bR) := by
    simpa [AR, bR, cR, dual_objective_values, dual_feasible_region,
      rational_dual_feasible_region] using hDual
  have hPrimalNonempty : Set.Nonempty (primal_feasible_region AR bR) := by
    have hxCanonical : x ∈ primal_feasible_region AR bR := by
      simpa [AR, bR, rational_matrix_polyhedron, primal_feasible_region] using hx
    exact ⟨x, hxCanonical⟩
  have hDualNonempty : Set.Nonempty (dual_feasible_region AR cR) := by
    have hyCanonical : y ∈ dual_feasible_region AR cR := by
      simpa [AR, cR, rational_dual_feasible_region, dual_feasible_region] using hy
    exact ⟨y, hyCanonical⟩
  have hStrongDuality :=
    linear_programming_duality_optimal_value_eq AR bR cR hPrimalNonempty hDualNonempty
  -- Strong duality identifies the supremum and infimum represented by the attained optima.
  calc
    (fun j ↦ (c j : ℝ)) ⬝ᵥ x = cR ⬝ᵥ x := rfl
    _ = sSup (primal_objective_values AR bR cR) := hPrimalCanonical.csSup_eq.symm
    _ = sInf (dual_objective_values AR bR cR) := hStrongDuality
    _ = y ⬝ᵥ bR := hDualCanonical.csInf_eq
    _ = y ⬝ᵥ fun i ↦ (b i : ℝ) := rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_6/ch4_sec4_6_theorem_4_27.lean`: if flooring the
right-hand side preserves the primal feasible set, it also preserves total dual integrality. -/
private lemma totallyDualIntegralFloorRhsOfSamePolyhedron
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hPolyhedron : rational_matrix_polyhedron A b =
      rational_matrix_polyhedron A (Int.cast ∘ fun i ↦ Int.floor (b i)))
    (hTDI : totally_dual_integral A b) :
    totally_dual_integral A (Int.cast ∘ fun i ↦ Int.floor (b i)) := by
  rw [totally_dual_integral_iff]
  intro c hFiniteFloor
  rw [rational_primal_has_finite_optimum_iff] at hFiniteFloor
  rcases hFiniteFloor with ⟨xStar, hxFloor, hOptimalFloor⟩
  have hxOriginal : xStar ∈ rational_matrix_polyhedron A b := by
    rw [hPolyhedron]
    exact hxFloor
  have hOptimalOriginal :
      IsGreatest
        ((fun x : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) ''
          rational_matrix_polyhedron A b)
        ((fun j ↦ (c j : ℝ)) ⬝ᵥ xStar) := by
    simpa only [hPolyhedron] using hOptimalFloor
  have hFiniteOriginal : rational_primal_has_finite_optimum A b c := by
    rw [rational_primal_has_finite_optimum_iff]
    exact ⟨xStar, hxOriginal, hOptimalOriginal⟩
  have hDualOriginal := hTDI c hFiniteOriginal
  rw [rational_dual_has_integral_optimal_solution_iff] at hDualOriginal
  rcases hDualOriginal with ⟨y, hyFeasible, hyIntegral, hyOptimal⟩
  have hOldValue :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar = y ⬝ᵥ fun i ↦ (b i : ℝ) :=
    rationalPrimalDualOptimalValuesEq A b c hxOriginal hyFeasible
      hOptimalOriginal hyOptimal
  have hyNonnegative : 0 ≤ y :=
    (mem_rational_dual_feasible_region_iff.mp hyFeasible).2
  have hFloorValueLeOld :
      y ⬝ᵥ (fun i ↦ ((((Int.cast ∘ fun j ↦ Int.floor (b j)) i) : ℚ) : ℝ)) ≤
        y ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
    -- Nonnegative dual multipliers preserve the coordinatewise floor inequality.
    refine Finset.sum_le_sum fun i _ ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (hyNonnegative i)
    have hFloorLe : (((Int.floor (b i) : ℤ) : ℚ) : ℝ) ≤ (b i : ℝ) := by
      exact (Rat.cast_le).mpr (Int.floor_le (b i))
    simpa using hFloorLe
  have hxFloorReal :
      xStar ∈ primal_feasible_region (A.map (Rat.castHom ℝ))
        (fun i ↦ ((((Int.cast ∘ fun j ↦ Int.floor (b j)) i) : ℚ) : ℝ)) := by
    simpa [rational_matrix_polyhedron, primal_feasible_region] using hxFloor
  have hyReal :
      y ∈ dual_feasible_region (A.map (Rat.castHom ℝ)) (fun j ↦ (c j : ℝ)) := by
    simpa [rational_dual_feasible_region, dual_feasible_region] using hyFeasible
  have hWeakFloor :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar ≤
        y ⬝ᵥ (fun i ↦ ((((Int.cast ∘ fun j ↦ Int.floor (b j)) i) : ℚ) : ℝ)) :=
    weak_duality_feasible_pair (A.map (Rat.castHom ℝ))
      (fun i ↦ ((((Int.cast ∘ fun j ↦ Int.floor (b j)) i) : ℚ) : ℝ))
      (fun j ↦ (c j : ℝ)) hxFloorReal hyReal
  have hFloorValue :
      y ⬝ᵥ (fun i ↦ ((((Int.cast ∘ fun j ↦ Int.floor (b j)) i) : ℚ) : ℝ)) =
        (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := by
    exact le_antisymm (hFloorValueLeOld.trans_eq hOldValue.symm) hWeakFloor
  -- The same integral dual point is optimal for the floored system.
  exact integralDualCertificateOfPrimalEquality A
    (Int.cast ∘ fun i ↦ Int.floor (b i)) c xStar y hxFloor hyFeasible hyIntegral hFloorValue

/-- Theorem 4.27 (2). If a rational polyhedron is integral, then it admits a totally dual
integral description `A x ≤ b` in which both `A` and `b` are integral. -/
theorem integral_rational_polyhedron_has_tdi_system_with_integral_rhs
    (hP : is_rational_polyhedron P)
    (hPi : is_integral P) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℤ,
      P = rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) (Int.cast ∘ b) ∧
        totally_dual_integral (A.map (Int.castRingHom ℚ)) (Int.cast ∘ b) := by
  -- The statement now carries the rational-polyhedron premise required by the source.
  obtain ⟨m, A, b, hPresentation, hTDI⟩ :=
    rational_polyhedron_has_tdi_system_with_integral_matrix P hP
  let bFloor : Fin m → ℤ := fun i ↦ Int.floor (b i)
  have hPresentedIntegral :
      is_integral (rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b) := by
    rw [← hPresentation]
    exact hPi
  have hFloorEquality := integralPolyhedronEqFloorRhs A b hPresentedIntegral
  refine ⟨m, A, bFloor, ?_, ?_⟩
  · -- Compose the original presentation with equality after flooring.
    have hFloorEquality' :
        rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b =
          rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) (Int.cast ∘ bFloor) := by
      simpa [bFloor] using hFloorEquality
    exact hPresentation.trans hFloorEquality'
  · -- Transfer the TDI certificate across the unchanged feasible set.
    simpa [bFloor] using
      (totallyDualIntegralFloorRhsOfSamePolyhedron
        (A.map (Int.castRingHom ℚ)) b hFloorEquality hTDI)

end Theorem427

#print axioms rational_polyhedron_has_tdi_system_with_integral_matrix
#print axioms integral_rational_polyhedron_has_tdi_system_with_integral_rhs
