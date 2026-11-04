/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_11.ch4_sec4_11_theorem_4_60
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

section Exercise423

variable {m n : ℕ}

namespace Exercise423Aux

variable {ι : Type*}

/-- Helper for Exercise 4.23: a rational family is a Hilbert basis when every integral point of
its rational cone is a nonnegative integral combination of the family vectors. -/
def IsHilbertBasis (a : ι → Fin n → ℚ) : Prop :=
  ∀ z : Fin n → ℤ,
    (fun i ↦ (z i : ℚ)) ∈ (PointedCone.hull ℚ (Set.range a) : Set (Fin n → ℚ)) →
      ∃ u : ι →₀ ℕ,
        (fun i ↦ (z i : ℚ)) = u.sum (fun i c ↦ c • a i)

/-- Helper for Exercise 4.23: the row indices active on a face `F` of the rational system
`A x ≤ b`. -/
def activeRowIndices
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (F : Set (Fin n → ℝ)) : Set (Fin m) :=
  {i | ∀ ⦃x : Fin n → ℝ⦄, x ∈ F → ((A.map (Rat.castHom ℝ)) *ᵥ x) i = (b i : ℝ)}

/-- Helper for Exercise 4.23: the active rows of `A x ≤ b` along `F`, viewed as a rational family
indexed by the active constraints. -/
def activeRows
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (F : Set (Fin n → ℝ)) :
    activeRowIndices A b F → Fin n → ℚ :=
  fun i ↦ A i.1

/-- Helper for Exercise 4.23: the Hilbert-basis criterion from Theorem 4.60 turns facewise
Hilbert bases into total dual integrality for the same system. -/
theorem totally_dual_integral_of_active_rows_form_hilbert_basis_on_each_face
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hfaces :
      ∀ (F : Set (Fin n → ℝ))
        (_hF_nonempty : F.Nonempty)
        (_hF_extreme : IsExtreme ℝ (rational_matrix_polyhedron A b) F),
          IsHilbertBasis (activeRows A b F)) :
    totally_dual_integral A b := by
  -- Reuse the Chapter 4.11 criterion verbatim after identifying the local helper owners with the
  -- upstream Hilbert-basis and active-row owners.
  simpa [IsHilbertBasis, activeRows, activeRowIndices, RationalFamily.IsHilbertBasis,
    RationalMatrixPolyhedron.activeRows, RationalMatrixPolyhedron.activeRowIndices] using
    (_root_.totally_dual_integral_of_active_rows_form_hilbert_basis_on_each_face A b hfaces)

end Exercise423Aux

/-- Helper for Exercise 4.23: after casting to `ℝ`, evaluating the uniformly scaled matrix on a
vector `x` multiplies the original row value by `k⁻¹`. -/
lemma pnat_inv_smul_mulVec_apply
    (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℝ) (k : ℕ+) (i : Fin m) :
    ((((k : ℚ)⁻¹ • A).map (Rat.castHom ℝ) *ᵥ x) i) =
      (((k : ℚ)⁻¹ : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i)) := by
  -- Cast the scaled matrix entrywise to `ℝ`, then pull the common scalar through `mulVec`.
  rw [show (((k : ℚ)⁻¹ • A).map (Rat.castHom ℝ)) =
      (((k : ℚ)⁻¹ : ℝ) • A.map (Rat.castHom ℝ)) by
        ext r c
        simp [Matrix.map_apply]]
  simp [Matrix.smul_mulVec, Pi.smul_apply]

/-- Helper for Exercise 4.23: after casting to `ℝ`, the uniformly scaled right-hand side equals
the original right-hand side multiplied by `k⁻¹`. -/
lemma pnat_inv_smul_rhs_apply
    (b : Fin m → ℚ) (k : ℕ+) (i : Fin m) :
    ((((k : ℚ)⁻¹) • b) i : ℝ) = (((k : ℚ)⁻¹ : ℝ) * (b i : ℝ)) := by
  -- The right-hand side is a pointwise scalar multiple, so evaluation exposes the same factor.
  simp [Pi.smul_apply]

/-- Helper for Exercise 4.23: scaling every inequality by the same positive rational leaves the
feasible polyhedron unchanged. -/
lemma rational_matrix_polyhedron_pnat_inv_smul_eq
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (k : ℕ+) :
    rational_matrix_polyhedron (((k : ℚ)⁻¹) • A) (((k : ℚ)⁻¹) • b) =
      rational_matrix_polyhedron A b := by
  ext x
  rw [mem_rational_matrix_polyhedron, mem_rational_matrix_polyhedron]
  constructor
  · intro hx i
    -- Rewrite the scaled inequality and cancel the common positive scalar.
    have hxi := hx i
    rw [pnat_inv_smul_mulVec_apply] at hxi
    have hxi' :
        (((k : ℚ)⁻¹ : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i)) ≤
          (((k : ℚ)⁻¹ : ℝ) * (b i : ℝ)) := by
      simpa [Pi.smul_apply] using hxi
    have hk_pos : 0 < (((k : ℚ)⁻¹ : ℝ)) := by positivity
    nlinarith
  · intro hx i
    -- The converse direction multiplies both sides by the same positive factor.
    have hxi := hx i
    have hk_pos : 0 < (((k : ℚ)⁻¹ : ℝ)) := by positivity
    have hxi' :
        (((k : ℚ)⁻¹ : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i)) ≤
          (((k : ℚ)⁻¹ : ℝ) * (b i : ℝ)) :=
      by nlinarith
    rw [pnat_inv_smul_mulVec_apply]
    simpa [Pi.smul_apply] using hxi'

/-- Helper for Exercise 4.23: the active row set on a fixed face is unchanged by uniform positive
scaling of the whole system. -/
lemma active_row_indices_pnat_inv_smul_eq
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (F : Set (Fin n → ℝ)) (k : ℕ+) :
    Exercise423Aux.activeRowIndices (((k : ℚ)⁻¹) • A) (((k : ℚ)⁻¹) • b) F =
      Exercise423Aux.activeRowIndices A b F := by
  ext i
  rw [Exercise423Aux.activeRowIndices, Exercise423Aux.activeRowIndices]
  constructor
  · intro hi x hxF
    -- Rewrite the scaled active-row equality and cancel the common positive factor.
    have hix := hi hxF
    rw [pnat_inv_smul_mulVec_apply, pnat_inv_smul_rhs_apply] at hix
    have hk_ne : (((k : ℚ)⁻¹ : ℝ)) ≠ 0 := by positivity
    exact mul_left_cancel₀ hk_ne hix
  · intro hi x hxF
    -- The same normalization works in the reverse direction.
    have hix := hi hxF
    rw [pnat_inv_smul_mulVec_apply, pnat_inv_smul_rhs_apply]
    have hk_ne : (((k : ℚ)⁻¹ : ℝ)) ≠ 0 := by positivity
    simpa [hix] using congrArg (fun t : ℝ ↦ (((k : ℚ)⁻¹ : ℝ) * t)) hix

/-- Helper for Exercise 4.23: once a rational family is a Hilbert basis, any further uniform
positive integer down-scaling is still a Hilbert basis. -/
lemma isHilbertBasis_of_pnat_inv_smul
    {ι : Type*}
    {a : ι → Fin n → ℚ}
    (k : ℕ+)
    (ha : Exercise423Aux.IsHilbertBasis a) :
    Exercise423Aux.IsHilbertBasis (fun i ↦ ((k : ℚ)⁻¹) • a i) := by
  intro z hz
  classical
  rcases (mem_hull_iff.mp hz) with ⟨s, r, hr_mem, coeff, hcoeff_nonneg, hz_eq⟩
  let idx : Fin s → ι := fun j ↦ Classical.choose (hr_mem j)
  have hidx : ∀ j : Fin s, r j = ((k : ℚ)⁻¹) • a (idx j) := by
    intro j
    exact (Classical.choose_spec (hr_mem j)).symm
  have hz_mem_unscaled_selected :
      (fun i ↦ (z i : ℚ)) ∈
        (PointedCone.hull ℚ (Set.range fun j : Fin s ↦ a (idx j)) : Set (Fin n → ℚ)) := by
    -- Repackage the scaled conic witness as a conic witness for the unscaled selected family.
    refine mem_hull_of_equivFin_nonnegative_family
      (fun j : Fin s ↦ a (idx j))
      (fun j ↦ coeff j * (k : ℚ)⁻¹)
      (fun i ↦ (z i : ℚ))
      (fun j ↦ mul_nonneg (hcoeff_nonneg j) (by positivity)) ?_
    ext t
    calc
      (fun i ↦ (z i : ℚ)) t = (∑ j : Fin s, coeff j • r j) t := by
        simpa using congrFun hz_eq t
      _ = ∑ j : Fin s, coeff j * r j t := by
            simp [Pi.smul_apply]
      _ = ∑ j : Fin s, coeff j * ((((k : ℚ)⁻¹) • a (idx j)) t) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hidx j]
      _ = ∑ j : Fin s, (coeff j * (k : ℚ)⁻¹) * a (idx j) t := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ j : Fin s, (coeff j * (k : ℚ)⁻¹) • a (idx j)) t := by
            simp [Pi.smul_apply]
  have hz_mem_unscaled :
      (fun i ↦ (z i : ℚ)) ∈ (PointedCone.hull ℚ (Set.range a) : Set (Fin n → ℚ)) := by
    -- Enlarge from the selected subfamily back to the original family.
    refine
      (show
        (PointedCone.hull ℚ (Set.range fun j : Fin s ↦ a (idx j)) : Set (Fin n → ℚ)) ⊆
          (PointedCone.hull ℚ (Set.range a) : Set (Fin n → ℚ)) from ?_) hz_mem_unscaled_selected
    exact Submodule.span_mono <| by
      intro y hy
      rcases hy with ⟨j, rfl⟩
      exact ⟨idx j, rfl⟩
  rcases ha z hz_mem_unscaled with ⟨u, hu_eq⟩
  refine ⟨(k : ℕ) • u, ?_⟩
  have hscaled_eq :
      u.sum (fun i c ↦ c • a i) =
        ((k : ℕ) • u).sum (fun i c ↦ c • (((k : ℚ)⁻¹) • a i)) := by
    have hsum_scaled :
        ((k : ℕ) • u).sum (fun i c ↦ c • (((k : ℚ)⁻¹) • a i)) =
          u.sum (fun i c ↦ (k * c) • (((k : ℚ)⁻¹) • a i)) := by
      -- Push the scalar multiplication on the `ℕ`-valued witness inside the `Finsupp.sum`.
      refine Finsupp.sum_smul_index ?_
      intro i
      simp
    calc
      u.sum (fun i c ↦ c • a i)
          = u.sum (fun i c ↦ (k * c) • (((k : ℚ)⁻¹) • a i)) := by
              refine Finsupp.sum_congr ?_
              intro i hi
              ext t
              simp [nsmul_eq_mul, Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
      _ = ((k : ℕ) • u).sum (fun i c ↦ c • (((k : ℚ)⁻¹) • a i)) := hsum_scaled.symm
  exact hu_eq.trans hscaled_eq

/-- Helper for Exercise 4.23: divisibility of positive integer scalings transports the
Hilbert-basis property from a coarser scaling to any finer scaling. -/
lemma isHilbertBasis_ofScalingDvd
    {ι : Type*}
    {r : ι → Fin n → ℚ}
    {k₁ k₂ : ℕ+}
    (hdiv : (k₁ : ℕ) ∣ (k₂ : ℕ))
    (hk₁ : Exercise423Aux.IsHilbertBasis (fun i ↦ ((k₁ : ℚ)⁻¹) • r i)) :
    Exercise423Aux.IsHilbertBasis (fun i ↦ ((k₂ : ℚ)⁻¹) • r i) := by
  rcases hdiv with ⟨d, hd⟩
  have hd_pos : 0 < d := by
    have hk₂_pos : 0 < (k₂ : ℕ) := k₂.pos
    by_contra hd_zero
    simp [hd_zero, hd] at hk₂_pos
  let d' : ℕ+ := ⟨d, hd_pos⟩
  have hscaled :
      Exercise423Aux.IsHilbertBasis
        (fun i ↦ ((d' : ℚ)⁻¹) • (((k₁ : ℚ)⁻¹) • r i)) :=
    isHilbertBasis_of_pnat_inv_smul d' hk₁
  -- Rewrite the two-step scaling as the single scaling by `k₂ = k₁ * d`.
  simpa [d', hd, smul_smul, mul_comm, mul_left_comm, mul_assoc, ← mul_inv_rev] using hscaled

/-- Helper for Exercise 4.23: the common denominator of a finite rational coefficient vector is
strictly positive. -/
lemma rationalVectorCommonDenominator_ne_zero
    {q : ℕ}
    (v : Fin q → ℚ) :
    rational_vector_common_denominator v ≠ 0 := by
  -- Every coordinate denominator is positive, so their finite least common multiple is nonzero.
  simpa [rational_vector_common_denominator] using
    (Finset.lcm_ne_zero_iff.2 fun i ↦ Nat.ne_of_gt (Rat.den_pos (v i)))

/-- Helper for Exercise 4.23: cone membership over a finite rational family can be rewritten with
nonnegative coefficients on the original index type itself. -/
lemma existsNonnegativeCoefficientFunctionOfMemHull
    {ι : Type*}
    [Fintype ι]
    (r : ι → Fin n → ℚ)
    {v : Fin n → ℚ}
    (hv : v ∈ (PointedCone.hull ℚ (Set.range r) : Set (Fin n → ℚ))) :
    ∃ coeff : ι → ℚ,
      (∀ i, 0 ≤ coeff i) ∧
        v = ∑ i, coeff i • r i := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  rcases (mem_hull_iff.mp hv) with ⟨s, r', hr_mem, coeff, hcoeff_nonneg, hv_eq⟩
  let idx : Fin s → ι := fun k ↦ Classical.choose (hr_mem k)
  have hidx : ∀ k : Fin s, r (idx k) = r' k := by
    intro k
    exact Classical.choose_spec (hr_mem k)
  let coeff' : ι → ℚ := fun i ↦ ∑ k : Fin s, if idx k = i then coeff k else 0
  refine ⟨coeff', ?_, ?_⟩
  · -- Each aggregated coefficient is a finite sum of nonnegative terms.
    intro i
    exact Finset.sum_nonneg fun k _ ↦ by
      by_cases hk : idx k = i
      · simp [coeff', hk, hcoeff_nonneg k]
      · simp [coeff', hk]
  · -- Collapse the selected-support witness back onto the original index type.
    ext j
    symm
    calc
      (∑ i : ι, coeff' i • r i) j
          = ∑ i : ι, coeff' i * r i j := by
              simp [Pi.smul_apply]
      _ = ∑ i : ι, (∑ k : Fin s, if idx k = i then coeff k else 0) * r i j := by
            simp [coeff']
      _ = ∑ i : ι, ∑ k : Fin s, (if idx k = i then coeff k else 0) * r i j := by
            simp_rw [Finset.sum_mul]
      _ = ∑ k : Fin s, ∑ i : ι, (if idx k = i then coeff k else 0) * r i j := by
            rw [Finset.sum_comm]
      _ = ∑ k : Fin s, coeff k * r' k j := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simpa [hidx k] using
              (by
                simp :
                  (∑ i : ι, (if idx k = i then coeff k else 0) * r i j) =
                    coeff k * r (idx k) j)
      _ = (∑ k : Fin s, coeff k • r' k) j := by
            simp [Pi.smul_apply]
      _ = v j := by
            simpa using (congrFun hv_eq j).symm

/-- Helper for Exercise 4.23: one integral cone point becomes an integral combination after
clearing the denominators of a finite conic witness. -/
lemma existsScaledCombinationOfIntegralConePoint
    {ι : Type*}
    [Fintype ι]
    (r : ι → Fin n → ℚ)
    (z : Fin n → ℤ)
    (hz : (fun i ↦ (z i : ℚ)) ∈ (PointedCone.hull ℚ (Set.range r) : Set (Fin n → ℚ))) :
    ∃ k : ℕ+, ∃ u : ι →₀ ℕ,
      (fun i ↦ (z i : ℚ)) =
        u.sum (fun i c ↦ c • (((k : ℚ)⁻¹) • r i)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  rcases existsNonnegativeCoefficientFunctionOfMemHull r hz with ⟨coeff, hcoeff_nonneg, hz_eq⟩
  let coeffFin : Fin (Fintype.card ι) → ℚ := fun j ↦ coeff (e.symm j)
  let d : ℕ := rational_vector_common_denominator coeffFin
  have hd_ne_zero : d ≠ 0 := rationalVectorCommonDenominator_ne_zero coeffFin
  let k : ℕ+ := ⟨d, Nat.pos_of_ne_zero hd_ne_zero⟩
  let uInt : ι → ℤ := fun i ↦ common_denominator_scaled_vector coeffFin (e i)
  have huInt_nonneg : ∀ i : ι, 0 ≤ uInt i := by
    intro i
    -- The cleared coefficient is a positive multiple of the original nonnegative coefficient.
    have hcoord :=
      congrFun (common_denominator_scaled_vector_eq_smul coeffFin) (e i)
    have hcoord_nonneg_q : 0 ≤ (uInt i : ℚ) := by
      rw [show (uInt i : ℚ) = (((k : ℕ) : ℚ) * coeff i) by
            simpa [uInt, coeffFin, k, d, Pi.smul_apply] using hcoord]
      exact mul_nonneg (by positivity) (hcoeff_nonneg i)
    exact_mod_cast hcoord_nonneg_q
  let uFun : ι → ℕ := fun i ↦ Int.toNat (uInt i)
  let u : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm uFun
  have hu_cast : ∀ i : ι, ((u i : ℕ) : ℚ) = (k : ℚ) * coeff i := by
    intro i
    have hcoord :=
      congrFun (common_denominator_scaled_vector_eq_smul coeffFin) (e i)
    calc
      ((u i : ℕ) : ℚ) = (Int.toNat (uInt i) : ℚ) := by
            simp [u, uFun]
      _ = (uInt i : ℚ) := by
            exact_mod_cast (Int.toNat_of_nonneg (huInt_nonneg i))
      _ = (k : ℚ) * coeff i := by
            simpa [uInt, coeffFin, k, d, Pi.smul_apply] using hcoord
  have hk_ne : (k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt k.pos)
  have hcoeff_scaled : ∀ i : ι, coeff i = ((u i : ℕ) : ℚ) * ((k : ℚ)⁻¹) := by
    intro i
    calc
      coeff i = (k : ℚ)⁻¹ * ((k : ℚ) * coeff i) := by
            field_simp [hk_ne]
      _ = ((u i : ℕ) : ℚ) * ((k : ℚ)⁻¹) := by
            rw [hu_cast i]
            ring
  refine ⟨k, u, ?_⟩
  -- Rewrite the cleared integer coefficients as a `Finsupp` witness over one scaled family.
  ext t
  calc
    (fun i ↦ (z i : ℚ)) t = (∑ i : ι, coeff i • r i) t := by
      simpa using congrFun hz_eq t
    _ = ∑ i : ι, coeff i * r i t := by
          simp [Pi.smul_apply]
    _ = ∑ i : ι, (((u i : ℕ) : ℚ) * ((k : ℚ)⁻¹)) * r i t := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hcoeff_scaled i]
    _ = ∑ i : ι, (((u i : ℕ) • (((k : ℚ)⁻¹) • r i)) : Fin n → ℚ) t := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [nsmul_eq_mul, Pi.smul_apply, mul_assoc, mul_comm]
    _ = (u.sum (fun i c ↦ c • (((k : ℚ)⁻¹) • r i))) t := by
          symm
          rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp), Finset.sum_apply]

/-- Helper for Exercise 4.23: a witness over one positive scaling lifts to any finer scaling
whose denominator is a multiple of the first one. -/
lemma scaledCombination_ofScalingDvd
    {ι : Type*}
    {r : ι → Fin n → ℚ}
    {z : Fin n → ℚ}
    {k₁ k₂ : ℕ+}
    (hdiv : (k₁ : ℕ) ∣ (k₂ : ℕ))
    {u : ι →₀ ℕ}
    (hu :
      z = u.sum (fun i c ↦ c • (((k₁ : ℚ)⁻¹) • r i))) :
    ∃ u' : ι →₀ ℕ,
      z = u'.sum (fun i c ↦ c • (((k₂ : ℚ)⁻¹) • r i)) := by
  rcases hdiv with ⟨d, hd⟩
  have hd_pos : 0 < d := by
    have hk₂_pos : 0 < (k₂ : ℕ) := k₂.pos
    by_contra hd_zero
    simp [hd_zero, hd] at hk₂_pos
  let d' : ℕ+ := ⟨d, hd_pos⟩
  refine ⟨(d : ℕ) • u, ?_⟩
  have hscaled_eq :
      u.sum (fun i c ↦ c • (((k₁ : ℚ)⁻¹) • r i)) =
        ((d : ℕ) • u).sum
          (fun i c ↦ c • (((d' : ℚ)⁻¹) • (((k₁ : ℚ)⁻¹) • r i))) := by
    have hsum_scaled :
        ((d : ℕ) • u).sum (fun i c ↦ c • (((d' : ℚ)⁻¹) • (((k₁ : ℚ)⁻¹) • r i))) =
          u.sum (fun i c ↦ (d * c) • (((d' : ℚ)⁻¹) • (((k₁ : ℚ)⁻¹) • r i))) := by
      -- Push the witness scaling inside the finite sum once.
      refine Finsupp.sum_smul_index ?_
      intro i
      simp
    calc
      u.sum (fun i c ↦ c • (((k₁ : ℚ)⁻¹) • r i))
          = u.sum (fun i c ↦ (d * c) • (((d' : ℚ)⁻¹) • (((k₁ : ℚ)⁻¹) • r i))) := by
              refine Finsupp.sum_congr ?_
              intro i hi
              ext t
              have hd'_ne : (d' : ℚ) ≠ 0 := by
                exact_mod_cast (Nat.ne_of_gt hd_pos)
              have hscalar :
                  ((u i : ℕ) : ℚ) = (((d * u i : ℕ) : ℚ) * ((d' : ℚ)⁻¹)) := by
                rw [show (d' : ℚ) = (d : ℚ) by rfl, Nat.cast_mul]
                field_simp [hd'_ne]
              calc
                (((u i : ℕ) • (((k₁ : ℚ)⁻¹) • r i)) : Fin n → ℚ) t
                    = (((u i : ℕ) : ℚ) * (((k₁ : ℚ)⁻¹) * r i t)) := by
                        simp [nsmul_eq_mul, Pi.smul_apply]
                _ = ((((d * u i : ℕ) : ℚ) * ((d' : ℚ)⁻¹)) * (((k₁ : ℚ)⁻¹) * r i t)) := by
                        rw [hscalar]
                _ = (((d * u i : ℕ) • (((d' : ℚ)⁻¹) • (((k₁ : ℚ)⁻¹) • r i))) : Fin n → ℚ) t := by
                        simp [nsmul_eq_mul, Pi.smul_apply, mul_assoc]
      _ = ((d : ℕ) • u).sum
            (fun i c ↦ c • (((d' : ℚ)⁻¹) • (((k₁ : ℚ)⁻¹) • r i))) := hsum_scaled.symm
  -- Rewrite the two-step scaling as the single target scaling `k₂`.
  simpa [d', hd, smul_smul, mul_comm, mul_left_comm, mul_assoc, ← mul_inv_rev] using
    hu.trans hscaled_eq

/-- Helper for Exercise 4.23: finitely many integral cone witnesses admit one common positive
integer scaling that turns all of them into integral combinations of the down-scaled family. -/
lemma existsCommonScalingForFiniteConeWitnessFamily
    {ι : Type*}
    [Fintype ι]
    {t : ℕ}
    (r : ι → Fin n → ℚ)
    (s : Fin t → Fin n → ℤ)
    (hs :
      ∀ j : Fin t,
        (fun i ↦ (s j i : ℚ)) ∈ (PointedCone.hull ℚ (Set.range r) : Set (Fin n → ℚ))) :
    ∃ k : ℕ+,
      ∀ j : Fin t, ∃ u : ι →₀ ℕ,
        (fun i ↦ (s j i : ℚ)) =
          u.sum (fun i c ↦ c • (((k : ℚ)⁻¹) • r i)) := by
  classical
  have hwitness :
      ∀ j : Fin t, ∃ k : ℕ+, ∃ u : ι →₀ ℕ,
        (fun i ↦ (s j i : ℚ)) =
          u.sum (fun i c ↦ c • (((k : ℚ)⁻¹) • r i)) := by
    intro j
    -- Clear denominators separately for each residue witness first.
    exact existsScaledCombinationOfIntegralConePoint r (s j) (hs j)
  let kWitness : Fin t → ℕ+ := fun j ↦ Classical.choose (hwitness j)
  let k : ℕ+ := ⟨∏ j : Fin t, (kWitness j : ℕ), by
    exact Finset.prod_pos fun j _ ↦ (kWitness j).pos⟩
  refine ⟨k, ?_⟩
  intro j
  have hu_j :
      (fun i ↦ (s j i : ℚ)) =
        (Classical.choose (Classical.choose_spec (hwitness j))).sum
          (fun i c ↦ c • (((kWitness j : ℚ)⁻¹) • r i)) := by
    exact Classical.choose_spec (Classical.choose_spec (hwitness j))
  have hdiv : (kWitness j : ℕ) ∣ (k : ℕ) := by
    dsimp [k]
    exact Finset.dvd_prod_of_mem (fun l : Fin t ↦ (kWitness l : ℕ)) (by simp)
  -- Upgrade the witness from its individual denominator to the common product denominator.
  exact scaledCombination_ofScalingDvd (r := r) (z := fun i ↦ (s j i : ℚ)) hdiv hu_j

/-- Helper for Exercise 4.23: splitting a rational cone witness into floors and fractional parts
produces an integral remainder whose rational realization has coefficients in `[0,1)`. -/
lemma existsHalfOpenBoxRemainderOfIntegralConePoint
    {q : ℕ}
    (a : Fin q → Fin n → ℤ)
    {z : Fin n → ℤ}
    (hz :
      (fun t ↦ (z t : ℚ)) ∈
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
    existsNonnegativeCoefficientFunctionOfMemHull (fun j : Fin q ↦ fun t ↦ (a j t : ℚ)) hz
  let μNat : Fin q → ℕ := fun j ↦ Int.toNat (Int.floor (coeff j))
  let μ₀ : Fin q →₀ ℕ := Finsupp.equivFunOnFinite.symm μNat
  have hμCast : ∀ j : Fin q, ((μ₀ j : ℕ) : ℚ) = (Int.floor (coeff j) : ℚ) := by
    intro j
    have hfloor_nonneg : 0 ≤ Int.floor (coeff j) := Int.floor_nonneg.mpr (hcoeff_nonneg j)
    calc
      ((μ₀ j : ℕ) : ℚ) = (Int.toNat (Int.floor (coeff j)) : ℚ) := by
            simp [μ₀, μNat]
      _ = (Int.floor (coeff j) : ℚ) := by
            exact_mod_cast (Int.toNat_of_nonneg hfloor_nonneg)
  have hμ₀Q_eq :
      (fun t ↦ ((μ₀.sum (fun j c ↦ c • a j)) t : ℚ)) =
        ∑ j : Fin q, (Int.floor (coeff j) : ℚ) • (fun t ↦ (a j t : ℚ)) := by
    ext t
    calc
      ((μ₀.sum (fun j c ↦ c • a j)) t : ℚ)
          = ∑ j : Fin q, ((μ₀ j : ℕ) : ℚ) * (a j t : ℚ) := by
              rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp), Finset.sum_apply]
              simp [nsmul_eq_mul]
      _ = ∑ j : Fin q, (Int.floor (coeff j) : ℚ) * (a j t : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hμCast j]
      _ = (∑ j : Fin q, (Int.floor (coeff j) : ℚ) • (fun s ↦ (a j s : ℚ))) t := by
            simp [Pi.smul_apply]
  let ρ : Fin n → ℤ := z - μ₀.sum (fun j c ↦ c • a j)
  refine ⟨coeff, μ₀, ρ, hcoeff_nonneg, ?_, ?_, ?_, ?_⟩
  · -- The remainder is exactly what is left after removing the floor witness.
    ext t
    simp [ρ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  · -- The rational remainder is represented by the fractional parts of the cone coefficients.
    ext t
    calc
      (ρ t : ℚ) = (z t : ℚ) - ((μ₀.sum (fun j c ↦ c • a j)) t : ℚ) := by
        simp [ρ]
      _ = (∑ j : Fin q, coeff j * (a j t : ℚ)) -
            ∑ j : Fin q, (Int.floor (coeff j) : ℚ) * (a j t : ℚ) := by
              rw [congrFun hz_eq t, congrFun hμ₀Q_eq t]
              simp [Pi.smul_apply]
      _ = ∑ j : Fin q,
            (coeff j - (Int.floor (coeff j) : ℚ)) * (a j t : ℚ) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ j : Fin q, Int.fract (coeff j) * (a j t : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hdecomp :
                coeff j - (Int.floor (coeff j) : ℚ) = Int.fract (coeff j) := by
              linarith [Int.floor_add_fract (coeff j)]
            simp [hdecomp]
      _ = (∑ j : Fin q, Int.fract (coeff j) • (fun s ↦ (a j s : ℚ))) t := by
            simp [Pi.smul_apply]
  · -- Fractional parts are nonnegative.
    intro j
    exact Int.fract_nonneg (coeff j)
  · -- Fractional parts stay strictly below `1`.
    intro j
    exact Int.fract_lt_one (coeff j)

/-- Helper for Exercise 4.23: a `[0,1]`-weighted integral combination stays between the sums of
the negative and positive coordinate parts. -/
lemma weightedIntegralCombination_mem_coordinateBox
    {q : ℕ}
    (a : Fin q → ℤ)
    (coeff : Fin q → ℚ)
    (hcoeff_nonneg : ∀ j : Fin q, 0 ≤ coeff j)
    (hcoeff_le_one : ∀ j : Fin q, coeff j ≤ 1) :
    (∑ j : Fin q, coeff j * (a j : ℚ)) ∈
      Set.Icc
        (∑ j : Fin q, ((min (a j) 0 : ℤ) : ℚ))
        (∑ j : Fin q, ((max (a j) 0 : ℤ) : ℚ)) := by
  constructor
  · -- Bound each summand below by its negative part, then sum the inequalities.
    refine Finset.sum_le_sum fun j _ ↦ by
      by_cases haj : a j ≤ 0
      · have hajQ : (a j : ℚ) ≤ 0 := by
          exact_mod_cast haj
        have hmul : (a j : ℚ) ≤ coeff j * (a j : ℚ) := by
          nlinarith [hcoeff_le_one j, hajQ]
        simpa [min_eq_left haj] using hmul
      · have h0aj : 0 ≤ a j := le_of_lt (lt_of_not_ge haj)
        have h0ajQ : (0 : ℚ) ≤ (a j : ℚ) := by
          exact_mod_cast h0aj
        have hmul : (0 : ℚ) ≤ coeff j * (a j : ℚ) :=
          mul_nonneg (hcoeff_nonneg j) h0ajQ
        simpa [min_eq_right h0aj] using hmul
  · -- Bound each summand above by its positive part, then sum the inequalities.
    refine Finset.sum_le_sum fun j _ ↦ by
      by_cases haj : 0 ≤ a j
      · have hajQ : (0 : ℚ) ≤ (a j : ℚ) := by
          exact_mod_cast haj
        have hmul : coeff j * (a j : ℚ) ≤ (a j : ℚ) := by
          nlinarith [hcoeff_nonneg j, hcoeff_le_one j, hajQ]
        simpa [max_eq_left haj] using hmul
      · have haj' : a j ≤ 0 := le_of_lt (lt_of_not_ge haj)
        have hajQ : (a j : ℚ) ≤ 0 := by
          exact_mod_cast haj'
        have hmul : coeff j * (a j : ℚ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (hcoeff_nonneg j) hajQ
        simpa [max_eq_right haj'] using hmul

/-- Helper for Exercise 4.23: the integer points in a coordinate box form a finite family. -/
lemma existsFiniteIntegralPointsOfCoordinateBox
    (lower upper : Fin n → ℤ) :
    ∃ t : ℕ, ∃ s : Fin t → Fin n → ℤ,
      (∀ j i, s j i ∈ Set.Icc (lower i) (upper i)) ∧
        ∀ ρ : Fin n → ℤ,
          (∀ i, ρ i ∈ Set.Icc (lower i) (upper i)) →
            ∃ j : Fin t, s j = ρ := by
  classical
  let box : Set (Fin n → ℤ) := {ρ | ∀ i, ρ i ∈ Set.Icc (lower i) (upper i)}
  have hboxFinite : box.Finite := by
    -- Finite products of finite coordinate intervals are finite.
    simpa [box, Set.pi] using
      (Set.Finite.pi' (t := fun i : Fin n ↦ Set.Icc (lower i) (upper i))
        fun i ↦ Set.finite_Icc (lower i) (upper i))
  obtain ⟨t, s, hs_inj, hs_range⟩ := hboxFinite.fin_param
  refine ⟨t, s, ?_, ?_⟩
  · -- Every enumerated vector belongs to the prescribed coordinate box.
    intro j i
    have hs_mem : s j ∈ box := by
      rw [← hs_range]
      exact ⟨j, rfl⟩
    exact hs_mem i
  · -- Every boxed vector appears somewhere in the finite parametrization.
    intro ρ hρ
    have hρ_mem : ρ ∈ box := hρ
    rw [← hs_range] at hρ_mem
    exact hρ_mem

/-- Helper for Exercise 4.23: a finite integral family admits finitely many bounded integral
remainders that cover every integral point of its cone after removing a nonnegative integral part.
-/
lemma existsFiniteIntegralRemainderFamilyOfIntegralCone
    {q : ℕ}
    (a : Fin q → Fin n → ℤ) :
    ∃ t : ℕ, ∃ s : Fin t → Fin n → ℤ,
      (∀ j : Fin t,
        (fun i ↦ (s j i : ℚ)) ∈
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
    {j |
      (fun i ↦ (sBox j i : ℚ)) ∈
        (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
          Set (Fin n → ℚ))}
  obtain ⟨t, e, he_inj, he_range⟩ := (Set.toFinite remainderIndex).fin_param
  let s : Fin t → Fin n → ℤ := fun j ↦ sBox (e j)
  refine ⟨t, s, ?_, ?_⟩
  · -- The filtered enumeration keeps exactly the bounded remainders that still lie in the cone.
    intro j
    have hej : e j ∈ remainderIndex := by
      rw [← he_range]
      exact ⟨j, rfl⟩
    exact hej
  · intro z hz
    obtain ⟨coeff, μ₀, ρ, hcoeff_nonneg, hz_split, hρ_eq, hfract_nonneg, hfract_lt_one⟩ :=
      existsHalfOpenBoxRemainderOfIntegralConePoint a hz
    have hρ_mem :
        (fun i ↦ (ρ i : ℚ)) ∈
          (PointedCone.hull ℚ (Set.range fun l : Fin q ↦ fun u ↦ (a l u : ℚ)) :
            Set (Fin n → ℚ)) := by
      -- The fractional remainder is itself a nonnegative conic combination of the generators.
      refine mem_hull_of_equivFin_nonnegative_family
        (fun l : Fin q ↦ fun u ↦ (a l u : ℚ))
        (fun l ↦ Int.fract (coeff l))
        (fun i ↦ (ρ i : ℚ))
        (fun l ↦ hfract_nonneg l) ?_
      simpa using hρ_eq
    have hρ_box :
        ∀ i : Fin n, ρ i ∈ Set.Icc (lower i) (upper i) := by
      intro i
      have hcoordBox :=
        weightedIntegralCombination_mem_coordinateBox
          (fun l : Fin q ↦ a l i)
          (fun l ↦ Int.fract (coeff l))
          hfract_nonneg
          (fun l ↦ (hfract_lt_one l).le)
      have hcoordEq :
          (ρ i : ℚ) = ∑ l : Fin q, Int.fract (coeff l) * (a l i : ℚ) := by
        simpa [Pi.smul_apply] using congrFun hρ_eq i
      rw [← hcoordEq] at hcoordBox
      rcases hcoordBox with ⟨hl, hu⟩
      exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩
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
    -- Put the chosen remainder back into the floor/fract decomposition of `z`.
    simpa [s, hjBox, add_comm, add_left_comm, add_assoc] using hz_split

/-- Helper for Exercise 4.23: reindexing a finite rational family by an equivalence preserves the
Hilbert-basis property. -/
lemma isHilbertBasis_equiv
    {ι κ : Type*}
    (e : ι ≃ κ)
    (a : κ → Fin n → ℚ) :
    Exercise423Aux.IsHilbertBasis (a ∘ e) ↔ Exercise423Aux.IsHilbertBasis a := by
  constructor
  · intro h z hz
    have hz' :
        (fun i ↦ (z i : ℚ)) ∈
          (PointedCone.hull ℚ (Set.range (a ∘ e)) : Set (Fin n → ℚ)) := by
      simpa [Function.comp, Set.range_comp] using hz
    rcases h z hz' with ⟨u, hu⟩
    refine ⟨u.mapDomain e, ?_⟩
    -- Push the finitely supported witness through the index equivalence once.
    calc
      (fun i ↦ (z i : ℚ))
          = u.sum (fun i c ↦ c • a (e i)) := hu
      _ = (u.mapDomain e).sum (fun k c ↦ c • a k) := by
            symm
            simpa [Finsupp.linearCombination_apply] using
              (Finsupp.linearCombination_mapDomain
                (R := ℕ) (v' := a) e u)
  · intro h z hz
    have hz' :
        (fun i ↦ (z i : ℚ)) ∈
          (PointedCone.hull ℚ (Set.range a) : Set (Fin n → ℚ)) := by
      simpa [Function.comp, Set.range_comp] using hz
    rcases h z hz' with ⟨u, hu⟩
    refine ⟨u.mapDomain e.symm, ?_⟩
    -- The reverse transport uses the inverse equivalence on witnesses.
    calc
      (fun i ↦ (z i : ℚ))
          = u.sum (fun k c ↦ c • a k) := hu
      _ = (u.mapDomain e.symm).sum (fun i c ↦ c • a (e i)) := by
            symm
            simpa [Finsupp.linearCombination_apply] using
              (Finsupp.linearCombination_mapDomain
                (R := ℕ) (v' := fun i : ι ↦ a (e i)) e.symm u)

/-- Helper for Exercise 4.23: every finite integral family admits a positive integer scaling whose
rational realization is a Hilbert basis. -/
lemma existsPositiveIntegerScalingHilbertBasisOfFiniteIntegralFamily
    {ι : Type*}
    [Fintype ι]
    (a : ι → Fin n → ℤ) :
    ∃ k : ℕ+,
      Exercise423Aux.IsHilbertBasis
        (fun i ↦ ((k : ℚ)⁻¹) • (fun t ↦ (a i t : ℚ))) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let aFin : Fin (Fintype.card ι) → Fin n → ℤ := fun j ↦ a (e.symm j)
  obtain ⟨t, s, hs_mem, hs_cover⟩ := existsFiniteIntegralRemainderFamilyOfIntegralCone aFin
  obtain ⟨k, hk⟩ :=
    existsCommonScalingForFiniteConeWitnessFamily
      (fun i : Fin (Fintype.card ι) ↦ fun t ↦ (aFin i t : ℚ))
      s
      hs_mem
  refine ⟨k, ?_⟩
  have hFin :
      Exercise423Aux.IsHilbertBasis
        (fun i : Fin (Fintype.card ι) ↦ ((k : ℚ)⁻¹) • (fun t ↦ (aFin i t : ℚ))) := by
    intro z hz
    have hz_unscaled :
        (fun i ↦ (z i : ℚ)) ∈
          (PointedCone.hull ℚ (Set.range fun i : Fin (Fintype.card ι) ↦ fun t ↦ (aFin i t : ℚ)) :
            Set (Fin n → ℚ)) := by
      rcases (mem_hull_iff.mp hz) with ⟨m, r', hr_mem, coeff, hcoeff_nonneg, hz_eq⟩
      let idx : Fin m → Fin (Fintype.card ι) := fun j ↦ Classical.choose (hr_mem j)
      have hidx :
          ∀ j : Fin m,
            r' j = ((k : ℚ)⁻¹) • (fun t ↦ (aFin (idx j) t : ℚ)) := by
        intro j
        exact (Classical.choose_spec (hr_mem j)).symm
      have hz_selected :
          (fun i ↦ (z i : ℚ)) ∈
            (PointedCone.hull ℚ (Set.range fun j : Fin m ↦ fun t ↦ (aFin (idx j) t : ℚ)) :
              Set (Fin n → ℚ)) := by
        refine mem_hull_of_equivFin_nonnegative_family
          (fun j : Fin m ↦ fun t ↦ (aFin (idx j) t : ℚ))
          (fun j ↦ coeff j * (k : ℚ)⁻¹)
          (fun i ↦ (z i : ℚ))
          (fun j ↦ mul_nonneg (hcoeff_nonneg j) (by positivity)) ?_
        ext t
        calc
          (fun i ↦ (z i : ℚ)) t = (∑ j : Fin m, coeff j • r' j) t := by
            simpa using congrFun hz_eq t
          _ = ∑ j : Fin m, coeff j * r' j t := by
                simp [Pi.smul_apply]
          _ = ∑ j : Fin m, coeff j * ((((k : ℚ)⁻¹) • (fun t ↦ (aFin (idx j) t : ℚ))) t) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [hidx j]
          _ = ∑ j : Fin m, (coeff j * (k : ℚ)⁻¹) * (aFin (idx j) t : ℚ) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
          _ = (∑ j : Fin m, (coeff j * (k : ℚ)⁻¹) •
                (fun t ↦ (aFin (idx j) t : ℚ))) t := by
                simp [Pi.smul_apply]
      refine
        (show
          (PointedCone.hull ℚ (Set.range fun j : Fin m ↦ fun t ↦ (aFin (idx j) t : ℚ)) :
            Set (Fin n → ℚ)) ⊆
            (PointedCone.hull ℚ
              (Set.range fun i : Fin (Fintype.card ι) ↦ fun t ↦ (aFin i t : ℚ)) :
                Set (Fin n → ℚ)) from ?_) hz_selected
      exact Submodule.span_mono <| by
        intro y hy
        rcases hy with ⟨j, rfl⟩
        exact ⟨idx j, rfl⟩
    rcases hs_cover z hz_unscaled with ⟨j, μ, hz_split⟩
    rcases hk j with ⟨u, hu⟩
    have hμ_unit :
        (fun t ↦ ((μ.sum (fun i c ↦ c • aFin i)) t : ℚ)) =
          μ.sum
            (fun i c ↦ c • (((1 : ℕ+) : ℚ)⁻¹) • (fun t ↦ (aFin i t : ℚ))) := by
      -- Regard the integral part as a witness at denominator `1`.
      ext t
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp), Finset.sum_apply]
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp), Finset.sum_apply]
      simp [nsmul_eq_mul, Pi.smul_apply]
    rcases
        scaledCombination_ofScalingDvd
          (r := fun i : Fin (Fintype.card ι) ↦ fun t ↦ (aFin i t : ℚ))
          (z := fun t ↦ ((μ.sum (fun i c ↦ c • aFin i)) t : ℚ))
          (k₁ := 1)
          (k₂ := k)
          (by simpa using (one_dvd (k : ℕ)))
          hμ_unit with
      ⟨μ', hμ'⟩
    refine ⟨u + μ', ?_⟩
    have hz_cast :
        (fun t ↦ (z t : ℚ)) =
          (fun t ↦ (s j t : ℚ)) +
            (fun t ↦ ((μ.sum (fun i c ↦ c • aFin i)) t : ℚ)) := by
      -- Cast the integer remainder decomposition coordinatewise to `ℚ`.
      ext t
      change (z t : ℚ) = (s j t : ℚ) + ((μ.sum (fun i c ↦ c • aFin i)) t : ℚ)
      exact_mod_cast congrFun hz_split t
    calc
      (fun t ↦ (z t : ℚ))
          = (fun t ↦ (s j t : ℚ)) +
              (fun t ↦ ((μ.sum (fun i c ↦ c • aFin i)) t : ℚ)) := hz_cast
      _ = u.sum
            (fun i c ↦ c • (((k : ℚ)⁻¹) • (fun t ↦ (aFin i t : ℚ)))) +
            μ'.sum
              (fun i c ↦ c • (((k : ℚ)⁻¹) • (fun t ↦ (aFin i t : ℚ)))) := by
            rw [hu, hμ']
      _ = (u + μ').sum
            (fun i c ↦ c • (((k : ℚ)⁻¹) • (fun t ↦ (aFin i t : ℚ)))) := by
            symm
            rw [Finsupp.sum_add_index]
            · intro i
              simp
            · intro i c₁ c₂
              simp [add_smul]
  -- Transport the indexed `Fin` witness back to the original family.
  have htransport :=
    (isHilbertBasis_equiv e
      (fun i : Fin (Fintype.card ι) ↦ ((k : ℚ)⁻¹) • (fun t ↦ (aFin i t : ℚ)))).2 hFin
  have hfamily :
      ((fun i : Fin (Fintype.card ι) ↦ ((k : ℚ)⁻¹) • (fun t ↦ (aFin i t : ℚ))) ∘ e) =
        (fun i : ι ↦ ((k : ℚ)⁻¹) • (fun t ↦ (a i t : ℚ))) := by
    funext i
    simp [aFin]
  simpa [hfamily] using htransport

/-- Helper for Exercise 4.23: every finite rational family admits some positive integer scaling
whose generators form a Hilbert basis. -/
lemma existsPositiveIntegerScalingHilbertBasisOfFiniteRationalFamily
    {ι : Type*}
    [Fintype ι]
    (r : ι → Fin n → ℚ) :
    ∃ k : ℕ+, Exercise423Aux.IsHilbertBasis (fun i ↦ ((k : ℚ)⁻¹) • r i) := by
  classical
  let d : ι → ℕ := fun i ↦ rational_vector_common_denominator (r i)
  have hd_ne_zero : ∀ i : ι, d i ≠ 0 := by
    intro i
    exact rationalVectorCommonDenominator_ne_zero (r i)
  let D : ℕ+ := ⟨∏ i : ι, d i, by
    exact Finset.prod_pos fun i _ ↦ Nat.pos_of_ne_zero (hd_ne_zero i)⟩
  have hdiv : ∀ i : ι, d i ∣ (D : ℕ) := by
    intro i
    dsimp [D]
    exact Finset.dvd_prod_of_mem (fun j : ι ↦ d j) (by simp)
  choose q hq using hdiv
  let a : ι → Fin n → ℤ := fun i ↦ q i • common_denominator_scaled_vector (r i)
  have ha_eq :
      ∀ i : ι, (fun t ↦ (a i t : ℚ)) = (D : ℚ) • r i := by
    intro i
    -- Multiply the vector-specific common-denominator clearing by the remaining quotient to reach
    -- the global common denominator `D`.
    calc
      (fun t ↦ (a i t : ℚ))
          = (q i : ℚ) • (fun t ↦ (common_denominator_scaled_vector (r i) t : ℚ)) := by
              ext t
              simp [a, Pi.smul_apply, nsmul_eq_mul]
      _ = (q i : ℚ) • ((rational_vector_common_denominator (r i) : ℚ) • r i) := by
            rw [common_denominator_scaled_vector_eq_smul]
      _ = (D : ℚ) • r i := by
            rw [smul_smul]
            rw [hq i, Nat.cast_mul, mul_comm]
  obtain ⟨k, hk⟩ := existsPositiveIntegerScalingHilbertBasisOfFiniteIntegralFamily a
  have hscaled :
      Exercise423Aux.IsHilbertBasis
        (fun i ↦ ((D : ℚ)⁻¹) • (((k : ℚ)⁻¹) • (fun t ↦ (a i t : ℚ)))) :=
    isHilbertBasis_of_pnat_inv_smul D hk
  refine ⟨k, ?_⟩
  have hfamily :
      (fun i ↦ ((D : ℚ)⁻¹) • (((k : ℚ)⁻¹) • (fun t ↦ (a i t : ℚ)))) =
        (fun i ↦ ((k : ℚ)⁻¹) • r i) := by
    funext i
    have hD_ne : (D : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt D.pos)
    calc
      ((D : ℚ)⁻¹) • (((k : ℚ)⁻¹) • (fun t ↦ (a i t : ℚ)))
          = ((D : ℚ)⁻¹) • (((k : ℚ)⁻¹) • ((D : ℚ) • r i)) := by
              rw [ha_eq i]
      _ = ((D : ℚ)⁻¹) • ((D : ℚ) • (((k : ℚ)⁻¹) • r i)) := by
            have hcomm :
                ((k : ℚ)⁻¹) • ((D : ℚ) • r i) =
                  (D : ℚ) • (((k : ℚ)⁻¹) • r i) := by
              simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
            rw [hcomm]
      _ = ((k : ℚ)⁻¹) • r i := by
            simpa using inv_smul_smul₀ hD_ne (((k : ℚ)⁻¹) • r i)
  simpa [hfamily] using hscaled

/-- Helper for Exercise 4.23: a single positive integer scaling works simultaneously for every
subset of the row family. -/
lemma existsGlobalScalingHilbertBasisForAllRowSubsets
    (A : Matrix (Fin m) (Fin n) ℚ) :
    ∃ k : ℕ+, ∀ S : Set (Fin m),
      Exercise423Aux.IsHilbertBasis (fun i : S ↦ ((k : ℚ)⁻¹) • A i.1) := by
  classical
  -- First choose one scaling witness for each subset of rows.
  have hsubset :
      ∀ S : Set (Fin m),
        ∃ k : ℕ+, Exercise423Aux.IsHilbertBasis (fun i : S ↦ ((k : ℚ)⁻¹) • A i.1) := by
    intro S
    exact existsPositiveIntegerScalingHilbertBasisOfFiniteRationalFamily (fun i : S ↦ A i.1)
  let kS : Set (Fin m) → ℕ+ := fun S ↦ Classical.choose (hsubset S)
  let k : ℕ+ := ⟨∏ S : Set (Fin m), (kS S : ℕ), by
    exact Finset.prod_pos fun S _ ↦ (kS S).pos⟩
  refine ⟨k, ?_⟩
  intro S
  have hbase :
      Exercise423Aux.IsHilbertBasis (fun i : S ↦ ((kS S : ℚ)⁻¹) • A i.1) :=
    Classical.choose_spec (hsubset S)
  have hdiv : (kS S : ℕ) ∣ (k : ℕ) := by
    dsimp [k]
    exact Finset.dvd_prod_of_mem (fun T : Set (Fin m) ↦ (kS T : ℕ)) (by simp)
  -- The product scaling is a further down-scaling of the subset-specific witness.
  exact isHilbertBasis_ofScalingDvd (r := fun i : S ↦ A i.1) hdiv hbase

/-- Helper for Exercise 4.23: a single positive scaling can make the active-row family on every
nonempty face of the original polyhedron into a Hilbert basis for the scaled system. -/
lemma exists_positive_integer_scaling_active_rows_hilbert_basis_on_each_face
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    ∃ k : ℕ+,
      ∀ (F : Set (Fin n → ℝ))
        (_hF_nonempty : F.Nonempty)
        (_hF_extreme : IsExtreme ℝ (rational_matrix_polyhedron A b) F),
          Exercise423Aux.IsHilbertBasis
            (Exercise423Aux.activeRows (((k : ℚ)⁻¹) • A) (((k : ℚ)⁻¹) • b) F) := by
  rcases existsGlobalScalingHilbertBasisForAllRowSubsets A with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro F _hF_nonempty _hF_extreme
  have hrows :
      Exercise423Aux.IsHilbertBasis
        (fun i : Exercise423Aux.activeRowIndices A b F ↦ ((k : ℚ)⁻¹) • A i.1) :=
    hk (Exercise423Aux.activeRowIndices A b F)
  -- Transport the subset-wise witness to the active-row family of the uniformly scaled system.
  rw [← active_row_indices_pnat_inv_smul_eq A b F k] at hrows
  simpa [Exercise423Aux.activeRows] using hrows

/-- Exercise 4.23. Let `A x ≤ b` be a rational system. Then there exists a positive integer `k`
such that the scaled system `(A / k) x ≤ b / k` is totally dual integral. -/
theorem exists_positive_integer_scaling_is_totally_dual_integral
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    ∃ k : ℕ+, totally_dual_integral (((k : ℚ)⁻¹) • A) (((k : ℚ)⁻¹) • b) := by
  rcases exists_positive_integer_scaling_active_rows_hilbert_basis_on_each_face A b with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  -- Route correction: keep the source-faithful Theorem 4.60 route, but isolate the criterion as a
  -- local helper because the upstream import currently rebuilds a broken dependency file.
  refine Exercise423Aux.totally_dual_integral_of_active_rows_form_hilbert_basis_on_each_face
    (((k : ℚ)⁻¹) • A) (((k : ℚ)⁻¹) • b) ?_
  intro F hF_nonempty hF_extreme
  have hF_extreme_original : IsExtreme ℝ (rational_matrix_polyhedron A b) F := by
    simpa [rational_matrix_polyhedron_pnat_inv_smul_eq A b k] using hF_extreme
  exact hk F hF_nonempty hF_extreme_original

end Exercise423
