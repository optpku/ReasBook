import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_definition_6_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_15

open scoped Matrix

section Lemma64Inequalities

variable {n : ℕ}

/-- A lower inequality `δ ≤ γ ⬝ᵥ x` is nontrivial for `P` when it is valid on `P`, but does not
already hold on the whole nonnegative orthant. The companion theorem
`isNontrivialValidGeInequality_iff_is_valid_inequality_neg` rewrites this source-facing condition
into the Chapter 3 owner `is_valid_inequality`. -/
def IsNontrivialValidGeInequality
    (P : Set (Fin n → ℝ)) (γ : Fin n → ℝ) (δ : ℝ) : Prop :=
  (∀ ⦃x : Fin n → ℝ⦄, x ∈ P → δ ≤ γ ⬝ᵥ x) ∧
    ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x

/-- `IsNontrivialValidGeInequality P γ δ` means validity of `δ ≤ γ ⬝ᵥ x` on `P` together with
failure of validity on the whole nonnegative orthant. -/
theorem isNontrivialValidGeInequality_iff
    {P : Set (Fin n → ℝ)} {γ : Fin n → ℝ} {δ : ℝ} :
    IsNontrivialValidGeInequality P γ δ ↔
      (∀ ⦃x : Fin n → ℝ⦄, x ∈ P → δ ≤ γ ⬝ᵥ x) ∧
        ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  Iff.rfl

/-- `IsNontrivialValidGeInequality P γ δ` is equivalent to the Chapter 3 valid-inequality owner
for `(-γ) ⬝ᵥ x ≤ -δ`, together with failure of the original lower inequality on the whole
nonnegative orthant. -/
theorem isNontrivialValidGeInequality_iff_is_valid_inequality_neg
    {P : Set (Fin n → ℝ)} {γ : Fin n → ℝ} {δ : ℝ} :
    IsNontrivialValidGeInequality P γ δ ↔
      is_valid_inequality P (-γ) (-δ) ∧
        ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x := by
  rw [isNontrivialValidGeInequality_iff, valid_ge_inequality_iff_is_valid_inequality_neg]

namespace IsNontrivialValidGeInequality

variable {P : Set (Fin n → ℝ)} {γ : Fin n → ℝ} {δ : ℝ}

/-- A nontrivial valid lower inequality is valid on the target set. -/
theorem valid
    (h : IsNontrivialValidGeInequality P γ δ) :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ P → δ ≤ γ ⬝ᵥ x :=
  h.1

/-- A nontrivial valid lower inequality does not already hold on the whole nonnegative orthant. -/
theorem not_validOnNonnegativeOrthant
    (h : IsNontrivialValidGeInequality P γ δ) :
    ¬ ∀ x : Fin n → ℝ, (∀ j : Fin n, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  h.2

/-- The Chapter 3 valid-inequality owner attached to a nontrivial valid lower inequality. -/
theorem isValidInequalityNeg
    (h : IsNontrivialValidGeInequality P γ δ) :
    is_valid_inequality P (-γ) (-δ) :=
  valid_ge_inequality_iff_is_valid_inequality_neg.mp h.valid

end IsNontrivialValidGeInequality

/-- A normalized lower valid inequality on `C` rewrites `δ ≤ γ ⬝ᵥ x` as
`γ' ⬝ᵥ x ≥ 1` on `C`, with coordinatewise nonnegative coefficients. -/
class IsNormalizedValidGeInequality
    (C : Set (Fin n → ℝ)) (γ : Fin n → ℝ) (δ : ℝ) (γ' : Fin n → ℝ) : Prop where
  valid : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → 1 ≤ γ' ⬝ᵥ x
  coeff_nonneg : ∀ j : Fin n, 0 ≤ γ' j

variable (C : Set (Fin n → ℝ))

/-- Validity on a nonempty
set closed under nonnegative coordinate rays forces every coefficient of a lower inequality to
be nonnegative. -/
theorem validGeInequalityCoeffNonnegOfRays
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
    (hC_nonempty : C.Nonempty)
    {γ : Fin n → ℝ}
    {δ : ℝ}
    (hvalid : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → δ ≤ γ ⬝ᵥ x) :
    ∀ j : Fin n, 0 ≤ γ j := by
  classical
  rcases hC_nonempty with ⟨x₀, hx₀⟩
  intro j
  by_contra hj
  have hj_neg : γ j < 0 := lt_of_not_ge hj
  have hj_ne : γ j ≠ 0 := ne_of_lt hj_neg
  let a := (γ ⬝ᵥ x₀ - δ + 1) / (-γ j)
  have ha : 0 ≤ a := by
    -- Validity at the anchor makes the numerator nonnegative, and the denominator is positive.
    have hnum_nonneg : 0 ≤ γ ⬝ᵥ x₀ - δ + 1 := by
      linarith [hvalid hx₀]
    have hden_nonneg : 0 ≤ -γ j := by
      linarith
    exact div_nonneg hnum_nonneg hden_nonneg
  have hshift_mem : x₀ + a • Pi.single j (1 : ℝ) ∈ C :=
    hC_coordinate_ray j hx₀ a ha
  have hshift_valid : δ ≤ γ ⬝ᵥ (x₀ + a • Pi.single j (1 : ℝ)) :=
    hvalid hshift_mem
  have hshift_value :
      γ ⬝ᵥ (x₀ + a • Pi.single j (1 : ℝ)) = δ - 1 := by
    -- The chosen distance along the negative coefficient ray lowers the value by exactly one.
    rw [dotProduct_add, dotProduct_smul, dotProduct_single_one]
    dsimp [a]
    field_simp [hj_ne]
    ring
  rw [hshift_value] at hshift_valid
  linarith

/-- Helper for Lemma 6.4: if all points of `C` are coordinatewise nonnegative, every coordinate
unit ray remains in `C`, and `C` is nonempty, then every nontrivial valid inequality
`δ ≤ γ ⬝ᵥ x` for `C` has positive right-hand side. -/
theorem corner_nontrivial_valid_inequality_rhs_pos
    (_hC_nonneg : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ j : Fin n, 0 ≤ x j)
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
    (hC_nonempty : C.Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq : IsNontrivialValidGeInequality C γ δ) :
    0 < δ := by
  have hγ_nonneg : ∀ j : Fin n, 0 ≤ γ j :=
    validGeInequalityCoeffNonnegOfRays C hC_coordinate_ray hC_nonempty hineq.valid
  -- A nonpositive right-hand side would make the inequality valid on the whole orthant.
  by_contra hδ
  have hδ_nonpos : δ ≤ 0 := le_of_not_gt hδ
  apply hineq.not_validOnNonnegativeOrthant
  intro x hx_nonneg
  exact hδ_nonpos.trans (dotProduct_nonneg_of_nonneg hγ_nonneg hx_nonneg)

/-- Helper for Lemma 6.4: if all points of `C` are coordinatewise nonnegative, every coordinate
unit ray remains in `C`, and `C` is nonempty, then every nontrivial valid inequality for `C` can
be rescaled to the valid inequality `(δ⁻¹ • γ) ⬝ᵥ x ≥ 1`. -/
theorem corner_nontrivial_valid_inequality_normalized
    (hC_nonneg : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ j : Fin n, 0 ≤ x j)
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
    (hC_nonempty : C.Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq : IsNontrivialValidGeInequality C γ δ) :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → 1 ≤ (δ⁻¹ • γ) ⬝ᵥ x := by
  have hδ_pos :=
    corner_nontrivial_valid_inequality_rhs_pos C hC_nonneg hC_coordinate_ray hC_nonempty γ δ hineq
  intro x hx
  -- Scale validity by the positive inverse of the right-hand side.
  have hscaled :=
    mul_le_mul_of_nonneg_left (hineq.valid hx) (inv_nonneg.mpr hδ_pos.le)
  simpa [smul_dotProduct, hδ_pos.ne'] using hscaled

/-- Helper for Lemma 6.4: under the same hypotheses, if `C` is nonempty, every coefficient of the
rescaled vector `δ⁻¹ • γ` is nonnegative. -/
theorem corner_nontrivial_valid_inequality_normalized_nonneg
    (hC_nonneg : ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ j : Fin n, 0 ≤ x j)
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
    (hC_nonempty : C.Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq : IsNontrivialValidGeInequality C γ δ) :
    ∀ j : Fin n, 0 ≤ (δ⁻¹ • γ) j := by
  have hγ_nonneg : ∀ j : Fin n, 0 ≤ γ j :=
    validGeInequalityCoeffNonnegOfRays C hC_coordinate_ray hC_nonempty hineq.valid
  have hδ_pos :=
    corner_nontrivial_valid_inequality_rhs_pos C hC_nonneg hC_coordinate_ray hC_nonempty γ δ hineq
  intro j
  -- Positive inverse scaling preserves coefficientwise nonnegativity.
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hδ_pos.le) (hγ_nonneg j)

end Lemma64Inequalities
