/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Gauge
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_29

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so this file keeps the source-facing one-dimensional `R_f` formulas
-- on `ℝ` while reusing the chapter's canonical `q = 1` continuous-relaxation owners.

noncomputable section

section Example635

open scoped IntegerVectorNotation

local notation "R1" => Fin 1 → ℝ
local notation "ContAssignment" => ℝ →₀ NNReal

private def realAsR1 : ℝ ≃ R1 where
  toFun r := fun _ ↦ r
  invFun r := r 0
  left_inv := fun _ ↦ rfl
  right_inv r := funext fun i ↦ congrArg r (Subsingleton.elim 0 i)

private abbrev scalarContAssignmentEquiv : ContAssignment ≃ (R1 →₀ NNReal) :=
  Finsupp.equivCongrLeft realAsR1

private theorem scalarContAssignmentEquiv_sum_apply_zero
    (y : ContAssignment) :
    (scalarContAssignmentEquiv y).sum (fun r a ↦ (a : ℝ) * r 0) =
      y.sum (fun r a ↦ (a : ℝ) * r) := by
  rw [scalarContAssignmentEquiv, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index]
  · simp [realAsR1]
  · intro r
    simp
  · intro r a₁ a₂
    rw [NNReal.coe_add, add_mul]

private theorem scalarContAssignmentEquiv_weighted_sum_apply_zero
    (ψ : ℝ → ℝ) (y : ContAssignment) :
    (scalarContAssignmentEquiv y).sum (fun r a ↦ ψ (r 0) * (a : ℝ)) =
      y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
  rw [scalarContAssignmentEquiv, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index]
  · simp [realAsR1]
  · intro r
    simp
  · intro r a₁ a₂
    rw [NNReal.coe_add, left_distrib]

private theorem continuousInfiniteBalance_scalarContAssignmentEquiv_apply_zero
    (f : ℝ) (y : ContAssignment) :
    continuous_infinite_balance (fun _ : Fin 1 ↦ f) (scalarContAssignmentEquiv y) 0 =
      f + y.sum (fun r a ↦ (a : ℝ) * r) := by
  rw [continuous_infinite_balance_apply, scalarContAssignmentEquiv_sum_apply_zero]

/-- The one-dimensional continuous infinite relaxation `R_f`, consisting of finitely supported
nonnegative coefficient families whose weighted sum with `f` is integral. This is the `q = 1`
specialization of the chapter's canonical feasible-set owner. -/
abbrev continuous_infinite_relaxation_feasible_set_on_R (f : ℝ) : Set ContAssignment :=
  scalarContAssignmentEquiv ⁻¹' continuous_infinite_relaxation_feasible_set (fun _ : Fin 1 ↦ f)

/-- Membership in `continuous_infinite_relaxation_feasible_set_on_R f` is exactly the
one-dimensional integrality condition from `R_f`. -/
theorem mem_continuous_infinite_relaxation_feasible_set_on_R_iff
    {f : ℝ} {y : ContAssignment} :
    y ∈ continuous_infinite_relaxation_feasible_set_on_R f ↔
      ∃ z : ℤ, f + y.sum (fun r a ↦ (a : ℝ) * r) = (z : ℝ) := by
  change scalarContAssignmentEquiv y ∈ continuous_infinite_relaxation_feasible_set
      (fun _ : Fin 1 ↦ f) ↔ _
  rw [mem_continuous_infinite_relaxation_feasible_set_iff, mem_integerVectors_iff_forall]
  constructor
  · intro hy
    rcases (show ∃ z : ℤ,
      (z : ℝ) =
        continuous_infinite_balance (fun _ : Fin 1 ↦ f) (scalarContAssignmentEquiv y) 0 from
      hy 0) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [continuousInfiniteBalance_scalarContAssignmentEquiv_apply_zero] using hz.symm
  · rintro ⟨z, hz⟩ i
    fin_cases i
    refine ⟨z, ?_⟩
    simpa [continuousInfiniteBalance_scalarContAssignmentEquiv_apply_zero] using hz.symm

/-- A function `ψ : ℝ → ℝ` is valid for the one-dimensional continuous infinite relaxation when
its cut inequality holds on every feasible point of `R_f`. This is the `q = 1` specialization of
the chapter's canonical continuous-valid-function owner. -/
abbrev IsValidFunctionForContinuousInfiniteRelaxationOnR
    (f : ℝ) (ψ : ℝ → ℝ) : Prop :=
  IsValidFunctionForContinuousInfiniteRelaxation (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0))

/-- Unfolding the one-dimensional valid-function owner recovers the canonical `q = 1` chapter
owner. -/
theorem isValidFunctionForContinuousInfiniteRelaxationOnR_iff
    {f : ℝ} {ψ : ℝ → ℝ} :
    IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ ↔
      IsValidFunctionForContinuousInfiniteRelaxation
        (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0)) :=
  Iff.rfl

/-- A one-dimensional valid function satisfies the defining inequality on every feasible point of
`R_f`. -/
theorem continuous_infinite_valid_function_on_R_one_le
    {f : ℝ} {ψ : ℝ → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ)
    {y : ContAssignment}
    (hy : y ∈ continuous_infinite_relaxation_feasible_set_on_R f) :
    1 ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
  change scalarContAssignmentEquiv y ∈ continuous_infinite_relaxation_feasible_set
      (fun _ : Fin 1 ↦ f) at hy
  simpa [scalarContAssignmentEquiv_weighted_sum_apply_zero] using
    continuous_infinite_valid_function_one_le hψ hy

/-- A valid function for the one-dimensional continuous infinite relaxation is minimal when every
valid function lying pointwise below it is equal to it. This is the `q = 1` specialization of the
chapter's canonical minimal-valid-function owner. -/
abbrev IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR
    (f : ℝ) (ψ : ℝ → ℝ) : Prop :=
  IsMinimalValidFunctionForContinuousInfiniteRelaxation
    (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0))

/-- Unfolding the one-dimensional minimal-valid-function owner recovers the canonical `q = 1`
chapter owner. -/
theorem isMinimalValidFunctionForContinuousInfiniteRelaxationOnR_iff
    {f : ℝ} {ψ : ℝ → ℝ} :
    IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ ↔
      IsMinimalValidFunctionForContinuousInfiniteRelaxation
        (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0)) :=
  Iff.rfl

/-- A minimal valid function on `ℝ` is valid. -/
instance instIsValidFunctionForContinuousInfiniteRelaxationOnROfMinimal
    {f : ℝ} {ψ : ℝ → ℝ}
    [hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ] :
    IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ :=
  hψ.toIsValidFunctionForContinuousInfiniteRelaxation

/-- Minimality on `R_f` can be used through pointwise domination by another valid function. -/
theorem isMinimalValidFunctionForContinuousInfiniteRelaxationOnR_eq_of_le
    {f : ℝ} {ψ ψ' : ℝ → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ)
    (hψ' : IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ')
    (hle : ∀ r : ℝ, ψ' r ≤ ψ r) :
    ψ' = ψ := by
  have hle' : ∀ r : R1, ψ' (r 0) ≤ ψ (r 0) := fun r ↦ hle (r 0)
  have hEq : (fun r : R1 ↦ ψ' (r 0)) = fun r : R1 ↦ ψ (r 0) :=
    continuous_infinite_minimal_valid_function_eq_of_le hψ hψ' hle'
  ext r
  exact congrFun hEq (fun _ ↦ r)

/-- A function strictly above a minimal valid function at some point cannot itself be minimal for
the one-dimensional continuous infinite relaxation. -/
theorem not_minimal_of_strictly_dominated_by_minimal_on_R
    {f : ℝ} {ψ₀ ψ : ℝ → ℝ}
    (hψ₀ : IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ₀)
    (hle : ∀ r : ℝ, ψ₀ r ≤ ψ r)
    (hstrict : ∃ r : ℝ, ψ₀ r < ψ r) :
    ¬ IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ := by
  intro hψ
  have hvalid₀ : IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ₀ :=
    hψ₀.toIsValidFunctionForContinuousInfiniteRelaxation
  have hEq := isMinimalValidFunctionForContinuousInfiniteRelaxationOnR_eq_of_le hψ hvalid₀ hle
  rcases hstrict with ⟨r, hr⟩
  have hEval : ψ₀ r = ψ r := congrArg (fun φ : ℝ → ℝ ↦ φ r) hEq
  have hnot : ¬ ψ₀ r < ψ r := by
    simp [hEval]
  exact hnot hr

/-- The translated interval `B - f = [-f, 1 - f]` from Example 6.35, where `B = [0,1]`. -/
def example_6_35_shifted_unit_interval (f : ℝ) : Set ℝ :=
  Set.Icc (-f) (1 - f)

/-- The function `ψ₀` from Example 6.35, written as the piecewise-linear function attached to the
slopes of the interval gauge. -/
def example_6_35_psi_zero (f : ℝ) : ℝ → ℝ :=
  fun r ↦
    if 0 ≤ r then
      r / (1 - f)
    else
      -r / f

/-- Expanding `example_6_35_psi_zero f` recovers its displayed piecewise formula. -/
@[simp] theorem example_6_35_psi_zero_apply
    (f r : ℝ) :
    example_6_35_psi_zero f r =
      if 0 ≤ r then
        r / (1 - f)
      else
        -r / f :=
  rfl

/-- Example 6.35 (1). Under the effective interval hypothesis `0 < f < 1` implied by the
source assumptions `0 < t` and `t + 1/2 < f < 1`, the function `ψ₀` is the gauge of the
translated interval `B - f = [-f, 1 - f]`, where `B = [0,1]`. -/
theorem example_6_35_psi_zero_eq_gauge
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    example_6_35_psi_zero f = gauge (example_6_35_shifted_unit_interval f) := by
  have hK_convex : Convex ℝ (example_6_35_shifted_unit_interval f) := by
    simpa [example_6_35_shifted_unit_interval] using convex_Icc (-f) (1 - f)
  have hK_zero :
      (0 : ℝ) ∈ interior (example_6_35_shifted_unit_interval f) := by
    rw [example_6_35_shifted_unit_interval, interior_Icc]
    exact ⟨neg_lt_zero.mpr hf0, sub_pos.mpr hf1⟩
  have hK_nhds : example_6_35_shifted_unit_interval f ∈ nhds (0 : ℝ) :=
    mem_interior_iff_mem_nhds.mp hK_zero
  have hright : gauge (example_6_35_shifted_unit_interval f) (1 - f) = 1 := by
    apply le_antisymm
    · -- The right endpoint belongs to the closed interval, so its gauge is at most one.
      apply gauge_le_one_of_mem
      simp [example_6_35_shifted_unit_interval]
    · -- A gauge below one would put the endpoint in the open interval, which is impossible.
      apply not_lt.mp
      intro hlt
      have hmem :=
        (gauge_lt_one_iff_mem_interior hK_convex hK_nhds).mp hlt
      rw [example_6_35_shifted_unit_interval, interior_Icc] at hmem
      exact (lt_irrefl (1 - f)) hmem.2
  have hleft : gauge (example_6_35_shifted_unit_interval f) (-f) = 1 := by
    apply le_antisymm
    · -- The left endpoint gives the analogous upper bound.
      apply gauge_le_one_of_mem
      simp [example_6_35_shifted_unit_interval]
    · -- Strict gauge inequality would likewise put the left endpoint in the interior.
      apply not_lt.mp
      intro hlt
      have hmem :=
        (gauge_lt_one_iff_mem_interior hK_convex hK_nhds).mp hlt
      rw [example_6_35_shifted_unit_interval, interior_Icc] at hmem
      exact (lt_irrefl (-f)) hmem.1
  funext r
  by_cases hr : 0 ≤ r
  · have hscale : 0 ≤ r / (1 - f) :=
      div_nonneg hr (sub_nonneg.mpr hf1.le)
    have hdenom_ne : 1 - f ≠ 0 := ne_of_gt (sub_pos.mpr hf1)
    have hr_eq : r = (r / (1 - f)) • (1 - f) := by
      simpa [smul_eq_mul] using (div_mul_cancel₀ r hdenom_ne).symm
    -- Positive rays scale the right endpoint of the interval.
    rw [example_6_35_psi_zero_apply, if_pos hr]
    calc
      r / (1 - f) = (r / (1 - f)) • (1 : ℝ) := by simp [smul_eq_mul]
      _ = (r / (1 - f)) •
          gauge (example_6_35_shifted_unit_interval f) (1 - f) := by rw [hright]
      _ = gauge (example_6_35_shifted_unit_interval f)
          ((r / (1 - f)) • (1 - f)) :=
        (gauge_smul_of_nonneg hscale (1 - f)).symm
      _ = gauge (example_6_35_shifted_unit_interval f) r := by rw [← hr_eq]
  · have hr_neg : r < 0 := lt_of_not_ge hr
    have hscale : 0 ≤ -r / f :=
      div_nonneg (neg_nonneg.mpr hr_neg.le) hf0.le
    have hr_eq : r = (-r / f) • (-f) := by
      simp only [smul_eq_mul]
      field_simp [hf0.ne']
    -- Negative rays scale the left endpoint of the interval.
    rw [example_6_35_psi_zero_apply, if_neg hr]
    calc
      -r / f = (-r / f) • (1 : ℝ) := by simp [smul_eq_mul]
      _ = (-r / f) • gauge (example_6_35_shifted_unit_interval f) (-f) := by rw [hleft]
      _ = gauge (example_6_35_shifted_unit_interval f) ((-r / f) • (-f)) :=
        (gauge_smul_of_nonneg hscale (-f)).symm
      _ = gauge (example_6_35_shifted_unit_interval f) r := by rw [← hr_eq]

/-- Helper for Example 6.35: the gauge of a convex scalar set containing zero in its interior is
bounded by the weighted sum of the gauges of a finitely supported nonnegative assignment. -/
private lemma gauge_le_nnrealFinsuppSum
    {K : Set ℝ}
    (hK_convex : Convex ℝ K)
    (hK_zero : (0 : ℝ) ∈ interior K)
    (y : ContAssignment) :
    gauge K (y.sum (fun r a ↦ (a : ℝ) * r)) ≤
      y.sum (fun r a ↦ gauge K r * (a : ℝ)) := by
  have hK_absorbent : Absorbent ℝ K :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp hK_zero)
  -- Subadditivity reduces the gauge of the assignment sum to its supported terms.
  calc
    gauge K (y.sum (fun r a ↦ (a : ℝ) * r)) =
        gauge K (y.support.sum (fun r ↦ (y r : ℝ) * r)) := by
          rw [Finsupp.sum]
    _ ≤ y.support.sum (fun r ↦ gauge K ((y r : ℝ) * r)) := by
          simpa using
            gauge_sum_le (s := K) hK_convex hK_absorbent y.support
              (fun r ↦ (y r : ℝ) * r)
    _ = y.support.sum (fun r ↦ gauge K r * (y r : ℝ)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hyr_nonneg : 0 ≤ (y r : ℝ) := by positivity
          simpa [smul_eq_mul, mul_comm] using
            gauge_smul_of_nonneg (s := K) (a := (y r : ℝ)) hyr_nonneg r
    _ = y.sum (fun r a ↦ gauge K r * (a : ℝ)) := by
          rw [Finsupp.sum]

/-- Helper for Example 6.35: the translated distance from `f` to any integer has gauge at least one
in `[-f, 1 - f]`. -/
private lemma one_le_gauge_integer_sub
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    (z : ℤ) :
    1 ≤ gauge (example_6_35_shifted_unit_interval f) ((z : ℝ) - f) := by
  have hK_convex : Convex ℝ (example_6_35_shifted_unit_interval f) := by
    simpa [example_6_35_shifted_unit_interval] using convex_Icc (-f) (1 - f)
  have hK_zero :
      (0 : ℝ) ∈ interior (example_6_35_shifted_unit_interval f) := by
    rw [example_6_35_shifted_unit_interval, interior_Icc]
    exact ⟨neg_lt_zero.mpr hf0, sub_pos.mpr hf1⟩
  have hK_nhds : example_6_35_shifted_unit_interval f ∈ nhds (0 : ℝ) :=
    mem_interior_iff_mem_nhds.mp hK_zero
  -- Interior membership would force the integer `z` strictly between zero and one.
  apply not_lt.mp
  intro hlt
  have hmem := (gauge_lt_one_iff_mem_interior hK_convex hK_nhds).mp hlt
  rw [example_6_35_shifted_unit_interval, interior_Icc] at hmem
  have hz0 : (0 : ℝ) < z := by linarith [hmem.1]
  have hz1 : (z : ℝ) < 1 := by linarith [hmem.2]
  have hz0_int : (0 : ℤ) < z := by exact_mod_cast hz0
  have hz1_int : z < (1 : ℤ) := by exact_mod_cast hz1
  omega

/-- Helper for Example 6.35: `example_6_35_psi_zero f` is valid for the scalar relaxation `R_f`. -/
private lemma example635PsiZeroValidForRf
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    IsValidFunctionForContinuousInfiniteRelaxationOnR f (example_6_35_psi_zero f) := by
  refine ⟨?_⟩
  intro Y hY
  let y : ContAssignment := scalarContAssignmentEquiv.symm Y
  have hY_eq : scalarContAssignmentEquiv y = Y :=
    scalarContAssignmentEquiv.apply_symm_apply Y
  have hy : y ∈ continuous_infinite_relaxation_feasible_set_on_R f := by
    change scalarContAssignmentEquiv y ∈
      continuous_infinite_relaxation_feasible_set (fun _ : Fin 1 ↦ f)
    rw [hY_eq]
    exact hY
  obtain ⟨z, hz⟩ :=
    mem_continuous_infinite_relaxation_feasible_set_on_R_iff.mp hy
  have hbalance : y.sum (fun r a ↦ (a : ℝ) * r) = (z : ℝ) - f := by
    linarith
  have hK_convex : Convex ℝ (example_6_35_shifted_unit_interval f) := by
    simpa [example_6_35_shifted_unit_interval] using convex_Icc (-f) (1 - f)
  have hK_zero :
      (0 : ℝ) ∈ interior (example_6_35_shifted_unit_interval f) := by
    rw [example_6_35_shifted_unit_interval, interior_Icc]
    exact ⟨neg_lt_zero.mpr hf0, sub_pos.mpr hf1⟩
  -- Compare the integer-shift gauge with the subadditive gauge sum of the assignment.
  have hscalar :
      1 ≤ y.sum (fun r a ↦ example_6_35_psi_zero f r * (a : ℝ)) := by
    calc
      1 ≤ gauge (example_6_35_shifted_unit_interval f) ((z : ℝ) - f) :=
        one_le_gauge_integer_sub hf0 hf1 z
      _ = gauge (example_6_35_shifted_unit_interval f)
          (y.sum (fun r a ↦ (a : ℝ) * r)) := by rw [hbalance]
      _ ≤ y.sum (fun r a ↦
          gauge (example_6_35_shifted_unit_interval f) r * (a : ℝ)) :=
        gauge_le_nnrealFinsuppSum hK_convex hK_zero y
      _ = y.sum (fun r a ↦ example_6_35_psi_zero f r * (a : ℝ)) := by
        rw [example_6_35_psi_zero_eq_gauge hf0 hf1]
  rw [← hY_eq, scalarContAssignmentEquiv_weighted_sum_apply_zero]
  exact hscalar

/-- Helper for Example 6.35: a scalar valid function below `example_6_35_psi_zero f` agrees with it
pointwise. -/
private lemma example635EqOfValidLePsiZero
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    {ψ' : ℝ → ℝ}
    (hψ' : IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ')
    (hle : ∀ r : ℝ, ψ' r ≤ example_6_35_psi_zero f r) :
    ψ' = example_6_35_psi_zero f := by
  funext r
  apply le_antisymm (hle r)
  rcases lt_trichotomy r 0 with hr_neg | hr_zero | hr_pos
  -- Nonpositive numerator and denominator give a nonnegative quotient on this ray.
  · have ha_nonneg : 0 ≤ -f / r :=
      div_nonneg_of_nonpos (neg_nonpos.mpr hf0.le) hr_neg.le
    let a : NNReal := ⟨-f / r, ha_nonneg⟩
    let y : ContAssignment := Finsupp.single r a
    have ha_coe : (a : ℝ) = -f / r := rfl
    have hbalance : f + y.sum (fun s b ↦ (b : ℝ) * s) = (0 : ℤ) := by
      simp [y, ha_coe]
      field_simp [hr_neg.ne]
      ring
    have hy : y ∈ continuous_infinite_relaxation_feasible_set_on_R f :=
      mem_continuous_infinite_relaxation_feasible_set_on_R_iff.mpr ⟨0, hbalance⟩
    have hcut : 1 ≤ ψ' r * (-f / r) := by
      simpa [y, a] using continuous_infinite_valid_function_on_R_one_le hψ' hy
    have hscaled : -r ≤ ψ' r * f := by
      calc
        -r = (-r) * 1 := by ring
        _ ≤ (-r) * (ψ' r * (-f / r)) :=
          mul_le_mul_of_nonneg_left hcut (neg_nonneg.mpr hr_neg.le)
        _ = ψ' r * f := by
          field_simp [hr_neg.ne]
    -- The singleton aimed at the left endpoint forces the negative-ray slope.
    simpa [example_6_35_psi_zero_apply, not_le.mpr hr_neg] using
      (div_le_iff₀ hf0).mpr hscaled
  · subst r
    have hnonneg : 0 ≤ ψ' 0 := by
      simpa using
        continuousInfiniteValidFunctionNonnegOnRationalVectors
          hψ' (0 : Fin 1 → ℚ)
    simpa [example_6_35_psi_zero_apply] using hnonneg
  · have hone_sub_f_pos : 0 < 1 - f := sub_pos.mpr hf1
    have ha_nonneg : 0 ≤ (1 - f) / r :=
      div_nonneg hone_sub_f_pos.le hr_pos.le
    let a : NNReal := ⟨(1 - f) / r, ha_nonneg⟩
    let y : ContAssignment := Finsupp.single r a
    have ha_coe : (a : ℝ) = (1 - f) / r := rfl
    have hbalance : f + y.sum (fun s b ↦ (b : ℝ) * s) = (1 : ℤ) := by
      simp [y, ha_coe]
      field_simp [hr_pos.ne']
      ring
    have hy : y ∈ continuous_infinite_relaxation_feasible_set_on_R f :=
      mem_continuous_infinite_relaxation_feasible_set_on_R_iff.mpr ⟨1, hbalance⟩
    have hcut : 1 ≤ ψ' r * ((1 - f) / r) := by
      simpa [y, a] using continuous_infinite_valid_function_on_R_one_le hψ' hy
    have hscaled : r ≤ ψ' r * (1 - f) := by
      calc
        r = r * 1 := by ring
        _ ≤ r * (ψ' r * ((1 - f) / r)) :=
          mul_le_mul_of_nonneg_left hcut hr_pos.le
        _ = ψ' r * (1 - f) := by
          field_simp [hr_pos.ne']
    -- The singleton aimed at the right endpoint forces the positive-ray slope.
    simpa [example_6_35_psi_zero_apply, hr_pos.le] using
      (div_le_iff₀ hone_sub_f_pos).mpr hscaled

/-- Helper for Example 6.35: validity and pointwise domination on `ℝ¹` reduce to the scalar
domination principle. -/
private lemma example635EqOfValidLePsiZeroOnR1
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    {ψ' : R1 → ℝ}
    (hψ' : IsValidFunctionForContinuousInfiniteRelaxation (fun _ : Fin 1 ↦ f) ψ')
    (hle : ∀ r : R1, ψ' r ≤ example_6_35_psi_zero f (r 0)) :
    ψ' = fun r : R1 ↦ example_6_35_psi_zero f (r 0) := by
  let φ : ℝ → ℝ := fun t ↦ ψ' (fun _ ↦ t)
  have hψ'_eq : (fun r : R1 ↦ φ (r 0)) = ψ' := by
    funext r
    apply congrArg ψ'
    funext i
    fin_cases i
    rfl
  have hφ_valid : IsValidFunctionForContinuousInfiniteRelaxationOnR f φ := by
    change IsValidFunctionForContinuousInfiniteRelaxation
      (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ φ (r 0))
    rw [hψ'_eq]
    exact hψ'
  have hφ_le : ∀ t : ℝ, φ t ≤ example_6_35_psi_zero f t := by
    intro t
    simpa [φ] using hle (fun _ ↦ t)
  have hφ_eq : φ = example_6_35_psi_zero f :=
    example635EqOfValidLePsiZero hf0 hf1 hφ_valid hφ_le
  -- Evaluation at the sole coordinate transports scalar equality back to `ℝ¹`.
  calc
    ψ' = fun r : R1 ↦ φ (r 0) := hψ'_eq.symm
    _ = fun r : R1 ↦ example_6_35_psi_zero f (r 0) :=
      congrArg (fun θ : ℝ → ℝ ↦ fun r : R1 ↦ θ (r 0)) hφ_eq

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_3/ch6_sec6_3_3_example_6_35.lean

Example 6.35 (2). Under the effective interval hypothesis `0 < f < 1` implied by the source
assumptions of Example 6.35, `ψ₀` is a minimal valid function for the one-dimensional continuous
infinite relaxation `R_f`. -/
theorem example_6_35_psi_zero_is_minimal_for_Rf
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f (example_6_35_psi_zero f) := by
  -- Validity comes from the gauge estimate; minimality is forced by the two endpoint tests.
  exact
    { toIsValidFunctionForContinuousInfiniteRelaxation :=
        example635PsiZeroValidForRf hf0 hf1
      eq_of_le := example635EqOfValidLePsiZeroOnR1 hf0 hf1 }

/-- Under the source hypotheses of Example 6.35, `example_6_35_psi_zero f` is available through
the canonical one-dimensional continuous-relaxation minimal-valid-function instance. -/
instance instExample635PsiZeroMinimalForRf
    {f : ℝ} [Fact (0 < f)] [Fact (f < 1)] :
    IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f (example_6_35_psi_zero f) :=
  example_6_35_psi_zero_is_minimal_for_Rf
    ‹Fact (0 < f)›.out ‹Fact (f < 1)›.out

/-- Example 6.35 (3). Under the effective interval hypothesis `0 < f < 1` implied by the source
assumptions of Example 6.35, any two functions `ψ₁` and `ψ₂` lying pointwise above `ψ₀` and
strictly above it somewhere are not minimal valid functions for `R_f`; this captures the source
conclusion for the liftings attached to `π₁` and `π₂`. -/
theorem example_6_35_psi_one_two_not_minimal_for_Rf
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    {ψ₁ ψ₂ : ℝ → ℝ}
    (hψ₁_ge : ∀ r : ℝ, example_6_35_psi_zero f r ≤ ψ₁ r)
    (hψ₂_ge : ∀ r : ℝ, example_6_35_psi_zero f r ≤ ψ₂ r)
    (hψ₁_strict : ∃ r : ℝ, example_6_35_psi_zero f r < ψ₁ r)
    (hψ₂_strict : ∃ r : ℝ, example_6_35_psi_zero f r < ψ₂ r) :
    ¬ IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ₁ ∧
      ¬ IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ₂ := by
  have hψ₀ :
      IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f (example_6_35_psi_zero f) := by
    -- Reuse the explicit minimality theorem with the hypotheses already in the context.
    exact example_6_35_psi_zero_is_minimal_for_Rf hf0 hf1
  constructor
  · exact not_minimal_of_strictly_dominated_by_minimal_on_R hψ₀ hψ₁_ge hψ₁_strict
  · exact not_minimal_of_strictly_dominated_by_minimal_on_R hψ₀ hψ₂_ge hψ₂_strict

end Example635

#print axioms example_6_35_psi_zero_is_minimal_for_Rf
