/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_lemma_6_4.Comparison
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_lemma_6_4.Inequalities

open scoped Matrix

section Lemma64

variable {I : Type} [Finite I] {n : ℕ}

omit [Finite I] in
/-- Helper for Lemma 6.4: changing one nonbasic
coefficient translates its tableau point along the corresponding tableau ray. -/
private lemma gomoryCornerNonbasicPoint_addSingle
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    (μ : Fin n → ℝ)
    (j : Fin n)
    (a : ℝ) :
    gomory_corner_nonbasic_point abar bbar (μ + a • Pi.single j (1 : ℝ)) =
      gomory_corner_nonbasic_point abar bbar μ + a • tableauCornerRay abar j := by
  classical
  -- Separate the old ray combination from the newly added coordinate contribution.
  unfold gomory_corner_nonbasic_point
  simp only [Pi.add_apply, add_smul]
  rw [Finset.sum_add_distrib]
  have hsingle :
      (∑ k : Fin n, (a • (Pi.single j (1 : ℝ) : Fin n → ℝ)) k •
        tableauCornerRay abar k) =
        a • tableauCornerRay abar j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [Ne.symm hkj]
    · simp
  rw [hsingle]
  abel

omit [Finite I] in
/-- Helper for Lemma 6.4: the common denominator of
a tableau column clears every basic coordinate of its corresponding tableau ray. -/
private lemma tableauColumnDenominator_smulRay_memLattice
    [Fintype I]
    (abar : I → Fin n → ℚ)
    (j : Fin n) :
    ((tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j) ∈
      tableau_mixed_integer_lattice := by
  intro i
  -- The selected rational coordinate denominator divides the column-wide least common multiple.
  have hden_dvd :
      (abar i j).den ∣ tableauColumnDenominator abar j := by
    rw [tableauColumnDenominator, rational_vector_common_denominator]
    simpa [tableauColumn] using
      (Finset.dvd_lcm
        (s := Finset.univ)
        (f := fun k : Fin (Fintype.card I) ↦ (tableauColumn abar j k).den)
        (Finset.mem_univ (Fintype.equivFin I i)))
  rcases hden_dvd with ⟨t, ht⟩
  refine ⟨-((t : ℤ) * (abar i j).num), ?_⟩
  -- Clear the selected rational coordinate first in `ℚ`, then transport the identity to `ℝ`.
  have hcleared_rat :
      (tableauColumnDenominator abar j : ℚ) * abar i j =
        (((t : ℤ) * (abar i j).num : ℤ) : ℚ) := by
    rw [ht, Nat.cast_mul]
    calc
      ((abar i j).den : ℚ) * (t : ℚ) * abar i j =
          (t : ℚ) * (abar i j * (abar i j).den) := by ring
      _ = (t : ℚ) * (abar i j).num := by
            rw [Rat.mul_den_eq_num]
      _ = (((t : ℤ) * (abar i j).num : ℤ) : ℚ) := by
            norm_num
  have hcleared_real :
      (tableauColumnDenominator abar j : ℝ) * (abar i j : ℝ) =
        (((t : ℤ) * (abar i j).num : ℤ) : ℝ) := by
    exact_mod_cast hcleared_rat
  calc
    ((tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j) (Sum.inl i)
        = (tableauColumnDenominator abar j : ℝ) * (-(abar i j : ℝ)) := by
            rw [Pi.smul_apply, tableauCornerRay_apply_inl, smul_eq_mul]
    _ = -(((t : ℤ) * (abar i j).num : ℤ) : ℝ) := by
          rw [mul_neg, hcleared_real]
    _ = ((-((t : ℤ) * (abar i j).num) : ℤ) : ℝ) := by
          norm_num

omit [Finite I] in
/-- Helper for Lemma 6.4: adding a natural multiple
of a denominator-cleared coordinate direction preserves the raw nonbasic generators. -/
private lemma gomoryCornerNonbasicGenerator_addDenominatorMultiple
    [Fintype I]
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    (μ : Fin n → ℝ)
    (hμ : μ ∈ gomory_corner_nonbasic_generators abar bbar)
    (j : Fin n)
    (k : ℕ) :
    μ + ((k : ℝ) * (tableauColumnDenominator abar j : ℝ)) • Pi.single j (1 : ℝ) ∈
      gomory_corner_nonbasic_generators abar bbar := by
  classical
  rcases hμ with ⟨hμ_nonneg, hμ_lattice⟩
  constructor
  · -- Only the selected coordinate changes, and it changes by a nonnegative amount.
    intro i
    by_cases hij : i = j
    · subst i
      simpa using
        add_nonneg (hμ_nonneg j)
          (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg (tableauColumnDenominator abar j)))
    · simpa [hij] using hμ_nonneg i
  · -- The associated tableau point changes by an integer multiple of a cleared lattice ray.
    rw [gomoryCornerNonbasicPoint_addSingle]
    refine add_mem_tableau_mixed_integer_lattice hμ_lattice ?_
    simpa only [Int.cast_natCast, smul_smul] using
      intCast_smul_mem_tableau_mixed_integer_lattice (k : ℤ)
        (tableauColumnDenominator_smulRay_memLattice abar j)

/-- Helper for Lemma 6.4: the nonbasic corner
polyhedron is closed under every nonnegative coordinate direction. -/
private lemma gomoryCornerNonbasicPolyhedron_addNonnegativeSingle
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    {x : Fin n → ℝ}
    (hx : x ∈ gomory_corner_nonbasic_polyhedron abar bbar)
    (j : Fin n)
    (a : ℝ)
    (ha : 0 ≤ a) :
    x + a • Pi.single j (1 : ℝ) ∈ gomory_corner_nonbasic_polyhedron abar bbar := by
  classical
  -- Local instance justification (finite enumeration): denominator clearing requires an
  -- enumeration of the finite basic index type.
  let _ : Fintype I := Fintype.ofFinite I
  rw [gomory_corner_nonbasic_polyhedron] at hx ⊢
  let e : Fin n → ℝ := Pi.single j (1 : ℝ)
  let S := gomory_corner_nonbasic_generators abar bbar
  have htranslated_generators :
      S ⊆ (fun y : Fin n → ℝ ↦ y + a • e) ⁻¹' convexHull ℝ S := by
    intro μ hμ
    have hD : 0 < (tableauColumnDenominator abar j : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (tableauColumnDenominator_ne_zero abar j)
    obtain ⟨k, hk⟩ := exists_nat_gt (a / (tableauColumnDenominator abar j : ℝ))
    have hk_pos : 0 < (k : ℝ) := by
      exact lt_of_le_of_lt (div_nonneg ha hD.le) hk
    have hstep_pos :
        0 < (k : ℝ) * (tableauColumnDenominator abar j : ℝ) :=
      mul_pos hk_pos hD
    have ha_le_step :
        a ≤ (k : ℝ) * (tableauColumnDenominator abar j : ℝ) := by
      exact (div_le_iff₀ hD).mp hk.le
    have hbase : μ ∈ convexHull ℝ S := subset_convexHull ℝ S hμ
    have hshift :
        μ + ((k : ℝ) * (tableauColumnDenominator abar j : ℝ)) • e ∈
          convexHull ℝ S := by
      exact subset_convexHull ℝ S
        (gomoryCornerNonbasicGenerator_addDenominatorMultiple abar bbar μ hμ j k)
    have hratio :
        a / ((k : ℝ) * (tableauColumnDenominator abar j : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨div_nonneg ha hstep_pos.le, (div_le_one hstep_pos).2 ha_le_step⟩
    have hinterp :=
      (convex_convexHull ℝ S).add_smul_mem hbase hshift hratio
    simpa only [e, smul_smul, div_mul_cancel₀ a hstep_pos.ne'] using hinterp
  -- The translated preimage is convex, so generator closure extends to the full convex hull.
  exact
    (convexHull_min htranslated_generators
      ((convex_convexHull ℝ S).translate_preimage_left (a • e))) hx

/-- Helper for Lemma 6.4: validity on a nonempty set
closed under nonnegative coordinate rays forces every coefficient of a lower inequality to be
nonnegative. -/
private lemma validGeInequalityCoeffNonnegOfCoordinateRays
    {C : Set (Fin n → ℝ)}
    (hC_nonempty : C.Nonempty)
    (hC_coordinate_ray :
      ∀ j : Fin n, ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → ∀ a : ℝ, 0 ≤ a →
        x + a • Pi.single j (1 : ℝ) ∈ C)
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
    -- Validity at the anchor makes the numerator positive, while `γ j < 0` makes the
    -- denominator positive.
    have hnum_nonneg : 0 ≤ γ ⬝ᵥ x₀ - δ + 1 := by
      linarith [hvalid hx₀]
    have hden_nonneg : 0 ≤ -γ j := by
      linarith
    dsimp [a]
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

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_1/ch6_sec6_1_lemma_6_4.lean

Lemma 6.4. Assume `corner(B)` is nonempty. Every nontrivial valid inequality for `corner(B)`
can be written in the form `γ' ⬝ᵥ x_N ≥ 1` with `γ' ≥ 0`, where `x_N` denotes the
nonbasic-coordinate point of `corner(B)`. This statement uses the source-facing owner
`gomory_corner_nonbasic_polyhedron abar bbar`, and records the normalized coefficients of the
given inequality explicitly as `δ⁻¹ • γ`. -/
theorem corner_polyhedron_nontrivial_valid_inequality_normal_form
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    (hcorner_nonempty : (gomory_corner_nonbasic_polyhedron abar bbar).Nonempty)
    (γ : Fin n → ℝ)
    (δ : ℝ)
    (hineq :
      IsNontrivialValidGeInequality (gomory_corner_nonbasic_polyhedron abar bbar) γ δ) :
    (∀ j : Fin n, 0 ≤ (δ⁻¹ • γ) j) ∧
      ∀ ⦃x : Fin n → ℝ⦄,
        x ∈ gomory_corner_nonbasic_polyhedron abar bbar →
          1 ≤ (δ⁻¹ • γ) ⬝ᵥ x := by
  -- First use the coordinate recession directions to force all original coefficients nonnegative.
  have hγ_nonneg : ∀ j : Fin n, 0 ≤ γ j :=
    validGeInequalityCoeffNonnegOfCoordinateRays hcorner_nonempty
      (fun j x hx a ha ↦
        gomoryCornerNonbasicPolyhedron_addNonnegativeSingle abar bbar hx j a ha)
      hineq.valid
  have hδ_pos : 0 < δ := by
    -- Otherwise coefficientwise nonnegativity would make the inequality valid on the entire
    -- nonnegative orthant, contradicting nontriviality.
    by_contra hδ
    have hδ_nonpos : δ ≤ 0 := le_of_not_gt hδ
    apply hineq.not_validOnNonnegativeOrthant
    intro x hx_nonneg
    have hdot_nonneg : 0 ≤ γ ⬝ᵥ x :=
      dotProduct_nonneg_of_nonneg hγ_nonneg hx_nonneg
    exact hδ_nonpos.trans hdot_nonneg
  constructor
  · -- Positive inverse scaling preserves the sign of every coefficient.
    intro j
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hδ_pos.le) (hγ_nonneg j)
  · intro x hx
    -- Multiply validity by `δ⁻¹` and normalize the positive right-hand side to one.
    have hscaled :=
      mul_le_mul_of_nonneg_left (hineq.valid hx) (inv_nonneg.mpr hδ_pos.le)
    simpa [smul_dotProduct, hδ_pos.ne'] using hscaled

end Lemma64
