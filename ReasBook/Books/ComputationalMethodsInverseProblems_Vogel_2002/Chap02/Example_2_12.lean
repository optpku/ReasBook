/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_8.HarmonicDiagonal
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_10

public section

open scoped BigOperators ENNReal

noncomputable section

namespace RealL2

/-- Helper for Example 2.12: the truncated harmonic coefficient sequence is bounded. -/
lemma harmonicTruncWeights_memℓp (N : ℕ) :
    Memℓp (fun j : ℕ ↦ if j < N then 1 / ((j : ℝ) + 1) else 0) ∞ := by
  -- The truncation is uniformly bounded by the original harmonic bound `1`.
  refine memℓp_infty ?_
  refine ⟨1, ?_⟩
  rintro _ ⟨j, rfl⟩
  by_cases hj : j < N
  · have hnonneg : 0 ≤ (j : ℝ) + 1 := by
      positivity
    have hden : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      nlinarith
    have hbound : (1 / ((j : ℝ) + 1) : ℝ) ≤ 1 := by
      simpa using
        (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden)
    simpa [hj, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound
  · simp [hj]

/-- Helper for Example 2.12: the first `N` harmonic coefficients, padded by zeros, as an
`ℓ∞` vector. -/
def harmonicTruncWeights (N : ℕ) : lp (fun _ : ℕ ↦ ℝ) ∞ :=
  ⟨fun j ↦ if j < N then 1 / ((j : ℝ) + 1) else 0, harmonicTruncWeights_memℓp N⟩

/-- Helper for Example 2.12: the truncated coefficient sequence acts coordinatewise by the
expected cutoff formula. -/
theorem harmonicTruncWeights_apply (N j : ℕ) :
    harmonicTruncWeights N j = if j < N then 1 / ((j : ℝ) + 1) else 0 := by
  simp [harmonicTruncWeights]

/-- Helper for Example 2.12: the harmonic tail coefficient sequence is bounded. -/
lemma harmonicTailWeights_memℓp (N : ℕ) :
    Memℓp (fun j : ℕ ↦ if N ≤ j then 1 / ((j : ℝ) + 1) else 0) ∞ := by
  -- The tail keeps the same harmonic coordinates and zeros out the initial block.
  refine memℓp_infty ?_
  refine ⟨1, ?_⟩
  rintro _ ⟨j, rfl⟩
  by_cases hj : N ≤ j
  · have hnonneg : 0 ≤ (j : ℝ) + 1 := by
      positivity
    have hden : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      nlinarith
    have hbound : (1 / ((j : ℝ) + 1) : ℝ) ≤ 1 := by
      simpa using
        (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden)
    simpa [hj, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound
  · simp [hj]

/-- Helper for Example 2.12: the harmonic tail coefficients, viewed as an `ℓ∞` vector. -/
def harmonicTailWeights (N : ℕ) : lp (fun _ : ℕ ↦ ℝ) ∞ :=
  ⟨fun j ↦ if N ≤ j then 1 / ((j : ℝ) + 1) else 0, harmonicTailWeights_memℓp N⟩

/-- Helper for Example 2.12: the tail coefficient sequence acts by the expected cutoff formula. -/
theorem harmonicTailWeights_apply (N j : ℕ) :
    harmonicTailWeights N j = if N ≤ j then 1 / ((j : ℝ) + 1) else 0 := by
  simp [harmonicTailWeights]

/-- Helper for Example 2.12: the span of the first `N` coordinate vectors in real `ℓ²`. -/
def coordinateSpan (N : ℕ) : Submodule ℝ (lp (fun _ : ℕ ↦ ℝ) 2) :=
  Submodule.span ℝ (Set.range fun i : Fin N => deltaSequence (i : ℕ))

/-- Helper for Example 2.12: truncating the harmonic diagonal gives a bounded finite-coordinate
diagonal operator. -/
def harmonicDiagonalTrunc (N : ℕ) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  diagonal (harmonicTruncWeights N)

/-- Helper for Example 2.12: the truncated harmonic diagonal keeps the first `N` coordinates and
zeros out the tail. -/
theorem harmonicDiagonalTrunc_apply (N : ℕ) (f : lp (fun _ : ℕ ↦ ℝ) 2) (j : ℕ) :
    harmonicDiagonalTrunc N f j = (if j < N then 1 / ((j : ℝ) + 1) else 0) * f j := by
  simpa [harmonicDiagonalTrunc, harmonicTruncWeights_apply] using
    diagonal_apply (harmonicTruncWeights N) f j

/-- Helper for Example 2.12: the truncated harmonic diagonal is the sum of its coordinate-basis
pieces. -/
lemma harmonicDiagonalTrunc_eq_sum_single (N : ℕ) (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    harmonicDiagonalTrunc N f =
      Finset.sum (Finset.range N)
        (fun i ↦ (((1 / ((i : ℝ) + 1)) * f i) : ℝ) • deltaSequence i) := by
  -- Compare both sides on each coordinate and isolate the unique surviving basis term.
  ext j
  by_cases hj : j < N
  · have hmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
    have hsum :
        (((Finset.sum (Finset.range N)
            (fun i ↦ (((1 / ((i : ℝ) + 1)) * f i) : ℝ) • deltaSequence i)) :
          lp (fun _ : ℕ ↦ ℝ) 2) j) =
          (1 / ((j : ℝ) + 1)) * f j := by
      rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single_of_mem j hmem]
      · simp [deltaSequence_apply]
      · intro i hi hij
        simp [deltaSequence_apply, hij.symm]
    rw [harmonicDiagonalTrunc_apply]
    simpa [hj] using hsum.symm
  · have hnotmem : j ∉ Finset.range N := by
      simp [Finset.mem_range, hj]
    have hsum :
        (((Finset.sum (Finset.range N)
            (fun i ↦ (((1 / ((i : ℝ) + 1)) * f i) : ℝ) • deltaSequence i)) :
          lp (fun _ : ℕ ↦ ℝ) 2) j) = 0 := by
      rw [lp.coeFn_sum, Finset.sum_apply]
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hij : j ≠ i := by
        intro hji
        apply hnotmem
        simpa [hji] using hi
      simp [deltaSequence_apply, hij]
    rw [harmonicDiagonalTrunc_apply]
    simpa [hj] using hsum.symm

/-- Helper for Example 2.12: every truncated image lies in the span of the first `N`
coordinate vectors. -/
lemma harmonicDiagonalTrunc_mem_coordinateSpan (N : ℕ) (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    harmonicDiagonalTrunc N f ∈ coordinateSpan N := by
  -- Rewrite the truncation as a finite basis sum and place each term in the span.
  rw [harmonicDiagonalTrunc_eq_sum_single]
  refine Submodule.sum_mem (coordinateSpan N) ?_
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)

/-- Helper for Example 2.12: the finite coordinate span is finite-dimensional. -/
lemma coordinateSpan_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (coordinateSpan N) := by
  classical
  -- A span generated by finitely many coordinates is finite-dimensional.
  dsimp [coordinateSpan]
  exact
    FiniteDimensional.span_of_finite
      (K := ℝ) (V := lp (fun _ : ℕ ↦ ℝ) 2)
      (A := Set.range fun i : Fin N => deltaSequence (i : ℕ))
      (Set.finite_range fun i : Fin N => deltaSequence (i : ℕ))

/-- Helper for Example 2.12: each truncation has finite-dimensional range. -/
lemma harmonicDiagonalTrunc_range_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (harmonicDiagonalTrunc N).range := by
  let S := coordinateSpan N
  have hS : FiniteDimensional ℝ S := coordinateSpan_finiteDimensional N
  have hle : (harmonicDiagonalTrunc N).range ≤ S := by
    rintro _ ⟨f, rfl⟩
    exact harmonicDiagonalTrunc_mem_coordinateSpan N f
  -- Local instance justification (finite-dimensional codomain): `FiniteDimensional.of_injective`
  -- requires the finite-dimensional structure on the enclosing coordinate span.
  letI : FiniteDimensional ℝ S := hS
  have hInclusion :
      Function.Injective (Submodule.inclusion hle : (harmonicDiagonalTrunc N).range →ₗ[ℝ] S) := by
    intro x y hxy
    cases x
    cases y
    cases hxy
    rfl
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) hInclusion

/-- Helper for Example 2.12: each truncation is compact because its range is finite-dimensional.
-/
lemma harmonicDiagonalTrunc_isCompactOperator (N : ℕ) :
    IsCompactOperator (harmonicDiagonalTrunc N) := by
  -- Package the finite-dimensional range criterion from Exercise 2.10.
  exact ContinuousLinearMap.isCompactOperator_of_finiteDimensional_range
    (harmonicDiagonalTrunc N) (harmonicDiagonalTrunc_range_finiteDimensional N)

/-- Helper for Example 2.12: the harmonic diagonal differs from its truncation by the tail
diagonal. -/
lemma harmonicDiagonal_sub_harmonicDiagonalTrunc_eq_tailDiagonal (N : ℕ) :
    harmonicDiagonal - harmonicDiagonalTrunc N = diagonal (harmonicTailWeights N) := by
  -- Compare the two operators coordinatewise, separating the retained block from the tail.
  ext f j
  by_cases hj : N ≤ j
  · have hlt : ¬ j < N := Nat.not_lt.mpr hj
    rw [show (harmonicDiagonal - harmonicDiagonalTrunc N) f j =
        harmonicDiagonal f j - harmonicDiagonalTrunc N f j by rfl]
    rw [harmonicDiagonal_apply, harmonicDiagonalTrunc_apply, diagonal_apply]
    simp [harmonicTailWeights_apply, hj, hlt]
  · have hlt : j < N := Nat.lt_of_not_ge hj
    rw [show (harmonicDiagonal - harmonicDiagonalTrunc N) f j =
        harmonicDiagonal f j - harmonicDiagonalTrunc N f j by rfl]
    rw [harmonicDiagonal_apply, harmonicDiagonalTrunc_apply, diagonal_apply]
    simp [harmonicTailWeights_apply, hj, hlt]

/-- Helper for Example 2.12: each tail coordinate is bounded by the first omitted harmonic
coefficient. -/
lemma harmonicTailWeights_norm_apply_le (N j : ℕ) :
    ‖harmonicTailWeights N j‖ ≤ 1 / ((N : ℝ) + 1) := by
  -- Split on whether the coordinate lies in the retained tail and compare reciprocal bounds.
  by_cases hj : N ≤ j
  · rw [harmonicTailWeights_apply, if_pos hj, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpos : 0 < (N : ℝ) + 1 := by
      positivity
    have hden : (N : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hj
    exact one_div_le_one_div_of_le hpos hden
  · have hnonneg : 0 ≤ 1 / ((N : ℝ) + 1) := by
      positivity
    simpa [harmonicTailWeights_apply, hj] using hnonneg

/-- Helper for Example 2.12: every tail coefficient is bounded by the first omitted harmonic
coefficient. -/
lemma norm_harmonicTailWeights_le (N : ℕ) :
    ‖harmonicTailWeights N‖ ≤ 1 / ((N : ℝ) + 1) := by
  -- Rewrite the `ℓ∞` norm as a coordinate supremum and bound each coordinate separately.
  rw [lp.norm_eq_ciSup]
  change sSup (Set.range fun j : ℕ ↦ ‖harmonicTailWeights N j‖) ≤ 1 / ((N : ℝ) + 1)
  refine csSup_le (Set.range_nonempty fun j : ℕ ↦ ‖harmonicTailWeights N j‖) ?_
  intro b hb
  rcases hb with ⟨j, rfl⟩
  exact harmonicTailWeights_norm_apply_le N j

/-- Helper for Example 2.12: each coordinate multiplication map is controlled by the `ℓ∞`
norm of the coefficient sequence. -/
lemma mulCoordinateOpNorm_le_lpNorm (d : lp (fun _ : ℕ ↦ ℝ) ∞) (j : ℕ) :
    ‖ContinuousLinearMap.mul ℝ ℝ (d j)‖ ≤ ‖d‖ := by
  -- Rewrite the coefficient norm through the `ℓ∞` supremum description and take the `j`th term.
  rw [ContinuousLinearMap.opNorm_mul_apply, lp.norm_eq_ciSup]
  exact le_ciSup (memℓp_infty_iff.mp d.prop) j

/-- Helper for Example 2.12: a diagonal operator is bounded above by the `ℓ∞` norm of its
coefficient sequence. -/
lemma norm_diagonal_le (d : lp (fun _ : ℕ ↦ ℝ) ∞) :
    ‖diagonal d‖ ≤ ‖d‖ := by
  -- Rebuild the owner `lp.mapCLM` model of the diagonal operator and compare the two by ext.
  have hK : 0 ≤ ‖d‖ := norm_nonneg d
  let D : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
    lp.mapCLM 2 (fun j => ContinuousLinearMap.mul ℝ ℝ (d j))
      hK (mulCoordinateOpNorm_le_lpNorm d)
  have hD : diagonal d = D := by
    -- Both operators multiply each coordinate by the same scalar `d j`.
    ext f j
    rw [diagonal_apply]
    rfl
  rw [hD]
  exact lp.norm_mapCLM_le 2 (fun j => ContinuousLinearMap.mul ℝ ℝ (d j))
    hK (mulCoordinateOpNorm_le_lpNorm d)

/-- Helper for Example 2.12: each truncation is the target operator minus its tail error. -/
lemma harmonicDiagonalTrunc_eq_target_sub_error (N : ℕ) :
    harmonicDiagonalTrunc N = harmonicDiagonal - (harmonicDiagonal - harmonicDiagonalTrunc N) := by
  -- Expand both sides on each input coordinate and simplify the additive cancellation.
  ext f j
  rw [show (harmonicDiagonal - (harmonicDiagonal - harmonicDiagonalTrunc N)) f j =
      harmonicDiagonal f j - (harmonicDiagonal f j - harmonicDiagonalTrunc N f j) by rfl]
  ring

/-- Helper for Example 2.12: the truncation error is controlled by the first omitted harmonic
coefficient. -/
lemma norm_harmonicDiagonal_sub_harmonicDiagonalTrunc_le (N : ℕ) :
    ‖harmonicDiagonal - harmonicDiagonalTrunc N‖ ≤ 1 / ((N : ℝ) + 1) := by
  -- Rewrite the error as a tail diagonal and bound its operator norm by the tail `ℓ∞` norm.
  calc
    ‖harmonicDiagonal - harmonicDiagonalTrunc N‖ = ‖diagonal (harmonicTailWeights N)‖ := by
      rw [harmonicDiagonal_sub_harmonicDiagonalTrunc_eq_tailDiagonal N]
    _ ≤ ‖harmonicTailWeights N‖ := norm_diagonal_le (harmonicTailWeights N)
    _ ≤ 1 / ((N : ℝ) + 1) := norm_harmonicTailWeights_le N

/-- Example 2.12. The diagonal operator `harmonicDiagonal` from Example 2.8 is a compact operator
on real `ℓ²`. -/
theorem harmonicDiagonal_isCompactOperator : IsCompactOperator harmonicDiagonal := by
  -- The tail estimate turns the finite-rank truncations into an operator-norm approximation.
  have herror :
      Filter.Tendsto (fun N ↦ harmonicDiagonal - harmonicDiagonalTrunc N) Filter.atTop
        (nhds (0 : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero
      (fun N ↦ norm_nonneg _)
      (fun N ↦ norm_harmonicDiagonal_sub_harmonicDiagonalTrunc_le N)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have htrunc :
      Filter.Tendsto harmonicDiagonalTrunc Filter.atTop (nhds harmonicDiagonal) := by
    -- Reconstruct the truncations from the convergent error sequence by subtraction from the
    -- target operator.
    have hconst :
        Filter.Tendsto
          (fun _ : ℕ ↦ harmonicDiagonal) Filter.atTop (nhds harmonicDiagonal) := by
      exact tendsto_const_nhds
    have haux :
        Filter.Tendsto (fun N ↦ harmonicDiagonal - (harmonicDiagonal - harmonicDiagonalTrunc N))
          Filter.atTop (nhds (harmonicDiagonal - 0)) := by
      exact hconst.sub herror
    convert haux using 1
    · ext N f j
      exact congrArg (fun T => T f j) (harmonicDiagonalTrunc_eq_target_sub_error N)
    · simp
  have hcompact :
      ∀ᶠ N in Filter.atTop, IsCompactOperator (harmonicDiagonalTrunc N) := by
    exact Filter.Eventually.of_forall (fun N ↦ harmonicDiagonalTrunc_isCompactOperator N)
  -- The compact operators are closed in operator norm.
  exact isCompactOperator_of_tendsto htrunc hcompact

end RealL2
