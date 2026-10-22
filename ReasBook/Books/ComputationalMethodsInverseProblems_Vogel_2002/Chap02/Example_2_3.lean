/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_3.Diagonal
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

open scoped ENNReal

/- Example 2.3 (1). Mathlib's canonical owner for the real Hilbert sequence space
`ℓ²(ℝ)` is `lp (fun _ : ℕ ↦ ℝ) 2`.
-/
#check lp (fun _ : ℕ ↦ ℝ) 2

namespace RealL2

/-- For Example 2.3, the inner product on `lp (fun _ : ℕ ↦ ℝ) 2` is
`∑' j, f j * g j`. -/
theorem inner_eq_tsum (f g : lp (fun _ : ℕ ↦ ℝ) 2) :
    inner ℝ f g = ∑' j, f j * g j := by
  have h : inner ℝ f g = ∑' j, inner ℝ (f j) (g j) :=
    lp.inner_eq_tsum f g
  simpa [Real.inner_apply, mul_comm] using h

/-- For Example 2.3, the induced norm on `lp (fun _ : ℕ ↦ ℝ) 2` is
`Real.sqrt (∑' j, (f j)^2)`. -/
theorem norm_eq_sqrt_tsum_sq (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    ‖f‖ = Real.sqrt (∑' j, (f j) ^ (2 : ℕ)) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  calc
    ‖f‖ = (∑' j, ‖f j‖ ^ ((2 : ℝ≥0∞).toReal : ℝ)) ^ (1 / ((2 : ℝ≥0∞).toReal : ℝ)) := by
      simpa using lp.norm_eq_tsum_rpow hp f
    _ = Real.sqrt (∑' j, ‖f j‖ ^ (2 : ℕ)) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    _ = Real.sqrt (∑' j, (f j) ^ (2 : ℕ)) := by
      congr with j
      rw [Real.norm_eq_abs, sq_abs]

/-- The canonical bounded diagonal operator attached to a coefficient sequence in `Memℓp d ∞`. -/
noncomputable def diagonalOfMem (d : ℕ → ℝ) (hd : Memℓp d ∞) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  diagonal ⟨d, hd⟩

/-- `diagonalOfMem` acts by coordinatewise multiplication. -/
theorem diagonalOfMem_apply (d : ℕ → ℝ) (hd : Memℓp d ∞) (f : lp (fun _ : ℕ ↦ ℝ) 2) (j : ℕ) :
    diagonalOfMem d hd f j = d j * f j :=
  diagonal_apply ⟨d, hd⟩ f j

/-- A bounded coefficient sequence on real `ℓ²` defines a bounded diagonal operator. -/
theorem exists_diagonal_of_memℓp {d : ℕ → ℝ} (hd : Memℓp d ∞) :
    ∃ D : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2, ∀ f j, D f j = d j * f j := by
  exact ⟨diagonalOfMem d hd, diagonalOfMem_apply d hd⟩

/-- A coordinatewise diagonal operator on real `ℓ²` has uniformly bounded coefficients. -/
theorem memℓp_infty_of_exists_diagonal {d : ℕ → ℝ}
    (hD : ∃ D : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2, ∀ f j, D f j = d j * f j) :
    Memℓp d ∞ := by
  rw [memℓp_infty_iff]
  rcases hD with ⟨D, hD⟩
  refine ⟨‖D‖, ?_⟩
  rintro _ ⟨j, rfl⟩
  let e : lp (fun _ : ℕ ↦ ℝ) 2 := lp.single 2 j (1 : ℝ)
  have hsingle : ‖e‖ = ‖(1 : ℝ)‖ := by
    have hp : 0 < ((2 : ℝ≥0∞).toReal : ℝ) := by norm_num
    have htsum :
        (∑' b, ‖e b‖ ^ ((2 : ℝ≥0∞).toReal : ℝ)) = ‖e j‖ ^ ((2 : ℝ≥0∞).toReal : ℝ) := by
      refine tsum_eq_single j ?_
      intro b hb
      simp [e, hb]
    calc
      ‖e‖ = (∑' b, ‖e b‖ ^ ((2 : ℝ≥0∞).toReal : ℝ)) ^ (1 / ((2 : ℝ≥0∞).toReal : ℝ)) := by
        simpa using lp.norm_eq_tsum_rpow hp e
      _ = (‖e j‖ ^ ((2 : ℝ≥0∞).toReal : ℝ)) ^ (1 / ((2 : ℝ≥0∞).toReal : ℝ)) := by
        rw [htsum]
      _ = ‖e j‖ := by
        rw [one_div, Real.rpow_rpow_inv _ hp.ne']
        exact norm_nonneg _
      _ = ‖(1 : ℝ)‖ := by
        simp [e]
  rw [norm_one] at hsingle
  calc
    ‖d j‖ = ‖D e j‖ := by
      congr 1
      simpa [e] using (hD e j).symm
    _ ≤ ‖D e‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖D‖ * ‖e‖ := D.le_opNorm _
    _ = ‖D‖ := by rw [hsingle, mul_one]

/-- For Example 2.3, a coordinatewise diagonal operator on real `ℓ²` is bounded exactly when
the coefficient sequence lies in `Memℓp d ∞`. -/
theorem diagonal_bounded_iff (d : ℕ → ℝ) :
    (∃ D : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2, ∀ f j, D f j = d j * f j) ↔
      Memℓp d ∞ := by
  constructor
  · exact memℓp_infty_of_exists_diagonal
  · exact exists_diagonal_of_memℓp

/-- Helper for Example 2.3: each coordinate multiplication map is bounded by the `ℓ∞` norm of
the coefficient sequence. -/
lemma mulCoordinateOpNorm_le (d : lp (fun _ : ℕ ↦ ℝ) ∞) (j : ℕ) :
    ‖ContinuousLinearMap.mul ℝ ℝ (d j)‖ ≤ ‖d‖ := by
  -- Rewrite both sides into the coordinate norm comparison packaged by `lp.norm_eq_ciSup`.
  rw [ContinuousLinearMap.opNorm_mul_apply, lp.norm_eq_ciSup]
  exact le_ciSup (memℓp_infty_iff.mp d.prop) j

/-- Helper for Example 2.3: each diagonal coefficient is controlled by the diagonal operator norm.
-/
lemma coordinateNorm_le_diagonalNorm (d : lp (fun _ : ℕ ↦ ℝ) ∞) (j : ℕ) :
    ‖d j‖ ≤ ‖diagonal d‖ := by
  have hp : 0 < (2 : ℝ≥0∞) := by norm_num
  let e : lp (fun _ : ℕ ↦ ℝ) 2 := lp.single 2 j (1 : ℝ)
  -- The basis vector `e_j` has unit norm in real `ℓ²`.
  have he : ‖e‖ = 1 := by
    simp [e, hp]
  -- The diagonal operator rescales `e_j` by the coefficient `d j`.
  have hDe : diagonal d e = lp.single 2 j (d j) := by
    ext k
    by_cases hk : k = j
    · subst hk
      rw [diagonal_apply]
      simp [e]
    · rw [diagonal_apply]
      simp [e, hk]
  -- Compare norms using the operator norm inequality on the unit basis vector.
  have hnorm : ‖diagonal d e‖ = ‖d j‖ := by
    rw [hDe]
    simp [hp]
  calc
    ‖d j‖ = ‖diagonal d e‖ := hnorm.symm
    _ ≤ ‖diagonal d‖ * ‖e‖ := (diagonal d).le_opNorm e
    _ = ‖diagonal d‖ := by rw [he, mul_one]

/-- Helper for Example 2.3: the real diagonal operator is symmetric on `ℓ²`. -/
lemma diagonalIsSymmetric (d : lp (fun _ : ℕ ↦ ℝ) ∞) :
    ((diagonal d : lp (fun _ : ℕ ↦ ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ ↦ ℝ) 2).IsSymmetric) := by
  intro f g
  -- Expand both inner products into coordinate sums and compare the summands pointwise.
  rw [inner_eq_tsum, inner_eq_tsum]
  refine tsum_congr fun j ↦ ?_
  simpa [diagonal_apply] using (show d j * f j * g j = f j * (d j * g j) by ring)

/-- Example 2.3. The operator norm of the bounded diagonal operator equals the `lp ... ∞`
norm of its coefficient sequence. -/
theorem norm_diagonal (d : lp (fun _ : ℕ ↦ ℝ) ∞) :
    ‖diagonal d‖ = ‖d‖ := by
  have hK : 0 ≤ ‖d‖ := norm_nonneg d
  let D : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
    lp.mapCLM 2 (fun j => ContinuousLinearMap.mul ℝ ℝ (d j)) hK (mulCoordinateOpNorm_le d)
  have hD : diagonal d = D := by
    ext f j
    rw [diagonal_apply]
    rfl
  apply le_antisymm
  · -- The diagonal operator inherits the uniform coordinate bound from `d`.
    rw [hD]
    exact lp.norm_mapCLM_le 2
      (fun j => ContinuousLinearMap.mul ℝ ℝ (d j))
      hK
      (mulCoordinateOpNorm_le d)
  · -- Testing on each basis vector recovers every coefficient from the operator norm.
    rw [lp.norm_eq_ciSup]
    change sSup (Set.range fun j : ℕ ↦ ‖d j‖) ≤ ‖diagonal d‖
    refine csSup_le (Set.range_nonempty (fun j : ℕ ↦ ‖d j‖)) ?_
    intro b hb
    rcases hb with ⟨j, rfl⟩
    exact coordinateNorm_le_diagonalNorm d j

/-- For Example 2.3, a real bounded diagonal operator on `lp (fun _ : ℕ ↦ ℝ) 2`
is self-adjoint. -/
theorem isSelfAdjoint_diagonal (d : lp (fun _ : ℕ ↦ ℝ) ∞) :
    IsSelfAdjoint (diagonal d) := by
  -- Symmetry on the real inner product space is the stable route to self-adjointness.
  exact (diagonalIsSymmetric d).isSelfAdjoint

end RealL2
