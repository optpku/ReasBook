/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Gershgorin

open Matrix

-- Semantic recall: `eigenvalue_mem_ball` in
-- `Mathlib.LinearAlgebra.Matrix.Gershgorin` is the canonical Gershgorin API for clause (1).
-- Semantic recall: `Matrix.IsHermitian.eigenvalues` is the source-facing owner for Hermitian
-- spectral statements in this chapter. The real matrix spectrum and `A.mulVecLin` spectrum are
-- companion bridge views, related by `hA.spectrum_real_eq_range_eigenvalues`.

section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n]

/-- Lower endpoint of the Gershgorin interval enclosure determined by the rows of a finite square
matrix over an `RCLike` field. -/
noncomputable def gershgorinLowerBound (A : Matrix n n 𝕜) : ℝ :=
  let _ : DecidableEq n := Classical.decEq n
  sInf (Set.range fun i : n ↦
    RCLike.re (A i i) - Finset.sum (Finset.univ.erase i) (fun j ↦ ‖A i j‖))

/-- Upper endpoint of the Gershgorin interval enclosure determined by the rows of a finite square
matrix over an `RCLike` field. -/
noncomputable def gershgorinUpperBound (A : Matrix n n 𝕜) : ℝ :=
  let _ : DecidableEq n := Classical.decEq n
  sSup (Set.range fun i : n ↦
    RCLike.re (A i i) + Finset.sum (Finset.univ.erase i) (fun j ↦ ‖A i j‖))

/- Chapter01 Theorem 1.2.14 (1): every eigenvalue of a complex square matrix lies in one of its
Gershgorin disks. This is exactly `eigenvalue_mem_ball`. -/
#check eigenvalue_mem_ball

/-- Helper for Chapter01 Theorem 1.2.14: a real point in a closed ball over an `RCLike` field lies
between the corresponding real interval endpoints. -/
lemma real_bounds_of_mem_closedBall
    {z : 𝕜} {x r : ℝ} (hx : (x : 𝕜) ∈ Metric.closedBall z r) :
    RCLike.re z - r ≤ x ∧ x ≤ RCLike.re z + r := by
  -- Convert the closed-ball membership into a norm inequality on `x - z`.
  have hnorm : ‖(x : 𝕜) - z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  -- The real part is controlled by the norm, so the ball yields the desired interval bounds.
  have habs : |x - RCLike.re z| ≤ r := by
    calc
      |x - RCLike.re z| = |RCLike.re ((x : 𝕜) - z)| := by simp
      _ ≤ ‖(x : 𝕜) - z‖ := RCLike.abs_re_le_norm _
      _ ≤ r := hnorm
  constructor
  · have hleft := (abs_le.mp habs).1
    linarith
  · have hright := (abs_le.mp habs).2
    linarith

/-- Helper for Chapter01 Theorem 1.2.14: `mulVecLin` and the matrix itself have the same real
spectrum. -/
lemma spectrum_real_mulVecLin_eq_spectrum_real_matrix [DecidableEq n] (A : Matrix n n 𝕜) :
    spectrum ℝ A.mulVecLin = spectrum ℝ A := by
  -- Route correction: compare both sides after base change from `ℝ` to `𝕜`.
  ext x
  constructor
  · intro hx
    have hxLin : (x : 𝕜) ∈ spectrum 𝕜 A.mulVecLin :=
      (spectrum.algebraMap_mem_iff 𝕜).2 hx
    have hxMatrix : (x : 𝕜) ∈ spectrum 𝕜 A := by
      rw [← Matrix.toLin'_apply' A, Matrix.spectrum_toLin'] at hxLin
      exact hxLin
    exact (spectrum.algebraMap_mem_iff 𝕜).1 hxMatrix
  · intro hx
    have hxMatrix : (x : 𝕜) ∈ spectrum 𝕜 A :=
      (spectrum.algebraMap_mem_iff 𝕜).2 hx
    have hxLin : (x : 𝕜) ∈ spectrum 𝕜 A.mulVecLin := by
      rw [← Matrix.toLin'_apply' A, Matrix.spectrum_toLin']
      exact hxMatrix
    exact (spectrum.algebraMap_mem_iff 𝕜).1 hxLin

/-- Chapter01 Theorem 1.2.14 (2): every ordered Hermitian eigenvalue is bounded below by the lower
Gershgorin interval endpoint. -/
theorem gershgorinLowerBound_le_eigenvalue
    [DecidableEq n] (A : Matrix n n 𝕜) (hA : A.IsHermitian) (i : n) :
    gershgorinLowerBound A ≤ hA.eigenvalues i := by
  let rowLower : n → ℝ := fun k ↦
    RCLike.re (A k k) - Finset.sum (Finset.univ.erase k) (fun j ↦ ‖A k j‖)
  -- Move the real Hermitian eigenvalue into the ambient `𝕜`-spectrum so Gershgorin applies.
  have hEig : Module.End.HasEigenvalue A.toLin' (hA.eigenvalues i : 𝕜) := by
    have hMemMatrix : (hA.eigenvalues i : 𝕜) ∈ spectrum 𝕜 A := by
      exact (spectrum.algebraMap_mem_iff 𝕜).2 (hA.eigenvalues_mem_spectrum_real i)
    have hMemLin : (hA.eigenvalues i : 𝕜) ∈ spectrum 𝕜 A.toLin' := by
      simpa using hMemMatrix
    apply Module.End.HasEigenvalue.of_mem_spectrum
    exact hMemLin
  -- Gershgorin gives a witness row whose disk contains the eigenvalue.
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hEig
  have hkBounds := real_bounds_of_mem_closedBall hk
  have hLowerRow : gershgorinLowerBound A ≤ rowLower k := by
    have hcsInf : sInf (Set.range rowLower) ≤ rowLower k :=
      csInf_le (Finite.bddBelow_range rowLower) ⟨k, rfl⟩
    simpa [gershgorinLowerBound, rowLower] using hcsInf
  -- The chosen row endpoint bounds the eigenvalue from below, so the global infimum does too.
  exact hLowerRow.trans hkBounds.1

/-- Companion least-eigenvalue view for Chapter01 Theorem 1.2.14 (2). -/
theorem gershgorinLowerBound_le_sInf_eigenvalues
    [DecidableEq n] (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    gershgorinLowerBound A ≤ sInf (Set.range hA.eigenvalues) := by
  rcases isEmpty_or_nonempty n with hEmpty | hNonempty
  · letI := hEmpty
    have hRangeEmpty : ∀ f : n → ℝ, Set.range f = (∅ : Set ℝ) := by
      intro f
      ext x
      constructor
      · intro hx
        rcases hx with ⟨i, rfl⟩
        exact (hEmpty.false i).elim
      · intro hx
        simp at hx
    -- When there are no indices, both ranges are empty and both conditional bounds collapse.
    simp [gershgorinLowerBound, hRangeEmpty]
  · letI := hNonempty
    -- In the nonempty case, every eigenvalue satisfies the pointwise lower bound.
    refine le_csInf (Set.range_nonempty hA.eigenvalues) ?_
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact gershgorinLowerBound_le_eigenvalue A hA i

/-- Companion bridge for Chapter01 Theorem 1.2.14 (2): the same lower bound written with the real
matrix spectrum. -/
theorem gershgorinLowerBound_le_sInf_spectrum_real
    [DecidableEq n] (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    gershgorinLowerBound A ≤ sInf (spectrum ℝ A) := by
  simpa [hA.spectrum_real_eq_range_eigenvalues] using
    gershgorinLowerBound_le_sInf_eigenvalues A hA

/-- Companion bridge for Chapter01 Theorem 1.2.14 (2): the same lower bound written with the real
spectrum of `A.mulVecLin`. -/
theorem gershgorinLowerBound_le_sInf_spectrum_mulVecLin
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    gershgorinLowerBound A ≤ sInf (spectrum ℝ A.mulVecLin) := by
  classical
  -- Transport the already-proved matrix-spectrum bound across the `mulVecLin` spectrum identity.
  simpa [spectrum_real_mulVecLin_eq_spectrum_real_matrix A] using
    (gershgorinLowerBound_le_sInf_spectrum_real A hA)

/-- Chapter01 Theorem 1.2.14 (3): every ordered Hermitian eigenvalue is bounded above by the upper
Gershgorin interval endpoint. -/
theorem eigenvalue_le_gershgorinUpperBound
    [DecidableEq n] (A : Matrix n n 𝕜) (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i ≤ gershgorinUpperBound A := by
  let rowUpper : n → ℝ := fun k ↦
    RCLike.re (A k k) + Finset.sum (Finset.univ.erase k) (fun j ↦ ‖A k j‖)
  -- Move the real Hermitian eigenvalue into the ambient `𝕜`-spectrum so Gershgorin applies.
  have hEig : Module.End.HasEigenvalue A.toLin' (hA.eigenvalues i : 𝕜) := by
    have hMemMatrix : (hA.eigenvalues i : 𝕜) ∈ spectrum 𝕜 A := by
      exact (spectrum.algebraMap_mem_iff 𝕜).2 (hA.eigenvalues_mem_spectrum_real i)
    have hMemLin : (hA.eigenvalues i : 𝕜) ∈ spectrum 𝕜 A.toLin' := by
      simpa using hMemMatrix
    apply Module.End.HasEigenvalue.of_mem_spectrum
    exact hMemLin
  -- Gershgorin gives a witness row whose disk contains the eigenvalue.
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hEig
  have hkBounds := real_bounds_of_mem_closedBall hk
  have hUpperRow : rowUpper k ≤ gershgorinUpperBound A := by
    have hcsSup : rowUpper k ≤ sSup (Set.range rowUpper) :=
      le_csSup (Finite.bddAbove_range rowUpper) ⟨k, rfl⟩
    simpa [gershgorinUpperBound, rowUpper] using hcsSup
  -- The chosen row endpoint bounds the eigenvalue from above, so the global supremum does too.
  exact hkBounds.2.trans hUpperRow

/-- Companion greatest-eigenvalue view for Chapter01 Theorem 1.2.14 (3). -/
theorem sSup_eigenvalues_le_gershgorinUpperBound
    [DecidableEq n] (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    sSup (Set.range hA.eigenvalues) ≤ gershgorinUpperBound A := by
  rcases isEmpty_or_nonempty n with hEmpty | hNonempty
  · letI := hEmpty
    have hRangeEmpty : ∀ f : n → ℝ, Set.range f = (∅ : Set ℝ) := by
      intro f
      ext x
      constructor
      · intro hx
        rcases hx with ⟨i, rfl⟩
        exact (hEmpty.false i).elim
      · intro hx
        simp at hx
    -- When there are no indices, both ranges are empty and both conditional bounds collapse.
    simp [gershgorinUpperBound, hRangeEmpty]
  · letI := hNonempty
    -- In the nonempty case, every eigenvalue satisfies the pointwise upper bound.
    refine csSup_le (Set.range_nonempty hA.eigenvalues) ?_
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact eigenvalue_le_gershgorinUpperBound A hA i

/-- Companion bridge for Chapter01 Theorem 1.2.14 (3): the same upper bound written with the real
matrix spectrum. -/
theorem sSup_spectrum_real_le_gershgorinUpperBound
    [DecidableEq n] (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    sSup (spectrum ℝ A) ≤ gershgorinUpperBound A := by
  simpa [hA.spectrum_real_eq_range_eigenvalues] using
    sSup_eigenvalues_le_gershgorinUpperBound A hA

/-- Companion bridge for Chapter01 Theorem 1.2.14 (3): the same upper bound written with the real
spectrum of `A.mulVecLin`. -/
theorem sSup_spectrum_mulVecLin_le_gershgorinUpperBound
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    sSup (spectrum ℝ A.mulVecLin) ≤ gershgorinUpperBound A := by
  classical
  -- Transport the already-proved matrix-spectrum bound across the `mulVecLin` spectrum identity.
  simpa [spectrum_real_mulVecLin_eq_spectrum_real_matrix A] using
    (sSup_spectrum_real_le_gershgorinUpperBound A hA)

end
