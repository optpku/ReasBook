/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_9
import Mathlib.Analysis.Matrix.Spectrum

open ContinuousLinearMap

-- Source/core/bridge triage for this file:
-- * source-facing owner: `rayleighQuotient` from `Definition_1_2_9`
-- * core/canonical owner: `ContinuousLinearMap.rayleighQuotient`
-- * bridge/view kept here: `A.toEuclideanLin.toContinuousLinearMap`, comparing the matrix
--   quotient with the canonical Euclidean Hermitian Rayleigh quotient on
--   `EuclideanSpace ℂ (Fin n)`
--
-- This file extends the chapter's matrix-side Rayleigh quotient owner with the extremal-value
-- statements of Theorem 1.2.10 on the canonical Euclidean space `EuclideanSpace ℂ (Fin n)`.

/-- Helper for Chapter01 Theorem 1.2.10: for a Hermitian matrix, the symmetric Euclidean quadratic
form of `A.toEuclideanLin` agrees with the matrix quadratic form `uᴴ A u`. -/
lemma toEuclideanLin_reApplyInnerSelf_eq_dotProduct_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (u : EuclideanSpace ℂ (Fin n)) :
    (((A.toEuclideanLin.toContinuousLinearMap).reApplyInnerSelf u : ℂ)) =
      dotProduct (star u.ofLp) (A.mulVec u.ofLp) := by
  have hSymm : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hself :
      (((A.toEuclideanLin.toContinuousLinearMap).reApplyInnerSelf u : ℂ)) =
        inner ℂ ((A.toEuclideanLin.toContinuousLinearMap) u) u := by
    exact hSymm.coe_reApplyInnerSelf_apply u
  -- Move from the symmetric Euclidean inner product back to the coordinate formula `uᴴ A u`.
  calc
    (((A.toEuclideanLin.toContinuousLinearMap).reApplyInnerSelf u : ℂ))
        = inner ℂ ((A.toEuclideanLin.toContinuousLinearMap) u) u := hself
    _ = inner ℂ (A.toEuclideanLin u) u := rfl
    _ = inner ℂ u (A.toEuclideanLin u) := by rw [hSymm u u]
    _ = dotProduct (star u.ofLp) (A.mulVec u.ofLp) := by
          rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
          rw [Matrix.toLpLin_apply (p := 2) (q := 2) A u]

/-- For a Hermitian matrix, the chapter's matrix-side complex quotient agrees with the canonical
real-valued Euclidean Rayleigh quotient of `A.toEuclideanLin.toContinuousLinearMap`. -/
theorem rayleighQuotient_eq_ofReal_toEuclideanLin_rayleighQuotient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (u : EuclideanSpace ℂ (Fin n)) :
    let T := A.toEuclideanLin.toContinuousLinearMap
    rayleighQuotient A u = (T.rayleighQuotient u : ℂ) :=
  by
    let T := A.toEuclideanLin.toContinuousLinearMap
    -- Rewrite the denominator as the squared Euclidean norm.
    have hden : dotProduct (star u.ofLp) u.ofLp = ((‖u‖ : ℂ) ^ 2) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
      simp
    -- The matrix quotient now matches the canonical Euclidean Rayleigh quotient definition.
    rw [rayleighQuotient_def, ← toEuclideanLin_reApplyInnerSelf_eq_dotProduct_mulVec A hA u, hden]
    simp [ContinuousLinearMap.rayleighQuotient]

/-- Chapter01 Theorem 1.2.10 (1): the matrix Rayleigh quotient is homogeneous on nonzero complex
scalar multiples. -/
theorem rayleighQuotient_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) {α : ℂ} (hα : α ≠ 0) :
    rayleighQuotient A (α • u) = rayleighQuotient A u := by
  have hα' : star α * α ≠ 0 := mul_ne_zero (star_ne_zero.mpr hα) hα
  have hnum :
      dotProduct (star (α • u.ofLp)) (A.mulVec (α • u.ofLp)) =
        (star α * α) * dotProduct (star u.ofLp) (A.mulVec u.ofLp) := by
    -- Both the vector and the matrix action contribute one factor of `α`.
    simp [Matrix.mulVec_smul, mul_comm, mul_assoc]
  have hden :
      dotProduct (star (α • u.ofLp)) (α • u.ofLp) =
        (star α * α) * dotProduct (star u.ofLp) u.ofLp := by
    -- The denominator scales by the same quadratic scalar.
    simp [mul_comm, mul_assoc]
  -- Cancel the common nonzero scalar factor.
  rw [rayleighQuotient_def, rayleighQuotient_def, hnum, hden, mul_div_mul_left _ _ hα']

/-- Helper for Chapter01 Theorem 1.2.10: the Rayleigh quotient at a Hermitian eigenvector basis
vector is the corresponding eigenvalue. -/
lemma rayleighQuotient_re_eigenvectorBasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (i : Fin n) :
    Complex.re (rayleighQuotient A (hA.eigenvectorBasis i)) = hA.eigenvalues i := by
  -- The Hermitian eigenvector equation rewrites the numerator to the eigenvalue times the norm.
  rw [rayleighQuotient_def, hA.mulVec_eigenvectorBasis, dotProduct_smul]
  -- The orthonormal eigenvector basis has unit norm, so the denominator is `1`.
  have hnorm : dotProduct (star ⇑(hA.eigenvectorBasis i)) ⇑(hA.eigenvectorBasis i) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]
  rw [hnorm]
  -- This reduces the quotient to the numerator formula already packaged by mathlib.
  simp [hA.eigenvalues_eq i]

/-- Helper for Chapter01 Theorem 1.2.10: every nonzero Rayleigh quotient is bounded above by any
greatest Hermitian eigenvalue. -/
lemma rayleighQuotient_le_of_isGreatest_eigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lambdaMax : ℝ)
    (hLambdaMax : IsGreatest (Set.range hA.eigenvalues) lambdaMax) :
    ∀ u : EuclideanSpace ℂ (Fin n), u ≠ 0 → Complex.re (rayleighQuotient A u) ≤ lambdaMax := by
  intro u hu
  let Tlin := A.toEuclideanLin
  let T := Tlin.toContinuousLinearMap
  have hSymm : Tlin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hbridge :
      Complex.re (rayleighQuotient A u) =
        RCLike.re (inner ℂ (Tlin u) u) / ‖u‖ ^ 2 := by
    -- The bridge theorem identifies the matrix quotient with the canonical real-valued quotient.
    have hbridgeC :
        rayleighQuotient A u =
          (((RCLike.re (inner ℂ (Tlin u) u) / ‖u‖ ^ 2 : ℝ)) : ℂ) := by
      simpa [T, Tlin, ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply] using
        rayleighQuotient_eq_ofReal_toEuclideanLin_rayleighQuotient A hA u
    exact congrArg Complex.re hbridgeC
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := ⟨⟨u, 0, hu⟩⟩
  let s : ℝ := ⨆ x : { x : EuclideanSpace ℂ (Fin n) // x ≠ 0 },
    RCLike.re (inner ℂ (Tlin x) x) / ‖(x : EuclideanSpace ℂ (Fin n))‖ ^ 2
  have hs_eigen : Module.End.HasEigenvalue Tlin (s : ℂ) := by
    -- The top Rayleigh quotient value is an eigenvalue of the symmetric Euclidean operator.
    simpa [s, Tlin] using
      LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional hSymm
  have hs_spec : (s : ℂ) ∈ spectrum ℂ A := by
    -- Transport that eigenvalue back from `A.toEuclideanLin` to the matrix spectrum.
    rw [← Matrix.spectrum_toLpLin (p := 2)]
    exact hs_eigen.mem_spectrum
  have hs_mem_range : s ∈ Set.range hA.eigenvalues := by
    rw [hA.spectrum_eq_image_range] at hs_spec
    rcases hs_spec with ⟨x, hx, hxeq⟩
    rcases hx with ⟨i, rfl⟩
    exact ⟨i, Complex.ofReal_injective hxeq⟩
  have hs_le : s ≤ lambdaMax := hLambdaMax.2 hs_mem_range
  have hs_bdd :
      BddAbove (Set.range fun x : { x : EuclideanSpace ℂ (Fin n) // x ≠ 0 } ↦
        RCLike.re (inner ℂ (Tlin x) x) / ‖(x : EuclideanSpace ℂ (Fin n))‖ ^ 2) := by
    refine ⟨‖T‖, ?_⟩
    rintro y ⟨x, rfl⟩
    simpa [T, Tlin, ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using
      le_trans (le_abs_self (T.rayleighQuotient x)) (T.rayleighQuotient_le_norm x)
  -- Compare the current quotient with the supremal Rayleigh value and then with `lambdaMax`.
  calc
    Complex.re (rayleighQuotient A u) = RCLike.re (inner ℂ (Tlin u) u) / ‖u‖ ^ 2 := hbridge
    _ ≤ s := by
      exact le_ciSup hs_bdd ⟨u, hu⟩
    _ ≤ lambdaMax := hs_le

/-- Helper for Chapter01 Theorem 1.2.10: every nonzero Rayleigh quotient is bounded below by any
least Hermitian eigenvalue. -/
lemma isLeast_eigenvalue_le_rayleighQuotient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lambdaMin : ℝ)
    (hLambdaMin : IsLeast (Set.range hA.eigenvalues) lambdaMin) :
    ∀ u : EuclideanSpace ℂ (Fin n), u ≠ 0 → lambdaMin ≤ Complex.re (rayleighQuotient A u) := by
  intro u hu
  let Tlin := A.toEuclideanLin
  let T := Tlin.toContinuousLinearMap
  have hSymm : Tlin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hbridge :
      Complex.re (rayleighQuotient A u) =
        RCLike.re (inner ℂ (Tlin u) u) / ‖u‖ ^ 2 := by
    -- The same bridge converts the matrix quotient to the canonical Euclidean quotient.
    have hbridgeC :
        rayleighQuotient A u =
          (((RCLike.re (inner ℂ (Tlin u) u) / ‖u‖ ^ 2 : ℝ)) : ℂ) := by
      simpa [T, Tlin, ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply] using
        rayleighQuotient_eq_ofReal_toEuclideanLin_rayleighQuotient A hA u
    exact congrArg Complex.re hbridgeC
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := ⟨⟨u, 0, hu⟩⟩
  let s : ℝ := ⨅ x : { x : EuclideanSpace ℂ (Fin n) // x ≠ 0 },
    RCLike.re (inner ℂ (Tlin x) x) / ‖(x : EuclideanSpace ℂ (Fin n))‖ ^ 2
  have hs_eigen : Module.End.HasEigenvalue Tlin (s : ℂ) := by
    -- The bottom Rayleigh quotient value is likewise an eigenvalue of the symmetric operator.
    simpa [s, Tlin] using
      LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional hSymm
  have hs_spec : (s : ℂ) ∈ spectrum ℂ A := by
    -- Transport the Euclidean spectral point back to the original matrix spectrum.
    rw [← Matrix.spectrum_toLpLin (p := 2)]
    exact hs_eigen.mem_spectrum
  have hs_mem_range : s ∈ Set.range hA.eigenvalues := by
    rw [hA.spectrum_eq_image_range] at hs_spec
    rcases hs_spec with ⟨x, hx, hxeq⟩
    rcases hx with ⟨i, rfl⟩
    exact ⟨i, Complex.ofReal_injective hxeq⟩
  have hs_ge : lambdaMin ≤ s := hLambdaMin.2 hs_mem_range
  have hs_bdd :
      BddBelow (Set.range fun x : { x : EuclideanSpace ℂ (Fin n) // x ≠ 0 } ↦
        RCLike.re (inner ℂ (Tlin x) x) / ‖(x : EuclideanSpace ℂ (Fin n))‖ ^ 2) := by
    refine ⟨-‖T‖, ?_⟩
    rintro y ⟨x, rfl⟩
    have hnorm : |T.rayleighQuotient x| ≤ ‖T‖ := T.rayleighQuotient_le_norm x
    have hneg : -‖T‖ ≤ -|T.rayleighQuotient x| := by exact neg_le_neg hnorm
    have habs : -|T.rayleighQuotient x| ≤ T.rayleighQuotient x := neg_abs_le _
    simpa [T, Tlin, ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using le_trans hneg habs
  -- The infimal Rayleigh value is below every nonzero quotient, so it bounds `u` from below.
  calc
    lambdaMin ≤ s := hs_ge
    _ ≤ RCLike.re (inner ℂ (Tlin u) u) / ‖u‖ ^ 2 := by
      exact ciInf_le hs_bdd ⟨u, hu⟩
    _ = Complex.re (rayleighQuotient A u) := hbridge.symm

/-- Chapter01 Theorem 1.2.10 (2): if `lambdaMax` is the greatest eigenvalue of the Hermitian
matrix `A`, then it is also the greatest value of the real part of the chapter's matrix Rayleigh
quotient on the unit sphere of `EuclideanSpace ℂ (Fin n)`. -/
theorem isGreatest_unitSphere_rayleighQuotient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lambdaMax : ℝ)
    (hLambdaMax : IsGreatest (Set.range hA.eigenvalues) lambdaMax) :
    IsGreatest ((fun u : EuclideanSpace ℂ (Fin n) ↦ Complex.re (rayleighQuotient A u)) ''
      Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) lambdaMax := by
  refine ⟨?_, ?_⟩
  · rcases hLambdaMax.1 with ⟨i, rfl⟩
    -- The source proof attains the endpoint at a unit eigenvector.
    refine ⟨hA.eigenvectorBasis i, ?_, ?_⟩
    · simp [hA.eigenvectorBasis.orthonormal.1 i]
    · simpa using rayleighQuotient_re_eigenvectorBasis A hA i
  · rintro _ ⟨u, hu, rfl⟩
    -- Every unit vector is nonzero, so the one-sided bound helper applies directly.
    exact rayleighQuotient_le_of_isGreatest_eigenvalue A hA lambdaMax hLambdaMax u
      (ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩)

/-- Chapter01 Theorem 1.2.10 (3): the maximum real part of the matrix Rayleigh quotient over
nonzero vectors equals the top endpoint of the Hermitian eigenvalue family `hA.eigenvalues`. -/
theorem isGreatest_nonzero_rayleighQuotient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lambdaMax : ℝ)
    (hLambdaMax : IsGreatest (Set.range hA.eigenvalues) lambdaMax) :
    IsGreatest ((fun u : EuclideanSpace ℂ (Fin n) ↦ Complex.re (rayleighQuotient A u)) ''
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) lambdaMax := by
  refine ⟨?_, ?_⟩
  · rcases hLambdaMax.1 with ⟨i, rfl⟩
    -- The same eigenvector witness also lies in the nonzero set because it has norm `1`.
    refine ⟨hA.eigenvectorBasis i, ?_, ?_⟩
    · simpa [Set.mem_compl_iff] using hA.eigenvectorBasis.orthonormal.ne_zero i
    · simpa using rayleighQuotient_re_eigenvectorBasis A hA i
  · rintro _ ⟨u, hu, rfl⟩
    -- The helper already gives the global nonzero upper bound.
    exact rayleighQuotient_le_of_isGreatest_eigenvalue A hA lambdaMax hLambdaMax u hu

/-- Chapter01 Theorem 1.2.10 (4): if `lambdaMin` is the least eigenvalue of the Hermitian matrix
`A`, then it is also the least value of the real part of the chapter's matrix Rayleigh quotient on
the unit sphere of `EuclideanSpace ℂ (Fin n)`. -/
theorem isLeast_unitSphere_rayleighQuotient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lambdaMin : ℝ)
    (hLambdaMin : IsLeast (Set.range hA.eigenvalues) lambdaMin) :
    IsLeast ((fun u : EuclideanSpace ℂ (Fin n) ↦ Complex.re (rayleighQuotient A u)) ''
      Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) lambdaMin := by
  refine ⟨?_, ?_⟩
  · rcases hLambdaMin.1 with ⟨i, rfl⟩
    -- The source minimum is attained at the unit eigenvector for the least eigenvalue.
    refine ⟨hA.eigenvectorBasis i, ?_, ?_⟩
    · simp [hA.eigenvectorBasis.orthonormal.1 i]
    · simpa using rayleighQuotient_re_eigenvectorBasis A hA i
  · rintro _ ⟨u, hu, rfl⟩
    -- Unit vectors are nonzero, so the lower-bound helper closes the order comparison.
    exact isLeast_eigenvalue_le_rayleighQuotient A hA lambdaMin hLambdaMin u
      (ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩)

/-- Chapter01 Theorem 1.2.10 (5): the minimum real part of the matrix Rayleigh quotient over
nonzero vectors equals the bottom endpoint of the Hermitian eigenvalue family `hA.eigenvalues`. -/
theorem isLeast_nonzero_rayleighQuotient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lambdaMin : ℝ)
    (hLambdaMin : IsLeast (Set.range hA.eigenvalues) lambdaMin) :
    IsLeast ((fun u : EuclideanSpace ℂ (Fin n) ↦ Complex.re (rayleighQuotient A u)) ''
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) lambdaMin := by
  refine ⟨?_, ?_⟩
  · rcases hLambdaMin.1 with ⟨i, rfl⟩
    -- The unit eigenvector witness remains valid on the nonzero domain.
    refine ⟨hA.eigenvectorBasis i, ?_, ?_⟩
    · simpa [Set.mem_compl_iff] using hA.eigenvectorBasis.orthonormal.ne_zero i
    · simpa using rayleighQuotient_re_eigenvectorBasis A hA i
  · rintro _ ⟨u, hu, rfl⟩
    -- The lower-bound helper already gives the needed comparison on `{0}ᶜ`.
    exact isLeast_eigenvalue_le_rayleighQuotient A hA lambdaMin hLambdaMin u hu

/-- Chapter01 Theorem 1.2.10 (6): for every nonzero vector, the real part of the matrix Rayleigh
quotient lies between the smallest and largest Hermitian eigenvalues. -/
theorem rayleighQuotient_mem_Icc_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (lambdaMin lambdaMax : ℝ)
    (hLambdaMin : IsLeast (Set.range hA.eigenvalues) lambdaMin)
    (hLambdaMax : IsGreatest (Set.range hA.eigenvalues) lambdaMax)
    (u : EuclideanSpace ℂ (Fin n)) (hu : u ≠ 0) :
    Complex.re (rayleighQuotient A u) ∈ Set.Icc lambdaMin lambdaMax :=
  by
    -- The final interval statement is exactly the conjunction of the two one-sided bounds.
    constructor
    · exact isLeast_eigenvalue_le_rayleighQuotient A hA lambdaMin hLambdaMin u hu
    · exact rayleighQuotient_le_of_isGreatest_eigenvalue A hA lambdaMax hLambdaMax u hu

/-- Helper for Chapter01 Theorem 1.2.10: the Rayleigh residual is orthogonal to the generating
vector. -/
lemma rayleighResidual_inner_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (u : EuclideanSpace ℂ (Fin n)) :
    let rq := Complex.re (rayleighQuotient A u)
    inner ℂ (A.toEuclideanLin u - (rq : ℂ) • u) u = 0 := by
  change inner ℂ (A.toEuclideanLin u - (Complex.re (rayleighQuotient A u) : ℂ) • u) u = 0
  by_cases hu : u = 0
  · simp [hu]
  · have hAu :
        inner ℂ (A.toEuclideanLin u) u = dotProduct (star u.ofLp) (A.mulVec u.ofLp) := by
      have hSymm : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
      have hself :
          inner ℂ (A.toEuclideanLin u) u =
            (((A.toEuclideanLin.toContinuousLinearMap).reApplyInnerSelf u : ℂ)) := by
        change inner ℂ ((LinearMap.toContinuousLinearMap A.toEuclideanLin) u) u =
          (((A.toEuclideanLin.toContinuousLinearMap).reApplyInnerSelf u : ℂ))
        symm
        exact hSymm.coe_reApplyInnerSelf_apply u
      calc
        inner ℂ (A.toEuclideanLin u) u
            = (((A.toEuclideanLin.toContinuousLinearMap).reApplyInnerSelf u : ℂ)) := hself
        _ = dotProduct (star u.ofLp) (A.mulVec u.ofLp) := by
              simpa using toEuclideanLin_reApplyInnerSelf_eq_dotProduct_mulVec A hA u
    have huu : inner ℂ u u = dotProduct (star u.ofLp) u.ofLp := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    have hden : dotProduct (star u.ofLp) u.ofLp ≠ 0 := by
      rw [← huu]
      exact inner_self_ne_zero.mpr hu
    have hshift :
        inner ℂ ((Complex.re (rayleighQuotient A u) : ℂ) • u) u =
          (Complex.re (rayleighQuotient A u) : ℂ) * dotProduct (star u.ofLp) u.ofLp := by
      rw [inner_smul_left, Complex.conj_ofReal, huu]
    -- Rewrite the residual orthogonality identity to the scalar equality
    -- `uᴴ A u - (uᴴ A u / uᴴ u) * (uᴴ u) = 0`.
    rw [inner_sub_left, hAu, hshift]
    rw [← rayleighQuotient_eq_ofReal_re A hA u, rayleighQuotient_def]
    rw [div_mul_cancel₀ _ hden, sub_self]

/-- Chapter01 Theorem 1.2.10 (7): among real scalar shifts `μ • u`, the real part of the matrix
Rayleigh quotient gives the smallest residual norm in `EuclideanSpace ℂ (Fin n)`. -/
theorem rayleighResidual_le_shiftResidual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (u : EuclideanSpace ℂ (Fin n)) (μ : ℝ) :
    let rq := Complex.re (rayleighQuotient A u)
    ‖A.toEuclideanLin u - (rq : ℂ) • u‖ ≤ ‖A.toEuclideanLin u - (μ : ℂ) • u‖ := by
  change ‖A.toEuclideanLin u - (Complex.re (rayleighQuotient A u) : ℂ) • u‖ ≤
    ‖A.toEuclideanLin u - (μ : ℂ) • u‖
  let r : EuclideanSpace ℂ (Fin n) :=
    A.toEuclideanLin u - (Complex.re (rayleighQuotient A u) : ℂ) • u
  let s : EuclideanSpace ℂ (Fin n) := ((Complex.re (rayleighQuotient A u) - μ : ℝ) : ℂ) • u
  have horth : inner ℂ r s = 0 := by
    -- The second summand is a scalar multiple of `u`, so orthogonality follows from the residual
    -- being orthogonal to `u`.
    rw [show s = ((Complex.re (rayleighQuotient A u) - μ : ℝ) : ℂ) • u by rfl]
    rw [inner_smul_right, rayleighResidual_inner_eq_zero A hA u]
    simp
  have hdecomp : A.toEuclideanLin u - (μ : ℂ) • u = r + s := by
    -- The shifted residual splits into the Rayleigh residual plus a multiple of `u`.
    unfold r s
    have hcast :
        (((Complex.re (rayleighQuotient A u) - μ : ℝ) : ℂ) • u) =
          (((Complex.re (rayleighQuotient A u) : ℂ) - (μ : ℂ)) • u) := by
      simp
    rw [hcast]
    rw [sub_smul]
    abel
  have hsq : ‖r + s‖ * ‖r + s‖ = ‖r‖ * ‖r‖ + ‖s‖ * ‖s‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero r s horth
  have hsq_le :
      ‖r‖ * ‖r‖ ≤ ‖A.toEuclideanLin u - (μ : ℂ) • u‖ * ‖A.toEuclideanLin u - (μ : ℂ) • u‖ := by
    have hs_nonneg : 0 ≤ ‖s‖ * ‖s‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖r‖ * ‖r‖ ≤ ‖r‖ * ‖r‖ + ‖s‖ * ‖s‖ := by linarith
      _ = ‖r + s‖ * ‖r + s‖ := by rw [hsq]
      _ = ‖A.toEuclideanLin u - (μ : ℂ) • u‖ * ‖A.toEuclideanLin u - (μ : ℂ) • u‖ := by
            rw [← hdecomp]
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by simpa [r] using hsq_le)
