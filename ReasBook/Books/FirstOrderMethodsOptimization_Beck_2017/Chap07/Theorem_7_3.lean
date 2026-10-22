/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_33
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "𝕊" => symmetricMatrices n
local notation "symmetricEigenvalues" => symmetric_eigenvalue_function

/-- The ambient real matrix space is equipped with its Frobenius norm. -/
local instance theorem7_3_frobeniusNormedAddCommGroup : NormedAddCommGroup Mₙ :=
  Matrix.frobeniusNormedAddCommGroup
local instance theorem7_3_frobeniusNormedSpace : NormedSpace ℝ Mₙ :=
  Matrix.frobeniusNormedSpace
local instance theorem7_3_frobeniusInnerProductSpace : InnerProductSpace ℝ Mₙ :=
  Matrix.frobeniusInnerProductSpace

/-- A real symmetric matrix is Hermitian. -/
-- Proof sketch: over `ℝ`, the conjugate transpose is the ordinary transpose, so `IsHermitian`
-- reduces to `IsSymm`.
theorem Matrix.IsSymm.theorem7_3_isHermitian_of_real {X : Mₙ} (hX : X.IsSymm) :
    X.IsHermitian := by
  -- Over `ℝ`, conjugate transpose is transpose, so symmetry is exactly Hermitian symmetry.
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hX

/-- The ordered eigenvalue map on real symmetric `n × n` matrices. -/
noncomputable def symmetricMatrixEigenvalues (X : Mₙ) (hX : X.IsSymm) : Fin n → ℝ :=
  hX.theorem7_3_isHermitian_of_real.eigenvalues

-- Proof sketch: unfold `symmetricMatrixEigenvalues`; evaluation at `i` is definitionally the
-- `i`-th ordered Hermitian eigenvalue of the symmetric matrix `X`.
/-- Evaluating `symmetricMatrixEigenvalues X hX` returns the corresponding ordered Hermitian
eigenvalue of the symmetric matrix `X`. -/
@[simp] theorem symmetricMatrixEigenvalues_apply (X : Mₙ) (hX : X.IsSymm) (i : Fin n) :
    symmetricMatrixEigenvalues X hX i = hX.theorem7_3_isHermitian_of_real.eigenvalues i := by
  -- This is the defining equation of `symmetricMatrixEigenvalues`.
  rfl

/-- The orthogonal conjugate of the diagonal matrix with diagonal `x`. -/
noncomputable def orthogonalDiagonalMap (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Fin n → ℝ) → Mₙ :=
  fun x ↦ (U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ

-- Proof sketch: unfold `orthogonalDiagonalMap`; the value at `x` is definitionally
-- `U * diagonal x * Uᵀ`.
/-- Evaluating `orthogonalDiagonalMap U` at `x` yields `U * diagonal x * Uᵀ`. -/
@[simp] theorem orthogonalDiagonalMap_apply
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    orthogonalDiagonalMap U x = (U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ := by
  -- This is the defining equation of `orthogonalDiagonalMap`.
  rfl

/-- The same diagonal-conjugation map with a Euclidean vector input. This is the vector-side
owner needed by the proximal formula, because the Frobenius norm on diagonal matrices corresponds
to the Euclidean `L²` norm on eigenvalue vectors. -/
noncomputable def orthogonalDiagonalMapEuclidean (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) → Mₙ :=
  fun x ↦ orthogonalDiagonalMap U x.ofLp

/-- The ambient spectral lift of a vector-side profile `f`, extended by `⊤` away from the
symmetric matrices. -/
noncomputable def symmetricSpectralLift (f : (Fin n → ℝ) → EReal) : Mₙ → EReal :=
  fun X ↦ if hX : X.IsSymm then f (symmetricMatrixEigenvalues X hX) else ⊤

-- Proof sketch: unfold `symmetricSpectralLift`; when `X` is symmetric, the `if`-branch selected
-- by `hX` is exactly `f (symmetricMatrixEigenvalues X hX)`.
/-- On a symmetric matrix `X`, `symmetricSpectralLift f X` is `f` applied to the ordered
eigenvalue vector of `X`. -/
theorem symmetricSpectralLift_apply_of_isSymm
    (f : (Fin n → ℝ) → EReal) (X : Mₙ) (hX : X.IsSymm) :
    symmetricSpectralLift f X = f (symmetricMatrixEigenvalues X hX) := by
  -- The symmetric branch of the defining `if` is selected by `hX`.
  simp [symmetricSpectralLift, hX]

-- Proof sketch: unfold `symmetricSpectralLift`; when `X` is not symmetric, the definition chooses
-- the `⊤` branch.
/-- On a nonsymmetric matrix `X`, `symmetricSpectralLift f X = ⊤`. -/
theorem symmetricSpectralLift_apply_of_not_isSymm
    (f : (Fin n → ℝ) → EReal) (X : Mₙ) (hX : ¬ X.IsSymm) :
    symmetricSpectralLift f X = ⊤ := by
  -- The nonsymmetric branch of the defining `if` is selected by `hX`.
  simp [symmetricSpectralLift, hX]

/-- Helper for Theorem 7.3: orthogonal conjugation preserves symmetry of real matrices. -/
theorem orthogonal_conjugate_isSymm
    (U : Matrix.orthogonalGroup (Fin n) ℝ) {X : Mₙ} (hX : X.IsSymm) :
    (((U : Mₙ)ᵀ) * X * (U : Mₙ)).IsSymm := by
  -- Conjugating a symmetric matrix by a fixed orthogonal matrix preserves the transpose symmetry.
  simpa [Matrix.IsSymm, Matrix.transpose_mul, mul_assoc] using
    congrArg (fun A : Mₙ ↦ (U : Mₙ)ᵀ * A * (U : Mₙ)) hX

/-- Helper for Theorem 7.3: the local ordered eigenvalue map differs from the Chapter 7 subtype
owner `symmetric_eigenvalue_function` only by a fixed permutation of `Fin n`. -/
lemma symmetricMatrixEigenvalues_eq_symmetric_eigenvalue_function_comp_perm :
    ∃ σ : Equiv.Perm (Fin n), ∀ X : Mₙ, ∀ hX : X.IsSymm,
      symmetricMatrixEigenvalues X hX =
        symmetricEigenvalues ⟨X, by
          simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩ ∘ σ := by
  obtain ⟨σ, hσ⟩ := exists_eigenvalue_reindex_perm (n := n)
  refine ⟨σ, ?_⟩
  intro X hX
  -- Theorem 7.2 already proves the fixed-permutation bridge on the subtype owner.
  simpa [symmetricMatrixEigenvalues] using hσ ⟨X, by
    simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩

/-- Helper for Theorem 7.3: the Frobenius norm is invariant under orthogonal conjugation. -/
lemma frobenius_norm_orthogonal_conjugate_eq
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : Mₙ) :
    ‖(U : Mₙ)ᵀ * A * (U : Mₙ)‖ = ‖A‖ := by
  -- Rewrite the Frobenius norm through `Tr(Aᵀ A)` and cycle the trace past the orthogonal factors.
  rw [frobenius_norm_eq_sqrt_trace_transpose_mul, frobenius_norm_eq_sqrt_trace_transpose_mul]
  congr 1
  have hUUt : (U : Mₙ) * (U : Mₙ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
  calc
    Matrix.trace ((((U : Mₙ)ᵀ * A * (U : Mₙ))ᵀ) * ((U : Mₙ)ᵀ * A * (U : Mₙ)))
      = Matrix.trace (((U : Mₙ)ᵀ * Aᵀ) * ((U : Mₙ) * (U : Mₙ)ᵀ) * A * (U : Mₙ)) := by
          simp [Matrix.transpose_mul, mul_assoc]
    _ = Matrix.trace (((U : Mₙ)ᵀ * Aᵀ) * A * (U : Mₙ)) := by
          rw [hUUt]
          simp [mul_assoc]
    _ = Matrix.trace ((U : Mₙ)ᵀ * (Aᵀ * A) * (U : Mₙ)) := by
          simp [mul_assoc]
    _ = Matrix.trace ((U : Mₙ) * (U : Mₙ)ᵀ * (Aᵀ * A)) := by
          exact Matrix.trace_mul_cycle ((U : Mₙ)ᵀ) (Aᵀ * A) (U : Mₙ)
    _ = Matrix.trace (Aᵀ * A) := by
          rw [hUUt]
          simp

/-- Helper for Theorem 7.3: evaluating the subtype spectral profile on a diagonal matrix recovers
the original vector profile, because diagonal entries and ordered eigenvalues differ only by a
permutation. -/
lemma symmetric_spectral_diagonal_pullback_eq
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (x : Fin n → ℝ) :
    (f ∘ symmetricEigenvalues) ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩ = f x := by
  -- Route correction: use the Chapter 7 ordered-eigenvalue owner directly and then remove the
  -- fixed permutation mismatch by permutation symmetry of `f`.
  have hf_desc :
      ∀ z : Fin n → ℝ, f z = f z↓ :=
    ((isPermutationSymmetricFunction_iff_forall_eq_descendingRearrangement f).1 hf_perm).2
  let σ : Equiv.Perm (Fin n) := Fin.revPerm.symm * (Tuple.sort x).symm
  have hσ : ∀ i, x i = x↓ (σ i) := by
    intro i
    simp [σ, descendingRearrangement, Function.comp_def, Equiv.Perm.coe_mul]
  have hdiag :
      Matrix.diagonal x =
        ((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
          Matrix.diagonal (x↓) *
          (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) := by
    have hdiagx : Matrix.diagonal x = Matrix.diagonal (x↓ ∘ σ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hσ]
      · simp [Matrix.diagonal, hij]
    calc
      Matrix.diagonal x = Matrix.diagonal (x↓ ∘ σ) := hdiagx
      _ = ((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
            Matrix.diagonal (x↓) *
            (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) :=
          diagonal_comp_perm_eq_orthogonal_conjugate σ (x↓)
  let X : 𝕊 := ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩
  let Y : 𝕊 := ⟨Matrix.diagonal (x↓), diagonal_mem_symmetricMatrices (x↓)⟩
  have hchar : ((X : Mₙ)).charpoly = ((Y : Mₙ)).charpoly := by
    -- Orthogonal conjugation preserves the characteristic polynomial, hence the ordered spectrum.
    dsimp [X, Y]
    calc
      Matrix.charpoly (Matrix.diagonal x) =
          Matrix.charpoly
            (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
              Matrix.diagonal (x↓) *
              (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ)) := by
            exact congrArg Matrix.charpoly hdiag
      _ = Matrix.charpoly (Matrix.diagonal (x↓)) := by
            exact orthogonal_conjugate_diagonal_charpoly (permutationOrthogonalMatrix σ) (x↓)
  have heq : symmetricEigenvalues X = symmetricEigenvalues Y := by
    -- The ordered Hermitian eigenvalue vector is determined by the characteristic polynomial.
    ext i
    rw [symmetric_eigenvalue_function_apply, symmetric_eigenvalue_function_apply]
    have heig0 :
        X.property.isHermitian.eigenvalues₀ = Y.property.isHermitian.eigenvalues₀ := by
      simp_rw [← List.ofFn_inj,
        ← X.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀,
        ← Y.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀, hchar]
    simpa using congrFun heig0 (Fin.cast (Fintype.card_fin n).symm i)
  have hY :
      symmetricEigenvalues Y = x↓ := by
    -- The already sorted diagonal matrix exposes its eigenvalues on the diagonal.
    simpa [Y] using
      diagonal_symmetric_eigenvalue_function_eq_of_antitone
        (x↓) (antitone_descendingRearrangement x)
  calc
    (f ∘ symmetricEigenvalues) X = f (symmetricEigenvalues Y) := by
      simp [heq]
    _ = f (x↓) := by
      rw [hY]
    _ = f x := by
      exact (hf_desc x).symm

/-- Helper for Theorem 7.3: moving the transpose action of an orthogonal matrix from the second
input of the dot product to the first input amounts to the orthogonal action on the first vector.
-/
lemma dotProduct_transpose_mulVec_eq_dotProduct_smul
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (y z : Fin n → ℝ) :
    dotProduct y ((A : Mₙ).transpose.mulVec z) =
      dotProduct (A • y) z := by
  -- Rewrite the left pairing by moving the transpose to the first input.
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rfl

/-- Helper for Theorem 7.3: an orthogonal matrix followed by its transpose acts as the identity on
`ℝ^n`. -/
lemma orthogonal_mulVec_transpose_mulVec
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (z : Fin n → ℝ) :
    (A : Mₙ).mulVec ((A : Mₙ).transpose.mulVec z) = z := by
  -- Collapse the matrix product to the identity by orthogonality.
  rw [Matrix.mulVec_mulVec]
  have hA : (A : Mₙ) * (A : Mₙ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (A : Mₙ)) (R := ℝ)).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Theorem 7.3: the transpose of an orthogonal matrix is the inverse of its action on
`ℝ^n`. -/
private lemma theorem7_3_orthogonal_transpose_mulVec_mulVec
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    ((A : Mₙ).transpose).mulVec ((A : Mₙ).mulVec x) = x := by
  -- Collapse the transpose-after-action product to the identity.
  rw [Matrix.mulVec_mulVec]
  have hA : (A : Mₙ).transpose * (A : Mₙ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Theorem 7.3: orthogonal precomposition transports the conjugate witness range by the
matching change of variables. -/
lemma conjugate_integrand_range_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (f : (Fin n → ℝ) → EReal)
    (y : Fin n → ℝ) :
    Set.range
        (fun x : Fin n → ℝ ↦
          (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - f (A • x)) =
      Set.range
        (fun z : Fin n → ℝ ↦
          (((dotProductEquiv ℝ (Fin n) (A • y)) z : ℝ) : EReal) - f z) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨A • x, ?_⟩
    simp only
    have hAx : A • x = (A : Mₙ).mulVec x := rfl
    have hx : ((A : Mₙ).transpose).mulVec (A • x) = x := by
      rw [hAx]
      exact theorem7_3_orthogonal_transpose_mulVec_mulVec A x
    have hdot :
        (((dotProductEquiv ℝ (Fin n) y)
            (((A : Mₙ).transpose).mulVec (A • x)) : ℝ) : EReal) =
          (((dotProductEquiv ℝ (Fin n) (A • y)) (A • x) : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y (A • x))
    rw [← hdot, hx]
  · rintro ⟨z, rfl⟩
    refine ⟨((A : Mₙ).transpose).mulVec z, ?_⟩
    simp only
    have hz : A • (A : Mₙ).transpose.mulVec z = z := by
      change (A : Mₙ).mulVec (((A : Mₙ).transpose).mulVec z) = z
      exact orthogonal_mulVec_transpose_mulVec A z
    have hdot :
        (((dotProductEquiv ℝ (Fin n) y)
            ((A : Mₙ).transpose.mulVec z) : ℝ) : EReal) =
          (((dotProductEquiv ℝ (Fin n) (A • y)) z : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y z)
    rw [hdot, hz]

/-- Helper for Theorem 7.3: precomposing the primal profile by an orthogonal matrix transports the
Fenchel conjugate point by that same orthogonal action. -/
lemma conjugate_function_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (f : (Fin n → ℝ) → EReal)
    (y : Fin n → ℝ) :
    conjugate_function (fun x : Fin n → ℝ ↦ f (A • x))
        (dotProductEquiv ℝ (Fin n) y) =
      conjugate_function f (dotProductEquiv ℝ (Fin n) (A • y)) := by
  -- Replace the defining supremum range by the orthogonal change of variables.
  rw [conjugate_function_apply, conjugate_function_apply,
    conjugate_integrand_range_precompose_orthogonal_eq]

/-- Helper for Theorem 7.3: the dot-product pullback of the conjugate profile is permutation
symmetric whenever `f` is. -/
lemma dotProduct_conjugate_profile_is_permutation_symmetric
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (hf_convex : is_convex_function f) :
    IsPermutationSymmetricFunction
      (fun x : Fin n → ℝ ↦ conjugate_function f (dotProductEquiv ℝ (Fin n) x)) := by
  let hproper : IsProperExtendedRealFunction f := hf_perm.toIsProperExtendedRealFunction
  let hconj := isProperExtendedRealFunction_conjugate_function f hproper hf_convex
  refine
    { toIsProperExtendedRealFunction := ?_
      map_smul := ?_ }
  · -- Properness transports across the dot-product linear equivalence.
    refine ⟨?_, ?_⟩
    · intro x
      exact hconj.ne_bot (dotProductEquiv ℝ (Fin n) x)
    · rcases hconj.effective_domain_nonempty with ⟨y, hy⟩
      refine ⟨(dotProductEquiv ℝ (Fin n)).symm y, ?_⟩
      have hdual :
          dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm y) = y :=
        (dotProductEquiv ℝ (Fin n)).apply_symm_apply y
      simpa [hdual] using hy
  · intro A hA y
    rcases hA with ⟨σ, rfl⟩
    -- Replace the conjugate profile by the orthogonal precomposition and then use symmetry of `f`.
    calc
      conjugate_function f
          (dotProductEquiv ℝ (Fin n) (permutationOrthogonalMatrix σ • y)) =
        conjugate_function (fun x : Fin n → ℝ ↦ f (permutationOrthogonalMatrix σ • x))
          (dotProductEquiv ℝ (Fin n) y) := by
            symm
            exact conjugate_function_precompose_orthogonal_eq (permutationOrthogonalMatrix σ) f y
      _ = conjugate_function f (dotProductEquiv ℝ (Fin n) y) := by
            have hpre :
                (fun x : Fin n → ℝ ↦ f (permutationOrthogonalMatrix σ • x)) = f := by
              ext x
              exact hf_perm.map_smul (permutationOrthogonalMatrix σ) (Set.mem_range_self σ) x
            rw [hpre]

/-- Helper for Theorem 7.3: taking the dot-product pullback conjugate twice recovers the Chapter 4
biconjugate of the vector profile. -/
lemma dotProduct_conjugate_profile_biconjugate_eq
    (f : (Fin n → ℝ) → EReal) :
    (fun x : Fin n → ℝ ↦
      conjugate_function
        (fun z : Fin n → ℝ ↦ conjugate_function f (dotProductEquiv ℝ (Fin n) z))
        (dotProductEquiv ℝ (Fin n) x)) =
      biconjugate_function f := by
  funext x
  -- Compare the defining suprema by transporting witnesses through `dotProductEquiv`.
  rw [conjugate_function_apply, biconjugate_function_apply]
  congr 1
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨dotProductEquiv ℝ (Fin n) z, ?_⟩
    simp [dotProduct_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm y, ?_⟩
    have hdual :
        dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm y) = y :=
      (dotProductEquiv ℝ (Fin n)).apply_symm_apply y
    have hpair' :
        (dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm y)) x = y x := by
      exact congrArg (fun ψ : Module.Dual ℝ (Fin n → ℝ) => ψ x) hdual
    have hpair : dotProduct x ((dotProductEquiv ℝ (Fin n)).symm y) = y x := by
      simpa [dotProductEquiv, dotProduct_comm] using hpair'
    simp [hdual, hpair]

/-- Helper for Theorem 7.3: the spectral profile on the symmetric subtype is closed and convex
whenever the vector profile is permutation symmetric, closed, and convex. -/
lemma symmetric_spectral_function_closed_convex_on_subtype
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    LowerSemicontinuous (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) ∧
      is_convex_function (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) := by
  let fconj : (Fin n → ℝ) → EReal :=
    fun x ↦ conjugate_function f (dotProductEquiv ℝ (Fin n) x)
  have hfconj_symm : IsPermutationSymmetricFunction fconj :=
    dotProduct_conjugate_profile_is_permutation_symmetric f hf_perm hf_convex
  have hmatrix_conj :
      (fun Y : 𝕊 ↦ conjugate_function (fun Z : 𝕊 ↦ f (symmetricEigenvalues Z))
          ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)) =
        fconj ∘ symmetricEigenvalues := by
    -- The first spectral conjugate formula identifies the matrix conjugate with the vector one.
    simpa [fconj, Function.comp] using spectral_conjugate_formula f hf_perm
  have hmatrix_conj_conj :
      (fun Y : 𝕊 ↦ conjugate_function (fconj ∘ symmetricEigenvalues)
          ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)) =
        (fun x : Fin n → ℝ ↦ conjugate_function fconj (dotProductEquiv ℝ (Fin n) x)) ∘
          symmetricEigenvalues := by
    -- Apply the same spectral formula once more to the conjugate profile.
    simpa [Function.comp] using spectral_conjugate_formula fconj hfconj_symm
  have hproper : IsProperExtendedRealFunction f := hf_perm.toIsProperExtendedRealFunction
  have hself : biconjugate_function f = f :=
    biconjugate_function_eq_self_of_proper_closed_convex f hproper hf_closed hf_convex
  have hmatrix_self :
      (fun Y : 𝕊 ↦ conjugate_function (fconj ∘ symmetricEigenvalues)
          ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)) =
        fun Y : 𝕊 ↦ f (symmetricEigenvalues Y) := by
    -- The second conjugation turns the vector profile into its biconjugate and then back to `f`.
    calc
      (fun Y : 𝕊 ↦ conjugate_function (fconj ∘ symmetricEigenvalues)
          ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)) =
          (fun x : Fin n → ℝ ↦ conjugate_function fconj (dotProductEquiv ℝ (Fin n) x)) ∘
            symmetricEigenvalues := hmatrix_conj_conj
      _ = biconjugate_function f ∘ symmetricEigenvalues := by
            rw [dotProduct_conjugate_profile_biconjugate_eq f]
      _ = fun Y : 𝕊 ↦ f (symmetricEigenvalues Y) := by
            simpa [Function.comp] using congrArg (fun g : (Fin n → ℝ) → EReal ↦ g ∘ symmetricEigenvalues) hself
  let G : 𝕊 → EReal :=
    fun Y ↦ conjugate_function (fun Z : 𝕊 ↦ f (symmetricEigenvalues Z))
      ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)
  have hdouble : G∗ = fun Y : 𝕊 ↦ f (symmetricEigenvalues Y) := by
    funext Y
    -- Rewrite the primal conjugate of `G` through the stabilized matrix-side biconjugate route.
    calc
      (G∗) Y = conjugate_function G ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y) := by
        rw [conjugate_function_primal_apply]
      _ = f (symmetricEigenvalues Y) := by
        exact congrFun
          (show (fun Y : 𝕊 ↦ conjugate_function G ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)) =
              fun Y : 𝕊 ↦ f (symmetricEigenvalues Y) by
            calc
              (fun Y : 𝕊 ↦ conjugate_function G ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)) =
                  (fun Y : 𝕊 ↦ conjugate_function (fconj ∘ symmetricEigenvalues)
                      ↑(InnerProductSpace.toDualMap ℝ 𝕊 Y)) := by
                        simp [G, hmatrix_conj]
              _ = fun Y : 𝕊 ↦ f (symmetricEigenvalues Y) := hmatrix_self) Y
  have hclosedconv := conjugate_function_closed_and_convex G
  -- The double conjugate is exactly the original spectral profile on the symmetric subtype.
  rw [hdouble] at hclosedconv
  exact hclosedconv

/-- Helper for Theorem 7.3: the spectral profile on the symmetric subtype is proper whenever the
vector profile is permutation symmetric. -/
lemma symmetric_spectral_function_proper_on_subtype
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f) :
    IsProperExtendedRealFunction (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) := by
  let hproper : IsProperExtendedRealFunction f := hf_perm.toIsProperExtendedRealFunction
  refine ⟨?_, ?_⟩
  · intro Y
    exact hproper.ne_bot (symmetricEigenvalues Y)
  · rcases hproper.effective_domain_nonempty with ⟨x, hx⟩
    refine ⟨⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩, ?_⟩
    rw [mem_effective_domain]
    have hdiag_eval :
        f (symmetricEigenvalues ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩) = f x := by
      simpa [Function.comp] using symmetric_spectral_diagonal_pullback_eq f hf_perm x
    exact hdiag_eval.symm ▸ hx

/-- Helper for Theorem 7.3: the Euclidean pullback `y ↦ f y.ofLp` is proper, closed, and convex
whenever `f` is. -/
lemma theorem7_3_euclidean_pullback_proper_closed_convex
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    IsProperExtendedRealFunction (fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp) ∧
      LowerSemicontinuous (fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp) ∧
      is_convex_function (fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp) := by
  let hproper : IsProperExtendedRealFunction f := hf_perm.toIsProperExtendedRealFunction
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro y
      exact hproper.ne_bot y.ofLp
    · rcases hproper.effective_domain_nonempty with ⟨x, hx⟩
      refine ⟨WithLp.toLp (p := (2 : ENNReal)) x, ?_⟩
      simpa using hx
  · -- Closedness is preserved by continuous precomposition along `ofLp`.
    simpa using hf_closed.comp
      (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin n ↦ ℝ))
  · -- Convexity is preserved by the affine pullback `y ↦ y.ofLp`.
    simpa using
      is_convex_function_precompose_affineMap hf_convex
        ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin n → ℝ)).toAffineMap)

/-- Helper for Theorem 7.3: on diagonal matrices, the ambient spectral lift evaluates to the
vector profile. -/
lemma symmetricSpectralLift_diagonal_eq
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (x : Fin n → ℝ) :
    symmetricSpectralLift f (Matrix.diagonal x) = f x := by
  have hdiag : (Matrix.diagonal x).IsSymm := by
    simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using diagonal_mem_symmetricMatrices x
  rw [symmetricSpectralLift_apply_of_isSymm f _ hdiag]
  obtain ⟨σ, hσ⟩ := symmetricMatrixEigenvalues_eq_symmetric_eigenvalue_function_comp_perm (n := n)
  let Xs : 𝕊 := ⟨Matrix.diagonal x, by
    simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hdiag⟩
  calc
    f (symmetricMatrixEigenvalues (Matrix.diagonal x) hdiag)
        = f (symmetricEigenvalues Xs ∘ σ) := by
            rw [hσ (Matrix.diagonal x) hdiag]
    _ = f (symmetricEigenvalues Xs) := by
          simpa [permutationOrthogonalMatrix_smul] using
            hf_perm.map_smul (permutationOrthogonalMatrix σ) (Set.mem_range_self σ)
              (symmetricEigenvalues Xs)
    _ = f x := by
          simpa [Function.comp, Xs] using symmetric_spectral_diagonal_pullback_eq f hf_perm x

/-- Helper for Theorem 7.3: on symmetric matrices, the ambient spectral lift matches the subtype
spectral profile after removing the fixed permutation bridge from Theorem 7.2. -/
lemma symmetricSpectralLift_apply_subtype_eq
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (X : Mₙ) (hX : X.IsSymm) :
    symmetricSpectralLift f X =
      f (symmetricEigenvalues ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩) := by
  let Xs : 𝕊 := ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩
  rw [symmetricSpectralLift_apply_of_isSymm f X hX]
  obtain ⟨σ, hσ⟩ := symmetricMatrixEigenvalues_eq_symmetric_eigenvalue_function_comp_perm (n := n)
  calc
    f (symmetricMatrixEigenvalues X hX) = f (symmetricEigenvalues Xs ∘ σ) := by
      rw [hσ X hX]
    _ = f (symmetricEigenvalues Xs) := by
          simpa [permutationOrthogonalMatrix_smul] using
            hf_perm.map_smul (permutationOrthogonalMatrix σ) (Set.mem_range_self σ)
              (symmetricEigenvalues Xs)

/-- Helper for Theorem 7.3: on the symmetric subtype, the subtype proximal objective coincides
with the ambient proximal objective of the spectral lift. -/
lemma subtype_proximal_objective_eq_ambient
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (X : Mₙ) (hX : X.IsSymm) (Y : 𝕊) :
    proximal_objective (fun Z : 𝕊 ↦ f (symmetricEigenvalues Z))
        ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩ Y =
      proximal_objective (symmetricSpectralLift f) X (Y : Mₙ) := by
  -- Rewrite the ambient spectral term through the fixed-permutation bridge and then unfold both
  -- quadratic penalties.
  rw [proximal_objective_apply, proximal_objective_apply,
    symmetricSpectralLift_apply_subtype_eq f hf_perm (Y : Mₙ) Y.property]
  rfl

/-- Helper for Theorem 7.3: at a symmetric base point, the ambient proximal set of
`symmetricSpectralLift f` is exactly the coercion-image of the proximal set on the symmetric
subtype. -/
lemma prox_symmetricSpectralLift_eq_subtype_image
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (X : Mₙ) (hX : X.IsSymm) :
    prox[symmetricSpectralLift f] X =
      ((↑) '' prox[fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)]
        ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩) :=
by
  let Xs : 𝕊 := ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩
  let hproper : IsProperExtendedRealFunction f := hf_perm.toIsProperExtendedRealFunction
  ext Z
  constructor
  · intro hZ
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hZ
    rcases hproper.effective_domain_nonempty with ⟨x0, hx0⟩
    have hfinite_diag :
        proximal_objective (symmetricSpectralLift f) X (Matrix.diagonal x0) < ⊤ := by
      -- A diagonal competitor coming from the effective domain keeps the ambient objective finite.
      rw [proximal_objective_apply, symmetricSpectralLift_diagonal_eq f hf_perm]
      simpa using EReal.add_lt_top (mem_effective_domain.mp hx0).ne (EReal.coe_ne_top _)
    have hZ_obj : proximal_objective (symmetricSpectralLift f) X Z ≤
        proximal_objective (symmetricSpectralLift f) X (Matrix.diagonal x0) := hZ (Matrix.diagonal x0)
    have hZ_finite : proximal_objective (symmetricSpectralLift f) X Z < ⊤ :=
      lt_of_le_of_lt hZ_obj hfinite_diag
    have hZsymm : Z.IsSymm := by
      by_contra hZnot
      have htop : proximal_objective (symmetricSpectralLift f) X Z = ⊤ := by
        rw [proximal_objective_apply, symmetricSpectralLift_apply_of_not_isSymm f Z hZnot]
        exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
      rw [htop] at hZ_finite
      simp at hZ_finite
    let Zs : 𝕊 := ⟨Z, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hZsymm⟩
    refine ⟨Zs, ?_, rfl⟩
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro Y
    -- Restrict the ambient minimizing inequality to symmetric competitors.
    have hZY := hZ (Y : Mₙ)
    calc
      proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) Xs Zs
          = proximal_objective (symmetricSpectralLift f) X Z := by
              change proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y))
                  ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩ Zs =
                proximal_objective (symmetricSpectralLift f) X (Zs : Mₙ)
              exact subtype_proximal_objective_eq_ambient f hf_perm X hX Zs
      _ ≤ proximal_objective (symmetricSpectralLift f) X (Y : Mₙ) := hZY
      _ = proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) Xs Y := by
            change proximal_objective (symmetricSpectralLift f) X (Y : Mₙ) =
              proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y))
                ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩ Y
            exact (subtype_proximal_objective_eq_ambient f hf_perm X hX Y).symm
  · rintro ⟨Y, hY, rfl⟩
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hY ⊢
    intro W
    by_cases hW : W.IsSymm
    · let Ws : 𝕊 := ⟨W, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hW⟩
      -- On symmetric competitors, the ambient and subtype objectives coincide.
      calc
        proximal_objective (symmetricSpectralLift f) X (Y : Mₙ)
            = proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) Xs Y := by
                change proximal_objective (symmetricSpectralLift f) X (Y : Mₙ) =
                  proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y))
                    ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩ Y
                exact (subtype_proximal_objective_eq_ambient f hf_perm X hX Y).symm
        _ ≤ proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) Xs Ws := hY Ws
        _ = proximal_objective (symmetricSpectralLift f) X W := by
              change proximal_objective (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y))
                  ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩ Ws =
                proximal_objective (symmetricSpectralLift f) X (Ws : Mₙ)
              exact subtype_proximal_objective_eq_ambient f hf_perm X hX Ws
    · -- Off the symmetric locus, the ambient spectral lift is `⊤`, so the comparison is automatic.
      have htop :
          proximal_objective (symmetricSpectralLift f) X W = ⊤ := by
        rw [proximal_objective_apply, symmetricSpectralLift_apply_of_not_isSymm f W hW]
        exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
      rw [htop]
      simp

/-- Helper for Theorem 7.3: orthogonal conjugation preserves the characteristic polynomial of a
real square matrix. -/
private lemma orthogonal_conjugate_charpoly
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : Mₙ) :
    Matrix.charpoly ((U : Mₙ)ᵀ * A * (U : Mₙ)) = Matrix.charpoly A := by
  -- Cycle the orthogonal factors past the characteristic polynomial and collapse them to `1`.
  have hUUt : (U : Mₙ) * (U : Mₙ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
  calc
    Matrix.charpoly ((U : Mₙ)ᵀ * A * (U : Mₙ))
        = Matrix.charpoly (((U : Mₙ)ᵀ * A) * (U : Mₙ)) := by
            simp [mul_assoc]
    _ = Matrix.charpoly ((U : Mₙ) * ((U : Mₙ)ᵀ * A)) := by
          rw [Matrix.charpoly_mul_comm]
    _ = Matrix.charpoly (((U : Mₙ) * (U : Mₙ)ᵀ) * A) := by
          simp [mul_assoc]
    _ = Matrix.charpoly A := by
          simpa [hUUt]

/-- Helper for Theorem 7.3: orthogonal conjugation preserves symmetry, and the converse holds by
conjugating back with the inverse orthogonal matrix. -/
lemma orthogonal_conjugate_isSymm_iff
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : Mₙ) :
    ((U : Mₙ)ᵀ * A * (U : Mₙ)).IsSymm ↔ A.IsSymm := by
  constructor
  · intro h
    -- Conjugate back by `U⁻¹`; orthogonality collapses the outer factors and recovers `A`.
    have hUUt : (U : Mₙ) * (U : Mₙ)ᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
    have hsymm :=
      orthogonal_conjugate_isSymm (U := U⁻¹) h
    have hsymm' : ((U : Mₙ) * ((U : Mₙ)ᵀ * A)).IsSymm := by
      simpa [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, mul_assoc, hUUt] using hsymm
    have hEq : (U : Mₙ) * ((U : Mₙ)ᵀ * A) = A := by
      calc
        (U : Mₙ) * ((U : Mₙ)ᵀ * A) = ((U : Mₙ) * (U : Mₙ)ᵀ) * A := by
          simp [mul_assoc]
        _ = A := by
          simp [hUUt]
    simpa [hEq] using hsymm'
  · -- The forward direction is the standard orthogonal-conjugation invariance of symmetry.
    exact orthogonal_conjugate_isSymm U

/-- Helper for Theorem 7.3: orthogonal conjugation preserves the local ordered eigenvalue vector of
a real symmetric matrix. -/
lemma symmetricMatrixEigenvalues_orthogonal_conjugate_eq
    (U : Matrix.orthogonalGroup (Fin n) ℝ) {A : Mₙ} (hA : A.IsSymm) :
    symmetricMatrixEigenvalues ((U : Mₙ)ᵀ * A * (U : Mₙ))
        ((orthogonal_conjugate_isSymm_iff U A).2 hA) =
      symmetricMatrixEigenvalues A hA := by
  let B : Mₙ := (U : Mₙ)ᵀ * A * (U : Mₙ)
  have hchar : Matrix.charpoly B = Matrix.charpoly A := by
    simpa [B] using orthogonal_conjugate_charpoly U A
  have hEq :
      ((orthogonal_conjugate_isSymm_iff U A).2 hA).theorem7_3_isHermitian_of_real.eigenvalues =
        hA.theorem7_3_isHermitian_of_real.eigenvalues := by
    exact
      ((Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (hA := ((orthogonal_conjugate_isSymm_iff U A).2 hA).theorem7_3_isHermitian_of_real)
        (hB := hA.theorem7_3_isHermitian_of_real))).2 hchar
  simpa [symmetricMatrixEigenvalues, B] using hEq

/-- Helper for Theorem 7.3: the ambient spectral lift is invariant under orthogonal conjugation. -/
lemma symmetricSpectralLift_orthogonal_conjugate_eq
    (f : (Fin n → ℝ) → EReal)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : Mₙ) :
    symmetricSpectralLift f ((U : Mₙ)ᵀ * A * (U : Mₙ)) = symmetricSpectralLift f A := by
  by_cases hA : A.IsSymm
  · rw [symmetricSpectralLift_apply_of_isSymm f _ ((orthogonal_conjugate_isSymm_iff U A).2 hA),
      symmetricSpectralLift_apply_of_isSymm f _ hA,
      symmetricMatrixEigenvalues_orthogonal_conjugate_eq U hA]
  · have hconj : ¬ ((U : Mₙ)ᵀ * A * (U : Mₙ)).IsSymm := by
      intro h
      exact hA ((orthogonal_conjugate_isSymm_iff U A).1 h)
    rw [symmetricSpectralLift_apply_of_not_isSymm f _ hconj,
      symmetricSpectralLift_apply_of_not_isSymm f _ hA]

/-- Helper for Theorem 7.3: conjugating `orthogonalDiagonalMap U d` back by `Uᵀ` recovers the
diagonal matrix `diag d`. -/
lemma orthogonal_conjugate_orthogonalDiagonalMap_eq_diagonal
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (d : Fin n → ℝ) :
    (U : Mₙ)ᵀ * orthogonalDiagonalMap U d * (U : Mₙ) = Matrix.diagonal d := by
  -- Collapse the orthogonal factors on both sides of the diagonal model.
  have hUUt : (U : Mₙ) * (U : Mₙ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
  have hUtU : (U : Mₙ)ᵀ * (U : Mₙ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  calc
    (U : Mₙ)ᵀ * orthogonalDiagonalMap U d * (U : Mₙ)
        = (U : Mₙ)ᵀ * ((U : Mₙ) * Matrix.diagonal d * (U : Mₙ)ᵀ) * (U : Mₙ) := by
            rw [orthogonalDiagonalMap_apply]
    _ = ((U : Mₙ)ᵀ * (U : Mₙ)) * Matrix.diagonal d * ((U : Mₙ)ᵀ * (U : Mₙ)) := by
          simp [mul_assoc]
    _ = Matrix.diagonal d := by
          simp [hUtU]

/-- Helper for Theorem 7.3: orthogonal conjugation normalizes the proximal objective at
`orthogonalDiagonalMap U d` to the diagonal-basis proximal objective at `Matrix.diagonal d`. -/
lemma proximal_objective_symmetricSpectralLift_orthogonal_conjugate_eq
    (f : (Fin n → ℝ) → EReal) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (d : Fin n → ℝ) (Z : Mₙ) :
    proximal_objective (symmetricSpectralLift f) (orthogonalDiagonalMap U d) Z =
      proximal_objective (symmetricSpectralLift f) (Matrix.diagonal d)
        ((U : Mₙ)ᵀ * Z * (U : Mₙ)) := by
  have hsub :
      ((U : Mₙ)ᵀ * Z * (U : Mₙ)) - Matrix.diagonal d =
        (U : Mₙ)ᵀ * (Z - orthogonalDiagonalMap U d) * (U : Mₙ) := by
    calc
      ((U : Mₙ)ᵀ * Z * (U : Mₙ)) - Matrix.diagonal d
          = ((U : Mₙ)ᵀ * Z * (U : Mₙ)) -
              ((U : Mₙ)ᵀ * orthogonalDiagonalMap U d * (U : Mₙ)) := by
                rw [orthogonal_conjugate_orthogonalDiagonalMap_eq_diagonal]
      _ = (U : Mₙ)ᵀ * (Z - orthogonalDiagonalMap U d) * (U : Mₙ) := by
            simp [mul_sub, sub_mul, mul_assoc]
  have hnorm :
      ‖((U : Mₙ)ᵀ * Z * (U : Mₙ)) - Matrix.diagonal d‖ =
        ‖Z - orthogonalDiagonalMap U d‖ := by
    rw [hsub, frobenius_norm_orthogonal_conjugate_eq U (Z - orthogonalDiagonalMap U d)]
  -- Rewrite both the spectral term and the Frobenius penalty under the orthogonal change of
  -- variables from the source proof.
  rw [proximal_objective_apply, proximal_objective_apply,
    ← symmetricSpectralLift_orthogonal_conjugate_eq f U Z, hnorm]

/-- Helper for Theorem 7.3: proximal membership is invariant under orthogonal conjugation to the
diagonal basis. -/
lemma mem_prox_symmetricSpectralLift_orthogonal_conjugate_iff
    (f : (Fin n → ℝ) → EReal) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (d : Fin n → ℝ) (Z : Mₙ) :
    Z ∈ prox[symmetricSpectralLift f] (orthogonalDiagonalMap U d) ↔
      ((U : Mₙ)ᵀ * Z * (U : Mₙ)) ∈ prox[symmetricSpectralLift f] (Matrix.diagonal d) := by
  have hUtU : (U : Mₙ)ᵀ * (U : Mₙ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hUUt : (U : Mₙ) * (U : Mₙ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
  rw [mem_proximal_mapping_iff, mem_proximal_mapping_iff, isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro h V
    have hcomp := h ((U : Mₙ) * V * (U : Mₙ)ᵀ)
    have hback :
        (U : Mₙ)ᵀ * (((U : Mₙ) * V * (U : Mₙ)ᵀ)) * (U : Mₙ) = V := by
      calc
        (U : Mₙ)ᵀ * (((U : Mₙ) * V * (U : Mₙ)ᵀ)) * (U : Mₙ)
            = (((U : Mₙ)ᵀ * (U : Mₙ)) * V) * ((U : Mₙ)ᵀ * (U : Mₙ)) := by
                simp [mul_assoc]
        _ = V := by
              simp [hUtU]
    -- Compare against the inverse-changed competitor and then normalize both objectives.
    calc
      proximal_objective (symmetricSpectralLift f) (Matrix.diagonal d)
          ((U : Mₙ)ᵀ * Z * (U : Mₙ))
          = proximal_objective (symmetricSpectralLift f) (orthogonalDiagonalMap U d) Z := by
              symm
              exact proximal_objective_symmetricSpectralLift_orthogonal_conjugate_eq f U d Z
      _ ≤ proximal_objective (symmetricSpectralLift f) (orthogonalDiagonalMap U d)
            ((U : Mₙ) * V * (U : Mₙ)ᵀ) := hcomp
      _ = proximal_objective (symmetricSpectralLift f) (Matrix.diagonal d) V := by
            rw [proximal_objective_symmetricSpectralLift_orthogonal_conjugate_eq f U d
              ((U : Mₙ) * V * (U : Mₙ)ᵀ), hback]
  · intro h V
    have hcomp := h ((U : Mₙ)ᵀ * V * (U : Mₙ))
    -- Use the same objective normalization in the forward change of variables.
    calc
      proximal_objective (symmetricSpectralLift f) (orthogonalDiagonalMap U d) Z
          = proximal_objective (symmetricSpectralLift f) (Matrix.diagonal d)
              ((U : Mₙ)ᵀ * Z * (U : Mₙ)) := by
                exact proximal_objective_symmetricSpectralLift_orthogonal_conjugate_eq f U d Z
      _ ≤ proximal_objective (symmetricSpectralLift f) (Matrix.diagonal d)
            ((U : Mₙ)ᵀ * V * (U : Mₙ)) := hcomp
      _ = proximal_objective (symmetricSpectralLift f) (orthogonalDiagonalMap U d) V := by
            exact (proximal_objective_symmetricSpectralLift_orthogonal_conjugate_eq f U d V).symm

/-- Helper for Theorem 7.3: a diagonal ambient proximal point at a diagonal base matrix induces a
Euclidean proximal point of the vector profile at the diagonal entries. -/
lemma diagonal_mem_prox_euclidean_of_mem_prox_symmetricSpectralLift
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (d w : Fin n → ℝ)
    (hdiag :
      Matrix.diagonal w ∈ prox[symmetricSpectralLift f] (Matrix.diagonal d)) :
    WithLp.toLp (p := (2 : ENNReal)) w ∈
      prox[fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp]
        (WithLp.toLp (p := (2 : ENNReal)) d) := by
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hdiag
  intro y
  have hcmp := hdiag (Matrix.diagonal y.ofLp)
  -- Restrict the ambient minimization inequality to diagonal competitors and rewrite both sides.
  simpa [proximal_objective_apply, symmetricSpectralLift_diagonal_eq f hf_perm,
    Matrix.frobenius_norm_diagonal] using hcmp

/-- Helper for Theorem 7.3: the sign pattern that flips only the `i`-th coordinate. -/
def coordinate_sign_pattern (i : Fin n) : Fin n → ℝ :=
  fun j ↦ if j = i then -1 else 1

/-- Helper for Theorem 7.3: the diagonal sign-flip matrix belongs to the orthogonal group. -/
noncomputable def coordinateSignFlip (i : Fin n) : Matrix.orthogonalGroup (Fin n) ℝ := by
  let s : Fin n → ℝ := coordinate_sign_pattern i
  have hsq : ∀ j : Fin n, s j * s j = 1 := by
    intro j
    by_cases hj : j = i <;> simp [s, coordinate_sign_pattern, hj]
  refine ⟨Matrix.diagonal s, ?_⟩
  refine (Matrix.mem_orthogonalGroup_iff (A := Matrix.diagonal s) (R := ℝ)).2 ?_
  calc
    Matrix.diagonal s * (Matrix.diagonal s)ᵀ = Matrix.diagonal s * Matrix.diagonal s := by
      simp
    _ = Matrix.diagonal (fun j ↦ s j * s j) := by
      rw [Matrix.diagonal_mul_diagonal]
    _ = 1 := by
      ext j k
      by_cases hjk : j = k
      · subst hjk
        simp [hsq]
      · simp [hjk]

/-- Helper for Theorem 7.3: the diagonal sign flip fixes every diagonal matrix. -/
lemma coordinateSignFlip_fixes_diagonal
    (i : Fin n) (d : Fin n → ℝ) :
    orthogonalDiagonalMap (coordinateSignFlip i) d = Matrix.diagonal d := by
  let s : Fin n → ℝ := coordinate_sign_pattern i
  have hsq : ∀ j : Fin n, s j * s j = 1 := by
    intro j
    by_cases hj : j = i <;> simp [s, coordinate_sign_pattern, hj]
  calc
    orthogonalDiagonalMap (coordinateSignFlip i) d
        = Matrix.diagonal s * Matrix.diagonal d * Matrix.diagonal s := by
            simp [orthogonalDiagonalMap_apply, coordinateSignFlip, s]
    _ = Matrix.diagonal (fun j ↦ s j * d j * s j) := by
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    _ = Matrix.diagonal d := by
          congr 1
          ext j
          calc
            s j * d j * s j = (s j * s j) * d j := by ring
            _ = d j := by simp [hsq]

/-- Helper for Theorem 7.3: the `i,j` entry of a diagonal sign-flip conjugate is multiplied by the
signs of the `i`-th and `j`-th coordinates. -/
lemma coordinateSignFlip_conjugate_apply
    (i : Fin n) (W : Mₙ) (j k : Fin n) :
    ((((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) * W *
      (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ)) j k) =
      coordinate_sign_pattern i j * W j k * coordinate_sign_pattern i k := by
  -- Expand the diagonal sign-flip on both sides and simplify the two surviving diagonal entries.
  simp [coordinateSignFlip, Matrix.mul_apply, Matrix.diagonal, coordinate_sign_pattern]

/-- Helper for Theorem 7.3: a matrix fixed by every coordinate sign-flip conjugation must be
diagonal. -/
lemma eq_diagonal_of_fixed_by_coordinateSignFlip
    (W : Mₙ)
    (hfix : ∀ i : Fin n,
      (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) * W *
        (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ)) = W) :
    W = Matrix.diagonal (fun i ↦ W i i) := by
  ext j k
  by_cases hjk : j = k
  · -- On the diagonal, both matrices agree by definition.
    subst hjk
    simp
  · -- Flipping the `j`-th coordinate changes the sign of the `j,k` entry and fixes `W`.
    have hentry := congrArg (fun A : Mₙ ↦ A j k) (hfix j)
    have hneg : -W j k = W j k := by
      simpa [coordinateSignFlip_conjugate_apply, coordinate_sign_pattern, hjk, eq_comm] using hentry
    have hzero : W j k = 0 := by
      linarith
    simp [Matrix.diagonal, hjk, hzero]

/-- Helper for Theorem 7.3: every proximal point at a diagonal base matrix is itself diagonal. -/
lemma diagonal_basis_prox_is_diagonal
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (d : Fin n → ℝ) {W : Mₙ}
    (hW : W ∈ prox[symmetricSpectralLift f] (Matrix.diagonal d)) :
    ∃ w : Fin n → ℝ, W = Matrix.diagonal w := by
  let Ds : 𝕊 := ⟨Matrix.diagonal d, diagonal_mem_symmetricMatrices d⟩
  have hclosedconv :=
    symmetric_spectral_function_closed_convex_on_subtype f hf_perm hf_closed hf_convex
  have hproper := symmetric_spectral_function_proper_on_subtype f hf_perm
  rcases prox_eq_singleton_of_proper_closed_convex
      (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) hproper hclosedconv.1 hclosedconv.2 Ds with
      ⟨Y0, hsubsingleton⟩
  have hambient :
      prox[symmetricSpectralLift f] (Matrix.diagonal d) = {(Y0 : Mₙ)} := by
    have hdiag : (Matrix.diagonal d).IsSymm := by
      simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using diagonal_mem_symmetricMatrices d
    rw [prox_symmetricSpectralLift_eq_subtype_image f hf_perm (Matrix.diagonal d) hdiag,
      hsubsingleton, Set.image_singleton]
  have hWeq : W = (Y0 : Mₙ) := by
    have hmem := hW
    rw [hambient] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have hfix :
      ∀ i : Fin n,
        (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) * W *
          (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ)) = W := by
    intro i
    have hUtU :
        (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) *
            ((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 (coordinateSignFlip i).2
    have hflip_mem :
        (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) * W *
          (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ)) ∈
          prox[symmetricSpectralLift f] (Matrix.diagonal d) := by
      have hflip_mem' :
          (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) * W *
            (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ)) ∈
            prox[symmetricSpectralLift f]
              (orthogonalDiagonalMap (coordinateSignFlip i) d) := by
        refine (mem_prox_symmetricSpectralLift_orthogonal_conjugate_iff f
            (coordinateSignFlip i) d _).2 ?_
        have hback :
            (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) *
                ((((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) * W *
                    (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ))) *
                ((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) = W := by
          calc
            (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) *
                ((((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) * W *
                    (((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ))) *
                ((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)
                = ((((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) *
                    ((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)) * W *
                    ((((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) *
                      ((coordinateSignFlip i : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)) := by
                        simp [mul_assoc]
            _ = W := by
                  simp [hUtU]
        simpa [hback] using hW
      rw [coordinateSignFlip_fixes_diagonal i d] at hflip_mem'
      exact hflip_mem'
    have hflip_mem_singleton := hflip_mem
    rw [hambient] at hflip_mem_singleton
    exact (Set.mem_singleton_iff.mp hflip_mem_singleton).trans hWeq.symm
  refine ⟨fun i ↦ W i i, eq_diagonal_of_fixed_by_coordinateSignFlip W hfix⟩

-- Proof sketch: conjugate the ambient proximal objective for `symmetricSpectralLift f` by the
-- orthogonal change of variables determined by `U`. The extension by `⊤` forces minimizers to stay
-- symmetric, the spectral term reduces to the vector profile on the diagonal basis, and the
-- Frobenius norm is orthogonally invariant. The remaining minimization problem is the vector-side
-- proximal problem at `symmetricMatrixEigenvalues X hX`.
/-- Theorem 7.3: if `f : ℝ^n → (-∞, ∞]` is permutation symmetric, proper, closed, and convex, and
if a real symmetric matrix `X` satisfies
`X = U * diag (symmetricMatrixEigenvalues X hX) * Uᵀ`, then the proximal set of the ambient
spectral lift of `f` at `X` is the image of the Euclidean vector proximal set at the ordered
eigenvalue vector of `X` under the map `x ↦ U * diag x * Uᵀ`. The vector-side proximal problem is
stated on `EuclideanSpace ℝ (Fin n)` and evaluates `f` through `.ofLp`, matching the Frobenius
geometry of diagonal matrices. -/
theorem prox_symmetricSpectralLift_eq_image_orthogonalDiagonalMap
    (f : (Fin n → ℝ) → EReal) (hf_perm : IsPermutationSymmetricFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (X : Mₙ) (hX : X.IsSymm) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hdiag : X = orthogonalDiagonalMap U (symmetricMatrixEigenvalues X hX)) :
    prox[symmetricSpectralLift f] X =
      orthogonalDiagonalMapEuclidean U ''
        prox[fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp]
          (WithLp.toLp (p := (2 : ENNReal)) (symmetricMatrixEigenvalues X hX)) :=
by
  let Xs : 𝕊 := ⟨X, by simpa [mem_symmetricMatrices_iff, Matrix.IsSymm] using hX⟩
  let eig : Fin n → ℝ := symmetricMatrixEigenvalues X hX
  let eigLp : EuclideanSpace ℝ (Fin n) := WithLp.toLp (p := (2 : ENNReal)) eig
  have hclosedconv :=
    symmetric_spectral_function_closed_convex_on_subtype f hf_perm hf_closed hf_convex
  have hproper := symmetric_spectral_function_proper_on_subtype f hf_perm
  rcases prox_eq_singleton_of_proper_closed_convex
      (fun Y : 𝕊 ↦ f (symmetricEigenvalues Y)) hproper hclosedconv.1 hclosedconv.2 Xs with
      ⟨Y0, hsubsingleton⟩
  have hambient :
      prox[symmetricSpectralLift f] X = {(Y0 : Mₙ)} := by
    rw [prox_symmetricSpectralLift_eq_subtype_image f hf_perm X hX,
      hsubsingleton, Set.image_singleton]
  have hpullback :=
    theorem7_3_euclidean_pullback_proper_closed_convex f hf_perm hf_closed hf_convex
  rcases prox_eq_singleton_of_proper_closed_convex
      (fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp)
      hpullback.1 hpullback.2.1 hpullback.2.2 eigLp with ⟨x0, hvecsingleton⟩
  have hY0_mem : (Y0 : Mₙ) ∈ prox[symmetricSpectralLift f] X := by
    simpa [hambient]
  have hdiag_mem :
      ((U : Mₙ)ᵀ * (Y0 : Mₙ) * (U : Mₙ)) ∈
        prox[symmetricSpectralLift f] (Matrix.diagonal eig) := by
    have hbase :
        (Y0 : Mₙ) ∈ prox[symmetricSpectralLift f] (orthogonalDiagonalMap U eig) := by
      simpa [eig, hdiag] using hY0_mem
    exact (mem_prox_symmetricSpectralLift_orthogonal_conjugate_iff f U eig (Y0 : Mₙ)).1 hbase
  rcases diagonal_basis_prox_is_diagonal f hf_perm hf_closed hf_convex eig hdiag_mem with
    ⟨w, hwdiag⟩
  have hdiag_mem' :
      Matrix.diagonal w ∈ prox[symmetricSpectralLift f] (Matrix.diagonal eig) := by
    simpa [hwdiag] using hdiag_mem
  have hw_euclidean :
      WithLp.toLp (p := (2 : ENNReal)) w ∈
        prox[fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp] eigLp :=
    diagonal_mem_prox_euclidean_of_mem_prox_symmetricSpectralLift f hf_perm eig w hdiag_mem'
  have hw_eq_x0 : WithLp.toLp (p := (2 : ENNReal)) w = x0 := by
    have hmem : WithLp.toLp (p := (2 : ENNReal)) w ∈ ({x0} : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [hvecsingleton, eigLp] using hw_euclidean
    simpa using hmem
  have hx0_ofLp : x0.ofLp = w := by
    simpa using (congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y.ofLp) hw_eq_x0).symm
  have hY0_eq :
      (Y0 : Mₙ) = orthogonalDiagonalMapEuclidean U x0 := by
    have hUUt : (U : Mₙ) * (U : Mₙ)ᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff (A := (U : Mₙ)) (R := ℝ)).1 U.2
    calc
      (Y0 : Mₙ)
          = (U : Mₙ) * (((U : Mₙ)ᵀ * (Y0 : Mₙ) * (U : Mₙ))) * (U : Mₙ)ᵀ := by
              calc
                (Y0 : Mₙ) = (((U : Mₙ) * (U : Mₙ)ᵀ) * (Y0 : Mₙ)) * ((U : Mₙ) * (U : Mₙ)ᵀ) := by
                              simp [hUUt]
                _ = (U : Mₙ) * (((U : Mₙ)ᵀ * (Y0 : Mₙ) * (U : Mₙ))) * (U : Mₙ)ᵀ := by
                      simp [mul_assoc]
      _ = (U : Mₙ) * Matrix.diagonal w * (U : Mₙ)ᵀ := by
            rw [hwdiag]
      _ = orthogonalDiagonalMapEuclidean U x0 := by
            simp [orthogonalDiagonalMapEuclidean, orthogonalDiagonalMap_apply, hx0_ofLp]
  -- Both the matrix-side and vector-side proximal sets are now identified as singletons.
  calc
    prox[symmetricSpectralLift f] X = {(Y0 : Mₙ)} := hambient
    _ = {orthogonalDiagonalMapEuclidean U x0} := by rw [hY0_eq]
    _ = orthogonalDiagonalMapEuclidean U ''
          prox[fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp] eigLp := by
            rw [hvecsingleton, Set.image_singleton]

-- Proof sketch: apply `prox_symmetricSpectralLift_eq_image_orthogonalDiagonalMap` and rewrite the
-- image of the singleton set `{x}` under `orthogonalDiagonalMapEuclidean U`.
/-- If the Euclidean vector proximal set of `f` at the ordered eigenvalue vector of `X` is the
singleton `{x}`, then the proximal set of the spectral lift at `X` is the singleton
`{U * diag x.ofLp * Uᵀ}`. -/
theorem prox_symmetricSpectralLift_eq_singleton_orthogonalDiagonalMap
    {f : (Fin n → ℝ) → EReal} (hf_perm : IsPermutationSymmetricFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    {X : Mₙ} (hX : X.IsSymm) {U : Matrix.orthogonalGroup (Fin n) ℝ}
    (hdiag : X = orthogonalDiagonalMap U (symmetricMatrixEigenvalues X hX))
    {x : EuclideanSpace ℝ (Fin n)}
    (hprox : prox[fun y : EuclideanSpace ℝ (Fin n) ↦ f y.ofLp]
        (WithLp.toLp (p := (2 : ENNReal)) (symmetricMatrixEigenvalues X hX)) = {x}) :
    prox[symmetricSpectralLift f] X = {orthogonalDiagonalMapEuclidean U x} := by
  -- Rewrite the spectral proximal set via the main image formula and collapse the singleton.
  rw [prox_symmetricSpectralLift_eq_image_orthogonalDiagonalMap f hf_perm hf_closed hf_convex
    X hX U hdiag, hprox, Set.image_singleton]

end
