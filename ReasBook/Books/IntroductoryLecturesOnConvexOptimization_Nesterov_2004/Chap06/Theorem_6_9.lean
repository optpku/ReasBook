/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_42
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_33

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open PositiveSemidefiniteCone
open scoped BigOperators MatrixOrder NNReal RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Theorem 6.9: use the Frobenius normed-group structure on ambient matrices when the
proof imports Chapter 6's Fréchet-derivative formulas for trace powers. -/
local instance theoremSixNineAmbientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Theorem 6.9: scalar multiplication on ambient matrices is measured with the
Frobenius norm in the imported calculus API. -/
local instance theoremSixNineAmbientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.frobeniusNormedSpace

/-- Helper for Theorem 6.9: the ambient matrix ring carries the Frobenius-compatible normed-ring
structure expected by the Chapter 6 derivative lemmas. -/
local instance theoremSixNineAmbientMatrixNormedRing : NormedRing Mat :=
  Matrix.frobeniusNormedRing

/-- Helper for Theorem 6.9: the ambient matrix algebra over `ℝ` uses the Frobenius norm so the
imported trace-power calculus applies verbatim on this file's owner stack. -/
local instance theoremSixNineAmbientMatrixNormedAlgebra : NormedAlgebra ℝ Mat :=
  Matrix.frobeniusNormedAlgebra

attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 1001] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

/- Theorem 6.9 lies in the chapter's symmetric-matrix trace-power / Hessian spectral domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the source-facing trace-power
  owner on `𝕊^n`;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the chapter's intrinsic ordered eigenvalue
  owner on `𝕊^n`;
- mathlib `CFC.abs`, together with `CFC.abs_nonneg` and Hermitian eigenvalues, as the canonical
  absolute-value owner for real symmetric matrices;
- mathlib `iteratedFDeriv`, the canonical Hessian quadratic-form owner for scalar-valued maps.

Best owner abstraction:
- source-facing: the Hessian quadratic-form bound for the Chapter 6 owner `π_k(X) = Trace (X^k)`
  on `𝕊^n`, together with the intrinsic spectral data coming from the matrix absolute values
  `CFC.abs X` and `CFC.abs H`;
- core/canonical: `π[k] : 𝕊^n → ℝ`, `iteratedFDeriv ℝ 2`, `eigenvalues`, and `CFC.abs`;
- bridge/view: Proposition 6.33's second-derivative expansion and the spectral inequality from
  Lemma 6.14.

Primitive data:
- `k : ℕ`;
- `X H : 𝕊^n`.

Derived API:
- the source-facing trace-power owner `π[k]`;
- the Hessian quadratic form `iteratedFDeriv ℝ 2 (π[k] : 𝕊^n → ℝ) X ![H, H]`;
- the Hermitian eigenvalue vectors of the matrix absolute values `CFC.abs X` and `CFC.abs H`.

Source/core/bridge triage:
- source-facing: Theorem 6.9's Hessian quadratic-form inequality on `𝕊^n`;
- core/canonical: `π[k]`, `iteratedFDeriv`, `eigenvalues`, and `CFC.abs`;
- bridge/view: the ambient trace/Frobenius expansion used only in Proposition 6.33.
-/

/-- Helper for Theorem 6.9: the `p`th mixed trace summand in the Proposition 6.33 expansion of the
Hessian quadratic form of `π[k]`. -/
private abbrev mixed_trace_term
    (k p : ℕ) (X H : SymmMat) : ℝ :=
  ((((X : Mat)).transpose ^ (k - 2 - p)) *
      (((H : Mat)).transpose * ((((X : Mat)).transpose ^ p) * (H : Mat)))).trace

/-- Helper for Theorem 6.9: the spectral pairing on the eigenvalues of `CFC.abs X` and
`CFC.abs H` that appears on the right-hand side of the theorem. -/
private abbrev abs_eigenvalue_pairing
    (k : ℕ) (X H : SymmMat) : ℝ :=
  ∑ i : Fin n,
    (((Matrix.nonneg_iff_posSemidef.mp
        (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^ (k - 2)) *
      (((Matrix.nonneg_iff_posSemidef.mp
          (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ))

/-- Helper for Theorem 6.9: package `|X|` as a point of the positive-semidefinite cone so
Lemma 6.14 applies without changing the main theorem statement. -/
private abbrev abs_psd
    (X : SymmMat) : 𝕊^n₊ :=
  ⟨|X|, Matrix.nonneg_iff_posSemidef.mp (RealSymmetricMatrixSpace.abs_nonneg X)⟩

/-- Helper for Theorem 6.9: view the positive-semidefinite power of `|X|` back in the symmetric
matrix carrier so later trace and eigenvalue expressions stay parser-stable. -/
private abbrev abs_psd_pow
    (X : SymmMat) (p : ℝ≥0) : SymmMat :=
  (((abs_psd X) ^ p : 𝕊^n₊) : SymmMat)

/-- Helper for Theorem 6.9: rewrite the mixed Proposition 6.33 summand in the standard
`X^p H X^(k-2-p)` sandwich form used by Lemma 6.14. -/
private abbrev sandwich_trace_term
    (k p : ℕ) (X H : SymmMat) : ℝ :=
  Matrix.trace
    (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
        ((X ^ (k - 2 - p) : SymmMat) : Mat)).transpose) * (H : Mat))

/-- Helper for Theorem 6.9: this is the same sandwich trace term after replacing `X` by the
positive-semidefinite matrix `|X|`. -/
private abbrev abs_sandwich_trace_term
    (k p : ℕ) (X H : SymmMat) : ℝ :=
  Matrix.trace
    (((((abs_psd_pow X (((p : ℕ) : ℝ≥0)) : SymmMat) : Mat) * (H : Mat) *
        ((abs_psd_pow X (((k - 2 - p : ℕ) : ℝ≥0)) : SymmMat) : Mat)).transpose) *
      (H : Mat))

/-- Helper for Theorem 6.9: the PSD pairing delivered by Lemma 6.14 after the `X ↦ |X|` pivot. -/
private abbrev abs_psd_power_pairing
    (k : ℕ) (X H : SymmMat) : ℝ :=
  ∑ i : Fin n,
    eigenvalues (abs_psd_pow X (((k - 2 : ℕ) : ℝ≥0))) i *
      eigenvalues (H ^ (2 : ℕ) : SymmMat) i

/-- Helper for Theorem 6.9: packaging `|X|` into `𝕊ⁿ₊` does not change the ordered ambient
Hermitian eigenvalue list of the same matrix. -/
private theorem abs_psd_eigenvalues_eq_ambient_abs_eigenvalues
    (X : SymmMat) :
    eigenvalues (abs_psd_pow X 1) =
      (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues := by
  -- Both Hermitian structures live on the same ambient matrix `CFC.abs X`, so proof irrelevance
  -- reduces the eigenvalue identification to equality of the underlying matrices.
  have habsHerm : (CFC.abs (X : Mat)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian
  have hcoe_pow :
      (((abs_psd_pow X (1 : ℝ≥0) : SymmMat) : Mat)) =
        (((CFC.abs (X : Mat)) ^ (1 : ℝ≥0)) : Mat) := by
    simpa [abs_psd_pow, abs_psd, RealSymmetricMatrixSpace.coe_abs] using
      (PositiveSemidefiniteCone.coe_pow (abs_psd X) (1 : ℝ≥0))
  have hcoe : (((abs_psd_pow X (1 : ℝ≥0) : SymmMat) : Mat)) = CFC.abs (X : Mat) := by
    calc
      (((abs_psd_pow X (1 : ℝ≥0) : SymmMat) : Mat))
          = (((CFC.abs (X : Mat)) ^ (1 : ℝ≥0)) : Mat) := hcoe_pow
      _ = CFC.abs (X : Mat) := by
            simpa using (CFC.nnrpow_one (CFC.abs (X : Mat)))
  exact
    ((habsHerm.eigenvalues_eq_eigenvalues_iff (isHermitian (abs_psd_pow X 1))).2 <| by
      simp [hcoe]).symm

/-- Helper for Theorem 6.9: the cone power `abs_psd_pow X p` is the ambient nonnegative power of
`CFC.abs X`, viewed back in the symmetric-matrix carrier. -/
private theorem abs_psd_pow_coe_eq_ambient_abs_nnrpow
    (X : SymmMat) (p : ℝ≥0) :
    (((abs_psd_pow X p : SymmMat) : Mat)) = (((CFC.abs (X : Mat)) ^ p) : Mat) := by
  -- Unfold the cone packaging once so later spectral rewrites can stay on the ambient matrix side.
  simpa [abs_psd_pow, abs_psd, RealSymmetricMatrixSpace.coe_abs] using
    (PositiveSemidefiniteCone.coe_pow (abs_psd X) p)

/-- Helper for Theorem 6.9: the intrinsic square `H²` has the same ordered eigenvalues as the
square of the positive-semidefinite absolute value `|H|²`. -/
private theorem square_eigenvalues_eq_abs_psd_square_eigenvalues
    (H : SymmMat) :
    eigenvalues (H ^ (2 : ℕ) : SymmMat) =
      eigenvalues (abs_psd_pow H (2 : ℝ≥0)) := by
  -- The matrices `H²` and `|H|²` coincide because `H` is self-adjoint and
  -- `|H|² = Hᵀ H = H²`.
  have hmat : (((H ^ (2 : ℕ) : SymmMat) : Mat)) = ((abs_psd_pow H (2 : ℝ≥0) : SymmMat) : Mat) := by
    calc
      (((H ^ (2 : ℕ) : SymmMat) : Mat)) = (H : Mat) * (H : Mat) := by
        simp [RealSymmetricMatrixSpace.coe_pow, pow_two]
      _ = star (H : Mat) * (H : Mat) := by
        rw [show star (H : Mat) = (H : Mat) by
          simpa using (RealSymmetricMatrixSpace.isHermitian H).eq]
      _ = (CFC.abs (H : Mat)) ^ (2 : ℝ≥0) := by
        simpa using (CFC.abs_nnrpow_two (H : Mat)).symm
      _ = ((abs_psd_pow H (2 : ℝ≥0) : SymmMat) : Mat) := by
        rw [abs_psd_pow_coe_eq_ambient_abs_nnrpow]
  exact
    ((isHermitian (H ^ (2 : ℕ) : SymmMat)).eigenvalues_eq_eigenvalues_iff
      (isHermitian (abs_psd_pow H (2 : ℝ≥0)))).2 <| by
        simp [hmat]

/-- Helper for Theorem 6.9: the Proposition 6.33 summand is exactly the standard sandwich trace
expression once the symmetry of `X` and `H` is used. -/
private theorem mixed_trace_term_eq_sandwich_trace_term
    (k p : ℕ) (X H : SymmMat) :
    mixed_trace_term k p X H = sandwich_trace_term k p X H := by
  -- Expand both trace formulas and use symmetry to align the factor order with Lemma 6.14.
  simp [mixed_trace_term, sandwich_trace_term, Matrix.mul_assoc,
    RealSymmetricMatrixSpace.coe_pow, (RealSymmetricMatrixSpace.isSymm X).eq,
    (RealSymmetricMatrixSpace.isSymm H).eq]

/-- Helper for Theorem 6.9: conjugating the intrinsic natural power `X^m` by the orthogonal
eigenbasis of `X` turns it into the diagonal matrix of the powered ordered eigenvalues. -/
private theorem conjugatedNatPower_eq_diagonalPow
    (m : ℕ) (X : SymmMat) :
    let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
    star (U : Mat) * (((X ^ m : SymmMat) : Mat)) * (U : Mat) =
      Matrix.diagonal (fun i => (eigenvalues X i) ^ m) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
  have hdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star U)) ((X : Mat)) =
        Matrix.diagonal (eigenvalues X) := by
    -- Move `X` into its fixed eigenbasis once, so later power rewrites stay purely diagonal.
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      (isHermitian X).conjStarAlgAut_star_eigenvectorUnitary
  calc
    star (U : Mat) * (((X ^ m : SymmMat) : Mat)) * (U : Mat)
        = ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (((X ^ m : SymmMat) : Mat)) := by
            simp [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
    _ = (((Unitary.conjStarAlgAut ℝ Mat) (star U)) ((X : Mat))) ^ m := by
          rw [show (((X ^ m : SymmMat) : Mat)) = (X : Mat) ^ m by
            simp [RealSymmetricMatrixSpace.coe_pow]]
          rw [map_pow]
    _ = (Matrix.diagonal (eigenvalues X)) ^ m := by
          rw [hdiag]
    _ = Matrix.diagonal (fun i => (eigenvalues X i) ^ m) := by
          simpa [Pi.pow_apply] using Matrix.diagonal_pow (eigenvalues X) m

/-- Helper for Theorem 6.9: the ambient absolute value `CFC.abs X` is diagonalized by the same
orthogonal eigenbasis as `X`, with diagonal entries `|λ_i(X)|`. -/
private theorem conjugatedAbs_eq_diagonalAbsEigenvalues
    (X : SymmMat) :
    let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
    star (U : Mat) * (CFC.abs (X : Mat)) * (U : Mat) =
      Matrix.diagonal (fun i => |eigenvalues X i|) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
  have habs_cfc : CFC.abs (X : Mat) = (isHermitian X).cfc (fun x => |x|) := by
    -- Rewrite the absolute value as the Hermitian functional calculus so the spectral theorem can
    -- evaluate it entrywise on the ordered eigenvalue list.
    rw [CFC.abs_eq_cfc_norm (X : Mat) (ha := by simpa using (isHermitian X)), (isHermitian X).cfc_eq]
    simp [Real.norm_eq_abs]
  rw [habs_cfc, Matrix.IsHermitian.cfc]
  simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
    unitary_mul_conjugated_mul_star (star U)
      (Matrix.diagonal (fun i => |eigenvalues X i|))

/-- Helper for Theorem 6.9: positive natural powers of `|X|` are diagonalized by the eigenbasis of
`X`, with diagonal entries `|λ_i(X)|^m`. -/
private theorem conjugatedAbsNatPower_eq_diagonalAbsPow
    (m : ℕ) (hm : 0 < m) (X : SymmMat) :
    let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
    star (U : Mat) * (((abs_psd_pow X (m : ℝ≥0) : SymmMat) : Mat)) * (U : Mat) =
      Matrix.diagonal (fun i => |eigenvalues X i| ^ m) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
  have hpow :
      (((abs_psd_pow X (m : ℝ≥0) : SymmMat) : Mat)) = (CFC.abs (X : Mat)) ^ m := by
    -- Convert the cone power back to the ambient absolute value and use that positive nat-cast
    -- exponents agree with ordinary matrix powers on nonnegative Hermitian matrices.
    calc
      (((abs_psd_pow X (m : ℝ≥0) : SymmMat) : Mat))
          = ((CFC.abs (X : Mat)) ^ (m : ℝ≥0)) := by
              simpa using abs_psd_pow_coe_eq_ambient_abs_nnrpow X (m : ℝ≥0)
      _ = ((CFC.abs (X : Mat)) ^ (m : ℝ)) := by
            rw [CFC.nnrpow_eq_rpow (show 0 < (m : ℝ≥0) by exact_mod_cast hm)]
            change (CFC.abs (X : Mat)) ^ ((m : ℕ) : ℝ) = (CFC.abs (X : Mat)) ^ (m : ℝ)
            rfl
      _ = (CFC.abs (X : Mat)) ^ m := by
            simpa using CFC.rpow_natCast (CFC.abs (X : Mat)) m (CFC.abs_nonneg (X : Mat))
  have habsdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (CFC.abs (X : Mat)) =
        Matrix.diagonal (fun i => |eigenvalues X i|) := by
    -- Reuse the fixed eigenbasis of `X` for `|X|`, which is the stable diagonal surface needed
    -- both for the trace majorization and for the final spectral transport.
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      conjugatedAbs_eq_diagonalAbsEigenvalues X
  calc
    star (U : Mat) * (((abs_psd_pow X (m : ℝ≥0) : SymmMat) : Mat)) * (U : Mat)
        = ((Unitary.conjStarAlgAut ℝ Mat) (star U))
            (((abs_psd_pow X (m : ℝ≥0) : SymmMat) : Mat)) := by
              simp [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
    _ = ((Unitary.conjStarAlgAut ℝ Mat) (star U)) ((CFC.abs (X : Mat)) ^ m) := by
          rw [hpow]
    _ = (((Unitary.conjStarAlgAut ℝ Mat) (star U)) (CFC.abs (X : Mat))) ^ m := by
          rw [map_pow]
    _ = (Matrix.diagonal (fun i => |eigenvalues X i|)) ^ m := by
          rw [habsdiag]
    _ = Matrix.diagonal (fun i => |eigenvalues X i| ^ m) := by
          simpa [Pi.pow_apply] using Matrix.diagonal_pow (fun i => |eigenvalues X i|) m

/-- Helper for Theorem 6.9: in the eigenbasis of `X`, the source sandwich trace term becomes the
diagonal weighted trace with weights `λ_i(X)^(k-2-p)` and `λ_j(X)^p`. -/
private theorem sandwichTrace_eq_diagonalNatWeightedTrace
    (k p : ℕ) (X H : SymmMat) :
    let q := k - 2 - p
    let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
    let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
    sandwich_trace_term k p X H =
      Matrix.trace
        (Matrix.diagonal (fun i => (eigenvalues X i) ^ q) * K *
          Matrix.diagonal (fun j => (eigenvalues X j) ^ p) * K) := by
  let q := k - 2 - p
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
  let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
  have hleft :
      sandwich_trace_term k p X H =
        Matrix.trace
          ((((X ^ q : SymmMat) : Mat) * (H : Mat) * ((X ^ p : SymmMat) : Mat)) * (H : Mat)) := by
    -- Remove the transpose in the sandwich term by symmetry of `H`, `X^p`, and `X^q`.
    simp [sandwich_trace_term, q, Matrix.transpose_mul, Matrix.mul_assoc,
      RealSymmetricMatrixSpace.coe_pow, (RealSymmetricMatrixSpace.isSymm X).eq,
      (RealSymmetricMatrixSpace.isSymm H).eq]
  have hqdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (((X ^ q : SymmMat) : Mat)) =
        Matrix.diagonal (fun i => (eigenvalues X i) ^ q) := by
    -- The `q`th intrinsic power stays diagonal in the eigenbasis fixed by `X`.
    simpa [U, q, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      conjugatedNatPower_eq_diagonalPow q X
  have hpdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (((X ^ p : SymmMat) : Mat)) =
        Matrix.diagonal (fun i => (eigenvalues X i) ^ p) := by
    -- The same diagonalization applies to the `p`th intrinsic power.
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      conjugatedNatPower_eq_diagonalPow p X
  have hHconj : ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (H : Mat) = K := by
    -- The direction matrix is conjugated once and then reused on both sides of the weighted
    -- diagonal trace identity.
    simp [K, U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
  rw [hleft]
  calc
    Matrix.trace ((((X ^ q : SymmMat) : Mat) * (H : Mat) * ((X ^ p : SymmMat) : Mat)) * (H : Mat))
        = Matrix.trace
            (((Unitary.conjStarAlgAut ℝ Mat) (star U))
              ((((X ^ q : SymmMat) : Mat) * (H : Mat) * ((X ^ p : SymmMat) : Mat)) *
                (H : Mat))) := by
              symm
              exact
                Matrix.trace_map
                  ((Unitary.conjStarAlgAut ℝ Mat) (star U))
                  ((((X ^ q : SymmMat) : Mat) * (H : Mat) * ((X ^ p : SymmMat) : Mat)) *
                    (H : Mat))
    _ = Matrix.trace
          (Matrix.diagonal (fun i => (eigenvalues X i) ^ q) * K *
            Matrix.diagonal (fun j => (eigenvalues X j) ^ p) * K) := by
          -- Evaluate the conjugated product factorwise after both powers of `X` have been put on
          -- the diagonal.
          simp_rw [map_mul]
          rw [hqdiag, hpdiag]
          simp [hHconj, K, U, Matrix.mul_assoc]

/-- Helper for Theorem 6.9: every Proposition 6.33 sandwich summand is bounded directly by the
PSD eigenvalue pairing after replacing the signed weights of `X` by the absolute-value weights of
`|X|` in a fixed eigenbasis. -/
private theorem sandwich_trace_term_le_abs_psd_power_pairing
    (k p : ℕ) (X H : SymmMat) (hk : 3 ≤ k) (hp : p ∈ Finset.range (k - 1)) :
    sandwich_trace_term k p X H ≤ abs_psd_power_pairing k X H := by
  let q : ℕ := k - 2 - p
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian X).eigenvectorUnitary
  let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
  let lam : Fin n → ℝ := eigenvalues X
  let lamAbs : Fin n → ℝ := fun i => |lam i|
  have hp_lt : p < k - 1 := Finset.mem_range.mp hp
  have hp_le : p ≤ k - 2 := by
    omega
  have hsum_nat : p + q = k - 2 := by
    dsimp [q]
    exact Nat.add_sub_of_le hp_le
  have hk_sub_pos : 0 < k - 2 := by
    omega
  have hK : Matrix.transpose K = K := by
    -- The conjugated direction stays symmetric in the fixed eigenbasis of `X`.
    simpa [K] using conjugatedDirection_transpose_eq_self U H
  have hsandwich :
      sandwich_trace_term k p X H =
        Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ q) * K * Matrix.diagonal (fun j => lam j ^ p) * K) := by
    -- Rewrite the source term in the fixed eigenbasis once so only scalar weight estimates remain.
    simpa [q, U, K, lam] using sandwichTrace_eq_diagonalNatWeightedTrace k p X H
  have hmixed_sum :
      Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ q) * K * Matrix.diagonal (fun j => lam j ^ p) * K) =
        ∑ i : Fin n, ∑ j : Fin n, lam i ^ q * (K i j) ^ (2 : ℕ) * lam j ^ p := by
    -- Expand the diagonal trace entrywise into a weighted square sum.
    simpa using
      diagonal_weighted_trace_eq_sumSquares
        (fun i => lam i ^ q)
        (fun j => lam j ^ p)
        K hK
  have habs_weighted :
      ∑ i : Fin n, ∑ j : Fin n, lam i ^ q * (K i j) ^ (2 : ℕ) * lam j ^ p
        ≤
          ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ q * (K i j) ^ (2 : ℕ) * lamAbs j ^ p := by
    -- Replace each signed scalar weight by its absolute-value majorant before invoking the PSD
    -- weighted-square inequality.
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    have hsq_nonneg : 0 ≤ (K i j) ^ (2 : ℕ) := by
      positivity
    have hpow_abs_i : |lam i ^ q| = lamAbs i ^ q := by
      simp [lamAbs, abs_pow]
    have hpow_abs_j : |lam j ^ p| = lamAbs j ^ p := by
      simp [lamAbs, abs_pow]
    have habs :
        |lam i ^ q * (K i j) ^ (2 : ℕ) * lam j ^ p|
          = lamAbs i ^ q * (K i j) ^ (2 : ℕ) * lamAbs j ^ p := by
      rw [abs_mul, abs_mul, abs_of_nonneg hsq_nonneg, hpow_abs_i, hpow_abs_j]
    exact le_trans (le_abs_self _) (by rw [habs])
  have hlam_nonneg : ∀ i : Fin n, 0 ≤ lamAbs i := by
    intro i
    exact abs_nonneg _
  have habs_power :
      ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ q * (K i j) ^ (2 : ℕ) * lamAbs j ^ p
        ≤
          ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ (k - 2) * (K i j) ^ (2 : ℕ) := by
    -- Apply the scalar power inequality on the nonnegative absolute eigenvalue list.
    have hweighted :=
      weightedMixedSquares_le_powerSquares
        (p := (p : ℝ≥0))
        (q := (q : ℝ≥0))
        hK hlam_nonneg
    have hweighted_nat :
        ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ q * (K i j) ^ (2 : ℕ) * lamAbs j ^ p
          ≤
            ∑ i : Fin n, ∑ j : Fin n,
              lamAbs i ^ ((((p : ℕ) : ℝ≥0) + ((q : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) * (K i j) ^ (2 : ℕ) := by
      simpa [lamAbs, Real.rpow_natCast] using hweighted
    have hsum_real :
        ((((p : ℕ) : ℝ≥0) + ((q : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) = ((k - 2 : ℕ) : ℝ) := by
      have hsum_cast_nat : ((p + q : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) := by
        exact_mod_cast hsum_nat
      simpa using hsum_cast_nat
    calc
      ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ q * (K i j) ^ (2 : ℕ) * lamAbs j ^ p
          ≤
            ∑ i : Fin n, ∑ j : Fin n,
              lamAbs i ^ ((((p : ℕ) : ℝ≥0) + ((q : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) * (K i j) ^ (2 : ℕ) :=
            hweighted_nat
      _ =
        ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ (k - 2) * (K i j) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [hsum_real, Real.rpow_natCast]
  have hpair_sum :
      Matrix.trace (Matrix.diagonal (fun i => lamAbs i ^ (k - 2)) * K * K) =
        ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ (k - 2) * (K i j) ^ (2 : ℕ) := by
    -- Expand the pure power-weighted trace in the same eigenbasis.
    calc
      Matrix.trace (Matrix.diagonal (fun i => lamAbs i ^ (k - 2)) * K * K)
          =
        Matrix.trace
          (Matrix.diagonal (fun i => lamAbs i ^ (k - 2)) * K *
            Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * K) := by
              simp [Matrix.mul_assoc]
      _ =
        ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ (k - 2) * (K i j) ^ (2 : ℕ) * (1 : ℝ) := by
          simpa using
            diagonal_weighted_trace_eq_sumSquares
              (fun i => lamAbs i ^ (k - 2))
              (fun _ : Fin n => (1 : ℝ))
              K hK
      _ =
        ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ (k - 2) * (K i j) ^ (2 : ℕ) := by
          simp
  have hpair_trace :
      Matrix.trace (Matrix.diagonal (fun i => lamAbs i ^ (k - 2)) * K * K) =
        ⟪((abs_psd X) ^ (((k - 2 : ℕ) : ℝ≥0) : ℝ≥0) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := by
    let A : Mat :=
      ((((abs_psd X) ^ (((k - 2 : ℕ) : ℝ≥0) : ℝ≥0) : 𝕊^n₊) : SymmMat) : Mat)
    have hdiag_abs_pow :
        star (U : Mat) * A * (U : Mat) =
          Matrix.diagonal (fun i => lamAbs i ^ (k - 2)) := by
      -- The total positive exponent `k - 2` keeps `|X|^(k-2)` on the same diagonal surface.
      simpa [A, U, lam, lamAbs] using
        conjugatedAbsNatPower_eq_diagonalAbsPow (k - 2) hk_sub_pos X
    have hpow_symm :
        Matrix.transpose A = A := by
      simpa [A] using
        (isSymm (((abs_psd X) ^ (((k - 2 : ℕ) : ℝ≥0) : ℝ≥0) : 𝕊^n₊) : SymmMat)).eq
    -- Translate the diagonal pure-power trace back to the Frobenius pairing with `|X|^(k-2)`.
    calc
      Matrix.trace (Matrix.diagonal (fun i => lamAbs i ^ (k - 2)) * K * K)
          = Matrix.trace
              (star (U : Mat) * A * (U : Mat) * K * K) := by
                  rw [hdiag_abs_pow]
      _ = Matrix.trace
            (star (U : Mat) * A * (H : Mat) * (H : Mat) * (U : Mat)) := by
                have hUK : (U : Mat) * K = (H : Mat) * (U : Mat) := by
                  have hUK' :
                      (U : Mat) * (star (U : Mat) * ((H : Mat) * (U : Mat))) =
                        (H : Mat) * (U : Mat) := by
                    have hcancel : (U : Mat) * star (U : Mat) = (1 : Mat) := by
                      exact Unitary.coe_mul_star_self U
                    calc
                      (U : Mat) * (star (U : Mat) * ((H : Mat) * (U : Mat)))
                          = ((U : Mat) * star (U : Mat)) * ((H : Mat) * (U : Mat)) := by
                              rw [Matrix.mul_assoc]
                      _ = (1 : Mat) * ((H : Mat) * (U : Mat)) := by
                            exact congrArg (fun M : Mat ↦ M * ((H : Mat) * (U : Mat))) hcancel
                      _ = (H : Mat) * (U : Mat) := by
                            simp
                  simpa [K, Matrix.mul_assoc] using hUK'
                calc
                  Matrix.trace (star (U : Mat) * A * (U : Mat) * K * K)
                      = Matrix.trace (star (U : Mat) * A * ((U : Mat) * K) * K) := by
                          simp [Matrix.mul_assoc]
                  _ = Matrix.trace (star (U : Mat) * A * ((H : Mat) * (U : Mat)) * K) := by
                        rw [hUK]
                  _ = Matrix.trace (star (U : Mat) * A * (H : Mat) * (U : Mat) * K) := by
                        simp [Matrix.mul_assoc]
                  _ = Matrix.trace (star (U : Mat) * A * (H : Mat) * ((U : Mat) * K)) := by
                        simp [Matrix.mul_assoc]
                  _ = Matrix.trace (star (U : Mat) * A * (H : Mat) * ((H : Mat) * (U : Mat))) := by
                        rw [hUK]
                  _ = Matrix.trace (star (U : Mat) * A * (H : Mat) * (H : Mat) * (U : Mat)) := by
                        simp [Matrix.mul_assoc]
      _ = Matrix.trace
            (A * (H : Mat) * (H : Mat)) := by
                simpa [Matrix.mul_assoc] using
                  trace_unitary_conjugation (star U) (A * (H : Mat) * (H : Mat))
      _ = ⟪((abs_psd X) ^ (((k - 2 : ℕ) : ℝ≥0) : ℝ≥0) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := by
            rw [RealSymmetricMatrixSpace.frobeniusInner_def, hpow_symm]
            simp [A, RealSymmetricMatrixSpace.coe_pow, pow_two, Matrix.mul_assoc]
  -- Chain the diagonal trace rewrite, the absolute-value majorization, and the PSD eigenvalue
  -- pairing bound in the fixed eigenbasis.
  calc
    sandwich_trace_term k p X H
        = Matrix.trace
            (Matrix.diagonal (fun i => lam i ^ q) * K * Matrix.diagonal (fun j => lam j ^ p) * K) :=
          hsandwich
    _ = ∑ i : Fin n, ∑ j : Fin n, lam i ^ q * (K i j) ^ (2 : ℕ) * lam j ^ p := hmixed_sum
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ q * (K i j) ^ (2 : ℕ) * lamAbs j ^ p :=
          habs_weighted
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, lamAbs i ^ (k - 2) * (K i j) ^ (2 : ℕ) := habs_power
    _ = Matrix.trace (Matrix.diagonal (fun i => lamAbs i ^ (k - 2)) * K * K) := hpair_sum.symm
    _ = ⟪((abs_psd X) ^ (((k - 2 : ℕ) : ℝ≥0) : ℝ≥0) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := hpair_trace
    _ ≤ abs_psd_power_pairing k X H := by
          simpa [abs_psd_power_pairing, abs_psd_pow] using
            (power_pairing_le_eigenvalue_pairing
              ((((k - 2 : ℕ) : ℝ≥0) : ℝ≥0))
              (abs_psd X) H)

/-- Helper for Theorem 6.9: once `X` is replaced by the positive-semidefinite matrix `|X|`,
Lemma 6.14 gives the required bound by the PSD eigenvalue pairing at exponent `k - 2`. -/
private theorem abs_sandwich_trace_term_le_abs_psd_power_pairing
    (k p : ℕ) (X H : SymmMat) (hp : p ∈ Finset.range (k - 1)) :
    abs_sandwich_trace_term k p X H ≤ abs_psd_power_pairing k X H := by
  -- Route correction: the imported Chapter 6 Lemma 6.14 file is currently unstable, so this
  -- theorem now isolates exactly the local `|X|`-specialized PSD sandwich bound still needed here.
  have hp_lt : p < k - 1 := Finset.mem_range.mp hp
  have hp_le : p ≤ k - 2 := by
    omega
  have hsum_nat : p + (k - 2 - p) = k - 2 := Nat.add_sub_of_le hp_le
  have hsum :
      (((p : ℕ) : ℝ≥0) + (((k - 2 - p : ℕ) : ℝ≥0))) = (((k - 2 : ℕ) : ℝ≥0) : ℝ≥0) := by
    exact_mod_cast hsum_nat
  -- Use the already proved two-step PSD comparison from Lemma 6.14 and then rewrite the total
  -- exponent back to the source-facing `k - 2` surface.
  calc
    abs_sandwich_trace_term k p X H
      ≤ ⟪((abs_psd X) ^
            ((((p : ℕ) : ℝ≥0) + (((k - 2 - p : ℕ) : ℝ≥0))) : ℝ≥0) : 𝕊^n₊),
          H ^ (2 : ℕ)⟫_F := by
            simpa [abs_sandwich_trace_term, abs_psd_pow] using
              (mixed_power_trace_le_power_pairing
                (((p : ℕ) : ℝ≥0))
                (((k - 2 - p : ℕ) : ℝ≥0))
                (abs_psd X) H)
    _ = ⟪((abs_psd X) ^ (((k - 2 : ℕ) : ℝ≥0) : ℝ≥0) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := by
          rw [hsum]
    _ ≤ abs_psd_power_pairing k X H := by
          simpa [abs_psd_power_pairing, abs_psd_pow] using
            (power_pairing_le_eigenvalue_pairing
              ((((k - 2 : ℕ) : ℝ≥0) : ℝ≥0))
              (abs_psd X) H)

/-- Helper for Theorem 6.9: on the ordered `eigenvalues₀` surface, the positive cone power
`|X|^m` has eigenvalues obtained by taking the `m`th powers of the ambient absolute eigenvalues of
`X`. -/
private theorem absPsdPowOrderedEigenvalues_eq_ambientAbsEigenvaluesPow
    (m : ℕ) (hm : 0 < m) (X : SymmMat) :
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (by simp)
    (isHermitian (abs_psd_pow X (m : ℝ≥0))).eigenvalues₀ =
      fun i ↦
        ((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues (e i)) ^ m := by
  let A : SymmMat := abs_psd_pow X (m : ℝ≥0)
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (by simp)
  let d : Fin n → ℝ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues
  let d₀ : Fin (Fintype.card (Fin n)) → ℝ := fun i ↦ d (e i)
  have hd₀_eq (i : Fin (Fintype.card (Fin n))) :
      d₀ i = (isHermitian (abs_psd_pow X 1)).eigenvalues₀ i := by
    -- Reindex the already settled `m = 1` absolute-eigenvalue identity to the ordered surface.
    have hi := congrFun (abs_psd_eigenvalues_eq_ambient_abs_eigenvalues X) (e i)
    simpa [d₀, d, e, RealSymmetricMatrixSpace.eigenvalues, Matrix.IsHermitian.eigenvalues] using
      hi.symm
  have hd₀_antitone : Antitone d₀ := by
    -- The ordered absolute eigenvalue list is antitone because it is exactly the `eigenvalues₀`
    -- list of the positive-semidefinite matrix `|X|`.
    intro i j hij
    rw [hd₀_eq i, hd₀_eq j]
    exact (isHermitian (abs_psd_pow X 1)).eigenvalues₀_antitone hij
  have hd₀_nonneg (i : Fin (Fintype.card (Fin n))) : 0 ≤ d₀ i := by
    -- Every ambient absolute eigenvalue is nonnegative.
    exact
      (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).eigenvalues_nonneg (e i)
  have hd₀pow_antitone : Antitone (fun i : Fin (Fintype.card (Fin n)) ↦ d₀ i ^ m) := by
    -- Raising a nonnegative antitone list to a natural power preserves the order.
    intro i j hij
    exact pow_le_pow_left₀ (hd₀_nonneg j) (hd₀_antitone hij) m
  have habs_one :
      (((abs_psd_pow X (1 : ℝ≥0) : SymmMat) : Mat)) = CFC.abs (X : Mat) := by
    -- The exponent-one cone power is exactly the ambient absolute value.
    calc
      (((abs_psd_pow X (1 : ℝ≥0) : SymmMat) : Mat))
          = ((CFC.abs (X : Mat)) ^ (1 : ℝ≥0)) := by
              simpa using abs_psd_pow_coe_eq_ambient_abs_nnrpow X (1 : ℝ≥0)
      _ = CFC.abs (X : Mat) := by
            simpa using (CFC.nnrpow_one (CFC.abs (X : Mat)))
  have hAeq_cfc :
      (((A : SymmMat) : Mat)) = cfc (fun x : ℝ ↦ x ^ m) (((abs_psd_pow X 1 : SymmMat) : Mat)) := by
    calc
      (((A : SymmMat) : Mat)) = (CFC.abs (X : Mat)) ^ m := by
        -- Convert the cone power back to the ambient matrix power of `CFC.abs X`.
        calc
          (((A : SymmMat) : Mat)) = ((CFC.abs (X : Mat)) ^ (m : ℝ≥0)) := by
            simpa [A] using abs_psd_pow_coe_eq_ambient_abs_nnrpow X (m : ℝ≥0)
          _ = ((CFC.abs (X : Mat)) ^ (m : ℝ)) := by
            rw [CFC.nnrpow_eq_rpow (show 0 < (m : ℝ≥0) by exact_mod_cast hm)]
            change (CFC.abs (X : Mat)) ^ ((m : ℕ) : ℝ) = (CFC.abs (X : Mat)) ^ (m : ℝ)
            rfl
          _ = (CFC.abs (X : Mat)) ^ m := by
            simpa using CFC.rpow_natCast (CFC.abs (X : Mat)) m (CFC.abs_nonneg (X : Mat))
      _ = ((((abs_psd_pow X (1 : ℝ≥0) : SymmMat) : Mat)) ^ m) := by
            rw [habs_one]
      _ = cfc (fun x : ℝ ↦ x ^ m) (((abs_psd_pow X 1 : SymmMat) : Mat)) := by
            symm
            exact cfc_pow_id (((abs_psd_pow X 1 : SymmMat) : Mat)) m
              (ha := by simpa using (isHermitian (abs_psd_pow X 1)))
  have hchar :
      (((A : SymmMat) : Mat)).charpoly =
        ∏ i : Fin (Fintype.card (Fin n)), (Polynomial.X - Polynomial.C (d₀ i ^ m)) := by
    -- Compute the characteristic polynomial through the functional calculus description and then
    -- reindex the product to the ordered `eigenvalues₀` index type.
    calc
      (((A : SymmMat) : Mat)).charpoly
          = (cfc (fun x : ℝ ↦ x ^ m) (((abs_psd_pow X 1 : SymmMat) : Mat))).charpoly := by
        rw [← hAeq_cfc]
      _ = ∏ i : Fin n, (Polynomial.X - Polynomial.C ((eigenvalues (abs_psd_pow X 1) i) ^ m)) := by
            simpa using
              (isHermitian (abs_psd_pow X 1)).charpoly_cfc_eq (fun x : ℝ ↦ x ^ m)
      _ = ∏ i : Fin n, (Polynomial.X - Polynomial.C (d i ^ m)) := by
            exact congrArg
              (fun f : Fin n → ℝ ↦ ∏ i : Fin n, (Polynomial.X - Polynomial.C (f i ^ m)))
              (abs_psd_eigenvalues_eq_ambient_abs_eigenvalues X)
      _ = ∏ i : Fin (Fintype.card (Fin n)), (Polynomial.X - Polynomial.C (d₀ i ^ m)) := by
            symm
            simpa [d₀] using
              (Equiv.prod_comp e (fun i : Fin n ↦ Polynomial.X - Polynomial.C (d i ^ m)))
  have hprod_ne :
      ∏ i : Fin (Fintype.card (Fin n)), (Polynomial.X - Polynomial.C (d₀ i ^ m)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ Polynomial.X_sub_C_ne_zero (d₀ i ^ m))
  have hroots :
      (((A : SymmMat) : Mat)).charpoly.roots =
        Multiset.map (RCLike.ofReal ∘ fun i : Fin (Fintype.card (Fin n)) ↦ d₀ i ^ m)
          Finset.univ.val := by
    -- Rewrite the characteristic polynomial roots directly to the powered ordered list before
    -- invoking the canonical sorted-root normal form.
    rw [hchar, Polynomial.roots_prod _ Finset.univ hprod_ne]
    simp_rw [Polynomial.roots_X_sub_C]
    simpa [Function.comp_def] using
      (Multiset.bind_singleton
        (s := Finset.univ.val)
        (f := fun i : Fin (Fintype.card (Fin n)) ↦ RCLike.ofReal (d₀ i ^ m)))
  have hsort :
      ((((A : SymmMat) : Mat)).charpoly.roots.map RCLike.re).sort (· ≥ ·) =
        List.ofFn (fun i : Fin (Fintype.card (Fin n)) ↦ d₀ i ^ m) := by
    -- The diagonal target list is already ordered, so sorting the explicit root multiset returns
    -- the same `List.ofFn`.
    rw [hroots]
    let l : List ℝ := List.ofFn (fun i : Fin (Fintype.card (Fin n)) ↦ d₀ i ^ m)
    have hl_multiset :
        (Multiset.map (RCLike.ofReal ∘ fun i : Fin (Fintype.card (Fin n)) ↦ d₀ i ^ m)
          Finset.univ.val).map (RCLike.re : ℝ → ℝ) = (l : Multiset ℝ) := by
      -- Expand the root multiset to the underlying multiset of the explicit ordered list.
      simp [l, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def]
    have hl_sorted : l.SortedGE := by
      -- Record the powered list as a genuinely sorted list before converting to the pairwise
      -- predicate expected by `mergeSort`.
      simpa [l] using hd₀pow_antitone.sortedGE_ofFn
    have hl_pairwise :
        l.Pairwise (fun a b : ℝ ↦ decide (b ≤ a) = true) := by
      -- Express the antitone powered list in the exact decidable relation expected by
      -- `List.mergeSort_of_pairwise`.
      simpa [decide_eq_true_eq] using hl_sorted.pairwise
    rw [hl_multiset]
    simpa [l, Multiset.coe_sort] using List.mergeSort_of_pairwise hl_pairwise
  -- Compare the canonical sorted-root description of `eigenvalues₀` with the explicit powered
  -- absolute-eigenvalue list.
  rw [← List.ofFn_inj]
  calc
    List.ofFn (isHermitian A).eigenvalues₀
        = ((((A : SymmMat) : Mat)).charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
            symm
            exact (isHermitian A).sort_roots_charpoly_eq_eigenvalues₀
    _ = List.ofFn (fun i : Fin (Fintype.card (Fin n)) ↦ d₀ i ^ m) := hsort

/-- Helper for Theorem 6.9: for a positive natural exponent, taking the nat-cast cone power of
`|X|` raises each ambient absolute eigenvalue of `X` to the same natural power. -/
private theorem abs_psd_pow_eigenvalues_eq_ambient_abs_eigenvalues_pow
    (m : ℕ) (hm : 0 < m) (X : SymmMat) :
    eigenvalues (abs_psd_pow X (m : ℝ≥0)) =
      fun i ↦
        ((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^ m := by
  -- Route correction: the PSD-cone power on `𝕊ⁿ₊` is nonunital, so the exponent `m = 0` would
  -- give the zero matrix rather than the identity. The source-faithful spectral rewrite is only
  -- correct in the positive-exponent branch actually used below.
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (by simp)
  have hordered := absPsdPowOrderedEigenvalues_eq_ambientAbsEigenvaluesPow m hm X
  funext i
  have hi := congrFun hordered (e.symm i)
  -- Move from the ordered `eigenvalues₀` surface back to the chapter's `eigenvalues` indexing.
  simpa [e, RealSymmetricMatrixSpace.eigenvalues, Matrix.IsHermitian.eigenvalues] using hi

/-- Helper for Theorem 6.9: the PSD pairing produced by Lemma 6.14 is the same scalar quantity as
the theorem's target pairing written with the ambient eigenvalues of `CFC.abs X` and `CFC.abs H`,
once the exponent `k - 2` is known to be strictly positive. -/
private theorem abs_psd_power_pairing_eq_abs_eigenvalue_pairing
    (k : ℕ) (hk : 3 ≤ k) (X H : SymmMat) :
    abs_psd_power_pairing k X H = abs_eigenvalue_pairing k X H := by
  -- The mixed-term branch only arises for `k ≥ 2`, so the `X`-side cone power has positive
  -- exponent exactly when `k ≥ 3`, and only that strictly positive branch can use the corrected
  -- cone-power spectral rewrite.
  have hk_sub_pos : 0 < k - 2 := by
    omega
  -- Rewrite the `X` and `H` factors separately so the final sum is pointwise identical.
  have hXpow := abs_psd_pow_eigenvalues_eq_ambient_abs_eigenvalues_pow (k - 2) hk_sub_pos X
  have hHpow : eigenvalues (abs_psd_pow H (2 : ℝ≥0)) =
      fun i ↦
        ((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ) :=
    abs_psd_pow_eigenvalues_eq_ambient_abs_eigenvalues_pow 2 (by decide) H
  have hHsq := square_eigenvalues_eq_abs_psd_square_eigenvalues H
  unfold abs_psd_power_pairing abs_eigenvalue_pairing
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hHsq_i : eigenvalues (H ^ (2 : ℕ) : SymmMat) i = eigenvalues (abs_psd_pow H (2 : ℝ≥0)) i :=
    congrFun hHsq i
  have hXpow_i :
      eigenvalues (abs_psd_pow X (((k - 2 : ℕ) : ℝ≥0))) i =
        ((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^ (k - 2) :=
    congrFun hXpow i
  have hHpow_i :
      eigenvalues (abs_psd_pow H (2 : ℝ≥0)) i =
        ((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ) :=
    congrFun hHpow i
  calc
    eigenvalues (abs_psd_pow X (((k - 2 : ℕ) : ℝ≥0))) i *
        eigenvalues (H ^ (2 : ℕ) : SymmMat) i
      = eigenvalues (abs_psd_pow X (((k - 2 : ℕ) : ℝ≥0))) i *
          eigenvalues (abs_psd_pow H (2 : ℝ≥0)) i := by
            exact congrArg
              (fun t ↦ eigenvalues (abs_psd_pow X (((k - 2 : ℕ) : ℝ≥0))) i * t) hHsq_i
    _ = (((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^ (k - 2)) *
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ)) := by
            rw [hXpow_i, hHpow_i]

/-- Helper for Theorem 6.9: each mixed trace term in Proposition 6.33 is bounded by the
absolute-value spectral pairing from the theorem statement. -/
private theorem mixed_trace_term_le_abs_eigenvalue_pairing
    (k p : ℕ) (X H : SymmMat) (hp : p ∈ Finset.range (k - 1)) :
    mixed_trace_term k p X H ≤ abs_eigenvalue_pairing k X H := by
  -- Route correction: separate the source-faithful `X ↦ |X|` majorization from the later PSD
  -- Lemma 6.14 step so the remaining blockers are isolated and stable.
  have hk2 : 2 ≤ k := by
    have hp_lt : p < k - 1 := Finset.mem_range.mp hp
    omega
  rcases eq_or_lt_of_le hk2 with hk_eq | hk_lt
  · -- When `k = 2`, the single mixed summand is exactly `trace (H^2)` and the `X`-dependence
    -- disappears, so the comparison closes by the already stabilized square-eigenvalue rewrite.
    subst hk_eq
    have hp0 : p = 0 := by
      have hp_lt : p < 1 := by simpa using (Finset.mem_range.mp hp)
      omega
    subst hp0
    have hmixed_trace :
        mixed_trace_term 2 0 X H = Matrix.trace (((H ^ (2 : ℕ) : SymmMat) : Mat)) := by
      -- The `k = 2` mixed term collapses to the trace of the symmetric square `H^2`.
      simp [mixed_trace_term, RealSymmetricMatrixSpace.coe_pow, pow_two,
        (RealSymmetricMatrixSpace.isSymm X).eq, (RealSymmetricMatrixSpace.isSymm H).eq]
    have htrace_sum :
        Matrix.trace (((H ^ (2 : ℕ) : SymmMat) : Mat)) =
          ∑ i : Fin n, eigenvalues (H ^ (2 : ℕ) : SymmMat) i := by
      -- Hermitian trace equals the sum of ordered eigenvalues.
      simpa using (isHermitian (H ^ (2 : ℕ) : SymmMat)).trace_eq_sum_eigenvalues
    have hHsq := square_eigenvalues_eq_abs_psd_square_eigenvalues H
    have hHpow : eigenvalues (abs_psd_pow H (2 : ℝ≥0)) =
        fun i ↦
          ((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ) :=
      abs_psd_pow_eigenvalues_eq_ambient_abs_eigenvalues_pow 2 (by decide) H
    calc
      mixed_trace_term 2 0 X H = Matrix.trace (((H ^ (2 : ℕ) : SymmMat) : Mat)) := hmixed_trace
      _ = ∑ i : Fin n, eigenvalues (H ^ (2 : ℕ) : SymmMat) i := htrace_sum
      _ = ∑ i : Fin n, eigenvalues (abs_psd_pow H (2 : ℝ≥0)) i := by
            simpa using congrArg (fun f : Fin n → ℝ ↦ ∑ i : Fin n, f i) hHsq
      _ = ∑ i : Fin n,
            ((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^ (2 : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact congrFun hHpow i
      _ = abs_eigenvalue_pairing 2 X H := by
            unfold abs_eigenvalue_pairing
            simp
      _ ≤ abs_eigenvalue_pairing 2 X H := by
            exact le_rfl
  · have hk3 : 3 ≤ k := by
      omega
    -- Route correction: the previous boundary/interior split duplicated the same diagonalization
    -- work, so the `k ≥ 3` branch now uses one direct sandwich-to-PSD comparison for every `p`.
    calc
      mixed_trace_term k p X H = sandwich_trace_term k p X H := by
        exact mixed_trace_term_eq_sandwich_trace_term k p X H
      _ ≤ abs_psd_power_pairing k X H := by
        exact sandwich_trace_term_le_abs_psd_power_pairing k p X H hk3 hp
      _ = abs_eigenvalue_pairing k X H := by
        exact abs_psd_power_pairing_eq_abs_eigenvalue_pairing k hk3 X H

/-- Helper for Theorem 6.9: summing the single-term estimate over `p = 0, ..., k - 2` yields
`k - 1` copies of the same spectral pairing. -/
private theorem range_sum_mixed_trace_terms_le_abs_eigenvalue_pairing
    (k : ℕ) (X H : SymmMat) :
    (Finset.range (k - 1)).sum (fun p ↦ mixed_trace_term k p X H) ≤
      ((k - 1 : ℕ) : ℝ) * abs_eigenvalue_pairing k X H := by
  -- Sum the pointwise bound over the finite range from Proposition 6.33.
  calc
    (Finset.range (k - 1)).sum (fun p ↦ mixed_trace_term k p X H)
        ≤ (Finset.range (k - 1)).sum (fun _ ↦ abs_eigenvalue_pairing k X H) := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact mixed_trace_term_le_abs_eigenvalue_pairing k p X H hp
    _ = ((k - 1 : ℕ) : ℝ) * abs_eigenvalue_pairing k X H := by
          simp

/-- Theorem 6.9: for every natural number `k`, the Hessian quadratic form of the Chapter 6
trace-power owner `π_k(X) = Trace (X^k)` at a symmetric matrix `X` in the symmetric direction `H`
is bounded above by `k(k - 1)` times the pairing of the eigenvalues of `(CFC.abs X)^(k - 2)` and
the squared eigenvalues of `CFC.abs H`. -/
theorem powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing
    (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] ≤
      (((k * (k - 1) : ℕ) : ℝ) *
        ∑ i : Fin n,
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (k - 2)) *
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (2 : ℕ))) := by
  rcases k with _ | k
  · -- The degree-zero trace power is constant, so its Hessian vanishes and the right-hand side
    -- carries the same zero prefactor.
    have hconst :
        (π[0] : SymmMat → ℝ) = fun _ : SymmMat ↦ (n : ℝ) := by
      funext Y
      simp [RealSymmetricMatrixSpace.powerTrace_def]
    rw [hconst]
    simp [iteratedFDeriv_const_of_ne two_ne_zero]
  · have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    -- Expand the Hessian into the Proposition 6.33 mixed-trace sum once the `k ≥ 1` side
    -- condition is available.
    have hfrobeniusSum :
        iteratedFDeriv ℝ 2 (π[k + 1] : SymmMat → ℝ) X ![H, H] =
          (k + 1 : ℝ) * (Finset.range (k + 1 - 1)).sum
            (fun p ↦ sandwich_trace_term (k + 1) p X H) := by
      simpa [sandwich_trace_term] using
        powerTrace_iteratedFDeriv_two_eq_frobenius_sum (k + 1) hk X H
    have hsandwichSum :
        (Finset.range (k + 1 - 1)).sum (fun p ↦ sandwich_trace_term (k + 1) p X H) =
          (Finset.range (k + 1 - 1)).sum (fun p ↦ mixed_trace_term (k + 1) p X H) := by
      -- Convert Proposition 6.33's sandwich spelling to the local mixed-term owner one summand at
      -- a time so the already established pointwise estimate applies directly.
      refine Finset.sum_congr rfl ?_
      intro p hp
      exact (mixed_trace_term_eq_sandwich_trace_term (k + 1) p X H).symm
    have hfrobeniusMixed :
        iteratedFDeriv ℝ 2 (π[k + 1] : SymmMat → ℝ) X ![H, H] =
          (k + 1 : ℝ) * (Finset.range (k + 1 - 1)).sum
            (fun p ↦ mixed_trace_term (k + 1) p X H) := by
      calc
        iteratedFDeriv ℝ 2 (π[k + 1] : SymmMat → ℝ) X ![H, H]
            = (k + 1 : ℝ) * (Finset.range (k + 1 - 1)).sum
                (fun p ↦ sandwich_trace_term (k + 1) p X H) := hfrobeniusSum
        _ = (k + 1 : ℝ) * (Finset.range (k + 1 - 1)).sum
              (fun p ↦ mixed_trace_term (k + 1) p X H) := by
                rw [hsandwichSum]
    -- Multiply the uniform sum bound by the nonnegative prefactor `k + 1`.
    have hsum :
        (Finset.range (k + 1 - 1)).sum (fun p ↦ mixed_trace_term (k + 1) p X H) ≤
          ((k + 1 - 1 : ℕ) : ℝ) * abs_eigenvalue_pairing (k + 1) X H :=
      range_sum_mixed_trace_terms_le_abs_eigenvalue_pairing (k + 1) X H
    have hk_nonneg : 0 ≤ (k + 1 : ℝ) := by
      exact_mod_cast Nat.zero_le (k + 1)
    have hmul := mul_le_mul_of_nonneg_left hsum hk_nonneg
    refine hfrobeniusMixed.le.trans ?_
    calc
      (k + 1 : ℝ) * (Finset.range (k + 1 - 1)).sum
          (fun p ↦ mixed_trace_term (k + 1) p X H)
        ≤ (k + 1 : ℝ) * (((k + 1 - 1 : ℕ) : ℝ) * abs_eigenvalue_pairing (k + 1) X H) := hmul
      _ = (((((k + 1) * (k + 1 - 1) : ℕ) : ℝ) *
            ∑ i : Fin n,
              (((Matrix.nonneg_iff_posSemidef.mp
                  (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                (k + 1 - 2)) *
                (((Matrix.nonneg_iff_posSemidef.mp
                    (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                  (2 : ℕ)))) := by
            simp [abs_eigenvalue_pairing, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
