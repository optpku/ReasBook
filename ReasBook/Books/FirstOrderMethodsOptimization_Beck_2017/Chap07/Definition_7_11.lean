/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_4

-- Declarations for this item will be appended below by the statement pipeline.

notation "𝕊[" n "]" => {A : Matrix (Fin n) (Fin n) ℝ // Matrix.IsSymm A}

noncomputable section

-- Proof sketch: for real matrices, Hermitian means equality with the conjugate transpose, and the
-- conjugate transpose of a real matrix is its ordinary transpose.
/-- A real symmetric matrix in `𝕊[n]` has a Hermitian underlying matrix. -/
theorem symmetricSubtype_isHermitian {n : ℕ} (X : 𝕊[n]) :
    (X : Matrix (Fin n) (Fin n) ℝ).IsHermitian := by
  -- Over `ℝ`, the conjugate transpose is the ordinary transpose, so symmetry is Hermitianity.
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using X.property

/-- Helper for Definition 7.11: the zero real matrix is symmetric, so it defines a point of
`𝕊[n]`. -/
theorem zero_matrix_isSymm {n : ℕ} : Matrix.IsSymm (0 : Matrix (Fin n) (Fin n) ℝ) := by
  -- Every entry of the zero matrix agrees with its transpose.
  exact (Matrix.isSymm_zero : Matrix.IsSymm (0 : Matrix (Fin n) (Fin n) ℝ))

/-- The ordered eigenvalue map on real symmetric `n × n` matrices. -/
noncomputable def symmetricEigenvalues {n : ℕ} (X : 𝕊[n]) : Fin n → ℝ :=
  (symmetricSubtype_isHermitian X).eigenvalues

-- Proof sketch: unfold `symmetricEigenvalues`; evaluation at `i` is definitionally the `i`-th
-- ordered Hermitian eigenvalue of the underlying real symmetric matrix.
/-- Evaluating `symmetricEigenvalues` returns the corresponding ordered Hermitian eigenvalue of the
underlying real symmetric matrix. -/
theorem symmetricEigenvalues_apply {n : ℕ} (X : 𝕊[n]) (i : Fin n) :
    symmetricEigenvalues X i = (symmetricSubtype_isHermitian X).eigenvalues i := by
  -- This is the defining evaluation rule for `symmetricEigenvalues`.
  rfl

namespace Function

section

/-- Definition 7.11: a proper extended-real-valued function on real symmetric `n × n` matrices is
spectral when it factors through the ordered eigenvalue map of a proper function on `ℝ^n`; any
such factor is an associated function. -/
class IsSpectralFunction {n : ℕ} (g : 𝕊[n] → EReal) : Prop
    extends IsProperExtendedRealFunction g where
  associatedFunction_exists :
    ∃ f : (Fin n → ℝ) → EReal, IsProperExtendedRealFunction f ∧
      ∀ X : 𝕊[n], g X = f (symmetricEigenvalues X)

-- Proof sketch: unpack `Function.IsSpectralFunction`; it consists exactly of properness of `g`
-- together with the existence of a proper function on `ℝ^n` whose composition with
-- `symmetricEigenvalues` recovers `g`.
/-- A function on real symmetric matrices is spectral exactly when it is proper and equals a proper
profile on `ℝ^n` composed with the ordered eigenvalue map. -/
theorem isSpectralFunction_iff_exists_associatedFunction {n : ℕ} (g : 𝕊[n] → EReal) :
    IsSpectralFunction g ↔
      IsProperExtendedRealFunction g ∧
        ∃ f : (Fin n → ℝ) → EReal, IsProperExtendedRealFunction f ∧
          ∀ X : 𝕊[n], g X = f (symmetricEigenvalues X) := by
  constructor
  · intro hg
    -- Read the properness field and the associated eigenvalue factorization directly from the
    -- class data.
    exact ⟨hg.toIsProperExtendedRealFunction, hg.associatedFunction_exists⟩
  · rintro ⟨hgProper, hfactorization⟩
    -- Repackage the properness datum and the associated-function witness into the class.
    exact
      { toIsProperExtendedRealFunction := hgProper
        associatedFunction_exists := hfactorization }

/-- The constant zero extended-real-valued function on real symmetric matrices is spectral. -/
instance {n : ℕ} : IsSpectralFunction (fun _ : 𝕊[n] ↦ (0 : EReal)) := by
  refine
    { toIsProperExtendedRealFunction := ?_
      associatedFunction_exists := ?_ }
  · refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · -- The constant zero function never takes the value `-∞`.
      intro X
      simp
    · -- The zero symmetric matrix is in the effective domain because the function value is finite.
      refine ⟨⟨0, zero_matrix_isSymm⟩, ?_⟩
      simp [effective_domain]
  · -- Choose the constant zero function on eigenvalue coordinates as the associated function.
    refine ⟨fun _ : Fin n → ℝ ↦ (0 : EReal), ?_, ?_⟩
    · refine
        { ne_bot := ?_
          effective_domain_nonempty := ?_ }
      · -- The associated function is also constant zero, so it never attains `-∞`.
        intro x
        simp
      · -- The zero vector witnesses a finite associated-function value.
        refine ⟨0, ?_⟩
        simp [effective_domain]
    · -- Composing the constant zero profile with `symmetricEigenvalues` is still the zero function.
      intro X
      simp

end

end Function
