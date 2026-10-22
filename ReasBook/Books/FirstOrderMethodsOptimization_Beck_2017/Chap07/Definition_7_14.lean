/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ}

local notation "𝕊" => symmetricMatrices n

/- Definition 7.14 is `source-facing`: it defines a class of subsets of the symmetric-matrix space
by requiring their indicator functions to factor through the ordered eigenvalue map via the
indicator of a permutation symmetric set in `ℝ^n`. The owner abstractions already present in the
project for this are `extendedIndicator`, `IsPermutationSymmetricFunction`, and
`symmetricEigenvalues`. -/

/-- A set `C ⊆ ℝ^n` is associated to a set `T ⊆ 𝕊^n` when the indicator of `T` is the
indicator of `C` composed with the ordered eigenvalue map, and the indicator of `C` is
permutation symmetric. -/
def IsAssociatedSymmetricSpectralSet (T : Set 𝕊) (C : Set (Fin n → ℝ)) : Prop :=
  IsPermutationSymmetricFunction (extendedIndicator C) ∧
    extendedIndicator T = extendedIndicator C ∘ symmetricEigenvalues_7_23

/-- Definition 7.14: a set `T ⊆ 𝕊^n` is symmetric spectral when its indicator function is the
indicator of a permutation symmetric set in `ℝ^n` composed with the ordered eigenvalue map; such
a set `C` is an associated set. -/
def IsSymmetricSpectralSet (T : Set 𝕊) : Prop :=
  ∃ C : Set (Fin n → ℝ), IsAssociatedSymmetricSpectralSet T C

-- Proof sketch: unfold `IsSymmetricSpectralSet`; the statement is exactly the existential
-- packaging of the associated-set relation introduced just above.
/-- A set in `𝕊^n` is symmetric spectral exactly when it admits an associated set in eigenvalue
coordinates. -/
theorem isSymmetricSpectralSet_iff_exists_associatedSet (T : Set 𝕊) :
    IsSymmetricSpectralSet T ↔
      ∃ C : Set (Fin n → ℝ), IsAssociatedSymmetricSpectralSet T C := by
  -- The theorem just unpacks the existential content of `IsSymmetricSpectralSet`.
  rfl

/-- Helper for Definition 7.14: an associated set directly provides the eigenvalue-factorization
of the indicator of the symmetric-matrix set. -/
theorem associated_set_factorization_of_extendedIndicator
    {T : Set 𝕊} {C : Set (Fin n → ℝ)} (hTC : IsAssociatedSymmetricSpectralSet T C) :
    HasPermutationSymmetricEigenvalueFactorization (extendedIndicator T) := by
  rcases hTC with ⟨hC_perm, hcomp⟩
  -- Repackage the associated-set data into the factorization constructor from Definition 7.23.
  exact
    HasPermutationSymmetricEigenvalueFactorization.mk
      (extendedIndicator C)
      hC_perm.toIsProperExtendedRealFunction
      hC_perm
      hcomp

-- Proof sketch: choose the associated set `C`; its extended indicator is permutation symmetric by
-- assumption, and the factorization equality is exactly the required eigenvalue-side
-- representation of the indicator.
/-- The indicator of a symmetric spectral set is a symmetric spectral function on `𝕊^n`. -/
theorem extendedIndicator_isSymmetricSpectralFunction_of_isSymmetricSpectralSet
    {T : Set 𝕊} (hT : IsSymmetricSpectralSet T) :
    IsSymmetricSpectralFunction (extendedIndicator T) := by
  rcases hT with ⟨C, hTC⟩
  -- Use the associated set from Definition 7.14 and package its factorization into the class.
  exact ⟨associated_set_factorization_of_extendedIndicator hTC⟩

end
