/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Matrix

section

variable {m n : ℕ}

/- Definition 7.22 is `source-facing`: it introduces a class of subsets of real rectangular
matrices by requiring their indicator functions to factor through the singular-value map via the
indicator of an absolutely permutation symmetric set in `ℝ^(min m n)`. The owner abstractions
already present in the project for this are `extendedIndicator`,
`Function.IsAbsolutelyPermutationSymmetric`, and `singular_value_function`. -/

/-- A set `C ⊆ ℝ^(min(m,n))` is associated to a set `T ⊆ ℝ^(m × n)` when the indicator of `T` is
the indicator of `C` composed with the singular-value map, and the indicator of `C` is absolutely
permutation symmetric. -/
def IsAssociatedSymmetricSpectralSet
    (T : Set (Matrix (Fin m) (Fin n) ℝ)) (C : Set (Fin (min m n) → ℝ)) : Prop :=
  Function.IsAbsolutelyPermutationSymmetric (extendedIndicator C) ∧
    extendedIndicator T = extendedIndicator C ∘ singular_value_function

/-- Definition 7.22: a set `T ⊆ ℝ^(m × n)` is symmetric spectral when its indicator function is
the indicator of an absolutely permutation symmetric set in singular-value coordinates composed
with the singular-value map; such a set `C` is an associated set. -/
def IsSymmetricSpectralSet (T : Set (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  ∃ C : Set (Fin (min m n) → ℝ), IsAssociatedSymmetricSpectralSet T C

-- Proof sketch: unfold `IsSymmetricSpectralSet`; the statement is exactly the existential
-- packaging of the associated-set relation introduced just above.
/-- A set of real `m × n` matrices is symmetric spectral exactly when it admits an associated set
in singular-value coordinates. -/
theorem isSymmetricSpectralSet_iff_exists_associatedSet
    (T : Set (Matrix (Fin m) (Fin n) ℝ)) :
    IsSymmetricSpectralSet T ↔
      ∃ C : Set (Fin (min m n) → ℝ), IsAssociatedSymmetricSpectralSet T C := by
  -- The theorem only unfolds the existential content of `IsSymmetricSpectralSet`.
  rfl

/-- Helper for Definition 7.22: an associated set directly provides the singular-value
factorization of the indicator of the ambient matrix set. -/
theorem associated_set_factorization_of_extendedIndicator
    {T : Set (Matrix (Fin m) (Fin n) ℝ)} {C : Set (Fin (min m n) → ℝ)}
    (hTC : IsAssociatedSymmetricSpectralSet T C) :
    HasAbsolutelyPermutationSymmetricSingularValueFactorization (extendedIndicator T) := by
  rcases hTC with ⟨hC_abs, hcomp⟩
  -- Repackage the associated-set data into the factorization constructor from Definition 7.19.
  exact
    HasAbsolutelyPermutationSymmetricSingularValueFactorization.mk
      (extendedIndicator C)
      hC_abs
      hcomp

-- Proof sketch: choose the associated set `C`; its extended indicator is absolutely permutation
-- symmetric by assumption, and the factorization equality is exactly the required singular-value
-- representation of `extendedIndicator T`.
/-- The indicator of a symmetric spectral set is a symmetric spectral function on real
`m × n` matrices. -/
theorem extendedIndicator_isSymmetricSpectralFunction_of_isSymmetricSpectralSet
    {T : Set (Matrix (Fin m) (Fin n) ℝ)} (hT : IsSymmetricSpectralSet T) :
    IsSymmetricSpectralFunction (extendedIndicator T) := by
  rcases hT with ⟨C, hTC⟩
  -- Use the associated set from Definition 7.22 and package its factorization into the class.
  exact ⟨associated_set_factorization_of_extendedIndicator hTC⟩

end

end Matrix
