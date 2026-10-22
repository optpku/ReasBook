/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Matrix

section

variable {m n : ℕ}

/- Definition 7.18 is `source-facing`: it defines spectral functions on real rectangular matrices
by factoring through the singular-value map. The `core/canonical` owner for the matrix spectral
data already present in the project is `singular_value_function`, built from
`LinearMap.singularValues` in Definition 7.15. -/

/-- Definition 7.18: a proper extended-real-valued function on `ℝ^(m × n)` is spectral when it
factors through the singular-value function via some proper extended-real-valued function on
`ℝ^(min m n)`; any such factor is an associated function. -/
class IsSpectralFunction (g : Matrix (Fin m) (Fin n) ℝ → EReal) : Prop
    extends IsProperExtendedRealFunction g where
  associatedFunction_exists :
    ∃ f : (Fin (min m n) → ℝ) → EReal,
      IsProperExtendedRealFunction f ∧ g = f ∘ singular_value_function

-- Proof sketch: unpack the class definition; it records exactly the properness of `g` together
-- with the existence of a proper associated function on singular-value coordinates whose
-- composition with `singular_value_function` recovers `g`.
/-- A function on real `m × n` matrices is spectral exactly when it is proper and equals a proper
associated function on singular-value coordinates composed with `singular_value_function`. -/
theorem isSpectralFunction_iff_exists_associatedFunction
    (g : Matrix (Fin m) (Fin n) ℝ → EReal) :
    IsSpectralFunction g ↔
      IsProperExtendedRealFunction g ∧
        ∃ f : (Fin (min m n) → ℝ) → EReal,
          IsProperExtendedRealFunction f ∧ g = f ∘ singular_value_function := by
  constructor
  · intro hg
    -- Read the properness field and the associated singular-value factorization from the class.
    exact ⟨hg.toIsProperExtendedRealFunction, hg.associatedFunction_exists⟩
  · rintro ⟨hgProper, hfactorization⟩
    -- Repackage the properness datum and associated-function witness into the class.
    exact
      { toIsProperExtendedRealFunction := hgProper
        associatedFunction_exists := hfactorization }

/-- Helper for Definition 7.18: the constant zero extended-real-valued function on real
`m × n` matrices is proper. -/
theorem matrix_const_zero_isProperExtendedRealFunction :
    IsProperExtendedRealFunction (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : EReal)) := by
  -- The constant zero function never attains `-∞`, and the zero matrix gives a finite value.
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro X
    simp
  · refine ⟨0, ?_⟩
    simp [effective_domain]

/-- Helper for Definition 7.18: the constant zero function on singular-value coordinates is
proper. -/
theorem singular_coordinate_const_zero_isProperExtendedRealFunction :
    IsProperExtendedRealFunction (fun _ : (Fin (min m n) → ℝ) ↦ (0 : EReal)) := by
  -- The zero profile never attains `-∞`, and the zero vector lies in its effective domain.
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro x
    simp
  · refine ⟨0, ?_⟩
    simp [effective_domain]

/-- Helper for Definition 7.18: composing the constant zero singular-value profile with the
singular-value function still gives the constant zero matrix-valued function. -/
theorem matrix_const_zero_factorization_through_singular_value_function :
    (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : EReal)) =
      (fun _ : (Fin (min m n) → ℝ) ↦ (0 : EReal)) ∘ singular_value_function := by
  -- Both sides evaluate to zero on every matrix.
  funext X
  simp [Function.comp_apply]

-- Proof sketch: choose the constant zero function on singular-value coordinates as the associated
-- function; it is proper, and composing it with `singular_value_function` still gives the constant
-- zero function on matrices.
/-- The constant zero extended-real-valued function on real `m × n` matrices is spectral. -/
instance : IsSpectralFunction (fun _ : Matrix (Fin m) (Fin n) ℝ ↦ (0 : EReal)) := by
  -- Choose the constant zero profile on singular-value coordinates as the associated function.
  refine
    { toIsProperExtendedRealFunction := matrix_const_zero_isProperExtendedRealFunction
      associatedFunction_exists := ?_ }
  exact
    ⟨fun _ : (Fin (min m n) → ℝ) ↦ (0 : EReal),
      singular_coordinate_const_zero_isProperExtendedRealFunction,
      matrix_const_zero_factorization_through_singular_value_function⟩

end

end Matrix
