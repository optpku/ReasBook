/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_4.PeriodicExtension

public section
universe u
namespace DiscreteSignal
variable {α : Type u}

/-- The periodicity criterion from equation `(5.21)`: a discrete vector is `n`-periodic exactly
when its values agree at integer indices that are congruent modulo `n`. -/
theorem periodic_iff_modEq {n : ℕ} {t : ℤ → α} :
    Function.Periodic t (n : ℤ) ↔ ∀ i j, i ≡ j [ZMOD n] → t i = t j := by
  constructor
  · intro h i j hij
    -- Periodicity identifies all representatives of the same residue class.
    exact h.eq_of_modEq hij
  · intro h
    -- Equality on congruence classes upgrades to periodicity by one-period shifts.
    exact Function.periodic_of_modEq h

/-- Definition 5.4. The periodic extension of `t : Fin n → α` is `n`-periodic and agrees with
`t` on the base window `0, ..., n - 1`; equation `(5.21)` is recorded separately by
`periodic_iff_modEq`. -/
theorem periodicExtension_spec {n : ℕ} (h : 0 < n) (t : Fin n → α) :
    Function.Periodic (periodicExtension h t) (n : ℤ) ∧
      ∀ i : Fin n, periodicExtension h t ((i : ℕ) : ℤ) = t i := by
  -- Pair the periodicity theorem with the base-window agreement theorem.
  exact ⟨periodicExtension_isPeriodic h t, periodicExtension_apply_natCast h t⟩

/-- The `[NeZero n]` periodic extension of `t : Fin n → α` is `n`-periodic and agrees with `t`
on the base window `0, ..., n - 1`. -/
theorem periodicExtensionOfNeZero_spec {n : ℕ} [NeZero n] (t : Fin n → α) :
    Function.Periodic (periodicExtensionOfNeZero t) (n : ℤ) ∧
      ∀ i : Fin n, periodicExtensionOfNeZero t ((i : ℕ) : ℤ) = t i := by
  -- Repackage the wrapper-level periodicity and base-window agreement.
  exact ⟨periodicExtensionOfNeZero_isPeriodic t, periodicExtensionOfNeZero_apply_natCast t⟩

end DiscreteSignal
