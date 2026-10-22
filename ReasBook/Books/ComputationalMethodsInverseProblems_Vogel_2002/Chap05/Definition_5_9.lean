/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_9.PeriodicExtension

public section

universe u

namespace Matrix

variable {α : Type u}

/-- Helper for Definition 5.9: a two-dimensional array is `(n_x, n_y)`-periodic exactly when
equality holds along each coordinate whenever the corresponding integer indices are congruent
modulo the matching side length. -/
theorem isPeriodic_iff_modEq {n_x n_y : ℕ} {t : ℤ → ℤ → α} :
    IsPeriodic n_x n_y t ↔
      (∀ i i' j, i ≡ i' [ZMOD n_x] → t i j = t i' j) ∧
        ∀ i j j', j ≡ j' [ZMOD n_y] → t i j = t i j' := by
  constructor
  · intro h
    rcases isPeriodic_iff.mp h with ⟨h_x, h_y⟩
    refine ⟨?_, ?_⟩
    · intro i i' j hij
      exact (h_x j).eq_of_modEq hij
    · intro i j j' hij
      exact (h_y i).eq_of_modEq hij
  · rintro ⟨h_x, h_y⟩
    exact isPeriodic_iff.mpr
      ⟨fun j ↦ Function.periodic_of_modEq (fun i i' hij ↦ h_x i i' j hij),
        fun i ↦ Function.periodic_of_modEq (fun j j' hij ↦ h_y i j j' hij)⟩

/-- Definition 5.9 (2). The periodic extension of a finite `n_x × n_y` array is
`(n_x, n_y)`-periodic and agrees with the original array on the base `Fin n_x × Fin n_y`
window. -/
theorem periodicExtension_spec {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (t : Matrix (Fin n_x) (Fin n_y) α) :
    IsPeriodic n_x n_y (periodicExtension h_x h_y t) ∧
      ∀ i : Fin n_x, ∀ j : Fin n_y,
        periodicExtension h_x h_y t ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) = t i j := by
  exact ⟨periodicExtension_isPeriodic h_x h_y t, periodicExtension_apply_natCast h_x h_y t⟩

/-- The `[NeZero]` periodic extension of a finite `n_x × n_y` array is `(n_x, n_y)`-periodic
and agrees with the original array on the base `Fin n_x × Fin n_y` window. -/
theorem periodicExtensionOfNeZero_spec {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (t : Matrix (Fin n_x) (Fin n_y) α) :
    IsPeriodic n_x n_y (periodicExtensionOfNeZero t) ∧
      ∀ i : Fin n_x, ∀ j : Fin n_y,
        periodicExtensionOfNeZero t ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) = t i j := by
  exact ⟨periodicExtensionOfNeZero_isPeriodic t, periodicExtensionOfNeZero_apply_natCast t⟩

end Matrix
