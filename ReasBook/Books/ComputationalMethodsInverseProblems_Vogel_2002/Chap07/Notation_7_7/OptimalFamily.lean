/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.Extr

public section

namespace ParameterChoice

universe u

/-- A parameter family `a` is optimal for an `n`-indexed objective family on an
`n`-indexed admissible family when `a n` minimizes the `n`th objective on the
`n`th admissible set for every data size `n`. -/
def IsOptimalParameterFamily {τ : Type u}
    (objective : ℕ → τ → ℝ) (admissible : ℕ → Set τ) (a : ℕ → τ) : Prop :=
  ∀ n, IsMinOn (objective n) (admissible n) (a n)

/-- The defining pointwise minimizer characterization of
`IsOptimalParameterFamily`. -/
theorem isOptimalParameterFamily_iff {τ : Type u}
    (objective : ℕ → τ → ℝ) (admissible : ℕ → Set τ) (a : ℕ → τ) :
    IsOptimalParameterFamily objective admissible a ↔
      ∀ n, IsMinOn (objective n) (admissible n) (a n) := Iff.rfl

/-- For a constant admissible set `S`, `IsOptimalParameterFamily` is equivalent
to minimizing each objective `objective n` on `S`. -/
theorem isOptimalParameterFamily_const_iff {τ : Type u}
    (objective : ℕ → τ → ℝ) (S : Set τ) (a : ℕ → τ) :
    IsOptimalParameterFamily objective (fun _ ↦ S) a ↔
      ∀ n, IsMinOn (objective n) S (a n) := Iff.rfl

end ParameterChoice
