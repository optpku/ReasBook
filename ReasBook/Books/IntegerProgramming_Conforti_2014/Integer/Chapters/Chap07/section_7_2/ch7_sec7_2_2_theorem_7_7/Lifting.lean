/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_19
import Mathlib.Data.Real.Archimedean
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped BigOperators Matrix

noncomputable section

namespace SequenceIndependentLifting

section OwnerAPI

universe u

variable {ι : Type u}

/-- The coefficient vector of the base inequality supported on `C`. -/
def base_coefficients
    [DecidableEq ι]
    (C : Finset ι)
    (α : ι → ℝ) : ι → ℝ :=
  C.piecewise α 0

/-- On the distinguished set `C`, `base_coefficients C α` agrees with `α`. -/
@[simp] theorem base_coefficients_apply_of_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α : ι → ℝ}
    {j : ι}
    (hj : j ∈ C) :
    base_coefficients C α j = α j :=
  Finset.piecewise_eq_of_mem _ _ _ hj

/-- Outside `C`, `base_coefficients C α` vanishes. -/
@[simp] theorem base_coefficients_apply_of_not_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α : ι → ℝ}
    {j : ι}
    (hj : j ∉ C) :
    base_coefficients C α j = 0 :=
  Finset.piecewise_eq_of_notMem _ _ _ hj

/-- The coefficient vector obtained by lifting the base inequality with a scalar function `φ`
evaluated at the weights `a j` outside `C`. -/
def lifted_coefficients
    [DecidableEq ι]
    (C : Finset ι)
    (α : ι → ℝ)
    (a : ι → ℝ)
    (φ : ℝ → ℝ) : ι → ℝ :=
  C.piecewise α (φ ∘ a)

/-- On `C`, `lifted_coefficients C α a φ` agrees with the original coefficients `α`. -/
@[simp] theorem lifted_coefficients_apply_of_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α a : ι → ℝ}
    {φ : ℝ → ℝ}
    {j : ι}
    (hj : j ∈ C) :
    lifted_coefficients C α a φ j = α j :=
  Finset.piecewise_eq_of_mem _ _ _ hj

/-- Outside `C`, `lifted_coefficients C α a φ` is given by `φ (a j)`. -/
@[simp] theorem lifted_coefficients_apply_of_not_mem
    [DecidableEq ι]
    {C : Finset ι}
    {α a : ι → ℝ}
    {φ : ℝ → ℝ}
    {j : ι}
    (hj : j ∉ C) :
    lifted_coefficients C α a φ j = φ (a j) :=
  Finset.piecewise_eq_of_notMem _ _ _ hj

/-- A coefficient vector is a lifting of the base inequality on `C` when it is valid for `S`
and agrees with `α` on `C`. -/
def is_lifting_of_base_inequality
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (c : ι → ℝ) : Prop :=
  is_valid_inequality S c β ∧ ∀ ⦃j : ι⦄, j ∈ C → c j = α j

/-- `is_lifting_of_base_inequality` unfolds to validity for `S` together with agreement
with the base coefficients on `C`. -/
theorem is_lifting_of_base_inequality_iff
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ} :
    is_lifting_of_base_inequality S C α β c ↔
      is_valid_inequality S c β ∧ ∀ ⦃j : ι⦄, j ∈ C → c j = α j :=
  Iff.rfl

/-- A lifting of the base inequality is, in particular, a valid inequality for `S`. -/
theorem is_lifting_of_base_inequality.is_valid_inequality
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_lifting_of_base_inequality S C α β c) :
    is_valid_inequality S c β :=
  hc.1

/-- A lifting of the base inequality agrees with the base coefficients on `C`. -/
theorem is_lifting_of_base_inequality.eq_base_of_mem
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_lifting_of_base_inequality S C α β c)
    {j : ι}
    (hj : j ∈ C) :
    c j = α j :=
  hc.2 hj

/-- A coefficient vector is the unique maximal lifting of the base inequality when it is a
lifting and every other lifting lies pointwise below it. -/
def is_unique_maximal_lifting_of_base_inequality
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (c : ι → ℝ) : Prop :=
  is_lifting_of_base_inequality S C α β c ∧
    ∀ c' : ι → ℝ,
      is_lifting_of_base_inequality S C α β c' →
        c' ≤ c

/-- `is_unique_maximal_lifting_of_base_inequality` unfolds to validity, agreement on `C`, and
pointwise domination over every other lifting. -/
theorem is_unique_maximal_lifting_of_base_inequality_iff
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ} :
    is_unique_maximal_lifting_of_base_inequality S C α β c ↔
      is_lifting_of_base_inequality S C α β c ∧
        ∀ c' : ι → ℝ,
          is_lifting_of_base_inequality S C α β c' →
            c' ≤ c :=
  Iff.rfl

/-- A unique maximal lifting is, in particular, a lifting of the base inequality. -/
theorem is_unique_maximal_lifting_of_base_inequality.is_lifting
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_unique_maximal_lifting_of_base_inequality S C α β c) :
    is_lifting_of_base_inequality S C α β c :=
  hc.1

/-- A unique maximal lifting dominates every other lifting pointwise. -/
theorem is_unique_maximal_lifting_of_base_inequality.maximal
    [Fintype ι]
    {S : Set (ι → ℝ)}
    {C : Finset ι}
    {α : ι → ℝ}
    {β : ℝ}
    {c : ι → ℝ}
    (hc : is_unique_maximal_lifting_of_base_inequality S C α β c)
    (c' : ι → ℝ)
    (hc' : is_lifting_of_base_inequality S C α β c') :
    c' ≤ c :=
  hc.2 c' hc'

end OwnerAPI

section Theorem77

variable {n : ℕ}

/-- A function on `[0,b]` is superadditive when `g (u + v)` dominates `g u + g v` whenever
`u`, `v`, and `u + v` all lie in the interval `[0,b]`. -/
def is_superadditive_on_Icc
    (g : ℝ → ℝ)
    (b : ℝ) : Prop :=
  ∀ ⦃u v : ℝ⦄,
    u ∈ Set.Icc (0 : ℝ) b →
    v ∈ Set.Icc (0 : ℝ) b →
    u + v ∈ Set.Icc (0 : ℝ) b →
    g u + g v ≤ g (u + v)

/-- The sequence-independent lifting profile associated with the base inequality on `C` and the
binary knapsack data `(a, b)`. -/
def lifting_profile
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) : ℝ → ℝ :=
  fun z ↦
    β -
      sSup
        {r : ℝ |
          ∃ x : Fin n → ℝ,
            x ∈ zero_one_knapsack_set a (b - z) ∧
            (∀ j, j ∉ C → x j = 0) ∧
            r = base_coefficients C α ⬝ᵥ x}

end Theorem77

end SequenceIndependentLifting
