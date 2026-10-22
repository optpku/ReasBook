/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Example 14.2 (1): The product of `{1, ..., 6}` and `{1,2,3}` is the set of pairs whose
coordinates lie in the respective factors. -/
-- Proof sketch: unfold membership in the product set and compare it with the explicit set-builder.
lemma one_to_six_prod_one_to_three_eq_set_of_pair_mem :
    (({1, 2, 3, 4, 5, 6} : Set ℕ) ×ˢ ({1, 2, 3} : Set ℕ)) =
      {ω : ℕ × ℕ | ω.1 ∈ ({1, 2, 3, 4, 5, 6} : Set ℕ) ∧ ω.2 ∈ ({1, 2, 3} : Set ℕ)} := by
  ext ω
  rfl

/-- Example 14.2 (2): Real-valued functions on the index set `{1,2,3}` are canonically equivalent
to the usual three-dimensional real coordinate space. -/
noncomputable def real_functions_on_one_two_three_equiv_real_cube :
    (({1, 2, 3} : Finset ℕ) → ℝ) ≃ ℝ × ℝ × ℝ :=
  (Equiv.piCongrLeft (fun _ : Fin 3 ↦ ℝ)
      (({1, 2, 3} : Finset ℕ).equivFinOfCardEq
        (by decide : ({1, 2, 3} : Finset ℕ).card = 3))).trans <|
    (Equiv.piCongrLeft (fun _ : Option (Fin 2) ↦ ℝ) (finSuccEquiv 2)).trans <|
      Equiv.piOptionEquivProd.trans <|
        Equiv.prodCongr (Equiv.refl ℝ) (finTwoArrowEquiv ℝ)

/- Example 14.2 (3): When the index set is `ℕ` and every factor is `ℝ`, the product space is the
space of real sequences. -/
#check (ℕ → ℝ)

/- Example 14.2 (4): When both the index set and the common factor are `ℝ`, the product space is
the type of maps `ℝ → ℝ`. -/
#check (ℝ → ℝ)
