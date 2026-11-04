/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Hull
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped Matrix

-- The textbook notation `P^k` for the `k`th split closure is represented in Lean by
-- `splitClosure^[k] P`.

section Definition513Extra1

variable {n : ℕ}

/-- Definition 5.1.3-extra-1 (1): a natural number `k` is the split rank of `P` relative to the
split-closure operator `splitClosure` and the integer set `S` when the `k`th split closure of `P`
is `conv(S)` and no smaller iterate has this property. -/
class is_split_rank_of_set
    (splitClosure : Set (Fin n → ℝ) → Set (Fin n → ℝ))
    (P S : Set (Fin n → ℝ))
    (k : ℕ) : Prop where
  /-- The `k`th split closure of `P` is `conv(S)`. -/
  eq_convex_hull : splitClosure^[k] P = convexHull ℝ S
  /-- No smaller split-closure iterate of `P` is `conv(S)`. -/
  minimal :
    ∀ ⦃j : ℕ⦄, j < k → splitClosure^[j] P ≠ convexHull ℝ S

/-- `is_split_rank_of_set splitClosure P S k` unfolds to attainment of `conv(S)` at the `k`th
iterate together with minimality of `k`. -/
theorem is_split_rank_of_set_iff
    {splitClosure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P S : Set (Fin n → ℝ)} {k : ℕ} :
    is_split_rank_of_set splitClosure P S k ↔
      splitClosure^[k] P = convexHull ℝ S ∧
        ∀ ⦃j : ℕ⦄, j < k → splitClosure^[j] P ≠ convexHull ℝ S := by
  constructor
  · intro hk
    exact ⟨hk.eq_convex_hull, hk.minimal⟩
  · rintro ⟨heq, hminimal⟩
    exact ⟨heq, hminimal⟩

/-- If `k` is the split rank of `P` relative to `S`, then no earlier split-closure iterate of `P`
is `conv(S)`. -/
theorem is_split_rank_of_set.not_eq_convex_hull
    {splitClosure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P S : Set (Fin n → ℝ)} {k j : ℕ}
    (hk : is_split_rank_of_set splitClosure P S k)
    (hj : j < k) :
    splitClosure^[j] P ≠ convexHull ℝ S :=
  hk.minimal hj

/-- Definition 5.1.3-extra-1 (2): a natural number `k` is the split rank of the valid inequality
`α x ≤ β` for `conv(S)` relative to `P` and the split-closure operator `splitClosure` when the
inequality is valid for `conv(S)`, becomes valid on the `k`th split closure of `P`, and no
smaller iterate has this validity property. -/
class is_split_rank_of_inequality
    (splitClosure : Set (Fin n → ℝ) → Set (Fin n → ℝ))
    (P S : Set (Fin n → ℝ))
    (α : Fin n → ℝ)
    (β : ℝ)
    (k : ℕ) : Prop where
  /-- The inequality is valid for `conv(S)`. -/
  valid_on_convex_hull : is_valid_inequality (convexHull ℝ S) α β
  /-- The inequality is valid for the `k`th split closure of `P`. -/
  valid_on_iterate : is_valid_inequality (splitClosure^[k] P) α β
  /-- No smaller split-closure iterate of `P` satisfies the inequality. -/
  minimal :
    ∀ ⦃j : ℕ⦄, j < k → ¬ is_valid_inequality (splitClosure^[j] P) α β

/-- `is_split_rank_of_inequality splitClosure P S α β k` unfolds to validity on `conv(S)`,
validity on the `k`th split closure of `P`, and minimality of `k`. -/
theorem is_split_rank_of_inequality_iff
    {splitClosure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P S : Set (Fin n → ℝ)} {α : Fin n → ℝ} {β : ℝ} {k : ℕ} :
    is_split_rank_of_inequality splitClosure P S α β k ↔
      is_valid_inequality (convexHull ℝ S) α β ∧
        is_valid_inequality (splitClosure^[k] P) α β ∧
          ∀ ⦃j : ℕ⦄, j < k → ¬ is_valid_inequality (splitClosure^[j] P) α β := by
  constructor
  · intro hk
    exact ⟨hk.valid_on_convex_hull, hk.valid_on_iterate, hk.minimal⟩
  · rintro ⟨hconv, hiter, hminimal⟩
    exact ⟨hconv, hiter, hminimal⟩

/-- If `k` is the split rank of `α x ≤ β`, then the inequality is not valid on any earlier
split-closure iterate of `P`. -/
theorem is_split_rank_of_inequality.not_valid_on_iterate
    {splitClosure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P S : Set (Fin n → ℝ)} {α : Fin n → ℝ} {β : ℝ} {k j : ℕ}
    (hk : is_split_rank_of_inequality splitClosure P S α β k)
    (hj : j < k) :
    ¬ is_valid_inequality (splitClosure^[j] P) α β :=
  hk.minimal hj

end Definition513Extra1
