/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Logic.Equiv.Basic

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling for this file:
-- * primary domain: permutation-group orbits for orbital fixing in a symmetric binary MILP
-- * sampled owner abstractions:
--   - mathlib's canonical orbit owner `MulAction.orbit`
--   - mathlib's canonical transitivity consequence `MulAction.orbit_eq_univ`
--   - mathlib's characterization theorem `MulAction.isPretransitive_iff_orbit_eq_univ`
--   - Chapter 9.5 Exercise 9.21's recall-only pattern for permutation-action facts already owned
--     upstream
-- * source/core/bridge triage:
--   - Example 9.14 is a `bridge/view` use of the canonical permutation-action owner
--   - `MulAction.orbit` is the `core/canonical` owner
--   - the source-facing membership consequence is used by orbital fixing
-- * primitive data: the index type `Fin n`, a chosen variable index `i`, and the full symmetric
--   group action
-- * derived API: the full-orbit fact `orbit_eq_univ` and its point-membership consequence

open MulAction

section Example_9_14

variable {n : ℕ}

/-- Example 9.14. Any two variable indices lie in the same permutation orbit under the full
symmetric-group action. -/
theorem example_9_14_mem_orbit (i j : Fin n) :
    j ∈ orbit (Equiv.Perm (Fin n)) i := by
  -- The transposition swapping `i` and `j` sends `i` to `j`.
  exact MulAction.mem_orbit_iff.mpr ⟨Equiv.swap i j, Equiv.swap_apply_left i j⟩

/-- Example 9.14. Under the full symmetric-group action, the orbit of any variable index is all
of `Fin n`. -/
theorem example_9_14_orbit_eq_univ (i : Fin n) :
    orbit (Equiv.Perm (Fin n)) i = Set.univ := by
  -- Every index lies in the orbit via the transposition witness above.
  apply Set.eq_univ_of_forall
  intro j
  exact example_9_14_mem_orbit i j

end Example_9_14
