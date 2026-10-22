/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- Lemma 1.5.1: the fundamental group of `ℝ` based at `0` is trivial. -/
-- Proof sketch: contract `ℝ` to `0` by the straight-line homotopy `(s, t) ↦ (1 - t) * s`,
-- obtain that `ℝ` is contractible and hence simply connected, and then identify the
-- fundamental group at `0` as a subsingleton loop-class group.
theorem fundamental_group_real_zero_subsingleton :
    Subsingleton (FundamentalGroup ℝ 0) := by
  let _ : SimplyConnectedSpace ℝ := inferInstance
  change Subsingleton (Path.Homotopic.Quotient (0 : ℝ) (0 : ℝ))
  infer_instance

/-- Every element of the fundamental group of `ℝ` at `0` is the identity. -/
-- Proof sketch: apply the subsingleton statement for `FundamentalGroup ℝ 0` and compare any
-- element with the unit element.
theorem fundamental_group_real_zero_eq_one (γ : FundamentalGroup ℝ 0) :
    γ = 1 :=
  fundamental_group_real_zero_subsingleton.elim γ 1
