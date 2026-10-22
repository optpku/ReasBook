/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {α : Type v} [LinearOrder α]

/- Definition 8.8 is `source-facing`: the textbook introduces the running minimum of the attained
objective values along a given iterate sequence `x^0, x^1, ...`. In this domain the canonical
finite-minimum owner is mathlib's `Finset.min'` applied to the image of the prefix
`Finset.range (k + 1)`, so the public API records the best value achieved up to iteration `k`
directly as that finite minimum, without introducing a surrogate wrapper for the iterate history. -/

-- Proof sketch: the prefix index set `Finset.range (k + 1)` contains `0`, hence its image under
-- `n ↦ f (x n)` contains the initial objective value `f (x 0)`.
/-- The finite set of objective values attained up to iteration `k` is nonempty. -/
theorem objective_value_prefix_nonempty (f : E → α) (x : ℕ → E) (k : ℕ) :
    ((Finset.range (k + 1)).image fun n ↦ f (x n)).Nonempty := by
  -- The prefix always contains the initial index `0`.
  refine ⟨f (x 0), Finset.mem_image.mpr ?_⟩
  -- Map that initial index into the finite set of attained objective values.
  exact ⟨0, by simp, rfl⟩

/-- Definition 8.8: the best achieved function value at iteration `k` is the minimum of the
objective values `f (x^n)` over all indices `n = 0, 1, …, k`. -/
def best_achieved_function_value (f : E → α) (x : ℕ → E) (k : ℕ) : α :=
  ((Finset.range (k + 1)).image fun n ↦ f (x n)).min' (objective_value_prefix_nonempty f x k)

/-- Helper for Definition 8.8: each prefix objective value belongs to the image finset of all
objective values attained up to iteration `k`. -/
lemma objective_value_mem_prefix_image
    (f : E → α) (x : ℕ → E) {k n : ℕ} (hn : n ∈ Finset.range (k + 1)) :
    f (x n) ∈ ((Finset.range (k + 1)).image fun m ↦ f (x m)) := by
  -- Record that the value comes from the index `n` already lying in the prefix.
  exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

-- Proof sketch: for `n ≤ k`, the value `f (x n)` belongs to the image of `Finset.range (k + 1)`.
-- Then apply `Finset.min'_le` to the defining finite set of attained objective values.
/-- The best achieved value up to iteration `k` is less than or equal to every objective value
attained by the first `k + 1` iterates. -/
theorem best_achieved_function_value_le_objective_value
    (f : E → α) (x : ℕ → E) (k n : ℕ) (hn : n ∈ Finset.range (k + 1)) :
    best_achieved_function_value f x k ≤ f (x n) := by
  -- Unfold the running minimum so the claim becomes the standard `Finset.min'` bound.
  unfold best_achieved_function_value
  -- Apply the minimum comparison to the member indexed by `n`.
  exact Finset.min'_le _ _ (objective_value_mem_prefix_image f x hn)

end
