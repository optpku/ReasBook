/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}

/- Algorithm 8.6 is `source-facing` in the convex-feasibility API. The canonical owner for each
projection step is the chapter map `metricProjection`, while the tie-breaking rule among farthest
sets should stay explicit rather than being hidden behind a noncanonical choice of maximizer.
Accordingly, the main declaration is the recursive iterate sequence generated from an index
selection rule `i`, and the greedy argmax condition is recorded separately by an admissibility
predicate on that rule. -/

/-- Algorithm 8.6: for a finite family `S` of nonempty closed convex sets, an initial point `x0`,
and a rule `i` selecting at each iterate one of the currently farthest sets, the greedy projection
algorithm generates the sequence `x^{k+1} = P_{S_{i_k}}(x^k)`. -/
def greedy_projection_method (S : Fin m → Set E)
    (hS_nonempty : ∀ j, (S j).Nonempty) (hS_closed : ∀ j, IsClosed (S j))
    (hS_convex : ∀ j, Convex ℝ (S j)) (i : ℕ → E → Fin m) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 =>
      -- Route correction: the chapter-level metric projection API is parameterized by completeness,
      -- so each closed set contributes that input through `hS_closed ik`.
      let xk := greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k
      let ik := i k xk
      metricProjection (S ik) (hS_nonempty ik) (hS_closed ik) (hS_convex ik) xk

/-- An index-selection rule is admissible for the greedy projection method when, at each current
iterate `x^k`, the selected index `i_k` attains the maximum of the distance profile
`j ↦ infDist x^k (S j)` over the finite family of sets. -/
def greedy_projection_method_is_admissible (S : Fin m → Set E)
    (hS_nonempty : ∀ j, (S j).Nonempty) (hS_closed : ∀ j, IsClosed (S j))
    (hS_convex : ∀ j, Convex ℝ (S j)) (i : ℕ → E → Fin m) (x0 : E) : Prop :=
  ∀ k,
    let xk := greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k
    ∀ j : Fin m, infDist xk (S j) ≤ infDist xk (S (i k xk))

-- Proof sketch: unfold the recursive definition of `greedy_projection_method` at `0`.
/-- The greedy-projection sequence starts at the prescribed initial point. -/
theorem greedy_projection_method_zero (S : Fin m → Set E)
    (hS_nonempty : ∀ j, (S j).Nonempty) (hS_closed : ∀ j, IsClosed (S j))
    (hS_convex : ∀ j, Convex ℝ (S j)) (i : ℕ → E → Fin m) (x0 : E) :
    greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 0 = x0 := by
  -- The base case is exactly the `0` branch of the recursive definition.
  rfl

-- Proof sketch: unfold the recursive definition of `greedy_projection_method` at `k + 1`.
/-- One step of the greedy projection method projects the current iterate onto the set selected by
the current maximizing index rule. -/
theorem greedy_projection_method_succ (S : Fin m → Set E)
    (hS_nonempty : ∀ j, (S j).Nonempty) (hS_closed : ∀ j, IsClosed (S j))
    (hS_convex : ∀ j, Convex ℝ (S j)) (i : ℕ → E → Fin m) (x0 : E) (k : ℕ) :
    greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 (k + 1) =
      metricProjection
        (S (i k (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k)))
        (hS_nonempty (i k (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k)))
        (hS_closed (i k (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k)))
        (hS_convex (i k (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k)))
        (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k) := by
  -- Unfolding one recursive step exposes the greedy projection update verbatim.
  rfl

-- Proof sketch: unfold `greedy_projection_method_is_admissible`, specialize at the index `k`,
-- and evaluate the resulting maximality condition at the competitor `j`.
/-- Under the admissibility condition, the selected set at iteration `k` has distance from the
current iterate at least as large as every other set in the family. -/
theorem greedy_projection_method_selected_set_farthest
    {S : Fin m → Set E} {hS_nonempty : ∀ j, (S j).Nonempty}
    {hS_closed : ∀ j, IsClosed (S j)} {hS_convex : ∀ j, Convex ℝ (S j)}
    {i : ℕ → E → Fin m} {x0 : E}
    (h : greedy_projection_method_is_admissible S hS_nonempty hS_closed hS_convex i x0)
    (k : ℕ) (j : Fin m) :
    infDist (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k) (S j) ≤
      infDist (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k)
        (S (i k (greedy_projection_method S hS_nonempty hS_closed hS_convex i x0 k))) := by
  -- The admissibility predicate stores exactly the farthest-set inequality at each iteration.
  simpa [greedy_projection_method_is_admissible] using h k j

end
