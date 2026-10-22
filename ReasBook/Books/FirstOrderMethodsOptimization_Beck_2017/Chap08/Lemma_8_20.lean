/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Metric

variable {α : Type u} [PseudoMetricSpace α]
variable {ι : Type v} [Finite ι] [Nonempty ι]

/- Lemma 8.20 is `source-facing`: the textbook function is the maximum of finitely many
distance-to-set functions. The canonical owner for each summand is `Metric.infDist`, and the
clean finite-family owner is their pointwise supremum over a finite nonempty index type. -/

/-- The function `x ↦ max_i d_{S_i}(x)` associated with a finite nonempty family of sets. -/
noncomputable def max_distance_to_sets (S : ι → Set α) : α → ℝ :=
  fun x ↦ ⨆ i, Metric.infDist x (S i)

-- Proof sketch: unfold `max_distance_to_sets`; the statement is the defining equation written in
-- the source-facing `d_{S_i}` notation.
omit [Finite ι] [Nonempty ι] in
/-- The owner `max_distance_to_sets` is the pointwise supremum of the individual distance
functions `x ↦ d_{S_i}(x)`. -/
theorem max_distance_to_sets_eq_iSup (S : ι → Set α) (x : α) :
    max_distance_to_sets S x = ⨆ i, Metric.infDist x (S i) := by
  -- Unfold the source-facing definition of the maximum distance objective.
  rfl

omit [Finite ι] in
/-- Helper for Lemma 8.20: on a finite nonempty index type, the supremum defining
`max_distance_to_sets` is the finite maximum over `Finset.univ`. -/
lemma max_distance_to_sets_eq_sup'_univ (S : ι → Set α) [Fintype ι] (x : α) :
    max_distance_to_sets S x =
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i)) := by
  classical
  -- Rewrite the conditionally complete supremum as the concrete finite supremum on `univ`.
  rw [max_distance_to_sets_eq_iSup]
  symm
  exact Finset.sup'_univ_eq_ciSup (f := fun i ↦ Metric.infDist x (S i))

/-- Helper for Lemma 8.20: the finite maximum of distance-to-set functions satisfies the same
one-sided triangle inequality as each coordinate distance. -/
lemma max_distance_to_sets_le_add_dist (S : ι → Set α) (x y : α) :
    max_distance_to_sets S x ≤ max_distance_to_sets S y + dist x y := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- Pass from the abstract supremum to a finite maximum so each coordinate can be bounded.
  rw [max_distance_to_sets_eq_sup'_univ, max_distance_to_sets_eq_sup'_univ]
  refine
    Finset.sup'_le (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
      (f := fun i ↦ Metric.infDist x (S i)) ?_
  intro i hi
  -- Apply the triangle inequality to one coordinate and then compare with the outer maximum.
  calc
    Metric.infDist x (S i) ≤ Metric.infDist y (S i) + dist x y :=
      Metric.infDist_le_infDist_add_dist
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun j ↦ Metric.infDist y (S j)) + dist x y := by
      exact add_le_add_left
        (Finset.le_sup' (s := (Finset.univ : Finset ι))
          (f := fun j ↦ Metric.infDist y (S j)) (Finset.mem_univ i)) _

-- Proof sketch: each coordinate function `x ↦ Metric.infDist x (S i)` is `1`-Lipschitz by
-- `Metric.lipschitz_infDist_pt`. Since the index type is finite, the pointwise supremum is an
-- iterated binary `max`, and `LipschitzWith.max` preserves the `1`-Lipschitz constant.
/-- Lemma 8.20: for a finite nonempty family of sets, the function `x ↦ max_i d_{S_i}(x)` is
globally Lipschitz continuous with constant `1`; in particular this applies to the nonempty closed
convex sets of the convex feasibility setting. -/
theorem lipschitzWith_max_distance_to_sets (S : ι → Set α) :
    LipschitzWith 1 (max_distance_to_sets S) := by
  -- The textbook argument is the one-sided triangle inequality followed by the generic
  -- `LipschitzWith.of_le_add` wrapper.
  exact
    LipschitzWith.of_le_add (f := max_distance_to_sets S)
      (fun x y ↦ max_distance_to_sets_le_add_dist (S := S) (x := x) (y := y))

end
