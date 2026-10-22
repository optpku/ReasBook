/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {ι : Type v} {α : Type u} [Fintype ι] [Nonempty ι] [PseudoMetricSpace α]

/- Definition 8.13 is `source-facing`: the textbook reformulates the feasibility problem for a
finite family of sets through the finite maximum of the point-to-set distances. The canonical
owners are therefore `Metric.infDist` for distance to a set, `Finset.sup'` for the finite maximum,
and mathlib's `IsMinOn` for the minimization viewpoint. The convexity hypotheses from the textbook
do not affect this metric formulation itself, so they are omitted from the owner and left for
later algorithmic results. -/

/-- Definition 8.13: the convex feasibility problem for a finite nonempty family of sets
`S i` can be reformulated through the max-distance objective
`x ↦ max_i d_{S_i}(x)`. -/
def convex_feasibility_max_distance (S : ι → Set α) : α → ℝ :=
  fun x ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i))

-- Proof sketch: unfold `convex_feasibility_max_distance`; evaluation at `x` is exactly the
-- defining finite maximum of the distances from `x` to the sets `S i`.
/-- Evaluating the convex-feasibility max-distance objective at `x` gives the finite maximum of the
distances from `x` to the sets `S i`. -/
@[simp] theorem convex_feasibility_max_distance_apply (S : ι → Set α) (x : α) :
    convex_feasibility_max_distance S x =
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i)) := by
  -- Unfold the source-facing definition so evaluation becomes the defining finite maximum.
  rfl

omit [Fintype ι] [Nonempty ι] [PseudoMetricSpace α] in
/-- Helper for Definition 8.13: a point in the total intersection provides a witness in each set of
the family. -/
theorem set_nonempty_of_nonempty_iInter {S : ι → Set α} (hinter : (⋂ i, S i).Nonempty) :
    ∀ i, (S i).Nonempty := by
  intro i
  -- Project the intersection witness to the `i`-th coordinate set.
  rcases hinter with ⟨x, hx⟩
  exact ⟨x, (Set.mem_iInter.mp hx) i⟩

/-- Helper for Definition 8.13: the max-distance objective is always nonnegative. -/
theorem convex_feasibility_max_distance_nonneg (S : ι → Set α) (x : α) :
    0 ≤ convex_feasibility_max_distance S x := by
  -- Rewrite the objective as a finite maximum of the individual set distances.
  rw [convex_feasibility_max_distance_apply]
  -- Compare `0` first to one distance term and then to the finite maximum.
  obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  exact le_trans
    (Metric.infDist_nonneg (x := x) (s := S i))
    (Finset.le_sup' (s := (Finset.univ : Finset ι)) (f := fun j ↦ Metric.infDist x (S j)) hi)

/-- Helper for Definition 8.13: every feasible point has zero max-distance objective value. -/
theorem convex_feasibility_max_distance_eq_zero_of_mem_iInter
    (S : ι → Set α) {x : α} (hx : x ∈ ⋂ i, S i) :
    convex_feasibility_max_distance S x = 0 := by
  -- Rewrite the objective as a finite maximum and show each coordinate distance vanishes.
  rw [convex_feasibility_max_distance_apply]
  refine Finset.sup'_eq_of_forall
    (s := (Finset.univ : Finset ι))
    (H := Finset.univ_nonempty)
    (f := fun i ↦ Metric.infDist x (S i))
    (a := 0) ?_
  intro i hi
  -- Membership in every set forces each point-to-set distance to be zero.
  exact Metric.infDist_zero_of_mem ((Set.mem_iInter.mp hx) i)

/-- Helper for Definition 8.13: if the max-distance objective vanishes, then the point lies in
every closed set of the family. -/
theorem mem_iInter_of_convex_feasibility_max_distance_eq_zero
    {S : ι → Set α} (hclosed : ∀ i, IsClosed (S i)) (hinter : (⋂ i, S i).Nonempty) {x : α}
    (hx0 : convex_feasibility_max_distance S x = 0) :
    x ∈ ⋂ i, S i := by
  -- Reduce intersection membership to coordinatewise membership.
  rw [Set.mem_iInter]
  intro i
  have hi : i ∈ (Finset.univ : Finset ι) := by
    simp
  have hi_le : Metric.infDist x (S i) ≤ convex_feasibility_max_distance S x := by
    -- Each coordinate distance is bounded above by the finite maximum.
    rw [convex_feasibility_max_distance_apply]
    exact Finset.le_sup' (s := (Finset.univ : Finset ι)) (f := fun j ↦ Metric.infDist x (S j)) hi
  have hi_eq_zero : Metric.infDist x (S i) = 0 := by
    -- Combine nonnegativity with the zero objective value to pin down the `i`-th distance.
    apply le_antisymm
    · rw [hx0] at hi_le
      exact hi_le
    · exact Metric.infDist_nonneg (x := x) (s := S i)
  -- Closedness upgrades zero distance to actual membership once nonemptiness is available.
  exact ((hclosed i).mem_iff_infDist_zero (set_nonempty_of_nonempty_iInter hinter i)).2 hi_eq_zero

-- Proof sketch: if `x ∈ ⋂ i, S i`, then every distance term is zero, so the objective value is
-- zero and hence minimal because each `Metric.infDist` is nonnegative. Conversely, if `x`
-- globally minimizes the objective, compare it with a feasible point from `hinter` to see that
-- the minimum value is zero. Then each distance term vanishes, and closedness together with the
-- nonemptiness inherited from `hinter` implies `x ∈ S i` for every `i`.
/-- The max-distance formulation has the same global minimizers as the original feasibility
problem: under closedness and nonempty intersection, a point minimizes the objective exactly when
it lies in `⋂ i, S i`. -/
theorem isMinOn_convex_feasibility_max_distance_iff_mem_iInter
    {S : ι → Set α} (hclosed : ∀ i, IsClosed (S i)) (hinter : (⋂ i, S i).Nonempty) {x : α} :
    IsMinOn (convex_feasibility_max_distance S) Set.univ x ↔ x ∈ ⋂ i, S i := by
  constructor
  · intro hxmin
    rcases hinter with ⟨y, hy⟩
    have hx_le : convex_feasibility_max_distance S x ≤ convex_feasibility_max_distance S y := by
      -- Rewrite global minimality on `Set.univ` as pointwise comparison with every test point.
      exact (isMinOn_univ_iff (f := convex_feasibility_max_distance S) (a := x)).1 hxmin y
    have hx_le_zero : convex_feasibility_max_distance S x ≤ 0 := by
      -- Compare the minimizer with the feasible witness, whose objective value is zero.
      rw [convex_feasibility_max_distance_eq_zero_of_mem_iInter S hy] at hx_le
      exact hx_le
    have hx0 : convex_feasibility_max_distance S x = 0 := by
      -- Nonnegativity shows that the minimizing value can only be zero.
      exact le_antisymm hx_le_zero (convex_feasibility_max_distance_nonneg S x)
    -- A zero objective means every coordinate distance is zero, hence `x` is feasible.
    exact mem_iInter_of_convex_feasibility_max_distance_eq_zero hclosed ⟨y, hy⟩ hx0
  · intro hx
    -- Route correction: prove optimality by showing feasible points have value `0` and every
    -- value of the max-distance objective is nonnegative.
    rw [isMinOn_univ_iff]
    intro y
    rw [convex_feasibility_max_distance_eq_zero_of_mem_iInter S hx]
    exact convex_feasibility_max_distance_nonneg S y

end
