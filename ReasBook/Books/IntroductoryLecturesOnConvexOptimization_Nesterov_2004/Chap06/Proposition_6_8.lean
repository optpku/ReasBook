/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: the estimate `‖v k - xStar‖² ≤ 2 * D` gives a uniform closed ball centered
-- at `xStar` containing every `v k`. Since each `x k` and `y k` lies in the convex hull of the
-- finite prefix `v 0, ..., v k`, convexity of that closed ball implies the same uniform bound for
-- `x k` and `y k`. Therefore the union of the three ranges is bounded.
/-- Helper for Proposition 6.8: each finite prefix convex hull of `v` is contained in the convex
hull of the full range of `v`. -/
lemma prefix_convexHull_subset_range_convexHull
    (v : ℕ → E) (k : ℕ) :
    convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)) ⊆ convexHull ℝ (Set.range v) := by
  -- Every point in the prefix already lies in the full range, so monotonicity of `convexHull`
  -- upgrades the finite hull to the global hull.
  refine convexHull_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨i, rfl⟩

/-- Helper for Proposition 6.8: the squared-distance estimate puts the range of `v` inside one
closed ball centered at `xStar`. -/
lemma range_subset_closedBall_of_sqDist_le
    (xStar : E) (D : ℝ) (v : ℕ → E)
    (hv : ∀ k, ‖v k - xStar‖ ^ 2 ≤ 2 * D) :
    Set.range v ⊆ Metric.closedBall xStar (Real.sqrt (2 * D)) := by
  rintro _ ⟨k, rfl⟩
  rw [mem_closedBall_iff_norm]
  -- Convert the squared-distance control into a norm bound with `sqrt`.
  exact Real.le_sqrt_of_sq_le (by simpa [pow_two] using hv k)

/-- Core owner form: if `v` has bounded range and each `x_k` and `y_k` lies in the convex hull of
the finite prefix `v_0, ..., v_k`, then the union of the three ranges is bounded. -/
theorem bounded_union_of_prefix_convex_hull_sequences_of_isBounded
    (v x y : ℕ → E)
    (hx : ∀ k, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hy : ∀ k, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hv : Bornology.IsBounded (Set.range v)) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := by
  -- The source proof works with one fixed container: `convexHull ℝ (Set.range v)`.
  have hconv : Bornology.IsBounded (convexHull ℝ (Set.range v)) :=
    (isBounded_convexHull).2 hv
  have hx_subset : Set.range x ⊆ convexHull ℝ (Set.range v) := by
    rintro _ ⟨k, rfl⟩
    exact prefix_convexHull_subset_range_convexHull v k (hx k)
  have hy_subset : Set.range y ⊆ convexHull ℝ (Set.range v) := by
    rintro _ ⟨k, rfl⟩
    exact prefix_convexHull_subset_range_convexHull v k (hy k)
  have hx_bounded : Bornology.IsBounded (Set.range x) := hconv.subset hx_subset
  have hy_bounded : Bornology.IsBounded (Set.range y) := hconv.subset hy_subset
  -- Once all three ranges are bounded, the boundedness of their union is immediate.
  simpa [Set.union_assoc] using hv.union (hx_bounded.union hy_bounded)

/-- The pointwise squared-distance estimate `‖v_k - xStar‖² ≤ 2 D` places the full range of `v`
in a common closed ball, hence `Set.range v` is bounded. -/
theorem isBounded_range_of_sqDist_le
    (xStar : E) (D : ℝ) (v : ℕ → E)
    (hv : ∀ k, ‖v k - xStar‖ ^ 2 ≤ 2 * D) :
    Bornology.IsBounded (Set.range v) := by
  -- The quantitative estimate gives one closed ball containing the entire range of `v`.
  exact Metric.isBounded_closedBall.subset (range_subset_closedBall_of_sqDist_le xStar D v hv)

/-- Proposition 6.8: if each `x_k` and `y_k` lies in the convex hull of the finite prefix
`v_0, ..., v_k` and the points `v_k` satisfy `‖v_k - xStar‖² ≤ 2 D` for all `k ≥ 0`, then
the three sequences are bounded, equivalently the union of their ranges is bounded. Here `D`
is the scalar value corresponding to the source quantity `d(xStar)`. -/
theorem bounded_union_of_prefix_convex_hull_sequences
    (xStar : E) (D : ℝ) (v x y : ℕ → E)
    (hx : ∀ k, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hy : ∀ k, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hv : ∀ k, ‖v k - xStar‖ ^ 2 ≤ 2 * D) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := by
  -- First bound the source sequence `v`, then feed that bound into the abstract convex-hull owner.
  exact bounded_union_of_prefix_convex_hull_sequences_of_isBounded v x y hx hy
    (isBounded_range_of_sqDist_le xStar D v hv)
