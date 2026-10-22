/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

open scoped BigOperators

section

local notation "Point" => EuclideanSpace ℝ (Fin 2)
local notation "DualPoint" => Fin 4 → ℝ

-- Domain sampling:
-- * source-facing layer: the smallest-enclosing-circle exercise on center/radius-squared pairs
--   and dual simplex multipliers;
-- * core/canonical owners inspected: `IsMinOn`, `IsMaxOn`, `Metric.closedBall`, `stdSimplex`,
--   `Finset.centerMass`;
-- * owner choice: keep the source-facing center/radius primitive data for the primal feasible set
--   because the radius varies with the point, so `Metric.closedBall` is only a companion
--   geometric owner here, while the dual feasible region itself is canonically `stdSimplex`.
-- * bridge/view decision: keep the raw weighted dual sum because the dual objective is defined on
--   all multipliers, then expose the canonical `centerMass` view on the feasible simplex where
--   the weights sum to `1`.

/-- The planar point with coordinates `(x, y)` used in Exercise 9.6. -/
def chapter09Exercise96Point (x y : ℝ) : Point :=
  EuclideanSpace.single 0 x + EuclideanSpace.single 1 y

/-- The first coordinate of `chapter09Exercise96Point x y` is `x`. -/
@[simp] theorem chapter09Exercise96Point_apply_zero (x y : ℝ) :
    chapter09Exercise96Point x y 0 = x := by
  simp [chapter09Exercise96Point]

/-- The second coordinate of `chapter09Exercise96Point x y` is `y`. -/
@[simp] theorem chapter09Exercise96Point_apply_one (x y : ℝ) :
    chapter09Exercise96Point x y 1 = y := by
  simp [chapter09Exercise96Point]

/-- The squared norm of `chapter09Exercise96Point x y` is `x^2 + y^2`. -/
@[simp] theorem chapter09Exercise96Point_normSq (x y : ℝ) :
    ‖chapter09Exercise96Point x y‖ ^ (2 : ℕ) = x ^ (2 : ℕ) + y ^ (2 : ℕ) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  norm_num [chapter09Exercise96Point]

/-- A primal variable for Exercise 9.6, consisting of the circle center and its squared
radius. -/
structure Chapter09Exercise96PrimalPoint where
  center : Point
  radiusSq : ℝ

/-- The four points in the plane that must be contained in the circle of Exercise 9.6. -/
def chapter09Exercise96Points : Fin 4 → Point :=
  ![
    chapter09Exercise96Point 1 (-4),
    chapter09Exercise96Point (-2) (-2),
    chapter09Exercise96Point (-4) 1,
    chapter09Exercise96Point 4 5
  ]

@[simp] theorem chapter09Exercise96Points_zero :
    chapter09Exercise96Points 0 = chapter09Exercise96Point 1 (-4) :=
  rfl

@[simp] theorem chapter09Exercise96Points_one :
    chapter09Exercise96Points 1 = chapter09Exercise96Point (-2) (-2) :=
  rfl

@[simp] theorem chapter09Exercise96Points_two :
    chapter09Exercise96Points 2 = chapter09Exercise96Point (-4) 1 :=
  rfl

@[simp] theorem chapter09Exercise96Points_three :
    chapter09Exercise96Points 3 = chapter09Exercise96Point 4 5 :=
  rfl

/-- The primal convex objective for Exercise 9.6 minimizes the squared radius. -/
def chapter09Exercise96PrimalObjective (z : Chapter09Exercise96PrimalPoint) : ℝ :=
  z.radiusSq

/-- Unfolding `chapter09Exercise96PrimalObjective` recovers the squared radius. -/
@[simp] theorem chapter09Exercise96PrimalObjective_eq (z : Chapter09Exercise96PrimalPoint) :
    chapter09Exercise96PrimalObjective z = z.radiusSq :=
  rfl

/-- The primal feasible set for Exercise 9.6 consists of the center-radius pairs whose closed
disk contains all four source points. -/
def chapter09Exercise96PrimalFeasibleSet : Set Chapter09Exercise96PrimalPoint :=
  {z | ∀ i : Fin 4, ‖chapter09Exercise96Points i - z.center‖ ^ (2 : ℕ) ≤ z.radiusSq}

/-- Membership in `chapter09Exercise96PrimalFeasibleSet` is exactly the source condition that the
squared distance from the center to each source point is at most the squared radius. -/
@[simp] theorem mem_chapter09Exercise96PrimalFeasibleSet
    (z : Chapter09Exercise96PrimalPoint) :
    z ∈ chapter09Exercise96PrimalFeasibleSet ↔
      ∀ i : Fin 4, ‖chapter09Exercise96Points i - z.center‖ ^ (2 : ℕ) ≤ z.radiusSq :=
  Iff.rfl

/-- Every feasible primal point has nonnegative squared radius. -/
theorem chapter09Exercise96_radiusSq_nonneg_of_mem_primalFeasibleSet
    {z : Chapter09Exercise96PrimalPoint} (hz : z ∈ chapter09Exercise96PrimalFeasibleSet) :
    0 ≤ z.radiusSq := by
  have h0 := (mem_chapter09Exercise96PrimalFeasibleSet z).1 hz 0
  nlinarith

/-- With a nonnegative squared radius, the primal feasible set is equivalently the condition that
all four source points lie in the corresponding closed ball. -/
theorem mem_chapter09Exercise96PrimalFeasibleSet_iff_forall_mem_closedBall
    (z : Chapter09Exercise96PrimalPoint) (hz0 : 0 ≤ z.radiusSq) :
    z ∈ chapter09Exercise96PrimalFeasibleSet ↔
      ∀ i : Fin 4,
        chapter09Exercise96Points i ∈ Metric.closedBall z.center (Real.sqrt z.radiusSq) := by
  constructor
  · intro hz i
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hi := (mem_chapter09Exercise96PrimalFeasibleSet z).1 hz i
    exact
      (Real.le_sqrt (norm_nonneg _) hz0).2 <|
        by simpa [Real.sq_sqrt hz0] using hi
  · intro hz
    rw [mem_chapter09Exercise96PrimalFeasibleSet]
    intro i
    have hi := hz i
    rw [Metric.mem_closedBall, dist_eq_norm] at hi
    exact
      by simpa [Real.sq_sqrt hz0] using
        (Real.le_sqrt (norm_nonneg _) hz0).1 hi

/-- Any feasible primal point defines a closed ball centered at `z.center` with radius
`√z.radiusSq` containing the four source points. -/
theorem chapter09Exercise96_mem_closedBall_of_mem_primalFeasibleSet
    {z : Chapter09Exercise96PrimalPoint} (hz : z ∈ chapter09Exercise96PrimalFeasibleSet)
    (i : Fin 4) :
    chapter09Exercise96Points i ∈ Metric.closedBall z.center (Real.sqrt z.radiusSq) := by
  exact
    (mem_chapter09Exercise96PrimalFeasibleSet_iff_forall_mem_closedBall z
        (chapter09Exercise96_radiusSq_nonneg_of_mem_primalFeasibleSet hz)).1 hz i

/-- The dual barycenter associated to a multiplier vector for Exercise 9.6. -/
def chapter09Exercise96DualBarycenter (l : DualPoint) : Point :=
  ∑ i : Fin 4, l i • chapter09Exercise96Points i

/-- On the feasible simplex `stdSimplex ℝ (Fin 4)`, the source weighted-sum dual barycenter is
exactly mathlib's canonical finite center of mass. -/
theorem chapter09Exercise96DualBarycenter_eq_centerMass
    (l : stdSimplex ℝ (Fin 4)) :
    chapter09Exercise96DualBarycenter l = Finset.univ.centerMass l chapter09Exercise96Points := by
  calc
    chapter09Exercise96DualBarycenter l = ∑ i : Fin 4, l i • chapter09Exercise96Points i := by
      simp [chapter09Exercise96DualBarycenter]
    _ = Finset.univ.centerMass l chapter09Exercise96Points := by
      symm
      exact Finset.univ.centerMass_eq_of_sum_1 chapter09Exercise96Points (stdSimplex.sum_eq_one l)

/-- The dual objective for the smallest-enclosing-circle formulation of Exercise 9.6. -/
def chapter09Exercise96DualObjective (l : DualPoint) : ℝ :=
  (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i‖ ^ (2 : ℕ)) -
    ‖chapter09Exercise96DualBarycenter l‖ ^ (2 : ℕ)

/-- Unfolding `chapter09Exercise96DualObjective` recovers the source quadratic dual formula. -/
@[simp] theorem chapter09Exercise96DualObjective_eq (l : DualPoint) :
    chapter09Exercise96DualObjective l =
      (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i‖ ^ (2 : ℕ)) -
        ‖chapter09Exercise96DualBarycenter l‖ ^ (2 : ℕ) :=
  rfl

/-- The smallest enclosing circle in Exercise 9.6 has center `(1, 1)` and squared radius
`25`. -/
def chapter09Exercise96PrimalOptimizer : Chapter09Exercise96PrimalPoint :=
  { center := chapter09Exercise96Point 1 1, radiusSq := 25 }

/-- The optimal center in `chapter09Exercise96PrimalOptimizer` is `(1, 1)`. -/
@[simp] theorem chapter09Exercise96PrimalOptimizer_center :
    chapter09Exercise96PrimalOptimizer.center = chapter09Exercise96Point 1 1 :=
  rfl

/-- The optimal squared radius in `chapter09Exercise96PrimalOptimizer` is `25`. -/
@[simp] theorem chapter09Exercise96PrimalOptimizer_radiusSq :
    chapter09Exercise96PrimalOptimizer.radiusSq = 25 :=
  rfl

/-- The named primal optimizer is feasible for the smallest-enclosing-circle problem. -/
@[simp] theorem chapter09Exercise96PrimalOptimizer_mem_primalFeasibleSet :
    chapter09Exercise96PrimalOptimizer ∈ chapter09Exercise96PrimalFeasibleSet := by
  rw [mem_chapter09Exercise96PrimalFeasibleSet]
  intro i
  fin_cases i <;>
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;>
    norm_num [chapter09Exercise96Points, chapter09Exercise96PrimalOptimizer,
      chapter09Exercise96Point]

/-- The solved dual multiplier vector for Exercise 9.6 is `(1 / 3, 0, 1 / 4, 5 / 12)`. -/
def chapter09Exercise96DualOptimizer : stdSimplex ℝ (Fin 4) :=
  ⟨![(1 / 3 : ℝ), 0, (1 / 4 : ℝ), (5 / 12 : ℝ)], by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_fin_one]⟩

/-- The coordinates of the solved dual multiplier vector are the source weights
`(1 / 3, 0, 1 / 4, 5 / 12)`. -/
@[simp] theorem chapter09Exercise96DualOptimizer_apply (i : Fin 4) :
    chapter09Exercise96DualOptimizer i =
      ![(1 / 3 : ℝ), 0, (1 / 4 : ℝ), (5 / 12 : ℝ)] i := by
  rfl

/-- The `i`-th coordinate of the dual barycenter is the weighted sum of the `i`-th source-point
coordinates. -/
@[simp] theorem chapter09Exercise96DualBarycenter_apply (l : DualPoint) (i : Fin 2) :
    chapter09Exercise96DualBarycenter l i =
      ∑ j : Fin 4, l j * chapter09Exercise96Points j i := by
  simp [chapter09Exercise96DualBarycenter]

/-- The source points have squared norms `17`, `8`, `17`, and `41`. -/
@[simp] theorem chapter09Exercise96Points_normSq_zero :
    ‖chapter09Exercise96Points 0‖ ^ (2 : ℕ) = 17 := by
  norm_num [chapter09Exercise96Points, chapter09Exercise96Point_normSq, Matrix.cons_val_zero,
    Matrix.cons_val_fin_one]

@[simp] theorem chapter09Exercise96Points_normSq_one :
    ‖chapter09Exercise96Points 1‖ ^ (2 : ℕ) = 8 := by
  norm_num [chapter09Exercise96Points, chapter09Exercise96Point_normSq, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

@[simp] theorem chapter09Exercise96Points_normSq_two :
    ‖chapter09Exercise96Points 2‖ ^ (2 : ℕ) = 17 := by
  norm_num [chapter09Exercise96Points, chapter09Exercise96Point_normSq, Matrix.cons_val_two,
    Matrix.cons_val_fin_one]

@[simp] theorem chapter09Exercise96Points_normSq_three :
    ‖chapter09Exercise96Points 3‖ ^ (2 : ℕ) = 41 := by
  norm_num [chapter09Exercise96Points, chapter09Exercise96Point_normSq, Matrix.cons_val_three,
    Matrix.cons_val_fin_one]

/-- The primal optimizer center `(1, 1)` has squared norm `2`. -/
@[simp] theorem chapter09Exercise96PrimalOptimizer_center_normSq :
    ‖chapter09Exercise96PrimalOptimizer.center‖ ^ (2 : ℕ) = 2 := by
  rw [chapter09Exercise96PrimalOptimizer_center]
  norm_num [chapter09Exercise96Point_normSq]

/-- The solved dual barycenter agrees with the primal optimizer center `(1, 1)`. -/
@[simp] theorem chapter09Exercise96DualBarycenter_dualOptimizer :
    chapter09Exercise96DualBarycenter chapter09Exercise96DualOptimizer =
      chapter09Exercise96PrimalOptimizer.center := by
  ext i
  fin_cases i <;>
    norm_num [chapter09Exercise96DualBarycenter_apply, chapter09Exercise96DualOptimizer_apply,
      chapter09Exercise96Points, chapter09Exercise96PrimalOptimizer, chapter09Exercise96Point,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_fin_one]

/-- Evaluating the primal objective at `chapter09Exercise96PrimalOptimizer` gives `25`. -/
@[simp] theorem chapter09Exercise96PrimalObjective_primalOptimizer :
    chapter09Exercise96PrimalObjective chapter09Exercise96PrimalOptimizer = 25 :=
  rfl

/-- Evaluating the dual objective at `chapter09Exercise96DualOptimizer` gives `25`. -/
@[simp] theorem chapter09Exercise96DualObjective_dualOptimizer :
    chapter09Exercise96DualObjective chapter09Exercise96DualOptimizer = 25 := by
  rw [chapter09Exercise96DualObjective_eq, chapter09Exercise96DualBarycenter_dualOptimizer,
    chapter09Exercise96PrimalOptimizer_center]
  norm_num [chapter09Exercise96DualOptimizer_apply, chapter09Exercise96Points_normSq_zero,
    chapter09Exercise96Points_normSq_one, chapter09Exercise96Points_normSq_two,
    chapter09Exercise96Points_normSq_three, chapter09Exercise96Point_normSq, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_fin_one]

/-- Helper for Chapter09 Exercise 9.6: the simplex-weighted squared distances to a center split
into the dual objective and the squared distance from that center to the weighted barycenter. -/
theorem chapter09Exercise96WeightedDistSq_eq_dualObjective_add_barycenterDistSq
    (l : stdSimplex ℝ (Fin 4)) (c : Point) :
    (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i - c‖ ^ (2 : ℕ)) =
      chapter09Exercise96DualObjective l +
        ‖chapter09Exercise96DualBarycenter l - c‖ ^ (2 : ℕ) := by
  have hSum : ∑ i : Fin 4, l i = 1 := stdSimplex.sum_eq_one l
  have hMass :
      (∑ i : Fin 4, l i) * ‖c‖ ^ (2 : ℕ) = ‖c‖ ^ (2 : ℕ) := by
    nlinarith [hSum]
  let pointInner : Fin 4 → ℝ :=
    fun i : Fin 4 ↦ inner ℝ (chapter09Exercise96Points i) c
  let weightedInner : ℝ :=
    Finset.univ.sum fun i : Fin 4 ↦ l i * pointInner i
  let expandedSummand : Fin 4 → ℝ :=
    fun i : Fin 4 ↦
      (l i * ‖chapter09Exercise96Points i‖ ^ (2 : ℕ)) +
        (-2) * (l i * pointInner i) +
          (l i * ‖c‖ ^ (2 : ℕ))
  have hInner :
      weightedInner = inner ℝ (chapter09Exercise96DualBarycenter l) c := by
    -- Convert the weighted linear term into the barycenter inner product.
    unfold weightedInner pointInner
    symm
    simpa [chapter09Exercise96DualBarycenter, real_inner_smul_left] using
      (sum_inner (𝕜 := ℝ) (E := Point) Finset.univ
        (fun i : Fin 4 ↦ l i • chapter09Exercise96Points i) c)
  have hLeft :
      (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i - c‖ ^ (2 : ℕ)) =
        (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i‖ ^ (2 : ℕ)) +
          (-2) * weightedInner +
            ‖c‖ ^ (2 : ℕ) := by
    -- Expand the distance square termwise and collect the weighted sums.
    calc
      (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i - c‖ ^ (2 : ℕ)) =
          (∑ i : Fin 4, expandedSummand i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        unfold expandedSummand pointInner
        rw [norm_sub_sq_real]
        ring
      _ =
          (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i‖ ^ (2 : ℕ)) +
            (-2) * weightedInner +
              (∑ i : Fin 4, l i) * ‖c‖ ^ (2 : ℕ) := by
        unfold expandedSummand weightedInner
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ =
          (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i‖ ^ (2 : ℕ)) +
            (-2) * weightedInner +
              ‖c‖ ^ (2 : ℕ) := by
        rw [hMass]
  have hRight :
      chapter09Exercise96DualObjective l +
          ‖chapter09Exercise96DualBarycenter l - c‖ ^ (2 : ℕ) =
        (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i‖ ^ (2 : ℕ)) +
          (-2) * inner ℝ (chapter09Exercise96DualBarycenter l) c +
            ‖c‖ ^ (2 : ℕ) := by
    -- Expand the correction term around the barycenter.
    rw [chapter09Exercise96DualObjective_eq, norm_sub_sq_real]
    ring
  -- Both sides now share the same quadratic normal form.
  nlinarith [hLeft, hRight, hInner]

/-- Helper for Chapter09 Exercise 9.6: averaging the primal feasibility inequalities with simplex
weights still bounds the weighted squared distance by the primal radius squared. -/
theorem chapter09Exercise96WeightedDistSq_le_radiusSq_of_memPrimalFeasibleSet
    {z : Chapter09Exercise96PrimalPoint} (hz : z ∈ chapter09Exercise96PrimalFeasibleSet)
    (l : stdSimplex ℝ (Fin 4)) :
    (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i - z.center‖ ^ (2 : ℕ)) ≤
      z.radiusSq := by
  have hLe :
      ∀ i : Fin 4,
        l i * ‖chapter09Exercise96Points i - z.center‖ ^ (2 : ℕ) ≤ l i * z.radiusSq := by
    intro i
    -- Multiply each primal-feasible inequality by the nonnegative simplex weight.
    exact mul_le_mul_of_nonneg_left
      ((mem_chapter09Exercise96PrimalFeasibleSet z).1 hz i)
      (l.2.1 i)
  -- Summing the weighted bounds collapses by the simplex normalization.
  calc
    (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i - z.center‖ ^ (2 : ℕ)) ≤
        ∑ i : Fin 4, l i * z.radiusSq := Finset.sum_le_sum fun i _ ↦ hLe i
    _ = (∑ i : Fin 4, l i) * z.radiusSq := by
      rw [← Finset.sum_mul]
    _ = z.radiusSq := by
      rw [stdSimplex.sum_eq_one l, one_mul]

/-- Helper for Chapter09 Exercise 9.6: every simplex multiplier has dual value at most the
squared radius of every primal-feasible circle. -/
theorem chapter09Exercise96DualObjective_le_radiusSq_of_memPrimalFeasibleSet
    {z : Chapter09Exercise96PrimalPoint} (hz : z ∈ chapter09Exercise96PrimalFeasibleSet)
    (l : stdSimplex ℝ (Fin 4)) :
    chapter09Exercise96DualObjective l ≤ z.radiusSq := by
  have hNonneg :
      0 ≤ ‖chapter09Exercise96DualBarycenter l - z.center‖ ^ (2 : ℕ) := by
    exact sq_nonneg ‖chapter09Exercise96DualBarycenter l - z.center‖
  -- Weak duality is the structural identity plus the weighted feasible bound.
  calc
    chapter09Exercise96DualObjective l ≤
        chapter09Exercise96DualObjective l +
          ‖chapter09Exercise96DualBarycenter l - z.center‖ ^ (2 : ℕ) := by
      nlinarith
    _ = (∑ i : Fin 4, l i * ‖chapter09Exercise96Points i - z.center‖ ^ (2 : ℕ)) := by
      symm
      exact chapter09Exercise96WeightedDistSq_eq_dualObjective_add_barycenterDistSq l z.center
    _ ≤ z.radiusSq :=
      chapter09Exercise96WeightedDistSq_le_radiusSq_of_memPrimalFeasibleSet hz l

/-- Chapter09 Exercise 9.6 (1): the smallest-circle problem is formulated as the convex program
minimizing `chapter09Exercise96PrimalObjective` over
`chapter09Exercise96PrimalFeasibleSet`, and the optimizer is the center-radius pair
`chapter09Exercise96PrimalOptimizer`. -/
theorem chapter09Exercise96PrimalIsMinOn :
    IsMinOn
      chapter09Exercise96PrimalObjective
      chapter09Exercise96PrimalFeasibleSet
      chapter09Exercise96PrimalOptimizer := by
  rw [isMinOn_iff]
  intro z hz
  -- Compare every feasible primal point with the explicit dual optimizer via weak duality.
  calc
    chapter09Exercise96PrimalObjective chapter09Exercise96PrimalOptimizer = 25 :=
      chapter09Exercise96PrimalObjective_primalOptimizer
    _ = chapter09Exercise96DualObjective chapter09Exercise96DualOptimizer := by
      symm
      exact chapter09Exercise96DualObjective_dualOptimizer
    _ ≤ z.radiusSq :=
      chapter09Exercise96DualObjective_le_radiusSq_of_memPrimalFeasibleSet hz
        chapter09Exercise96DualOptimizer
    _ = chapter09Exercise96PrimalObjective z := by
      rfl

/-- Chapter09 Exercise 9.6 (2): the explicit dual problem is solved by the multiplier vector
`chapter09Exercise96DualOptimizer`. -/
theorem chapter09Exercise96DualIsMaxOn :
    IsMaxOn
      chapter09Exercise96DualObjective
      (stdSimplex ℝ (Fin 4))
      chapter09Exercise96DualOptimizer := by
  rw [isMaxOn_iff]
  intro l hl
  -- Route correction: use the primal optimizer and weak duality, rather than recomputing the
  -- dual quadratic directly for every feasible multiplier.
  calc
    chapter09Exercise96DualObjective l ≤
        chapter09Exercise96PrimalObjective chapter09Exercise96PrimalOptimizer := by
      change chapter09Exercise96DualObjective
          (↑(⟨l, hl⟩ : stdSimplex ℝ (Fin 4)) : DualPoint) ≤
            chapter09Exercise96PrimalObjective chapter09Exercise96PrimalOptimizer
      simpa only [chapter09Exercise96PrimalObjective_eq] using
        chapter09Exercise96DualObjective_le_radiusSq_of_memPrimalFeasibleSet
          chapter09Exercise96PrimalOptimizer_mem_primalFeasibleSet
          (⟨l, hl⟩ : stdSimplex ℝ (Fin 4))
    _ = 25 := chapter09Exercise96PrimalObjective_primalOptimizer
    _ = chapter09Exercise96DualObjective chapter09Exercise96DualOptimizer := by
      symm
      exact chapter09Exercise96DualObjective_dualOptimizer

/-- Chapter09 Exercise 9.6 (3): the optimal value of the primal convex program is `25`, so the
smallest enclosing circle has radius `5`. -/
theorem chapter09Exercise96PrimalOptimalValue :
    chapter09Exercise96PrimalObjective chapter09Exercise96PrimalOptimizer = 25 :=
  chapter09Exercise96PrimalObjective_primalOptimizer

/-- Chapter09 Exercise 9.6 (4): the optimal value of the solved dual problem is also `25`. -/
theorem chapter09Exercise96DualOptimalValue :
    chapter09Exercise96DualObjective chapter09Exercise96DualOptimizer = 25 :=
  chapter09Exercise96DualObjective_dualOptimizer

end
