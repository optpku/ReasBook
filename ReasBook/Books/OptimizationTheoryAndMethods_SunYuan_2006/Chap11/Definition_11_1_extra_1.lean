/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_1

noncomputable section

section Chapter11Definition111Extra1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling:
-- * primary domain: first-order constrained optimization in a real Hilbert space
-- * owner abstractions inspected:
--   `IsFeasibleDirectionAt`, `feasibleDirections`, `descentDirections`,
--   `IsDescentDirectionAt`
-- * source-facing layer here: the combined notion of a feasible descent direction
-- * primitive data: feasible-direction data from Chapter 8 and descent-direction data from
--   Chapter 1
-- * derived API: feasibility of the base point, differentiability, and the set-valued view

/-- `IsFeasibleDescentDirection f xk X d` records that `d` is
a feasible direction of `X` at `xk` and a strict descent direction for `f` at `xk`. -/
class IsFeasibleDescentDirection
    (f : E → ℝ) (xk : E) (X : Set E) (d : E) : Prop
    extends IsFeasibleDirectionAt X xk d where
  isDescentDirectionAt : IsDescentDirectionAt f xk d

/-- `IsFeasibleDescentDirection f xk X d` is a proposition. -/
instance instSubsingletonIsFeasibleDescentDirection
    (f : E → ℝ) (xk d : E) (X : Set E) :
    Subsingleton (IsFeasibleDescentDirection f xk X d) :=
  inferInstance

/-- A feasible descent direction is based at a feasible point. -/
theorem IsFeasibleDescentDirection.mem_base
    {f : E → ℝ} {xk d : E} {X : Set E}
    (h : IsFeasibleDescentDirection f xk X d) :
    xk ∈ X :=
  h.toIsFeasibleDirectionAt.mem

/-- A feasible descent direction is automatically a point of differentiability. -/
theorem IsFeasibleDescentDirection.differentiableAt
    {f : E → ℝ} {xk d : E} {X : Set E}
    (h : IsFeasibleDescentDirection f xk X d) :
    DifferentiableAt ℝ f xk :=
  h.isDescentDirectionAt.differentiableAt

/-- A feasible descent direction has negative gradient pairing. -/
theorem IsFeasibleDescentDirection.descent
    {f : E → ℝ} {xk d : E} {X : Set E}
    (h : IsFeasibleDescentDirection f xk X d) :
    inner ℝ d (gradient f xk) < 0 := by
  simpa [real_inner_comm] using h.isDescentDirectionAt.inner_gradient_neg

/-- `IsFeasibleDescentDirection` is exactly the conjunction of the Chapter 8 feasible-direction
owner and the Chapter 1 descent-direction owner. -/
theorem isFeasibleDescentDirection_iff_feasible_and_descent
    (f : E → ℝ) (xk d : E) (X : Set E) :
    IsFeasibleDescentDirection f xk X d ↔
      IsFeasibleDirectionAt X xk d ∧ IsDescentDirectionAt f xk d := by
  constructor
  · intro h
    exact ⟨h.toIsFeasibleDirectionAt, h.isDescentDirectionAt⟩
  · rintro ⟨hfeasible, hdescent⟩
    exact
      { toIsFeasibleDirectionAt := hfeasible
        isDescentDirectionAt := hdescent }

/-- Unfolding formula for `IsFeasibleDescentDirection`. -/
theorem isFeasibleDescentDirection_iff
    (f : E → ℝ) (xk d : E) (X : Set E) :
    IsFeasibleDescentDirection f xk X d ↔
      d ≠ 0 ∧
        (∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) δ, xk + t • d ∈ X) ∧
          inner ℝ d (gradient f xk) < 0 := by
  rw [isFeasibleDescentDirection_iff_feasible_and_descent, isFeasibleDirectionAt_iff,
    isDescentDirectionAt_iff]
  constructor
  · rintro ⟨hfeasible, hdescent⟩
    exact ⟨hfeasible.1, hfeasible.2, by simpa [real_inner_comm] using hdescent⟩
  · rintro ⟨hne, hsmall_segment_mem, hdescent⟩
    exact ⟨⟨hne, hsmall_segment_mem⟩, by simpa [real_inner_comm] using hdescent⟩

/-- `feasibleDescentDirections f xk X` is the set of feasible descent directions of `f` at the
feasible iterate `xk`. -/
def feasibleDescentDirections (f : E → ℝ) (xk : E) (X : Set E) : Set E :=
  feasibleDirections xk X ∩ descentDirections f xk

/-- Membership in `feasibleDescentDirections f xk X` is exactly the Chapter 11 feasible-descent
predicate. -/
theorem mem_feasibleDescentDirections_iff
    (f : E → ℝ) (xk d : E) (X : Set E) :
    d ∈ feasibleDescentDirections f xk X ↔
      IsFeasibleDescentDirection f xk X d := by
  rw [feasibleDescentDirections, Set.mem_inter_iff, mem_feasibleDirections_iff,
    isFeasibleDescentDirection_iff_feasible_and_descent, mem_descentDirections_iff,
    isDescentDirectionAt_iff]
  constructor
  · rintro ⟨hfeasible, hdescent⟩
    exact ⟨hfeasible, by simpa [real_inner_comm] using hdescent⟩
  · rintro ⟨hfeasible, hdescent⟩
    exact ⟨hfeasible, by simpa [real_inner_comm] using hdescent⟩

/-- Chapter11 Definition 11.1-extra-1: a feasible descent direction yields a positive feasible
step with strictly smaller objective
value. -/
theorem IsFeasibleDescentDirection.exists_feasible_improving_step
    {f : E → ℝ} {xk d : E} {X : Set E}
    (hd : IsFeasibleDescentDirection f xk X d) :
    ∃ α : ℝ, α > 0 ∧ xk + α • d ∈ X ∧ f (xk + α • d) < f xk := by
  -- Extract the feasible-step radius and the strict-decrease radius from the two owners.
  rcases hd.toIsFeasibleDirectionAt.small_segment_mem with ⟨δF, hδF, hfeasible⟩
  rcases hd.isDescentDirectionAt.exists_localDecrease with ⟨δD, hδD, hdecrease⟩
  -- Use one half-sized step that lies inside both positive radii.
  let α : ℝ := min δF δD / 2
  have hmin_pos : 0 < min δF δD := by
    exact lt_min hδF hδD
  have hα_pos : 0 < α := by
    simpa [α] using div_pos hmin_pos (show (0 : ℝ) < 2 by norm_num)
  have hα_lt_min : α < min δF δD := by
    simpa [α] using half_lt_self hmin_pos
  have hα_mem : α ∈ Set.Icc (0 : ℝ) δF := by
    -- The common step stays inside the feasible interval `[0, δF]`.
    refine ⟨le_of_lt hα_pos, ?_⟩
    exact le_trans hα_lt_min.le (min_le_left _ _)
  have hα_lt_δD : α < δD := by
    -- The same step also stays strictly inside the decrease interval `(0, δD)`.
    exact lt_of_lt_of_le hα_lt_min (min_le_right _ _)
  refine ⟨α, hα_pos, ?_, ?_⟩
  · -- Apply the feasible-ray witness at the common step.
    exact hfeasible α hα_mem
  · -- Apply the local-decrease witness at the same step.
    exact hdecrease α hα_pos hα_lt_δD

/-- A feasible descent direction yields a positive feasible step with strictly smaller objective
value. -/
theorem exists_feasible_improving_step_of_mem_feasibleDescentDirections
    (f : E → ℝ) {xk d : E} {X : Set E}
    (hd : d ∈ feasibleDescentDirections f xk X) :
    ∃ α : ℝ, α > 0 ∧ xk + α • d ∈ X ∧ f (xk + α • d) < f xk :=
  (mem_feasibleDescentDirections_iff f xk d X).mp hd |>.exists_feasible_improving_step

#print axioms feasibleDescentDirections

end Chapter11Definition111Extra1
