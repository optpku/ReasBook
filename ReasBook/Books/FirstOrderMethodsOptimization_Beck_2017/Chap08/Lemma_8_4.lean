/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Lemma 8.4 is `source-facing` in the chapter's constrained maximization API. The relevant owner
abstractions are mathlib's `ConcaveOn`, `ConvexOn`, and `IsMaxOn`. Since `IsMaxOn` does not encode
feasibility of the maximizer, the only local helper introduced here is the optimal-solution set of
feasible maximizers on a given constraint set. -/

/-- The optimal solution set of maximizing `g` over the feasible region `s`. -/
def optimalSolutionSet (g : E → ℝ) (s : Set E) : Set E :=
  {y | y ∈ s ∧ IsMaxOn g s y}

/-- The feasible region cut out by the single constraint `f1 ≤ 0`. -/
def oneConstraintFeasibleRegion (f1 : E → ℝ) : Set E :=
  {y | f1 y ≤ 0}

/-- The feasible region cut out by the two constraints `f1 ≤ 0` and `f2 ≤ 0`. -/
def twoConstraintFeasibleRegion (f1 f2 : E → ℝ) : Set E :=
  {y | f1 y ≤ 0 ∧ f2 y ≤ 0}

/-- The boundary slice of the `f1 ≤ 0` feasible region where `f2 = 0`. -/
def boundaryConstraintFeasibleRegion (f1 f2 : E → ℝ) : Set E :=
  {y | f1 y ≤ 0 ∧ f2 y = 0}

-- Proof sketch: unfold `optimalSolutionSet`; membership is exactly feasibility together with the
-- owner predicate `IsMaxOn` on the same feasible region.
/-- A point belongs to `optimalSolutionSet g s` exactly when it is feasible for `s` and maximizes
`g` on `s`. -/
@[simp] theorem mem_optimalSolutionSet {g : E → ℝ} {s : Set E} {y : E} :
    y ∈ optimalSolutionSet g s ↔ y ∈ s ∧ IsMaxOn g s y := by
  rfl

/-- The alternative that the unique one-constraint maximizer remains the unique
two-constraint maximizer. -/
def optimalSolutionSetSingletonCase (g f1 f2 : E → ℝ) (yTilde : E) : Prop :=
  f2 yTilde ≤ 0 ∧ optimalSolutionSet g (twoConstraintFeasibleRegion f1 f2) = {yTilde}

/-- The alternative that the two-constraint optimal set is exactly the boundary-constrained
maximizer set. -/
def optimalSolutionSetBoundaryCase (g f1 f2 : E → ℝ) (yTilde : E) : Prop :=
  0 < f2 yTilde ∧
    optimalSolutionSet g (twoConstraintFeasibleRegion f1 f2) =
      optimalSolutionSet g (boundaryConstraintFeasibleRegion f1 f2)

/-- Helper for Lemma 8.4: a feasible point with `f2 < 0` can be improved by moving along the
segment to the unique one-constraint maximizer until the boundary `f2 = 0` is reached. -/
lemma exists_boundary_point_gt_of_mem_twoConstraint_of_f2_lt_zero
    (g f1 f2 : E → ℝ) (hg_concave : ConcaveOn ℝ Set.univ g)
    (hf1_convex : ConvexOn ℝ Set.univ f1) (hf2_convex : ConvexOn ℝ Set.univ f2)
    (yTilde : E)
    (hyTilde :
      optimalSolutionSet g (oneConstraintFeasibleRegion f1) = {yTilde})
    {y : E} (hy : y ∈ twoConstraintFeasibleRegion f1 f2)
    (hy_f2_lt : f2 y < 0) (hyTilde_f2_pos : 0 < f2 yTilde) :
    ∃ z, z ∈ boundaryConstraintFeasibleRegion f1 f2 ∧ g y < g z := by
  have hyTilde_mem : yTilde ∈ optimalSolutionSet g (oneConstraintFeasibleRegion f1) := by
    rw [hyTilde]
    simp
  have hyTilde_feasible : yTilde ∈ oneConstraintFeasibleRegion f1 :=
    (mem_optimalSolutionSet.mp hyTilde_mem).1
  have hyTilde_isMax : IsMaxOn g (oneConstraintFeasibleRegion f1) yTilde :=
    (mem_optimalSolutionSet.mp hyTilde_mem).2
  have hyTilde_unique :
      ∀ {x : E},
        x ∈ oneConstraintFeasibleRegion f1 →
          IsMaxOn g (oneConstraintFeasibleRegion f1) x → x = yTilde := by
    intro x hx hx_isMax
    have hx_mem : x ∈ optimalSolutionSet g (oneConstraintFeasibleRegion f1) :=
      mem_optimalSolutionSet.mpr ⟨hx, hx_isMax⟩
    rw [hyTilde] at hx_mem
    simpa using hx_mem
  have hy_lt_yTilde : g y < g yTilde := by
    have hy_le_yTilde : g y ≤ g yTilde := (isMaxOn_iff.mp hyTilde_isMax) y hy.1
    have hy_ne_yTilde : y ≠ yTilde := by
      intro hEq
      have : f2 yTilde < 0 := by simpa [hEq] using hy_f2_lt
      exact not_lt_of_ge hyTilde_f2_pos.le this
    have hy_eq_imp : g y = g yTilde → False := by
      intro hEq
      have hy_isMax : IsMaxOn g (oneConstraintFeasibleRegion f1) y := by
        rw [isMaxOn_iff]
        intro x hx
        have hx_le : g x ≤ g yTilde := (isMaxOn_iff.mp hyTilde_isMax) x hx
        simpa [hEq] using hx_le
      exact hy_ne_yTilde (hyTilde_unique hy.1 hy_isMax)
    exact lt_of_le_of_ne hy_le_yTilde fun hEq ↦ hy_eq_imp hEq
  let φ : ℝ → ℝ := fun t ↦ f2 (AffineMap.lineMap y yTilde t)
  have hφ_convex : ConvexOn ℝ Set.univ φ := by
    simpa [φ, Function.comp_def] using
      (hf2_convex.comp_affineMap (AffineMap.lineMap y yTilde))
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    exact (hφ_convex.continuousOn isOpen_univ).mono fun _ _ ↦ by simp
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (φ 0) (φ 1) := by
    constructor
    · simpa [φ] using hy_f2_lt.le
    · simpa [φ] using hyTilde_f2_pos.le
  obtain ⟨t0, ht0_mem, ht0_zero⟩ :=
    (intermediate_value_Icc (a := (0 : ℝ)) (b := 1) zero_le_one hφ_cont) hzero_mem
  have ht0_ne_zero : t0 ≠ 0 := by
    intro ht0_eq
    have : f2 y = 0 := by simpa [φ, ht0_eq] using ht0_zero
    exact hy_f2_lt.ne this
  have ht0_ne_one : t0 ≠ 1 := by
    intro ht0_eq
    have : f2 yTilde = 0 := by simpa [φ, ht0_eq] using ht0_zero
    exact hyTilde_f2_pos.ne' this
  have ht0_pos : 0 < t0 := lt_of_le_of_ne ht0_mem.1 ht0_ne_zero.symm
  have ht0_lt_one : t0 < 1 := lt_of_le_of_ne ht0_mem.2 ht0_ne_one
  let z : E := AffineMap.lineMap y yTilde t0
  have hz_f1_le :
      f1 z ≤ (1 - t0) * f1 y + t0 * f1 yTilde := by
    -- Convexity keeps the segment inside the `f1 ≤ 0` feasible region.
    simpa [z, AffineMap.lineMap_apply_module] using
      (hf1_convex.2 (by simp : y ∈ Set.univ) (by simp : yTilde ∈ Set.univ)
        (sub_nonneg.mpr ht0_mem.2) ht0_mem.1 (by ring))
  have hz_f1 : f1 z ≤ 0 := by
    have hleft_nonpos : (1 - t0) * f1 y ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht0_mem.2) hy.1
    have hright_nonpos : t0 * f1 yTilde ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos ht0_mem.1 hyTilde_feasible
    have hcomb_nonpos : (1 - t0) * f1 y + t0 * f1 yTilde ≤ 0 := by
      linarith
    exact hz_f1_le.trans hcomb_nonpos
  have hz_f2 : f2 z = 0 := by
    -- The intermediate-value step chooses the exact boundary crossing.
    simpa [z, φ] using ht0_zero
  have hz_g_ge :
      (1 - t0) * g y + t0 * g yTilde ≤ g z := by
    -- Concavity turns the strict improvement at `yTilde` into a better boundary point.
    simpa [z, AffineMap.lineMap_apply_module] using
      (hg_concave.2 (by simp : y ∈ Set.univ) (by simp : yTilde ∈ Set.univ)
        (sub_nonneg.mpr ht0_mem.2) ht0_mem.1 (by ring))
  have hy_lt_comb : g y < (1 - t0) * g y + t0 * g yTilde := by
    have hmul_pos : 0 < t0 * (g yTilde - g y) := by
      exact mul_pos ht0_pos (sub_pos.mpr hy_lt_yTilde)
    have hy_lt_shifted : g y < g y + t0 * (g yTilde - g y) := by
      linarith
    have hrewrite : g y + t0 * (g yTilde - g y) = (1 - t0) * g y + t0 * g yTilde := by
      ring
    simpa [hrewrite] using hy_lt_shifted
  refine ⟨z, ⟨hz_f1, hz_f2⟩, ?_⟩
  exact lt_of_lt_of_le hy_lt_comb hz_g_ge

-- Proof sketch: use the one-constraint optimal-set equality
-- `optimalSolutionSet g (oneConstraintFeasibleRegion f1) = {yTilde}` to encode the uniqueness
-- hypothesis. If `f2 yTilde ≤ 0`, then the unique maximizer for the larger feasible set is
-- already feasible for the two-constraint problem, so the optimal set stays `{yTilde}`. If
-- `0 < f2 yTilde`, convexity of the feasible region cut out by `f1` and concavity of `g` force
-- every two-constraint optimizer onto the boundary `f2 = 0`, hence the optimal set agrees with
-- the boundary-constrained maximizer set. The order trichotomy on `f2 yTilde` makes the two
-- alternatives exclusive and exhaustive, yielding `Xor'`.
/-- Lemma 8.4: if the maximization problem with only the constraint `f1 ≤ 0` has unique optimal
solution `yTilde`, then exactly one of the following holds for the two-constraint problem:
(i) `f2 yTilde ≤ 0` and the optimal solution set is `{yTilde}`;
(ii) `0 < f2 yTilde` and the optimal solution set is the maximizer set on the boundary
`f2 = 0`. -/
theorem optimalSolutionSet_xor_singleton_or_boundary_of_unique_one_constraint_solution
    (g f1 f2 : E → ℝ) (hg_concave : ConcaveOn ℝ Set.univ g)
    (hf1_convex : ConvexOn ℝ Set.univ f1) (hf2_convex : ConvexOn ℝ Set.univ f2)
    (yTilde : E)
    (hyTilde :
      optimalSolutionSet g (oneConstraintFeasibleRegion f1) = {yTilde}) :
    Xor'
      (optimalSolutionSetSingletonCase g f1 f2 yTilde)
      (optimalSolutionSetBoundaryCase g f1 f2 yTilde) := by
  have hyTilde_mem : yTilde ∈ optimalSolutionSet g (oneConstraintFeasibleRegion f1) := by
    rw [hyTilde]
    simp
  have hyTilde_feasible : yTilde ∈ oneConstraintFeasibleRegion f1 :=
    (mem_optimalSolutionSet.mp hyTilde_mem).1
  have hyTilde_isMax : IsMaxOn g (oneConstraintFeasibleRegion f1) yTilde :=
    (mem_optimalSolutionSet.mp hyTilde_mem).2
  have hyTilde_unique :
      ∀ {y : E},
        y ∈ oneConstraintFeasibleRegion f1 →
          IsMaxOn g (oneConstraintFeasibleRegion f1) y → y = yTilde := by
    intro y hy hy_isMax
    have hy_mem : y ∈ optimalSolutionSet g (oneConstraintFeasibleRegion f1) :=
      mem_optimalSolutionSet.mpr ⟨hy, hy_isMax⟩
    rw [hyTilde] at hy_mem
    simpa using hy_mem
  by_cases hyTilde_f2_nonpos : f2 yTilde ≤ 0
  · have hsingleton :
        optimalSolutionSetSingletonCase g f1 f2 yTilde := by
      refine ⟨hyTilde_f2_nonpos, ?_⟩
      apply Set.Subset.antisymm
      · intro y hy
        have hy_feasible : y ∈ twoConstraintFeasibleRegion f1 f2 :=
          (mem_optimalSolutionSet.mp hy).1
        have hy_isMaxTwo : IsMaxOn g (twoConstraintFeasibleRegion f1 f2) y :=
          (mem_optimalSolutionSet.mp hy).2
        have hy_le_yTilde : g y ≤ g yTilde := (isMaxOn_iff.mp hyTilde_isMax) y hy_feasible.1
        have hyTilde_feasible_two : yTilde ∈ twoConstraintFeasibleRegion f1 f2 :=
          ⟨hyTilde_feasible, hyTilde_f2_nonpos⟩
        have hyTilde_le_y : g yTilde ≤ g y := (isMaxOn_iff.mp hy_isMaxTwo) yTilde hyTilde_feasible_two
        have hgy_eq : g y = g yTilde := le_antisymm hy_le_yTilde hyTilde_le_y
        have hy_isMaxOne : IsMaxOn g (oneConstraintFeasibleRegion f1) y := by
          -- Equality of objective values upgrades the two-constraint optimizer to the
          -- one-constraint maximizer characterized by `hyTilde`.
          rw [isMaxOn_iff]
          intro x hx
          have hx_le : g x ≤ g yTilde := (isMaxOn_iff.mp hyTilde_isMax) x hx
          simpa [hgy_eq] using hx_le
        have hy_eq : y = yTilde := hyTilde_unique hy_feasible.1 hy_isMaxOne
        simp [hy_eq]
      · intro y hy
        have hy_eq : y = yTilde := by simpa using hy
        subst y
        have hyTilde_feasible_two : yTilde ∈ twoConstraintFeasibleRegion f1 f2 :=
          ⟨hyTilde_feasible, hyTilde_f2_nonpos⟩
        apply mem_optimalSolutionSet.mpr
        refine ⟨hyTilde_feasible_two, ?_⟩
        -- Any two-constraint feasible point is also feasible for the one-constraint problem.
        rw [isMaxOn_iff]
        intro x hx
        exact (isMaxOn_iff.mp hyTilde_isMax) x hx.1
    exact Or.inl ⟨hsingleton, fun hboundary ↦ not_lt_of_ge hyTilde_f2_nonpos hboundary.1⟩
  · have hyTilde_f2_pos : 0 < f2 yTilde := lt_of_not_ge hyTilde_f2_nonpos
    have hboundary :
        optimalSolutionSetBoundaryCase g f1 f2 yTilde := by
      refine ⟨hyTilde_f2_pos, ?_⟩
      apply Set.Subset.antisymm
      · intro y hy
        have hy_feasible : y ∈ twoConstraintFeasibleRegion f1 f2 :=
          (mem_optimalSolutionSet.mp hy).1
        have hy_isMaxTwo : IsMaxOn g (twoConstraintFeasibleRegion f1 f2) y :=
          (mem_optimalSolutionSet.mp hy).2
        have hy_f2_eq_zero : f2 y = 0 := by
          by_contra hy_f2_ne_zero
          have hy_f2_lt : f2 y < 0 := lt_of_le_of_ne hy_feasible.2 hy_f2_ne_zero
          obtain ⟨z, hz_boundary, hy_lt_z⟩ :=
            exists_boundary_point_gt_of_mem_twoConstraint_of_f2_lt_zero
              g f1 f2 hg_concave hf1_convex hf2_convex yTilde hyTilde
              hy_feasible hy_f2_lt hyTilde_f2_pos
          have hz_feasible : z ∈ twoConstraintFeasibleRegion f1 f2 := ⟨hz_boundary.1, hz_boundary.2.le⟩
          exact not_lt_of_ge ((isMaxOn_iff.mp hy_isMaxTwo) z hz_feasible) hy_lt_z
        apply mem_optimalSolutionSet.mpr
        refine ⟨⟨hy_feasible.1, hy_f2_eq_zero⟩, ?_⟩
        -- Once every optimizer is forced onto `f2 = 0`, optimality restricts to the boundary.
        rw [isMaxOn_iff]
        intro z hz
        exact (isMaxOn_iff.mp hy_isMaxTwo) z ⟨hz.1, hz.2.le⟩
      · intro y hy
        have hy_boundary : y ∈ boundaryConstraintFeasibleRegion f1 f2 :=
          (mem_optimalSolutionSet.mp hy).1
        have hy_isMaxBoundary : IsMaxOn g (boundaryConstraintFeasibleRegion f1 f2) y :=
          (mem_optimalSolutionSet.mp hy).2
        apply mem_optimalSolutionSet.mpr
        refine ⟨⟨hy_boundary.1, hy_boundary.2.le⟩, ?_⟩
        -- Compare any two-constraint feasible point to a boundary maximizer by either staying
        -- on the boundary or improving to it along the source-proof segment.
        rw [isMaxOn_iff]
        intro x hx
        by_cases hx_f2_eq_zero : f2 x = 0
        · exact (isMaxOn_iff.mp hy_isMaxBoundary) x ⟨hx.1, hx_f2_eq_zero⟩
        · have hx_f2_lt : f2 x < 0 := lt_of_le_of_ne hx.2 hx_f2_eq_zero
          obtain ⟨z, hz_boundary, hx_lt_z⟩ :=
            exists_boundary_point_gt_of_mem_twoConstraint_of_f2_lt_zero
              g f1 f2 hg_concave hf1_convex hf2_convex yTilde hyTilde
              hx hx_f2_lt hyTilde_f2_pos
          exact (lt_of_lt_of_le hx_lt_z ((isMaxOn_iff.mp hy_isMaxBoundary) z hz_boundary)).le
    exact Or.inr ⟨hboundary, fun hsingleton ↦ not_lt_of_ge hsingleton.1 hyTilde_f2_pos⟩

end
