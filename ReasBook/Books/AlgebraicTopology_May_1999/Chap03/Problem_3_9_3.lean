/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

/-- The branching interval obtained from countably many copies of `(0,1]` and a single point over
`0`. -/
abbrev BranchingInterval : Type :=
  { z : Set.Icc (0 : ℝ) 1 × ℕ // ((z.1 : ℝ) = 0 → z.2 = 0) }

/-- Problem 3.9.3: the projection from the branching interval onto the closed unit interval is the
standard example of a surjective local homeomorphism that fails to be a covering map. -/
def branchingIntervalProjection : BranchingInterval → Set.Icc (0 : ℝ) 1 :=
  fun z ↦ z.1.1

/-- Helper for Problem 3.9.3: the distinguished point `0` of the closed unit interval. -/
def zero_base : Set.Icc (0 : ℝ) 1 :=
  ⟨0, ⟨le_rfl, zero_le_one⟩⟩

/-- Helper for Problem 3.9.3: the `0`th branch exists above every base point. -/
def zero_branch_point (x : Set.Icc (0 : ℝ) 1) : BranchingInterval :=
  ⟨⟨x, 0⟩, fun _ ↦ rfl⟩

/-- Helper for Problem 3.9.3: the positive part of the closed unit interval. -/
def positive_base_slice : Set (Set.Icc (0 : ℝ) 1) :=
  { x | 0 < (x : ℝ) }

/-- Helper for Problem 3.9.3: the fixed `n`th branch above the positive part of the base. -/
def positive_branch_slice (n : ℕ) : Set BranchingInterval :=
  { z | 0 < (branchingIntervalProjection z : ℝ) ∧ z.1.2 = n }

/-- Helper for Problem 3.9.3: a small neighborhood of `0` in the base interval. -/
def zero_base_slice : Set (Set.Icc (0 : ℝ) 1) :=
  { x | (x : ℝ) < (1 / 2 : ℝ) }

/-- Helper for Problem 3.9.3: the `0`th branch above the small neighborhood of `0`. -/
def zero_branch_slice : Set BranchingInterval :=
  { z | (branchingIntervalProjection z : ℝ) < (1 / 2 : ℝ) ∧ z.1.2 = 0 }

/-- Helper for Problem 3.9.3: a positive base point supports every branch index. -/
theorem positive_base_supports_branch (n : ℕ) {x : Set.Icc (0 : ℝ) 1}
    (hx : 0 < (x : ℝ)) : ((x : ℝ) = 0 → n = 0) := by
  -- A positive base point cannot satisfy the branch-collapsing condition at `0`.
  intro hx0
  linarith

/-- Helper for Problem 3.9.3: reinserting a positive base point into a chosen branch. -/
def positive_branch_point (n : ℕ)
    (x : { x : Set.Icc (0 : ℝ) 1 | x ∈ positive_base_slice }) : BranchingInterval :=
  ⟨⟨x.1, n⟩, positive_base_supports_branch n x.2⟩

/-- Helper for Problem 3.9.3: the branching projection is continuous. -/
theorem continuous_branchingIntervalProjection : Continuous branchingIntervalProjection := by
  change Continuous (fun z : BranchingInterval ↦ z.1.1)
  fun_prop

/-- Helper for Problem 3.9.3: the branch index is a continuous map to the discrete space `ℕ`. -/
theorem continuous_branch_index : Continuous fun z : BranchingInterval ↦ z.1.2 := by
  fun_prop

/-- Helper for Problem 3.9.3: the positive base slice is open in the closed interval. -/
theorem isOpen_positive_base_slice : IsOpen positive_base_slice := by
  simpa [positive_base_slice] using isOpen_lt continuous_const continuous_subtype_val

/-- Helper for Problem 3.9.3: the small neighborhood of `0` is open in the closed interval. -/
theorem isOpen_zero_base_slice : IsOpen zero_base_slice := by
  simpa [zero_base_slice] using isOpen_lt continuous_subtype_val continuous_const

/-- Helper for Problem 3.9.3: each positive branch slice is open in the branching interval. -/
theorem isOpen_positive_branch_slice (n : ℕ) : IsOpen (positive_branch_slice n) := by
  have hpos : IsOpen { z : BranchingInterval | 0 < (branchingIntervalProjection z : ℝ) } := by
    simpa [positive_base_slice] using
      isOpen_positive_base_slice.preimage continuous_branchingIntervalProjection
  have hbranch : IsOpen { z : BranchingInterval | z.1.2 = n } := by
    simpa using (isOpen_discrete ({n} : Set ℕ)).preimage continuous_branch_index
  simpa [positive_branch_slice, Set.setOf_and] using hpos.inter hbranch

/-- Helper for Problem 3.9.3: the zero-branch neighborhood is open in the branching interval. -/
theorem isOpen_zero_branch_slice : IsOpen zero_branch_slice := by
  have hsmall :
      IsOpen { z : BranchingInterval | (branchingIntervalProjection z : ℝ) < (1 / 2 : ℝ) } := by
    simpa [zero_base_slice] using
      isOpen_zero_base_slice.preimage continuous_branchingIntervalProjection
  have hbranch : IsOpen { z : BranchingInterval | z.1.2 = 0 } := by
    simpa using (isOpen_discrete ({0} : Set ℕ)).preimage continuous_branch_index
  simpa [zero_branch_slice, Set.setOf_and] using hsmall.inter hbranch

/-- Helper for Problem 3.9.3: on a fixed positive branch, the projection is an open embedding. -/
theorem positive_branch_slice_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding ((positive_branch_slice n).restrict branchingIntervalProjection) := by
  let e : { z : BranchingInterval | z ∈ positive_branch_slice n } ≃ₜ
      { x : Set.Icc (0 : ℝ) 1 | x ∈ positive_base_slice } :=
    { toEquiv :=
        { toFun := fun z ↦ ⟨branchingIntervalProjection z.1, z.2.1⟩
          invFun := fun x ↦
            ⟨positive_branch_point n x, ⟨x.2, rfl⟩⟩
          left_inv := by
            -- Reinsert the same base point into the same branch.
            rintro ⟨z, hz⟩
            apply Subtype.ext
            apply Subtype.ext
            rcases z with ⟨⟨x, m⟩, hz0⟩
            exact Prod.ext rfl hz.2.symm
          right_inv := by
            -- Forgetting and then reinserting the branch does nothing on the base slice.
            intro x
            apply Subtype.ext
            rfl }
      continuous_toFun := by
        -- The forward map just forgets the fixed branch coordinate.
        exact Continuous.subtype_mk
          (by
            change Continuous
              (fun z : { z : BranchingInterval | z ∈ positive_branch_slice n } ↦ z.1.1.1)
            fun_prop)
          (fun z ↦ z.2.1)
      continuous_invFun := by
        -- The inverse continuously reinserts the constant branch index.
        exact Continuous.subtype_mk
          (Continuous.subtype_mk
            (by
              fun_prop)
            (fun x ↦ positive_base_supports_branch n x.2))
          (fun x ↦ ⟨x.2, rfl⟩) }
  -- Compose the branchwise homeomorphism with the open inclusion of the positive base slice.
  simpa [e] using
    (isOpen_positive_base_slice.isOpenEmbedding_subtypeVal).comp e.isOpenEmbedding

/-- Helper for Problem 3.9.3: near `0`, the zero branch projects by an open embedding. -/
theorem zero_branch_slice_isOpenEmbedding :
    Topology.IsOpenEmbedding (zero_branch_slice.restrict branchingIntervalProjection) := by
  let e : { z : BranchingInterval | z ∈ zero_branch_slice } ≃ₜ
      { x : Set.Icc (0 : ℝ) 1 | x ∈ zero_base_slice } :=
    { toEquiv :=
        { toFun := fun z ↦ ⟨branchingIntervalProjection z.1, z.2.1⟩
          invFun := fun x ↦
            ⟨zero_branch_point x.1, ⟨x.2, rfl⟩⟩
          left_inv := by
            -- Over this neighborhood the branch index is forced to be `0`.
            rintro ⟨z, hz⟩
            apply Subtype.ext
            apply Subtype.ext
            rcases z with ⟨⟨x, m⟩, hz0⟩
            exact Prod.ext rfl hz.2.symm
          right_inv := by
            -- Forgetting and then reinserting the zero branch fixes the base point.
            intro x
            apply Subtype.ext
            rfl }
      continuous_toFun := by
        -- The forward map again forgets the branch coordinate.
        exact Continuous.subtype_mk
          (by
            change Continuous (fun z : { z : BranchingInterval | z ∈ zero_branch_slice } ↦ z.1.1.1)
            fun_prop)
          (fun z ↦ z.2.1)
      continuous_invFun := by
        -- The inverse continuously inserts the constant zero branch.
        exact Continuous.subtype_mk
          (Continuous.subtype_mk
            (by
              fun_prop)
            (fun _ ↦ fun _ ↦ rfl))
          (fun x ↦ ⟨x.2, rfl⟩) }
  -- The chart identifies the zero branch neighborhood with an open base neighborhood.
  simpa [e] using
    (isOpen_zero_base_slice.isOpenEmbedding_subtypeVal).comp e.isOpenEmbedding

/-- Helper for Problem 3.9.3: every open neighborhood of `0` in `[0,1]` contains a positive
point. -/
theorem unit_interval_exists_positive_mem_of_open_zero
    {V : Set (Set.Icc (0 : ℝ) 1)} (hVOpen : IsOpen V) (hzV : zero_base ∈ V) :
    ∃ y : Set.Icc (0 : ℝ) 1, 0 < (y : ℝ) ∧ y ∈ V := by
  -- Move from openness at `0` to a metric ball around the endpoint.
  have hVnhds : V ∈ nhds zero_base := hVOpen.mem_nhds hzV
  rcases Metric.mem_nhds_iff.mp hVnhds with ⟨ε, hεpos, hεsub⟩
  let y : Set.Icc (0 : ℝ) 1 := ⟨min (ε / 2) (1 / 2), by
    constructor
    · have hy_nonneg : 0 ≤ min (ε / 2) (1 / 2) := by
        apply le_min
        · linarith
        · norm_num
      simpa using hy_nonneg
    · have hy_le_half : min (ε / 2) (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
      linarith⟩
  have hypos : 0 < (y : ℝ) := by
    -- Choosing the smaller of `ε / 2` and `1 / 2` keeps us positive and inside the interval.
    dsimp [y]
    apply lt_min
    · linarith
    · norm_num
  have hylt : (y : ℝ) < ε := by
    dsimp [y]
    have hmin : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
    linarith
  refine ⟨y, hypos, hεsub ?_⟩
  -- This chosen point lies in the radius-`ε` ball around `0`.
  change dist (y : ℝ) (zero_base : ℝ) < ε
  rw [show ((zero_base : Set.Icc (0 : ℝ) 1) : ℝ) = 0 by rfl, Real.dist_eq]
  have hy_nonneg : 0 ≤ (y : ℝ) := y.2.1
  simp [abs_of_nonneg hy_nonneg, hylt]

/-- Helper for Problem 3.9.3: the fiber over `0` is a singleton. -/
theorem branching_interval_projection_fiber_zero_subsingleton :
    Subsingleton (branchingIntervalProjection ⁻¹' ({zero_base} : Set (Set.Icc (0 : ℝ) 1))) := by
  refine ⟨?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  apply Subtype.ext
  apply Subtype.ext
  -- Both lifts have first coordinate `0`, hence their branch indices are forced to be `0`.
  have ha0 : ((a.1.1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
    simpa [branchingIntervalProjection, zero_base] using
      congrArg (fun x : Set.Icc (0 : ℝ) 1 ↦ ((x : Set.Icc (0 : ℝ) 1) : ℝ)) ha
  have hb0 : ((b.1.1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
    simpa [branchingIntervalProjection, zero_base] using
      congrArg (fun x : Set.Icc (0 : ℝ) 1 ↦ ((x : Set.Icc (0 : ℝ) 1) : ℝ)) hb
  have haBranch : a.1.2 = 0 := a.2 ha0
  have hbBranch : b.1.2 = 0 := b.2 hb0
  exact Prod.ext (ha.trans hb.symm) (haBranch.trans hbBranch.symm)

/-- Helper for Problem 3.9.3: every positive base point has two distinct lifts. -/
theorem branching_interval_projection_has_two_lifts_of_pos (y : Set.Icc (0 : ℝ) 1)
    (hy : 0 < (y : ℝ)) :
    ∃ a b : branchingIntervalProjection ⁻¹' ({y} : Set (Set.Icc (0 : ℝ) 1)), a ≠ b := by
  let yPos : { x : Set.Icc (0 : ℝ) 1 | x ∈ positive_base_slice } := ⟨y, hy⟩
  -- Take one lift on the zero branch and another on branch `1`.
  refine ⟨⟨zero_branch_point y, rfl⟩, ⟨positive_branch_point 1 yPos, rfl⟩, ?_⟩
  intro hEq
  -- Distinct branch indices force the two lifts to be different.
  have hUnderlying := Subtype.ext_iff.mp hEq
  have hNat : 0 = 1 := by
    simpa [zero_branch_point, positive_branch_point, yPos] using
      congrArg (fun z : BranchingInterval ↦ z.1.2) hUnderlying
  exact Nat.zero_ne_one hNat

/-- The branching interval projection is surjective onto the closed unit interval. -/
-- Proof sketch: send `0` to the distinguished point lying over `0`, and send every positive
-- `x ∈ [0,1]` to the point on the `0`th branch with first coordinate `x`.
theorem branchingIntervalProjection_surjective :
    Function.Surjective branchingIntervalProjection := by
  -- Every base point has a canonical lift on branch `0`.
  intro y
  exact ⟨zero_branch_point y, rfl⟩

/-- The branching interval projection is a local homeomorphism. -/
-- Proof sketch: away from `0`, restrict to a neighborhood inside a single branch `{n}`; at the
-- distinguished point over `0`, use the `0`th branch together with the relative topology on
-- `[0,1]` to obtain a neighborhood homeomorphic to an interval in the base.
theorem branchingIntervalProjection_isLocalHomeomorph :
    IsLocalHomeomorph branchingIntervalProjection := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro z
  by_cases hzpos : 0 < (branchingIntervalProjection z : ℝ)
  · -- Away from `0`, stay inside the unique branch already containing `z`.
    refine ⟨positive_branch_slice z.1.2, ?_, ?_⟩
    · exact (isOpen_positive_branch_slice z.1.2).mem_nhds ⟨hzpos, rfl⟩
    · exact positive_branch_slice_isOpenEmbedding z.1.2
  · -- At `0`, the branching relation forces us onto branch `0`.
    have hznonneg : 0 ≤ (branchingIntervalProjection z : ℝ) := z.1.1.2.1
    have hzzero : (branchingIntervalProjection z : ℝ) = 0 := by
      linarith
    have hzbranch : z.1.2 = 0 := z.2 hzzero
    refine ⟨zero_branch_slice, ?_, ?_⟩
    · refine isOpen_zero_branch_slice.mem_nhds ?_
      refine ⟨?_, hzbranch⟩
      simp [hzzero]
    · exact zero_branch_slice_isOpenEmbedding

/-- The branching interval projection is not a covering map in the sense of Definition 3.1.5. -/
-- Proof sketch: every neighborhood of `0` in `[0,1]` contains positive points. Over `0` the fiber
-- is a singleton, while over every positive point the fiber is countably infinite, so no
-- neighborhood of `0` can be evenly covered with a fixed discrete fiber.
theorem branchingIntervalProjection_not_isPathConnectedCoveringMap :
    ¬ IsPathConnectedCoveringMap branchingIntervalProjection := by
  -- Route correction: the contradiction is detected at the evenly covered neighborhood of `0`.
  intro hp
  rcases hp.2 zero_base with ⟨_hdisc, V, hzV, hVOpen, _hVPath, _hpre, H, hH⟩
  -- Any open neighborhood of `0` in the base contains a positive point.
  obtain ⟨y, hypos, hyV⟩ := unit_interval_exists_positive_mem_of_open_zero hVOpen hzV
  obtain ⟨a, b, hab⟩ := branching_interval_projection_has_two_lifts_of_pos y hypos
  have haV : branchingIntervalProjection a.1 ∈ V := by
    rw [a.2]
    exact hyV
  have hbV : branchingIntervalProjection b.1 ∈ V := by
    rw [b.2]
    exact hyV
  let aV : branchingIntervalProjection ⁻¹' V := ⟨a.1, haV⟩
  let bV : branchingIntervalProjection ⁻¹' V := ⟨b.1, hbV⟩
  have hzeroSub :
      Subsingleton (branchingIntervalProjection ⁻¹' ({zero_base} : Set (Set.Icc (0 : ℝ) 1))) :=
    branching_interval_projection_fiber_zero_subsingleton
  have hImages : H aV = H bV := by
    apply Prod.ext
    · -- The chart sends both lifts to the same base point `y`.
      apply Subtype.ext
      rw [hH aV, hH bV]
      rw [a.2, b.2]
    · -- The fiber coordinate over `0` is unique.
      exact hzeroSub.elim _ _
  have hEqV : aV = bV := H.injective hImages
  have hEq : a = b := by
    -- Forget the ambient neighborhood restriction to recover equality in the fiber over `y`.
    apply Subtype.ext
    exact congrArg (fun x : branchingIntervalProjection ⁻¹' V ↦ x.1) hEqV
  exact hab hEq
