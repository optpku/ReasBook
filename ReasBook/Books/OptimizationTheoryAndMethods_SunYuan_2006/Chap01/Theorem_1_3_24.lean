/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_23
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

/-!
Chapter01 Theorem 1.3.24 lives in convex separation.

Domain sampling:
* mathlib proof engine for convex closed-point separation:
  `geometric_hahn_banach_closed_point`;
* chapter owner for the source-facing supporting-sunYuanHyperplane notion:
  `IsSupportingHyperplaneAt`;
* chapter owner for the oriented half-space surface:
  `closedLowerHalfSpace`;
* chapter bridge from the owner to the anchored inequality surface:
  `isSupportingHyperplaneAt_iff_halfSpace`.

Best owner abstraction:
* the source-facing theorem is existence of a supporting sunYuanHyperplane at a frontier point;
* the oriented lower-half-space conclusion on `closure S` is a bridge/view obtained by choosing
  the sign of the supporting normal.

Layer choice:
* `existsSupportingHyperplaneAt_of_mem_frontier` is `source-facing`;
* `existsNonzeroSupportingVectorOnClosure` is the `bridge/view` companion.

Primitive data:
* `S`, `hS_convex`, `xbar`, `hxbar`.

Derived API:
* `IsSupportingHyperplaneAt S xbar p`;
* the oriented inclusion `closure S ⊆ closedLowerHalfSpace p ⟪p, xbar⟫`, obtained by the
  nonempty-interior / empty-interior split proved below.
-/

section Theorem1324

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Chapter01 Theorem 1.3.24: when `S` has nonempty interior, Hahn-Banach separates the
boundary point `xbar` from `interior S`, and continuity extends the resulting inequality from `S`
to `closure S`. -/
lemma existsNonzeroSupportingVectorOnClosure_of_nonemptyInterior
    (S : Set E) (hS_convex : Convex ℝ S) (xbar : E) (hxbar : xbar ∈ frontier S)
    (hSint : (interior S).Nonempty) :
    ∃ p : E, p ≠ 0 ∧ closure S ⊆ closedLowerHalfSpace p ⟪p, xbar⟫ := by
  have hxbar_not_mem_interior : xbar ∉ interior S := by
    rw [frontier, mem_sdiff] at hxbar
    exact hxbar.2
  obtain ⟨f, hfne, hS_le⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hS_convex hxbar_not_mem_interior hSint
  let p : E := (InnerProductSpace.toDual ℝ E).symm f
  have hp : p ≠ 0 := by
    intro hp
    apply hfne
    simpa [p] using congrArg (InnerProductSpace.toDual ℝ E) hp
  refine ⟨p, hp, ?_⟩
  refine closure_minimal ?_ ?_
  · intro x hx
    have hx' : f x ≤ f xbar := hS_le x hx
    simpa [p, InnerProductSpace.toDual_symm_apply] using hx'
  · have hcont : Continuous (fun x : E ↦ ⟪p, x⟫) := continuous_const.inner continuous_id
    simpa [closedLowerHalfSpace, Set.preimage] using isClosed_Iic.preimage hcont

/-- Helper for Chapter01 Theorem 1.3.24: the closure of `S` stays inside its affine span. -/
lemma closure_subset_affineSpan (S : Set E) : closure S ⊆ affineSpan ℝ S := by
  -- The affine span is closed in finite dimensions, so closure adds no new points outside it.
  exact closure_minimal (subset_affineSpan ℝ S) (AffineSubspace.closed_of_finiteDimensional _)

/-- Helper for Chapter01 Theorem 1.3.24: a proper affine subspace admits a nonzero normal vector
whose anchored inner product vanishes on the whole subspace. -/
lemma existsNonzeroNormalOfAffineSubspaceNeTop
    (A : AffineSubspace ℝ E) (xbar : E) (hxbar : xbar ∈ A) (hA_ne_top : A ≠ ⊤) :
    ∃ p : E, p ≠ 0 ∧ ∀ x ∈ A, ⟪p, x - xbar⟫ = (0 : ℝ) := by
  have hdir_ne_top : A.direction ≠ ⊤ := by
    -- If the direction were all of `E`, the affine subspace itself would already be `⊤`.
    intro hdir_top
    apply hA_ne_top
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨xbar, hxbar⟩).mp hdir_top
  have horth_ne_bot : A.directionᗮ ≠ ⊥ := by
    -- A proper direction has a nontrivial orthogonal complement.
    intro horth_bot
    apply hdir_ne_top
    exact (Submodule.orthogonal_eq_bot_iff).mp horth_bot
  obtain ⟨p, hp_mem, hp_ne_zero⟩ := A.directionᗮ.ne_bot_iff.mp horth_ne_bot
  refine ⟨p, hp_ne_zero, ?_⟩
  intro x hx
  -- Anchored differences of points in the affine subspace lie in its direction.
  have hx_vsub : x - xbar ∈ A.direction := by
    simpa using AffineSubspace.vsub_mem_direction hx hxbar
  -- Orthogonality of `p` to the direction turns that anchored difference into zero inner product.
  exact ((Submodule.mem_orthogonal' A.direction p).1 hp_mem) (x - xbar) hx_vsub

/-- Helper for Chapter01 Theorem 1.3.24: if `interior S = ∅`, then the whole closure of `S`
lies in a proper affine sunYuanHyperplane through `xbar`, yielding a supporting lower half-space. -/
lemma existsNonzeroSupportingVectorOnClosure_of_emptyInterior
    (S : Set E) (hS_convex : Convex ℝ S) (xbar : E) (hxbar : xbar ∈ frontier S)
    (hSint_empty : ¬ (interior S).Nonempty) :
    ∃ p : E, p ≠ 0 ∧ closure S ⊆ closedLowerHalfSpace p ⟪p, xbar⟫ := by
  have hxbar_closure : xbar ∈ closure S := frontier_subset_closure hxbar
  have hxbar_affineSpan : xbar ∈ affineSpan ℝ S := closure_subset_affineSpan S hxbar_closure
  have hAffine_ne_top : affineSpan ℝ S ≠ ⊤ := by
    -- Empty interior forces the affine span to be proper.
    intro hAffine_top
    apply hSint_empty
    exact (Convex.interior_nonempty_iff_affineSpan_eq_top hS_convex).2 hAffine_top
  obtain ⟨p, hp_ne_zero, hp_zero⟩ :=
    existsNonzeroNormalOfAffineSubspaceNeTop (affineSpan ℝ S) xbar hxbar_affineSpan hAffine_ne_top
  refine ⟨p, hp_ne_zero, ?_⟩
  intro x hx
  have hx_affineSpan : x ∈ affineSpan ℝ S := closure_subset_affineSpan S hx
  -- Every point of `closure S` lies in the affine span, so the anchored inner product is zero.
  have hzero : ⟪p, x - xbar⟫ = (0 : ℝ) := hp_zero x hx_affineSpan
  have hinner : ⟪p, x⟫ = ⟪p, xbar⟫ := by
    -- Rewriting the anchored equality gives the half-space boundary equation.
    exact sub_eq_zero.mp (by simpa [inner_sub_right] using hzero)
  -- Equality on the boundary is enough for membership in the closed lower half-space.
  simpa [closedLowerHalfSpace] using le_of_eq hinner

/-- Helper for Chapter01 Theorem 1.3.24: choose a nonzero supporting vector on `closure S` by
splitting into the nonempty-interior and empty-interior cases. -/
lemma existsNonzeroSupportingVectorOnClosureAtFrontier
    (S : Set E) (hS_convex : Convex ℝ S) (xbar : E) (hxbar : xbar ∈ frontier S) :
    ∃ p : E, p ≠ 0 ∧ closure S ⊆ closedLowerHalfSpace p ⟪p, xbar⟫ := by
  -- Route correction: bypass the imported bridge theorem.
  -- The in-file proof splits directly on `interior S`.
  by_cases hSint : (interior S).Nonempty
  · exact existsNonzeroSupportingVectorOnClosure_of_nonemptyInterior S hS_convex xbar hxbar hSint
  · exact existsNonzeroSupportingVectorOnClosure_of_emptyInterior S hS_convex xbar hxbar hSint

/-- Chapter01 Theorem 1.3.24: if `S` is convex and `xbar ∈ frontier S`, then there exists a
supporting sunYuanHyperplane of `S` at `xbar`. The source states this in `ℝ^n`; here the owner theorem
is stated on an abstract finite-dimensional real inner-product space, which is source-faithful up
to linear isometry and avoids choosing coordinates. The source's explicit nonemptiness hypothesis
is redundant because `xbar ∈ frontier S` already implies `S.Nonempty`. -/
theorem existsSupportingHyperplaneAt_of_mem_frontier
    (S : Set E) (hS_convex : Convex ℝ S) (xbar : E) (hxbar : xbar ∈ frontier S) :
    ∃ p : E, IsSupportingHyperplaneAt S xbar p := by
  -- First obtain the oriented supporting inequality on `closure S`.
  obtain ⟨p, hp, hp_closure⟩ :=
    existsNonzeroSupportingVectorOnClosureAtFrontier S hS_convex xbar hxbar
  have hS_nonempty : S.Nonempty := by
    -- A frontier point belongs to `closure S`, so `S` itself cannot be empty.
    have hxbar_closure : xbar ∈ closure S := frontier_subset_closure hxbar
    by_contra hS_empty
    rw [Set.not_nonempty_iff_eq_empty] at hS_empty
    simp [hS_empty] at hxbar_closure
  refine ⟨p, ?_⟩
  -- Package the oriented half-space inclusion into the chapter owner predicate.
  rw [isSupportingHyperplaneAt_iff]
  refine ⟨hS_nonempty, hxbar, hp, Or.inr ?_⟩
  exact subset_trans subset_closure hp_closure

end Theorem1324
