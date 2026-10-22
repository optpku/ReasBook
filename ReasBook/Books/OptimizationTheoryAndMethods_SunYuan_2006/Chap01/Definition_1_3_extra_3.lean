/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Cone.InnerDual

open Pointwise
open scoped RealInnerProductSpace

-- Domain sampling for this file:
-- * `ProperCone.innerDual`, `ProperCone.mem_innerDual`, and
--   `ProperCone.innerDual_innerDual` are the core/canonical dual-cone API in complete real
--   inner-product spaces.
-- * `ConvexCone` is the source-facing bundled owner for convex cones, and closed nonempty
--   convex cones lift canonically to `ProperCone`.
--
-- The declaration `polarCone` below is a source-facing bridge/view: it keeps the textbook sign
-- convention `⟪p, x⟫ ≤ 0` by reusing the core owner `ProperCone.innerDual` on `-S`.

section Chapter01Definition13Extra3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Property (1) for Chapter01 Definition 1.3-extra-3: for `S : Set E`, the polar cone of `S` is the
proper cone of all vectors `p` such that `⟪p, x⟫ ≤ 0` for every `x ∈ S`. -/
noncomputable abbrev polarCone (S : Set E) : ProperCone ℝ E :=
  ProperCone.innerDual (-S)

/-- Membership in `polarCone S` is the defining pointwise inequality. -/
theorem mem_polarCone_iff {S : Set E} {p : E} :
    p ∈ (polarCone S : Set E) ↔ ∀ x ∈ S, ⟪p, x⟫ ≤ (0 : ℝ) := by
  constructor
  · intro hp x hx
    -- Evaluate the dual-cone condition on `-x`, the point of `-S` corresponding to `x ∈ S`.
    have hp' : p ∈ ProperCone.innerDual (-S) := by
      simpa [polarCone] using hp
    have hx_neg : -x ∈ (-S : Set E) := by
      simpa [Set.mem_neg] using hx
    have hneg : 0 ≤ ⟪-x, p⟫ := (ProperCone.mem_innerDual.mp hp') hx_neg
    -- Rewriting the sign yields the textbook inequality `⟪p, x⟫ ≤ 0`.
    have hneg' : 0 ≤ (-⟪p, x⟫) := by
      simpa [real_inner_comm, inner_neg_left] using hneg
    exact neg_nonneg.mp hneg'
  · intro hp
    -- To show `p` is in the polar cone, test the defining inequality on an arbitrary point of `-S`.
    have hp' : p ∈ ProperCone.innerDual (-S) := by
      rw [ProperCone.mem_innerDual]
      intro x hx
      have hx' : -x ∈ S := by
        simpa [Set.mem_neg] using hx
      have hpx : ⟪p, -x⟫ ≤ 0 := hp (-x) hx'
      -- The sign normalization turns `⟪p, -x⟫ ≤ 0` into `0 ≤ ⟪x, p⟫`.
      have hnonpos : (-⟪x, p⟫) ≤ 0 := by
        simpa [real_inner_comm, inner_neg_right] using hpx
      exact neg_nonpos.mp hnonpos
    simpa [polarCone] using hp'

/-- The zero vector belongs to the polar cone of any set. -/
theorem zero_mem_polarCone {S : Set E} :
    (0 : E) ∈ polarCone S := by
  -- The polar cone is a proper cone, so it contains `0` by its bundled additive structure.
  exact (polarCone S).zero_mem

/-- The polar cone is closed under addition. -/
theorem add_mem_polarCone {S : Set E} {p q : E}
    (hp : p ∈ polarCone S) (hq : q ∈ polarCone S) :
    p + q ∈ polarCone S := by
  -- Add the defining inequalities for `p` and `q` pointwise on `S`.
  refine mem_polarCone_iff.mpr ?_
  intro x hx
  -- Rewrite the inner product of `p + q` as the sum of the two defining inequalities.
  have hsum : ⟪p, x⟫ + ⟪q, x⟫ ≤ 0 :=
    add_nonpos ((mem_polarCone_iff.mp hp) x hx) ((mem_polarCone_iff.mp hq) x hx)
  simpa [inner_add_left] using hsum

/-- The polar cone is closed under multiplication by nonnegative scalars. -/
theorem smul_mem_polarCone {S : Set E} {a : ℝ} (ha : 0 ≤ a) {p : E}
    (hp : p ∈ polarCone S) : a • p ∈ polarCone S := by
  -- Nonnegative scaling is part of the `ProperCone` API.
  simpa using ProperCone.smul_mem (polarCone S) hp ha

/-- Property (2) for Chapter01 Definition 1.3-extra-3: the polar cone of any set is closed. -/
theorem polarCone_isClosed {S : Set E} :
    IsClosed (polarCone S : Set E) := by
  -- `polarCone S` is already bundled as a closed cone.
  simpa using ProperCone.isClosed (polarCone S)

/-- Property (3) for Chapter01 Definition 1.3-extra-3: the polar cone of any set is convex. -/
theorem polarCone_convex {S : Set E} :
    Convex ℝ (polarCone S : Set E) := by
  -- Convexity is likewise inherited from the bundled proper-cone structure.
  simpa using ProperCone.convex (polarCone S)

/-- Property (4) for Chapter01 Definition 1.3-extra-3:
every set is contained in its double polar cone. -/
theorem subset_polarCone_polarCone {S : Set E} :
    S ⊆ polarCone (polarCone S : Set E) := by
  intro x hx
  -- Unfold the outer polar membership and test the inner polar inequality at `x`.
  refine mem_polarCone_iff.mpr ?_
  intro p hp
  -- Swapping the inner-product arguments turns the inner polar inequality into the needed one.
  simpa [real_inner_comm] using (mem_polarCone_iff.mp hp) x hx

/-- Helper for Chapter01 Definition 1.3-extra-3: negating the polar cone recovers the canonical
inner dual with the standard `0 ≤ ⟪x, y⟫` convention. -/
lemma neg_polarCone_eq_innerDual {S : Set E} :
    -(polarCone S : Set E) = (ProperCone.innerDual S : Set E) := by
  ext y
  constructor
  · intro hy
    have hy' : -y ∈ polarCone S := by
      simpa [Set.mem_neg] using hy
    -- Translate the local sign convention into the positive inner-dual convention.
    refine ProperCone.mem_innerDual.mpr ?_
    intro x hx
    have hxy : ⟪-y, x⟫ ≤ 0 := (mem_polarCone_iff.mp hy') x hx
    have hxy' : (-⟪x, y⟫) ≤ 0 := by
      simpa [real_inner_comm, inner_neg_left] using hxy
    exact neg_nonpos.mp hxy'
  · intro hy
    have hy' : -y ∈ polarCone S := by
      -- Prove the defining polar inequality for `-y` from the inner-dual inequality for `y`.
      refine mem_polarCone_iff.mpr ?_
      intro x hx
      have hxy : 0 ≤ ⟪x, y⟫ := (ProperCone.mem_innerDual.mp hy) hx
      have hxy' : (-⟪x, y⟫) ≤ 0 := neg_nonpos.mpr hxy
      simpa [real_inner_comm, inner_neg_left] using hxy'
    simpa [Set.mem_neg] using hy'

/-- Helper for Chapter01 Definition 1.3-extra-3: the local polar-cone convention satisfies the
standard bipolar theorem on bundled proper cones. -/
lemma polarCone_polarCone_eq_of_properCone (K : ProperCone ℝ E) :
    (polarCone (polarCone (K : Set E) : Set E) : Set E) = K := by
  -- Normalize the outer polar cone to the canonical double inner dual.
  rw [polarCone, neg_polarCone_eq_innerDual]
  -- The remaining statement is exactly mathlib's bipolar theorem for proper cones.
  exact congrArg (fun C : ProperCone ℝ E => (C : Set E)) (ProperCone.innerDual_innerDual K)

/-- Chapter01 Definition 1.3-extra-3 (5): a nonempty closed convex cone agrees with its double
polar cone. The bundled source-facing owner for the cone is `ConvexCone`. -/
theorem polarCone_polarCone_eq (C : ConvexCone ℝ E)
    (hC_nonempty : Set.Nonempty (C : Set E)) (hC_closed : IsClosed (C : Set E)) :
    (polarCone (polarCone (C : Set E) : Set E) : Set E) = C := by
  -- Lift the closed nonempty convex cone to the canonical proper-cone owner.
  lift C to ProperCone ℝ E using ⟨hC_nonempty, hC_closed⟩
  -- After the lift, the set-level statement is exactly the proper-cone bipolar theorem.
  change (polarCone (polarCone (C : Set E) : Set E) : Set E) = (C : Set E)
  simpa using polarCone_polarCone_eq_of_properCone C

/-- Chapter01 Definition 1.3-extra-3 (6): inclusion reverses under the polar-cone operation. -/
theorem polarCone_anti {S1 S2 : Set E} (hsub : S1 ⊆ S2) :
    polarCone S2 ≤ polarCone S1 := by
  intro p hp
  -- Restrict the defining inequalities for `S2` along the inclusion `S1 ⊆ S2`.
  refine mem_polarCone_iff.mpr ?_
  intro x hx
  exact (mem_polarCone_iff.mp hp) x (hsub hx)

end Chapter01Definition13Extra3
