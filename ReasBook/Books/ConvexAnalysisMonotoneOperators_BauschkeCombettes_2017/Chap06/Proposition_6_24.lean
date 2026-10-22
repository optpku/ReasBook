/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace

universe u

namespace Set

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal set of a subset of a real inner product space, corresponding to the textbook
notation `C^⊥`. -/
def orthogonalSet (C : Set E) : Set E :=
  {u | ∀ x ∈ C, ⟪x, u⟫_ℝ = 0}

scoped notation:max C "^⊥" => Set.orthogonalSet C

-- Proof sketch: unfold `orthogonalSet` and simplify the defining predicate.
/-- Membership in the orthogonal set means being orthogonal to every point of the original set. -/
theorem mem_orthogonalSet {C : Set E} {u : E} :
    u ∈ orthogonalSet C ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ = 0 := by
  -- Unfold the defining set to expose the pointwise orthogonality condition.
  simp [orthogonalSet]

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The positive polar cone of a subset of a real Hilbert space, corresponding to the textbook
notation `C^⊕`. -/
abbrev positivePolar (C : Set E) : Set E :=
  (ProperCone.innerDual C : Set E)

/-- The negative polar cone of a subset of a real Hilbert space, corresponding to the textbook
notation `C^⊖`. -/
abbrev negativePolar (C : Set E) : Set E :=
  (ProperCone.innerDual (-C) : Set E)

-- Proof sketch: unfold `positivePolar` to `ProperCone.innerDual C` and use the defining membership
-- criterion for the inner dual cone.
/-- Membership in the positive polar cone means having nonnegative inner product with every point of
the original set. -/
theorem mem_positivePolar {C : Set E} {u : E} :
    u ∈ positivePolar C ↔ ∀ x ∈ C, 0 ≤ ⟪x, u⟫_ℝ := by
  -- Rewrite `positivePolar` to the inner dual and read off its defining inequality.
  constructor
  · intro hu x hx
    exact (ProperCone.mem_innerDual.mp hu) hx
  · intro hu
    exact ProperCone.mem_innerDual.mpr fun x hx ↦ hu x hx

-- Proof sketch: unfold `negativePolar` as the inner dual of `-C` and rewrite membership in `-C`
-- by substituting `x = -c`.
/-- Membership in the negative polar cone means having nonpositive inner product with every point of
the original set. -/
theorem mem_negativePolar {C : Set E} {u : E} :
    u ∈ negativePolar C ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 0 := by
  -- Rewrite membership in `-C` by testing the defining inequality on the negated point.
  change u ∈ (ProperCone.innerDual (-C) : Set E) ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 0
  constructor
  · intro hu x hx
    have hx_neg : -x ∈ -C := Set.mem_neg.mpr (by simpa using hx)
    have hdual : 0 ≤ ⟪-x, u⟫_ℝ := hu hx_neg
    simpa [inner_neg_left] using hdual
  · intro hu y hy
    have hyC : -y ∈ C := Set.mem_neg.mp hy
    have hnonpos : ⟪-y, u⟫_ℝ ≤ 0 := hu (-y) hyC
    simpa [inner_neg_left] using hnonpos

-- Proof sketch: the negative polar is an antitone construction because every inequality required
-- for `C` is also required for the smaller set `D`.
/-- Proposition 6.24 (1): textbook clause (i) for the negative polar cone. If `D ⊆ C`, then
`C^⊖ ⊆ D^⊖`. -/
theorem negativePolar_subset_of_subset {C D : Set E} (hDC : D ⊆ C) :
    negativePolar C ⊆ negativePolar D := by
  -- Any nonpositive inequality valid on `C` remains valid on the smaller set `D`.
  intro u hu
  rw [mem_negativePolar] at hu ⊢
  intro x hx
  exact hu x (hDC hx)

-- Proof sketch: the positive polar is antitone for the same reason as the negative polar.
/-- Proposition 6.24 (2): textbook clause (i) for the positive polar cone. If `D ⊆ C`, then
`C^⊕ ⊆ D^⊕`. -/
theorem positivePolar_subset_of_subset {C D : Set E} (hDC : D ⊆ C) :
    positivePolar C ⊆ positivePolar D := by
  -- Any nonnegative inequality valid on `C` remains valid on the smaller set `D`.
  intro u hu
  rw [mem_positivePolar] at hu ⊢
  intro x hx
  exact hu x (hDC hx)

-- Proof sketch: `negativePolar C` is the underlying set of the proper cone `ProperCone.innerDual
-- (-C)`, so it contains `0`.
/-- Proposition 6.24 (3): textbook clause (ii). The negative polar cone is nonempty. -/
theorem negativePolar_nonempty (C : Set E) :
    (negativePolar C).Nonempty := by
  -- The inner dual of any set is a proper cone, hence contains the origin.
  simpa [negativePolar] using (ProperCone.innerDual (-C)).nonempty

-- Proof sketch: `positivePolar C` is the underlying set of the proper cone `ProperCone.innerDual
-- C`, so it contains `0`.
/-- Proposition 6.24 (4): textbook clause (ii). The positive polar cone is nonempty. -/
theorem positivePolar_nonempty (C : Set E) :
    (positivePolar C).Nonempty := by
  -- The inner dual of any set is a proper cone, hence contains the origin.
  simpa [positivePolar] using (ProperCone.innerDual C).nonempty

-- Proof sketch: `negativePolar C` is the underlying set of the proper cone `ProperCone.innerDual
-- (-C)`, and proper cones are closed.
/-- Proposition 6.24 (5): textbook clause (ii). The negative polar cone is closed. -/
theorem negativePolar_isClosed (C : Set E) :
    IsClosed (negativePolar C) := by
  -- Proper cones are closed, and `negativePolar C` is the carrier of an inner dual cone.
  simpa [negativePolar] using (ProperCone.innerDual (-C)).isClosed

-- Proof sketch: `positivePolar C` is the underlying set of the proper cone `ProperCone.innerDual
-- C`, and proper cones are closed.
/-- Proposition 6.24 (6): textbook clause (ii). The positive polar cone is closed. -/
theorem positivePolar_isClosed (C : Set E) :
    IsClosed (positivePolar C) := by
  -- Proper cones are closed, and `positivePolar C` is the carrier of an inner dual cone.
  simpa [positivePolar] using (ProperCone.innerDual C).isClosed

-- Proof sketch: the underlying set of every proper cone is convex, and `negativePolar C` is
-- realized as `ProperCone.innerDual (-C)`.
/-- Proposition 6.24 (7): textbook clause (ii). The negative polar cone is convex. -/
theorem negativePolar_convex (C : Set E) :
    Convex ℝ (negativePolar C) := by
  -- Proper cones are convex, and `negativePolar C` is the carrier of an inner dual cone.
  simpa [negativePolar] using (ProperCone.innerDual (-C)).convex

-- Proof sketch: the underlying set of every proper cone is convex, and `positivePolar C` is
-- realized as `ProperCone.innerDual C`.
/-- Proposition 6.24 (8): textbook clause (ii). The positive polar cone is convex. -/
theorem positivePolar_convex (C : Set E) :
    Convex ℝ (positivePolar C) := by
  -- Proper cones are convex, and `positivePolar C` is the carrier of an inner dual cone.
  simpa [positivePolar] using (ProperCone.innerDual C).convex

-- Proof sketch: a proper cone is stable under positive scalar multiplication, so its underlying set
-- satisfies the project cone predicate `IsCone`.
/-- Proposition 6.24 (9): textbook clause (ii). The negative polar cone is a cone. -/
theorem negativePolar_isCone (C : Set E) :
    IsCone (negativePolar C) := by
  -- One inclusion uses the scalar `1`; the other uses closure of the inner dual under scaling.
  refine Subset.antisymm ?_ ?_
  · intro x hx
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · intro x hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    exact (ProperCone.innerDual (-C)).smul_mem hy ha.le

-- Proof sketch: a proper cone is stable under positive scalar multiplication, so its underlying set
-- satisfies the project cone predicate `IsCone`.
/-- Proposition 6.24 (10): textbook clause (ii). The positive polar cone is a cone. -/
theorem positivePolar_isCone (C : Set E) :
    IsCone (positivePolar C) := by
  -- One inclusion uses the scalar `1`; the other uses closure of the inner dual under scaling.
  refine Subset.antisymm ?_ ?_
  · intro x hx
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · intro x hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    exact (ProperCone.innerDual C).smul_mem hy ha.le

/-- Helper for Proposition 6.24: the halfspace cut out by the nonpositive inner-product inequality
with a fixed vector. -/
private def nonpositiveInnerHalfspace (u : E) : Set E :=
  {x | ⟪x, u⟫_ℝ ≤ 0}

/-- Helper for Proposition 6.24: positive scalar multiples remain in the nonpositive inner-product
halfspace. -/
private lemma nonpositiveInnerHalfspace_smul_mem {u : E} :
    ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x : E⦄, x ∈ nonpositiveInnerHalfspace u →
      a • x ∈ nonpositiveInnerHalfspace u := by
  intro a ha x hx
  -- Scale the first inner-product entry and preserve the sign using `ha ≥ 0`.
  dsimp [nonpositiveInnerHalfspace] at hx ⊢
  simpa [real_inner_smul_left] using mul_nonpos_of_nonneg_of_nonpos ha.le hx

/-- Helper for Proposition 6.24: sums remain in the nonpositive inner-product halfspace. -/
private lemma nonpositiveInnerHalfspace_add_mem {u : E} :
    ∀ ⦃x : E⦄, x ∈ nonpositiveInnerHalfspace u → ∀ ⦃y : E⦄,
      y ∈ nonpositiveInnerHalfspace u → x + y ∈ nonpositiveInnerHalfspace u := by
  intro x hx y hy
  -- Add the two inequalities after expanding the inner product in the first argument.
  dsimp [nonpositiveInnerHalfspace] at hx hy ⊢
  simpa [inner_add_left] using add_nonpos hx hy

/-- Helper for Proposition 6.24: the nonpositive inner-product halfspace is a convex cone. -/
private def nonpositiveInnerConvexCone (u : E) : ConvexCone ℝ E where
  carrier := nonpositiveInnerHalfspace u
  smul_mem' := nonpositiveInnerHalfspace_smul_mem
  add_mem' := nonpositiveInnerHalfspace_add_mem

/-- Helper for Proposition 6.24: the nonpositive inner-product halfspace is closed. -/
private lemma nonpositiveInnerHalfspace_isClosed (u : E) :
    IsClosed (nonpositiveInnerHalfspace u) := by
  -- Realize the halfspace as the preimage of the closed ray `(-∞, 0]`.
  simpa [nonpositiveInnerHalfspace] using
    isClosed_le (continuous_id.inner continuous_const) continuous_const

/-- Helper for Proposition 6.24: a nonpositive inner-product inequality persists from `C` to its
convex hull, conical hull, and closure. -/
private theorem nonpos_inner_halfspace_stability {C : Set E} {u : E}
    (hu : ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 0) :
    (∀ x ∈ convexHull ℝ C, ⟪x, u⟫_ℝ ≤ 0) ∧
      (∀ x ∈ cone C, ⟪x, u⟫_ℝ ≤ 0) ∧
      ∀ x ∈ closure C, ⟪x, u⟫_ℝ ≤ 0 := by
  have hC : C ⊆ nonpositiveInnerHalfspace u := by
    intro x hx
    exact hu x hx
  have hconvHull : convexHull ℝ C ⊆ nonpositiveInnerHalfspace u := by
    -- The halfspace is convex, so convex-hull minimality extends the inequality.
    refine convexHull_min hC ?_
    simpa [nonpositiveInnerConvexCone] using (nonpositiveInnerConvexCone u).convex
  have hcone : cone C ⊆ nonpositiveInnerHalfspace u := by
    -- Route correction: the conical-hull step must use `ConvexCone.hull_min`, since `cone` is the
    -- bundled convex-cone hull from Definition 6.9.
    simpa [Set.cone, nonpositiveInnerConvexCone] using
      (ConvexCone.hull_min (R := ℝ) (s := C) (C := nonpositiveInnerConvexCone u) hC)
  have hclosure : closure C ⊆ nonpositiveInnerHalfspace u := by
    -- Closedness of the halfspace transports the inequality to the closure.
    exact closure_minimal hC (nonpositiveInnerHalfspace_isClosed u)
  exact ⟨fun x hx ↦ hconvHull hx, fun x hx ↦ hcone hx, fun x hx ↦ hclosure hx⟩

-- Proof sketch: passing from `C` to its conical hull does not change the inequalities defining the
-- negative polar, because those inequalities are preserved under positive scalar multiplication and
-- addition.
/-- Proposition 6.24 (11): textbook clause (iii) for the conical hull. The negative polar cone is
unchanged by replacing `C` with `cone C`. -/
theorem negativePolar_cone_eq (C : Set E) :
    negativePolar (cone C) = negativePolar C := by
  ext u
  rw [mem_negativePolar, mem_negativePolar]
  constructor
  · intro hu x hx
    -- Restrict the inequality from `cone C` back to the original set via `C ⊆ cone C`.
    exact hu x (by simpa [Set.cone] using (ConvexCone.subset_hull (R := ℝ) (s := C) hx))
  · intro hu
    -- The halfspace-stability helper extends the inequality from `C` to `cone C`.
    exact (nonpos_inner_halfspace_stability (C := C) (u := u) hu).2.1

-- Proof sketch: passing from `C` to its convex hull does not change the inequalities defining the
-- negative polar, because those inequalities are preserved under convex combinations.
/-- Proposition 6.24 (12): textbook clause (iii) for the convex hull. The negative polar cone is
unchanged by replacing `C` with `conv C`, represented in Lean by `convexHull ℝ C`. -/
theorem negativePolar_convexHull_eq (C : Set E) :
    negativePolar (convexHull ℝ C) = negativePolar C := by
  ext u
  rw [mem_negativePolar, mem_negativePolar]
  constructor
  · intro hu x hx
    -- Restrict the inequality from the convex hull back to the original set.
    exact hu x (subset_convexHull ℝ C hx)
  · intro hu
    -- The halfspace-stability helper extends the inequality from `C` to its convex hull.
    exact (nonpos_inner_halfspace_stability (C := C) (u := u) hu).1

-- Proof sketch: the inner product with a fixed vector is continuous, so the defining inequalities
-- for the negative polar extend from `C` to `closure C` and restrict back by inclusion.
/-- Proposition 6.24 (13): textbook clause (iii) for the closure. The negative polar cone is
unchanged by replacing `C` with `closure C`. -/
theorem negativePolar_closure_eq (C : Set E) :
    negativePolar (closure C) = negativePolar C := by
  ext u
  rw [mem_negativePolar, mem_negativePolar]
  constructor
  · intro hu x hx
    -- Restrict the inequality from the closure back to the original set.
    exact hu x (subset_closure hx)
  · intro hu
    -- The halfspace-stability helper extends the inequality from `C` to its closure.
    exact (nonpos_inner_halfspace_stability (C := C) (u := u) hu).2.2

-- Proof sketch: belonging to both polar cones means each inner product is simultaneously
-- nonnegative and nonpositive, hence zero; conversely orthogonality implies both inequalities.
/-- Proposition 6.24 (14): textbook clause (iv). The intersection of the negative and positive
polar cones is the orthogonal set of `C`. -/
theorem negativePolar_inter_positivePolar_eq_orthogonalSet (C : Set E) :
    negativePolar C ∩ positivePolar C = orthogonalSet C := by
  ext u
  rw [mem_orthogonalSet]
  constructor
  · rintro ⟨hu_neg, hu_pos⟩ x hx
    -- The two polar inequalities squeeze the inner product to zero.
    have hnonpos : ⟪x, u⟫_ℝ ≤ 0 := (mem_negativePolar.mp hu_neg) x hx
    have hnonneg : 0 ≤ ⟪x, u⟫_ℝ := (mem_positivePolar.mp hu_pos) x hx
    linarith
  · intro hu
    -- Exact orthogonality implies both the nonpositive and nonnegative inequalities.
    refine ⟨mem_negativePolar.mpr ?_, mem_positivePolar.mpr ?_⟩
    · intro x hx
      simp [hu x hx]
    · intro x hx
      simp [hu x hx]

-- Proof sketch: apply clause (iii) to replace `C` by `closure (cone C)`, then use the symmetry
-- hypothesis `closure (cone C) = -closure (cone C)` to identify the positive and negative defining
-- inequalities.
/-- Proposition 6.24 (15): textbook clause (v). If `closure (cone C)` is symmetric, then the
negative and positive polar cones of `C` coincide. -/
theorem negativePolar_eq_positivePolar_of_closure_cone_eq_neg {C : Set E}
    (hC_symm : closure (cone C) = -closure (cone C)) :
    negativePolar C = positivePolar C := by
  ext u
  rw [mem_negativePolar, mem_positivePolar]
  constructor
  · intro hu x hx
    -- First extend the nonpositive inequality from `C` to the symmetric closed cone.
    have hu_closedCone : ∀ y ∈ closure (cone C), ⟪y, u⟫_ℝ ≤ 0 := by
      have hu' : u ∈ negativePolar (closure (cone C)) := by
        rw [negativePolar_closure_eq, negativePolar_cone_eq]
        exact mem_negativePolar.mpr hu
      exact mem_negativePolar.mp hu'
    have hx_closedCone : x ∈ closure (cone C) := by
      exact subset_closure <| by
        simpa [Set.cone] using (ConvexCone.subset_hull (R := ℝ) (s := C) hx)
    have hx_neg_mem : -x ∈ closure (cone C) := by
      have hx_symm : x ∈ -closure (cone C) := by
        rw [← hC_symm]
        exact hx_closedCone
      exact Set.mem_neg.mp hx_symm
    -- Evaluating at `-x` flips the sign and yields the desired nonnegative inequality.
    have hnonpos : ⟪-x, u⟫_ℝ ≤ 0 := hu_closedCone (-x) hx_neg_mem
    simpa [inner_neg_left] using hnonpos
  · intro hu x hx
    -- Convert the positive inequality on `C` into a negative inequality for `-u`.
    have hneg_u : -u ∈ negativePolar C := by
      rw [mem_negativePolar]
      intro y hy
      have hnonneg : 0 ≤ ⟪y, u⟫_ℝ := hu y hy
      simpa [inner_neg_right] using hnonneg
    have hneg_closedCone : ∀ y ∈ closure (cone C), ⟪y, -u⟫_ℝ ≤ 0 := by
      have hneg_u' : -u ∈ negativePolar (closure (cone C)) := by
        rw [negativePolar_closure_eq, negativePolar_cone_eq]
        exact hneg_u
      exact mem_negativePolar.mp hneg_u'
    have hx_closedCone : x ∈ closure (cone C) := by
      exact subset_closure <| by
        simpa [Set.cone] using (ConvexCone.subset_hull (R := ℝ) (s := C) hx)
    have hx_neg_mem : -x ∈ closure (cone C) := by
      have hx_symm : x ∈ -closure (cone C) := by
        rw [← hC_symm]
        exact hx_closedCone
      exact Set.mem_neg.mp hx_symm
    -- Evaluating the `-u` inequality at `-x` removes both minus signs.
    have hnonpos : ⟪-x, -u⟫_ℝ ≤ 0 := hneg_closedCone (-x) hx_neg_mem
    simpa [inner_neg_left, inner_neg_right] using hnonpos

-- Proof sketch: combine the previous equality of the two polar cones with clause (iv), which
-- identifies their intersection with the orthogonal set of `C`.
/-- Proposition 6.24 (16): textbook clause (v). If `closure (cone C)` is symmetric, then the
positive polar cone of `C` equals the orthogonal set of `C`. -/
theorem positivePolar_eq_orthogonalSet_of_closure_cone_eq_neg {C : Set E}
    (hC_symm : closure (cone C) = -closure (cone C)) :
    positivePolar C = orthogonalSet C := by
  -- Replace the negative polar by the positive polar, then invoke clause (iv).
  calc
    positivePolar C = negativePolar C ∩ positivePolar C := by
      ext u
      constructor
      · intro hu
        have hneg : u ∈ negativePolar C := by
          simpa [negativePolar_eq_positivePolar_of_closure_cone_eq_neg hC_symm] using hu
        exact ⟨hneg, hu⟩
      · intro hu
        exact hu.2
    _ = orthogonalSet C := negativePolar_inter_positivePolar_eq_orthogonalSet C

end

end Set
