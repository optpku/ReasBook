/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section Ambient

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.49 lies in the convex-feasibility separation-oracle domain.

Sampled owner-style declarations:
- `SeparatesPointFromWith` in `Definition_3_1_4_1`, the chapter owner for a nonzero affine
  separator between a point and a set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of an
  ambient feasible set together with a real-valued objective;
- `ConvexMinimizationWithSeparationOracle` in `Definition_3_51`, the later source-facing owner for
  constrained convex minimization with a stricter infeasible-query oracle.

Best owner abstraction:
- source-facing owner: `FeasibilityProblemWithSeparationOracle E`;
- core separating witness for an infeasible query: `SeparatesPointFromWith S xBar g ⟪g, xBar⟫`;
- derived callable owner view: `SeparationOracle S`.

Primitive data:
- the feasible set `S`;
- its nonempty / closed / convex witnesses;
- the oracle reply map.

Derived API:
- the retained half-space cut `cuttingHalfspace xBar g` attached to a separating reply;
- the bridge between that cut and the upstream point/set separation owner;
- its canonical nonzero-vector bridge to `AffineHyperplane.closedLowerHalfspace`;
- its closedness and convexity lemmas;
- no extra callable wrapper, since `SeparationOracle S` is already the direct query-to-answer map.

Because Definition 3.49 is objective-free, `SetConstrainedMinimizationProblem` is only a possible
bridge/view downstream, not the public owner here. -/

/-- The retained half-space cut determined by a query point `xBar` and vector `g`,
equivalently `{x | 0 ≤ ⟪g, xBar - x⟫}`. -/
def cuttingHalfspace (xBar g : E) : Set E :=
  {x | inner ℝ g x ≤ inner ℝ g xBar}

/-- Membership in the retained cut is exactly the textbook inequality
`0 ≤ ⟪g, xBar - x⟫`. -/
@[simp] theorem mem_cuttingHalfspace_iff {xBar g x : E} :
    x ∈ cuttingHalfspace xBar g ↔ 0 ≤ inner ℝ g (xBar - x) := by
  simp [cuttingHalfspace, inner_sub_right, sub_nonneg]

/-- For a nonzero cutting vector, the retained cut is exactly the closed lower half-space of the
earlier affine-nesterovHyperplane owner with offset `⟪g, xBar⟫`. -/
theorem cuttingHalfspace_eq_closedLowerHalfspace {xBar g : E} (hg : g ≠ 0) :
    cuttingHalfspace xBar g =
      (⟨g, hg, inner ℝ g xBar⟩ : AffineHyperplane E).closedLowerHalfspace :=
  rfl

/-- The retained cut is closed. -/
theorem cuttingHalfspace_closed (xBar g : E) :
    IsClosed (cuttingHalfspace xBar g) := by
  simpa [cuttingHalfspace] using
    (isClosed_le (continuous_const.inner continuous_id) continuous_const)

/-- The retained cut is convex. -/
theorem cuttingHalfspace_convex (xBar g : E) :
    Convex ℝ (cuttingHalfspace xBar g) := by
  simpa [cuttingHalfspace, innerₗ_apply_apply] using
    (convex_halfSpace_le (LinearMap.isLinear (innerₗ E g)) (inner ℝ g xBar))

/-- The retained-cut formulation `S ⊆ cuttingHalfspace xBar g` is exactly the upstream
point-versus-set separation owner specialized to the canonical offset `⟪g, xBar⟫`. -/
theorem separatesPointFromWith_inner_iff {S : Set E} {xBar g : E} :
    SeparatesPointFromWith S xBar g (inner ℝ g xBar) ↔
      g ≠ 0 ∧ S ⊆ cuttingHalfspace xBar g := by
  constructor
  · intro hsep
    refine ⟨hsep.ne_zero, ?_⟩
    intro x hx
    simpa [cuttingHalfspace] using hsep.le_offset hx
  · rintro ⟨hg, hcut⟩
    refine ⟨hg, ?_⟩
    constructor
    · simpa [cuttingHalfspace] using hcut
    · simp [AffineHyperplane.closedUpperHalfspace]

/-- A separation-oracle answer at `xBar` either certifies feasibility or, on an infeasible query,
returns a genuine separating vector in the chapter's canonical point/set separation sense. -/
inductive SeparationOracleAnswer (S : Set E) (xBar : E) where
  /-- The oracle certifies that the query point already lies in the feasible set. -/
  | feasible : xBar ∈ S → SeparationOracleAnswer S xBar
  /-- The oracle returns a vector `g` witnessing that the infeasible query point `xBar` is
  separated from `S` by the retained cut `⟪g, x⟫ ≤ ⟪g, xBar⟫`. -/
  | separatingVector :
      (g : E) →
      xBar ∉ S →
      SeparatesPointFromWith S xBar g (inner ℝ g xBar) →
      SeparationOracleAnswer S xBar

namespace SeparationOracleAnswer

/-- The observable part of a separation-oracle answer: `none` means the oracle certified the
query point feasible, while `some g` records the separating vector returned on an infeasible
query. -/
def oracleReply {S : Set E} {xBar : E} (answer : SeparationOracleAnswer S xBar) : Option E :=
  match answer with
  | .feasible _ => none
  | .separatingVector g _ _ => some g

@[simp] theorem oracleReply_feasible {S : Set E} {xBar : E} (hxBar : xBar ∈ S) :
    (SeparationOracleAnswer.feasible hxBar).oracleReply = (none : Option E) :=
  rfl

@[simp] theorem oracleReply_separatingVector {S : Set E} {xBar g : E}
    (hxBar : xBar ∉ S)
    (hsep : SeparatesPointFromWith S xBar g (inner ℝ g xBar)) :
    (SeparationOracleAnswer.separatingVector g hxBar hsep).oracleReply = some g :=
  rfl

/-- A separating answer cuts away the infeasible query point while keeping the feasible set in
the retained half-space. -/
theorem separatingVector_subset_cuttingHalfspace {S : Set E} {xBar g : E}
    (hsep : SeparatesPointFromWith S xBar g (inner ℝ g xBar)) :
    S ⊆ cuttingHalfspace xBar g :=
  (separatesPointFromWith_inner_iff.mp hsep).2

end SeparationOracleAnswer

/-- A separation oracle for `S` answers each query point by either certifying membership in `S`
or producing a separating vector. -/
abbrev SeparationOracle (S : Set E) : Type u :=
  ∀ xBar : E, SeparationOracleAnswer S xBar

end Ambient

section Ambient

variable (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 3.49: a feasibility problem with separation oracle consists of a nonempty closed
convex set `S` in a real inner-product space together with a separation oracle that, for every
query point `xBar`, either certifies `xBar ∈ S` or, when `xBar ∉ S`, returns a nonzero vector
`g` that separates `xBar` from `S` by the retained-cut inequality `⟪g, xBar - x⟫ ≥ 0` for all
`x ∈ S`. Specializing `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` formulation.
Solving the feasibility problem means producing a point of `S`. -/
structure FeasibilityProblemWithSeparationOracle where
  /-- The feasible set `S` in the ambient space. -/
  feasibleSet : Set E
  /-- The feasible set is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- A separation oracle for the feasible set. -/
  oracle : SeparationOracle feasibleSet

namespace FeasibilityProblemWithSeparationOracle

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The underlying Chapter 1 constrained-problem owner with the same feasible set and the
constant-zero objective. This is only a bridge/view: the source-facing owner remains the
feasibility problem together with its separation oracle. -/
def toSetConstrainedMinimizationProblem
    (problem : FeasibilityProblemWithSeparationOracle E) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := fun _ ↦ 0

/-- A feasibility problem with separation oracle coerces to its feasible set. -/
instance : Coe (FeasibilityProblemWithSeparationOracle E) (Set E) where
  coe problem := problem.feasibleSet

/-- A feasibility problem with separation oracle can be used as the membership predicate of its
feasible set. -/
instance : Membership E (FeasibilityProblemWithSeparationOracle E) where
  mem problem x := x ∈ problem.feasibleSet

/-- Membership in the coerced feasible set of a feasibility problem is exactly feasibility in its
stored set `S`. -/
@[simp] theorem mem_coe
    {problem : FeasibilityProblemWithSeparationOracle E}
    {x : E} :
    x ∈ (problem : Set E) ↔ x ∈ problem.feasibleSet :=
  Iff.rfl

/-- Membership in a feasibility problem is exactly membership in its feasible set `S`. -/
@[simp] theorem mem_iff
    {problem : FeasibilityProblemWithSeparationOracle E}
    {x : E} :
    x ∈ problem ↔ x ∈ problem.feasibleSet :=
  by rfl

/-- The bridge to the generic constrained-problem owner keeps the original feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : FeasibilityProblemWithSeparationOracle E) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- Evaluating the bridged constrained problem returns the constant zero objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : FeasibilityProblemWithSeparationOracle E)
    (x : E) :
    problem.toSetConstrainedMinimizationProblem x = 0 :=
  rfl

/-- Feasibility in the bridged constrained problem is exactly feasibility in the original
problem. -/
@[simp] theorem mem_toSetConstrainedMinimizationProblem_feasibleSet_iff
    {problem : FeasibilityProblemWithSeparationOracle E}
    {x : E} :
    x ∈ problem.toSetConstrainedMinimizationProblem.feasibleSet ↔ x ∈ problem.feasibleSet :=
  Iff.rfl

end FeasibilityProblemWithSeparationOracle

end Ambient
