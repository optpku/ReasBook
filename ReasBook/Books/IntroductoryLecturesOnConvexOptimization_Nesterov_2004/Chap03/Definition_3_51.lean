/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_49
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set

universe u

section Ambient

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A vector `g` strictly separates the query point `xBar` from the feasible set `Q` by an affine
inequality `⟪g, x⟫ ≤ β < ⟪g, xBar⟫`. -/
def SeparatesByCuttingVector (Q : Set E) (xBar g : E) : Prop :=
  ∃ β : ℝ, (∀ x ∈ Q, inner ℝ g x ≤ β) ∧ β < inner ℝ g xBar

namespace SeparatesByCuttingVector

/-- A strict cutting vector puts the whole feasible set on the lower side of the returned affine
functional. -/
-- Proof sketch: unpack the separating level `β`; combine `⟪g, x⟫ ≤ β` on `Q` with
-- `β < ⟪g, xBar⟫` to obtain `⟪g, x⟫ ≤ ⟪g, xBar⟫`.
theorem subset_cuttingHalfspace {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) :
    Q ⊆ cuttingHalfspace xBar g := by
  rcases hsep with ⟨β, hβ, hlt⟩
  intro x hx
  exact le_trans (hβ x hx) (le_of_lt hlt)

/-- Over a nonempty feasible set, a strict cutting vector is nonzero. -/
theorem ne_zero {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) (hQ : Q.Nonempty) :
    g ≠ 0 := by
  rintro rfl
  rcases hsep with ⟨β, hβ, hlt⟩
  rcases hQ with ⟨x, hx⟩
  have hβ_nonneg : 0 ≤ β := by simpa using hβ x hx
  exact (not_lt_of_ge hβ_nonneg) (by simpa using hlt)

/-- Over a nonempty feasible set, a strict cutting vector yields the canonical Chapter 3
point-versus-set separation owner at the retained offset `⟪g, xBar⟫`. -/
theorem separatesPointFromWith_inner {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) (hQ : Q.Nonempty) :
    SeparatesPointFromWith Q xBar g (inner ℝ g xBar) :=
  (separatesPointFromWith_inner_iff).2
    ⟨hsep.ne_zero hQ, hsep.subset_cuttingHalfspace⟩

/-- Over a nonempty feasible set, a strict cutting vector also yields a strict affine-nesterovHyperplane
separator in the earlier Chapter 3 owner form. -/
theorem exists_strictlySeparatesPointFromWith {Q : Set E} {xBar g : E}
    (hsep : SeparatesByCuttingVector Q xBar g) (hQ : Q.Nonempty) :
    ∃ β : ℝ, StrictlySeparatesPointFromWith Q xBar g β := by
  have hg : g ≠ 0 := by
    rintro rfl
    rcases hsep with ⟨β, hβ, hlt⟩
    rcases hQ with ⟨x, hx⟩
    have hβ_nonneg : 0 ≤ β := by simpa using hβ x hx
    exact (not_lt_of_ge hβ_nonneg) (by simpa using hlt)
  rcases hsep with ⟨β, hβ, hlt⟩
  refine ⟨β, ?_⟩
  refine ⟨hg, ?_⟩
  · refine ⟨?_, Or.inr hlt⟩
    constructor
    · intro x hx
      exact hβ x hx
    · exact le_of_lt hlt

end SeparatesByCuttingVector

/-- A separation oracle for minimizing `f` over `Q` returns a subgradient at feasible query
points and a strict separating vector at infeasible query points. -/
structure ConvexMinimizationSeparationOracle (Q : Set E) (f : E → ℝ) where
  /-- The vector returned by the oracle at the query point. -/
  oracle : E → E
  /-- On feasible query points, the returned vector is a subgradient of `f`. -/
  subgradient_spec :
    ∀ ⦃xBar : E⦄, xBar ∈ Q →
      IsSubgradientAt (fun x ↦ (f x : WithTop ℝ)) xBar (oracle xBar)
  /-- On infeasible query points, the returned vector strictly separates the query point from
  `Q`. -/
  separating_spec :
    ∀ ⦃xBar : E⦄, xBar ∉ Q → SeparatesByCuttingVector Q xBar (oracle xBar)

namespace ConvexMinimizationSeparationOracle

variable {Q : Set E} {f : E → ℝ}

/-- A convex minimization separation oracle can be used as the returned query-to-vector map. -/
instance : CoeFun (ConvexMinimizationSeparationOracle Q f) (fun _ ↦ E → E) where
  coe oracle := oracle.oracle

/-- Evaluating a convex minimization separation oracle returns its query vector. -/
@[simp] theorem coe_apply
    (oracle : ConvexMinimizationSeparationOracle Q f) (xBar : E) :
    oracle xBar = oracle.oracle xBar :=
  rfl

/-- Forgetting the feasible-point subgradient branch turns a convex minimization separation oracle
into the earlier Chapter 3 feasibility separation oracle on `Q`. -/
def toSeparationOracle
    (oracle : ConvexMinimizationSeparationOracle Q f) (hQ : Q.Nonempty) :
    SeparationOracle Q :=
  let _ : DecidablePred (fun xBar : E ↦ xBar ∈ Q) := Classical.decPred _
  fun xBar ↦
    if hxBar : xBar ∈ Q then
      .feasible hxBar
    else
      .separatingVector
        (oracle.oracle xBar)
        hxBar
        ((oracle.separating_spec hxBar).separatesPointFromWith_inner hQ)

@[simp] theorem toSeparationOracle_of_mem
    (oracle : ConvexMinimizationSeparationOracle Q f) (hQ : Q.Nonempty)
    {xBar : E} (hxBar : xBar ∈ Q) :
    toSeparationOracle oracle hQ xBar = SeparationOracleAnswer.feasible hxBar := by
  classical
  simp [toSeparationOracle, hxBar]

@[simp] theorem toSeparationOracle_of_not_mem
    (oracle : ConvexMinimizationSeparationOracle Q f) (hQ : Q.Nonempty)
    {xBar : E} (hxBar : xBar ∉ Q) :
    ∃ hsep,
      toSeparationOracle oracle hQ xBar =
        SeparationOracleAnswer.separatingVector (oracle.oracle xBar) hxBar hsep := by
  classical
  refine ⟨(oracle.separating_spec hxBar).separatesPointFromWith_inner hQ, ?_⟩
  simp [toSeparationOracle, hxBar]

end ConvexMinimizationSeparationOracle

/-- Definition 3.51: a convex minimization problem with set constraint and separation oracle
consists of a convex real-valued objective on a real inner-product space, a bounded closed convex
feasible set with nonempty interior, and an oracle returning subgradients on feasible points and
strict separating vectors outside the feasible set. -/
structure ConvexMinimizationWithSeparationOracle
    (E : Type u) [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends SetConstrainedMinimizationProblem E where
  /-- The objective is convex on the whole ambient space. -/
  objective_convex : ConvexOn ℝ univ objective
  /-- The feasible set is bounded. -/
  feasibleSet_bounded : Bornology.IsBounded feasibleSet
  /-- The feasible set is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The feasible set has nonempty interior. -/
  feasibleSet_interior_nonempty : (interior feasibleSet).Nonempty
  /-- A separation oracle for the constrained minimization problem. -/
  oracle : ConvexMinimizationSeparationOracle feasibleSet objective

namespace ConvexMinimizationWithSeparationOracle

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex minimization problem with separation oracle can be used as its objective function. -/
instance : CoeFun (ConvexMinimizationWithSeparationOracle E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a convex minimization problem with separation oracle returns its objective value. -/
@[simp] theorem coe_apply
    (problem : ConvexMinimizationWithSeparationOracle E) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The feasible set is nonempty because a point in its interior is feasible. -/
-- Proof sketch: choose a point of `interior feasibleSet` and use `interior_subset`.
theorem feasibleSet_nonempty (problem : ConvexMinimizationWithSeparationOracle E) :
    problem.feasibleSet.Nonempty := by
  rcases problem.feasibleSet_interior_nonempty with ⟨x, hx⟩
  exact ⟨x, interior_subset hx⟩

/-- Forgetting the objective and feasible-point subgradient branch yields the earlier Chapter 3
feasibility problem with separation oracle on the same feasible set. -/
def toFeasibilityProblemWithSeparationOracle
    (problem : ConvexMinimizationWithSeparationOracle E) :
    FeasibilityProblemWithSeparationOracle E where
  feasibleSet := problem.feasibleSet
  feasibleSet_nonempty := problem.feasibleSet_nonempty
  feasibleSet_closed := problem.feasibleSet_closed
  feasibleSet_convex := problem.feasibleSet_convex
  oracle :=
    ConvexMinimizationSeparationOracle.toSeparationOracle
      problem.oracle
      problem.feasibleSet_nonempty

@[simp] theorem toFeasibilityProblemWithSeparationOracle_feasibleSet
    (problem : ConvexMinimizationWithSeparationOracle E) :
    problem.toFeasibilityProblemWithSeparationOracle.feasibleSet = problem.feasibleSet :=
  rfl

end ConvexMinimizationWithSeparationOracle

end Ambient

end
