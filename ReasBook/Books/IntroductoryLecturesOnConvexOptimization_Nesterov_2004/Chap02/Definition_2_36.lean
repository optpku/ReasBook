/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

/- Primary domain: constrained smooth strongly convex objectives on feasible sets in a real
Hilbert space.

Sampled owner-style declarations:
* `IsStrongConvexSmoothObjective`, `𝓢[μ, L]¹¹`, and `mem_S11_iff` in `Definition_2_17`;
* `ConvexC1SeminormSmoothOn` and `𝓕[L, p]¹¹(Q)` in `Theorem_2_5`;
* mathlib `StrongConvexOn`;
* `StrongConvexOnWith.lower_tangent_quadratic` in `Definition_2_14`.

Best owner abstraction:
* source-facing: the constrained textbook class `𝓢[μ, L]¹¹(Q)`;
* core/canonical: the conjunction
  `0 < μ ∧ μ ≤ L ∧ StrongConvexOn Q μ f ∧
    ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f`;
* bridge/view: the whole-space owner bridge
  `IsStrongConvexSmoothObjective.toConstrainedStrongConvexSmooth_univ`.

Primitive data:
* the feasible set `Q`;
* the parameters `μ` and `L`;
* the canonical strong-convex owner `StrongConvexOn Q μ f`;
* the canonical smooth owner
  `ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f`.

Derived API:
* positivity and parameter comparison;
* convexity of `Q`, `C¹` regularity on `Q`, the ambient gradient witnesses on `Q`, and the
  gradient-Lipschitz bound on `Q`;
* the upper and lower tangent quadratic inequalities.

Definition 2.36 therefore uses the chapter's `𝓢[μ, L]¹¹` notation surface directly, specialized
from the whole-space class to the feasible-set class on the same finite-dimensional owner layer as
`ConvexC1SeminormSmoothOn`, instead of introducing a parallel wrapper predicate. -/

/-- The constrained smooth strongly convex class as a set of objectives on `Q`. The source-facing
surface is the notation `𝓢[μ, L]¹¹(Q)`. -/
abbrev S11On (μ L : ℝ) (Q : Set E) : Set (E → ℝ) :=
  setOf (fun f ↦
    0 < μ ∧
      μ ≤ L ∧
      StrongConvexOn Q μ f ∧
      ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f)

scoped[StrongConvexSmooth] notation "𝓢[" μ ", " L "]¹¹(" Q ")" =>
  S11On μ L Q

/-- The constrained notation `𝓢[μ, L]¹¹(Q)` is the source-facing set view of the canonical
strong-convex/smooth owner data on `Q`. -/
theorem mem_S11On_iff {μ L : ℝ} {Q : Set E} {f : E → ℝ} :
    f ∈ 𝓢[μ, L]¹¹(Q) ↔
      0 < μ ∧
        μ ≤ L ∧
        StrongConvexOn Q μ f ∧
        ConvexC1SeminormSmoothOn (normSeminorm ℝ E) (Real.toNNReal L) Q f :=
  Iff.rfl

namespace StrongConvexSmoothOn

variable {μ L : ℝ} {Q : Set E} {f : E → ℝ}

/-- Membership in `𝓢[μ, L]¹¹(Q)` forces positivity of the strong-convexity parameter. -/
theorem mu_pos (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    0 < μ := by
  rcases hf with ⟨hμ, _, _, _⟩
  exact hμ

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes the parameter relation `μ ≤ L`. -/
theorem mu_le_L (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    μ ≤ L := by
  rcases hf with ⟨_, hμL, _, _⟩
  exact hμL

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes the reused Chapter 2 smooth owner on `Q`. -/
theorem smooth (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    ConvexC1SeminormSmoothOn p (Real.toNNReal L) Q f := by
  rcases hf with ⟨_, _, _, hsmooth⟩
  exact hsmooth

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes `C¹` regularity on `Q`. -/
theorem contDiffOn (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    ContDiffOn ℝ 1 f Q := by
  exact (StrongConvexSmoothOn.smooth hf).contDiffOn

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes strong convexity on `Q`. -/
theorem strongConvexOn (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    StrongConvexOn Q μ f := by
  rcases hf with ⟨_, _, hstrong, _⟩
  exact hstrong

/-- A function in `𝓢[μ, L]¹¹(Q)` has a convex feasible set `Q`. -/
theorem convex (hf : f ∈ 𝓢[μ, L]¹¹(Q)) :
    Convex ℝ Q := by
  rcases strongConvexOn hf with ⟨hQ_convex, _⟩
  exact hQ_convex

/-- Membership in `𝓢[μ, L]¹¹(Q)` includes the stated ambient-gradient Lipschitz bound on `Q`. -/
theorem gradient_lipschitz
    (hf : f ∈ 𝓢[μ, L]¹¹(Q))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖ := by
  have hL : 0 ≤ L := le_trans (StrongConvexSmoothOn.mu_pos hf).le (StrongConvexSmoothOn.mu_le_L hf)
  simpa [Real.toNNReal_of_nonneg hL, Seminorm.dualNorm_normSeminorm_eq_norm] using
    (StrongConvexSmoothOn.smooth hf).dualNorm_gradient_sub_le hx hy

/-- The original upper tangent-plane inequality on `Q` is a derived consequence of the local
`𝓢[μ, L]¹¹(Q)` owner data. -/
theorem upper_tangent_quadratic
    (hf : f ∈ 𝓢[μ, L]¹¹(Q))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) + (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  have hL : 0 ≤ L := le_trans (StrongConvexSmoothOn.mu_pos hf).le (StrongConvexSmoothOn.mu_le_L hf)
  have hbound :
      f y - f x - inner ℝ (∇ f x) (y - x) ≤
        ((Real.toNNReal L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    simpa using (StrongConvexSmoothOn.smooth hf).tangentErrorBounds.upperBound hx hy
  have hbound' :
      f y - f x - inner ℝ (∇ f x) (y - x) ≤
        (L / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    simpa [Real.toNNReal_of_nonneg hL] using hbound
  have hbound'' :
      f y - f x - inner ℝ (∇ f x) (y - x) ≤
        (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    simpa [norm_sub_rev] using hbound'
  linarith

/-- The original lower tangent-plane inequality on `Q` is a derived consequence of the owner
strong-convexity abstraction together with `C¹` regularity. -/
  theorem lower_tangent_quadratic
    (hf : f ∈ 𝓢[μ, L]¹¹(Q))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Project the strong-convexity owner from the constrained `𝓢[μ, L]¹¹(Q)` data.
  have hstrong : StrongConvexOn Q μ f := StrongConvexSmoothOn.strongConvexOn hf
  -- The smooth owner supplies the ambient gradient witness needed by the tangent inequality.
  have hgrad : HasGradientAt f (∇ f x) x := (StrongConvexSmoothOn.smooth hf).hasGradientAt hx
  -- Apply the canonical lower tangent theorem at the feasible pair `(x, y)`.
  simpa using
    StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt hstrong hx hy hgrad

end StrongConvexSmoothOn

namespace SetConstrainedMinimizationProblem

variable {μ L : ℝ}

/-- Definition 2.36: a constrained smooth strongly convex minimization problem with parameters `μ`
and `L` is a set-constrained minimization problem on a real Hilbert space whose feasible set is
nonempty and closed and whose objective belongs to `𝓢^{1,1}_{μ,L}(Q)` on that feasible set. -/
structure IsConstrainedStrongConvexSmooth
    (problem : SetConstrainedMinimizationProblem E)
    (μ L : ℝ) : Prop where
  nonempty : problem.feasibleSet.Nonempty
  isClosed : IsClosed problem.feasibleSet
  objective_mem : problem.objective ∈ 𝓢[μ, L]¹¹(problem.feasibleSet)

variable {problem : SetConstrainedMinimizationProblem E}

/-- The feasible set of a constrained smooth strongly convex problem is convex. -/
theorem IsConstrainedStrongConvexSmooth.convex
    (h : problem.IsConstrainedStrongConvexSmooth μ L) :
    Convex ℝ problem.feasibleSet := by
  exact StrongConvexSmoothOn.convex h.objective_mem

/- Definition 2.36 is therefore expressed by a value
`problem : SetConstrainedMinimizationProblem E` together with a proof
`h : problem.IsConstrainedStrongConvexSmooth μ L`.

A global minimizer is expressed directly by the canonical predicate
`IsMinOn problem.objective problem.feasibleSet x`; no additional wrapper declaration is needed
here. -/

end SetConstrainedMinimizationProblem

namespace IsStrongConvexSmoothObjective

variable {μ L : ℝ} {f : E → ℝ}

/-- A whole-space strongly convex smooth objective canonically induces the constrained owner
problem on feasible set `Set.univ` on the finite-dimensional Chapter 2 owner layer. -/
-- Proof sketch: package `f` as the ambient constrained problem on `Set.univ`. The set geometry is
-- immediate, while the objective-side constrained smooth/strongly-convex data come from the
-- whole-space owner hypothesis together with `hf.mu_le_L`.
theorem toConstrainedStrongConvexSmooth_univ [Nontrivial E]
    (hf : IsStrongConvexSmoothObjective μ L f) :
    (SetConstrainedMinimizationProblem.unconstrained f).IsConstrainedStrongConvexSmooth
      μ L := by
  exact
    ⟨Set.univ_nonempty, isClosed_univ,
      ⟨hf.mu_pos, hf.mu_le_L, hf.strongConvexOn, hf.toConvexC1SeminormSmooth.toOn⟩⟩

end IsStrongConvexSmoothObjective
