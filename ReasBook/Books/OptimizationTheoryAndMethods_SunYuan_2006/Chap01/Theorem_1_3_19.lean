/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_14

-- Domain sampling:
-- * primary domain: Hessian lower bounds, strong convexity, and anchored lower level sets in
--   real inner-product spaces;
-- * inspected owner declarations:
--   - `StrongConvexOn` from Chapter 1 Definition 1.3.6 / mathlib's strong-convexity API;
--   - `exists_strongConvexOn_iff_iteratedFDeriv_uniformly_pos` from Chapter 1 Theorem 1.3.14;
--   - `ConvexOn.convex_le` from mathlib's convex sublevel-set API;
--   - `IsClosed.isClosed_le` from mathlib's closed sublevel-set API;
-- * best owner abstraction: the primitive Hessian-bound owners
--   `HasHessianLowerBoundOn` / `HasHessianUpperBoundOn`, with
--   `HasLowerLevelHessianLowerBound` / `HasLowerLevelHessianUpperBound` as the source-facing
--   lower-level-set specializations;
-- * layer targeted here: `source-facing`, with the convexity/boundedness conclusions routed
--   through the existing canonical `StrongConvexOn` bridge rather than through a parallel local
--   wrapper.
-- Primitive data vs derived API:
-- * primitive data: a set `S`, a function `f`, and ambient Hessian quadratic-form bounds on `S`;
-- * derived API: the lower-level-set specializations, relative/ambient closedness of anchored
--   lower level sets, and the convexity/boundedness consequences obtained from the source-facing
--   lower-level-set Hessian owner.

universe u

section LowerLevelSet

variable {E : Type u}

/-- The lower level set of `f` on `S` at the value `f x0`. -/
abbrev lowerLevelSetOn (S : Set E) (f : E → ℝ) (x0 : E) : Set E :=
  {y | y ∈ S ∧ f y ≤ f x0}

/-- Membership in `lowerLevelSetOn S f x0` means belonging to `S` and lying below the level
`f x0`. -/
@[simp] theorem mem_lowerLevelSetOn (S : Set E) (f : E → ℝ) (x0 y : E) :
    y ∈ lowerLevelSetOn S f x0 ↔ y ∈ S ∧ f y ≤ f x0 :=
  Iff.rfl

/-- If `x0 ∈ S`, then the base point belongs to its anchored lower level set. -/
theorem self_mem_lowerLevelSetOn (S : Set E) (f : E → ℝ) {x0 : E} (hx0 : x0 ∈ S) :
    x0 ∈ lowerLevelSetOn S f x0 :=
  ⟨hx0, le_rfl⟩

end LowerLevelSet

section HessianBounds

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `HasHessianLowerBoundOn S f m` records the quadratic-form lower Hessian bound
`m * ‖u‖ ^ 2 ≤ (iteratedFDeriv ℝ 2 f x) ![u, u]` for all `x ∈ S` and `u : E`. -/
def HasHessianLowerBoundOn (S : Set E) (f : E → ℝ) (m : ℝ) : Prop :=
  ∀ x ∈ S, ∀ u : E, m * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u]

/-- `HasHessianUpperBoundOn S f M` records the quadratic-form upper Hessian bound
`(iteratedFDeriv ℝ 2 f x) ![u, u] ≤ M * ‖u‖ ^ 2` for all `x ∈ S` and `u : E`. -/
def HasHessianUpperBoundOn (S : Set E) (f : E → ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ S, ∀ u : E, (iteratedFDeriv ℝ 2 f x) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ)

/-- Restricting an ambient Hessian lower bound to a subset preserves the bound. -/
theorem HasHessianLowerBoundOn.mono
    {S T : Set E} {f : E → ℝ} {m : ℝ}
    (h : HasHessianLowerBoundOn S f m) (hTS : T ⊆ S) :
    HasHessianLowerBoundOn T f m :=
  fun x hx u ↦ h x (hTS hx) u

/-- Restricting an ambient Hessian upper bound to a subset preserves the bound. -/
theorem HasHessianUpperBoundOn.mono
    {S T : Set E} {f : E → ℝ} {M : ℝ}
    (h : HasHessianUpperBoundOn S f M) (hTS : T ⊆ S) :
    HasHessianUpperBoundOn T f M :=
  fun x hx u ↦ h x (hTS hx) u

/-- `HasLowerLevelHessianLowerBound S f x0 m` is the source-facing specialization of
`HasHessianLowerBoundOn` to the anchored lower level set `lowerLevelSetOn S f x0`. -/
abbrev HasLowerLevelHessianLowerBound
    (S : Set E) (f : E → ℝ) (x0 : E) (m : ℝ) : Prop :=
  HasHessianLowerBoundOn (lowerLevelSetOn S f x0) f m

/-- `HasLowerLevelHessianUpperBound S f x0 M` is the source-facing specialization of
`HasHessianUpperBoundOn` to the anchored lower level set `lowerLevelSetOn S f x0`. -/
abbrev HasLowerLevelHessianUpperBound
    (S : Set E) (f : E → ℝ) (x0 : E) (M : ℝ) : Prop :=
  HasHessianUpperBoundOn (lowerLevelSetOn S f x0) f M

end HessianBounds

/-- Chapter01 Theorem 1.3.19 (1): the anchored lower level set is closed as a subset of `S`
whenever `f` is continuous on `S`. The stronger Hessian hypotheses belong to the later convexity
and boundedness consequences, not to this relative-closedness statement. -/
theorem isClosed_lowerLevelSetOn
    {E : Type u} [TopologicalSpace E]
    (S : Set E) (f : E → ℝ) (x0 : E)
    (hCont : ContinuousOn f S) :
    IsClosed ({y : S | f y ≤ f x0} : Set S) := sorry

/-- Auxiliary bridge: if `S` is closed, then `lowerLevelSetOn S f x0` is closed in the ambient
space. -/
theorem isClosed_lowerLevelSetOn_of_isClosed
    {E : Type u} [TopologicalSpace E]
    (S : Set E) (f : E → ℝ) (x0 : E)
    (hS_closed : IsClosed S) (hCont : ContinuousOn f S) :
    IsClosed (lowerLevelSetOn S f x0) := sorry

section Theorem1319

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Chapter01 Theorem 1.3.19 (2): if `S` is open and convex, `f` is `C²` on `S`, and the
Hessian quadratic form has a uniform positive lower bound on the anchored lower level set
`lowerLevelSetOn S f x0`, then that anchored lower level set is convex. -/
theorem convex_lowerLevelSetOn_of_hessian_uniformly_pos
    (S : Set E) (f : E → ℝ) (x0 : E)
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S)
    (hLower : ∃ m > 0, HasLowerLevelHessianLowerBound S f x0 m) :
    Convex ℝ (lowerLevelSetOn S f x0) := sorry

/-- Chapter01 Theorem 1.3.19 (3): if `S` is open and convex, `f` is `C²` on `S`, the Hessian
quadratic form has a uniform positive lower bound on the anchored lower level set
`lowerLevelSetOn S f x0`, and `x0 ∈ S`, then that anchored lower level set is bounded. -/
theorem bounded_lowerLevelSetOn_of_hessian_uniformly_pos
    (S : Set E) (f : E → ℝ) (x0 : E)
    (hx0 : x0 ∈ S)
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S)
    (hLower : ∃ m > 0, HasLowerLevelHessianLowerBound S f x0 m) :
    Bornology.IsBounded (lowerLevelSetOn S f x0) := sorry

end Theorem1319
