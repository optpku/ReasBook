/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module
open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped ConvexAnalysis BInducedNorm

universe u

/- Definition 6.2 lies in the chapter's Fenchel-smoothing / extended-real convex-analysis domain.

Sampled owner-style declarations:
- `fenchelConjugate` in `Chap06/Definition_6_1`, the chapter owner for Fenchel suprema in `EReal`
- `dom` in `Chap03/Definition_3_1_1_2`, the project owner for the effective domain of an
  extended-real-valued function
- `LinearMap.BilinForm.dualNorm` in `Chap04/Definition_4_3_4`, the Chapter 4 finite-dimensional
  owner for bilinear-form-induced support-function norms on `Module.Dual ℝ E`
- `IsMaxOn` in mathlib, the canonical attained-maximum owner used to recover textbook `max`
  formulas from supremum owners

Best owner abstraction:
- source-facing: `fenchelSmoothApproximation`
- core/canonical: `fenchelConjugate f`, `dom (fenchelConjugate f)`, and
  `LinearMap.BilinForm.dualNorm`
- bridge/view: the attained-maximum companions
  `fenchelSmoothApproximation_eq_maximand_of_isMaxOn` and
  `fenchelSmoothApproximation_toReal_eq_of_isMaxOn`

Primitive data:
- `B : BilinForm ℝ E`
- `[Fact B.toQuadraticMap.PosDef]`
- `f : E → EReal`
- `μ : NNReal`

Derived API:
- `fenchelSmoothApproximationMaximand`
- `fenchelSmoothApproximation_apply`
- `fenchelSmoothApproximation_toReal_eq_of_isMaxOn`

Source/core/bridge triage:
- source-facing: `fenchelSmoothApproximation`
- core/canonical: `dom`, `fenchelConjugate`, `LinearMap.BilinForm.dualNorm`
- bridge/view: the attained-maximum theorems turning the `EReal` supremum owner back into the
  textbook real-valued maximization formula when a maximizer exists

The source-facing object is the smoothing attached to a primal function through its Fenchel
conjugate. The previous raw-`fStar` surface promoted that derived dual function to a second public
owner. This refinement keeps `fenchelConjugate f` as the canonical dual input and defines the
smoothing directly from `f`. The owner remains `EReal`-valued so empty or unbounded dual fibers
retain their correct order-theoretic value, while the companion attained-maximum theorems recover
the textbook `f_μ : E → ℝ` / `max` formula on the finite-value regime.
-/

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- The quadratically regularized affine functional used in the Nesterov smoothing formula,
built from the Fenchel conjugate of `f` and regularized by the Chapter 4 dual-norm owner
`‖s‖[B,*]`. -/
def fenchelSmoothApproximationMaximand
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal)
    (x : E) (s : Dual ℝ E) : EReal :=
  (s x : EReal) - fenchelConjugate f s - (((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ)

/-- On `dom (fenchelConjugate f)`, the regularized maximand is the coercion of the corresponding
real-valued textbook expression. -/
theorem fenchelSmoothApproximationMaximand_eq_coe
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f)) :
    fenchelSmoothApproximationMaximand B f μ x s =
      (((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ) : EReal) := by
  rw [fenchelSmoothApproximationMaximand]
  rw [show fenchelConjugate f s = ((fenchelConjugate f s).toReal : EReal) by
    exact (EReal.coe_toReal hs.1 hs.2).symm]
  norm_num

/-- Definition 6.2: the smooth approximation `f_μ` attached to `f` is the supremum over
`dom (fenchelConjugate f)` of the affine functional
`s ↦ ⟪s, x⟫ - (fenchelConjugate f) s`, regularized by
`(μ / 2) * ‖s‖[B,*]^2` for a nonnegative smoothing parameter `μ`. The owner lives in `EReal`, so
empty or unbounded supremum sets retain their correct extended-real values; the companion theorem
`fenchelSmoothApproximation_toReal_eq_of_isMaxOn` recovers the textbook real-valued maximum
whenever the supremum is attained on `dom (fenchelConjugate f)`. -/
def fenchelSmoothApproximation
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) : E → EReal :=
  fun x ↦
    sSup (fenchelSmoothApproximationMaximand B f μ x '' dom (fenchelConjugate f))

-- Proof sketch: unfold `fenchelSmoothApproximation`; the right-hand side is exactly the defining
-- supremum formula over `dom (fenchelConjugate f)`.
/-- Evaluating the smooth approximation recovers the defining regularized supremum over
`dom (fenchelConjugate f)`. -/
@[simp] theorem fenchelSmoothApproximation_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) :
    fenchelSmoothApproximation B f μ x =
      sSup (fenchelSmoothApproximationMaximand B f μ x '' dom (fenchelConjugate f)) :=
  rfl

private theorem fenchelSmoothApproximationMaximand_isGreatest
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    IsGreatest
      (fenchelSmoothApproximationMaximand B f μ x '' dom (fenchelConjugate f))
      (fenchelSmoothApproximationMaximand B f μ x s) := by
  refine ⟨⟨s, hs, rfl⟩, ?_⟩
  intro y hy
  rcases hy with ⟨t, ht, rfl⟩
  exact (isMaxOn_iff.mp hmax) t ht

/-- If the dual supremum is attained at `s`, then the smooth approximation equals that attained
maximand value. -/
theorem fenchelSmoothApproximation_eq_maximand_of_isMaxOn
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    fenchelSmoothApproximation B f μ x =
      fenchelSmoothApproximationMaximand B f μ x s := by
  rw [fenchelSmoothApproximation_apply]
  rw [(fenchelSmoothApproximationMaximand_isGreatest B f μ x hs hmax).csSup_eq]

/-- Under the textbook attained-maximum hypothesis, `f_μ(x)` is the displayed real-valued
maximum `⟪s, x⟫ - f^*(s) - (μ / 2) ‖s‖[B,*]^2`. -/
theorem fenchelSmoothApproximation_eq_coe_of_isMaxOn
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    fenchelSmoothApproximation B f μ x =
      (((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ) : EReal) := by
  rw [fenchelSmoothApproximation_eq_maximand_of_isMaxOn B f μ x hs hmax]
  rw [fenchelSmoothApproximationMaximand_eq_coe B f μ x hs]

/-- Under the textbook attained-maximum hypothesis, the `EReal` owner recovers the stated
real-valued formula for `f_μ(x)`. -/
theorem fenchelSmoothApproximation_toReal_eq_of_isMaxOn
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    (fenchelSmoothApproximation B f μ x).toReal =
      (s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 := by
  simpa using
    congrArg EReal.toReal (fenchelSmoothApproximation_eq_coe_of_isMaxOn B f μ x hs hmax)
