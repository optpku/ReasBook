/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Algorithm 6.1 lies in the chapter's composite convex optimization / similar-triangles domain.

Sampled owner-style declarations:
- `CompositeConvexMinimizationProblem` in `Chap03/Definition_3_21`, the chapter owner of a
  closed feasible set together with a smooth convex term and a closed convex regularizer;
- `CompositeLipschitzGradientModel` and
  `CompositeLipschitzGradientModel.auxiliaryObjective` in `Chap06/Definition_6_8`, the chapter
  owner that adds the chosen gradient field, Lipschitz constant, prox-function data, and
  tractable prox subproblems;
- `SimilarTrianglesMethod` in this file, which organizes first-order algorithm iterates as data
  over a canonical composite problem owner rather than re-declaring the ambient problem in each
  algorithm structure.

Best owner abstraction:
- source-facing: `SimilarTrianglesMethod`;
- core/canonical: `CompositeLipschitzGradientModel E`;
- bridge/view: the explicit interpolation and estimating-function recursion formulas below.

Primitive data:
- a composite Lipschitz-gradient model `model`, which already owns the feasible set, smooth term,
  regularizer, gradient, curvature constant, and prox-function;
- a starting point `x0 : model.feasibleSet`;
- the iterate sequence `x`, the minimizing sequence `v`, and the estimating functions `φ`;
- the initialization and recursion laws of Algorithm 6.1.

Derived API:
- feasibility/closedness/convexity/prox data inherited from `model`, rather than re-stored in the
  algorithm structure;
- the interpolation point `y_k`;
- the owner-level feasibility surface `x_k ∈ Q` and `y_k ∈ Q`;
- the estimating-function update formula specialized to the owner model.

Source/core/bridge triage:
- source-facing: `SimilarTrianglesMethod`;
- core/canonical: `CompositeLipschitzGradientModel E`;
- bridge/view: `similarTrianglesInterpolationPoint`, `similarTrianglesEstimatingUpdate`, and the
  derived namespace API below.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The interpolation coefficient `(k + 1) / 2` used in the estimating-function update of the
method of similar triangles. -/
def similarTrianglesEstimatingWeight (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) / 2

/-- Expanding `similarTrianglesEstimatingWeight` recovers the coefficient `(k + 1) / 2`. -/
-- Proof sketch: unfold `similarTrianglesEstimatingWeight`.
theorem similarTrianglesEstimatingWeight_def (k : ℕ) :
    similarTrianglesEstimatingWeight k = ((k : ℝ) + 1) / 2 :=
  rfl

/-- The interpolation point `y_k = (k / (k + 2)) x_k + (2 / (k + 2)) v_k` used by the method of
similar triangles. -/
def similarTrianglesInterpolationPoint (k : ℕ) (xk vk : E) : E :=
  (((k : ℝ) / ((k : ℝ) + 2)) • xk) + (((2 : ℝ) / ((k : ℝ) + 2)) • vk)

/-- Expanding `similarTrianglesInterpolationPoint` gives the textbook convex combination defining
`y_k`. -/
-- Proof sketch: unfold `similarTrianglesInterpolationPoint`.
theorem similarTrianglesInterpolationPoint_def (k : ℕ) (xk vk : E) :
    similarTrianglesInterpolationPoint k xk vk =
      (((k : ℝ) / ((k : ℝ) + 2)) • xk) + (((2 : ℝ) / ((k : ℝ) + 2)) • vk) :=
  rfl

/-- The textbook interpolation point is the affine line-map point with parameter `2 / (k + 2)`.
-/
theorem similarTrianglesInterpolationPoint_eq_lineMap (k : ℕ) (xk vk : E) :
    similarTrianglesInterpolationPoint k xk vk =
      AffineMap.lineMap xk vk ((2 : ℝ) / ((k : ℝ) + 2)) := by
  rw [AffineMap.lineMap_apply_module, similarTrianglesInterpolationPoint]
  have hk :
      1 - (2 : ℝ) / ((k : ℝ) + 2) = (k : ℝ) / ((k : ℝ) + 2) := by
    field_simp
    ring
  simp [hk]

/-- The estimating-function update
`φ_{k+1}(x) = φ_k(x) + ((k + 1) / 2) [f(y_k) + ⟨∇ f(y_k), x - y_k⟩ + Ψ(x)]`
for the method of similar triangles, written over the chapter's canonical composite
Lipschitz-gradient owner. -/
def similarTrianglesEstimatingUpdate
    (model : CompositeLipschitzGradientModel E) (φk : E → WithTop ℝ) (k : ℕ) (yk : E) :
    E → WithTop ℝ :=
  fun x ↦
    φk x +
      (((similarTrianglesEstimatingWeight k *
          (model.smoothPart yk + model.smoothGradient yk (x - yk)) : ℝ) : WithTop ℝ) +
        (similarTrianglesEstimatingWeight k : WithTop ℝ) * model.nonsmoothPart x)

/-- Evaluating `similarTrianglesEstimatingUpdate` recovers the affine lower model of `f` at `y_k`
plus the weighted nonsmooth term `Ψ(x)`. -/
-- Proof sketch: unfold `similarTrianglesEstimatingUpdate`.
theorem similarTrianglesEstimatingUpdate_apply
    (model : CompositeLipschitzGradientModel E) (φk : E → WithTop ℝ) (k : ℕ) (yk x : E) :
    similarTrianglesEstimatingUpdate model φk k yk x =
      φk x +
        (((similarTrianglesEstimatingWeight k *
            (model.smoothPart yk + model.smoothGradient yk (x - yk)) : ℝ) : WithTop ℝ) +
          (similarTrianglesEstimatingWeight k : WithTop ℝ) * model.nonsmoothPart x) := by
  simp [similarTrianglesEstimatingUpdate]

/-- Algorithm 6.1: the method of similar triangles for minimizing `f + Ψ` over a closed convex
set `Q` with a chosen `L`-Lipschitz gradient field and a differentiable `1`-strongly convex
prox-function is iterate data over the chapter's canonical
`CompositeLipschitzGradientModel`. Its primitive data are the iterate sequence `x_k`, feasible
minimizers `v_k` of the estimating functions `φ_k`, the initialization `x₀ = v₀`, `φ₀(x) = L d(x)`,
the estimating-function recursion at
`y_k = (k / (k + 2)) x_k + (2 / (k + 2)) v_k`, and the update
`x_{k+1} = (k / (k + 2)) x_k + (2 / (k + 2)) v_{k+1}`. -/
structure SimilarTrianglesMethod
    (model : CompositeLipschitzGradientModel E) (x0 : model.feasibleSet) where
  /-- The iterate sequence `x₀, x₁, x₂, ...`. -/
  x : ℕ → E
  /-- The minimizers `v₀, v₁, v₂, ...` of the estimating functions. -/
  v : ℕ → model.feasibleSet
  /-- The estimating functions `φ₀, φ₁, φ₂, ...`. -/
  φ : ℕ → E → WithTop ℝ
  /-- The initial iterate is the prescribed point `x₀`. -/
  x_zero : x 0 = x0
  /-- The initial estimating-sequence minimizer is `v₀ = x₀`. -/
  v_zero : v 0 = x0
  /-- The initial estimating function is `φ₀(x) = L d(x)`. -/
  phi_zero :
    φ 0 = fun z ↦ (((model.L : ℝ) * model.proxFunction z : ℝ) : WithTop ℝ)
  /-- Each `v_{k+1}` minimizes the updated estimating function `φ_{k+1}` on the feasible set. -/
  v_succ_isMin (k : ℕ) : IsMinOn (φ (k + 1)) model.feasibleSet (v (k + 1))
  /-- The estimating functions satisfy the recursive update from the method of similar
  triangles. -/
  phi_succ (k : ℕ) :
    φ (k + 1) =
      similarTrianglesEstimatingUpdate model (φ k) k
        (similarTrianglesInterpolationPoint k (x k) (v k))
  /-- The iterate update is
  `x_{k+1} = (k / (k + 2)) x_k + (2 / (k + 2)) v_{k+1}`. -/
  x_succ (k : ℕ) : x (k + 1) = similarTrianglesInterpolationPoint k (x k) (v (k + 1))

namespace SimilarTrianglesMethod

variable {model : CompositeLipschitzGradientModel E} {x0 : model.feasibleSet}

/-- A method of similar triangles can be used as its iterate sequence `x_k`. -/
instance :
    CoeFun (SimilarTrianglesMethod model x0) (fun _ ↦ ℕ → E) where
  coe method := method.x

/-- The interpolation point `y_k` attached to a method of similar triangles. -/
def interpolationPoint
    (method : SimilarTrianglesMethod model x0) (k : ℕ) : E :=
  similarTrianglesInterpolationPoint k (method.x k) (method.v k)

/-- Every minimizing point `v_k` chosen by a method of similar triangles belongs to the feasible
set `Q`. -/
@[simp] theorem minimizingPoint_mem_feasibleSet
    (method : SimilarTrianglesMethod model x0) (k : ℕ) :
    (method.v k : E) ∈ model.feasibleSet :=
  (method.v k).property

/-- Every iterate `x_k` produced by a method of similar triangles belongs to the feasible set
`Q`. -/
theorem iterate_mem_feasibleSet
    (method : SimilarTrianglesMethod model x0) (k : ℕ) :
    method.x k ∈ model.feasibleSet := by
  induction k with
  | zero =>
      rw [method.x_zero]
      exact x0.property
  | succ k ih =>
      have hvk : (method.v (k + 1) : E) ∈ model.feasibleSet :=
        method.minimizingPoint_mem_feasibleSet (k + 1)
      have ht :
          ((2 : ℝ) / ((k : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) 1 := by
        have hden : 0 < (k : ℝ) + 2 := by positivity
        have hnum : (2 : ℝ) ≤ (k : ℝ) + 2 := by nlinarith
        constructor
        · positivity
        · exact (div_le_iff₀ hden).2 (by nlinarith)
      rw [method.x_succ k, similarTrianglesInterpolationPoint_eq_lineMap]
      exact model.feasibleSet_convex.lineMap_mem ih hvk ht

/-- A method of similar triangles can be used as its iterate sequence `x_k`. -/
@[simp] theorem coe_apply
    (method : SimilarTrianglesMethod model x0) (k : ℕ) :
    method k = method.x k :=
  rfl

/-- The interpolation point of a method of similar triangles is the textbook convex combination of
`x_k` and `v_k`. -/
-- Proof sketch: unfold `interpolationPoint` and `similarTrianglesInterpolationPoint`.
theorem interpolationPoint_def
    (method : SimilarTrianglesMethod model x0) (k : ℕ) :
    method.interpolationPoint k =
      (((k : ℝ) / ((k : ℝ) + 2)) • method.x k) +
        (((2 : ℝ) / ((k : ℝ) + 2)) • method.v k) :=
  rfl

/-- Every interpolation point `y_k` of a method of similar triangles belongs to the feasible set
`Q`. -/
theorem interpolationPoint_mem_feasibleSet
    (method : SimilarTrianglesMethod model x0) (k : ℕ) :
    method.interpolationPoint k ∈ model.feasibleSet := by
  have hxk : method.x k ∈ model.feasibleSet :=
    method.iterate_mem_feasibleSet k
  have hvk : (method.v k : E) ∈ model.feasibleSet :=
    method.minimizingPoint_mem_feasibleSet k
  have ht :
      ((2 : ℝ) / ((k : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) 1 := by
    have hden : 0 < (k : ℝ) + 2 := by positivity
    have hnum : (2 : ℝ) ≤ (k : ℝ) + 2 := by nlinarith
    constructor
    · positivity
    · exact (div_le_iff₀ hden).2 (by nlinarith)
  rw [interpolationPoint, similarTrianglesInterpolationPoint_eq_lineMap]
  exact model.feasibleSet_convex.lineMap_mem hxk hvk ht

end SimilarTrianglesMethod

end
