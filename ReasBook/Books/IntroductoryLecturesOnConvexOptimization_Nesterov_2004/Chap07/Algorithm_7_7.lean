/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Algorithm 7.7 lies in the Chapter 7 translated ellipsoid-rounding / positive-definite
matrix-dual-norm domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv` in `Chap07/Definition_7_23`, the chapter
  owner of the `G`-dual norm `‖·‖[G,*]`;
- `IsGammaNRounding` in `Chap07/Definition_7_32`, the chapter owner of the resulting `γ n`
  rounding notion;
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner from mathlib;
- `IsMaxOn`, the canonical owner for chosen maximizers on a set.

Best owner abstraction:
- source-facing: Algorithm 7.7's center/shape/maximizer iteration data;
- core/canonical: the Chapter 7 dual norm `‖·‖[G,*]` on positive-definite matrices;
- bridge/view: the explicit inverse-matrix formula for that dual norm and the derived maximal
  radius.

Primitive data:
- the convex set `C`, the parameter `γ`, and the initial data `v₀`, `G₀`;
- the center, shape-matrix, and maximizer sequences;
- positive definiteness of each shape matrix.

Derived API:
- the current `Gₖ`-dual distance, expressed through the chapter owner `‖·‖[G,*]`;
- the maximal radius `rₖ` as the supremum of that dual distance over `C`;
- the initial positive definiteness of `G₀`, recovered from `shape_zero` and `shape_posDef`.

The previous version duplicated the Chapter 7 dual-norm owner by defining the dual distance
directly from `G⁻¹`, introduced a one-off displacement wrapper for `g - v`, and stored the radius
sequence plus `G₀ ≻ 0` as primitive data even though both are derived from the core owner layer.
This refinement keeps the source-facing iteration data, but moves the metric surface back to the
existing Chapter 7 owner and shrinks the primitive record accordingly.
The dimension bound `2 ≤ n` is not primitive algorithm data for this owner layer, so it is left to
later theorem statements where that numerical hypothesis is actually used.
-/

/-- The `G`-dual distance from `g` to the center `v`, namely `‖g - v‖[G,*]`. -/
abbrev generalConvexRoundingDualDistance
    (G : {G : Mat // G.PosDef}) (v g : E) : ℝ :=
  ‖g - v‖[G,*]

/-- Expanding `generalConvexRoundingDualDistance G v g` gives the inverse-matrix formula for the
underlying Chapter 7 dual norm. -/
theorem generalConvexRoundingDualDistance_eq_sqrt_inner_inv
    (G : {G : Mat // G.PosDef}) (v g : E) :
    generalConvexRoundingDualDistance G v g =
      Real.sqrt (inner ℝ (g - v) ((Matrix.toEuclideanLin G.1⁻¹) (g - v))) := by
  simpa [generalConvexRoundingDualDistance] using
    positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv G (g - v)

/-- The maximal `G`-dual distance from the current center `v` to the convex set `C`. -/
def generalConvexRoundingRadius
    (C : Set E) (G : {G : Mat // G.PosDef}) (v : E) : ℝ :=
  sSup (generalConvexRoundingDualDistance G v '' C)

/-- Evaluating `generalConvexRoundingRadius C G v` gives the supremum of the current
`G`-dual distance over `C`. -/
@[simp]
theorem generalConvexRoundingRadius_eq_sSup
    (C : Set E) (G : {G : Mat // G.PosDef}) (v : E) :
    generalConvexRoundingRadius C G v =
      sSup (generalConvexRoundingDualDistance G v '' C) :=
  rfl

/-- The argmax set of the current `G`-dual distance from the center `v` over the convex set `C`.
-/
abbrev generalConvexRoundingArgmax
    (C : Set E) (G : {G : Mat // G.PosDef}) (v : E) : Set E :=
  {g | g ∈ C ∧ IsMaxOn (generalConvexRoundingDualDistance G v) C g}

/-- Membership in `generalConvexRoundingArgmax C G v` means that `g` lies in `C` and maximizes
the current `G`-dual distance on `C`. -/
@[simp]
theorem mem_generalConvexRoundingArgmax_iff
    {C : Set E} {G : {G : Mat // G.PosDef}} {v g : E} :
    g ∈ generalConvexRoundingArgmax C G v ↔
      g ∈ C ∧ IsMaxOn (generalConvexRoundingDualDistance G v) C g :=
  Iff.rfl

/-- The coefficient
`α = (2 / (n + 1)) * ((r - n) / (r - 1))`
used in Algorithm 7.7 when `r > γ n`. -/
def generalConvexRoundingAlpha (dim : ℕ) (r : ℝ) : ℝ :=
  (2 / ((dim : ℝ) + 1)) * ((r - (dim : ℝ)) / (r - 1))

/-- The coefficient
`β = α / r + ((r - 1) / 2)^2 * (α / r)^2`
used in the rank-one matrix update of Algorithm 7.7. -/
def generalConvexRoundingBeta (dim : ℕ) (r : ℝ) : ℝ :=
  generalConvexRoundingAlpha dim r / r +
    (((r - 1) / 2) ^ (2 : ℕ)) * ((generalConvexRoundingAlpha dim r / r) ^ (2 : ℕ))

/-- The center update
`v₊ = v + α ((r - 1) / (2 r)) (g - v)` from Algorithm 7.7. -/
def generalConvexRoundingNextCenter
    (dim : ℕ) (r : ℝ) (v g : E) : E :=
  v + (generalConvexRoundingAlpha dim r * ((r - 1) / (2 * r))) • (g - v)

/-- The shape-matrix update
`G₊ = (1 - α) G + β (g - v) (g - v)ᵀ` from Algorithm 7.7. -/
def generalConvexRoundingNextShape
    (dim : ℕ) (r : ℝ) (G : Mat) (v g : E) : Mat :=
  (1 - generalConvexRoundingAlpha dim r) • G +
    generalConvexRoundingBeta dim r • Matrix.vecMulVec (g - v) (g - v)

/-- The stopping predicate `r ≤ γ n` from Algorithm 7.7. -/
def generalConvexRoundingShouldStop (gamma : ℝ) (dim : ℕ) (r : ℝ) : Prop :=
  r ≤ gamma * (dim : ℝ)

/-- Algorithm 7.7: an iterative scheme for computing a `γ n`-rounding of a convex set `C`
with nonempty interior consists of a parameter `γ > 1`, initial data `v₀ ∈ ℝⁿ` and `G₀ ≻ 0`,
sequences of centers `v_k`, positive-definite shape matrices `G_k`, and maximizers
`g_k ∈ argmax_{g ∈ C} ‖g - v_k‖_{G_k}^*`, where
`r_k = max_{g ∈ C} ‖g - v_k‖_{G_k}^*` is the corresponding maximal value, such that whenever
`r_k > γ n` the updates for `v_{k+1}` and `G_{k+1}` are exactly the displayed formulas with
`α_k = (2 / (n + 1)) ((r_k - n) / (r_k - 1))` and
`β_k = α_k / r_k + ((r_k - 1) / 2)^2 (α_k / r_k)^2`. -/
structure GeneralConvexRoundingAlgorithm
    (C : Set E) (gamma : ℝ) (v0 : E) (G0 : Mat) where
  /-- The ambient set `C` is convex. -/
  convexSet : Convex ℝ C
  /-- The ambient convex set `C` has nonempty interior. -/
  interior_nonempty : (interior C).Nonempty
  /-- The rounding parameter satisfies `γ > 1`. -/
  gamma_one_lt : 1 < gamma
  /-- The center sequence `v₀, v₁, v₂, ...`. -/
  center : ℕ → E
  /-- The shape-matrix sequence `G₀, G₁, G₂, ...`. -/
  shape : ℕ → Mat
  /-- The chosen maximizers `g₀, g₁, g₂, ...`. -/
  maximizer : ℕ → E
  /-- The center sequence starts from the prescribed initial point `v₀`. -/
  center_zero : center 0 = v0
  /-- The shape sequence starts from the prescribed initial matrix `G₀`. -/
  shape_zero : shape 0 = G0
  /-- Every shape matrix `G_k` is positive definite. -/
  shape_posDef : ∀ k : ℕ, (shape k).PosDef
  /-- Each chosen point `g_k` lies in the canonical argmax set of the current `G_k`-dual distance
  on `C`. -/
  maximizer_mem_argmax :
    ∀ k : ℕ,
      let G : {G : Mat // G.PosDef} := ⟨shape k, shape_posDef k⟩
      maximizer k ∈ generalConvexRoundingArgmax C G (center k)
  /-- If the stopping test fails at step `k`, then the next center is updated by
  `v_{k+1} = v_k + α_k ((r_k - 1) / (2 r_k)) (g_k - v_k)`, where
  `r_k = max_{g ∈ C} ‖g - v_k‖_{G_k}^*`. -/
  center_succ :
    ∀ k : ℕ,
      let G : {G : Mat // G.PosDef} := ⟨shape k, shape_posDef k⟩
      let r := generalConvexRoundingRadius C G (center k)
      ¬ generalConvexRoundingShouldStop gamma n r →
        center (k + 1) =
          generalConvexRoundingNextCenter n r (center k) (maximizer k)
  /-- If the stopping test fails at step `k`, then the next shape matrix is updated by
  `G_{k+1} = (1 - α_k) G_k + β_k (g_k - v_k) (g_k - v_k)ᵀ`, where
  `r_k = max_{g ∈ C} ‖g - v_k‖_{G_k}^*`. -/
  shape_succ :
    ∀ k : ℕ,
      let G : {G : Mat // G.PosDef} := ⟨shape k, shape_posDef k⟩
      let r := generalConvexRoundingRadius C G (center k)
      ¬ generalConvexRoundingShouldStop gamma n r →
        shape (k + 1) =
          generalConvexRoundingNextShape n r (shape k) (center k) (maximizer k)

namespace GeneralConvexRoundingAlgorithm

/-- A run of Algorithm 7.7 can be used as its center sequence `v₀, v₁, v₂, ...`. -/
instance
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat} :
    CoeFun (GeneralConvexRoundingAlgorithm C gamma v0 G0) (fun _ ↦ ℕ → E) where
  coe algorithm := algorithm.center

/-- The current positive-definite shape matrix, packaged in the canonical Chapter 7 dual-norm
owner. -/
def currentShape
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) (k : ℕ) :
    {G : Mat // G.PosDef} :=
  ⟨algorithm.shape k, algorithm.shape_posDef k⟩

/-- The maximal current `G_k`-dual distance from the center `v_k` to the set `C`. -/
def radius
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) (k : ℕ) : ℝ :=
  generalConvexRoundingRadius C (algorithm.currentShape k) (algorithm.center k)

/-- The canonical one-sided step quantity `σₖ = (rₖ - n) / (n + 1)`, attached to the current
shape `Gₖ` and maximizer displacement `gₖ - vₖ`. -/
abbrev oneSidedRoundingSigma
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) (k : ℕ) : ℝ :=
  _root_.oneSidedRoundingSigma
    (algorithm.currentShape k) (algorithm.maximizer k - algorithm.center k)

/-- The stopping predicate `r_k ≤ γ n` at step `k`. -/
def stoppingCriterion
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) (k : ℕ) : Prop :=
  generalConvexRoundingShouldStop gamma n (algorithm.radius k)

/-- The initial shape matrix `G₀` is positive definite, derived from the persistent positive
definiteness of the shape sequence. -/
theorem initial_shape_posDef
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) :
    G0.PosDef := by
  simpa [algorithm.shape_zero] using algorithm.shape_posDef 0

/-- Each chosen point `g_k` lies in the canonical argmax set of the current `G_k`-dual distance.
-/
theorem maximizer_mem_argmax_set
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) (k : ℕ) :
    algorithm.maximizer k ∈
      generalConvexRoundingArgmax C (algorithm.currentShape k) (algorithm.center k) := by
  simpa [currentShape] using algorithm.maximizer_mem_argmax k

/-- For each step `k`, the chosen point `g_k` lies in `C` and maximizes the current `G_k`-dual
distance on `C`. -/
theorem maximizer_mem_and_isMaxOn
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) (k : ℕ) :
    algorithm.maximizer k ∈ C ∧
      IsMaxOn
        (generalConvexRoundingDualDistance (algorithm.currentShape k) (algorithm.center k))
        C
        (algorithm.maximizer k) := by
  simpa using algorithm.maximizer_mem_argmax_set k

/-- If the stopping test fails at step `k`, then the next center is the textbook update from
Algorithm 7.7. -/
theorem center_succ_of_not_stopping
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) {k : ℕ}
    (hk : ¬ algorithm.stoppingCriterion k) :
    algorithm.center (k + 1) =
      generalConvexRoundingNextCenter n (algorithm.radius k)
        (algorithm.center k) (algorithm.maximizer k) := by
  simpa [stoppingCriterion, radius, currentShape] using algorithm.center_succ k hk

/-- If the stopping test fails at step `k`, then the next shape matrix is the textbook update from
Algorithm 7.7. -/
theorem shape_succ_of_not_stopping
    {C : Set E} {gamma : ℝ} {v0 : E} {G0 : Mat}
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0) {k : ℕ}
    (hk : ¬ algorithm.stoppingCriterion k) :
    algorithm.shape (k + 1) =
      generalConvexRoundingNextShape n (algorithm.radius k)
        (algorithm.shape k) (algorithm.center k) (algorithm.maximizer k) := by
  simpa [stoppingCriterion, radius, currentShape] using algorithm.shape_succ k hk

end GeneralConvexRoundingAlgorithm

end
