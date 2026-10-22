/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped ConstrainedArgmin
open scoped WithTopConvexAnalysis

universe u

/- Theorem 6.2 lies in the chapter's composite-acceleration / similar-triangles domain.

Sampled owner-style declarations:
- `CompositeLipschitzGradientModel` in `Definition_6_8`, the chapter owner for a composite
  problem together with its chosen gradient field, Lipschitz constant, prox-function, and
  tractable prox subproblems;
- `constrainedArgmin` with notation `argmin[Q] f` in `Chap01/Definition_1_3_3`, the project
  owner for constrained minimizers on a feasible set;
- `NesterovIsProxCenter` in `Definition_6_31`, the canonical normalized prox-center owner for the initial
  point of the prox term;
- `SimilarTrianglesMethod`, `similarTrianglesEstimatingWeight`, and
  `SimilarTrianglesMethod.interpolationPoint` in `Algorithm_6_1`, the canonical owner layer for
  method `(6.1.19)`;
- `similarTrianglesEstimatingUpdate` in `Algorithm_6_1`, the owner recursion for the estimating
  functions `φ_k`.

Best owner abstraction:
- source-facing: Theorem 6.2's explicit estimating-function lower bound and the resulting
  suboptimality estimate;
- core/canonical: `SimilarTrianglesMethod` over `CompositeLipschitzGradientModel`, together with
  the normalized prox-center owner `NesterovIsProxCenter model.feasibleSet model.proxFunction x0` and
  the constrained minimizer owner
  `argmin[model.feasibleSet] (fun x ↦ model.smoothPart x + withTopRealPart model.nonsmoothPart x)`;
- bridge/view: the closed-form estimating function on the feasible-set owner `model.feasibleSet`,
  using the canonical Chapter 3 finite real part `withTopRealPart model.nonsmoothPart` rather
  than a parallel global real-valued regularizer witness.

Primitive data:
- a similar-triangles method over the canonical composite Lipschitz-gradient owner;
- a normalized prox-center `x0` for the prox-function `d`;
- the closed convex regularizer `model.nonsmoothPart : E → WithTop ℝ`, already owned by the
  Chapter 3 composite problem structure;
- the explicit affine-model closed form of `φ_k` on the feasible-set subtype, where the
  regularizer is canonically read through `withTopRealPart`.

Derived API:
- the closed-form estimating function `estimatingFunction`;
- the bridge theorem comparing `method.φ` with the closed-form `φ_k`;
- the lower-bound and suboptimality statements of Theorem 6.2, with constrained optimality
  consumed through the Chapter 1 argmin owner rather than a parallel raw `IsMinOn` hypothesis.

Source/core/bridge triage:
- source-facing: the two theorem statements below;
- core/canonical: `SimilarTrianglesMethod`, `NesterovIsProxCenter`, and `argmin[Q] f`;
- bridge/view: `estimatingFunction` and `phi_eq_estimatingFunction`. -/

namespace SimilarTrianglesMethod

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {model : CompositeLipschitzGradientModel E} {x0 : model.feasibleSet}

/-- The closed-form estimating function `φ_k` from Theorem 6.2, written on the canonical
similar-triangles owner surface over the feasible-set subtype and using the chapter owner
`withTopRealPart model.nonsmoothPart` for the regularizer term. -/
def estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) : model.feasibleSet → ℝ :=
  fun x ↦
    (model.L : ℝ) * model.proxFunction x +
      Finset.sum (Finset.range k) (fun i ↦
        similarTrianglesEstimatingWeight i *
          (model.smoothPart (method.interpolationPoint i) +
            model.smoothGradient (method.interpolationPoint i)
              (x - method.interpolationPoint i))) +
      (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x

/-- Helper for Theorem 6.2: the ambient closed-form owner of `φ_k`, obtained by reading the same
formula directly on `E` before restricting to the feasible-set subtype. -/
def estimatingFunctionAmbient
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) : E → ℝ :=
  fun x ↦
    (model.L : ℝ) * model.proxFunction x +
      Finset.sum (Finset.range k) (fun i ↦
        similarTrianglesEstimatingWeight i *
          (model.smoothPart (method.interpolationPoint i) +
            model.smoothGradient (method.interpolationPoint i)
              (x - method.interpolationPoint i))) +
      (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x

/-- Evaluating the explicit estimating function recovers the prox term, the accumulated affine
models of `model.smoothPart` at the interpolation points `y_i`, and the penalty term
`((k (k + 1)) / 4) withTopRealPart model.nonsmoothPart x` on the feasible set. -/
-- Proof sketch: unfold `estimatingFunction`.
@[simp] theorem estimatingFunction_apply
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.estimatingFunction k x =
      (model.L : ℝ) * model.proxFunction x +
        Finset.sum (Finset.range k) (fun i ↦
          similarTrianglesEstimatingWeight i *
            (model.smoothPart (method.interpolationPoint i) +
              model.smoothGradient (method.interpolationPoint i)
                (x - method.interpolationPoint i))) +
        (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x := by
  -- Unfolding the owner-level definition gives the claimed closed form immediately.
  rfl

/-- Evaluating the ambient estimating function recovers the same explicit real-valued closed form
used in Theorem 6.2, now on arbitrary ambient points `x : E`. -/
@[simp] theorem estimatingFunctionAmbient_apply
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : E) :
    method.estimatingFunctionAmbient k x =
      (model.L : ℝ) * model.proxFunction x +
        Finset.sum (Finset.range k) (fun i ↦
          similarTrianglesEstimatingWeight i *
            (model.smoothPart (method.interpolationPoint i) +
              model.smoothGradient (method.interpolationPoint i)
                (x - method.interpolationPoint i))) +
        (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x := by
  -- Unfolding the ambient owner shows exactly the same coefficient data.
  rfl

/-- Helper for Theorem 6.2: restricting the ambient closed form to a feasible point recovers the
original subtype-valued owner `estimatingFunction`. -/
@[simp] theorem estimatingFunctionAmbient_restrict
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) {x : E} (hx : x ∈ model.feasibleSet) :
    method.estimatingFunctionAmbient k x = method.estimatingFunction k ⟨x, hx⟩ := by
  -- Both closed forms are definitionally the same once the subtype point is coerced to `E`.
  rfl

/-- Helper for Theorem 6.2: the similar-triangles weights sum to the closed form
`k (k + 1) / 4`. -/
theorem sum_similarTrianglesEstimatingWeight
    (k : ℕ) :
    Finset.sum (Finset.range k) similarTrianglesEstimatingWeight =
      ((k : ℝ) * (k + 1)) / 4 := by
  induction k with
  | zero =>
      -- The empty sum matches the quadratic closed form at `k = 0`.
      norm_num [similarTrianglesEstimatingWeight_def]
  | succ k ih =>
      -- Expanding the last weight reduces the claim to a single quadratic identity.
      rw [Finset.sum_range_succ, ih, similarTrianglesEstimatingWeight_def]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/-- Helper for Theorem 6.2: the explicit estimating function satisfies the real-valued successor
recursion from method `(6.1.19)`. -/
theorem estimatingFunction_succ
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.estimatingFunction (k + 1) x =
      method.estimatingFunction k x +
        similarTrianglesEstimatingWeight k *
          (model.smoothPart (method.interpolationPoint k) +
            model.smoothGradient (method.interpolationPoint k)
              (x - method.interpolationPoint k)) +
        similarTrianglesEstimatingWeight k * withTopRealPart model.nonsmoothPart x := by
  -- Expanding the last affine model reduces the recursion to the coefficient identity
  -- `A_{k+1} = A_k + ((k + 1) / 2)`.
  unfold estimatingFunction
  rw [Finset.sum_range_succ]
  have hcoeff :
      (((((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) / 4) : ℝ) =
        (((k : ℝ) * (k + 1)) / 4) + similarTrianglesEstimatingWeight k := by
    rw [similarTrianglesEstimatingWeight_def]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hcoeff]
  ring

/-- Helper for Theorem 6.2: the ambient closed-form owner satisfies the same real-valued
successor recursion as the subtype-restricted owner. -/
theorem estimatingFunctionAmbient_succ
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : E) :
    method.estimatingFunctionAmbient (k + 1) x =
      method.estimatingFunctionAmbient k x +
        similarTrianglesEstimatingWeight k *
          (model.smoothPart (method.interpolationPoint k) +
            model.smoothGradient (method.interpolationPoint k)
              (x - method.interpolationPoint k)) +
        similarTrianglesEstimatingWeight k * withTopRealPart model.nonsmoothPart x := by
  -- The ambient recursion is the same coefficient computation as for the subtype owner.
  unfold estimatingFunctionAmbient
  rw [Finset.sum_range_succ]
  have hcoeff :
      (((((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) / 4) : ℝ) =
        (((k : ℝ) * (k + 1)) / 4) + similarTrianglesEstimatingWeight k := by
    rw [similarTrianglesEstimatingWeight_def]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hcoeff]
  ring

-- Proof sketch: prove by induction on `k`, using `phi_zero`, `phi_succ`,
-- `similarTrianglesEstimatingUpdate_apply`, and the ambient real recursion
-- `estimatingFunctionAmbient_succ`, with the nonsmooth term rewritten on the feasible set via
-- `withTopRealPart`.
/-- Helper for Theorem 6.2: on feasible points, the recursive estimating-function owner
`method.φ k` is the extended-real coercion of the ambient closed form. -/
theorem phi_eq_estimatingFunctionAmbient
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) {x : E} (hx : x ∈ model.feasibleSet) :
    method.φ k x = (method.estimatingFunctionAmbient k x : WithTop ℝ) := by
  induction k with
  | zero =>
      -- At stage zero, both owners are exactly `L d(x)`.
      rw [method.phi_zero]
      simp [estimatingFunctionAmbient]
  | succ k ih =>
      -- Rewrite the recursive `WithTop` update into the real-valued ambient successor formula.
      rw [method.phi_succ, similarTrianglesEstimatingUpdate_apply, ih]
      have hxdom : x ∈ dom model.nonsmoothPart :=
        model.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain hx
      have hsucc :
          (method.estimatingFunctionAmbient (k + 1) x : WithTop ℝ) =
            ((method.estimatingFunctionAmbient k x +
                similarTrianglesEstimatingWeight k *
                  (model.smoothPart (method.interpolationPoint k) +
                    model.smoothGradient (method.interpolationPoint k)
                      (x - method.interpolationPoint k)) +
                similarTrianglesEstimatingWeight k *
                  withTopRealPart model.nonsmoothPart x : ℝ) : WithTop ℝ) := by
        exact congrArg (fun r : ℝ ↦ (r : WithTop ℝ))
          (method.estimatingFunctionAmbient_succ k x)
      have hpsi :
          (((similarTrianglesEstimatingWeight k : ℝ) : WithTop ℝ) *
              model.nonsmoothPart x) =
            ((similarTrianglesEstimatingWeight k *
                withTopRealPart model.nonsmoothPart x : ℝ) : WithTop ℝ) := by
        rw [← coe_withTopRealPart hxdom]
        norm_num
      rw [hsucc, hpsi]
      simpa only [SimilarTrianglesMethod.interpolationPoint, WithTop.coe_add, add_assoc]

-- Proof sketch: specialize the ambient bridge `phi_eq_estimatingFunctionAmbient` to the subtype
-- point `x : model.feasibleSet`, then simplify using the restriction lemma.
/-- On the feasible set `Q`, the recursive estimating-function owner `method.φ k` is the
extended-real coercion of the closed-form `φ_k` from Theorem 6.2. -/
theorem phi_eq_estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.φ k x = (method.estimatingFunction k x : WithTop ℝ) := by
  -- The ambient bridge specializes back to the original subtype owner without further work.
  simpa using method.phi_eq_estimatingFunctionAmbient k x.property

/-- Helper for Theorem 6.2: the minimizing property of `v_{k+1}` transfers from the
`WithTop ℝ`-valued recursive owner `φ_{k+1}` to the real-valued ambient closed form. -/
theorem estimatingFunctionAmbient_isMinOn_succ
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) :
    IsMinOn (method.estimatingFunctionAmbient (k + 1)) model.feasibleSet (method.v (k + 1)) := by
  rw [isMinOn_iff]
  intro x hx
  -- Compare `φ_{k+1}` at the minimizer and at `x`, then read the resulting `WithTop` inequality
  -- back in `ℝ` via the ambient bridge on feasible points.
  have hmin_withTop_all :
      ∀ y ∈ model.feasibleSet,
        method.φ (k + 1) (method.v (k + 1)) ≤ method.φ (k + 1) y := by
    simpa [isMinOn_iff] using method.v_succ_isMin k
  have hmin_withTop := hmin_withTop_all x hx
  have hv_eq :
      method.φ (k + 1) (method.v (k + 1)) =
        (method.estimatingFunctionAmbient (k + 1) (method.v (k + 1)) : WithTop ℝ) :=
    method.phi_eq_estimatingFunctionAmbient (k + 1)
      (method.minimizingPoint_mem_feasibleSet (k + 1))
  have hx_eq :
      method.φ (k + 1) x =
        (method.estimatingFunctionAmbient (k + 1) x : WithTop ℝ) :=
    method.phi_eq_estimatingFunctionAmbient (k + 1) hx
  rw [hv_eq, hx_eq] at hmin_withTop
  exact_mod_cast hmin_withTop

/-- Helper for Theorem 6.2: the smooth part lies above its affine support at every feasible base
point. -/
theorem smoothPart_lower_support_on_feasible
    {x y : E}
    (hx : x ∈ model.feasibleSet) (hy : y ∈ model.feasibleSet) :
    model.smoothPart y ≥
      model.smoothPart x + model.smoothGradient x (y - x) := by
  let seg : ℝ → E := AffineMap.lineMap x y
  have hmaps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) model.feasibleSet :=
    model.feasibleSet_convex.mapsTo_lineMap hx hy
  have hseg_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (model.smoothPart ∘ seg) := by
    refine (model.smoothPart_convex.comp_affineMap (AffineMap.lineMap x y)).subset ?_
      (convex_Icc (0 : ℝ) 1)
    intro t ht
    exact hmaps ht
  have hderiv :
      HasDerivWithinAt (model.smoothPart ∘ seg) (model.smoothGradient x (y - x))
        (Set.Icc (0 : ℝ) 1) 0 := by
    -- Compose the feasible derivative at `x` with the line segment from `x` to `y`.
    simpa [seg] using
      (model.smoothPart_hasGradientWithinAt (hmaps (by simp))).comp_hasDerivWithinAt (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap hmaps
  have hslope :=
    hseg_conv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hderiv
  have hslope' :
      model.smoothGradient x (y - x) ≤ model.smoothPart y - model.smoothPart x := by
    simpa [seg, slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
  linarith

/-- Helper for Theorem 6.2: the corrected smooth remainder along a feasible segment has the
expected within-derivative. -/
private theorem smoothPart_segment_corrected_remainder_hasDerivWithinAt
    {x y : E}
    (hx : x ∈ model.feasibleSet) (hy : y ∈ model.feasibleSet)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun u : ℝ ↦
        model.smoothPart (AffineMap.lineMap x y u) - model.smoothPart x -
          u * model.smoothGradient x (y - x))
      ((model.smoothGradient (AffineMap.lineMap x y t) - model.smoothGradient x) (y - x))
      (Set.Icc (0 : ℝ) 1) t := by
  let seg : ℝ → E := AffineMap.lineMap x y
  have hseg_maps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) model.feasibleSet :=
    model.feasibleSet_convex.mapsTo_lineMap hx hy
  have hseg_mem : seg t ∈ model.feasibleSet := hseg_maps ht
  have hseg_deriv :
      HasDerivWithinAt
        (fun u : ℝ ↦ model.smoothPart (seg u))
        (model.smoothGradient (seg t) (y - x))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- Differentiate the smooth part along the feasible segment from `x` to `y`.
    simpa [seg] using
      (model.smoothPart_hasGradientWithinAt hseg_mem).comp_hasDerivWithinAt_of_eq t
        AffineMap.hasDerivWithinAt_lineMap hseg_maps rfl
  have hlin :
      HasDerivWithinAt
        (fun u : ℝ ↦ u * model.smoothGradient x (y - x))
        (model.smoothGradient x (y - x))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- The affine correction contributes the frozen base linearization.
    simpa [one_mul] using
      ((hasDerivAt_id t).mul_const (model.smoothGradient x (y - x))).hasDerivWithinAt
  have hmain :
      HasDerivWithinAt
        (fun u : ℝ ↦
          model.smoothPart (seg u) - model.smoothPart x -
            u * model.smoothGradient x (y - x))
        (model.smoothGradient (seg t) (y - x) - model.smoothGradient x (y - x))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- Subtract the constant base value and the frozen affine term from the segment restriction.
    convert
      (hseg_deriv.sub
          (hasDerivWithinAt_const (s := Set.Icc (0 : ℝ) 1) (x := t) (model.smoothPart x))).sub hlin using 1
    ring
  simpa [seg] using hmain

/-- Helper for Theorem 6.2: the derivative of the corrected smooth remainder is bounded by the
Lipschitz-gradient modulus along feasible segments. -/
private theorem smoothPart_segment_corrected_remainder_norm_le
    {x y : E}
    (hx : x ∈ model.feasibleSet) (hy : y ∈ model.feasibleSet)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ‖((model.smoothGradient (AffineMap.lineMap x y t) - model.smoothGradient x) (y - x))‖ ≤
      (model.L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
  have hline_mem : AffineMap.lineMap x y t ∈ model.feasibleSet :=
    model.feasibleSet_convex.lineMap_mem hx hy (Set.mem_Icc_of_Ico ht)
  have hgrad_bound :
      ‖model.smoothGradient (AffineMap.lineMap x y t) - model.smoothGradient x‖ ≤
        (model.L : ℝ) * ‖AffineMap.lineMap x y t - x‖ := by
    -- The chosen gradient field is `L`-Lipschitz on the feasible set.
    simpa [dist_eq_norm] using model.smoothGradient_lipschitz.norm_sub_le hline_mem hx
  have hseg_norm : ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
    -- Along the segment, the distance to the left endpoint scales linearly with `t`.
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg ht.1, norm_sub_rev] using
      (dist_lineMap_left x y t)
  -- Combine the operator-norm estimate with the explicit segment-length formula.
  calc
    ‖((model.smoothGradient (AffineMap.lineMap x y t) - model.smoothGradient x) (y - x))‖ ≤
        ‖model.smoothGradient (AffineMap.lineMap x y t) - model.smoothGradient x‖ * ‖y - x‖ :=
      (model.smoothGradient (AffineMap.lineMap x y t) - model.smoothGradient x).le_opNorm (y - x)
    _ ≤ ((model.L : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
      gcongr
    _ = ((model.L : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
      rw [hseg_norm]
    _ = (model.L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
      ring

/-- Helper for Theorem 6.2: the smooth part admits the standard quadratic upper model on the
feasible set. -/
theorem smoothPart_upper_model_on_feasible
    {x y : E}
    (hx : x ∈ model.feasibleSet) (hy : y ∈ model.feasibleSet) :
    model.smoothPart y ≤
      model.smoothPart x + model.smoothGradient x (y - x) +
        ((model.L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let remainder : ℝ → ℝ := fun s ↦
    model.smoothPart (AffineMap.lineMap x y s) - model.smoothPart x -
      s * model.smoothGradient x (y - x)
  have hcont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- The corrected segment remainder is continuous because it has a within-derivative on `[0,1]`.
    exact
      (smoothPart_segment_corrected_remainder_hasDerivWithinAt (model := model)
        hx hy t ht).continuousWithinAt
  have hdiff : DifferentiableOn ℝ remainder (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    -- Inside the open interval, the within-derivative upgrades to an ordinary derivative.
    exact
      ((smoothPart_segment_corrected_remainder_hasDerivWithinAt (model := model)
          hx hy t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
        |>.differentiableWithinAt
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := remainder)
      (B := fun t : ℝ ↦ (model.L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ))
      (a := (0 : ℝ)) (b := 1)
      (by norm_num)
      hcont
      hdiff
      (Filter.Eventually.of_forall fun t ht_mem ↦ by
        have hderivAt :=
          (smoothPart_segment_corrected_remainder_hasDerivWithinAt (model := model)
            hx hy t (Set.mem_Icc_of_Ioo ht_mem)).hasDerivAt (Icc_mem_nhds ht_mem.1 ht_mem.2)
        rw [hderivAt.deriv]
        simpa using
          smoothPart_segment_corrected_remainder_norm_le (model := model)
            hx hy (t := t) (Set.mem_Ico_of_Ioo ht_mem))
      (by
        simpa [mul_assoc] using
          (show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
            intervalIntegrable_id).const_mul ((model.L : ℝ) * ‖y - x‖ ^ (2 : ℕ)))
  have hR0 : remainder 0 = 0 := by
    simp [remainder]
  have hR1 :
      remainder 1 =
        model.smoothPart y - model.smoothPart x - model.smoothGradient x (y - x) := by
    simp [remainder]
  rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hbound
  have hrem := abs_le.mp <|
    calc
      |model.smoothPart y - model.smoothPart x - model.smoothGradient x (y - x)| ≤
          ∫ t in (0 : ℝ)..1, (model.L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := hbound
      _ = ((model.L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
          calc
            ∫ t in (0 : ℝ)..1, (model.L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) =
                ∫ t in (0 : ℝ)..1, ((model.L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * t := by
                  congr with t
                  ring
            _ = ((model.L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
                  rw [intervalIntegral.integral_const_mul]
            _ = ((model.L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
                  rw [integral_id]
                  norm_num
                  ring
  linarith [hrem.2]

/-- Helper for Theorem 6.2: the updated estimating function has the quadratic-growth lower bound
at its minimizer `v_{k+1}`. -/
theorem estimatingFunction_quadratic_growth_succ
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.estimatingFunction (k + 1) x ≥
      method.estimatingFunction (k + 1) (method.v (k + 1)) +
        ((model.L : ℝ) / 2) * ‖(method.v (k + 1) : E) - x‖ ^ (2 : ℕ) := by
  by_cases hL : 0 < (model.L : ℝ)
  · let proxTerm : E → ℝ := fun z ↦ (model.L : ℝ) * model.proxFunction z
    let perturbation : E → ℝ := fun z ↦
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        similarTrianglesEstimatingWeight i *
          (model.smoothPart (method.interpolationPoint i) +
            model.smoothGradient (method.interpolationPoint i)
              (z - method.interpolationPoint i))) +
        ((((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) / 4) *
          withTopRealPart model.nonsmoothPart z
    have hperturb_convex :
        ConvexOn ℝ model.feasibleSet perturbation := by
      have hsum_convex :
          ConvexOn ℝ model.feasibleSet
            (fun z ↦
              Finset.sum (Finset.range (k + 1)) (fun i ↦
                similarTrianglesEstimatingWeight i *
                  (model.smoothPart (method.interpolationPoint i) +
                    model.smoothGradient (method.interpolationPoint i)
                      (z - method.interpolationPoint i)))) := by
        -- Each affine lower model is convex, so their weighted finite sum stays convex.
        classical
        refine Finset.induction_on (Finset.range (k + 1))
          (by simpa using convexOn_const (0 : ℝ) model.feasibleSet_convex) ?_
        intro i s hi hs
        have hbase_convex :
            ConvexOn ℝ model.feasibleSet
              (fun z : E ↦
                model.smoothPart (method.interpolationPoint i) +
                  model.smoothGradient (method.interpolationPoint i)
                    (z - method.interpolationPoint i)) := by
          let c : ℝ :=
            model.smoothPart (method.interpolationPoint i) -
              model.smoothGradient (method.interpolationPoint i) (method.interpolationPoint i)
          have hconst :
              ConvexOn ℝ model.feasibleSet (fun _ : E ↦ c) :=
            convexOn_const c model.feasibleSet_convex
          have hlinear :
              ConvexOn ℝ model.feasibleSet
                (fun z : E ↦ model.smoothGradient (method.interpolationPoint i) z) := by
            simpa using
              ((model.smoothGradient (method.interpolationPoint i)).toLinearMap.convexOn
                model.feasibleSet_convex)
          -- Recenter the affine model as a constant plus a linear functional.
          have hshift :
              ConvexOn ℝ model.feasibleSet
                (fun z : E ↦ model.smoothGradient (method.interpolationPoint i) z + c) := by
            simpa [Pi.add_apply] using hlinear.add hconst
          simpa [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
        have hweight_convex :
            ConvexOn ℝ model.feasibleSet
              (fun z : E ↦
                similarTrianglesEstimatingWeight i *
                  (model.smoothPart (method.interpolationPoint i) +
                    model.smoothGradient (method.interpolationPoint i)
                      (z - method.interpolationPoint i))) := by
          have hweight_nonneg : 0 ≤ similarTrianglesEstimatingWeight i := by
            rw [similarTrianglesEstimatingWeight_def]
            positivity
          simpa [smul_eq_mul] using
            ConvexOn.smul hweight_nonneg hbase_convex
        simpa [perturbation, Finset.sum_insert hi] using hweight_convex.add hs
      have hpsi_convex :
          ConvexOn ℝ model.feasibleSet
            (fun z ↦
              ((((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) / 4) *
                withTopRealPart model.nonsmoothPart z) := by
        have hcoeff_nonneg :
            0 ≤ ((((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) / 4 : ℝ) := by
          positivity
        simpa [smul_eq_mul] using
          ConvexOn.smul hcoeff_nonneg model.nonsmoothPart_closedConvex.convexOn_withTopRealPart
      simpa [perturbation] using hsum_convex.add hpsi_convex
    have hscaled_prox :
        StrongConvexOnWith (normSeminorm ℝ E) (model.L : ℝ) model.feasibleSet proxTerm := by
      refine ⟨model.proxFunction_isProxFunction.strongConvexOnWith.1, hL, ?_⟩
      intro u hu v hv a b ha hb hab
      have hprox :=
        model.proxFunction_isProxFunction.strongConvexOnWith.2.2 hu hv ha hb hab
      have hscaled :=
        mul_le_mul_of_nonneg_left hprox (show 0 ≤ (model.L : ℝ) by exact model.L.2)
      -- Scaling the prox term preserves the same strong-convexity shape with modulus `L`.
      calc
        proxTerm (a • u + b • v)
            = (model.L : ℝ) * model.proxFunction (a • u + b • v) := by
                rfl
        _ ≤ (model.L : ℝ) *
              (a * model.proxFunction u + b * model.proxFunction v -
                a * b * ((1 / 2 : ℝ) * ‖u - v‖ ^ (2 : ℕ))) := hscaled
        _ = a * proxTerm u + b * proxTerm v -
              a * b * (((model.L : ℝ) / 2) * ‖u - v‖ ^ (2 : ℕ)) := by
              dsimp [proxTerm]
              ring
    have hambient_eq :
        method.estimatingFunctionAmbient (k + 1) = fun z ↦ proxTerm z + perturbation z := by
      funext z
      dsimp [SimilarTrianglesMethod.estimatingFunctionAmbient, proxTerm, perturbation]
      ring
    have hambient_strong :
        StrongConvexOnWith (normSeminorm ℝ E) (model.L : ℝ) model.feasibleSet
          (method.estimatingFunctionAmbient (k + 1)) := by
      rw [hambient_eq]
      refine ⟨hscaled_prox.1, hL, ?_⟩
      intro u hu v hv a b ha hb hab
      have hprox := hscaled_prox.2.2 hu hv ha hb hab
      have hperturb := hperturb_convex.2 hu hv ha hb hab
      -- The prox term supplies the quadratic correction, and the perturbation is merely convex.
      calc
        (proxTerm + perturbation) (a • u + b • v)
            = proxTerm (a • u + b • v) + perturbation (a • u + b • v) := by
                rfl
        _ ≤
            (a * proxTerm u + b * proxTerm v -
                a * b * (((model.L : ℝ) / 2) * ‖u - v‖ ^ (2 : ℕ))) +
              (a * perturbation u + b * perturbation v) := add_le_add hprox hperturb
        _ = a * (proxTerm u + perturbation u) + b * (proxTerm v + perturbation v) -
              a * b * (((model.L : ℝ) / 2) * ‖u - v‖ ^ (2 : ℕ)) := by
              ring
    have hquad :=
      hambient_strong.quadratic_growth_of_isMinOn_of_mem
        (method.minimizingPoint_mem_feasibleSet (k + 1))
        (method.estimatingFunctionAmbient_isMinOn_succ k)
        x x.property
    -- Restrict the ambient quadratic-growth bound back to the subtype owner used in the theorem.
    rw [method.estimatingFunctionAmbient_restrict (k := k + 1)
      (hx := method.minimizingPoint_mem_feasibleSet (k + 1))] at hquad
    rw [method.estimatingFunctionAmbient_restrict (k := k + 1) (hx := x.property)] at hquad
    simpa [coe_normSeminorm, norm_sub_rev] using hquad
  · have hL_nonpos : (model.L : ℝ) ≤ 0 := le_of_not_gt hL
    have hL_zero : (model.L : ℝ) = 0 := by
      linarith [show 0 ≤ (model.L : ℝ) by exact model.L.2]
    have hmin :
        method.estimatingFunctionAmbient (k + 1) (method.v (k + 1)) ≤
          method.estimatingFunctionAmbient (k + 1) x :=
      (isMinOn_iff.mp (method.estimatingFunctionAmbient_isMinOn_succ k)) x x.property
    -- When `L = 0`, the quadratic term vanishes and minimality alone gives the estimate.
    rw [method.estimatingFunctionAmbient_restrict (k := k + 1)
      (hx := method.minimizingPoint_mem_feasibleSet (k + 1))] at hmin
    rw [method.estimatingFunctionAmbient_restrict (k := k + 1) (hx := x.property)] at hmin
    simpa [hL_zero] using hmin

-- Proof sketch: combine the quadratic-growth bound from the prox-center hypothesis at `k = 0`
-- with the standard estimating-sequence induction on feasible points using
-- `phi_eq_estimatingFunction`, the minimizing property `v_succ_isMin`, convexity of `f`, and
-- the update rules of `SimilarTrianglesMethod`.
/-- Theorem 6.2 [Chapter6_2.json:20]: equation `(6.1.20)` states that if `x_k`, `y_k`, and
`v_k` are generated by method `(6.1.19)`, then for every `k ≥ 0` and every feasible point
`x ∈ Q`,
`((k (k + 1)) / 4) \tilde f(x_k) + (L / 2) ‖v_k - x‖² ≤ φ_k(x)`, where
`\tilde f(x_k) = f(x_k) + Ψ(x_k)` is read through the canonical finite-real-part bridge on
`Q`. -/
theorem objective_le_estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (hx0 : NesterovIsProxCenter model.feasibleSet model.proxFunction (x0 : E))
    (k : ℕ) (x : model.feasibleSet) :
    (((k : ℝ) * (k + 1)) / 4) *
          (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) +
        ((model.L : ℝ) / 2) * ‖(method.v k : E) - x‖ ^ (2 : ℕ) ≤
      method.estimatingFunction k x := by
  induction k generalizing x with
  | zero =>
      -- The initial estimate is exactly the prox-center quadratic lower bound scaled by `L`.
      have hquad :=
        prox_center_quadratic_lower_bound model.proxFunction_isProxFunction hx0 x.property
      have hscaled :=
        mul_le_mul_of_nonneg_left hquad (show 0 ≤ (model.L : ℝ) by exact model.L.2)
      have hscaled' :
          ((model.L : ℝ) / 2) * ‖x - (x0 : E)‖ ^ (2 : ℕ) ≤
            (model.L : ℝ) * model.proxFunction x := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      rw [method.v_zero]
      simpa [estimatingFunction, norm_sub_rev] using hscaled'
  | succ k ih =>
      set Aprev : ℝ := ((k : ℝ) * (k + 1)) / 4
      set A : ℝ := ((((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) / 4)
      set a : ℝ := similarTrianglesEstimatingWeight k
      set τ : ℝ := (2 : ℝ) / ((k : ℝ) + 2)
      have hAprev_nonneg : 0 ≤ Aprev := by
        dsimp [Aprev]
        positivity
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        positivity
      have hτ_nonneg : 0 ≤ τ := by
        dsimp [τ]
        positivity
      have hone_sub_tau :
          1 - τ = (k : ℝ) / ((k : ℝ) + 2) := by
        dsimp [τ]
        field_simp
        ring
      have h_one_sub_nonneg : 0 ≤ 1 - τ := by
        rw [hone_sub_tau]
        positivity
      have hsum_tau : (1 - τ) + τ = 1 := by
        ring
      have hA_split : A = Aprev + a := by
        dsimp [A, Aprev, a]
        rw [similarTrianglesEstimatingWeight_def]
        norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        ring_nf
      have ha_eq : a = A * τ := by
        dsimp [A, a, τ]
        rw [similarTrianglesEstimatingWeight_def]
        norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        field_simp
        ring_nf
      have hAprev_eq : Aprev = A * (1 - τ) := by
        linarith [hA_split, ha_eq]
      have hAτsq :
          A * τ ^ (2 : ℕ) ≤ 1 := by
        have hrewrite :
            A * τ ^ (2 : ℕ) = ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
          calc
            A * τ ^ (2 : ℕ) = (A * τ) * τ := by
              ring
            _ = a * τ := by
              rw [← ha_eq]
            _ = (((k : ℝ) + 1) / 2) * ((2 : ℝ) / ((k : ℝ) + 2)) := by
              dsimp [a, τ]
              rw [similarTrianglesEstimatingWeight_def]
            _ = ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
              field_simp
        rw [hrewrite]
        have hden : 0 < (k : ℝ) + 2 := by
          positivity
        exact (div_le_iff₀ hden).2 (by nlinarith)
      have hiter :
          method (k + 1) = (1 - τ) • method k + τ • method.v (k + 1) := by
        -- Route correction: normalize the iterate step first so the source weighted identities
        -- can be consumed directly instead of hiding them inside ad hoc algebra.
        rw [method.x_succ k, similarTrianglesInterpolationPoint_def]
        simpa [τ, hone_sub_tau]
      have hinterp :
          method.interpolationPoint k = (1 - τ) • method k + τ • method.v k := by
        -- The interpolation point uses the same coefficient package as the successor iterate.
        rw [method.interpolationPoint_def]
        simpa [τ, hone_sub_tau]
      have hdisp :
          method (k + 1) - method.interpolationPoint k =
            τ • ((method.v (k + 1) : E) - method.v k) := by
        -- Subtract the two affine combinations to expose the textbook displacement identity.
        rw [hiter, hinterp]
        calc
          (1 - τ) • method k + τ • method.v (k + 1) -
              ((1 - τ) • method k + τ • method.v k)
              = τ • (method.v (k + 1) : E) - τ • (method.v k : E) := by
                  abel_nf
          _ = τ • ((method.v (k + 1) : E) - method.v k) := by
                  rw [smul_sub]
      have hiter_disp :
          method (k + 1) - method.interpolationPoint k =
            (1 - τ) • (method k - method.interpolationPoint k) +
              τ • (((method.v (k + 1) : E) - method.interpolationPoint k)) := by
        -- Recenter the successor displacement at `y_k` before applying the frozen gradient.
        rw [hiter]
        have hinterp_split :
            method.interpolationPoint k =
              (1 - τ) • method.interpolationPoint k + τ • method.interpolationPoint k := by
          rw [← add_smul, hsum_tau, one_smul]
        conv_lhs => rw [hinterp_split]
        rw [smul_sub, smul_sub]
        abel_nf
      have hgrad_split :
          A * model.smoothGradient (method.interpolationPoint k)
            (method (k + 1) - method.interpolationPoint k) =
            Aprev * model.smoothGradient (method.interpolationPoint k)
              (method k - method.interpolationPoint k) +
              a * model.smoothGradient (method.interpolationPoint k)
                (((method.v (k + 1) : E) - method.interpolationPoint k)) := by
        -- Apply the fixed linear form `∇f(y_k)` to the affine decomposition and rewrite weights.
        rw [hiter_disp, map_add, map_smul, map_smul, hAprev_eq, ha_eq]
        ring
      have hsupport :
          model.smoothPart (method k) ≥
            model.smoothPart (method.interpolationPoint k) +
              model.smoothGradient (method.interpolationPoint k)
                (method k - method.interpolationPoint k) := by
        -- Lower support at `y_k` turns the stage-`k` affine model into the actual value `f(x_k)`.
        exact smoothPart_lower_support_on_feasible (model := model)
          (x := method.interpolationPoint k) (y := method k)
          (method.interpolationPoint_mem_feasibleSet k) (method.iterate_mem_feasibleSet k)
      have hsupport_scaled :
          Aprev *
              (model.smoothPart (method.interpolationPoint k) +
                model.smoothGradient (method.interpolationPoint k)
                  (method k - method.interpolationPoint k)) ≤
            Aprev * model.smoothPart (method k) := by
        -- The previous-stage weight is nonnegative, so the support inequality scales directly.
        exact mul_le_mul_of_nonneg_left hsupport hAprev_nonneg
      have hupper :
          model.smoothPart (method (k + 1)) ≤
            model.smoothPart (method.interpolationPoint k) +
              model.smoothGradient (method.interpolationPoint k)
                (method (k + 1) - method.interpolationPoint k) +
              ((model.L : ℝ) / 2) * ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ) := by
        -- Upper-model control at `(y_k, x_{k+1})` gives the smooth contribution for the new step.
        exact smoothPart_upper_model_on_feasible (model := model)
          (x := method.interpolationPoint k) (y := method (k + 1))
          (method.interpolationPoint_mem_feasibleSet k) (method.iterate_mem_feasibleSet (k + 1))
      have hquad_term :
          A * (((model.L : ℝ) / 2) *
              ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) ≤
            ((model.L : ℝ) / 2) * ‖(method.v k : E) - method.v (k + 1)‖ ^ (2 : ℕ) := by
        -- The quadratic remainder contracts to the minimizer displacement via `x_{k+1} - y_k`.
        rw [hdisp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ_nonneg]
        calc
          A * (((model.L : ℝ) / 2) *
                (τ * ‖(method.v (k + 1) : E) - method.v k‖) ^ (2 : ℕ))
              = (A * τ ^ (2 : ℕ)) *
                  (((model.L : ℝ) / 2) * ‖(method.v (k + 1) : E) - method.v k‖ ^ (2 : ℕ)) := by
                  ring
          _ ≤ 1 *
                (((model.L : ℝ) / 2) * ‖(method.v (k + 1) : E) - method.v k‖ ^ (2 : ℕ)) := by
                gcongr
          _ = ((model.L : ℝ) / 2) * ‖(method.v k : E) - method.v (k + 1)‖ ^ (2 : ℕ) := by
                simp [norm_sub_rev]
      have hsmooth :
          A * model.smoothPart (method (k + 1)) ≤
            Aprev * model.smoothPart (method k) +
              a * (model.smoothPart (method.interpolationPoint k) +
                model.smoothGradient (method.interpolationPoint k)
                  (((method.v (k + 1) : E) - method.interpolationPoint k))) +
              ((model.L : ℝ) / 2) * ‖(method.v k : E) - method.v (k + 1)‖ ^ (2 : ℕ) := by
        have hupper_scaled :
            A * model.smoothPart (method (k + 1)) ≤
              A *
                (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (method (k + 1) - method.interpolationPoint k) +
                  ((model.L : ℝ) / 2) *
                    ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hupper hA_nonneg
        -- Combine the upper model, the lower support at `x_k`, and the coefficient identities.
        have hvalue_split :
            A * model.smoothPart (method.interpolationPoint k) =
              Aprev * model.smoothPart (method.interpolationPoint k) +
                a * model.smoothPart (method.interpolationPoint k) := by
          rw [hA_split]
          ring
        have hweighted_split :
            A * model.smoothPart (method.interpolationPoint k) +
                A * model.smoothGradient (method.interpolationPoint k)
                  (method (k + 1) - method.interpolationPoint k) =
              Aprev *
                (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (method k - method.interpolationPoint k)) +
                a * (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (((method.v (k + 1) : E) - method.interpolationPoint k))) := by
          linarith [hvalue_split, hgrad_split]
        have hweighted_full :
            A * model.smoothPart (method.interpolationPoint k) +
                A * model.smoothGradient (method.interpolationPoint k)
                  (method (k + 1) - method.interpolationPoint k) +
                A * (((model.L : ℝ) / 2) *
                  ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) =
              Aprev *
                (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (method k - method.interpolationPoint k)) +
                a * (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (((method.v (k + 1) : E) - method.interpolationPoint k))) +
                A * (((model.L : ℝ) / 2) *
                  ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) := by
          rw [hweighted_split]
        calc
          A * model.smoothPart (method (k + 1))
              ≤ A *
                  (model.smoothPart (method.interpolationPoint k) +
                    model.smoothGradient (method.interpolationPoint k)
                      (method (k + 1) - method.interpolationPoint k) +
                    ((model.L : ℝ) / 2) *
                      ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) :=
                hupper_scaled
          _ = A * model.smoothPart (method.interpolationPoint k) +
                A * model.smoothGradient (method.interpolationPoint k)
                  (method (k + 1) - method.interpolationPoint k) +
                A * (((model.L : ℝ) / 2) *
                  ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) := by
                ring
          _ = Aprev *
                (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (method k - method.interpolationPoint k)) +
                a * (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (((method.v (k + 1) : E) - method.interpolationPoint k))) +
                A * (((model.L : ℝ) / 2) *
                  ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) := by
                exact hweighted_full
          _ ≤ Aprev * model.smoothPart (method k) +
                a * (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (((method.v (k + 1) : E) - method.interpolationPoint k))) +
                A * (((model.L : ℝ) / 2) *
                  ‖method (k + 1) - method.interpolationPoint k‖ ^ (2 : ℕ)) := by
                linarith [hsupport_scaled]
          _ ≤ Aprev * model.smoothPart (method k) +
                a * (model.smoothPart (method.interpolationPoint k) +
                  model.smoothGradient (method.interpolationPoint k)
                    (((method.v (k + 1) : E) - method.interpolationPoint k))) +
                ((model.L : ℝ) / 2) * ‖(method.v k : E) - method.v (k + 1)‖ ^ (2 : ℕ) := by
                linarith [hquad_term]
      have hpsi :
          withTopRealPart model.nonsmoothPart (method (k + 1)) ≤
            (1 - τ) * withTopRealPart model.nonsmoothPart (method k) +
              τ * withTopRealPart model.nonsmoothPart (method.v (k + 1)) := by
        -- Convexity of `Ψ` along the iterate update supplies the weighted nonsmooth estimate.
        rw [hiter]
        exact model.nonsmoothPart_closedConvex.convexOn_withTopRealPart.2
          (method.iterate_mem_feasibleSet k)
          (method.minimizingPoint_mem_feasibleSet (k + 1))
          h_one_sub_nonneg hτ_nonneg hsum_tau
      have hpsi_scaled :
          A * withTopRealPart model.nonsmoothPart (method (k + 1)) ≤
            Aprev * withTopRealPart model.nonsmoothPart (method k) +
              a * withTopRealPart model.nonsmoothPart (method.v (k + 1)) := by
        have hpsi_mul := mul_le_mul_of_nonneg_left hpsi hA_nonneg
        calc
          A * withTopRealPart model.nonsmoothPart (method (k + 1))
              ≤ A *
                  ((1 - τ) * withTopRealPart model.nonsmoothPart (method k) +
                    τ * withTopRealPart model.nonsmoothPart (method.v (k + 1))) := hpsi_mul
          _ = Aprev * withTopRealPart model.nonsmoothPart (method k) +
                a * withTopRealPart model.nonsmoothPart (method.v (k + 1)) := by
                rw [hAprev_eq, ha_eq]
                ring
      have hih_at_v :
          Aprev * model.smoothPart (method k) +
              Aprev * withTopRealPart model.nonsmoothPart (method k) +
              ((model.L : ℝ) / 2) * ‖(method.v k : E) - method.v (k + 1)‖ ^ (2 : ℕ) ≤
            method.estimatingFunction k (method.v (k + 1)) := by
        -- Evaluate the induction hypothesis at the new minimizing point `v_{k+1}`.
        simpa only [Aprev, add_mul, mul_add, norm_sub_rev] using
          ih (method.v (k + 1))
      have hphi_succ :
          method.estimatingFunction (k + 1) (method.v (k + 1)) =
            method.estimatingFunction k (method.v (k + 1)) +
              a * (model.smoothPart (method.interpolationPoint k) +
                model.smoothGradient (method.interpolationPoint k)
                  (((method.v (k + 1) : E) - method.interpolationPoint k))) +
              a * withTopRealPart model.nonsmoothPart (method.v (k + 1)) := by
        -- Expand the closed-form estimating function at `v_{k+1}` by one update step.
        simpa [a] using method.estimatingFunction_succ k (method.v (k + 1))
      have hmaster_aux :
          A * model.smoothPart (method (k + 1)) +
              A * withTopRealPart model.nonsmoothPart (method (k + 1)) ≤
            method.estimatingFunction k (method.v (k + 1)) +
              a * (model.smoothPart (method.interpolationPoint k) +
                model.smoothGradient (method.interpolationPoint k)
                  (((method.v (k + 1) : E) - method.interpolationPoint k))) +
              a * withTopRealPart model.nonsmoothPart (method.v (k + 1)) := by
        -- Add the smooth and nonsmooth estimates, then absorb the quadratic term with the IH.
        linarith [hsmooth, hpsi_scaled, hih_at_v]
      have hmaster :
          A * (model.smoothPart (method (k + 1)) +
              withTopRealPart model.nonsmoothPart (method (k + 1))) ≤
            method.estimatingFunction (k + 1) (method.v (k + 1)) := by
        -- Repackage the master inequality in the source form `A_{k+1} \tilde f(x_{k+1}) ≤ φ_{k+1}(v_{k+1})`.
        rw [hphi_succ]
        simpa [mul_add] using hmaster_aux
      have hquad_x :
          method.estimatingFunction (k + 1) (method.v (k + 1)) +
              ((model.L : ℝ) / 2) * ‖(method.v (k + 1) : E) - x‖ ^ (2 : ℕ) ≤
            method.estimatingFunction (k + 1) x := by
        -- Quadratic growth at the minimizer transfers the estimate from `v_{k+1}` to arbitrary `x`.
        simpa using method.estimatingFunction_quadratic_growth_succ k x
      have hfinal :
          A * (model.smoothPart (method (k + 1)) +
              withTopRealPart model.nonsmoothPart (method (k + 1))) +
              ((model.L : ℝ) / 2) * ‖(method.v (k + 1) : E) - x‖ ^ (2 : ℕ) ≤
            method.estimatingFunction (k + 1) x := by
        linarith [hmaster, hquad_x]
      simpa [A] using hfinal

-- Proof sketch: apply `objective_le_estimatingFunction` with `x = xStar`, unpack the canonical
-- argmin owner hypothesis through `mem_constrainedArgmin_iff` to recover feasibility and the
-- minimizing property of `xStar` for the composite objective, and divide by
-- `((k (k + 1)) / 4)` for `k ≥ 1`.
/-- The suboptimality estimate `(6.1.21)` obtained from the estimating-function lower bound:
if `xStar` is an optimal solution of problem `(6.1.18)`, then for every `k ≥ 1` the iterate
suboptimality and the squared distance to `v_k` satisfy the displayed accelerated rate
estimate. -/
theorem suboptimality_bound
    (method : SimilarTrianglesMethod model x0)
    (hx0 : NesterovIsProxCenter model.feasibleSet model.proxFunction (x0 : E))
    (xStar : E)
    (hxStar : xStar ∈
      argmin[model.feasibleSet]
        (fun x ↦ model.smoothPart x + withTopRealPart model.nonsmoothPart x))
    {k : ℕ} (hk : 1 ≤ k) :
    (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
        (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) +
        (2 * (model.L : ℝ) / ((k : ℝ) * (k + 1))) * ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) ≤
      (4 * (model.L : ℝ) * model.proxFunction xStar) / ((k : ℝ) * (k + 1)) := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem, _hxStar_min⟩
  set A : ℝ := ((k : ℝ) * (k + 1)) / 4
  have hk_nat_pos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk_nat_pos
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hmain :
      A * (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) +
          ((model.L : ℝ) / 2) * ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) ≤
        method.estimatingFunction k ⟨xStar, hxStar_mem⟩ := by
    -- Start from the estimate-sequence lower bound specialized at the optimal solution `xStar`.
    simpa only [A] using method.objective_le_estimatingFunction hx0 k ⟨xStar, hxStar_mem⟩
  have hsum_affine :
      Finset.sum (Finset.range k) (fun i ↦
          similarTrianglesEstimatingWeight i *
            (model.smoothPart (method.interpolationPoint i) +
              model.smoothGradient (method.interpolationPoint i)
                (xStar - method.interpolationPoint i))) ≤
        Finset.sum (Finset.range k) (fun i ↦
          similarTrianglesEstimatingWeight i * model.smoothPart xStar) := by
    -- Each affine model at `y_i` underestimates `f(xStar)`, so the weighted sum does as well.
    refine Finset.sum_le_sum ?_
    intro i hi
    have hsupport_i :
        model.smoothPart xStar ≥
          model.smoothPart (method.interpolationPoint i) +
            model.smoothGradient (method.interpolationPoint i)
              (xStar - method.interpolationPoint i) := by
      exact smoothPart_lower_support_on_feasible (model := model)
        (x := method.interpolationPoint i) (y := xStar)
        (method.interpolationPoint_mem_feasibleSet i) hxStar_mem
    have hweight_nonneg : 0 ≤ similarTrianglesEstimatingWeight i := by
      rw [similarTrianglesEstimatingWeight_def]
      positivity
    exact mul_le_mul_of_nonneg_left hsupport_i hweight_nonneg
  have hphi_upper :
      method.estimatingFunction k ⟨xStar, hxStar_mem⟩ ≤
        (model.L : ℝ) * model.proxFunction xStar +
          A * (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) := by
    -- Replace every affine smooth term in `φ_k(xStar)` by `f(xStar)` and collapse the weights.
    rw [method.estimatingFunction_apply]
    calc
      (model.L : ℝ) * model.proxFunction xStar +
          Finset.sum (Finset.range k) (fun i ↦
            similarTrianglesEstimatingWeight i *
              (model.smoothPart (method.interpolationPoint i) +
                model.smoothGradient (method.interpolationPoint i)
                  (xStar - method.interpolationPoint i))) +
          A * withTopRealPart model.nonsmoothPart xStar
          ≤
        (model.L : ℝ) * model.proxFunction xStar +
          Finset.sum (Finset.range k) (fun i ↦
            similarTrianglesEstimatingWeight i * model.smoothPart xStar) +
          A * withTopRealPart model.nonsmoothPart xStar := by
            gcongr
      _ = (model.L : ℝ) * model.proxFunction xStar +
            (Finset.sum (Finset.range k) similarTrianglesEstimatingWeight) *
              model.smoothPart xStar +
            A * withTopRealPart model.nonsmoothPart xStar := by
            rw [Finset.sum_mul]
      _ = (model.L : ℝ) * model.proxFunction xStar +
            A * model.smoothPart xStar +
            A * withTopRealPart model.nonsmoothPart xStar := by
            rw [sum_similarTrianglesEstimatingWeight]
      _ = (model.L : ℝ) * model.proxFunction xStar +
            A * (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) := by
            ring
  have hbound :
      A * (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) +
          ((model.L : ℝ) / 2) * ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) ≤
        (model.L : ℝ) * model.proxFunction xStar +
          A * (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) := by
    -- The lower estimate from Theorem 6.2 meets the upper estimate on `φ_k(xStar)`.
    exact le_trans hmain hphi_upper
  have hbound_sub :
      A * ((model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
            (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar)) +
          ((model.L : ℝ) / 2) * ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) ≤
        (model.L : ℝ) * model.proxFunction xStar := by
    -- Move the optimal objective value to the left before dividing by `A_k`.
    linarith [hbound]
  have hcoef_norm :
      A * ((2 * (model.L : ℝ)) / ((k : ℝ) * (k + 1))) = (model.L : ℝ) / 2 := by
    have hden_ne : ((k : ℝ) * (k + 1)) ≠ 0 := by
      positivity
    dsimp [A]
    field_simp [hden_ne]
    ring_nf
  have hcoef_rhs :
      A * ((4 * (model.L : ℝ) * model.proxFunction xStar) / ((k : ℝ) * (k + 1))) =
        (model.L : ℝ) * model.proxFunction xStar := by
    have hden_ne : ((k : ℝ) * (k + 1)) ≠ 0 := by
      positivity
    dsimp [A]
    field_simp [hden_ne]
  have hscaled :
      A *
          ((model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
              (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) +
            (2 * (model.L : ℝ) / ((k : ℝ) * (k + 1))) *
              ‖(method.v k : E) - xStar‖ ^ (2 : ℕ)) ≤
        A * ((4 * (model.L : ℝ) * model.proxFunction xStar) / ((k : ℝ) * (k + 1))) := by
    -- After multiplying by `A_k = k (k + 1) / 4`, both rational coefficients collapse.
    calc
      A *
          ((model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
              (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) +
            (2 * (model.L : ℝ) / ((k : ℝ) * (k + 1))) *
              ‖(method.v k : E) - xStar‖ ^ (2 : ℕ))
          = A *
              ((model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
                (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar)) +
              (A * ((2 * (model.L : ℝ)) / ((k : ℝ) * (k + 1)))) *
                ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) := by
              ring
      _ = A *
              ((model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
                (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar)) +
              ((model.L : ℝ) / 2) * ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) := by
              rw [hcoef_norm]
      _ ≤ (model.L : ℝ) * model.proxFunction xStar := hbound_sub
      _ = A * ((4 * (model.L : ℝ) * model.proxFunction xStar) / ((k : ℝ) * (k + 1))) := by
              rw [hcoef_rhs]
  nlinarith [hscaled, hA_pos]

end SimilarTrianglesMethod

end
