/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

variable (n : ℕ)

local notation "F" => Fin n → ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 2.5 lies in the finite-dimensional strong-convexity domain for entropy on the
standard simplex.

Sampled owner-style declarations before refining this file:
* project `StrongConvexOnWith` in `Definition_2_14`
* mathlib `stdSimplex`
* mathlib `convex_stdSimplex`
* mathlib `WithLp.linearEquiv`
* mathlib `PiLp.norm_eq_sum`

Best owner abstraction for the main theorem:
* `StrongConvexOnWith p μ Q f` on the canonical function-space simplex owner
  `Q = stdSimplex ℝ (Fin n)`

Primitive data:
* the canonical simplex owner `stdSimplex ℝ (Fin n)`
* the source-facing entropy function `entropyFunction n : (Fin n → ℝ) → ℝ`

Derived API:
* the owner `ℓ₁` seminorm `simplexL1Seminorm n` on `Fin n → ℝ`, obtained by pulling back the
  owner `L¹` norm on `WithLp 1 (Fin n → ℝ)`
* its coordinate formula `simplexL1Seminorm_apply`
* the Euclidean bridge `EuclideanSpace.l1Seminorm n`, obtained by pulling back
  `simplexL1Seminorm n` along `EuclideanSpace.equiv`
* the coordinate-pullback bridge theorem obtained from Proposition 2.5 via `EuclideanSpace.equiv`

Source/core/bridge triage:
* source-facing: `entropyFunction n` and its strong-convexity statement on `stdSimplex ℝ (Fin n)`
* core/canonical: the owner predicate `StrongConvexOnWith`
* bridge/view: the Euclidean coordinate pullback
  `(EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n)` and `EuclideanSpace.l1Seminorm n`
  as the coordinate pullback of the owner `simplexL1Seminorm n`
-/

/-- The canonical `ℓ₁` seminorm on `Fin n → ℝ`, obtained by pulling back the owner `L¹` norm on
`WithLp 1 (Fin n → ℝ)` along `WithLp.toLp`. -/
private abbrev functionL1Equiv : F ≃ₗ[ℝ] WithLp 1 F :=
  (WithLp.linearEquiv 1 ℝ F).symm

/-- The canonical `ℓ₁` seminorm on `Fin n → ℝ`. -/
abbrev simplexL1Seminorm : Seminorm ℝ F :=
  Seminorm.comp (normSeminorm ℝ (WithLp 1 F)) (functionL1Equiv n).toLinearMap

private theorem simplexL1Seminorm_toLp (x : F) :
    simplexL1Seminorm n x = ‖WithLp.toLp (1 : ENNReal) x‖ := by
  change ‖functionL1Equiv n x‖ = ‖WithLp.toLp (1 : ENNReal) x‖
  rfl

/-- Applying the canonical `ℓ₁` seminorm to a function sums the absolute values of its
coordinates. -/
theorem simplexL1Seminorm_apply (x : F) :
    simplexL1Seminorm n x = ∑ i, ‖x i‖ := by
  rw [simplexL1Seminorm_toLp]
  simpa [Real.norm_eq_abs] using
    PiLp.norm_eq_sum (by simp : 0 < (1 : ENNReal).toReal) (WithLp.toLp (1 : ENNReal) x)

/-- The canonical `ℓ₁` seminorm on `Fin n → ℝ` is a norm. -/
instance simplexL1Seminorm_isNorm : Seminorm.IsNorm (simplexL1Seminorm n : Seminorm ℝ F) where
  eq_zero_of_map_eq_zero := by
    intro x hx
    exact (functionL1Equiv n).map_eq_zero_iff.mp <|
      norm_eq_zero.mp <| by
        simpa [simplexL1Seminorm, functionL1Equiv] using hx

/-- The entropy function `x ↦ ∑ᵢ xᵢ log xᵢ` on the canonical simplex ambient space
`Fin n → ℝ`. -/
def entropyFunction : F → ℝ :=
  fun x ↦ ∑ i, x i * Real.log (x i)

/-- Evaluating `entropyFunction` expands to the coordinatewise entropy sum. -/
theorem entropyFunction_apply (x : F) :
    entropyFunction n x = ∑ i, x i * Real.log (x i) :=
  rfl

/-- Helper for Proposition 2.5: the Euclidean-coordinate realization of the entropy function. -/
private def entropyCoordinateFunction : E → ℝ :=
  fun x ↦ entropyFunction n ((EuclideanSpace.equiv (Fin n) ℝ) x)

/-- Helper for Proposition 2.5: the coordinate `ℓ₁` seminorm used for the Hessian argument on
`ℝⁿ`. -/
private abbrev coordinateL1Seminorm : Seminorm ℝ E :=
  Seminorm.comp (simplexL1Seminorm n) (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

/-- Helper for Proposition 2.5: the derivative of the explicit Euclidean entropy gradient at a
strictly positive point. -/
private abbrev entropyCoordinateGradientFDeriv (x : E) : E →L[ℝ] E :=
  (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin n ↦
      (x i)⁻¹ • (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))

/-- Helper for Proposition 2.5: the strict subprobability simplex
`{x : ℝⁿ | x_i > 0, ∑ i, x_i < 1}` is the open owner domain used for the Hessian argument. -/
private def openSubprobabilitySimplex : Set E :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

/-- Helper for Proposition 2.5: the fixed interior anchor used to approach boundary simplex
points from the strict subprobability simplex. -/
private def subprobabilityInteriorAnchor : E :=
  WithLp.toLp 2 fun _ ↦ ((2 : ℝ) * (n + 1))⁻¹

/-- Helper for Proposition 2.5: the Euclidean coordinate `ℓ₁` seminorm sums the absolute values
of the coordinates. -/
private theorem coordinateL1Seminorm_apply (x : E) :
    coordinateL1Seminorm n x = ∑ i, ‖x i‖ := by
  simpa [coordinateL1Seminorm] using
    simplexL1Seminorm_apply n ((EuclideanSpace.equiv (Fin n) ℝ) x)

/-- Helper for Proposition 2.5: membership in the Euclidean preimage of the standard simplex is
the coordinatewise nonnegativity-plus-sum-one condition. -/
private theorem mem_preimage_stdSimplex_iff {x : E} :
    x ∈ ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n)) ↔
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
  simp [stdSimplex]

/-- Helper for Proposition 2.5: the strict subprobability simplex is open. -/
private theorem isOpen_openSubprobabilitySimplex :
    IsOpen (openSubprobabilitySimplex n) := by
  -- Each coordinate positivity constraint is open, and the strict sum bound is open as well.
  have hpos : IsOpen {x : E | ∀ i, 0 < x i} := by
    simpa [Set.setOf_forall] using
      isOpen_iInter_of_finite fun i : Fin n ↦
        isOpen_lt continuous_const
          (PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i)
  have hsum : IsOpen {x : E | ∑ i, x i < 1} := by
    have hcont : Continuous fun x : E ↦ ∑ i, x i := by
      exact continuous_finset_sum _ fun i _ ↦
        PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i
    exact isOpen_lt hcont continuous_const
  simpa [openSubprobabilitySimplex, Set.setOf_and] using hpos.inter hsum

/-- Helper for Proposition 2.5: the strict subprobability simplex is convex. -/
private theorem convex_openSubprobabilitySimplex :
    Convex ℝ (openSubprobabilitySimplex n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    -- Positivity is preserved because at least one endpoint weight is positive.
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0
      subst hb1
      simpa [openSubprobabilitySimplex] using hy.1 i
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hax_pos : 0 < a * x i := mul_pos ha_pos (hx.1 i)
      have hyb_nonneg : 0 ≤ b * y i := mul_nonneg hb (hy.1 i).le
      calc
        0 < a * x i + 0 := by linarith
        _ ≤ a * x i + b * y i := by linarith
        _ = (a • x + b • y) i := by simp [smul_eq_mul]
  · -- The sum constraint is affine, so the strict upper bound is preserved by convexity.
    have hxsum : ∑ i, x i < 1 := hx.2
    have hysum : ∑ i, y i < 1 := hy.2
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0
      subst hb1
      simpa [smul_eq_mul] using hy.2
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        subst hb0
        subst ha1
        simpa [smul_eq_mul] using hx.2
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        calc
          ∑ i, (a • x + b • y) i = a * ∑ i, x i + b * ∑ i, y i := by
            simp [smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
          _ < a * 1 + b * 1 := by
                have hax : a * ∑ i, x i < a := by nlinarith
                have hby : b * ∑ i, y i < b := by nlinarith
                linarith
          _ = 1 := by linarith

/-- Helper for Proposition 2.5: the anchor point has strictly positive coordinates. -/
private theorem subprobabilityInteriorAnchor_pos (i : Fin n) :
    0 < subprobabilityInteriorAnchor n i := by
  -- The anchor is the constant vector with value `1 / (2 (n + 1))`.
  simp [subprobabilityInteriorAnchor]
  positivity

/-- Helper for Proposition 2.5: the anchor point lies strictly below the simplex nesterovHyperplane. -/
private theorem subprobabilityInteriorAnchor_sum_lt_one :
    ∑ i, subprobabilityInteriorAnchor n i < 1 := by
  -- The anchor sum is `n / (2 (n + 1))`, hence strictly smaller than `1`.
  have hsum :
      ∑ i, subprobabilityInteriorAnchor n i = (n : ℝ) / ((2 : ℝ) * (n + 1)) := by
    simp [subprobabilityInteriorAnchor, div_eq_mul_inv]
  rw [hsum]
  have hden : ((2 : ℝ) * (n + 1)) ≠ 0 := by positivity
  field_simp [hden]
  nlinarith

/-- Helper for Proposition 2.5: the Euclidean Riesz functional is the sum of the coordinate
projections weighted by the coordinates of the representing vector. -/
private theorem toDual_eq_sum_pi_proj (v : E) :
    (InnerProductSpace.toDual ℝ E) v =
      ∑ i : Fin n,
        v i • (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ) := by
  ext h
  -- Identify both linear forms by evaluating them on an arbitrary vector.
  change inner ℝ v h = _
  rw [PiLp.inner_apply]
  -- On Euclidean coordinates, both sides are the same finite sum `∑ i, hᵢ vᵢ`.
  change (∑ i : Fin n, h i * v i) = _
  simp [mul_comm]

/-- Helper for Proposition 2.5: the Euclidean-coordinate entropy function is continuous. -/
private theorem entropyCoordinateFunction_continuous :
    Continuous (entropyCoordinateFunction n) := by
  -- Continuity follows termwise from the continuous extension of `x ↦ x log x`.
  -- Each coordinate term is continuous after composing with the corresponding projection.
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Continuous fun x : E ↦ x i * Real.log (x i) := by
    intro i hi
    exact Real.continuous_mul_log.comp
      (PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i)
  -- Summing the coordinate terms recovers the entropy function.
  simpa [entropyCoordinateFunction, entropyFunction] using continuous_finset_sum _ hterms

/-- Helper for Proposition 2.5: on the strict subprobability simplex, each boundary simplex point
can be joined to the fixed anchor while staying inside the open owner domain. -/
private theorem preimage_stdSimplex_segment_anchor_mem_openSubprobabilitySimplex
    {x : E} (hx : x ∈ ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n)))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (1 - t) • x + t • subprobabilityInteriorAnchor n ∈ openSubprobabilitySimplex n := by
  have hx' : (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
    simpa using (mem_preimage_stdSimplex_iff (n := n) (x := x)).mp hx
  refine ⟨?_, ?_⟩
  · intro i
    -- The positive anchor makes every positive-time perturbation land in the strict interior.
    have hanchor : 0 < subprobabilityInteriorAnchor n i :=
      subprobabilityInteriorAnchor_pos (n := n) i
    have hright : 0 < t * subprobabilityInteriorAnchor n i := mul_pos ht.1 hanchor
    have hleft : 0 ≤ (1 - t) * x i := mul_nonneg (sub_nonneg.mpr ht.2) (hx'.1 i)
    calc
      0 < 0 + t * subprobabilityInteriorAnchor n i := by simpa using hright
      _ ≤ (1 - t) * x i + t * subprobabilityInteriorAnchor n i := by linarith
      _ = ((1 - t) • x + t • subprobabilityInteriorAnchor n) i := by
            simp [smul_eq_mul]
  · -- The sum interpolates between `1` and the anchor sum, so it becomes strict for `t > 0`.
    have hanchor : ∑ i, subprobabilityInteriorAnchor n i < 1 :=
      subprobabilityInteriorAnchor_sum_lt_one (n := n)
    calc
      ∑ i, ((1 - t) • x + t • subprobabilityInteriorAnchor n) i
          = (1 - t) * ∑ i, x i + t * ∑ i, subprobabilityInteriorAnchor n i := by
              simp [smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
      _ < 1 := by
            nlinarith [hx'.2, hanchor, ht.1, ht.2]

/-- Helper for Proposition 2.5: on the positive orthant, the Euclidean-coordinate entropy
gradient is the coordinate vector `log x + 1`. -/
private theorem entropyCoordinateFunction_hasGradientAt_of_pos
    {x : E} (hx : ∀ i, 0 < x i) :
    HasGradientAt
      (entropyCoordinateFunction n)
      (WithLp.toLp 2 fun i ↦ Real.log (x i) + 1)
      x := by
  -- Route correction: work with the Fréchet derivative first, then identify it with the Riesz
  -- representative of the Euclidean gradient via `toDual_eq_sum_pi_proj`.
  have hsum :
      HasFDerivAt
        (entropyCoordinateFunction n)
        (∑ i : Fin n,
          (Real.log (x i) + 1) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))
        x := by
    have hterms :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          HasFDerivAt
            (fun y : E ↦ y i * Real.log (y i))
            (((Real.log (x i) + 1) : ℝ) •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))
            x := by
      intro i hi
      -- Differentiate the one-variable entropy term after the coordinate projection.
      have happly :
          HasFDerivAt
            (fun y : E ↦ y i)
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)
            x := by
        simpa using PiLp.hasFDerivAt_apply (2 : ENNReal) x i
      have hscalar :
          HasDerivAt
            (fun t : ℝ ↦ t * Real.log t)
            (Real.log (x i) + 1)
            (x i) := by
        exact Real.hasDerivAt_mul_log (hx i).ne'
      simpa [Function.comp] using hscalar.comp_hasFDerivAt x happly
    -- Summing the coordinate derivatives gives the Fréchet derivative of the whole entropy sum.
    convert HasFDerivAt.sum hterms using 1
    funext y
    simp [entropyCoordinateFunction, entropyFunction]
  have hfrechet :
      HasFDerivAt
        (entropyCoordinateFunction n)
        ((InnerProductSpace.toDual ℝ E) (WithLp.toLp 2 fun i ↦ Real.log (x i) + 1))
        x := by
    -- The summed coordinate functional is exactly the Riesz functional of `log x + 1`.
    simpa [toDual_eq_sum_pi_proj (n := n) (WithLp.toLp 2 fun i ↦ Real.log (x i) + 1)] using hsum
  -- Convert the Fréchet derivative into the Euclidean gradient witness.
  simpa using hfrechet.hasGradientAt

/-- Helper for Proposition 2.5: the Euclidean-coordinate entropy function is `C²` on the strict
subprobability simplex. -/
private theorem entropy_contDiffOn_open_subprobability_simplex :
    ContDiffOn ℝ 2 (entropyCoordinateFunction n) (openSubprobabilitySimplex n) := by
  intro x hx
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContDiffWithinAt
          ℝ 2
          (fun y : E ↦ y i * Real.log (y i))
          (openSubprobabilitySimplex n)
          x := by
    intro i hi
    -- Each coordinate projection is smooth, and positivity on the open simplex allows `log`.
    have happly :
        ContDiffWithinAt
          ℝ 2
          (fun y : E ↦ y i)
          (openSubprobabilitySimplex n)
          x := by
      have hcont : ContDiffAt ℝ 2 (fun y : E ↦ y i) x := by
        simpa [Function.comp] using
          (contDiff_apply ℝ ℝ (n := (2 : WithTop ℕ∞)) i).contDiffAt.comp x
            (((EuclideanSpace.equiv (Fin n) ℝ).contDiff (n := (2 : WithTop ℕ∞))).contDiffAt)
      exact hcont.contDiffWithinAt
    have hlog :
        ContDiffWithinAt
          ℝ 2
          (fun y : E ↦ Real.log (y i))
          (openSubprobabilitySimplex n)
          x := by
      exact happly.log (hx.1 i).ne'
    exact happly.mul hlog
  -- Summing the coordinate `C²` terms gives `C²` regularity of the entropy sum.
  simpa [entropyCoordinateFunction, entropyFunction] using ContDiffWithinAt.sum hterms

/-- Helper for Proposition 2.5: near a strict subprobability point, the Euclidean entropy
gradient has the coordinate formula `x ↦ log x + 1`. -/
private theorem entropyCoordinateFunction_hasFDerivAt_gradient_of_mem_openSubprobabilitySimplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) :
    HasFDerivAt
      (gradient (entropyCoordinateFunction n))
      (entropyCoordinateGradientFDeriv (n := n) x)
      x := by
  -- Route correction: differentiate the explicit positive-orthant gradient field, then replace
  -- the totalized gradient by this field on a neighborhood of the positive point.
  let G : E → E := fun y ↦ WithLp.toLp 2 fun i ↦ Real.log (y i) + 1
  let H : E → Fin n → ℝ := fun y i ↦ Real.log (y i) + 1
  let H' : E →L[ℝ] Fin n → ℝ :=
    ContinuousLinearMap.pi fun i : Fin n ↦
      ((x i)⁻¹ : ℝ) •
        (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)
  have hEq : gradient (entropyCoordinateFunction n) =ᶠ[nhds x] G := by
    have hpos : {y : E | ∀ i : Fin n, 0 < y i} ∈ nhds x := by
      have hopen : IsOpen {y : E | ∀ i : Fin n, 0 < y i} := by
        simpa [Set.setOf_forall] using
          isOpen_iInter_of_finite fun i : Fin n ↦
            isOpen_lt continuous_const
              (PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i)
      exact hopen.mem_nhds hx.1
    filter_upwards [hpos] with y hy
    exact (entropyCoordinateFunction_hasGradientAt_of_pos (n := n) hy).gradient
  have hH : HasFDerivAt H H' x := by
    rw [hasFDerivAt_pi]
    intro i
    have happly :
        HasFDerivAt
          (fun y : E ↦ y i)
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)
          x := by
      simpa using PiLp.hasFDerivAt_apply (2 : ENNReal) x i
    have hlog :
        HasFDerivAt
          (fun y : E ↦ Real.log (y i))
          (((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))
          x := by
      simpa [Function.comp] using (Real.hasDerivAt_log (hx.1 i).ne').comp_hasFDerivAt x happly
    -- The added constant `1` does not change the derivative.
    simpa [H, H'] using hlog.add_const (1 : ℝ)
  have hToLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin n → ℝ) → E)
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
        (H x) := by
    simpa using PiLp.hasFDerivAt_toLp (2 : ENNReal) (H x)
  let T : (Fin n → ℝ) →L[ℝ] E :=
    (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  have hG :
      HasFDerivAt
        G
        (T.comp H')
        x := by
    -- First differentiate the coordinate function `H`, then package the coordinates with `toLp`.
    simpa [G, H, T] using hToLp.comp x hH
  -- Replace the abstract gradient by its explicit coordinate formula near the positive point.
  simpa [entropyCoordinateGradientFDeriv, H'] using hG.congr_of_eventuallyEq hEq

/-- Helper for Proposition 2.5: on the strict subprobability simplex, the Euclidean entropy
Hessian acts diagonally with entries `x_i⁻¹`. -/
private theorem entropy_hessian_apply_on_open_subprobability_simplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) (h : E) :
    hessian (entropyCoordinateFunction n) x h = WithLp.toLp 2 fun i ↦ h i / x i := by
  have hderiv :=
    entropyCoordinateFunction_hasFDerivAt_gradient_of_mem_openSubprobabilitySimplex (n := n) hx
  -- The Hessian is the derivative of the gradient, now identified with the explicit diagonal map.
  change fderiv ℝ (gradient (entropyCoordinateFunction n)) x h = _
  rw [hderiv.fderiv]
  ext i
  simp [entropyCoordinateGradientFDeriv, div_eq_mul_inv, mul_comm]

/-- Helper for Proposition 2.5: the Euclidean entropy Hessian quadratic form is
`∑ i, h_i^2 / x_i` on the strict subprobability simplex. -/
private theorem entropy_hessian_quadratic_form_on_open_subprobability_simplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) (h : E) :
    inner ℝ (hessian (entropyCoordinateFunction n) x h) h =
      ∑ i, (h i) ^ (2 : ℕ) / x i := by
  -- Rewrite the Hessian by the explicit diagonal formula, then expand the Euclidean inner product.
  rw [entropy_hessian_apply_on_open_subprobability_simplex (n := n) hx h]
  simpa [pow_two, dotProduct, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 fun i ↦ h i / x i) h)

/-- Helper for Proposition 2.5: the Euclidean entropy Hessian dominates the square of the
coordinate `ℓ₁` seminorm on the strict subprobability simplex. -/
private theorem entropy_hessian_lower_bound_l1_on_open_subprobability_simplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) (h : E) :
    (coordinateL1Seminorm n h) ^ (2 : ℕ) ≤
      inner ℝ (hessian (entropyCoordinateFunction n) x h) h := by
  rw [entropy_hessian_quadratic_form_on_open_subprobability_simplex (n := n) hx h]
  rw [coordinateL1Seminorm_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let s : ℝ := ∑ i : Fin n, x i
    let A : ℝ := ∑ i : Fin n, ‖h i‖
    let B : ℝ := ∑ i : Fin n, ‖h i‖ ^ (2 : ℕ) / x i
    have hs_pos : 0 < s := by
      dsimp [s]
      have hi0 : 0 < x i0 := hx.1 i0
      exact lt_of_lt_of_le hi0 <|
        Finset.single_le_sum (fun i hi => (hx.1 i).le) (Finset.mem_univ i0)
    have hs_le_one : s ≤ 1 := le_of_lt hx.2
    have hB_nonneg : 0 ≤ B := by
      refine Finset.sum_nonneg fun i hi ↦ ?_
      have hxi : 0 ≤ x i := (hx.1 i).le
      positivity
    have hTitu :
        A ^ (2 : ℕ) / s ≤ B := by
      dsimp [A, B, s]
      simpa [Real.norm_eq_abs, sq_abs] using
        (Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin n)) (fun i ↦ ‖h i‖)
          (fun i hi ↦ hx.1 i))
    have hmain : A ^ (2 : ℕ) ≤ s * B := by
      have hdiv := (div_le_iff₀ hs_pos).mp hTitu
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hsB : s * B ≤ B := by
      nlinarith
    simpa [A, B, Real.norm_eq_abs, sq_abs] using hmain.trans hsB

/-- Helper for Proposition 2.5: the Euclidean-coordinate entropy function is `1`-strongly convex
on the coordinate realization of the simplex. -/
private theorem entropyCoordinateFunction_strongConvexOnWith_l1_preimage_stdSimplex :
    StrongConvexOnWith
      (coordinateL1Seminorm n) 1
      ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n))
      (entropyCoordinateFunction n) := by
  let S : Set E := ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n))
  have hS_conv : Convex ℝ S := by
    simpa [S] using
      (convex_stdSimplex ℝ (Fin n)).linear_preimage
        (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap
  have hopenStrong :
      StrongConvexOnWith
        (coordinateL1Seminorm n) 1
        (openSubprobabilitySimplex n)
        (entropyCoordinateFunction n) := by
    rw [StrongConvexOnWith.iff_hessian_quadratic_form_lower_bound
      (p := coordinateL1Seminorm n) (μ := (1 : ℝ))
      (U := openSubprobabilitySimplex n) (f := entropyCoordinateFunction n)]
    · intro x hx h
      simpa using entropy_hessian_lower_bound_l1_on_open_subprobability_simplex (n := n) hx h
    · norm_num
    · exact isOpen_openSubprobabilitySimplex (n := n)
    · exact convex_openSubprobabilitySimplex (n := n)
    · exact entropy_contDiffOn_open_subprobability_simplex (n := n)
  refine ⟨hS_conv, zero_lt_one, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : E := a • x + b • y
  let xt : ℝ → E := fun t ↦ (1 - t) • x + t • subprobabilityInteriorAnchor n
  let yt : ℝ → E := fun t ↦ (1 - t) • y + t • subprobabilityInteriorAnchor n
  let zt : ℝ → E := fun t ↦ (1 - t) • z + t • subprobabilityInteriorAnchor n
  have hz : z ∈ S := hS_conv hx hy ha hb hab
  have hIoc : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioc (0 : ℝ) 1 := by
    have hlt_one : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hlt_one] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  have hineq :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        entropyCoordinateFunction n (zt t) ≤
          a * entropyCoordinateFunction n (xt t) +
            b * entropyCoordinateFunction n (yt t) -
              a * b * ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))) := by
    filter_upwards [hIoc] with t ht
    have hxt : xt t ∈ openSubprobabilitySimplex n :=
      preimage_stdSimplex_segment_anchor_mem_openSubprobabilitySimplex (n := n) hx ht
    have hyt : yt t ∈ openSubprobabilitySimplex n :=
      preimage_stdSimplex_segment_anchor_mem_openSubprobabilitySimplex (n := n) hy ht
    have hstrong := hopenStrong.2.2 hxt hyt ha hb hab
    have hsegment : a • xt t + b • yt t = zt t := by
      ext i
      dsimp [xt, yt, zt, z]
      calc
        a * ((1 - t) * x i + t * subprobabilityInteriorAnchor n i) +
            b * ((1 - t) * y i + t * subprobabilityInteriorAnchor n i)
            = (1 - t) * (a * x i + b * y i) +
                (a + b) * (t * subprobabilityInteriorAnchor n i) := by ring
        _ = (1 - t) * (a * x i + b * y i) + t * subprobabilityInteriorAnchor n i := by
              rw [hab]
              ring
        _ = (1 - t) * (a * x i + b * y i) + t * subprobabilityInteriorAnchor n i := by rfl
    have hdiff :
        xt t - yt t = (1 - t) • (x - y) := by
      ext i
      dsimp [xt, yt]
      ring
    have hnorm :
        coordinateL1Seminorm n (xt t - yt t) =
          (1 - t) * coordinateL1Seminorm n (x - y) := by
      rw [hdiff, map_smul_eq_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    have hnorm_sq :
        (coordinateL1Seminorm n (xt t - yt t)) ^ (2 : ℕ) =
          (1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ) := by
      rw [hnorm]
      ring
    -- Rewrite the open-domain strong-convexity inequality in terms of the boundary-approximation
    -- path and the rescaled `ℓ₁` correction.
    have hstrong' := hstrong
    rw [hsegment, hnorm_sq] at hstrong'
    simpa [xt, yt, zt, z, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hstrong'
  have hxt_tendsto : Filter.Tendsto xt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by
    have hcont : Continuous xt := by
      dsimp [xt]
      fun_prop
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    simp [xt]
  have hyt_tendsto : Filter.Tendsto yt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds y) := by
    have hcont : Continuous yt := by
      dsimp [yt]
      fun_prop
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    simp [yt]
  have hzt_tendsto : Filter.Tendsto zt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds z) := by
    have hcont : Continuous zt := by
      dsimp [zt]
      fun_prop
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    simp [zt]
  have hlhs :
      Filter.Tendsto
        (fun t : ℝ ↦ entropyCoordinateFunction n (zt t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (entropyCoordinateFunction n z)) := by
    exact (entropyCoordinateFunction_continuous (n := n)).tendsto z |>.comp hzt_tendsto
  have hrhs :
      Filter.Tendsto
        (fun t : ℝ ↦
          a * entropyCoordinateFunction n (xt t) +
            b * entropyCoordinateFunction n (yt t) -
              a * b * ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (a * entropyCoordinateFunction n x +
            b * entropyCoordinateFunction n y -
              a * b * ((1 / 2 : ℝ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ)))) := by
    have hxtf :
        Filter.Tendsto
          (fun t : ℝ ↦ entropyCoordinateFunction n (xt t))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (entropyCoordinateFunction n x)) := by
      exact (entropyCoordinateFunction_continuous (n := n)).tendsto x |>.comp hxt_tendsto
    have hytf :
        Filter.Tendsto
          (fun t : ℝ ↦ entropyCoordinateFunction n (yt t))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (entropyCoordinateFunction n y)) := by
      exact (entropyCoordinateFunction_continuous (n := n)).tendsto y |>.comp hyt_tendsto
    have hcorr :
        Filter.Tendsto
          (fun t : ℝ ↦ a * b *
            ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (a * b * ((1 / 2 : ℝ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ)))) := by
      have hcont :
          Continuous fun t : ℝ ↦
            a * b *
              ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))) := by
        fun_prop
      convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
      simp
    exact (hxtf.const_mul a).add (hytf.const_mul b) |>.sub hcorr
  letI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hlimit := le_of_tendsto_of_tendsto hlhs hrhs hineq
  simpa [z, S, smul_eq_mul] using hlimit

/-- Helper for Proposition 2.5: strong convexity pulls back along a linear equivalence by
precomposition. -/
private theorem strongConvexOnWith_precompose_linear_equiv
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    [NormedSpace ℝ G] [NormedSpace ℝ H]
    (e : G ≃L[ℝ] H) {p : Seminorm ℝ H} {μ : ℝ} {Q : Set H} {f : H → ℝ}
    (hf : StrongConvexOnWith p μ Q f) :
    StrongConvexOnWith (Seminorm.comp p e.toLinearMap) μ (e ⁻¹' Q) (fun x : G ↦ f (e x)) := by
  refine ⟨hf.1.linear_preimage e.toLinearMap, hf.2.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Rewrite the pulled-back segment inequality through the linear equivalence.
  simpa [Seminorm.comp_apply, map_add, map_smulₛₗ, smul_eq_mul] using
    hf.2.2 hx hy ha hb hab

/-- Proposition 2.5: the entropy function `x ↦ ∑ᵢ xᵢ log xᵢ` is `1`-strongly convex on the
standard simplex `Δ_n = stdSimplex ℝ (Fin n)` with respect to the canonical `ℓ₁` norm on the
function-space owner `Fin n → ℝ`. -/
-- Proof sketch: prove the source-faithful statement first on the Euclidean realization of the
-- simplex, where the Hessian criterion applies on the strict subprobability simplex, and then
-- transport the result back along `EuclideanSpace.equiv`.
theorem entropyFunction_strongConvexOnWith_l1_stdSimplex :
    StrongConvexOnWith (simplexL1Seminorm n) 1 (stdSimplex ℝ (Fin n)) (entropyFunction n) := by
  -- Transport the Euclidean-coordinate theorem back to the function-space owner.
  simpa [entropyCoordinateFunction, coordinateL1Seminorm, simplexL1Seminorm] using
    (strongConvexOnWith_precompose_linear_equiv (EuclideanSpace.equiv (Fin n) ℝ).symm
      (entropyCoordinateFunction_strongConvexOnWith_l1_preimage_stdSimplex (n := n)))

namespace EuclideanSpace

/-- The canonical coordinate `ℓ₁` seminorm on `ℝⁿ`, obtained by pulling back the owner
`simplexL1Seminorm n` along the coordinate linear equivalence. -/
abbrev l1Seminorm : Seminorm ℝ E :=
  Seminorm.comp (simplexL1Seminorm n) (equiv (Fin n) ℝ).toLinearMap

/-- Applying the canonical coordinate `ℓ₁` seminorm to a vector sums the absolute values of its
coordinates. -/
-- Proof sketch: `l1Seminorm n` is the coordinate pullback of the owner `simplexL1Seminorm n`, so
-- apply `simplexL1Seminorm_apply` to the coordinate function `equiv (Fin n) ℝ x`.
theorem l1Seminorm_apply (x : E) :
    l1Seminorm n x = ∑ i, ‖x i‖ := by
  simpa [l1Seminorm] using simplexL1Seminorm_apply n ((equiv (Fin n) ℝ) x)

/-- The canonical coordinate `ℓ₁` seminorm is a norm on `ℝⁿ`. -/
-- Proof sketch: `l1Seminorm n` is the pullback of the owner norm `simplexL1Seminorm n` along the
-- coordinate linear equivalence `equiv (Fin n) ℝ`, so vanishing reduces to
-- `simplexL1Seminorm_isNorm` on the coordinate function.
instance l1Seminorm_isNorm : Seminorm.IsNorm (l1Seminorm n : Seminorm ℝ E) where
  eq_zero_of_map_eq_zero := by
    intro x hx
    let hSimplex : Seminorm.IsNorm (simplexL1Seminorm n : Seminorm ℝ F) := inferInstance
    exact (equiv (Fin n) ℝ).injective <|
      hSimplex.eq_zero_of_map_eq_zero <| by
        simpa [l1Seminorm] using hx

/-- Proposition 2.5 transported to Euclidean coordinates: precomposing the canonical owner
`entropyFunction n` with `equiv (Fin n) ℝ` yields a `1`-strongly convex function on the
preimage of `stdSimplex ℝ (Fin n)` with respect to the coordinate `ℓ₁` norm. -/
-- Proof sketch: compute the Hessian of the entropy on the relative interior of the coordinate
-- realization of `stdSimplex` as the diagonal form `∑ᵢ hᵢ² / xᵢ`, then use the simplex
-- normalization `∑ᵢ xᵢ = 1` to bound this quadratic form below by `‖h‖₁²`. This yields the
-- second-order criterion for `1`-strong convexity with respect to the canonical coordinate `ℓ₁`
-- seminorm.
theorem entropyFunction_strongConvexOnWith_l1_preimage_stdSimplex :
    StrongConvexOnWith
      (l1Seminorm n) 1
      ((equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n))
      (fun x : E ↦ _root_.entropyFunction n ((equiv (Fin n) ℝ) x)) :=
  by
    -- The public Euclidean statement is definitionally the private coordinate theorem above.
    simpa [l1Seminorm, entropyCoordinateFunction, coordinateL1Seminorm] using
      (entropyCoordinateFunction_strongConvexOnWith_l1_preimage_stdSimplex (n := n))

end EuclideanSpace

end
