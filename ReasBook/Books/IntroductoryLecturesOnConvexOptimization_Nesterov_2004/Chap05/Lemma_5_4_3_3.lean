/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E]

/-
Lemma 5.4.3.3 lies in the Chapter 5 cone-barrier domain.

Sampled owner-style declarations in this domain:
* mathlib `ConvexCone ℝ (E × ℝ)`, the canonical owner for cone domains in the intrinsic ambient
  product space;
* project `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraphs,
  which realizes the second-order cone as the epigraph of `x ↦ ‖x‖`;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, the canonical `L²` product owner for
  the ambient inner-product geometry of the barrier statement;
* project `epigraphLogBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_3_5`, which already
  states a Chapter 5 logarithmic barrier theorem on that canonical `L²` owner over complete real
  inner-product spaces;
* project `IsSelfConcordantBarrierOnWith`, the canonical barrier owner targeted by the theorem
  below.

Source/core/bridge triage:
* source-facing: the explicit second-order cone barrier formula;
* core/canonical: the second-order cone itself, best owned as `ConvexCone ℝ (E × ℝ)`;
* bridge/view: the membership and evaluation lemmas exposing the textbook formulas directly.

The refinement here is therefore to keep the explicit textbook cone and barrier on raw pairs, use
the canonical `ConvexCone` owner for the cone data, realize its carrier through the chapter
epigraph owner instead of a duplicate set-builder, and state the barrier theorem on the canonical
`L²` product owner `WithLp 2 (E × ℝ)` via the bridge `WithLp.ofLp`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook model `ℝⁿ × ℝ`. -/

/-- The second-order cone `K₂ = {(x, t) | ‖x‖ ≤ t}` in `E × ℝ`. -/
theorem secondOrderCone_smul_mem {τ : ℝ} (hτ : 0 < τ) {p : E × ℝ}
    (hp : ‖p.1‖ ≤ p.2) :
    ‖(τ • p).1‖ ≤ (τ • p).2 := by
  calc
    ‖(τ • p).1‖ = τ * ‖p.1‖ := by
      simp [norm_smul, Real.norm_of_nonneg hτ.le]
    _ ≤ τ * p.2 := mul_le_mul_of_nonneg_left hp hτ.le
    _ = (τ • p).2 := by rfl

omit [NormedSpace ℝ E] in
/-- The second-order cone is closed under vector addition. -/
theorem secondOrderCone_add_mem {p q : E × ℝ}
    (hp : ‖p.1‖ ≤ p.2) (hq : ‖q.1‖ ≤ q.2) :
    ‖(p + q).1‖ ≤ (p + q).2 := by
  calc
    ‖(p + q).1‖ ≤ ‖p.1‖ + ‖q.1‖ := norm_add_le _ _
    _ ≤ p.2 + q.2 := add_le_add hp hq
    _ = (p + q).2 := rfl

/-- The second-order cone `K₂ = {(x, t) | ‖x‖ ≤ t}` in `E × ℝ`. -/
def secondOrderCone (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ConvexCone ℝ (E × ℝ) where
  carrier := constrainedEpigraph (Set.univ : Set E) fun x ↦ ((‖x‖ : ℝ) : WithTop ℝ)
  smul_mem' := fun {_c} hc {_x} hx ↦ by
    simpa [constrainedEpigraph] using
      secondOrderCone_smul_mem hc (by simpa [constrainedEpigraph] using hx)
  add_mem' := fun {_x} hx {_y} hy ↦ by
    simpa [constrainedEpigraph] using
      secondOrderCone_add_mem
        (by simpa [constrainedEpigraph] using hx)
        (by simpa [constrainedEpigraph] using hy)

namespace SecondOrderCone

/- Source-facing notation for the second-order cone owner as a subset of `E × ℝ`. -/
scoped notation "K₂[" E "]" => (secondOrderCone E : Set (E × ℝ))

end SecondOrderCone

open scoped SecondOrderCone

-- Proof sketch: unfold `secondOrderCone`; membership is exactly the displayed norm inequality in
-- the defining set-builder.
/-- Membership in `secondOrderCone` means that the scalar coordinate dominates the Euclidean norm
of the vector coordinate. -/
@[simp]
theorem mem_secondOrderCone_iff (p : E × ℝ) :
    p ∈ K₂[E] ↔ ‖p.1‖ ≤ p.2 := by
  change p ∈ constrainedEpigraph (Set.univ : Set E) (fun x ↦ ((‖x‖ : ℝ) : WithTop ℝ)) ↔
      ‖p.1‖ ≤ p.2
  simp [constrainedEpigraph]

-- Proof sketch: `secondOrderCone` is the closed sublevel set of the continuous function
-- `p ↦ ‖p.1‖ - p.2`, so its interior is obtained by replacing the weak inequality by the strict
-- inequality `‖p.1‖ < p.2`.
/-- A point lies in the interior of `secondOrderCone` exactly when its scalar coordinate is
strictly larger than the Euclidean norm of its vector coordinate. -/
theorem mem_interior_secondOrderCone_iff (p : E × ℝ) :
    p ∈ interior K₂[E] ↔ ‖p.1‖ < p.2 := by
  constructor
  · intro hp
    have hpK : p ∈ K₂[E] := interior_subset hp
    have hp_le : ‖p.1‖ ≤ p.2 := (mem_secondOrderCone_iff p).1 hpK
    -- Exclude the boundary case by perturbing only the scalar coordinate downward.
    by_contra hp_not_strict
    have hp_eq : ‖p.1‖ = p.2 := le_antisymm hp_le (not_lt.mp hp_not_strict)
    let γ : ℝ → E × ℝ := fun s ↦ (p.1, s)
    have hγ : Continuous γ := by
      fun_prop
    have hpre : γ ⁻¹' interior K₂[E] ∈ nhds p.2 := by
      exact hγ.continuousAt.preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using hp))
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    have hdown : p.2 - ε / 2 ∈ Metric.ball p.2 ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hneg : p.2 - ε / 2 - p.2 < 0 := by
        linarith
      rw [abs_of_neg hneg]
      linarith
    have hmem : γ (p.2 - ε / 2) ∈ interior K₂[E] := hεsub hdown
    have hcone : γ (p.2 - ε / 2) ∈ K₂[E] := interior_subset hmem
    have hbound : ‖p.1‖ ≤ p.2 - ε / 2 := by
      simpa [γ] using (mem_secondOrderCone_iff (γ (p.2 - ε / 2))).1 hcone
    rw [hp_eq] at hbound
    linarith
  · intro hp
    let φ : E × ℝ → ℝ := fun q ↦ ‖q.1‖ - q.2
    have hφ_cont : ContinuousAt φ p := by
      have hφ : Continuous φ := by
        simpa [φ] using continuous_fst.norm.sub continuous_snd
      exact hφ.continuousAt
    have hφ_neg : φ p < 0 := by
      simpa [φ] using sub_neg.mpr hp
    have hnhds : K₂[E] ∈ nhds p := by
      refine Filter.mem_of_superset
        (hφ_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hφ_neg)) ?_
      intro q hq
      have hq' : ‖q.1‖ - q.2 < 0 := by
        simpa [φ] using hq
      exact (mem_secondOrderCone_iff q).2 (le_of_lt (sub_neg.mp hq'))
    exact mem_interior_iff_mem_nhds.mpr hnhds

/-- Helper for Lemma 5.4.3.3: interior points of the second-order cone have positive scalar
coordinate. -/
theorem secondOrderCone_scalar_pos_of_mem_interior (p : E × ℝ)
    (hp : p ∈ interior K₂[E]) :
    0 < p.2 := by
  -- The strict interior inequality dominates the always nonnegative norm term.
  exact lt_of_le_of_lt (norm_nonneg _) ((mem_interior_secondOrderCone_iff p).1 hp)

/-- Helper for Lemma 5.4.3.3: the Lorentz slack `t^2 - ‖x‖^2` is positive on the interior of the
second-order cone. -/
theorem secondOrderCone_slack_pos_of_mem_interior (p : E × ℝ)
    (hp : p ∈ interior K₂[E]) :
    0 < p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ) := by
  have hstrict : ‖p.1‖ < p.2 := (mem_interior_secondOrderCone_iff p).1 hp
  have hdiff : 0 < p.2 - ‖p.1‖ := sub_pos.mpr hstrict
  have hsum : 0 < p.2 + ‖p.1‖ := by
    have ht_pos : 0 < p.2 := secondOrderCone_scalar_pos_of_mem_interior p hp
    exact add_pos_of_pos_of_nonneg ht_pos (norm_nonneg _)
  -- Factor the slack as `(t - ‖x‖) * (t + ‖x‖)` and use the strict interior inequality.
  calc
    0 < (p.2 - ‖p.1‖) * (p.2 + ‖p.1‖) := mul_pos hdiff hsum
    _ = p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ) := by ring

/-- The logarithmic barrier `(x, t) ↦ -log (t^2 - ‖x‖^2)` on the second-order cone. -/
def secondOrderConeBarrier : E × ℝ → ℝ :=
  fun p ↦ -Real.log (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ))

-- Proof sketch: unfold `secondOrderConeBarrier`.
omit [NormedSpace ℝ E] in
/-- Evaluating `secondOrderConeBarrier` reproduces the textbook formula
`(x, t) ↦ -log (t^2 - ‖x‖^2)`. -/
@[simp]
theorem secondOrderConeBarrier_apply (p : E × ℝ) :
    secondOrderConeBarrier p =
      -Real.log (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) := rfl

end

section

variable [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance instLocalChap05_Lemma_5_4_3_31 : SeminormedAddCommGroup (E × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instLocalChap05_Lemma_5_4_3_32 : NormedAddCommGroup (E × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 E ℝ

noncomputable local instance instLocalChap05_Lemma_5_4_3_33 : NormedSpace ℝ (E × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instInnerProductSpaceChap05_Lemma_5_4_3_31 : InnerProductSpace ℝ (E × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Lemma_5_4_3_34 : CompleteSpace (E × ℝ) := inferInstance

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

/-- Helper for Lemma 5.4.3.3: the canonical affine bridge from the `WithLp` owner `Z` back to
raw pairs `E × ℝ`. -/
private def ofPairContinuousAffine : Z →ᴬ[ℝ] E × ℝ :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toContinuousLinearMap).toContinuousAffineMap

/-- Helper for Lemma 5.4.3.3: applying the raw-pair affine bridge recovers `WithLp.ofLp`. -/
@[simp] private theorem ofPairContinuousAffine_apply (z : Z) :
    ofPairContinuousAffine z = ofZ z :=
  rfl

/-- Helper for Lemma 5.4.3.3: the second coordinate of `WithLp.ofLp`, packaged as a continuous
affine map so the scalar `-log` barrier can be pulled back to the canonical owner `Z`. -/
private def secondCoordinateAffine : Z →ᴬ[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap.comp ofPairContinuousAffine

/-- Helper for Lemma 5.4.3.3: a `C²` real-valued map has differentiable gradient at the same
point, so the Hessian quadratic-form identity for second directional derivatives is available. -/
lemma differentiableAt_gradient_of_contDiffAt_two
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    {g : E₁ → ℝ} {x : E₁} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  let D : StrongDual ℝ E₁ →L[ℝ] E₁ :=
    (InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- The gradient is the inverse Riesz map applied to the Fréchet derivative field.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Lemma 5.4.3.3: the quadratic-log model
`t ↦ -log (φ₀ + δ t - (q / 2) t²)` has the expected first derivative at `0`. -/
private theorem negLog_quadratic_model_firstDeriv_at_zero
    {phi0 delta quad : ℝ} (hphi : 0 < phi0) :
    deriv
        (fun t : ℝ ↦ -Real.log (phi0 + delta * t - (quad / 2 : ℝ) * t ^ (2 : ℕ))) 0 =
      -delta / phi0 := by
  let q : ℝ → ℝ := fun t ↦ phi0 + delta * t - (quad / 2 : ℝ) * t ^ (2 : ℕ)
  have hq0 : q 0 = phi0 := by
    simp [q]
  have hq_cont : ContDiffAt ℝ 3 q 0 := by
    -- The quadratic slack is polynomial, so the scalar chain rule applies up to order three.
    fun_prop
  have hq_deriv : deriv q = fun t : ℝ ↦ delta - quad * t := by
    ext t
    have hlin : HasDerivAt (fun s : ℝ ↦ delta * s) delta t := by
      simpa [mul_comm] using (hasDerivAt_id t).const_mul delta
    have hquad :
        HasDerivAt (fun s : ℝ ↦ (quad / 2 : ℝ) * s ^ (2 : ℕ)) ((quad / 2 : ℝ) * (2 * t)) t := by
      have hpow : HasDerivAt (fun s : ℝ ↦ s ^ (2 : ℕ)) (2 * t) t := by
        simpa [pow_two, two_mul] using (hasDerivAt_id t).pow 2
      simpa [mul_assoc] using hpow.const_mul (quad / 2 : ℝ)
    have hderiv :
        HasDerivAt q (0 + delta - (quad / 2 : ℝ) * (2 * t)) t := by
      exact (hasDerivAt_const t phi0).add hlin |>.sub hquad
    -- Normalize the derivative only after the chain rule has produced the stable polynomial form.
    have hderiv_eq := hderiv.deriv
    calc
      deriv q t = 0 + delta - (quad / 2 : ℝ) * (2 * t) := hderiv_eq
      _ = delta - quad * t := by ring
  have hq_hasDeriv : HasDerivAt q (deriv q 0) 0 := by
    exact (hq_cont.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hlog_hasDeriv :
      HasDerivAt Real.log ((q 0)⁻¹) (q 0) := by
    simpa [hq0] using Real.hasDerivAt_log hphi.ne'
  have hcomp_deriv :
      deriv (fun t : ℝ ↦ -Real.log (q t)) 0 = -((q 0)⁻¹ * deriv q 0) := by
    have hcomp_log :
        deriv (fun t : ℝ ↦ Real.log (q t)) 0 = (q 0)⁻¹ * deriv q 0 := by
      simpa [Function.comp] using (hlog_hasDeriv.comp 0 hq_hasDeriv).deriv
    -- Differentiate `-log ∘ q` and rewrite the result through the basepoint data of `q`.
    calc
      deriv (fun t : ℝ ↦ -Real.log (q t)) 0
          = -deriv (fun t : ℝ ↦ Real.log (q t)) 0 := by
              simpa using (deriv.neg (f := fun t : ℝ ↦ Real.log (q t)) (x := 0))
      _ = -((q 0)⁻¹ * deriv q 0) := by
            rw [hcomp_log]
  calc
    deriv (fun t : ℝ ↦ -Real.log (phi0 + delta * t - (quad / 2 : ℝ) * t ^ (2 : ℕ))) 0
        = deriv (fun t : ℝ ↦ -Real.log (q t)) 0 := by
            simp [q]
    _ = -((q 0)⁻¹ * deriv q 0) := hcomp_deriv
    _ = -(phi0⁻¹ * delta) := by
          rw [hq0, hq_deriv]
          ring
    _ = -delta / phi0 := by
          rw [div_eq_mul_inv]
          ring

/-- Helper for Lemma 5.4.3.3: the quadratic-log slice has the textbook second and third
directional-derivative values at the base point `t = 0`. -/
private theorem negLog_quadratic_model_directional_data_at_zero
    {phi0 delta quad : ℝ} (hphi : 0 < phi0) :
    iteratedDeriv 2
        (fun t : ℝ ↦ -Real.log (phi0 + delta * t - (quad / 2 : ℝ) * t ^ (2 : ℕ))) 0 =
      delta ^ (2 : ℕ) / phi0 ^ (2 : ℕ) + quad / phi0 ∧
    iteratedDeriv 3
        (fun t : ℝ ↦ -Real.log (phi0 + delta * t - (quad / 2 : ℝ) * t ^ (2 : ℕ))) 0 =
      -(2 * delta ^ (3 : ℕ) / phi0 ^ (3 : ℕ) + 3 * delta * quad / phi0 ^ (2 : ℕ)) := by
  let q : ℝ → ℝ := fun t ↦ phi0 + delta * t - (quad / 2 : ℝ) * t ^ (2 : ℕ)
  have hq0 : q 0 = phi0 := by
    simp [q]
  have hq_cont : ContDiffAt ℝ 3 q 0 := by
    -- The quadratic slack is a polynomial, so the scalar chain rule applies up to order three.
    fun_prop
  have hlog_cont : ContDiffAt ℝ 3 Real.log (q 0) := by
    -- Positivity at the basepoint keeps the logarithm away from its singularity.
    have hq0_ne : q 0 ≠ 0 := by
      simpa [hq0] using hphi.ne'
    exact Real.contDiffAt_log.2 hq0_ne
  have hq_deriv : deriv q = fun t : ℝ ↦ delta - quad * t := by
    ext t
    have hlin : HasDerivAt (fun s : ℝ ↦ delta * s) delta t := by
      simpa [mul_comm] using (hasDerivAt_id t).const_mul delta
    have hquad :
        HasDerivAt (fun s : ℝ ↦ (quad / 2 : ℝ) * s ^ (2 : ℕ)) ((quad / 2 : ℝ) * (2 * t)) t := by
      have hpow : HasDerivAt (fun s : ℝ ↦ s ^ (2 : ℕ)) (2 * t) t := by
        simpa [pow_two, two_mul] using (hasDerivAt_id t).pow 2
      simpa [mul_assoc] using hpow.const_mul (quad / 2 : ℝ)
    have hderiv :
        HasDerivAt q (0 + delta - (quad / 2 : ℝ) * (2 * t)) t := by
      exact (hasDerivAt_const t phi0).add hlin |>.sub hquad
    -- Normalize the derivative only after the chain rule has produced the stable polynomial form.
    have hderiv_eq := hderiv.deriv
    calc
      deriv q t = 0 + delta - (quad / 2 : ℝ) * (2 * t) := hderiv_eq
      _ = delta - quad * t := by ring
  have hq_second : iteratedDeriv 2 q = fun t : ℝ ↦ -quad := by
    ext t
    calc
      iteratedDeriv 2 q t = deriv (deriv q) t := by
        simp [iteratedDeriv_succ]
      _ = deriv (fun s : ℝ ↦ delta - quad * s) t := by
        rw [hq_deriv]
      _ = -quad := by
        have hderiv : HasDerivAt (fun s : ℝ ↦ delta - quad * s) (-quad) t := by
          simpa [mul_comm] using
            (hasDerivAt_const t delta).sub ((hasDerivAt_id t).const_mul quad)
        exact hderiv.deriv
  have hq_third : iteratedDeriv 3 q 0 = 0 := by
    -- A quadratic scalar slack has vanishing third iterated derivative.
    calc
      iteratedDeriv 3 q 0 = deriv (iteratedDeriv 2 q) 0 := by
        simp [iteratedDeriv_succ]
      _ = deriv (fun t : ℝ ↦ -quad) 0 := by
        rw [hq_second]
      _ = 0 := by
        simp
  have hderiv_log : deriv Real.log = fun s : ℝ ↦ s⁻¹ := by
    ext s
    rw [Real.deriv_log]
  have hsecond_log :
      iteratedDeriv 2 Real.log phi0 = -(phi0 ^ (2 : ℕ))⁻¹ := by
    calc
      iteratedDeriv 2 Real.log phi0 = deriv (deriv Real.log) phi0 := by
              simp [iteratedDeriv_succ]
      _ = deriv (fun s : ℝ ↦ s⁻¹) phi0 := by
            rw [hderiv_log]
      _ = -(phi0 ^ (2 : ℕ))⁻¹ := by
            rw [deriv_inv]
  have hthird_log :
      iteratedDeriv 3 Real.log phi0 = 2 * (phi0 ^ (3 : ℕ))⁻¹ := by
    calc
      iteratedDeriv 3 Real.log phi0 = iteratedDeriv 2 (deriv Real.log) phi0 := by
              simp [iteratedDeriv_succ']
      _ = iteratedDeriv 2 (fun s : ℝ ↦ s⁻¹) phi0 := by
            rw [hderiv_log]
      _ = deriv^[2] Inv.inv phi0 := by
            rw [iteratedDeriv_eq_iterate]
      _ = 2 * phi0 ^ (-3 : ℤ) := by
            simpa using iter_deriv_inv 2 phi0
      _ = 2 * (phi0 ^ (3 : ℕ))⁻¹ := by
            rw [zpow_neg]
            field_simp [hphi.ne']
  have hcomp_two :
      iteratedDeriv 2 (fun t : ℝ ↦ Real.log (q t)) 0 =
        iteratedDeriv 2 Real.log (q 0) * deriv q 0 ^ (2 : ℕ) +
          deriv Real.log (q 0) * iteratedDeriv 2 q 0 := by
    -- Apply the scalar second-order chain rule to the quadratic slack.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (g := Real.log)
        (f := q)
        (x := 0)
        (hlog_cont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
        (hq_cont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)))
  have hcomp_three :
      iteratedDeriv 3 (fun t : ℝ ↦ Real.log (q t)) 0 =
        iteratedDeriv 3 Real.log (q 0) * deriv q 0 ^ (3 : ℕ) +
          3 * iteratedDeriv 2 Real.log (q 0) * iteratedDeriv 2 q 0 * deriv q 0 +
          deriv Real.log (q 0) * iteratedDeriv 3 q 0 := by
    -- The third-order chain rule produces the cubic source-proof expression at the basepoint.
    simpa [Function.comp] using
      (iteratedDeriv_comp_three
        (g := Real.log)
        (f := q)
        (x := 0)
        hlog_cont
        hq_cont)
  have hsecond :
      iteratedDeriv 2 (fun t : ℝ ↦ -Real.log (q t)) 0 =
        delta ^ (2 : ℕ) / phi0 ^ (2 : ℕ) + quad / phi0 := by
    calc
      iteratedDeriv 2 (fun t : ℝ ↦ -Real.log (q t)) 0
          = -iteratedDeriv 2 (fun t : ℝ ↦ Real.log (q t)) 0 := by
              simp
      _ = -(iteratedDeriv 2 Real.log (q 0) * deriv q 0 ^ (2 : ℕ) +
              deriv Real.log (q 0) * iteratedDeriv 2 q 0) := by
            rw [hcomp_two]
      _ = -(-(phi0 ^ (2 : ℕ))⁻¹ * delta ^ (2 : ℕ) + phi0⁻¹ * (-quad)) := by
            rw [hq0, hsecond_log, hderiv_log, hq_deriv, hq_second]
            simp
      _ = delta ^ (2 : ℕ) / phi0 ^ (2 : ℕ) + quad / phi0 := by
            field_simp [hphi.ne']
            ring
  have hthird :
      iteratedDeriv 3 (fun t : ℝ ↦ -Real.log (q t)) 0 =
        -(2 * delta ^ (3 : ℕ) / phi0 ^ (3 : ℕ) + 3 * delta * quad / phi0 ^ (2 : ℕ)) := by
    calc
      iteratedDeriv 3 (fun t : ℝ ↦ -Real.log (q t)) 0
          = -iteratedDeriv 3 (fun t : ℝ ↦ Real.log (q t)) 0 := by
              simp
      _ = -(iteratedDeriv 3 Real.log (q 0) * deriv q 0 ^ (3 : ℕ) +
              3 * iteratedDeriv 2 Real.log (q 0) * iteratedDeriv 2 q 0 * deriv q 0 +
              deriv Real.log (q 0) * iteratedDeriv 3 q 0) := by
            rw [hcomp_three]
      _ = -(2 * (phi0 ^ (3 : ℕ))⁻¹ * delta ^ (3 : ℕ) +
            3 * (-(phi0 ^ (2 : ℕ))⁻¹) * (-quad) * delta +
            phi0⁻¹ * 0) := by
              rw [hq0, hthird_log, hsecond_log, hderiv_log, hq_deriv, hq_second, hq_third]
              simp
      _ = -(2 * delta ^ (3 : ℕ) / phi0 ^ (3 : ℕ) + 3 * delta * quad / phi0 ^ (2 : ℕ)) := by
            field_simp [hphi.ne']
            ring
  simpa [q] using And.intro hsecond hthird

/-- Helper for Lemma 5.4.3.3: the second-order-cone barrier is `C³` at every interior point. -/
private theorem secondOrderConeBarrier_contDiffAt_three
    {p : E × ℝ} (hp : p ∈ interior (secondOrderCone E : Set (E × ℝ))) :
    ContDiffAt ℝ 3 secondOrderConeBarrier p := by
  let slack : E × ℝ → ℝ := fun q ↦ q.2 ^ (2 : ℕ) - inner ℝ q.1 q.1
  have hslack_pos : 0 < slack p := by
    -- On the cone interior the Lorentz slack stays strictly positive, so `log` is regular.
    simpa [slack, real_inner_self_eq_norm_sq] using secondOrderCone_slack_pos_of_mem_interior p hp
  have hslack_cont : ContDiffAt ℝ 3 slack p := by
    -- The slack itself is polynomial in the coordinates and therefore `C³`.
    let sndMap : E × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
    let fstMap : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
    have hsnd : ContDiffAt ℝ 3 (fun q : E × ℝ ↦ sndMap q) p :=
      sndMap.contDiff.contDiffAt
    have hfst : ContDiffAt ℝ 3 (fun q : E × ℝ ↦ fstMap q) p :=
      fstMap.contDiff.contDiffAt
    have hsndSq : ContDiffAt ℝ 3 (fun q : E × ℝ ↦ sndMap q * sndMap q) p :=
      hsnd.mul hsnd
    have hinner : ContDiffAt ℝ 3 (fun q : E × ℝ ↦ inner ℝ (fstMap q) (fstMap q)) p :=
      hfst.inner ℝ hfst
    simpa [slack, sndMap, fstMap, pow_two] using hsndSq.sub hinner
  have hlog_cont : ContDiffAt ℝ 3 (fun q : E × ℝ ↦ Real.log (slack q)) p := by
    exact (Real.contDiffAt_log.2 hslack_pos.ne').comp p hslack_cont
  -- Add the outer minus sign only after the positive scalar slack has been isolated.
  simpa [secondOrderConeBarrier, slack, real_inner_self_eq_norm_sq] using hlog_cont.neg

/-- Helper for Lemma 5.4.3.3: restricting the Lorentz barrier to a line gives the quadratic-log
slice from the source proof. -/
private theorem secondOrderConeBarrier_slice_eq (p u : E × ℝ) :
    directionalSlice secondOrderConeBarrier p u =
      fun a : ℝ ↦
        -Real.log
          (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ) +
            2 * (p.2 * u.2 - inner ℝ p.1 u.1) * a +
            (u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)) * a ^ (2 : ℕ)) := by
  funext a
  -- Expand the line `p + a • u` and collect the constant, linear, and quadratic Lorentz terms.
  rw [directionalSlice, secondOrderConeBarrier_apply]
  change
    -Real.log ((p.2 + a * u.2) ^ (2 : ℕ) - ‖p.1 + a • u.1‖ ^ (2 : ℕ)) =
      -Real.log
        (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ) +
          2 * (p.2 * u.2 - inner ℝ p.1 u.1) * a +
          (u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)) * a ^ (2 : ℕ))
  congr 1
  congr 1
  have hnorm :
      ‖p.1 + a • u.1‖ ^ (2 : ℕ) =
        ‖p.1‖ ^ (2 : ℕ) + 2 * inner ℝ p.1 u.1 * a + ‖u.1‖ ^ (2 : ℕ) * a ^ (2 : ℕ) := by
    -- Expand the vector norm square through the inner product before collecting coefficients.
    calc
      ‖p.1 + a • u.1‖ ^ (2 : ℕ) = inner ℝ (p.1 + a • u.1) (p.1 + a • u.1) := by
          rw [← real_inner_self_eq_norm_sq]
      _ = inner ℝ p.1 p.1 + inner ℝ p.1 (a • u.1) + inner ℝ (a • u.1) p.1 +
            inner ℝ (a • u.1) (a • u.1) := by
              rw [inner_add_left, inner_add_right, inner_add_right]
              ring
      _ = ‖p.1‖ ^ (2 : ℕ) + 2 * inner ℝ p.1 u.1 * a + ‖u.1‖ ^ (2 : ℕ) * a ^ (2 : ℕ) := by
            rw [inner_smul_right, real_inner_smul_left, real_inner_smul_left, inner_smul_right,
              real_inner_comm u.1 p.1, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
            ring
  rw [hnorm]
  ring

/-- Helper for Lemma 5.4.3.3: the Lorentz barrier slice yields the source proof's normalized
`ω₁`/`ω₂` formulas for the gradient pairing and the second and third directional derivatives. -/
private theorem secondOrderConeBarrier_directional_data
    {p u : E × ℝ} (hp : p ∈ interior (secondOrderCone E : Set (E × ℝ))) :
    let s : ℝ := p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)
    let c : ℝ := p.2 * u.2 - inner ℝ p.1 u.1
    let d : ℝ := u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)
    let ω1 : ℝ := -(2 * c) / s
    let ω2 : ℝ := -(2 * d) / s
    inner ℝ (∇ secondOrderConeBarrier p) u = ω1 ∧
      secondDirectionalDerivative secondOrderConeBarrier p u = ω1 ^ (2 : ℕ) + ω2 ∧
      thirdDirectionalDerivative secondOrderConeBarrier p u =
        2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2 := by
  let s : ℝ := p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)
  let c : ℝ := p.2 * u.2 - inner ℝ p.1 u.1
  let d : ℝ := u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)
  let ω1 : ℝ := -(2 * c) / s
  let ω2 : ℝ := -(2 * d) / s
  have hs : 0 < s := by
    simpa [s] using secondOrderCone_slack_pos_of_mem_interior p hp
  have hcont : ContDiffAt ℝ 3 secondOrderConeBarrier p :=
    secondOrderConeBarrier_contDiffAt_three (p := p) hp
  have hdiff : DifferentiableAt ℝ secondOrderConeBarrier p :=
    hcont.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hslice :
      directionalSlice secondOrderConeBarrier p u =
        fun a : ℝ ↦
          -Real.log (s + (2 * c) * a - (((-2 * d) / 2 : ℝ) * a ^ (2 : ℕ))) := by
    calc
      directionalSlice secondOrderConeBarrier p u
          = fun a : ℝ ↦ -Real.log (s + 2 * c * a + d * a ^ (2 : ℕ)) := by
              simpa [s, c, d] using secondOrderConeBarrier_slice_eq (p := p) (u := u)
      _ = fun a : ℝ ↦
            -Real.log (s + (2 * c) * a - (((-2 * d) / 2 : ℝ) * a ^ (2 : ℕ))) := by
              funext a
              congr 1
              ring
  have hslice_deriv :
      deriv (directionalSlice secondOrderConeBarrier p u) 0 =
        inner ℝ (∇ secondOrderConeBarrier p) u := by
    -- Rewrite the slice derivative through the Chapter 1 gradient pairing owner.
    calc
      deriv (directionalSlice secondOrderConeBarrier p u) 0 = lineDeriv ℝ secondOrderConeBarrier p u := by
        rfl
      _ = fderiv ℝ secondOrderConeBarrier p u := hdiff.lineDeriv_eq_fderiv
      _ = inner ℝ (∇ secondOrderConeBarrier p) u := by
            rw [← inner_gradient_left hdiff]
  have hscalar1 :=
    negLog_quadratic_model_firstDeriv_at_zero
      (phi0 := s) (delta := 2 * c) (quad := -2 * d) hs
  have hscalar23 :=
    negLog_quadratic_model_directional_data_at_zero
      (phi0 := s) (delta := 2 * c) (quad := -2 * d) hs
  have hgrad_pair : inner ℝ (∇ secondOrderConeBarrier p) u = ω1 := by
    -- Read the first derivative of the normalized Lorentz slice at `0`.
    calc
      inner ℝ (∇ secondOrderConeBarrier p) u = deriv (directionalSlice secondOrderConeBarrier p u) 0 := by
        symm
        exact hslice_deriv
      _ = deriv
            (fun a : ℝ ↦
              -Real.log (s + (2 * c) * a - (((-2 * d) / 2 : ℝ) * a ^ (2 : ℕ)))) 0 := by
              rw [hslice]
      _ = -(2 * c) / s := by
            simpa using hscalar1
      _ = ω1 := by
            simp [ω1]
  have hsecond :
      secondDirectionalDerivative secondOrderConeBarrier p u = ω1 ^ (2 : ℕ) + ω2 := by
    -- The second directional derivative is exactly the scalar second derivative of the slice.
    calc
      secondDirectionalDerivative secondOrderConeBarrier p u
          = iteratedDeriv 2 (directionalSlice secondOrderConeBarrier p u) 0 := by
              rfl
      _ = iteratedDeriv 2
            (fun a : ℝ ↦
              -Real.log (s + (2 * c) * a - (((-2 * d) / 2 : ℝ) * a ^ (2 : ℕ)))) 0 := by
              rw [hslice]
      _ = (2 * c) ^ (2 : ℕ) / s ^ (2 : ℕ) + (-2 * d) / s := by
            simpa using hscalar23.1
      _ = ω1 ^ (2 : ℕ) + ω2 := by
            dsimp [ω1, ω2]
            field_simp [hs.ne']
  have hthird :
      thirdDirectionalDerivative secondOrderConeBarrier p u =
        2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2 := by
    -- The third directional derivative matches the cubic source-proof expression for the slice.
    calc
      thirdDirectionalDerivative secondOrderConeBarrier p u
          = iteratedDeriv 3 (directionalSlice secondOrderConeBarrier p u) 0 := by
              rfl
      _ = iteratedDeriv 3
            (fun a : ℝ ↦
              -Real.log (s + (2 * c) * a - (((-2 * d) / 2 : ℝ) * a ^ (2 : ℕ)))) 0 := by
              rw [hslice]
      _ = -(2 * (2 * c) ^ (3 : ℕ) / s ^ (3 : ℕ) + 3 * (2 * c) * (-2 * d) / s ^ (2 : ℕ)) := by
            simpa using hscalar23.2
      _ = 2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2 := by
            dsimp [ω1, ω2]
            field_simp [hs.ne']
            ring
  exact by
    simpa [s, c, d, ω1, ω2] using And.intro hgrad_pair (And.intro hsecond hthird)

/-- Helper for Lemma 5.4.3.3: when the vector part vanishes, the Lorentz discriminant collapses
to the obvious square `t² ‖h‖²`. -/
private theorem secondOrderCone_lorentz_discriminant_zero_branch
    (p u : E × ℝ) (hp1 : p.1 = 0) :
    (p.2 * u.2 - inner ℝ p.1 u.1) ^ (2 : ℕ) -
        (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) * (u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)) =
      p.2 ^ (2 : ℕ) * ‖u.1‖ ^ (2 : ℕ) := by
  -- Setting `x = 0` removes the mixed inner-product term and leaves a single norm square.
  rw [hp1]
  simp [pow_two]
  ring_nf

/-- Helper for Lemma 5.4.3.3: away from the zero vector, the Lorentz discriminant is a sum of
squares obtained by splitting the direction into its component parallel to `p.1` and the
orthogonal remainder. -/
private theorem secondOrderCone_lorentz_discriminant_sum_of_squares
    (p u : E × ℝ) (hp1 : p.1 ≠ 0) :
    let α : ℝ := inner ℝ p.1 u.1 / ‖p.1‖ ^ (2 : ℕ)
    let v : E := u.1 - α • p.1
    (p.2 * u.2 - inner ℝ p.1 u.1) ^ (2 : ℕ) -
        (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) * (u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)) =
      ‖p.1‖ ^ (2 : ℕ) * (p.2 * α - u.2) ^ (2 : ℕ) +
        (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) * ‖v‖ ^ (2 : ℕ) := by
  let α : ℝ := inner ℝ p.1 u.1 / ‖p.1‖ ^ (2 : ℕ)
  let v : E := u.1 - α • p.1
  have hnorm_sq_ne : ‖p.1‖ ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hp1)
  have horth : inner ℝ p.1 v = 0 := by
    -- The remainder `v` is chosen orthogonal to `p.1` by subtracting the parallel component.
    dsimp [v, α]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hnorm_sq_ne]
    ring
  have hu_split : u.1 = α • p.1 + v := by
    -- Reconstruct the direction from its parallel and orthogonal pieces.
    dsimp [v]
    abel
  have hinner : inner ℝ p.1 u.1 = α * ‖p.1‖ ^ (2 : ℕ) := by
    -- The orthogonal remainder contributes no inner product with `p.1`.
    calc
      inner ℝ p.1 u.1 = inner ℝ p.1 (α • p.1 + v) := by rw [hu_split]
      _ = inner ℝ p.1 (α • p.1) + inner ℝ p.1 v := by rw [inner_add_right]
      _ = α * ‖p.1‖ ^ (2 : ℕ) + 0 := by rw [inner_smul_right, real_inner_self_eq_norm_sq, horth]
      _ = α * ‖p.1‖ ^ (2 : ℕ) := by ring
  have hnorm_split :
      ‖u.1‖ ^ (2 : ℕ) = α ^ (2 : ℕ) * ‖p.1‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) := by
    have horth' : inner ℝ (α • p.1) v = 0 := by
      rw [real_inner_smul_left, horth]
      ring
    calc
      ‖u.1‖ ^ (2 : ℕ) = ‖α • p.1 + v‖ ^ (2 : ℕ) := by rw [hu_split]
      _ = ‖α • p.1‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) := by
            simpa [pow_two] using
              norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (α • p.1) v horth'
      _ = (|α| * ‖p.1‖) ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = α ^ (2 : ℕ) * ‖p.1‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) := by
            rw [pow_two, pow_two]
            nlinarith [sq_abs α]
  -- Route correction: isolate the parallel/orthogonal decomposition first, then the Lorentz
  -- discriminant becomes a scalar polynomial identity.
  calc
    (p.2 * u.2 - inner ℝ p.1 u.1) ^ (2 : ℕ) -
        (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) * (u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ))
        =
      (p.2 * u.2 - α * ‖p.1‖ ^ (2 : ℕ)) ^ (2 : ℕ) -
        (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) *
          (u.2 ^ (2 : ℕ) - (α ^ (2 : ℕ) * ‖p.1‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ))) := by
            rw [hinner, hnorm_split]
    _ = ‖p.1‖ ^ (2 : ℕ) * (p.2 * α - u.2) ^ (2 : ℕ) +
          (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) * ‖v‖ ^ (2 : ℕ) := by
            ring

/-- Helper for Lemma 5.4.3.3: the Lorentz-slice discriminant is nonnegative at interior points of
the second-order cone. This is the source proof's Cauchy-Schwarz invariant. -/
theorem secondOrderCone_lorentz_discriminant_nonneg
    {p u : E × ℝ} (hp : p ∈ interior (secondOrderCone E : Set (E × ℝ))) :
    0 ≤
      (p.2 * u.2 - inner ℝ p.1 u.1) ^ (2 : ℕ) -
        (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) * (u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)) := by
  by_cases hp1 : p.1 = 0
  · -- In the degenerate branch the discriminant is exactly the square `t² ‖h‖²`.
    rw [secondOrderCone_lorentz_discriminant_zero_branch (p := p) (u := u) hp1]
    positivity
  · let α : ℝ := inner ℝ p.1 u.1 / ‖p.1‖ ^ (2 : ℕ)
    let v : E := u.1 - α • p.1
    -- The nonzero branch is the source-faithful reverse-Cauchy identity plus positivity of each
    -- summand on the interior cone.
    rw [secondOrderCone_lorentz_discriminant_sum_of_squares (p := p) (u := u) hp1]
    have hslack : 0 ≤ p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ) := by
      exact le_of_lt (secondOrderCone_slack_pos_of_mem_interior p hp)
    have hparallel :
        0 ≤ ‖p.1‖ ^ (2 : ℕ) * (p.2 * α - u.2) ^ (2 : ℕ) := by
      exact mul_nonneg (sq_nonneg ‖p.1‖) (sq_nonneg (p.2 * α - u.2))
    have horth :
        0 ≤ (p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)) * ‖v‖ ^ (2 : ℕ) := by
      exact mul_nonneg hslack (sq_nonneg ‖v‖)
    exact add_nonneg hparallel horth

/-- Helper for Lemma 5.4.3.3: the scalar Lorentz-slice condition
`0 ≤ ω₁² + 2 ω₂` closes both the cubic bound and the parameter-`2` estimate. -/
theorem lorentz_slice_scalar_bounds
    (ω1 ω2 : ℝ) (hω : 0 ≤ ω1 ^ (2 : ℕ) + 2 * ω2) :
    |2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2| ≤
        2 * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) ∧
      ω1 ^ (2 : ℕ) ≤ 2 * (ω1 ^ (2 : ℕ) + ω2) := by
  constructor
  · let total : ℝ := ω1 ^ (2 : ℕ) + ω2
    have htotal_nonneg : 0 ≤ total := by
      -- The weaker hypothesis still implies the square-root argument is nonnegative.
      dsimp [total]
      nlinarith [sq_nonneg ω1, hω]
    have hfactor_nonneg : 0 ≤ 3 * ω1 ^ (2 : ℕ) + 4 * ω2 := by
      -- Rewrite the remaining factor in terms of `ω1² + 2 ω2`.
      nlinarith [sq_nonneg ω1, hω]
    have hpoly :
        4 * total ^ (3 : ℕ) - (2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2) ^ (2 : ℕ) =
          ω2 ^ (2 : ℕ) * (3 * ω1 ^ (2 : ℕ) + 4 * ω2) := by
      dsimp [total]
      ring
    have hsq :
        (2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2) ^ (2 : ℕ) ≤ 4 * total ^ (3 : ℕ) := by
      have hrhs_nonneg :
          0 ≤ ω2 ^ (2 : ℕ) * (3 * ω1 ^ (2 : ℕ) + 4 * ω2) := by
        exact mul_nonneg (sq_nonneg ω2) hfactor_nonneg
      nlinarith [hpoly]
    have hright_sq :
        (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ) = 4 * total ^ (3 : ℕ) := by
      calc
        (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ)
            = 4 * ((Real.sqrt total) ^ (2 : ℕ)) ^ (3 : ℕ) := by
                ring
        _ = 4 * total ^ (3 : ℕ) := by
              rw [Real.sq_sqrt htotal_nonneg]
    have hsq' :
        |2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2| ^ (2 : ℕ) ≤
          (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ) := by
      rw [sq_abs, hright_sq]
      exact hsq
    have hleft_nonneg : 0 ≤ |2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2| := abs_nonneg _
    have hright_nonneg : 0 ≤ 2 * (Real.sqrt total) ^ (3 : ℕ) := by positivity
    nlinarith
  · -- The parameter bound is the linear consequence of `0 ≤ ω1² + 2 ω2`.
    nlinarith [hω]

/-- Helper for Lemma 5.4.3.3: on raw pairs `E × ℝ`, the Lorentz barrier itself is the single
source-faithful theorem that remains to be proved before the public `WithLp` statement. -/
theorem raw_secondOrderConeBarrier_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith
      (E := E × ℝ)
      (interior (secondOrderCone E : Set (E × ℝ)))
      2
      secondOrderConeBarrier := by
  -- Route correction: the old perspective-gap route was nonaffine and blocked the pullback step.
  -- The remaining proof should instead work directly with the Lorentz slack line slice
  -- `a ↦ -log (s + 2 c a + d a^2)`, use the derivative formulas at `a = 0`, and then close both
  -- barrier inequalities from `secondOrderCone_lorentz_discriminant_nonneg` and
  -- `lorentz_slice_scalar_bounds`.
  let dom : Set (E × ℝ) := interior (secondOrderCone E : Set (E × ℝ))
  let F : E × ℝ → ℝ := secondOrderConeBarrier
  have hF_contDiffOn : ContDiffOn ℝ 3 F dom := by
    intro p hp
    simpa [F, dom] using (secondOrderConeBarrier_contDiffAt_three (p := p) hp).contDiffWithinAt
  have hstd : IsStandardSelfConcordantOn dom F := by
    have hdom_open : IsOpen dom := by
      simpa [dom] using isOpen_interior
    have hdom_convex : Convex ℝ dom := by
      simpa [dom] using (secondOrderCone E).convex.interior
    have hF_C2 : ContDiffOn ℝ 2 F dom := hF_contDiffOn.of_le (by norm_num)
    refine
      { isOpen_domain := hdom_open
        contDiffOn := hF_contDiffOn
        convexOn := ?_
        third_deriv_bound := ?_ }
    · -- The Lorentz discriminant makes the Hessian quadratic form nonnegative on every line.
      refine (convexOn_iff_hessian_quadratic_form_nonneg hdom_open hdom_convex hF_C2).2 ?_
      intro p hp u
      let s : ℝ := p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)
      let c : ℝ := p.2 * u.2 - inner ℝ p.1 u.1
      let d : ℝ := u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)
      let ω1 : ℝ := -(2 * c) / s
      let ω2 : ℝ := -(2 * d) / s
      have hs : 0 < s := by
        simpa [s, dom] using secondOrderCone_slack_pos_of_mem_interior p hp
      have hdisc : 0 ≤ c ^ (2 : ℕ) - s * d := by
        simpa [s, c, d] using secondOrderCone_lorentz_discriminant_nonneg (p := p) (u := u) hp
      have hω :
          0 ≤ ω1 ^ (2 : ℕ) + 2 * ω2 := by
        dsimp [ω1, ω2]
        field_simp [hs.ne']
        nlinarith [hdisc]
      have hω_nonneg : 0 ≤ ω1 ^ (2 : ℕ) + ω2 := by
        nlinarith [hω, sq_nonneg ω1]
      have hcont : ContDiffAt ℝ 3 F p := by
        simpa [F, dom] using secondOrderConeBarrier_contDiffAt_three (p := p) hp
      have hdiff : DifferentiableAt ℝ F p :=
        hcont.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
      have hgrad : DifferentiableAt ℝ (∇ F) p :=
        differentiableAt_gradient_of_contDiffAt_two
          (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      have hdata :=
        secondOrderConeBarrier_directional_data (p := p) (u := u) (E := E) hp
      have hquad :
          inner ℝ u (hessian F p u) = ω1 ^ (2 : ℕ) + ω2 := by
        calc
          inner ℝ u (hessian F p u) = secondDirectionalDerivative F p u := by
            symm
            exact secondDirectionalDerivative_eq_hessian_quadratic_form
              (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
          _ = ω1 ^ (2 : ℕ) + ω2 := by
                simpa [F] using hdata.2.1
      rw [real_inner_comm, hquad]
      exact hω_nonneg
    · intro p hp u
      let s : ℝ := p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)
      let c : ℝ := p.2 * u.2 - inner ℝ p.1 u.1
      let d : ℝ := u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)
      let ω1 : ℝ := -(2 * c) / s
      let ω2 : ℝ := -(2 * d) / s
      have hs : 0 < s := by
        simpa [s, dom] using secondOrderCone_slack_pos_of_mem_interior p hp
      have hdisc : 0 ≤ c ^ (2 : ℕ) - s * d := by
        simpa [s, c, d] using secondOrderCone_lorentz_discriminant_nonneg (p := p) (u := u) hp
      have hω :
          0 ≤ ω1 ^ (2 : ℕ) + 2 * ω2 := by
        dsimp [ω1, ω2]
        field_simp [hs.ne']
        nlinarith [hdisc]
      have hcont : ContDiffAt ℝ 3 F p := by
        simpa [F, dom] using secondOrderConeBarrier_contDiffAt_three (p := p) hp
      have hdiff : DifferentiableAt ℝ F p :=
        hcont.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
      have hgrad : DifferentiableAt ℝ (∇ F) p :=
        differentiableAt_gradient_of_contDiffAt_two
          (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      have hdata :=
        secondOrderConeBarrier_directional_data (p := p) (u := u) (E := E) hp
      have hnorm :
          ‖u‖[F; p] = Real.sqrt (ω1 ^ (2 : ℕ) + ω2) := by
        -- Rewrite the local norm through the already-computed second directional derivative.
        rw [hessianLocalNorm_def]
        calc
          Real.sqrt (inner ℝ u (hessian F p u))
              = Real.sqrt (secondDirectionalDerivative F p u) := by
                  congr 1
                  symm
                  exact secondDirectionalDerivative_eq_hessian_quadratic_form
                    (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
          _ = Real.sqrt (ω1 ^ (2 : ℕ) + ω2) := by
                simpa [F] using congrArg Real.sqrt hdata.2.1
      calc
        |thirdDirectionalDerivative F p u| = |2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2| := by
          simpa [F] using congrArg abs hdata.2.2
        _ ≤ 2 * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) := by
          exact (lorentz_slice_scalar_bounds ω1 ω2 hω).1
        _ = 2 * ‖u‖[F; p] ^ (3 : ℕ) := by
          rw [hnorm]
        _ = 2 * (1 : ℝ) * ‖u‖[F; p] ^ (3 : ℕ) := by
          ring
  refine
    { toIsStandardSelfConcordantOn := hstd
      barrier_parameter_bound := ?_ }
  intro p hp u
  have hPos : (hessian F p).IsPositive := hstd.hessian_isPositive hp
  refine ((_root_.barrier_parameter_bound_iff_gradient_inner_sq_le hPos).2 ?_) u
  intro u
  let s : ℝ := p.2 ^ (2 : ℕ) - ‖p.1‖ ^ (2 : ℕ)
  let c : ℝ := p.2 * u.2 - inner ℝ p.1 u.1
  let d : ℝ := u.2 ^ (2 : ℕ) - ‖u.1‖ ^ (2 : ℕ)
  let ω1 : ℝ := -(2 * c) / s
  let ω2 : ℝ := -(2 * d) / s
  have hs : 0 < s := by
    simpa [s, dom] using secondOrderCone_slack_pos_of_mem_interior p hp
  have hdisc : 0 ≤ c ^ (2 : ℕ) - s * d := by
    simpa [s, c, d] using secondOrderCone_lorentz_discriminant_nonneg (p := p) (u := u) hp
  have hω :
      0 ≤ ω1 ^ (2 : ℕ) + 2 * ω2 := by
    dsimp [ω1, ω2]
    field_simp [hs.ne']
    nlinarith [hdisc]
  have hcont : ContDiffAt ℝ 3 F p := by
    simpa [F, dom] using secondOrderConeBarrier_contDiffAt_three (p := p) hp
  have hdiff : DifferentiableAt ℝ F p :=
    hcont.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgrad : DifferentiableAt ℝ (∇ F) p :=
    differentiableAt_gradient_of_contDiffAt_two
      (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hdata :=
    secondOrderConeBarrier_directional_data (p := p) (u := u) (E := E) hp
  have hnorm_sq :
      ‖u‖[F; p] ^ (2 : ℕ) = ω1 ^ (2 : ℕ) + ω2 := by
    calc
      ‖u‖[F; p] ^ (2 : ℕ) = inner ℝ u (hessian F p u) := by
        simpa [hessianLocalNorm_def] using Real.sq_sqrt (hPos.inner_nonneg_right u)
      _ = secondDirectionalDerivative F p u := by
            symm
            exact secondDirectionalDerivative_eq_hessian_quadratic_form
              (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      _ = ω1 ^ (2 : ℕ) + ω2 := by
            simpa [F] using hdata.2.1
  calc
    (inner ℝ (∇ F p) u) ^ (2 : ℕ) = ω1 ^ (2 : ℕ) := by
      simpa [F] using congrArg (fun r : ℝ ↦ r ^ (2 : ℕ)) hdata.1
    _ ≤ 2 * (ω1 ^ (2 : ℕ) + ω2) := (lorentz_slice_scalar_bounds ω1 ω2 hω).2
    _ = (2 : ℝ) * ‖u‖[F; p] ^ (2 : ℕ) := by
          rw [← hnorm_sq]

-- Proof sketch: restrict the function to an arbitrary affine line `α ↦ (x + α • h, t + α * τ)`
-- inside `E × ℝ` and compute the derivatives of
-- `-log ((t + α * τ)^2 - ‖x + α • h‖^2)` as in the textbook. The inequality
-- `(t * τ - ⟪x, h⟫)^2 ≥ (t^2 - ‖x‖^2) * (τ^2 - ‖h‖^2)` gives the barrier-parameter bound with
-- `ν = 2`, and the same one-dimensional derivative computation yields the standard
-- self-concordance part on the interior domain `‖x‖ < t`.
/-- Lemma 5.4.3.3: the function `(x, t) ↦ -log (t^2 - ‖x‖^2)` is a `2`-self-concordant barrier
for the second-order cone `K₂ = {(x, t) ∈ E × ℝ | ‖x‖ ≤ t}`, viewed on the canonical `L²`
product owner `WithLp 2 (E × ℝ)` through the canonical raw-pair bridge `WithLp.ofLp`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ × ℝ` statement. -/
theorem secondOrderConeBarrier_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior (secondOrderCone E : Set (E × ℝ)))
      2
      (secondOrderConeBarrier ∘ ofZ) := by
  -- Pull the raw Lorentz barrier theorem back along the canonical raw-pair affine bridge.
  change IsSelfConcordantBarrierOnWith
      (ofPairContinuousAffine ⁻¹' interior (secondOrderCone E : Set (E × ℝ)))
      2
      (secondOrderConeBarrier ∘ ofPairContinuousAffine)
  simpa using
    (IsSelfConcordantBarrierOnWith.comp_continuousAffineMap
      (E := Z)
      (E₁ := E × ℝ)
      (dom := interior (secondOrderCone E : Set (E × ℝ)))
      (ν := 2)
      (F := secondOrderConeBarrier)
      raw_secondOrderConeBarrier_isSelfConcordantBarrierOnWith
      ofPairContinuousAffine)

end
