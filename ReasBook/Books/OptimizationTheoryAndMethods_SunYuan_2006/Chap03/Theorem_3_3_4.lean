/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.MonotoneConvergence
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_3_1

open scoped Gradient
open scoped Topology
open Filter Set

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

-- `ModifiedNewtonMethod` is the source-facing Chapter 3 owner for the modified Newton iterates,
-- gradients, directions, step sizes, and corrected Hessian data. The source uses the
-- quantitative descent bridge recalled in Example 3.3.3 to fit the Chapter 2 exact-line-search
-- convergence theorem; because the current run owner does not record that bridge, this file
-- packages it into a theorem-local source-faithful owner for the labeled theorem rather than
-- exposing it as a separate public hypothesis.

/-- Source-faithful quantitative bridge recalled in Chapter03 Example 3.3.3 (7): there exists
`κ > 0` such that every nonstationary modified-Newton step satisfies the descent estimate
`(3.3.16)`,
`-⟪∇ f (x_k), d_k⟫ / ‖d_k‖ ≥ (1 / κ) * ‖∇ f (x_k)‖`.

The current `ModifiedNewtonMethod` owner records the iterates, gradients, corrected linear
systems, exact line-search steps, and updates, but it does not by itself carry this uniform
descent estimate. The source theorem uses this recalled Chapter 3 bridge to enter the Chapter 2
global-convergence theorem, so it is kept explicit here rather than replaced by the more abstract
uniform angle-gap condition. -/
def ModifiedNewtonExample333DescentEstimate
    (f : E → ℝ)
    (A : ModifiedNewtonMethod n f) : Prop :=
  ∃ κ > 0, ∀ k : ℕ, ∇ f (A k) ≠ 0 →
    -(inner ℝ (∇ f (A k)) (A.d k)) / ‖A.d k‖ ≥ (1 / κ) * ‖∇ f (A k)‖

/-- Source-faithful run owner for Chapter03 Theorem 3.3.4: a modified Newton run together with
the descent estimate `(3.3.16)` recalled in Example 3.3.3. This packages the inherited Chapter 3
bridge into the run data so that the labeled theorem matches the book header instead of exposing
the recall as a separate hypothesis. -/
structure ModifiedNewtonMethodWithExample333DescentEstimate
    (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) extends ModifiedNewtonMethod n f where
  example333DescentEstimate :
    ModifiedNewtonExample333DescentEstimate f toModifiedNewtonMethod

/-- A source-faithful Theorem 3.3.4 run can be used as its indexed iterate sequence. -/
instance {f : E → ℝ} :
    CoeFun (ModifiedNewtonMethodWithExample333DescentEstimate n f)
      (fun _ ↦ ℕ → E) where
  coe A := A.toModifiedNewtonMethod

/-- Internal Chapter 3 setup: the modified Newton run `A` satisfies the uniform angle-gap bridge
recalled in Example 3.3.3, which is the ingredient needed to route the Chapter 3 method into
the Chapter 2 exact-line-search global-convergence theorem. -/
def ModifiedNewtonGlobalConvergenceSetup
    (f : E → ℝ)
    (A : ModifiedNewtonMethod n f) : Prop :=
  ∃ μ > 0, ∀ k : ℕ, ∇ f (A k) ≠ 0 →
    InnerProductGeometry.angle (A.d k) (-(∇ f (A k))) ≤ Real.pi / 2 - μ

/-- Helper for Chapter03 Theorem 3.3.4: on a nonstationary iterate, the modified Newton
direction is nonzero because the corrected linear system cannot send `0` to a nonzero gradient. -/
lemma modifiedNewton_direction_ne_of_gradient_ne
    (f : E → ℝ)
    (A : ModifiedNewtonMethod n f)
    (k : ℕ)
    (hk : ∇ f (A k) ≠ 0) :
    A.d k ≠ 0 := by
  -- Read the corrected linear system at `d_k = 0` and contradict the nonzero gradient.
  intro hd
  have hsystem : (0 : E) = -∇ f (A k) := by
    simpa [hd] using A.linearSystem_eq_neg_gradient k
  have hzero : ∇ f (A k) = 0 := by
    have := congrArg Neg.neg hsystem
    simpa using this.symm
  exact hk hzero

/-- Helper for Chapter03 Theorem 3.3.4: every nonstationary modified-Newton step is a genuine
descent direction, so the Chapter 1 descent API is available without unfolding the corrected
matrix construction. -/
lemma modifiedNewton_isDescentDirectionAt
    (f : E → ℝ)
    (A : ModifiedNewtonMethod n f)
    (k : ℕ)
    (hk : ∇ f (A k) ≠ 0) :
    IsDescentDirectionAt f (A k) (A.d k) := by
  -- Rewrite the descent test to the gradient pairing inequality.
  rw [isDescentDirectionAt_iff]
  have hd_ne : A.d k ≠ 0 :=
    modifiedNewton_direction_ne_of_gradient_ne f A k hk
  have hpos :
      0 < dotProduct (A.d k) ((A.correctedMatrix k).mulVec (A.d k)) :=
    Matrix.PosDef.dotProduct_mulVec_pos (A.corrected_posDef k) (by simpa using hd_ne)
  have hrewrite :
      dotProduct (A.d k) ((A.correctedMatrix k).mulVec (A.d k)) =
        -inner ℝ (A.g k) (A.d k) := by
    -- Convert the positive-definite quadratic form to the gradient pairing using the
    -- recorded corrected linear system.
    rw [A.linearSystem k, dotProduct_neg]
    have hdot :
        dotProduct (A.d k) (A.g k) = inner ℝ (A.g k) (A.d k) := by
      simpa [dotProduct, PiLp.inner_apply] using
        real_inner_comm (A.d k) (A.g k)
    rw [hdot]
  have hinner_neg_g : inner ℝ (A.g k) (A.d k) < 0 := by
    linarith [hpos, hrewrite]
  simpa [A.gradient_eq k] using hinner_neg_g

/-- Helper for Chapter03 Theorem 3.3.4: a fixed positive angle gap from `π / 2` forces
`Real.sin μ` to be positive. -/
lemma sin_pos_of_uniformAngleGap
    (f : E → ℝ)
    (x d : ℕ → E)
    (μ : ℝ)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    0 < Real.sin μ := by
  -- The uniform angle upper bound places `μ` inside `(0, π / 2]`.
  have hmu_le_pi_div_two : μ ≤ Real.pi / 2 := by
    have hang_nonneg :
        0 ≤ InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) :=
      InnerProductGeometry.angle_nonneg _ _
    have hang_le :
        InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) ≤ Real.pi / 2 - μ :=
      h_angle 0 (hgrad_ne 0)
    linarith
  have hmu_lt_pi : μ < Real.pi := by
    linarith [Real.pi_pos, hmu_le_pi_div_two]
  exact Real.sin_pos_of_pos_of_lt_pi hμ hmu_lt_pi

/-- Helper for Chapter03 Theorem 3.3.4: on any nonstationary iterate, exact line search strictly
decreases the objective. -/
lemma exactLineSearchStrictDecreaseOfGradientNeZero
    (f : E → ℝ)
    (x d : ℕ → E)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (k : ℕ)
    (hk : ∇ f (x k) ≠ 0) :
    f (x (k + 1)) < f (x k) := by
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k hk
  -- Compare the exact step with a short locally decreasing trial step.
  rcases hdesc.exists_localDecrease_lineSearchObjective with ⟨δ, hδpos, hδdecrease⟩
  have hhalf_pos : 0 < δ / 2 := by positivity
  have hhalf_lt : δ / 2 < δ := by linarith
  have htrial :
      lineSearchObjective f (x k) (d k) (δ / 2) <
        lineSearchObjective f (x k) (d k) 0 :=
    hδdecrease (δ / 2) hhalf_pos hhalf_lt
  have hmin :
      lineSearchObjective f (x k) (d k) (α k) ≤
        lineSearchObjective f (x k) (d k) (δ / 2) :=
    (h_exactLineSearch k).optimal (by positivity)
  have hstrict :
      lineSearchObjective f (x k) (d k) (α k) <
        lineSearchObjective f (x k) (d k) 0 :=
    lt_of_le_of_lt hmin htrial
  -- Rewriting through the update rule gives the textbook one-step decrease.
  simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update k] using hstrict

/-- Helper for Chapter03 Theorem 3.3.4: in the nonstationary branch, the objective values are
monotone decreasing. -/
lemma exactLineSearchObjectiveAntitone
    (f : E → ℝ)
    (x d : ℕ → E)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    Antitone (fun k : ℕ ↦ f (x k)) := by
  -- One-step strict decrease upgrades to antitonicity on `ℕ`.
  refine antitone_nat_of_succ_le fun k ↦ ?_
  exact
    (exactLineSearchStrictDecreaseOfGradientNeZero
      f x d α h_descent h_exactLineSearch h_update k (hgrad_ne k)).le

/-- Helper for Chapter03 Theorem 3.3.4: every nonstationary iterate stays below the initial
objective value. -/
lemma exactLineSearchObjective_le_initial
    (f : E → ℝ)
    (x d : ℕ → E)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    ∀ k : ℕ, f (x k) ≤ f (x 0) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k hk =>
      have hstrict :
          f (x (k + 1)) < f (x k) :=
        exactLineSearchStrictDecreaseOfGradientNeZero
          f x d α h_descent h_exactLineSearch h_update k (hgrad_ne k)
      linarith

/-- Helper for Chapter03 Theorem 3.3.4: if the objective sequence is antitone and does not tend
to `-∞`, then the successive decrease gaps converge to `0`. -/
lemma decreaseGapTendstoZeroOfNotAtBot
    (f : E → ℝ)
    (x d : ℕ → E)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (h_not_atBot : ¬ Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot) :
    Tendsto (fun k : ℕ ↦ f (x k) - f (x (k + 1))) atTop (nhds 0) := by
  have hanti : Antitone (fun k : ℕ ↦ f (x k)) :=
    exactLineSearchObjectiveAntitone f x d α h_descent h_exactLineSearch h_update hgrad_ne
  rcases tendsto_atTop_of_antitone hanti with hbot | ⟨l, hl⟩
  · exact False.elim (h_not_atBot hbot)
  · have hl_shift : Tendsto (fun k : ℕ ↦ f (x (k + 1))) atTop (nhds l) :=
      hl.comp (tendsto_add_atTop_nat 1)
    -- Subtracting the shifted limit gives the vanishing one-step gap.
    simpa using hl.sub hl_shift

/-- Helper for Chapter03 Theorem 3.3.4: if the gradients do not converge to `0`, then some
positive lower bound for their norms occurs frequently. -/
lemma frequentlyGradientNormGeOfNotTendstoZero
    (f : E → ℝ)
    (x : ℕ → E)
    (h_not :
      ¬ Tendsto (fun k : ℕ ↦ ∇ f (x k)) atTop (nhds (0 : E))) :
    ∃ ε > 0, ∃ᶠ k : ℕ in atTop, ε ≤ ‖∇ f (x k)‖ := by
  have h_not_norm :
      ¬ Tendsto (fun k : ℕ ↦ ‖∇ f (x k)‖) atTop (nhds (0 : ℝ)) := by
    intro hnorm
    apply h_not
    simpa [tendsto_iff_dist_tendsto_zero, dist_eq_norm] using hnorm
  have hnorm_char :
      Tendsto (fun k : ℕ ↦ ‖∇ f (x k)‖) atTop (nhds (0 : ℝ)) ↔
        ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (‖∇ f (x n)‖) 0 < ε := by
    exact Metric.tendsto_atTop
  rw [hnorm_char] at h_not_norm
  push Not at h_not_norm
  rcases h_not_norm with ⟨ε, hε, hεfail⟩
  refine ⟨ε, hε, ?_⟩
  rw [frequently_atTop]
  intro N
  rcases hεfail N with ⟨n, hnN, hn⟩
  refine ⟨n, hnN, ?_⟩
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn

/-- Helper for Chapter03 Theorem 3.3.4: on a compact neighborhood of the relevant level set,
every normalized trial step of length at most `αbar` enjoys the same affine decrease bound. -/
lemma compactLevelSet_normalizedTrialDrop
    (f : E → ℝ)
    (Kthick : Set E)
    (x d : ℕ → E)
    (μ αbar ε : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_hasGradient :
      ∀ y ∈ Kthick, HasGradientAt f (∇ f y) y)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_pos : 0 < αbar)
    (hαbar_spec :
      ∀ ⦃y z : E⦄,
        y ∈ Kthick →
        z ∈ Kthick →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2)
    {k : ℕ}
    (hkε : ε ≤ ‖∇ f (x k)‖)
    (hstep_mem :
      ∀ s ∈ Set.Icc (0 : ℝ) αbar,
        x k + s • ((‖d k‖)⁻¹ • d k) ∈ Kthick) :
    f (x k + αbar • ((‖d k‖)⁻¹ • d k)) ≤
      f (x k) - αbar * (ε * Real.sin μ) / 2 := by
  let u : E := (‖d k‖)⁻¹ • d k
  let φ : ℝ → ℝ := lineSearchObjective f (x k) u
  let B : ℝ → ℝ := fun t ↦ f (x k) - t * ((ε * Real.sin μ) / 2)
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k (hgrad_ne k)
  have hdk_ne : d k ≠ 0 := hdesc.direction_ne
  have hsin_pos : 0 < Real.sin μ :=
    sin_pos_of_uniformAngleGap f x d μ hμ h_angle hgrad_ne
  have hu_norm : ‖u‖ = 1 := by
    -- The normalized direction is a unit vector because the current step is nonzero.
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hdk_ne))]
    field_simp [norm_ne_zero_iff.mpr hdk_ne]
  have hRayDiff :
      ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ ↦ x k + s • u) t := by
    intro t
    exact (((hasDerivAt_id' t).smul_const u).const_add (x k)).differentiableAt
  have hbase_u :
      inner ℝ (∇ f (x k)) u ≤ -(ε * Real.sin μ) := by
    have hangle_nonneg :
        0 ≤ InnerProductGeometry.angle (d k) (-(∇ f (x k))) :=
      InnerProductGeometry.angle_nonneg _ _
    have hcos_lower :
        Real.sin μ ≤ Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) := by
      have hcos :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          hangle_nonneg
          (by linarith [Real.pi_pos])
          (h_angle k (hgrad_ne k))
      simpa [Real.cos_pi_div_two_sub] using hcos
    have hbase_dir :
        ε * Real.sin μ ≤ -(inner ℝ (∇ f (x k)) (d k) / ‖d k‖) := by
      have hmul_cos_lower :
          ‖∇ f (x k)‖ * Real.sin μ ≤
            ‖∇ f (x k)‖ *
              Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) := by
        exact mul_le_mul_of_nonneg_left hcos_lower (norm_nonneg _)
      calc
        ε * Real.sin μ ≤ ‖∇ f (x k)‖ * Real.sin μ := by
          exact mul_le_mul_of_nonneg_right hkε (le_of_lt hsin_pos)
        _ ≤ ‖∇ f (x k)‖ *
              Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) :=
          hmul_cos_lower
        _ = -(inner ℝ (∇ f (x k)) (d k) / ‖d k‖) := by
          simpa using
            gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm
              f (x k) (d k)
    have hrewrite :
        inner ℝ (∇ f (x k)) u = inner ℝ (∇ f (x k)) (d k) / ‖d k‖ := by
      dsimp [u]
      rw [inner_smul_right, div_eq_mul_inv, mul_comm]
    have hbase_u' :
        ε * Real.sin μ ≤ -inner ℝ (∇ f (x k)) u := by
      simpa [hrewrite] using hbase_dir
    linarith
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) αbar) := by
    intro t ht
    have hGradAt :
        HasGradientAt f (∇ f (x k + t • u)) (x k + t • u) :=
      h_hasGradient (x k + t • u) (by simpa [u] using hstep_mem t ht)
    -- Each point on the short normalized ray is differentiable, so the scalar profile is
    -- continuous on the whole interval.
    dsimp [φ]
    exact (hGradAt.differentiableAt.comp t (hRayDiff t)).continuousAt.continuousWithinAt
  have hφ_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) αbar, HasDerivWithinAt φ (deriv φ t) (Set.Ici t) t := by
    intro t ht
    have hGradAt :
        HasGradientAt f (∇ f (x k + t • u)) (x k + t • u) :=
      h_hasGradient (x k + t • u) (by simpa [u] using hstep_mem t ⟨ht.1, ht.2.le⟩)
    -- The right derivative is computed from the ordinary derivative of the ray profile.
    dsimp [φ]
    exact (hGradAt.differentiableAt.comp t (hRayDiff t)).hasDerivAt.hasDerivWithinAt
  have hB_cont : ContinuousOn B (Set.Icc (0 : ℝ) αbar) := by
    intro t ht
    -- The affine barrier is continuous everywhere.
    dsimp [B]
    exact ((continuous_const.continuousAt).sub
      (continuous_id.continuousAt.mul continuous_const.continuousAt)).continuousWithinAt
  have hB_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) αbar,
        HasDerivWithinAt B (-((ε * Real.sin μ) / 2)) (Set.Ici t) t := by
    intro t ht
    have hB_derivAt : HasDerivAt B (-((ε * Real.sin μ) / 2)) t := by
      -- Differentiate the affine comparison function explicitly.
      dsimp [B]
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id' t).mul_const ((ε * Real.sin μ) / 2)).neg).const_add (f (x k)))
    exact hB_derivAt.hasDerivWithinAt
  have hbase : φ 0 ≤ B 0 := by
    simp [φ, B, lineSearchObjective_zero]
  have hbound :
      ∀ t ∈ Set.Ico (0 : ℝ) αbar, deriv φ t ≤ -((ε * Real.sin μ) / 2) := by
    intro t ht
    let y : E := x k + t • u
    have hy : y ∈ Kthick := by
      simpa [y, u] using hstep_mem t ⟨ht.1, ht.2.le⟩
    have hxk : x k ∈ Kthick := by
      simpa [u] using hstep_mem 0 ⟨le_rfl, hαbar_pos.le⟩
    have hdist_le : dist (x k) y ≤ αbar := by
      calc
        dist (x k) y = ‖t • u‖ := by
          simp [y, dist_eq_norm, sub_eq_add_neg, u, add_comm]
        _ = |t| * ‖u‖ := norm_smul t u
        _ = t := by
          rw [hu_norm, abs_of_nonneg ht.1]
          simp
        _ ≤ αbar := ht.2.le
    have hGradAt : HasGradientAt f (∇ f y) y := h_hasGradient y hy
    have hderiv :
        deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u := by
      simpa [y] using
        (hGradAt.deriv_lineSearchObjective_apply :
          deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u)
    have h_grad_close :
        ‖∇ f y - ∇ f (x k)‖ ≤ (ε * Real.sin μ) / 2 :=
      hαbar_spec hy hxk (by simpa [dist_comm] using hdist_le)
    have hdiff_inner :
        inner ℝ (∇ f y - ∇ f (x k)) u ≤ (ε * Real.sin μ) / 2 := by
      have hnorm_bound :
          inner ℝ (∇ f y - ∇ f (x k)) u ≤ ‖∇ f y - ∇ f (x k)‖ * ‖u‖ :=
        real_inner_le_norm _ _
      rw [hu_norm, mul_one] at hnorm_bound
      exact le_trans hnorm_bound h_grad_close
    have hsum :
        inner ℝ (∇ f y) u =
          inner ℝ (∇ f y - ∇ f (x k)) u + inner ℝ (∇ f (x k)) u := by
      rw [inner_sub_left]
      ring
    -- Split the slope into the base-point descent term and the uniform continuity error.
    rw [hderiv, hsum]
    linarith
  have hbarrier :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) αbar → φ t ≤ B t :=
    image_le_of_deriv_right_le_deriv_boundary hφ_cont hφ_deriv hbase hB_cont hB_deriv hbound
  -- Evaluate the barrier inequality at the endpoint `αbar`.
  calc
    f (x k + αbar • ((‖d k‖)⁻¹ • d k)) = φ αbar := by
      simp [φ, u, lineSearchObjective_apply]
    _ ≤ B αbar := hbarrier ⟨hαbar_pos.le, le_rfl⟩
    _ = f (x k) - αbar * (ε * Real.sin μ) / 2 := by
      ring

/-- Helper for Chapter03 Theorem 3.3.4: on a compact level set inside an open `C²` domain, a
uniform angle gap yields one fixed objective decrease whenever the current gradient norm is
bounded away from `0`. -/
lemma exactLineSearchUniformStepDropOnCompactLevelSet
    (f : E → ℝ)
    (D : Set E)
    (x d : ℕ → E)
    (α : ℕ → ℝ)
    (μ : ℝ)
    (hD_open : IsOpen D)
    (h_contDiff : ContDiffOn ℝ 2 f D)
    (h_compact : IsCompact (D ∩ {y | f y ≤ f (x 0)}))
    (h_mem : ∀ k, x k ∈ D)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ αbar > 0, ∀ k : ℕ, ε ≤ ‖∇ f (x k)‖ →
        f (x (k + 1)) ≤ f (x k) - αbar * (ε * Real.sin μ) / 2 := by
  intro ε hε
  let K : Set E := D ∩ {y | f y ≤ f (x 0)}
  obtain ⟨δ, hδ_pos, hδ_subset⟩ :=
    h_compact.exists_cthickening_subset_open hD_open (by intro y hy; exact hy.1)
  let Kthick : Set E := Metric.cthickening δ K
  have hK_subset : K ⊆ Kthick := Metric.self_subset_cthickening K
  have hKthick_subset : Kthick ⊆ D := hδ_subset
  have hKthick_compact : IsCompact Kthick := h_compact.cthickening
  have hC1fderiv : ContDiffOn ℝ 1 (fderiv ℝ f) D := by
    -- Differentiate the `C²` objective once on the open domain.
    simpa using h_contDiff.fderiv_of_isOpen hD_open (by norm_num)
  have hC1grad : ContDiffOn ℝ 1 (gradient f) D := by
    -- Rewrite the gradient as the Riesz representative of the derivative.
    change ContDiffOn ℝ 1
      (fun z ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)) D
    have hsymmContDiff :
        ContDiff ℝ 1 ((InnerProductSpace.toDual ℝ E).symm :
          ((E →L[ℝ] ℝ) → E)) :=
      (InnerProductSpace.toDual ℝ E).symm.contDiff
    exact ContDiff.comp_contDiffOn hsymmContDiff hC1fderiv
  have h_hasGradient :
      ∀ y ∈ Kthick, HasGradientAt f (∇ f y) y := by
    intro y hy
    have hyD : y ∈ D := hKthick_subset hy
    have hyDiff : DifferentiableAt ℝ f y :=
      (h_contDiff.contDiffAt (hD_open.mem_nhds hyD)).differentiableAt (by norm_num)
    -- Inside the open neighborhood, the canonical gradient is the genuine gradient.
    exact hyDiff.hasGradientAt
  have h_gradUniform : UniformContinuousOn (∇ f) Kthick := by
    have hcont : ContinuousOn (∇ f) Kthick := by
      exact hC1grad.continuousOn.mono fun _ hy ↦ hKthick_subset hy
    exact hKthick_compact.uniformContinuousOn_of_continuous hcont
  have hsin_pos : 0 < Real.sin μ :=
    sin_pos_of_uniformAngleGap f x d μ hμ h_angle hgrad_ne
  have hhalf_pos : 0 < (ε * Real.sin μ) / 2 := by
    positivity
  rcases (Metric.uniformContinuousOn_iff_le.mp h_gradUniform) ((ε * Real.sin μ) / 2) hhalf_pos with
    ⟨αuc, hαuc_pos, hαuc_spec⟩
  let αbar : ℝ := min δ αuc
  have hαbar_pos : 0 < αbar := by
    dsimp [αbar]
    exact lt_min hδ_pos hαuc_pos
  have hαbar_le_δ : αbar ≤ δ := by
    dsimp [αbar]
    exact min_le_left _ _
  have hαbar_le_αuc : αbar ≤ αuc := by
    dsimp [αbar]
    exact min_le_right _ _
  refine ⟨αbar, hαbar_pos, ?_⟩
  intro k hkε
  have hxk_memK : x k ∈ K := by
    constructor
    · exact h_mem k
    · exact
        exactLineSearchObjective_le_initial
          f x d α h_descent h_exactLineSearch h_update hgrad_ne k
  have hstep_mem :
      ∀ s ∈ Set.Icc (0 : ℝ) αbar,
        x k + s • ((‖d k‖)⁻¹ • d k) ∈ Kthick := by
    intro s hs
    apply Metric.mem_cthickening_of_dist_le
      (x k + s • ((‖d k‖)⁻¹ • d k)) (x k) δ K hxk_memK
    calc
      dist (x k + s • ((‖d k‖)⁻¹ • d k)) (x k) =
          ‖s • ((‖d k‖)⁻¹ • d k)‖ := by
            simp [dist_eq_norm, sub_eq_add_neg, add_comm]
      _ = |s| * ‖((‖d k‖)⁻¹ • d k)‖ := norm_smul s _
      _ = s * ‖((‖d k‖)⁻¹ • d k)‖ := by rw [abs_of_nonneg hs.1]
      _ ≤ s := by
        have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k (hgrad_ne k)
        have hdk_ne : d k ≠ 0 := hdesc.direction_ne
        have hu_norm : ‖((‖d k‖)⁻¹ • d k)‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hdk_ne))]
          field_simp [norm_ne_zero_iff.mpr hdk_ne]
        rw [hu_norm, mul_one]
      _ ≤ αbar := hs.2
      _ ≤ δ := hαbar_le_δ
  have hαbar_spec :
      ∀ ⦃y z : E⦄,
        y ∈ Kthick →
        z ∈ Kthick →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2 := by
    intro y z hy hz hdist
    exact hαuc_spec y hy z hz (le_trans hdist hαbar_le_αuc)
  have htrial_drop :
      f (x k + αbar • ((‖d k‖)⁻¹ • d k)) ≤
        f (x k) - αbar * (ε * Real.sin μ) / 2 :=
    compactLevelSet_normalizedTrialDrop
      f Kthick x d μ αbar ε h_descent h_hasGradient hμ h_angle hgrad_ne hαbar_pos
      hαbar_spec hkε hstep_mem
  have htrial_nonneg : 0 ≤ αbar / ‖d k‖ := by
    exact div_nonneg hαbar_pos.le (norm_nonneg _)
  have hoptimal :
      f (x (k + 1)) ≤ f (x k + αbar • ((‖d k‖)⁻¹ • d k)) := by
    have hopt :
        lineSearchObjective f (x k) (d k) (α k) ≤
          lineSearchObjective f (x k) (d k) (αbar / ‖d k‖) :=
      (h_exactLineSearch k).optimal htrial_nonneg
    -- Rewrite the scalar trial parameter as the normalized step of length `αbar`.
    simpa [lineSearchObjective_apply, h_update k, div_eq_mul_inv, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using hopt
  exact le_trans hoptimal htrial_drop

/-- Helper for Chapter03 Theorem 3.3.4: a nonstationary exact-line-search run on the compact
level set `D ∩ {y | f y ≤ f (x 0)}` has gradients converging to `0`. -/
theorem exactLineSearchGradientTendstoZeroOnCompactLevelSet
    (f : E → ℝ)
    (D : Set E)
    (x d : ℕ → E)
    (α : ℕ → ℝ)
    (μ : ℝ)
    (hD_open : IsOpen D)
    (h_contDiff : ContDiffOn ℝ 2 f D)
    (h_compact : IsCompact (D ∩ {y | f y ≤ f (x 0)}))
    (h_mem : ∀ k, x k ∈ D)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    Tendsto (fun k ↦ ∇ f (x k)) atTop (𝓝 0) := by
  let K : Set E := D ∩ {y | f y ≤ f (x 0)}
  have hcont_level : ContinuousOn f K := by
    -- Restrict the ambient `C²` regularity to the compact level set.
    exact h_contDiff.continuousOn.mono fun _ hy ↦ hy.1
  rcases IsCompact.bddBelow_image h_compact hcont_level with ⟨m, hm⟩
  have h_not_atBot : ¬ Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot := by
    intro hbot
    rw [tendsto_atTop_atBot] at hbot
    rcases hbot (m - 1) with ⟨N, hN⟩
    have hxN : x N ∈ K := by
      constructor
      · exact h_mem N
      · exact
          exactLineSearchObjective_le_initial
            f x d α h_descent h_exactLineSearch h_update hgrad_ne N
    have hmN : m ≤ f (x N) := hm ⟨x N, hxN, rfl⟩
    have hbotN : f (x N) ≤ m - 1 := hN N le_rfl
    linarith
  have hgap_tendsto :
      Tendsto (fun k : ℕ ↦ f (x k) - f (x (k + 1))) atTop (nhds 0) :=
    decreaseGapTendstoZeroOfNotAtBot
      f x d α h_descent h_exactLineSearch h_update hgrad_ne h_not_atBot
  by_contra hgrad_not
  obtain ⟨ε, hε, hfreq⟩ :=
    frequentlyGradientNormGeOfNotTendstoZero f x hgrad_not
  obtain ⟨αbar, hαbar_pos, hdrop⟩ :=
    exactLineSearchUniformStepDropOnCompactLevelSet
      f D x d α μ hD_open h_contDiff h_compact h_mem h_descent h_exactLineSearch
      h_update hμ h_angle hgrad_ne hε
  have hsin_pos : 0 < Real.sin μ :=
    sin_pos_of_uniformAngleGap f x d μ hμ h_angle hgrad_ne
  have hconst_pos : 0 < αbar * (ε * Real.sin μ) / 2 := by
    positivity
  obtain ⟨φ, hφmono, hφfreq⟩ := extraction_of_frequently_atTop hfreq
  have hgap_subseq :
      Tendsto (fun n : ℕ ↦ f (x (φ n)) - f (x (φ n + 1))) atTop (nhds 0) :=
    hgap_tendsto.comp hφmono.tendsto_atTop
  rw [Metric.tendsto_atTop] at hgap_subseq
  obtain ⟨N, hN⟩ := hgap_subseq _ hconst_pos
  have hlower :
      αbar * (ε * Real.sin μ) / 2 ≤
        f (x (φ N)) - f (x (φ N + 1)) := by
    linarith [hdrop (φ N) (hφfreq N)]
  have hsmall :
      dist (f (x (φ N)) - f (x (φ N + 1))) 0 < αbar * (ε * Real.sin μ) / 2 :=
    hN N le_rfl
  have hsmall' :
      f (x (φ N)) - f (x (φ N + 1)) < αbar * (ε * Real.sin μ) / 2 := by
    have hgap_nonneg :
        0 ≤ f (x (φ N)) - f (x (φ N + 1)) := by
      have hconst_nonneg : 0 ≤ αbar * (ε * Real.sin μ) / 2 := by positivity
      exact le_trans hconst_nonneg hlower
    simpa [Real.dist_eq, abs_of_nonneg hgap_nonneg] using hsmall
  linarith

/-- Internal Chapter 3 helper: once the source-recalled uniform angle-gap bridge from
Example 3.3.3 has been supplied for a modified Newton run, the Chapter 2 exact-line-search
convergence route yields `∇ f (A k) ⟶ 0`. This helper is intentionally unlabeled, because the
book's Theorem 3.3.4 does not expose the angle-gap data as part of its public statement. -/
theorem modifiedNewton_gradient_tendsto_zero_of_uniform_angle
    (f : E → ℝ)
    (D : Set E)
    (A : ModifiedNewtonMethod n f)
    (μ : ℝ)
    (hD_open : IsOpen D)
    (h_contDiff : ContDiffOn ℝ 2 f D)
    (h_compact : IsCompact (D ∩ {x | f x ≤ f A.x0}))
    (h_mem : ∀ k, A k ∈ D)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (A k) ≠ 0 →
        InnerProductGeometry.angle (A.d k) (-(∇ f (A k))) ≤ Real.pi / 2 - μ) :
    Tendsto (fun k ↦ ∇ f (A k)) atTop (𝓝 0) := by
  by_cases hstop : ∃ k : ℕ, ∇ f (A k) = 0
  · rcases hstop with ⟨k0, hk0⟩
    have htail_zero : ∀ m : ℕ, ∇ f (A (k0 + m)) = 0 := by
      intro m
      induction m with
      | zero =>
          simpa using hk0
      | succ m hm =>
          have hlin :
              (A.correctedMatrix (k0 + m)).mulVec (A.d (k0 + m)) = 0 := by
            simpa [hm] using A.linearSystem_eq_neg_gradient (k0 + m)
          have hd_zero : A.d (k0 + m) = 0 := by
            by_contra hd_ne
            have hpos :=
              Matrix.PosDef.dotProduct_mulVec_pos (A.corrected_posDef (k0 + m))
                (x := (A.d (k0 + m)).ofLp) (by simpa using hd_ne)
            rw [hlin, dotProduct_zero] at hpos
            linarith
          have hxnext : A (k0 + (m + 1)) = A (k0 + m) := by
            simpa [Nat.add_assoc, hd_zero] using A.update (k0 + m)
          -- Once one iterate is stationary, the corrected linear system forces a zero step, so
          -- the subsequent iterate coincides with the current one and the gradient stays zero.
          simpa [hxnext] using hm
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨k0, ?_⟩
    intro n hn
    rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
    simpa [htail_zero m, dist_eq_norm] using hε
  · have hgrad_ne : ∀ k : ℕ, ∇ f (A k) ≠ 0 := by
      intro k hk
      exact hstop ⟨k, hk⟩
    -- Route correction: instead of forcing the Chapter 2 theorem through
    -- `initialSublevelSet f A.x0`, run the same contradiction on the compact level set
    -- `D ∩ {y | f y ≤ f A.x0}` and a compact neighborhood inside `D`.
    exact
      exactLineSearchGradientTendstoZeroOnCompactLevelSet
        f D A A.d A.α μ hD_open h_contDiff (by simpa [A.x_zero] using h_compact) h_mem
        (fun k hk ↦ modifiedNewton_isDescentDirectionAt f A k hk)
        A.exactLineSearch A.update hμ h_angle hgrad_ne

/-- Internal Chapter 3 bridge: the source-faithful descent estimate `(3.3.16)` recalled in
Example 3.3.3 implies the uniform angle-gap setup needed by
`modifiedNewton_gradient_tendsto_zero_of_uniform_angle`. -/
theorem modifiedNewtonGlobalConvergenceSetup_of_example333DescentEstimate
    (f : E → ℝ)
    (A : ModifiedNewtonMethod n f)
    (h_example333 : ModifiedNewtonExample333DescentEstimate f A) :
    ModifiedNewtonGlobalConvergenceSetup f A := by
  rcases h_example333 with ⟨κ, hκ, hestimate⟩
  refine ⟨Real.pi / 2 - Real.arccos (1 / κ), ?_, ?_⟩
  · -- The reciprocal cosine threshold coming from Example 3.3.3 is strictly positive.
    have harccos_lt :
        Real.arccos (1 / κ) < Real.pi / 2 :=
      (Real.arccos_lt_pi_div_two).2 (one_div_pos.mpr hκ)
    linarith
  · intro k hk
    let θ := InnerProductGeometry.angle (A.d k) (-(∇ f (A k)))
    have hgrad_pos : 0 < ‖∇ f (A k)‖ := norm_pos_iff.mpr hk
    have hdescent : IsDescentDirectionAt f (A k) (A.d k) :=
      modifiedNewton_isDescentDirectionAt f A k hk
    have hestimate' :
        (1 / κ) * ‖∇ f (A k)‖ ≤
          -(inner ℝ (∇ f (A k)) (A.d k) / ‖A.d k‖) := by
      -- Re-express the source estimate in the cosine-identity normal form.
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hestimate k hk
    have hcos_times :
        (1 / κ) * ‖∇ f (A k)‖ ≤ ‖∇ f (A k)‖ * Real.cos θ := by
      simpa [θ] using
        (show
          (1 / κ) * ‖∇ f (A k)‖ ≤
            ‖∇ f (A k)‖ *
              Real.cos (InnerProductGeometry.angle (A.d k) (-(∇ f (A k)))) by
          simpa [
            gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm,
            θ
          ] using hestimate')
    have hcos_lower : 1 / κ ≤ Real.cos θ := by
      nlinarith
    have hθ_nonneg : 0 ≤ θ := by
      simpa [θ] using InnerProductGeometry.angle_nonneg (A.d k) (-(∇ f (A k)))
    have hθ_le_pi : θ ≤ Real.pi := by
      simpa [θ] using InnerProductGeometry.angle_le_pi (A.d k) (-(∇ f (A k)))
    have hθ_le_arccos : θ ≤ Real.arccos (1 / κ) := by
      -- Monotonicity of `arccos` on `[0, π]` turns the cosine lower bound into an angle bound.
      have harccos_cmp :
          Real.arccos (Real.cos θ) ≤ Real.arccos (1 / κ) :=
        Real.arccos_le_arccos hcos_lower
      simpa [Real.arccos_cos hθ_nonneg hθ_le_pi] using harccos_cmp
    simpa [θ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hθ_le_arccos

/-- Chapter03 Theorem 3.3.4: if `f` is twice continuously differentiable on an open
set `D`, the sublevel set `D ∩ {x | f x ≤ f x0}` is compact, and `A` is a modified
Newton run in the source sense of Chapter 3, whose iterates stay in `D`, then
`∇ f (A k) ⟶ 0`. The Example 3.3.3 descent estimate used by the source proof is packaged inside
the run owner instead of appearing as a separate hypothesis. -/
theorem modifiedNewton_gradient_tendsto_zero
    (f : E → ℝ)
    (D : Set E)
    (A : ModifiedNewtonMethodWithExample333DescentEstimate n f)
    (hD_open : IsOpen D)
    (h_contDiff : ContDiffOn ℝ 2 f D)
    (h_compact : IsCompact (D ∩ {x | f x ≤ f A.x0}))
    (h_mem : ∀ k, A k ∈ D) :
    Tendsto (fun k ↦ ∇ f (A k)) atTop (𝓝 0) := by
  -- Extract the fixed angle gap encoded by the source Example 3.3.3 estimate.
  rcases
      modifiedNewtonGlobalConvergenceSetup_of_example333DescentEstimate
        f A.toModifiedNewtonMethod A.example333DescentEstimate with
    ⟨μ, hμ, h_angle⟩
  -- The convergence statement is the local wrapper around the uniform-angle helper.
  exact
    modifiedNewton_gradient_tendsto_zero_of_uniform_angle
      f D A.toModifiedNewtonMethod μ hD_open h_contDiff h_compact h_mem hμ h_angle

end
