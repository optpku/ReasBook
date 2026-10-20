module

public import ReasLib.Optimization.DFP.Polar.PointGeometry
public import ReasLib.Optimization.DFP.Polar.InterpolationSum
public import ReasLib.Optimization.DFP.Polar.ActualObjective
public import ReasLib.Analysis.Calculus.Gradient.HessianHolder
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.HolderSharpness

/-- Helper for eq:counterexample-nonlipschitz: the ratio of a cubic scale to a
quadratic scale raised to `1+β` has the exact source exponent `1−2β`. -/
theorem cubic_div_quadratic_rpow (t β : ℝ) (ht : 0 < t) :
    t ^ 3 / (t ^ 2) ^ (1 + β) = t ^ (1 - 2 * β) := by
  have hthree : t ^ 3 = t ^ (3 : ℝ) := (Real.rpow_natCast t 3).symm
  have htwo : t ^ 2 = t ^ (2 : ℝ) := (Real.rpow_natCast t 2).symm
  have hexponent : (3 : ℝ) - 2 * (1 + β) = 1 - 2 * β := by ring
  rw [hthree, htwo, ← Real.rpow_mul ht.le, ← Real.rpow_sub ht, hexponent]

/-- Helper for eq:counterexample-nonlipschitz: the exact cubic-to-quadratic
ratio retains its source exponent after a fixed positive step coefficient. -/
theorem cubic_div_scaled_quadratic_rpow (c U t β : ℝ) (hU : 0 < U) (ht : 0 < t) :
    c * t ^ 3 / (U * t ^ 2) ^ (1 + β) =
      (c / U ^ (1 + β)) * t ^ (1 - 2 * β) := by
  rw [Real.mul_rpow hU.le (sq_nonneg t)]
  calc
    c * t ^ 3 / (U ^ (1 + β) * (t ^ 2) ^ (1 + β)) =
        (c / U ^ (1 + β)) * (t ^ 3 / (t ^ 2) ^ (1 + β)) :=
      (div_mul_div_comm _ _ _ _).symm
    _ = (c / U ^ (1 + β)) * t ^ (1 - 2 * β) := by
      rw [cubic_div_quadratic_rpow t β ht]

/-- Helper for eq:counterexample-nonlipschitz: a cubic residual lower bound
and quadratic positive step upper bound give the precise source power lower bound. -/
theorem cubicQuadraticRatio_lower {a d t c U β : ℝ}
    (ht : 0 < t) (hc : 0 ≤ c) (hU : 0 < U) (hβ : 0 ≤ 1 + β)
    (hd : 0 < d) (ha : c * t ^ 3 ≤ a) (hstep : d ≤ U * t ^ 2) :
    (c / U ^ (1 + β)) * t ^ (1 - 2 * β) ≤ a / d ^ (1 + β) := by
  have haNonneg : 0 ≤ a := (mul_nonneg hc (pow_nonneg ht.le 3)).trans ha
  have hdenom := Real.rpow_le_rpow hd.le hstep hβ
  have hlargePositive := Real.rpow_pos_of_pos (mul_pos hU (sq_pos_of_pos ht)) (1 + β)
  rw [← cubic_div_scaled_quadratic_rpow c U t β hU ht]
  calc
    c * t ^ 3 / (U * t ^ 2) ^ (1 + β) ≤ a / (U * t ^ 2) ^ (1 + β) :=
      div_le_div_of_nonneg_right ha hlargePositive.le
    _ ≤ a / d ^ (1 + β) :=
      div_le_div_of_nonneg_left haNonneg (Real.rpow_pos_of_pos hd _) hdenom

/-- Helper for eq:counterexample-nonlipschitz: a cubic residual upper bound
and quadratic step lower bound give the corresponding source power upper bound. -/
theorem cubicQuadraticRatio_upper {a d t C lower β : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C) (hlower : 0 < lower) (hβ : 0 ≤ 1 + β)
    (ha : a ≤ C * t ^ 3) (hstep : lower * t ^ 2 ≤ d) :
    a / d ^ (1 + β) ≤ (C / lower ^ (1 + β)) * t ^ (1 - 2 * β) := by
  have hd := (mul_pos hlower (sq_pos_of_pos ht)).trans_le hstep
  have hdenom := Real.rpow_le_rpow (mul_pos hlower (sq_pos_of_pos ht)).le hstep hβ
  rw [← cubic_div_scaled_quadratic_rpow C lower t β hlower ht]
  calc
    a / d ^ (1 + β) ≤ (C * t ^ 3) / d ^ (1 + β) :=
      div_le_div_of_nonneg_right ha (Real.rpow_pos_of_pos hd _).le
    _ ≤ (C * t ^ 3) / (lower * t ^ 2) ^ (1 + β) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (pow_nonneg ht.le 3))
        (Real.rpow_pos_of_pos (mul_pos hlower (sq_pos_of_pos ht)) _) hdenom

/-- Helper for eq:counterexample-nonlipschitz: positive scales tending to zero
make the source power `t^(1−2β)` diverge for every `β>1/2`. -/
theorem sourcePower_tendsto_atTop {t : ℕ → ℝ} (ht : ∀ n, 0 < t n)
    (hzero : Tendsto t atTop (𝓝 0)) {β : ℝ} (hβ : 1 / 2 < β) :
    Tendsto (fun n ↦ t n ^ (1 - 2 * β)) atTop atTop := by
  have hexponent : 1 - 2 * β < 0 := by linarith
  have hwithin : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Filter.Eventually.of_forall ht⟩
  exact (tendsto_rpow_neg_nhdsGT_zero hexponent).comp hwithin

/-- Helper for eq:counterexample-nonlipschitz: cubic residuals with positive
quadratic steps force the source normalized residual ratio to diverge. -/
theorem cubicQuadraticRatio_tendsto_atTop {a d t : ℕ → ℝ} {c U β : ℝ}
    (ht : ∀ n, 0 < t n) (hzero : Tendsto t atTop (𝓝 0))
    (hc : 0 < c) (hU : 0 < U) (hβ : 1 / 2 < β)
    (hd : ∀ n, 0 < d n) (ha : ∀ n, c * t n ^ 3 ≤ a n)
    (hstep : ∀ n, d n ≤ U * t n ^ 2) :
    Tendsto (fun n ↦ a n / d n ^ (1 + β)) atTop atTop := by
  have hcoefficient : 0 < c / U ^ (1 + β) := div_pos hc (Real.rpow_pos_of_pos hU _)
  have hpower := (sourcePower_tendsto_atTop ht hzero hβ).const_mul_atTop hcoefficient
  have hexponent : 0 ≤ 1 + β := by linarith
  apply tendsto_atTop_mono _ hpower
  intro n
  exact cubicQuadraticRatio_lower (ht n) hc.le hU hexponent (hd n) (ha n) (hstep n)

/-- Helper for eq:counterexample-nonlipschitz: on any convex set a Hölder Hessian
bounds the gradient Taylor remainder by the source order `‖y−x‖^(1+β)`.
The mean-value bound has the same order as the source integral estimate. -/
theorem norm_gradientRemainder_le_on_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {S : Set E} (hf : ContDiff ℝ 2 f) (hS : Convex ℝ S)
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hholder : ∀ x ∈ S, ∀ y ∈ S, ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖gradient f y - gradient f x - hessian f x (y - x)‖ ≤ C * ‖y - x‖ ^ (1 + β) := by
  have hgradient : Differentiable ℝ (gradient f) :=
    (hf.gradient_succ (n := 1)).differentiable_one
  rw [hessian_def]
  apply norm_firstOrderRemainder_le_of_holderDerivative hC hβ
  · intro z _
    exact hgradient z
  · intro z hz
    have hzS := hS.segment_subset hx hy hz
    simpa only [hessian_def] using hholder z hzS x hx

/-- Helper for eq:counterexample-nonlipschitz and thm:main: a divergent secant
gradient remainder ratio excludes a Hölder Hessian on any convex set containing
the original segment endpoints. -/
theorem not_holderHessianOn_of_remainderRatio_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {S : Set E} (hf : ContDiff ℝ 2 f) (hS : Convex ℝ S)
    {x y : ℕ → E} (hx : ∀ n, x n ∈ S) (hy : ∀ n, y n ∈ S)
    (hstep : ∀ n, 0 < ‖y n - x n‖) {β : ℝ} (hβ : 0 ≤ β)
    (hdiverge : Tendsto
      (fun n ↦ ‖gradient f (y n) - gradient f (x n) - hessian f (x n) (y n - x n)‖ /
        ‖y n - x n‖ ^ (1 + β)) atTop atTop) :
    ¬ ∃ C ≥ 0, ∀ x ∈ S, ∀ y ∈ S,
      ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β := by
  rintro ⟨C, hC, hholder⟩
  obtain ⟨n, hn⟩ := (hdiverge.eventually (eventually_gt_atTop C)).exists
  have hbound := norm_gradientRemainder_le_on_convex hf hS hC hβ hholder (hx n) (hy n)
  have hratio := (div_le_iff₀ (Real.rpow_pos_of_pos (hstep n) (1 + β))).mpr hbound
  exact (not_lt_of_ge hratio) hn

/-- Helper for eq:counterexample-nonlipschitz: the original even physical step. -/
def evenStep (p : Parameters) (j : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.point (2 * j + 1) - p.point (2 * j)

/-- Helper for eq:counterexample-nonlipschitz: the original even-step formula. -/
theorem evenStep_def (p : Parameters) (j : ℕ) :
    evenStep p j = p.point (2 * j + 1) - p.point (2 * j) := by rfl

/-- Helper for eq:counterexample-nonlipschitz: the gradient secant Taylor residual
of the exact source interpolation objective at an original even step. -/
def evenResidual (p : Parameters) (κ : ℝ) (j : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  gradient (InterpolationSum.polarObjective p κ) (p.point (2 * j + 1)) -
    gradient (InterpolationSum.polarObjective p κ) (p.point (2 * j)) -
    hessian (InterpolationSum.polarObjective p κ) (p.point (2 * j)) (evenStep p j)

/-- Helper for eq:counterexample-nonlipschitz: the actual source residual formula. -/
theorem evenResidual_def (p : Parameters) (κ : ℝ) (j : ℕ) :
    evenResidual p κ j =
      gradient (InterpolationSum.polarObjective p κ) (p.point (2 * j + 1)) -
        gradient (InterpolationSum.polarObjective p κ) (p.point (2 * j)) -
        hessian (InterpolationSum.polarObjective p κ) (p.point (2 * j)) (evenStep p j) := by rfl

/-- Helper for eq:counterexample-nonlipschitz: the original even interpolation
correction vanishes exactly, because the original even multiplier equals one. -/
theorem polarCoefficient_even (p : Parameters) (j : ℕ) :
    InterpolationSum.polarCoefficient p (2 * j) = 0 := by
  rw [InterpolationSum.polarCoefficient_apply, Parameters.gradient_def, Parameters.zeta_even,
    one_smul, sub_self]

/-- Helper for eq:counterexample-nonlipschitz: actual endpoint gradients and the
source identity Hessian identify the even residual with the original odd correction. -/
theorem evenResidual_eq_oddCoefficient_of_endpoints (p : Parameters) (κ : ℝ)
    (hgradient : ∀ k, gradient (InterpolationSum.polarObjective p κ) (p.point k) = p.gradient k)
    (hhessian : ∀ k, fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) (p.point k) = 1)
    (j : ℕ) : evenResidual p κ j = InterpolationSum.polarCoefficient p (2 * j + 1) := by
  have heven : p.gradient (2 * j) = p.point (2 * j) := by
    rw [Parameters.gradient_def, Parameters.zeta_even, one_smul]
  rw [evenResidual_def, hgradient, hgradient, hessian_def, hhessian,
    one_apply_eq_self, evenStep_def, heven, InterpolationSum.polarCoefficient_apply]
  abel

/-- Helper for thm:main and eq:counterexample-nonlipschitz: the source initial
level set of the exact objective and the original, untruncated trajectory. -/
def initialLevelSet (p : Parameters) (κ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | InterpolationSum.polarObjective p κ x ≤ InterpolationSum.polarObjective p κ (p.point 0)}

/-- Helper for thm:main and eq:counterexample-nonlipschitz: membership in the
source initial level set. -/
theorem mem_initialLevelSet (p : Parameters) (κ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ initialLevelSet p κ ↔
      InterpolationSum.polarObjective p κ x ≤ InterpolationSum.polarObjective p κ (p.point 0) := by
  rfl

/-- Helper for thm:main and eq:counterexample-nonlipschitz: the exact endpoint
values and original radial monotonicity keep every actual iterate in the initial level set. -/
theorem points_mem_initialLevelSet_of_values (p : Parameters) (κ : ℝ)
    (hr : ∀ k, 0 ≤ p.radius k) (hanti : Antitone p.radius)
    (hvalue : ∀ k, InterpolationSum.polarObjective p κ (p.point k) = (1 / 2 : ℝ) * p.radius k ^ 2)
    (k : ℕ) : p.point k ∈ initialLevelSet p κ := by
  rw [mem_initialLevelSet, hvalue, hvalue]
  have hsquare := pow_le_pow_left₀ (hr k) (hanti (Nat.zero_le k)) 2
  linarith

/-- Helper for thm:main and eq:counterexample-nonlipschitz: convexity of the
actual objective makes its original initial level set convex. -/
theorem convex_initialLevelSet_of_convexOn (p : Parameters) (κ : ℝ)
    (hconvex : ConvexOn ℝ Set.univ (InterpolationSum.polarObjective p κ)) :
    Convex ℝ (initialLevelSet p κ) := by
  have h := hconvex.convex_le (InterpolationSum.polarObjective p κ (p.point 0))
  simpa only [Set.mem_univ, true_and, initialLevelSet] using h

/-- Helper for eq:counterexample-nonlipschitz: a uniform quartic error about the
source cubic coefficient gives quantitative cubic lower and upper bounds. -/
theorem cubic_bounds_of_quartic_error {a L E t : ℝ} (ht : 0 ≤ t)
    (hsmall : E * t ≤ L / 2) (herror : |a - L * t ^ 3| ≤ E * t ^ 4) :
    (L / 2) * t ^ 3 ≤ a ∧ a ≤ (3 * L / 2) * t ^ 3 := by
  have herr : E * t ^ 4 ≤ (L / 2) * t ^ 3 := by
    calc
      E * t ^ 4 = (E * t) * t ^ 3 := by ring
      _ ≤ (L / 2) * t ^ 3 := mul_le_mul_of_nonneg_right hsmall (pow_nonneg ht 3)
  have hbounds := abs_le.mp herror
  constructor
  · nlinarith
  · nlinarith

/-- Helper for eq:counterexample-nonlipschitz: the frozen actual point geometry
gives the original even-step quadratic bounds at the original cycle scale. -/
theorem evenStep_bounds_of_pointEstimates {p : Parameters} {lower upper separation : ℝ}
    (h : PointGeometry.PointEstimates p lower upper separation) (j : ℕ) :
    lower * p.scale j ^ 2 ≤ ‖evenStep p j‖ ∧ ‖evenStep p j‖ ≤ upper * p.scale j ^ 2 := by
  have hindex : 2 * j / 2 = j := by omega
  simpa only [evenStep_def, hindex] using h.step (2 * j)

/-- Helper for eq:counterexample-nonlipschitz: the normalized actual source
even residual used to test all exponents above one half. -/
def evenResidualRatio (p : Parameters) (κ β : ℝ) (j : ℕ) : ℝ :=
  ‖evenResidual p κ j‖ / ‖evenStep p j‖ ^ (1 + β)

/-- Helper for eq:counterexample-nonlipschitz: the actual even residual ratio formula. -/
theorem evenResidualRatio_def (p : Parameters) (κ β : ℝ) (j : ℕ) :
    evenResidualRatio p κ β j = ‖evenResidual p κ j‖ / ‖evenStep p j‖ ^ (1 + β) := by rfl

/-- Helper for eq:counterexample-nonlipschitz: proved cubic residual and quadratic
step bounds give both sides of the actual source ratio's power comparison. -/
theorem evenResidualRatio_bounds_of_cubic_bounds {p : Parameters}
    {κ c C lower upper separation β : ℝ}
    (hstart : 0 < p.startIndex) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : 0 < lower) (hupper : 0 < upper) (hβ : 0 ≤ 1 + β)
    (hpoints : PointGeometry.PointEstimates p lower upper separation)
    (hresidual : ∀ j, c * p.scale j ^ 3 ≤ ‖evenResidual p κ j‖ ∧
      ‖evenResidual p κ j‖ ≤ C * p.scale j ^ 3) (j : ℕ) :
    (c / upper ^ (1 + β)) * p.scale j ^ (1 - 2 * β) ≤ evenResidualRatio p κ β j ∧
      evenResidualRatio p κ β j ≤ (C / lower ^ (1 + β)) * p.scale j ^ (1 - 2 * β) := by
  have ht := ScaleTails.scale_pos p hstart j
  have hstep := evenStep_bounds_of_pointEstimates hpoints j
  have hd : 0 < ‖evenStep p j‖ := (mul_pos hlower (sq_pos_of_pos ht)).trans_le hstep.1
  rw [evenResidualRatio_def]
  exact ⟨cubicQuadraticRatio_lower ht hc hupper hβ hd (hresidual j).1 hstep.2,
    cubicQuadraticRatio_upper ht hC hlower hβ (hresidual j).2 hstep.1⟩

/-- Helper for eq:counterexample-nonlipschitz: a proved cubic lower bound for the
actual even residual forces its ratio to diverge for every exponent above one half. -/
theorem evenResidualRatio_tendsto_of_cubic_lower {p : Parameters} {κ c lower upper separation β : ℝ}
    (hstart : 0 < p.startIndex) (hc : 0 < c) (hlower : 0 < lower) (hupper : 0 < upper)
    (hβ : 1 / 2 < β) (hpoints : PointGeometry.PointEstimates p lower upper separation)
    (hresidual : ∀ j, c * p.scale j ^ 3 ≤ ‖evenResidual p κ j‖) :
    Tendsto (evenResidualRatio p κ β) atTop atTop := by
  have ht := ScaleTails.scale_pos p hstart
  have hstep := evenStep_bounds_of_pointEstimates hpoints
  have hpositive (j : ℕ) : 0 < ‖evenStep p j‖ :=
    (mul_pos hlower (sq_pos_of_pos (ht j))).trans_le (hstep j).1
  have hdiverge := cubicQuadraticRatio_tendsto_atTop ht (ScaleTails.scale_tendsto_zero p)
    hc hupper hβ hpositive hresidual (fun j ↦ (hstep j).2)
  rw [funext (evenResidualRatio_def p κ β)]
  exact hdiverge

/-- Helper for thm:main and eq:counterexample-nonlipschitz: the actual strong
convexity certificate supplies convexity of the original initial level set. -/
theorem convex_initialLevelSet_of_strongConvex {p : Parameters} {κ μ : ℝ}
    (hμ : 0 ≤ μ) (hstrong : StrongConvexOn Set.univ μ (InterpolationSum.polarObjective p κ)) :
    Convex ℝ (initialLevelSet p κ) := by
  exact convex_initialLevelSet_of_convexOn p κ
    (strongConvexOn_zero.mp (StrongConvexOn.mono hμ hstrong))

/-- Helper for eq:counterexample-nonlipschitz: the frozen exact source endpoint
data identify every actual even residual with its original odd interpolation correction. -/
theorem evenResidual_eq_oddCoefficient {p : Parameters} {κ ε C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ ε C H) (j : ℕ) :
    evenResidual p κ j = InterpolationSum.polarCoefficient p (2 * j + 1) := by
  exact evenResidual_eq_oddCoefficient_of_endpoints p κ
    (fun k ↦ (h.endpoints k).2.1) (fun k ↦ (h.endpoints k).2.2) j

/-- Helper for eq:counterexample-nonlipschitz: the actual cubic feedback estimate
has positive cubic bounds at every original index once the starting scale is small. -/
theorem oddCoefficient_cubic_bounds {p : Parameters} {A E : ℝ}
    (h : ActualObjective.CoefficientEstimates p A E) (hstart : 0 < p.startIndex)
    (hE : 0 ≤ E) (hsmall : E * p.scale 0 ≤ p.feedbackRate / 2) (j : ℕ) :
    (p.feedbackRate / 2) * p.scale j ^ 3 ≤ ‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ ∧
      ‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ ≤
        (3 * p.feedbackRate / 2) * p.scale j ^ 3 := by
  have ht := ScaleTails.scale_nonneg p j
  have hscale := ScaleTails.scale_antitone p hstart (Nat.zero_le j)
  have hsmallj := (mul_le_mul_of_nonneg_left hscale hE).trans hsmall
  exact cubic_bounds_of_quartic_error ht hsmallj (h.odd_error j)

/-- Helper for eq:counterexample-nonlipschitz: actual source endpoint identities
and the proved cubic feedback error give cubic bounds for the actual even residual. -/
theorem evenResidual_cubic_bounds {p : Parameters} {κ ε C H A E : ℝ}
    (hobjective : ActualObjective.ObjectiveEstimates p κ ε C H)
    (hcoefficients : ActualObjective.CoefficientEstimates p A E) (hstart : 0 < p.startIndex)
    (hE : 0 ≤ E) (hsmall : E * p.scale 0 ≤ p.feedbackRate / 2) (j : ℕ) :
    (p.feedbackRate / 2) * p.scale j ^ 3 ≤ ‖evenResidual p κ j‖ ∧
      ‖evenResidual p κ j‖ ≤ (3 * p.feedbackRate / 2) * p.scale j ^ 3 := by
  rw [evenResidual_eq_oddCoefficient hobjective]
  exact oddCoefficient_cubic_bounds hcoefficients hstart hE hsmall j

/-- Helper for thm:main and eq:counterexample-nonlipschitz: actual source endpoint
values and decreasing radii give initial-level membership for the entire original orbit. -/
theorem points_mem_initialLevelSet {p : Parameters} {κ ε C H : ℝ} {D : Fin 2 → ℝ}
    {K c B : ℝ} (hobjective : ActualObjective.ObjectiveEstimates p κ ε C H)
    (hradii : RadiusProducts.RadiusEstimates p D K c B) (k : ℕ) :
    p.point k ∈ initialLevelSet p κ := by
  exact points_mem_initialLevelSet_of_values p κ
    (fun k ↦ zero_le_one.trans (hradii.above_one k).le) hradii.strictAnti.antitone
    (fun k ↦ (hobjective.endpoints k).1) k

/-- Helper for eq:counterexample-nonlipschitz and thm:main: a proved cubic
actual residual excludes a Hölder Hessian on every convex set containing the original points. -/
theorem not_holderHessianOn_of_evenCubicResidual {p : Parameters}
    {κ c lower upper separation β : ℝ}
    (hf : ContDiff ℝ 2 (InterpolationSum.polarObjective p κ))
    (hstart : 0 < p.startIndex) (hc : 0 < c) (hlower : 0 < lower) (hupper : 0 < upper)
    (hβ : 1 / 2 < β) (hpoints : PointGeometry.PointEstimates p lower upper separation)
    (hresidual : ∀ j, c * p.scale j ^ 3 ≤ ‖evenResidual p κ j‖)
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : Convex ℝ S) (hmem : ∀ k, p.point k ∈ S) :
    ¬ ∃ C ≥ 0, ∀ x ∈ S, ∀ y ∈ S,
      ‖hessian (InterpolationSum.polarObjective p κ) x -
        hessian (InterpolationSum.polarObjective p κ) y‖ ≤ C * ‖x - y‖ ^ β := by
  have ht := ScaleTails.scale_pos p hstart
  have hstep := evenStep_bounds_of_pointEstimates hpoints
  have hpositive (j : ℕ) : 0 < ‖p.point (2 * j + 1) - p.point (2 * j)‖ := by
    simpa only [evenStep_def] using
      (mul_pos hlower (sq_pos_of_pos (ht j))).trans_le (hstep j).1
  have hdiverge := evenResidualRatio_tendsto_of_cubic_lower hstart hc hlower hupper hβ
    hpoints hresidual
  rw [funext (evenResidualRatio_def p κ β)] at hdiverge
  simp only [evenResidual_def, evenStep_def] at hdiverge
  have hβnonneg : 0 ≤ β := by linarith
  exact not_holderHessianOn_of_remainderRatio_tendsto hf hS
    (fun j ↦ hmem (2 * j)) (fun j ↦ hmem (2 * j + 1)) hpositive hβnonneg hdiverge

/-- Helper for thm:main and eq:counterexample-nonlipschitz: a small interface
for the source sharpness conclusions at the exact actual objective and original trajectory. -/
structure SharpnessEstimates (p : Parameters) (κ c C lower upper : ℝ) : Prop where
  /-- Helper for eq:counterexample-nonlipschitz: the exact original odd correction identity. -/
  residual : ∀ j, evenResidual p κ j = InterpolationSum.polarCoefficient p (2 * j + 1)
  /-- Helper for eq:counterexample-nonlipschitz: positive cubic residual bounds. -/
  residual_bounds : ∀ j, c * p.scale j ^ 3 ≤ ‖evenResidual p κ j‖ ∧
    ‖evenResidual p κ j‖ ≤ C * p.scale j ^ 3
  /-- Helper for eq:counterexample-nonlipschitz: the same original steps have quadratic size. -/
  step_bounds : ∀ j, lower * p.scale j ^ 2 ≤ ‖evenStep p j‖ ∧
    ‖evenStep p j‖ ≤ upper * p.scale j ^ 2
  /-- Helper for eq:counterexample-nonlipschitz: both sides of the source residual power law. -/
  ratio_bounds : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1, ∀ j,
    (c / upper ^ (1 + β)) * p.scale j ^ (1 - 2 * β) ≤ evenResidualRatio p κ β j ∧
      evenResidualRatio p κ β j ≤ (C / lower ^ (1 + β)) * p.scale j ^ (1 - 2 * β)
  /-- Helper for eq:counterexample-nonlipschitz: all source residual ratios diverge. -/
  ratio_diverges : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
    Tendsto (evenResidualRatio p κ β) atTop atTop
  /-- Helper for thm:main: the original initial level set is convex. -/
  level_convex : Convex ℝ (initialLevelSet p κ)
  /-- Helper for thm:main: every original point belongs to the initial level set. -/
  level_contains : ∀ k, p.point k ∈ initialLevelSet p κ
  /-- Helper for thm:main: sharpness on every convex set containing the actual orbit. -/
  no_holder_on : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
    ∀ S : Set (EuclideanSpace ℝ (Fin 2)), Convex ℝ S → (∀ k, p.point k ∈ S) →
      ¬ ∃ L ≥ 0, ∀ x ∈ S, ∀ y ∈ S,
        ‖hessian (InterpolationSum.polarObjective p κ) x -
          hessian (InterpolationSum.polarObjective p κ) y‖ ≤ L * ‖x - y‖ ^ β
  /-- Helper for thm:main: the actual initial-level Hessian admits no larger source exponent. -/
  no_holder_initial : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
    ¬ ∃ L ≥ 0, ∀ x ∈ initialLevelSet p κ, ∀ y ∈ initialLevelSet p κ,
      ‖hessian (InterpolationSum.polarObjective p κ) x -
        hessian (InterpolationSum.polarObjective p κ) y‖ ≤ L * ‖x - y‖ ^ β

/-- Helper for thm:main and eq:counterexample-nonlipschitz: actual objective,
coefficient, and geometry certificates yield the source sharpness contradiction. -/
theorem sharpnessEstimatesOfActualData {p : Parameters} {κ ε C H A E lower upper separation : ℝ}
    {D : Fin 2 → ℝ} {K c B : ℝ}
    (hobjective : ActualObjective.ObjectiveEstimates p κ ε C H)
    (hcoefficients : ActualObjective.CoefficientEstimates p A E)
    (hradii : RadiusProducts.RadiusEstimates p D K c B)
    (hpoints : PointGeometry.PointEstimates p lower upper separation)
    (hstart : 0 < p.startIndex) (hfeedback : 0 < p.feedbackRate) (hE : 0 ≤ E)
    (hlower : 0 < lower) (hupper : 0 < upper) (hε : ε < 1)
    (hsmall : E * p.scale 0 ≤ p.feedbackRate / 2) :
    SharpnessEstimates p κ (p.feedbackRate / 2) (3 * p.feedbackRate / 2) lower upper := by
  have hresidual := evenResidual_cubic_bounds hobjective hcoefficients hstart hE hsmall
  have hlow : 0 < p.feedbackRate / 2 := half_pos hfeedback
  have hhigh : 0 ≤ 3 * p.feedbackRate / 2 := by positivity
  have hlevel := convex_initialLevelSet_of_strongConvex (sub_pos.mpr hε).le hobjective.strongConvex
  have hmem := points_mem_initialLevelSet hobjective hradii
  have hnot : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
      ∀ S : Set (EuclideanSpace ℝ (Fin 2)), Convex ℝ S → (∀ k, p.point k ∈ S) →
        ¬ ∃ L ≥ 0, ∀ x ∈ S, ∀ y ∈ S,
          ‖hessian (InterpolationSum.polarObjective p κ) x -
            hessian (InterpolationSum.polarObjective p κ) y‖ ≤ L * ‖x - y‖ ^ β := by
    intro β hβ S hS hcontains
    exact not_holderHessianOn_of_evenCubicResidual hobjective.objective_contDiff hstart hlow
      hlower hupper hβ.1 hpoints (fun j ↦ (hresidual j).1) S hS hcontains
  refine ⟨evenResidual_eq_oddCoefficient hobjective, hresidual,
    evenStep_bounds_of_pointEstimates hpoints, ?_, ?_, hlevel, hmem, hnot, ?_⟩
  · intro β hβ j
    have hexponent : 0 ≤ 1 + β := by linarith [hβ.1]
    exact evenResidualRatio_bounds_of_cubic_bounds hstart hlow.le hhigh hlower hupper
      hexponent hpoints hresidual j
  · intro β hβ
    exact evenResidualRatio_tendsto_of_cubic_lower hstart hlow hlower hupper hβ.1 hpoints
      (fun j ↦ (hresidual j).1)
  · intro β hβ
    exact hnot β hβ (initialLevelSet p κ) hlevel hmem

/-- Helper for eq:counterexample-nonlipschitz: the source feedback coefficient
is independent of every natural starting index in the actual parameter family. -/
theorem feedbackRate_of (j₀ : ℕ) (νStar : ℝ) :
    (Parameters.of j₀ νStar).feedbackRate = 4 * baseAngle / (9 * νStar) := by
  rw [Parameters.feedbackRate_def, Parameters.of_cycleParameter]

/-- eq:counterexample-nonlipschitz and thm:main (sharp exponent): the exact source
objective has cubic even secant residuals and quadratic steps, so its residual ratio
has order `t^(1−2β)` and diverges for every `β∈(1/2,1]`. The Hessian is not β-Hölder
on its original convex initial level set. All support and quantitative constants are
chosen before the accuracy and every subsequent natural starting index. -/
theorem polarHolderSharpness :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ κ > 0, ∃ C > 0, ∃ H > 0, ∃ cResidual > 0, ∃ CResidual > 0,
        ∃ lower > 0, ∃ upper > 0, ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
            ActualObjective.ObjectiveEstimates (Parameters.of j₀ νStar) κ ε C H ∧
              SharpnessEstimates (Parameters.of j₀ νStar) κ cResidual CResidual lower upper := by
  obtain ⟨η₀, hη₀, hobjectives⟩ := ActualObjective.polarObjectiveEstimates
  obtain ⟨η₁, hη₁, hcoefficients⟩ := ActualObjective.actualCoefficientEstimates
  obtain ⟨η₂, hη₂, hgeometry⟩ := PointGeometry.polarPointGeometry
  refine ⟨min η₀ (min η₁ η₂), lt_min hη₀ (lt_min hη₁ hη₂), ?_⟩
  intro νStar hnear
  have hnear₀ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₀) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnear₁ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₁) := by
    have hle := (min_le_right η₀ (min η₁ η₂)).trans (min_le_left η₁ η₂)
    exact ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl hle)⟩
  have hnear₂ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₂) := by
    have hle := (min_le_right η₀ (min η₁ η₂)).trans (min_le_right η₁ η₂)
    exact ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl hle)⟩
  obtain ⟨κ, hκ, C, hC, H, hH, haccuracy⟩ := hobjectives νStar hnear₀
  obtain ⟨_, A, _, E, hE, K₁, _, c₁, _, B₁, _, J₁, hJ₁, hdata⟩ := hcoefficients νStar hnear₁
  obtain ⟨_, K₂, _, c₂, _, B₂, _, lower, hlower, upper, hupper, separation, _, J₂, _, hpoints⟩ :=
    hgeometry νStar hnear₂
  let L := 4 * baseAngle / (9 * νStar)
  have ha := AngularGeometry.baseAngle_pos
  have hν : 0 < νStar := ha.trans hnear.1
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hcutoff : 0 < L / (2 * E) := by positivity
  obtain ⟨J₃, _, hscale⟩ := Continuation.existsStartThreshold _ hcutoff
  have hCResidual : 0 < 3 * L / 2 := by positivity
  refine ⟨κ, hκ, C, hC, H, hH, L / 2, half_pos hL, 3 * L / 2, hCResidual,
    lower, hlower, upper, hupper, ?_⟩
  intro ε hε hεone
  obtain ⟨J₀, hJ₀, hobjective⟩ := haccuracy ε hε hεone
  refine ⟨max J₀ (max J₁ (max J₂ J₃)), hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  have hj₀₀ := (le_max_left J₀ (max J₁ (max J₂ J₃))).trans hj₀
  have hj₀₁ := (le_max_left J₁ (max J₂ J₃)).trans
    ((le_max_right J₀ (max J₁ (max J₂ J₃))).trans hj₀)
  have hj₀₂ := (le_max_left J₂ J₃).trans
    ((le_max_right J₁ (max J₂ J₃)).trans
      ((le_max_right J₀ (max J₁ (max J₂ J₃))).trans hj₀))
  have hj₀₃ := (le_max_right J₂ J₃).trans
    ((le_max_right J₁ (max J₂ J₃)).trans
      ((le_max_right J₀ (max J₁ (max J₂ J₃))).trans hj₀))
  let p := Parameters.of j₀ νStar
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₁.trans_le hj₀₁
  have hfeedback : p.feedbackRate = L := feedbackRate_of j₀ νStar
  have hzero : p.scale 0 < L / (2 * E) := hscale νStar j₀ hj₀₃
  have hdenominator : 0 < 2 * E := by positivity
  have hsmall : E * p.scale 0 ≤ p.feedbackRate / 2 := by
    rw [hfeedback]
    nlinarith [(lt_div_iff₀ hdenominator).mp hzero]
  have hactualObjective := hobjective j₀ hj₀₀
  have hactualCoefficient := (hdata j₀ hj₀₁).2.1
  obtain ⟨hradius, hpoint⟩ := hpoints j₀ hj₀₂
  have hsharp := sharpnessEstimatesOfActualData hactualObjective hactualCoefficient hradius
    hpoint hstart (hdata j₀ hj₀₁).2.2 hE.le hlower hupper hεone hsmall
  rw [hfeedback] at hsharp
  exact ⟨hactualObjective, hsharp⟩

end DFP.Polar.HolderSharpness
