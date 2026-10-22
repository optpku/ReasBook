/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.Continuation
public import ReasLib.Optimization.DFP.Polar.PointGeometry
public import ReasLib.Optimization.DFP.Polar.ActualObjective

public section

open Filter DFP.Polar
open scoped Topology InnerProduct BigOperators ContDiff

namespace DFPWolfe.V21

/-- Helper for lem:polar-continuation: the fast error is exactly the source
displacement from `(A w(ν(A)), 1+A w(ν(A))²)` at the state's own first coordinate. -/
theorem polarFastErrorFormula (x : ℝ × ℝ × ℝ) :
    FastContraction.fastError x =
      ![x.2.1 - x.1 * cycleW (TwoCycle.inverseParameter x.1),
        x.2.2 - (1 + x.1 * cycleW (TwoCycle.inverseParameter x.1) ^ 2)] := by
  rw [FastContraction.fastError_def, FastContraction.fastCoordinates_apply,
    FastContraction.fastCoordinates_apply, TwoCycle.evenState_apply]
  ext i
  fin_cases i
  all_goals rfl

/-- lem:polar-continuation. For every fixed cycle parameter sufficiently close
to `baseAngle` from above, choose the fast width `N`, then the slow width `M`,
then a positive natural threshold `J`. Every freshly initialized original
trajectory with `j₀≥J` obeys the slow `O(t)` and fast `O(t³)` tube bounds at
every cycle. The fast error is the original curve displacement displayed in
`polarFastErrorFormula`; both its fixed source norm and ordinary norm are bounded.
The original matrix recurrence holds at every index, and every raw matrix is
positive definite with positive off-diagonal entry, secant scalar `σ` and factor `W`.
All widths and thresholds precede every later choice of `j₀` (main.tex:649–739). -/
theorem polarContinuation :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ N > 0, ∃ M > 0,
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
          let p := Parameters.of j₀ νStar
          (∀ j : ℕ,
            |(p.normalizedEvenState j).1 - p.kStar| ≤ M * p.scale j ∧
            FastContraction.fixedNorm (FastContraction.fastError (p.normalizedEvenState j)) ≤
              N * p.scale j ^ 3 ∧
            ‖FastContraction.fastError (p.normalizedEvenState j)‖ ≤
              (‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1) *
                N * p.scale j ^ 3 ∧
            (p.normalizedEvenState j).1 ∈ TwoCycle.normalizationSet ∧
              0 < (p.normalizedEvenState j).1) ∧
          (∀ k, p.matrix (k + 1) = matrixStep (p.matrix k) (p.angleIncrement k)
            (p.zeta k) (p.zeta (k + 1))) ∧
          ∀ k, (p.matrix k).PosDef ∧ 0 < p.matrix k 0 1 ∧
            0 < p.sigma k ∧ 0 < p.radiusRatio k := by
  obtain ⟨η, hη, hcontinuation⟩ := Continuation.polarContinuation
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, N, hN, M, hM, J, hJ, hall⟩ := hcontinuation νStar hnear
  refine ⟨hparameter, N, hN, M, hM, J, hJ, ?_⟩
  intro j₀ hj₀
  obtain ⟨htube, hpositive⟩ := hall j₀ hj₀
  refine ⟨?_, Parameters.matrix_succ _, hpositive⟩
  intro j
  have hfast := (htube j).2.1
  have hnorm := FastContraction.norm_le_basisOperator_mul_fixedNorm
    (FastContraction.fastError ((Parameters.of j₀ νStar).normalizedEvenState j))
  have hnonnegative := FastContraction.fixedNorm_nonneg
    (FastContraction.fastError ((Parameters.of j₀ νStar).normalizedEvenState j))
  have hconstant : 0 ≤ ‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1 := by
    positivity
  have hordinary : ‖FastContraction.fastError
      ((Parameters.of j₀ νStar).normalizedEvenState j)‖ ≤
      (‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1) *
        N * (Parameters.of j₀ νStar).scale j ^ 3 := by
    calc
      _ ≤ (‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1) *
          FastContraction.fixedNorm (FastContraction.fastError
            ((Parameters.of j₀ νStar).normalizedEvenState j)) := by
        nlinarith
      _ ≤ (‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1) *
          (N * (Parameters.of j₀ νStar).scale j ^ 3) :=
        mul_le_mul_of_nonneg_left hfast hconstant
      _ = _ := by ring
  exact ⟨(htube j).1, hfast, hordinary, (htube j).2.2⟩

/-- Helper for lem:polar-geometry: the radial expansion uses precisely the source
coefficients `D₀=2aQ_E-2a²` and `D₁=aQ_O-a²/2`, with the original cycle slopes. -/
theorem polarRadiusCoefficients (νStar : ℝ) :
    RadiusExpansions.radiusCoefficient νStar 0 =
      2 * baseAngle * (cycleZ νStar + 2 * baseAngle) - 2 * baseAngle ^ 2 ∧
    RadiusExpansions.radiusCoefficient νStar 1 =
      baseAngle * (cycleW νStar + baseAngle) - baseAngle ^ 2 / 2 := by
  constructor
  · rw [RadiusExpansions.radiusCoefficient_even, RadiusExpansions.referenceSlope_even]
  · rw [RadiusExpansions.radiusCoefficient_odd, RadiusExpansions.referenceSlope_odd]

/-- lem:polar-geometry. The original points have radial expansion
`rₖ-1=3(D₀+D₁)t+O(t²)`, radial decrements comparable to `t⁴`, and successive
distances comparable to `t²`. Here `D=radiusCoefficient νStar` is the original
coefficient from the even and odd factor expansions. The radii strictly decrease
to one and satisfy the exact quotient recurrence. The full accumulation set is
the unit circle, and every distinct pair has the source maximum-scale separation.
All positive constants are fixed before every `j₀≥J` (main.tex:761–815). -/
theorem polarGeometry :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ K > 0, ∃ c > 0, ∃ B > 0,
        ∃ lower > 0, ∃ upper > 0, ∃ separation > 0, ∃ J : ℕ, 0 < J ∧
          ∀ j₀ ≥ J,
            let p := Parameters.of j₀ νStar
            StrictAnti p.radius ∧ Tendsto p.radius atTop (𝓝 1) ∧
            (∀ k, 1 < p.radius k ∧ 1 < p.radiusRatio k ∧
              p.radius (k + 1) = p.radius k / p.radiusRatio k) ∧
            (∀ k,
              |p.radius k - 1 - 3 * (RadiusExpansions.radiusCoefficient νStar 0 +
                RadiusExpansions.radiusCoefficient νStar 1) * p.scale (k / 2)| ≤
                  K * p.scale (k / 2) ^ 2 ∧
              (c * p.scale (k / 2) ^ 4 ≤ p.radius k - p.radius (k + 1) ∧
                p.radius k - p.radius (k + 1) ≤ B * p.scale (k / 2) ^ 4) ∧
              lower * p.scale (k / 2) ^ 2 ≤ ‖p.point (k + 1) - p.point k‖ ∧
                ‖p.point (k + 1) - p.point k‖ ≤ upper * p.scale (k / 2) ^ 2) ∧
            (∀ k m, ‖p.point m - p.point k‖ ^ 2 = (p.radius m - p.radius k) ^ 2 +
              4 * p.radius m * p.radius k * Real.sin ((p.angle m - p.angle k) / 2) ^ 2) ∧
            {x | MapClusterPt x atTop p.point} = Metric.sphere 0 1 ∧
            ∀ k m, k ≠ m → separation * max (p.scale (k / 2) ^ 2)
              (p.scale (m / 2) ^ 2) ≤ ‖p.point m - p.point k‖ := by
  obtain ⟨η, hη, hgeometry⟩ := PointGeometry.polarPointGeometry
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, K, hK, c, hc, B, hB, lower, hlower, upper, hupper,
    separation, hseparation, J, hJ, hall⟩ := hgeometry νStar hnear
  refine ⟨hparameter, K, hK, c, hc, B, hB, lower, hlower, upper, hupper,
    separation, hseparation, J, hJ, ?_⟩
  intro j₀ hj₀
  obtain ⟨hradius, hpoints⟩ := hall j₀ hj₀
  have hcluster : {x | MapClusterPt x atTop (Parameters.of j₀ νStar).point} =
      Metric.sphere 0 1 := by
    ext x
    simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using hpoints.cluster x
  refine ⟨hradius.strictAnti, hradius.tendsto_one, ?_, ?_,
    hpoints.chord, hcluster, hpoints.separate⟩
  · intro k
    exact ⟨hradius.above_one k, hradius.factor_above_one k, hradius.recurrence k⟩
  · intro k
    exact ⟨hradius.expansion k, hradius.drop k, hpoints.step k⟩

/-- Helper for lem:polar-interpolation: the unchanged exponentially flat η and
its exact source quotient χ are smooth, lie between zero and one, equal one on
the inner third-ball, and vanish on the full closed exterior of the unit ball. -/
theorem polarCutoffFormula :
    (∀ t : ℝ, ExplicitCutoff.eta t = if 0 < t then Real.exp (-1 / t) else 0) ∧
    ContDiff ℝ ∞ (ExplicitCutoff.chi (E := EuclideanSpace ℝ (Fin 2))) ∧
    ∀ z : EuclideanSpace ℝ (Fin 2),
      ExplicitCutoff.chi z = ExplicitCutoff.eta (1 - ‖z‖ ^ 2) /
        (ExplicitCutoff.eta (1 - ‖z‖ ^ 2) + ExplicitCutoff.eta (‖z‖ ^ 2 - 1 / 9)) ∧
      0 ≤ ExplicitCutoff.chi z ∧ ExplicitCutoff.chi z ≤ 1 ∧
      (‖z‖ ≤ 1 / 3 → ExplicitCutoff.chi z = 1) ∧
      (1 ≤ ‖z‖ → ExplicitCutoff.chi z = 0) := by
  refine ⟨ExplicitCutoff.eta_apply, ExplicitCutoff.contDiff_chi, ?_⟩
  intro z
  exact ⟨ExplicitCutoff.chi_apply z, ExplicitCutoff.chi_nonneg z,
    ExplicitCutoff.chi_le_one z, ExplicitCutoff.chi_eq_one, ExplicitCutoff.chi_eq_zero⟩

/-- Helper for lem:polar-interpolation: one constant depending only on the original
cutoff controls the global half-Hölder Hessian of each actual smooth correction,
with exactly the source factor `‖aₖ‖ ρₖ^(-3/2)`. -/
theorem polarBumpRegularity :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (p : Parameters) (κ : ℝ),
      0 < p.startIndex → 0 < κ → ∀ k,
        ContDiff ℝ ∞ (InterpolationSum.polarBump p κ k) ∧
        ∀ x y, ‖hessian (InterpolationSum.polarBump p κ k) x -
          hessian (InterpolationSum.polarBump p κ k) y‖ ≤
            Cχ * ‖InterpolationSum.polarCoefficient p k‖ *
              (InterpolationSum.polarSupportRadius p κ k) ^ (-3 / 2 : ℝ) *
                ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cχ, hCχ, hholder⟩ := ActualObjective.exists_polarBump_holder
  refine ⟨Cχ, hCχ, ?_⟩
  intro p κ hstart hκ k
  refine ⟨ActualObjective.contDiff_polarBump p κ k, ?_⟩
  intro x y
  rw [hessian_def, hessian_def, ActualObjective.norm_hessian_sub_eq_secondFDeriv_sub]
  exact hholder p κ hstart hκ k x y

/-- lem:polar-interpolation. Fix the original cutoff's constant `Cχ`, then a
sufficiently small right parameter neighborhood. For each fixed `νStar`, choose
the support coefficient `κ` and uniform constants `C,H` before the accuracy and
every later initialized `j₀≥J`. Each smooth original bump has the source scaled
half-Hölder Hessian bound. The accepted `ObjectiveEstimates` records the disjoint
open support balls and their closed support bounds, the exact infinite correction
sum, C² regularity across the circle, vanishing two-jet on the circle and exact
center two-jets. It also records the uniform `Ct₀` Hessian bound, global half-Hölder
modulus `H`, and the actual objective's values, original gradients and identity
Hessians at every endpoint. The objective is quadratic on the closed unit disk
and uniformly convex. `polarInterpolationConclusions` exposes these fields directly.
All objects use the original `eta`, `chi` and `ρₖ=κt²` (main.tex:910–1040). -/
theorem polarInterpolation :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∃ η > 0,
      ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
        ∃ κ > 0, ∃ C > 0, ∃ H > 0, ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
            let p := Parameters.of j₀ νStar
            ActualObjective.ObjectiveEstimates p κ ε C H ∧
            ∀ k, ContDiff ℝ ∞ (InterpolationSum.polarBump p κ k) ∧
              ∀ x y, ‖hessian (InterpolationSum.polarBump p κ k) x -
                hessian (InterpolationSum.polarBump p κ k) y‖ ≤
                  Cχ * ‖InterpolationSum.polarCoefficient p k‖ *
                    (InterpolationSum.polarSupportRadius p κ k) ^ (-3 / 2 : ℝ) *
                      ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cχ, hCχ, hbumps⟩ := polarBumpRegularity
  obtain ⟨η, hη, hobjective⟩ := ActualObjective.polarObjectiveEstimates
  refine ⟨Cχ, hCχ, η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨κ, hκ, C, hC, H, hH, haccuracy⟩ := hobjective νStar hnear
  refine ⟨κ, hκ, C, hC, H, hH, ?_⟩
  intro ε hε hεone
  obtain ⟨J, hJ, hall⟩ := haccuracy ε hε hεone
  refine ⟨J, hJ, ?_⟩
  intro j₀ hj₀
  have hstart : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hJ.trans_le hj₀
  exact ⟨hall j₀ hj₀, hbumps _ κ hstart hκ⟩

/-- Helper for lem:polar-interpolation: direct mathematical conclusions of the
proved actual objective certificate. The original cutoff formula, exact support
radii, disjoint function supports, closed support exterior, true infinite sum,
C² regularity, vanishing circle and center two-jets, exact endpoint Hessian `I`,
uniform `Ct₀` Hessian bound and both global half-Hölder bounds are explicit.
The certificate is supplied for every later `j₀` by `polarInterpolation`, rather
than assumed as a geometric or regularity premise of that source theorem. -/
theorem polarInterpolationConclusions {p : Parameters} {κ ε C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ ε C H) :
    Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (p.point k)
      (InterpolationSum.polarSupportRadius p κ k)) ∧
    Set.univ.PairwiseDisjoint (fun k ↦ Function.support (InterpolationSum.polarBump p κ k)) ∧
    (∀ k, 0 < InterpolationSum.polarSupportRadius p κ k ∧
      InterpolationSum.polarSupportRadius p κ k = κ * p.scale (k / 2) ^ 2 ∧
      tsupport (InterpolationSum.polarBump p κ k) ⊆
        Metric.closedBall (p.point k) (InterpolationSum.polarSupportRadius p κ k) ∧
      ∀ x ∈ Metric.closedBall (p.point k) (InterpolationSum.polarSupportRadius p κ k),
        1 < ‖x‖) ∧
    (∀ k x, InterpolationSum.polarBump p κ k x =
      ExplicitCutoff.chi ((κ * p.scale (k / 2) ^ 2)⁻¹ • (x - p.point k)) *
        inner ℝ (p.gradient k - p.point k) (x - p.point k)) ∧
    (∀ x, InterpolationSum.polarPerturbation p κ x = ∑' k, InterpolationSum.polarBump p κ k x) ∧
    (∀ x, InterpolationSum.polarObjective p κ x =
      (1 / 2 : ℝ) * ‖x‖ ^ 2 + InterpolationSum.polarPerturbation p κ x) ∧
    ContDiff ℝ 2 (InterpolationSum.polarPerturbation p κ) ∧
    ContDiff ℝ 2 (InterpolationSum.polarObjective p κ) ∧
    (∀ x, ‖x‖ = 1 → InterpolationSum.polarPerturbation p κ x = 0 ∧
      gradient (InterpolationSum.polarPerturbation p κ) x = 0 ∧
      hessian (InterpolationSum.polarPerturbation p κ) x = 0) ∧
    (∀ k, InterpolationSum.polarPerturbation p κ (p.point k) = 0 ∧
      gradient (InterpolationSum.polarPerturbation p κ) (p.point k) = p.gradient k - p.point k ∧
      hessian (InterpolationSum.polarPerturbation p κ) (p.point k) = 0) ∧
    (∀ k, InterpolationSum.polarObjective p κ (p.point k) = (1 / 2 : ℝ) * p.radius k ^ 2 ∧
      gradient (InterpolationSum.polarObjective p κ) (p.point k) = p.gradient k ∧
      hessian (InterpolationSum.polarObjective p κ) (p.point k) = 1) ∧
    (∀ x, ‖hessian (InterpolationSum.polarPerturbation p κ) x‖ ≤ C * p.scale 0) ∧
    (∀ x y, ‖hessian (InterpolationSum.polarPerturbation p κ) x -
      hessian (InterpolationSum.polarPerturbation p κ) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) ∧
    (∀ x y, ‖hessian (InterpolationSum.polarObjective p κ) x -
      hessian (InterpolationSum.polarObjective p κ) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) ∧
    (∀ x, ‖x‖ ≤ 1 → InterpolationSum.polarObjective p κ x = (1 / 2 : ℝ) * ‖x‖ ^ 2) ∧
    HasHessianBounds (1 - ε) (1 + ε) (InterpolationSum.polarObjective p κ) ∧
    StrongConvexOn Set.univ (1 - ε) (InterpolationSum.polarObjective p κ) ∧
    InterpolationSum.polarObjective p κ 0 = 0 ∧
    ∀ x, (∀ y, InterpolationSum.polarObjective p κ x ≤
      InterpolationSum.polarObjective p κ y) ↔ x = 0 := by
  have hopen : ∀ k, Function.support (InterpolationSum.polarBump p κ k) ⊆
      Metric.ball (p.point k) (InterpolationSum.polarSupportRadius p κ k) := by
    intro k
    rw [ActualObjective.polarBump_eq_bump]
    exact InterpolationSum.support_bump_subset_ball h.geometry k
  have hsupport := h.geometry.disjoint_open.mono hopen
  refine ⟨h.geometry.disjoint_open, hsupport, ?_, InterpolationSum.polarBump_apply p κ,
    h.sum_formula, InterpolationSum.polarObjective_apply p κ, h.perturbation_contDiff,
    h.objective_contDiff, ?_, ?_, ?_, ?_, ?_, ?_, h.disk, h.hessian_bounds,
    h.strongConvex, h.origin, h.unique_minimizer⟩
  · intro k
    refine ⟨h.geometry.radius_pos k, InterpolationSum.polarSupportRadius_apply p κ k,
      h.closed_support k, ?_⟩
    intro x hx
    have hmargin := h.geometry.closedBall_norm_margin k hx
    have hradius := h.geometry.radius_pos k
    linarith
  · intro x hx
    simpa only [hessian_def] using h.sphere_jets x hx
  · intro k
    simpa only [hessian_def, InterpolationSum.polarCoefficient_apply] using h.center_jets k
  · intro k
    simpa only [hessian_def] using h.endpoints k
  · intro x
    rw [hessian_def, norm_fderiv_gradient_eq_norm_fderiv_fderiv]
    exact h.perturbation_bound x
  · intro x y
    rw [hessian_def, hessian_def, ActualObjective.norm_hessian_sub_eq_secondFDeriv_sub]
    exact h.perturbation_holder x y
  · intro x y
    simpa only [hessian_def] using h.hessian_holder x y

end DFPWolfe.V21
