module

public import ReasLib.Optimization.DFP.Polar.RestoringDrift
public import ReasLib.Optimization.DFP.Polar.FastContraction
public import ReasLib.Optimization.DFP.Polar.Normalized.Recurrence

/-!
# Barriers for the polar continuation tube

These lemmas prove the source's tube barrier and the order of its constant
choices, conditional on explicit fast and slow update estimates. They use the
original analytic scale map `Normalized.nextScale`. Instantiating the update
estimates and proving feasibility of the polar matrix trajectory are separate
integration obligations.
-/

public section

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DFP.Polar.Normalized

/-- Helper for lem:polar-continuation: the exponential cubic-root branch is
strictly positive at every real scale. -/
theorem unitRoot_pos (t : ℝ) : 0 < unitRoot t := by
  rw [unitRoot_def]
  exact Real.exp_pos _

/-- Helper for lem:polar-continuation: the original next scale is positive
at every positive input scale. -/
theorem nextScale_pos (t : ℝ) (ht : 0 < t) : 0 < nextScale t := by
  rw [nextScale_def]
  exact div_pos ht (unitRoot_pos t)

/-- Helper for lem:polar-continuation: the cubic root is at least one at
nonnegative scales. -/
theorem one_le_unitRoot (t : ℝ) (ht : 0 ≤ t) : 1 ≤ unitRoot t := by
  have hbase : 0 < 1 + t ^ 3 := by positivity
  have hcube := unitRoot_cube t hbase
  have hroot := unitRoot_pos t
  by_contra h
  have hlt : unitRoot t < 1 := lt_of_not_ge h
  have hfactor : 0 < (1 - unitRoot t) * (unitRoot t ^ 2 + unitRoot t + 1) := by
    positivity
  have hidentity :
      (1 - unitRoot t) * (unitRoot t ^ 2 + unitRoot t + 1) = 1 - unitRoot t ^ 3 := by
    ring
  rw [hidentity] at hfactor
  nlinarith [pow_nonneg ht 3]

/-- Helper for lem:polar-continuation: the prescribed next scale never exceeds
its nonnegative input scale. -/
theorem nextScale_le_self (t : ℝ) (ht : 0 ≤ t) : nextScale t ≤ t := by
  rw [nextScale_def]
  exact div_le_self ht (one_le_unitRoot t ht)

/-- Helper for lem:polar-continuation: the exact next scale is bounded below
by `t - t ^ 4 / 3` at every nonnegative scale. -/
theorem nextScale_lower_quartic (t : ℝ) (ht : 0 ≤ t) :
    t - t ^ 4 / 3 ≤ nextScale t := by
  have hbase : 0 < 1 + t ^ 3 := by positivity
  have hcubic : t ^ 3 = unitRoot t ^ 3 - 1 := by
    rw [unitRoot_cube t hbase]
    ring
  have hfour : t ^ 4 = t * t ^ 3 := by ring
  have hidentity :
      t - (t - t ^ 4 / 3) * unitRoot t =
        t * (unitRoot t - 1) ^ 2 * (unitRoot t ^ 2 + 2 * unitRoot t + 3) / 3 := by
    rw [hfour, hcubic]
    ring
  have hnonnegative :
      0 ≤ t * (unitRoot t - 1) ^ 2 * (unitRoot t ^ 2 + 2 * unitRoot t + 3) / 3 := by
    have hroot := unitRoot_pos t
    positivity
  rw [nextScale_def]
  apply (le_div_iff₀ (unitRoot_pos t)).mpr
  linarith

/-- Helper for lem:polar-continuation: cubing the original scale update gives
the exact rational recurrence `t ^ 3 / (1 + t ^ 3)`. -/
theorem nextScale_cube (t : ℝ) (ht : 0 ≤ t) :
    nextScale t ^ 3 = t ^ 3 / (1 + t ^ 3) := by
  have hbase : 0 < 1 + t ^ 3 := by positivity
  rw [nextScale_def, div_pow, unitRoot_cube t hbase]

/-- Helper for lem:polar-continuation: the cubic scale barrier loses at most
`t ^ 6` in one step. -/
theorem nextScale_cube_lower (t : ℝ) (ht : 0 ≤ t) :
    t ^ 3 - t ^ 6 ≤ nextScale t ^ 3 := by
  have hbase : 0 < 1 + t ^ 3 := by positivity
  rw [nextScale_cube t ht]
  apply (le_div_iff₀ hbase).mpr
  nlinarith [pow_nonneg ht 9]

end DFP.Polar.Normalized

namespace DFP.Polar.TubeBounds

/-- Helper for lem:polar-continuation: the manuscript's scalar slow update
before its fast-error and fourth-order perturbations. -/
def scalarStep (G : ℝ → ℝ) (K t b : ℝ) : ℝ :=
  b + t ^ 3 * G (K + b)

/-- Helper for lem:polar-continuation: the explicit formula for the scalar
slow update. -/
theorem scalarStep_apply (G : ℝ → ℝ) (K t b : ℝ) :
    scalarStep G K t b = b + t ^ 3 * G (K + b) := by
  rfl

/-- Helper for lem:polar-continuation: the scalar update has derivative
`1 + t ^ 3 * deriv G (K + b)`. -/
theorem hasDerivAt_scalarStep (G : ℝ → ℝ) (K t b : ℝ)
    (hG : DifferentiableAt ℝ G (K + b)) :
    HasDerivAt (scalarStep G K t) (1 + t ^ 3 * deriv G (K + b)) b := by
  have hshift : HasDerivAt (fun x : ℝ ↦ K + x) 1 b :=
    (hasDerivAt_id b).const_add K
  have hd := (hasDerivAt_id b).add ((hG.hasDerivAt.comp b hshift).const_mul (t ^ 3))
  have hfun :
      (id + fun y : ℝ ↦ t ^ 3 * (G ∘ HAdd.hAdd K) y) = scalarStep G K t := by
    funext x
    exact (scalarStep_apply G K t x).symm
  rw [hfun] at hd
  simpa only [mul_one] using hd

/-- Helper for lem:polar-continuation: two-sided drift derivative bounds make
the scalar update increasing and contractive toward its equilibrium, for one
fixed sufficiently small scale. -/
theorem scalarStep_control (G : ℝ → ℝ) (K r rate D t : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hsmall : D * t ^ 3 ≤ 1) (heq : G K = 0)
    (hdiff : ∀ x ∈ Set.Icc (K - r) (K + r), DifferentiableAt ℝ G x)
    (hderiv : ∀ x ∈ Set.Icc (K - r) (K + r),
      -D ≤ deriv G x ∧ deriv G x ≤ -rate) :
    MonotoneOn (scalarStep G K t) (Set.Icc (-r) r) ∧
      0 ≤ 1 - rate * t ^ 3 ∧
      ∀ b ∈ Set.Icc (-r) r,
        |scalarStep G K t b| ≤ (1 - rate * t ^ 3) * |b| := by
  have htranslate : ∀ b ∈ Set.Icc (-r) r, K + b ∈ Set.Icc (K - r) (K + r) := by
    intro b hb
    constructor
    · linarith [hb.1]
    · linarith [hb.2]
  have hd : ∀ b ∈ Set.Icc (-r) r,
      HasDerivAt (scalarStep G K t) (1 + t ^ 3 * deriv G (K + b)) b := by
    intro b hb
    exact hasDerivAt_scalarStep G K t b (hdiff _ (htranslate b hb))
  have hnonnegative : ∀ b ∈ Set.Icc (-r) r,
      0 ≤ 1 + t ^ 3 * deriv G (K + b) := by
    intro b hb
    have hlower := (hderiv _ (htranslate b hb)).1
    have hmul := mul_le_mul_of_nonneg_left hlower (pow_nonneg ht 3)
    nlinarith
  have hupper : ∀ b ∈ Set.Icc (-r) r,
      1 + t ^ 3 * deriv G (K + b) ≤ 1 - rate * t ^ 3 := by
    intro b hb
    have hbound := (hderiv _ (htranslate b hb)).2
    have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg ht 3)
    nlinarith
  have hcontinuous : ContinuousOn (scalarStep G K t) (Set.Icc (-r) r) := by
    intro b hb
    exact (hd b hb).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ (scalarStep G K t)
      (interior (Set.Icc (-r) r)) := by
    intro b hb
    exact (hd b (interior_subset hb)).differentiableAt.differentiableWithinAt
  have hmonotone : MonotoneOn (scalarStep G K t) (Set.Icc (-r) r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcontinuous hdifferentiable
    intro b hb
    rw [(hd b (interior_subset hb)).deriv]
    exact hnonnegative b (interior_subset hb)
  have hzeroMember : (0 : ℝ) ∈ Set.Icc (-r) r := ⟨neg_nonpos.mpr hr, hr⟩
  have hcoefficient : 0 ≤ 1 - rate * t ^ 3 :=
    (hnonnegative 0 hzeroMember).trans (hupper 0 hzeroMember)
  refine ⟨hmonotone, hcoefficient, ?_⟩
  intro b hb
  have hwithin : ∀ x ∈ Set.Icc (-r) r,
      HasDerivWithinAt (scalarStep G K t) (1 + t ^ 3 * deriv G (K + x))
        (Set.Icc (-r) r) x := by
    intro x hx
    exact (hd x hx).hasDerivWithinAt
  have hnorm : ∀ x ∈ Set.Icc (-r) r,
      ‖1 + t ^ 3 * deriv G (K + x)‖ ≤ 1 - rate * t ^ 3 := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonnegative x hx)]
    exact hupper x hx
  have hbound := (convex_Icc (-r) r).norm_image_sub_le_of_norm_hasDerivWithin_le
    hwithin hnorm hzeroMember hb
  have hzero : scalarStep G K t 0 = 0 := by
    rw [scalarStep_apply]
    simp only [add_zero, heq, mul_zero]
  simpa only [hzero, sub_zero, Real.norm_eq_abs] using hbound

/-- Helper for lem:polar-continuation: a fixed cubic fast margin absorbs both
the quadratic fast error and the decrease of the prescribed cubic scale. -/
theorem fastBarrier (γ C N t q qNext : ℝ)
    (hγ : 0 ≤ γ) (hC : 0 ≤ C) (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hqin : q ≤ N * t ^ 3)
    (hmargin : (C * N ^ 2 + N) * t ^ 3 ≤ N - γ * N - C)
    (hupdate : qNext ≤ γ * q + C * t ^ 3 + C * q ^ 2) :
    qNext ≤ N * Normalized.nextScale t ^ 3 := by
  have hquadratic : q ^ 2 ≤ N ^ 2 * t ^ 6 := by
    have hbound := pow_le_pow_left₀ hq hqin 2
    simpa only [mul_pow, ← pow_mul, Nat.reduceMul] using hbound
  have hlinear := mul_le_mul_of_nonneg_left hqin hγ
  have hsquare := mul_le_mul_of_nonneg_left hquadratic hC
  have hscaled := mul_le_mul_of_nonneg_right hmargin (pow_nonneg ht 3)
  have hpre : qNext ≤ N * (t ^ 3 - t ^ 6) := by
    nlinarith [hupdate]
  exact hpre.trans (mul_le_mul_of_nonneg_left (Normalized.nextScale_cube_lower t ht) hN)

/-- Helper for lem:polar-continuation: a restoring rate above `1 / 3` absorbs
the fourth-order slow error and cubic coupling to a fast cubic tube. -/
theorem slowBarrier (G : ℝ → ℝ) (K rate Ccross Cslow N M t q b bNext : ℝ)
    (hcross : 0 ≤ Ccross) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hq : q ≤ N * t ^ 3) (hb : |b| ≤ M * t)
    (hcoefficient : 0 ≤ 1 - rate * t ^ 3)
    (hcontract : |scalarStep G K t b| ≤ (1 - rate * t ^ 3) * |b|)
    (hmargin : Ccross * N * t ^ 2 ≤ (rate - 1 / 3) * M - Cslow)
    (herror : |bNext - scalarStep G K t b| ≤ Ccross * t ^ 3 * q + Cslow * t ^ 4) :
    |bNext| ≤ M * Normalized.nextScale t := by
  have htriangle : |bNext| ≤ |bNext - scalarStep G K t b| + |scalarStep G K t b| := by
    have hsum := abs_add_le (bNext - scalarStep G K t b) (scalarStep G K t b)
    simpa only [sub_add_cancel] using hsum
  have hfast := mul_le_mul_of_nonneg_left hq (mul_nonneg hcross (pow_nonneg ht 3))
  have hslow := mul_le_mul_of_nonneg_left hb hcoefficient
  have hscaled := mul_le_mul_of_nonneg_right hmargin (pow_nonneg ht 4)
  have hpre : |bNext| ≤ M * (t - t ^ 4 / 3) := by
    nlinarith [htriangle, herror, hcontract]
  exact hpre.trans (mul_le_mul_of_nonneg_left (Normalized.nextScale_lower_quartic t ht) hM)

/-- Helper for lem:polar-continuation: the fast width can be fixed with a
strict cubic margin before any slow width or initial scale is chosen. -/
theorem existsFastWidth (γ Cfast : ℝ) (hγ : γ < 1) (hC : 0 ≤ Cfast) :
    ∃ N > 0, γ * N + Cfast < N := by
  let N := (Cfast + 1) / (1 - γ)
  have hdenom : 0 < 1 - γ := sub_pos.mpr hγ
  have hnumerator : 0 < Cfast + 1 := by linarith
  have hN : 0 < N := div_pos hnumerator hdenom
  have hidentity : (1 - γ) * N = Cfast + 1 := by
    dsimp only [N]
    field_simp [hdenom.ne']
  refine ⟨N, hN, ?_⟩
  nlinarith

/-- Helper for lem:polar-continuation: the slow width can be chosen with a
strict margin over the fourth-order error once the restoring rate exceeds
`1 / 3`. -/
theorem existsSlowWidth (rate Cslow : ℝ) (hrate : (1 / 3 : ℝ) < rate)
    (hC : 0 ≤ Cslow) :
    ∃ M > 0, Cslow < (rate - 1 / 3) * M := by
  let M := (Cslow + 1) / (rate - 1 / 3)
  have hdenom : 0 < rate - 1 / 3 := sub_pos.mpr hrate
  have hnumerator : 0 < Cslow + 1 := by linarith
  have hM : 0 < M := div_pos hnumerator hdenom
  have hidentity : (rate - 1 / 3) * M = Cslow + 1 := by
    dsimp only [M]
    rw [mul_comm, div_mul_cancel₀ _ hdenom.ne']
  refine ⟨M, hM, ?_⟩
  linarith

/-- Helper for lem:polar-continuation: every positive bound eventually
dominates a constant times a positive power of the scale. -/
private theorem smallScalePolynomial_lt (c B : ℝ) (hB : 0 < B) (n : ℕ) :
    ∀ᶠ t : ℝ in 𝓝 0, c * t ^ (n + 1) < B := by
  have hc : ContinuousAt (fun t : ℝ ↦ c * t ^ (n + 1)) 0 := by fun_prop
  have hzero : c * (0 : ℝ) ^ (n + 1) < B := by simpa using hB
  exact hc.eventually (Iio_mem_nhds hzero)

/-- Helper for lem:polar-continuation: after the fast and slow widths and
their strict margins have been fixed, one common positive scale threshold
keeps the tube in its neighborhoods and absorbs all remaining errors. -/
theorem existsScaleThreshold (N M Cfast Ccross D r ρ marginFast marginSlow : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hfast : 0 < marginFast) (hslow : 0 < marginSlow) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ ε →
      M * t ≤ r ∧ N * t ^ 3 ≤ ρ ∧ D * t ^ 3 ≤ 1 ∧
      (Cfast * N ^ 2 + N) * t ^ 3 ≤ marginFast ∧
      Ccross * N * t ^ 2 ≤ marginSlow := by
  have hone : (0 : ℝ) < 1 := zero_lt_one
  have hslowRadius := smallScalePolynomial_lt M r hr 0
  have hfastRadius := smallScalePolynomial_lt N ρ hρ 2
  have hderivative := smallScalePolynomial_lt D 1 hone 2
  have hfastMargin := smallScalePolynomial_lt (Cfast * N ^ 2 + N) marginFast hfast 2
  have hslowMargin := smallScalePolynomial_lt (Ccross * N) marginSlow hslow 1
  have heventually : ∀ᶠ t : ℝ in 𝓝 0,
      M * t ≤ r ∧ N * t ^ 3 ≤ ρ ∧ D * t ^ 3 ≤ 1 ∧
      (Cfast * N ^ 2 + N) * t ^ 3 ≤ marginFast ∧
      Ccross * N * t ^ 2 ≤ marginSlow := by
    filter_upwards [hslowRadius, hfastRadius, hderivative, hfastMargin, hslowMargin] with
      t hsr hfr hd hfm hsm
    refine ⟨?_, hfr.le, hd.le, hfm.le, hsm.le⟩
    simpa only [Nat.zero_add, pow_one] using hsr.le
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp heventually
  refine ⟨min 1 (δ / 2), lt_min hone (half_pos hδ), min_le_left _ _, ?_⟩
  intro t ht htε
  have hnear : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact (htε.trans (min_le_right _ _)).trans_lt (half_lt_self hδ)
  exact hbound hnear

/-- Helper for lem:polar-continuation: fix the source estimates and a compact
restoring neighborhood, then select the fast width `N`, the slow width `M`,
and finally one scale threshold. These constants give both one-step tube
barriers for every update satisfying the explicit fast and slow estimates. -/
theorem existsInvariantTubeConstants (G : ℝ → ℝ)
    (K γ Cfast Ccross Cslow rate D r ρ : ℝ)
    (hγnonnegative : 0 ≤ γ) (hγ : γ < 1)
    (hfast : 0 ≤ Cfast) (hcross : 0 ≤ Ccross) (hslow : 0 ≤ Cslow)
    (hrate : (1 / 3 : ℝ) < rate) (hr : 0 < r) (hρ : 0 < ρ)
    (heq : G K = 0)
    (hdiff : ∀ x ∈ Set.Icc (K - r) (K + r), DifferentiableAt ℝ G x)
    (hderiv : ∀ x ∈ Set.Icc (K - r) (K + r),
      -D ≤ deriv G x ∧ deriv G x ≤ -rate) :
    ∃ N > 0, γ * N + Cfast < N ∧
      ∃ M > 0, Cslow < (rate - 1 / 3) * M ∧
      ∃ ε > 0, ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ ε →
        M * t ≤ r ∧ N * t ^ 3 ≤ ρ ∧
        ∀ q qNext b bNext : ℝ, 0 ≤ q → q ≤ N * t ^ 3 → |b| ≤ M * t →
          qNext ≤ γ * q + Cfast * t ^ 3 + Cfast * q ^ 2 →
          |bNext - scalarStep G K t b| ≤ Ccross * t ^ 3 * q + Cslow * t ^ 4 →
          qNext ≤ N * Normalized.nextScale t ^ 3 ∧
            |bNext| ≤ M * Normalized.nextScale t := by
  obtain ⟨N, hN, hNmargin⟩ := existsFastWidth γ Cfast hγ hfast
  obtain ⟨M, hM, hMmargin⟩ := existsSlowWidth rate Cslow hrate hslow
  have hfastMargin : 0 < N - γ * N - Cfast := by linarith
  have hslowMargin : 0 < (rate - 1 / 3) * M - Cslow := sub_pos.mpr hMmargin
  obtain ⟨ε, hε, hεone, hthreshold⟩ := existsScaleThreshold N M Cfast Ccross D r ρ
    (N - γ * N - Cfast) ((rate - 1 / 3) * M - Cslow) hr hρ hfastMargin hslowMargin
  refine ⟨N, hN, hNmargin, M, hM, hMmargin, ε, hε, hεone, ?_⟩
  intro t ht htε
  obtain ⟨hslowRadius, hfastRadius, hDsmall, hfastSmall, hslowSmall⟩ := hthreshold t ht htε
  refine ⟨hslowRadius, hfastRadius, ?_⟩
  intro q qNext b bNext hq hqin hbin hfastUpdate hslowUpdate
  have hb : b ∈ Set.Icc (-r) r := abs_le.mp (hbin.trans hslowRadius)
  have hcontrol := scalarStep_control G K r rate D t hr.le ht.le hDsmall heq hdiff hderiv
  constructor
  · exact fastBarrier γ Cfast N t q qNext hγnonnegative hfast hN.le ht.le
      hq hqin hfastSmall hfastUpdate
  · exact slowBarrier G K rate Ccross Cslow N M t q b bNext hcross hM.le ht.le
      hqin hbin hcontrol.2.1 (hcontrol.2.2 b hb) hslowSmall hslowUpdate

/-- Helper for lem:polar-continuation: the actual scalar restoring drift has
a finite lower derivative bound on every compact regular inverse-branch set. -/
theorem restoringDrift_compact_deriv_lower (νStar : ℝ) (𝒦 : Set ℝ)
    (h𝒦 : IsCompact 𝒦)
    (hregular : ∀ A ∈ 𝒦, A ≠ 0 ∧ ContDiffAt ℝ ω TwoCycle.inverseParameter A) :
    ∃ D > 0, ∀ A ∈ 𝒦, -D ≤ deriv (TwoCycle.restoringDrift νStar) A := by
  have hcontinuous : ContinuousOn (deriv (TwoCycle.restoringDrift νStar)) 𝒦 := by
    intro A hA
    have hbranch := hregular A hA
    have hanalytic := TwoCycle.restoringDrift_analyticAt νStar A hbranch.1 hbranch.2
    have hsmooth : ContDiffAt ℝ ω (TwoCycle.restoringDrift νStar) A := hanalytic.contDiffAt
    have horder : (0 : ℕ∞ω) + 1 ≤ ω := le_top
    exact (hsmooth.derivWithin horder).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := h𝒦.bddBelow_image hcontinuous
  have hD : 0 < |B| + 1 := by positivity
  refine ⟨|B| + 1, hD, ?_⟩
  intro A hA
  have hbound : B ≤ deriv (TwoCycle.restoringDrift νStar) A :=
    hB (Set.mem_image_of_mem _ hA)
  linarith [neg_abs_le B]

/-- Helper for lem:polar-continuation: the accepted slow-drift theorem gives
an actual compact restoring neighborhood with both a negative derivative upper
bound and a finite lower derivative bound. -/
theorem existsRestoringDerivativeBounds :
    ∃ rate > (1 / 3 : ℝ), ∃ δ > 0,
      ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + δ),
        νStar ∈ TwoCycle.parameterSet ∧ ∃ r > 0, ∃ D > 0,
          TwoCycle.restoringDrift νStar (cycleK νStar) = 0 ∧
          ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
            ContDiffAt ℝ ω (TwoCycle.restoringDrift νStar) A ∧ 0 < A ∧
              -D ≤ deriv (TwoCycle.restoringDrift νStar) A ∧
              deriv (TwoCycle.restoringDrift νStar) A ≤ -rate := by
  obtain ⟨rate, hrate, δ, hδ, hrestoring⟩ := TwoCycle.restoringSlowDrift
  refine ⟨rate, hrate, δ, hδ, ?_⟩
  intro νStar hνStar
  obtain ⟨hparameter, r, hr, _, _, _, _, heq, hbranch⟩ := hrestoring νStar hνStar
  have hregular : ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
      A ≠ 0 ∧ ContDiffAt ℝ ω TwoCycle.inverseParameter A := by
    intro A hA
    exact ⟨(hbranch A hA).2.2.1.ne', (hbranch A hA).1⟩
  obtain ⟨D, hD, hlower⟩ := restoringDrift_compact_deriv_lower νStar
    (Set.Icc (cycleK νStar - r) (cycleK νStar + r)) isCompact_Icc hregular
  refine ⟨hparameter, r, hr, D, hD, heq, ?_⟩
  intro A hA
  have hproperties := hbranch A hA
  have hsmooth : ContDiffAt ℝ ω (TwoCycle.restoringDrift νStar) A :=
    (TwoCycle.restoringDrift_analyticAt νStar A hproperties.2.2.1.ne'
      hproperties.1).contDiffAt
  exact ⟨hsmooth, hproperties.2.2.1, hlower A hA, hproperties.2.2.2.1⟩

/-- Helper for lem:polar-continuation: one-step barriers propagate along the
original next-scale recurrence from zero initial errors, keeping every later
scale below the same fixed threshold. This is an abstract tube induction. -/
theorem tubeBounds_of_barriers (t q b : ℕ → ℝ) (N M ε : ℝ)
    (hN : 0 ≤ N) (hM : 0 ≤ M) (ht : 0 < t 0) (hsmall : t 0 ≤ ε)
    (hscale : ∀ j, Normalized.nextScale (t j) = t (j + 1))
    (hqzero : q 0 = 0) (hbzero : b 0 = 0)
    (hbarrier : ∀ j, 0 < t j → t j ≤ ε → q j ≤ N * t j ^ 3 → |b j| ≤ M * t j →
      q (j + 1) ≤ N * Normalized.nextScale (t j) ^ 3 ∧
        |b (j + 1)| ≤ M * Normalized.nextScale (t j)) :
    ∀ j, 0 < t j ∧ t j ≤ ε ∧ q j ≤ N * t j ^ 3 ∧ |b j| ≤ M * t j := by
  intro j
  induction j with
  | zero =>
      refine ⟨ht, hsmall, ?_, ?_⟩
      · rw [hqzero]
        exact mul_nonneg hN (pow_nonneg ht.le 3)
      · rw [hbzero, abs_zero]
        exact mul_nonneg hM ht.le
  | succ j ih =>
      obtain ⟨hpositive, hthreshold, hfast, hslow⟩ := ih
      have hnext := hbarrier j hpositive hthreshold hfast hslow
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← hscale j]
        exact Normalized.nextScale_pos (t j) hpositive
      · calc
          t (j + 1) = Normalized.nextScale (t j) := (hscale j).symm
          _ ≤ t j := Normalized.nextScale_le_self (t j) hpositive.le
          _ ≤ ε := hthreshold
      · rw [← hscale j]
        exact hnext.1
      · rw [← hscale j]
        exact hnext.2

/-- Helper for lem:polar-continuation: the abstract tube induction applies
to the source's prescribed `Parameters.scale` sequence without replacing its
scale construction. The hypothesis is the explicit one-step barrier. -/
theorem tubeBounds_on_prescribedScales (p : Parameters) (hstart : 0 < p.startIndex)
    (q b : ℕ → ℝ) (N M ε : ℝ) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hsmall : p.scale 0 ≤ ε) (hqzero : q 0 = 0) (hbzero : b 0 = 0)
    (hbarrier : ∀ j, 0 < p.scale j → p.scale j ≤ ε →
      q j ≤ N * p.scale j ^ 3 → |b j| ≤ M * p.scale j →
      q (j + 1) ≤ N * Normalized.nextScale (p.scale j) ^ 3 ∧
        |b (j + 1)| ≤ M * Normalized.nextScale (p.scale j)) :
    ∀ j, 0 < p.scale j ∧ p.scale j ≤ ε ∧
      q j ≤ N * p.scale j ^ 3 ∧ |b j| ≤ M * p.scale j := by
  have hstartReal : 0 < (p.startIndex : ℝ) := by exact_mod_cast hstart
  have ht : 0 < p.scale 0 := by
    rw [Parameters.scale_def]
    simpa only [Nat.add_zero] using Real.rpow_pos_of_pos hstartReal (-(1 : ℝ) / 3)
  exact tubeBounds_of_barriers p.scale q b N M ε hN hM ht hsmall
    (Normalized.nextScale_scale p · hstart) hqzero hbzero hbarrier

/-- Helper for lem:polar-continuation: the source fast and slow estimates
give a tube on the prescribed scales in the fixed fast norm. The widths and
threshold are chosen before `Parameters` and its initial index. This theorem
is conditional on the stated update estimates and does not assert feasibility
of the actual polar matrix sequence. -/
theorem existsFixedNormTube_of_estimates (G : ℝ → ℝ)
    (K γ Cfast Ccross Cslow rate D r ρ : ℝ)
    (hγnonnegative : 0 ≤ γ) (hγ : γ < 1)
    (hfast : 0 ≤ Cfast) (hcross : 0 ≤ Ccross) (hslow : 0 ≤ Cslow)
    (hrate : (1 / 3 : ℝ) < rate) (hr : 0 < r) (hρ : 0 < ρ)
    (heq : G K = 0)
    (hdiff : ∀ x ∈ Set.Icc (K - r) (K + r), DifferentiableAt ℝ G x)
    (hderiv : ∀ x ∈ Set.Icc (K - r) (K + r),
      -D ≤ deriv G x ∧ deriv G x ≤ -rate) :
    ∃ N > 0, γ * N + Cfast < N ∧
      ∃ M > 0, Cslow < (rate - 1 / 3) * M ∧
      ∃ ε > 0, ε ≤ 1 ∧
        ∀ p : Parameters, 0 < p.startIndex → p.scale 0 ≤ ε →
        ∀ (u : ℕ → Fin 2 → ℝ) (b : ℕ → ℝ), u 0 = 0 → b 0 = 0 →
          (∀ j, 0 < p.scale j → p.scale j ≤ ε →
            FastContraction.fixedNorm (u j) ≤ N * p.scale j ^ 3 → |b j| ≤ M * p.scale j →
            FastContraction.fixedNorm (u (j + 1)) ≤
              γ * FastContraction.fixedNorm (u j) + Cfast * p.scale j ^ 3 +
                Cfast * FastContraction.fixedNorm (u j) ^ 2 ∧
            |b (j + 1) - scalarStep G K (p.scale j) (b j)| ≤
              Ccross * p.scale j ^ 3 * FastContraction.fixedNorm (u j) +
                Cslow * p.scale j ^ 4) →
          ∀ j, 0 < p.scale j ∧ p.scale j ≤ ε ∧
            FastContraction.fixedNorm (u j) ≤ N * p.scale j ^ 3 ∧
            |b j| ≤ M * p.scale j ∧ FastContraction.fixedNorm (u j) ≤ ρ ∧ |b j| ≤ r := by
  obtain ⟨N, hN, hNmargin, M, hM, hMmargin, ε, hε, hεone, hstep⟩ :=
    existsInvariantTubeConstants G K γ Cfast Ccross Cslow rate D r ρ
      hγnonnegative hγ hfast hcross hslow hrate hr hρ heq hdiff hderiv
  refine ⟨N, hN, hNmargin, M, hM, hMmargin, ε, hε, hεone, ?_⟩
  intro p hstart hsmall u b huzero hbzero hupdates
  have hqzero : FastContraction.fixedNorm (u 0) = 0 :=
    (FastContraction.fixedNorm_eq_zero (u 0)).mpr huzero
  have hbarrier : ∀ j, 0 < p.scale j → p.scale j ≤ ε →
      FastContraction.fixedNorm (u j) ≤ N * p.scale j ^ 3 → |b j| ≤ M * p.scale j →
      FastContraction.fixedNorm (u (j + 1)) ≤ N * Normalized.nextScale (p.scale j) ^ 3 ∧
        |b (j + 1)| ≤ M * Normalized.nextScale (p.scale j) := by
    intro j ht htε hqin hbin
    have hupdate := hupdates j ht htε hqin hbin
    exact (hstep (p.scale j) ht htε).2.2
      (FastContraction.fixedNorm (u j)) (FastContraction.fixedNorm (u (j + 1)))
      (b j) (b (j + 1)) (FastContraction.fixedNorm_nonneg (u j)) hqin hbin
      hupdate.1 hupdate.2
  have htube := tubeBounds_on_prescribedScales p hstart
    (fun j ↦ FastContraction.fixedNorm (u j)) b N M ε hN.le hM.le hsmall hqzero hbzero hbarrier
  intro j
  obtain ⟨ht, htε, hfastBound, hslowBound⟩ := htube j
  have hneighborhood := hstep (p.scale j) ht htε
  exact ⟨ht, htε, hfastBound, hslowBound, hfastBound.trans hneighborhood.2.1,
    hslowBound.trans hneighborhood.1⟩

end DFP.Polar.TubeBounds
