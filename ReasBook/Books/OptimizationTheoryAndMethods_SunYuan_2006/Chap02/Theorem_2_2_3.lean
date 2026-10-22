/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Monotone.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Lemma_2_2_6

open Filter
open scoped Gradient

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Source/core/bridge:
-- * source-facing owners: the two accumulation-direction theorems below;
-- * core/canonical local ingredient: the Chapter 2 exact-line-search owner
--   `IsExactLineSearchStepOnNonnegativeRay`, built from `lineSearchObjective`, together with
--   subsequence convergence via `Tendsto`;
-- The source theorem stays stated on explicit iterate, direction, and step-size sequences.
-- The iterate-update equation from Algorithm 2.2.1 is part of the source semantics and must stay
-- explicit: the exact-line-search stationarity equations live at `x k + α k • d k`, while the
-- theorem concludes about accumulation points extracted from a subsequence of the iterates `x`.

/-- Helper for Chapter02 Theorem 2.2.3: exact line search makes each objective step
nonincreasing. -/
lemma objectiveStep_le_of_exactLineSearch
    (f : Point → ℝ) (x d : ℕ → Point) (α : ℕ → ℝ)
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (k : ℕ) :
    f (x (k + 1)) ≤ f (x k) := by
  -- Compare the exact step against the admissible trial step `0`.
  have hopt :
      lineSearchObjective f (x k) (d k) (α k) ≤
        lineSearchObjective f (x k) (d k) 0 :=
    (h_exactLineSearch k).optimal (by simp)
  -- Rewriting through the iterate update recovers the source-facing decrease statement.
  simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update k] using hopt

/-- Helper for Chapter02 Theorem 2.2.3: a convergent subsequence cannot sustain a uniform
objective drop along successive selected iterates. -/
lemma subseqLimit_forbidsFixedDrop
    (F : ℕ → ℝ) {φ : ℕ → ℕ} {L c : ℝ}
    (hstep : ∀ k : ℕ, F (k + 1) ≤ F k)
    (hφ : StrictMono φ)
    (h_tendsto : Tendsto (F ∘ φ) atTop (nhds L))
    (hc : 0 < c)
    (hdrop : ∀ᶠ n in atTop, F (φ n + 1) ≤ F (φ n) - c) :
    False := by
  have h_antitone : Antitone F := antitone_nat_of_succ_le hstep
  obtain ⟨Ndist, hNdist⟩ := Metric.tendsto_atTop.1 h_tendsto (c / 4) (by positivity)
  obtain ⟨Ndrop, hNdrop⟩ := Filter.eventually_atTop.1 hdrop
  let N := max Ndist Ndrop
  have hnear :
      dist (F (φ N)) L < c / 4 := hNdist N (le_max_left _ _)
  have hnearSucc :
      dist (F (φ (N + 1))) L < c / 4 := by
    exact hNdist (N + 1) (le_trans (le_max_left _ _) (Nat.le_succ _))
  have habs :
      |F (φ N) - L| < c / 4 := by
    simpa [Real.dist_eq] using hnear
  have habsSucc :
      |F (φ (N + 1)) - L| < c / 4 := by
    simpa [Real.dist_eq] using hnearSucc
  have hshift : φ N + 1 ≤ φ (N + 1) :=
    Nat.succ_le_of_lt (hφ (Nat.lt_succ_self N))
  have hdropN :
      F (φ N + 1) ≤ F (φ N) - c := hNdrop N (le_max_right _ _)
  have hchain :
      F (φ (N + 1)) ≤ F (φ N) - c := by
    exact le_trans (h_antitone hshift) hdropN
  have hupper : F (φ N) < L + c / 4 := by
    linarith [abs_lt.mp habs |>.2]
  have hlower : L - c / 4 < F (φ (N + 1)) := by
    linarith [abs_lt.mp habsSucc |>.1]
  linarith

/-- Helper for Chapter02 Theorem 2.2.3: a `C¹` function has continuous gradient on interior
points of the domain. -/
lemma continuousAt_gradient_of_contDiffOn
    {D : Set Point} (f : Point → ℝ)
    (hD : IsOpen D)
    (hC1 : ContDiffOn ℝ 1 f D)
    {x : Point} (hx : x ∈ D) :
    ContinuousAt (∇ f) x := by
  have hfContDiffAt : ContDiffAt ℝ 1 f x :=
    hC1.contDiffAt (hD.mem_nhds hx)
  have hfderivContDiffAt : ContDiffAt ℝ 0 (fderiv ℝ f) x :=
    hfContDiffAt.fderiv_right (m := 0) (by norm_num)
  have hgradContDiffAt :
      ContDiffAt ℝ 0 (((InnerProductSpace.toDual ℝ Point).symm) ∘ (fderiv ℝ f)) x := by
    exact
      (LinearIsometryEquiv.contDiff ((InnerProductSpace.toDual ℝ Point).symm)).contDiffAt.comp x
        hfderivContDiffAt
  change ContinuousAt (((InnerProductSpace.toDual ℝ Point).symm) ∘ (fderiv ℝ f)) x
  exact hgradContDiffAt.continuousAt

/-- Helper for Chapter02 Theorem 2.2.3: a `C²` function has continuous Hessian operator
`fderiv ℝ (∇ f)` on interior points of the domain. -/
lemma continuousAt_gradientFDeriv_of_contDiffOn
    {D : Set Point} (f : Point → ℝ)
    (hD : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    {x : Point} (hx : x ∈ D) :
    ContinuousAt (fderiv ℝ (∇ f)) x := by
  have hfContDiffAt : ContDiffAt ℝ 2 f x :=
    hC2.contDiffAt (hD.mem_nhds hx)
  have hfderivContDiffAt : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hfContDiffAt.fderiv_right_succ
  have hgradContDiffAt :
      ContDiffAt ℝ 1 (((InnerProductSpace.toDual ℝ Point).symm) ∘ (fderiv ℝ f)) x := by
    exact
      (LinearIsometryEquiv.contDiff ((InnerProductSpace.toDual ℝ Point).symm)).contDiffAt.comp x
        hfderivContDiffAt
  have hgradC1 : ContDiffAt ℝ 1 (∇ f) x := by
    change ContDiffAt ℝ 1 (((InnerProductSpace.toDual ℝ Point).symm) ∘ (fderiv ℝ f)) x
    exact hgradContDiffAt
  exact hgradC1.continuousAt_fderiv one_ne_zero

/-- Helper for Chapter02 Theorem 2.2.3: if the endpoint of a segment lies in a ball centered at
its base point, then the whole segment stays in the ball. -/
lemma segment_subset_ball_of_mem_ball
    {xStar x : Point} {ε : ℝ}
    (hx : x ∈ Metric.ball xStar ε) :
    segment ℝ xStar x ⊆ Metric.ball xStar ε := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg hx
  have hxStar : xStar ∈ Metric.ball xStar ε := Metric.mem_ball_self hε
  -- Convexity of the ball propagates the endpoint control to the whole segment.
  exact (convex_ball xStar ε).segment_subset hxStar hx

/-- Helper for Chapter02 Theorem 2.2.3: a strict trial-step decrease at the limit pair persists
along a convergent subsequence of iterates and directions. -/
lemma eventually_trialStepDrop_of_limitTrialStepDrop
    (f : Point → ℝ) (x d : ℕ → Point)
    {xBar dBar : Point} {φ : ℕ → ℕ} {αStar : ℝ}
    (hx_tendsto : Tendsto (x ∘ φ) atTop (nhds xBar))
    (hd_tendsto : Tendsto (d ∘ φ) atTop (nhds dBar))
    (hContBase : ContinuousAt f xBar)
    (hContStep : ContinuousAt f (xBar + αStar • dBar))
    (hdropBar :
      lineSearchObjective f xBar dBar αStar < lineSearchObjective f xBar dBar 0) :
    ∃ c > 0, ∀ᶠ n in atTop,
      lineSearchObjective f (x (φ n)) (d (φ n)) αStar ≤
        lineSearchObjective f (x (φ n)) (d (φ n)) 0 - c := by
  let trial : ℕ → ℝ := fun n ↦ f (x (φ n) + αStar • d (φ n))
  let base : ℕ → ℝ := fun n ↦ f (x (φ n))
  have hstep_tendsto :
      Tendsto (fun n : ℕ ↦ x (φ n) + αStar • d (φ n))
        atTop (nhds (xBar + αStar • dBar)) := by
    simpa [Function.comp] using hx_tendsto.add (hd_tendsto.const_smul αStar)
  have htrial_tendsto :
      Tendsto trial atTop (nhds (lineSearchObjective f xBar dBar αStar)) := by
    -- Evaluate the line-search objective at the fixed trial step through the traced endpoint.
    change Tendsto (f ∘ fun n : ℕ ↦ x (φ n) + αStar • d (φ n)) atTop
      (nhds (f (xBar + αStar • dBar)))
    exact hContStep.tendsto.comp hstep_tendsto
  have hbase_tendsto :
      Tendsto base atTop (nhds (lineSearchObjective f xBar dBar 0)) := by
    -- The base value is just the objective at the iterate itself.
    have hbase_tendsto' :
        Tendsto (fun n : ℕ ↦ f ((x ∘ φ) n)) atTop (nhds (f xBar)) :=
      hContBase.tendsto.comp hx_tendsto
    have hbase_tendsto'' :
        Tendsto (fun n : ℕ ↦ f (x (φ n))) atTop (nhds (f xBar)) := by
      simpa [Function.comp] using hbase_tendsto'
    simpa [base, lineSearchObjective_zero] using hbase_tendsto''
  let c := (lineSearchObjective f xBar dBar 0 - lineSearchObjective f xBar dBar αStar) / 3
  have hc_pos : 0 < c := by
    dsimp [c]
    linarith
  have htrial_event :
      ∀ᶠ n in atTop, trial n < lineSearchObjective f xBar dBar αStar + c := by
    have hIio :
        Set.Iio (lineSearchObjective f xBar dBar αStar + c) ∈
          nhds (lineSearchObjective f xBar dBar αStar) :=
      Iio_mem_nhds (by linarith [hc_pos])
    exact htrial_tendsto hIio
  have hbase_event :
      ∀ᶠ n in atTop, lineSearchObjective f xBar dBar 0 - c < base n := by
    have hIoi :
        Set.Ioi (lineSearchObjective f xBar dBar 0 - c) ∈
          nhds (lineSearchObjective f xBar dBar 0) :=
      Ioi_mem_nhds (by linarith [hc_pos])
    exact hbase_tendsto hIoi
  refine ⟨c, hc_pos, ?_⟩
  filter_upwards [htrial_event, hbase_event] with n htrial hbase
  have hstrict : trial n < base n - c := by
    dsimp [c] at htrial hbase ⊢
    linarith [htrial, hbase, hdropBar]
  simpa [trial, base, lineSearchObjective_apply, lineSearchObjective_zero] using hstrict.le

/-- Orthogonality consequence for Chapter02 Theorem 2.2.3: let `f` be continuously
differentiable on an open set `D`,
assume each step size `α k` is an exact line-search step on the nonnegative ray from `x k`
along `d k`, the iterates satisfy the Algorithm 2.2.1 update
`x (k + 1) = x k + α k • d k`, and
`inner ℝ (∇ f (x k)) (d k) ≤ 0` for every `k`, and let `xBar ∈ D` be the limit of a
subsequence of iterates `x ∘ φ` along which the directions `d ∘ φ` converge to `dBar`.
Then `inner ℝ (∇ f xBar) dBar = 0`. -/
theorem exactLineSearch_accumulationDirection_orthogonalToGradient
    {D : Set Point} (f : Point → ℝ) (x d : ℕ → Point) (α : ℕ → ℝ)
    (hD : IsOpen D)
    (hC1 : ContDiffOn ℝ 1 f D)
    (h_iterates : ∀ k : ℕ, x k ∈ D)
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_gradientDirection_nonpos : ∀ k : ℕ, inner ℝ (∇ f (x k)) (d k) ≤ 0)
    {xBar dBar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxBar : xBar ∈ D)
    (hx_tendsto : Tendsto (x ∘ φ) atTop (nhds xBar))
    (hd_tendsto : Tendsto (d ∘ φ) atTop (nhds dBar)) :
    inner ℝ (∇ f xBar) dBar = 0 := by
  let _ := h_iterates
  -- Route correction: use one fixed short trial step near the limit pair instead of splitting
  -- into the source proof's `α_k → 0` and `liminf α_k > 0` cases.
  have hcontGrad : ContinuousAt (∇ f) xBar :=
    continuousAt_gradient_of_contDiffOn f hD hC1 hxBar
  have hpair_tendsto :
      Tendsto (fun n : ℕ ↦ inner ℝ (∇ f (x (φ n))) (d (φ n)))
        atTop
        (nhds (inner ℝ (∇ f xBar) dBar)) := by
    exact (hcontGrad.tendsto.comp hx_tendsto).inner hd_tendsto
  have hpair_nonpos : inner ℝ (∇ f xBar) dBar ≤ 0 := by
    by_contra hpos
    have hpos' : 0 < inner ℝ (∇ f xBar) dBar := by
      linarith
    have hEventuallyPos :
        ∀ᶠ n in atTop, 0 < inner ℝ (∇ f (x (φ n))) (d (φ n)) := by
      exact hpair_tendsto (Ioi_mem_nhds hpos')
    have hEventuallyNonpos :
        ∀ᶠ n in atTop, inner ℝ (∇ f (x (φ n))) (d (φ n)) ≤ 0 :=
      Filter.Eventually.of_forall (fun n ↦ h_gradientDirection_nonpos (φ n))
    obtain ⟨Npos, hNpos⟩ := Filter.eventually_atTop.1 hEventuallyPos
    obtain ⟨Nnonpos, hNnonpos⟩ := Filter.eventually_atTop.1 hEventuallyNonpos
    let N := max Npos Nnonpos
    exact (not_lt_of_ge (hNnonpos N (le_max_right _ _))) (hNpos N (le_max_left _ _))
  rcases eq_or_lt_of_le hpair_nonpos with hzero | hneg
  · exact hzero
  · have hdesc : IsDescentDirectionAt f xBar dBar := hneg
    rcases hdesc.exists_localDecrease_lineSearchObjective with ⟨δ, hδ_pos, hδ_drop⟩
    rcases Metric.mem_nhds_iff.mp (hD.mem_nhds hxBar) with ⟨ε, hε_pos, hε_ball⟩
    let αStar := min (δ / 2) (ε / (2 * (‖dBar‖ + 1)))
    have hαStar_pos : 0 < αStar := by
      dsimp [αStar]
      positivity
    have hαStar_lt : αStar < δ := by
      calc
        αStar ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have hxStepBall : xBar + αStar • dBar ∈ Metric.ball xBar ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hB_pos : 0 < ‖dBar‖ + 1 := by positivity
      have hB_ne : ‖dBar‖ + 1 ≠ 0 := by positivity
      have hmul :
          αStar * (‖dBar‖ + 1) ≤ ε / 2 := by
        have hα_le : αStar ≤ ε / (2 * (‖dBar‖ + 1)) := min_le_right _ _
        have := mul_le_mul_of_nonneg_right hα_le (show 0 ≤ ‖dBar‖ + 1 by positivity)
        have hcalc :
            (ε / (2 * (‖dBar‖ + 1))) * (‖dBar‖ + 1) = ε / 2 := by
          field_simp [hB_ne]
        simpa [hcalc] using this
      have hnorm :
          ‖αStar • dBar‖ < ε := by
        have hnorm_le :
            ‖αStar • dBar‖ ≤ αStar * (‖dBar‖ + 1) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hαStar_pos)]
          nlinarith [norm_nonneg dBar]
        have hhalf_lt : ε / 2 < ε := by linarith
        exact lt_of_le_of_lt hnorm_le (lt_of_le_of_lt hmul hhalf_lt)
      simpa [sub_eq_add_neg] using hnorm
    have hxStep : xBar + αStar • dBar ∈ D := hε_ball hxStepBall
    have hdropBar :
        lineSearchObjective f xBar dBar αStar < lineSearchObjective f xBar dBar 0 :=
      hδ_drop αStar hαStar_pos hαStar_lt
    have hContBase : ContinuousAt f xBar :=
      (hC1.contDiffAt (hD.mem_nhds hxBar)).continuousAt
    have hContStep : ContinuousAt f (xBar + αStar • dBar) :=
      (hC1.contDiffAt (hD.mem_nhds hxStep)).continuousAt
    rcases
      eventually_trialStepDrop_of_limitTrialStepDrop
        f x d hx_tendsto hd_tendsto hContBase hContStep hdropBar with
      ⟨c, hc_pos, htrialDrop⟩
    have hactualDrop :
        ∀ᶠ n in atTop, f (x (φ n + 1)) ≤ f (x (φ n)) - c := by
      filter_upwards [htrialDrop] with n hn
      have hopt :
          lineSearchObjective f (x (φ n)) (d (φ n)) (α (φ n)) ≤
            lineSearchObjective f (x (φ n)) (d (φ n)) αStar :=
        (h_exactLineSearch (φ n)).optimal (le_of_lt hαStar_pos)
      have hstep :
          lineSearchObjective f (x (φ n)) (d (φ n)) (α (φ n)) ≤
            lineSearchObjective f (x (φ n)) (d (φ n)) 0 - c :=
        le_trans hopt hn
      -- Rewrite the exact-step objective through the iterate update.
      simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update (φ n)] using hstep
    have hbase_tendsto :
        Tendsto (fun n : ℕ ↦ f (x (φ n))) atTop (nhds (f xBar)) := by
      exact ((hC1.contDiffAt (hD.mem_nhds hxBar)).continuousAt.tendsto).comp hx_tendsto
    have hstepMono : ∀ k : ℕ, f (x (k + 1)) ≤ f (x k) :=
      objectiveStep_le_of_exactLineSearch f x d α h_exactLineSearch h_update
    exact False.elim <|
      subseqLimit_forbidsFixedDrop
        (fun k ↦ f (x k)) hstepMono hφ hbase_tendsto hc_pos hactualDrop

/-- Second-order consequence for Chapter02 Theorem 2.2.3: under the hypotheses of the
orthogonality result, if `f` is twice
continuously differentiable on `D`, then the limiting direction `dBar` has nonnegative
second-order directional curvature at `xBar`,
`0 ≤ inner ℝ dBar ((fderiv ℝ (∇ f) xBar) dBar)`. -/
theorem exactLineSearch_accumulationDirection_hessianQuadratic_nonneg
    {D : Set Point} (f : Point → ℝ) (x d : ℕ → Point) (α : ℕ → ℝ)
    (hD : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (h_iterates : ∀ k : ℕ, x k ∈ D)
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_gradientDirection_nonpos : ∀ k : ℕ, inner ℝ (∇ f (x k)) (d k) ≤ 0)
    {xBar dBar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxBar : xBar ∈ D)
    (hx_tendsto : Tendsto (x ∘ φ) atTop (nhds xBar))
    (hd_tendsto : Tendsto (d ∘ φ) atTop (nhds dBar)) :
    0 ≤ inner ℝ dBar ((fderiv ℝ (∇ f) xBar) dBar) := by
  have hC1 : ContDiffOn ℝ 1 f D := by
    simpa using (hC2.of_le (by decide) : ContDiffOn ℝ 1 f D)
  have horth :
      inner ℝ (∇ f xBar) dBar = 0 :=
    exactLineSearch_accumulationDirection_orthogonalToGradient
      f x d α hD hC1 h_iterates h_exactLineSearch h_update h_gradientDirection_nonpos
      hφ hxBar hx_tendsto hd_tendsto
  by_contra hneg
  rcases Metric.mem_nhds_iff.mp (hD.mem_nhds hxBar) with ⟨εD, hεD_pos, hεD_ball⟩
  let Q : Point → ℝ := fun z ↦ inner ℝ dBar ((fderiv ℝ (∇ f) z) dBar)
  have hQcont : ContinuousAt Q xBar := by
    -- Continuity of the Hessian operator gives continuity of the fixed-direction quadratic form.
    exact
      continuousAt_const.inner
        ((continuousAt_gradientFDeriv_of_contDiffOn f hD hC2 hxBar).clm_apply continuousAt_const)
  have hQevent : {z : Point | Q z < Q xBar / 2} ∈ nhds xBar := by
    have : Q xBar < Q xBar / 2 := by
      dsimp [Q]
      linarith
    exact hQcont (Iio_mem_nhds this)
  rcases Metric.mem_nhds_iff.mp hQevent with ⟨εQ, hεQ_pos, hεQ_ball⟩
  let ε := min εD εQ
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min hεD_pos hεQ_pos
  let αStar := ε / (2 * (‖dBar‖ + 1))
  have hαStar_pos : 0 < αStar := by
    dsimp [αStar]
    positivity
  have hxStepBall : xBar + αStar • dBar ∈ Metric.ball xBar ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hB_pos : 0 < ‖dBar‖ + 1 := by positivity
    have hB_ne : ‖dBar‖ + 1 ≠ 0 := by positivity
    have hmul :
        αStar * (‖dBar‖ + 1) = ε / 2 := by
      dsimp [αStar]
      field_simp [hB_ne]
    have hnorm :
        ‖αStar • dBar‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hαStar_pos)]
      have hnorm_le : αStar * ‖dBar‖ ≤ αStar * (‖dBar‖ + 1) := by
        nlinarith [norm_nonneg dBar]
      have hhalf_lt : ε / 2 < ε := by linarith
      rw [hmul] at hnorm_le
      exact lt_of_le_of_lt hnorm_le hhalf_lt
    simpa [sub_eq_add_neg] using hnorm
  have hxStepBallD : xBar + αStar • dBar ∈ Metric.ball xBar εD := by
    rw [Metric.mem_ball] at hxStepBall ⊢
    have hlt : dist (xBar + αStar • dBar) xBar < ε := hxStepBall
    exact lt_of_lt_of_le hlt (min_le_left _ _)
  have hxStep : xBar + αStar • dBar ∈ D := hεD_ball hxStepBallD
  have h_segment_ball :
      segment ℝ xBar (xBar + αStar • dBar) ⊆ Metric.ball xBar ε :=
    segment_subset_ball_of_mem_ball hxStepBall
  have h_segment :
      segment ℝ xBar (xBar + αStar • dBar) ⊆ D := by
    intro z hz
    have hzBallD : z ∈ Metric.ball xBar εD := by
      rw [Metric.mem_ball]
      have hlt : dist z xBar < ε := h_segment_ball hz
      exact lt_of_lt_of_le hlt (min_le_left _ _)
    exact hεD_ball hzBallD
  let trace : ℝ → Point := fun t ↦ xBar + t • (αStar • dBar)
  have htrace_mem :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1, trace t ∈ D := by
    intro t ht
    have hseg :
        trace t ∈ segment ℝ xBar (xBar + αStar • dBar) := by
      rw [segment_eq_image' ℝ xBar (xBar + αStar • dBar)]
      refine ⟨t, by simpa [Set.uIcc_of_le zero_le_one] using ht, ?_⟩
      simp [trace, smul_smul]
    exact h_segment hseg
  have hquadBound :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        Q (trace t) < Q xBar / 2 := by
    intro t ht
    have hball_mem : trace t ∈ Metric.ball xBar εQ := by
      have hseg :
          trace t ∈ segment ℝ xBar (xBar + αStar • dBar) := by
        rw [segment_eq_image' ℝ xBar (xBar + αStar • dBar)]
        refine ⟨t, by simpa [Set.uIcc_of_le zero_le_one] using ht, ?_⟩
        simp [trace, smul_smul]
      have hball : trace t ∈ Metric.ball xBar ε := h_segment_ball hseg
      rw [Metric.mem_ball] at hball ⊢
      exact lt_of_lt_of_le hball (min_le_right _ _)
    exact hεQ_ball hball_mem
  have hquadCont :
      ContinuousOn (fun t : ℝ ↦ Q (trace t)) (Set.uIcc (0 : ℝ) 1) := by
    intro t ht
    have hzt : trace t ∈ D := htrace_mem t ht
    have htraceCont : Continuous trace :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hquadAt : ContinuousAt Q (trace t) := by
      exact
        continuousAt_const.inner
          ((continuousAt_gradientFDeriv_of_contDiffOn f hD hC2 hzt).clm_apply continuousAt_const)
    exact (hquadAt.comp htraceCont.continuousAt).continuousWithinAt
  have hweightedCont :
      ContinuousOn
        (fun t : ℝ ↦ (1 - t) * Q (trace t))
        (Set.uIcc (0 : ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).mul hquadCont
  have hweightedInt :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * Q (trace t))
        MeasureTheory.volume 0 1 :=
    hweightedCont.intervalIntegrable
  have hconstInt :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * (Q xBar / 2))
        MeasureTheory.volume 0 1 := by
    exact
      ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).intervalIntegrable_of_Icc
        zero_le_one
  have hpointwise :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) * Q (trace t) ≤ (1 - t) * (Q xBar / 2) := by
    intro t ht
    have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc_of_le ht.1 ht.2
    have hfac_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hq_lt : Q (trace t) < Q xBar / 2 := hquadBound t ht'
    exact mul_le_mul_of_nonneg_left hq_lt.le hfac_nonneg
  have hIntegral_le :
      ∫ t in (0 : ℝ)..1, (1 - t) * Q (trace t) ≤
        ∫ t in (0 : ℝ)..1, (1 - t) * (Q xBar / 2) := by
    exact intervalIntegral.integral_mono_on zero_le_one hweightedInt hconstInt hpointwise
  have hweight_eval : ∫ t in (0 : ℝ)..1, (1 - t) = (1 / 2 : ℝ) := by
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hid : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
      continuous_id.intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const, integral_id]
    norm_num
  have hconst_eval :
      ∫ t in (0 : ℝ)..1, (1 - t) * (Q xBar / 2) = Q xBar / 4 := by
    rw [intervalIntegral.integral_mul_const]
    rw [hweight_eval]
    ring
  have hTaylor :=
    lineTaylorFormula_withIntegralHessianRemainder
      (D := D) f xBar dBar αStar hD h_segment hC2
  have hdropBar :
      lineSearchObjective f xBar dBar αStar < lineSearchObjective f xBar dBar 0 := by
    -- Taylor's formula plus the uniformly negative Hessian trace gives a strict trial-step drop.
    calc
      lineSearchObjective f xBar dBar αStar
          = f xBar + αStar * inner ℝ (∇ f xBar) dBar +
              αStar ^ (2 : ℕ) *
                ∫ t in (0 : ℝ)..1, (1 - t) * Q (trace t) := by
              simpa [Q, trace, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hTaylor
      _ = f xBar + αStar ^ (2 : ℕ) *
              ∫ t in (0 : ℝ)..1, (1 - t) * Q (trace t) := by
            simp [horth]
      _ ≤ f xBar + αStar ^ (2 : ℕ) *
              ∫ t in (0 : ℝ)..1, (1 - t) * (Q xBar / 2) := by
            gcongr
      _ = f xBar + αStar ^ (2 : ℕ) * (Q xBar / 4) := by
            rw [hconst_eval]
      _ < f xBar := by
            dsimp [Q] at hneg ⊢
            have hsq_pos : 0 < αStar ^ (2 : ℕ) := by positivity
            have hquarter_neg :
                inner ℝ dBar ((fderiv ℝ (∇ f) xBar) dBar) / 4 < 0 := by
              linarith
            have hmul_neg :
                αStar ^ (2 : ℕ) * (inner ℝ dBar ((fderiv ℝ (∇ f) xBar) dBar) / 4) < 0 :=
              mul_neg_of_pos_of_neg hsq_pos hquarter_neg
            linarith
      _ = lineSearchObjective f xBar dBar 0 := by
            simp [lineSearchObjective_zero]
  have hContBase : ContinuousAt f xBar :=
    (hC2.contDiffAt (hD.mem_nhds hxBar)).continuousAt
  have hContStep : ContinuousAt f (xBar + αStar • dBar) :=
    (hC2.contDiffAt (hD.mem_nhds hxStep)).continuousAt
  rcases
    eventually_trialStepDrop_of_limitTrialStepDrop
      f x d hx_tendsto hd_tendsto hContBase hContStep hdropBar with
    ⟨c, hc_pos, htrialDrop⟩
  have hactualDrop :
      ∀ᶠ n in atTop, f (x (φ n + 1)) ≤ f (x (φ n)) - c := by
    filter_upwards [htrialDrop] with n hn
    have hopt :
        lineSearchObjective f (x (φ n)) (d (φ n)) (α (φ n)) ≤
          lineSearchObjective f (x (φ n)) (d (φ n)) αStar :=
      (h_exactLineSearch (φ n)).optimal (le_of_lt hαStar_pos)
    have hstep :
        lineSearchObjective f (x (φ n)) (d (φ n)) (α (φ n)) ≤
          lineSearchObjective f (x (φ n)) (d (φ n)) 0 - c :=
      le_trans hopt hn
    -- Rewriting the exact-step objective through the iterate update gives the fixed-drop tail.
    simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update (φ n)] using hstep
  have hbase_tendsto :
      Tendsto (fun n : ℕ ↦ f (x (φ n))) atTop (nhds (f xBar)) := by
    exact ((hC2.contDiffAt (hD.mem_nhds hxBar)).continuousAt.tendsto).comp hx_tendsto
  have hstepMono : ∀ k : ℕ, f (x (k + 1)) ≤ f (x k) :=
    objectiveStep_le_of_exactLineSearch f x d α h_exactLineSearch h_update
  exact False.elim <|
    subseqLimit_forbidsFixedDrop
      (fun k ↦ f (x k)) hstepMono hφ hbase_tendsto hc_pos hactualDrop

/-- Chapter02 Theorem 2.2.3: under the `C²` hypothesis, the limiting
direction is orthogonal to `∇ f xBar` and has nonnegative second-order directional curvature
at `xBar`. -/
theorem exactLineSearch_accumulationDirection_firstAndSecondOrderConditions
    {D : Set Point} (f : Point → ℝ) (x d : ℕ → Point) (α : ℕ → ℝ)
    (hD : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (h_iterates : ∀ k : ℕ, x k ∈ D)
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_gradientDirection_nonpos : ∀ k : ℕ, inner ℝ (∇ f (x k)) (d k) ≤ 0)
    {xBar dBar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxBar : xBar ∈ D)
    (hx_tendsto : Tendsto (x ∘ φ) atTop (nhds xBar))
    (hd_tendsto : Tendsto (d ∘ φ) atTop (nhds dBar)) :
    inner ℝ (∇ f xBar) dBar = 0 ∧
      0 ≤ inner ℝ dBar ((fderiv ℝ (∇ f) xBar) dBar) := by
  constructor
  · have hC1 : ContDiffOn ℝ 1 f D := by
      simpa using (hC2.of_le (by decide) : ContDiffOn ℝ 1 f D)
    exact exactLineSearch_accumulationDirection_orthogonalToGradient
      f x d α hD hC1 h_iterates h_exactLineSearch h_update h_gradientDirection_nonpos
      hφ hxBar hx_tendsto hd_tendsto
  · exact exactLineSearch_accumulationDirection_hessianQuadratic_nonneg
      f x d α hD hC2 h_iterates h_exactLineSearch h_update h_gradientDirection_nonpos
      hφ hxBar hx_tendsto hd_tendsto

end
