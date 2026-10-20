module

public import ReasLib.Optimization.DFP.Polar.PlanarCounterexample
public import ReasLib.Optimization.DFP.Polar.SequenceAsymptotics

public section

open Filter
open DFP.Polar
open scoped Topology BigOperators Asymptotics

namespace DFPWolfe.V21

namespace SequenceProperties

open DFP.Polar.SequenceAsymptotics

/-- Helper for sec:known-results and lem:planar-degeneration: the source sequence
conclusions for one fixed original trajectory. The parameters `Cgrad`, `lower`,
`upper`, `productLower`, and `productUpper` are fixed comparison constants. The
scalar definitions are the accepted original source definitions, with current
matrix and previous curvature in `freeCoefficient` at every source index `k≥1`. -/
structure SourceEstimates (p : Parameters)
    (ν Cgrad lower upper productLower productUpper : ℝ) : Prop where
  /-- Helper for sec:known-results: the original cubic feedback coefficient is positive. -/
  feedback_pos : 0 < p.feedbackRate
  /-- Helper for sec:known-results: both ratio expansions have the same uniform
  fourth-order error constant, at every original phase index. -/
  gradient_ratio_errors : ∀ j,
    |gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3| ≤ Cgrad * p.scale j ^ 4 ∧
    |gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3| ≤ Cgrad * p.scale j ^ 4
  /-- Helper for sec:known-results: every even phase decreases and every odd
  phase increases the actual gradient norm. -/
  gradient_oscillation : ∀ j,
    ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j)‖ ∧
    ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j + 2)‖
  /-- Helper for sec:known-results: the gradient norm is not eventually nonincreasing. -/
  gradient_not_nonincreasing : ¬ ∀ᶠ k in atTop, ‖p.gradient (k + 1)‖ ≤ ‖p.gradient k‖
  /-- Helper for sec:known-results: the gradient norm is not eventually nondecreasing. -/
  gradient_not_nondecreasing : ¬ ∀ᶠ k in atTop, ‖p.gradient k‖ ≤ ‖p.gradient (k + 1)‖
  /-- Helper for sec:known-results: the actual physical step norms are comparable
  to the squared prescribed scales, with the fixed positive comparison constants. -/
  step_bounds : ∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖step p k‖ ∧
    ‖step p k‖ ≤ upper * p.scale (k / 2) ^ 2
  /-- Helper for sec:known-results: the total physical step length is infinite,
  both as nonsummability and as partial sums tending to positive infinity. -/
  length_diverges : (¬ Summable (fun k ↦ ‖step p k‖)) ∧
    Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ‖step p k‖) atTop atTop
  /-- Helper for sec:known-results: every accepted endpoint directional pairing is nonzero. -/
  endpoint_nonzero : ∀ k, WolfeRatios.endSlope p k ≠ 0
  /-- Helper for eq:planar-scalar-definition and sec:known-results: the exact
  physical secant curvature retains the source `σ/(1+ω²)` identity. -/
  curvature_law : ∀ k, curvature p k = p.sigma k / (1 + p.omega k ^ 2)
  /-- Helper for eq:planar-scalar-definition and sec:known-results: the actual
  normalized secant curvature tends to one. -/
  curvature_limit : Tendsto (curvature p) atTop (𝓝 1)
  /-- Helper for lem:planar-degeneration and sec:known-results: the original
  physical inverse-Hessian determinants have the exact source quartic equivalent. -/
  determinant_order : (fun k ↦ (p.inverseHessian k).det) ~[atTop]
    (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar)
  /-- Helper for eq:planar-scalar-definition and sec:known-results: the ORIGINAL
  `λ_k=κ_(k−1)det H_k` has that same source quartic equivalent. -/
  free_coefficient_order : freeCoefficient p ~[atTop]
    (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar)
  /-- Helper for lem:planar-degeneration and sec:known-results: the original
  free coefficient is comparable to consecutive physical step products. -/
  free_coefficient_step_bounds : ∀ᶠ k in atTop,
    productLower * (‖step p (k - 1)‖ * ‖step p k‖) ≤ freeCoefficient p k ∧
    freeCoefficient p k ≤ productUpper * (‖step p (k - 1)‖ * ‖step p k‖)
  /-- Helper for sec:known-results: Xu's ORIGINAL scalar has the even source
  coefficient `2awStar` and odd source coefficient `azStar`. -/
  xu_orders : ((fun j ↦ xuScalar p (2 * j)) ~[atTop]
      (fun j ↦ (2 * baseAngle * cycleW ν) * p.scale j ^ 4)) ∧
    ((fun j ↦ xuScalar p (2 * j + 1)) ~[atTop]
      (fun j ↦ (baseAngle * cycleZ ν) * p.scale j ^ 4))
  /-- Helper for sec:known-results: the NEXT even to current odd Xu ratio tends
  to the exact source constant, which is strictly larger than four. -/
  xu_jump : Tendsto (fun j ↦ xuScalar p (2 * j + 2) / xuScalar p (2 * j + 1))
      atTop (𝓝 (2 * cycleW ν / cycleZ ν)) ∧ 4 < 2 * cycleW ν / cycleZ ν
  /-- Helper for sec:known-results: Xu's original scalar is not eventually nonincreasing. -/
  xu_not_nonincreasing : ¬ ∀ᶠ k in atTop, xuScalar p (k + 1) ≤ xuScalar p k

/-- Helper for sec:known-results: the accepted actual sequence theorem yields
one source record, with all positive constants fixed before every later start.
The product constants use the SAME step bounds and exact source normalization. -/
theorem sourceSequenceNeighborhood :
    ∃ η > 0, ∀ ν ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ Cgrad > 0, ∃ lower > 0, ∃ upper > 0,
        ∃ productLower > 0, ∃ productUpper > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
          SourceEstimates (Parameters.of j₀ ν) ν Cgrad lower upper productLower productUpper := by
  obtain ⟨η, hη, hactual⟩ := polarSequenceAsymptotics
  refine ⟨η, hη, ?_⟩
  intro ν hnear
  obtain ⟨hparameter, Cgrad, hCgrad, lower, hlower, upper, hupper, J, hJ, hall⟩ := hactual ν hnear
  have hK : 0 < cycleK ν := by
    simpa only [Set.mem_Ioi] using (TwoCycle.cycleFamily_mapsTo_positive hparameter).1
  let productLower := 1 / (8 * upper ^ 2 * cycleK ν)
  let productUpper := 2 / (lower ^ 2 * cycleK ν)
  have hProductLower : 0 < productLower := by
    dsimp only [productLower]
    positivity
  have hProductUpper : 0 < productUpper := by
    dsimp only [productUpper]
    positivity
  refine ⟨Cgrad, hCgrad, lower, hlower, upper, hupper,
    productLower, hProductLower, productUpper, hProductUpper, J, hJ, ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ ν
  obtain ⟨hL, herrors, _, hsigns, hnotDown, hnotUp, hsteps, hlength, hendpoint,
    hcurvatureLaw, hcurvatureLimit, hdet, hfree, hEvenXu, hOddXu, hJump, hJumpLarge, hXuNot⟩ :=
    hall j₀ hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ.trans_le hj₀
  have hpK : p.kStar = cycleK ν := by
    rw [Parameters.kStar_def, Parameters.of_cycleParameter]
  have hKp : 0 < p.kStar := by
    rw [hpK]
    exact hK
  have hproduct : ∀ᶠ k in atTop,
      productLower * (‖step p (k - 1)‖ * ‖step p k‖) ≤ freeCoefficient p k ∧
      freeCoefficient p k ≤ productUpper * (‖step p (k - 1)‖ * ‖step p k‖) := by
    have h := freeCoefficient_stepProduct_bounds p hstart hKp hlower hupper hsteps hfree
    simpa only [productLower, productUpper, hpK] using h
  exact ⟨hL, herrors, hsigns, hnotDown, hnotUp, hsteps, hlength, hendpoint,
    hcurvatureLaw, hcurvatureLimit, hdet, hfree, hproduct,
    ⟨hEvenXu, hOddXu⟩, ⟨hJump, hJumpLarge⟩, hXuNot⟩

/-- Helper for sec:known-results: exact source endpoint data turn the actual
all-index model Wolfe certificates into the canonical strong Wolfe predicate. -/
theorem strongWolfeOfSourceModel {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hc₁ : 0 < c₁) (horder : c₁ < c₂) (hc₂ : c₂ < 1)
    (hmodel : ∀ k, WolfeRatios.ModelStrongWolfe p k c₁ c₂) :
    ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k) := by
  have hendpoints (k : ℕ) := PlanarCounterexample.modelStrongWolfe_radial_endpoints p k (hmodel k)
  exact PlanarCounterexample.strongWolfe_of_radial_endpoints h hc₁ horder hc₂
    (fun k ↦ (hendpoints k).1) (fun k ↦ (hendpoints k).2)

/-- Helper for sec:known-results: the canonical scaled inverse-DFP step is
exactly the original physical displacement under the source identity. -/
theorem canonicalStep_eq_source {p : Parameters} {κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    DFP.steps w.iteration.stepLength
      (DFP.directions w.iteration.inverseHessian
        (DFP.gradients w.iteration.objective w.iteration.point)) k = step p k := by
  have hdisplacement : w.iteration.point (k + 1) - w.iteration.point k =
      DFP.steps w.iteration.stepLength
        (DFP.directions w.iteration.inverseHessian
          (DFP.gradients w.iteration.objective w.iteration.point)) k := by
    rw [w.iteration.pointSucc k]
    abel
  rw [← hdisplacement, h.point, step_def]

/-- Helper for sec:known-results and eq:planar-scalar-definition: canonical
gradient changes equal the original prescribed source secants. -/
theorem canonicalSecant_eq_source {p : Parameters} {κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    DFP.gradientChanges (DFP.gradients w.iteration.objective w.iteration.point) k =
      secant p k := by
  rw [h.gradients, DFP.gradientChanges_apply, secant_def]

/-- Helper for sec:known-results: Xu's scalar formed from the canonical step,
gradient change and SAME original step length equals the source scalar exactly. -/
theorem canonicalXuScalar_eq_source {p : Parameters} {κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    inner ℝ (DFP.steps w.iteration.stepLength
      (DFP.directions w.iteration.inverseHessian
        (DFP.gradients w.iteration.objective w.iteration.point)) k)
      (DFP.gradientChanges (DFP.gradients w.iteration.objective w.iteration.point) k) /
        w.iteration.stepLength k = xuScalar p k := by
  rw [canonicalStep_eq_source h, canonicalSecant_eq_source h, h.stepLength,
    xuScalar_def, secantPairing_def]

/-- Helper for sec:known-results and eq:planar-scalar-definition: the canonical
normalized secant curvature is exactly the original source `κ_k`. -/
theorem canonicalCurvature_eq_source {p : Parameters} {κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    inner ℝ (DFP.steps w.iteration.stepLength
      (DFP.directions w.iteration.inverseHessian
        (DFP.gradients w.iteration.objective w.iteration.point)) k)
      (DFP.gradientChanges (DFP.gradients w.iteration.objective w.iteration.point) k) /
      ‖DFP.steps w.iteration.stepLength
        (DFP.directions w.iteration.inverseHessian
          (DFP.gradients w.iteration.objective w.iteration.point)) k‖ ^ 2 = curvature p k := by
  rw [canonicalStep_eq_source h, canonicalSecant_eq_source h, curvature_def, secantPairing_def]

/-- Helper for sec:known-results and eq:planar-scalar-definition: previous
canonical curvature times the CURRENT canonical determinant is the ORIGINAL
source `λ_k`, with natural subtraction merely totalizing index zero. -/
theorem canonicalFreeCoefficient_eq_source {p : Parameters} {κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    (inner ℝ (DFP.steps w.iteration.stepLength
      (DFP.directions w.iteration.inverseHessian
        (DFP.gradients w.iteration.objective w.iteration.point)) (k - 1))
      (DFP.gradientChanges (DFP.gradients w.iteration.objective w.iteration.point) (k - 1)) /
      ‖DFP.steps w.iteration.stepLength
        (DFP.directions w.iteration.inverseHessian
          (DFP.gradients w.iteration.objective w.iteration.point)) (k - 1)‖ ^ 2) *
      (w.iteration.inverseHessian k).det = freeCoefficient p k := by
  rw [canonicalCurvature_eq_source h, h.inverseHessian, freeCoefficient_def]

/-- Helper for sec:known-results: BOTH failures of eventual monotonicity hold
for the canonical objective gradients of the SAME standard counterexample. -/
theorem SourceEstimates.canonicalGradientOscillation
    {p : Parameters} {ν Cgrad lower upper productLower productUpper κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : SourceEstimates p ν Cgrad lower upper productLower productUpper)
    (hsource : PlanarCounterexample.SourceIdentity p κ w) :
    (¬ ∀ᶠ k in atTop,
      ‖DFP.gradients w.iteration.objective w.iteration.point (k + 1)‖ ≤
        ‖DFP.gradients w.iteration.objective w.iteration.point k‖) ∧
    (¬ ∀ᶠ k in atTop,
      ‖DFP.gradients w.iteration.objective w.iteration.point k‖ ≤
        ‖DFP.gradients w.iteration.objective w.iteration.point (k + 1)‖) := by
  rw [hsource.gradients]
  exact ⟨h.gradient_not_nonincreasing, h.gradient_not_nondecreasing⟩

/-- Helper for sec:known-results: the SAME canonical inverse-DFP scaled steps
retain the quadratic comparisons and infinite total physical length. -/
theorem SourceEstimates.canonicalStepProperties
    {p : Parameters} {ν Cgrad lower upper productLower productUpper κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : SourceEstimates p ν Cgrad lower upper productLower productUpper)
    (hsource : PlanarCounterexample.SourceIdentity p κ w) :
    let s := DFP.steps w.iteration.stepLength
      (DFP.directions w.iteration.inverseHessian
        (DFP.gradients w.iteration.objective w.iteration.point))
    (∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖s k‖ ∧ ‖s k‖ ≤ upper * p.scale (k / 2) ^ 2) ∧
    (¬ Summable (fun k ↦ ‖s k‖)) ∧
      Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ‖s k‖) atTop atTop := by
  dsimp only
  simp_rw [canonicalStep_eq_source hsource]
  exact ⟨h.step_bounds, h.length_diverges⟩

/-- Helper for sec:known-results: the canonical next-endpoint gradient paired
with the SAME canonical step is nonzero at every accepted endpoint. -/
theorem SourceEstimates.canonicalEndpointNonzero
    {p : Parameters} {ν Cgrad lower upper productLower productUpper κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : SourceEstimates p ν Cgrad lower upper productLower productUpper)
    (hsource : PlanarCounterexample.SourceIdentity p κ w) (k : ℕ) :
    inner ℝ (DFP.gradients w.iteration.objective w.iteration.point (k + 1))
      (DFP.steps w.iteration.stepLength
        (DFP.directions w.iteration.inverseHessian
          (DFP.gradients w.iteration.objective w.iteration.point)) k) ≠ 0 := by
  rw [canonicalStep_eq_source hsource, hsource.gradients, step_def]
  simpa only [WolfeRatios.endSlope_def] using h.endpoint_nonzero k

/-- Helper for sec:known-results: the exact canonical unit-circle cluster set
excludes convergence of the iterates to ANY point, not only to the minimizer. -/
theorem not_convergent_of_circle_cluster {ε c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.CounterexampleProperties ε w) :
    ¬ ∃ z : EuclideanSpace ℝ (Fin 2), Tendsto w.iteration.point atTop (𝓝 z) := by
  rintro ⟨z, hz⟩
  have hzero := (h.cluster (polarUnit 0)).mpr (PhysicalRealization.polarUnit_norm 0)
  have hpi := (h.cluster (polarUnit Real.pi)).mpr (PhysicalRealization.polarUnit_norm Real.pi)
  obtain ⟨φ, hφ, hφlimit⟩ := hzero.tendsto_subseq
  obtain ⟨ψ, hψ, hψlimit⟩ := hpi.tendsto_subseq
  have hzeroz := tendsto_nhds_unique hφlimit (hz.comp hφ.tendsto_atTop)
  have hpiz := tendsto_nhds_unique hψlimit (hz.comp hψ.tendsto_atTop)
  have hcoordinate := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0)
    (hzeroz.trans hpiz.symm)
  norm_num only [polarUnit_apply_zero, Real.cos_zero, Real.cos_pi] at hcoordinate

end SequenceProperties

/-- sec:known-results and the polar paragraph following lem:planar-degeneration:
the SAME canonical planar strong-Wolfe counterexample has Theorem 1's analytic,
geometric and sharpness conclusions AND all original source sequence properties.

The Wolfe parameter `νStar` is selected inside the intersection of the source-data
and sequence neighborhoods. It is fixed first; the support coefficient and every
sequence comparison constant are then fixed before ALL requested accuracies and
ALL later starting indices. For each accuracy, one natural threshold combines
the source objective, model Wolfe, and sequence thresholds. `SourceIdentity` keeps
the objective, points, canonical gradients, matrices and positive step lengths
equal to the original prescribed data of that SAME `Parameters.of j₀ νStar`. -/
theorem planarCounterexampleFamilyWithSequenceProperties (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ Cgrad > 0, ∃ lower > 0, ∃ upper > 0,
      ∃ productLower > 0, ∃ productUpper > 0,
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
          PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ w ∧
          PlanarCounterexample.CounterexampleProperties ε w ∧
          SequenceProperties.SourceEstimates (Parameters.of j₀ νStar) νStar
            Cgrad lower upper productLower productUpper := by
  obtain ⟨ηs, hηs, hsourceData⟩ := PlanarCounterexample.sourceDataNeighborhood
  obtain ⟨ηq, hηq, hsequenceData⟩ := SequenceProperties.sourceSequenceNeighborhood
  obtain ⟨νStar, hνStar, _, Jw, _, hmodels⟩ :=
    WolfeRatios.existsUniformModelWolfe c₁ c₂ (min ηs ηq) hc₁ hc₁lim hc₂lim hc₂ (lt_min hηs hηq)
  have hnearSource : νStar ∈ Set.Ioo baseAngle (baseAngle + ηs) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl (min_le_left ηs ηq)) hνStar
  have hnearSequence : νStar ∈ Set.Ioo baseAngle (baseAngle + ηq) :=
    Set.Ioo_subset_Ioo_right (add_le_add le_rfl (min_le_right ηs ηq)) hνStar
  obtain ⟨κ, hκ, C, _, H, hH, haccuracy⟩ := hsourceData νStar hnearSource
  obtain ⟨Cgrad, hCgrad, lower, hlower, upper, hupper, productLower, hProductLower,
    productUpper, hProductUpper, Jq, _, hsequences⟩ := hsequenceData νStar hnearSequence
  refine ⟨νStar, hνStar.1, κ, hκ, Cgrad, hCgrad, lower, hlower, upper, hupper,
    productLower, hProductLower, productUpper, hProductUpper, ?_⟩
  intro ε hε _
  let δ := min ε (1 / 2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
  have hδ : 0 < δ := lt_min hε hhalf
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hδone : δ < 1 := hδhalf.trans_lt hhalfOne
  obtain ⟨Js, hJs, hsource⟩ := haccuracy δ hδ hδone
  refine ⟨max Js (max Jw Jq), hJs.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  have hjSource : Js ≤ j₀ := (le_max_left _ _).trans hj₀
  have hjWolfe : Jw ≤ j₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hj₀
  have hjSequence : Jq ≤ j₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hj₀
  have hactual := hsource j₀ hjSource
  have hwolfe := SequenceProperties.strongWolfeOfSourceModel hactual.objective
    hc₁ (hc₁lim.trans_le hc₂lim) hc₂ (hmodels j₀ hjWolfe)
  obtain ⟨w, hidentity, hproperties⟩ :=
    PlanarCounterexample.certificateOfSourceData hactual hδhalf hδε hH.le hwolfe
  exact ⟨w, hidentity, hproperties, hsequences j₀ hjSequence⟩

/-- Helper for sec:known-results and lem:planar-degeneration: for any requested
accuracy, one canonical planar strong-Wolfe counterexample simultaneously has
all Theorem 1 properties and all source sequence refinements, with exact source identity. -/
theorem planarCounterexampleWithSequenceProperties (c₁ c₂ ε : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1)
    (hε : 0 < ε) (hεone : ε < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ Cgrad > 0, ∃ lower > 0, ∃ upper > 0,
      ∃ productLower > 0, ∃ productUpper > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
      ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
        PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ w ∧
        PlanarCounterexample.CounterexampleProperties ε w ∧
        SequenceProperties.SourceEstimates (Parameters.of j₀ νStar) νStar
          Cgrad lower upper productLower productUpper := by
  obtain ⟨νStar, hνStar, κ, hκ, Cgrad, hCgrad, lower, hlower, upper, hupper,
    productLower, hProductLower, productUpper, hProductUpper, haccuracy⟩ :=
    planarCounterexampleFamilyWithSequenceProperties c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  obtain ⟨J, hJ, hfamily⟩ := haccuracy ε hε hεone
  obtain ⟨w, hidentity, hproperties, hsequences⟩ := hfamily J le_rfl
  exact ⟨νStar, hνStar, κ, hκ, Cgrad, hCgrad, lower, hlower, upper, hupper,
    productLower, hProductLower, productUpper, hProductUpper, J, hJ,
    w, hidentity, hproperties, hsequences⟩

end DFPWolfe.V21
