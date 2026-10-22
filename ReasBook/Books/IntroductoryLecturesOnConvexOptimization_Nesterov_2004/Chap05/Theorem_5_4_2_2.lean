/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_2_2.CoreTransport
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_2_2.PointwiseCore

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open MeasureTheory

noncomputable section

/-- Classical decidability for propositions, used to evaluate the interior-membership branch in
`universalBarrierAmbient`. -/
local instance {p : Prop} : Decidable p := Classical.propDecidable p

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceTheorem5422 : MeasurableSpace E := borel E
local instance instBorelSpaceTheorem5422 : BorelSpace E := ⟨rfl⟩

/- Theorem 5.4.2.2 lies in the chapter's universal-barrier / finite-dimensional convex-geometry
domain.

Sampled owner-style declarations:
* `universalBarrierVolume` from `Definition_5_4_2_2`, the source-facing owner of the volume term
  `V(x)`;
* `polarSetAt` and `mem_polarSetAt_iff` from `Definition_5_4_2_1`, the geometric owner behind
  that volume term;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for self-concordant
  barriers on open convex domains;
* `polarSetAt_isCompact_convex` from `Theorem_5_4_2_1`, the preceding subsection's intrinsic
  finite-dimensional geometry theorem for the same based-polar construction.

Best owner abstraction:
* source-facing: the intrinsic universal barrier
  `universalBarrier c₁ Q : interior Q → ℝ`;
* core/canonical: `universalBarrierVolume Q x` together with
  `IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* bridge/view: the ambient totalization
  `universalBarrierAmbient c₁ Q : E → ℝ`, used only to feed the Chapter 5 barrier owner.

Primitive data:
* a finite-dimensional real inner-product space `E`;
* a set `Q : Set E`;
* the proper-convex regime on `Q`: convexity together with the absence of affine lines;
* a scaling constant `c₁`.

Derived API:
* the positivity bridge `universalBarrierVolume_pos`;
* the intrinsic barrier owner
  `universalBarrier c₁ Q : interior Q → ℝ`;
* the source-facing identity `universalBarrier_eq_log_volume`;
* the ambient bridge `universalBarrierAmbient c₁ Q : E → ℝ`;
* the Chapter 5 barrier owner
  `IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q)`;
* the intrinsic dimension factor `Module.finrank ℝ E`, which recovers the textbook dimension `n`
  on `EuclideanSpace ℝ (Fin n)`.

The previous version unnecessarily fixed the ambient space to `EuclideanSpace ℝ (Fin n)`. The
based-polar volume owner and the source formula `x ↦ c₁ log V(x)` are already intrinsic, so the
refined file keeps the same source mathematics while moving the public API to the canonical
finite-dimensional real inner-product owner level. The proper-convex/no-affine-line hypotheses are
kept only on the positivity bridge `universalBarrierVolume_pos` and on the final
self-concordance theorem, where they actually matter; the owner itself is just the source formula
`x ↦ c₁ log V(x)`. The ambient zero-extension is retained only as a thin bridge because
`IsSelfConcordantBarrierOnWith` is formulated for ambient maps `E → ℝ`. The theorem-level
positive constants are exposed on the canonical `NNRealˣ` surface rather than as ad hoc
positive-real subtypes. The final source-facing theorem keeps the textbook nonempty-interior
hypothesis while still expressing the ambient space intrinsically through `Module.finrank ℝ E`.
-/

-- Proof sketch: by Theorem 5.4.2.1 the based polar `polarSetAt Q x` is compact and has nonempty
-- interior under the proper-convex/no-affine-line hypotheses, so its finite-dimensional volume is
-- strictly positive.
/-- For a proper convex set `Q`, every interior based-polar body has strictly positive volume. This
positivity is the bridge that makes `log (universalBarrierVolume Q x)` the actual universal-barrier
formula rather than Lean's junk-value extension outside the proper-convex regime. -/
theorem universalBarrierVolume_pos
    (Q : Set E)
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (x : interior Q) :
    0 < universalBarrierVolume Q x := by
  -- The previous subsection gives nonempty interior for the based polar, hence positive volume.
  have hpolar_interior :
      (interior (polarSetAt Q (x : E))).Nonempty :=
    polarSetAt_interior_nonempty hQ_convex hQ_noAffineLine x.property
  have hpolar_pos : 0 < volume (polarSetAt Q (x : E)) :=
    Measure.measure_pos_of_nonempty_interior volume hpolar_interior
  -- Compactness of the based polar supplies the finiteness needed to pass to `toReal`.
  have hpolar_compact_convex : IsCompact (polarSetAt Q (x : E)) ∧ Convex ℝ (polarSetAt Q (x : E)) :=
    polarSetAt_isCompact_convex x.property
  have hpolar_compact : IsCompact (polarSetAt Q (x : E)) := hpolar_compact_convex.1
  have hpolar_lt_top : volume (polarSetAt Q (x : E)) < ⊤ :=
    hpolar_compact.measure_lt_top
  simpa [universalBarrierVolume] using ENNReal.toReal_pos hpolar_pos.ne' hpolar_lt_top.ne

/-- Helper for Theorem 5.4.2.2: on the empty domain, every barrier obligation is vacuous. -/
theorem empty_isSelfConcordantBarrierOnWith
    (ν : NNReal) (F : E → ℝ) :
    IsSelfConcordantBarrierOnWith (∅ : Set E) ν F := by
  -- The empty-domain branch is discharged directly because no pointwise obligation can fire.
  refine
    { toIsStandardSelfConcordantOn := ?_
      barrier_parameter_bound := ?_ }
  · refine
      { isOpen_domain := by simp
        contDiffOn := by simp
        convexOn := ?_
        third_deriv_bound := ?_ }
    · refine ⟨by simpa using (convex_empty : Convex ℝ (∅ : Set E)), ?_⟩
      intro x hx
      exact hx.elim
    · intro x hx u
      exact hx.elim
  · intro x hx u
    exact hx.elim

/-- Helper for Theorem 5.4.2.2: every constant function is a `0`-self-concordant barrier on the
whole space. -/
theorem constant_isSelfConcordantBarrierOnWith_univ
    (c : ℝ) :
    IsSelfConcordantBarrierOnWith (Set.univ : Set E) 0 (fun _ : E ↦ c) := by
  -- Reuse the quadratic-affine zero-self-concordance API specialized to a constant objective.
  have hself :
      IsSelfConcordantOnWith (Set.univ : Set E) 0 (fun _ : E ↦ c) := by
    simpa [quadraticAffineObjective] using
      (quadraticAffineObjective_isSelfConcordantOnWith_zero
        c (0 : E) (0 : E →L[ℝ] E) ContinuousLinearMap.isPositive_zero)
  refine
    { toIsStandardSelfConcordantOn := ?_
      barrier_parameter_bound := ?_ }
  · -- Increasing the self-concordance constant from `0` to `1` gives the standard owner.
    exact hself.of_le (by norm_num)
  · intro x hx u
    -- The constant objective has zero gradient and zero Hessian, so the barrier bound is exact.
    have hzero_selfAdjoint :
        IsSelfAdjoint (0 : E →L[ℝ] E) := by
      simpa using (IsSelfAdjoint.zero : IsSelfAdjoint (0 : E →L[ℝ] E))
    have hgrad :
        gradient (fun _ : E ↦ c) = fun _ : E ↦ (0 : E) := by
      simpa [quadraticAffineObjective] using
        quadraticAffineObjective_gradient_eq c (0 : E) (0 : E →L[ℝ] E) hzero_selfAdjoint
    have hhess :
        hessian (fun _ : E ↦ c) x = 0 := by
      simpa [quadraticAffineObjective] using
        quadraticAffineObjective_hessian_eq c (0 : E) (0 : E →L[ℝ] E) hzero_selfAdjoint x
    rw [hgrad, hhess]
    simp

/-- Helper for Theorem 5.4.2.2: when `E` has finrank `0`, the universal barrier ambient map is a
constant function on a subsingleton space, so the barrier parameter collapses to `0`. -/
theorem universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_finrank_zero
    (c₁ : ℝ) {Q : Set E} (hfin : Module.finrank ℝ E = 0) :
    IsSelfConcordantBarrierOnWith (interior Q) 0 (universalBarrierAmbient c₁ Q) := by
  letI : Subsingleton E := Module.finrank_zero_iff.mp hfin
  by_cases hdom : (interior Q).Nonempty
  · -- Route correction: the zero-finrank branch avoids the missing analytic bridge by reducing
    -- the ambient universal barrier to a constant function on `Set.univ`.
    have hdom_univ : interior Q = (Set.univ : Set E) := by
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        rcases hdom with ⟨y, hy⟩
        exact Subsingleton.elim y x ▸ hy
    have hfun :
        universalBarrierAmbient c₁ Q = fun _ : E ↦ universalBarrierAmbient c₁ Q 0 := by
      funext x
      exact congrArg (universalBarrierAmbient c₁ Q) (Subsingleton.elim x 0)
    simpa [hdom_univ, hfun] using
      constant_isSelfConcordantBarrierOnWith_univ (universalBarrierAmbient c₁ Q 0)
  · -- If the domain is empty, the barrier instance is completely vacuous.
    have hdom_empty : interior Q = (∅ : Set E) :=
      Set.not_nonempty_iff_eq_empty.mp hdom
    simpa [hdom_empty] using
      empty_isSelfConcordantBarrierOnWith (0 : NNReal) (universalBarrierAmbient c₁ Q)

/-- Helper for Theorem 5.4.2.2: on interior points, the exponential transform of the ambient
universal barrier is the corresponding power of the intrinsic volume term. -/
private lemma universalBarrierAmbient_expNegDiv_eq_volumePower
    {c₁ : ℝ} {ν : NNReal} {Q : Set E} {x : E}
    (hx : x ∈ interior Q)
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) :
    Real.exp (-(universalBarrierAmbient c₁ Q x / (ν : ℝ))) =
      (universalBarrierVolume Q ⟨x, hx⟩) ^ (-(c₁ / (ν : ℝ))) := by
  -- First reduce the ambient owner to the intrinsic `c₁ * log V(x)` formula on `interior Q`.
  have hvol_pos : 0 < universalBarrierVolume Q ⟨x, hx⟩ :=
    universalBarrierVolume_pos Q hQ_convex hQ_noAffineLine ⟨x, hx⟩
  calc
    Real.exp (-(universalBarrierAmbient c₁ Q x / (ν : ℝ)))
        = Real.exp (-(c₁ * Real.log (universalBarrierVolume Q ⟨x, hx⟩) / (ν : ℝ))) := by
            rw [universalBarrierAmbient_eq_universalBarrier hx, universalBarrier_eq_log_volume]
    -- Then rewrite the exponential into the canonical `rpow` normal form.
    _ = Real.exp (Real.log (universalBarrierVolume Q ⟨x, hx⟩) * (-(c₁ / (ν : ℝ)))) := by
          congr 1
          ring
    _ = (universalBarrierVolume Q ⟨x, hx⟩) ^ (-(c₁ / (ν : ℝ))) := by
          symm
          simpa [mul_comm] using
            (Real.rpow_def_of_pos hvol_pos (-(c₁ / (ν : ℝ))))

/-- The ambient volume-power owner that matches the source-side universal-barrier transform on
`interior Q`. Outside `interior Q` we use `0`, but the subsequent concavity statements are always
restricted to `interior Q`, so only the source-facing branch matters. -/
private def universalBarrierVolumePowerAmbient
    (c₁ : ℝ) (ν : NNReal) (Q : Set E) :
    E → ℝ :=
  fun x ↦
    if hx : x ∈ interior Q then
      (universalBarrierVolume Q ⟨x, hx⟩) ^ (-(c₁ / (ν : ℝ)))
    else
      0

/-- Helper for Theorem 5.4.2.2: on `interior Q`, the ambient exponential transform agrees with
the source-facing volume-power owner. -/
private theorem universalBarrierAmbient_expNegDiv_eq_volumePowerAmbient
    {c₁ : ℝ} {ν : NNReal} {Q : Set E}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) :
    Set.EqOn
      (fun x ↦ Real.exp (-(universalBarrierAmbient c₁ Q x / (ν : ℝ))))
      (universalBarrierVolumePowerAmbient c₁ ν Q)
      (interior Q) := by
  intro x hx
  -- On the domain, both owners reduce to the same intrinsic volume power.
  simpa [universalBarrierVolumePowerAmbient, hx] using
    (universalBarrierAmbient_expNegDiv_eq_volumePower hx hQ_convex hQ_noAffineLine)

/-- Helper for Theorem 5.4.2.2: concavity of the source-facing volume-power owner transports
directly to the ambient exponential transform required by the barrier API. -/
private theorem universalBarrierAmbient_expTransform_concave_of_volumePowerConcave
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hconc :
      ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient c₁ ν Q)) :
    ConcaveOn ℝ (interior Q)
      (fun x ↦ Real.exp (-(universalBarrierAmbient c₁ Q x / (ν : ℝ)))) := by
  -- Rewrite the exponential transform to the canonical volume-power owner on `interior Q`.
  refine hconc.congr ?_
  intro x hx
  simpa using
    (universalBarrierAmbient_expNegDiv_eq_volumePowerAmbient hQ_convex hQ_noAffineLine hx).symm

/-- Helper for Theorem 5.4.2.2: package the pointwise core data into the standard
self-concordance owner on `interior Q`. -/
private theorem
    universalBarrierAmbient_isStandardSelfConcordantOn_of_pointwiseCore
    {Q : Set E} {c₁ : ℝ}
    (hQ_convex : Convex ℝ Q)
    (hcont :
      ContDiffOn ℝ 3 (universalBarrierAmbient c₁ Q) (interior Q))
    (hquad :
      ∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (universalBarrierAmbient c₁ Q) x u))
    (hthird :
      ∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (universalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (universalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) :
    IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q) := by
  -- The pointwise Hessian and cubic estimates are exactly the fields of the standard owner.
  have hdom_open : IsOpen (interior Q) := isOpen_interior
  have hdom_convex : Convex ℝ (interior Q) := hQ_convex.interior
  have hC2 :
      ContDiffOn ℝ 2 (universalBarrierAmbient c₁ Q) (interior Q) :=
    hcont.of_le (by norm_num)
  refine
    { isOpen_domain := hdom_open
      contDiffOn := hcont
      convexOn := ?_
      third_deriv_bound := ?_ }
  · -- Convert Hessian quadratic-form nonnegativity into convexity on the open interior domain.
    refine (convexOn_iff_hessian_quadratic_form_nonneg hdom_open hdom_convex hC2).2 ?_
    intro x hx u
    simpa [real_inner_comm] using hquad x hx u
  · -- The cubic derivative field is already in the standard-self-concordance normal form.
    intro x hx u
    simpa using hthird x hx u

/-- Helper for Theorem 5.4.2.2: assemble the barrier owner directly from the pointwise
gradient-square estimate, without passing through a separate concavity theorem. -/
private theorem
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_pointwiseCore
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q))
    (hgrad :
      ∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (universalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (universalBarrierAmbient c₁ Q) x u)) :
    IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q) := by
  refine
    { toIsStandardSelfConcordantOn := hstd
      barrier_parameter_bound := ?_ }
  intro x hx u
  -- At each interior point, the standard owner gives Hessian positivity, so Lemma 5.3.1 turns
  -- the gradient-square estimate into the required barrier inequality.
  have hPos :
      (hessian (universalBarrierAmbient c₁ Q) x).IsPositive := hstd.hessian_isPositive hx
  exact
    (IsSelfConcordantBarrierOnWith.gradient_sq_le_mul_hessian_iff_barrier_bound hPos).2
      (fun v ↦ hgrad x hx v) u

/-- Helper for Theorem 5.4.2.2: the Chapter 5 logarithmic Taylor criterion assembles the barrier
owner for `universalBarrierAmbient c₁ Q` directly from standard self-concordance and the lower
Taylor bound on `interior Q`. -/
private theorem
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_standardAndLogarithmicTaylor
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q))
    (hν : 0 < (ν : ℝ))
    (hlog :
      ∀ {x y : E}, x ∈ interior Q → y ∈ interior Q →
        let t := 1 - (1 / (ν : ℝ)) * inner ℝ (∇ (universalBarrierAmbient c₁ Q) x) (y - x)
        0 < t ∧
          universalBarrierAmbient c₁ Q y ≥
            universalBarrierAmbient c₁ Q x - (ν : ℝ) * Real.log t) :
    IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q) := by
  -- Route correction: this packages the plan-6 owner directly through Theorem 5.3.7, without
  -- passing through the older pointwise-core or concavity repackaging route.
  refine
    (isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound hstd hν).2 ?_
  intro x y hx hy
  -- The input hypothesis is already in the exact Chapter 5 logarithmic-Taylor normal form.
  simpa using hlog hx hy

/-- Helper for Theorem 5.4.2.2: standard self-concordance together with concavity of the
source-facing volume-power owner yields the barrier owner for the ambient universal barrier. -/
private theorem
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_standardAndVolumeConcave
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q))
    (hconc :
      ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient c₁ ν Q))
    (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q) := by
  -- Transport the source-side concavity statement to the exponential transform seen by
  -- `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div`.
  have hconcExp :
      ConcaveOn ℝ (interior Q)
        (fun x ↦ Real.exp (-(universalBarrierAmbient c₁ Q x / (ν : ℝ)))) :=
    universalBarrierAmbient_expTransform_concave_of_volumePowerConcave
      hQ_convex hQ_noAffineLine hconc
  -- The chapter equivalence then turns the transformed concavity into the barrier owner.
  exact
    (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div hstd hν).2 hconcExp

/-- Helper for Theorem 5.4.2.2: the explicit source-facing ambient owner is globally identical to
the canonical ambient universal barrier. -/
@[simp] theorem explicitUniversalBarrierAmbient_eq_universalBarrierAmbient
    (c₁ : ℝ) (Q : Set E) :
    explicitUniversalBarrierAmbient c₁ Q = universalBarrierAmbient c₁ Q := by
  -- Both ambient owners use the same interior branch, so a pointwise split on membership closes
  -- the bridge once for all later differential-operator rewrites.
  funext x
  by_cases hx : x ∈ interior Q
  · simp [explicitUniversalBarrierAmbient, universalBarrierAmbient, universalBarrier, hx]
  · simp [explicitUniversalBarrierAmbient, universalBarrierAmbient, hx]

/-- Helper for Theorem 5.4.2.2: the line slice through an interior point stays in `interior Q`
on some explicit interval `|t| < ε` around `0`. -/
private theorem exists_pos_lineSliceRadius_mem_interior
    {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → x + t • u ∈ interior Q := by
  have hmem :
      {t : ℝ | x + t • u ∈ interior Q} ∈ nhds (0 : ℝ) :=
    lineMap_eventually_mem_interior hx u
  rw [Metric.mem_nhds_iff] at hmem
  rcases hmem with ⟨ε, hεpos, hsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro t ht
  have hball : t ∈ Metric.ball (0 : ℝ) ε := by
    -- On `ℝ`, the metric ball around `0` is exactly the absolute-value interval `|t| < ε`.
    simpa [Metric.ball, Real.dist_eq] using ht
  exact hsub hball

/-- Helper for Theorem 5.4.2.2: on a sufficiently small interval around `0`, the scalar line
slice of the explicit ambient owner is exactly the intrinsic `c₁ * log V` branch. -/
private theorem exists_pos_lineSliceRadius_eq_logVolumeAlongLine
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε →
      ∃ hxt : x + t • u ∈ interior Q,
        directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u t =
          c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩) := by
  rcases exists_pos_lineSliceRadius_mem_interior hx u with ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, ?_⟩
  intro t ht
  refine ⟨hε t ht, ?_⟩
  -- Inside the radius `ε`, the slice remains on the intended log-volume branch.
  simp [directionalSlice, explicitUniversalBarrierAmbient, hε t ht]

/-- Helper for Theorem 5.4.2.2: near `t = 0`, the explicit ambient owner stays on its log-volume
branch along the line `t ↦ x + t • u`. -/
private theorem explicitUniversalBarrierAmbient_eventuallyEq_logVolumeAlongLine
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E) :
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∃ hxt : x + t • u ∈ interior Q,
        explicitUniversalBarrierAmbient c₁ Q (x + t • u) =
          c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩) := by
  -- Route correction: freeze the `if x ∈ interior Q` branch once on a neighborhood of `0`
  -- instead of re-unfolding the ambient owner inside every slice calculation.
  filter_upwards [lineMap_eventually_mem_interior hx u] with t ht
  refine ⟨ht, ?_⟩
  -- Once the line stays in the interior branch, the source-facing owner is literally `c₁ log V`.
  simp [explicitUniversalBarrierAmbient, ht]

/-- Helper for Theorem 5.4.2.2: a barrier witness for `universalBarrierAmbient` packages the
local `C³`/Hessian/gradient data for the explicit ambient universal-barrier formula. -/
private theorem explicitUniversalBarrierAmbient_pointwiseData_of_barrier
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q)) :
    ∀ x ∈ interior Q,
      ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
        (∀ u, 0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
        (∀ u,
          |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
            2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
        (∀ u,
          (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  intro x hx
  -- Read the regularity and differential inequalities from the barrier owner on `interior Q`.
  have hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q) :=
    hbarrier.toIsStandardSelfConcordantOn
  have hcontAt :
      ContDiffAt ℝ 3 (universalBarrierAmbient c₁ Q) x :=
    hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds hx)
  have hquad :
      ∀ u, 0 ≤ inner ℝ u (hessian (universalBarrierAmbient c₁ Q) x u) := by
    intro u
    exact hstd.hessian_posSemidef hx u
  have hthird :
      ∀ u,
        |thirdDirectionalDerivative (universalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (universalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
    intro u
    simpa [one_mul, hessianLocalNorm] using hstd.third_deriv_bound hx u
  have hgrad :
      ∀ u,
        (inner ℝ (∇ (universalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (universalBarrierAmbient c₁ Q) x u) := by
    have hPos :
        (hessian (universalBarrierAmbient c₁ Q) x).IsPositive := hstd.hessian_isPositive hx
    exact
      (IsSelfConcordantBarrierOnWith.gradient_sq_le_mul_hessian_iff_barrier_bound
        (F := universalBarrierAmbient c₁ Q) (x := x) (μ := ν) hPos).1
        (hbarrier.barrier_parameter_bound hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The ambient owner and the explicit source-facing formula are definitionally the same map.
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hcontAt
  · intro u
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using
      hquad u
  · intro u
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient, one_mul, hessianLocalNorm]
      using hthird u
  · intro u
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using
      hgrad u

/-- Helper for Theorem 5.4.2.2: a barrier witness for `universalBarrierAmbient` forces concavity
of the source-facing volume-power owner on `interior Q`. -/
private theorem universalBarrierVolumePowerAmbient_concave_of_barrier
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q))
    (hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q))
    (hν : 0 < (ν : ℝ)) :
    ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient c₁ ν Q) := by
  -- First read concavity of the exponential transform from the barrier criterion.
  have hconcExp :
      ConcaveOn ℝ (interior Q)
        (fun x ↦ Real.exp (-(universalBarrierAmbient c₁ Q x / (ν : ℝ)))) :=
    (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div hstd hν).1 hbarrier
  -- Then rewrite that transform to the source-facing volume-power owner on `interior Q`.
  exact
    hconcExp.congr
      (universalBarrierAmbient_expNegDiv_eq_volumePowerAmbient hQ_convex hQ_noAffineLine)

/-- Helper for Theorem 5.4.2.2: once the ambient universal barrier is known to be standard
self-concordant and its source-facing volume power is concave, the full explicit pointwise core
for `explicitUniversalBarrierAmbient` follows by one barrier-to-pointwise packaging step. -/
private theorem explicitUniversalBarrierAmbient_pointwiseCore_of_standardAndVolumeConcave
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q))
    (hconc :
      ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient c₁ ν Q))
    (hν : 0 < (ν : ℝ)) :
    ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
      (∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
      (∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
      (∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  -- First assemble the barrier owner from the standard-self-concordance and concavity inputs.
  have hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν (universalBarrierAmbient c₁ Q) :=
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_standardAndVolumeConcave
      hQ_convex hQ_noAffineLine hstd hconc hν
  -- Then project the barrier fields back to the explicit source-facing ambient formula.
  have hpointwise :
      ∀ x ∈ interior Q,
        ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
          (∀ u, 0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
          (∀ u,
            |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
              2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
          (∀ u,
            (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
              (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) :=
    explicitUniversalBarrierAmbient_pointwiseData_of_barrier hbarrier
  have hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) :=
    explicitUniversalBarrierAmbient_contDiffOn_of_pointwiseData (by
      intro x hx
      exact (hpointwise x hx).1)
  refine ⟨hcont, ?_, ?_, ?_⟩
  · -- The projected pointwise package already contains the Hessian quadratic-form nonnegativity.
    intro x hx u
    exact (hpointwise x hx).2.1 u
  · -- The cubic third-derivative estimate is likewise part of the same pointwise package.
    intro x hx u
    exact (hpointwise x hx).2.2.1 u
  · -- Finally read off the barrier-parameter inequality from the projected pointwise package.
    intro x hx u
    exact (hpointwise x hx).2.2.2 u

/-- Helper for Theorem 5.4.2.2: pointwise `C³` control and the standard scalar slice inequalities
package directly into the standard self-concordance owner on `interior Q`. -/
private theorem
    explicitUniversalBarrierAmbient_standardSelfConcordant_of_contDiffAtAndStandardSliceData
    {Q : Set E} {c₁ : ℝ}
    (hQ_convex : Convex ℝ Q)
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hsliceStd :
      ∀ x ∈ interior Q, ∀ u,
        let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
        0 ≤ iteratedDeriv 2 φ 0 ∧
          |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) :
    IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient c₁ Q) := by
  have hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) :=
    explicitUniversalBarrierAmbient_contDiffOn_of_pointwiseData hcontAt
  have hquad :
      ∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (universalBarrierAmbient c₁ Q) x u) := by
    intro x hx u
    let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    have hslice_xu := hsliceStd x hx u
    dsimp [φ] at hslice_xu
    rcases
      directionalSliceDerivativesAtZero_eq_ambientOwners
        (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) (hcontAt x hx) with
      ⟨_, hsecond, _⟩
    have hquadExplicit :
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) := by
      -- The scalar second-derivative lower bound is exactly Hessian quadratic-form nonnegativity.
      rw [← hsecond]
      exact hslice_xu.1
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hquadExplicit
  have hthird :
      ∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (universalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (universalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
    intro x hx u
    let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    have hslice_xu := hsliceStd x hx u
    dsimp [φ] at hslice_xu
    rcases
      directionalSliceDerivativesAtZero_eq_ambientOwners
        (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) (hcontAt x hx) with
      ⟨_, hsecond, hthird⟩
    have hthirdExplicit :
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
      -- Rewrite the scalar cubic bound into the explicit ambient local-norm owner first.
      calc
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u|
            = |iteratedDeriv 3 φ 0| := by
                rw [← hthird]
        _ ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := hslice_xu.2
        _ = 2 * (Real.sqrt (inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)))
              ^ (3 : ℕ) := by
                rw [hsecond]
        _ = 2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
                rw [hessianLocalNorm_def]
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hthirdExplicit
  have hcontAmbient :
      ContDiffOn ℝ 3 (universalBarrierAmbient c₁ Q) (interior Q) := by
    -- Normalize the source-facing ambient owner back to the canonical owner before packaging.
    simpa [explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hcont
  -- The owner-level standard-self-concordance constructor consumes the pointwise Hessian and
  -- cubic bounds once the ambient owner is normalized.
  exact
    universalBarrierAmbient_isStandardSelfConcordantOn_of_pointwiseCore
      hQ_convex hcontAmbient hquad hthird

/-- Helper for Theorem 5.4.2.2: an intrinsic interval-local slice formula transports to the
ambient directional slice near `t = 0`. -/
private theorem directionalSlice_eventuallyEq_intrinsicLogVolumeLineSlice
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E)
    {ε : ℝ} (hεpos : 0 < ε) {ψ : ℝ → ℝ}
    (hψeq :
      ∀ t : ℝ, |t| < ε →
        ∃ hxt : x + t • u ∈ interior Q,
          ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) :
    directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u =ᶠ[nhds (0 : ℝ)] ψ := by
  rcases exists_pos_lineSliceRadius_eq_logVolumeAlongLine (c₁ := c₁) (Q := Q) (x := x) hx u with
    ⟨η, hηpos, hηeq⟩
  let δ : ℝ := min ε η
  have hδpos : 0 < δ := by
    -- Intersect the two interval-local descriptions on the smaller common radius.
    exact lt_min hεpos hηpos
  have hδball : ∀ᶠ t : ℝ in nhds (0 : ℝ), t ∈ Metric.ball (0 : ℝ) δ := by
    exact Metric.ball_mem_nhds (0 : ℝ) hδpos
  have hδnhds : ∀ᶠ t : ℝ in nhds (0 : ℝ), |t| < δ := by
    -- On `ℝ`, the metric ball around `0` is exactly the absolute-value interval `|t| < δ`.
    simpa [Metric.ball, Real.dist_eq] using hδball
  filter_upwards [hδnhds] with t ht
  have htε : |t| < ε := lt_of_lt_of_le ht (min_le_left _ _)
  have htη : |t| < η := lt_of_lt_of_le ht (min_le_right _ _)
  rcases hηeq t htη with ⟨hxt, hslice_t⟩
  rcases hψeq t htε with ⟨hxt', hψt⟩
  have hsub : (⟨x + t • u, hxt⟩ : interior Q) = ⟨x + t • u, hxt'⟩ := by
    ext
    rfl
  -- Both descriptions reduce to the same intrinsic `c₁ * log V` slice on the common interval.
  calc
    directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u t
        = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩) := hslice_t
    _ = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt'⟩) := by
          simpa using
            congrArg (fun y : interior Q ↦ c₁ * Real.log (universalBarrierVolume Q y)) hsub
    _ = ψ t := hψt.symm

/-- Helper for Theorem 5.4.2.2: interval-local intrinsic log-volume slice data upgrades to the
ambient standard directional-slice interface already used by the packaging theorems. -/
private theorem directionalSlice_standardBounds_of_intrinsicLogVolumeLineSlice
    {Q : Set E} {c₁ : ℝ} {x : E} (hx : x ∈ interior Q) (u : E)
    {ε : ℝ} (hεpos : 0 < ε) {ψ : ℝ → ℝ}
    (hψeq :
      ∀ t : ℝ, |t| < ε →
        ∃ hxt : x + t • u ∈ interior Q,
          ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩))
    (hψsecond : 0 ≤ iteratedDeriv 2 ψ 0)
    (hψthird :
      |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) :
    let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    0 ≤ iteratedDeriv 2 φ 0 ∧
      |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := by
  let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
  -- First replace the ambient directional slice by the intrinsic log-volume slice near `0`.
  have heq : φ =ᶠ[nhds (0 : ℝ)] ψ :=
    directionalSlice_eventuallyEq_intrinsicLogVolumeLineSlice
      (c₁ := c₁) (Q := Q) (x := x) hx u hεpos hψeq
  -- Then transport the second- and third-derivative owners across that neighborhood identity.
  have hsecond_eq : iteratedDeriv 2 φ 0 = iteratedDeriv 2 ψ 0 := by
    simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 2 heq
  have hthird_eq : iteratedDeriv 3 φ 0 = iteratedDeriv 3 ψ 0 := by
    simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 3 heq
  -- The intrinsic scalar inequalities now rewrite directly to the ambient directional slice.
  refine ⟨?_, ?_⟩
  · rw [hsecond_eq]
    exact hψsecond
  · rw [hsecond_eq, hthird_eq]
    exact hψthird

/-- Helper for Theorem 5.4.2.2: interval-local intrinsic log-volume slice data upgrades to the
ambient standard directional-slice interface already used by the packaging theorems. -/
private theorem
    explicitUniversalBarrierAmbient_standardSliceData_of_intrinsicLogVolumeLineSlice
    {Q : Set E} {c₁ : ℝ}
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hsliceIntrinsic :
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          ContDiffOn ℝ 3 ψ (Set.Ioo (-ε) ε) ∧
          (∀ t : ℝ, |t| < ε →
            ∃ hxt : x + t • u ∈ interior Q,
              ψ t = c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩)) ∧
          0 ≤ iteratedDeriv 2 ψ 0 ∧
            |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ)) :
    ∀ x ∈ interior Q,
      ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
        ∀ u,
          let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
          0 ≤ iteratedDeriv 2 φ 0 ∧
            |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := by
  intro x hx
  refine ⟨hcontAt x hx, ?_⟩
  intro u
  rcases hsliceIntrinsic x hx u with ⟨ε, hεpos, ψ, hψcont, hψeq, hψsecond, hψthird⟩
  -- The `ContDiffAt` component is already part of the source-facing hypothesis.
  have _hψ0 : ContDiffAt ℝ 3 ψ 0 := by
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
      -- The interval-local slice theorem is centered at the base point `t = 0`.
      constructor <;> nlinarith
    exact hψcont.contDiffAt (isOpen_Ioo.mem_nhds h0)
  -- The derivative inequalities themselves are handled by the dedicated transport helper.
  simpa using
    directionalSlice_standardBounds_of_intrinsicLogVolumeLineSlice
      (Q := Q) (c₁ := c₁) (x := x) hx u hεpos hψeq hψsecond hψthird

/-- Helper for Theorem 5.4.2.2: pointwise `C³` control and the pointwise Hessian/third-derivative
owners imply the standard scalar slice inequalities at each interior base point. -/
private theorem explicitUniversalBarrierAmbient_standardSliceData_of_pointwiseCore
    {Q : Set E} {c₁ : ℝ}
    (hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q))
    (hquad :
      ∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))
    (hthird :
      ∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) :
    ∀ x ∈ interior Q,
      ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x ∧
        ∀ u,
          let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
          0 ≤ iteratedDeriv 2 φ 0 ∧
            |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := by
  intro x hx
  have hcontAt : ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x := by
    -- The pointwise `C³` owner is read off from the open-domain `ContDiffOn` hypothesis.
    exact hcont.contDiffAt (isOpen_interior.mem_nhds hx)
  refine ⟨hcontAt, ?_⟩
  intro u
  -- Rewrite the scalar slice derivatives to the ambient Hessian and third-derivative owners.
  rcases
    directionalSliceDerivativesAtZero_eq_ambientOwners
      (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) hcontAt with
    ⟨_, hsecond, hthirdEq⟩
  dsimp
  refine ⟨?_, ?_⟩
  · rw [hsecond]
    exact hquad x hx u
  · calc
      |iteratedDeriv 3 (directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u) 0|
          = |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| := by
              rw [hthirdEq]
      _ ≤ 2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) :=
            hthird x hx u
      _ = 2 * (Real.sqrt
            (inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u))) ^ (3 : ℕ) := by
              rw [hessianLocalNorm_def]
      _ = 2 * (Real.sqrt
            (iteratedDeriv 2 (directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u) 0))
            ^ (3 : ℕ) := by
              rw [← hsecond]

/-- Helper for Theorem 5.4.2.2: the imported source-facing pointwise core theorem packages into
the weaker simultaneous owner consisting of standard slice data for
`explicitUniversalBarrierAmbient` and concavity of the matching volume-power transform. -/
private theorem
    exists_absolute_constants_universalBarrier_standardSliceDataAndVolumePowerConcave_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        (∀ x ∈ interior Q,
          ContDiffAt ℝ 3 F x ∧
            ∀ u,
              let φ := directionalSlice F x u
              0 ≤ iteratedDeriv 2 φ 0 ∧
                |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) ∧
          ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases exists_absolute_constants_universalBarrier_pointwiseCore_of_nonemptyInterior with
    ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      ContDiffOn ℝ 3 F (interior Q) ∧
        (∀ x ∈ interior Q, ∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
        (∀ x ∈ interior Q, ∀ u,
          |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
        (∀ x ∈ interior Q, ∀ u,
          (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian F x u)) := by
    -- Reuse the imported source-facing pointwise core as the only analytic input.
    simpa [F, ν] using hcore hfin hQint hQ_convex hQ_noAffineLine
  rcases hcore' with ⟨hcont, hquad, hthird, hgrad⟩
  have hsliceStd :
      ∀ x ∈ interior Q,
        ContDiffAt ℝ 3 F x ∧
          ∀ u,
            let φ := directionalSlice F x u
            0 ≤ iteratedDeriv 2 φ 0 ∧
              |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) :=
    explicitUniversalBarrierAmbient_standardSliceData_of_pointwiseCore hcont hquad hthird
  have hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient (c₁ : ℝ) Q) :=
    -- Package the explicit pointwise data into the canonical ambient owner once.
    explicitUniversalBarrierAmbient_standardSelfConcordant_of_contDiffAtAndStandardSliceData
      hQ_convex
      (by
        intro x hx
        exact (hsliceStd x hx).1)
      (by
        intro x hx u
        exact (hsliceStd x hx).2 u)
  have hgradAmbient :
      ∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (universalBarrierAmbient (c₁ : ℝ) Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (universalBarrierAmbient (c₁ : ℝ) Q) x u) := by
    -- Normalize the explicit owner to `universalBarrierAmbient` exactly at the barrier step.
    simpa [F, explicitUniversalBarrierAmbient_eq_universalBarrierAmbient] using hgrad
  have hbarrier :
      IsSelfConcordantBarrierOnWith (interior Q) ν
        (universalBarrierAmbient (c₁ : ℝ) Q) :=
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_pointwiseCore hstd hgradAmbient
  have hν_pos_nnreal : (0 : NNReal) < ν := by
    -- The universal-barrier parameter is strictly positive in the positive-finrank branch.
    dsimp [ν]
    exact mul_pos (pos_iff_ne_zero.mpr (Units.ne_zero c₂)) (by exact_mod_cast hfin)
  have hν_pos : 0 < (ν : ℝ) := by
    exact_mod_cast hν_pos_nnreal
  have hconc :
      ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) :=
    -- Once the barrier owner is assembled, concavity is the chapter-level projection theorem.
    universalBarrierVolumePowerAmbient_concave_of_barrier
      hQ_convex hQ_noAffineLine hstd hbarrier hν_pos
  exact ⟨hsliceStd, hconc⟩

/-- Helper for Theorem 5.4.2.2: the analytic core is the simultaneous standard
self-concordance/volume-power-concavity statement on `interior Q`. -/
-- Route correction: the unresolved analytic work is now isolated at the source-facing owner
-- level, so this theorem now packages the weaker standard slice data into standard
-- self-concordance and keeps concavity on the canonical volume-power owner directly.
private theorem
    exists_absolute_constants_universalBarrierStandardAndVolumeConcave_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient (c₁ : ℝ) Q) ∧
          ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
  rcases
    exists_absolute_constants_universalBarrier_standardSliceDataAndVolumePowerConcave_of_nonemptyInterior
      with ⟨c₁, c₂, hdata⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hdata' :
      (∀ x ∈ interior Q,
        ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient (c₁ : ℝ) Q) x ∧
          ∀ u,
            let φ := directionalSlice (explicitUniversalBarrierAmbient (c₁ : ℝ) Q) x u
            0 ≤ iteratedDeriv 2 φ 0 ∧
              |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ)) ∧
        ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
    simpa [ν] using hdata hfin hQint hQ_convex hQ_noAffineLine
  rcases hdata' with ⟨hsliceStd, hconc⟩
  -- Package the weaker slice data into the standard self-concordance owner.
  have hstd :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient (c₁ : ℝ) Q) :=
    explicitUniversalBarrierAmbient_standardSelfConcordant_of_contDiffAtAndStandardSliceData
      hQ_convex
      (by
        intro x hx
        exact (hsliceStd x hx).1)
      (by
        intro x hx u
        exact (hsliceStd x hx).2 u)
  exact ⟨hstd, hconc⟩

/-- Helper for Theorem 5.4.2.2: once the analytic core is available, the barrier owner follows
from the chapter concavity criterion for `x ↦ exp (-(U(x) / ν))`. -/
private theorem exists_absolute_constants_universalBarrierBarrier_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  rcases exists_absolute_constants_universalBarrierStandardAndVolumeConcave_of_nonemptyInterior with
    ⟨c₁, c₂, hcore⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
  have hcore' :
      IsStandardSelfConcordantOn (interior Q) (universalBarrierAmbient (c₁ : ℝ) Q) ∧
        ConcaveOn ℝ (interior Q) (universalBarrierVolumePowerAmbient (c₁ : ℝ) ν Q) := by
    simpa [ν] using hcore hfin hQint hQ_convex hQ_noAffineLine
  rcases hcore' with ⟨hstd, hconc⟩
  have hν_pos_nnreal : (0 : NNReal) < ν := by
    -- Both factors in the barrier parameter are strictly positive in the nonempty branch.
    dsimp [ν]
    exact mul_pos (pos_iff_ne_zero.mpr (Units.ne_zero c₂)) (by exact_mod_cast hfin)
  have hν_pos : 0 < (ν : ℝ) := by
    exact_mod_cast hν_pos_nnreal
  -- Assemble the barrier owner from the standard-self-concordance and concavity components.
  simpa [ν] using
    universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_standardAndVolumeConcave
      hQ_convex hQ_noAffineLine hstd hconc hν_pos

/-- Helper for Theorem 5.4.2.2: the remaining analytic frontier is the local pointwise calculus
package for `explicitUniversalBarrierAmbient` at each interior base point. -/
private theorem exists_absolute_constants_universalBarrier_pointwiseDataAtInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        let F : E → ℝ := explicitUniversalBarrierAmbient (c₁ : ℝ) Q
        let ν : NNReal := (c₂ : NNReal) * Module.finrank ℝ E
        ∀ x ∈ interior Q,
          ContDiffAt ℝ 3 F x ∧
            (∀ u, 0 ≤ inner ℝ u (hessian F x u)) ∧
            (∀ u,
              |thirdDirectionalDerivative F x u| ≤ 2 * hessianLocalNorm F x u ^ (3 : ℕ)) ∧
            (∀ u,
              (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
                (ν : ℝ) * inner ℝ u (hessian F x u)) := by
  rcases exists_absolute_constants_universalBarrierBarrier_of_nonemptyInterior with
    ⟨c₁, c₂, hbarrier⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  -- Once the barrier owner exists, the local source-facing pointwise package is just projection.
  simpa using
    explicitUniversalBarrierAmbient_pointwiseData_of_barrier
      (hbarrier hfin hQint hQ_convex hQ_noAffineLine)

/-- Helper for Theorem 5.4.2.2: in the nonempty-interior positive-dimensional regime, the
universal barrier is assembled directly from the pointwise core data. -/
private theorem exists_absolute_constants_universalBarrier_positiveFinrank_of_nonemptyInterior :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        (interior Q).Nonempty →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  rcases exists_absolute_constants_universalBarrierBarrier_of_nonemptyInterior with
    ⟨c₁, c₂, hbarrier⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQint hQ_convex hQ_noAffineLine
  -- The positive-dimensional branch is now exactly the barrier-owner theorem assembled above.
  exact hbarrier hfin hQint hQ_convex hQ_noAffineLine

/-- Helper for Theorem 5.4.2.2: isolate the genuinely positive-dimensional universal-barrier
bridge as the only remaining analytic frontier after splitting off the vacuous empty-domain case. -/
theorem exists_absolute_constants_universalBarrier_positiveFinrank :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        0 < Module.finrank ℝ E →
        Convex ℝ Q →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) := by
  rcases exists_absolute_constants_universalBarrier_positiveFinrank_of_nonemptyInterior with
    ⟨c₁, c₂, hpositive⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hfin hQ_convex hQ_noAffineLine
  by_cases hQint : (interior Q).Nonempty
  · -- The source regime is the nonempty-interior branch proved above.
    exact hpositive hfin hQint hQ_convex hQ_noAffineLine
  · -- Outside that regime, the barrier owner is vacuous on the empty domain.
    have hdom_empty : interior Q = (∅ : Set E) :=
      Set.not_nonempty_iff_eq_empty.mp hQint
    simpa [hdom_empty] using
      empty_isSelfConcordantBarrierOnWith
        (((c₂ : NNReal) * Module.finrank ℝ E : NNReal))
        (universalBarrierAmbient (c₁ : ℝ) Q)

-- Proof sketch: use the universal-barrier volume definition from Definition 5.4.2.2 and the
-- sharp one-dimensional marginal moment inequalities from the preceding subsection. These yield
-- standard self-concordance for `x ↦ c₁ log V(x)` on `interior Q` together with the barrier
-- gradient bound of order `n`, uniformly for absolute positive constants `c₁` and `c₂`. The
-- intrinsic formulation expresses this parameter as `c₂ * Module.finrank ℝ E`, which
-- specializes to the textbook `c₂ * n` on `EuclideanSpace ℝ (Fin n)`.
/-- Theorem 5.4.2.2, stated with the intrinsic owner and its ambient bridge: there exist absolute
positive constants `c₁` and `c₂` such that for every proper convex set `Q` in a finite-dimensional
real inner-product space `E`, the ambient bridge of the universal barrier
`x ↦ c₁ * log (V(x))` is a `((c₂ : NNReal) * Module.finrank ℝ E)`-self-concordant barrier on
`interior Q` under the source hypothesis that `interior Q` is nonempty. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `(c₂ * n)` parameter. -/
theorem exists_absolute_constants_universalBarrier_isSelfConcordantBarrierOnWith :
    ∃ c₁ c₂ : NNRealˣ,
      ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        {Q : Set E},
        (Convex ℝ Q) →
        (∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q) →
        (interior Q).Nonempty →
        IsSelfConcordantBarrierOnWith (interior Q)
          ((c₂ : NNReal) * Module.finrank ℝ E)
          (universalBarrierAmbient (c₁ : ℝ) Q) :=
by
  rcases exists_absolute_constants_universalBarrier_positiveFinrank with ⟨c₁, c₂, hpositive⟩
  refine ⟨c₁, c₂, ?_⟩
  intro E _ _ _ Q hQ_convex hQ_noAffineLine hQ_interior
  by_cases hfin : Module.finrank ℝ E = 0
  · -- The degenerate branch is fully reduced to the constant-barrier helper proved above.
    simpa [hfin] using
      universalBarrierAmbient_isSelfConcordantBarrierOnWith_of_finrank_zero (c₁ : ℝ) hfin
  · -- Route correction: only the positive-dimensional bridge remains here.
    have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hfin
    exact hpositive hfin_pos hQ_convex hQ_noAffineLine

end
