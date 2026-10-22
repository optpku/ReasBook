/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Example_16_2.Shared
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_12

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal unitInterval

noncomputable section

/-- Helper for Example 16.2: the canonical owner law has characteristic function exactly equal,
as a function, to the normalized Gaussian-over-`√Gamma` CFP from the shared file. -/
private theorem gaussianOverSqrtGammaLaw_charFun_eq_fun
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    charFun (((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ)) =
      gaussianOverSqrtGammaCFP σ2 θ r := by
  -- Proof comment: package the pointwise characteristic-function computation into a reusable
  -- function equality so the owner/CFP transport lemmas all rewrite through the same bridge.
  funext t
  exact gaussianOverSqrtGammaLaw_charFun_eq σ2 θ r hσ2 hθ hr t

/-- Helper for Example 16.2: Theorem 16.12 closes owner-law infinite divisibility as soon as the
owner characteristic function itself is known to be infinitely divisible. -/
private theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_ownerCharFun
    (σ2 : ℝ≥0) (θ r : ℝ) (hθ : 0 < θ) (hr : 0 < r)
    (hownerCFP :
      IsInfinitelyDivisibleCFP
        (charFun (((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ)))) :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
  -- Proof comment: this is the owner-side form of Theorem 16.12, separated so the remaining
  -- frontier can be phrased as an owner characteristic-function statement instead of a transport
  -- script fragment.
  exact isInfinitelyDivisible_of_charFun_isInfinitelyDivisibleCFP hownerCFP

/-- Helper for Example 16.2: once the canonical characteristic function
`gaussianOverSqrtGammaCFP` is known to be infinitely divisible, Theorem 16.12 transports that
fact back to the canonical owner law. -/
private theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_cfp
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hcfp : IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
  have hownerCFP :
      IsInfinitelyDivisibleCFP
        (charFun (((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ))) := by
    -- Proof comment: rewrite the owner characteristic function to the canonical CFP before
    -- invoking the owner-side bridge from Theorem 16.12.
    simpa [gaussianOverSqrtGammaLaw_charFun_eq_fun σ2 θ r hσ2 hθ hr] using hcfp
  -- Proof comment: the only remaining work after the rewrite is the owner-side Theorem 16.12
  -- transport packaged in the previous helper.
  exact gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_ownerCharFun σ2 θ r hθ hr hownerCFP

/-- Helper for Example 16.2: the owner-law characteristic function is infinitely divisible
exactly when the normalized Gaussian-over-`√Gamma` CFP is. -/
private theorem gaussianOverSqrtGammaLaw_charFun_isInfinitelyDivisible_iff_cfp
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    IsInfinitelyDivisibleCFP
        (charFun (((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ))) ↔
      IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  -- Proof comment: this is the owner/CFP rewrite packaged as a single reusable equivalence, so
  -- the remaining frontier can be stated without duplicating function-extensionality arguments.
  simp [gaussianOverSqrtGammaLaw_charFun_eq_fun σ2 θ r hσ2 hθ hr]

/-- Helper for Example 16.2: owner-law infinite divisibility transports directly to the normalized
Gaussian-over-`√Gamma` characteristic function. -/
private theorem gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_owner
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (howner : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw σ2 θ r hθ hr)) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  -- Proof comment: transport owner-law infinite divisibility to its characteristic function and
  -- then rewrite that characteristic function to the normalized canonical CFP.
  exact
    (gaussianOverSqrtGammaLaw_charFun_isInfinitelyDivisible_iff_cfp σ2 θ r hσ2 hθ hr).1
      (MeasureTheory.ProbabilityMeasure.charFun_isInfinitelyDivisible howner)

/-- Helper for Example 16.2: for the canonical Gaussian-over-`√Gamma` law, infinite divisibility
of the owner law and of its normalized characteristic function are equivalent. -/
private theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible_iff_cfp
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) ↔
      IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  constructor
  · intro howner
    -- Proof comment: this is the owner-to-CFP transport direction isolated in the previous
    -- helper so the remaining frontier stays concentrated in one place.
    exact gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_owner σ2 θ r hσ2 hθ hr howner
  · intro hcfp
    -- Proof comment: the reverse direction is exactly the owner-side transport lemma above.
    exact gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_cfp σ2 θ r hσ2 hθ hr hcfp

/-- Helper for Example 16.2: any `ℕ+`-indexed characteristic-function root approximation of
`gaussianOverSqrtGammaCFP σ2 θ r` already proves infinite divisibility of that canonical
Gaussian-over-`√Gamma` characteristic function. -/
private theorem gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_rootApprox
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hroot :
      ∃ ψSeq : ℕ+ → ℝ → ℂ,
        (∀ n : ℕ+, IsCFP (ψSeq n)) ∧
          ∀ t : ℝ,
            Filter.Tendsto (fun n : ℕ+ ↦ (ψSeq n t) ^ (n : ℕ)) Filter.atTop
              (nhds (gaussianOverSqrtGammaCFP σ2 θ r t))) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP σ2 θ r) := by
  have hcont : ContinuousAt (gaussianOverSqrtGammaCFP σ2 θ r) 0 := by
    rcases gaussianOverSqrtGammaCFP_isCFP σ2 θ r hσ2 hθ hr with ⟨μ, hμ⟩
    -- Proof comment: every characteristic function of a probability law is continuous at `0`, so
    -- the canonical Gaussian-over-`√Gamma` transform inherits continuity at the origin.
    simpa [hμ] using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt
  -- Proof comment: Corollary 16.8 is exactly the bridge from a positive-integer root
  -- approximation to infinite divisibility of the limiting characteristic function.
  exact
    (isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto
      (φ := gaussianOverSqrtGammaCFP σ2 θ r) hcont).2 hroot

/-- Helper for Example 16.2: an explicit `ℕ+`-indexed characteristic-function root
approximation of the exact unit Gaussian-over-`√Gamma` CFP already closes the corresponding unit
owner law. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_of_rootApprox
    (r : ℝ) (hr : 0 < r)
    (hroot :
      ∃ ψSeq : ℕ+ → ℝ → ℂ,
        (∀ n : ℕ+, IsCFP (ψSeq n)) ∧
          ∀ t : ℝ,
            Filter.Tendsto (fun n : ℕ+ ↦ (ψSeq n t) ^ (n : ℕ)) Filter.atTop
              (nhds (gaussianOverSqrtGammaCFP 1 1 r t))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  have hcfp : IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
    -- Proof comment: the previous root-approximation bridge already proves infinite divisibility
    -- of the exact unit characteristic function.
    exact
      gaussianOverSqrtGammaCFP_isInfinitelyDivisible_of_rootApprox
        1 1 r zero_lt_one zero_lt_one hr hroot
  -- Proof comment: once the unit characteristic function is infinitely divisible, the earlier
  -- owner/CFP transport closes the exact unit owner law immediately.
  exact
    gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_cfp
      1 1 r zero_lt_one zero_lt_one hr hcfp

/-- Helper for Example 16.2: the Gaussian-over-`√Gamma` ratio map is almost everywhere
measurable under the law hypotheses. -/
private lemma ratioGaussianSqrtGamma_aemeasurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {σ2 : ℝ≥0} {θ r : ℝ}
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    AEMeasurable (fun ω ↦ X ω / Real.sqrt (Y ω)) P := by
  -- Proof comment: the Gaussian and Gamma laws already provide a.e.-measurability of the two
  -- coordinates, so the ratio map is assembled from measurable division and `sqrt`.
  simpa using hX.aemeasurable.div hY.aemeasurable.sqrt

/-- Helper for Example 16.2: the pushforward law of the ratio map `ω ↦ X ω / √(Y ω)` matches the
canonical owner law `gaussianOverSqrtGammaLaw` once the Gaussian and Gamma marginals are
identified. -/
private theorem ratioGaussianSqrtGamma_map_eq_ownerLaw
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    let Z : Ω → ℝ := fun ω ↦ X ω / Real.sqrt (Y ω)
    let hZ : AEMeasurable Z P := ratioGaussianSqrtGamma_aemeasurable hX hY
    (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) =
      gaussianOverSqrtGammaLaw σ2 θ r hθ hr := by
  dsimp
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  -- Proof comment: both candidate owner laws have the same characteristic function
  -- `gaussianOverSqrtGammaCFP`, so characteristic-function extensionality identifies them.
  rw [ratioGaussianSqrtGamma_map_charFun_eq (P := P) (X := X) (Y := Y)
    (ratioGaussianSqrtGamma_aemeasurable hX hY) hXY σ2 θ r hσ2 hθ hr hX hY t]
  exact (gaussianOverSqrtGammaLaw_charFun_eq σ2 θ r hσ2 hθ hr t).symm

/-- Helper for Example 16.2: scaling a law by multiplication with `a` is implemented as a
probability-measure pushforward. -/
private noncomputable def scaleLaw (a : ℝ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map μ
    ((measurable_const.mul measurable_id).aemeasurable :
      AEMeasurable (fun x : ℝ ↦ a * x) (μ : Measure ℝ))

/-- Helper for Example 16.2: the unit-rate Gamma law scaled by `1 / θ` has the Gamma law with
rate `θ`. -/
private theorem gammaMeasure_unitRate_map_div_eq_gammaMeasure
    (θ r : ℝ) (hθ : 0 < θ) (hr : 0 < r) :
    Measure.map (fun y : ℝ ↦ y / θ) (gammaMeasure r 1) = gammaMeasure r θ := by
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure r θ) := isProbabilityMeasure_gammaMeasure hr hθ
  apply Measure.ext_of_charFun
  ext t
  -- Proof comment: identify the pushforward by comparing the explicit Gamma characteristic
  -- functions after rewriting division as multiplication by `θ⁻¹`.
  calc
    charFun (Measure.map (fun y : ℝ ↦ y / θ) (gammaMeasure r 1)) t
        = charFun (gammaMeasure r 1) (θ⁻¹ * t) := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              (MeasureTheory.charFun_map_mul (μ := gammaMeasure r 1) θ⁻¹ t)
    _ = (1 - (((θ : ℂ)⁻¹ * (t : ℂ)) / 1) * Complex.I) ^ (-r : ℂ) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (charFun_gammaMeasure r 1 hr zero_lt_one (θ⁻¹ * t))
    _ = (1 - (t / θ) * Complex.I) ^ (-r : ℂ) := by
          congr 1
          field_simp [hθ.ne']
    _ = charFun (gammaMeasure r θ) t := by
          rw [charFun_gammaMeasure r θ hr hθ t]

/-- Helper for Example 16.2: the canonical Gamma law lives on `[0, ∞)` almost surely. -/
private lemma ae_nonneg_gammaMeasure_rate
    (r θ : ℝ) :
    ∀ᵐ y ∂ gammaMeasure r θ, 0 ≤ y := by
  rw [gammaMeasure, ae_withDensity_iff (by
    simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal r θ))]
  filter_upwards with y hy
  -- Proof comment: the Gamma density vanishes on the negative half-line, so negative values are
  -- null under `gammaMeasure`.
  by_contra hy_neg
  exact hy (gammaPDF_of_neg (lt_of_not_ge hy_neg))

/-- Helper for Example 16.2: scalar pushforwards commute with additive convolution powers. -/
private theorem map_mul_pow_eq_map_pow_mul
    (μ : ProbabilityMeasure ℝ) (a : ℝ) (n : ℕ+) :
    scaleLaw a μ ^ (n : ℕ) = scaleLaw a (μ ^ (n : ℕ)) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  ext t
  -- Proof comment: compare both laws through their characteristic functions; scaling sends `t`
  -- to `a * t`, and `charFun_pow` records the convolution power.
  calc
    charFun (((scaleLaw a μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) t
        = charFun (((scaleLaw a μ : ProbabilityMeasure ℝ) : Measure ℝ)) t ^ (n : ℕ) := by
            simpa using
              congrArg
                (fun f : ℝ → ℂ ↦ f t)
                (ProbabilityMeasure.charFun_pow (scaleLaw a μ) (n : ℕ))
    _ = charFun (μ : Measure ℝ) (a * t) ^ (n : ℕ) := by
          exact congrArg (fun z : ℂ ↦ z ^ (n : ℕ)) <| by
            simpa [scaleLaw] using (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) a t)
    _ = charFun (((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ)) (a * t) := by
          symm
          simpa using
            congrArg (fun f : ℝ → ℂ ↦ f (a * t)) (ProbabilityMeasure.charFun_pow μ (n : ℕ))
    _ = charFun (((scaleLaw a (μ ^ (n : ℕ)) : ProbabilityMeasure ℝ) : Measure ℝ)) t := by
          symm
          simpa [scaleLaw] using
            (MeasureTheory.charFun_map_mul
              (μ := (((μ ^ (n : ℕ) : ProbabilityMeasure ℝ) : Measure ℝ))) a t)

/-- Helper for Example 16.2: scaling a real infinitely divisible law preserves infinite
divisibility. -/
private theorem isInfinitelyDivisible_map_mul
    {μ : ProbabilityMeasure ℝ}
    (hμ : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ) (a : ℝ) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (scaleLaw a μ) := by
  refine ⟨?_⟩
  intro n
  rcases hμ.exists_root n with ⟨ν, hν⟩
  refine ⟨scaleLaw a ν, ?_⟩
  -- Proof comment: push the chosen convolution root forward by the same scalar map and commute
  -- that pushforward through the convolution power.
  calc
    scaleLaw a ν ^ (n : ℕ) = scaleLaw a (ν ^ (n : ℕ)) := by
            exact map_mul_pow_eq_map_pow_mul ν a n
    _ = scaleLaw a μ := by
          rw [hν]

/-- Helper for Example 16.2: the general Gaussian-over-`√Gamma` owner law is a scalar image of
the unit-variance/unit-rate owner law. -/
private theorem gaussianOverSqrtGammaLaw_eq_map_unitRate
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    gaussianOverSqrtGammaLaw σ2 θ r hθ hr =
      scaleLaw (Real.sqrt ((σ2 : ℝ) * θ))
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  let P : Measure (ℝ × ℝ) := (gaussianReal (0 : ℝ) 1).prod (gammaMeasure r 1)
  let X : ℝ × ℝ → ℝ := fun z ↦ z.1
  let Y : ℝ × ℝ → ℝ := fun z ↦ z.2
  let Xσ : ℝ × ℝ → ℝ := fun z ↦ Real.sqrt (σ2 : ℝ) * z.1
  let Yθ : ℝ × ℝ → ℝ := fun z ↦ z.2 / θ
  let Z : ℝ × ℝ → ℝ := fun z ↦ z.1 / Real.sqrt z.2
  let Zσθ : ℝ × ℝ → ℝ := fun z ↦ Xσ z / Real.sqrt (Yθ z)
  let a : ℝ := Real.sqrt ((σ2 : ℝ) * θ)
  letI : IsProbabilityMeasure (gammaMeasure r 1) := isProbabilityMeasure_gammaMeasure hr zero_lt_one
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hXY : IndepFun X Y P := by
    -- Proof comment: the product law makes the two coordinate projections independent.
    simpa [P, X, Y] using
      (ProbabilityTheory.indepFun_prod
        (μ := gaussianReal (0 : ℝ) 1) (ν := gammaMeasure r 1)
        (X := id) (Y := id) measurable_id measurable_id)
  have hX : HasLaw X (gaussianReal (0 : ℝ) 1) P := by
    -- Proof comment: the first coordinate of the product law has the unit Gaussian marginal.
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simpa [P, X] using
      (Measure.map_fst_prod (μ := gaussianReal (0 : ℝ) 1) (ν := gammaMeasure r 1))
  have hY : HasLaw Y (gammaMeasure r 1) P := by
    -- Proof comment: the second coordinate of the product law has the unit-rate Gamma marginal.
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    simpa [P, Y] using
      (Measure.map_snd_prod (μ := gaussianReal (0 : ℝ) 1) (ν := gammaMeasure r 1))
  have hXσ_base :
      HasLaw (fun x : ℝ ↦ Real.sqrt (σ2 : ℝ) * x) (gaussianReal (0 : ℝ) σ2)
        (gaussianReal (0 : ℝ) 1) := by
    refine ⟨(measurable_const.mul measurable_id).aemeasurable, ?_⟩
    -- Proof comment: scaling the unit Gaussian by `√σ²` produces variance `σ²`.
    simpa [Real.sq_sqrt, le_of_lt hσ2] using
      (ProbabilityTheory.gaussianReal_map_const_mul
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (c := Real.sqrt (σ2 : ℝ)))
  have hYθ_base :
      HasLaw (fun y : ℝ ↦ y / θ) (gammaMeasure r θ) (gammaMeasure r 1) := by
    refine ⟨measurable_id.div_const θ |>.aemeasurable, ?_⟩
    -- Proof comment: scale the unit-rate Gamma law by `1 / θ` to obtain rate `θ`.
    exact gammaMeasure_unitRate_map_div_eq_gammaMeasure θ r hθ hr
  have hXσ : HasLaw Xσ (gaussianReal (0 : ℝ) σ2) P := by
    -- Proof comment: compose the first coordinate with the Gaussian scaling law.
    simpa [Xσ, X, Function.comp] using HasLaw.comp hXσ_base hX
  have hYθ : HasLaw Yθ (gammaMeasure r θ) P := by
    -- Proof comment: compose the second coordinate with the Gamma scaling law.
    simpa [Yθ, Y, Function.comp] using HasLaw.comp hYθ_base hY
  have hXσYθ : IndepFun Xσ Yθ P := by
    -- Proof comment: independent coordinates remain independent after separate measurable
    -- scalar transformations.
    simpa [Xσ, Yθ, X, Y, Function.comp] using
      hXY.comp (measurable_const.mul measurable_id) (measurable_id.div_const θ)
  have hZ : AEMeasurable Z P := by
    simpa [Z] using measurable_fst.aemeasurable.div measurable_snd.aemeasurable.sqrt
  have hZσθ : AEMeasurable Zσθ P := by
    simpa [Zσθ, Xσ, Yθ] using
      (measurable_const.mul measurable_fst).aemeasurable.div
        ((measurable_snd.div_const θ).aemeasurable.sqrt)
  have hUnitMap :
      (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZ : ProbabilityMeasure ℝ) =
        gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr := by
    -- Proof comment: the unit owner law is the ratio law of the canonical unit pair.
    exact
      ratioGaussianSqrtGamma_map_eq_ownerLaw
        (P := P) (X := X) (Y := Y) hXY 1 1 r zero_lt_one zero_lt_one hr hX hY
  have hGeneralMap :
      (ProbabilityMeasure.map ⟨P, inferInstance⟩ hZσθ : ProbabilityMeasure ℝ) =
        gaussianOverSqrtGammaLaw σ2 θ r hθ hr := by
    -- Proof comment: after scaling the coordinates, the same product space realizes the general
    -- owner law.
    exact
      ratioGaussianSqrtGamma_map_eq_ownerLaw
        (P := P) (X := Xσ) (Y := Yθ) hXσYθ σ2 θ r hσ2 hθ hr hXσ hYθ
  have hYnonneg : ∀ᵐ z ∂ P, 0 ≤ z.2 := by
    -- Proof comment: the Gamma coordinate is almost surely nonnegative under the product law.
    simpa [Y, P] using
      (hY.ae_iff (by fun_prop)).2 (ae_nonneg_gammaMeasure_rate r 1)
  have hratio :
      (fun z : ℝ × ℝ ↦ Zσθ z) =ᵐ[P] fun z ↦ a * Z z := by
    filter_upwards [hYnonneg] with z hz
    have hsqrt :
        Real.sqrt (z.2 / θ) = Real.sqrt z.2 / Real.sqrt θ := by
      rw [Real.sqrt_div hz θ]
    have ha :
        Real.sqrt (σ2 : ℝ) * Real.sqrt θ = a := by
      dsimp [a]
      symm
      exact Real.sqrt_mul (le_of_lt hσ2) θ
    -- Proof comment: on the nonnegative Gamma support, the denominator rescales by `1 / √θ`,
    -- so the whole ratio rescales by `√(σ² θ)`.
    dsimp [Zσθ, Z, Xσ, Yθ, a]
    calc
      Real.sqrt (σ2 : ℝ) * z.1 / Real.sqrt (z.2 / θ)
          = Real.sqrt (σ2 : ℝ) * z.1 / (Real.sqrt z.2 / Real.sqrt θ) := by
              rw [hsqrt]
      _ = (Real.sqrt (σ2 : ℝ) * z.1 * Real.sqrt θ) / Real.sqrt z.2 := by
            rw [div_div_eq_mul_div]
      _ = (Real.sqrt (σ2 : ℝ) * Real.sqrt θ * z.1) / Real.sqrt z.2 := by
            ring
      _ = (a * z.1) / Real.sqrt z.2 := by
            rw [ha]
      _ = a * (z.1 / Real.sqrt z.2) := by
            rw [mul_div_assoc]
  apply ProbabilityMeasure.toMeasure_injective
  -- Proof comment: rewrite both sides as pushforwards of the same unit product model and then
  -- use the almost-sure identity of the two ratio maps.
  calc
    ((gaussianOverSqrtGammaLaw σ2 θ r hθ hr : ProbabilityMeasure ℝ) : Measure ℝ)
        = ((ProbabilityMeasure.map ⟨P, inferInstance⟩ hZσθ : ProbabilityMeasure ℝ) : Measure ℝ) := by
            rw [hGeneralMap]
    _ = Measure.map Zσθ P := by
          simp [ProbabilityMeasure.toMeasure_map]
    _ = Measure.map (fun z : ℝ × ℝ ↦ a * Z z) P := by
          exact Measure.map_congr hratio
    _ = Measure.map (fun x : ℝ ↦ a * x) (Measure.map Z P) := by
          simpa [Function.comp, Z] using
            (Measure.map_map (measurable_const.mul measurable_id)
              (measurable_fst.div measurable_snd.sqrt) (μ := P)).symm
    _ = ((scaleLaw a (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) : ProbabilityMeasure ℝ) :
          Measure ℝ) := by
          rw [← hUnitMap]
          simp [scaleLaw, ProbabilityMeasure.toMeasure_map]

/-- Helper for Example 16.2: once the unit-variance/unit-rate owner law is infinitely divisible,
the general Gaussian-over-`√Gamma` owner law follows by scalar transport. -/
private theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_unitRate
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hunit :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
  have hscaled :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (scaleLaw (Real.sqrt ((σ2 : ℝ) * θ))
          (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr)) :=
    isInfinitelyDivisible_map_mul hunit (Real.sqrt ((σ2 : ℝ) * θ))
  -- Proof comment: the previous scaling identity rewrites the general owner law to the scaled
  -- unit owner law, so infinite divisibility transports immediately.
  simpa [gaussianOverSqrtGammaLaw_eq_map_unitRate σ2 θ r hσ2 hθ hr] using hscaled

/-- Helper for Example 16.2: the reciprocal-Gamma time law on `[0, ∞)` obtained by pushing the
unit-rate Gamma law forward along `y ↦ y⁻¹`. -/
private noncomputable def reciprocalGammaTimeLaw (r : ℝ) (hr : 0 < r) : ProbabilityMeasure NNReal :=
  ProbabilityMeasure.map
    ⟨gammaMeasure r 1, isProbabilityMeasure_gammaMeasure hr zero_lt_one⟩
    ((measurable_real_toNNReal.comp measurable_inv).aemeasurable)

/-- Helper for Example 16.2: the unit-rate Gamma law has no atom at `0`. -/
private lemma gammaMeasure_unitRate_singleton_zero (r : ℝ) :
    gammaMeasure r 1 ({0} : Set ℝ) = 0 := by
  -- Proof comment: Gamma laws are absolutely continuous with respect to Lebesgue measure.
  rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  simp

/-- Helper for Example 16.2: the unit-rate Gamma law is almost surely strictly positive. -/
private lemma ae_pos_gammaMeasure_unitRate (r : ℝ) :
    ∀ᵐ y ∂ gammaMeasure r 1, 0 < y := by
  have hnonneg : ∀ᵐ y ∂ gammaMeasure r 1, 0 ≤ y := ae_nonneg_gammaMeasure_rate r 1
  have hne_zero : ∀ᵐ y ∂ gammaMeasure r 1, y ≠ 0 := by
    rw [ae_iff]
    simpa using gammaMeasure_unitRate_singleton_zero r
  -- Proof comment: combine the nonnegative Gamma support with the absence of an atom at `0`.
  filter_upwards [hnonneg, hne_zero] with y hy_nonneg hy_ne
  exact lt_of_le_of_ne hy_nonneg (Ne.symm hy_ne)

/-- Helper for Example 16.2: the unit-rate Gamma law viewed on `[0, ∞)` via `Real.toNNReal`. -/
private noncomputable def unitRateGammaTimeLaw (r : ℝ) (hr : 0 < r) : ProbabilityMeasure NNReal :=
  ProbabilityMeasure.map
    ⟨gammaMeasure r 1, isProbabilityMeasure_gammaMeasure hr zero_lt_one⟩
    measurable_real_toNNReal.aemeasurable

/-- Helper for Example 16.2: the `NNReal` unit-rate Gamma law inherits the zero-atom property at
the origin. -/
private lemma unitRateGammaTimeLaw_singleton_zero (r : ℝ) (hr : 0 < r) :
    (((unitRateGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)
      ({0} : Set NNReal)) = 0 := by
  rw [unitRateGammaTimeLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply_of_aemeasurable measurable_real_toNNReal.aemeasurable
      (measurableSet_singleton 0)]
  have hpreimage_eq :
      Real.toNNReal ⁻¹' ({0} : Set NNReal) = Set.Iic (0 : ℝ) := by
    ext y
    constructor
    · intro hy
      -- Proof comment: `toNNReal y = 0` is exactly the statement `y ≤ 0`.
      exact Real.toNNReal_eq_zero.mp (by simpa [Set.mem_preimage] using hy)
    · intro hy
      -- Proof comment: the converse direction is the same equivalence read backwards.
      simpa [Set.mem_preimage] using (Real.toNNReal_eq_zero.mpr hy)
  have hIic_ae :
      ∀ᵐ y ∂ gammaMeasure r 1, y ∉ Set.Iic (0 : ℝ) := by
    filter_upwards [ae_pos_gammaMeasure_unitRate r] with y hy
    have hy_not_le : ¬ y ≤ 0 := by
      linarith
    simpa [Set.mem_Iic] using hy_not_le
  rw [hpreimage_eq]
  rw [ae_iff] at hIic_ae
  simpa using hIic_ae

/-- Helper for Example 16.2: the reciprocal-Gamma time law is the inversion pushforward of the
`NNReal` unit-rate Gamma law. -/
private theorem reciprocalGammaTimeLaw_eq_map_inv_unitRateGammaTimeLaw
    (r : ℝ) (hr : 0 < r) :
    reciprocalGammaTimeLaw r hr =
      ProbabilityMeasure.map (unitRateGammaTimeLaw r hr) measurable_inv.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  have hcongr :
      (fun y : ℝ ↦ (Real.toNNReal (y⁻¹) : NNReal)) =ᵐ[gammaMeasure r 1]
        fun y : ℝ ↦ ((Real.toNNReal y : NNReal)⁻¹) := by
    filter_upwards [ae_pos_gammaMeasure_unitRate r] with y hy
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg hy.le, Real.toNNReal_of_nonneg (inv_nonneg.mpr hy.le)]
  calc
    ((reciprocalGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)
        = Measure.map (Real.toNNReal ∘ Inv.inv) (gammaMeasure r 1) := by
            simp [reciprocalGammaTimeLaw, ProbabilityMeasure.toMeasure_map]
    _ = Measure.map (fun y : ℝ ↦ (Real.toNNReal (y⁻¹) : NNReal)) (gammaMeasure r 1) := by
          rfl
    _ = Measure.map (fun y : ℝ ↦ ((Real.toNNReal y : NNReal)⁻¹)) (gammaMeasure r 1) := by
          exact Measure.map_congr hcongr
    _ = ((ProbabilityMeasure.map (unitRateGammaTimeLaw r hr) measurable_inv.aemeasurable :
            ProbabilityMeasure NNReal) : Measure NNReal) := by
          symm
          rw [unitRateGammaTimeLaw, ProbabilityMeasure.toMeasure_map]
          simpa [Function.comp, ProbabilityMeasure.toMeasure_map] using
            (Measure.map_map measurable_inv measurable_real_toNNReal
              (μ := gammaMeasure r 1))

/-- Helper for Example 16.2: the reciprocal-Gamma time law has Mellin transform equal to the
negative Mellin transform of the `NNReal` unit-rate Gamma law. -/
private theorem mellinTransform_reciprocalGammaTimeLaw_eq_neg
    (r : ℝ) (hr : 0 < r) (s : ℝ) :
    mellinTransform
        (((reciprocalGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)) s =
      mellinTransform
        (((unitRateGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal)) (-s) := by
  rw [reciprocalGammaTimeLaw_eq_map_inv_unitRateGammaTimeLaw r hr]
  -- Proof comment: after rewriting the reciprocal-Gamma law as an inversion pushforward, the
  -- Chapter 15 Mellin-transform inversion identity applies directly.
  simpa using
    (mellinTransform_map_inv_eq_neg
      (((unitRateGammaTimeLaw r hr : ProbabilityMeasure NNReal) : Measure NNReal))
      (unitRateGammaTimeLaw_singleton_zero r hr) (s := s))

/-- Helper for Example 16.2: the Gaussian-mixture time parameter attached to frequency `t`, namely
the nonnegative scalar `t² / 2` viewed in `NNReal`. -/
private noncomputable def gaussianTimeMixtureParameter (t : ℝ) : NNReal :=
  Real.toNNReal (t ^ (2 : ℕ) / 2)

/-- Helper for Example 16.2: coercing the Gaussian-mixture time parameter back to `ℝ` recovers the
original nonnegative scalar `t² / 2`. -/
private lemma coe_gaussianTimeMixtureParameter (t : ℝ) :
    ((gaussianTimeMixtureParameter t : NNReal) : ℝ) = t ^ (2 : ℕ) / 2 := by
  -- Proof comment: `t² / 2` is nonnegative, so `Real.toNNReal` is a two-sided coercion here.
  have ht_nonneg : 0 ≤ t ^ (2 : ℕ) / 2 := by
    positivity
  simp [gaussianTimeMixtureParameter, Real.toNNReal_of_nonneg ht_nonneg]

/-- Helper for Example 16.2: the positive-time Gaussian-mixture characteristic-function candidate
attached to an `NNReal` time law. -/
private noncomputable def gaussianTimeMixtureCFP (τ : ProbabilityMeasure NNReal) : ℝ → ℂ :=
  fun t ↦
    ∫ s : NNReal,
      ((Real.exp
          (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ))) : ℝ) : ℂ)
        ∂(τ : Measure NNReal)

/-- Helper for Example 16.2: the Gaussian-mixture CFP is the complex coercion of the underlying
real Laplace integral. -/
private lemma gaussianTimeMixtureCFP_eq_ofReal_laplace
    (τ : ProbabilityMeasure NNReal) (t : ℝ) :
    gaussianTimeMixtureCFP τ t =
      ((∫ s : NNReal,
          Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ)))
        ∂(τ : Measure NNReal)) : ℂ) := by
  -- Proof comment: the complex-valued integral of a real-valued kernel is exactly the coercion of
  -- the corresponding real integral.
  simpa [gaussianTimeMixtureCFP] using
    (integral_ofReal
      (μ := (τ : Measure NNReal))
      (f := fun s : NNReal ↦
        Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ)))))

/-- Helper for Example 16.2: the standard Gaussian characteristic function at frequency
`√s * t` matches the Laplace kernel at time `s` and parameter `t² / 2`. -/
private lemma charFun_stdGaussian_eq_gaussianTimeMixtureKernel
    (s : NNReal) (t : ℝ) :
    charFun (gaussianReal (0 : ℝ) 1) (Real.sqrt (s : ℝ) * t) =
      (((Real.exp
          (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ))) : ℝ)) : ℂ) := by
  have hs : 0 ≤ (s : ℝ) := by
    exact_mod_cast s.2
  have hsq :
      (Real.sqrt (s : ℝ) * t) ^ (2 : ℕ) / 2 =
        (((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ) := by
    -- Proof comment: the square of `√s * t` is `s * t²`, so the Gaussian exponent is exactly the
    -- Laplace time parameter `s` multiplied by `t² / 2`.
    rw [coe_gaussianTimeMixtureParameter]
    calc
      (Real.sqrt (s : ℝ) * t) ^ (2 : ℕ) / 2
          = ((Real.sqrt (s : ℝ)) ^ (2 : ℕ) * t ^ (2 : ℕ)) / 2 := by
              ring
      _ = ((s : ℝ) * t ^ (2 : ℕ)) / 2 := by
            rw [Real.sq_sqrt hs]
      _ = (t ^ (2 : ℕ) / 2) * (s : ℝ) := by
            ring
  -- Proof comment: rewrite the Gaussian characteristic function with `charFun_gaussianReal` and
  -- simplify its exponent using the previous normalization.
  rw [ProbabilityTheory.charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  norm_num
  exact_mod_cast hsq

/-- Helper for Example 16.2: the Laplace kernel on `[0, ∞)` is integrable against every
probability law. -/
private lemma integrableNnrealLaplaceKernel (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    Integrable (fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ)))) (μ : Measure NNReal) := by
  -- Proof comment: the exponential kernel is bounded by the constant function `1`.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  have hnonneg : 0 ≤ Real.exp (-((t : ℝ) * (x : ℝ))) := by
    positivity
  rw [Real.norm_of_nonneg hnonneg]
  refine Real.exp_le_one_iff.mpr ?_
  have ht : 0 ≤ (t : ℝ) := by
    positivity
  have hx : 0 ≤ (x : ℝ) := by
    exact_mod_cast x.2
  nlinarith

/-- Helper for Example 16.2: additive convolution on `[0, ∞)` turns the Laplace kernel into a
product. -/
private lemma nnrealLaplaceIntegral_mul
    (μ ν : ProbabilityMeasure NNReal) (t : NNReal) :
    ∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂((μ * ν : ProbabilityMeasure NNReal) : Measure NNReal) =
      (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) *
        ∫ y, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(ν : Measure NNReal) := by
  -- Proof comment: convolution is the pushforward of the product measure under addition, and the
  -- Laplace kernel factorizes across sums.
  rw [ProbabilityMeasure.toMeasure_mul, Measure.conv]
  rw [integral_map_of_stronglyMeasurable measurable_add]
  · calc
      ∫ z : NNReal × NNReal, Real.exp (-((t : ℝ) * ((z.1 + z.2 : NNReal) : ℝ)))
          ∂((μ : Measure NNReal).prod (ν : Measure NNReal)) =
        ∫ z : NNReal × NNReal,
            Real.exp (-((t : ℝ) * (z.1 : ℝ))) * Real.exp (-((t : ℝ) * (z.2 : ℝ)))
            ∂((μ : Measure NNReal).prod (ν : Measure NNReal)) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
              rcases z with ⟨x, y⟩
              change
                Real.exp (-((t : ℝ) * (((x + y : NNReal) : ℝ)))) =
                  Real.exp (-((t : ℝ) * (x : ℝ))) * Real.exp (-((t : ℝ) * (y : ℝ)))
              rw [show (((x + y : NNReal) : ℝ)) = (x : ℝ) + (y : ℝ) by rfl]
              rw [mul_add, neg_add, Real.exp_add]
      _ = (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) *
            ∫ y, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(ν : Measure NNReal) := by
              simpa using
                (integral_prod_mul
                  (μ := (μ : Measure NNReal))
                  (ν := (ν : Measure NNReal))
                  (f := fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ))))
                  (g := fun y : NNReal ↦ Real.exp (-((t : ℝ) * (y : ℝ)))))
  · fun_prop

/-- Helper for Example 16.2: convolution powers on `[0, ∞)` raise the Laplace transform to the
matching power. -/
private lemma nnrealLaplaceIntegral_pow
    (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    ∀ m : ℕ,
      ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ)))
          ∂((μ ^ m : ProbabilityMeasure NNReal) : Measure NNReal) =
        (∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) ^ m
  | 0 => by
      -- Proof comment: the zeroth convolution power is `δ₀`, whose Laplace integral is `1`.
      simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
  | m + 1 => by
      -- Proof comment: one more convolution factor multiplies the Laplace transform by the base
      -- Laplace value.
      rw [pow_succ, nnrealLaplaceIntegral_mul, nnrealLaplaceIntegral_pow μ t m, pow_succ]

/-- Helper for Example 16.2: the Gaussian-mixture owner law obtained from a nonnegative time law
by scaling a standard Gaussian with `√s`. -/
private noncomputable def gaussianTimeMixtureLaw (τ : ProbabilityMeasure NNReal) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ⟨((gaussianReal (0 : ℝ) 1).prod (τ : Measure NNReal)), by infer_instance⟩
    ((by
      fun_prop : Measurable (fun z : ℝ × NNReal ↦ Real.sqrt (z.2 : ℝ) * z.1)).aemeasurable)

/-- Helper for Example 16.2: the Gaussian-mixture owner law has characteristic function equal to
the Laplace transform of the time law at `t² / 2`. -/
private theorem gaussianTimeMixtureLaw_charFun_eq
    (τ : ProbabilityMeasure NNReal) :
    charFun (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ)) =
      gaussianTimeMixtureCFP τ := by
  funext t
  let P : Measure (ℝ × NNReal) := ((gaussianReal (0 : ℝ) 1).prod (τ : Measure NNReal))
  let f : ℝ × NNReal → ℂ := fun z ↦ Complex.exp (t * (Real.sqrt (z.2 : ℝ) * z.1) * Complex.I)
  have hZ :
      AEMeasurable (fun z : ℝ × NNReal ↦ Real.sqrt (z.2 : ℝ) * z.1) P := by
    -- Proof comment: the Gaussian-mixture owner law is defined by scaling the Gaussian coordinate
    -- by `√s`.
    dsimp [P]
    fun_prop
  have hf : AEStronglyMeasurable f P := by
    -- Proof comment: the product-space integrand is a measurable complex exponential.
    dsimp [f, P]
    fun_prop
  have hInt : Integrable f P := by
    -- Proof comment: the complex exponential has norm `1`, so the product-space integral is
    -- absolutely bounded by the constant integrable function `1`.
    refine Integrable.of_bound hf 1 ?_
    filter_upwards with z
    simp [f, Complex.norm_exp]
  have hmap :
      (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ)) =
        Measure.map (fun z : ℝ × NNReal ↦ Real.sqrt (z.2 : ℝ) * z.1) P := by
    -- Proof comment: unfold the owner-law pushforward once, but keep the product-model interface
    -- opaque afterwards.
    simp [gaussianTimeMixtureLaw, P, ProbabilityMeasure.toMeasure_map]
  calc
    charFun (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ)) t
        = ∫ z, f z ∂P := by
            -- Proof comment: expand the characteristic function of the pushed-forward mixture law.
            rw [hmap, charFun_apply_real]
            rw [integral_map hZ]
            · refine integral_congr_ae ?_
              filter_upwards with z
              simp [f]
            · fun_prop
    _ = ∫ s, ∫ x, f (x, s) ∂(gaussianReal (0 : ℝ) 1) ∂(τ : Measure NNReal) := by
          -- Proof comment: separate the product integral into Gaussian and time coordinates.
          simpa [P] using integral_prod_symm f hInt
    _ = ∫ s, charFun (gaussianReal (0 : ℝ) 1) (Real.sqrt (s : ℝ) * t) ∂(τ : Measure NNReal) := by
          -- Proof comment: for each time value `s`, the inner Gaussian integral is the Gaussian
          -- characteristic function at frequency `√s * t`.
          refine integral_congr_ae ?_
          filter_upwards with s
          rw [charFun_apply_real]
          congr 1
          funext x
          simp [f]
          ring
    _ = ∫ s, (((Real.exp
            (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (s : ℝ))) : ℝ)) : ℂ)
            ∂(τ : Measure NNReal) := by
          -- Proof comment: rewrite the inner Gaussian characteristic function into the Laplace
          -- kernel of the time law.
          refine integral_congr_ae ?_
          filter_upwards with s
          exact charFun_stdGaussian_eq_gaussianTimeMixtureKernel s t
    _ = gaussianTimeMixtureCFP τ t := by
          rfl

/-- Helper for Example 16.2: every positive-time Gaussian mixture is a characteristic function,
realized by the corresponding product-model owner law. -/
private theorem gaussianTimeMixture_isCFP (τ : ProbabilityMeasure NNReal) :
    IsCFP (gaussianTimeMixtureCFP τ) := by
  -- Proof comment: the previous helper identifies the mixture formula with the characteristic
  -- function of the explicit Gaussian-mixture owner law.
  refine ⟨gaussianTimeMixtureLaw τ, ?_⟩
  exact gaussianTimeMixtureLaw_charFun_eq τ

/-- Helper for Example 16.2: once the exact Gaussian-mixture characteristic function is known to
be infinitely divisible, Theorem 16.12 transports that CFP statement back to the owner law of the
mixture itself. -/
private theorem gaussianTimeMixtureLaw_isInfinitelyDivisible_of_cfp
    (τ : ProbabilityMeasure NNReal)
    (hcfp : IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP τ)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (gaussianTimeMixtureLaw τ) := by
  have hownerCFP :
      IsInfinitelyDivisibleCFP
        (charFun (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ))) := by
    -- Proof comment: rewrite the owner characteristic function of the Gaussian mixture to its
    -- explicit Laplace-transform CFP before applying Theorem 16.12.
    simpa [gaussianTimeMixtureLaw_charFun_eq τ] using hcfp
  -- Proof comment: once the owner characteristic function is infinitely divisible, the owner law
  -- itself is infinitely divisible by the earlier CFP-to-owner bridge.
  exact isInfinitelyDivisible_of_charFun_isInfinitelyDivisibleCFP hownerCFP

/-- Helper for Example 16.2: the unit Gaussian-over-`√Gamma` characteristic function is exactly
the Gaussian-mixture CFP obtained from the reciprocal-Gamma time law. -/
private theorem gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture
    (r : ℝ) (hr : 0 < r) :
    gaussianOverSqrtGammaCFP 1 1 r = gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr) := by
  funext t
  have hnonneg : ∀ᵐ y ∂gammaMeasure r 1, 0 ≤ y := ae_nonneg_gammaMeasure_rate r 1
  calc
    gaussianOverSqrtGammaCFP 1 1 r t
        = ∫ y,
            (((Real.exp
                (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) *
                    (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)))) : ℝ)) : ℂ)
              ∂(gammaMeasure r 1) := by
            -- Proof comment: on the nonnegative Gamma support, `t / √y` is the same frequency as
            -- `√(y⁻¹) * t`, so the unit Gaussian kernel becomes the reciprocal-Gamma Laplace
            -- kernel.
            refine integral_congr_ae ?_
            filter_upwards [hnonneg] with y hy
            have hy_inv : 0 ≤ y⁻¹ := inv_nonneg.mpr hy
            have hfreq :
                Real.sqrt (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)) * t = t / Real.sqrt y := by
              simp [Real.toNNReal_of_nonneg hy_inv, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
            calc
              charFun (gaussianReal (0 : ℝ) 1) (t / Real.sqrt y)
                  = charFun (gaussianReal (0 : ℝ) 1)
                      (Real.sqrt (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)) * t) := by
                        rw [hfreq]
              _ = (((Real.exp
                      (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) *
                          (((Real.toNNReal (y⁻¹) : NNReal) : ℝ)))) : ℝ)) : ℂ) := by
                    exact charFun_stdGaussian_eq_gaussianTimeMixtureKernel
                      (Real.toNNReal (y⁻¹)) t
    _ = gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr) t := by
          -- Proof comment: now rewrite the reciprocal-Gamma law as the pushforward of the
          -- unit-rate Gamma law under inversion.
          rw [gaussianTimeMixtureCFP_eq_ofReal_laplace, reciprocalGammaTimeLaw,
            ProbabilityMeasure.toMeasure_map]
          rw [integral_map ((measurable_real_toNNReal.comp measurable_inv).aemeasurable)]
          · rfl
          · fun_prop

/-- Helper for Example 16.2: exact convolution roots of a positive-time law induce exact power
identities for the corresponding Gaussian-mixture characteristic functions. -/
private theorem gaussianTimeMixture_pow_eq_of_timePow_eq
    {τ τn : ProbabilityMeasure NNReal} (n : ℕ+) (hpow : τn ^ (n : ℕ) = τ) :
    ∀ t : ℝ, (gaussianTimeMixtureCFP τn t) ^ (n : ℕ) = gaussianTimeMixtureCFP τ t := by
  intro t
  have hrootLap :
      ∫ x : NNReal,
          Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
          ∂(τ : Measure NNReal) =
        (∫ x : NNReal,
            Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
            ∂(τn : Measure NNReal)) ^ (n : ℕ) := by
    -- Proof comment: the exact time-law root identity transports directly through the Laplace
    -- transform of the time law.
    simpa [hpow] using nnrealLaplaceIntegral_pow τn (gaussianTimeMixtureParameter t) (n : ℕ)
  have hrootLapC :
      (((∫ x : NNReal,
          Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
          ∂(τn : Measure NNReal)) : ℂ) ^ (n : ℕ)) =
        ((∫ x : NNReal,
            Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
            ∂(τ : Measure NNReal)) : ℂ) := by
    exact_mod_cast hrootLap.symm
  calc
    (gaussianTimeMixtureCFP τn t) ^ (n : ℕ)
        = (((∫ x : NNReal,
                Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
                ∂(τn : Measure NNReal)) : ℂ) ^ (n : ℕ)) := by
              rw [gaussianTimeMixtureCFP_eq_ofReal_laplace]
    _ = ((∫ x : NNReal,
            Real.exp (-((((gaussianTimeMixtureParameter t : NNReal) : ℝ)) * (x : ℝ)))
            ∂(τ : Measure NNReal)) : ℂ) := hrootLapC
    _ = gaussianTimeMixtureCFP τ t := by
          rw [gaussianTimeMixtureCFP_eq_ofReal_laplace]

/-- Helper for Example 16.2: an infinitely divisible positive-time law yields an infinitely
divisible Gaussian-mixture characteristic function. -/
private theorem gaussianTimeMixtureCFP_isInfinitelyDivisible_of_timeLaw
    {τ : ProbabilityMeasure NNReal}
    (hτ : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible τ) :
    IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP τ) := by
  have hcont : ContinuousAt (gaussianTimeMixtureCFP τ) 0 := by
    rcases gaussianTimeMixture_isCFP τ with ⟨μ, hμ⟩
    -- Proof comment: every characteristic function of a probability law is continuous at `0`,
    -- and the Gaussian-mixture formula is already identified with such a characteristic function.
    simpa [hμ] using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt
  refine (isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto hcont).2 ?_
  classical
  let τroot : ℕ+ → ProbabilityMeasure NNReal := fun n ↦ Classical.choose (hτ.exists_root n)
  have hτroot : ∀ n : ℕ+, τroot n ^ (n : ℕ) = τ := by
    intro n
    exact Classical.choose_spec (hτ.exists_root n)
  refine ⟨fun n ↦ gaussianTimeMixtureCFP (τroot n), ?_, ?_⟩
  · intro n
    -- Proof comment: every exact time root still defines a genuine Gaussian-mixture
    -- characteristic function.
    exact gaussianTimeMixture_isCFP (τroot n)
  · intro t
    have hconst :
        (fun n : ℕ+ ↦ (gaussianTimeMixtureCFP (τroot n) t) ^ (n : ℕ)) =
          fun _ : ℕ+ ↦ gaussianTimeMixtureCFP τ t := by
      funext n
      -- Proof comment: the exact time-law root identity transports directly through the Laplace
      -- transform defining the Gaussian-mixture characteristic function.
      exact gaussianTimeMixture_pow_eq_of_timePow_eq n (hτroot n) t
    -- Proof comment: after the power transport, the approximating sequence is pointwise
    -- constant, so Corollary 16.8 applies immediately.
    rw [hconst]
    exact tendsto_const_nhds

/-- Helper for Example 16.2: once the positive-time law is infinitely divisible, the associated
Gaussian-mixture owner law is infinitely divisible as well. -/
private theorem gaussianTimeMixtureLaw_isInfinitelyDivisible_of_timeLaw
    {τ : ProbabilityMeasure NNReal}
    (hτ : MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible τ) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (gaussianTimeMixtureLaw τ) := by
  have hcfp :
      IsInfinitelyDivisibleCFP
        (charFun (((gaussianTimeMixtureLaw τ : ProbabilityMeasure ℝ) : Measure ℝ))) := by
    -- Proof comment: rewrite the owner characteristic function to the Gaussian-mixture CFP and
    -- then apply the already-proved time-law-to-CFP bridge.
    simpa [gaussianTimeMixtureLaw_charFun_eq τ] using
      gaussianTimeMixtureCFP_isInfinitelyDivisible_of_timeLaw hτ
  -- Proof comment: Theorem 16.12 turns the owner characteristic-function statement into owner-law
  -- infinite divisibility.
  exact isInfinitelyDivisible_of_charFun_isInfinitelyDivisibleCFP hcfp

/-- Helper for Example 16.2: the unit Gaussian-over-`√Gamma` owner law is exactly the explicit
Gaussian-mixture owner law driven by the reciprocal-Gamma time law. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_eq_gaussianTimeMixtureLaw
    (r : ℝ) (hr : 0 < r) :
    gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr =
      gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun (((gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr : ProbabilityMeasure ℝ) :
        Measure ℝ)) t
        = gaussianOverSqrtGammaCFP 1 1 r t := by
            exact gaussianOverSqrtGammaLaw_charFun_eq 1 1 r zero_lt_one zero_lt_one hr t
    _ = gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr) t := by
          exact congrFun (gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture r hr) t
    _ = charFun (((gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr) :
        ProbabilityMeasure ℝ) : Measure ℝ)) t := by
          symm
          exact congrFun (gaussianTimeMixtureLaw_charFun_eq (reciprocalGammaTimeLaw r hr)) t

/-- Helper for Example 16.2: infinite divisibility of the reciprocal-Gamma time law is enough to
close the unit Gaussian-over-`√Gamma` owner law. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_of_timeLaw
    (r : ℝ) (hr : 0 < r)
    (htime :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible (reciprocalGammaTimeLaw r hr)) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  have hmix :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr)) :=
    gaussianTimeMixtureLaw_isInfinitelyDivisible_of_timeLaw htime
  -- Proof comment: the unit owner law is literally the Gaussian mixture driven by the
  -- reciprocal-Gamma time law, so the owner-level time-law bridge closes the theorem directly.
  simpa [gaussianOverSqrtGammaLaw_unitRate_eq_gaussianTimeMixtureLaw r hr] using hmix

/-- Helper for Example 16.2: once the explicit reciprocal-Gamma Gaussian-mixture owner law is
known to be infinitely divisible, the canonical unit Gaussian-over-`√Gamma` owner law follows by
the already-proved owner identification. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_of_mixtureLaw
    (r : ℝ) (hr : 0 < r)
    (hmix :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr))) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  -- Proof comment: the unit owner law is exactly the reciprocal-Gamma Gaussian mixture.
  simpa [gaussianOverSqrtGammaLaw_unitRate_eq_gaussianTimeMixtureLaw r hr] using hmix

/-- Helper for Example 16.2: this is the remaining analytic frontier after the proved
scale-to-unit and owner/CFP transport steps. The downstream target only needs the unit owner law,
so the live blocker is now stated directly at that owner-law level rather than through the
stronger reciprocal-Gamma time-law statement. -/
private theorem gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_direct
    (r : ℝ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
  -- Route correction: earlier attempts kept the blocker at the stronger reciprocal-Gamma time law.
  -- The proved transport layer only consumes the unit owner law, so the missing analytic theorem
  -- should be supplied directly in this owner formulation.
  -- Proof comment: all mixture-side rewrites are now downstream corollaries, so the only missing
  -- input is the cited direct infinite-divisibility theorem for the exact unit owner law.
  -- TODO: prove this direct owner-law statement, for example by a dependency-closed analytic
  -- representation of `gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr` or its equivalent unit CFP.
  sorry

/-- Helper for Example 16.2: once the exact unit owner law is available, the unit
Gaussian-over-`√Gamma` characteristic function is infinitely divisible by the established
owner/CFP bridge. -/
private theorem gaussianOverSqrtGammaUnit_cfp_isInfinitelyDivisible_direct
    (r : ℝ) (hr : 0 < r) :
    IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
  -- Proof comment: the direct unit owner-law theorem is exactly the object consumed by the
  -- owner/CFP equivalence, so no additional root approximation package is needed here.
  exact
    (gaussianOverSqrtGammaLaw_isInfinitelyDivisible_iff_cfp 1 1 r zero_lt_one zero_lt_one hr).1
      (gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_direct r hr)

/-- Helper for Example 16.2: once the exact unit owner law is available, the reciprocal-Gamma
Gaussian-mixture characteristic function follows by rewriting the unit characteristic function. -/
private theorem gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible_of_unitOwnerLaw
    (r : ℝ) (hr : 0 < r)
    (hunit :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr)) :
    IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr)) := by
  have hunitCFP :
      IsInfinitelyDivisibleCFP (gaussianOverSqrtGammaCFP 1 1 r) := by
    -- Proof comment: the exact unit owner-law theorem is already the canonical input for the
    -- local owner/CFP equivalence, so convert it once before rewriting to the mixture CFP.
    exact
      (gaussianOverSqrtGammaLaw_isInfinitelyDivisible_iff_cfp 1 1 r zero_lt_one zero_lt_one hr).1
        hunit
  -- Proof comment: the unit Gaussian-over-`√Gamma` characteristic function is exactly the
  -- reciprocal-Gamma Gaussian-mixture characteristic function.
  simpa [gaussianOverSqrtGammaUnit_cfp_eq_gaussianTimeMixture r hr] using hunitCFP

/-- Helper for Example 16.2: once the exact unit owner law is available, the reciprocal-Gamma
Gaussian-mixture characteristic function follows by rewriting the unit characteristic function. -/
private theorem gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible
    (r : ℝ) (hr : 0 < r) :
    IsInfinitelyDivisibleCFP (gaussianTimeMixtureCFP (reciprocalGammaTimeLaw r hr)) := by
  -- Route correction: the live blocker is the exact unit owner law, not the reciprocal-Gamma
  -- Gaussian-mixture CFP. This theorem is now only a rewrite bridge out of that smaller frontier.
  -- Proof comment: the preceding bridge packages the owner/CFP conversion, so only the exact
  -- unit owner-law frontier remains open here.
  exact
    gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible_of_unitOwnerLaw r hr
      (gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_direct r hr)

/-- Helper for Example 16.2: once the exact reciprocal-Gamma Gaussian-mixture characteristic
function is known to be infinitely divisible, the corresponding owner law follows by the generic
Gaussian-mixture CFP-to-owner bridge. -/
private theorem gaussianTimeMixtureLaw_reciprocalGamma_isInfinitelyDivisible
    (r : ℝ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianTimeMixtureLaw (reciprocalGammaTimeLaw r hr)) := by
  -- Proof comment: after isolating the analytic frontier at the exact mixture characteristic
  -- function, the owner-law statement is just the generic Theorem 16.12 transport.
  exact
    gaussianTimeMixtureLaw_isInfinitelyDivisible_of_cfp
      (reciprocalGammaTimeLaw r hr)
      (gaussianTimeMixtureCFP_reciprocalGamma_isInfinitelyDivisible r hr)

/-- Helper for Example 16.2: this is the single cited analytic theorem for the canonical
Gaussian-over-`√Gamma` owner law. All downstream CFP and map-law corollaries are already reduced
to this owner-level infinite-divisibility statement. -/
theorem gaussianOverSqrtGammaLaw_isInfinitelyDivisible
    (σ2 : ℝ≥0) (θ r : ℝ) (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (gaussianOverSqrtGammaLaw σ2 θ r hθ hr) := by
  -- Route correction: earlier attempts tried to encode the cited variance-mixture theorem as a
  -- local infinitesimal-array package for Theorem 16.12. The proved part of the route is now the
  -- scale-to-unit reduction, so the only remaining analytic frontier is the unit law with
  -- `σ² = θ = 1`.
  have hunit :
      MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
        (gaussianOverSqrtGammaLaw 1 1 r zero_lt_one hr) := by
    -- Proof comment: after the route correction, the only remaining missing premise is the direct
    -- unit owner-law theorem, which is exactly the object consumed by the already-proved scaling
    -- transport.
    exact gaussianOverSqrtGammaLaw_unitRate_isInfinitelyDivisible_direct r hr
  -- Proof comment: the proved scale-to-unit transport turns the unit-case theorem into the full
  -- `σ², θ` statement without reopening the analytic argument.
  exact gaussianOverSqrtGammaLaw_isInfinitelyDivisible_of_unitRate σ2 θ r hσ2 hθ hr hunit
