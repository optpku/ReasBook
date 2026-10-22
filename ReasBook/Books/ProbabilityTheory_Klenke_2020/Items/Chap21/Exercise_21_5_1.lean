/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/-- Helper for Exercise 21.5.1: a measurable representative of the terminal Brownian value. -/
def brownianTerminalRepresentative (hB : IsBrownianMotion μ B) : Ω → ℝ :=
  (hB.aestronglyMeasurable 1).mk (B 1)

/-- Helper for Exercise 21.5.1: the measurable endpoint representative agrees almost everywhere
with the original terminal value. -/
lemma brownianTerminalRepresentative_ae_eq (hB : IsBrownianMotion μ B) :
    brownianTerminalRepresentative hB =ᵐ[μ] B 1 := by
  -- Proof comment: `AEStronglyMeasurable.mk` only changes the endpoint on a null set.
  simpa [brownianTerminalRepresentative] using (hB.aestronglyMeasurable 1).ae_eq_mk.symm

/-- Helper for Exercise 21.5.1: the endpoint representative is genuinely measurable. -/
lemma measurable_brownianTerminalRepresentative (hB : IsBrownianMotion μ B) :
    Measurable (brownianTerminalRepresentative hB) := by
  -- Proof comment: this is the measurable witness produced by `AEStronglyMeasurable.mk`.
  simpa [brownianTerminalRepresentative] using (hB.aestronglyMeasurable 1).measurable_mk

/-- Helper for Exercise 21.5.1: the covariance kernel of Brownian motion is `s ⊓ t`. -/
lemma brownianCovariance_eq_min (hB : IsBrownianMotion μ B) (s t : NNReal) :
    cov[B s, B t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
  -- Proof comment: this is the standard covariance identity for Brownian motion.
  simpa using brownianMotion_covariance_eq hB s t

/-- Helper for Exercise 21.5.1: every fixed Brownian marginal belongs to `L²`. -/
lemma brownianEval_memLp_two
    (hB : IsBrownianMotion μ B) (t : NNReal) :
    MemLp (B t) 2 μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  by_cases ht : t = 0
  · -- Proof comment: the time-zero Brownian coordinate is the constant zero function.
    subst ht
    simp [hB.zero]
  · -- Proof comment: every positive-time Brownian marginal is Gaussian, hence square integrable.
    exact (hB.gaussian_marginal (pos_iff_ne_zero.mpr ht)).hasGaussianLaw.memLp_two

/-- The conditioning event `{ω | B 1 ω ∈ (-ε, ε)}` used in Exercise 21.5.1, expressed through a
measurable endpoint representative. -/
def brownianEndpointWindow (hB : IsBrownianMotion μ B) (ε : ℝ) : Set Ω :=
  brownianTerminalRepresentative hB ⁻¹' Set.Ioo (-ε) ε

/-- Helper for Exercise 21.5.1: the finite Brownian coordinate tuple is almost everywhere
measurable. -/
theorem aemeasurable_brownianFiniteDimensionalCoordinates
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    AEMeasurable (finiteDimensionalEvaluation B fun i ↦ (times i : NNReal)) μ := by
  -- Route correction: the Brownian-motion owner now provides AE measurability at fixed times, so
  -- the tuple evaluation must be built in that normal form.
  exact aemeasurable_pi_lambda _ fun i ↦ hB.aemeasurable (times i)

/-- Helper for Exercise 21.5.1: the finite Brownian-bridge coordinate tuple is almost everywhere
measurable. -/
theorem aemeasurable_brownianBridgeFiniteDimensionalCoordinates
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    AEMeasurable (fun ω i ↦ brownianBridge B (times i) ω) μ := by
  -- Proof comment: each bridge coordinate is the difference between `B_t` and a scalar multiple
  -- of the AE-measurable endpoint.
  exact aemeasurable_pi_lambda _ fun i ↦ by
    simpa [brownianBridge] using
      (((hB.aestronglyMeasurable (times i)).sub
        ((hB.aestronglyMeasurable 1).const_mul (times i : ℝ))).aemeasurable)

theorem brownianEndpointWindow_measure_ne_zero
    (hB : IsBrownianMotion μ B) {ε : ℝ} (hε : 0 < ε) :
    μ (brownianEndpointWindow hB ε) ≠ 0 := by
  have hB1 : HasLaw (B 1) (gaussianReal 0 1) μ :=
    hB.gaussian_marginal (by positivity)
  have hRep : HasLaw (brownianTerminalRepresentative hB) (gaussianReal 0 1) μ := by
    -- Proof comment: the endpoint representative is a.e. equal to `B 1`, so it has the same law.
    exact hB1.congr (brownianTerminalRepresentative_ae_eq hB)
  have hRep_meas : Measurable (brownianTerminalRepresentative hB) :=
    measurable_brownianTerminalRepresentative hB
  have hgauss_ne : gaussianReal 0 1 (Set.Ioo (-ε) ε) ≠ 0 := by
    intro hzero
    have hvol_zero : (volume : Measure ℝ) (Set.Ioo (-ε) ε) = 0 :=
      gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero
    have hvol_pos : (0 : ENNReal) < (volume : Measure ℝ) (Set.Ioo (-ε) ε) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hvol_pos.ne' hvol_zero
  have hμeq :
      μ (brownianEndpointWindow hB ε) = gaussianReal 0 1 (Set.Ioo (-ε) ε) := by
    calc
      μ (brownianEndpointWindow hB ε) =
          μ ((brownianTerminalRepresentative hB) ⁻¹' Set.Ioo (-ε) ε) := by
        rfl
      _ = Measure.map (brownianTerminalRepresentative hB) μ (Set.Ioo (-ε) ε) := by
        rw [Measure.map_apply hRep_meas measurableSet_Ioo]
      _ = gaussianReal 0 1 (Set.Ioo (-ε) ε) := by
        rw [hRep.map_eq]
  rw [hμeq]
  exact hgauss_ne

/-- Helper for Exercise 21.5.1: conditioning on the endpoint window preserves total mass `1`. -/
lemma brownianEndpointWindow_cond_isProbabilityMeasure
    (hB : IsBrownianMotion μ B) (ε : Set.Ioi (0 : ℝ)) :
    IsProbabilityMeasure (μ[|brownianEndpointWindow hB ε]) := by
  -- Proof comment: the endpoint window has positive `μ`-mass, so the standard conditional-measure
  -- owner stays normalized.
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  exact cond_isProbabilityMeasure (brownianEndpointWindow_measure_ne_zero hB ε.2)

/- For this item:
- `source-facing`: the conditioned finite-dimensional Brownian coordinate law and the matching
  Brownian-bridge finite-dimensional law.
- `core/canonical`: both are `ProbabilityMeasure (Fin (n + 1) → ℝ)` owners.
- `bridge/view`: the conditioning event and the coordinate pushforwards; the Brownian side uses
  the chapter owner `finiteDimensionalEvaluation`, and the right-limit is expressed directly on
  the positive parameter space `Set.Ioi 0` rather than through a second public law family.
-/

/-- The Brownian-bridge finite-dimensional law at the time tuple `times`. -/
def brownianBridgeFiniteDimensionalLaw
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map ⟨μ, hB.isProbabilityMeasure⟩
    (aemeasurable_brownianBridgeFiniteDimensionalCoordinates hB times)

/-- The finite-dimensional law of the Brownian coordinates at `times`, conditioned on the endpoint
event `B₁ ∈ (-ε, ε)` for a positive window radius `ε`. -/
def conditionedBrownianFiniteDimensionalLaw
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) (ε : Set.Ioi (0 : ℝ)) :
    ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map
    ⟨μ[|brownianEndpointWindow hB ε], brownianEndpointWindow_cond_isProbabilityMeasure hB ε⟩
    ((aemeasurable_brownianFiniteDimensionalCoordinates hB times).mono_ac
      ProbabilityTheory.cond_absolutelyContinuous)

/-- The conditioned law of the terminal Brownian value `B 1` on the window `(-ε, ε)`. -/
def conditionedBrownianEndpointLaw
    (hB : IsBrownianMotion μ B) (ε : Set.Ioi (0 : ℝ)) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ⟨μ[|brownianEndpointWindow hB ε], brownianEndpointWindow_cond_isProbabilityMeasure hB ε⟩
    (measurable_brownianTerminalRepresentative hB).aemeasurable

/-- Helper for Exercise 21.5.1: the unconditioned law of the terminal Brownian value `B 1`. -/
def brownianTerminalLaw (hB : IsBrownianMotion μ B) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map ⟨μ, hB.isProbabilityMeasure⟩
    (measurable_brownianTerminalRepresentative hB).aemeasurable

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 21.5.1: the Brownian coordinate tuple splits into the bridge tuple plus
the deterministic endpoint shift `tᵢ B₁`. -/
lemma finiteDimensionalEvaluation_eq_brownianBridge_add_endpointShift
    {n : ℕ} (times : Fin (n + 1) → BrownianBridgeTime) (ω : Ω) :
    finiteDimensionalEvaluation B (fun i ↦ (times i : NNReal)) ω =
      fun i ↦ brownianBridge B (times i) ω + (times i : ℝ) * B 1 ω := by
  -- Proof comment: unpack the finite-dimensional evaluation and rewrite each coordinate by the
  -- defining Brownian-bridge decomposition `B_t = (B_t - t B₁) + t B₁`.
  funext i
  simp [finiteDimensionalEvaluation, brownianBridge]

/-- Helper for Exercise 21.5.1: every bridge coordinate is uncorrelated with the terminal value
`B 1`. -/
lemma brownianBridgeCoordinate_covTerminal_eq_zero
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) (i : Fin (n + 1)) :
    cov[fun ω ↦ brownianBridge B (times i) ω, B 1; μ] = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hbridge :
      (fun ω ↦ brownianBridge B (times i) ω) =
        fun ω ↦ B (times i) ω - (times i : ℝ) * B 1 ω := by
    -- Proof comment: this is the defining bridge decomposition at the fixed time `times i`.
    funext ω
    simp [brownianBridge]
  have hti_mem : MemLp (B (times i)) 2 μ := brownianEval_memLp_two_ofBrownianMotion hB (times i)
  have h1_mem : MemLp (B 1) 2 μ := brownianEval_memLp_two_ofBrownianMotion hB 1
  have hcov_t1 : cov[B (times i), B 1; μ] = (times i : ℝ) := by
    -- Proof comment: since `times i ≤ 1`, the Brownian covariance kernel collapses to `times i`.
    simpa [inf_eq_left.mpr (times i).2.2] using brownianMotion_covariance_eq hB (times i) 1
  have hcov_11 : cov[B 1, B 1; μ] = 1 := by
    -- Proof comment: the terminal Brownian variance is the covariance kernel at `(1,1)`.
    simpa using brownianMotion_covariance_eq hB 1 1
  -- Proof comment: expand `B_t - t B₁` against `B₁`; the two covariance terms cancel.
  rw [hbridge]
  rw [covariance_fun_sub_left hti_mem (h1_mem.const_mul (times i : ℝ)) h1_mem]
  rw [covariance_const_mul_left, hcov_t1, hcov_11]
  ring

/-- Helper for Exercise 21.5.1: the bridge coordinates together with the terminal value form a
jointly Gaussian process. -/
lemma brownianBridgeAndEndpoint_isGaussianProcess
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    IsGaussianProcess
      (Sum.elim
        (fun i : Fin (n + 1) => fun ω ↦ brownianBridge B (times i) ω)
        (fun _ : Unit => fun ω ↦ B 1 ω))
      μ := by
  let hGaussian : IsGaussianProcess B μ := brownianMotion_isGaussianProcess hB
  -- Proof comment: each bridge coordinate is an affine linear image of the Brownian pair
  -- `(B_(times i), B₁)`, while the right coordinate is the evaluation `B₁` itself.
  refine hGaussian.of_isGaussianProcess ?_
  intro z
  cases z with
  | inl i =>
      refine ⟨{(times i : NNReal), 1}, ?_, ?_⟩
      · refine
          { toFun := fun x ↦ x ⟨(times i : NNReal), by simp⟩ - (times i : ℝ) * x ⟨1, by simp⟩
            map_add' := by
              intro x y
              change
                (x ⟨(times i : NNReal), by simp⟩ + y ⟨(times i : NNReal), by simp⟩) -
                    (times i : ℝ) * (x ⟨1, by simp⟩ + y ⟨1, by simp⟩) =
                  (x ⟨(times i : NNReal), by simp⟩ - (times i : ℝ) * x ⟨1, by simp⟩) +
                    (y ⟨(times i : NNReal), by simp⟩ - (times i : ℝ) * y ⟨1, by simp⟩)
              ring
            map_smul' := by
              intro c x
              change
                c * x ⟨(times i : NNReal), by simp⟩ - (times i : ℝ) * (c * x ⟨1, by simp⟩) =
                  c * (x ⟨(times i : NNReal), by simp⟩ - (times i : ℝ) * x ⟨1, by simp⟩)
              ring
            cont := by
              fun_prop }
      · -- Proof comment: evaluating this linear map on the restricted Brownian vector gives the
        -- bridge coordinate `B_t - t B₁`.
        intro ω
        simp [brownianBridge]
  | inr _ =>
      refine ⟨{(1 : NNReal)}, ?_, ?_⟩
      · refine
          { toFun := fun x ↦ x ⟨1, by simp⟩
            map_add' := by
              intro x y
              simp
            map_smul' := by
              intro c x
              simp
            cont := by
              fun_prop }
      · -- Proof comment: the terminal coordinate is already a single Brownian evaluation.
        intro ω
        simp

/-- Helper for Exercise 21.5.1: the finite bridge-coordinate tuple is independent of the terminal
value `B 1`. -/
lemma brownianBridgeCoordinates_indepTerminalValue
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    IndepFun (fun ω i ↦ brownianBridge B (times i) ω) (B 1) μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Y : Unit → Ω → ℝ := fun _ ω ↦ B 1 ω
  have hIndepFamily :
      IndepFun (fun ω i ↦ brownianBridge B (times i) ω) (fun ω u ↦ Y u ω) μ := by
    -- Proof comment: use a `Unit`-indexed copy of the terminal value so that the Gaussian
    -- independence lemma matches the family-vs-family interface exactly.
    refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero
      (brownianBridgeAndEndpoint_isGaussianProcess hB times) ?_ ?_ ?_
    · intro i
      simpa using (aemeasurable_brownianBridgeFiniteDimensionalCoordinates hB times).eval i
    · intro u
      cases u
      simpa [Y] using hB.aemeasurable 1
    · intro i u
      cases u
      simpa [Y] using brownianBridgeCoordinate_covTerminal_eq_zero hB times i
  -- Proof comment: the bridge tuple and the terminal value sit inside one jointly Gaussian
  -- family, and then evaluate the `Unit`-indexed side at `()`.
  simpa [Y] using hIndepFamily.comp measurable_id (by
    simpa using measurable_pi_apply ())

/-- Helper for Exercise 21.5.1: pushforward commutes with conditioning on a measurable preimage. -/
lemma mapCondPreimage_eq_condMap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} {s : Set β}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) :
    Measure.map f (μ[|f ⁻¹' s]) = (Measure.map f μ)[|s] := by
  -- Proof comment: after unfolding `cond`, both sides are the same scaled restriction of the
  -- pushforward measure.
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul,
    Measure.restrict_map_of_aemeasurable hf hs,
    Measure.map_apply_of_aemeasurable hf hs]

/-- Helper for Exercise 21.5.1: conditioning a product measure on a second-coordinate event only
conditions the second factor. -/
lemma prod_cond_snd_preimage_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {κ : Measure β} [IsProbabilityMeasure ν] [SFinite κ]
    {s : Set β} (_hs : MeasurableSet s) :
    (ν.prod κ)[|Prod.snd ⁻¹' s] = ν.prod (κ[|s]) := by
  have hs_pre : Prod.snd ⁻¹' s = (Set.univ : Set α) ×ˢ s := by
    ext p
    simp
  have hmass : (ν.prod κ) ((Set.univ : Set α) ×ˢ s) = κ s := by
    -- Proof comment: the second-coordinate event is the rectangle `univ ×ˢ s`, so the first
    -- factor contributes the unit mass `ν univ = 1`.
    rw [Measure.prod_prod, measure_univ, one_mul]
  -- Proof comment: after rewriting the event as a rectangle, conditioning is just restriction and
  -- renormalization, and the scalar normalization moves to the second product factor.
  rw [ProbabilityTheory.cond, hs_pre, hmass, ← Measure.prod_restrict, Measure.restrict_univ,
    ← Measure.prod_smul_right, ProbabilityTheory.cond]

/-- Helper for Exercise 21.5.1: reconstruct the Brownian coordinate tuple from the bridge tuple
and the terminal value. -/
def brownianBridgeReconstruction {n : ℕ} (times : Fin (n + 1) → BrownianBridgeTime) :
    (Fin (n + 1) → ℝ) × ℝ → Fin (n + 1) → ℝ :=
  fun p i ↦ p.1 i + (times i : ℝ) * p.2

/-- Helper for Exercise 21.5.1: the reconstruction map from bridge coordinates and endpoint is
continuous. -/
lemma continuous_brownianBridgeReconstruction {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Continuous (brownianBridgeReconstruction times) := by
  -- Proof comment: each coordinate is an affine function of `(bridge tuple, endpoint)`.
  refine continuous_pi fun i ↦ ?_
  simpa [brownianBridgeReconstruction] using
    (((continuous_apply i).comp continuous_fst).add
      (continuous_const.mul continuous_snd))

/-- Helper for Exercise 21.5.1: before conditioning, the joint law of the bridge coordinates and
the terminal value is the product of their marginals. -/
lemma brownianBridgePairLaw_eq_prod
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Measure.map
      (fun ω ↦ ((fun i ↦ brownianBridge B (times i) ω), brownianTerminalRepresentative hB ω)) μ =
      ((brownianBridgeFiniteDimensionalLaw hB times).prod (brownianTerminalLaw hB) :
        Measure ((Fin (n + 1) → ℝ) × ℝ)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Y : Ω → Fin (n + 1) → ℝ := fun ω i ↦ brownianBridge B (times i) ω
  let Z : Ω → ℝ := brownianTerminalRepresentative hB
  have hY_ae : AEMeasurable Y μ := aemeasurable_brownianBridgeFiniteDimensionalCoordinates hB times
  have hZ_meas : Measurable Z := measurable_brownianTerminalRepresentative hB
  have hB1_eq_Z : (B 1) =ᵐ[μ] Z := by
    simpa [Z] using (brownianTerminalRepresentative_ae_eq hB).symm
  have hIndep : IndepFun Y Z μ := by
    -- Proof comment: endpoint independence survives passage to an a.e.-equal measurable
    -- representative of `B 1`.
    exact (brownianBridgeCoordinates_indepTerminalValue hB times).congr (ae_eq_refl _) hB1_eq_Z
  -- Proof comment: once the bridge tuple and endpoint are independent, their joint pushforward is
  -- the product of the two marginal laws.
  simpa [brownianBridgeFiniteDimensionalLaw, brownianTerminalLaw, Y, Z] using
    (indepFun_iff_map_prod_eq_prod_map_map hY_ae hZ_meas.aemeasurable).1 hIndep

/-- Helper for Exercise 21.5.1: conditioning the terminal marginal on the interval
`(-ε, ε)` agrees with mapping the conditioned Brownian measure by the measurable endpoint
representative. -/
lemma brownianTerminalLaw_cond_eq_conditioned
    (hB : IsBrownianMotion μ B) (ε : Set.Ioi (0 : ℝ)) :
    ((brownianTerminalLaw hB : Measure ℝ)[|Set.Ioo (-(ε : ℝ)) (ε : ℝ)]) =
      (conditionedBrownianEndpointLaw hB ε : Measure ℝ) := by
  let Z : Ω → ℝ := brownianTerminalRepresentative hB
  let S : Set ℝ := Set.Ioo (-(ε : ℝ)) (ε : ℝ)
  -- Proof comment: conditioning commutes with pushforward when the conditioning event is a
  -- measurable preimage under the map.
  simpa [brownianTerminalLaw, conditionedBrownianEndpointLaw, brownianEndpointWindow, Z, S] using
    (mapCondPreimage_eq_condMap
      (μ := μ)
      (f := Z)
      (s := S)
      (measurable_brownianTerminalRepresentative hB).aemeasurable
      measurableSet_Ioo).symm

/-- Helper for Exercise 21.5.1: after conditioning on the endpoint window, the joint law of the
bridge coordinates and the endpoint splits as the product of the bridge law and the conditioned
endpoint law. -/
lemma conditionedBridgePairLaw_eq_prod
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) (ε : Set.Ioi (0 : ℝ)) :
    Measure.map
      (fun ω ↦ ((fun i ↦ brownianBridge B (times i) ω), brownianTerminalRepresentative hB ω))
      (μ[|brownianEndpointWindow hB ε]) =
      ((brownianBridgeFiniteDimensionalLaw hB times).prod (conditionedBrownianEndpointLaw hB ε) :
        Measure ((Fin (n + 1) → ℝ) × ℝ)) := by
  let Φ : Ω → (Fin (n + 1) → ℝ) × ℝ :=
    fun ω ↦ ((fun i ↦ brownianBridge B (times i) ω), brownianTerminalRepresentative hB ω)
  let S : Set ℝ := Set.Ioo (-(ε : ℝ)) (ε : ℝ)
  let T : Set ((Fin (n + 1) → ℝ) × ℝ) := Prod.snd ⁻¹' S
  have hΦ_ae : AEMeasurable Φ μ :=
    (aemeasurable_brownianBridgeFiniteDimensionalCoordinates hB times).prodMk
      (measurable_brownianTerminalRepresentative hB).aemeasurable
  have hT_meas : MeasurableSet T := measurable_snd measurableSet_Ioo
  have hmap_cond :
      Measure.map Φ (μ[|brownianEndpointWindow hB ε]) = (Measure.map Φ μ)[|T] := by
    -- Proof comment: the pair map `Φ` records the endpoint as its second coordinate, so the
    -- endpoint window is exactly the measurable preimage of `T`.
    simpa [Φ, T, S, brownianEndpointWindow] using
      (mapCondPreimage_eq_condMap (μ := μ) (f := Φ) (s := T) hΦ_ae hT_meas)
  calc
    Measure.map Φ (μ[|brownianEndpointWindow hB ε]) = (Measure.map Φ μ)[|T] := hmap_cond
    _ =
        (((brownianBridgeFiniteDimensionalLaw hB times).prod (brownianTerminalLaw hB) :
          Measure ((Fin (n + 1) → ℝ) × ℝ))[|T]) := by
          rw [brownianBridgePairLaw_eq_prod hB times]
    _ =
        (((brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)).prod
          ((brownianTerminalLaw hB : Measure ℝ)[|S])) : Measure ((Fin (n + 1) → ℝ) × ℝ)) := by
          simpa using
            (prod_cond_snd_preimage_eq
              (ν := (brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)))
              (κ := (brownianTerminalLaw hB : Measure ℝ))
              (s := S)
              measurableSet_Ioo)
    _ =
        (((brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)).prod
          (conditionedBrownianEndpointLaw hB ε : Measure ℝ)) :
          Measure ((Fin (n + 1) → ℝ) × ℝ)) := by
          rw [brownianTerminalLaw_cond_eq_conditioned hB ε]

/-- Helper for Exercise 21.5.1: the conditioned endpoint law is supported on the conditioning
window. -/
lemma conditionedBrownianEndpointLaw_apply_window_eq_one
    (hB : IsBrownianMotion μ B) (ε : Set.Ioi (0 : ℝ)) :
    (conditionedBrownianEndpointLaw hB ε : Measure ℝ) (Set.Ioo (-(ε : ℝ)) (ε : ℝ)) = 1 := by
  let Z : Ω → ℝ := brownianTerminalRepresentative hB
  let A : Set Ω := brownianEndpointWindow hB ε
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hA_ne_zero : μ A ≠ 0 := brownianEndpointWindow_measure_ne_zero hB ε.2
  have hA_meas : MeasurableSet A := by
    simpa [A, Z] using ((measurable_brownianTerminalRepresentative hB) measurableSet_Ioo)
  -- Proof comment: mapping by `B 1` turns the endpoint window back into the conditioning event
  -- itself, so `cond_apply_self` gives the normalized mass.
  change Measure.map Z (μ[|A]) (Set.Ioo (-(ε : ℝ)) (ε : ℝ)) = 1
  rw [Measure.map_apply_of_aemeasurable (measurable_brownianTerminalRepresentative hB).aemeasurable
      measurableSet_Ioo]
  change μ[Z ⁻¹' Set.Ioo (-(ε : ℝ)) (ε : ℝ) | A] = 1
  simpa [A, Z] using cond_apply_self (μ := μ) (s := A) hA_ne_zero (measure_ne_top μ A)

/-- Helper for Exercise 21.5.1: the conditioned endpoint laws converge weakly to the Dirac mass at
`0` as the conditioning window shrinks. -/
lemma conditionedBrownianEndpointLaw_tendsto_diracProba_zero
    (hB : IsBrownianMotion μ B) :
    Tendsto (fun ε : Set.Ioi (0 : ℝ) ↦ conditionedBrownianEndpointLaw hB ε)
      (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)))
      (𝓝 (diracProba (0 : ℝ))) := by
  apply MeasureTheory.tendsto_of_forall_isOpen_le_liminf'
  intro G hG_open
  by_cases h0 : (0 : ℝ) ∈ G
  · rcases Metric.mem_nhds_iff.mp (hG_open.mem_nhds h0) with ⟨δ, hδ_pos, hδ_subset⟩
    have hsmall :
        ∀ᶠ ε : Set.Ioi (0 : ℝ) in
          Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)),
          (ε : ℝ) < δ := by
      change Subtype.val ⁻¹' Set.Iio δ ∈
        Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ))
      refine Filter.mem_comap.2 ?_
      refine ⟨Set.Iio δ, ?_, by intro ε hε; exact hε⟩
      exact (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ)) (Iio_mem_nhds hδ_pos)
    have h_eventually_one :
        ∀ᶠ ε : Set.Ioi (0 : ℝ) in
          Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)),
          ((conditionedBrownianEndpointLaw hB ε : Measure ℝ) G) = 1 := by
      filter_upwards [hsmall] with ε hε
      have hsubset : Set.Ioo (-(ε : ℝ)) (ε : ℝ) ⊆ G := by
        intro x hx
        have hx_abs : |x| < δ := by
          have hx_abs' : |x| < (ε : ℝ) := abs_lt.mpr ⟨hx.1, hx.2⟩
          exact lt_trans hx_abs' hε
        exact hδ_subset <| by simpa [Metric.mem_ball, Real.dist_eq] using hx_abs
      have h_ge : 1 ≤ ((conditionedBrownianEndpointLaw hB ε : Measure ℝ) G) := by
        calc
          1 = (conditionedBrownianEndpointLaw hB ε : Measure ℝ) (Set.Ioo (-(ε : ℝ)) (ε : ℝ)) := by
                symm
                exact conditionedBrownianEndpointLaw_apply_window_eq_one hB ε
          _ ≤ (conditionedBrownianEndpointLaw hB ε : Measure ℝ) G := measure_mono hsubset
      have h_le_one : ((conditionedBrownianEndpointLaw hB ε : Measure ℝ) G) ≤ 1 := by
        calc
          (conditionedBrownianEndpointLaw hB ε : Measure ℝ) G ≤
              (conditionedBrownianEndpointLaw hB ε : Measure ℝ) Set.univ := by
                exact measure_mono (by intro x _; simp)
          _ = 1 := by simp
      exact le_antisymm h_le_one h_ge
    have h_liminf :
        1 ≤
          Filter.liminf
            (fun ε : Set.Ioi (0 : ℝ) ↦ ((conditionedBrownianEndpointLaw hB ε : Measure ℝ) G))
            (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ))) := by
      refine le_liminf_of_le (by isBoundedDefault) ?_
      · exact h_eventually_one.mono fun _ hε ↦ by simp [hε]
    have hdirac : (diracProba (0 : ℝ) : Measure ℝ) G = 1 := by simp [h0]
    rw [hdirac]
    exact h_liminf
  · have hzero :
        0 ≤
          Filter.liminf
            (fun ε : Set.Ioi (0 : ℝ) ↦ ((conditionedBrownianEndpointLaw hB ε : Measure ℝ) G))
            (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ))) :=
      zero_le _
    have hdirac : (diracProba (0 : ℝ) : Measure ℝ) G = 0 := by simp [h0]
    rw [hdirac]
    exact hzero

/-- Helper for Exercise 21.5.1: the conditioned finite-dimensional Brownian law is the image of
the product of the bridge law and the conditioned endpoint law under the reconstruction map. -/
lemma conditionedBrownianFiniteDimensionalLaw_eq_bridgeProdEndpoint_map
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) (ε : Set.Ioi (0 : ℝ)) :
    conditionedBrownianFiniteDimensionalLaw hB times ε =
      ((brownianBridgeFiniteDimensionalLaw hB times).prod (conditionedBrownianEndpointLaw hB ε)).map
        (continuous_brownianBridgeReconstruction times).measurable.aemeasurable := by
  let X : Ω → Fin (n + 1) → ℝ := finiteDimensionalEvaluation B fun i ↦ (times i : NNReal)
  let Φ : Ω → (Fin (n + 1) → ℝ) × ℝ :=
    fun ω ↦ ((fun i ↦ brownianBridge B (times i) ω), brownianTerminalRepresentative hB ω)
  let A : Set Ω := brownianEndpointWindow hB ε
  have hΦ_ae_cond : AEMeasurable Φ (μ[|A]) :=
    ((aemeasurable_brownianBridgeFiniteDimensionalCoordinates hB times).mono_ac
        ProbabilityTheory.cond_absolutelyContinuous).prodMk
      (measurable_brownianTerminalRepresentative hB).aemeasurable
  have hB1_eq_rep :
      (B 1) =ᵐ[μ[|A]] brownianTerminalRepresentative hB :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le
      ((brownianTerminalRepresentative_ae_eq hB).symm)
  have hX_eq :
      X =ᵐ[μ[|A]] fun ω ↦ brownianBridgeReconstruction times (Φ ω) := by
    -- Proof comment: under the conditioned measure, the only replacement is `B₁ = Z` a.e.; the
    -- coordinate decomposition itself is pointwise.
    filter_upwards [hB1_eq_rep] with ω hω
    funext i
    calc
      X ω i =
          brownianBridge B (times i) ω + (times i : ℝ) * B 1 ω := by
            simpa [X] using
              congrFun (finiteDimensionalEvaluation_eq_brownianBridge_add_endpointShift
                (B := B) times ω) i
      _ =
          brownianBridge B (times i) ω +
            (times i : ℝ) * brownianTerminalRepresentative hB ω := by rw [hω]
      _ = brownianBridgeReconstruction times (Φ ω) i := by
            simp [Φ, brownianBridgeReconstruction]
  -- Proof comment: rewrite the conditioned Brownian tuple as the reconstruction map applied to
  -- the conditioned pair law, then insert the factorized pair law from the previous lemma.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  change Measure.map X (μ[|A]) s =
    Measure.map (brownianBridgeReconstruction times)
      ((((brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)).prod
        (conditionedBrownianEndpointLaw hB ε : Measure ℝ)) :
          Measure ((Fin (n + 1) → ℝ) × ℝ))) s
  calc
    Measure.map X (μ[|A]) s =
        Measure.map (fun ω ↦ brownianBridgeReconstruction times (Φ ω)) (μ[|A]) s := by
          rw [Measure.map_congr hX_eq]
    _ =
        Measure.map (brownianBridgeReconstruction times) (Measure.map Φ (μ[|A])) s := by
          have hmap :
              Measure.map (fun ω ↦ brownianBridgeReconstruction times (Φ ω)) (μ[|A]) =
                Measure.map (brownianBridgeReconstruction times) (Measure.map Φ (μ[|A])) := by
            symm
            exact AEMeasurable.map_map_of_aemeasurable
              (continuous_brownianBridgeReconstruction times).measurable.aemeasurable hΦ_ae_cond
          exact congrArg (fun m : Measure (Fin (n + 1) → ℝ) => m s) hmap
    _ =
        Measure.map (brownianBridgeReconstruction times)
          ((((brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)).prod
            (conditionedBrownianEndpointLaw hB ε : Measure ℝ)) :
              Measure ((Fin (n + 1) → ℝ) × ℝ))) s := by
          exact congrArg (fun m : Measure ((Fin (n + 1) → ℝ) × ℝ) =>
              Measure.map (brownianBridgeReconstruction times) m s)
            (conditionedBridgePairLaw_eq_prod hB times ε)

/-- Helper for Exercise 21.5.1: when the endpoint law is `δ₀`, the reconstruction map reduces to
the identity on bridge-coordinate tuples. -/
lemma brownianBridgeProdDirac_map_reconstruction_eq
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    (((brownianBridgeFiniteDimensionalLaw hB times).prod (diracProba (0 : ℝ))).map
      (continuous_brownianBridgeReconstruction times).measurable.aemeasurable) =
      brownianBridgeFiniteDimensionalLaw hB times := by
  -- Proof comment: under `δ₀`, the pair law is the image of the bridge law by `x ↦ (x, 0)`, and
  -- the reconstruction map sends `(x, 0)` back to `x`.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  change
    Measure.map (brownianBridgeReconstruction times)
        (((brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)).prod
          (diracProba (0 : ℝ) : Measure ℝ))) s =
      (brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)) s
  have hprod :
      ((brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)).prod
        (diracProba (0 : ℝ) : Measure ℝ)) =
        Measure.map (fun x ↦ (x, (0 : ℝ)))
          (brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)) := by
    simpa using
      (Measure.prod_dirac
        (μ := (brownianBridgeFiniteDimensionalLaw hB times : Measure (Fin (n + 1) → ℝ)))
        (y := (0 : ℝ)))
  rw [hprod]
  rw [AEMeasurable.map_map_of_aemeasurable
      (continuous_brownianBridgeReconstruction times).measurable.aemeasurable
      measurable_prodMk_right.aemeasurable]
  have hzero :
      (fun x ↦ brownianBridgeReconstruction times (x, (0 : ℝ))) = fun x : Fin (n + 1) → ℝ ↦ x := by
    funext x
    funext i
    simp [brownianBridgeReconstruction]
  have hpre :
      (brownianBridgeReconstruction times ∘ fun x ↦ (x, (0 : ℝ))) ⁻¹' s = s := by
    ext x
    have hx : brownianBridgeReconstruction times (x, (0 : ℝ)) = x := by
      simpa using congrFun hzero x
    simp [Function.comp, hx]
  rw [Measure.map_apply_of_aemeasurable
      (AEMeasurable.comp_measurable
        (continuous_brownianBridgeReconstruction times).measurable.aemeasurable
        measurable_prodMk_right)
      hs,
    hpre]

-- Proof sketch: for each fixed finite tuple of times in `[0,1]`, compute the conditioned Gaussian
-- law of `(W_{t₀}, …, W_{tₙ})` given `W₁ ∈ (-ε, ε)` and let `ε ↓ 0`. The limiting centered
-- Gaussian vector has covariance matrix `((tᵢ : NNReal) ⊓ (tⱼ : NNReal)) - tᵢ tⱼ`, which is the
-- finite-dimensional law of the Brownian bridge from the recalled Gaussianity and covariance
-- statements above.
/-- Exercise 21.5.1: for every finite tuple of times in `[0,1]`, the event-conditioned law of the
Brownian coordinates given `B₁ ∈ (-ε, ε)` converges, as `ε ↓ 0`, to the corresponding
Brownian-bridge finite-dimensional law. -/
theorem conditioned_brownian_finiteDimensionalDistributions_tendsto_brownianBridge
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Tendsto (fun ε : Set.Ioi (0 : ℝ) ↦ conditionedBrownianFiniteDimensionalLaw hB times ε)
      (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)))
      (𝓝 (brownianBridgeFiniteDimensionalLaw hB times)) := by
  let ν : ProbabilityMeasure (Fin (n + 1) → ℝ) := brownianBridgeFiniteDimensionalLaw hB times
  have hprod_pair :
      Tendsto
        (fun ε : Set.Ioi (0 : ℝ) ↦ (ν, conditionedBrownianEndpointLaw hB ε))
        (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)))
        (𝓝 (ν, diracProba (0 : ℝ))) :=
    tendsto_const_nhds.prodMk_nhds (conditionedBrownianEndpointLaw_tendsto_diracProba_zero hB)
  have hprod :
      Tendsto
        (fun ε : Set.Ioi (0 : ℝ) ↦ ν.prod (conditionedBrownianEndpointLaw hB ε))
        (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)))
        (𝓝 (ν.prod (diracProba (0 : ℝ)))) := by
    exact (ProbabilityMeasure.continuous_prod.tendsto _).comp hprod_pair
  have hmap :
      Tendsto
        (fun ε : Set.Ioi (0 : ℝ) ↦
          (ν.prod (conditionedBrownianEndpointLaw hB ε)).map
            (continuous_brownianBridgeReconstruction times).measurable.aemeasurable)
        (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)))
        (𝓝 ((ν.prod (diracProba (0 : ℝ))).map
          (continuous_brownianBridgeReconstruction times).measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun ε : Set.Ioi (0 : ℝ) ↦ ν.prod (conditionedBrownianEndpointLaw hB ε))
      (ν.prod (diracProba (0 : ℝ))) hprod (continuous_brownianBridgeReconstruction times)
  -- Proof comment: rewrite both ends by the transport lemmas proved above.
  simpa [ν, conditionedBrownianFiniteDimensionalLaw_eq_bridgeProdEndpoint_map,
    brownianBridgeProdDirac_map_reconstruction_eq] using hmap

end ProbabilityTheory
