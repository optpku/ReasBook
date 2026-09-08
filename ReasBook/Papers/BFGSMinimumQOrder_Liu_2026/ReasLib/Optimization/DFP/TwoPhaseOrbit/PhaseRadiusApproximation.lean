module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTailUniform
public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
import ReasLib.Analysis.Asymptotics.UniformRemainder.BigOToExplicit
import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet.Transport
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleSummability
import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GradientNormSmoothness
import Mathlib.LinearAlgebra.UnitaryGroup

public section
noncomputable section
open Filter
open scoped Asymptotics Matrix Topology

namespace DFP.TwoPhaseOrbit

/-- Equal finite Taylor jets make the difference little-o of the corresponding power. -/
private theorem subIsLittleOOfFunctionEq {m : ℕ} {f g : ℝ → ℝ}
    (hf : ContDiffAt ℝ m f 0) (hg : ContDiffAt ℝ m g 0)
    (hjet : FiniteTaylorJet.ofFunction ℝ m f 0 =
      FiniteTaylorJet.ofFunction ℝ m g 0) :
    (fun x : ℝ ↦ f x - g x) =o[𝓝 0] (fun x : ℝ ↦ x ^ m) := by
  let J := FiniteTaylorJet.ofFunction ℝ m f 0
  let K := FiniteTaylorJet.ofFunction ℝ m g 0
  have hfrem : (fun x : ℝ ↦ J.remainder f 0 x) =o[𝓝 0]
      (fun x : ℝ ↦ x ^ m) :=
    FiniteTaylorJet.remainder_ofFunction_isLittleO hf
  have hgrem : (fun x : ℝ ↦ K.remainder g 0 x) =o[𝓝 0]
      (fun x : ℝ ↦ x ^ m) :=
    FiniteTaylorJet.remainder_ofFunction_isLittleO hg
  refine (hfrem.sub hgrem).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [] with x
  rw [FiniteTaylorJet.remainder_def, FiniteTaylorJet.remainder_def]
  dsimp only [J, K]
  rw [hjet]
  ring

/-- The initial normalized gradient norm along the slow graph differs from one by a cubic-order remainder. -/
private theorem slowCurveInitialNormalizedErrorBigO (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm - 1) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
  let f : ℝ → ℝ := fun ε ↦
    (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).initialGradientNorm
  let P : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 4
  have hpath : ContDiffAt ℝ 5 DFP.TwoLeg.slowGraphJetPath 0 := by
    have hp' : ContDiffAt ℝ 5
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) 0 := by fun_prop
    have hpathEq : DFP.TwoLeg.slowGraphJetPath =
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) := by
      funext ε
      exact DFP.TwoLeg.slowGraphJetPath_apply ε
    rw [hpathEq]
    exact hp'
  have hf : ContDiffAt ℝ 5 f 0 := by
    have hbase : DFP.TwoLeg.slowGraphJetPath 0 =
        ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      rw [DFP.TwoLeg.slowGraphJetPath_apply]
      norm_num
    have hc := DFP.TwoLeg.initialGradientNorm_contDiffAt 5
    rw [← hbase] at hc
    have hc := hc.comp 0 hpath
    simpa only [f, Function.comp_def] using hc
  have hP : ContDiffAt ℝ 5 P 0 := by
    dsimp only [P]
    fun_prop
  have hjet : FiniteTaylorJet.ofFunction ℝ 5 f 0 =
      FiniteTaylorJet.ofFunction ℝ 5 P 0 := by
    simpa only [f, P] using DFP.TwoLeg.NormJet.slowInitialGradient
  have hgraphLittle := subIsLittleOOfFunctionEq hf hP hjet
  have hfiveThree : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 5)).isBigO
  have hgraph : (fun ε : ℝ ↦ f ε - P ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := hgraphLittle.isBigO.trans hfiveThree
  have hpoly : (fun ε : ℝ ↦ P ε - 1) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    have hpow : (fun ε : ℝ ↦ ε ^ 4) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) :=
      (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 4)).isBigO
    simpa only [P, add_sub_cancel_left] using hpow.const_mul_left (2 : ℝ)
  have hslow : (fun ε : ℝ ↦ f ε - 1) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    refine (hgraph.add hpoly).congr_left ?_
    intro ε
    ring
  let graph := DFP.TwoLeg.SlowGraph.ofAsymptotics p h hp hh
  have hstableRaw := graph.map_sub_map_jet_isBigO
    (DFP.TwoLeg.initialGradientNorm_contDiffAt 1)
  have hstable : (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
        (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).initialGradientNorm) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [graph, DFP.TwoLeg.SlowGraph.path_apply] using hstableRaw
  have hstableThree := hstable.trans hfiveThree
  refine (hstableThree.add hslow).congr_left ?_
  intro ε
  dsimp only [f]
  ring

/-- The intermediate normalized gradient norm along the slow graph differs from one by a cubic-order remainder. -/
private theorem slowCurveIntermediateNormalizedErrorBigO (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm - 1) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
  let f : ℝ → ℝ := fun ε ↦
    (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).intermediateGradientNorm
  let P : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6
  have hpath : ContDiffAt ℝ 6 DFP.TwoLeg.slowGraphJetPath 0 := by
    have hp' : ContDiffAt ℝ 6
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) 0 := by fun_prop
    have hpathEq : DFP.TwoLeg.slowGraphJetPath =
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) := by
      funext ε
      exact DFP.TwoLeg.slowGraphJetPath_apply ε
    rw [hpathEq]
    exact hp'
  have hf : ContDiffAt ℝ 6 f 0 := by
    have hbase : DFP.TwoLeg.slowGraphJetPath 0 =
        ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      rw [DFP.TwoLeg.slowGraphJetPath_apply]
      norm_num
    have hc := DFP.TwoLeg.intermediateGradientNorm_contDiffAt 6
    rw [← hbase] at hc
    have hc := hc.comp 0 hpath
    simpa only [f, Function.comp_def] using hc
  have hP : ContDiffAt ℝ 6 P 0 := by
    dsimp only [P]
    fun_prop
  have hjet : FiniteTaylorJet.ofFunction ℝ 6 f 0 =
      FiniteTaylorJet.ofFunction ℝ 6 P 0 := by
    simpa only [f, P] using DFP.TwoLeg.NormJet.slowIntermediateGradient
  have hgraphLittle := subIsLittleOOfFunctionEq hf hP hjet
  have hsixThree : (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 6)).isBigO
  have hgraph : (fun ε : ℝ ↦ f ε - P ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := hgraphLittle.isBigO.trans hsixThree
  have hpoly : (fun ε : ℝ ↦ P ε - 1) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    have h3 := Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)
    have h4 : (fun ε : ℝ ↦ ε ^ 4) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) :=
      (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 4)).isBigO
    have h6 : (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := hsixThree
    have hsum := (h3.const_mul_left (-2 : ℝ)).add
      ((h4.const_mul_left (-2 : ℝ)).add (h6.const_mul_left (-112 / 5 : ℝ)))
    refine hsum.congr_left ?_
    intro ε
    dsimp only [P]
    ring
  have hslow : (fun ε : ℝ ↦ f ε - 1) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    refine (hgraph.add hpoly).congr_left ?_
    intro ε
    ring
  let graph := DFP.TwoLeg.SlowGraph.ofAsymptotics p h hp hh
  have hstableRaw := graph.map_sub_map_jet_isBigO
    (DFP.TwoLeg.intermediateGradientNorm_contDiffAt 1)
  have hstable : (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
        (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).intermediateGradientNorm) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [graph, DFP.TwoLeg.SlowGraph.path_apply] using hstableRaw
  have hfiveThree : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 5)).isBigO
  have hstableThree := hstable.trans hfiveThree
  refine (hstableThree.add hslow).congr_left ?_
  intro ε
  dsimp only [f]
  ring

/-- The normalized gradient norm selected by the endpoint phase. -/
private def phaseNormalizedGradientNorm (p h : ℝ → ℝ)
    (σ : Fin 2) (ε : ℝ) : ℝ :=
  if σ = 0 then
    (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm
  else
    (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm

/-- The two endpoint phases admit common constants for their cubic normalized-gradient bounds. -/
private theorem existsPhaseNormalizedGradientBound (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ C > 0, ∃ δ > 0, ∀ σ : Fin 2, ∀ ε : ℝ,
      |ε| < δ →
        |phaseNormalizedGradientNorm p h σ ε - 1| ≤ C * |ε| ^ 3 := by
  have hfamily : ∀ σ : Fin 2,
      (fun ε : ℝ ↦ phaseNormalizedGradientNorm p h σ ε - 1) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
    intro σ
    fin_cases σ
    · simpa [phaseNormalizedGradientNorm] using
        slowCurveInitialNormalizedErrorBigO p h hp hh
    · simpa [phaseNormalizedGradientNorm] using
        slowCurveIntermediateNormalizedErrorBigO p h hp hh
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_finite_natPow_bound_of_isBigO hfamily
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro σ ε hε
  simpa only [Real.norm_eq_abs] using hbound σ ε hε

/-- A special orthogonal matrix preserves the Euclidean norm of a planar vector. -/
private theorem normSpecialOrthogonalMulVecPhaseRadius
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (v : Fin 2 → ℝ) :
    ‖WithLp.toLp 2 (M.mulVec v)‖ = ‖WithLp.toLp 2 v‖ := by
  rcases Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp hM with
    ⟨hdiag, hoff, hunit⟩
  have hleft := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (M.mulVec v))
  have hright := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)
  rw [Fin.sum_univ_two] at hleft hright
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hleft
  have hsquare : ‖WithLp.toLp 2 (M.mulVec v)‖ ^ 2 =
      ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [hleft, hright]
    rw [hdiag, hoff] at hunit ⊢
    nlinarith
  nlinarith [norm_nonneg (WithLp.toLp 2 (M.mulVec v)),
    norm_nonneg (WithLp.toLp 2 v)]

/-- For a phase-valid state, the gradient norm factors through its amplitude and initial normalized gradient norm. -/
private theorem normGradientEqAmplitudeMulInitialPhaseRadius
    (s : State) (hs : State.PhaseValidity s) :
    ‖s.gradient‖ =
      s.amplitude * (DFP.TwoLeg.observableMap s.coordinates).initialGradientNorm := by
  have hnorms := congrArg Prod.fst
    (DFP.TwoLeg.observableMap_gradientNorms s.ε s.p s.h)
  simp only [] at hnorms
  rw [State.gradient_def, norm_smul, Real.norm_eq_abs, abs_of_pos hs.amplitude_pos]
  rw [normSpecialOrthogonalMulVecPhaseRadius s.frame hs.frame_specialOrthogonal]
  rw [State.coordinates_def, hnorms]

/-- For a phase-valid state, the middle-gradient norm factors through its amplitude and intermediate normalized gradient norm. -/
private theorem normMiddleGradientEqAmplitudeMulIntermediatePhaseRadius
    (s : State) (hs : State.PhaseValidity s) :
    ‖s.middleGradient‖ =
      s.amplitude *
        (DFP.TwoLeg.observableMap s.coordinates).intermediateGradientNorm := by
  have hnorms := congrArg (fun norms ↦ norms.2.1)
    (DFP.TwoLeg.observableMap_gradientNorms s.ε s.p s.h)
  simp only [] at hnorms
  rw [State.middleGradient_def, norm_smul, Real.norm_eq_abs,
    abs_of_pos hs.amplitude_pos]
  rw [normSpecialOrthogonalMulVecPhaseRadius s.frame hs.frame_specialOrthogonal]
  rw [State.coordinates_def, hnorms]

/-- The radial error of a center perturbation is bounded by the center norm and normalized gradient error. -/
private theorem radialErrorLeCenterAddNormalized
    {E : Type*} [SeminormedAddCommGroup E]
    (centerError gradient : E) (amplitude normalized : ℝ)
    (hamplitude : 0 ≤ amplitude)
    (hgradient : ‖gradient‖ = amplitude * normalized) :
    |‖centerError + gradient‖ - amplitude| ≤
      ‖centerError‖ + amplitude * |normalized - 1| := by
  calc
    |‖centerError + gradient‖ - amplitude| ≤
        |‖centerError + gradient‖ - ‖gradient‖| +
          |‖gradient‖ - amplitude| := abs_sub_le _ _ _
    _ ≤ ‖centerError‖ + amplitude * |normalized - 1| := by
      apply add_le_add
      · calc
          |‖centerError + gradient‖ - ‖gradient‖| ≤
              ‖(centerError + gradient) - gradient‖ := abs_norm_sub_norm_le _ _
          _ = ‖centerError‖ := by congr 1; abel
      · rw [hgradient]
        calc
          |amplitude * normalized - amplitude| =
              |amplitude * (normalized - 1)| := by
                congr 1
                ring
          _ = amplitude * |normalized - 1| := by
            rw [abs_mul, abs_of_nonneg hamplitude]
          _ ≤ amplitude * |normalized - 1| := le_rfl

/-- Endpoint radial errors along an invariant slow-curve orbit admit a uniform cubic bound. -/
private theorem slowCurvePhaseRadiusErrorCubeBound (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ C > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        (∀ j : ℕ, (orbit.state j).ε ∈ Set.Ioc 0 ε₀) ∧
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
              ∀ j : ℕ, ∀ σ : Fin 2,
                |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
                    (orbit.state j).amplitude| ≤
                  C * |(orbit.state j).ε| ^ 3 := by
  obtain ⟨Cnorm, hCnorm, δ, hδ, hnorm⟩ :=
    existsPhaseNormalizedGradientBound p h h_pJet h_hJet
  obtain ⟨ηCenter, hηCenter, Kcenter, hKcenter, hcenter⟩ :=
    slowCurveCenterTailUniformBound p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hamp⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hgraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hvalid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
      p h h_invariant h_pJet h_hJet ηGraph hηGraph
  let εbar := min ηCenter (min ηAmp (min ηGraph (min ηValid (δ / 2))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηCenter.1
      (lt_min hηAmp.1 (lt_min hηGraph.1 (lt_min hηValid.1 (half_pos hδ))))
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηCenter.2
  have hGmax : 0 < Gmax := hGmin.trans_le hGminMax
  let C := Kcenter + Gmax * Cnorm
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, C, hC, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεCenter : ε₀ ∈ Set.Ioc 0 ηCenter :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεDeltaHalf : ε₀ ≤ δ / 2 :=
    hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨Glim, hGlim, hGlimTendsto, hampRaw⟩ := hamp ε₀ hεAmp
  have hampBound (j : ℕ) : (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := by
    simpa only [orbit] using hampRaw j
  have hphase (j : ℕ) : DFP.TwoPhaseOrbit.State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hvalid ε₀ hεValid j
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hc'
  have hgraphCoordinates (j : ℕ) :
      (orbit.state j).coordinates =
        ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    obtain ⟨hcoordinateGraph, _⟩ := hgraph ε₀ hεGraph j
    calc
      (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
            simpa only [orbit] using
              DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      _ = ((DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := hcoordinateGraph
      _ = ((orbit.state j).ε, p (orbit.state j).ε,
          h (orbit.state j).ε) := by rw [hεcoord j]
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    obtain ⟨_, hs⟩ := hgraph ε₀ hεGraph j
    rw [hεcoord j]
    exact hs
  refine ⟨hscale, ?_⟩
  intro Clim hClim j σ
  have hcenterBound := hcenter ε₀ hεCenter Clim hClim j
  have hεSmall : |(orbit.state j).ε| < δ := by
    rw [abs_of_pos (hscale j).1]
    exact ((hscale j).2.trans hεDeltaHalf).trans_lt (half_lt_self hδ)
  have hnormBound := hnorm σ (orbit.state j).ε hεSmall
  have hnormBound' :
      |phaseNormalizedGradientNorm p h σ (orbit.state j).ε - 1| ≤
        Cnorm * (orbit.state j).ε ^ 3 := by
    simpa only [abs_of_pos (hscale j).1] using hnormBound
  fin_cases σ

  · change |‖orbit.endpoint (2 * j) - Clim‖ -
      (orbit.state j).amplitude| ≤ C * |(orbit.state j).ε| ^ 3
    have hgradient : ‖(orbit.state j).gradient‖ =
        (orbit.state j).amplitude *
          phaseNormalizedGradientNorm p h 0 (orbit.state j).ε := by
      rw [DFP.TwoPhaseOrbit.normGradientEqAmplitudeMulInitialPhaseRadius
        (orbit.state j) (hphase j), hgraphCoordinates j]
      simp [phaseNormalizedGradientNorm]
    have hpoint : (orbit.state j).point - Clim =
        ((orbit.state j).center - Clim) + (orbit.state j).gradient := by
      rw [DFP.TwoPhaseOrbit.State.center_def]
      abel
    have hradial := radialErrorLeCenterAddNormalized
      ((orbit.state j).center - Clim) (orbit.state j).gradient
      (orbit.state j).amplitude
      (phaseNormalizedGradientNorm p h 0 (orbit.state j).ε)
      (hphase j).amplitude_pos.le hgradient
    rw [DFP.TwoPhaseOrbit.endpoint_even, hpoint]
    calc
      |‖((orbit.state j).center - Clim) + (orbit.state j).gradient‖ -
          (orbit.state j).amplitude| ≤
          ‖(orbit.state j).center - Clim‖ +
            (orbit.state j).amplitude *
              |phaseNormalizedGradientNorm p h 0 (orbit.state j).ε - 1| := hradial
      _ ≤ Kcenter * (orbit.state j).ε ^ 3 +
          (orbit.state j).amplitude * (Cnorm * (orbit.state j).ε ^ 3) := by
        apply add_le_add
        · exact (le_add_of_nonneg_right
            (norm_nonneg ((orbit.state j).middleCenter - Clim))).trans hcenterBound
        · exact mul_le_mul_of_nonneg_left hnormBound' (hphase j).amplitude_pos.le
      _ ≤ Kcenter * (orbit.state j).ε ^ 3 +
          Gmax * (Cnorm * (orbit.state j).ε ^ 3) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (hampBound j).2
            (mul_nonneg hCnorm.le (pow_nonneg (hscale j).1.le 3)))
      _ = C * |(orbit.state j).ε| ^ 3 := by
        rw [abs_of_pos (hscale j).1]
        dsimp only [C]
        ring
  · change |‖orbit.endpoint (2 * j + 1) - Clim‖ -
      (orbit.state j).amplitude| ≤ C * |(orbit.state j).ε| ^ 3
    have hgradient : ‖(orbit.state j).middleGradient‖ =
        (orbit.state j).amplitude *
          phaseNormalizedGradientNorm p h 1 (orbit.state j).ε := by
      rw [DFP.TwoPhaseOrbit.normMiddleGradientEqAmplitudeMulIntermediatePhaseRadius
        (orbit.state j) (hphase j), hgraphCoordinates j]
      simp [phaseNormalizedGradientNorm]
    have hpoint : (orbit.state j).middlePoint - Clim =
        ((orbit.state j).middleCenter - Clim) + (orbit.state j).middleGradient := by
      rw [DFP.TwoPhaseOrbit.State.middleCenter_def]
      abel
    have hradial := radialErrorLeCenterAddNormalized
      ((orbit.state j).middleCenter - Clim) (orbit.state j).middleGradient
      (orbit.state j).amplitude
      (phaseNormalizedGradientNorm p h 1 (orbit.state j).ε)
      (hphase j).amplitude_pos.le hgradient
    rw [DFP.TwoPhaseOrbit.endpoint_odd, hpoint]
    calc
      |‖((orbit.state j).middleCenter - Clim) + (orbit.state j).middleGradient‖ -
          (orbit.state j).amplitude| ≤
          ‖(orbit.state j).middleCenter - Clim‖ +
            (orbit.state j).amplitude *
              |phaseNormalizedGradientNorm p h 1 (orbit.state j).ε - 1| := hradial
      _ ≤ Kcenter * (orbit.state j).ε ^ 3 +
          (orbit.state j).amplitude * (Cnorm * (orbit.state j).ε ^ 3) := by
        apply add_le_add
        · exact (le_add_of_nonneg_left
            (norm_nonneg ((orbit.state j).center - Clim))).trans hcenterBound
        · exact mul_le_mul_of_nonneg_left hnormBound' (hphase j).amplitude_pos.le
      _ ≤ Kcenter * (orbit.state j).ε ^ 3 +
          Gmax * (Cnorm * (orbit.state j).ε ^ 3) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (hampBound j).2
            (mul_nonneg hCnorm.le (pow_nonneg (hscale j).1.le 3)))
      _ = C * |(orbit.state j).ε| ^ 3 := by
        rw [abs_of_pos (hscale j).1]
        dsimp only [C]
        ring

/-- Both endpoint phases have radial error bounded by a cubic power of the
cycle scale along every sufficiently small invariant slow-curve orbit. -/
theorem slowCurvePhaseRadiusErrorIsBigO (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ σ : Fin 2,
            (fun j : ℕ ↦
                ‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
                  (orbit.state j).amplitude) =O[atTop]
              (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
  obtain ⟨εbar, hεbar, C, hC, hcore⟩ :=
    slowCurvePhaseRadiusErrorCubeBound p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hbound := (hcore ε₀ hε₀).2
  intro Clim hClim σ
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, Eventually.of_forall ?_⟩
  intro j
  have hj := hbound Clim hClim j σ
  simpa only [Real.norm_eq_abs, norm_pow] using hj

/-- Both endpoint phases have radial error little-o of the square of the
cycle scale along every sufficiently small invariant slow-curve orbit. -/
theorem slowCurvePhaseRadiusErrorIsLittleO (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ σ : Fin 2,
            (fun j : ℕ ↦
                ‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
                  (orbit.state j).amplitude) =o[atTop]
              (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
  obtain ⟨ηCore, hηCore, C, hC, hcore⟩ :=
    slowCurvePhaseRadiusErrorCubeBound p h h_invariant h_pJet h_hJet
  obtain ⟨ηSum, hηSum, hsum⟩ :=
    DFP.TwoLeg.slowCurveScaleFourthPowerSummable p h h_invariant h_pJet h_hJet
  let εbar := min ηCore ηSum
  have hεbarPos : 0 < εbar := lt_min hηCore.1 hηSum
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηCore.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεCore : ε₀ ∈ Set.Ioc 0 ηCore :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεSum : ε₀ ∈ Set.Ioc 0 ηSum :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hscale : ∀ j : ℕ, (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    simpa only [orbit] using (hcore ε₀ hεCore).1
  have hbound : ∀ Clim : EuclideanSpace ℝ (Fin 2),
      Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
        ∀ j : ℕ, ∀ σ : Fin 2,
          |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
              (orbit.state j).amplitude| ≤
            C * |(orbit.state j).ε| ^ 3 := by
    simpa only [orbit] using (hcore ε₀ hεCore).2
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hc'
  have hsummable : Summable (fun j : ℕ ↦ (orbit.state j).ε ^ 4) := by
    have hs := hsum ε₀ hεSum
    simpa only [hεcoord] using hs
  have hfourZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε ^ 4)
      atTop (𝓝 0) := hsummable.tendsto_atTop_zero
  have hscaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε)
      atTop (𝓝 0) := by
    have hroot := hfourZero.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 4)
    refine hroot.congr' (Eventually.of_forall ?_)
    intro j
    have hid := Real.pow_rpow_inv_natCast (hscale j).1.le (by norm_num : 4 ≠ 0)
    convert hid using 1
    · norm_num
  have hcubeLittleSquare : (fun j : ℕ ↦ (orbit.state j).ε ^ 3) =o[atTop]
      (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    have hsmall : (fun j : ℕ ↦ (orbit.state j).ε) =o[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff ℝ).2 hscaleZero
    have hmul := hsmall.mul_isBigO
      (Asymptotics.isBigO_refl (fun j : ℕ ↦ (orbit.state j).ε ^ 2) atTop)
    refine hmul.congr' (Eventually.of_forall ?_) (Eventually.of_forall ?_)
    · intro j
      ring
    · intro j
      simp
  intro Clim hClim σ
  have hbig : (fun j : ℕ ↦
        ‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
          (orbit.state j).amplitude) =O[atTop]
      (fun j : ℕ ↦ (orbit.state j).ε ^ 3) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨C, Eventually.of_forall ?_⟩
    intro j
    simpa only [Real.norm_eq_abs, norm_pow] using hbound Clim hClim j σ
  exact hbig.trans_isLittleO hcubeLittleSquare

/-- A monotone right-hand modulus uniformly bounds both phase-radius errors by
the square of the cycle scale over all sufficiently small initial scales. -/
theorem slowCurvePhaseRadiusErrorUniform (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ ωR : ℝ → ℝ,
      ((∀ η ∈ Set.Ioc 0 εbar, 0 ≤ ωR η) ∧
          MonotoneOn ωR (Set.Ioc 0 εbar) ∧ Tendsto ωR (𝓝[>] 0) (𝓝 0)) ∧
        ∀ η ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 η,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
              ∀ j : ℕ, ∀ σ : Fin 2,
                |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
                    (orbit.state j).amplitude| ≤
                  ωR η * (orbit.state j).ε ^ 2 := by
  obtain ⟨εbar, hεbar, C, hC, hcore⟩ :=
    slowCurvePhaseRadiusErrorCubeBound p h h_invariant h_pJet h_hJet
  let ωR : ℝ → ℝ := fun η ↦ C * η
  refine ⟨εbar, hεbar, ωR, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro η hη
      exact mul_nonneg hC.le hη.1.le
    · intro a ha b hb hab
      exact mul_le_mul_of_nonneg_left hab hC.le
    · have hc : ContinuousAt ωR 0 := by
        dsimp only [ωR]
        fun_prop
      have ht : Tendsto ωR (𝓝 0) (𝓝 0) := by
        convert hc.tendsto using 1
        norm_num [ωR]
      exact ht.mono_left inf_le_left
  · intro η hη ε₀ hε₀
    dsimp only
    let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
    have hεCore : ε₀ ∈ Set.Ioc 0 εbar :=
      ⟨hε₀.1, hε₀.2.trans hη.2⟩
    have hscale := (hcore ε₀ hεCore).1
    have hbound := (hcore ε₀ hεCore).2
    intro Clim hClim j σ
    have hpositive : 0 ≤ (orbit.state j).ε ^ 2 := sq_nonneg _
    calc
      |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
          (orbit.state j).amplitude| ≤
          C * |(orbit.state j).ε| ^ 3 := hbound Clim hClim j σ
      _ = C * (orbit.state j).ε * (orbit.state j).ε ^ 2 := by
        rw [abs_of_pos (hscale j).1]
        ring
      _ ≤ C * η * (orbit.state j).ε ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((hscale j).2.trans hε₀.2) hC.le)
          hpositive
      _ = ωR η * (orbit.state j).ε ^ 2 := by rfl

end DFP.TwoPhaseOrbit
