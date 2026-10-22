/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.BrownianMotionVectorStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_74
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Lemma_25_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Remark_25_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_2_1

open Filter MeasureTheory ProbabilityTheory Topology InnerProductSpace Laplacian
open scoped InnerProductSpace Manifold

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

/-- Helper for Theorem 25.38: a Brownian vector started at a deterministic point has almost surely
continuous sample paths. -/
private theorem brownianVectorStartedAt_aeContinuous
    {μ : Measure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt μ W x) :
    ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω) := by
  have hcont_coord :
      ∀ i : Fin d, ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω i) := by
    intro i
    -- Proof comment: each coordinate owner already carries the almost-sure continuity statement.
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      (hW.isBrownianMotionStartedAt i).continuous_paths
  have hall :
      ∀ᵐ ω ∂μ, ∀ i : Fin d, Continuous (fun t : NNReal ↦ W t ω i) := by
    rw [ae_all_iff]
    intro i
    exact hcont_coord i
  filter_upwards [hall] with ω hω
  have hcoords : Continuous (fun t : NNReal ↦ fun i : Fin d ↦ W t ω i) :=
    continuous_pi fun i ↦ hω i
  -- Proof comment: continuity of the Euclidean path is coordinatewise continuity on the finite
  -- product model of `State`.
  simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp hcoords

/-- Helper for Theorem 25.38: a Brownian vector started at a deterministic point also starts there
almost surely at time `0` as a `State`-valued process. -/
private theorem brownianVectorStart_ae_eq_const
    (μ : ProbabilityMeasure Ω)
    {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x := by
  have hcoords :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ i : Fin d, W 0 ω i = x i := by
    rw [ae_all_iff]
    intro i
    exact
      brownianStart_ae_eq_const_of_measurable
        ((hW.isBrownianMotionStartedAt i).stronglyMeasurable 0).measurable
        (hW.isBrownianMotionStartedAt i)
  -- Proof comment: coordinatewise almost-sure equality upgrades to equality in the Euclidean
  -- state space by extensionality.
  filter_upwards [hcoords] with ω hω
  ext i
  exact hω i

/-- Helper for Theorem 25.38: if every sample path is continuous and the exit time from `U` is
almost surely finite, then the exit clock is a stopping time for the natural filtration. -/
private theorem stageExit_isStoppingTime_of_continuous_of_aeExitFinite
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤) :
    IsStoppingTime
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (hittingAfter W Uᶜ 0) := by
  classical
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  let D : NNReal → Ω → ℝ := fun t ω ↦ Metric.infDist (W t ω) Uᶜ
  have hUne : U ≠ Set.univ := by
    intro hUuniv
    have hTop :
        ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω = ⊤ := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      simp [hUuniv]
    have hFalse : ∀ᵐ ω ∂(μ : Measure Ω), False := by
      filter_upwards [hExitFinite, hTop] with ω hωfin hωtop
      exact (ne_of_lt hωfin) hωtop
    have hUnivZero : (μ : Measure Ω) Set.univ = 0 := by
      simp [ae_iff] at hFalse
    have hUnivOne : (μ : Measure Ω) Set.univ = 1 := by
      simp
    rw [hUnivZero] at hUnivOne
    norm_num at hUnivOne
  have hUc_nonempty : (Uᶜ : Set State).Nonempty := Set.nonempty_compl.2 hUne
  have hDsm : ∀ t : NNReal, StronglyMeasurable (D t) := by
    intro t
    -- Proof comment: each distance slice is a continuous observable of the Brownian state at
    -- time `t`.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWsm t).measurable).stronglyMeasurable
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hDcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ D t ω := by
    intro ω
    -- Proof comment: the distance-to-complement process inherits continuity from the path of
    -- `W`.
    exact (Metric.continuous_infDist_pt (Uᶜ)).comp (hWcont ω)
  have hDadapted : Adapted (Filtration.natural W hWsm) D := by
    intro t
    -- Proof comment: the distance slice at time `t` only depends on the Brownian state at the
    -- same time.
    exact
      ((Metric.continuous_infDist_pt (Uᶜ)).measurable.comp
        (hWstrong.stronglyMeasurable_le (i := t) (j := t) le_rfl).measurable)
  have hDnat :
      Filtration.natural D hDsm ≤ Filtration.natural W hWsm :=
    (adapted_iff_natural_le hDsm).1 hDadapted
  have hτdist :
      IsStoppingTime (Filtration.natural D hDsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    have hpair : ({(0 : ℝ), 0} : Set ℝ) = ({0} : Set ℝ) := by
      ext y
      simp
    -- Proof comment: the exit clock from `U` is the zero-hitting time of the distance process.
    simpa [hpair] using
      twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := D) hDsm hDcont (a := 0) (b := 0)
  have hEqτ :
      hittingAfter W Uᶜ 0 = hittingAfter D ({0} : Set ℝ) 0 := by
    ext ω
    have hclosedUc : IsClosed (Uᶜ : Set State) := isClosed_compl_iff.mpr hUo
    have hCond :
        (∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ) ↔
          ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := by
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    change
      (if ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ Uᶜ} : NNReal) : ENNReal)
        else ⊤) =
        (if ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ D i ω ∈ ({0} : Set ℝ)} : NNReal) :
            ENNReal)
        else ⊤)
    by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ Uᶜ
    · have h' : ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := hCond.mp h
      rw [if_pos h, if_pos h']
      congr 1
      ext
      simp [D, Set.mem_singleton_iff, hclosedUc.mem_iff_infDist_zero hUc_nonempty]
    · have h' : ¬ ∃ j, (0 : NNReal) ≤ j ∧ D j ω ∈ ({0} : Set ℝ) := mt hCond.mpr h
      -- Proof comment: if neither process ever reaches its target set, both clocks stay at `⊤`.
      rw [if_neg h, if_neg h']
  have hτdistW :
      IsStoppingTime (Filtration.natural W hWsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    intro i
    exact hDnat i _ (hτdist i)
  -- Proof comment: rewrite the exit clock through the distance process and transport the scalar
  -- stopping-time owner back to the Brownian natural filtration.
  simpa [hEqτ] using hτdistW

/-- Helper for Theorem 25.38: stopping preserves continuity of `State`-valued sample paths. -/
private theorem continuous_stoppedVectorProcess_of_continuous
    {X : VectorProcess} {σ : Ω → ENNReal} {ω : Ω}
    (hXCont : Continuous fun t : NNReal ↦ X t ω) :
    Continuous fun t : NNReal ↦ stoppedProcess X σ t ω := by
  have hfinite : ∀ t : NNReal, min (t : ENNReal) (σ ω) ≠ ⊤ := fun t ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  let clipped : NNReal → {s : ENNReal | s ≠ ⊤} := fun t ↦
    ⟨min (t : ENNReal) (σ ω), hfinite t⟩
  have hClipped : Continuous clipped := by
    -- Proof comment: the stopped path is the original path precomposed with the clipped time
    -- map `t ↦ min(t, σ(ω))`.
    exact (ENNReal.continuous_coe.inf continuous_const).subtype_mk hfinite
  have hTime :
      Continuous fun t : NNReal ↦ WithTop.untop (clipped t).1 (clipped t).2 := by
    simpa [clipped] using (WithTop.continuous_untop.comp hClipped)
  have hEq :
      (fun t : NNReal ↦ stoppedProcess X σ t ω) =
        fun t : NNReal ↦ X (WithTop.untop (clipped t).1 (clipped t).2) ω := by
    funext t
    change X ((min (t : ENNReal) (σ ω)).untopA) ω =
      X (WithTop.untop (min (t : ENNReal) (σ ω)) (hfinite t)) ω
    rw [WithTop.untopA_eq_untop (hfinite t)]
    rfl
  -- Proof comment: after normalizing the stopped path to a clipped-time composition, continuity
  -- is inherited from the original path.
  rw [hEq]
  exact hXCont.comp hTime

/-- Helper for Theorem 25.38: after recentering the Brownian path at `x` and patching only the
time-zero value, adding `x` back recovers the original path at every deterministic time outside
one null set. -/
private theorem stageTranslatedPatchedBrownian_ae_allTimes_eq_original
    (μ : ProbabilityMeasure Ω)
    {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x + B t ω = W t ω := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  filter_upwards [hStartAe] with ω hω t
  by_cases ht : t = 0
  · subst ht
    -- Proof comment: at time `0`, the patched translation is literally `0`, so adding back `x`
    -- returns the deterministic start value.
    simpa [B, hω]
  · -- Proof comment: away from time `0`, the subtraction of `x` is exactly cancelled by adding
    -- `x` back.
    simpa [B, ht, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 25.38: if `x + B t ω = W t ω` holds at every deterministic time, then the
same translation identity persists after stopping both paths at the same clock. -/
private theorem translatedPatchedBrownian_stopped_eq_original
    {W B : VectorProcess} {τ : Ω → ENNReal} {x : State} {ω : Ω}
    (hEq : ∀ t : NNReal, x + B t ω = W t ω)
    (t : NNReal) :
    x + stoppedProcess B τ t ω = stoppedProcess W τ t ω := by
  by_cases hτ : τ ω = ⊤
  · -- Proof comment: if the stop never occurs, both stopped paths are just the original paths at
    -- time `t`.
    simpa [stoppedProcess, hτ] using hEq t
  · let s : NNReal := (τ ω).untopA
    have hs : ((s : NNReal) : ENNReal) = τ ω := by
      dsimp [s]
      rw [WithTop.untopA_eq_untop hτ]
      exact WithTop.coe_untop _ _
    by_cases ht : s ≤ t
    · have hτle : τ ω ≤ (t : ENNReal) := by
        rw [← hs]
        exact_mod_cast ht
      have hBstop :
          stoppedProcess B τ t ω = B s ω := by
        simpa [s] using
          (stoppedProcess_eq_of_ge (u := B) (τ := τ) (ω := ω) (i := t) hτle)
      have hWstop :
          stoppedProcess W τ t ω = W s ω := by
        simpa [s] using
          (stoppedProcess_eq_of_ge (u := W) (τ := τ) (ω := ω) (i := t) hτle)
      -- Proof comment: after the stopping time, both processes are frozen at the same clipped
      -- time `s`.
      simpa [hBstop, hWstop] using hEq s
    · have hτgt : t < s := lt_of_not_ge ht
      have htle : (t : ENNReal) ≤ τ ω := by
        rw [← hs]
        exact le_of_lt (by exact_mod_cast hτgt)
      have hBstop :
          stoppedProcess B τ t ω = B t ω := by
        exact stoppedProcess_eq_of_le (u := B) (τ := τ) (ω := ω) (i := t) htle
      have hWstop :
          stoppedProcess W τ t ω = W t ω := by
        exact stoppedProcess_eq_of_le (u := W) (τ := τ) (ω := ω) (i := t) htle
      -- Proof comment: before the stopping time, both stopped paths still agree with the raw
      -- processes at time `t`.
      simpa [hBstop, hWstop] using hEq t

/-- Helper for Theorem 25.38: harmonicity on a buffer implies pointwise vanishing of the
Laplacian on that buffer. -/
private theorem laplacian_eq_zero_on_buffer
    {F : State → ℝ} {V : Set State}
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    {z : State} (hz : z ∈ V) :
    Δ F z = 0 := by
  -- Proof comment: the harmonic-neighborhood owner gives an eventual identity `ΔF = 0` near
  -- `z`, and evaluating that neighborhood identity at `z` closes the goal.
  exact (hFharm z hz).2.self_of_nhds

/-- Helper for Theorem 25.38: evaluating `F` on the translated stopped path agrees almost surely
at every time with evaluating `F` on the original stopped Brownian path. -/
private theorem stageStoppedTranslatedSurface_eq_visibleIncrement
    {μ : ProbabilityMeasure Ω}
    {W : VectorProcess} {U : Set State} {F : State → ℝ} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      F (x + stoppedProcess B (hittingAfter W Uᶜ 0) t ω) - F x =
        F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hTranslate :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x + B t ω = W t ω :=
    stageTranslatedPatchedBrownian_ae_allTimes_eq_original μ hW
  filter_upwards [hTranslate] with ω hω t
  -- Proof comment: rewrite the shifted stopped path back to the original Brownian stop before
  -- evaluating `F`.
  rw [translatedPatchedBrownian_stopped_eq_original
    (W := W) (B := B) (τ := hittingAfter W Uᶜ 0) (x := x) (ω := ω) hω t]

/-- Helper for Theorem 25.38: once the Laplacian vanishes along the stopped path, the associated
deterministic drift integral is identically zero. -/
private theorem stoppedLaplacianIntegral_eq_zero
    {μ : Measure Ω} {W : VectorProcess} {τ : Ω → ENNReal} {F : State → ℝ}
    (hLap :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        Δ F (stoppedProcess W τ t ω) = 0) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        ((1 : ℝ) / 2) * Δ F (stoppedProcess W τ s.toNNReal ω) = 0 := by
  filter_upwards [hLap] with ω hω t
  have hIntegrandZero :
      (fun s : ℝ ↦ ((1 : ℝ) / 2) * Δ F (stoppedProcess W τ s.toNNReal ω)) =
        fun _ : ℝ ↦ (0 : ℝ) := by
    funext s
    simp [hω s.toNNReal]
  -- Proof comment: once the integrand is rewritten to the zero function pointwise, the stopped
  -- drift primitive collapses immediately.
  rw [hIntegrandZero]
  simp

/-- Helper for Theorem 25.38: compact closure gives a deterministic uniform bound for a Dirichlet
solution on `closure G`. -/
private theorem existsAbsLeOnClosure
    {G : Set State} {f : frontier G → ℝ} {u : State → ℝ}
    (hGcpt : IsCompact (closure G)) (hu : SolvesDirichletProblem G f u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure G, |u z| ≤ C := by
  have hImageCompact : IsCompact (u '' closure G) :=
    hGcpt.image_of_continuousOn hu.continuousOn_closure
  rcases hImageCompact.bddBelow with ⟨l, hl⟩
  rcases hImageCompact.bddAbove with ⟨r, hr⟩
  refine ⟨max |l| |r|, by positivity, ?_⟩
  intro z hz
  have hzImage : u z ∈ u '' closure G := ⟨z, hz, rfl⟩
  have hlz : l ≤ u z := hl hzImage
  have hrz : u z ≤ r := hr hzImage
  -- Proof comment: compactness bounds the image of `u`, so the larger endpoint controls the
  -- absolute value on the whole closed domain.
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc
      -max |l| |r| ≤ -|l| := neg_le_neg (le_max_left |l| |r|)
      _ ≤ l := neg_abs_le l
      _ ≤ u z := hlz
  · calc
      u z ≤ r := hrz
      _ ≤ |r| := le_abs_self r
      _ ≤ max |l| |r| := le_max_right |l| |r|

/-- Helper for Theorem 25.38: a compact subset of an open set admits an open buffer whose closure
still stays inside the ambient open set. -/
private theorem exists_open_buffer_of_isCompact_subset_open
    {K G : Set State}
    (hKcompact : IsCompact K)
    (hKG : K ⊆ G)
    (hGo : IsOpen G) :
    ∃ T : Set State, IsOpen T ∧ K ⊆ T ∧ closure T ⊆ G := by
  have hGnhds : G ∈ 𝓝ˢ K := hGo.mem_nhdsSet.2 hKG
  rcases hKcompact.exists_isOpen_closure_subset hGnhds with ⟨T, hTo, hKT, hTcl⟩
  -- Proof comment: compactness lets us shrink the neighborhood filter of `K` to one open set
  -- whose closure already lies inside `G`.
  exact ⟨T, hTo, hKT, hTcl⟩

/-- Helper for Theorem 25.38: a harmonic function on an open buffer around a precompact stage
admits a global `C²` extension that stays harmonic on the stage and agrees with the original
function there. -/
private theorem existsStageHarmonicExtension
    {V T G : Set State} {u : State → ℝ}
    (hVT : closure V ⊆ T) (hTG : closure T ⊆ G) (hTo : IsOpen T)
    (hu : InnerProductSpace.HarmonicOnNhd u G) :
    ∃ F : State → ℝ,
      ContDiff ℝ 2 F ∧
      InnerProductSpace.HarmonicOnNhd F V ∧
      Set.EqOn F u V := by
  rcases exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, State)) (M := State) (n := (2 : ℕ∞)) (s := closure V) (t := T)
      isClosed_closure
      (by simpa [hTo.interior_eq] using hVT) with
    ⟨φ, hOne, hZero, _hRange⟩
  let F : State → ℝ := fun x ↦ φ x * u x
  have hφ : ContDiff ℝ 2 φ := by
    simpa using φ.contMDiff.contDiff
  have hF_contDiff : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ closure T
    · have hxG : x ∈ G := hTG hx
      -- Proof comment: on the closure of the cutoff support, both factors are already `C²`.
      exact (hφ.contDiffAt).mul (hu x hxG).1
    · have hFzero : F =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        have hOutside : (closure T)ᶜ ∈ 𝓝 x :=
          isClosed_closure.isOpen_compl.mem_nhds hx
        filter_upwards [hOutside] with y hy
        have hyT : y ∉ T := fun hyT ↦ hy (subset_closure hyT)
        simp [F, hZero y hyT]
      -- Proof comment: away from the buffer, the cutoff vanishes on a whole neighborhood.
      exact contDiffAt_const.congr_of_eventuallyEq hFzero
  have hF_harmonic : InnerProductSpace.HarmonicOnNhd F V := by
    intro x hxV
    have hxT : x ∈ T := hVT (subset_closure hxV)
    have hxG : x ∈ G := hTG (subset_closure hxT)
    have hφx : ∀ᶠ y in 𝓝 x, φ y = 1 :=
      mem_nhdsSet_iff_forall.mp hOne x (subset_closure hxV)
    have hEq : F =ᶠ[𝓝 x] u := by
      filter_upwards [hφx] with y hy
      simp [F, hy]
    -- Proof comment: near points of `V`, the cutoff is identically `1`, so the extension is
    -- literally the original harmonic function.
    exact (InnerProductSpace.harmonicAt_congr_nhds hEq).2 (hu x hxG)
  have hF_eq : Set.EqOn F u V := by
    intro x hxV
    have hφx : ∀ᶠ y in 𝓝 x, φ y = 1 :=
      mem_nhdsSet_iff_forall.mp hOne x (subset_closure hxV)
    -- Proof comment: evaluating the neighborhood identity at the stage point gives pointwise
    -- agreement on `V`.
    have hx1 : φ x = 1 := hφx.self_of_nhds
    simp [F, hx1]
  exact ⟨F, hF_contDiff, hF_harmonic, hF_eq⟩

/-- Helper for Theorem 25.38: starting from a point of an open domain, one can choose an
increasing exhaustion by inner open stages whose closures stay compactly inside the domain. -/
private theorem existsInnerExhaustionStartingAt
    {G : Set State} (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    {x : State} (hx : x ∈ G) :
    ∃ U : ℕ → Set State,
      (∀ n, IsOpen (U n)) ∧
      (∀ n, x ∈ U n) ∧
      (∀ n, IsCompact (closure (U n))) ∧
      (∀ n, closure (U n) ⊆ G) ∧
      Monotone U ∧
      (⋃ n, U n) = G := by
  by_cases hGcempty : Gᶜ = ∅
  · let U : ℕ → Set State := fun _ ↦ G
    have hGuniv : G = Set.univ := by
      ext y
      have hyc : y ∉ Gᶜ := by simpa [hGcempty]
      simpa using hyc
    refine ⟨U, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      simpa [U] using hG
    · intro n
      simpa [U] using hx
    · intro n
      simpa [U, hGcempty, closure_univ] using hGcpt
    · intro n
      simpa [U, hGuniv]
    · intro m n hmn
      simp [U]
    · ext y
      simp [U, hGuniv]
  · have hGcne : (Gᶜ : Set State).Nonempty := Set.nonempty_iff_ne_empty.mpr hGcempty
    let δ : ℝ := Metric.infDist x Gᶜ
    have hδpos : 0 < δ := by
      have hxnot : x ∉ Gᶜ := by simpa using hx
      exact ((isClosed_compl_iff.mpr hG).notMem_iff_infDist_pos hGcne).mp hxnot
    let r : ℕ → ℝ := fun n ↦ min (δ / 2) (1 / ((n + 1 : ℕ) : ℝ))
    let U : ℕ → Set State := fun n ↦ {y | r n < Metric.infDist y Gᶜ}
    have hU_open : ∀ n, IsOpen (U n) := by
      intro n
      -- Proof comment: each stage is a strict superlevel set of the continuous distance-to-
      -- complement map.
      simpa [U] using
        (Metric.continuous_infDist_pt (Gᶜ)).isOpen_preimage (Set.Ioi (r n)) isOpen_Ioi
    have hU_x : ∀ n, x ∈ U n := by
      intro n
      have hrlt : r n < δ := by
        calc
          r n ≤ δ / 2 := min_le_left _ _
          _ < δ := by linarith
      simpa [U, δ] using hrlt
    have hrpos : ∀ n, 0 < r n := by
      intro n
      have hInvPos : 0 < (1 / ((n + 1 : ℕ) : ℝ)) := by
        positivity
      exact lt_min (by linarith) hInvPos
    have hU_closure_subset : ∀ n, closure (U n) ⊆ G := by
      intro n
      let S : Set State := {y | r n ≤ Metric.infDist y Gᶜ}
      have hUsubsetS : U n ⊆ S := by
        intro y hy
        change r n ≤ Metric.infDist y Gᶜ
        exact le_of_lt (by simpa [U] using hy)
      have hSclosed : IsClosed S := by
        -- Proof comment: pass from the open superlevel set to the closed weak superlevel set
        -- before pushing the closure back into `G`.
        simpa [S] using
          (isClosed_le continuous_const (Metric.continuous_infDist_pt (Gᶜ)))
      refine subset_trans (closure_minimal hUsubsetS hSclosed) ?_
      · intro y hy
        change r n ≤ Metric.infDist y Gᶜ at hy
        by_contra hyc
        have : Metric.infDist y Gᶜ = 0 := Metric.infDist_zero_of_mem hyc
        have hle : r n ≤ 0 := by simpa [this] using hy
        exact (not_le_of_gt (hrpos n)) hle
    have hU_compact : ∀ n, IsCompact (closure (U n)) := by
      intro n
      refine IsCompact.of_isClosed_subset hGcpt isClosed_closure ?_
      exact subset_trans (hU_closure_subset n) subset_closure
    have hU_mono : Monotone U := by
      intro m n hmn y hy
      have hcast : ((m + 1 : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ hmn
      have hInv :
          (1 / ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
        exact one_div_le_one_div_of_le (by positivity) hcast
      have hrmono : r n ≤ r m := min_le_min_left _ hInv
      -- Proof comment: the distance threshold decreases with `n`, so the superlevel sets grow.
      exact lt_of_le_of_lt hrmono hy
    have hUnion : (⋃ n, U n) = G := by
      ext y
      constructor
      · intro hy
        rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
        exact hU_closure_subset n (subset_closure hyn)
      · intro hyG
        have hypos : 0 < Metric.infDist y Gᶜ := by
          have hynot : y ∉ Gᶜ := by simpa using hyG
          exact ((isClosed_compl_iff.mpr hG).notMem_iff_infDist_pos hGcne).mp hynot
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hypos
        have hn' : 1 / ((n + 1 : ℕ) : ℝ) < Metric.infDist y Gᶜ := by
          simpa using hn
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        have hrlt :
            r n < Metric.infDist y Gᶜ := by
          calc
            r n ≤ 1 / ((n + 1 : ℕ) : ℝ) := min_le_right _ _
            _ < Metric.infDist y Gᶜ := hn'
        exact hrlt
    exact ⟨U, hU_open, hU_x, hU_compact, hU_closure_subset, hU_mono, hUnion⟩

/-- Helper for Theorem 25.38: a function continuous on `closure G` admits a global continuous
extension agreeing with the original function on `closure G`. -/
private theorem existsContinuousExtensionOnClosure
    {G : Set State} {u : State → ℝ}
    (hu : ContinuousOn u (closure G)) :
    ∃ U : State → ℝ, Continuous U ∧ Set.EqOn U u (closure G) := by
  let uCl : C(closure G, ℝ) :=
    ⟨fun z ↦ u z, continuousOn_iff_continuous_restrict.mp hu⟩
  rcases
      ContinuousMap.exists_restrict_eq
        (s := closure G)
        isClosed_closure
        uCl with ⟨U, hU⟩
  refine ⟨U, U.continuous, ?_⟩
  intro z hz
  -- Proof comment: the Tietze extension restricts back to the original continuous map on the
  -- closed set `closure G`, so evaluation at `z` recovers the original value.
  have hzEq : U.restrict (closure G) ⟨z, hz⟩ = uCl ⟨z, hz⟩ := by
    exact congrArg (fun f : C(closure G, ℝ) ↦ f ⟨z, hz⟩) hU
  simpa [uCl] using hzEq

/-- Helper for Theorem 25.38: subtracting the deterministic starting point from a scalar Brownian
motion started at `x` produces a Brownian motion started at `0`. -/
private theorem brownianStartedAt_sub_const_startedAtZero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ B t ω - x) 0 := by
  refine
    { stronglyMeasurable := ?_
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: subtracting a constant preserves strong measurability at every time.
    intro t
    exact (hB.stronglyMeasurable t).sub stronglyMeasurable_const
  · -- Proof comment: the recentered zero-time event is exactly the original start event at `x`.
    have hpreimage :
        (fun ω ↦ B 0 ω - x) ⁻¹' ({0} : Set ℝ) = B 0 ⁻¹' ({x} : Set ℝ) := by
      ext ω
      constructor
      · intro hω
        change B 0 ω - x = 0 at hω
        change B 0 ω = x
        linarith
      · intro hω
        have hxω : B 0 ω = x := by
          simpa using hω
        change B 0 ω - x = 0
        simp [hxω]
    rw [hpreimage]
    exact hB.start
  · -- Proof comment: subtracting the same constant from each time slice leaves increments
    -- unchanged.
    intro n t ht
    simpa only [sub_sub_sub_cancel_right] using hB.indepIncrements n t ht
  · -- Proof comment: the same cancellation preserves stationarity of increments.
    intro r s t
    simpa only [sub_sub_sub_cancel_right] using hB.stationaryIncrements r s t
  · -- Proof comment: the time-`t` Gaussian marginal is translated from mean `x` to mean `0`.
    intro t ht
    simpa using ProbabilityTheory.gaussianReal_sub_const (hB.gaussian_marginal ht) x
  · -- Proof comment: sample-path continuity is preserved under subtraction of a deterministic
    -- constant.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.sub continuous_const

/-- Helper for Theorem 25.38: covariance is unchanged under almost-everywhere replacement of the
two random variables. -/
private theorem covariance_congr_ae_theorem25_38
    {μ : Measure Ω} {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : μ[X] = μ[X'] := MeasureTheory.integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := MeasureTheory.integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Theorem 25.38: patching the time-zero value of a Brownian motion started at `0`
to the literal constant `0` yields the standard Brownian spelling. -/
private theorem pointwiseZeroVersion_isBrownianMotion_startedAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotionStartedAt μ B 0) :
    IsBrownianMotion μ (fun t ω ↦ if t = 0 then 0 else B t ω) := by
  let B0 : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else B t ω
  have hZeroAe : B 0 =ᵐ[μ] fun _ ↦ 0 :=
    brownianStart_ae_eq_const_of_measurable (hB.stronglyMeasurable 0).measurable hB
  have hmod : ∀ t : NNReal, B0 t =ᵐ[μ] B t := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simpa [B0] using hZeroAe.symm
    · exact Filter.Eventually.of_forall fun ω ↦ by simp [B0, ht]
  have hgauss : IsGaussianProcess B μ :=
    IsBrownianMotionStartedAt.isGaussianProcess_zero hB
  have hgauss0 : IsGaussianProcess B0 μ := hgauss.congr fun t ↦ (hmod t).symm
  have hmean : ∀ t : NNReal, ∫ ω, B t ω ∂μ = 0 :=
    (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance μ B).1 hB
      |>.2.2.1
  have hmean0 : ∀ t : NNReal, ∫ ω, B0 t ω ∂μ = 0 := by
    intro t
    -- Proof comment: the pointwise-zero version is a deterministic-time modification of `B`, so
    -- the centered mean identity transports slice by slice.
    rw [integral_congr_ae (hmod t), hmean t]
  have hcov0 : ∀ s t : NNReal, cov[B0 s, B0 t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance only depends on the deterministic-time slices up to almost-
    -- everywhere equality.
    rw [covariance_congr_ae_theorem25_38 (hmod s) (hmod t), startedAtZero_covariance_eq hB s t]
  have hcont0 : HasAlmostSurelyContinuousPaths μ B0 := by
    -- Proof comment: on the full-measure start event `B 0 = 0`, the patched path agrees with the
    -- original continuous Brownian path at every time.
    filter_upwards [hB.continuous_paths, hZeroAe] with ω hωcont hω0
    have hEq : (fun t : NNReal ↦ B0 t ω) = fun t : NNReal ↦ B t ω := by
      funext t
      by_cases ht : t = 0
      · subst ht
        simpa [B0] using hω0.symm
      · simp [B0, ht]
    have hPathEq : processPath B0 ω = processPath B ω := by
      simpa [processPath] using hEq
    simpa [HasAlmostSurelyContinuousPaths] using hPathEq ▸ hωcont
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ B0).2
      ⟨by
          funext ω
          simp [B0]
        , hgauss0, hmean0, hcov0, hcont0⟩

/-- Helper for Theorem 25.38: recentering a Brownian vector started at `x` and patching only the
time-zero value produces a standard Brownian vector. -/
private theorem shiftedPatchedVector_isStandardBrownian
    (μ : ProbabilityMeasure Ω)
    {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    IsStandardBrownianMotionVector (μ : Measure Ω) B := by
  intro B
  refine
    { isBrownianMotion := ?_
      iIndepFun := ?_ }
  · intro i
    have hBi0 :
        IsBrownianMotionStartedAt (μ : Measure Ω) (fun t ω ↦ W t ω i - x i) 0 := by
      -- Proof comment: recenter the `i`-th coordinate at its deterministic start value.
      simpa using
        brownianStartedAt_sub_const_startedAtZero
          (μ := (μ : Measure Ω))
          (B := fun t ω ↦ W t ω i)
          (x := x i)
          (hW.isBrownianMotionStartedAt i)
    -- Proof comment: the only remaining normalization is the literal time-zero patch.
    convert
      pointwiseZeroVersion_isBrownianMotion_startedAtZero
        (μ := (μ : Measure Ω))
        (B := fun t ω ↦ W t ω i - x i)
        hBi0 using 1
    ext t ω
    by_cases ht : t = 0 <;> simp [B, ht]
  · -- Proof comment: coordinate-path independence is stable under deterministic recentering and
    -- the time-zero patch, because both are measurable pathwise transforms.
    convert
      hW.iIndepFun.comp (fun i f t ↦ if t = 0 then 0 else f t - x i) (by
        intro i
        exact measurable_pi_lambda _ fun t ↦ by
          by_cases ht : t = 0
          · simp [ht]
          · simpa [ht] using (measurable_pi_apply t).sub measurable_const) using 1
    ext i ω t
    by_cases ht : t = 0 <;> simp [B, ht]

/-- Helper for Theorem 25.38: a standard Brownian vector is a Gaussian process in the Euclidean
state space. -/
private theorem standardBrownianVector_isGaussianProcess_theorem25_38
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) :
    IsGaussianProcess W μ := by
  classical
  letI : IsStandardBrownianMotionVector μ W := hW
  let ψ : State ≃L[ℝ] (Fin d → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)
  refine
    { hasGaussianLaw := fun I ↦ ?_ }
  let Xi : Fin d → Ω → I → ℝ := fun i ω t ↦ W t ω i
  have hXi_gauss : ∀ i : Fin d, HasGaussianLaw (Xi i) μ := by
    intro i
    let hBi : IsBrownianMotion μ (fun t ω ↦ W t ω i) := inferInstance
    let hGi : IsGaussianProcess (fun t ω ↦ W t ω i) μ :=
      IsBrownianMotion.isGaussianProcess hBi
    simpa [Xi] using hGi.hasGaussianLaw I
  have hXi_indep : iIndepFun Xi μ := by
    -- Proof comment: coordinate-path independence survives restriction to a finite time set.
    refine hW.iIndepFun.comp (fun _ f ↦ I.restrict f) ?_
    intro i
    exact measurable_pi_lambda _ fun t ↦ measurable_pi_apply (t : NNReal)
  let L : (Fin d → I → ℝ) →L[ℝ] I → State :=
    { toFun := fun x t ↦ ψ.symm (fun i ↦ x i t)
      map_add' := by
        intro x y
        ext t i
        rfl
      map_smul' := by
        intro c x
        ext t i
        rfl
      cont := by
        refine continuous_pi fun t ↦ ?_
        exact ψ.symm.continuous.comp <| continuous_pi fun i ↦
          (continuous_apply t).comp (continuous_apply i) }
  have hgauss :
      HasGaussianLaw (fun ω ↦ fun i ↦ Xi i ω) μ :=
    ProbabilityTheory.iIndepFun.hasGaussianLaw hXi_gauss hXi_indep
  -- Proof comment: repackage the coordinatewise Gaussian law back into the Euclidean state
  -- space used by the Brownian vector.
  simpa [Xi] using hgauss.map L

/-- Helper for Theorem 25.38: almost every sample path of a standard Brownian vector carries the
full Kronecker-delta coordinate quadratic-covariation family, written directly on the canonical
vector-path coordinates. -/
private theorem standardBrownianCoordinateCovariationFamily_ae_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector (μ : Measure Ω) W) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
        ∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
            (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) j)
            (fun T ↦ if i = j then (T : ℝ) else 0) := by
  have hdiag :
      ∀ i : Fin d,
        ∀ᵐ ω ∂(μ : Measure Ω),
          ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (fun T ↦ (T : ℝ)) := by
    intro i
    filter_upwards
      [(hW.isBrownianMotion i).ae_tendsto_partitionQuadraticVariationApproximationUpTo
        Definition2158.dyadicPartitionSequence] with ω hω hcontω
    -- Proof comment: each coordinate path is scalar Brownian motion, so its quadratic variation
    -- converges to the deterministic clock.
    refine selfCovariation_of_tendstoQuadraticVariation ?_
    intro T
    simpa [vectorPathComponent, processPath] using hω T
  have hoff :
      ∀ i j : Fin d, i ≠ j →
        ∀ᵐ ω ∂(μ : Measure Ω),
          ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) j)
              0 := by
    intro i j hij
    filter_upwards
      [covariation_ae_eq_zero_of_indep_brownian
        (hW.isBrownianMotion i)
        (hW.isBrownianMotion j)
        (hW.iIndepFun.indepFun hij)] with ω hω hcontω
    -- Proof comment: distinct Brownian coordinates are independent, so their pathwise quadratic
    -- covariation vanishes on the same full-measure event.
    simpa [vectorPathComponent, processPath] using
      hω
        ((continuous_apply i).comp hcontω)
        ((continuous_apply j).comp hcontω)
  have hpair :
      ∀ i j : Fin d,
        ∀ᵐ ω ∂(μ : Measure Ω),
          ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ W s ω, hcontω⟩ : VectorPathSpace d) j)
              (fun T ↦ if i = j then (T : ℝ) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      filter_upwards [hdiag i] with ω hω hcontω
      -- Proof comment: on the diagonal the Kronecker primitive is exactly the time path.
      simpa using hω hcontω
    · filter_upwards [hoff i j hij] with ω hω hcontω
      -- Proof comment: off the diagonal the Kronecker primitive is identically zero.
      simpa [hij] using hω hcontω
  filter_upwards
    [ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ hpair i j] with ω hω hcontω i j
  -- Proof comment: intersect the finite coordinate family into one reusable almost-sure event.
  exact hω i j hcontω

/-- Helper for Theorem 25.38: the zero-patched centered path admits one almost-sure good event on
which it is continuous and lies in the Chapter 25 class `𝒞_qv^d` with the standard Brownian
Kronecker coordinate covariations. -/
private theorem zeroPatchedCenteredGoodPath_ae_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω),
      ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
        let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
        Xω ∈ (𝒞_qv^d) ∧
          ∀ i j : Fin d,
            HasQuadraticCovariationAlong
              (vectorPathComponent Xω i)
              (vectorPathComponent Xω j)
              (fun T ↦ if i = j then (T : ℝ) else 0) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hEqAe :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = W t ω - x := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_38
        (μ := μ) (W := W) (x := x) hW
  have hCovAe :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
          ∀ i j : Fin d,
            HasQuadraticCovariationAlong
              (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) i)
              (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) j)
              (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      standardBrownianCoordinateCovariationFamily_ae_theorem25_38
        (μ := μ)
        (W := B)
        (shiftedPatchedVector_isStandardBrownian (μ := μ) (W := W) (x := x) hW)
  filter_upwards [hEqAe, hCovAe] with ω hω hCovω
  have hRawCont : Continuous fun t : NNReal ↦ W t ω - x := by
    -- Proof comment: the unpatched centered path is continuous because the Brownian path is
    -- continuous and the deterministic center `x` is constant.
    simpa [sub_eq_add_neg] using (hWcont ω).add continuous_const
  have hcontω : Continuous fun t : NNReal ↦ B t ω := by
    -- Proof comment: on the almost-sure start event, the zero patch agrees at every time with
    -- the raw centered path, so continuity transports across that all-times equality.
    have hEq : (fun t : NNReal ↦ B t ω) = fun t : NNReal ↦ W t ω - x := funext hω
    exact hEq.symm ▸ hRawCont
  refine ⟨hcontω, ?_⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hFamily :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent Xω i)
          (vectorPathComponent Xω j)
          (fun T ↦ if i = j then (T : ℝ) else 0) := by
    intro i j
    simpa [Xω] using hCovω hcontω i j
  have hXω : Xω ∈ (𝒞_qv^d) := by
    refine (mem_𝒞_qv_d_iff_exists_family Xω).2 ?_
    refine ⟨fun i j ↦ fun T ↦ if i = j then (T : ℝ) else 0, ?_⟩
    intro i j
    exact hFamily i j
  -- Proof comment: one continuity witness and one Kronecker family already package the centered
  -- sample path into the Chapter 25 `𝒞_qv^d` interface.
  exact ⟨hXω, hFamily⟩

/-- Helper for Theorem 25.38: patching a Brownian motion started at `0` on one measurable null
set by the constant-zero path preserves the Brownian law and makes every sample path continuous.
This is the scalar owner bridge used to build a same-space continuous modification of a Brownian
vector started at a deterministic point. -/
private theorem zeroStarted_nullPatch_isBrownianMotion
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotionStartedAt μ B 0)
    {N : Set Ω} [DecidablePred (· ∈ N)] (hN_meas : MeasurableSet N) (hN_null : μ N = 0)
    (hcont : ∀ ω ∉ N, Continuous fun t : NNReal ↦ B t ω)
    (hzero : ∀ ω ∉ N, B 0 ω = 0) :
    IsBrownianMotion μ (fun t ω ↦ if ω ∈ N then 0 else B t ω) := by
  let Bc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else B t ω
  have hOutside : ∀ᵐ ω ∂μ, ω ∉ N := compl_mem_ae_iff.mpr hN_null
  have hmod : ∀ t : NNReal, Bc t =ᵐ[μ] B t := by
    intro t
    filter_upwards [hOutside] with ω hω
    simp [Bc, hω]
  have hgauss : IsGaussianProcess B μ :=
    IsBrownianMotionStartedAt.isGaussianProcess_zero hB
  have hgaussc : IsGaussianProcess Bc μ := hgauss.congr fun t ↦ (hmod t).symm
  have hmean : ∀ t : NNReal, ∫ ω, B t ω ∂μ = 0 :=
    (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance μ B).1 hB
      |>.2.2.1
  have hmeanc : ∀ t : NNReal, ∫ ω, Bc t ω ∂μ = 0 := by
    intro t
    -- Proof comment: deterministic-time null-set patching preserves the centered mean of each
    -- Brownian slice.
    rw [integral_congr_ae (hmod t), hmean t]
  have hcovc : ∀ s t : NNReal, cov[Bc s, Bc t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance is unchanged when both deterministic-time slices are replaced by
    -- the null-set patch almost everywhere.
    rw [covariance_congr_ae_theorem25_38 (hmod s) (hmod t), startedAtZero_covariance_eq hB s t]
  have hcontc : HasAlmostSurelyContinuousPaths μ Bc := by
    -- Proof comment: off the chosen null set the path is the original continuous sample path, and
    -- on the null set it is the constant-zero path.
    filter_upwards [hOutside] with ω hω
    by_cases hωN : ω ∈ N
    · have hPathEq : processPath Bc ω = fun _ : NNReal ↦ (0 : ℝ) := by
        funext t
        simp [processPath, Bc, hωN]
      simpa [HasAlmostSurelyContinuousPaths] using
        hPathEq ▸ (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
    · have hPathEq : processPath Bc ω = fun t : NNReal ↦ B t ω := by
        funext t
        simp [processPath, Bc, hωN]
      simpa [HasAlmostSurelyContinuousPaths] using hPathEq ▸ hcont ω hωN
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ Bc).2
      ⟨by
          funext ω
          by_cases hω : ω ∈ N
          · simp [Bc, hω]
          · simp [Bc, hω, hzero ω hω]
        , hgaussc, hmeanc, hcovc, hcontc⟩

/-- Helper for Theorem 25.38: a Brownian vector started at `x` admits a same-space modification
whose sample paths are everywhere continuous and which agrees with the original process at all
times outside one measurable null set. -/
private theorem existsContinuousBrownianVectorStartedAtModification
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    ∃ Wc : VectorProcess,
      IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x ∧
      (∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω) ∧
      (∀ ω : Ω, Wc 0 ω = x) ∧
      (∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, W t ω = Wc t ω) := by
  classical
  have hcont_ae :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous fun t : NNReal ↦ W t ω :=
    brownianVectorStartedAt_aeContinuous hW
  have hstart_ae :
      ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  have hgood :
      ∀ᵐ ω ∂(μ : Measure Ω), (Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x :=
    hcont_ae.and hstart_ae
  let bad : Set Ω := {ω | ¬ ((Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x)}
  have hbad_null : (μ : Measure Ω) bad = 0 := by
    simpa [bad] using (ae_iff.1 hgood)
  obtain ⟨N, hbad_subset, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hbad_null
  have hN_good :
      ∀ ω : Ω, ω ∉ N → (Continuous fun t : NNReal ↦ W t ω) ∧ W 0 ω = x := by
    intro ω hωN
    by_contra hbadω
    exact hωN (hbad_subset hbadω)
  let Wc : VectorProcess := fun t ω ↦ if ω ∈ N then x else W t ω
  have hWc_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa [Wc, hω] using (continuous_const : Continuous fun _ : NNReal ↦ x)
    · simpa [Wc, hω] using (hN_good ω hω).1
  have hWc_eq :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, W t ω = Wc t ω := by
    filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω t
    have hω' : ω ∉ N := by simpa using hω
    simp [Wc, hω']
  have hWc_start : ∀ ω : Ω, Wc 0 ω = x := by
    intro ω
    by_cases hω : ω ∈ N
    · simp [Wc, hω]
    · simpa [Wc, hω] using (hN_good ω hω).2
  have hWc_owner : IsBrownianMotionVectorStartedAt (μ : Measure Ω) Wc x := by
    refine
      { isBrownianMotionStartedAt := ?_
        iIndepFun := ?_ }
    · intro i
      let B : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
      let Bc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else B t ω
      have hB : IsBrownianMotionStartedAt (μ : Measure Ω) B 0 := by
        -- Proof comment: recenter the `i`-th coordinate at its deterministic start value.
        simpa [B] using
          brownianStartedAt_sub_const_startedAtZero
            (hW.isBrownianMotionStartedAt i)
      have hBc : IsBrownianMotion (μ : Measure Ω) Bc := by
        -- Proof comment: patch the recentered coordinate on the common null set so every sample
        -- path becomes continuous.
        apply zeroStarted_nullPatch_isBrownianMotion
          (μ := (μ : Measure Ω)) (B := B) hB hN_meas hN_null
        · intro ω hω
          have hcoord_cont : Continuous fun t : NNReal ↦ Wc t ω i := by
            simpa using
              (continuous_apply i).comp
                ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp (hWc_cont ω))
          simpa [Wc, hω] using hcoord_cont.sub continuous_const
        · intro ω hω
          have hi : W 0 ω i = x i := by
            simpa [Wc, hω] using congrArg (fun y : State ↦ y i) (hWc_start ω)
          simp [B, hi]
      -- Proof comment: adding the deterministic start value back recovers the patched coordinate
      -- of `Wc`.
      have hTranslated :
          IsBrownianMotionStartedAt
            (μ : Measure Ω) (fun t ω ↦ x i + Bc t ω) (x i) := by
        letI : IsProbabilityMeasure (μ : Measure Ω) := by infer_instance
        refine
          { stronglyMeasurable := fun t ↦ (hBc.stronglyMeasurable t).const_add (x i)
            start := ?_
            indepIncrements := ?_
            stationaryIncrements := ?_
            gaussian_marginal := ?_
            continuous_paths := ?_ }
        · have hpreimage : (fun ω ↦ x i + Bc 0 ω) ⁻¹' ({x i} : Set ℝ) = Set.univ := by
            ext ω
            simp [hBc.zero]
          rw [hpreimage]
          simp
        · rw [hasIndepIncrements_iff_nat]
          intro t ht
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            hBc.indepIncrements.nat (t := t) ht
        · intro r s t
          have hleft :
              (fun ω ↦ (x i + Bc ((s + t) + r) ω) - (x i + Bc (t + r) ω)) =
                (fun ω ↦ Bc ((s + t) + r) ω - Bc (t + r) ω) := by
            funext ω
            ring
          have hright :
              (fun ω ↦ (x i + Bc (s + r) ω) - (x i + Bc r ω)) =
                (fun ω ↦ Bc (s + r) ω - Bc r ω) := by
            funext ω
            ring
          simpa [hleft, hright] using hBc.stationaryIncrements r s t
        · intro t ht
          simpa [add_comm] using
            ProbabilityTheory.gaussianReal_add_const (hBc.gaussian_marginal ht) (x i)
        · filter_upwards [hBc.continuous_paths] with ω hω
          simpa [HasAlmostSurelyContinuousPaths, processPath] using continuous_const.add hω
      convert hTranslated using 1
      funext t ω
      by_cases hω : ω ∈ N <;> simp [Wc, B, Bc, hω, sub_eq_add_neg, add_assoc, add_left_comm]
    · have hcoord_eq :
          ∀ i : Fin d,
            (fun ω ↦ fun t : NNReal ↦ W t ω i) =ᵐ[(μ : Measure Ω)]
              (fun ω ↦ fun t : NNReal ↦ Wc t ω i) := by
        intro i
        filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω
        have hω' : ω ∉ N := by simpa using hω
        funext t
        simp [Wc, hω']
      -- Proof comment: patching on one common null set preserves the independence of the
      -- coordinate-path family.
      exact hW.iIndepFun.congr hcoord_eq
  exact ⟨Wc, hWc_owner, hWc_cont, hWc_start, hWc_eq⟩

/-- Helper for Theorem 25.38: Brownian motion exits any open set with compact closure almost
surely in finite time under one fixed starting law. -/
private theorem ae_exitTime_lt_top_of_isCompact_closure_startedAt
    [NeZero d]
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {G : Set State} {x : State}
    (hx : x ∈ G)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (_hG : IsOpen G) (hGcpt : IsCompact (closure G)) :
    ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Gᶜ 0 ω < ⊤ := by
  let i : Fin d := 0
  obtain ⟨R, hRsubset⟩ := hGcpt.isBounded.subset_closedBall (0 : State)
  have hxClosure : x ∈ closure G := subset_closure hx
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hRsubset hxClosure
  have hxi_abs : |x i| ≤ R := by
    calc
      |x i| = ‖x i‖ := by simp
      _ ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
      _ ≤ R := hxR
  let a : ℝ := -(R + 1) - x i
  let b : ℝ := R + 1 - x i
  have ha : a < 0 := by
    -- Proof comment: the lower scalar barrier stays strictly below `0` because `x` already lies
    -- in the compact ball containing `closure G`.
    have hxi_lower : -R ≤ x i := (abs_le.mp hxi_abs).1
    dsimp [a]
    linarith
  have hb : 0 < b := by
    -- Proof comment: the upper scalar barrier stays strictly above `0` for the same reason.
    have hxi_upper : x i ≤ R := (abs_le.mp hxi_abs).2
    dsimp [b]
    linarith
  let B0 : NNReal → Ω → ℝ := fun t ω ↦ if t = 0 then 0 else W t ω i - x i
  have hB0 : IsBrownianMotion (μ : Measure Ω) B0 := by
    let Z : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    have hZ : IsBrownianMotionStartedAt (μ : Measure Ω) Z 0 := by
      -- Proof comment: recenter the chosen coordinate so the scalar motion starts at `0`.
      simpa [Z] using
        brownianStartedAt_sub_const_startedAtZero (hW.isBrownianMotionStartedAt i)
    -- Proof comment: patch the zero-time value to the literal constant `0` so the scalar owner
    -- matches the standard Brownian-motion theorem used for the hitting argument.
    simpa [B0, Z] using
      pointwiseZeroVersion_isBrownianMotion_startedAtZero
        (μ := (μ : Measure Ω)) (B := Z) hZ
  have hτscalar :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter B0 ({a, b} : Set ℝ) 0 ω ≠ ⊤ :=
    brownianMotion_twoSidedHittingTime_ae_ne_top (hB := hB0) (a := a) (b := b) ha hb
  filter_upwards [hτscalar] with ω hω
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hω
  rcases hω with ⟨t, ht_nonneg, hτ_mem⟩
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    have hB0_zero : B0 t ω = 0 := by
      simp [B0, ht0]
    rcases hτ_mem with hτa | hτb
    · have : a = 0 := by rw [← hτa]; exact hB0_zero
      linarith
    · have : b = 0 := by rw [← hτb]; exact hB0_zero
      linarith
  have hcoord_hit :
      W t ω i = -(R + 1) ∨ W t ω i = R + 1 := by
    rcases hτ_mem with hτa | hτb
    · left
      have hEq : W t ω i - x i = a := by
        simpa [B0, ht_ne_zero] using hτa
      dsimp [a] at hEq
      linarith
    · right
      have hEq : W t ω i - x i = b := by
        simpa [B0, ht_ne_zero] using hτb
      dsimp [b] at hEq
      linarith
  have hcoord_abs : |W t ω i| = R + 1 := by
    rcases hcoord_hit with hleft | hright
    · have hRp1_nonneg : 0 ≤ R + 1 := by linarith [hxR]
      rw [hleft, abs_neg, abs_of_nonneg hRp1_nonneg]
    · have hRp1_nonneg : 0 ≤ R + 1 := by linarith [hxR]
      rw [hright, abs_of_nonneg hRp1_nonneg]
  have hnot_closedBall : W t ω ∉ Metric.closedBall (0 : State) R := by
    intro hball
    have hnorm_le : ‖W t ω‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hcoord_le : R + 1 ≤ ‖W t ω‖ := by
      calc
        R + 1 = |W t ω i| := hcoord_abs.symm
        _ = ‖W t ω i‖ := by simp
        _ ≤ ‖W t ω‖ := by simpa using PiLp.norm_apply_le (W t ω) i
    linarith
  have hWt_mem : W t ω ∈ Gᶜ := by
    -- Proof comment: once one coordinate reaches magnitude `R + 1`, the whole state leaves the
    -- compact ball containing `closure G`, so it lies outside `G`.
    intro hWtG
    exact hnot_closedBall (hRsubset (subset_closure hWtG))
  have hτ_le : hittingAfter W Gᶜ 0 ω ≤ t := by
    -- Proof comment: after the path reaches `Gᶜ` at time `t`, the exit clock from `G` is no
    -- later than `t`.
    exact
      hittingAfter_le_of_mem
        (u := W) (s := Gᶜ) (n := (0 : NNReal)) (i := t) (ω := ω) ht_nonneg hWt_mem
  exact lt_of_le_of_lt hτ_le (by simpa using (WithTop.coe_lt_top t))

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 25.38: a continuous path that hits a closed target by finite time lands in
that target at the hitting time. -/
private theorem mem_closedSet_at_hittingAfter_of_lt_top_local
    {A : Set State} {W : VectorProcess} {ω : Ω}
    (hAclosed : IsClosed A)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hτ : hittingAfter W A 0 ω < ⊤) :
    W (hittingAfter W A 0 ω).untopA ω ∈ A := by
  have hτ_ne_top : hittingAfter W A 0 ω ≠ ⊤ := ne_of_lt hτ
  let hitSet : Set NNReal := {t : NNReal | W t ω ∈ A}
  have hHitExists : ∃ t : NNReal, W t ω ∈ A := by
    simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hτ_ne_top
    rcases hτ_ne_top with ⟨t, _, htA⟩
    exact ⟨t, htA⟩
  have hHitNonempty : hitSet.Nonempty := by
    rcases hHitExists with ⟨t, htA⟩
    exact ⟨t, htA⟩
  have hHitClosed : IsClosed hitSet := by
    change IsClosed ((fun t : NNReal ↦ W t ω) ⁻¹' A)
    exact hAclosed.preimage hcont
  have hHitBddBelow : BddBelow hitSet := ⟨0, fun _ _ ↦ bot_le⟩
  have hsInf_mem : sInf hitSet ∈ hitSet :=
    hHitClosed.csInf_mem hHitNonempty hHitBddBelow
  have hτ_eq : (hittingAfter W A 0 ω).untopA = sInf hitSet := by
    rw [hittingAfter]
    rw [if_pos]
    · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ W i ω ∈ A} = hitSet by
            ext t
            simp [hitSet]]
      simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf hitSet))
    · rcases hHitExists with ⟨t, htA⟩
      exact ⟨t, bot_le, htA⟩
  simpa [hitSet, hτ_eq] using hsInf_mem

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 25.38: for an open stage `U`, a continuous path started in `U` reaches the
closure of `U` at its finite exit time from `U`. -/
private theorem mem_closure_at_exit_of_lt_top
    {U : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤) :
    W (hittingAfter W Uᶜ 0 ω).untopA ω ∈ closure U := by
  let τU : NNReal := (hittingAfter W Uᶜ 0 ω).untopA
  have hτ_mem : W τU ω ∈ Uᶜ := by
    -- Proof comment: the finite exit point lies in the closed complement by the previous
    -- closed-target hitting-time lemma.
    simpa [τU] using
      mem_closedSet_at_hittingAfter_of_lt_top_local
        (A := Uᶜ)
        (hAclosed := isClosed_compl_iff.mpr hUo)
        hcont
        hτ
  have hτ_pos : 0 < τU := by
    by_contra hτ_pos
    have hτ_zero : τU = 0 := le_antisymm (le_of_not_gt hτ_pos) bot_le
    have hW0_mem : W 0 ω ∈ Uᶜ := by
      simpa [hτ_zero] using hτ_mem
    exact hW0_mem hStart
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  have hτ_coe : ((τU : NNReal) : WithTop NNReal) = hittingAfter W Uᶜ 0 ω := by
    rw [show τU = (hittingAfter W Uᶜ 0 ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hτ_ne_top]
    exact WithTop.coe_untop _ _
  have hLeftU : ∀ s : NNReal, s < τU → W s ω ∈ U := by
    intro s hs
    have hs_lt_hit : (s : WithTop NNReal) < hittingAfter W Uᶜ 0 ω := by
      rw [← hτ_coe]
      exact_mod_cast hs
    have hs_not_mem :
        W s ω ∉ Uᶜ :=
      notMem_of_lt_hittingAfter
        (u := W) (s := Uᶜ) (n := (0 : NNReal)) (ω := ω) hs_lt_hit (by simp)
    simpa using hs_not_mem
  rw [mem_closure_iff]
  intro o ho hτo
  have hPreimage : {s : NNReal | W s ω ∈ o} ∈ 𝓝 τU := by
    exact hcont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds ho hτo)
  rcases mem_nhds_iff.mp hPreimage with ⟨u, hu_subset, hu_open, hτu⟩
  have hτ_leftClosure : τU ∈ closure (Set.Iio τU : Set NNReal) := by
    have hclosureIio : closure (Set.Iio τU : Set NNReal) = Set.Iic τU :=
      closure_Iio' ⟨0, hτ_pos⟩
    rw [hclosureIio]
    simp
  rcases (mem_closure_iff.mp hτ_leftClosure) u hu_open hτu with ⟨s, hs_mem_u, hs_lt⟩
  -- Proof comment: every neighborhood of the exit point contains earlier path values still in
  -- `U`, so the exit point lies in `closure U`.
  exact ⟨W s ω, hu_subset hs_mem_u, hLeftU s hs_lt⟩

/-- Helper for Theorem 25.38: under finite exit, the stopped exit value belongs to `closure U`. -/
private theorem stoppedValue_mem_closure_at_exit_of_lt_top
    {U : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤) :
    stoppedValue W (hittingAfter W Uᶜ 0) ω ∈ closure U := by
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  -- Proof comment: under finite exit, `stoppedValue` is the path value at the concrete exit time.
  simpa [stoppedValue, hτ_ne_top] using
    mem_closure_at_exit_of_lt_top
      (U := U) (W := W) (ω := ω) hUo hcont hStart hτ

/-- Helper for Theorem 25.38: if two paths agree at every deterministic time, then their
`hittingAfter` clocks against a fixed target and the corresponding stopped values agree as well. -/
private theorem hittingAfter_stoppedValue_eq_of_forall_eq
    {A : Set State} {W Wc : VectorProcess} {ω : Ω}
    (hall : ∀ t : NNReal, W t ω = Wc t ω) :
    hittingAfter W A 0 ω = hittingAfter Wc A 0 ω ∧
      stoppedValue W (hittingAfter W A 0) ω =
        stoppedValue Wc (hittingAfter Wc A 0) ω := by
  have hHit :
      hittingAfter W A 0 ω = hittingAfter Wc A 0 ω := by
    classical
    unfold hittingAfter
    by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ W j ω ∈ A
    · have h' : ∃ j, (0 : NNReal) ≤ j ∧ Wc j ω ∈ A := by
        rcases h with ⟨j, hj0, hjA⟩
        exact ⟨j, hj0, by simpa [hall j] using hjA⟩
      have hSet :
          {j : NNReal | (0 : NNReal) ≤ j ∧ W j ω ∈ A} =
            {j : NNReal | (0 : NNReal) ≤ j ∧ Wc j ω ∈ A} := by
        ext j
        simp [hall j]
      rw [if_pos h, if_pos h']
      exact congrArg (fun s : Set NNReal ↦ (((sInf s : NNReal) : WithTop NNReal))) hSet
    · have h' : ¬ ∃ j, (0 : NNReal) ≤ j ∧ Wc j ω ∈ A := by
        intro h'
        apply h
        rcases h' with ⟨j, hj0, hjA⟩
        exact ⟨j, hj0, by simpa [hall j] using hjA⟩
      rw [if_neg h, if_neg h']
  refine ⟨hHit, ?_⟩
  calc
    stoppedValue W (hittingAfter W A 0) ω = W (hittingAfter W A 0 ω).untopA ω := rfl
    _ = Wc (hittingAfter W A 0 ω).untopA ω := by simpa using hall _
    _ = Wc (hittingAfter Wc A 0 ω).untopA ω := by rw [hHit]
    _ = stoppedValue Wc (hittingAfter Wc A 0) ω := rfl

/-- Helper for Theorem 25.38: the exit clock and exit value agree almost surely between a
Brownian path and a same-space continuous modification that coincides with it at every time
outside one null set. -/
private theorem stageExitStoppedValue_ae_eq_continuousVersion
    {μ : Measure Ω} {W Wc : VectorProcess} {U : Set State}
    (hEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, W t ω = Wc t ω) :
    ∀ᵐ ω ∂μ,
      hittingAfter W Uᶜ 0 ω = hittingAfter Wc Uᶜ 0 ω ∧
        stoppedValue W (hittingAfter W Uᶜ 0) ω =
          stoppedValue Wc (hittingAfter Wc Uᶜ 0) ω := by
  filter_upwards [hEq] with ω hω
  simpa using hittingAfter_stoppedValue_eq_of_forall_eq (A := Uᶜ) hω

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 25.38: once the exit time from `U` is finite, the stage-stopped path is
eventually constant along deterministic integer horizons. -/
private theorem tendsto_stageStoppedProcess_nat_to_stoppedValue
    {W : VectorProcess} {U : Set State} {ω : Ω}
    (hτfin : hittingAfter W Uᶜ 0 ω < ⊤) :
    Tendsto
      (fun n : ℕ ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω)
      atTop
      (𝓝 (stoppedValue W (hittingAfter W Uᶜ 0) ω)) := by
  have hEventuallyEq :
      (fun n : ℕ ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω) =ᶠ[atTop]
        fun _ ↦ stoppedValue W (hittingAfter W Uᶜ 0) ω := by
    filter_upwards
        [tendsto_natCast_atTop_atTop.eventually_ge_atTop
          ((hittingAfter W Uᶜ 0 ω).untopA)] with n hn
    have hτn : hittingAfter W Uᶜ 0 ω ≤ (n : ENNReal) :=
      (WithTop.untopA_le_iff
        (x := hittingAfter W Uᶜ 0 ω) (hx := ne_top_of_lt hτfin)).1 hn
    -- Proof comment: once the deterministic horizon dominates the finite exit time, the stopped
    -- path has already frozen at the terminal exit value.
    simpa [stoppedValue] using
      (stoppedProcess_eq_of_ge
        (u := W) (τ := hittingAfter W Uᶜ 0) (ω := ω) (i := (n : NNReal)) hτn)
  exact Filter.Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 25.38: composing the stage-stopped path with a continuous function
preserves convergence to the terminal stopped value. -/
private theorem tendsto_stageStoppedExtension_nat_to_stoppedValue
    {W : VectorProcess} {U : Set State} {F : State → ℝ} {ω : Ω}
    (hτfin : hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F) :
    Tendsto
      (fun n : ℕ ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω))
      atTop
      (𝓝 (F (stoppedValue W (hittingAfter W Uᶜ 0) ω))) := by
  -- Proof comment: the stage-stopped path is eventually constant, so continuity of `F`
  -- transports the limit to the terminal stopped value.
  exact hFcont.continuousAt.tendsto.comp <|
    tendsto_stageStoppedProcess_nat_to_stoppedValue (W := W) (U := U) hτfin

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 25.38: once the exit time is finite, the deterministic stopped Dirichlet
values are eventually equal to the boundary datum at the exit position. -/
private theorem tendsto_stageStoppedDirichlet_to_boundaryValue
    {G : Set State} {W : VectorProcess} {ω : Ω}
    {exitValue : Ω → frontier G} {f : frontier G → ℝ} {u : State → ℝ}
    (hτ : hittingAfter W Gᶜ 0 ω < ⊤)
    (hExit : (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    (hu : SolvesDirichletProblem G f u) :
    Tendsto
      (fun n : ℕ ↦ u (stoppedProcess W (hittingAfter W Gᶜ 0) n ω))
      atTop
      (𝓝 (f (exitValue ω))) := by
  have hτ_ne_top : hittingAfter W Gᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  have hEventuallyEq :
      (fun n : ℕ ↦ u (stoppedProcess W (hittingAfter W Gᶜ 0) n ω)) =ᶠ[atTop]
        fun _ ↦ u (stoppedValue W (hittingAfter W Gᶜ 0) ω) := by
    filter_upwards
        [tendsto_natCast_atTop_atTop.eventually_ge_atTop
          ((hittingAfter W Gᶜ 0 ω).untopA)] with n hn
    have hτn : hittingAfter W Gᶜ 0 ω ≤ (n : ENNReal) :=
      (WithTop.untopA_le_iff
        (x := hittingAfter W Gᶜ 0 ω) (hx := ne_top_of_lt hτ)).1 hn
    -- Proof comment: once the deterministic horizon dominates the finite exit time, the stopped
    -- path has already frozen at the terminal exit value.
    simpa [stoppedValue, hτ_ne_top] using
      congrArg u
        (stoppedProcess_eq_of_ge
          (u := W) (τ := hittingAfter W Gᶜ 0) (ω := ω) (i := (n : NNReal)) hτn)
  have hLimitToStopped :
      Tendsto
        (fun n : ℕ ↦ u (stoppedProcess W (hittingAfter W Gᶜ 0) n ω))
        atTop
        (𝓝 (u (stoppedValue W (hittingAfter W Gᶜ 0) ω))) :=
    Filter.Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds
  have hBoundary :
      u (stoppedValue W (hittingAfter W Gᶜ 0) ω) = f (exitValue ω) := by
    calc
      u (stoppedValue W (hittingAfter W Gᶜ 0) ω) = u (exitValue ω : State) := by
        rw [← hExit]
      _ = f (exitValue ω) := hu.boundary_eq (exitValue ω)
  -- Proof comment: finite exit makes the sequence eventually constant, and the exit-value
  -- identification turns that terminal constant into the boundary datum.
  simpa [hBoundary] using hLimitToStopped

/-- Helper for Theorem 25.38: if `closure U ⊆ V`, then every deterministic-horizon stop
`W_{R ∧ τ_{Uᶜ}}` stays inside `V`. -/
private theorem stageStoppedProcess_mem_buffer
    {U V : Set State} {W : VectorProcess} {ω : Ω}
    (hUo : IsOpen U)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ U)
    (hUV : closure U ⊆ V)
    (hτ : hittingAfter W Uᶜ 0 ω < ⊤)
    (R : NNReal) :
    stoppedProcess W (hittingAfter W Uᶜ 0) R ω ∈ V := by
  let τU : NNReal := (hittingAfter W Uᶜ 0 ω).untopA
  have hτ_ne_top : hittingAfter W Uᶜ 0 ω ≠ ⊤ := ne_of_lt hτ
  have hτ_coe : ((τU : NNReal) : WithTop NNReal) = hittingAfter W Uᶜ 0 ω := by
    rw [show τU = (hittingAfter W Uᶜ 0 ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hτ_ne_top]
    exact WithTop.coe_untop _ _
  by_cases hRτ : R < τU
  · have hStopped :
        stoppedProcess W (hittingAfter W Uᶜ 0) R ω = W R ω := by
      apply stoppedProcess_eq_of_le
      rw [← hτ_coe]
      exact le_of_lt (by exact_mod_cast hRτ)
    have hInside : W R ω ∈ U := by
      have hRt : (R : WithTop NNReal) < hittingAfter W Uᶜ 0 ω := by
        rw [← hτ_coe]
        exact_mod_cast hRτ
      have hNot :
          W R ω ∉ Uᶜ :=
        notMem_of_lt_hittingAfter
          (u := W) (s := Uᶜ) (n := (0 : NNReal)) (ω := ω) hRt (by simp)
      simpa using hNot
    -- Proof comment: before the exit time, the deterministic stop is still inside `U`, hence
    -- inside every buffer containing `closure U`.
    rw [hStopped]
    exact hUV (subset_closure hInside)
  · have hτR : τU ≤ R := le_of_not_gt hRτ
    have hStopped :
        stoppedProcess W (hittingAfter W Uᶜ 0) R ω = W τU ω := by
      apply stoppedProcess_eq_of_ge
      rw [← hτ_coe]
      exact_mod_cast hτR
    have hExitClosure :
        W τU ω ∈ closure U := by
      simpa [τU] using
        mem_closure_at_exit_of_lt_top
          (U := U)
          hUo
          hcont
          hStart
          hτ
    -- Proof comment: once the deterministic cap reaches the exit time, the stopped path is the
    -- actual exit point, which belongs to `closure U ⊆ V`.
    rw [hStopped]
    exact hUV hExitClosure

/-- Helper for Theorem 25.38: every deterministic-horizon stop of the Brownian stage stays in the
harmonic buffer, so the Laplacian of the extension vanishes there almost surely. -/
private theorem stageStoppedLaplacian_eq_zero
    {μ : ProbabilityMeasure Ω}
    {W : VectorProcess} {U V : Set State} {F : State → ℝ} {x : State}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hExitFinite : ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Δ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) = 0 := by
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  filter_upwards [hExitFinite, hStartAe] with ω hωfin hωstart t
  have hStart : W 0 ω ∈ U := by
    simpa [hωstart] using hx
  have hmemV :
      stoppedProcess W (hittingAfter W Uᶜ 0) t ω ∈ V :=
    stageStoppedProcess_mem_buffer
      (U := U) (V := V) (W := W) (ω := ω)
      hUo
      (hWcont ω)
      hStart
      hUV
      hωfin
      t
  -- Proof comment: once the deterministic stop is known to stay in `V`, harmonicity kills the
  -- Laplacian at that stopped point.
  exact laplacian_eq_zero_on_buffer hFharm hmemV

/-- Helper for Theorem 25.38: after recentering and patching the Brownian path, the stopped
Laplacian-zero identity transports from the original path to the shifted stopped spelling. -/
private theorem shiftedStoppedExtension_laplacian_eq_zero
    {μ : ProbabilityMeasure Ω}
    {W : VectorProcess} {U V : Set State} {F : State → ℝ} {x : State}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hExitFinite : ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Δ F (x + stoppedProcess B (hittingAfter W Uᶜ 0) t ω) = 0 := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hTranslate :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, x + B t ω = W t ω :=
    stageTranslatedPatchedBrownian_ae_allTimes_eq_original μ hW
  have hStoppedLap :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        Δ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) = 0 :=
    stageStoppedLaplacian_eq_zero
      (μ := μ) (W := W) (U := U) (V := V) (F := F) (x := x)
      hx hW hWcont hUo hUV hExitFinite hFharm
  filter_upwards [hTranslate, hStoppedLap] with ω hωTranslate hωLap t
  have hStoppedEq :
      x + stoppedProcess B (hittingAfter W Uᶜ 0) t ω =
        stoppedProcess W (hittingAfter W Uᶜ 0) t ω :=
    translatedPatchedBrownian_stopped_eq_original
      (W := W) (B := B) (τ := hittingAfter W Uᶜ 0) (x := x) (ω := ω)
      hωTranslate
      t
  -- Proof comment: rewrite the shifted stopped point back to the original stopped Brownian path,
  -- where the vanishing-Laplacian statement is already available.
  rw [hStoppedEq]
  exact hωLap t

/-- Helper for Theorem 25.38: if a global extension agrees with `u` on `closure U`, then their
deterministic stopped-value integrals over the exit clock from `U` coincide. -/
private theorem integral_stageStopped_eq_of_eqOn_closure
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {u F : State → ℝ}
    (hx : x ∈ U) (hUo : IsOpen U)
    (hWcont :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous fun t : NNReal ↦ W t ω)
    (hStart :
      ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hEq : Set.EqOn F u (closure U))
    (n : ℕ) :
    ∫ ω, F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) =
      ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := by
  refine integral_congr_ae ?_
  filter_upwards [hWcont, hStart, hExitFinite] with ω hωcont hωstart hωfin
  have hStartMem : W 0 ω ∈ U := by
    simpa [hωstart] using hx
  have hmem :
      stoppedProcess W (hittingAfter W Uᶜ 0) n ω ∈ closure U :=
    stageStoppedProcess_mem_buffer
      (U := U) (V := closure U) (W := W) (ω := ω)
      hUo hωcont hStartMem (by intro z hz; exact hz) hωfin n
  -- Proof comment: every deterministic stopped value stays on `closure U`, where the global
  -- extension and the original solution agree pointwise.
  exact hEq hmem

/-- Helper for Theorem 25.38: if a measurable extension agrees with `u` on `closure U`, then each
deterministic stage slice `ω ↦ u(W_{n ∧ τ_U}(ω))` is almost-everywhere strongly measurable. -/
private theorem stageStopped_eqOnClosure_aestronglyMeasurable_atNat
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {u F : State → ℝ}
    (hx : x ∈ U) (hUo : IsOpen U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hStart : ∀ ω : Ω, W 0 ω = x)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFmeas : Measurable F)
    (hEq : Set.EqOn F u (closure U))
    (n : ℕ) :
    AEStronglyMeasurable
      (fun ω ↦ u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω))
      (μ : Measure Ω) := by
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  have hτ :
      IsStoppingTime
        (Filtration.natural W hWsm)
        (hittingAfter W Uᶜ 0) :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite
  have hWstrong :
      StronglyAdapted (Filtration.natural W hWsm) W :=
    Filtration.stronglyAdapted_natural (u := W) hWsm
  have hWprog :
      ProgMeasurable (Filtration.natural W hWsm) W :=
    hWstrong.progMeasurable_of_continuous hWcont
  have hσ :
      IsStoppingTime
        (Filtration.natural W hWsm)
        (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) :=
    hτ.min_const (n : NNReal)
  have hStoppedMeas :
      Measurable
        (stoppedValue W (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal))) :=
    (measurable_stoppedValue hWprog hσ).mono hσ.measurableSpace_le le_rfl
  have hStoppedEq :
      (fun ω ↦ stoppedProcess W (hittingAfter W Uᶜ 0) n ω) =
        stoppedValue W (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) := by
    funext ω
    -- Proof comment: the deterministic stage `n` is the stopped value at the clipped clock
    -- `τ_U ∧ n`.
    simpa [min_comm] using
      (stoppedProcess_eq_stoppedValue_apply
        (u := W) (τ := hittingAfter W Uᶜ 0) (i := (n : NNReal)) ω).symm
  have hFStageMeas :
      Measurable
        (fun ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω)) := by
    -- Proof comment: rewrite the deterministic stopped slice through the measurable clipped
    -- stopping time, then compose with the measurable extension `F`.
    simpa [hStoppedEq] using hFmeas.comp hStoppedMeas
  have hStageEq :
      (fun ω ↦ u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω)) =ᵐ[(μ : Measure Ω)]
        fun ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) := by
    filter_upwards [hExitFinite] with ω hωfin
    have hStartMem : W 0 ω ∈ U := by
      simpa [hStart ω] using hx
    have hmem :
        stoppedProcess W (hittingAfter W Uᶜ 0) n ω ∈ closure U :=
      stageStoppedProcess_mem_buffer
        (U := U) (V := closure U) (W := W) (ω := ω)
        hUo (hWcont ω) hStartMem (by intro z hz; exact hz) hωfin n
    -- Proof comment: every deterministic stopped value stays on `closure U`, so `F` can be
    -- rewritten back to the original Dirichlet function `u`.
    exact (hEq hmem).symm
  exact hFStageMeas.aestronglyMeasurable.congr hStageEq.symm

/-- Helper for Theorem 25.38: a closure bound on `u` controls every deterministic stop before the
finite exit time. -/
private theorem abs_stageStoppedDirichlet_le_of_closureBound
    {G : Set State} {W : VectorProcess} {ω : Ω} {u : State → ℝ} {C : ℝ}
    (hG : IsOpen G)
    (hcont : Continuous fun t : NNReal ↦ W t ω)
    (hStart : W 0 ω ∈ G)
    (hτ : hittingAfter W Gᶜ 0 ω < ⊤)
    (hC : ∀ z ∈ closure G, |u z| ≤ C)
    (R : NNReal) :
    |u (stoppedProcess W (hittingAfter W Gᶜ 0) R ω)| ≤ C := by
  have hmem :
      stoppedProcess W (hittingAfter W Gᶜ 0) R ω ∈ closure G :=
    stageStoppedProcess_mem_buffer
      (U := G) (V := closure G) (W := W) (ω := ω)
      hG hcont hStart (by intro z hz; exact hz) hτ R
  -- Proof comment: every deterministic stage of the stopped path remains in `closure G`, so the
  -- precomputed compact-closure bound applies directly.
  exact hC _ hmem

/-- Helper for Theorem 25.38: once a bounded local martingale is written as a process minus its
initial constant, every deterministic-time slice has expectation equal to that initial value. -/
private theorem expectation_eq_of_bounded_localMartingale_increment
    {μ : ProbabilityMeasure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ} {c : ℝ}
    (hLocal : IsLocalMartingale ℱ (μ : Measure Ω) (fun t ω ↦ M t ω - c))
    (hBounded : BoundedInTimeAe (μ : Measure Ω) (fun t ω ↦ M t ω - c))
    (hInitial : M 0 =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ c) :
    ∀ n : ℕ, c = ∫ ω, M n ω ∂(μ : Measure Ω) := by
  intro n
  have hMart :
      Martingale (fun t ω ↦ M t ω - c) ℱ (μ : Measure Ω) :=
    martingale_of_bounded_local_martingale hLocal hBounded
  have hZeroIntegral :
      ∫ ω, M n ω - c ∂(μ : Measure Ω) = 0 := by
    have hConstEq :
        ∫ ω, M n ω - c ∂(μ : Measure Ω) =
          ∫ ω, M 0 ω - c ∂(μ : Measure Ω) := by
      -- Proof comment: boundedness upgrades the local martingale to a genuine martingale, so its
      -- deterministic-time expectations are constant.
      simpa [setIntegral_univ] using
        (hMart.setIntegral_eq
          (show (0 : NNReal) ≤ n by exact zero_le _)
          (s := Set.univ)
          MeasurableSet.univ).symm
    have hInitialZero :
        (fun ω ↦ M 0 ω - c) =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ (0 : ℝ) := by
      filter_upwards [hInitial] with ω hω
      simp [hω]
    calc
      ∫ ω, M n ω - c ∂(μ : Measure Ω) =
          ∫ ω, M 0 ω - c ∂(μ : Measure Ω) :=
        hConstEq
      _ = 0 := by
        rw [integral_congr_ae hInitialZero]
        simp
  have hSliceIntegrable : Integrable (M n) (μ : Measure Ω) := by
    have hAdd :
        Integrable (fun ω ↦ (M n ω - c) + c) (μ : Measure Ω) :=
      (hMart.integrable n).add (integrable_const c)
    have hEq :
        (fun ω ↦ (M n ω - c) + c) = M n := by
      funext ω
      ring
    exact hEq ▸ hAdd
  have hConstIntegrable : Integrable (fun _ : Ω ↦ c) (μ : Measure Ω) :=
    integrable_const c
  have hSub :
      ∫ ω, M n ω - c ∂(μ : Measure Ω) =
        ∫ ω, M n ω ∂(μ : Measure Ω) - ∫ ω, c ∂(μ : Measure Ω) := by
    -- Proof comment: rewrite the increment integral as the difference of the slice integral and
    -- the deterministic starting constant.
    simpa [Pi.sub_apply] using integral_sub hSliceIntegrable hConstIntegrable
  have hConstIntegral : ∫ ω, c ∂(μ : Measure Ω) = c := by
    simp
  linarith [hZeroIntegral, hSub, hConstIntegral]

/-- Helper for Theorem 25.38: compact closure gives a deterministic uniform bound for any
continuous observable on `closure U`. -/
private theorem existsAbsLeOnCompactClosure_continuous
    {U : Set State} {F : State → ℝ}
    (hUcpt : IsCompact (closure U))
    (hFcont : Continuous F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure U, |F z| ≤ C := by
  have hImageCompact : IsCompact (F '' closure U) := hUcpt.image hFcont
  rcases hImageCompact.bddBelow with ⟨l, hl⟩
  rcases hImageCompact.bddAbove with ⟨r, hr⟩
  refine ⟨max |l| |r|, by positivity, ?_⟩
  intro z hz
  have hzImage : F z ∈ F '' closure U := ⟨z, hz, rfl⟩
  have hlz : l ≤ F z := hl hzImage
  have hrz : F z ≤ r := hr hzImage
  -- Proof comment: compactness bounds the image of `closure U`, so the larger endpoint controls
  -- the absolute value on that whole set.
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc
      -max |l| |r| ≤ -|l| := neg_le_neg (le_max_left |l| |r|)
      _ ≤ l := neg_abs_le l
      _ ≤ F z := hlz
  · calc
      F z ≤ r := hrz
      _ ≤ |r| := le_abs_self r
      _ ≤ max |l| |r| := le_max_right |l| |r|

/-- Helper for Theorem 25.38: composing a measurable state observable with a process preserves
strong adaptedness in its natural filtration. -/
private theorem stateComposition_stronglyAdapted_natural
    {W : VectorProcess} (hWsm : ∀ t : NNReal, StronglyMeasurable (W t))
    {F : State → ℝ} (hFmeas : Measurable F) :
    StronglyAdapted (Filtration.natural W hWsm) (fun t ω ↦ F (W t ω)) := by
  intro t
  have hWt :
      StronglyMeasurable[Filtration.natural W hWsm t] (W t) :=
    Filtration.stronglyAdapted_natural (u := W) hWsm t
  -- Proof comment: each deterministic-time slice factors through the current state `W t ω`
  -- followed by the measurable observable `F`.
  simpa using hFmeas.stronglyMeasurable.comp_measurable hWt.measurable

/-- Helper for Theorem 25.38: if all deterministic-horizon stops of a continuous adapted process
are martingales, then the process is a continuous local martingale. -/
private theorem isContinuousLocalMartingale_of_constStoppedMartingale_local
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {Y : NNReal → Ω → ℝ}
    (hY_adapted : Adapted ℱ Y)
    (hY_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω)
    (hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱ μ) :
    IsContinuousLocalMartingale ℱ μ Y := by
  refine
    { local_martingale := ?_
      continuous := hY_cont }
  refine (isLocalMartingale_iff ℱ μ Y).2 ⟨hY_adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ Y (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    -- Proof comment: deterministic horizons are stopping times.
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    -- Proof comment: the deterministic localizing sequence `n ↦ n` increases to `∞`.
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    have hMart :
        Martingale (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ :=
      hStopped n
    have hUI :
        UniformIntegrable
          (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          1
          μ := by
      -- Proof comment: stopping again at the same deterministic horizon changes nothing, so the
      -- standard deterministic-stop martingale owner supplies uniform integrability.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
        (martingaleUniformIntegrable_stoppedProcessConstTime
          (μ := μ)
          (ℱ := ℱ)
          (X := stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          hMart
          (n : NNReal)).2
    exact ⟨hMart, hUI⟩

/-- Helper for Theorem 25.38: `EqUpTo μ T X Y` records one measurable null set outside which
`X` and `Y` agree at every deterministic time in `[0,T]`. -/
private def EqUpTo {α : Type _} (μ : Measure Ω) (T : NNReal)
    (X Y : NNReal → Ω → α) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
    ∀ ⦃t : NNReal⦄, t ≤ T → {ω | X t ω ≠ Y t ω} ⊆ N

/-- Helper for Theorem 25.38: equality up to a horizon composes transitively. -/
private theorem eqUpTo_trans
    {μ : Measure Ω} {α : Type _} {T : NNReal}
    {X Y Z : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) (hYZ : EqUpTo μ T Y Z) :
    EqUpTo μ T X Z := by
  rcases hXY with ⟨NXY, hNXY_meas, hNXY_null, hNXY_sub⟩
  rcases hYZ with ⟨NYZ, hNYZ_meas, hNYZ_null, hNYZ_sub⟩
  refine ⟨NXY ∪ NYZ, hNXY_meas.union hNYZ_meas, ?_, ?_⟩
  · have hUnionLe : μ (NXY ∪ NYZ) ≤ μ NXY + μ NYZ := measure_union_le NXY NYZ
    refine le_antisymm ?_ bot_le
    simpa [hNXY_null, hNYZ_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXYω : X t ω ≠ Y t ω
    · exact Set.mem_union_left NYZ (hNXY_sub ht hXYω)
    · have hEqXY : X t ω = Y t ω := not_ne_iff.mp hXYω
      have hYZω : Y t ω ≠ Z t ω := by
        intro hEqYZ
        exact hω (hEqXY.trans hEqYZ)
      exact Set.mem_union_right NXY (hNYZ_sub ht hYZω)

/-- Helper for Theorem 25.38: equality up to a horizon is symmetric. -/
private theorem eqUpTo_sym
    {μ : Measure Ω} {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    EqUpTo μ T Y X := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  exact hN_sub ht (by
    intro hEq
    exact hω hEq.symm)

/-- Helper for Theorem 25.38: one `EqUpTo` witness can be read as equality on `[0,T]` outside a
single measurable null set. -/
private theorem eqUpTo_forall_eq
    {μ : Measure Ω} {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
      ∀ ⦃t : NNReal⦄, t ≤ T → ∀ ⦃ω : Ω⦄, ω ∉ N → X t ω = Y t ω := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  by_contra hneq
  exact hω (hN_sub ht hneq)

/-- Helper for Theorem 25.38: equality up to a horizon is reflexive. -/
private theorem eqUpTo_rfl
    {μ : Measure Ω} {α : Type _} (T : NNReal) (X : NNReal → Ω → α) :
    EqUpTo μ T X X := by
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht
  simp

/-- Helper for Theorem 25.38: equality up to a horizon is stable under addition. -/
private theorem eqUpTo_add
    {μ : Measure Ω} {T : NNReal}
    {X X' Y Y' : NNReal → Ω → ℝ}
    (hX : EqUpTo μ T X X') (hY : EqUpTo μ T Y Y') :
    EqUpTo μ T
      (fun t ω ↦ X t ω + Y t ω)
      (fun t ω ↦ X' t ω + Y' t ω) := by
  rcases hX with ⟨NX, hNX_meas, hNX_null, hNX_sub⟩
  rcases hY with ⟨NY, hNY_meas, hNY_null, hNY_sub⟩
  refine ⟨NX ∪ NY, hNX_meas.union hNY_meas, ?_, ?_⟩
  · have hUnionLe : μ (NX ∪ NY) ≤ μ NX + μ NY := measure_union_le NX NY
    refine le_antisymm ?_ bot_le
    simpa [hNX_null, hNY_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXω : X t ω ≠ X' t ω
    · exact Set.mem_union_left NY (hNX_sub ht hXω)
    · have hEqX : X t ω = X' t ω := not_ne_iff.mp hXω
      have hYω : Y t ω ≠ Y' t ω := by
        intro hEqY
        apply hω
        simpa [hEqX, hEqY]
      exact Set.mem_union_right NX (hNY_sub ht hYω)

/-- Helper for Theorem 25.38: one all-times almost-sure identity yields equality on every fixed
horizon. -/
private theorem eqUpTo_of_ae_allTimes
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω) :
    EqUpTo μ T X Y := by
  classical
  let N : Set Ω := {ω | ¬ ∀ t : NNReal, X t ω = Y t ω}
  refine ⟨toMeasurable μ N, measurableSet_toMeasurable _ _, ?_, ?_⟩
  · -- Proof comment: the measurable hull of the exceptional set is still null because the
    -- all-times identity already holds almost surely.
    rw [measure_toMeasurable]
    simpa [N, ae_iff] using hXY
  · intro t ht ω hω
    exact subset_toMeasurable μ N (by
      change ¬ ∀ s : NNReal, X s ω = Y s ω
      intro hAll
      exact hω (hAll t))

/-- Helper for Theorem 25.38: an indistinguishability witness already gives equality on every
deterministic horizon. This is the transport adapter from the Chapter 25.21 owner API to the
theorem-local `EqUpTo` spelling. -/
private theorem eqUpTo_of_areIndistinguishable_theorem25_38
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : AreIndistinguishable μ X Y) :
    EqUpTo μ T X Y := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  -- Proof comment: the single measurable null set from indistinguishability already controls the
  -- disagreement event at each deterministic time in `[0, T]`.
  exact ⟨N, hN_meas, hN_null, fun _ _ ↦ hN_sub _⟩

/-- Helper for Theorem 25.38: finite sums preserve horizon-wise equality. -/
private theorem eqUpTo_finsetSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {μ : Measure Ω} {T : NNReal}
    {X Y : ι → NNReal → Ω → ℝ}
    (hXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i)) :
    EqUpTo μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ X i t ω))
      (fun t ω ↦ Finset.sum s (fun i ↦ Y i t ω)) := by
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sums are definitionally the same zero process.
      simpa using eqUpTo_rfl (μ := μ) T (fun _ _ ↦ (0 : ℝ))
  | @insert a s ha ih =>
      have hsXY : ∀ i ∈ s, EqUpTo μ T (X i) (Y i) := by
        intro i hi
        exact hXY i (by simp [hi])
      -- Proof comment: combine the head witness with the recursive tail witness after rewriting
      -- both sums into head-plus-tail form.
      simpa [Finset.sum_insert, ha] using eqUpTo_add (hXY a (by simp)) (ih hsXY)

/-- Helper for Theorem 25.38: a genuine continuous local martingale is automatically a witness up
to any deterministic horizon. -/
private def IsContinuousLocalMartingaleUpToLocal
    (ℱ : Filtration NNReal ‹MeasurableSpace Ω›) (μ : Measure Ω)
    (T : NNReal) (N : NNReal → Ω → ℝ) : Prop :=
  ∃ N' : NNReal → Ω → ℝ,
    IsContinuousLocalMartingale ℱ μ N' ∧ EqUpTo μ T N N'

/-- Helper for Theorem 25.38: a genuine continuous local martingale already supplies its own
fixed-horizon `...UpToLocal` witness. -/
private theorem isContinuousLocalMartingaleUpToLocal_of_isContinuousLocalMartingale
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {T : NNReal} {N : NNReal → Ω → ℝ}
    (hN : IsContinuousLocalMartingale ℱ μ N) :
    IsContinuousLocalMartingaleUpToLocal ℱ μ T N := by
  -- Proof comment: keep the same process as the genuine witness and record reflexive horizon-wise
  -- equality.
  exact ⟨N, hN, eqUpTo_rfl (μ := μ) T N⟩

/-- Helper for Theorem 25.38: finite sums preserve the local fixed-horizon martingale witness. -/
private theorem finsetSum_isContinuousLocalMartingaleUpToLocal
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    (s : Finset (Fin d)) {T : NNReal} {N : Fin d → NNReal → Ω → ℝ}
    (hN : ∀ i ∈ s, IsContinuousLocalMartingaleUpToLocal ℱ μ T (N i)) :
    IsContinuousLocalMartingaleUpToLocal ℱ μ T
      (fun t ω ↦ Finset.sum s (fun i ↦ N i t ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ _ ↦ (0 : ℝ), ?_, ?_⟩
      · refine
          { local_martingale := ?_
            continuous := ?_ }
        · simpa using (MeasureTheory.martingale_zero ℝ ℱ μ).isLocalMartingale
        · intro ω
          simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      · simpa using eqUpTo_rfl (μ := μ) T (fun _ _ ↦ (0 : ℝ))
  | @insert i s hi hs =>
      rcases hN i (by simp) with ⟨Ni, hNi, hEqi⟩
      have hsN :
          ∀ j ∈ s, IsContinuousLocalMartingaleUpToLocal ℱ μ T (N j) := by
        intro j hj
        exact hN j (by simp [hj])
      rcases hs hsN with ⟨Ns, hNs, hEqs⟩
      let Nsum : NNReal → Ω → ℝ := fun t ω ↦ Ni t ω + Ns t ω
      refine ⟨Nsum, ?_, ?_⟩
      · refine
          { local_martingale := hNi.local_martingale.add hNs.local_martingale
            continuous := ?_ }
        intro ω
        -- Proof comment: the witness sum is continuous because both component witnesses already
        -- have continuous sample paths.
        simpa [Nsum] using (hNi.continuous ω).add (hNs.continuous ω)
      · have hEqSum :
          EqUpTo μ T
            (fun t ω ↦ N i t ω + Finset.sum s (fun j ↦ N j t ω))
            Nsum :=
          eqUpTo_add hEqi hEqs
        -- Proof comment: rewrite the visible sum into head-plus-tail form, then consume the
        -- combined horizonwise equality witness.
        simpa [Nsum, Finset.sum_insert, hi] using hEqSum

/-- Helper for Theorem 25.38: deterministic stopping at `T` turns a local `EqUpTo`
comparison on `[0, T]` into all-times almost-sure equality of the two deterministic stops. -/
private theorem ae_eq_stoppedProcess_const_of_eqUpTo
    {μ : Measure Ω} {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : EqUpTo μ T X Y) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω =
        stoppedProcess Y (fun _ ↦ (T : ENNReal)) t ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hXY with
    ⟨N, hN_meas, hN_null, hN_eq⟩
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := compl_mem_ae_iff.mpr hN_null
  filter_upwards [hNae] with ω hω t
  -- Proof comment: both deterministic stops are evaluated at the clipped time `min t T`, which
  -- stays inside the horizon controlled by the `EqUpTo` witness.
  simpa [stoppedProcessConstTime_eq_min] using hN_eq (min_le_right t T) hω

/-- Helper for Theorem 25.38: a deterministic bound transfers across an all-times almost-sure
equality of processes. -/
private theorem boundedInTimeAe_of_ae_allTimes_eq
    {μ : Measure Ω} {X Y : NNReal → Ω → ℝ}
    (hX : BoundedInTimeAe μ X)
    (hEq : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω) :
    BoundedInTimeAe μ Y := by
  rcases hX with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC, hEq] with ω hωBound hωEq t
  simpa [hωEq t] using hωBound t

/-- Helper for Theorem 25.38: deterministic stopping preserves the local-martingale property for
continuous paths on the probability-space surface used in this file. -/
private theorem isLocalMartingale_stoppedProcess_constTime_theorem25_38
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    (hM : IsLocalMartingale ℱ μ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    (T : NNReal) :
    IsLocalMartingale ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨hM_adapted, τSeq, hτSeq⟩
  refine
    (isLocalMartingale_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal)))).2 ⟨?_, τSeq, ?_⟩
  · -- Proof comment: deterministic stopping preserves adaptedness once the source process has
    -- continuous sample paths.
    exact
      (hM_adapted.stronglyAdapted.stoppedProcess hM_cont (isStoppingTime_const ℱ T)).adapted
  · rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hLim, hStopped⟩
    refine
      (isLocalizingSequence_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) τSeq).2
        ⟨hStopping, hLim, ?_⟩
    intro n
    obtain ⟨hMart, hUI⟩ := hStopped n
    have hDoubleStop :
        stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) := by
      have hLeft :
          stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
              stoppedProcess M
                (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))))
      have hRight :
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
              stoppedProcess M
                (fun ω ↦ min (((fun _ ↦ (T : ENNReal)) ω)) ((τSeq n) ω)))
      exact hLeft.trans hRight.symm
    have hStoppedConst :
        Martingale
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            ℱ
            μ ∧
          UniformIntegrable
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            1
            μ :=
      martingale_uniformIntegrable_stoppedProcess_constTime
        (μ := μ) (ℱ := ℱ) (M := stoppedProcess M (τSeq n)) hMart T
    -- Proof comment: after swapping the two stops, each doubly stopped slice is just a
    -- deterministic stop of the martingale owner already supplied by the localizing sequence.
    exact hDoubleStop ▸ hStoppedConst

/-- Helper for Theorem 25.38: a martingale on a finite-measure space is already a local
martingale via the deterministic localizing sequence `τₙ ≡ n`. -/
private theorem martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_38
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    -- Proof comment: deterministic horizons are stopping times.
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    -- Proof comment: the deterministic localizing sequence `n ↦ n` increases to `∞`.
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa using
      martingale_uniformIntegrable_stoppedProcess_constTime
        (μ := μ) (ℱ := ℱ) (M := M) hM (n := (n : NNReal))

/-- Helper for Theorem 25.38: a continuous adapted process inherits the local-martingale owner of
an all-times almost surely equal model. -/
private theorem isLocalMartingale_congr_ae_allTimes_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N : NNReal → Ω → ℝ}
    (hM : IsLocalMartingale ℱ μ M)
    (hN_adapted : Adapted ℱ N)
    (hN_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω)
    (hMN : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω) :
    IsLocalMartingale ℱ μ N := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨_, τSeq, hτSeq⟩
  refine (isLocalMartingale_iff ℱ μ N).2 ⟨hN_adapted, τSeq, ?_⟩
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hlim, hStopped⟩
  refine (isLocalizingSequence_iff ℱ μ N τSeq).2 ⟨hStopping, hlim, ?_⟩
  intro n
  obtain ⟨hMart, hUI⟩ := hStopped n
  have hStoppedEq :
      ∀ t : NNReal,
        stoppedProcess M (τSeq n) t =ᵐ[μ] stoppedProcess N (τSeq n) t := by
    intro t
    -- Proof comment: compare both stopped processes at the shared clipped time `t ∧ τₙ(ω)`.
    filter_upwards [hMN] with ω hω
    simpa [stoppedProcess] using hω ((min (t : ENNReal) (τSeq n ω)).untopA)
  have hStoppedStrong :
      StronglyAdapted ℱ (stoppedProcess N (τSeq n)) := by
    -- Proof comment: continuity lets the target process retain strong adaptedness after stopping
    -- at the common localizing sequence.
    exact hN_adapted.stronglyAdapted.stoppedProcess hN_cont (hStopping n)
  refine ⟨martingale_congr_ae hMart hStoppedStrong hStoppedEq, ?_⟩
  -- Proof comment: uniform integrability is invariant under deterministic-time almost-sure
  -- equality of the stopped family.
  exact (uniformIntegrable_congr_ae hStoppedEq).1 hUI

/-- Helper for Theorem 25.38: a bounded deterministic stop is a martingale once it agrees on
`[0,T]` with a deterministic-horizon continuous-local-martingale-up-to witness. -/
private theorem martingaleOfConstStoppedEqUpToLocalMartingaleUpTo
    {μ : ProbabilityMeasure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X N : NNReal → Ω → ℝ} {T : NNReal}
    (hXStrong :
      StronglyAdapted ℱ (stoppedProcess X (fun _ ↦ (T : ENNReal))))
    (hXBounded :
      BoundedInTimeAe (μ : Measure Ω)
        (stoppedProcess X (fun _ ↦ (T : ENNReal))))
    (hXN : EqUpTo (μ : Measure Ω) T X N)
    (hNUpTo : IsContinuousLocalMartingaleUpToLocal ℱ (μ : Measure Ω) T N) :
    Martingale (stoppedProcess X (fun _ ↦ (T : ENNReal))) ℱ (μ : Measure Ω) := by
  rcases hNUpTo with ⟨N', hN', hNN'⟩
  have hOwnerEq :
      EqUpTo (μ : Measure Ω) T N' X :=
    eqUpTo_trans (eqUpTo_sym hNN') (eqUpTo_sym hXN)
  have hOwnerStopEq :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        stoppedProcess N' (fun _ ↦ (T : ENNReal)) t ω =
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω :=
    ae_eq_stoppedProcess_const_of_eqUpTo hOwnerEq
  have hOwnerStoppedLocal :
      IsLocalMartingale ℱ (μ : Measure Ω)
        (stoppedProcess N' (fun _ ↦ (T : ENNReal))) :=
    isLocalMartingale_stoppedProcess_constTime_theorem25_38
      hN'.local_martingale
      hN'.continuous
      T
  have hOwnerStoppedBounded :
      BoundedInTimeAe (μ : Measure Ω)
        (stoppedProcess N' (fun _ ↦ (T : ENNReal))) := by
    have hOwnerStopEq_symm :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω =
            stoppedProcess N' (fun _ ↦ (T : ENNReal)) t ω := by
      filter_upwards [hOwnerStopEq] with ω hω t
      exact (hω t).symm
    exact
      boundedInTimeAe_of_ae_allTimes_eq
        hXBounded
        hOwnerStopEq_symm
  have hOwnerStoppedMart :
      Martingale (stoppedProcess N' (fun _ ↦ (T : ENNReal))) ℱ (μ : Measure Ω) :=
    martingale_of_bounded_local_martingale hOwnerStoppedLocal hOwnerStoppedBounded
  have hTargetStopEq :
      ∀ t : NNReal,
        stoppedProcess N' (fun _ ↦ (T : ENNReal)) t =ᵐ[(μ : Measure Ω)]
          stoppedProcess X (fun _ ↦ (T : ENNReal)) t := by
    intro t
    filter_upwards [hOwnerStopEq] with ω hω
    exact hω t
  -- Proof comment: the owner stop is already a martingale, and the visible deterministic stop
  -- inherits that property through timewise almost-sure equality plus its packaged strong
  -- adaptedness.
  exact martingale_congr_ae hOwnerStoppedMart hXStrong hTargetStopEq

/-- Helper for Theorem 25.38: stopping the raw harmonic increment at `τ` is exactly the visibly
stopped increment. -/
private theorem stageStoppedExtension_eq_stoppedRawIncrement
    {W : VectorProcess} {τ : Ω → ENNReal} {F : State → ℝ} {x : State} :
    stoppedProcess (fun t ω ↦ F (W t ω) - F x) τ =
      fun t ω ↦ F (stoppedProcess W τ t ω) - F x := by
  funext t ω
  by_cases hτ : τ ω = ⊤
  · simp [stoppedProcess, hτ]
  · simp [stoppedProcess, hτ]

/-- Helper for Theorem 25.38: clipping the raw increment by `τ ∧ n` is the same as stopping the
visible stopped increment at the deterministic horizon `n`. -/
private theorem rawIncrement_minConst_eq_stageStoppedIncrement_const
    {W : VectorProcess} {U : Set State} {F : State → ℝ} {x : State}
    (n : ℕ) :
    stoppedProcess
        (fun t ω ↦ F (W t ω) - F x)
        (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) =
      stoppedProcess
        (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
        (fun _ ↦ ((n : NNReal) : ENNReal)) := by
  have hDoubleStop :
      stoppedProcess
          (stoppedProcess
            (fun t ω ↦ F (W t ω) - F x)
            (hittingAfter W Uᶜ 0))
          (fun _ ↦ ((n : NNReal) : ENNReal)) =
        stoppedProcess
          (fun t ω ↦ F (W t ω) - F x)
          (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) := by
    -- Proof comment: stopping the raw increment first at `τ` and then at `n` collapses to one
    -- stop at the clipped clock `τ ∧ n`.
    simpa [min_comm] using
      (stoppedProcess_stoppedProcess' :
        stoppedProcess
            (stoppedProcess
              (fun t ω ↦ F (W t ω) - F x)
              (hittingAfter W Uᶜ 0))
            (fun _ ↦ ((n : NNReal) : ENNReal)) =
          stoppedProcess
            (fun t ω ↦ F (W t ω) - F x)
            (fun ω ↦
              min (((fun _ ↦ ((n : NNReal) : ENNReal)) ω))
                ((hittingAfter W Uᶜ 0) ω)))
  -- Proof comment: rewrite the once-stopped raw increment into the visible stopped increment
  -- before transporting the deterministic stop across the equality.
  calc
    stoppedProcess
        (fun t ω ↦ F (W t ω) - F x)
        (fun ω ↦ min (hittingAfter W Uᶜ 0 ω) (n : ENNReal)) =
      stoppedProcess
          (stoppedProcess
            (fun t ω ↦ F (W t ω) - F x)
            (hittingAfter W Uᶜ 0))
          (fun _ ↦ ((n : NNReal) : ENNReal)) := hDoubleStop.symm
    _ =
      stoppedProcess
        (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
        (fun _ ↦ ((n : NNReal) : ENNReal)) := by
          rw [stageStoppedExtension_eq_stoppedRawIncrement]

/-- Helper for Theorem 25.38: stopping the translated increment at `τ` is the same as evaluating
`F` on the translated stopped path. -/
private theorem stageStoppedTranslatedSurface_eq_stoppedRawTranslatedIncrement
    {B : VectorProcess} {τ : Ω → ENNReal} {F : State → ℝ} {x : State} :
    stoppedProcess (fun t ω ↦ F (x + B t ω) - F x) τ =
      fun t ω ↦ F (x + stoppedProcess B τ t ω) - F x := by
  let G : State → ℝ := fun z ↦ F (x + z)
  have hStop :
      stoppedProcess (fun t ω ↦ G (B t ω) - G (0 : State)) τ =
        fun t ω ↦ G (stoppedProcess B τ t ω) - G (0 : State) := by
    -- Proof comment: rewrite the translated increment as an ordinary raw increment for the
    -- translated observable `G z := F (x + z)`.
    simpa [G] using
      (stageStoppedExtension_eq_stoppedRawIncrement
        (W := B) (τ := τ) (F := G) (x := (0 : State)))
  -- Proof comment: unfold the translated observable `G` on both sides.
  simpa [G] using hStop

/-- Helper for Theorem 25.38: deterministic stopping preserves strong adaptedness for the visibly
stopped increment. -/
private theorem stageStoppedVisibleIncrement_constStop_stronglyAdapted
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F)
    (T : NNReal) :
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    StronglyAdapted ℱW
      (stoppedProcess
        (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
        (fun _ ↦ (T : ENNReal))) := by
  intro τ ℱW
  have hτstop : IsStoppingTime ℱW τ := by
    -- Proof comment: the exit clock is a stopping time in the natural filtration of `W`.
    simpa [τ, ℱW] using
      stageExit_isStoppingTime_of_continuous_of_aeExitFinite
        (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite
  have hRawStrong :
      StronglyAdapted ℱW (fun t ω ↦ F (W t ω) - F x) := by
    intro t
    -- Proof comment: each deterministic-time slice is the measurable observable `F` applied to
    -- the current Brownian state, followed by subtraction of the deterministic base value.
    exact
      ((stateComposition_stronglyAdapted_natural
          (hWsm := brownianVectorStartedAt_stronglyMeasurable hW)
          (hFmeas := hFcont.measurable)) t).sub stronglyMeasurable_const
  have hRawCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (W t ω) - F x := by
    intro ω
    -- Proof comment: continuity of the raw increment comes from continuity of the Brownian path
    -- and of `F`.
    simpa using (hFcont.comp (hWcont ω)).sub continuous_const
  have hStoppedStrong :
      StronglyAdapted ℱW (stoppedProcess (fun t ω ↦ F (W t ω) - F x) τ) :=
    hRawStrong.stoppedProcess hRawCont hτstop
  have hTargetAdapted :
      Adapted ℱW (fun t ω ↦ F (stoppedProcess W τ t ω) - F x) := by
    -- Proof comment: normalize the visible target to the stopped raw increment before reading
    -- off adaptedness.
    simpa [stageStoppedExtension_eq_stoppedRawIncrement
      (W := W) (τ := τ) (F := F) (x := x)] using hStoppedStrong.adapted
  have hTargetCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ F (stoppedProcess W τ t ω) - F x := by
    intro ω
    have hStoppedCont :
        Continuous fun t : NNReal ↦ stoppedProcess W τ t ω :=
      continuous_stoppedVectorProcess_of_continuous (X := W) (σ := τ) (ω := ω) (hWcont ω)
    -- Proof comment: continuity of the stopped state path survives composition with `F` and
    -- subtraction of the deterministic base value.
    simpa using (hFcont.comp hStoppedCont).sub continuous_const
  -- Proof comment: deterministic stopping preserves strong adaptedness for the already stopped
  -- visible increment.
  exact hTargetAdapted.stronglyAdapted.stoppedProcess hTargetCont (isStoppingTime_const ℱW T)

/-- Helper for Theorem 25.38: compactness of `closure U` bounds every deterministic stop of the
visibly stopped increment uniformly in time. -/
private theorem stageStoppedVisibleIncrement_constStop_boundedInTimeAe
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hUcpt : IsCompact (closure U))
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F)
    (T : NNReal) :
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    BoundedInTimeAe
      (μ : Measure Ω)
      (stoppedProcess
        (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
        (fun _ ↦ (T : ENNReal))) := by
  intro τ
  rcases existsAbsLeOnCompactClosure_continuous (U := U) (F := F) hUcpt hFcont with
    ⟨C, hCnonneg, hC⟩
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hW
  refine ⟨C + |F x|, ?_⟩
  filter_upwards [hExitFinite, hStartAe] with ω hωfin hωstart t
  have hStartMem : W 0 ω ∈ U := by
    simpa [hωstart] using hx
  have hmem :
      stoppedProcess W τ (min t T) ω ∈ closure U :=
    stageStoppedProcess_mem_buffer
      (U := U) (V := closure U) (W := W) (ω := ω)
      hUo
      (hWcont ω)
      hStartMem
      (by intro z hz; exact hz)
      hωfin
      (min t T)
  have hValueBound :
      |F (stoppedProcess W τ (min t T) ω)| ≤ C :=
    hC _ hmem
  -- Proof comment: the clipped stopped state stays in `closure U`, so the compact-closure bound
  -- on `F` controls the visible increment after one application of `abs_sub_le`.
  calc
    |stoppedProcess (fun s ω ↦ F (stoppedProcess W τ s ω) - F x)
        (fun _ ↦ (T : ENNReal)) t ω|
        = |F (stoppedProcess W τ (min t T) ω) - F x| := by
            simp [stoppedProcessConstTime_eq_min]
    _ ≤ |F (stoppedProcess W τ (min t T) ω)| + |F x| := by
          simpa [sub_eq_add_neg, abs_neg] using
            (abs_add_le (F (stoppedProcess W τ (min t T) ω)) (-F x))
    _ ≤ C + |F x| := add_le_add hValueBound le_rfl

/-- Helper for Theorem 25.38: for `F ∈ C²(State)`, each coordinate partial derivative `∂[i] F`
is continuous. -/
private theorem continuousPartialDeriv_theorem25_38
    (F : State → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin d) :
    Continuous (∂[i] F) := by
  have happly :
      Continuous fun x : State ↦ (fderiv ℝ F x) (EuclideanSpace.single i (1 : ℝ)) := by
    -- Proof comment: a `C²` map has continuous Fréchet derivative, and evaluation at the fixed
    -- basis vector preserves continuity.
    simpa using
      (hF.continuous_fderiv_apply (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).comp
        (continuous_id.prodMk continuous_const)
  -- Proof comment: rewrite the coordinate derivative through the Fréchet derivative formula.
  simpa [partialDeriv_eq_fderiv_apply F (hF.differentiable (by norm_num)) i] using happly

/-- Helper for Theorem 25.38: a `C²` map has differentiable coordinate partial derivatives. -/
private theorem differentiablePartialDeriv_shiftedConstLift_theorem25_38
    (F : State → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin d) :
    Differentiable ℝ (∂[i] F) := by
  let ei : State := EuclideanSpace.single i (1 : ℝ)
  have hfd :
      ContDiff ℝ 1 (fun y ↦ (fderiv ℝ F y) ei) := by
    -- Proof comment: evaluating the Fréchet derivative on the fixed basis vector `eᵢ` lowers the
    -- regularity demand from `C²` to `C¹`.
    simpa [ei] using
      ((contDiff_succ_iff_fderiv_apply (𝕜 := ℝ) (D := State) (E := ℝ) (n := 1)
        (f := F)).mp hF).2.2 ei
  -- Proof comment: the named partial derivative is exactly this derivative-evaluation map.
  simpa [partialDeriv_eq_fderiv_apply F (hF.differentiable (by norm_num)) i] using
    hfd.differentiable_one

/-- Helper for Theorem 25.38: the zero-patched centered vector path agrees almost surely at every
deterministic time with the raw centered Brownian path. -/
private theorem centeredPath_zeroPatched_eq_ae_allTimes_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = W t ω - x := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const (μ := μ) hW
  filter_upwards [hStartAe] with ω hω t
  by_cases ht : t = 0
  · -- Proof comment: at time `0`, the zero patch matches the raw centered path because the
    -- Brownian vector starts at `x` almost surely.
    subst ht
    simp [B, hω]
  · -- Proof comment: away from time `0`, the zero-patched path is definitionally the raw
    -- centered Brownian path.
    simp [B, ht]

/-- Helper for Theorem 25.38: translating the input of a `C²` function preserves the `C²`
regularity needed for the centered pathwise Itô route. -/
private theorem translatedContDiff_theorem25_38
    {F : State → ℝ} (hFcontDiff : ContDiff ℝ 2 F) (x : State) :
    ContDiff ℝ 2 (fun z : State ↦ F (x + z)) := by
  -- Proof comment: the centered-path proof uses the translated observable `z ↦ F (x + z)`, so
  -- we package once that affine translation preserves `C²` regularity.
  simpa using hFcontDiff.comp ((contDiff_const.add contDiff_id).of_le le_top)

/-- Helper for Theorem 25.38: the coordinate partial derivatives of a translated observable are
the translated coordinate partial derivatives of the original observable. -/
private theorem translatedPartialDeriv_eq_theorem25_38
    {F : State → ℝ} (hF : Differentiable ℝ F) (x z : State) (i : Fin d) :
    (∂[i] fun w : State ↦ F (x + w)) z = (∂[i] F) (x + z) := by
  let G : State → ℝ := fun w : State ↦ F (x + w)
  have hG : Differentiable ℝ G := by
    intro w
    -- Proof comment: composing with the affine translation `w ↦ x + w` preserves
    -- differentiability.
    exact ((hF (x + w)).hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)).differentiableAt
  have hFDeriv :
      fderiv ℝ G z = fderiv ℝ F (x + z) := by
    have hcomp :
        HasFDerivAt G (fderiv ℝ F (x + z)) z := by
      -- Proof comment: the derivative of the translation map is the identity, so the translated
      -- observable has the same derivative matrix as `F` at the translated point.
      simpa [G] using (hF (x + z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_add x)
    simpa using hcomp.fderiv
  have hEval :
      (fderiv ℝ G z) (EuclideanSpace.single i (1 : ℝ)) =
        (fderiv ℝ F (x + z)) (EuclideanSpace.single i (1 : ℝ)) := by
    -- Proof comment: evaluate the identified Fréchet derivatives on the `i`-th basis vector to
    -- recover the coordinate partial derivative.
    simpa using
      congrArg
        (fun L : State →L[ℝ] ℝ ↦ L (EuclideanSpace.single i (1 : ℝ)))
        hFDeriv
  -- Proof comment: rewrite both named partial derivatives through the Fréchet derivative.
  simpa [partialDeriv_eq_fderiv_apply G hG i, partialDeriv_eq_fderiv_apply F hF i] using hEval

/-- Helper for Theorem 25.38: second coordinate partial derivatives commute with translation in
the same way as first coordinate partial derivatives. -/
private theorem translatedSecondPartialDeriv_eq_theorem25_38
    {F : State → ℝ} (hF : ContDiff ℝ 2 F) (x z : State) (i j : Fin d) :
    (∂²[i, j] fun w : State ↦ F (x + w)) z = (∂²[i, j] F) (x + z) := by
  have hFirst :
      (∂[i] fun w : State ↦ F (x + w)) =
        fun w : State ↦ (∂[i] F) (x + w) := by
    funext w
    -- Proof comment: the first translated partial derivative already matches the translated
    -- partial derivative of `F` pointwise.
    exact
      translatedPartialDeriv_eq_theorem25_38
        (F := F)
        (hF := hF.differentiable (by norm_num))
        x
        w
        i
  -- Proof comment: once the first translated partial derivative is identified, apply the same
  -- translation lemma to the differentiable function `∂[i] F`.
  rw [secondPartialDeriv, hFirst]
  exact
    translatedPartialDeriv_eq_theorem25_38
      (F := ∂[i] F)
      (hF := differentiablePartialDeriv_shiftedConstLift_theorem25_38 F hF i)
      x
      z
      j

/-- Helper for Theorem 25.38: the Kronecker-delta bracket primitive is the set integral of the
constant density `1` on the diagonal and `0` off the diagonal. -/
private theorem kroneckerPrimitive_eq_setIntegral_theorem25_38
    (i j : Fin d) (T : NNReal) :
    (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (if i = j then (1 : ℝ) else 0)) =
      if i = j then (T : ℝ) else 0 := by
  by_cases hij : i = j
  · subst hij
    have hle : (0 : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast T.2
    -- Proof comment: on the diagonal, the constant-density primitive is just the interval
    -- length.
    rw [if_pos rfl, MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le hle]
    simp
  · -- Proof comment: off the diagonal, the Kronecker density vanishes identically.
    simp [hij, MeasureTheory.setIntegral_const]

/-- Helper for Theorem 25.38: the constant Kronecker-delta density is integrable on every compact
interval. -/
private theorem kroneckerDensity_integrableOn_theorem25_38
    (i j : Fin d) (b : ℝ) :
    IntegrableOn (fun s : ℝ ↦ if i = j then (1 : ℝ) else 0) (Set.Icc (0 : ℝ) b) := by
  -- Proof comment: the density is either the constant `1` or the constant `0`.
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Helper for Theorem 25.38: a Kronecker-delta quadratic-covariation family collapses the raw
double correction term to the diagonal set-integral family. -/
private theorem kroneckerQuadraticCorrection_eq_diagIntegrals_theorem25_38
    {F : State → ℝ} (hF : ContDiff ℝ 2 F)
    {X : VectorPathSpace d}
    (hcov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          (fun T ↦ if i = j then (T : ℝ) else 0))
    (T : NNReal) :
    ((1 : ℝ) / 2) *
        ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (X s))
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            T
      =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂²[i, i] F) (X s.toNNReal) := by
  have hpair :
      ∀ i j : Fin d,
        pathwiseQuadraticCovariationIntegral
          (fun s ↦ (∂²[i, j] F) (X s))
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          T
        =
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (if i = j then (1 : ℝ) else 0) * (∂²[i, j] F) (X s.toNNReal) := by
    intro i j
    -- Proof comment: rewrite each pairwise covariation term through the scalar-density bridge,
    -- using the Kronecker primitive as `∫ 1` on the diagonal and `∫ 0` off the diagonal.
    exact
      pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationDensity
        (fun s ↦ (∂²[i, j] F) (X s))
        (Yi := vectorPathComponent X i)
        (Yj := vectorPathComponent X j)
        (aii := fun _ : ℝ ↦ (1 : ℝ))
        (aij := fun _ : ℝ ↦ if i = j then (1 : ℝ) else 0)
        (ajj := fun _ : ℝ ↦ (1 : ℝ))
        (by simpa [kroneckerPrimitive_eq_setIntegral_theorem25_38] using hcov i i)
        (by simpa [kroneckerPrimitive_eq_setIntegral_theorem25_38] using hcov j j)
        (by simpa [kroneckerPrimitive_eq_setIntegral_theorem25_38] using hcov i j)
        (fun n ↦ by simpa using kroneckerDensity_integrableOn_theorem25_38 i i (n : ℝ))
        (fun n ↦ by simpa using kroneckerDensity_integrableOn_theorem25_38 i j (n : ℝ))
        (fun n ↦ by simpa using kroneckerDensity_integrableOn_theorem25_38 j j (n : ℝ))
        ((continuous_secondPartialDeriv F hF i j).comp X.continuous)
        T
        (by simpa using kroneckerDensity_integrableOn_theorem25_38 i j (T : ℝ))
  -- Proof comment: after the pairwise rewrite, every off-diagonal summand is zero and the
  -- diagonal summands are exactly the desired second-derivative integrals.
  calc
    ((1 : ℝ) / 2) *
        ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (X s))
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            T
      =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d, ∑ j : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              (if i = j then (1 : ℝ) else 0) * (∂²[i, j] F) (X s.toNNReal) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hpair i j
    _ =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂²[i, i] F) (X s.toNNReal) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            simp [hj]
          · intro hi_not_mem
            exact False.elim (hi_not_mem (Finset.mem_univ i))

/-- Helper for Theorem 25.38: the zero-patched centered coordinate differs from the raw centered
coordinate only at time `0`, and Brownian motion started at `x` already hits that value almost
surely. -/
private theorem centeredCoordinate_zeroPatched_eq_ae_allTimes_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else W t ω - x) i
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, Bi t ω = Zi t ω := by
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else W t ω - x) i
  have hStartAe : ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const (μ := μ) hW
  filter_upwards [hStartAe] with ω hω t
  by_cases ht : t = 0
  · -- Proof comment: at time `0`, the zero patch agrees with the centered coordinate because
    -- Brownian motion starts at `x` almost surely.
    subst ht
    simp [Bi, Zi, hω]
  · -- Proof comment: away from time `0`, the zero patch is definitionally the centered
    -- coordinate.
    simp [Bi, Zi, ht]

/-- Helper for Theorem 25.38: the compensated square of the zero-patched centered coordinate
agrees almost surely at every deterministic time with the compensated square of the raw centered
coordinate. -/
private theorem centeredCoordinate_compensatedSquare_zeroPatched_eq_ae_allTimes_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else W t ω - x) i
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      Bi t ω ^ 2 - (t : ℝ) = Zi t ω ^ 2 - (t : ℝ) := by
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else W t ω - x) i
  filter_upwards
      [centeredCoordinate_zeroPatched_eq_ae_allTimes_theorem25_38
        (μ := μ) (W := W) (x := x) hW i] with ω hω t
  -- Proof comment: once the coordinates agree pointwise, the compensated squares agree by the
  -- same deterministic algebra.
  rw [hω t]

/-- Helper for Theorem 25.38: the natural filtration of the pointwise-zero patched centered
coordinate is contained in the natural filtration of the ambient Brownian vector process `W`. -/
private theorem pointwiseZeroCoordinateNatural_le_brownianNatural_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x) (i : Fin d) :
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else W t ω - x) i
    Filtration.natural Bi
        (by
          intro t
          by_cases ht : t = 0
          · simp [Bi, ht]
          ·
            have hcoord :
                Measurable (fun ω : Ω ↦ W t ω i - x i) :=
              (((continuous_apply i).measurable.comp
                (brownianVectorStartedAt_stronglyMeasurable hW t).measurable).sub
                measurable_const)
            simpa [Bi, ht] using hcoord.stronglyMeasurable)
      ≤
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW) := by
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else W t ω - x) i
  have hBi_sm : ∀ t : NNReal, StronglyMeasurable (Bi t) := by
    intro t
    by_cases ht : t = 0
    · simp [Bi, ht]
    ·
      have hcoord :
          Measurable (fun ω : Ω ↦ W t ω i - x i) :=
        (((continuous_apply i).measurable.comp
          (brownianVectorStartedAt_stronglyMeasurable hW t).measurable).sub
          measurable_const)
      simpa [Bi, ht] using hcoord.stronglyMeasurable
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  have hBi_adapted : Adapted ℱW Bi := by
    have hcoordStrong :
        StronglyAdapted ℱW (fun t ω ↦ W t ω i - x i) := by
      intro t
      have hslice :
          StronglyMeasurable[ℱW t] (W t) :=
        Filtration.stronglyAdapted_natural
          (u := W) (brownianVectorStartedAt_stronglyMeasurable hW) t
      exact
        ((((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).sub
          measurable_const).stronglyMeasurable)
    intro t
    by_cases ht : t = 0
    · simpa [Bi, ht] using
        (stronglyMeasurable_const : StronglyMeasurable[ℱW t] fun _ : Ω ↦ (0 : ℝ)).measurable
    · simpa [Bi, ht] using (hcoordStrong t).measurable
  -- Proof comment: once every deterministic-time slice of the scalar coordinate process is
  -- adapted to the ambient Brownian filtration, the natural-filtration universal property gives
  -- the desired inclusion.
  exact (adapted_iff_natural_le hBi_sm).mp hBi_adapted

/-- Helper for Theorem 25.38: in the natural filtration of `W`, each centered coordinate
`t ↦ W t ω i - x i` is a continuous local martingale with deterministic time as square
variation. -/
private theorem centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi ∧
    IsContinuousSquareVariationProcess
        ℱW
        (μ : Measure Ω)
        Zi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := by
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (if t = 0 then (0 : State) else W t ω - x) i
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  have hBi : IsBrownianMotion (μ : Measure Ω) Bi := by
    -- Proof comment: patching the time-zero value of the centered coordinate produces the
    -- standard Brownian coordinate used to access the canonical martingale owners.
    simpa [Bi] using
      (shiftedPatchedVector_isStandardBrownian (μ := μ) (W := W) (x := x) hW).isBrownianMotion i
  have hBiNatLe :
      Filtration.natural Bi hBi.stronglyMeasurable ≤ ℱW := by
    simpa [Bi, ℱW] using
      pointwiseZeroCoordinateNatural_le_brownianNatural_theorem25_38
        (μ := μ) (W := W) (x := x) hW i
  have hBiMartNat :
      Martingale Bi (Filtration.natural Bi hBi.stronglyMeasurable) (μ : Measure Ω) :=
    brownianMartingale_natural (μ := (μ : Measure Ω)) (B := Bi) hBi
  have hBiLocal :
      IsLocalMartingale ℱW (μ : Measure Ω) Bi :=
    martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_38
      (martingale_of_le_filtration hBiNatLe hBiMartNat)
  have hZi_adapted : Adapted ℱW Zi := by
    have hcoordStrong :
        StronglyAdapted ℱW Zi := by
      intro t
      have hslice :
          StronglyMeasurable[ℱW t] (W t) :=
        Filtration.stronglyAdapted_natural
          (u := W) (brownianVectorStartedAt_stronglyMeasurable hW) t
      exact
        ((((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).sub
          measurable_const).stronglyMeasurable)
    exact hcoordStrong.adapted
  have hZi_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Zi t ω := by
    intro ω
    -- Proof comment: the centered coordinate is the continuous Brownian coordinate minus the
    -- deterministic starting value.
    simpa [Zi] using ((EuclideanSpace.proj i).continuous.comp (hWcont ω)).sub continuous_const
  have hBiEqZi :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, Bi t ω = Zi t ω := by
    -- Proof comment: use the dedicated zero-patch bridge so the local-martingale transport stays
    -- in one canonical spelling.
    simpa [Bi, Zi] using
      centeredCoordinate_zeroPatched_eq_ae_allTimes_theorem25_38
        (μ := μ) (W := W) (x := x) hW i
  have hZi_local :
      IsLocalMartingale ℱW (μ : Measure Ω) Zi :=
    isLocalMartingale_congr_ae_allTimes_theorem25_38
      hBiLocal
      hZi_adapted
      hZi_cont
      hBiEqZi
  have hZi_sq_local :
      IsLocalMartingale
        ℱW
        (μ : Measure Ω)
        (fun t ω ↦ Zi t ω ^ 2 - (t : ℝ)) := by
    have hBiSqMartNat :
        Martingale
          (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ))
          (Filtration.natural Bi hBi.stronglyMeasurable)
          (μ : Measure Ω) :=
      brownian_sq_sub_time_martingale (μ := (μ : Measure Ω)) (B := Bi) hBi
    have hBiSqLocal :
        IsLocalMartingale
          ℱW
          (μ : Measure Ω)
          (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ)) :=
      martingale_isLocalMartingale_of_isFiniteMeasure_theorem25_38
        (martingale_of_le_filtration hBiNatLe hBiSqMartNat)
    have hZiSq_adapted :
        Adapted ℱW (fun t ω ↦ Zi t ω ^ 2 - (t : ℝ)) := by
      simpa [pow_two] using
        (hZi_adapted.mul hZi_adapted).sub
          (adapted_const' ℱW (fun t : NNReal ↦ (t : ℝ)))
    have hZiSq_cont :
        ∀ ω : Ω, Continuous fun t : NNReal ↦ Zi t ω ^ 2 - (t : ℝ) := by
      intro ω
      -- Proof comment: the compensated square is continuous because both the coordinate path and
      -- the deterministic time clock are continuous.
      simpa [pow_two] using (hZi_cont ω).mul (hZi_cont ω) |>.sub continuous_subtype_val
    have hBiSqEqZiSq :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          Bi t ω ^ 2 - (t : ℝ) = Zi t ω ^ 2 - (t : ℝ) := by
      -- Proof comment: reuse the extracted compensated-square bridge instead of rebuilding the
      -- same time-zero case split locally.
      simpa [Bi, Zi] using
        centeredCoordinate_compensatedSquare_zeroPatched_eq_ae_allTimes_theorem25_38
          (μ := μ) (W := W) (x := x) hW i
    exact
      isLocalMartingale_congr_ae_allTimes_theorem25_38
        hBiSqLocal
        hZiSq_adapted
        hZiSq_cont
        hBiSqEqZiSq
  have hZi_contLocal :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi := by
    exact ⟨hZi_local, hZi_cont⟩
  refine ⟨hZi_contLocal, ?_⟩
  refine
    { zero := by
        funext ω
        simp
      adapted := adapted_const' ℱW (fun t : NNReal ↦ (t : ℝ))
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · intro ω
    -- Proof comment: the deterministic time clock is continuous on `NNReal`.
    simpa using continuous_subtype_val
  · intro ω s t hst
    exact_mod_cast hst
  · refine
      { local_martingale := hZi_sq_local
        continuous := ?_ }
    intro ω
    -- Proof comment: the compensated square of the centered coordinate is continuous because the
    -- coordinate path and the deterministic clock are continuous.
    simpa [Zi, pow_two] using
      (((EuclideanSpace.proj i).continuous.comp (hWcont ω)).sub continuous_const).mul
        (((EuclideanSpace.proj i).continuous.comp (hWcont ω)).sub continuous_const) |>.sub
        continuous_subtype_val

/-- Helper for Theorem 25.38: the raw `i`-th partial-derivative coefficient along the Brownian
path. -/
private def coordinatePartialDerivProcess_theorem25_38
    {W : VectorProcess} {F : State → ℝ}
    (i : Fin d) : NNReal → Ω → ℝ :=
  fun r ω ↦ (∂[i] F) (W r ω)

/-- Helper for Theorem 25.38: before the exit time, the `i`-th partial-derivative coefficient is
progressively measurable in the natural filtration of `W`. -/
private theorem centeredCoordinateStoppedPartialDerivProgMeasurableNatural_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {U : Set State} {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) :
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let Hi : NNReal → Ω → ℝ :=
      coordinatePartialDerivProcess_theorem25_38 (Ω := Ω) (W := W) (F := F) i
    ProgMeasurable ℱW (processBeforeStoppingTime Hi τ) := by
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let Hi : NNReal → Ω → ℝ :=
    coordinatePartialDerivProcess_theorem25_38 (Ω := Ω) (W := W) (F := F) i
  have hτstop : IsStoppingTime ℱW τ := by
    -- Proof comment: the exit clock is already packaged as a stopping time in the natural
    -- filtration of `W`.
    simpa [τ, ℱW] using
      stageExit_isStoppingTime_of_continuous_of_aeExitFinite
        (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite
  have hHi_strong : StronglyAdapted ℱW Hi := by
    intro t
    -- Proof comment: each deterministic-time slice is the continuous observable `∂[i] F`
    -- applied to the Brownian state at time `t`.
    exact
      stateComposition_stronglyAdapted_natural
        (W := W)
        (hWsm := brownianVectorStartedAt_stronglyMeasurable hW)
        (hFmeas := (continuousPartialDeriv_theorem25_38 F hFcontDiff i).measurable)
        t
  have hHi_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Hi t ω := by
    intro ω
    -- Proof comment: the raw coefficient is the continuous partial derivative observed along the
    -- continuous Brownian sample path.
    simpa [Hi] using ((continuousPartialDeriv_theorem25_38 F hFcontDiff i).comp (hWcont ω))
  have hHi_prog : ProgMeasurable ℱW Hi :=
    hHi_strong.progMeasurable_of_continuous hHi_cont
  -- Proof comment: stopping a progressively measurable coefficient before the exit time preserves
  -- progressive measurability.
  exact MeasureTheory.processBeforeStoppingTime_progMeasurable hHi_prog hτstop

/-- Helper for Theorem 25.38: the stopped partial-derivative coefficient has finite square energy
on every deterministic interval `[0,T]`. -/
private theorem stoppedPartialDeriv_sqIntegrableOnIcc_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess}
    {U : Set State} {F : State → ℝ}
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T : NNReal) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      IntegrableOn
        (fun s : ℝ ↦
          (processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              (hittingAfter W Uᶜ 0)
              s.toNNReal
              ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
  filter_upwards [hExitFinite] with ω hωfin
  let τω : NNReal := (hittingAfter W Uᶜ 0 ω).untopA
  have hτω : ((τω : NNReal) : ENNReal) = hittingAfter W Uᶜ 0 ω := by
    dsimp [τω]
    rw [WithTop.untopA_eq_untop (ne_of_lt hωfin)]
    exact WithTop.coe_untop _ _
  let S : NNReal := min T τω
  let rawCoeff : ℝ → ℝ := fun s ↦
    coordinatePartialDerivProcess_theorem25_38
      (Ω := Ω) (W := W) (F := F) i s.toNNReal ω
  let stoppedCoeff : ℝ → ℝ := fun s ↦
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_38
        (Ω := Ω) (W := W) (F := F) i)
      (hittingAfter W Uᶜ 0)
      s.toNNReal
      ω
  have hRawCont : Continuous rawCoeff := by
    -- Proof comment: compose the continuous Brownian sample path with the continuous partial
    -- derivative observable.
    exact (continuousPartialDeriv_theorem25_38 F hFcontDiff i).comp
      ((hWcont ω).comp continuous_real_toNNReal)
  have hRawSqInt :
      IntegrableOn (fun s : ℝ ↦ rawCoeff s ^ 2) (Set.Icc (0 : ℝ) (S : ℝ)) := by
    -- Proof comment: on the clipped interval `[0, T ∧ τ(ω)]`, the unstopped coefficient is a
    -- continuous real path on a compact interval.
    simpa [rawCoeff] using (hRawCont.pow 2).integrableOn_Icc
  have hStoppedSqIntSmall :
      IntegrableOn (fun s : ℝ ↦ stoppedCoeff s ^ 2) (Set.Icc (0 : ℝ) (S : ℝ)) := by
    refine hRawSqInt.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hs_toNNReal_le_S : s.toNNReal ≤ S := by
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2
    have hs_toNNReal_le_τω : s.toNNReal ≤ τω :=
      hs_toNNReal_le_S.trans (min_le_right T τω)
    have hs_le_exit :
        (s.toNNReal : ENNReal) ≤ hittingAfter W Uᶜ 0 ω := by
      have hs_le_exit' : (s.toNNReal : ENNReal) ≤ (τω : ENNReal) := by
        exact_mod_cast hs_toNNReal_le_τω
      -- Proof comment: on the clipped horizon the stopping indicator is still active, so the
      -- stopped coefficient agrees with the raw partial derivative.
      exact hs_le_exit'.trans_eq hτω
    dsimp [stoppedCoeff]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs_le_exit]
  have hStoppedSqInt :
      IntegrableOn (fun s : ℝ ↦ stoppedCoeff s ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)) := by
    refine IntegrableOn.of_forall_diff_eq_zero hStoppedSqIntSmall measurableSet_Icc ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1.1
    have hs_not_le_S : ¬ s ≤ S := by
      intro hsS
      exact hs.2 ⟨hs_nonneg, hsS⟩
    have hs_not_le_exit :
        ¬ (s.toNNReal : ENNReal) ≤ hittingAfter W Uᶜ 0 ω := by
      intro hs_le_exit
      have hs_toNNReal_le_τω : s.toNNReal ≤ τω := by
        -- Proof comment: once the exit clock is finite, comparison in `ENNReal` drops back to
        -- the underlying `NNReal` value of the exit time.
        exact_mod_cast (hτω.symm ▸ hs_le_exit)
      have hs_le_τω : s ≤ τω := by
        simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le_τω
      exact hs_not_le_S (le_min hs.1.2 hs_le_τω)
    -- Proof comment: beyond the clipped exit horizon, the stopped coefficient is identically
    -- zero, so the remaining tail contributes no energy.
    dsimp [stoppedCoeff]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs_not_le_exit]
    simp
  simpa [stoppedCoeff] using hStoppedSqInt

/-- Helper for Theorem 25.38: after deterministically cutting off the exit-stopped `i`-th
partial-derivative coefficient at horizon `T`, the same square-energy witness extends to every
test interval `[0,U]`. -/
private theorem stoppedPartialDeriv_constCutoff_sqIntegrableOnIcc_allHorizons_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess}
    {U : Set State} {F : State → ℝ}
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T U' : NNReal) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      IntegrableOn
        (fun s : ℝ ↦
          (processBeforeStoppingTime
              (processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_38
                  (Ω := Ω) (W := W) (F := F) i)
                (hittingAfter W Uᶜ 0))
              (fun _ ↦ (T : ENNReal))
              s.toNNReal
              ω) ^ 2)
        (Set.Icc (0 : ℝ) (U' : ℝ)) := by
  have hBase :
      ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (ProbabilityTheory.processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_38
                  (Ω := Ω) (W := W) (F := F) i)
                (hittingAfter W Uᶜ 0)
                s.toNNReal
                ω) ^ 2)
          (Set.Icc (0 : ℝ) (T : ℝ)) :=
    stoppedPartialDeriv_sqIntegrableOnIcc_theorem25_38
      (μ := μ) (W := W) (U := U) (F := F)
      hWcont hExitFinite hFcontDiff i T
  filter_upwards [hBase] with ω hω
  let g : ℝ → ℝ := fun s ↦
    (ProbabilityTheory.processBeforeStoppingTime
        (ProbabilityTheory.processBeforeStoppingTime
          (coordinatePartialDerivProcess_theorem25_38
            (Ω := Ω) (W := W) (F := F) i)
          (hittingAfter W Uᶜ 0))
        (fun _ ↦ (T : ENNReal))
        s.toNNReal
        ω) ^ 2
  have hBaseCut :
      IntegrableOn g (Set.Icc (0 : ℝ) (T : ℝ)) := by
    refine hω.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hs_toNNReal_le : s.toNNReal ≤ T := by
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2
    have hs_cutoff : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      exact_mod_cast hs_toNNReal_le
    -- Proof comment: on the base interval `[0, T]`, the deterministic cutoff leaves the
    -- exit-stopped coefficient unchanged.
    have hOuter :
        ProbabilityTheory.processBeforeStoppingTime
            (ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              (hittingAfter W Uᶜ 0))
            (fun _ ↦ (T : ENNReal))
            s.toNNReal
            ω =
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s.toNNReal
            ω := by
      rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs_cutoff]
    dsimp [g]
    rw [hOuter]
  have hCut :
      IntegrableOn g (Set.Icc (0 : ℝ) (U' : ℝ)) := by
    refine IntegrableOn.of_forall_diff_eq_zero hBaseCut measurableSet_Icc ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1.1
    have hs_not_le : ¬ s ≤ T := by
      intro hs_le
      exact hs.2 ⟨hs_nonneg, hs_le⟩
    have hs_not_cutoff :
        ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      intro hs_cutoff
      have hs_toNNReal_le : s.toNNReal ≤ T := by
        exact_mod_cast hs_cutoff
      have hs_le : s ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le
      exact hs_not_le hs_le
    -- Proof comment: once `s > T`, the deterministic cutoff kills the coefficient, so the tail
    -- contributes zero energy on `[0, U']`.
    dsimp [g]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs_not_cutoff]
    simp
  simpa [g] using hCut

/-- Helper for Theorem 25.38: the fixed-horizon cutoff coefficient satisfies the exact
unit-density bracket-energy spelling needed for the deterministic-cutoff Itô input. -/
private theorem stoppedPartialDeriv_constCutoff_unitDensityIntegrable_allHorizons_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess}
    {U : Set State} {F : State → ℝ}
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T U' : NNReal) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      IntegrableOn
        (fun s : ℝ ↦
          (processBeforeStoppingTime
              (processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_38
                  (Ω := Ω) (W := W) (F := F) i)
                (hittingAfter W Uᶜ 0))
              (fun _ ↦ (T : ENNReal))
              s.toNNReal
              ω) ^ 2 * (1 : ℝ))
        (Set.Icc (0 : ℝ) (U' : ℝ)) := by
  have hSq :
      ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (processBeforeStoppingTime
                (processBeforeStoppingTime
                  (coordinatePartialDerivProcess_theorem25_38
                    (Ω := Ω) (W := W) (F := F) i)
                  (hittingAfter W Uᶜ 0))
                (fun _ ↦ (T : ENNReal))
                s.toNNReal
                ω) ^ 2)
          (Set.Icc (0 : ℝ) (U' : ℝ)) :=
    stoppedPartialDeriv_constCutoff_sqIntegrableOnIcc_allHorizons_theorem25_38
      (μ := μ) (W := W) (U := U) (F := F)
      hWcont hExitFinite hFcontDiff i T U'
  filter_upwards [hSq] with ω hω
  -- Proof comment: the unit bracket density is definitionally `1`, so this is the same square
  -- energy statement as above.
  simpa using hω

/-- Helper for Theorem 25.38: the centered coordinate in the natural filtration of `W` already
fits the Chapter 25.21 absolutely-continuous bracket interface with deterministic density `1`. -/
private theorem centeredCoordinate_hasAbsolutelyContinuousSquareVariation_natural_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω) (i : Fin d) :
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi := by
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let hPair :=
    centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i
  let hZi : IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi := hPair.1
  have hSq :
      IsContinuousSquareVariationProcess
        ℱW
        (μ : Measure Ω)
        Zi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := hPair.2
  refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), hSq, ?_, ?_⟩
  · -- Proof comment: the bracket density is the deterministic constant `1`, so progressive
    -- measurability is immediate.
    simpa using
      (progMeasurable_const : ProgMeasurable ℱW (fun _ _ : Ω ↦ (1 : ℝ)))
  · intro t ω
    -- Proof comment: the chosen square variation is still the deterministic clock, so the
    -- integral identity is exactly `∫_0^t 1 ds = t`.
    simp [Real.volume_Icc]

/-- Helper for Theorem 25.38: package the measurable and square-variation side conditions for the
deterministically cut off stopped coordinate coefficient. -/
private theorem coordinateConstCutoffItoInputData_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T : NNReal) :
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        τ
    ProgMeasurable ℱW Hi ∧
      (∀ U' : NNReal, ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (ProbabilityTheory.processBeforeStoppingTime
                Hi
                (fun _ ↦ (T : ENNReal))
                s.toNNReal
                ω) ^ 2 * (1 : ℝ))
          (Set.Icc (0 : ℝ) (U' : ℝ))) ∧
      ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi := by
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
  let hZi :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i).1
  let Hi : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_38
        (Ω := Ω) (W := W) (F := F) i)
      τ
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the exit-stopped coefficient is already progressively measurable in the
    -- natural filtration of `W`.
    simpa [ℱW, τ, Hi] using
      centeredCoordinateStoppedPartialDerivProgMeasurableNatural_theorem25_38
        (μ := μ) (W := W) (x := x) (U := U) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff i
  · intro U'
    -- Proof comment: after adding the deterministic cutoff at horizon `T`, the unit-density
    -- square-energy bound holds on every test interval `[0,U']`.
    simpa [τ, Hi] using
      stoppedPartialDeriv_constCutoff_unitDensityIntegrable_allHorizons_theorem25_38
        (μ := μ) (W := W) (U := U) (F := F)
        hWcont hExitFinite hFcontDiff i T U'
  · -- Proof comment: the centered coordinate already carries the required absolutely continuous
    -- bracket witness with density `1`.
    simpa [ℱW, Zi, hZi] using
      centeredCoordinate_hasAbsolutelyContinuousSquareVariation_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i

/-- Helper for Theorem 25.38: for one coordinate, the Chapter 25.21 constructor already produces
the fixed-horizon continuous-local-martingale owner of the deterministic-cutoff Itô term. -/
private theorem coordinateConstCutoffItoUpTo_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) (T : NNReal) :
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        τ
    ∃ N : NNReal → Ω → ℝ,
      IsContinuousLocalMartingaleUpToLocal ℱW (μ : Measure Ω) T N ∧
      EqUpTo (μ : Measure Ω) T
        N
        (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi) := by
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
  let hZi :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i).1
  let Hi : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_38
        (Ω := Ω) (W := W) (F := F) i)
      τ
  let Hcut : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (T : ENNReal))
  rcases
      coordinateConstCutoffItoInputData_theorem25_38
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff i T with
    ⟨hHi_prog, hHi_sq, _hbrInput⟩
  have hHcut_prog : ProgMeasurable ℱW Hcut := by
    -- Proof comment: deterministic cutoff preserves progressive measurability of the stopped
    -- coefficient.
    exact
      MeasureTheory.processBeforeStoppingTime_progMeasurable
        hHi_prog
        (isStoppingTime_const ℱW T)
  have hSq :
      IsContinuousSquareVariationProcess
        ℱW
        (μ : Measure Ω)
        Zi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i).2
  let hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi := by
    refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), hSq, ?_, ?_⟩
    · -- Proof comment: the bracket density is again the deterministic constant `1`.
      simpa using
        (progMeasurable_const : ProgMeasurable ℱW (fun _ _ : Ω ↦ (1 : ℝ)))
    · intro t ω
      -- Proof comment: the associated bracket process is still the deterministic time clock.
      simp [Real.volume_Icc]
  have hHcut_sq :
      ∀ U' : NNReal, ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (Hcut s.toNNReal ω) ^ 2 * (hbr.density s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (U' : ℝ)) := by
    intro U'
    filter_upwards [hHi_sq U'] with ω hω
    -- Proof comment: the chosen bracket density for the centered coordinate is definitionally
    -- the constant function `1`.
    refine hω.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hDensity : (hbr.density s.toNNReal ω : ℝ) = 1 := by
      simp [hbr]
    rw [hDensity, mul_one]
  rcases
      ProbabilityTheory.exists_continuousLocalMartingaleItoIntegral
        hZi hbr hHcut_prog hHcut_sq with
    ⟨N, hN⟩
  refine ⟨N, ?_, ?_⟩
  · -- Proof comment: the Chapter 25.21 owner is already a genuine continuous local martingale,
    -- so it supplies its own fixed-horizon witness.
    exact
      isContinuousLocalMartingaleUpToLocal_of_isContinuousLocalMartingale
        hN.continuousLocalMartingale
  · have hEqCanonicalCut :
        EqUpTo
          (μ : Measure Ω)
          T
          N
          (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hcut) := by
      exact
        eqUpTo_of_areIndistinguishable_theorem25_38
          (ProbabilityTheory.IsContinuousLocalMartingaleItoIntegralOwner
            .indistinguishable_canonical hN.itoIntegral)
    have hEqCutoff :
        EqUpTo
          (μ : Measure Ω)
          T
          (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hcut)
          (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi) := by
      exact
        eqUpTo_sym <|
          by
            simpa [EqUpTo, ProbabilityTheory.Theorem25_21.EqUpTo, Hcut, Hi] using
              (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
                (μ := (μ : Measure Ω))
                (ℱ := ℱW)
                (hM := hZi)
                (H := Hi)
                T)
    -- Proof comment: combine the owner's indistinguishability with the deterministic-cutoff
    -- comparison to return from the visible cutoff process to the original stopped coefficient.
    exact eqUpTo_trans hEqCanonicalCut hEqCutoff

/-- Helper for Theorem 25.38: before the exit time, the theorem-local stopped coordinate
integrand is just the raw translated partial derivative observed along the centered path. -/
private theorem stoppedCoordinatePartial_beforeExit_eq_theorem25_38
    {W : VectorProcess} {x : State} {U : Set State} {F : State → ℝ}
    {B : VectorProcess} {ω : Ω} (hω : ∀ t : NNReal, B t ω = W t ω - x)
    (i : Fin d) {t : NNReal}
    (ht : (t : ENNReal) ≤ hittingAfter W Uᶜ 0 ω) :
    ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        (hittingAfter W Uᶜ 0)
        t
        ω =
      (∂[i] F) (x + B t ω) := by
  rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos ht]
  have hstate : x + B t ω = W t ω := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun z : State ↦ x + z) (hω t)
  -- Proof comment: before exit the stopping cutoff is inactive, so only the translated state
  -- identity `x + B t ω = W t ω` remains to rewrite the coefficient.
  simpa [coordinatePartialDerivProcess_theorem25_38, hstate]

/-- Helper for Theorem 25.38: after the exit time, the theorem-local stopped coordinate
integrand vanishes identically. -/
private theorem stoppedCoordinatePartial_afterExit_eq_zero_theorem25_38
    {W : VectorProcess} {U : Set State} {F : State → ℝ}
    (i : Fin d) {ω : Ω} {t : NNReal}
    (ht : hittingAfter W Uᶜ 0 ω < (t : ENNReal)) :
    ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        (hittingAfter W Uᶜ 0)
        t
        ω = 0 := by
  -- Proof comment: once `t` lies strictly after the exit horizon, the stopping cutoff forces the
  -- coefficient to zero by definition.
  rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg (not_le_of_lt ht)]

/-- Helper for Theorem 25.38: on a fixed sample, the stopped coordinate coefficient is exactly
the raw translated coefficient cut off at the clipped exit time. -/
private theorem sampleStoppedCoordinate_eq_constCutoffRaw_theorem25_38
    {W : VectorProcess} {x : State} {U : Set State} {F : State → ℝ}
    {B : VectorProcess} {ω : Ω}
    (hω : ∀ t : NNReal, B t ω = W t ω - x)
    (hF : Differentiable ℝ F)
    (i : Fin d) {T : NNReal}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω) :
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        (hittingAfter W Uᶜ 0)
    ∀ s : NNReal,
      Hi s ω =
        if (s : ENNReal) ≤ (T : ENNReal) then
          (∂[i] fun z : State ↦ F (x + z)) (B s ω)
        else
          0 := by
  intro Hi s
  by_cases hs : (s : ENNReal) ≤ (T : ENNReal)
  · have hs_exit : (s : ENNReal) ≤ hittingAfter W Uᶜ 0 ω := by
      simpa [hT] using hs
    -- Proof comment: before the clipped horizon, the stopped coefficient is still the raw
    -- translated partial derivative observed along the centered sample path.
    calc
      Hi s ω = (∂[i] F) (x + B s ω) := by
        exact
          stoppedCoordinatePartial_beforeExit_eq_theorem25_38
            (W := W) (x := x) (U := U) (F := F) (B := B) (ω := ω)
            hω i hs_exit
      _ = (∂[i] fun z : State ↦ F (x + z)) (B s ω) := by
            symm
            exact translatedPartialDeriv_eq_theorem25_38 (F := F) (hF := hF) x (B s ω) i
      _ =
          if (s : ENNReal) ≤ (T : ENNReal) then
            (∂[i] fun z : State ↦ F (x + z)) (B s ω)
          else
            0 := by
              simp [hs]
  · have hs_exit : hittingAfter W Uᶜ 0 ω < (s : ENNReal) := by
      have hs_not_exit : ¬ (s : ENNReal) ≤ hittingAfter W Uᶜ 0 ω := by
        simpa [hT] using hs
      exact lt_of_not_ge hs_not_exit
    -- Proof comment: once the sample time is strictly past the clipped horizon, both the stopped
    -- coefficient and its deterministic cutoff are already zero.
    calc
      Hi s ω = 0 := by
        exact
          stoppedCoordinatePartial_afterExit_eq_zero_theorem25_38
            (W := W) (U := U) (F := F) i hs_exit
      _ =
          if (s : ENNReal) ≤ (T : ENNReal) then
            (∂[i] fun z : State ↦ F (x + z)) (B s ω)
          else
            0 := by
              simp [hs]

/-- Helper for Theorem 25.38: at a fixed horizon `T`, the canonical Itô value depends only on
the samplewise coefficient values on `Set.Icc 0 T`. -/
private theorem continuousLocalMartingaleItoIntegralProcess_eq_of_eqOnIcc_theorem25_38
    {μ : Measure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M K L : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {T : NNReal} {ω : Ω}
    (hKL : Set.EqOn (fun s : NNReal ↦ K s ω) (fun s ↦ L s ω) (Set.Icc 0 T)) :
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM K T ω =
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM L T ω := by
  let X : C(NNReal, ℝ) := ⟨fun s ↦ M s ω, hM.continuous ω⟩
  have hRows :
      partitionPathwiseItoApproximationUpTo
          (fun s ↦ K s ω)
          X
          Definition2158.dyadicPartitionSequence
          T =
        partitionPathwiseItoApproximationUpTo
          (fun s ↦ L s ω)
          X
          Definition2158.dyadicPartitionSequence
          T := by
    funext row
    -- Proof comment: every dyadic left endpoint contributing to the fixed-horizon row lies in
    -- `Set.Icc 0 T`, so the intervalwise coefficient identity rewrites the whole row sequence.
    exact
      partitionPathwiseItoApproximationUpTo_congrOn_Icc
        (P := Definition2158.dyadicPartitionSequence)
        (X := X)
        (T := T)
        hKL
        row
  -- Proof comment: the canonical Itô value is defined as the `limUnder` of the dyadic rows, so
  -- equality of the row family pins down the same fixed-time value.
  rw [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess,
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess,
    pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
  exact congrArg (limUnder atTop) hRows

/-- Helper for Theorem 25.38: at the matching cutoff horizon `T`, cutting the coefficient off at
`T` does not change the canonical Itô value. -/
private theorem continuousLocalMartingaleItoIntegralProcess_eq_constCutoffValue_theorem25_38
    {μ : Measure Ω}
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal) (ω : Ω) :
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM
        (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T
        ω =
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hM H T ω := by
  -- Proof comment: on `Set.Icc 0 T`, the deterministic cutoff already agrees pointwise with the
  -- original coefficient.
  exact
    continuousLocalMartingaleItoIntegralProcess_eq_of_eqOnIcc_theorem25_38
      (μ := μ)
      (ℱ := ℱ)
      (M := M)
      (K := ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (L := H)
      (hM := hM)
      (T := T)
      (ω := ω)
      (by
        intro s hs
        simp [ProbabilityTheory.processBeforeStoppingTime_apply, hs.2])

/-- Helper for Theorem 25.38: on a good centered sample path, the theorem-local canonical
coordinate owner is exactly the corresponding pathwise Itô integral along that centered path. -/
private theorem canonicalCoordinate_apply_eq_stoppedCenteredPathwiseItoIntegral_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {U : Set State} {F : State → ℝ} {B : VectorProcess}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (ω : Ω)
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = W t ω - x)
    (i : Fin d) (t : NNReal) :
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        (hittingAfter W Uᶜ 0)
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
      pathwiseItoIntegralAlong
        (fun s : NNReal ↦ Hi s ω)
        (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) i)
        Definition2158.dyadicPartitionSequence
        t := by
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
  let hZi :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i).1
  let Hi : NNReal → Ω → ℝ :=
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_38
        (Ω := Ω) (W := W) (F := F) i)
      (hittingAfter W Uᶜ 0)
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hPath :
      (⟨fun s ↦ Zi s ω, hZi.continuous ω⟩ : C(NNReal, ℝ)) = vectorPathComponent Xω i := by
    ext s
    simpa [Zi, Xω, vectorPathComponent] using (congrArg (fun z : State ↦ z i) (hω s)).symm
  -- Proof comment: unfold the canonical stochastic Itô process once, then transport its driving
  -- path to the centered vector-path coordinate via the extracted path equality `hPath`.
  simp only [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess]
  simpa [Hi, Xω] using
    congrArg
      (fun X : C(NNReal, ℝ) ↦
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ Hi s ω)
          X
          Definition2158.dyadicPartitionSequence
          t)
      hPath

/-- Helper for Theorem 25.38: expanding the multidimensional dyadic Itô row shows that it is the
finite sum of the coordinate dyadic rows. -/
private theorem dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_38
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo F X T n =
      ∑ k : Fin d,
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ (∂[k] F) (X t))
          (vectorPathComponent X k)
          Definition2158.dyadicPartitionSequence
          T
          n := by
  -- Proof comment: unfolding the multidimensional dyadic row exposes a finite sum over partition
  -- cells and a finite sum over coordinates, which can be swapped directly.
  rw [dyadicMultidimensionalItoApproximationUpTo, Finset.sum_comm]
  simp [partitionPathwiseItoApproximationUpTo]

/-- Helper for Theorem 25.38: a truncated dyadic Itô row only depends on the coefficient values
at the sampled left endpoints that actually occur in that row. -/
private theorem partitionPathwiseItoApproximationUpTo_eq_of_leftEndpointEq_theorem25_38
    {K L : NNReal → ℝ} {X : C(NNReal, ℝ)}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {T : NNReal} {row : ℕ}
    (hKL : ∀ j : ℕ, j < partitionBoundIndex P row T → K (P row j) = L (P row j)) :
    partitionPathwiseItoApproximationUpTo K X P T row =
      partitionPathwiseItoApproximationUpTo L X P T row := by
  -- Proof comment: after unfolding the row, each summand is indexed by one sampled left
  -- endpoint `P row j`, so the hypothesis rewrites the finite sum termwise.
  rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hKL j (Finset.mem_range.mp hj)]

/-- Helper for Theorem 25.38: along any strict-mono family of partition rows, the predecessor
point converges to the target horizon because the mesh tends to zero. -/
private theorem partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_38
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hmesh
      (fun n ↦ bot_le)
      ?_
  intro n
  -- Proof comment: every predecessor point lies within one mesh width of `T`, so shrinking
  -- mesh forces the predecessor horizon to converge to `T`.
  simpa [edist_comm] using partitionPredecessorPointWithinMeshEarly P (φ n) T

/-- Helper for Theorem 25.38: a truncated dyadic Itô row is the predecessor-horizon row plus the
single boundary increment on its last active cell. -/
private theorem partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_38
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {T : NNReal} {n : ℕ} :
    partitionPathwiseItoApproximationUpTo H X P T n =
      partitionPathwiseItoApproximationUpTo H X P (partitionPredecessorPointEarly P n T) n +
        H (partitionPredecessorPointEarly P n T) *
          (X T - X (partitionPredecessorPointEarly P n T)) := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0 : T ≤ 0 := by
        simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
      exact le_antisymm hle0 bot_le
    -- Proof comment: when the truncation index is zero, both sums are empty and the boundary
    -- increment vanishes because the horizon is already `0`.
    subst hT0
    simp [partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hpred : partitionPredecessorPointEarly P n T = P n k := by
      -- Proof comment: once the truncation index is positive, the predecessor point is the last
      -- active left endpoint in that row.
      simp [partitionPredecessorPointEarly, hk]
    have hpredIdx :
        partitionBoundIndex P n (partitionPredecessorPointEarly P n T) = k := by
      -- Proof comment: the predecessor horizon is itself the partition point `P n k`.
      rw [hpred, partitionBoundIndex_eq_of_partitionPoint]
    have hnext :
        partitionNextPointUpTo P n k T = T := by
      -- Proof comment: at the last contributing index, the clipped successor hits the target
      -- horizon exactly.
      rw [partitionNextPointUpTo, min_eq_right]
      simpa [hk] using le_partitionBoundIndex_time P n T
    have hprefix :
        ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x T) - X (P n x)) =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_ltT : j + 1 < partitionBoundIndex P n T := by
        simpa [hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
      have hnextT : partitionNextPointUpTo P n j T = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) T hj_ltT)
      have hnextPred : partitionNextPointUpTo P n j (P n k) = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact
          ((IsAdmissiblePartitionSequence.strictMono (P := P) n).monotone)
            (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      rw [hnextT, hnextPred]
    calc
      partitionPathwiseItoApproximationUpTo H X P T n =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x T) - X (P n x)) +
              H (P n k) * (X T - X (P n k)) := by
            rw [partitionPathwiseItoApproximationUpTo, hk, Finset.sum_range_succ, hnext]
      _ =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) +
              H (P n k) * (X T - X (P n k)) := by
            rw [hprefix]
      _ =
          partitionPathwiseItoApproximationUpTo H X P (partitionPredecessorPointEarly P n T) n +
            H (partitionPredecessorPointEarly P n T) *
              (X T - X (partitionPredecessorPointEarly P n T)) := by
            rw [partitionPathwiseItoApproximationUpTo, hpredIdx, hpred]
            simp

/-- Helper for Theorem 25.38: if two horizons lie in the same partition cell, then the raw
pathwise row sums differ only by the final boundary increment between those two times. -/
private theorem partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary_raw_theorem25_38
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {S T : NNReal} {n : ℕ} (hST : S ≤ T)
    (hSame : partitionBoundIndex P n S = partitionBoundIndex P n T) :
    partitionPathwiseItoApproximationUpTo H X P T n =
      partitionPathwiseItoApproximationUpTo H X P S n +
        H (partitionPredecessorPointEarly P n T) * (X T - X S) := by
  by_cases hidx : partitionBoundIndex P n T = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0 : T ≤ 0 := by
        simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
      exact le_antisymm hle0 bot_le
    have hS0 : S = 0 := by
      exact le_antisymm (le_trans hST (by simpa [hT0])) bot_le
    -- Proof comment: when the common truncation index is `0`, both horizons are already `0`,
    -- so both finite sums and the boundary increment vanish.
    subst hT0
    subst hS0
    simp [partitionPathwiseItoApproximationUpTo, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hidx
    let pred := partitionPredecessorPointEarly P n T
    have hidxS : partitionBoundIndex P n S = k + 1 := by
      rw [hSame, hk]
    have hpredEq : partitionPredecessorPointEarly P n S = pred := by
      -- Proof comment: same-cell horizons have the same predecessor endpoint on the chosen row.
      simp [pred, partitionPredecessorPointEarly, hk, hidxS]
    have hTpred :
        partitionPathwiseItoApproximationUpTo H X P T n =
          partitionPathwiseItoApproximationUpTo H X P pred n +
            H pred * (X T - X pred) := by
      -- Proof comment: the later horizon `T` differs from its predecessor row by one boundary
      -- increment on the final active cell.
      simpa [pred] using
        partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_38
          H X P (T := T) (n := n)
    have hSpred :
        partitionPathwiseItoApproximationUpTo H X P S n =
          partitionPathwiseItoApproximationUpTo H X P pred n +
            H pred * (X S - X pred) := by
      -- Proof comment: the earlier same-cell horizon `S` has exactly the same predecessor row.
      simpa [pred, hpredEq] using
        partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_38
          H X P (T := S) (n := n)
    have hPrefix :
        partitionPathwiseItoApproximationUpTo H X P pred n =
          partitionPathwiseItoApproximationUpTo H X P S n -
            H pred * (X S - X pred) := by
      linarith [hSpred]
    -- Proof comment: subtracting the shared predecessor-row decomposition leaves only the last
    -- boundary increment from `S` to `T`.
    calc
      partitionPathwiseItoApproximationUpTo H X P T n =
          partitionPathwiseItoApproximationUpTo H X P pred n +
            H pred * (X T - X pred) := hTpred
      _ =
          (partitionPathwiseItoApproximationUpTo H X P S n -
              H pred * (X S - X pred)) +
            H pred * (X T - X pred) := by
              rw [hPrefix]
      _ =
          partitionPathwiseItoApproximationUpTo H X P S n +
            H pred * (X T - X S) := by
              ring

/-- Helper for Theorem 25.38: in the non-partition branch, the clipped-successor raw row and the
raw row at the clipped horizon lie in the same dyadic cell, so they differ by exactly one
predecessor-side boundary increment. -/
private theorem rawRow_firstPastExit_nonPartition_eq_clipped_plus_boundary_theorem25_38
    (H : NNReal → ℝ) (X : C(NNReal, ℝ)) {S T : NNReal} {n : ℕ}
    (hST : S ≤ T)
    (hSame :
      partitionBoundIndex Definition2158.dyadicPartitionSequence n S =
        partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    partitionPathwiseItoApproximationUpTo
        H
        X
        Definition2158.dyadicPartitionSequence
        T
        n =
      partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          S
          n +
        H (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T) *
          (X T - X S) := by
  -- Proof comment: the non-partition branch is exactly the dyadic same-cell raw-row identity.
  simpa using
    partitionPathwiseItoApproximationUpTo_eq_sameCell_add_boundary_raw_theorem25_38
      H X Definition2158.dyadicPartitionSequence hST hSame

/-- Helper for Theorem 25.38: once every sampled left endpoint in a tail lies strictly after the
exit horizon, the stopped coordinate coefficient kills that entire tail sum. -/
private theorem stoppedCoordinateRowTail_eq_zero_afterTime_theorem25_38
    {W : VectorProcess} {U : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {ω : Ω} {T t : NNReal} {row first : ℕ}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hAfter : T < P row first) :
    ∑ j in Finset.Ico first (partitionBoundIndex P row t),
      ProbabilityTheory.processBeforeStoppingTime
          (coordinatePartialDerivProcess_theorem25_38
            (Ω := Ω) (W := W) (F := F) i)
          (hittingAfter W Uᶜ 0)
          (P row j)
          ω *
        (X (partitionNextPointUpTo P row j t) - X (P row j)) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hj_ge : first ≤ j := (Finset.mem_Ico.mp hj).1
  have hleft_le :
      P row first ≤ P row j :=
    (instStrictMono_of_isAdmissiblePartitionSequence (P := P) row).monotone hj_ge
  have hAfter_j : T < P row j := lt_of_lt_of_le hAfter hleft_le
  have hCoeff :
      ProbabilityTheory.processBeforeStoppingTime
          (coordinatePartialDerivProcess_theorem25_38
            (Ω := Ω) (W := W) (F := F) i)
          (hittingAfter W Uᶜ 0)
          (P row j)
          ω =
        0 := by
    have hExit :
        hittingAfter W Uᶜ 0 ω < ((P row j : NNReal) : ENNReal) := by
      rw [← hT]
      exact_mod_cast hAfter_j
    -- Proof comment: every sampled time in the tail lies strictly after the exit horizon, so the
    -- stopped coordinate integrand vanishes pointwise there.
    exact
      stoppedCoordinatePartial_afterExit_eq_zero_theorem25_38
        (W := W) (U := U) (F := F) i hExit
  -- Proof comment: after the pointwise coefficient rewrite, each tail summand is literally zero.
  simp [hCoeff]

/-- Helper for Theorem 25.38: in the partition-point branch, advancing one same-row clipped
successor adds exactly the single increment sampled at that partition point. -/
private theorem rawRow_firstPastExit_partitionPoint_eq_clipped_plus_boundary_theorem25_38
    (H : NNReal → ℝ) (X : C(NNReal, ℝ)) {t T : NNReal} {n m : ℕ}
    (hT : T = Definition2158.dyadicPartitionSequence n m)
    (hm : m < partitionBoundIndex Definition2158.dyadicPartitionSequence n t) :
    partitionPathwiseItoApproximationUpTo
        H
        X
        Definition2158.dyadicPartitionSequence
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
        n =
      partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          T
          n +
        H T *
          (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) - X T) := by
  have hStep :
      partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
          n -
        partitionPathwiseItoApproximationUpTo
          H
          X
          Definition2158.dyadicPartitionSequence
          T
          n =
      H T *
        (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) - X T) := by
    -- Proof comment: the imported same-row theorem already computes the one-step row increment;
    -- rewriting the partition point as `T` puts it in the horizon spelling used here.
    simpa [hT] using
      partitionPathwiseItoApproximationUpTo_nextPoint_sub_sameRow H X t n m hm
  -- Proof comment: rearrange the one-step increment identity into the forward row-equality form
  -- needed in the clipped-successor branch.
  linarith [hStep]

/-- Helper for Theorem 25.38: when two clipped horizons lie in the same dyadic cell, the
multidimensional row differs only by the summed predecessor-side boundary increment. -/
private theorem dyadicMultidimensionalItoApproximationUpTo_sameCell_add_boundary_theorem25_38
    (F : State → ℝ) (X : VectorPathSpace d) {S T : NNReal} {n : ℕ}
    (hST : S ≤ T)
    (hSame :
      partitionBoundIndex Definition2158.dyadicPartitionSequence n S =
        partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    dyadicMultidimensionalItoApproximationUpTo F X T n =
      dyadicMultidimensionalItoApproximationUpTo F X S n +
        ∑ i : Fin d,
          (∂[i] F)
            (X (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T)) *
            (vectorPathComponent X i T -
              vectorPathComponent X i S) := by
  have hCoord :
      ∀ i : Fin d,
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            T
            n
          =
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            S
            n +
          (∂[i] F)
            (X (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T)) *
            (vectorPathComponent X i T -
              vectorPathComponent X i S) := by
    intro i
    -- Proof comment: apply the scalar same-cell boundary decomposition to each coordinate row
    -- and keep the common predecessor horizon in the multidimensional spelling.
    simpa using
      rawRow_firstPastExit_nonPartition_eq_clipped_plus_boundary_theorem25_38
        (H := fun s : NNReal ↦ (∂[i] F) (X s))
        (X := vectorPathComponent X i)
        hST
        hSame
  calc
    dyadicMultidimensionalItoApproximationUpTo F X T n =
        ∑ i : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            T
            n := by
          rw [dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_38]
    _ =
        ∑ i : Fin d,
          (partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F) (X s))
              (vectorPathComponent X i)
              Definition2158.dyadicPartitionSequence
              S
              n +
            (∂[i] F)
              (X (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T)) *
              (vectorPathComponent X i T -
                vectorPathComponent X i S)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hCoord i
    _ =
        (∑ i : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            S
            n) +
          ∑ i : Fin d,
            (∂[i] F)
              (X (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T)) *
              (vectorPathComponent X i T -
                vectorPathComponent X i S) := by
          rw [Finset.sum_add_distrib]
    _ =
        dyadicMultidimensionalItoApproximationUpTo F X S n +
          ∑ i : Fin d,
            (∂[i] F)
              (X (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T)) *
              (vectorPathComponent X i T -
                vectorPathComponent X i S) := by
          rw [dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_38]

/-- Helper for Theorem 25.38: when the clipped horizon is itself a dyadic partition point, the
next clipped multidimensional row differs only by the summed one-step boundary increment. -/
private theorem
    dyadicMultidimensionalItoApproximationUpTo_partitionPoint_eq_clipped_plus_boundary_theorem25_38
    (F : State → ℝ) (X : VectorPathSpace d) {t T : NNReal} {n m : ℕ}
    (hT : T = Definition2158.dyadicPartitionSequence n m)
    (hm : m < partitionBoundIndex Definition2158.dyadicPartitionSequence n t) :
    dyadicMultidimensionalItoApproximationUpTo
        F
        X
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
        n =
      dyadicMultidimensionalItoApproximationUpTo F X T n +
        ∑ i : Fin d,
          (∂[i] F) (X T) *
            (vectorPathComponent X i
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) -
              vectorPathComponent X i T) := by
  have hCoord :
      ∀ i : Fin d,
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
            n
          =
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            T
            n +
          (∂[i] F) (X T) *
            (vectorPathComponent X i
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) -
              vectorPathComponent X i T) := by
    intro i
    -- Proof comment: the scalar partition-point bridge already computes the unique extra
    -- increment picked up by moving from `T` to the clipped successor horizon.
    simpa [hT] using
      rawRow_firstPastExit_partitionPoint_eq_clipped_plus_boundary_theorem25_38
        (H := fun s : NNReal ↦ (∂[i] F) (X s))
        (X := vectorPathComponent X i)
        (t := t)
        (n := n)
        (m := m)
        hT
        hm
  calc
    dyadicMultidimensionalItoApproximationUpTo
        F
        X
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
        n =
        ∑ i : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
            n := by
          rw [dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_38]
    _ =
        ∑ i : Fin d,
          (partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F) (X s))
              (vectorPathComponent X i)
              Definition2158.dyadicPartitionSequence
              T
              n +
            (∂[i] F) (X T) *
              (vectorPathComponent X i
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) -
                vectorPathComponent X i T)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hCoord i
    _ =
        (∑ i : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (X s))
            (vectorPathComponent X i)
            Definition2158.dyadicPartitionSequence
            T
            n) +
          ∑ i : Fin d,
            (∂[i] F) (X T) *
              (vectorPathComponent X i
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) -
                vectorPathComponent X i T) := by
          rw [Finset.sum_add_distrib]
    _ =
        dyadicMultidimensionalItoApproximationUpTo F X T n +
          ∑ i : Fin d,
            (∂[i] F) (X T) *
              (vectorPathComponent X i
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) -
                vectorPathComponent X i T) := by
          rw [dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_38]

/-- Helper for Theorem 25.38: the single boundary increment from the predecessor-point
decomposition vanishes along any strict-mono subsequence when both the coefficient and path are
continuous. -/
private theorem partitionItoBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_38
    (H : NNReal → ℝ) (hH : Continuous H) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto
      (fun n ↦
        H (partitionPredecessorPointEarly P (φ n) T) *
          (X T - X (partitionPredecessorPointEarly P (φ n) T)))
      atTop
      (𝓝 0) := by
  have hpred :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P (φ n) T) atTop (𝓝 T) :=
    partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_38 P hφ T
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 (H T)) :=
    hH.continuousAt.tendsto.comp hpred
  have hPath :
      Tendsto
        (fun n ↦ X (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 (X T)) :=
    X.continuous.continuousAt.tendsto.comp hpred
  have hIncrement :
      Tendsto
        (fun n ↦ X T - X (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
      tendsto_const_nhds
    have hSub :
        Tendsto
          (fun n ↦ X T - X (partitionPredecessorPointEarly P (φ n) T))
          atTop
          (𝓝 (X T - X T)) :=
      hConst.sub hPath
    simpa using hSub
  -- Proof comment: the coefficient converges to its target value while the boundary increment
  -- itself converges to zero, so the product vanishes.
  simpa using hCoeff.mul hIncrement

/-- Helper for Theorem 25.38: the first clipped successor after the predecessor cell still
converges to the target horizon along any strict-mono family of rows. -/
private theorem partitionBoundarySuccessor_tendsto_alongStrictMonoRows_theorem25_38
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto
      (fun n ↦
        partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T)
      atTop
      (𝓝 T) := by
  by_cases hT0 : T = 0
  · subst hT0
    have hzero :
        (fun n ↦
          partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) 0 - 1) 0) =
          fun _ : ℕ ↦ 0 := by
      funext n
      simp [partitionNextPointUpTo, partitionBoundIndex_zero,
        IsAdmissiblePartitionSequence.zero_eq (P := P) (φ n)]
    rw [hzero]
    exact tendsto_const_nhds
  · have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
      hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
    rw [tendsto_iff_edist_tendsto_0]
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by simpa using hmesh.add hmesh)
        (fun n ↦ bot_le)
        ?_
    intro n
    let row := φ n
    have hidx_ne_zero : partitionBoundIndex P row T ≠ 0 := by
      intro hzero
      have hT_le_zero : T ≤ 0 := by
        have hle : T ≤ P row 0 := by
          simpa [hzero] using le_partitionBoundIndex_time P row T
        simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) row] using hle
      exact (not_lt_of_ge hT_le_zero) (bot_lt_iff_ne_bot.mpr hT0)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P row T = k + 1 :=
      ⟨partitionBoundIndex P row T - 1, (Nat.sub_add_cancel (Nat.pos_of_ne_zero hidx_ne_zero)).symm⟩
    have hpred :
        partitionPredecessorPointEarly P row T = P row k := by
      -- Proof comment: for positive truncation index, the predecessor point is the last active
      -- left endpoint of the row.
      simp [partitionPredecessorPointEarly, hk]
    have hsucc :
        partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T =
          partitionNextPointUpTo P row k T := by
      simp [hk]
    have hk_lt : k < partitionBoundIndex P row T := by
      simpa [hk] using Nat.lt_succ_self k
    have hsucc_mesh :
        edist
            (partitionPredecessorPointEarly P row T)
            (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T)
          ≤ partitionMesh P row := by
      -- Proof comment: the clipped successor of the predecessor cell lies within one mesh width
      -- of that predecessor endpoint.
      rw [hpred, hsucc]
      simpa using
        edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh P row k T hk_lt
    have hpred_mesh :
        edist (partitionPredecessorPointEarly P row T) T ≤ partitionMesh P row :=
      partitionPredecessorPointWithinMeshEarly P row T
    calc
      edist
          (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T)
          T
        ≤ edist
            (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) T)
            (partitionPredecessorPointEarly P row T) +
          edist (partitionPredecessorPointEarly P row T) T := by
            exact edist_triangle _ _ _
      _ ≤ partitionMesh P row + partitionMesh P row := by
            exact add_le_add (by simpa [edist_comm] using hsucc_mesh) hpred_mesh

/-- Helper for Theorem 25.38: the boundary increment from the predecessor cell to its clipped
successor also vanishes along any strict-mono family of rows. -/
private theorem partitionItoSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_38
    (H : NNReal → ℝ) (hH : Continuous H) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T : NNReal) :
    Tendsto
      (fun n ↦
        H (partitionPredecessorPointEarly P (φ n) T) *
          (X (partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T) - X T))
      atTop
      (𝓝 0) := by
  have hCoeff :
      Tendsto
        (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T))
        atTop
        (𝓝 (H T)) := by
    -- Proof comment: the coefficient is still sampled at the predecessor points converging to
    -- the target horizon.
    exact
      hH.continuousAt.tendsto.comp
        (partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_38 P hφ T)
  have hSucc :
      Tendsto
        (fun n ↦ X (partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T))
        atTop
        (𝓝 (X T)) :=
    X.continuous.continuousAt.tendsto.comp
      (partitionBoundarySuccessor_tendsto_alongStrictMonoRows_theorem25_38 P hφ T)
  have hIncrement :
      Tendsto
        (fun n ↦
          X (partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) T) - X T)
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
      tendsto_const_nhds
    -- Proof comment: continuity of the path at the clipped successor times forces the successor
    -- boundary increment to vanish.
    simpa using hSucc.sub hConst
  -- Proof comment: the predecessor coefficient stays bounded near its limit while the successor
  -- side boundary increment itself vanishes, so the product goes to `0`.
  simpa using hCoeff.mul hIncrement

/-- Helper for Theorem 25.38: if the sampled left endpoint is exactly the target horizon on each
row, then the next clipped successor along those rows still converges back to that same horizon as
the mesh tends to zero. -/
private theorem partitionExactSuccessor_tendsto_alongStrictMonoRows_theorem25_38
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ κ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hκ : ∀ n : ℕ, T = P (φ n) (κ n))
    (hκ_lt : ∀ n : ℕ, κ n < partitionBoundIndex P (φ n) t) :
    Tendsto
      (fun n ↦ partitionNextPointUpTo P (φ n) (κ n) t)
      atTop
      (𝓝 T) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hmesh
      (fun n ↦ bot_le)
      ?_
  intro n
  have hstep :
      edist
          (P (φ n) (κ n))
          (partitionNextPointUpTo P (φ n) (κ n) t)
        ≤ partitionMesh P (φ n) :=
    edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh
      P
      (φ n)
      (κ n)
      t
      (hκ_lt n)
  calc
    edist (partitionNextPointUpTo P (φ n) (κ n) t) T
      = edist (partitionNextPointUpTo P (φ n) (κ n) t) (P (φ n) (κ n)) := by
          rw [hκ n]
    _ = edist (P (φ n) (κ n)) (partitionNextPointUpTo P (φ n) (κ n) t) := by
          rw [edist_comm]
    _ ≤ partitionMesh P (φ n) := hstep

/-- Helper for Theorem 25.38: when the target horizon is itself a sampled partition point on each
row, the corresponding one-step exact-successor boundary increment still vanishes along any
strict-mono family of rows. -/
private theorem partitionItoExactSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_38
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ κ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hκ : ∀ n : ℕ, T = P (φ n) (κ n))
    (hκ_lt : ∀ n : ℕ, κ n < partitionBoundIndex P (φ n) t) :
    Tendsto
      (fun n ↦
        H T *
          (X (partitionNextPointUpTo P (φ n) (κ n) t) - X T))
      atTop
      (𝓝 0) := by
  have hSucc :
      Tendsto
        (fun n ↦ X (partitionNextPointUpTo P (φ n) (κ n) t))
        atTop
        (𝓝 (X T)) :=
    X.continuous.continuousAt.tendsto.comp
      (partitionExactSuccessor_tendsto_alongStrictMonoRows_theorem25_38
        P
        hφ
        hκ
        hκ_lt)
  have hIncrement :
      Tendsto
        (fun n ↦ X (partitionNextPointUpTo P (φ n) (κ n) t) - X T)
        atTop
        (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
      tendsto_const_nhds
    -- Proof comment: continuity of the path at the exact partition-point horizon forces the
    -- one-step successor increment itself to vanish.
    simpa using hSucc.sub hConst
  -- Proof comment: here the coefficient is frozen at the exact partition point `T`, so only the
  -- vanishing successor increment remains asymptotically.
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ H T) atTop (𝓝 (H T))).mul hIncrement

/-- Helper for Theorem 25.38: if each coordinate dyadic row converges to a chosen realization,
then the `limUnder` of their finite sum is the sum of those coordinate limits. -/
private lemma limUnder_finset_sum_eq_of_tendsto_theorem25_38
    {ι : Type _} (s : Finset ι) {f : ι → ℕ → ℝ} {L : ι → ℝ}
    (h : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (L i))) :
    limUnder atTop (fun row ↦ Finset.sum s fun i ↦ f i row) = Finset.sum s L := by
  -- Proof comment: finite sums preserve convergence, so the canonical `limUnder` value of the
  -- row sum is the sum of the pointwise limits.
  simpa using (tendsto_finset_sum s fun i hi ↦ h i hi).limUnder_eq

/-- Helper for Theorem 25.38: once a fixed-horizon dyadic Itô row has any genuine limit, that
limit is automatically the canonical `pathwiseItoIntegralAlong` value. -/
private theorem partitionPathwiseItoApproximationUpTo_tendsto_canonical_of_exists_limit_theorem25_38
    {H : NNReal → ℝ} {X : C(NNReal, ℝ)} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P]
    (T : NNReal)
    (hExist :
      ∃ L : ℝ,
        Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (𝓝 L)) :
    Tendsto
      (partitionPathwiseItoApproximationUpTo H X P T)
      atTop
      (𝓝 (pathwiseItoIntegralAlong H X P T)) := by
  rcases hExist with ⟨L, hL⟩
  have hCanonical : pathwiseItoIntegralAlong H X P T = L :=
    pathwiseItoIntegralAlong_eq_of_tendsto T hL
  -- Proof comment: identify the canonical `limUnder` owner with the explicit limit `L`, then
  -- reuse the already established convergence to `L`.
  simpa [hCanonical] using hL

/-- Helper for Theorem 25.38: the raw translated coordinate coefficient is progressively
measurable in the natural filtration of the underlying Brownian vector. -/
private theorem rawCoordinatePartialDerivProgMeasurableNatural_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) :
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (W t ω - x)
    ProgMeasurable ℱW Hi := by
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (W t ω - x)
  have hHi_strong : StronglyAdapted ℱW Hi := by
    intro t
    -- Proof comment: each deterministic-time slice is the continuous observable
    -- `z ↦ ∂[i]F(z - x)` applied to the Brownian state at time `t`.
    exact
      stateComposition_stronglyAdapted_natural
        (W := W)
        (hWsm := brownianVectorStartedAt_stronglyMeasurable hW)
        (hFmeas := ((continuousPartialDeriv_theorem25_38 F hFcontDiff i).comp
          (continuous_id.sub continuous_const)).measurable)
        t
  have hHi_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Hi t ω := by
    intro ω
    -- Proof comment: along each sample path, the raw translated coefficient is a continuous
    -- partial derivative observed on the centered Brownian path `W_t(ω) - x`.
    simpa [Hi] using
      ((continuousPartialDeriv_theorem25_38 F hFcontDiff i).comp
        ((hWcont ω).sub continuous_const))
  -- Proof comment: strong adaptation plus pathwise continuity gives progressive measurability in
  -- the natural filtration.
  exact hHi_strong.progMeasurable_of_continuous hHi_cont

/-- Helper for Theorem 25.38: the raw translated coordinate coefficient satisfies the finite
bracket-energy hypothesis needed for the Chapter 25.22 subsequence machinery. -/
private theorem rawCoordinatePartialDerivHasFiniteBracketEnergy_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) :
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    let hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi :=
      centeredCoordinate_hasAbsolutelyContinuousSquareVariation_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i
    let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (W t ω - x)
    ProbabilityTheory.HasFiniteBracketEnergy hbr Hi := by
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
  let hZi :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i).1
  let hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi :=
    centeredCoordinate_hasAbsolutelyContinuousSquareVariation_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i
  let Hi : NNReal → Ω → ℝ := fun t ω ↦ (∂[i] F) (W t ω - x)
  have hHi_prog : ProgMeasurable ℱW Hi := by
    -- Proof comment: the previous lemma already packages progressive measurability of the raw
    -- translated coefficient.
    simpa [ℱW, Hi] using
      rawCoordinatePartialDerivProgMeasurableNatural_theorem25_38
        (μ := μ) (W := W) (x := x) (F := F)
        hW hWcont hFcontDiff i
  have hHi_sq :
      ∀ T : NNReal, ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (Hi s.toNNReal ω) ^ 2 * (hbr.density s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)) := by
    intro T
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hRealCont : Continuous fun s : ℝ ↦ Hi s.toNNReal ω := by
      -- Proof comment: composing the raw translated coefficient with `Real.toNNReal` keeps the
      -- samplewise continuity needed for compact-interval square integrability.
      simpa [Hi] using
        ((continuousPartialDeriv_theorem25_38 F hFcontDiff i).comp
          (((hWcont ω).sub continuous_const).comp continuous_real_toNNReal))
    have hSq :
        IntegrableOn
          (fun s : ℝ ↦ (Hi s.toNNReal ω) ^ 2)
          (Set.Icc (0 : ℝ) (T : ℝ)) := by
      simpa using (hRealCont.pow 2).integrableOn_Icc
    refine hSq.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hDensity : (hbr.density s.toNNReal ω : ℝ) = 1 := by
      simp [hbr]
    rw [hDensity, mul_one]
  -- Proof comment: with unit bracket density, compact-interval square integrability of the raw
  -- translated coefficient is exactly the Chapter 25.22 finite-energy condition.
  simpa [ProbabilityTheory.HasFiniteBracketEnergy] using
    Theorem25_22.brownianRepresentationItoIntegrand_hasFiniteBracketEnergy
      (ℱ := ℱW)
      (μ := (μ : Measure Ω))
      hbr
      hHi_prog
      hHi_sq

/-- Helper for Theorem 25.38: for the raw translated coordinate coefficient, the canonical
stochastic Itô owner agrees with the pathwise dyadic owner along the centered sample path. -/
private theorem canonicalRawCoordinate_apply_eq_centeredPathwiseItoIntegral_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {F : State → ℝ} {B : VectorProcess}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (ω : Ω)
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = W t ω - x)
    (i : Fin d) (t : NNReal) :
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    let Hi : NNReal → Ω → ℝ := fun s ξ ↦ (∂[i] F) (W s ξ - x)
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
      pathwiseItoIntegralAlong
        (fun s : NNReal ↦ Hi s ω)
        (vectorPathComponent (⟨fun s ↦ B s ω, hcontω⟩ : VectorPathSpace d) i)
        Definition2158.dyadicPartitionSequence
        t := by
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
  let hZi :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i).1
  let Hi : NNReal → Ω → ℝ := fun s ξ ↦ (∂[i] F) (W s ξ - x)
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hPath :
      (⟨fun s ↦ Zi s ω, hZi.continuous ω⟩ : C(NNReal, ℝ)) = vectorPathComponent Xω i := by
    ext s
    simpa [Zi, Xω, vectorPathComponent] using (congrArg (fun z : State ↦ z i) (hω s)).symm
  -- Proof comment: unfold the canonical stochastic owner once, then transport its driving path
  -- to the centered sample-path coordinate via the exact path identity `hPath`.
  simp only [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess]
  simpa [Hi, Xω] using
    congrArg
      (fun X : C(NNReal, ℝ) ↦
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ Hi s ω)
          X
          Definition2158.dyadicPartitionSequence
          t)
      hPath

/-- Helper for Theorem 25.38: any explicit pathwise witness for the raw centered coordinate
integral immediately yields convergence of the clipped dyadic rows to the canonical
`pathwiseItoIntegralAlong` value. -/
private theorem rawClippedCoordinateRows_tendsto_of_hasPathwiseWitness_theorem25_38
    {B : VectorProcess} {F : State → ℝ}
    {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (i : Fin d) (T : NNReal)
    (hIto :
      let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
      ∃ I : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          I) :
    let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T
          n)
      atTop
      (𝓝
        (pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T)) := by
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  rcases hIto with ⟨I, hI⟩
  -- Proof comment: once a genuine pathwise Itô realization is available, its defining
  -- convergence statement is exactly the target, and the canonical `pathwiseItoIntegralAlong`
  -- value is recovered by the owner equality.
  simpa [Xω, hI.eq_pathwiseItoIntegralAlong] using hI.tendsto T

/-- Helper for Theorem 25.38: on the raw centered Brownian sample path, the scalar centered
coordinate path is exactly the corresponding coordinate projection of the centered vector path. -/
private theorem rawCenteredCoordinatePath_eq_vectorPathComponent_theorem25_38
    {W : VectorProcess} {x : State} {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ W t ω - x)
    (i : Fin d) :
    (⟨fun s ↦ W s ω i - x i, ((continuous_apply i).comp hcontω)⟩ : C(NNReal, ℝ)) =
      vectorPathComponent (⟨fun s ↦ W s ω - x, hcontω⟩ : VectorPathSpace d) i := by
  -- Proof comment: evaluating the centered vector path in coordinate `i` literally recovers the
  -- centered scalar coordinate process.
  ext s
  simp [vectorPathComponent]

/-- Helper for Theorem 25.38: after reindexing any strict-mono dyadic row family, the Chapter
25.2.1 subsequence theorem still yields a further strict-mono refinement whose raw centered
coordinate rows converge almost surely to the canonical stochastic coordinate owner. -/
private theorem existsCenteredCoordinateRefinementSubsequence_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hF : ContDiff ℝ 2 F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (i : Fin d) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ T : NNReal,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F) (W s ω - x))
              (⟨fun s ↦ W s ω i - x i,
                ((continuous_apply i).comp ((hWcont ω).sub continuous_const))⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              (φ (ψ n)))
          atTop
          (𝓝
            (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
              ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
                (μ := μ) (W := W) (x := x) hW hWcont i).1)
              (fun s ξ ↦ (∂[i] F) (W s ξ - x))
              T
              ω)) := by
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
  let hZi :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
    (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i).1
  let hbr : ProbabilityTheory.HasAbsolutelyContinuousSquareVariation Zi hZi :=
    centeredCoordinate_hasAbsolutelyContinuousSquareVariation_natural_theorem25_38
      (μ := μ) (W := W) (x := x) hW hWcont i
  let Hi : NNReal → Ω → ℝ := fun s ξ ↦ (∂[i] F) (W s ξ - x)
  have hHi_prog : ProgMeasurable ℱW Hi := by
    -- Proof comment: the earlier natural-filtration measurability lemma packages the coefficient
    -- owner required by the Chapter 25.2.1 subsequence theorem.
    simpa [ℱW, Hi] using
      rawCoordinatePartialDerivProgMeasurableNatural_theorem25_38
        (μ := μ) (W := W) (x := x) (F := F) hW hWcont hF i
  have hHi_cont : ∀ ω : Ω, Continuous fun s : NNReal ↦ Hi s ω := by
    intro ω
    -- Proof comment: along each sample path, the raw translated partial derivative is a
    -- continuous observable of the centered Brownian path.
    simpa [Hi] using
      ((continuousPartialDeriv_theorem25_38 F hF i).comp
        ((hWcont ω).sub continuous_const))
  have hFiniteEnergy : ProbabilityTheory.HasFiniteBracketEnergy hbr Hi := by
    -- Proof comment: the centered Brownian coordinate has unit bracket density, so the previous
    -- finite-energy lemma applies without any further normalization.
    simpa [ℱW, Zi, hZi, hbr, Hi] using
      rawCoordinatePartialDerivHasFiniteBracketEnergy_theorem25_38
        (μ := μ) (W := W) (x := x) (F := F) hW hWcont hF i
  let Pφ : ℕ → ℕ → NNReal := fun n k ↦ Definition2158.dyadicPartitionSequence (φ n) k
  letI : IsAdmissiblePartitionSequence Pφ :=
    isAdmissiblePartitionSequence_comp (P := Definition2158.dyadicPartitionSequence) hφ
  obtain ⟨ψ, hψ, hψae⟩ :=
    ProbabilityTheory.exists_partitionSubsequence_with_ae_pathwise_itoApproximation
      (μ := (μ : Measure Ω)) (ℱ := ℱW) (M := Zi) (H := Hi)
      hZi hbr hHi_prog hHi_cont hFiniteEnergy Pφ
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψae] with ω hω T
  -- Proof comment: unfolding the reindexed partition sequence shows that the refined `Pφ`-rows
  -- are exactly the original dyadic rows along the composite selector `φ ∘ ψ`.
  simpa [Pφ, Hi, Zi, Function.comp] using hω T

/-- Helper for Theorem 25.38: after any strict-mono reindexing, the zero-patched centered
Brownian coordinate rows admit a further strict-mono refinement that converges almost surely to
the canonical pathwise dyadic owner. -/
private theorem centeredCoordinateRefinementSubsequence_ae_tendsto_pathwise_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hF : ContDiff ℝ 2 F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (i : Fin d) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T
                  (φ (ψ n)))
              atTop
              (𝓝
                (pathwiseItoIntegralAlong
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T)) := by
  intro B
  obtain ⟨ψ, hψ, hψae⟩ :=
    existsCenteredCoordinateRefinementSubsequence_theorem25_38
      (μ := μ) (W := W) (x := x) (F := F) hW hWcont hF hφ i
  have hGood :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          Xω ∈ (𝒞_qv^d) ∧
            ∀ i j : Fin d,
              HasQuadraticCovariationAlong
                (vectorPathComponent Xω i)
                (vectorPathComponent Xω j)
                (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      zeroPatchedCenteredGoodPath_ae_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont
  have hEqAe :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = W t ω - x := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_38
        (μ := μ) (W := W) (x := x) hW
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hGood, hEqAe, hψae] with ω hGoodω hω hSubseq
  rcases hGoodω with ⟨hcontω, hGoodω⟩
  refine ⟨hcontω, ?_⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  intro T
  have hPath :
      (⟨fun s ↦ W s ω i - x i,
        ((continuous_apply i).comp ((hWcont ω).sub continuous_const))⟩ : C(NNReal, ℝ)) =
        vectorPathComponent Xω i := by
    -- Proof comment: the centered scalar coordinate path is exactly the `i`-th coordinate of
    -- the centered vector path `Xω`.
    ext s
    simpa [Xω, vectorPathComponent] using congrArg (fun z : State ↦ z i) (hω s)
  have hCoeff :
      (fun s : NNReal ↦ (∂[i] F) (W s ω - x)) =
        fun s : NNReal ↦ (∂[i] F) (Xω s) := by
    -- Proof comment: the pointwise identity `B s ω = W s ω - x` rewrites the raw translated
    -- coefficient into the theorem-local centered path spelling.
    funext s
    simpa [Xω] using congrArg (fun z : State ↦ (∂[i] F) z) (hω s).symm
  have hRows :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F) (W s ω - x))
          (⟨fun s ↦ W s ω i - x i,
            ((continuous_apply i).comp ((hWcont ω).sub continuous_const))⟩ : C(NNReal, ℝ))
          Definition2158.dyadicPartitionSequence
          T
          (φ (ψ n))) =
        fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T
            (φ (ψ n)) := by
    -- Proof comment: after rewriting the coefficient and the driving scalar path, the refined
    -- dyadic rows are literally the theorem-local centered rows.
    funext n
    rw [hPath, hCoeff]
  have hLimit :
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
          ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
            (μ := μ) (W := W) (x := x) hW hWcont i).1)
          (fun s ξ ↦ (∂[i] F) (W s ξ - x))
          T
          ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
    -- Proof comment: the canonical stochastic owner is already identified with the centered
    -- pathwise owner once the sample path is rewritten to `Xω`.
    calc
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
          ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
            (μ := μ) (W := W) (x := x) hW hWcont i).1)
          (fun s ξ ↦ (∂[i] F) (W s ξ - x))
          T
          ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (W s ω - x))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
            simpa [Xω] using
              canonicalRawCoordinate_apply_eq_centeredPathwiseItoIntegral_theorem25_38
                (μ := μ) (W := W) (x := x) (F := F) (B := B)
                hW
                hWcont
                ω
                hcontω
                hω
                i
                T
      _ =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
            rw [hCoeff]
  have hBase :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F) (W s ω - x))
            (⟨fun s ↦ W s ω i - x i,
              ((continuous_apply i).comp ((hWcont ω).sub continuous_const))⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            (φ (ψ n)))
        atTop
        (𝓝
          (ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess
            ((centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
              (μ := μ) (W := W) (x := x) hW hWcont i).1)
            (fun s ξ ↦ (∂[i] F) (W s ξ - x))
            T
            ω)) :=
    hSubseq T
  rw [hRows] at hBase
  simpa [hLimit] using hBase

/-- Helper for Theorem 25.38: the coordinate-refinement subsequence theorem does not depend on
which continuity proof is used for the centered sample path. This lets later arguments reuse one
common witness across all coordinates. -/
private theorem
    centeredCoordinateRefinementSubsequence_ae_tendsto_allContinuousWitnesses_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hF : ContDiff ℝ 2 F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (i : Fin d) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T
                  (φ (ψ n)))
              atTop
              (𝓝
                (pathwiseItoIntegralAlong
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T)) := by
  intro B
  obtain ⟨ψ, hψ, hψae⟩ :=
    centeredCoordinateRefinementSubsequence_ae_tendsto_pathwise_theorem25_38
      (μ := μ) (W := W) (x := x) (F := F) hW hWcont hF hφ i
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψae] with ω hω hcontω
  rcases hω with ⟨hcontω', hω'⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  let Xω' : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω'⟩
  have hXeq : Xω = Xω' := by
    ext s
    rfl
  intro T
  -- Proof comment: the dyadic row family only depends on the underlying centered path, so
  -- changing the proof of continuity leaves both the reindexed rows and their canonical limit
  -- unchanged.
  simpa [Xω, Xω'] using (hXeq.symm ▸ hω' T)

/-- Helper for Theorem 25.38: one strict-mono selector can be chosen so that almost every
centered sample path carries simultaneous coordinate-row convergence for every `i : Fin d`. -/
private theorem existsCommonCoordinateRefinementSubsequence_ae_tendsto_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hF : ContDiff ℝ 2 F) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          ∀ i : Fin d, ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T
                  (χ n))
              atTop
              (𝓝
                (pathwiseItoIntegralAlong
                  (fun s : NNReal ↦ (∂[i] F) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T)) := by
  intro B
  have hFinset :
      ∀ s : Finset (Fin d),
        ∃ χ : ℕ → ℕ, StrictMono χ ∧
          ∀ᵐ ω ∂(μ : Measure Ω),
            ∀ hcontω : Continuous fun t : NNReal ↦ B t ω,
              let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
              ∀ i : Fin d, i ∈ s → ∀ T : NNReal,
                Tendsto
                  (fun n ↦
                    partitionPathwiseItoApproximationUpTo
                      (fun s : NNReal ↦ (∂[i] F) (Xω s))
                      (vectorPathComponent Xω i)
                      Definition2158.dyadicPartitionSequence
                      T
                      (χ n))
                  atTop
                  (𝓝
                    (pathwiseItoIntegralAlong
                      (fun s : NNReal ↦ (∂[i] F) (Xω s))
                      (vectorPathComponent Xω i)
                      Definition2158.dyadicPartitionSequence
                      T)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨id, strictMono_id, ?_⟩
        refine Filter.Eventually.of_forall ?_
        intro ω hcontω i hi T
        exact False.elim (Finset.not_mem_empty i hi)
    | @insert i s hi hs =>
        rcases hs with ⟨χ, hχ, hχae⟩
        obtain ⟨ψ, hψ, hψae⟩ :=
          centeredCoordinateRefinementSubsequence_ae_tendsto_allContinuousWitnesses_theorem25_38
            (μ := μ) (W := W) (x := x) (F := F) hW hWcont hF hχ i
        refine ⟨χ ∘ ψ, hχ.comp hψ, ?_⟩
        filter_upwards [hχae, hψae] with ω hωs hωi hcontω
        intro j hj T
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · -- Proof comment: the newly inserted coordinate uses the fresh refinement theorem
          -- directly along the common selector `χ ∘ ψ`.
          simpa [Function.comp] using hωi hcontω T
        · -- Proof comment: every previously handled coordinate keeps its limit after one more
          -- strict-mono reindexing because convergence persists along subsequences.
          simpa [Function.comp] using (hωs hcontω j hj' T).comp hψ.tendsto_atTop
  rcases hFinset Finset.univ with ⟨χ, hχ, hχae⟩
  refine ⟨χ, hχ, ?_⟩
  filter_upwards [hχae] with ω hω hcontω
  intro i T
  -- Proof comment: the induction runs over `Finset.univ`, so the resulting selector works for
  -- every coordinate simultaneously.
  exact hω hcontω i (by simp) T

/-- Helper for Theorem 25.38: convergence at `atTop` follows once every strict-mono subsequence
admits a further strict-mono refinement converging to the same limit. -/
private theorem tendstoAtTopOfStrictMonoSubseqTendsto_theorem25_38
    {α : Type*} [TopologicalSpace α] {u : ℕ → α} {a : α}
    (hRefine :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun n ↦ u (φ (ψ n))) atTop (𝓝 a)) :
    Tendsto u atTop (𝓝 a) := by
  -- Proof comment: reduce the statement to the standard subsequence criterion by extracting a
  -- strict-mono subsequence from every arbitrary `atTop`-tending row map.
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨φ, hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, hψ, hlim⟩ := hRefine (ns ∘ φ) hnsφ
  refine ⟨φ ∘ ψ, ?_⟩
  -- Proof comment: the composed strict-mono extraction is exactly the convergent refinement
  -- required by `Filter.tendsto_of_subseq_tendsto`.
  simpa [Function.comp] using hlim

/-- Helper for Theorem 25.38: along any strict-mono family of partition rows, one can pass to a
strict-mono refinement on which the clipped horizon is either always an exact partition point or
always strictly inside the active dyadic cell. -/
private theorem exists_strictMono_refinement_partition_or_nonPartition_theorem25_38
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (T : NNReal) :
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ n : ℕ, T = P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T)) ∨
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ n : ℕ, T < P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T)) := by
  let exactRow : ℕ → Prop := fun n ↦
    T = P (φ n) (partitionBoundIndex P (φ n) T)
  by_cases hFreqExact : ∃ᶠ n in atTop, exactRow n
  · obtain ⟨ψ, hψ, hExact⟩ := extraction_of_frequently_atTop hFreqExact
    -- Proof comment: if exact partition rows occur frequently, extract a strict-mono refinement
    -- on which every row hits the clipped horizon exactly.
    exact Or.inl ⟨ψ, hψ, hExact⟩
  · have hEventuallyNon : ∀ᶠ n in atTop, ¬ exactRow n := by
      simpa [Filter.Frequently] using hFreqExact
    have hFreqNon : ∃ᶠ n in atTop, ¬ exactRow n :=
      hEventuallyNon.frequently
    obtain ⟨ψ, hψ, hNonExact⟩ := extraction_of_frequently_atTop hFreqNon
    refine Or.inr ⟨ψ, hψ, ?_⟩
    intro n
    have hle :
        T ≤ P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T) :=
      le_partitionBoundIndex_time P (φ (ψ n)) T
    have hne :
        T ≠ P (φ (ψ n)) (partitionBoundIndex P (φ (ψ n)) T) := by
      simpa [exactRow] using hNonExact n
    -- Proof comment: outside the exact-partition case, the defining bound-index point still lies
    -- above `T`, so it is automatically the strict non-partition branch.
    exact lt_of_le_of_ne hle hne

/-- Helper for Theorem 25.38: in the genuine after-exit non-partition branch, the stopped
coordinate row at horizon `t` is exactly the raw row evaluated at the clipped successor horizon on
the same dyadic row. -/
private theorem stoppedCoordinateRow_eq_rawFirstPastExit_nonPartition_theorem25_38
    {W : VectorProcess} {U : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hAfter : T < t)
    (hNonPart :
      T < Definition2158.dyadicPartitionSequence n
        (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    (hK :
      ∀ j : ℕ,
        j < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
          ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              (hittingAfter W Uᶜ 0)
              (Definition2158.dyadicPartitionSequence n j)
              ω =
            K (Definition2158.dyadicPartitionSequence n j)) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        (partitionNextPointUpTo
          Definition2158.dyadicPartitionSequence
          n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
          t)
        n := by
  let P := Definition2158.dyadicPartitionSequence
  let k := partitionBoundIndex P n T
  let succ := partitionNextPointUpTo P n (k - 1) t
  let stoppedCoeff : NNReal → ℝ := fun s ↦
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_38
        (Ω := Ω) (W := W) (F := F) i)
      (hittingAfter W Uᶜ 0)
      s
      ω
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hT_lt_zero : T < 0 := by
      simpa [P, k, hk0, IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hNonPart
    exact (not_lt_of_ge bot_le) hT_lt_zero
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne_zero
  have hT_lt_succ : T < succ := by
    -- Proof comment: in the non-partition branch, both the next partition point and the target
    -- horizon `t` lie strictly after the exit horizon `T`, so their clipped minimum does too.
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact lt_min hNonPart hAfter
  have hsucc_le_pk : succ ≤ P n k := by
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hsuccIdx : partitionBoundIndex P n succ = k := by
    have hpred_lt_T : P n k' < T := by
      have hk'_lt : k' < k := by
        simpa [k, hk'] using Nat.lt_succ_self k'
      exact partitionPoint_lt_time_of_lt_partitionBoundIndex P n k' T hk'_lt
    have hpred_lt_succ : P n k' < succ := lt_trans hpred_lt_T hT_lt_succ
    -- Proof comment: the clipped successor still sits in the same dyadic cell, so its
    -- truncation index remains `k`.
    simpa [k, hk'] using
      partitionBoundIndex_eq_succ_of_lt_of_le P n k' hpred_lt_succ (by
        simpa [k, hk'] using hsucc_le_pk)
  have hk_le_t : k ≤ partitionBoundIndex P n t := by
    calc
      k = partitionBoundIndex P n succ := hsuccIdx.symm
      _ ≤ partitionBoundIndex P n t := partitionBoundIndex_monotone P n (by
        dsimp [succ]
        rw [partitionNextPointUpTo]
        exact min_le_right _ _)
  have hPrefix :
      ∑ j in Finset.range k,
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j))
        =
      ∑ j in Finset.range k,
        K (P n j) *
          (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hK j (by simpa [k] using Finset.mem_range.mp hj)]
    have hj1_le_k : j + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hnext :
        partitionNextPointUpTo P n j t =
          partitionNextPointUpTo P n j succ := by
      rcases lt_or_eq_of_le hj1_le_k with hj1_lt | hj1_eq
      · have hj1_lt_t : j + 1 < partitionBoundIndex P n t :=
          lt_of_lt_of_le hj1_lt hk_le_t
        have hj1_lt_succ : j + 1 < partitionBoundIndex P n succ := by
          simpa [hsuccIdx] using hj1_lt
        have hnext_t : partitionNextPointUpTo P n j t = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) t hj1_lt_t)
        have hnext_succ : partitionNextPointUpTo P n j succ = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt
              (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) succ hj1_lt_succ)
        rw [hnext_t, hnext_succ]
      · have hj_eq : j = k - 1 := by
        omega
      -- Proof comment: at the last contributing left endpoint, both clipped successors coincide
      -- with the chosen clipped successor horizon itself.
        have hnext_t : partitionNextPointUpTo P n j t = succ := by
          simpa [succ, hj_eq]
        have hnext_succ : partitionNextPointUpTo P n j succ = succ := by
          rw [hj_eq, partitionNextPointUpTo, min_eq_right]
          exact hsucc_le_pk
        rw [hnext_t, hnext_succ]
    rw [hnext]
  have hTail :
      ∑ j in Finset.Ico k (partitionBoundIndex P n t),
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j)) = 0 := by
    -- Proof comment: once the left endpoint index reaches `k`, every sampled time lies strictly
    -- after the exit horizon `T`, so the stopped coefficient kills the whole tail.
    simpa [P, k, stoppedCoeff] using
      stoppedCoordinateRowTail_eq_zero_afterTime_theorem25_38
        (W := W) (U := U) (F := F) i X P (ω := ω) (T := T) (t := t) (row := n)
        (first := k) hT hNonPart
  have hRawSucc :
      partitionPathwiseItoApproximationUpTo K X P succ n =
        ∑ j in Finset.range k,
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    rw [partitionPathwiseItoApproximationUpTo, hsuccIdx]
  calc
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        P
        t
        n
      =
        ∑ j in Finset.range k,
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) +
        ∑ j in Finset.Ico k (partitionBoundIndex P n t),
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) := by
          rw [partitionPathwiseItoApproximationUpTo, ← Finset.sum_range_add_sum_Ico _ hk_le_t]
    _ =
        ∑ j in Finset.range k,
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
          rw [hTail, add_zero, hPrefix]
    _ = partitionPathwiseItoApproximationUpTo K X P succ n := hRawSucc.symm

/-- Helper for Theorem 25.38: in the partition-point branch, the stopped coordinate row at
horizon `t` is exactly the raw row evaluated at the clipped successor horizon on that same row. -/
private theorem stoppedCoordinateRow_eq_rawClippedSuccessor_partitionPoint_theorem25_38
    {W : VectorProcess} {U : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n m : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hPart : T = Definition2158.dyadicPartitionSequence n m)
    (hm : m < partitionBoundIndex Definition2158.dyadicPartitionSequence n t)
    (hK :
      ∀ j : ℕ, j ≤ m →
        ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            (Definition2158.dyadicPartitionSequence n j)
            ω =
          K (Definition2158.dyadicPartitionSequence n j)) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t)
        n := by
  let P := Definition2158.dyadicPartitionSequence
  let succ := partitionNextPointUpTo P n m t
  let stoppedCoeff : NNReal → ℝ := fun s ↦
    ProbabilityTheory.processBeforeStoppingTime
      (coordinatePartialDerivProcess_theorem25_38
        (Ω := Ω) (W := W) (F := F) i)
      (hittingAfter W Uᶜ 0)
      s
      ω
  have hT_lt_succ : T < succ := by
    -- Proof comment: the partition-point branch assumes `m` is still strictly below the
    -- truncation index of `t`, so the clipped successor lies strictly after `T = P n m`.
    have hsucc_eq : succ = P n (m + 1) := by
      dsimp [succ]
      rw [partitionNextPointUpTo, min_eq_left]
      exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (m + 1) t hm)
    rw [hsucc_eq, hPart]
    exact (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n) (Nat.lt_succ_self m)
  have hsucc_le_next : succ ≤ P n (m + 1) := by
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hsuccIdx : partitionBoundIndex P n succ = m + 1 := by
    -- Proof comment: the clipped successor sits strictly between `P n m` and `P n (m + 1)`,
    -- so its truncation index is exactly `m + 1`.
    rw [hPart] at hT_lt_succ
    exact partitionBoundIndex_eq_succ_of_lt_of_le P n m hT_lt_succ hsucc_le_next
  have hm_le_t : m + 1 ≤ partitionBoundIndex P n t := Nat.succ_le_of_lt hm
  have hPrefix :
      ∑ j in Finset.range (m + 1),
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j))
        =
      ∑ j in Finset.range (m + 1),
        K (P n j) *
          (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hK j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    have hj1_le : j + 1 ≤ m + 1 := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hnext :
        partitionNextPointUpTo P n j t =
          partitionNextPointUpTo P n j succ := by
      rcases lt_or_eq_of_le hj1_le with hj1_lt | hj1_eq
      · have hnext_t : partitionNextPointUpTo P n j t = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) t
              (lt_of_lt_of_le hj1_lt hm_le_t))
        have hnext_succ : partitionNextPointUpTo P n j succ = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact
            le_of_lt
              (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) succ (by
                simpa [hsuccIdx] using hj1_lt))
        rw [hnext_t, hnext_succ]
      · have hj_eq : j = m := by
          omega
        -- Proof comment: at the boundary index `m`, both clipped successors are exactly the
        -- single successor horizon chosen in this branch.
        have hnext_t : partitionNextPointUpTo P n j t = succ := by
          simpa [succ, hj_eq]
        have hnext_succ : partitionNextPointUpTo P n j succ = succ := by
          rw [hj_eq, succ, partitionNextPointUpTo, min_eq_right]
          exact hsucc_le_next
        rw [hnext_t, hnext_succ]
    rw [hnext]
  have hTail :
      ∑ j in Finset.Ico (m + 1) (partitionBoundIndex P n t),
        stoppedCoeff (P n j) *
          (X (partitionNextPointUpTo P n j t) - X (P n j)) = 0 := by
    have hAfterStart : T < P n (m + 1) := by
      rw [hPart]
      exact (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n) (Nat.lt_succ_self m)
    -- Proof comment: every later sampled left endpoint lies strictly after exit, so the stopped
    -- coordinate coefficient again kills the remaining tail.
    simpa [P, stoppedCoeff] using
      stoppedCoordinateRowTail_eq_zero_afterTime_theorem25_38
        (W := W) (U := U) (F := F) i X P (ω := ω) (T := T) (t := t) (row := n)
        (first := m + 1) hT hAfterStart
  have hRawSucc :
      partitionPathwiseItoApproximationUpTo K X P succ n =
        ∑ j in Finset.range (m + 1),
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
    rw [partitionPathwiseItoApproximationUpTo, hsuccIdx]
  calc
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        P
        t
        n
      =
        ∑ j in Finset.range (m + 1),
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) +
        ∑ j in Finset.Ico (m + 1) (partitionBoundIndex P n t),
          stoppedCoeff (P n j) *
            (X (partitionNextPointUpTo P n j t) - X (P n j)) := by
          rw [partitionPathwiseItoApproximationUpTo, ← Finset.sum_range_add_sum_Ico _ hm_le_t]
    _ =
        ∑ j in Finset.range (m + 1),
          K (P n j) *
            (X (partitionNextPointUpTo P n j succ) - X (P n j)) := by
          rw [hTail, add_zero, hPrefix]
    _ = partitionPathwiseItoApproximationUpTo K X P succ n := hRawSucc.symm

/-- Helper for Theorem 25.38: after exit, the stopped coordinate row at horizon `t` is always a
raw row on the same dyadic row, evaluated at the appropriate exact/non-partition successor
horizon determined by the clipped exit time `T`. -/
private def afterExitMovingHorizon_theorem25_38
    (n : ℕ) (T t : NNReal) : NNReal :=
  if hExact :
      T =
        Definition2158.dyadicPartitionSequence n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) then
    partitionNextPointUpTo
      Definition2158.dyadicPartitionSequence
      n
      (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)
      t
  else
    partitionNextPointUpTo
      Definition2158.dyadicPartitionSequence
      n
      (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
      t

/-- Helper for Theorem 25.38: once the raw translated coordinate coefficient is known on every
sampled left endpoint up to the clipped exit time, the after-exit stopped row at time `t`
rewrites uniformly to the raw row at the exact/non-partition successor horizon from the same
dyadic cell. -/
private theorem stoppedCoordinateRow_eq_rawMovingHorizon_afterExit_theorem25_38
    {W : VectorProcess} {U : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hAfter : T < t)
    (hK_lt :
      ∀ j : ℕ,
        j < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
          ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              (hittingAfter W Uᶜ 0)
              (Definition2158.dyadicPartitionSequence n j)
              ω =
            K (Definition2158.dyadicPartitionSequence n j)) :
    (hK_exact :
      T =
          Definition2158.dyadicPartitionSequence n
            (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) →
        ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            T
            ω =
          K T) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        (afterExitMovingHorizon_theorem25_38 n T t)
        n := by
  let P := Definition2158.dyadicPartitionSequence
  let k := partitionBoundIndex P n T
  by_cases hExact : T = P n k
  · have hk_lt_t : k < partitionBoundIndex P n t := by
      by_contra hk_not
      have hk_ge : partitionBoundIndex P n t ≤ k := Nat.not_lt.mp hk_not
      have hbound_le : P n (partitionBoundIndex P n t) ≤ P n k :=
        (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n).monotone hk_ge
      have hbound_lt_t : P n (partitionBoundIndex P n t) < t := by
        calc
          P n (partitionBoundIndex P n t) ≤ P n k := hbound_le
          _ = T := hExact.symm
          _ < t := hAfter
      exact (not_lt_of_ge (le_partitionBoundIndex_time P n t)) hbound_lt_t
    have hK :
        ∀ j : ℕ,
          j ≤ k →
            ProbabilityTheory.processBeforeStoppingTime
                (coordinatePartialDerivProcess_theorem25_38
                  (Ω := Ω) (W := W) (F := F) i)
                (hittingAfter W Uᶜ 0)
                (P n j)
                ω =
              K (P n j) := by
      intro j hj
      rcases lt_or_eq_of_le hj with hj_lt | rfl
      · exact hK_lt j hj_lt
      · simpa [P, k, hExact] using hK_exact hExact
    -- Proof comment: in the exact-partition branch, the moving horizon is just the clipped next
    -- partition point, and the packaged exact-row identity applies directly.
    simpa [afterExitMovingHorizon_theorem25_38, P, k, hExact] using
      stoppedCoordinateRow_eq_rawClippedSuccessor_partitionPoint_theorem25_38
        (W := W) (U := U) (F := F) i X (ω := ω) (t := t) (T := T) (n := n) (m := k)
        (K := K) hT hExact hk_lt_t hK
  · have hNonPart : T < P n k := by
      have hle : T ≤ P n k := le_partitionBoundIndex_time P n T
      exact lt_of_le_of_ne hle hExact
    -- Proof comment: outside the exact-partition case, the exit time stays strictly inside the
    -- active cell, so the non-partition moving-successor identity gives the required rewrite.
    simpa [afterExitMovingHorizon_theorem25_38, P, k, hExact] using
      stoppedCoordinateRow_eq_rawFirstPastExit_nonPartition_theorem25_38
        (W := W) (U := U) (F := F) i X (ω := ω) (t := t) (T := T) (n := n)
        (K := K) hT hAfter hNonPart hK_lt

/-- Helper for Theorem 25.38: in the after-exit non-partition branch, the stopped coordinate row
at horizon `t` is the raw clipped row at `T` plus the single successor-side boundary increment on
that same dyadic cell. -/
private theorem stoppedCoordinateRow_eq_rawClipped_plus_successorBoundary_nonPartition_theorem25_38
    {W : VectorProcess} {U : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hAfter : T < t)
    (hNonPart :
      T < Definition2158.dyadicPartitionSequence n
        (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    (hK :
      ∀ j : ℕ,
        j < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
          ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              (hittingAfter W Uᶜ 0)
              (Definition2158.dyadicPartitionSequence n j)
              ω =
            K (Definition2158.dyadicPartitionSequence n j)) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        T
        n +
      K (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n T) *
        (X
            (partitionNextPointUpTo
              Definition2158.dyadicPartitionSequence
              n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
              T) -
          X T) := by
  let P := Definition2158.dyadicPartitionSequence
  let k := partitionBoundIndex P n T
  let succ := partitionNextPointUpTo P n (k - 1) T
  have hStopToSucc :
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦
            ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              (hittingAfter W Uᶜ 0)
              s
              ω)
          X
          P
          t
          n
        =
      partitionPathwiseItoApproximationUpTo
          K
          X
          P
          succ
          n := by
    -- Proof comment: first normalize the stopped row to the raw row at the clipped successor
    -- horizon from the same dyadic cell.
    simpa [P, k, succ] using
      stoppedCoordinateRow_eq_rawFirstPastExit_nonPartition_theorem25_38
        (W := W) (U := U) (F := F) i X (ω := ω) (t := t) (T := T) (n := n)
        (K := K) hT hAfter hNonPart hK
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hT_lt_zero : T < 0 := by
      simpa [P, k, hk0, IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hNonPart
    exact (not_lt_of_ge bot_le) hT_lt_zero
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne_zero
  have hT_lt_succ : T < succ := by
    -- Proof comment: in the non-partition branch, the clipped successor still lies strictly
    -- after the clipped horizon `T`.
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact lt_min hNonPart hAfter
  have hsucc_le_pk : succ ≤ P n k := by
    dsimp [succ]
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hsuccIdx : partitionBoundIndex P n succ = k := by
    have hpred_lt_T : P n k' < T := by
      have hk'_lt : k' < k := by
        simpa [k, hk'] using Nat.lt_succ_self k'
      exact partitionPoint_lt_time_of_lt_partitionBoundIndex P n k' T hk'_lt
    have hpred_lt_succ : P n k' < succ := lt_trans hpred_lt_T hT_lt_succ
    -- Proof comment: `succ` remains in the same active dyadic cell as `T`, so the truncation
    -- index does not change.
    simpa [k, hk'] using
      partitionBoundIndex_eq_succ_of_lt_of_le P n k' hpred_lt_succ (by
        simpa [k, hk'] using hsucc_le_pk)
  have hPredEq :
      partitionPredecessorPointEarly P n succ =
        partitionPredecessorPointEarly P n T := by
    -- Proof comment: same-cell horizons share the same predecessor endpoint.
    simp [partitionPredecessorPointEarly, hsuccIdx, k, hk']
  have hRawSucc :
      partitionPathwiseItoApproximationUpTo K X P succ n =
        partitionPathwiseItoApproximationUpTo K X P T n +
          K (partitionPredecessorPointEarly P n T) * (X succ - X T) := by
    -- Proof comment: once both raw horizons are in the same cell, only the final
    -- successor-side boundary increment remains.
    calc
      partitionPathwiseItoApproximationUpTo K X P succ n =
          partitionPathwiseItoApproximationUpTo K X P T n +
            K (partitionPredecessorPointEarly P n succ) * (X succ - X T) := by
              exact
                rawRow_firstPastExit_nonPartition_eq_clipped_plus_boundary_theorem25_38
                  (H := K)
                  (X := X)
                  (S := T)
                  (T := succ)
                  (n := n)
                  (le_of_lt hT_lt_succ)
                  (by simpa [k] using hsuccIdx.symm)
      _ =
          partitionPathwiseItoApproximationUpTo K X P T n +
            K (partitionPredecessorPointEarly P n T) * (X succ - X T) := by
              rw [hPredEq]
  -- Proof comment: compose the stopped-to-successor normalization with the raw same-cell
  -- boundary decomposition to obtain the final after-exit row formula.
  calc
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        P
        t
        n
      = partitionPathwiseItoApproximationUpTo K X P succ n := hStopToSucc
    _ =
        partitionPathwiseItoApproximationUpTo K X P T n +
          K (partitionPredecessorPointEarly P n T) * (X succ - X T) := hRawSucc

/-- Helper for Theorem 25.38: in the after-exit partition-point branch, the stopped coordinate row
at horizon `t` is the raw clipped row at `T` plus the single exact-successor boundary increment
from `T` to the clipped next partition point. -/
private theorem
    stoppedCoordinateRow_eq_rawClipped_plus_exactSuccessorBoundary_partitionPoint_theorem25_38
    {W : VectorProcess} {U : Set State} {F : State → ℝ}
    (i : Fin d) (X : C(NNReal, ℝ)) {ω : Ω} {t T : NNReal} {n m : ℕ}
    {K : NNReal → ℝ}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hPart : T = Definition2158.dyadicPartitionSequence n m)
    (hm : m < partitionBoundIndex Definition2158.dyadicPartitionSequence n t)
    (hK :
      ∀ j : ℕ, j ≤ m →
        ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            (Definition2158.dyadicPartitionSequence n j)
            ω =
          K (Definition2158.dyadicPartitionSequence n j)) :
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        Definition2158.dyadicPartitionSequence
        t
        n
      =
    partitionPathwiseItoApproximationUpTo
        K
        X
        Definition2158.dyadicPartitionSequence
        T
        n +
      K T *
        (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n m t) - X T) := by
  let P := Definition2158.dyadicPartitionSequence
  let succ := partitionNextPointUpTo P n m t
  have hStopToSucc :
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦
            ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              (hittingAfter W Uᶜ 0)
              s
              ω)
          X
          P
          t
          n
        =
      partitionPathwiseItoApproximationUpTo
          K
          X
          P
          succ
          n := by
    -- Proof comment: the exact-partition branch again first rewrites the stopped row to the raw
    -- row at the clipped successor horizon.
    simpa [P, succ] using
      stoppedCoordinateRow_eq_rawClippedSuccessor_partitionPoint_theorem25_38
        (W := W) (U := U) (F := F) i X (ω := ω) (t := t) (T := T) (n := n) (m := m)
        (K := K) hT hPart hm hK
  have hRawSucc :
      partitionPathwiseItoApproximationUpTo K X P succ n =
        partitionPathwiseItoApproximationUpTo K X P T n +
          K T * (X succ - X T) := by
    -- Proof comment: for an exact partition point, moving once to the clipped successor adds
    -- exactly one explicit boundary increment sampled at `T`.
    simpa [P, succ] using
      rawRow_firstPastExit_partitionPoint_eq_clipped_plus_boundary_theorem25_38
        (H := K) (X := X) (t := t) (T := T) (n := n) (m := m) hPart hm
  -- Proof comment: combine the stopped-row normalization with the exact successor-row formula.
  calc
    partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            (hittingAfter W Uᶜ 0)
            s
            ω)
        X
        P
        t
        n
      = partitionPathwiseItoApproximationUpTo K X P succ n := hStopToSucc
    _ =
        partitionPathwiseItoApproximationUpTo K X P T n +
          K T * (X succ - X T) := hRawSucc

/-- Helper for Theorem 25.38: on rows where the clipped horizon is itself a partition point, the
moving-horizon raw row differs from the clipped raw row by exactly the one-step exact-successor
boundary increment, so that error tends to `0` along any strict-mono row family. -/
private theorem rawCoordinateExactSuccessorError_tendsto_zero_afterExit_theorem25_38
    (H : NNReal → ℝ) (X : C(NNReal, ℝ))
    {φ κ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hκ :
      ∀ n : ℕ,
        T = Definition2158.dyadicPartitionSequence (φ n) (κ n))
    (hκ_lt :
      ∀ n : ℕ,
        κ n < partitionBoundIndex Definition2158.dyadicPartitionSequence (φ n) t) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t)
            (φ n) -
          partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            T
            (φ n))
      atTop
      (𝓝 0) := by
  have hEq :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t)
            (φ n) -
          partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            T
            (φ n)) =
        fun n ↦
          H T *
            (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t) -
              X T) := by
    funext n
    have hRow :
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t)
            (φ n) =
          partitionPathwiseItoApproximationUpTo
              H
              X
              Definition2158.dyadicPartitionSequence
              T
              (φ n) +
            H T *
              (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t) -
                X T) := by
      -- Proof comment: on an exact-partition row, moving from `T` to the clipped successor adds
      -- only the explicit one-step boundary increment sampled at `T`.
      exact
        rawRow_firstPastExit_partitionPoint_eq_clipped_plus_boundary_theorem25_38
          (H := H)
          (X := X)
          (t := t)
          (T := T)
          (n := φ n)
          (m := κ n)
          (hκ n)
          (hκ_lt n)
    linarith
  have hBoundary :
      Tendsto
        (fun n ↦
          H T *
            (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence (φ n) (κ n) t) -
              X T))
        atTop
        (𝓝 0) := by
    -- Proof comment: the exact-successor boundary increment vanishes because the clipped
    -- successor converges back to the fixed partition point `T`.
    simpa using
      partitionItoExactSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_38
        (H := H)
        (X := X)
        (P := Definition2158.dyadicPartitionSequence)
        hφ
        hκ
        hκ_lt
  rw [hEq]
  exact hBoundary

/-- Helper for Theorem 25.38: in the genuine after-exit non-partition branch, the clipped
successor selected by the later horizon `t` still converges back to the clipped exit time `T`
along any strict-mono family of rows. -/
private theorem partitionAfterExitSuccessor_tendsto_alongStrictMonoRows_theorem25_38
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hAfter : T < t)
    (hNonPart :
      ∀ n : ℕ,
        T < P (φ n) (partitionBoundIndex P (φ n) T)) :
    Tendsto
      (fun n ↦
        partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) t)
      atTop
      (𝓝 T) := by
  have hmesh :
      Tendsto (fun n ↦ partitionMesh P (φ n)) atTop (𝓝 0) :=
    hP.mesh_tendsto_zero.comp hφ.tendsto_atTop
  rw [tendsto_iff_edist_tendsto_0]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      (by simpa using hmesh.add hmesh)
      (fun n ↦ bot_le)
      ?_
  intro n
  let row := φ n
  let k := partitionBoundIndex P row T
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hT_lt_zero : T < 0 := by
      simpa [row, k, hk0, IsAdmissiblePartitionSequence.zero_eq (P := P) row] using hNonPart n
    exact (not_lt_of_ge bot_le) hT_lt_zero
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = k' + 1 :=
    Nat.exists_eq_succ_of_ne_zero hk_ne_zero
  have hpred : partitionPredecessorPointEarly P row T = P row k' := by
    -- Proof comment: the strict non-partition hypothesis forces a positive truncation index, so
    -- the predecessor point is the last active left endpoint on this row.
    simp [row, k, partitionPredecessorPointEarly, hk']
  have hk'_lt_t : k' < partitionBoundIndex P row t := by
    have hpred_lt_T : P row k' < T := by
      -- Proof comment: the predecessor endpoint sits strictly before the clipped horizon `T`.
      simpa [row, k, hk'] using
        partitionPoint_lt_time_of_lt_truncationBoundIndex P row k' T (Nat.lt_succ_self k')
    by_contra hk'_not
    have hle : partitionBoundIndex P row t ≤ k' := Nat.not_lt.mp hk'_not
    have ht_le : t ≤ P row k' := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P row t) hle)
    exact (not_le_of_gt (lt_of_lt_of_lt hpred_lt_T hAfter)) ht_le
  have hsucc_mesh :
      edist
          (partitionPredecessorPointEarly P row T)
          (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) t)
        ≤ partitionMesh P row := by
    -- Proof comment: once the predecessor endpoint is fixed, the later-horizon clipped
    -- successor lies within one mesh width of that predecessor.
    rw [hpred]
    simpa [row, k, hk'] using
      edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh P row k' t hk'_lt_t
  have hpred_mesh :
      edist (partitionPredecessorPointEarly P row T) T ≤ partitionMesh P row :=
    partitionPredecessorPointWithinMeshEarly P row T
  calc
    edist (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) t) T
      ≤
        edist
            (partitionNextPointUpTo P row (partitionBoundIndex P row T - 1) t)
            (partitionPredecessorPointEarly P row T) +
          edist (partitionPredecessorPointEarly P row T) T := by
            exact edist_triangle _ _ _
    _ ≤ partitionMesh P row + partitionMesh P row := by
          exact add_le_add (by simpa [edist_comm] using hsucc_mesh) hpred_mesh

/-- Helper for Theorem 25.38: in the genuine after-exit non-partition branch, the moving-horizon
raw row differs from the clipped raw row by one same-cell boundary increment, and that error
tends to `0` along any strict-mono family of rows. -/
private theorem rawCoordinateNonPartitionSuccessorError_tendsto_zero_afterExit_theorem25_38
    (H : NNReal → ℝ) (hH : Continuous H) (X : C(NNReal, ℝ))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {T t : NNReal}
    (hAfter : T < t)
    (hNonPart :
      ∀ n : ℕ,
        T <
          Definition2158.dyadicPartitionSequence
            (φ n)
            (partitionBoundIndex Definition2158.dyadicPartitionSequence (φ n) T)) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo
              Definition2158.dyadicPartitionSequence
              (φ n)
              (partitionBoundIndex Definition2158.dyadicPartitionSequence (φ n) T - 1)
              t)
            (φ n) -
          partitionPathwiseItoApproximationUpTo
            H
            X
            Definition2158.dyadicPartitionSequence
            T
            (φ n))
      atTop
      (𝓝 0) := by
  let P := Definition2158.dyadicPartitionSequence
  let succ : ℕ → NNReal := fun n ↦
    partitionNextPointUpTo P (φ n) (partitionBoundIndex P (φ n) T - 1) t
  have hEq :
      (fun n ↦
        partitionPathwiseItoApproximationUpTo H X P (succ n) (φ n) -
          partitionPathwiseItoApproximationUpTo H X P T (φ n)) =
        fun n ↦
          H (partitionPredecessorPointEarly P (φ n) T) * (X (succ n) - X T) := by
    funext n
    let row := φ n
    let k := partitionBoundIndex P row T
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      have hT_lt_zero : T < 0 := by
        simpa [P, row, k, hk0, IsAdmissiblePartitionSequence.zero_eq (P := P) row] using
          hNonPart n
      exact (not_lt_of_ge bot_le) hT_lt_zero
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = k' + 1 :=
      Nat.exists_eq_succ_of_ne_zero hk_ne_zero
    have hpred_lt_T : P row k' < T := by
      -- Proof comment: the predecessor endpoint of the active non-partition cell lies strictly
      -- before the clipped horizon `T`.
      simpa [P, row, k, hk'] using
        partitionPoint_lt_time_of_lt_truncationBoundIndex P row k' T (Nat.lt_succ_self k')
    have hT_lt_succ : T < succ n := by
      -- Proof comment: both the later horizon `t` and the next partition point on the active
      -- cell stay strictly above `T`, so the clipped successor lies strictly to the right of `T`.
      dsimp [succ]
      rw [partitionNextPointUpTo]
      exact lt_min (hNonPart n) hAfter
    have hsucc_le_pk : succ n ≤ P row k := by
      dsimp [succ]
      rw [partitionNextPointUpTo]
      exact min_le_left _ _
    have hsuccIdx : partitionBoundIndex P row (succ n) = k := by
      have hpred_lt_succ : P row k' < succ n := lt_trans hpred_lt_T hT_lt_succ
      -- Proof comment: the moving horizon still lies in the same active cell, so the
      -- truncation index remains equal to the clipped-horizon index `k`.
      simpa [P, row, k, hk'] using
        partitionBoundIndex_eq_succ_of_lt_of_le
          P
          row
          k'
          hpred_lt_succ
          (by simpa [P, row, k, hk'] using hsucc_le_pk)
    have hPredEq :
        partitionPredecessorPointEarly P row (succ n) =
          partitionPredecessorPointEarly P row T := by
      -- Proof comment: horizons in the same dyadic cell have the same predecessor endpoint.
      simp [P, row, partitionPredecessorPointEarly, hsuccIdx, k, hk']
    have hRow :
        partitionPathwiseItoApproximationUpTo H X P (succ n) row =
          partitionPathwiseItoApproximationUpTo H X P T row +
            H (partitionPredecessorPointEarly P row T) * (X (succ n) - X T) := by
      calc
        partitionPathwiseItoApproximationUpTo H X P (succ n) row =
            partitionPathwiseItoApproximationUpTo H X P T row +
              H (partitionPredecessorPointEarly P row (succ n)) * (X (succ n) - X T) := by
                exact
                  rawRow_firstPastExit_nonPartition_eq_clipped_plus_boundary_theorem25_38
                    (H := H)
                    (X := X)
                    (S := T)
                    (T := succ n)
                    (n := row)
                    (le_of_lt hT_lt_succ)
                    (by simpa [P, row, k] using hsuccIdx.symm)
        _ =
            partitionPathwiseItoApproximationUpTo H X P T row +
              H (partitionPredecessorPointEarly P row T) * (X (succ n) - X T) := by
                rw [hPredEq]
    linarith
  have hBoundary :
      Tendsto
        (fun n ↦
          H (partitionPredecessorPointEarly P (φ n) T) * (X (succ n) - X T))
        atTop
        (𝓝 0) := by
    have hCoeff :
        Tendsto
          (fun n ↦ H (partitionPredecessorPointEarly P (φ n) T))
          atTop
          (𝓝 (H T)) := by
      -- Proof comment: the predecessor endpoints still converge to `T`, so the sampled
      -- coefficient converges to its target value by continuity of `H`.
      exact
        hH.continuousAt.tendsto.comp
          (partitionPredecessorPointEarly_tendsto_alongStrictMonoRows_theorem25_38 P hφ T)
    have hSucc :
        Tendsto (fun n ↦ X (succ n)) atTop (𝓝 (X T)) :=
      X.continuous.continuousAt.tendsto.comp
        (partitionAfterExitSuccessor_tendsto_alongStrictMonoRows_theorem25_38
          P
          hφ
          hAfter
          hNonPart)
    have hIncrement :
        Tendsto (fun n ↦ X (succ n) - X T) atTop (𝓝 0) := by
      have hConst : Tendsto (fun _ : ℕ ↦ X T) atTop (𝓝 (X T)) :=
        tendsto_const_nhds
      -- Proof comment: once the moving clipped successors converge back to `T`, the final
      -- same-cell path increment vanishes.
      simpa using hSucc.sub hConst
    -- Proof comment: the predecessor coefficient remains bounded near `T` while the moving
    -- same-cell increment vanishes, so the whole error term tends to `0`.
    simpa using hCoeff.mul hIncrement
  rw [hEq]
  exact hBoundary

/-- Helper for Theorem 25.38: after the exit time, the dyadic row of the theorem-local
deterministic cutoff coefficient at horizon `U'` is exactly the raw moving-horizon row on the
fixed centered sample path. -/
private theorem constCutoffCoordinateRows_eq_rawMovingHorizon_afterExit_theorem25_38
    {W : VectorProcess} {x : State} {U : Set State} {F : State → ℝ}
    {B : VectorProcess} {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = W t ω - x)
    (hF : Differentiable ℝ F)
    (i : Fin d) {T U' : NNReal}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hTU : T < U') :
    let F0 : State → ℝ := fun z : State ↦ F (x + z)
    let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        (hittingAfter W Uᶜ 0)
    let HiCut : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (T : ENNReal))
    ∀ row : ℕ,
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ HiCut s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row
        =
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          (afterExitMovingHorizon_theorem25_38 row T U')
          row := by
  intro F0 Xω Hi HiCut row
  have hHiSample :
      ∀ s : NNReal,
        Hi s ω =
          if (s : ENNReal) ≤ (T : ENNReal) then
            (∂[i] F0) (Xω s)
          else
            0 := by
    -- Proof comment: along the fixed sample, the exit-stopped coordinate coefficient is exactly
    -- the raw translated coefficient clipped at the exit horizon `T`.
    simpa [Hi, F0, Xω] using
      sampleStoppedCoordinate_eq_constCutoffRaw_theorem25_38
        (W := W) (x := x) (U := U) (F := F) (B := B) (ω := ω)
        hω
        hF
        i
        (T := T)
        hT
  have hHiCutSample : ∀ s : NNReal, HiCut s ω = Hi s ω := by
    intro s
    by_cases hs : (s : ENNReal) ≤ (T : ENNReal)
    · -- Proof comment: before `T`, the extra deterministic cutoff leaves the already stopped
      -- coefficient unchanged.
      simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs]
    · have hHiZero : Hi s ω = 0 := by
        simpa [hs] using hHiSample s
      -- Proof comment: after `T`, both the exit-stopped coefficient and its deterministic
      -- cutoff are already zero on the fixed sample.
      simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs, hHiZero]
  have hCutToStop :
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ HiCut s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row
        =
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ Hi s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row := by
    -- Proof comment: the fixed-sample coefficient equality `HiCut = Hi` lets us normalize the
    -- dyadic row to the single-stopped coefficient before applying the after-exit row rewrite.
    exact
      partitionPathwiseItoApproximationUpTo_congrOn_Icc
        (P := Definition2158.dyadicPartitionSequence)
        (X := vectorPathComponent Xω i)
        (T := U')
        (hKL := by
          intro s hs
          exact hHiCutSample s)
        row
  have hRawRow :
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ Hi s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row
        =
      partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          (afterExitMovingHorizon_theorem25_38 row T U')
          row := by
    -- Proof comment: once the sample coefficient is normalized, the existing exact/non-partition
    -- after-exit row decomposition transports the stopped row to the raw moving-horizon row.
    exact
      stoppedCoordinateRow_eq_rawMovingHorizon_afterExit_theorem25_38
        (W := W)
        (U := U)
        (F := F)
        i
        (vectorPathComponent Xω i)
        (ω := ω)
        (t := U')
        (T := T)
        (n := row)
        (K := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        hT
        hTU
        (by
          intro j hj
          have hs_le_T :
              Definition2158.dyadicPartitionSequence row j ≤ T := by
            exact
              (partitionPoint_mem_Icc_of_lt_truncationBoundIndex
                Definition2158.dyadicPartitionSequence
                row
                j
                T
                hj).2
          have hs_cutoff :
              ((Definition2158.dyadicPartitionSequence row j : NNReal) : ENNReal) ≤
                (T : ENNReal) := by
            exact_mod_cast hs_le_T
          simpa [hs_cutoff] using
            hHiSample (Definition2158.dyadicPartitionSequence row j))
        (by
          intro hExact
          simpa [hExact] using hHiSample T)
  exact hCutToStop.trans hRawRow

/-- Helper for Theorem 25.38: once every strict-mono clipped-horizon row family admits a further
strict-mono refinement converging to the clipped canonical value, the exact/non-partition
boundary-error lemmas transport that limit to the after-exit moving-horizon rows. -/
private theorem rawMovingHorizon_tendsto_clippedCanonical_afterExit_theorem25_38
    {F0 : State → ℝ} (hF0 : ContDiff ℝ 2 F0)
    {Xω : VectorPathSpace d}
    (i : Fin d) {t Tω : NNReal} (hTω_lt_t : Tω < t)
    {L : ℝ}
    (hL :
      L =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          Tω)
    (hRefine :
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                Tω
                (φ (ψ n)))
            atTop
            (𝓝 L)) :
    Tendsto
      (fun row ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          (afterExitMovingHorizon_theorem25_38 row Tω t)
          row)
      atTop
      (𝓝 L) := by
  have hCoeffCont : Continuous fun s : NNReal ↦ (∂[i] F0) (Xω s) := by
    -- Proof comment: both after-exit transport branches only use continuity of the translated
    -- coefficient along the fixed centered path.
    exact (continuousPartialDeriv_theorem25_38 F0 hF0 i).comp Xω.continuous
  refine tendstoAtTopOfStrictMonoSubseqTendsto_theorem25_38 ?_
  intro φ hφ
  obtain hExact | hNonPart :=
    exists_strictMono_refinement_partition_or_nonPartition_theorem25_38
      Definition2158.dyadicPartitionSequence
      (φ := φ)
      Tω
  · rcases hExact with ⟨ψ, hψ, hExactRows⟩
    let clipped : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        Tω
        (φ (ψ n))
    let moving : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        (afterExitMovingHorizon_theorem25_38 (φ (ψ n)) Tω t)
        (φ (ψ n))
    let κ : ℕ → ℕ := fun n ↦
      partitionBoundIndex Definition2158.dyadicPartitionSequence (φ (ψ n)) Tω
    have hκ :
        ∀ n : ℕ,
          Tω = Definition2158.dyadicPartitionSequence (φ (ψ n)) (κ n) := by
      intro n
      simpa [κ] using hExactRows n
    have hκ_lt :
        ∀ n : ℕ,
          κ n < partitionBoundIndex Definition2158.dyadicPartitionSequence (φ (ψ n)) t := by
      intro n
      have hpoint_lt_t :
          Definition2158.dyadicPartitionSequence (φ (ψ n)) (κ n) < t := by
        rw [← hκ n]
        exact hTω_lt_t
      exact
        lt_partitionBoundIndex_of_partitionPoint_lt_time
          Definition2158.dyadicPartitionSequence
          (φ (ψ n))
          (κ n)
          t
          hpoint_lt_t
    have hBase :
        Tendsto clipped atTop (𝓝 L) := by
      -- Proof comment: the exact-partition branch uses the caller-supplied clipped-horizon
      -- refinement package on the composed selector `φ ∘ ψ`.
      simpa [clipped, Function.comp] using hRefine (φ ∘ ψ) (hφ.comp hψ)
    have hMovingEq :
        moving =
          fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              (partitionNextPointUpTo
                Definition2158.dyadicPartitionSequence
                (φ (ψ n))
                (κ n)
                t)
              (φ (ψ n)) := by
      funext n
      simp [moving, κ, afterExitMovingHorizon_theorem25_38, hκ n]
    have hError :
        Tendsto (fun n ↦ moving n - clipped n) atTop (𝓝 0) := by
      rw [hMovingEq]
      -- Proof comment: in the exact-partition branch, the moving horizon differs from the
      -- clipped horizon only by the one-step exact-successor boundary increment.
      simpa [clipped, Function.comp] using
        rawCoordinateExactSuccessorError_tendsto_zero_afterExit_theorem25_38
          (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (X := vectorPathComponent Xω i)
          (φ := φ ∘ ψ)
          (κ := κ)
          (hφ := hφ.comp hψ)
          (T := Tω)
          (t := t)
          hκ
          hκ_lt
    have hTransport :
        Tendsto moving atTop (𝓝 L) := by
      have hCombined :
          Tendsto
            (fun n ↦ clipped n + (moving n - clipped n))
            atTop
            (𝓝 (L + 0)) :=
        hBase.add hError
      -- Proof comment: add back the vanishing exact-successor boundary error to transport the
      -- clipped-horizon limit to the moving-horizon raw rows.
      convert hCombined using 1
      · ext n
        ring
      · simp
    exact ⟨ψ, hψ, hTransport⟩
  · rcases hNonPart with ⟨ψ, hψ, hNonPartRows⟩
    let clipped : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        Tω
        (φ (ψ n))
    let moving : ℕ → ℝ := fun n ↦
      partitionPathwiseItoApproximationUpTo
        (fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (vectorPathComponent Xω i)
        Definition2158.dyadicPartitionSequence
        (afterExitMovingHorizon_theorem25_38 (φ (ψ n)) Tω t)
        (φ (ψ n))
    have hBase :
        Tendsto clipped atTop (𝓝 L) := by
      -- Proof comment: the non-partition branch uses the same universal clipped-horizon
      -- refinement input; only the boundary-error normalization changes.
      simpa [clipped, Function.comp] using hRefine (φ ∘ ψ) (hφ.comp hψ)
    have hMovingEq :
        moving =
          fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              (partitionNextPointUpTo
                Definition2158.dyadicPartitionSequence
                (φ (ψ n))
                (partitionBoundIndex
                  Definition2158.dyadicPartitionSequence
                  (φ (ψ n))
                  Tω - 1)
                t)
              (φ (ψ n)) := by
      funext n
      have hNotExact :
          ¬ Tω =
            Definition2158.dyadicPartitionSequence
              (φ (ψ n))
              (partitionBoundIndex
                Definition2158.dyadicPartitionSequence
                (φ (ψ n))
                Tω) := by
        exact ne_of_lt (hNonPartRows n)
      simp [moving, afterExitMovingHorizon_theorem25_38, hNotExact]
    have hError :
        Tendsto (fun n ↦ moving n - clipped n) atTop (𝓝 0) := by
      rw [hMovingEq]
      -- Proof comment: in the non-partition branch, the moving horizon stays in the same active
      -- dyadic cell as `Tω`, so the only difference is the same-cell boundary increment.
      simpa [clipped, Function.comp] using
        rawCoordinateNonPartitionSuccessorError_tendsto_zero_afterExit_theorem25_38
          (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
          hCoeffCont
          (X := vectorPathComponent Xω i)
          (φ := φ ∘ ψ)
          (hφ := hφ.comp hψ)
          (T := Tω)
          (t := t)
          hTω_lt_t
          hNonPartRows
    have hTransport :
        Tendsto moving atTop (𝓝 L) := by
      have hCombined :
          Tendsto
            (fun n ↦ clipped n + (moving n - clipped n))
            atTop
            (𝓝 (L + 0)) :=
        hBase.add hError
      -- Proof comment: add back the vanishing same-cell boundary error to transport the
      -- clipped-horizon limit to the moving-horizon raw rows.
      convert hCombined using 1
      · ext n
        ring
      · simp
    exact ⟨ψ, hψ, hTransport⟩

/-- Helper for Theorem 25.38: once the coordinate coefficient is deterministically cut off at the
sample-specific horizon `T`, the canonical cutoff coordinate should be frozen at every later time.
-/
private theorem constCutoffCanonicalCoordinate_freeze_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ} {B : VectorProcess}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hFcontDiff : ContDiff ℝ 2 F)
    {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ B t ω)
    (hω : ∀ t : NNReal, B t ω = W t ω - x)
    (i : Fin d) {T U' : NNReal}
    (hT : (T : ENNReal) = hittingAfter W Uᶜ 0 ω)
    (hTU : T < U')
    (hIto :
      let F0 : State → ℝ := fun z : State ↦ F (x + z)
      let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
      ∃ I : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          I) :
    let F0 : State → ℝ := fun z : State ↦ F (x + z)
    let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        (hittingAfter W Uᶜ 0)
    let HiCut : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (T : ENNReal))
    ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut U' ω =
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut T ω := by
  intro F0 Xω ℱW Zi hZi Hi HiCut
  have hF0 : ContDiff ℝ 2 F0 := by
    -- Proof comment: the theorem-local raw coefficient is the translated `F`, so its regularity
    -- is exactly the translated `ContDiff` package already available in the file.
    simpa [F0] using translatedContDiff_theorem25_38 (F := F) hFcontDiff x
  have hT_le :
      (T : ENNReal) ≤ hittingAfter W Uᶜ 0 ω := by
    simpa [hT] using le_rfl
  have hCanonicalAtClipped :
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut T ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
    have hCanonicalHi :
        ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi T ω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := by
      -- Proof comment: first rewrite the stochastic canonical coordinate to its dyadic pathwise
      -- spelling along the fixed centered sample path.
      simpa [ℱW, Zi, hZi, Hi, Xω] using
        canonicalCoordinate_apply_eq_stoppedCenteredPathwiseItoIntegral_theorem25_38
          (μ := μ) (W := W) (x := x) (U := U) (F := F) (B := B)
          hW hWcont ω hcontω hω i T
    have hRows :
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T
            n) =
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              T
              n) := by
      funext n
      -- Proof comment: on the clipped interval `[0, T]`, the theorem-local stopped coefficient
      -- is exactly the raw translated partial derivative along the centered sample path.
      exact
        partitionPathwiseItoApproximationUpTo_eq_of_leftEndpointEq_theorem25_38
          (P := Definition2158.dyadicPartitionSequence)
          (X := vectorPathComponent Xω i)
          (T := T)
          (row := n)
          (hKL := by
            intro j hj
            have hs_le_T :
                Definition2158.dyadicPartitionSequence n j ≤ T := by
              exact
                (partitionPoint_mem_Icc_of_lt_truncationBoundIndex
                  Definition2158.dyadicPartitionSequence
                  n
                  j
                  T
                  hj).2
            have hs_le_exit :
                ((Definition2158.dyadicPartitionSequence n j : NNReal) : ENNReal) ≤
                  hittingAfter W Uᶜ 0 ω := by
              exact le_trans (by exact_mod_cast hs_le_T) hT_le
            calc
              Hi (Definition2158.dyadicPartitionSequence n j) ω =
                  (∂[i] F) (x + B (Definition2158.dyadicPartitionSequence n j) ω) := by
                exact
                  stoppedCoordinatePartial_beforeExit_eq_theorem25_38
                    (W := W) (x := x) (U := U) (F := F) (B := B) (ω := ω)
                    hω i hs_le_exit
              _ = (∂[i] F) (x + Xω (Definition2158.dyadicPartitionSequence n j)) := by
                    simp [Xω]
              _ = (∂[i] F0) (Xω (Definition2158.dyadicPartitionSequence n j)) := by
                    symm
                    exact
                      translatedPartialDeriv_eq_theorem25_38
                        (F := F)
                        (hF := hFcontDiff.differentiable (by norm_num))
                        x
                        (Xω (Definition2158.dyadicPartitionSequence n j))
                        i))
    have hPathwiseEq :
        pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := by
      -- Proof comment: equality of the whole clipped dyadic row family identifies the two
      -- canonical `pathwiseItoIntegralAlong` values.
      rw [pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
      exact congrArg (limUnder atTop) hRows
    calc
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut T ω =
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi T ω := by
            exact
              continuousLocalMartingaleItoIntegralProcess_eq_constCutoffValue_theorem25_38
                (μ := (μ : Measure Ω))
                (ℱ := ℱW)
                (M := Zi)
                (H := Hi)
                (hM := hZi)
                T
                ω
      _ =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := hCanonicalHi
      _ =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T := hPathwiseEq
  have hMovingRows :
      (fun row ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ HiCut s ω)
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          U'
          row) =
        fun row ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            (afterExitMovingHorizon_theorem25_38 row T U')
            row := by
    funext row
    -- Proof comment: after the exit time, every theorem-local cutoff row at horizon `U'`
    -- matches the raw moving-horizon row on the same dyadic level.
    simpa [F0, Xω, Hi, HiCut] using
      constCutoffCoordinateRows_eq_rawMovingHorizon_afterExit_theorem25_38
        (W := W) (x := x) (U := U) (F := F) (B := B) (ω := ω)
        hcontω
        hω
        (hFcontDiff.differentiable (by norm_num))
        i
        (T := T)
        (U' := U')
        hT
        hTU
        row
  have hMovingLimit :
      Tendsto
        (fun row ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            (afterExitMovingHorizon_theorem25_38 row T U')
            row)
        atTop
        (𝓝
          (pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            T)) := by
    have hRefine :
        ∀ φ : ℕ → ℕ, StrictMono φ →
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T
                  (φ (ψ n)))
              atTop
              (𝓝
                (pathwiseItoIntegralAlong
                  (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                  (vectorPathComponent Xω i)
                  Definition2158.dyadicPartitionSequence
                  T)) := by
      intro φ hφ
      refine ⟨id, strictMono_id, ?_⟩
      -- Proof comment: a genuine pathwise witness on the fixed centered path already gives
      -- convergence of every strict-mono clipped row family to the same canonical value.
      simpa [Function.comp] using
        rawClippedCoordinateRows_tendsto_alongStrictMono_of_hasPathwiseWitness_theorem25_38
          (F := F0)
          (X := Xω)
          i
          T
          (hφ := hφ)
          (by simpa [F0, Xω] using hIto)
    -- Proof comment: convert the deterministic witness into the refinement package expected by
    -- the moving-horizon transport lemma, then reuse the exact/non-partition boundary control.
    exact
      rawMovingHorizon_tendsto_clippedCanonical_afterExit_theorem25_38
        (F0 := F0)
        hF0
        i
        hTU
        rfl
        hRefine
  have hCanonicalAtLater :
      ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut U' ω =
        pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          T := by
    have hCutLimit :
        Tendsto
          (fun row ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ HiCut s ω)
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              U'
              row)
          atTop
          (𝓝
            (pathwiseItoIntegralAlong
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              T)) := by
      -- Proof comment: rewrite the visible cutoff row family to the raw moving-horizon family
      -- and reuse the after-exit transport limit.
      rw [hMovingRows]
      exact hMovingLimit
    -- Proof comment: once the theorem-local cutoff row family has a genuine limit, the canonical
    -- fixed-time owner at `U'` is exactly that limit.
    rw [ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess]
    exact pathwiseItoIntegralAlong_eq_of_tendsto U' hCutLimit
  -- Proof comment: both the later deterministic cutoff value and the clipped-horizon value are
  -- now identified with the same raw clipped canonical limit.
  exact hCanonicalAtLater.trans hCanonicalAtClipped.symm

/-- Helper for Theorem 25.38: the translated diagonal Hessian correction on the clipped horizon
is exactly the stopped Laplacian integral on `[0, t]`. -/
private theorem translatedDiagIntegral_eq_stoppedLaplacianIntegral_theorem25_38
    {x : State} {F : State → ℝ} {B : VectorProcess} {τ : Ω → ENNReal}
    {ω : Ω} {Xω : VectorPathSpace d} {t Tω : NNReal}
    (hFcontDiff : ContDiff ℝ 2 F)
    (hXω : ∀ s : NNReal, Xω s = B s ω)
    (hTω_coe : (Tω : ENNReal) = min (t : ENNReal) (τ ω))
    (hTω_le : (Tω : ENNReal) ≤ τ ω) :
    ((1 : ℝ) / 2) *
        ∑ i : Fin d,
          ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ),
            (∂²[i, i] (fun z : State ↦ F (x + z))) (Xω s.toNNReal)
      =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x + B s ω))
              τ
              u.toNNReal
              ω := by
  let F0 : State → ℝ := fun z : State ↦ F (x + z)
  have hF0 : ContDiff ℝ 2 F0 := by
    simpa [F0] using translatedContDiff_theorem25_38 (F := F) hFcontDiff x
  let rawLap : ℝ → ℝ := fun s ↦ ((1 : ℝ) / 2) * Δ F (x + B s.toNNReal ω)
  let stoppedLap : ℝ → ℝ := fun s ↦
    ((1 : ℝ) / 2) *
      ProbabilityTheory.processBeforeStoppingTime
        (fun u ω ↦ Δ F (x + B u ω))
        τ
        s.toNNReal
        ω
  have hTω_le_t : Tω ≤ t := by
    have hle : (Tω : ENNReal) ≤ (t : ENNReal) := by
      rw [hTω_coe]
      exact min_le_left _ _
    exact_mod_cast hle
  have hDiagTermInt :
      ∀ i : Fin d,
        IntegrableOn
          (fun s : ℝ ↦ (∂²[i, i] F0) (Xω s.toNNReal))
          (Set.Icc (0 : ℝ) (Tω : ℝ)) := by
    intro i
    have hCont :
        Continuous fun s : ℝ ↦ (∂²[i, i] F0) (Xω s.toNNReal) := by
      -- Proof comment: the translated second partial derivative is continuous and the fixed
      -- sample path stays continuous after composing with `Real.toNNReal`.
      exact
        (continuous_secondPartialDeriv F0 hF0 i i).comp
          (Xω.continuous.comp continuous_real_toNNReal)
    simpa using hCont.integrableOn_Icc
  have hDiagIntegrand :
      (fun s : ℝ ↦ ∑ i : Fin d, (∂²[i, i] F0) (Xω s.toNNReal)) =
        fun s : ℝ ↦ Δ F (x + B s.toNNReal ω) := by
    funext s
    calc
      ∑ i : Fin d, (∂²[i, i] F0) (Xω s.toNNReal)
          = ∑ i : Fin d, (∂²[i, i] F) (x + Xω s.toNNReal) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              symm
              exact
                translatedSecondPartialDeriv_eq_theorem25_38
                  (F := F) hFcontDiff x (Xω s.toNNReal) i i
      _ = Δ F (x + Xω s.toNNReal) := by
            symm
            exact laplacian_eq_sum_secondPartialDeriv F hFcontDiff (x + Xω s.toNNReal)
      _ = Δ F (x + B s.toNNReal ω) := by
            rw [hXω s.toNNReal]
  have hIndicatorSubset :
      Set.Icc (0 : ℝ) (Tω : ℝ) ⊆ Set.Icc (0 : ℝ) (t : ℝ) := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hTω_le_t⟩
  have hIndicatorEq :
      Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) stoppedLap =
        Set.indicator (Set.Icc (0 : ℝ) (Tω : ℝ)) rawLap := by
    funext s
    by_cases hsTω : s ∈ Set.Icc (0 : ℝ) (Tω : ℝ)
    · have hs_toNNReal_le_Tω : s.toNNReal ≤ Tω := by
        exact (Real.toNNReal_le_iff_le_coe).2 hsTω.2
      have hs_le_exit : (s.toNNReal : ENNReal) ≤ τ ω := by
        exact le_trans (by exact_mod_cast hs_toNNReal_le_Tω) hTω_le
      have hs_mem_t : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := hIndicatorSubset hsTω
      -- Proof comment: on the clipped interval `[0, Tω]`, the stopping cutoff is inactive and
      -- both indicator-restricted integrands spell the same translated Laplacian term.
      simp [Set.indicator, hsTω, hs_mem_t, stoppedLap, rawLap,
        ProbabilityTheory.processBeforeStoppingTime_apply, hs_le_exit]
    · by_cases hst : s ∈ Set.Icc (0 : ℝ) (t : ℝ)
      · have hs_nonneg : 0 ≤ s := hst.1
        have hs_not_le_Tω : ¬ s ≤ Tω := by
          intro hs_le_Tω
          exact hsTω ⟨hs_nonneg, hs_le_Tω⟩
        have hs_not_le_exit :
            ¬ (s.toNNReal : ENNReal) ≤ τ ω := by
          intro hs_le_exit
          have hs_toNNReal_le_t : s.toNNReal ≤ t := by
            exact (Real.toNNReal_le_iff_le_coe).2 hst.2
          have hs_toNNReal_le_Tω : s.toNNReal ≤ Tω := by
            have hmin :
                (s.toNNReal : ENNReal) ≤ (Tω : ENNReal) := by
              rw [hTω_coe]
              exact le_min (by exact_mod_cast hs_toNNReal_le_t) hs_le_exit
            exact_mod_cast hmin
          have hs_le_Tω : s ≤ Tω := by
            simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le_Tω
          exact hs_not_le_Tω hs_le_Tω
        -- Proof comment: on `(Tω, t]`, the stopped integrand is forced to zero because the
        -- clipped horizon has already passed the exit time.
        simp [Set.indicator, hsTω, hst, stoppedLap, rawLap,
          ProbabilityTheory.processBeforeStoppingTime_apply, hs_not_le_exit]
      · simp [Set.indicator, hsTω, hst, stoppedLap, rawLap]
  -- Proof comment: collapse the diagonal sum to the Laplacian of `F` along the centered path and
  -- then absorb the deterministic cutoff into the stopped indicator on `[0, t]`.
  calc
    ((1 : ℝ) / 2) *
        ∑ i : Fin d,
          ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), (∂²[i, i] F0) (Xω s.toNNReal)
        =
          ((1 : ℝ) / 2) *
            ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ),
              ∑ i : Fin d, (∂²[i, i] F0) (Xω s.toNNReal) := by
            rw [← integral_finset_sum Finset.univ hDiagTermInt]
    _ = ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), rawLap s := by
          rw [← integral_const_mul]
          congr 1
          exact hDiagIntegrand
    _ = ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) (Tω : ℝ)) rawLap s := by
          rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) stoppedLap s := by
          rw [hIndicatorEq.symm]
    _ =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x + B s ω))
              τ
              u.toNNReal
              ω := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
          rfl

/-- Helper for Theorem 25.38: once the samplewise stopped-Itô identity is isolated, the
finite-horizon `EqUpTo` theorem becomes a pure packaging step. -/
private theorem vectorPathComponent_mem_𝒞_qvAlong_of_mem_𝒞_qv_d_theorem25_38
    {X : VectorPathSpace d} (hX : X ∈ (𝒞_qv^d)) (i : Fin d) :
    vectorPathComponent X i ∈ 𝒞_qvAlong Definition2158.dyadicPartitionSequence := by
  rcases (mem_𝒞_qv_d_iff_exists_family X).mp hX with ⟨cov, hcov⟩
  refine (mem_𝒞_qvAlong_iff _).2 ?_
  refine ⟨cov i i, ?_⟩
  -- Proof comment: the scalar coordinate path inherits continuous square variation from its
  -- self-covariation inside the good-path family attached to `X ∈ 𝒞_qv^d`.
  simpa using
    hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self (hcov i i)

/-- Helper for Theorem 25.38: on a fixed good centered path, the translated `i`-th coordinate
integrand should admit a genuine pathwise Itô witness against the corresponding coordinate path.
-/
private theorem coordinatePathwiseItoWitness_onGoodCenteredPath_theorem25_38
    {F : State → ℝ}
    (hF : ContDiff ℝ 2 F)
    {X : VectorPathSpace d}
    (hX : X ∈ (𝒞_qv^d))
    (i : Fin d) :
    ∃ I : NNReal → ℝ,
      HasPathwiseItoIntegralAlong
        (fun s : NNReal ↦ (∂[i] F) (X s))
        (vectorPathComponent X i)
        Definition2158.dyadicPartitionSequence
        I := by
  -- Route correction: the old stochastic all-cutoffs theorem was the wrong frontier. The live
  -- blocker is this deterministic good-path witness, which should let the fixed-sample freeze
  -- theorem use ordinary pathwise convergence instead of uncountable AE uniformization.
  -- TODO: derive the witness from the scalar `𝒞_qvAlong` owner of `vectorPathComponent X i`
  -- together with the Chapter 25 pathwise Itô API for smooth observables on good paths.
  sorry

/-- Helper for Theorem 25.38: if the centered coordinate integral already has a chosen pathwise
Itô realization on a fixed good path, then the clipped dyadic rows converge to the canonical
owner at that horizon. -/
private theorem rawClippedCoordinateRows_tendsto_onGoodCenteredPath_of_hasPathwiseWitness_theorem25_38
    {F : State → ℝ} {X : VectorPathSpace d}
    (i : Fin d) (T : NNReal)
    (hIto :
      ∃ I : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (X s))
          (vectorPathComponent X i)
          Definition2158.dyadicPartitionSequence
          I) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F) (X s))
          (vectorPathComponent X i)
          Definition2158.dyadicPartitionSequence
          T
          n)
      atTop
      (𝓝
        (pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (X s))
          (vectorPathComponent X i)
          Definition2158.dyadicPartitionSequence
          T)) := by
  rcases hIto with ⟨I, hI⟩
  -- Proof comment: once the coordinate integral has any chosen pathwise realization, the
  -- canonical `pathwiseItoIntegralAlong` is that realization and inherits its fixed-horizon
  -- convergence statement.
  simpa [hI.eq_pathwiseItoIntegralAlong] using hI.tendsto T

/-- Helper for Theorem 25.38: a strict-mono reindexing preserves any already established
fixed-horizon convergence of the clipped coordinate rows. -/
private theorem
    rawClippedCoordinateRows_tendsto_alongStrictMono_of_hasPathwiseWitness_theorem25_38
    {F : State → ℝ} {X : VectorPathSpace d}
    (i : Fin d) (T : NNReal)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hIto :
      ∃ I : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (X s))
          (vectorPathComponent X i)
          Definition2158.dyadicPartitionSequence
          I) :
    Tendsto
      (fun n ↦
        partitionPathwiseItoApproximationUpTo
          (fun s : NNReal ↦ (∂[i] F) (X s))
          (vectorPathComponent X i)
          Definition2158.dyadicPartitionSequence
          T
          (φ n))
      atTop
      (𝓝
        (pathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F) (X s))
          (vectorPathComponent X i)
          Definition2158.dyadicPartitionSequence
          T)) := by
  -- Proof comment: reindex the convergent full dyadic row family along the strict-mono selector
  -- `φ`; the limit stays unchanged.
  exact
    (rawClippedCoordinateRows_tendsto_onGoodCenteredPath_of_hasPathwiseWitness_theorem25_38
      (F := F) (X := X) i T hIto).comp hφ.tendsto_atTop

/-- Helper for Theorem 25.38: on the diagonal, a square-variation witness is already the matching
quadratic-covariation witness. -/
private theorem selfContinuousQuadraticCovariation_of_squareVariation_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M A : NNReal → Ω → ℝ}
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) :
    IsContinuousQuadraticCovariationProcess ℱ μ M M A := by
  refine
    { zero := hA.zero
      adapted := hA.adapted
      continuous := hA.continuous
      locally_finite_variation := hA.locally_finite_variation
      local_martingale_mul_sub := ?_ }
  -- Proof comment: on the diagonal, the compensated product `M * M - A` is exactly the
  -- square-variation local martingale `M^2 - A`.
  simpa using hA.local_martingale_sq_sub

/-- Helper for Theorem 25.38: if two continuous local martingales share the same square-variation
witness and the same quadratic-covariation witness, then their difference has zero square
variation. -/
private theorem sub_zeroSquareVariation_of_sharedWitness_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A) :
    IsContinuousSquareVariationProcess ℱ μ
      (fun t ω ↦ M t ω - N t ω)
      (fun _ _ ↦ (0 : ℝ)) := by
  refine
    { zero := ?_
      adapted := ?_
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · funext ω
    simp
  · intro t
    simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
  · intro ω
    simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · intro ω s t hst
    simp
  · have hQuadCont :
        IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω) := by
      refine ⟨hQuad.local_martingale_mul_sub, ?_⟩
      intro ω
      exact (hMmart.continuous ω).mul (hNmart.continuous ω) |>.sub (hQuad.continuous ω)
    refine
      { local_martingale := ?_
        continuous := ?_ }
    · let hDoubleQuad : IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            (M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)) :=
          isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hQuadCont hQuadCont
      have hTarget :
          IsContinuousLocalMartingale ℱ μ
            (fun t ω ↦
              (M t ω ^ 2 - A t ω) +
                ((N t ω ^ 2 - A t ω) -
                  ((M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)))) :=
        isContinuousLocalMartingale_addLocal
          (ℱ := ℱ)
          (μ := μ)
          hAleft.local_martingale_sq_sub
          (isContinuousLocalMartingale_subLocal
            (ℱ := ℱ)
            (μ := μ)
            hAright.local_martingale_sq_sub
            hDoubleQuad)
      convert hTarget.local_martingale using 1
      funext t ω
      ring
    · intro ω
      let hDoubleQuad : IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            (M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)) :=
          isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hQuadCont hQuadCont
      let hTarget :
          IsContinuousLocalMartingale ℱ μ
            (fun t ω ↦
              (M t ω ^ 2 - A t ω) +
                ((N t ω ^ 2 - A t ω) -
                  ((M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)))) :=
        isContinuousLocalMartingale_addLocal
          (ℱ := ℱ)
          (μ := μ)
          hAleft.local_martingale_sq_sub
          (isContinuousLocalMartingale_subLocal
            (ℱ := ℱ)
            (μ := μ)
            hAright.local_martingale_sq_sub
            hDoubleQuad)
      simpa using hTarget.continuous ω

/-- Helper for Theorem 25.38: a continuous local martingale with zero square variation is almost
surely zero at every deterministic time once its initial value vanishes almost surely. -/
private theorem ae_eq_zero_at_time_of_zeroSquareVariation_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hXsq : IsContinuousSquareVariationProcess ℱ μ X (fun _ _ ↦ (0 : ℝ)))
    (hX0 : X 0 =ᵐ[μ] fun _ : Ω ↦ 0)
    (T : NNReal) :
    X T =ᵐ[μ] fun _ : Ω ↦ 0 := by
  rcases _root_.ProbabilityTheory.existsUnique_continuousSquareVariationProcess
      (ℱ := ℱ) (μ := μ) hX with
    ⟨B, _hB, huniq⟩
  have hCanonEqB :
      AreIndistinguishable μ (⟨X⟩[hX]) B := by
    exact huniq _ (continuousSquareVariationProcess_spec hX)
  have hBEqZero :
      AreIndistinguishable μ B (fun _ _ ↦ (0 : ℝ)) := by
    exact huniq _ hXsq
  have hCanonEqZero :
      AreIndistinguishable μ (⟨X⟩[hX]) (fun _ _ ↦ (0 : ℝ)) := by
    exact areIndistinguishable_trans hCanonEqB hBEqZero
  have hZeroAllTimes :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0 := by
    rcases hCanonEqZero with ⟨bad, _hbad_meas, hbad_null, hbad_sub⟩
    have hbad_ae : ∀ᵐ ω ∂μ, ω ∉ bad :=
      compl_mem_ae_iff.mpr hbad_null
    filter_upwards [hbad_ae] with ω hωbad t
    by_contra hneq
    exact hωbad (hbad_sub t hneq)
  have hConstAtTime :
      X T =ᵐ[μ] X 0 :=
    ae_eq_initial_at_time_of_ae_squareVariation_eq_zero ℱ hX hZeroAllTimes T
  exact hConstAtTime.trans hX0

/-- Helper for Theorem 25.38: shared square-variation and quadratic-covariation witnesses force
two continuous local martingales to agree almost surely at any fixed deterministic time once
their initial values agree. -/
private theorem ae_eq_at_time_of_sharedWitness_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hZero : M 0 =ᵐ[μ] N 0)
    (T : NNReal) :
    M T =ᵐ[μ] N T := by
  have hSubSq :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦ M t ω - N t ω)
        (fun _ _ ↦ (0 : ℝ)) :=
    sub_zeroSquareVariation_of_sharedWitness_theorem25_38
      hMmart hNmart hAleft hAright hQuad
  have hSubZero :
      (fun ω ↦ M 0 ω - N 0 ω) =ᵐ[μ] fun _ : Ω ↦ 0 := by
    -- Proof comment: the shared initial-value hypothesis turns the difference process into a
    -- zero-start continuous local martingale.
    filter_upwards [hZero] with ω hω
    simp [hω]
  have hSubAtTime :
      (fun ω ↦ M T ω - N T ω) =ᵐ[μ] fun _ : Ω ↦ 0 :=
    ae_eq_zero_at_time_of_zeroSquareVariation_theorem25_38
      (ℱ := ℱ)
      (μ := μ)
      (X := fun t ω ↦ M t ω - N t ω)
      (isContinuousLocalMartingale_subLocal (ℱ := ℱ) (μ := μ) hMmart hNmart)
      hSubSq
      hSubZero
      T
  -- Proof comment: once the difference vanishes almost surely at time `T`, the endpoint values
  -- must agree there.
  filter_upwards [hSubAtTime] with ω hω
  exact sub_eq_zero.mp hω

/-- Helper for Theorem 25.38: a deterministic cutoff already freezes its bracket witness after
the cutoff horizon. -/
private theorem constCutoffBracket_eq_stoppedConstTime_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal) :
    stoppedProcess
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))))
        (fun _ ↦ (T : ENNReal)) =
      bracketDensityIntegralUpTo hbr
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))) := by
  funext t ω
  by_cases ht : t ≤ T
  · -- Proof comment: before `T`, the deterministic stop evaluates the same bracket witness at
    -- the current time.
    simp [stoppedProcessConstTime_eq_min, min_eq_left ht]
  · have hTt : T ≤ t := le_of_not_ge ht
    have hTt_real : (T : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hTt
    let f : ℝ → ℝ := fun s ↦
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
        (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ)
    have hCutoffZero :
        ∀ ⦃s : ℝ⦄, s ∈ Set.Icc (0 : ℝ) (t : ℝ) →
          ¬ s ∈ Set.Icc (0 : ℝ) (T : ℝ) →
            f s = 0 := by
      intro s hs hs_not_mem
      have hsT : ¬ s ≤ (T : ℝ) := by
        intro hs_le_T
        exact hs_not_mem ⟨hs.1, hs_le_T⟩
      have hs_not_cutoff : ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
        intro hs_cutoff
        exact hsT ((Real.toNNReal_le_iff_le_coe).1 (by exact_mod_cast hs_cutoff))
      -- Proof comment: beyond `T`, the deterministic cutoff forces the bracket-density
      -- integrand itself to vanish.
      simp [f, ProbabilityTheory.processBeforeStoppingTime_apply, hs_not_cutoff]
    have hIndicatorEq :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), f s) =
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := by
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro s hs
      by_cases hs_mem : s ∈ Set.Icc (0 : ℝ) (T : ℝ)
      · simp [Set.indicator_of_mem, hs_mem]
      · simp [Set.indicator_of_notMem, hs_mem, hCutoffZero hs hs_mem]
    have hSubset :
        Set.Icc (0 : ℝ) (T : ℝ) ⊆ Set.Icc (0 : ℝ) (t : ℝ) := by
      intro s hs
      exact ⟨hs.1, hs.2.trans hTt_real⟩
    have hFreeze :
        bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
            t
            ω =
          bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
            T
            ω := by
      -- Proof comment: after rewriting the later-horizon integral by the indicator of `[0,T]`,
      -- only the original interval `[0,T]` remains.
      simpa [bracketDensityIntegralUpTo, f] using
        (calc
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), f s =
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
                Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := hIndicatorEq
          _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s := by
            rw [integral_indicator measurableSet_Icc]
            simp [Measure.restrict_restrict, Set.inter_eq_right.mpr hSubset, measurableSet_Icc])
    -- Proof comment: once the bracket witness is constant after `T`, stopping it at `T` leaves
    -- the same process.
    calc
      stoppedProcess
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal))))
          (fun _ ↦ (T : ENNReal))
          t
          ω =
        bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          T
          ω := by
            simp [stoppedProcessConstTime_eq_min, min_eq_right hTt]
      _ =
        bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
          t
          ω := hFreeze.symm

/-- Helper for Theorem 25.38: if two continuous compensators agree up to `T` off one null set and
are both frozen after `T`, then they agree for all deterministic times off one null set. -/
private theorem ae_eq_allTimes_of_eqUpTo_and_frozen_after_theorem25_38
    {μ : Measure Ω} {A B : NNReal → Ω → ℝ}
    {T : NNReal}
    (hEq : EqUpTo μ T A B)
    (hAfreeze :
      ∀ ω : Ω, ∀ t : NNReal, T ≤ t → A t ω = A T ω)
    (hBfreeze :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → B t ω = B T ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEq with
    ⟨S, _hSmeas, hSnull, hSeq⟩
  have hSae : ∀ᵐ ω ∂μ, ω ∉ S :=
    compl_mem_ae_iff.mpr hSnull
  filter_upwards [hSae, hBfreeze] with ω hωS hBω t
  by_cases ht : t ≤ T
  · exact hSeq ht hωS
  · have hTt : T ≤ t := le_of_not_ge ht
    -- Proof comment: above `T`, both compensators collapse to their terminal time-`T` value.
    calc
      A t ω = A T ω := hAfreeze ω t hTt
      _ = B T ω := hSeq le_rfl hωS
      _ = B t ω := (hBω t hTt).symm

/-- Helper for Theorem 25.38: an all-times almost-sure compensator identity transports a genuine
quadratic-covariation witness to the replacement compensator. -/
private theorem continuousQuadraticCovariation_of_ae_eq_allTimes_compensator_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A B : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hCovB : IsContinuousQuadraticCovariationProcess ℱ μ M N B)
    (hAzero : A 0 = 0)
    (hAadapted : Adapted ℱ A)
    (hAcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ A t ω)
    (hALFV :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ A t ω, hAcont ω⟩ : C(NNReal, ℝ))
          Set.univ)
    (hABall : ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω) :
    IsContinuousQuadraticCovariationProcess ℱ μ M N A := by
  have hMulAdapted :
      Adapted ℱ (fun t ω ↦ M t ω * N t ω) := by
    exact hM.adapted.mul hN.adapted
  have hMulCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω * N t ω := by
    intro ω
    exact (hM.continuous ω).mul (hN.continuous ω)
  refine
    { zero := hAzero
      adapted := hAadapted
      continuous := hAcont
      locally_finite_variation := hALFV
      local_martingale_mul_sub := ?_ }
  -- Proof comment: once `A` and `B` agree at all deterministic times outside one null set, the
  -- compensated product local martingale transports from `B` to `A`.
  exact
    isLocalMartingale_congr_ae_allTimes_theorem25_38
      hCovB.local_martingale_mul_sub
      (hMulAdapted.sub hAadapted)
      (fun ω ↦ (hMulCont ω).sub (hAcont ω))
      (by
        filter_upwards [hABall] with ω hω t
        simp [hω t])

/-- Helper for Theorem 25.38: once the right path is frozen after `T`, the dyadic mixed row at a
later horizon differs from the horizon-`T` row by one explicit boundary increment. -/
private theorem
    partitionQuadraticCovariationSum_eq_terminal_plus_boundary_of_rightConstAfter_theorem25_38
    {F G : PathSpace}
    {T t : NNReal}
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T)
    (n : ℕ) :
    partitionQuadraticCovariationSum
        Definition2158.dyadicPartitionSequence
        F
        G
        t
        n =
      partitionQuadraticCovariationSum
          Definition2158.dyadicPartitionSequence
          F
          G
          T
          n +
        (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
            F T) *
          (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
  let P := Definition2158.dyadicPartitionSequence
  let K := partitionBoundIndex P n T
  let N := partitionBoundIndex P n t
  let termt : ℕ → ℝ := fun k ↦
    (F (partitionNextPointUpTo P n k t) - F (P n k)) *
      (G (partitionNextPointUpTo P n k t) - G (P n k))
  let termT : ℕ → ℝ := fun k ↦
    (F (partitionNextPointUpTo P n k T) - F (P n k)) *
      (G (partitionNextPointUpTo P n k T) - G (P n k))
  have hKN : K ≤ N := dyadicPartitionBoundIndex_monotone n hTt
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [K, hK0] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by
        simpa [P, Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hle0' bot_le
    subst hT0
    have hsumt_zero :
        partitionQuadraticCovariationSum P F G t n = 0 := by
      rw [partitionQuadraticCovariationSum]
      have htail :
          ∀ k ∈ Finset.range (partitionBoundIndex P n t), termt k = 0 := by
        intro k hk
        have hk_mem :
            P n k ∈ Set.Icc 0 t :=
          Theorem25_22.partitionPoint_mem_Icc_of_lt_partitionBoundIndex
            P n k t (Finset.mem_range.mp hk)
        have hnext_mem :
            partitionNextPointUpTo P n k t ∈ Set.Icc 0 t := by
          constructor
          · exact bot_le
          · simp [partitionNextPointUpTo]
        have hleft : G (P n k) = G 0 := hGconst (P n k) hk_mem.1
        have hright : G (partitionNextPointUpTo P n k t) = G 0 := hGconst _ hnext_mem.1
        -- Proof comment: once the right path is frozen from time `0`, every mixed increment is
        -- zero.
        simp [termt, hleft, hright]
      refine Finset.sum_eq_zero ?_
      intro k hk
      exact htail k hk
    have hsumT_zero :
        partitionQuadraticCovariationSum P F G 0 n = 0 := by
      simp [P, partitionQuadraticCovariationSum, dyadicPartitionBoundIndex_zero]
    -- Proof comment: if `T = 0`, both truncated mixed rows and the boundary factor vanish.
    simp [P, K, hK0, hsumt_zero, hsumT_zero, dyadicSquareVariationBoundaryPoint,
      Definition2158.dyadicPartitionSequence, partitionNextPointUpTo]
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, K = j + 1 := ⟨K - 1, (Nat.sub_add_cancel hKpos).symm⟩
    have hjBoundT : j < K := by
      rw [hj]
      exact Nat.lt_succ_self j
    have hjBoundt : j < N := lt_of_lt_of_le hjBoundT hKN
    have hPj_lt_T : P n j < T := by
      simpa [K] using dyadicPartition_lt_time_of_lt_boundIndex n hjBoundT
    have hPj1_ge_T : T ≤ P n (j + 1) := by
      simpa [K, hj] using le_partitionBoundIndex_time P n T
    have htruncate_t :
        partitionQuadraticCovariationSum P F G t n =
          Finset.sum (Finset.range (j + 1)) termt := by
      rw [partitionQuadraticCovariationSum]
      have hsplit :
          Finset.sum (Finset.range N) termt =
            Finset.sum (Finset.range (j + 1)) termt +
              Finset.sum (Finset.Ico (j + 1) N) termt := by
        symm
        exact Finset.sum_range_add_sum_Ico termt (Nat.succ_le_of_lt hjBoundt)
      have htail :
          Finset.sum (Finset.Ico (j + 1) N) termt = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        have hk_ge : j + 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hPk_ge_T : T ≤ P n k := by
          exact le_trans hPj1_ge_T
            ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone hk_ge)
        have hk_lt_N : k < N := (Finset.mem_Ico.mp hk).2
        have hnext_ge_T : T ≤ partitionNextPointUpTo P n k t := by
          rw [partitionNextPointUpTo]
          exact le_min
            (le_trans hPk_ge_T
              ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone
                (Nat.le_succ k)))
            hTt
        have hleft : G (P n k) = G T := hGconst _ hPk_ge_T
        have hright : G (partitionNextPointUpTo P n k t) = G T := hGconst _ hnext_ge_T
        -- Proof comment: every cell strictly after the boundary cell contributes zero because
        -- the right path is already frozen there.
        simp [termt, hleft, hright]
      rw [hsplit, htail, add_zero]
    have hprefix :
        Finset.sum (Finset.range j) termt =
          Finset.sum (Finset.range j) termT := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk_lt_j : k < j := Finset.mem_range.mp hk
      have hk1_lt_K : k + 1 < K := by
        rw [hj]
        exact Nat.succ_lt_succ hk_lt_j
      have hk1_lt_T : P n (k + 1) < T := by
        simpa [K] using dyadicPartition_lt_time_of_lt_boundIndex n hk1_lt_K
      have hnext_t :
          partitionNextPointUpTo P n k t = P n (k + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (lt_of_lt_of_le hk1_lt_T hTt)
      have hnext_T :
          partitionNextPointUpTo P n k T = P n (k + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt hk1_lt_T
      -- Proof comment: strictly before the boundary cell, the two horizons use the same
      -- successor point.
      simp [termt, termT, hnext_t, hnext_T]
    have htermT_last :
        termT j =
          (F T - F (dyadicSquareVariationBoundaryPoint T n)) *
            (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
      have hnext_T :
          partitionNextPointUpTo P n j T = T := by
        rw [partitionNextPointUpTo, min_eq_right hPj1_ge_T]
      have hboundary :
          dyadicSquareVariationBoundaryPoint T n = P n j := by
        simp [dyadicSquareVariationBoundaryPoint, P, K, hj]
      -- Proof comment: on the last horizon-`T` cell, the right endpoint is exactly `T`.
      simp [termT, hnext_T, hboundary]
    have htermt_last :
        termt j =
          (F (partitionNextPointUpTo P n j t) - F (dyadicSquareVariationBoundaryPoint T n)) *
            (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
      have hnext_ge_T : T ≤ partitionNextPointUpTo P n j t := by
        rw [partitionNextPointUpTo]
        exact le_min
          (le_trans hPj1_ge_T
            ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone
              (Nat.le_succ j)))
          hTt
      have hboundary :
          dyadicSquareVariationBoundaryPoint T n = P n j := by
        simp [dyadicSquareVariationBoundaryPoint, P, K, hj]
      have hfreeze :
          G (partitionNextPointUpTo P n j t) = G T := hGconst _ hnext_ge_T
      -- Proof comment: on the unique boundary cell, only the right increment freezes.
      simp [termt, hfreeze, hboundary]
    have hsumT :
        partitionQuadraticCovariationSum P F G T n =
          Finset.sum (Finset.range j) termT + termT j := by
      simp [partitionQuadraticCovariationSum, K, hj, termT, Finset.sum_range_succ]
    have hsumt :
        partitionQuadraticCovariationSum P F G t n =
          Finset.sum (Finset.range j) termt + termt j := by
      rw [htruncate_t, Finset.sum_range_succ]
    -- Proof comment: after canceling the common prefix, only the explicit boundary increment
    -- remains.
    calc
      partitionQuadraticCovariationSum P F G t n
          = Finset.sum (Finset.range j) termT + termt j := by
              rw [hsumt, hprefix]
      _ = partitionQuadraticCovariationSum P F G T n - termT j + termt j := by
            rw [hsumT]
            ring
      _ = partitionQuadraticCovariationSum P F G T n +
            ((F (partitionNextPointUpTo P n j t) - F T) *
                (G T - G (dyadicSquareVariationBoundaryPoint T n))) := by
            rw [htermT_last, htermt_last]
            ring
      _ = partitionQuadraticCovariationSum P F G T n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n))) := by
            simp [P, K, hj]

/-- Helper for Theorem 25.38: if `T < t`, the clipped successor of the predecessor cell for `T`
at horizon `t` still converges back to `T`. -/
private theorem tendsto_boundarySuccessor_of_lt_theorem25_38
    (t T : NNReal)
    (hTt : T < t) :
    Tendsto
      (fun n ↦
        partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
          t)
      atTop
      (𝓝 T) := by
  let P := Definition2158.dyadicPartitionSequence
  let pred : ℕ → NNReal := fun n ↦ dyadicSquareVariationBoundaryPoint T n
  let succ : ℕ → NNReal := fun n ↦
    partitionNextPointUpTo P n (partitionBoundIndex P n T - 1) t
  have hpred : Tendsto pred atTop (𝓝 T) := tendsto_dyadicSquareVariationBoundaryPoint T
  have hmesh :
      Tendsto (fun n : ℕ ↦ partitionMesh P n) atTop (𝓝 0) :=
    Definition2158.tendsto_partitionMesh_dyadicPartitionSequence
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hεhalf : 0 < ε / 2 := by positivity
  rcases Metric.tendsto_atTop.1 hpred (ε / 2) hεhalf with ⟨N₁, hN₁⟩
  rcases
      (ENNReal.tendsto_atTop_zero.mp hmesh) (ENNReal.ofReal (ε / 2))
        (ENNReal.ofReal_pos.mpr hεhalf) with
    ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hpred_dist : dist (pred n) T < ε / 2 := hN₁ n hn₁
  have hpred_le_T : pred n ≤ T := by
    simpa [pred, dyadicSquareVariationBoundaryPoint, dyadicPartitionPredecessorPoint] using
      dyadicPartitionPredecessorPoint_le_time n T
  have hpred_lt : pred n < t := lt_of_le_of_lt hpred_le_T hTt
  have hpred_lt_bound :
      partitionBoundIndex P n T - 1 < partitionBoundIndex P n t := by
    have hpred_eq :
        pred n = P n (partitionBoundIndex P n T - 1) := by
      rfl
    have hlt :
        P n (partitionBoundIndex P n T - 1) < t := by
      simpa [hpred_eq] using hpred_lt
    exact lt_partitionBoundIndex_of_dyadicPartitionPoint_lt_time n
      (partitionBoundIndex P n T - 1) t hlt
  have hsucc_edist :
      edist (pred n) (succ n) ≤ partitionMesh P n := by
    simpa [pred, succ, P] using
      edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n
        (partitionBoundIndex P n T - 1) t hpred_lt_bound
  have hsucc_dist :
      dist (pred n) (succ n) ≤ ε / 2 := by
    have hmesh_le :
        partitionMesh P n ≤ ENNReal.ofReal (ε / 2) := hN₂ n hn₂
    have hsucc_edist' :
        edist (pred n) (succ n) ≤ ENNReal.ofReal (ε / 2) :=
      le_trans hsucc_edist hmesh_le
    exact
      (ENNReal.ofReal_le_ofReal_iff hεhalf.le).mp
        (by simpa [edist_dist] using hsucc_edist')
  -- Proof comment: the predecessor already converges to `T`, and the successor stays within one
  -- mesh width of that predecessor.
  calc
    dist (succ n) T ≤ dist (succ n) (pred n) + dist T (pred n) :=
      dist_triangle_right (succ n) T (pred n)
    _ < ε / 2 + ε / 2 := by
      exact add_lt_add_of_le_of_lt
        (by simpa [dist_comm] using hsucc_dist)
        (by simpa [dist_comm] using hpred_dist)
    _ = ε := by ring

/-- Helper for Theorem 25.38: if the right path is frozen after `T`, the unique boundary
increment relating the horizon-`t` and horizon-`T` dyadic mixed rows vanishes. -/
private theorem tendsto_boundaryMixedIncrement_zero_of_rightConstAfter_theorem25_38
    {F G : PathSpace}
    {T t : NNReal}
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T) :
    Tendsto
      (fun n ↦
        (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
            F T) *
          (G T - G (dyadicSquareVariationBoundaryPoint T n)))
      atTop
      (𝓝 0) := by
  by_cases hEq : t = T
  · subst hEq
    -- Proof comment: at the terminal horizon itself, the boundary factor is identically zero.
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    rcases Nat.eq_zero_or_pos
        (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) with hidx | hidx
    · have hT0 : T = 0 := by
        have hle0 : T ≤ Definition2158.dyadicPartitionSequence n 0 := by
          simpa [hidx] using
            le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
        have hle0' : T ≤ 0 := by
          simpa [Definition2158.dyadicPartitionSequence] using hle0
        exact le_antisymm hle0' bot_le
      simp [dyadicSquareVariationBoundaryPoint, hidx, hT0]
    · obtain ⟨j, hj⟩ :
          ∃ j : ℕ,
            partitionBoundIndex Definition2158.dyadicPartitionSequence n T = j + 1 :=
          ⟨partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1,
            (Nat.sub_add_cancel hidx).symm⟩
      have hnext :
          partitionNextPointUpTo Definition2158.dyadicPartitionSequence n j T = T := by
        have hT_le :
            T ≤ Definition2158.dyadicPartitionSequence n (j + 1) := by
          simpa [hj] using
            le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
        rw [partitionNextPointUpTo, min_eq_right hT_le]
      simp [hj, hnext]
  · have hLt : T < t := lt_of_le_of_ne hTt (Ne.symm hEq)
    have hsucc :
        Tendsto
          (fun n ↦
            F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t))
          atTop
          (𝓝 (F T)) :=
      F.continuous.continuousAt.tendsto.comp
        (tendsto_boundarySuccessor_of_lt_theorem25_38 t T hLt)
    have hpred :
        Tendsto (fun n ↦ G (dyadicSquareVariationBoundaryPoint T n)) atTop (𝓝 (G T)) :=
      G.continuous.continuousAt.tendsto.comp
        (tendsto_dyadicSquareVariationBoundaryPoint T)
    have hleft :
        Tendsto
          (fun n ↦
            F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) - F T)
          atTop
          (𝓝 0) := by
      simpa using hsucc.sub tendsto_const_nhds
    have hright :
        Tendsto (fun n ↦ G T - G (dyadicSquareVariationBoundaryPoint T n))
          atTop
          (𝓝 0) := by
      simpa using tendsto_const_nhds.sub hpred
    -- Proof comment: both boundary endpoints converge to `T`, so each factor vanishes.
    simpa using hleft.mul hright

/-- Helper for Theorem 25.38: a pathwise quadratic-covariation witness against a path that is
constant after `T` must itself be frozen after `T`. -/
private theorem hasQuadraticCovariationAlong_eq_terminal_of_rightConstAfter_theorem25_38
    {F G : PathSpace}
    {B : NNReal → ℝ}
    {T t : NNReal}
    (hB : HasQuadraticCovariationAlong F G B)
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T) :
    B t = B T := by
  have hrewrite :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            T
            n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n))))
        atTop
        (𝓝 (B T)) := by
    simpa using
      (HasQuadraticCovariationAlong.tendsto_partition_sum hB T).add
        (tendsto_boundaryMixedIncrement_zero_of_rightConstAfter_theorem25_38
          (F := F) (G := G) hTt hGconst)
  have hEqRows :
      (fun n ↦
        partitionQuadraticCovariationSum
          Definition2158.dyadicPartitionSequence
          F
          G
          t
          n) =ᶠ[atTop]
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            T
            n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n)))) :=
    Filter.Eventually.of_forall fun n ↦
      partitionQuadraticCovariationSum_eq_terminal_plus_boundary_of_rightConstAfter_theorem25_38
        (F := F) (G := G) hTt hGconst n
  have hLimitAtT :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            t
            n)
        atTop
        (𝓝 (B T)) :=
    Tendsto.congr' hEqRows hrewrite
  -- Proof comment: the same dyadic mixed row at horizon `t` converges both to `B t` and to
  -- `B T`, so uniqueness of limits freezes the witness.
  exact tendsto_nhds_unique
    (HasQuadraticCovariationAlong.tendsto_partition_sum hB t)
    hLimitAtT

/-- Helper for Theorem 25.38: a genuine quadratic-covariation process with the second coordinate
deterministically stopped at `T` has a compensator frozen almost surely after `T`. -/
private theorem aeCompensatorEqTerminalOfRightStoppedCovariation_theorem25_38
    {μ : Measure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X A : NNReal → Ω → ℝ}
    (T : NNReal)
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hA :
      IsContinuousQuadraticCovariationProcess ℱ μ
        X
        (stoppedProcess X (fun _ ↦ (T : ENNReal)))
        A) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
  let Xstop : NNReal → Ω → ℝ := stoppedProcess X (fun _ ↦ (T : ENNReal))
  have hXstop :
      IsContinuousLocalMartingale ℱ μ Xstop := by
    refine
      { local_martingale :=
          _root_.ProbabilityTheory.isLocalMartingale_stoppedProcess
            hX.local_martingale
            hX.continuous
            (isStoppingTime_const ℱ T)
        continuous := ?_ }
    intro ω
    exact continuous_stoppedProcess_of_continuous hX.continuous ω
  filter_upwards
    [aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
      (μ := μ)
      (ℱ := ℱ)
      (M := X)
      (N := Xstop)
      (A := A)
      hX
      hXstop
      hA] with ω hω t hTt
  let F : PathSpace := ⟨fun s ↦ X s ω, hX.continuous ω⟩
  let G : PathSpace := ⟨fun s ↦ Xstop s ω, hXstop.continuous ω⟩
  have hGconst : ∀ s : NNReal, T ≤ s → G s = G T := by
    intro s hs
    -- Proof comment: after the deterministic stop time, the second path is literally frozen at
    -- the value `X T ω`.
    calc
      G s = X T ω := by
        simp [G, Xstop, stoppedProcessConstTime_eq_min, min_eq_right hs]
      _ = G T := by
        simp [G, Xstop, stoppedProcessConstTime_eq_min]
  simpa [F, G] using
    hasQuadraticCovariationAlong_eq_terminal_of_rightConstAfter_theorem25_38
      (F := F)
      (G := G)
      (B := fun s ↦ A s ω)
      hω
      hTt
      hGconst

/-- Helper for Theorem 25.38: deterministic-time modifications of continuous paths agree
simultaneously at all times almost surely. -/
private theorem ae_all_eq_of_modifications_of_continuous_theorem25_38
    {μ : Measure Ω} {X Y : NNReal → Ω → ℝ}
    (hXY : AreModifications μ X Y)
    (hXcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    (hYcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω := by
  have hRat : ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, X (q : NNReal) ω = Y (q : NNReal) ω := by
    rw [ae_all_iff]
    intro q
    simpa using hXY (q : NNReal)
  filter_upwards [hRat] with ω hωRat t
  have hEqOn :
      Set.EqOn (fun s : NNReal ↦ X s ω) (fun s : NNReal ↦ Y s ω)
        (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    exact hωRat q
  -- Proof comment: nonnegative rationals are dense in `NNReal`, so continuity upgrades the
  -- timewise modification relation to one null set controlling all times.
  exact congrFun (Continuous.ext_on nnratDense (hXcont ω) (hYcont ω) hEqOn) t

/-- Helper for Theorem 25.38: for a deterministic cutoff `T`, the canonical cutoff coordinate is
almost surely frozen at every later deterministic time. -/
private theorem constCutoffCoordinate_ae_eq_terminalValue_of_le_theorem25_38
    {μ : ProbabilityMeasure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ (μ : Measure Ω) M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T U : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hTU : T ≤ U) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        U =ᵐ[(μ : Measure Ω)]
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        T := by
  let Ncut :
      NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM
      (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  let Nstop :
      NNReal → Ω → ℝ :=
    stoppedProcess Ncut (fun _ ↦ (T : ENNReal))
  let A :
      NNReal → Ω → ℝ :=
    bracketDensityIntegralUpTo hbr
      (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  have hCanonical :
      IsContinuousLocalMartingale ℱ (μ : Measure Ω) Ncut ∧
        IsContinuousSquareVariationProcess ℱ (μ : Measure Ω) Ncut A := by
    -- Proof comment: the Chapter 25.21 canonical global clauses already package the deterministic
    -- cutoff coordinate and its bracket witness.
    simpa [Ncut, A] using
      canonicalConstCutoffGlobalClauses
        (μ := (μ : Measure Ω))
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        (hbr := hbr)
        T
        hH_prog
        hH_sq
  have hStoppedMart :
      IsLocalMartingale ℱ (μ : Measure Ω) Nstop := by
    -- Proof comment: deterministic stopping preserves the local-martingale clause of the
    -- canonical cutoff coordinate.
    simpa [Nstop] using
      isLocalMartingale_stoppedProcess_constTime_theorem25_38
        (μ := (μ : Measure Ω))
        hCanonical.1.local_martingale
        hCanonical.1.continuous
        T
  have hStoppedCanonical :
      IsContinuousLocalMartingale ℱ (μ : Measure Ω) Nstop := by
    refine
      { local_martingale := hStoppedMart
        continuous := ?_ }
    intro ω
    simpa [Nstop] using continuous_stoppedProcess_of_continuous hCanonical.1.continuous ω
  have hStoppedSq :
      IsContinuousSquareVariationProcess ℱ (μ : Measure Ω) Nstop A := by
    have hStoppedSqRaw :
        IsContinuousSquareVariationProcess ℱ (μ : Measure Ω)
          Nstop
          (stoppedProcess A (fun _ ↦ (T : ENNReal))) := by
      -- Proof comment: first stop the canonical square-variation witness at the same
      -- deterministic horizon.
      simpa [Nstop, A] using
        _root_.ProbabilityTheory.stoppedSquareVariationProcess
          (ℱ := ℱ)
          (μ := (μ : Measure Ω))
          hCanonical.2
          (isStoppingTime_const ℱ T)
    -- Proof comment: for a deterministic cutoff coefficient, the bracket witness is already
    -- frozen after `T`, so stopping it does not change the process.
    simpa [A, constCutoffBracket_eq_stoppedConstTime_theorem25_38
      (μ := (μ : Measure Ω)) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using
      hStoppedSqRaw
  have hEqUpTo :
      EqUpTo (μ : Measure Ω) T Ncut Nstop := by
    refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
    intro t ht ω hω
    exact hω (by
      simpa [Nstop, stoppedProcessConstTime_eq_min, min_eq_left ht])
  have hSelfQuad :
      IsContinuousQuadraticCovariationProcess ℱ (μ : Measure Ω) Ncut Ncut A := by
    exact selfContinuousQuadraticCovariation_of_squareVariation_theorem25_38 hCanonical.2
  have hCross :
      IsContinuousQuadraticCovariationProcess ℱ (μ : Measure Ω) Ncut Nstop A := by
    rcases
        _root_.ProbabilityTheory.existsUnique_continuousQuadraticCovariationProcess
          (((ProbabilityTheory.mem_Mlocc_iff ℱ (μ : Measure Ω) Ncut)).2 hCanonical.1)
          (((ProbabilityTheory.mem_Mlocc_iff ℱ (μ : Measure Ω) Nstop)).2 hStoppedCanonical) with
      ⟨B, hCrossRaw, _huniq⟩
    have hCanonicalEqB :
        EqUpTo (μ : Measure Ω) T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          B := by
      exact
        eqUpTo_quadraticCovariationIntegralUpTo_of_continuousQuadraticCovariationProcessLocal
          (μ := (μ : Measure Ω))
          (ℱ := ℱ)
          (M₁ := M)
          (M₂ := M)
          (H₁ := H)
          (H₂ := H)
          (hM₁ := hM)
          (hM₂ := hM)
          (hbr₁ := hbr)
          (hbr₂ := hbr)
          T
          (eqUpTo_rfl (μ := (μ : Measure Ω)) T Ncut)
          hEqUpTo
          hCanonical.1
          hStoppedCanonical
          hCanonical.2
          hStoppedSq
          hCrossRaw
    have hCanonicalEqA :
        EqUpTo (μ : Measure Ω) T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          A := by
      exact
        eqUpTo_quadraticCovariationIntegralUpTo_of_continuousQuadraticCovariationProcessLocal
          (μ := (μ : Measure Ω))
          (ℱ := ℱ)
          (M₁ := M)
          (M₂ := M)
          (H₁ := H)
          (H₂ := H)
          (hM₁ := hM)
          (hM₂ := hM)
          (hbr₁ := hbr)
          (hbr₂ := hbr)
          T
          (eqUpTo_rfl (μ := (μ : Measure Ω)) T Ncut)
          (eqUpTo_rfl (μ := (μ : Measure Ω)) T Ncut)
          hCanonical.1
          hCanonical.1
          hCanonical.2
          hCanonical.2
          hSelfQuad
    have hEqBAUpTo : EqUpTo (μ : Measure Ω) T B A := by
      -- Proof comment: both compensators agree on `[0,T]` with the same canonical mixed bracket.
      exact eqUpTo_trans (eqUpTo_sym hCanonicalEqB) hCanonicalEqA
    have hAfreeze :
        ∀ ω : Ω, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
      intro ω t hTt
      have hAeq :
          stoppedProcess A (fun _ ↦ (T : ENNReal)) t ω = A t ω := by
        simpa [A, constCutoffBracket_eq_stoppedConstTime_theorem25_38
          (μ := (μ : Measure Ω)) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using rfl
      calc
        A t ω = stoppedProcess A (fun _ ↦ (T : ENNReal)) t ω := hAeq.symm
        _ = A T ω := by
          simpa [stoppedProcessConstTime_eq_min, min_eq_right hTt] using
            congrFun (stoppedProcessConstTime_eq_min (X := A) T t) ω
    have hBfreeze :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, T ≤ t → B t ω = B T ω := by
      -- Route correction: freeze the genuine witness by the new pathwise right-constant
      -- covariation argument, not by another owner-side construction.
      exact
        aeCompensatorEqTerminalOfRightStoppedCovariation_theorem25_38
          (μ := (μ : Measure Ω))
          (ℱ := ℱ)
          (X := Ncut)
          (A := B)
          T
          hCanonical.1
          hCrossRaw
    have hABall :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, A t ω = B t ω := by
      exact
        ae_eq_allTimes_of_eqUpTo_and_frozen_after_theorem25_38
          (μ := (μ : Measure Ω))
          (T := T)
          hEqBAUpTo.symm
          hAfreeze
          hBfreeze
    -- Proof comment: transport the genuine witness `B` to the canonical compensator `A` using
    -- the all-times almost-sure equality of compensators.
    exact
      continuousQuadraticCovariation_of_ae_eq_allTimes_compensator_theorem25_38
        (μ := (μ : Measure Ω))
        (ℱ := ℱ)
        hCanonical.1
        hStoppedCanonical
        hCrossRaw
        hCanonical.2.zero
        hCanonical.2.adapted
        hCanonical.2.continuous
        (locallyFiniteVariation_of_continuous_monotone
          (μ := (μ : Measure Ω))
          hCanonical.2.continuous
          hCanonical.2.monotone)
        hABall
  have hZero :
      Ncut 0 =ᵐ[(μ : Measure Ω)] Nstop 0 := by
    -- Proof comment: deterministic stopping never changes the time-`0` value.
    refine Filter.Eventually.of_forall ?_
    intro ω
    simp [Nstop, stoppedProcess]
  have hEqAtU :
      Ncut U =ᵐ[(μ : Measure Ω)] Nstop U := by
    exact
      ae_eq_at_time_of_sharedWitness_theorem25_38
        (ℱ := ℱ)
        (μ := (μ : Measure Ω))
        hCanonical.1
        hStoppedCanonical
        hCanonical.2
        hStoppedSq
        hCross
        hZero
        U
  have hStoppedAtU :
      Nstop U =ᵐ[(μ : Measure Ω)] Ncut T := by
    -- Proof comment: after time `T`, the deterministic stop is literally frozen at `Ncut T`.
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [Nstop, min_eq_right hTU] using
      congrFun (stoppedProcessConstTime_eq_min (X := Ncut) T U) ω
  -- Proof comment: compare the later value with its deterministic stop and normalize that stop
  -- at time `U`.
  simpa [Ncut] using hEqAtU.trans hStoppedAtU

/-- Helper for Theorem 25.38: for a fixed deterministic cutoff `T`, the canonical cutoff
coordinate agrees almost surely at all times with its deterministic stop. -/
private theorem constCutoffCoordinate_ae_eq_stoppedConstTime_allTimes_theorem25_38
    {μ : ProbabilityMeasure Ω} {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ (μ : Measure Ω) M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂(μ : Measure Ω),
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        t
        ω =
      stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (T : ENNReal))
        t
        ω := by
  let Ncut :
      NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM
      (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  let Nstop :
      NNReal → Ω → ℝ :=
    stoppedProcess Ncut (fun _ ↦ (T : ENNReal))
  have hCanonical :
      IsContinuousLocalMartingale ℱ (μ : Measure Ω) Ncut ∧
        IsContinuousSquareVariationProcess ℱ (μ : Measure Ω)
          Ncut
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) :=
    canonicalConstCutoffGlobalClauses
      (μ := (μ : Measure Ω))
      (ℱ := ℱ)
      (M := M)
      (H := H)
      (hM := hM)
      (hbr := hbr)
      T
      hH_prog
      hH_sq
  have hMods : AreModifications (μ : Measure Ω) Ncut Nstop := by
    intro U
    by_cases hUT : U ≤ T
    · refine Filter.Eventually.of_forall ?_
      intro ω
      simpa [Nstop, stoppedProcessConstTime_eq_min, min_eq_left hUT]
    · have hTU : T ≤ U := le_of_not_ge hUT
      have hFreeze :
          Ncut U =ᵐ[(μ : Measure Ω)] Ncut T :=
        constCutoffCoordinate_ae_eq_terminalValue_of_le_theorem25_38
          (μ := μ)
          (ℱ := ℱ)
          (M := M)
          (H := H)
          (hM := hM)
          (hbr := hbr)
          T
          U
          hH_prog
          hH_sq
          hTU
      have hStoppedAtU :
          Nstop U =ᵐ[(μ : Measure Ω)] Ncut T := by
        refine Filter.Eventually.of_forall ?_
        intro ω
        simpa [Nstop, min_eq_right hTU] using
          congrFun (stoppedProcessConstTime_eq_min (X := Ncut) T U) ω
      exact hFreeze.trans hStoppedAtU.symm
  have hNstop_cont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ Nstop t ω := by
    simpa [Nstop] using continuous_stoppedProcess_of_continuous hCanonical.1.continuous
  -- Proof comment: the fixed-time modification relation upgrades to one null set controlling all
  -- deterministic times because both processes have continuous sample paths.
  simpa [Ncut, Nstop] using
    ae_all_eq_of_modifications_of_continuous_theorem25_38
      (μ := (μ : Measure Ω))
      hMods
      hCanonical.1.continuous
      hNstop_cont

/-- Helper for Theorem 25.38: on almost every good centered sample path, the deterministically cut
coordinate canonical value is frozen after the clipped exit horizon. -/
private theorem constCutoffCanonicalCoordinate_freeze_aeAllTimes_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (i : Fin d) :
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
    let hZi :
        IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
      (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont i).1
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        τ
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      let Tω : NNReal := (min (t : ENNReal) (τ ω)).untopA
      let HiCut : NNReal → Ω → ℝ :=
        ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (Tω : ENNReal))
      τ ω < t →
        ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω =
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω := by
  intro τ ℱW Zi hZi Hi
  let B : VectorProcess := fun s ω ↦ if s = 0 then 0 else W s ω - x
  have hGood :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun s : NNReal ↦ B s ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          Xω ∈ (𝒞_qv^d) ∧
            ∀ i j : Fin d,
              HasQuadraticCovariationAlong
                (vectorPathComponent Xω i)
                (vectorPathComponent Xω j)
                (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      zeroPatchedCenteredGoodPath_ae_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont
  have hEqAe : ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal, B s ω = W s ω - x := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_38
        (μ := μ) (W := W) (x := x) hW
  filter_upwards [hGood, hEqAe] with ω hGoodω hω t
  intro Tω HiCut hτ_lt_t
  have hTω_ne_top : min (t : ENNReal) (τ ω) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (by simp))
  have hTω_coe : (Tω : ENNReal) = min (t : ENNReal) (τ ω) := by
    dsimp [Tω]
    rw [WithTop.untopA_eq_untop hTω_ne_top]
    exact WithTop.coe_untop _ _
  have hTω_eq_exit : (Tω : ENNReal) = τ ω := by
    rw [hTω_coe, min_eq_right (le_of_lt hτ_lt_t)]
  have hTω_lt_t : Tω < t := by
    exact_mod_cast (show (Tω : ENNReal) < (t : ENNReal) by
      rw [hTω_eq_exit]
      exact hτ_lt_t)
  rcases hGoodω with ⟨hcontω, hGoodω⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hXω : Xω ∈ (𝒞_qv^d) := by
    simpa [Xω] using hGoodω.1
  have hIto :
      let F0 : State → ℝ := fun z : State ↦ F (x + z)
      let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
      ∃ I : NNReal → ℝ,
        HasPathwiseItoIntegralAlong
          (fun s : NNReal ↦ (∂[i] F0) (Xω s))
          (vectorPathComponent Xω i)
          Definition2158.dyadicPartitionSequence
          I := by
    -- Proof comment: the AE wrapper reduces the after-exit freeze to the deterministic witness
    -- attached to this one good centered sample path.
    simpa using
      coordinatePathwiseItoWitness_onGoodCenteredPath_theorem25_38
        (F := fun z : State ↦ F (x + z))
        (translatedContDiff_theorem25_38 (F := F) hFcontDiff x)
        hXω
        i
  -- Proof comment: after fixing one good centered path and identifying `Tω` with the exit time,
  -- the fixed-path freeze theorem gives the desired samplewise after-exit constancy.
  simpa [τ, ℱW, Zi, hZi, Hi, HiCut, B, Xω, Tω] using
    constCutoffCanonicalCoordinate_freeze_theorem25_38
      (μ := μ)
      (W := W)
      (U := U)
      (x := x)
      (F := F)
      (B := B)
      hW
      hWcont
      hFcontDiff
      (ω := ω)
      hcontω
      hω
      i
      (T := Tω)
      (U' := t)
      hTω_eq_exit
      hTω_lt_t
      hIto

/-- Helper for Theorem 25.38: once the samplewise stopped-Itô identity is isolated, the
finite-horizon `EqUpTo` theorem becomes a pure packaging step. -/
private theorem stoppedCenteredPatchedIto_aeAllTimes_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let canonical :
        Fin d → NNReal → Ω → ℝ := fun i =>
          let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
          let hZi :
              IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
            (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
              (μ := μ) (W := W) (x := x) hW hWcont i).1
          let Hi : NNReal → Ω → ℝ :=
            ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              τ
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
    ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Δ F (x + B s ω))
                τ
                u.toNNReal
                ω =
        ∑ i : Fin d, canonical i t ω := by
  intro B τ ℱW canonical
  -- Route correction: the remaining frontier is now the samplewise stopped-Itô identity itself,
  -- not the later `EqUpTo` packaging.
  have hGood :
      ∀ᵐ ω ∂(μ : Measure Ω),
        ∃ hcontω : Continuous fun t : NNReal ↦ B t ω,
          let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
          Xω ∈ (𝒞_qv^d) ∧
            ∀ i j : Fin d,
              HasQuadraticCovariationAlong
                (vectorPathComponent Xω i)
                (vectorPathComponent Xω j)
                (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [B] using
      zeroPatchedCenteredGoodPath_ae_theorem25_38
        (μ := μ) (W := W) (x := x) hW hWcont
  have hEqAe :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, B t ω = W t ω - x := by
    simpa [B] using
      centeredPath_zeroPatched_eq_ae_allTimes_theorem25_38
        (μ := μ) (W := W) (x := x) hW
  let F0 : State → ℝ := fun z : State ↦ F (x + z)
  have hF0 : ContDiff ℝ 2 F0 := by
    simpa [F0] using translatedContDiff_theorem25_38 (F := F) hFcontDiff x
  have hCutoffFreezeAll :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ i : Fin d, ∀ t : NNReal,
        let Tω : NNReal := (min (t : ENNReal) (τ ω)).untopA
        let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
        let hZi :
            IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
            (μ := μ) (W := W) (x := x) hW hWcont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            τ
        let HiCut : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (Tω : ENNReal))
        τ ω < t →
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω =
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω := by
    rw [ae_all_iff]
    intro i
    simpa [τ, ℱW] using
      constCutoffCanonicalCoordinate_freeze_aeAllTimes_theorem25_38
        (μ := μ)
        (W := W)
        (U := U)
        (x := x)
        (F := F)
        hW
        hWcont
        hUo
        hExitFinite
        hFcontDiff
        i
  obtain ⟨χ, hχ, hχae⟩ :=
    existsCommonCoordinateRefinementSubsequence_ae_tendsto_theorem25_38
      (μ := μ) (W := W) (x := x) (F := F0) hW hWcont hF0
  filter_upwards [hExitFinite, hGood, hEqAe, hχae, hCutoffFreezeAll] with
      ω hτω hGoodω hω hχω hFreezeω t
  rcases hGoodω with ⟨hcontω, hGoodω⟩
  let Xω : VectorPathSpace d := ⟨fun s ↦ B s ω, hcontω⟩
  have hGoodω' :
      Xω ∈ (𝒞_qv^d) ∧
        ∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent Xω i)
            (vectorPathComponent Xω j)
            (fun T ↦ if i = j then (T : ℝ) else 0) := by
    simpa [Xω] using hGoodω
  have hXω : Xω ∈ (𝒞_qv^d) := hGoodω'.1
  let Tω : NNReal := (min (t : ENNReal) (τ ω)).untopA
  have hminFin : min (t : ENNReal) (τ ω) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (by simp))
  have hTω_coe : (Tω : ENNReal) = min (t : ENNReal) (τ ω) := by
    dsimp [Tω]
    rw [WithTop.untopA_eq_untop hminFin]
    exact WithTop.coe_untop _ _
  have hTω_le : (Tω : ENNReal) ≤ τ ω := by
    rw [hTω_coe]
    exact min_le_right _ _
  have hLeft :
      F0 (Xω Tω) - F0 (Xω 0) =
        stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω := by
    -- Proof comment: evaluating the translated observable at the clipped horizon `Tω` is exactly
    -- the theorem-local stopped surface because `Xω` is the centered sample path and `Xω 0 = 0`.
    simp [F0, Xω, Tω, stoppedProcess, B]
  let quadω : ℝ :=
    ((1 : ℝ) / 2) *
      ∑ i : Fin d, ∑ j : Fin d,
        pathwiseQuadraticCovariationIntegral
          (fun s ↦ (∂²[i, j] F0) (Xω s))
          (vectorPathComponent Xω i)
          (vectorPathComponent Xω j)
          Tω
  have hPathwiseCore :
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω =
        pathwiseMultidimensionalItoIntegral F0 Xω Tω + quadω := by
    -- Proof comment: apply the multidimensional pathwise Itô formula at the clipped horizon
    -- `Tω`, then rewrite the left side back to the theorem-local stopped surface.
    calc
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω
          = F0 (Xω Tω) - F0 (Xω 0) := hLeft.symm
      _ =
          pathwiseMultidimensionalItoIntegral F0 Xω Tω + quadω := by
            simpa [quadω] using
              pathwiseMultidimensionalItoFormula F0 hF0 Xω hXω Tω
  have hReduced :
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω - quadω =
        pathwiseMultidimensionalItoIntegral F0 Xω Tω := by
    -- Proof comment: moving the raw quadratic correction to the left isolates the first-order
    -- multidimensional pathwise Itô integral.
    calc
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω - quadω =
          (pathwiseMultidimensionalItoIntegral F0 Xω Tω + quadω) - quadω := by
            rw [hPathwiseCore]
      _ = pathwiseMultidimensionalItoIntegral F0 Xω Tω := by ring
  have hQuadDiag :
      quadω =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), (∂²[i, i] F0) (Xω s.toNNReal) := by
    -- Proof comment: the Kronecker-delta covariation family collapses the double correction term
    -- to the diagonal set-integral family.
    simpa [quadω] using
      kroneckerQuadraticCorrection_eq_diagIntegrals_theorem25_38
        (F := F0) hF0 (X := Xω) hGoodω'.2 Tω
  have hCoordinateAtClipped :
      ∀ i : Fin d,
        canonical i Tω ω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω := by
    intro i
    let Hi : NNReal → Ω → ℝ :=
      ProbabilityTheory.processBeforeStoppingTime
        (coordinatePartialDerivProcess_theorem25_38
          (Ω := Ω) (W := W) (F := F) i)
        τ
    have hCanonicalHi :
        canonical i Tω ω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω := by
      -- Proof comment: rewrite the theorem-local stochastic canonical coordinate to its dyadic
      -- pathwise spelling along the centered sample path.
      simpa [canonical, Hi, Xω] using
        canonicalCoordinate_apply_eq_stoppedCenteredPathwiseItoIntegral_theorem25_38
          (μ := μ) (W := W) (x := x) (U := U) (F := F) (B := B)
          hW hWcont ω hcontω hω i Tω
    have hRows :
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω
            n) =
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              Tω
              n) := by
      funext n
      -- Proof comment: every sampled left endpoint in the clipped row lies before the exit
      -- horizon, so the stopped coefficient agrees there with the translated raw partial
      -- derivative along the centered path.
      exact
        partitionPathwiseItoApproximationUpTo_eq_of_leftEndpointEq_theorem25_38
          (P := Definition2158.dyadicPartitionSequence)
          (X := vectorPathComponent Xω i)
          (T := Tω)
          (row := n)
          (hKL := by
            intro j hj
            have hs_le_Tω :
                Definition2158.dyadicPartitionSequence n j ≤ Tω := by
              exact
                (partitionPoint_mem_Icc_of_lt_truncationBoundIndex
                  Definition2158.dyadicPartitionSequence
                  n
                  j
                  Tω
                  hj).2
            have hs_le_exit :
                ((Definition2158.dyadicPartitionSequence n j : NNReal) : ENNReal) ≤ τ ω := by
              exact le_trans (by exact_mod_cast hs_le_Tω) hTω_le
            calc
              Hi (Definition2158.dyadicPartitionSequence n j) ω =
                  (∂[i] F) (x + B (Definition2158.dyadicPartitionSequence n j) ω) := by
                exact
                  stoppedCoordinatePartial_beforeExit_eq_theorem25_38
                    (W := W) (x := x) (U := U) (F := F) (B := B) (ω := ω)
                    hω i hs_le_exit
              _ = (∂[i] F) (x + Xω (Definition2158.dyadicPartitionSequence n j)) := by
                simp [Xω]
              _ = (∂[i] F0) (Xω (Definition2158.dyadicPartitionSequence n j)) := by
                symm
                exact
                  translatedPartialDeriv_eq_theorem25_38
                    (F := F)
                    (hF := hFcontDiff.differentiable (by norm_num))
                    x
                    (Xω (Definition2158.dyadicPartitionSequence n j))
                    i))
  have hPathwiseEq :
        pathwiseItoIntegralAlong
            (fun s : NNReal ↦ Hi s ω)
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω =
          pathwiseItoIntegralAlong
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω := by
      -- Proof comment: the canonical pathwise integral is a `limUnder` of the dyadic rows, so
      -- identical rows give identical fixed-horizon canonical values.
      rw [pathwiseItoIntegralAlong, pathwiseItoIntegralAlong]
      exact congrArg (limUnder atTop) hRows
    exact hCanonicalHi.trans hPathwiseEq
  have hRawRowDecomp :
      ∀ i : Fin d, ∀ n : ℕ,
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            Tω
            n
          =
        partitionPathwiseItoApproximationUpTo
            (fun s : NNReal ↦ (∂[i] F0) (Xω s))
            (vectorPathComponent Xω i)
            Definition2158.dyadicPartitionSequence
            (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)
            n
          +
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i Tω -
                vectorPathComponent Xω i
                  (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) := by
    intro i n
    -- Proof comment: the clipped raw coordinate row already splits into a predecessor-horizon row
    -- plus one explicit boundary increment on the final active cell.
    simpa using
      partitionPathwiseItoApproximationUpTo_eq_predecessor_add_boundary_theorem25_38
        (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        (X := vectorPathComponent Xω i)
        (P := Definition2158.dyadicPartitionSequence)
        (T := Tω)
        (n := n)
  have hRawBoundaryTendsto :
      ∀ i : Fin d,
        Tendsto
          (fun n ↦
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i Tω -
                vectorPathComponent Xω i
                  (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)))
          atTop
          (𝓝 0) := by
    intro i
    have hCoeffCont : Continuous fun s : NNReal ↦ (∂[i] F0) (Xω s) := by
      -- Proof comment: the translated partial derivative is continuous and the centered sample
      -- path `Xω` is continuous.
      exact (continuousPartialDeriv_theorem25_38 F0 hF0 i).comp Xω.continuous
    -- Proof comment: the explicit predecessor-cell boundary term from the raw coordinate row
    -- vanishes as the dyadic mesh shrinks.
    simpa using
      partitionItoBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_38
        (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        hCoeffCont
        (X := vectorPathComponent Xω i)
        (P := Definition2158.dyadicPartitionSequence)
        (hφ := fun a b hab ↦ hab)
        (T := Tω)
  have hRawSuccessorBoundaryTendsto :
      ∀ i : Fin d,
        Tendsto
          (fun n ↦
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i
                  (partitionNextPointUpTo
                    Definition2158.dyadicPartitionSequence
                    n
                    (partitionBoundIndex Definition2158.dyadicPartitionSequence n Tω - 1)
                    Tω) -
                vectorPathComponent Xω i Tω))
          atTop
          (𝓝 0) := by
    intro i
    have hCoeffCont : Continuous fun s : NNReal ↦ (∂[i] F0) (Xω s) := by
      -- Proof comment: the same translated partial derivative is continuous along the centered
      -- sample path, so the successor-side boundary term is controlled by the new geometric
      -- convergence lemma.
      exact (continuousPartialDeriv_theorem25_38 F0 hF0 i).comp Xω.continuous
    simpa using
      partitionItoSuccessorBoundaryTerm_tendsto_zero_alongStrictMonoRows_theorem25_38
        (H := fun s : NNReal ↦ (∂[i] F0) (Xω s))
        hCoeffCont
        (X := vectorPathComponent Xω i)
        (P := Definition2158.dyadicPartitionSequence)
        (hφ := fun a b hab ↦ hab)
        (T := Tω)
  have hSummedRawBoundaryTendsto :
      Tendsto
        (fun n ↦
          ∑ i : Fin d,
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i Tω -
                vectorPathComponent Xω i
                  (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)))
        atTop
        (𝓝 0) := by
    -- Proof comment: the finite sum of predecessor-side boundary errors still vanishes because
    -- each coordinate boundary term already tends to `0`.
    simpa using
      tendsto_finset_sum Finset.univ fun i hi ↦ hRawBoundaryTendsto i
  have hSummedRawSuccessorBoundaryTendsto :
      Tendsto
        (fun n ↦
          ∑ i : Fin d,
            (∂[i] F0)
              (Xω (partitionPredecessorPointEarly Definition2158.dyadicPartitionSequence n Tω)) *
              (vectorPathComponent Xω i
                  (partitionNextPointUpTo
                    Definition2158.dyadicPartitionSequence
                    n
                    (partitionBoundIndex Definition2158.dyadicPartitionSequence n Tω - 1)
                    Tω) -
                vectorPathComponent Xω i Tω))
        atTop
        (𝓝 0) := by
    -- Proof comment: the same finite-sum argument packages the successor-side coordinate errors
    -- into one vanishing multidimensional boundary term.
    simpa using
      tendsto_finset_sum Finset.univ fun i hi ↦ hRawSuccessorBoundaryTendsto i
  have hDyadicMultidimTendsto :
      Tendsto
        (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F0 Xω Tω n)
        atTop
        (𝓝 (pathwiseMultidimensionalItoIntegral F0 Xω Tω)) := by
    -- Proof comment: Theorem 25.30 already controls the clipped multidimensional dyadic row on
    -- every good centered path.
    simpa using
      tendsto_dyadicMultidimensionalItoApproximationUpTo F0 hF0 Xω hXω Tω
  have hRawClippedCoordinateSubseqTendsto :
      ∀ i : Fin d,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun s : NNReal ↦ (∂[i] F0) (Xω s))
              (vectorPathComponent Xω i)
              Definition2158.dyadicPartitionSequence
              Tω
              (χ n))
          atTop
          (𝓝 (canonical i Tω ω)) := by
    intro i
    -- Proof comment: the selector `χ` was chosen before fixing `ω`, so on this good centered
    -- sample path each clipped raw coordinate row already converges to its clipped canonical
    -- value along the same common subsequence.
    simpa [hCoordinateAtClipped i] using hχω hcontω i Tω
  have hClippedFirstOrder :
      pathwiseMultidimensionalItoIntegral F0 Xω Tω = ∑ i : Fin d, canonical i Tω ω := by
    have hDyadicMultidimSubseqTendsto :
        Tendsto
          (fun n ↦
            dyadicMultidimensionalItoApproximationUpTo F0 Xω Tω (χ n))
          atTop
          (𝓝 (pathwiseMultidimensionalItoIntegral F0 Xω Tω)) :=
      hDyadicMultidimTendsto.comp hχ.tendsto_atTop
    have hSummedCoordinateSubseqTendsto :
        Tendsto
          (fun n ↦
            ∑ i : Fin d,
              partitionPathwiseItoApproximationUpTo
                (fun s : NNReal ↦ (∂[i] F0) (Xω s))
                (vectorPathComponent Xω i)
                Definition2158.dyadicPartitionSequence
                Tω
                (χ n))
          atTop
          (𝓝 (∑ i : Fin d, canonical i Tω ω)) := by
      -- Proof comment: along the common selector `χ`, every coordinate row converges on this
      -- sample path, so the finite sum converges to the sum of the clipped canonical values.
      simpa using
        tendsto_finset_sum Finset.univ fun i hi ↦ hRawClippedCoordinateSubseqTendsto i
    have hDyadicToCanonical :
        Tendsto
          (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F0 Xω Tω (χ n))
          atTop
          (𝓝 (∑ i : Fin d, canonical i Tω ω)) := by
      -- Proof comment: each multidimensional dyadic row is still exactly the finite sum of its
      -- coordinate rows, so the chosen subsequence inherits the same coordinate-limit value.
      simpa [dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_theorem25_38]
        using hSummedCoordinateSubseqTendsto
    -- Proof comment: the common subsequence of the multidimensional dyadic row now has two
    -- candidate limits, so uniqueness identifies the clipped multidimensional integral with the
    -- summed clipped coordinate values.
    exact (tendsto_nhds_unique hDyadicMultidimSubseqTendsto hDyadicToCanonical).symm
  have hFirstOrder :
      pathwiseMultidimensionalItoIntegral F0 Xω Tω = ∑ i : Fin d, canonical i t ω := by
    by_cases ht_beforeExit : (t : ENNReal) ≤ τ ω
    · have hTω_eq_t : Tω = t := by
        apply ENNReal.coe_injective
        rw [hTω_coe, min_eq_left ht_beforeExit]
      -- Proof comment: before exit, the clipped horizon is already `t`, so the clipped common
      -- limit `hClippedFirstOrder` is exactly the target identity.
      simpa [hTω_eq_t] using hClippedFirstOrder
    · -- Route correction: the clipped common-limit identity is now closed, so the only remaining
      -- work is the genuinely after-exit transport from the stopped coordinate values at time
      -- `t` back to the clipped horizon `Tω`.
      have hAfter : τ ω < t := lt_of_not_ge ht_beforeExit
      have hTω_eq_exit : (Tω : ENNReal) = τ ω := by
        rw [hTω_coe, min_eq_right (le_of_lt hAfter)]
      have hTω_lt_t : Tω < t := by
        exact_mod_cast (show (Tω : ENNReal) < (t : ENNReal) by
          rw [hTω_eq_exit]
          exact hAfter)
      have hCoordinateAfterExit :
          ∀ i : Fin d, canonical i t ω = canonical i Tω ω := by
        intro i
        let Zi : NNReal → Ω → ℝ := fun s ξ ↦ W s ξ i - x i
        let hZi :
            IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
            (μ := μ) (W := W) (x := x) hW hWcont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            τ
        let HiCut : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime Hi (fun _ ↦ (Tω : ENNReal))
        have hHiSample :
            ∀ s : NNReal,
              Hi s ω =
                if (s : ENNReal) ≤ (Tω : ENNReal) then
                  (∂[i] F0) (Xω s)
                else
                  0 := by
          -- Proof comment: after exit, the samplewise stopped coefficient is exactly the raw
          -- translated coefficient cut off at the clipped horizon `Tω`.
          simpa [Hi, F0, Xω, τ] using
            sampleStoppedCoordinate_eq_constCutoffRaw_theorem25_38
              (W := W) (x := x) (U := U) (F := F) (B := B) (ω := ω)
              hω
              (hFcontDiff.differentiable (by norm_num))
              i
              (T := Tω)
              hTω_eq_exit
        have hHiCutSample :
            ∀ s : NNReal, HiCut s ω = Hi s ω := by
          intro s
          by_cases hs : (s : ENNReal) ≤ (Tω : ENNReal)
          · -- Proof comment: before `Tω`, cutting the already-stopped coefficient again at
            -- `Tω` does nothing.
            simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs]
          · have hHiZero : Hi s ω = 0 := by
              simpa [hs] using hHiSample s
            -- Proof comment: after `Tω`, both the original samplewise stopped coefficient and
            -- the additional deterministic cutoff are already zero.
            simp [HiCut, ProbabilityTheory.processBeforeStoppingTime_apply, hs, hHiZero]
        have hAtTimeT :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω := by
          -- Proof comment: at the fixed sample `ω`, the coefficient used by the canonical
          -- coordinate already agrees with its deterministic cutoff on the whole interval
          -- `Set.Icc 0 t`.
          exact
            continuousLocalMartingaleItoIntegralProcess_eq_of_eqOnIcc_theorem25_38
              (μ := (μ : Measure Ω))
              (ℱ := ℱW)
              (M := Zi)
              (K := Hi)
              (L := HiCut)
              (hM := hZi)
              (T := t)
              (ω := ω)
              (by
                intro s hs
                exact (hHiCutSample s).symm)
        have hAtTimeTω :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi Tω ω := by
          -- Proof comment: at the clipped horizon itself, the deterministic cutoff is exactly
          -- the original coefficient.
          exact
            continuousLocalMartingaleItoIntegralProcess_eq_constCutoffValue_theorem25_38
              (μ := (μ : Measure Ω))
              (ℱ := ℱW)
              (M := Zi)
              (H := Hi)
              (hM := hZi)
              Tω
              ω
        have hCutoffFreeze :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut t ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi HiCut Tω ω := by
          -- Route correction: the after-exit freeze is now supplied by the stochastic
          -- all-cutoffs comparison, so the old fixed-path refinement package is no longer part
          -- of the live frontier.
          simpa [τ, ℱW, Zi, hZi, Hi, HiCut, Tω] using hFreezeω i t hAfter
        have hCoordinateEq :
            ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi t ω =
              ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi Tω ω := by
          -- Proof comment: both time slices are compared through the same deterministic-cutoff
          -- canonical coordinate, which is the only remaining missing freeze step.
          exact hAtTimeT.trans (hCutoffFreeze.trans hAtTimeTω)
        simpa [canonical, Zi, hZi, Hi, τ] using hCoordinateEq
      -- Proof comment: once every coordinate is transported from the after-exit time `t` back to
      -- the clipped horizon `Tω`, the already-established clipped identity closes the branch by
      -- finite summation.
      calc
        pathwiseMultidimensionalItoIntegral F0 Xω Tω = ∑ i : Fin d, canonical i Tω ω :=
          hClippedFirstOrder
        _ = ∑ i : Fin d, canonical i t ω := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          symm
          exact hCoordinateAfterExit i
  have hQuadNormalized :
      quadω =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x + B s ω))
              τ
              u.toNNReal
              ω := by
    -- Proof comment: the diagonal correction has been factored into a dedicated translated
    -- Laplacian bridge, so only the already-proved diagonal reduction `hQuadDiag` remains here.
    calc
      quadω =
          ((1 : ℝ) / 2) *
            ∑ i : Fin d,
              ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), (∂²[i, i] F0) (Xω s.toNNReal) := hQuadDiag
      _ =
          ((1 : ℝ) / 2) *
            ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ),
              ∑ i : Fin d, (∂²[i, i] F0) (Xω s.toNNReal) := by
            rw [← integral_finset_sum Finset.univ hDiagTermInt]
      _ = ∫ s in Set.Icc (0 : ℝ) (Tω : ℝ), rawLap s := by
            rw [← integral_const_mul]
            congr 1
            exact hDiagIntegrand
      _ = ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) (Tω : ℝ)) rawLap s := by
            rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      _ = ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) stoppedLap s := by
            rw [hIndicatorEq.symm]
      _ =
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Δ F (x + B s ω))
                τ
                u.toNNReal
                ω := by
            simpa [F0] using
              translatedDiagIntegral_eq_stoppedLaplacianIntegral_theorem25_38
                (x := x) (F := F) (B := B) (τ := τ) (ω := ω) (Xω := Xω)
                (t := t) (Tω := Tω)
                hFcontDiff
                (fun s ↦ by simp [Xω])
                hTω_coe
                hTω_le
  -- Proof comment: once the first-order term is identified with the canonical coordinate sum and
  -- the diagonal correction is rewritten as the cutoff Laplacian integral, the theorem is the
  -- direct rearrangement of `hReduced`.
  calc
    stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x + B s ω))
              τ
              u.toNNReal
              ω =
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω - quadω := by
          rw [hQuadNormalized]
    _ = pathwiseMultidimensionalItoIntegral F0 Xω Tω := hReduced
    _ = ∑ i : Fin d, canonical i t ω := hFirstOrder

/-- Helper for Theorem 25.38: on `[0,T]`, the translated driftless stopped surface agrees with the
finite sum of the canonical coordinate Itô processes. -/
private theorem canonicalFamilyEqUpTo_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    let canonical :
        Fin d → NNReal → Ω → ℝ := fun i =>
          let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
          let hZi :
              IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
            (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
              (μ := μ) (W := W) (x := x) hW hWcont i).1
          let Hi : NNReal → Ω → ℝ :=
            ProbabilityTheory.processBeforeStoppingTime
              (coordinatePartialDerivProcess_theorem25_38
                (Ω := Ω) (W := W) (F := F) i)
              τ
          ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
    let Y : NNReal → Ω → ℝ := fun t ω ↦
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            ProbabilityTheory.processBeforeStoppingTime
              (fun s ω ↦ Δ F (x + B s ω))
              τ
              u.toNNReal
              ω
    EqUpTo (μ : Measure Ω) T Y (fun t ω ↦ ∑ i : Fin d, canonical i t ω) := by
  intro B τ ℱW canonical Y
  have hAll :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal, Y t ω = ∑ i : Fin d, canonical i t ω := by
    -- Proof comment: the samplewise stopped-Itô theorem already performs the stochastic work, so
    -- this theorem only repackages that all-times almost-sure equality into `EqUpTo`.
    simpa [B, τ, ℱW, canonical, Y] using
      stoppedCenteredPatchedIto_aeAllTimes_theorem25_38
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff T
  -- Proof comment: an all-times almost-sure identity yields the fixed-horizon `EqUpTo`
  -- relation immediately.
  exact eqUpTo_of_ae_allTimes hAll

/-- Helper for Theorem 25.38: choose one fixed-horizon owner for each coordinate Itô term and
transport the canonical family comparison termwise to that owner family. -/
private theorem shiftedTranslatedSurface_eqUpTo_coordinateConstCutoffFamily_theorem25_38
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    ∃ N : Fin d → NNReal → Ω → ℝ,
      (∀ i : Fin d,
        IsContinuousLocalMartingaleUpToLocal ℱW (μ : Measure Ω) T (N i)) ∧
      EqUpTo (μ : Measure Ω) T
        (fun t ω ↦
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x + B s ω))
                  τ
                  u.toNNReal
                  ω)
        (fun t ω ↦ ∑ i : Fin d, N i t ω) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let canonical :
      Fin d → NNReal → Ω → ℝ := fun i =>
        let Zi : NNReal → Ω → ℝ := fun t ω ↦ W t ω i - x i
        let hZi :
            IsContinuousLocalMartingale ℱW (μ : Measure Ω) Zi :=
          (centeredCoordinate_isContinuousLocalMartingale_and_timeBracket_natural_theorem25_38
            (μ := μ) (W := W) (x := x) hW hWcont i).1
        let Hi : NNReal → Ω → ℝ :=
          ProbabilityTheory.processBeforeStoppingTime
            (coordinatePartialDerivProcess_theorem25_38
              (Ω := Ω) (W := W) (F := F) i)
            τ
        ProbabilityTheory.continuousLocalMartingaleItoIntegralProcess hZi Hi
  let N : Fin d → NNReal → Ω → ℝ := fun i ↦
    Classical.choose <|
      coordinateConstCutoffItoUpTo_theorem25_38
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff i T
  have hN_upTo :
      ∀ i : Fin d,
        IsContinuousLocalMartingaleUpToLocal ℱW (μ : Measure Ω) T (N i) := by
    intro i
    exact
      (Classical.choose_spec <|
        coordinateConstCutoffItoUpTo_theorem25_38
          (μ := μ) (W := W) (U := U) (x := x) (F := F)
          hW hWcont hUo hExitFinite hFcontDiff i T).1
  have hN_canonical :
      ∀ i : Fin d,
        EqUpTo (μ : Measure Ω) T (N i) (canonical i) := by
    intro i
    exact
      (Classical.choose_spec <|
        coordinateConstCutoffItoUpTo_theorem25_38
          (μ := μ) (W := W) (U := U) (x := x) (F := F)
          hW hWcont hUo hExitFinite hFcontDiff i T).2
  have hCanonicalFamily :
      EqUpTo (μ : Measure Ω) T
        (fun t ω ↦
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x + B s ω))
                  τ
                  u.toNNReal
                  ω)
        (fun t ω ↦ ∑ i : Fin d, canonical i t ω) := by
    -- Proof comment: the canonical-family theorem isolates the samplewise Itô comparison from
    -- the later owner transport.
    simpa [B, τ, ℱW, canonical] using
      canonicalFamilyEqUpTo_theorem25_38
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff T
  have hTransport :
      EqUpTo (μ : Measure Ω) T
        (fun t ω ↦ ∑ i : Fin d, canonical i t ω)
        (fun t ω ↦ ∑ i : Fin d, N i t ω) := by
    -- Proof comment: replace the canonical coordinate family by the chosen owner family
    -- coordinatewise on the same fixed horizon.
    exact
      eqUpTo_sym <|
        eqUpTo_finsetSum
          (s := Finset.univ)
          (μ := (μ : Measure Ω))
          (T := T)
          (X := N)
          (Y := canonical)
          (fun i _ ↦ hN_canonical i)
  refine ⟨N, hN_upTo, ?_⟩
  -- Proof comment: compose the canonical-family comparison with the termwise owner transport.
  exact eqUpTo_trans hCanonicalFamily hTransport

/-- Helper for Theorem 25.38: the exact remaining fixed-horizon stochastic frontier is an
`EqUpTo` bridge from the visible stopped increment to a deterministic-horizon local martingale
owner. -/
private theorem shiftedTranslatedSurface_constStop_eqUpToCanonicalOwner
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F) :
    ∀ T : NNReal,
      let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
      let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
      let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
        Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
      let Y : NNReal → Ω → ℝ := fun t ω ↦
        stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              processBeforeStoppingTime
                (fun s ω ↦ Δ F (x + B s ω))
                τ
                u.toNNReal
                ω
    ∃ Nsum : NNReal → Ω → ℝ,
        EqUpTo (μ : Measure Ω) T Y Nsum ∧
        IsContinuousLocalMartingaleUpToLocal ℱW (μ : Measure Ω) T Nsum := by
  intro T B τ ℱW Y
  rcases
      shiftedTranslatedSurface_eqUpTo_coordinateConstCutoffFamily_theorem25_38
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff T with
    ⟨N, hN_upTo, hEq⟩
  let Nsum : NNReal → Ω → ℝ := fun t ω ↦ ∑ i : Fin d, N i t ω
  refine ⟨Nsum, ?_, ?_⟩
  · -- Proof comment: the family theorem already identifies the translated surface with the sum of
    -- the chosen coordinate owners.
    simpa [B, τ, ℱW, Y, Nsum] using hEq
  · -- Proof comment: finite sums preserve the fixed-horizon local-martingale owner property.
    simpa [Nsum] using
      finsetSum_isContinuousLocalMartingaleUpToLocal
        (μ := (μ : Measure Ω))
        (ℱ := ℱW)
        (s := Finset.univ)
        (T := T)
        (N := N)
        (fun i _ ↦ hN_upTo i)

/-- Helper for Theorem 25.38: the visible stopped increment already agrees on `[0,T]` with the
driftless translated stopped surface, so the only remaining stochastic input is the translated
surface owner. -/
private theorem visibleStoppedIncrement_eqUpTo_shiftedTranslatedSurface
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V)
    (T : NNReal) :
    let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let Y : NNReal → Ω → ℝ := fun t ω ↦
      stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 : ℝ) / 2) *
            processBeforeStoppingTime
              (fun s ω ↦ Δ F (x + B s ω))
              τ
              u.toNNReal
              ω
    EqUpTo
      (μ : Measure Ω)
      T
      (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
      Y := by
  intro B τ Y
  have hSurface :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        Y t ω = F (stoppedProcess W τ t ω) - F x := by
    have hShiftedLap :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          Δ F (x + stoppedProcess B τ t ω) = 0 := by
      -- Proof comment: harmonicity kills the Laplacian along the translated stopped path.
      simpa [B, τ] using
        shiftedStoppedExtension_laplacian_eq_zero
          (μ := μ) (W := W) (U := U) (V := V) (F := F) (x := x)
          hx hW hWcont hUo hUV hExitFinite hFharm
    have hCutoffDriftZero :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun s ω ↦ Δ F (x + B s ω))
                τ
                u.toNNReal
                ω = 0 := by
      filter_upwards [hShiftedLap] with ω hω t
      have hIntegrandZero :
          (fun s : ℝ ↦
            ((1 : ℝ) / 2) *
              ProbabilityTheory.processBeforeStoppingTime
                (fun u ω ↦ Δ F (x + B u ω))
                τ
                s.toNNReal
                ω) = fun _ : ℝ ↦ (0 : ℝ) := by
        funext s
        by_cases hs : (s.toNNReal : ENNReal) ≤ τ ω
        · have hStopEq : stoppedProcess B τ s.toNNReal ω = B s.toNNReal ω := by
            exact stoppedProcess_eq_of_le (u := B) (τ := τ) (ω := ω) (i := s.toNNReal) hs
          have hLapAt : Δ F (x + B s.toNNReal ω) = 0 := by
            simpa [hStopEq] using hω s.toNNReal
          rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_pos hs]
          simp [hLapAt]
        · rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hs]
          simp
      -- Proof comment: the cutoff drift vanishes because the integrand is zero before `τ` by
      -- harmonicity and is forced to zero after `τ` by the cutoff itself.
      rw [hIntegrandZero]
      simp
    have hTranslatedVisible :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω =
            F (stoppedProcess W τ t ω) - F x := by
      filter_upwards
          [stageStoppedTranslatedSurface_eq_visibleIncrement
            (μ := μ) (W := W) (U := U) (F := F) (x := x) hW] with ω hω t
      have hStopSurface :
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω =
            F (x + stoppedProcess B τ t ω) - F x := by
        -- Proof comment: rewrite the translated stopped surface to the explicit stopped-path
        -- spelling before comparing it with the visible stopped increment.
        simpa using
          congrArg
            (fun Z : NNReal → Ω → ℝ ↦ Z t ω)
            (stageStoppedTranslatedSurface_eq_stoppedRawTranslatedIncrement
              (B := B) (τ := τ) (F := F) (x := x))
      exact hStopSurface.trans (hω t)
    filter_upwards [hTranslatedVisible, hCutoffDriftZero] with ω hωVisible hωDrift t
    calc
      Y t ω =
          stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              ((1 : ℝ) / 2) *
                ProbabilityTheory.processBeforeStoppingTime
                  (fun s ω ↦ Δ F (x + B s ω))
                  τ
                  u.toNNReal
                  ω := by
            rfl
      _ = stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω := by
            rw [hωDrift t]
            ring
      _ = F (stoppedProcess W τ t ω) - F x := hωVisible t
  have hSurfaceSymm :
      ∀ᵐ ω ∂(μ : Measure Ω), ∀ t : NNReal,
        F (stoppedProcess W τ t ω) - F x = Y t ω := by
    filter_upwards [hSurface] with ω hω t
    exact (hω t).symm
  -- Proof comment: once the translated stopped surface is rewritten back to the visible stopped
  -- increment and the harmonic drift is shown to vanish, the desired horizon-wise equality is
  -- an immediate `EqUpTo` witness.
  exact eqUpTo_of_ae_allTimes hSurfaceSymm

/-- Helper for Theorem 25.38: the exact remaining fixed-horizon stochastic frontier is an
`EqUpTo` bridge from the visible stopped increment to a deterministic-horizon local martingale
owner. -/
private theorem stageStoppedVisibleIncrement_constStop_eqUpToCanonicalOwner
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      ∃ Nsum : NNReal → Ω → ℝ,
        EqUpTo
          (μ : Measure Ω)
          T
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          Nsum ∧
        IsContinuousLocalMartingaleUpToLocal
          (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
          (μ : Measure Ω)
          T
          Nsum := by
  intro T
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let Y : NNReal → Ω → ℝ := fun t ω ↦
    stoppedProcess (fun s ω ↦ F (x + B s ω) - F x) τ t ω -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        ((1 : ℝ) / 2) *
          processBeforeStoppingTime
            (fun s ω ↦ Δ F (x + B s ω))
            τ
            u.toNNReal
            ω
  have hVisible :
      EqUpTo
        (μ : Measure Ω)
        T
        (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
        Y := by
    -- Proof comment: the visible stopped increment already agrees with the driftless translated
    -- surface on `[0, T]`.
    simpa [B, τ, Y] using
      visibleStoppedIncrement_eqUpTo_shiftedTranslatedSurface
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUV hExitFinite hFharm T
  rcases
      shiftedTranslatedSurface_constStop_eqUpToCanonicalOwner
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff T with
    ⟨Nsum, hYEq, hNsum⟩
  refine ⟨Nsum, eqUpTo_trans hVisible hYEq, ?_⟩
  -- Proof comment: after the visible-to-translated comparison is fixed, the local-martingale-up-to
  -- owner is exactly the one already supplied for the translated surface.
  simpa [B, τ, ℱW, Y] using hNsum

/-- Helper for Theorem 25.38: once the visible stopped increment is matched on `[0,T]` with a
deterministic-horizon owner, its deterministic stop is a genuine martingale. -/
private theorem stageStoppedVisibleIncrement_constStop_martingaleFrontier
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    ∀ T : NNReal,
      Martingale
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)
          (fun _ ↦ (T : ENNReal)))
        (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
        (μ : Measure Ω) := by
  intro T
  let X : NNReal → Ω → ℝ :=
    fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  have hXStrong :
      StronglyAdapted ℱW (stoppedProcess X (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: deterministic stopping preserves strong adaptedness of the visible target,
    -- so only the finite-horizon owner comparison remains.
    simpa [X, ℱW] using
      stageStoppedVisibleIncrement_constStop_stronglyAdapted
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcontDiff.continuous T
  have hXBounded :
      BoundedInTimeAe (μ : Measure Ω) (stoppedProcess X (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: compactness of `closure U` supplies the deterministic bound needed for the
    -- bounded-local-martingale upgrade.
    simpa [X] using
      stageStoppedVisibleIncrement_constStop_boundedInTimeAe
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hx hW hWcont hUo hUcpt hExitFinite hFcontDiff.continuous T
  rcases
      stageStoppedVisibleIncrement_constStop_eqUpToCanonicalOwner
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUcpt hUV hExitFinite hFcontDiff hFharm T with
    ⟨Nsum, hEq, hUpTo⟩
  -- Proof comment: the deterministic stop is now exactly the generic `EqUpTo`-transport
  -- situation handled by the adapter above.
  exact
    martingaleOfConstStoppedEqUpToLocalMartingaleUpTo
      (μ := μ)
      (ℱ := ℱW)
      (X := X)
      (N := Nsum)
      (T := T)
      hXStrong
      hXBounded
      (by simpa [X] using hEq)
      (by simpa [ℱW] using hUpTo)

/-- Helper for Theorem 25.38: once the translated deterministic stop is a martingale, the visibly
stopped increment inherits that martingale property by an almost-sure all-times rewrite. -/
private theorem stageStoppedVisibleIncrement_constStop_martingale_of_translated
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {F : State → ℝ}
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcont : Continuous F)
    (T : NNReal)
    (hTranslatedMart :
      let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
      let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
      let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
        Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
      Martingale
        (stoppedProcess
          (stoppedProcess
            (fun t ω ↦ F (x + B t ω) - F x)
            τ)
          (fun _ ↦ (T : ENNReal)))
        ℱW
        (μ : Measure Ω)) :
    let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
    let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
      Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
    Martingale
      (stoppedProcess
        (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
        (fun _ ↦ (T : ENNReal)))
      ℱW
      (μ : Measure Ω) := by
  let B : VectorProcess := fun t ω ↦ if t = 0 then 0 else W t ω - x
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  have hTargetStrong :
      StronglyAdapted
        ℱW
        (stoppedProcess
          (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
          (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: the visible deterministic stop is strongly adapted by stopping the already
    -- stopped visible increment once more at the deterministic horizon `T`.
    simpa [τ, ℱW] using
      stageStoppedVisibleIncrement_constStop_stronglyAdapted
        (μ := μ) (W := W) (U := U) (x := x) (F := F)
        hW hWcont hUo hExitFinite hFcont T
  have hStopEq :
      ∀ t : NNReal,
        stoppedProcess
            (stoppedProcess
              (fun t ω ↦ F (x + B t ω) - F x)
              τ)
            (fun _ ↦ (T : ENNReal))
            t =ᵐ[(μ : Measure Ω)]
          stoppedProcess
            (fun t ω ↦ F (stoppedProcess W τ t ω) - F x)
            (fun _ ↦ (T : ENNReal))
            t := by
    intro t
    have hSurface :
        ∀ᵐ ω ∂(μ : Measure Ω), ∀ s : NNReal,
          F (x + stoppedProcess B τ s ω) - F x =
            F (stoppedProcess W τ s ω) - F x := by
      -- Proof comment: the translated stopped surface already agrees with the visible stopped
      -- increment at every deterministic time on one common full-measure event.
      simpa [B, τ] using
        stageStoppedTranslatedSurface_eq_visibleIncrement
          (μ := μ) (W := W) (U := U) (F := F) (x := x) hW
    filter_upwards [hSurface] with ω hω
    have hAtMin := hω (min t T)
    -- Proof comment: compare both deterministic stops at the clipped time `min t T`, after
    -- rewriting the translated branch through the stopped translated surface.
    simpa [stoppedProcessConstTime_eq_min,
      stageStoppedTranslatedSurface_eq_stoppedRawTranslatedIncrement
        (B := B) (τ := τ) (F := F) (x := x)] using hAtMin
  -- Proof comment: transport the martingale owner from the translated deterministic stop to the
  -- visible deterministic stop through the all-times almost-sure equality above.
  exact martingale_congr_ae (by simpa [B, τ, ℱW] using hTranslatedMart) hTargetStrong hStopEq

/-- Helper for Theorem 25.38: a continuous local martingale up to `τ` becomes a genuine
continuous local martingale after stopping at `τ`. -/
private theorem continuousLocalMartingale_stoppedProcess_of_upTo
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) :
    IsContinuousLocalMartingale ℱ μ (stoppedProcess M τ) := by
  -- Proof comment: this is exactly Corollary 21.74, so no local reconstruction is needed once
  -- the up-to witness and the stopping-time owner are already available.
  simpa using
    IsContinuousLocalMartingaleUpTo.isContinuousLocalMartingale_stoppedProcess
      (ℱ := ℱ)
      (μ := μ)
      (τ := τ)
      (M := M)
      hM
      hτ

/-- Helper for Theorem 25.38: the remaining stochastic blocker has been reduced to constructing a
continuous local-martingale-up-to witness for the unstopped harmonic increment before the exit
clock. Once this is available, Corollary 21.74 turns the stopped increment into an honest local
martingale automatically. -/
private theorem stageExtension_increment_isContinuousLocalMartingaleUpTo
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    IsContinuousLocalMartingaleUpTo
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (μ : Measure Ω)
      (hittingAfter W Uᶜ 0)
      (fun t ω ↦ F (W t ω) - F x) := by
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  let M : NNReal → Ω → ℝ := fun t ω ↦ F (W t ω) - F x
  let Y : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess W τ t ω) - F x
  let hWsm : ∀ t : NNReal, StronglyMeasurable (W t) :=
    brownianVectorStartedAt_stronglyMeasurable hW
  have hτstop : IsStoppingTime ℱW τ := by
    -- Proof comment: the exit clock from the precompact stage is already packaged as a stopping
    -- time in the natural filtration of `W`.
    simpa [τ, ℱW] using
      stageExit_isStoppingTime_of_continuous_of_aeExitFinite
        (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite
  have hFStrong :
      StronglyAdapted ℱW (fun t ω ↦ F (W t ω)) := by
    -- Proof comment: composing the Brownian state with the measurable observable `F` preserves
    -- strong adaptedness in the natural filtration.
    simpa [ℱW] using
      stateComposition_stronglyAdapted_natural
        (W := W)
        hWsm
        hFcontDiff.continuous.measurable
  have hMStrong : StronglyAdapted ℱW M := by
    intro t
    -- Proof comment: subtracting the deterministic offset `F x` does not change adaptedness.
    simpa [M] using (hFStrong t).sub stronglyMeasurable_const
  have hMAdapted : Adapted ℱW M := hMStrong.adapted
  have hMCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω := by
    intro ω
    -- Proof comment: the raw increment inherits continuity from the Brownian path and the
    -- continuity of `F`.
    simpa [M] using (hFcontDiff.continuous.comp (hWcont ω)).sub continuous_const
  have hYEq : stoppedProcess M τ = Y := by
    -- Proof comment: the visibly stopped increment is exactly the stopped raw increment.
    simpa [τ, M, Y] using
      (stageStoppedExtension_eq_stoppedRawIncrement
        (W := W) (τ := τ) (F := F) (x := x))
  have hYCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω := by
    -- Proof comment: once `Y` is rewritten as the stopped raw increment, pathwise continuity is
    -- the standard continuity of stopped continuous processes.
    simpa [hYEq] using continuous_stoppedProcess_of_continuous hMCont
  have hConstStopped :
      ∀ T : NNReal,
        Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱW (μ : Measure Ω) := by
    intro T
    -- Proof comment: the fixed-horizon martingale statement is now isolated in the dedicated
    -- visible frontier theorem, so the local-martingale reconstruction below no longer carries
    -- the translated transport layer inline.
    simpa [Y, τ, ℱW] using
      stageStoppedVisibleIncrement_constStop_martingaleFrontier
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUcpt hUV hExitFinite hFcontDiff hFharm T
  have hLocalizing :
      IsLocalizingSequenceUpTo ℱW (μ : Measure Ω) τ M
        (fun n ω ↦ min (τ ω) (n : ENNReal)) := by
    refine ⟨hτstop, ?_, ?_, ?_⟩
    · intro n
      -- Proof comment: each clipped horizon `τ ∧ n` is again a stopping time.
      exact hτstop.min_const (n : NNReal)
    · filter_upwards with ω
      refine ⟨?_, ?_⟩
      · intro a b hab
        -- Proof comment: monotonicity is pointwise because only the deterministic cap grows with
        -- the index.
        exact min_le_min le_rfl (by exact_mod_cast hab)
      · let clip : ENNReal → ENNReal := fun s ↦ min (τ ω) s
        have hClipCont : Continuous clip := continuous_const.inf continuous_id
        -- Proof comment: the clipped deterministic caps converge to `τ(ω)` by continuity of the
        -- map `s ↦ τ(ω) ∧ s` at `∞`.
        simpa [clip, min_comm] using
          hClipCont.continuousAt.tendsto.comp ENNReal.tendsto_nat_nhds_top
    · intro n
      have hRewrite :
          stoppedProcess M (fun ω ↦ min (τ ω) (n : ENNReal)) =
            stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)) := by
        -- Proof comment: the localizers `τ ∧ n` on the raw increment are the same processes as
        -- the deterministic stops of the visibly stopped increment.
        simpa [τ, M, Y] using
          rawIncrement_minConst_eq_stageStoppedIncrement_const
            (W := W) (U := U) (F := F) (x := x) n
      have hMart :
          Martingale
            (stoppedProcess M (fun ω ↦ min (τ ω) (n : ENNReal)))
            ℱW
            (μ : Measure Ω) := hRewrite.symm ▸ hConstStopped n
      have hUI :
          UniformIntegrable
            (stoppedProcess M (fun ω ↦ min (τ ω) (n : ENNReal)))
            1
            (μ : Measure Ω) := by
        have hStoppedUI :
            UniformIntegrable
              (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
              1
              (μ : Measure Ω) := by
          -- Proof comment: a deterministic stop of a martingale is uniformly integrable after
          -- stopping once more at the same deterministic horizon.
          simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
            (martingaleUniformIntegrable_stoppedProcessConstTime
              (μ := (μ : Measure Ω))
              (ℱ := ℱW)
              (X := stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
              (hConstStopped n)
              (n : NNReal)).2
        exact hRewrite.symm ▸ hStoppedUI
      exact ⟨hMart, hUI⟩
  -- Proof comment: once the fixed-horizon martingale frontier is supplied, the clipped sequence
  -- `τ ∧ n` already satisfies the Chapter 21 definition of a continuous local martingale up to
  -- `τ`.
  exact
    ⟨(isLocalMartingaleUpTo_iff ℱW (μ : Measure Ω) τ M).2
        ⟨hMAdapted, fun n ω ↦ min (τ ω) (n : ENNReal), hLocalizing⟩,
      hMCont⟩

/-- Helper for Theorem 25.38: the only remaining stochastic-core input is the local-martingale
owner for the stopped harmonic extension on one precompact stage. -/
private theorem stageStoppedExtension_increment_isLocalMartingale
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U V : Set State} {x : State}
    {F : State → ℝ}
    (hx : x ∈ U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ W t ω)
    (hUo : IsOpen U) (hUcpt : IsCompact (closure U))
    (hUV : closure U ⊆ V)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hFcontDiff : ContDiff ℝ 2 F)
    (hFharm : InnerProductSpace.HarmonicOnNhd F V) :
    IsLocalMartingale
      (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (μ : Measure Ω)
      (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x) := by
  let τ : Ω → ENNReal := hittingAfter W Uᶜ 0
  let ℱW : Filtration NNReal ‹MeasurableSpace Ω› :=
    Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW)
  have hτstop : IsStoppingTime ℱW τ :=
    stageExit_isStoppingTime_of_continuous_of_aeExitFinite
      (μ := μ) (W := W) (U := U) (x := x) hW hWcont hUo hExitFinite
  have hUpTo :
      IsContinuousLocalMartingaleUpTo
        ℱW
        (μ : Measure Ω)
        τ
        (fun t ω ↦ F (W t ω) - F x) := by
    -- Proof comment: after the route correction, the only live stochastic input is the smaller
    -- up-to-local-martingale witness before the exit clock.
    simpa [τ, ℱW] using
      stageExtension_increment_isContinuousLocalMartingaleUpTo
        (μ := μ) (W := W) (U := U) (V := V) (x := x) (F := F)
        hx hW hWcont hUo hUcpt hUV hExitFinite hFcontDiff hFharm
  have hStopped :
      IsContinuousLocalMartingale ℱW (μ : Measure Ω)
        (stoppedProcess (fun t ω ↦ F (W t ω) - F x) τ) := by
    -- Proof comment: the released-clock construction from Corollary 21.74 is reproduced locally
    -- here, so the only remaining missing input is the pre-exit up-to owner `hUpTo`.
    exact
      continuousLocalMartingale_stoppedProcess_of_upTo
        (μ := (μ : Measure Ω))
        (ℱ := ℱW)
        (τ := τ)
        (M := fun t ω ↦ F (W t ω) - F x)
        hUpTo
        hτstop
  -- Proof comment: Corollary 21.74 upgrades the up-to witness to a genuine local martingale for
  -- the stopped raw increment, and that stopped raw increment is exactly the visible target.
  simpa [τ, stageStoppedExtension_eq_stoppedRawIncrement]
    using hStopped.local_martingale

/-- Helper for Theorem 25.38: once a global extension agrees with `u` on `closure U` and its
stopped increment is a bounded local martingale, every deterministic horizon already satisfies the
optional-stopping identity for `u` on the stage `U`. -/
private theorem stageStoppedExtension_expectation_eq_atNat
    {μ : ProbabilityMeasure Ω} {W : VectorProcess} {U : Set State} {x : State}
    {u F : State → ℝ}
    (hx : x ∈ U) (hUo : IsOpen U)
    (hW : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x)
    (hWcont :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous fun t : NNReal ↦ W t ω)
    (hStart :
      ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x)
    (hExitFinite :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Uᶜ 0 ω < ⊤)
    (hEq : Set.EqOn F u (closure U))
    (hClosureBound :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure U, |u z| ≤ C)
    (hLocal :
      IsLocalMartingale
        (Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
        (μ : Measure Ω)
        (fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x)) :
    ∀ n : ℕ,
      u x = ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := by
  let M : NNReal → Ω → ℝ := fun t ω ↦ F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω)
  have hxClosure : x ∈ closure U := subset_closure hx
  have hFx : F x = u x := hEq hxClosure
  have hInitialAe : M 0 =ᵐ[(μ : Measure Ω)] fun _ : Ω ↦ F x := by
    filter_upwards [hStart] with ω hωstart
    have hStop0 :
        stoppedProcess W (hittingAfter W Uᶜ 0) 0 ω = W 0 ω :=
      stoppedProcess_eq_of_le
        (u := W) (τ := hittingAfter W Uᶜ 0) (ω := ω) (i := 0) bot_le
    -- Proof comment: at the zero horizon, the stopped stage path is still the Brownian start.
    simp [M, hStop0, hωstart]
  rcases hClosureBound with ⟨C, _hCnonneg, hC⟩
  have hBounded :
      BoundedInTimeAe (μ : Measure Ω) (fun t ω ↦ M t ω - F x) := by
    refine ⟨C + |F x|, ?_⟩
    filter_upwards [hWcont, hStart, hExitFinite] with ω hωcont hωstart hωfin t
    have hStartMem : W 0 ω ∈ U := by
      simpa [hωstart] using hx
    have hmem :
        stoppedProcess W (hittingAfter W Uᶜ 0) t ω ∈ closure U :=
      stageStoppedProcess_mem_buffer
        (U := U) (V := closure U) (W := W) (ω := ω)
        hUo hωcont hStartMem (by intro z hz; exact hz) hωfin t
    have hEqStage :
        F (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) =
          u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) :=
      hEq hmem
    -- Proof comment: rewrite the stopped extension back to `u` on `closure U`, then use the
    -- closure bound together with the deterministic offset `F x`.
    calc
      |M t ω - F x|
          = |u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω) - F x| := by
              simp [M, hEqStage]
      _ ≤ |u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω)| + |F x| := by
            simpa [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (u (stoppedProcess W (hittingAfter W Uᶜ 0) t ω))
                (-F x))
      _ ≤ C + |F x| := add_le_add (hC _ hmem) le_rfl
  intro n
  have hStageEqF :
      ∫ ω, M n ω ∂(μ : Measure Ω) =
        ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := by
    simpa [M] using
      integral_stageStopped_eq_of_eqOn_closure
        (μ := μ) (W := W) (U := U) (x := x)
        (u := u) (F := F) hx hUo hWcont hStart hExitFinite hEq n
  have hExpectationF :
      F x = ∫ ω, M n ω ∂(μ : Measure Ω) :=
    expectation_eq_of_bounded_localMartingale_increment
      (μ := μ)
      (ℱ := Filtration.natural W (brownianVectorStartedAt_stronglyMeasurable hW))
      (M := M) (c := F x) hLocal hBounded hInitialAe n
  -- Proof comment: the local-martingale expectation identity is first proved for the extension
  -- `F`, then transported back to `u` because every stopped value remains on `closure U`.
  calc
    u x = F x := hFx.symm
    _ = ∫ ω, M n ω ∂(μ : Measure Ω) := hExpectationF
    _ = ∫ ω, u (stoppedProcess W (hittingAfter W Uᶜ 0) n ω) ∂(μ : Measure Ω) := hStageEqF

/-- Helper for Theorem 25.38: compact closure forces the frontier to be compact as well. -/
private theorem isCompact_frontier_of_isCompact_closure
    {G : Set State} (hGcpt : IsCompact (closure G)) :
    IsCompact (frontier G) :=
  IsCompact.of_isClosed_subset hGcpt isClosed_frontier frontier_subset_closure

/-- Helper for Theorem 25.38: a Dirichlet solution already gives a continuous boundary datum on
`frontier G`. -/
private theorem continuous_boundaryDatum_of_solvesDirichletProblem
    {G : Set State} {f : frontier G → ℝ} {u : State → ℝ}
    (hu : SolvesDirichletProblem G f u) :
    Continuous f := by
  have hcont_u : Continuous (fun y : frontier G ↦ u y) := by
    -- Proof comment: continuity on `closure G` restricts directly to the frontier subtype.
    exact continuousOn_iff_continuous_restrict.mp
      (hu.continuousOn_closure.mono frontier_subset_closure)
  -- Proof comment: the restricted solution is exactly the boundary datum on the frontier.
  refine hcont_u.congr ?_
  intro y
  exact hu.boundary_eq y

/-- Helper for Theorem 25.38: compactness of the frontier makes the boundary datum strongly
measurable for harmonic measure. -/
private theorem aestronglyMeasurable_boundaryDatum_harmonicMeasure
    (P : State → ProbabilityMeasure Ω) (G : Set State)
    (exitValue : Ω → frontier G) (hExitMeas : Measurable exitValue)
    {f : frontier G → ℝ} {u : State → ℝ}
    (hGcpt : IsCompact (closure G)) (hu : SolvesDirichletProblem G f u) (x : G) :
    AEStronglyMeasurable f
      (harmonicMeasure P G exitValue hExitMeas x : Measure (frontier G)) := by
  letI : CompactSpace (frontier G) :=
    isCompact_iff_compactSpace.mp (isCompact_frontier_of_isCompact_closure hGcpt)
  -- Proof comment: on a compact frontier, continuity is enough for strong measurability under any
  -- Borel probability measure, in particular under harmonic measure.
  exact
    (continuous_boundaryDatum_of_solvesDirichletProblem hu).aestronglyMeasurable_of_compactSpace

/-- Helper for Theorem 25.38: once the exit expectation formula is known, the harmonic-measure
formula is just the pushforward integral identity. -/
private theorem dirichlet_solution_eq_harmonicMeasureIntegralCore
    (P : State → ProbabilityMeasure Ω) {G : Set State}
    {exitValue : Ω → frontier G} (hExitMeas : Measurable exitValue)
    {f : frontier G → ℝ} {u : State → ℝ}
    (hGcpt : IsCompact (closure G)) (hu : SolvesDirichletProblem G f u)
    {x : State} (hx : x ∈ G)
    (hExitRep : u x = ∫ ω, f (exitValue ω) ∂(P x : Measure Ω)) :
    u x =
      ∫ y, f y ∂(harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ : Measure (frontier G)) := by
  have hf :
      AEStronglyMeasurable f
        (harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ : Measure (frontier G)) :=
    aestronglyMeasurable_boundaryDatum_harmonicMeasure
      P G exitValue hExitMeas hGcpt hu ⟨x, hx⟩
  -- Proof comment: `harmonicMeasure` is already the pushforward of `P x` along `exitValue`.
  rw [integral_harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ hf]
  exact hExitRep

/-- Helper for Theorem 25.38: every compact time prefix strictly before the global exit time lies
inside one stage of the inner exhaustion. -/
private theorem innerExhaustion_prefix_subset_stage
    {Wc : VectorProcess} {G : Set State} {U : ℕ → Set State} {ω : Ω} {t : NNReal}
    (hUo : ∀ n, IsOpen (U n))
    (hUmono : Monotone U)
    (hUunion : (⋃ n, U n) = G)
    (hWcCont : Continuous fun s : NNReal ↦ Wc s ω)
    (ht : (t : ENNReal) < hittingAfter Wc Gᶜ 0 ω) :
    ∃ N : ℕ, ∀ s ∈ Set.Icc (0 : NNReal) t, Wc s ω ∈ U N := by
  let K : Set State := (fun s : NNReal ↦ Wc s ω) '' Set.Icc (0 : NNReal) t
  have hKcompact : IsCompact K := by
    -- Proof comment: the path image of the compact interval `[0,t]` is compact by continuity.
    exact isCompact_Icc.image_of_continuousOn hWcCont.continuousOn
  have hKsubset : K ⊆ ⋃ n, U n := by
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    have hslt : (s : ENNReal) < hittingAfter Wc Gᶜ 0 ω :=
      lt_of_le_of_lt (by exact_mod_cast hs.2) ht
    have hsG : Wc s ω ∈ G := by
      have hsNotGc :
          Wc s ω ∉ Gᶜ :=
        notMem_of_lt_hittingAfter
          (u := Wc) (s := Gᶜ) (n := (0 : NNReal)) (ω := ω) hslt hs.1
      simpa using hsNotGc
    -- Proof comment: every prefix point stays in `G`, so the exhaustion cover places it in one
    -- stage.
    simpa [hUunion] using hsG
  obtain ⟨N, hKN⟩ :=
    hKcompact.elim_directed_cover U hUo hKsubset hUmono.directed_le
  refine ⟨N, ?_⟩
  intro s hs
  -- Proof comment: after compactness chooses one stage covering the whole prefix image, every
  -- time slice in `[0,t]` lands in that same stage.
  exact hKN (Set.mem_image_of_mem (fun r : NNReal ↦ Wc r ω) hs)

/-- Helper for Theorem 25.38: along an increasing inner exhaustion, the stage exit clocks
increase to the global exit clock on every continuous path with finite global exit. -/
private theorem innerExhaustion_hittingAfter_tendsto_exit
    {Wc : VectorProcess} {G : Set State} {U : ℕ → Set State} {ω : Ω}
    (hUo : ∀ n, IsOpen (U n))
    (hUcl : ∀ n, closure (U n) ⊆ G)
    (hUmono : Monotone U)
    (hUunion : (⋃ n, U n) = G)
    (hWcCont : Continuous fun t : NNReal ↦ Wc t ω)
    (hτfin : hittingAfter Wc Gᶜ 0 ω < ⊤) :
    Tendsto
      (fun n : ℕ ↦ hittingAfter Wc (U n)ᶜ 0 ω)
      atTop
      (𝓝 (hittingAfter Wc Gᶜ 0 ω)) := by
  let τ : ENNReal := hittingAfter Wc Gᶜ 0 ω
  let τn : ℕ → ENNReal := fun n ↦ hittingAfter Wc (U n)ᶜ 0 ω
  have hUsub : ∀ n, U n ⊆ G := by
    intro n z hz
    exact hUcl n (subset_closure hz)
  have hτn_mono : Monotone τn := by
    intro m n hmn
    -- Proof comment: larger stages have smaller complements, so their exit times occur later.
    exact
      hittingAfter_anti Wc (0 : NNReal)
        (show (U n)ᶜ ⊆ (U m)ᶜ by
          intro z hz hzm
          exact hz (hUmono hmn hzm))
        ω
  have hτn_le_τ : ∀ n, τn n ≤ τ := by
    intro n
    -- Proof comment: since each stage sits inside `G`, exiting the stage cannot happen after
    -- exiting `G`.
    exact
      hittingAfter_anti Wc (0 : NNReal)
        (show Gᶜ ⊆ (U n)ᶜ by
          intro z hz hzn
          exact hz (hUsub n hzn))
        ω
  have hLower : ∀ c : ENNReal, c < τ → ∃ N : ℕ, c < τn N := by
    intro c hc
    have hc_ne_top : c ≠ ⊤ := ne_of_lt (lt_trans hc hτfin)
    let t : NNReal := c.toNNReal
    have hct : (t : ENNReal) = c := by
      exact ENNReal.coe_toNNReal hc_ne_top
    obtain ⟨N, hN⟩ :=
      innerExhaustion_prefix_subset_stage
        (Wc := Wc) (G := G) (U := U) (ω := ω) (t := t)
        hUo hUmono hUunion hWcCont (by simpa [τ, t, hct] using hc)
    have hNotLe : ¬ τn N ≤ c := by
      intro hle
      have hτN_fin : τn N < ⊤ := lt_of_le_of_lt (hτn_le_τ N) hτfin
      have hτN_ne_top : τn N ≠ ⊤ := ne_of_lt hτN_fin
      have hτN_mem :
          Wc (τn N).untopA ω ∈ (U N)ᶜ := by
        exact
          mem_closedSet_at_hittingAfter_of_lt_top_local
            (A := (U N)ᶜ)
            (hAclosed := isClosed_compl_iff.mpr (hUo N))
            hWcCont
            hτN_fin
      have hτN_le_t : (τn N).untopA ≤ t := by
        exact (WithTop.untopA_le_iff (x := τn N) (hx := hτN_ne_top)).2 <|
          by simpa [t, hct] using hle
      have hτN_in : Wc (τn N).untopA ω ∈ U N :=
        hN (τn N).untopA ⟨bot_le, hτN_le_t⟩
      exact hτN_mem hτN_in
    -- Proof comment: if the stage exit were already at or before `c`, some prefix point would
    -- lie in `(U N)ᶜ`, contradicting the compact-prefix containment.
    exact ⟨N, lt_of_not_ge hNotLe⟩
  have hLub : IsLUB (Set.range τn) τ := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases hy with ⟨n, rfl⟩
      exact hτn_le_τ n
    · intro b hb
      refine le_of_forall_lt ?_
      intro c hc
      obtain ⟨N, hN⟩ := hLower c hc
      exact lt_of_lt_of_le hN (hb (Set.mem_range_self N))
  -- Proof comment: monotone convergence now turns the pathwise lower/upper bounds into the
  -- desired limit of exit clocks.
  simpa [τ, τn] using tendsto_atTop_isLUB hτn_mono hLub

/-- Helper for Theorem 25.38: along an inner exhaustion `U n ⊂⊂ G`, the diagonal stopped values
`u(W^c_{n ∧ τ_{U_n}})` should converge almost surely to the boundary value at the exit point from
`G`. -/
private theorem tendsto_innerStageExitDirichlet_to_boundaryValue
    {μ : ProbabilityMeasure Ω}
    {W Wc : VectorProcess} {G : Set State} {x : State}
    {U : ℕ → Set State} {exitValue : Ω → frontier G} {f : frontier G → ℝ} {u : State → ℝ}
    (hx : x ∈ G) (hG : IsOpen G)
    (hUo : ∀ n, IsOpen (U n))
    (hUx : ∀ n, x ∈ U n)
    (hUcl : ∀ n, closure (U n) ⊆ G)
    (hUmono : Monotone U)
    (hUunion : (⋃ n, U n) = G)
    (hWcCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Wc t ω)
    (hWcStart : ∀ ω : Ω, Wc 0 ω = x)
    (hExitFiniteWc :
      ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc Gᶜ 0 ω < ⊤)
    (hExitEqWc :
      ∀ᵐ ω ∂(μ : Measure Ω),
        hittingAfter W Gᶜ 0 ω = hittingAfter Wc Gᶜ 0 ω ∧
          stoppedValue W (hittingAfter W Gᶜ 0) ω =
            stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω)
    (hExit :
      ∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    (hu : SolvesDirichletProblem G f u) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      Tendsto
        (fun n : ℕ ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
        atTop
        (𝓝 (f (exitValue ω))) := by
  filter_upwards [hExitFiniteWc, hExitEqWc] with ω hτfin hEqWc
  let τ : ENNReal := hittingAfter Wc Gᶜ 0 ω
  let τn : ℕ → ENNReal := fun n ↦ hittingAfter Wc (U n)ᶜ 0 ω
  have hτ_ne_top : τ ≠ ⊤ := ne_of_lt hτfin
  have hτn_le_τ : ∀ n, τn n ≤ τ := by
    intro n
    exact
      hittingAfter_anti Wc (0 : NNReal)
        (show Gᶜ ⊆ (U n)ᶜ by
          intro z hz hzn
          exact hz (hUcl n (subset_closure hzn)))
        ω
  have hτn_fin : ∀ n, τn n < ⊤ := by
    intro n
    exact lt_of_le_of_lt (hτn_le_τ n) hτfin
  have hτn_tendsto :
      Tendsto τn atTop (𝓝 τ) := by
    simpa [τ, τn] using
      innerExhaustion_hittingAfter_tendsto_exit
        (Wc := Wc) (G := G) (U := U) (ω := ω)
        hUo hUcl hUmono hUunion (hWcCont ω) hτfin
  have hTimeTendsto :
      Tendsto (fun n : ℕ ↦ (τn n).toNNReal) atTop (𝓝 τ.toNNReal) := by
    -- Proof comment: the finite exit clocks can be moved from `ENNReal` to `NNReal` because the
    -- global exit time is finite and every stage exit happens no later than it.
    simpa [τn, Function.comp] using (ENNReal.tendsto_toNNReal hτ_ne_top).comp hτn_tendsto
  have hPathTendsto :
      Tendsto (fun n : ℕ ↦ Wc ((τn n).toNNReal) ω) atTop (𝓝 (Wc τ.toNNReal ω)) := by
    -- Proof comment: once the exit clocks converge in time, continuity of the sample path turns
    -- that into convergence of the exit positions.
    exact (hWcCont ω).continuousAt.tendsto.comp hTimeTendsto
  have hStoppedValueEqStage :
      ∀ n : ℕ,
        stoppedValue Wc (hittingAfter Wc (U n)ᶜ 0) ω = Wc ((τn n).toNNReal) ω := by
    intro n
    have hτn_ne_top : τn n ≠ ⊤ := ne_of_lt (hτn_fin n)
    change Wc ((τn n).untopA) ω = Wc ((τn n).toNNReal) ω
    congr 1
    have hUntop :
        (((τn n).untopA : NNReal) : ENNReal) = τn n := by
      rw [WithTop.untopA_eq_untop hτn_ne_top]
      exact WithTop.coe_untop _ _
    have hToNN :
        (((τn n).toNNReal : NNReal) : ENNReal) = τn n := by
      rw [ENNReal.coe_toNNReal hτn_ne_top]
    exact ENNReal.coe_injective (hUntop.trans hToNN.symm)
  have hStoppedValueEqGlobal :
      stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω = Wc (τ.toNNReal) ω := by
    change Wc τ.untopA ω = Wc τ.toNNReal ω
    congr 1
    have hUntop : ((τ.untopA : NNReal) : ENNReal) = τ := by
      rw [WithTop.untopA_eq_untop hτ_ne_top]
      exact WithTop.coe_untop _ _
    have hToNN : ((τ.toNNReal : NNReal) : ENNReal) = τ := by
      rw [ENNReal.coe_toNNReal hτ_ne_top]
    exact ENNReal.coe_injective (hUntop.trans hToNN.symm)
  have hPathWithin :
      ∀ᶠ n : ℕ in atTop, Wc ((τn n).toNNReal) ω ∈ closure G := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hStartMem : Wc 0 ω ∈ U n := by
      simpa [hWcStart ω] using hUx n
    have hStageClosure :
        stoppedValue Wc (hittingAfter Wc (U n)ᶜ 0) ω ∈ closure (U n) := by
      exact
        stoppedValue_mem_closure_at_exit_of_lt_top
          (U := U n) (W := Wc) (ω := ω)
          (hUo n)
          (hWcCont ω)
          hStartMem
          (hτn_fin n)
    have hStageInG :
        stoppedValue Wc (hittingAfter Wc (U n)ᶜ 0) ω ∈ G := hUcl n hStageClosure
    -- Proof comment: each stage exit point already lies in `closure (U n) ⊆ G`, hence in
    -- `closure G`.
    exact subset_closure <| by simpa [hStoppedValueEqStage n] using hStageInG
  have hExitFiniteW :
      hittingAfter W Gᶜ 0 ω < ⊤ := by
    simpa [hEqWc.1] using hτfin
  have hExitStateWc :
      (exitValue ω : State) = stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω := by
    calc
      (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω := hExit ω hExitFiniteW
      _ = stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω := hEqWc.2
  have hLimitMem :
      Wc (τ.toNNReal) ω ∈ closure G := by
    have hFrontierMem : (exitValue ω : State) ∈ frontier G := (exitValue ω).2
    -- Proof comment: the transported global exit position is literally the frontier-valued exit
    -- datum, so it lies in `closure G`.
    simpa [hExitStateWc, hStoppedValueEqGlobal] using frontier_subset_closure hFrontierMem
  have hValueTendsto :
      Tendsto (fun n : ℕ ↦ u (Wc ((τn n).toNNReal) ω)) atTop (𝓝 (u (Wc τ.toNNReal ω))) := by
    apply (hu.continuousOn_closure (Wc τ.toNNReal ω) hLimitMem).tendsto.comp
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hPathTendsto hPathWithin
  have hDiagEventuallyEq :
      (fun n : ℕ ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω)) =ᶠ[atTop]
        fun n ↦ u (Wc ((τn n).toNNReal) ω) := by
    filter_upwards
        [tendsto_natCast_atTop_atTop.eventually_ge_atTop (τ.toNNReal)] with n hn
    have hτn_le_n : τn n ≤ (n : ENNReal) := by
      calc
        τn n ≤ τ := hτn_le_τ n
        _ = ((τ.toNNReal : NNReal) : ENNReal) := by rw [ENNReal.coe_toNNReal hτ_ne_top]
        _ ≤ n := by exact_mod_cast hn
    have hτn_ne_top : τn n ≠ ⊤ := ne_of_lt (hτn_fin n)
    have hStopEq :
        stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω = Wc ((τn n).toNNReal) ω := by
      have hStopUntop :
          stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω = Wc (τn n).untopA ω := by
        simpa [τn] using
          (stoppedProcess_eq_of_ge
            (u := Wc) (τ := hittingAfter Wc (U n)ᶜ 0) (ω := ω) (i := (n : NNReal)) hτn_le_n)
      have hTimeEq :
          (τn n).untopA = (τn n).toNNReal := by
        have hUntop :
            (((τn n).untopA : NNReal) : ENNReal) = τn n := by
          rw [WithTop.untopA_eq_untop hτn_ne_top]
          exact WithTop.coe_untop _ _
        have hToNN :
            (((τn n).toNNReal : NNReal) : ENNReal) = τn n := by
          rw [ENNReal.coe_toNNReal hτn_ne_top]
        exact ENNReal.coe_injective (hUntop.trans hToNN.symm)
      simpa [hTimeEq] using hStopUntop
    -- Proof comment: once the deterministic horizon dominates the stage exit clock, the
    -- diagonal stop is the actual stage exit value.
    simpa [hStopEq]
  have hBoundary :
      u (Wc (τ.toNNReal) ω) = f (exitValue ω) := by
    calc
      u (Wc (τ.toNNReal) ω) = u (stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω) := by
        rw [hStoppedValueEqGlobal]
      _ = u (exitValue ω : State) := by
        rw [← hExitStateWc]
      _ = f (exitValue ω) := hu.boundary_eq (exitValue ω)
  have hDiagTendsto :
      Tendsto
        (fun n : ℕ ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
        atTop
        (𝓝 (u (Wc τ.toNNReal ω))) :=
    Filter.Tendsto.congr' hDiagEventuallyEq.symm hValueTendsto
  -- Proof comment: the diagonal sequence is eventually the stage exit value, those stage exits
  -- converge to the global exit point, and the boundary relation identifies the terminal value.
  simpa [hBoundary] using hDiagTendsto

/-- Helper for Theorem 25.38: for a fixed start point, the stochastic proof reduces to a single
optional-stopping bridge after the deterministic geometry and domination data are packaged. -/
private theorem dirichletSolution_eq_exitExpectation_startedAt
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    {G : Set State} (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    {exitValue : Ω → frontier G}
    (hW : ∀ x : G, IsBrownianMotionVectorStartedAt (P x : Measure Ω) W x)
    (hExit :
      ∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    {f : frontier G → ℝ} {u : State → ℝ}
    (hu : SolvesDirichletProblem G f u)
    {x : State} (hx : x ∈ G) :
    u x = ∫ ω, f (exitValue ω) ∂(P x : Measure Ω) := by
  let μ : ProbabilityMeasure Ω := P x
  have hWx : IsBrownianMotionVectorStartedAt (μ : Measure Ω) W x := by
    simpa [μ] using hW ⟨x, hx⟩
  have hWcont :
      ∀ᵐ ω ∂(μ : Measure Ω), Continuous (fun t : NNReal ↦ W t ω) :=
    brownianVectorStartedAt_aeContinuous hWx
  have hStart :
      ∀ᵐ ω ∂(μ : Measure Ω), W 0 ω = x :=
    brownianVectorStart_ae_eq_const μ hWx
  have hClosureBound :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closure G, |u z| ≤ C :=
    existsAbsLeOnClosure hGcpt hu
  let _ := hWcont
  let _ := hStart
  let _ := hClosureBound
  let _ := hExit
  by_cases hd : d = 0
  · subst hd
    have hG_univ : G = Set.univ := by
      ext y
      constructor
      · intro hy
        simp
      · intro hy
        have hyx : y = x := Subsingleton.elim _ _
        simpa [hyx] using hx
    have hFrontierIsEmpty : IsEmpty (frontier G) := by
      rw [hG_univ, frontier_univ]
      infer_instance
    have hΩ_nonempty : Nonempty Ω := by
      by_contra hΩ
      have hUnivEmpty : (Set.univ : Set Ω) = ∅ := by
        ext ω
        exact False.elim (hΩ ⟨ω⟩)
      have hMeasureOne : (μ : Measure Ω) Set.univ = 1 := by
        simp
      rw [hUnivEmpty] at hMeasureOne
      norm_num at hMeasureOne
    rcases hΩ_nonempty with ⟨ω⟩
    exact False.elim (hFrontierIsEmpty.false (exitValue ω))
  · letI : NeZero d := ⟨hd⟩
    have hExitFinite :
        ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter W Gᶜ 0 ω < ⊤ :=
      ae_exitTime_lt_top_of_isCompact_closure_startedAt
        (x := x) hx hWx hG hGcpt
    rcases
        existsContinuousBrownianVectorStartedAtModification
          (μ := μ) (W := W) (x := x) hWx with
      ⟨Wc, hWc, hWcCont, hWcStart, hWcEq⟩
    have hExitEqWc :
        ∀ᵐ ω ∂(μ : Measure Ω),
          hittingAfter W Gᶜ 0 ω = hittingAfter Wc Gᶜ 0 ω ∧
            stoppedValue W (hittingAfter W Gᶜ 0) ω =
              stoppedValue Wc (hittingAfter Wc Gᶜ 0) ω :=
      stageExitStoppedValue_ae_eq_continuousVersion
        (μ := (μ : Measure Ω)) (W := W) (Wc := Wc) (U := G) hWcEq
    have hExitFiniteWc :
        ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc Gᶜ 0 ω < ⊤ := by
      filter_upwards [hExitFinite, hExitEqWc] with ω hω hEq
      simpa [hEq.1] using hω
    rcases hClosureBound with ⟨C, hCnonneg, hC⟩
    obtain ⟨U, hUo, hUx, hUcpt, hUcl, hUmono, hUunion⟩ :=
      existsInnerExhaustionStartingAt (G := G) hG hGcpt hx
    obtain ⟨Uext, hUextCont, hUextEq⟩ :=
      existsContinuousExtensionOnClosure (G := G) (u := u) hu.continuousOn_closure
    have hExitFiniteStage :
        ∀ n : ℕ,
          ∀ᵐ ω ∂(μ : Measure Ω), hittingAfter Wc (U n)ᶜ 0 ω < ⊤ := by
      intro n
      exact
        ae_exitTime_lt_top_of_isCompact_closure_startedAt
          (x := x) (hx := hUx n) hWc (hUo n) (hUcpt n)
    have hNatIdentity :
        ∀ n : ℕ,
          u x =
            ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω) := by
      intro n
      rcases
          exists_open_buffer_of_isCompact_subset_open
            (K := closure (U n))
            (hKcompact := hUcpt n)
            (hKG := hUcl n)
            (hGo := hG) with
        ⟨Tn, hTn_open, hTn_contains, hTn_closure_subset⟩
      rcases
          existsStageHarmonicExtension
            (V := closure (U n))
            (T := Tn)
            (G := G)
            (hVT := by simpa [closure_closure] using hTn_contains)
            (hTG := hTn_closure_subset)
            (hTo := hTn_open)
            hu.harmonicOnNhd with
        ⟨Fn, hFncontDiff, hFnharm, hFneq⟩
      have hStageClosureBound :
          ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ z ∈ closure (U n), |u z| ≤ Cn := by
        refine ⟨C, hCnonneg, ?_⟩
        intro z hz
        exact hC z (subset_closure (hUcl n hz))
      have hStageLocal :
          IsLocalMartingale
            (Filtration.natural Wc (brownianVectorStartedAt_stronglyMeasurable hWc))
            (μ : Measure Ω)
            (fun t ω ↦
              Fn (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) t ω) - Fn x) :=
        stageStoppedExtension_increment_isLocalMartingale
          (μ := μ) (W := Wc) (U := U n) (V := closure (U n)) (x := x) (F := Fn)
          (hUx n)
          hWc
          hWcCont
          (hUo n)
          (hUcpt n)
          (by intro z hz; exact hz)
          (hExitFiniteStage n)
          hFncontDiff
          hFnharm
      -- Proof comment: on each precompact stage `U n`, optional stopping applies to a global
      -- harmonic extension `Fn` and then transports back to `u` on `closure (U n)`.
      exact
        stageStoppedExtension_expectation_eq_atNat
          (μ := μ) (W := Wc) (U := U n) (x := x) (u := u) (F := Fn)
          (hUx n)
          (hUo n)
          hWc
          (Filter.Eventually.of_forall hWcCont)
          (Filter.Eventually.of_forall hWcStart)
          (hExitFiniteStage n)
          hFneq
          hStageClosureBound
          hStageLocal
          n
    have hMeasNat :
        ∀ n : ℕ,
          AEStronglyMeasurable
            (fun ω ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
            (μ : Measure Ω) := by
      intro n
      -- Proof comment: the fixed global continuous extension `Uext` is measurable, and on the
      -- stopped stage slice it agrees almost surely with `u` because the path stays in
      -- `closure (U n)`.
      exact
        stageStopped_eqOnClosure_aestronglyMeasurable_atNat
          (μ := μ) (W := Wc) (U := U n) (x := x) (u := u) (F := Uext)
          (hUx n)
          (hUo n)
          hWc
          hWcCont
          hWcStart
          (hExitFiniteStage n)
          hUextCont.measurable
          (fun z hz ↦ hUextEq (subset_closure (hUcl n hz)))
          n
    have hBoundNat :
        ∀ n : ℕ, ∀ᵐ ω ∂(μ : Measure Ω),
          |u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω)| ≤ C := by
      intro n
      filter_upwards [hExitFiniteStage n] with ω hωfin
      have hStartMem : Wc 0 ω ∈ U n := by
        simpa [hWcStart ω] using hUx n
      have hmem :
          stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω ∈ closure G := by
        exact
          subset_closure <|
            hUcl n <|
              stageStoppedProcess_mem_buffer
                (U := U n) (V := closure (U n)) (W := Wc) (ω := ω)
                (hUo n)
                (hWcCont ω)
                hStartMem
                (by intro z hz; exact hz)
                hωfin
                n
      exact hC _ hmem
    have hDiagonalLimit :
        ∀ᵐ ω ∂(μ : Measure Ω),
          Tendsto
            (fun n : ℕ ↦ u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω))
            atTop
            (𝓝 (f (exitValue ω))) := by
      -- Proof comment: the remaining geometric convergence step is now isolated to the inner
      -- exhaustion and the transported exit-value identity.
      exact
        tendsto_innerStageExitDirichlet_to_boundaryValue
          (μ := μ) (W := W) (Wc := Wc) (G := G) (x := x) (U := U)
          (exitValue := exitValue) (f := f) (u := u)
          hx hG hUo hUx hUcl hUmono hUunion hWcCont hWcStart hExitFiniteWc hExitEqWc hExit hu
    have hIntegralTendsto :
        Tendsto
          (fun n : ℕ ↦
            ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω))
          atTop
          (𝓝 (∫ ω, f (exitValue ω) ∂(μ : Measure Ω))) := by
      exact
        MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun _ ↦ C)
          hMeasNat
          (integrable_const C)
          hBoundNat
          hDiagonalLimit
    have hConstTendsto :
        Tendsto
          (fun n : ℕ ↦
            ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω))
          atTop
          (𝓝 (u x)) := by
      have hSeqEq :
          (fun n : ℕ ↦
            ∫ ω, u (stoppedProcess Wc (hittingAfter Wc (U n)ᶜ 0) n ω) ∂(μ : Measure Ω)) =
            fun _ : ℕ ↦ u x := by
        funext n
        exact (hNatIdentity n).symm
      simpa [hSeqEq] using tendsto_const_nhds
    let _ := hWc
    let _ := hWcCont
    let _ := hWcStart
    let _ := hExitFiniteWc
    let _ := hExitEqWc
    -- Proof comment: the stagewise optional-stopping identities and the dominated-convergence
    -- setup are now explicit, so uniqueness of the limit yields the desired exit expectation.
    exact (tendsto_nhds_unique hIntegralTendsto hConstTendsto).symm

/-- Theorem 25.38: a Dirichlet solution agrees with the boundary datum evaluated at the Brownian
exit position, equivalently with the integral against harmonic measure. -/
theorem dirichlet_solution_eq_exit_expectation
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    {G : Set State} (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    {exitValue : Ω → frontier G} (hExitMeas : Measurable exitValue)
    (hW : ∀ x : G, IsBrownianMotionVectorStartedAt (P x : Measure Ω) W x)
    (hExit :
      ∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    {f : frontier G → ℝ} {u : State → ℝ}
    (hu : SolvesDirichletProblem G f u) :
    ∀ {x : State} (hx : x ∈ G),
      u x = ∫ ω, f (exitValue ω) ∂(P x : Measure Ω) ∧
        u x =
          ∫ y, f y ∂(harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ :
            Measure (frontier G)) := by
  intro x hx
  have hExitRep : u x = ∫ ω, f (exitValue ω) ∂(P x : Measure Ω) := by
    -- Proof comment: the public theorem now delegates the stochastic core to the fixed-start
    -- helper, while the harmonic-measure rewrite remains a separate deterministic layer.
    exact
      dirichletSolution_eq_exitExpectation_startedAt
        (P := P) (W := W) (G := G) hG hGcpt hW hExit hu hx
  refine ⟨hExitRep, ?_⟩
  exact
    dirichlet_solution_eq_harmonicMeasureIntegralCore
      P hExitMeas hGcpt hu hx hExitRep

/-- Helper for Theorem 25.38: once the exit representation holds for a fixed Brownian family,
two Dirichlet solutions with the same boundary datum agree on `closure G`. -/
theorem dirichletSolutions_eqOnClosure_of_exitRepresentation
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
    {G : Set State} (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    {exitValue : Ω → frontier G} (hExitMeas : Measurable exitValue)
    (hW : ∀ x : G, IsBrownianMotionVectorStartedAt (P x : Measure Ω) W x)
    (hExit :
      ∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    {f : frontier G → ℝ} {u v : State → ℝ}
    (hu : SolvesDirichletProblem G f u) (hv : SolvesDirichletProblem G f v) :
    Set.EqOn u v (closure G) := by
  intro x hxClosure
  classical
  by_cases hx : x ∈ G
  · have huRep :=
      (dirichlet_solution_eq_exit_expectation
        (P := P) (W := W) (G := G) hG hGcpt
        (exitValue := exitValue) hExitMeas hW hExit (f := f) (u := u) hu hx).1
    have hvRep :=
      (dirichlet_solution_eq_exit_expectation
        (P := P) (W := W) (G := G) hG hGcpt
        (exitValue := exitValue) hExitMeas hW hExit (f := f) (u := v) hv hx).1
    -- Proof comment: inside `G`, both solutions are identified with the same exit expectation.
    exact huRep.trans hvRep.symm
  · have hxFrontier : x ∈ frontier G := by
      -- Proof comment: on an open set, points of `closure G` outside `G` lie on the frontier.
      rw [frontier, hG.interior_eq]
      exact ⟨hxClosure, hx⟩
    -- Proof comment: on the frontier, both solutions agree with the common boundary datum `f`.
    calc
      u x = f ⟨x, hxFrontier⟩ := hu.boundary_eq ⟨x, hxFrontier⟩
      _ = v x := (hv.boundary_eq ⟨x, hxFrontier⟩).symm

end ProbabilityTheory
