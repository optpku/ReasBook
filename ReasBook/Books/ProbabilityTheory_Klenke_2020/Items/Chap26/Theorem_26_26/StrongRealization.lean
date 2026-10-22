/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.GeneralizedStrongSolutionAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_10

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ

/-- Helper for Theorem 26.26: package a measurable state-only raw restart solver into the
fixed-start restart kernel used by the `n`-dimensional strong-Markov API. -/
private noncomputable def stateRestartKernelOfRaw
    {β : Type*} [MeasurableSpace β]
    (noiseKernel : Kernel State β)
    (restartRaw : (State × β) → (NNReal → State))
    (hRestartRaw : Measurable restartRaw) :
    Kernel State (NNReal → State) :=
  Kernel.deterministic restartRaw hRestartRaw ∘ₖ (Kernel.id ×ₖ noiseKernel)

/-- Helper for Theorem 26.26: each row of `stateRestartKernelOfRaw` is the pushforward of the
corresponding noise row under the measurable state-only restart solver. -/
private theorem integral_stateRestartKernelOfRaw_apply
    {β : Type*} [MeasurableSpace β]
    (noiseKernel : Kernel State β)
    [IsSFiniteKernel noiseKernel]
    (restartRaw : (State × β) → (NNReal → State))
    (hRestartRaw : Measurable restartRaw)
    (x : State)
    {f : (NNReal → State) → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂ stateRestartKernelOfRaw noiseKernel restartRaw hRestartRaw x =
      ∫ z, f (restartRaw (x, z)) ∂ noiseKernel x := by
  have hMap :
      stateRestartKernelOfRaw noiseKernel restartRaw hRestartRaw =
        (Kernel.id ×ₖ noiseKernel).map restartRaw := by
    simpa [stateRestartKernelOfRaw] using
      (Kernel.deterministic_comp_eq_map hRestartRaw (Kernel.id ×ₖ noiseKernel))
  have hProdMap :
      (Kernel.id ×ₖ noiseKernel) x = Measure.map (Prod.mk x) (noiseKernel x) := by
    ext s hs
    rw [Kernel.id_prod_apply' noiseKernel x hs, Measure.map_apply (by fun_prop) hs]
  rw [hMap, Kernel.map_apply _ hRestartRaw x]
  rw [MeasureTheory.integral_map hRestartRaw.aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable]
  rw [hProdMap]
  exact
    MeasureTheory.integral_map
      ((by
        have hMeas : Measurable (Prod.mk x : β → State × β) := by
          fun_prop
        exact hMeas.aemeasurable))
      ((hf.comp hRestartRaw).stronglyMeasurable.aestronglyMeasurable)

/-- Helper for Theorem 26.26: once the restart identity is written using a measurable state-only
raw solver, the fixed-start strong-Markov kernel is obtained by packaging that solver rowwise. -/
theorem existsStateRestartKernel_of_measurableRestartRaw
    {β : Type*} [MeasurableSpace β]
    (noiseKernel : Kernel State β)
    [IsSFiniteKernel noiseKernel]
    (restartRaw : (State × β) → (NNReal → State))
    (hRestartRaw : Measurable restartRaw)
    {Ω : Type u} [MeasurableSpace Ω]
    {X : NNReal → Ω → State}
    {P : ProbabilityMeasure Ω}
    (hRestart :
      ∀ (τ : Ω → WithTop NNReal)
        (hτ : IsStoppingTime (processFiltration X) τ),
        (∀ᵐ ω ∂(P : Measure Ω), τ ω ≠ ⊤) →
        ∀ (f : (NNReal → State) → ℝ),
          Measurable f →
          (∃ C : ℝ, ∀ y, |f y| ≤ C) →
          ((P : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) |
            hτ.measurableSpace]) =ᵐ[(P : Measure Ω)] fun ω ↦
              ∫ z, f (restartRaw (stoppedValue X τ ω, z)) ∂ noiseKernel
                (stoppedValue X τ ω)) :
    ∃ κ : Kernel State (NNReal → State),
      HasStrongMarkovPropertyAtStartNDim P X κ := by
  let κ : Kernel State (NNReal → State) :=
    stateRestartKernelOfRaw noiseKernel restartRaw hRestartRaw
  refine ⟨κ, ?_⟩
  intro τ hτ hτfinite f hf hbounded
  have hRow :
      (fun ω ↦
        ∫ z, f (restartRaw (stoppedValue X τ ω, z)) ∂
          noiseKernel (stoppedValue X τ ω)) =
        fun ω ↦
          ∫ y, f y ∂ κ (stoppedValue X τ ω) := by
    funext ω
    symm
    exact
      integral_stateRestartKernelOfRaw_apply
        noiseKernel
        restartRaw
        hRestartRaw
        (stoppedValue X τ ω)
        hf
  -- Proof comment: after replacing each stopped-state row by the packaged restart kernel row, the
  -- assumed restart identity is exactly the fixed-start strong-Markov statement.
  simpa [κ, hRow] using hRestart τ hτ hτfinite f hf hbounded

/-- Helper for Theorem 26.26: a path-valued strong solution already packages as the process-level
pathwise strong realization used in clause (3). -/
theorem hasPathwiseStrongSolutionRealization_of_strongSolution
    {Ω : Type u} [MeasurableSpace Ω]
    {σ : NNReal → State → Fin n → Fin m → ℝ}
    {b : NNReal → State → Fin n → ℝ}
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (P : ProbabilityMeasure Ω)
    (x : State)
    {Wpath : Ω → EuclideanPathSpace m} {Xpath : Ω → EuclideanPathSpace n}
    (hStrong :
      StrongSolution n m
        (fun ξ W' X' ↦ SolvesStrongGeneralizedSDE σ b (P : Measure Ω) ℱ ξ W' X')
        (fun _ ↦ x)
        Wpath
        Xpath) :
    HasPathwiseStrongSolutionRealization
      (IsBrownianMotionWithFiltration ℱ (P : Measure Ω))
      (fun ξ W X ↦ IsGeneralizedNDimensionalDiffusion ℱ (P : Measure Ω) ξ W σ b X)
      ℱ
      (fun _ ↦ x)
      (pathProcess Wpath)
      (pathProcess Xpath) := by
  rcases hStrong with ⟨F, hRealization, hSolves⟩
  rcases hSolves with ⟨_, hDiffusion⟩
  refine ⟨?_, Wpath, rfl, Xpath, rfl, ?_⟩
  · rcases hDiffusion with ⟨hBrownian, N, hIto, hbProg, hbInt, hStateEq⟩
    refine ⟨?_, ?_, hBrownian, ?_⟩
    · intro i
      have hXpathAdapted : Adapted ℱ (fun t ω ↦ Xpath ω t) := by
        -- Proof comment: the exact realization identity lets the operator measurability control
        -- the solved path itself.
        simpa [hRealization] using
          StrongSolutionOperator.adaptedPathProcessRealization
            F
            measurable_const
            hBrownian.2
      have hCoordAdapted : Adapted ℱ (fun t ω ↦ Xpath ω t i) := by
        intro t
        exact (measurable_pi_apply i).comp (hXpathAdapted t)
      -- Proof comment: continuous adapted coordinate paths are progressively measurable.
      exact
        (Adapted.stronglyAdapted hCoordAdapted).progMeasurable_of_continuous
          (fun ω ↦ (continuous_apply i).comp (Xpath ω).continuous)
    · intro i ω
      -- Proof comment: coordinate continuity is inherited from the ambient continuous path.
      exact (continuous_apply i).comp (Xpath ω).continuous
    · -- Proof comment: the strong-solution clause already carries the generalized diffusion
      -- equation in process form once the path lifts are evaluated.
      exact ⟨hBrownian, N, hIto, hbProg, hbInt, hStateEq⟩
  · -- Proof comment: keep the same strong-solution operator witness and only rewrite the ambient
    -- solution relation from path variables to their process evaluations.
    exact ⟨F, hRealization, hDiffusion⟩

/-- Helper for Theorem 26.26: on any fixed Brownian path witness, a Dirac-law unique-strong owner
already yields one exact pathwise strong realization on that same witness space. -/
theorem diracPathwiseStrongRealization_onBrownianPath
    {Ω : Type u} [MeasurableSpace Ω]
    {σ : NNReal → State → Fin n → Fin m → ℝ}
    {b : NNReal → State → Fin n → ℝ}
    (P : ProbabilityMeasure Ω)
    (Wpath : Ω → EuclideanPathSpace m)
    (hWpath :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Wpath))
        (P : Measure Ω)
        (pathProcess Wpath))
    {x : State}
    (hStrong :
      HasUniqueStrongSolution
        GeneralizedSDEBrownianMotion
        (SolvesStrongGeneralizedSDE σ b)
        (Measure.dirac x)) :
    ∃ Xpath : Ω → EuclideanPathSpace n,
      HasPathwiseStrongSolutionRealization
        (IsBrownianMotionWithFiltration
          (processFiltration (pathProcess Wpath))
          (P : Measure Ω))
        (fun ξ W X ↦
          IsGeneralizedNDimensionalDiffusion
            (processFiltration (pathProcess Wpath))
            (P : Measure Ω)
            ξ
            W
            σ
            b
            X)
        (processFiltration (pathProcess Wpath))
        (fun _ ↦ x)
        (pathProcess Wpath)
        (pathProcess Xpath) := by
  rcases hStrong with ⟨F, hF⟩
  let ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω) :=
    processFiltration (pathProcess Wpath)
  let Xpath : Ω → EuclideanPathSpace n := F.realization (fun _ : Ω ↦ x) Wpath
  have hBrownianData :
      GeneralizedSDEBrownianMotion (P : Measure Ω) ℱ Wpath := by
    -- Proof comment: the chosen path-valued Brownian witness already matches the generalized
    -- Brownian-motion owner after repackaging its filtration witness.
    exact ⟨inferInstance, hWpath⟩
  have hStrongRealization :
      StrongSolution n m
        (fun ξ W' X' ↦ SolvesStrongGeneralizedSDE σ b (P : Measure Ω) ℱ ξ W' X')
        (fun _ : Ω ↦ x)
        Wpath
        Xpath := by
    refine ⟨F, rfl, ?_⟩
    -- Proof comment: specialize the unique-strong operator to the fixed Brownian witness and the
    -- constant deterministic initial datum `x`.
    exact
      hF.solves_all_inputs
        (P : Measure Ω)
        ℱ
        (fun _ : Ω ↦ x)
        Wpath
        hBrownianData
        measurable_const
        (indepFun_const_left x Wpath)
        (hasLaw_const_dirac_forProbability (P : Measure Ω) x)
  refine ⟨Xpath, ?_⟩
  -- Proof comment: once the path-valued strong solution is fixed, the earlier support theorem
  -- turns it into the process-level pathwise realization required by clause (3).
  exact
    hasPathwiseStrongSolutionRealization_of_strongSolution
      (σ := σ)
      (b := b)
      (P := P)
      (x := x)
      hStrongRealization

end ProbabilityTheory
