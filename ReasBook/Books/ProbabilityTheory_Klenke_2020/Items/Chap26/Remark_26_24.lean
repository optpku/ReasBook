/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_22.Support

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

section

variable (σ : DiffusionCoeff)

local notation "σσᵀ" => diffusionMatrixOfCoefficient σ

/-- Helper for Remark 26.24: a constant random state on a probability space has Dirac law at its
value. -/
theorem hasLaw_const_dirac_forProbability
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (x : State) :
    HasLaw (fun _ : Ω ↦ x) (Measure.dirac x) P := by
  -- Proof comment: pushing a probability measure forward along a constant map produces the
  -- corresponding Dirac measure.
  refine ⟨measurable_const.aemeasurable, ?_⟩
  simpa using (Measure.map_const P x)

/-- Helper for Remark 26.24: a random state whose law is `δ_x` is almost surely equal to the
constant state `x`. -/
theorem aeEq_const_of_diracLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → State} {x : State}
    (hξ : HasLaw ξ (Measure.dirac x) P) :
    ξ =ᵐ[P] fun _ ↦ x := by
  -- Proof comment: `HasLaw.ae_iff` transfers the full-measure singleton event under `δ_x` back to
  -- the original probability space.
  change ∀ᵐ ω ∂P, ξ ω = x
  exact (hξ.ae_iff (p := fun y : State ↦ y = x) (by fun_prop)).2 (by simp)

/-- Helper for Remark 26.24: any Dirac-start local-martingale-problem solution starts at the
deterministic point `x` almost surely. -/
theorem aeEq_pathStart_const_of_diracLocalMartingaleProblemSolution
    {a : NNReal → State → Fin n → Fin n → ℝ} {b : DriftCoeff}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    {μ : Measure Ω} {X : Ω → EuclideanPathSpace n} {x : State}
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X) :
    (fun ω ↦ X ω 0) =ᵐ[μ] fun _ ↦ x := by
  -- Proof comment: the initial-law field of `hX` is already a Dirac-law statement, so the
  -- general `aeEq_const_of_diracLaw` bridge applies directly to the time-zero coordinate.
  exact aeEq_const_of_diracLaw hX.initial_law

/-- Helper for Remark 26.24: each coordinate of a Dirac-start local-martingale-problem solution
starts from the corresponding deterministic coordinate of `x` almost surely. -/
theorem aeEq_pathStart_coordinate_const_of_diracLocalMartingaleProblemSolution
    {a : NNReal → State → Fin n → Fin n → ℝ} {b : DriftCoeff}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    {μ : Measure Ω} {X : Ω → EuclideanPathSpace n} {x : State}
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X) (i : Fin n) :
    (fun ω ↦ X ω 0 i) =ᵐ[μ] fun _ ↦ x i := by
  -- Proof comment: apply the path-valued almost-sure identity at time `0` and project to the
  -- `i`-th coordinate.
  filter_upwards
      [aeEq_pathStart_const_of_diracLocalMartingaleProblemSolution (hX := hX)] with ω hω
  exact congrArg (fun y : State ↦ y i) hω

/-- Helper for Remark 26.24: the standard martingale part starts from the initial coordinate
value because the drift integral over `[0, 0]` vanishes. -/
theorem localMartingaleProblemMartingalePart_zero
    {b : DriftCoeff} {Ω : Type u} [MeasurableSpace Ω]
    {X : Ω → EuclideanPathSpace n} (i : Fin n) (ω : Ω) :
    localMartingaleProblemMartingalePart b X i 0 ω = X ω 0 i := by
  -- Proof comment: unfold the martingale part at time `0` and use that the drift integral on a
  -- degenerate interval is zero.
  rw [localMartingaleProblemMartingalePart_apply]
  simp

/-- Helper for Remark 26.24: subtracting the time-zero value from the standard martingale part
produces the centered coordinate increment used in the source formulation. -/
theorem localMartingaleProblemMartingalePart_sub_zero
    {b : DriftCoeff} {Ω : Type u} [MeasurableSpace Ω]
    {X : Ω → EuclideanPathSpace n} (i : Fin n) (t : NNReal) (ω : Ω) :
    localMartingaleProblemMartingalePart b X i t ω -
        localMartingaleProblemMartingalePart b X i 0 ω =
      X ω t i - X ω 0 i -
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X ω s.toNNReal) i := by
  -- Proof comment: expand the martingale part at time `t`, rewrite the zero-time term using the
  -- previous lemma, and then normalize the resulting scalar identity.
  rw [localMartingaleProblemMartingalePart_apply, localMartingaleProblemMartingalePart_zero]
  ring

/-- Helper for Remark 26.24: for a Dirac-start local martingale problem solution, the time-zero
standard martingale part in coordinate `i` is almost surely the deterministic value `x i`. -/
theorem aeEq_localMartingaleProblemMartingalePart_zero_const_of_diracLocalMartingaleProblemSolution
    {a : NNReal → State → Fin n → Fin n → ℝ} {b : DriftCoeff}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    {μ : Measure Ω} {X : Ω → EuclideanPathSpace n} {x : State}
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X) (i : Fin n) :
    (fun ω ↦ localMartingaleProblemMartingalePart b X i 0 ω) =ᵐ[μ] fun _ ↦ x i := by
  -- Proof comment: first rewrite the zero-time compensated coordinate as the actual initial
  -- coordinate, then use the already established Dirac-start identification of `X 0`.
  filter_upwards
      [aeEq_pathStart_coordinate_const_of_diracLocalMartingaleProblemSolution (hX := hX) i]
      with ω hω
  rw [localMartingaleProblemMartingalePart_zero]
  exact hω

/-- Helper for Remark 26.24: for a Dirac-start local martingale problem solution, the centered
standard martingale part agrees almost surely with the source-style increment centered at `x`. -/
theorem aeEq_localMartingaleProblemMartingalePart_sub_zero_dirac
    {a : NNReal → State → Fin n → Fin n → ℝ} {b : DriftCoeff}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    {μ : Measure Ω} {X : Ω → EuclideanPathSpace n} {x : State}
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X)
    (i : Fin n) (t : NNReal) :
    (fun ω ↦
      localMartingaleProblemMartingalePart b X i t ω -
        localMartingaleProblemMartingalePart b X i 0 ω) =ᵐ[μ]
      fun ω ↦
        X ω t i - x i -
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X ω s.toNNReal) i := by
  -- Proof comment: expand the centered standard martingale part pointwise and then replace the
  -- random initial coordinate by the deterministic Dirac start `x i`.
  filter_upwards
      [aeEq_pathStart_coordinate_const_of_diracLocalMartingaleProblemSolution (hX := hX) i]
      with ω hω
  rw [localMartingaleProblemMartingalePart_sub_zero]
  simpa [hω]

/-- Helper for Remark 26.24: well-posedness is exactly the family of Dirac-start existence and
unique-law assertions spelled out in Definition 26.23. -/
theorem localMartingaleProblemWellPosed_of_diracData
    {a : NNReal → State → Fin n → Fin n → ℝ} {b : DriftCoeff}
    (h :
      ∀ x : State,
        (∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → EuclideanPathSpace n),
          IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ (P : Measure Ω) X) ∧
            LocalMartingaleProblemHasUniqueLaw.{u, v} (Measure.dirac x) a b) :
    LocalMartingaleProblemWellPosed.{u, v} a b := by
  -- Proof comment: this is just the defining `iff` for well-posedness, repackaged so the main
  -- theorem can focus on producing the Dirac-start data from Theorems 26.8, 26.18, and 26.21.
  exact (localMartingaleProblemWellPosed_iff).2 h

/-- Helper for Remark 26.24: the pointwise bounds in the remark are exactly the Chapter 26
Lipschitz and linear-growth hypotheses. -/
theorem sdeLipschitzAndLinearGrowth_of_remarkHypotheses
    {b : DriftCoeff} {K : ℝ}
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2)) :
    SDESpaceLipschitzWith K b σ ∧ SDELinearGrowthWith K b σ := by
  -- Proof comment: the remark states the two Chapter 26 coefficient conditions in fully
  -- unfolded form, so the packaging is only a definitional rewrite.
  exact
    ⟨by
        simpa [SDESpaceLipschitzWith] using hbσ_lipschitz,
      by
        simpa [SDELinearGrowthWith] using hbσ_growth⟩

/-- Helper for Remark 26.24: the remark hypotheses give a unique strong generalized SDE solution
for each deterministic initial law `δ_x`. -/
theorem diracHasUniqueStrongSolution_of_lipschitzLinearGrowth
    {b : DriftCoeff} {K : ℝ}
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2))
    (x : State) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE σ b)
      (Measure.dirac x) := by
  -- Proof comment: first package the remark bounds into the Chapter 26 coefficient owners, then
  -- apply Theorem 26.8 at the deterministic start `x`.
  rcases
      sdeLipschitzAndLinearGrowth_of_remarkHypotheses
        (σ := σ)
        (b := b)
        hbσ_lipschitz
        hbσ_growth with
    ⟨hLipschitz, hGrowth⟩
  exact
    hasUniqueStrongSolution_of_lipschitz_linearGrowth
      (b := b)
      (σ := σ)
      hLipschitz
      hGrowth
      x

/-- Helper for Remark 26.24: Theorem 26.18 upgrades the deterministic-start strong solution from
Theorem 26.8 to generalized weak existence for the same Dirac initial law. -/
theorem diracGeneralizedWeakExistence_of_lipschitzLinearGrowth
    {b : DriftCoeff} {K : ℝ}
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2))
    (x : State) :
    Nonempty (GeneralizedWeakSDESolution (Measure.dirac x) σ b) := by
  have hStrong :
      HasUniqueStrongSolution
        GeneralizedSDEBrownianMotion
        (SolvesStrongGeneralizedSDE σ b)
        (Measure.dirac x) :=
    diracHasUniqueStrongSolution_of_lipschitzLinearGrowth
      (σ := σ)
      (b := b)
      hbσ_lipschitz
      hbσ_growth
      x
  -- Proof comment: once the deterministic-start strong owner is available, the `26.18`
  -- existence theorem supplies one generalized weak solution with the same Dirac initial law.
  exact
    weakExistence_of_hasUniqueStrongGeneralizedSDESolution
      (σ := σ)
      (b := b)
      (μ₀ := Measure.dirac x)
      hStrong

/-- Helper for Remark 26.24: Theorem 26.18 also upgrades the deterministic-start strong solution
from Theorem 26.8 to weak uniqueness for every generalized weak solution with initial law `δ_x`.
-/
theorem diracGeneralizedWeakUniqueness_of_lipschitzLinearGrowth
    {b : DriftCoeff} {K : ℝ}
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2))
    (x : State) :
    ∀ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b, L.IsWeaklyUnique := by
  have hStrong :
      HasUniqueStrongSolution
        GeneralizedSDEBrownianMotion
        (SolvesStrongGeneralizedSDE σ b)
        (Measure.dirac x) :=
    diracHasUniqueStrongSolution_of_lipschitzLinearGrowth
      (σ := σ)
      (b := b)
      hbσ_lipschitz
      hbσ_growth
      x
  intro L
  -- Proof comment: the `26.18` uniqueness theorem turns the same deterministic-start strong
  -- owner into equality of state-path laws for every generalized weak realization.
  exact
    generalizedWeakSolution_isWeaklyUnique_of_hasUniqueStrongGeneralizedSDESolution
      (σ := σ)
      (b := b)
      (μ₀ := Measure.dirac x)
      hStrong
      L

/-- Helper for Remark 26.24: the theorem chain `26.8 -> 26.18` already yields both generalized
weak existence and generalized weak uniqueness at every deterministic start `x`. -/
theorem diracGeneralizedWeakData_of_lipschitzLinearGrowth
    {b : DriftCoeff} {K : ℝ}
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2))
    (x : State) :
    Nonempty (GeneralizedWeakSDESolution (Measure.dirac x) σ b) ∧
      ∀ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b, L.IsWeaklyUnique := by
  -- Proof comment: package the two `26.18` consequences together so the remaining frontier in
  -- the main theorem is purely the missing bridge to the local martingale problem surface.
  refine ⟨?_, ?_⟩
  · exact
      diracGeneralizedWeakExistence_of_lipschitzLinearGrowth
        (σ := σ)
        (b := b)
        hbσ_lipschitz
        hbσ_growth
        x
  · exact
      diracGeneralizedWeakUniqueness_of_lipschitzLinearGrowth
        (σ := σ)
        (b := b)
        hbσ_lipschitz
        hbσ_growth
        x

/-- Helper for Remark 26.24: the deterministic-start `26.8 -> 26.18` chain already produces one
generalized weak SDE solution that is weakly unique among all Dirac-start generalized weak
solutions. -/
theorem exists_diracWeaklyUniqueGeneralizedWeakSolution_of_lipschitzLinearGrowth
    {b : DriftCoeff} {K : ℝ}
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2))
    (x : State) :
    ∃ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b, L.IsWeaklyUnique := by
  rcases
      diracGeneralizedWeakExistence_of_lipschitzLinearGrowth
        (σ := σ)
        (b := b)
        hbσ_lipschitz
        hbσ_growth
        x with
    ⟨L⟩
  -- Proof comment: once one deterministic-start generalized weak solution exists, the `26.18`
  -- uniqueness clause upgrades that witness itself to a weakly unique one.
  exact
    ⟨L,
      diracGeneralizedWeakUniqueness_of_lipschitzLinearGrowth
        (σ := σ)
        (b := b)
        hbσ_lipschitz
        hbσ_growth
        x
        L⟩

/-- Helper for Remark 26.24: all deterministic-start generalized weak SDE solutions share one
canonical state-path law under the remark hypotheses. -/
theorem exists_diracGeneralizedWeakCanonicalLaw_of_lipschitzLinearGrowth
    {b : DriftCoeff} {K : ℝ}
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2))
    (x : State) :
    ∃ ν : Measure PathSpace,
      ∀ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b, L.statePathLaw = ν := by
  rcases
      exists_diracWeaklyUniqueGeneralizedWeakSolution_of_lipschitzLinearGrowth
        (σ := σ)
        (b := b)
        hbσ_lipschitz
        hbσ_growth
        x with
    ⟨L₀, hL₀⟩
  refine ⟨L₀.statePathLaw, ?_⟩
  intro L
  -- Proof comment: weak uniqueness identifies every deterministic-start generalized weak law
  -- with the chosen witness law `L₀.statePathLaw`.
  exact hL₀ L

/-- Helper for Remark 26.24: unpacking `L.solvesGeneralizedDiffusion` exposes a diffusion term `N`
whose `i`-th coordinate is exactly the source-centered martingale part of `L`. -/
theorem GeneralizedWeakSDESolution.exists_diffusionTerm_for_sourceMartingalePart
    {b : DriftCoeff} {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    (L : GeneralizedWeakSDESolution μ₀ σ b) (i : Fin n) :
    ∃ N : NNReal → L.Ω → State,
      IsMatrixBrownianLocalItoIntegral
        L.ℱ
        L.μ
        L.W
        (fun t ω i j ↦ σ t (L ω t) i j)
        N ∧
      sourceLocalMartingaleProblemMartingalePart b L i = fun t ω ↦ N t ω i := by
  rcases L.solvesGeneralizedDiffusion with
    ⟨_hBrownian, N, hIto, _hDriftMeas, _hDriftInt, hStateEq⟩
  refine ⟨N, hIto, ?_⟩
  -- Proof comment: rewrite the state equation coordinatewise and cancel the shared initial datum
  -- and drift integral against the source-centered definition.
  funext t ω
  have hInitialState : L ω 0 = L.ξ ω := L.initialState_eq ω
  have hInitialCoordinate : L ω 0 i = L.ξ ω i := by
    simpa using congrArg (fun x : State ↦ x i) hInitialState
  have hStateCoordinate := congrFun (congrFun (congrFun hStateEq t) ω) i
  calc
    sourceLocalMartingaleProblemMartingalePart b L i t ω =
        L ω t i - L ω 0 i -
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal) i := by
            rfl
    _ =
        (L.ξ ω i +
            N t ω i +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal) i) -
          L ω 0 i -
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal) i := by
              rw [hStateCoordinate]
    _ = N t ω i := by
      rw [hInitialCoordinate]
      ring

/-- Helper for Remark 26.24: evaluating the ordinary martingale-part formula on the canonical
process `id` after a realization map `X` is the same as evaluating the original formula before
pushforward. -/
theorem localMartingaleProblemMartingalePart_id_comp_path
    {b : DriftCoeff} {Ω : Type u} [MeasurableSpace Ω]
    {X : Ω → PathSpace} (i : Fin n) (t : NNReal) (ω : Ω) :
    localMartingaleProblemMartingalePart b id i t (X ω) =
      localMartingaleProblemMartingalePart b X i t ω := by
  -- Proof comment: both sides unfold to the same compensated coordinate once the identity path
  -- map is evaluated at `X ω`.
  simp [localMartingaleProblemMartingalePart]

/-- Helper for Remark 26.24: the prescribed covariation process is unchanged when the canonical
process `id` is evaluated on a pushed-forward path law. -/
theorem localMartingaleProblemCovariation_id_comp_path
    {a : NNReal → State → Fin n → Fin n → ℝ}
    {Ω : Type u} [MeasurableSpace Ω]
    {X : Ω → PathSpace} (i j : Fin n) (t : NNReal) (ω : Ω) :
    localMartingaleProblemCovariation a id i j t (X ω) =
      localMartingaleProblemCovariation a X i j t ω := by
  -- Proof comment: unfolding the two compensators shows that the identity-path spelling and the
  -- original realization spelling agree pointwise.
  simp [localMartingaleProblemCovariation]

/-- Helper for Remark 26.24: deterministic-time evaluation on canonical path space is measurable.
-/
theorem measurable_path_eval (t : NNReal) :
    Measurable (ContinuousMap.evalCLM ℝ t : PathSpace → State) := by
  -- Proof comment: evaluation at a fixed time is continuous on the continuous-path space, hence
  -- measurable.
  simpa using (continuous_eval_const t).measurable

/-- Helper for Remark 26.24: the canonical filtration on `PathSpace` is the filtration generated
by the coordinate process `t ↦ ω t`. -/
abbrev canonicalPathFiltration : Filtration NNReal (borel PathSpace) :=
  generatedFiltration
    (fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State))
    measurable_path_eval

/-- Helper for Remark 26.24: the canonical coordinate process on path space is adapted to its own
generated filtration by construction. -/
private theorem adapted_pathProcess_id_generatedFiltration :
    Adapted canonicalPathFiltration (pathProcess (id : PathSpace → PathSpace)) := by
  -- Proof comment: the generated filtration is the smallest filtration making every coordinate
  -- evaluation measurable, which is exactly the canonical process `pathProcess id`.
  rw [adapted_iff_generatedFiltration_le measurable_path_eval]
  intro t
  exact le_rfl

/-- Helper for Remark 26.24: the time-zero slice of a continuous local martingale is integrable
because every localizing sequence stops it to the same value at time `0`. -/
theorem integrable_timeZero_of_isContinuousLocalMartingale
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    Integrable (fun ω ↦ M 0 ω) μ := by
  rcases hM.localizing_sequence with ⟨τSeq, hτSeq⟩
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨_, _, hStopped⟩
  have hStoppedAtZero : stoppedProcess M (τSeq 0) 0 = M 0 := by
    funext ω
    -- Proof comment: every stopping time is bounded below by `0`, so stopping does nothing at
    -- time `0`.
    exact stoppedProcess_eq_of_le (by simp)
  -- Proof comment: the localized martingale is integrable at time `0`, and this slice is
  -- exactly the original initial value.
  simpa [hStoppedAtZero] using (hStopped 0).1.integrable 0

/-- Helper for Remark 26.24: freezing a continuous local martingale at time `0` yields a
time-constant continuous local martingale. -/
theorem isContinuousLocalMartingale_timeZeroConst
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsFiniteMeasure μ] {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    IsContinuousLocalMartingale ℱ μ (fun _ ω ↦ M 0 ω) := by
  have hM0_meas : StronglyMeasurable[ℱ 0] (fun ω ↦ M 0 ω) :=
    Measurable.stronglyMeasurable (hM.adapted 0)
  have hM0_int : Integrable (fun ω ↦ M 0 ω) μ :=
    integrable_timeZero_of_isContinuousLocalMartingale hM
  refine
    { local_martingale := ?_
      continuous := ?_ }
  · -- Proof comment: a time-constant process is a martingale with terminal value `M 0`.
    refine (isLocalMartingale_iff ℱ μ (fun _ : NNReal ↦ fun ω ↦ M 0 ω)).2 ?_
    refine ⟨(martingale_const_fun ℱ μ hM0_meas hM0_int).stronglyAdapted.adapted, ?_⟩
    refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
    refine
      (isLocalizingSequence_iff ℱ μ (fun _ : NNReal ↦ fun ω ↦ M 0 ω)
        (fun n _ ↦ (n : ENNReal))).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · intro n
      simpa using (isStoppingTime_const ℱ (n : NNReal))
    · refine Filter.Eventually.of_forall fun _ ↦ ?_
      refine ⟨fun a b hab ↦ by
        simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
      simpa using ENNReal.tendsto_nat_nhds_top
    · intro n
      refine ⟨?_, ?_⟩
      · simpa [stoppedProcess] using (martingale_const_fun ℱ μ hM0_meas hM0_int)
      · simpa [stoppedProcess] using
          (uniformIntegrable_const
            le_rfl (by simp) (memLp_one_iff_integrable.2 hM0_int))
  · -- Proof comment: each sample path is constant in time.
    intro ω
    simpa using (continuous_const : Continuous fun _ : NNReal ↦ M 0 ω)

/-- Helper for Remark 26.24: a continuous local martingale becomes a genuine martingale after
stopping at any deterministic time `T`. -/
theorem martingaleStoppedProcessConst_of_isContinuousLocalMartingale
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) (T : NNReal) :
    Martingale (stoppedProcess M (fun _ ↦ (T : ENNReal))) ℱ μ := by
  -- Proof comment: first package the continuous local martingale as an up-to-`∞` owner, then
  -- apply the deterministic-stop martingale theorem from Chapter 21.
  simpa [min_comm] using
    IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
      (ℱ := ℱ)
      (μ := μ)
      (τ := fun _ ↦ (∞ : ENNReal))
      (M := M)
      (continuousLocalMartingaleUpToInfinity (ℱ := ℱ) (μ := μ) hM)
      T

/-- Helper for Remark 26.24: on a finite-measure space, deterministic-stop martingale owners for
all horizons recover the original continuous local martingale. -/
theorem isContinuousLocalMartingale_of_constStoppedMartingale
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsFiniteMeasure μ] {M : NNReal → Ω → ℝ}
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous (fun t : NNReal ↦ M t ω))
    (hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess M (fun _ ↦ (T : ENNReal))) ℱ μ) :
    IsContinuousLocalMartingale ℱ μ M := by
  refine
    { local_martingale := ?_
      continuous := hM_cont }
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM_adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · -- Proof comment: the deterministic localizers `n ↦ n` increase pointwise to `∞`.
    refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    have hMart :
        Martingale (stoppedProcess M (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ :=
      hStopped n
    have hUI :
        UniformIntegrable
          (stoppedProcess M (fun _ ↦ ((n : NNReal) : ENNReal)))
          1
          μ := by
      -- Proof comment: stopping the already-stopped martingale again at the same deterministic
      -- horizon changes nothing, so the standard martingale-to-UI bridge applies directly.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
        martingale_uniformIntegrable_stoppedProcess_constTime
          (μ := μ)
          (ℱ := ℱ)
          hMart
          (n := (n : NNReal))
    exact ⟨hMart, hUI⟩

/-- Helper for Remark 26.24: timewise almost-sure equality is preserved by deterministic-time
stopping. -/
theorem stoppedProcess_const_areModifications
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {M N : NNReal → Ω → ℝ}
    (hEq : AreModifications μ M N) (T : NNReal) :
    AreModifications μ
      (stoppedProcess M (fun _ ↦ (T : ENNReal)))
      (stoppedProcess N (fun _ ↦ (T : ENNReal))) := by
  intro t
  -- Proof comment: deterministic stopping at horizon `T` only evaluates the original processes
  -- at the clipped time `min t T`.
  simpa [stoppedProcessConstTime_eq_min] using hEq (min t T)

/-- Helper for Remark 26.24: a martingale property transports across timewise almost-sure
equality once the target process is adapted. -/
theorem martingale_of_areModifications
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {M N : NNReal → Ω → ℝ}
    (hM_adapted : Adapted ℱ M)
    (hEq : AreModifications μ M N)
    (hN : Martingale N ℱ μ) :
    Martingale M ℱ μ := by
  refine ⟨hM_adapted.stronglyAdapted, ?_⟩
  intro s t hst
  -- Proof comment: conditional expectations respect almost-sure equality, so the source
  -- martingale identity for `N` transfers directly to `M`.
  calc
    μ[M t | ℱ s] =ᵐ[μ] μ[N t | ℱ s] := by
      exact condExp_congr_ae (hEq t)
    _ =ᵐ[μ] N s := hN.condExp_ae_eq hst
    _ =ᵐ[μ] M s := (hEq s).symm

/-- Helper for Remark 26.24: a continuous local martingale owner transports across timewise
almost-sure equality when the target process keeps the expected adaptedness and continuity. -/
theorem isContinuousLocalMartingale_of_areModifications
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {M N : NNReal → Ω → ℝ}
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous (fun t : NNReal ↦ M t ω))
    (hEq : AreModifications μ M N)
    (hN : IsContinuousLocalMartingale ℱ μ N) :
    IsContinuousLocalMartingale ℱ μ M := by
  refine
    isContinuousLocalMartingale_of_constStoppedMartingale
      (μ := μ)
      hM_adapted
      hM_cont
      ?_
  intro T
  have hStoppedAdapted :
      Adapted ℱ (stoppedProcess M (fun _ ↦ (T : ENNReal))) := by
    intro t
    -- Proof comment: deterministic stopping only clips the evaluation time from `t` to `min t T`.
    simpa [stoppedProcessConstTime_eq_min] using
      (hM_adapted (min t T)).mono (ℱ.mono (min_le_left _ _)) le_rfl
  have hStoppedMartingale :
      Martingale (stoppedProcess N (fun _ ↦ (T : ENNReal))) ℱ μ :=
    martingaleStoppedProcessConst_of_isContinuousLocalMartingale (μ := μ) hN T
  -- Proof comment: the deterministic-stop martingale property of `N` now transports to the
  -- matching stopped version of `M`.
  exact
    martingale_of_areModifications
      hStoppedAdapted
      (stoppedProcess_const_areModifications hEq T)
      hStoppedMartingale

/-- Helper for Remark 26.24: quadratic-covariation owners transport across timewise almost-sure
equality of the two martingale coordinates. -/
theorem hasContinuousQuadraticCovariation_of_areModifications
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M N M' N' A : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hM' : IsContinuousLocalMartingale ℱ μ M')
    (hN' : IsContinuousLocalMartingale ℱ μ N')
    (hEqM : AreModifications μ M M')
    (hEqN : AreModifications μ N N')
    (hCov : HasContinuousQuadraticCovariation ℱ μ M' N' A) :
    HasContinuousQuadraticCovariation ℱ μ M N A := by
  have hMulSubEq :
      AreModifications μ
        (fun t ω ↦ M t ω * N t ω - A t ω)
        (fun t ω ↦ M' t ω * N' t ω - A t ω) := by
    intro t
    -- Proof comment: pointwise multiplication and subtraction preserve the timewise
    -- almost-sure equality of the two coordinate processes.
    filter_upwards [hEqM t, hEqN t] with ω hωM hωN
    simp [hωM, hωN]
  have hMulSub' :
      IsContinuousLocalMartingale ℱ μ
        (fun t ω ↦ M' t ω * N' t ω - A t ω) := by
    refine
      { local_martingale := hCov.local_martingale_mul_sub
        continuous := ?_ }
    intro ω
    exact ((hM'.continuous ω).mul (hN'.continuous ω)).sub (hCov.continuous ω)
  have hMulSub :
      IsContinuousLocalMartingale ℱ μ
        (fun t ω ↦ M t ω * N t ω - A t ω) := by
    refine
      isContinuousLocalMartingale_of_areModifications
        (μ := μ)
        (hM_adapted := hM.adapted.mul hN.adapted |>.sub hCov.adapted)
        (hM_cont := ?_)
        hMulSubEq
        hMulSub'
    intro ω
    exact ((hM.continuous ω).mul (hN.continuous ω)).sub (hCov.continuous ω)
  refine
    { zero := hCov.zero
      adapted := hCov.adapted
      continuous := hCov.continuous
      locally_finite_variation := hCov.locally_finite_variation
      local_martingale_mul_sub := hMulSub.local_martingale }

/-- Helper for Remark 26.24: locally bounded variation on `Set.univ` is stable under addition of
continuous paths. -/
theorem locallyBoundedVariationOn_univ_add
    {G H : C(NNReal, ℝ)}
    (hG : LocallyBoundedVariationOn G Set.univ)
    (hH : LocallyBoundedVariationOn H Set.univ) :
    LocallyBoundedVariationOn (G + H) Set.univ := by
  have hGmem : G ∈ continuousVariationSubmodule := by
    exact (mem_continuousVariationSubmodule_iff G).2 hG
  have hHmem : H ∈ continuousVariationSubmodule := by
    exact (mem_continuousVariationSubmodule_iff H).2 hH
  have hSumMem : G + H ∈ continuousVariationSubmodule := by
    exact Submodule.add_mem continuousVariationSubmodule hGmem hHmem
  -- Proof comment: `continuousVariationSubmodule` is closed under addition, so membership of the
  -- two summands immediately yields locally bounded variation for their sum.
  exact (mem_continuousVariationSubmodule_iff (G + H)).1 hSumMem

/-- Helper for Remark 26.24: the zero process is a quadratic-covariation witness on the right of
any continuous local martingale. -/
theorem hasContinuousQuadraticCovariation_zero_right
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    HasContinuousQuadraticCovariation ℱ μ M (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ)) := by
  refine
    { zero := by
        funext ω
        simp
      adapted := by
        intro t
        simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
      continuous := by
        intro ω
        simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      locally_finite_variation := zeroProcess_locallyFiniteVariation (μ := μ)
      local_martingale_mul_sub := ?_ }
  -- Proof comment: `M * 0 - 0` is the zero process, so it is the zero scalar multiple of the
  -- local martingale part of `M`.
  simpa using hM.local_martingale.const_mul (0 : ℝ)

/-- Helper for Remark 26.24: continuous quadratic covariation is symmetric in the two martingale
coordinates because the product term is commutative. -/
theorem hasContinuousQuadraticCovariation_symm
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M N A : NNReal → Ω → ℝ}
    (hCov : HasContinuousQuadraticCovariation ℱ μ M N A) :
    HasContinuousQuadraticCovariation ℱ μ N M A := by
  refine
    { zero := hCov.zero
      adapted := hCov.adapted
      continuous := hCov.continuous
      locally_finite_variation := hCov.locally_finite_variation
      local_martingale_mul_sub := ?_ }
  -- Proof comment: swapping the two coordinates does not change the product `MN`.
  simpa [mul_comm] using hCov.local_martingale_mul_sub

/-- Helper for Remark 26.24: if `A` and `B` are quadratic-covariation witnesses for `(M, N)` and
`(M, P)`, then `A + B` is a witness for `(M, N + P)`. -/
theorem hasContinuousQuadraticCovariation_add_right
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M N P A B : NNReal → Ω → ℝ}
    (hMN : HasContinuousQuadraticCovariation ℱ μ M N A)
    (hMP : HasContinuousQuadraticCovariation ℱ μ M P B) :
    HasContinuousQuadraticCovariation
      ℱ
      μ
      M
      (fun t ω ↦ N t ω + P t ω)
      (fun t ω ↦ A t ω + B t ω) := by
  refine
    { zero := by
        funext ω
        simp [hMN.zero, hMP.zero]
      adapted := by
        intro t
        exact (hMN.adapted t).add (hMP.adapted t)
      continuous := by
        intro ω
        exact (hMN.continuous ω).add (hMP.continuous ω)
      locally_finite_variation := ?_
      local_martingale_mul_sub := ?_ }
  · filter_upwards [hMN.locally_finite_variation, hMP.locally_finite_variation] with ω hωA hωB
    let GA : C(NNReal, ℝ) := ⟨fun t ↦ A t ω, hMN.continuous ω⟩
    let GB : C(NNReal, ℝ) := ⟨fun t ↦ B t ω, hMP.continuous ω⟩
    -- Proof comment: the new compensator is the sum of the two old compensators, so local
    -- bounded variation follows from closure of `continuousVariationSubmodule` under addition.
    simpa [GA, GB] using locallyBoundedVariationOn_univ_add hωA hωB
  · -- Proof comment: expand `M (N + P) - (A + B)` and add the two known local martingale
    -- witnesses termwise.
    simpa [mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hMN.local_martingale_mul_sub.add hMP.local_martingale_mul_sub

/-- Helper for Remark 26.24: finite sums on the right preserve continuous quadratic covariation
with a fixed continuous local martingale left coordinate. -/
theorem hasContinuousQuadraticCovariation_finsetSum_right
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*}
    (s : Finset ι)
    {M : NNReal → Ω → ℝ}
    {N A : ι → NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hCov :
      ∀ i ∈ s, HasContinuousQuadraticCovariation ℱ μ M (N i) (A i)) :
    HasContinuousQuadraticCovariation
      ℱ
      μ
      M
      (fun t ω ↦ ∑ i in s, N i t ω)
      (fun t ω ↦ ∑ i in s, A i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sum is the zero process, so the base case is the zero-right
      -- quadratic-covariation witness.
      simpa using hasContinuousQuadraticCovariation_zero_right (μ := μ) (ℱ := ℱ) hM
  | @insert a s ha hs =>
      have hHead :
          HasContinuousQuadraticCovariation ℱ μ M (N a) (A a) := by
        exact hCov a (by simp [ha])
      have hTail :
          HasContinuousQuadraticCovariation
            ℱ
            μ
            M
            (fun t ω ↦ ∑ i in s, N i t ω)
            (fun t ω ↦ ∑ i in s, A i t ω) := by
        refine hs ?_
        intro i hi
        exact hCov i (by simp [hi, ha])
      -- Proof comment: isolate the inserted summand and apply the right-addition lemma to the
      -- head witness and the inductive tail witness.
      simpa [Finset.sum_insert, ha] using
        hasContinuousQuadraticCovariation_add_right (μ := μ) (ℱ := ℱ) hHead hTail

/-- Helper for Remark 26.24: finite sums on the left preserve continuous quadratic covariation
with a fixed continuous local martingale right coordinate. -/
theorem hasContinuousQuadraticCovariation_finsetSum_left
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*}
    (s : Finset ι)
    {N : NNReal → Ω → ℝ}
    {M A : ι → NNReal → Ω → ℝ}
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hCov :
      ∀ i ∈ s, HasContinuousQuadraticCovariation ℱ μ (M i) N (A i)) :
    HasContinuousQuadraticCovariation
      ℱ
      μ
      (fun t ω ↦ ∑ i in s, M i t ω)
      N
      (fun t ω ↦ ∑ i in s, A i t ω) := by
  have hRight :
      HasContinuousQuadraticCovariation
        ℱ
        μ
        N
        (fun t ω ↦ ∑ i in s, M i t ω)
        (fun t ω ↦ ∑ i in s, A i t ω) := by
    refine
      hasContinuousQuadraticCovariation_finsetSum_right
        (μ := μ)
        (ℱ := ℱ)
        (s := s)
        hN
        ?_
    intro i hi
    exact hasContinuousQuadraticCovariation_symm (hCov i hi)
  -- Proof comment: apply the right-sided finite-sum theorem after swapping the two coordinates,
  -- then swap back by symmetry.
  exact hasContinuousQuadraticCovariation_symm hRight

/-- Helper for Remark 26.24: on a finite-measure space, deterministic times localize any
martingale. -/
private theorem finiteMeasure_martingale_isLocalMartingale
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsFiniteMeasure μ] {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  -- Proof comment: deterministic times `τₙ ≡ n` are stopping times increasing to `∞`, so they
  -- form a localizing sequence for any martingale on a finite-measure space.
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M (fun n _ ↦ (n : ENNReal))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa using martingale_uniformIntegrable_stoppedProcess_constTime (μ := μ) (ℱ := ℱ) hM
      (n := (n : NNReal))

/-- Helper for Remark 26.24: finite sums of continuous local martingales are again continuous
local martingales. -/
theorem finsetSum_isContinuousLocalMartingale
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (s : Finset ι) (M : ι → NNReal → Ω → ℝ)
    (hM : ∀ i ∈ s, IsContinuousLocalMartingale ℱ μ (M i)) :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ ∑ i in s, M i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sum is the zero process, which is already a continuous local
      -- martingale.
      refine
        ⟨finiteMeasure_martingale_isLocalMartingale
          (μ := μ)
          (ℱ := ℱ)
          (martingale_const_fun
            ℱ
            μ
            stronglyMeasurable_const
            (by simpa using integrable_const (0 : ℝ))), ?_⟩
      intro ω
      simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  | @insert a s ha hs =>
      have haM : IsContinuousLocalMartingale ℱ μ (M a) := by
        exact hM a (by simp [ha])
      have hsM :
          IsContinuousLocalMartingale ℱ μ (fun t ω ↦ ∑ i in s, M i t ω) := by
        refine hs ?_
        intro i hi
        exact hM i (by simp [hi, ha])
      -- Proof comment: after isolating one summand, use closure of continuous local martingales
      -- under addition and rewrite the inserted finite sum back to the target spelling.
      refine
        ⟨haM.local_martingale.add hsM.local_martingale, ?_⟩
      intro ω
      simpa [Finset.sum_insert, ha] using (haM.continuous ω).add (hsM.continuous ω)

/-- Helper for Remark 26.24: each Brownian coordinate already carries the continuous local
martingale and identity-bracket package needed by the finite-horizon Itô pair theorem. -/
theorem brownianCoordinateIdentityBracketData
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : NNReal → Ω → Fin m → ℝ}
    (hW : IsBrownianMotionWithFiltration ℱ μ W)
    (k : Fin m) :
    ∃ hMk : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ W t ω k),
      HasAbsolutelyContinuousSquareVariation (fun t ω ↦ W t ω k) hMk ∧
        IsContinuousSquareVariationProcess ℱ μ
          (fun t ω ↦ W t ω k)
          (fun t _ ↦ (t : ℝ)) := by
  -- Proof comment: use the already-packaged constant-one Brownian Itô integral on coordinate
  -- `k`, then rewrite its square-variation compensator to the identity path `t ↦ t`.
  have hCoordIto :
      IsBrownianLocalItoIntegral ℱ μ
        (fun t ω ↦ W t ω k)
        (fun _ _ ↦ (1 : ℝ))
        (fun t ω ↦ W t ω k) := by
    simpa [CoordinateProcess.toEuclidean] using
      (brownianCoordinate_constOne_isBrownianLocalItoIntegral
        (ℱ := ℱ)
        (μ := μ)
        (W := W.toEuclidean)
        hW.1
        k)
  have hCoordData :
      IsContinuousLocalMartingale ℱ μ (fun t ω ↦ W t ω k) ∧
        IsContinuousSquareVariationProcess ℱ μ
          (fun t ω ↦ W t ω k)
          (MeasureTheory.secondMomentCompensator (fun _ _ ↦ (1 : ℝ))) :=
    brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
      (ℱ := ℱ)
      (μ := μ)
      hCoordIto
  have hCoordBracket :
      HasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ W t ω k)
        hCoordData.1 := by
    refine ⟨fun _ _ ↦ (1 : NNReal), ?_, ?_, ?_⟩
    · -- Proof comment: the deterministic unit density is progressively measurable.
      simpa using
        (stronglyMeasurable_const.progMeasurable :
          ProgMeasurable ℱ (fun _ _ : Ω ↦ (1 : ℝ)))
    · -- Proof comment: the square-variation compensator of the constant-one integral is the
      -- standard second-moment compensator.
      simpa [MeasureTheory.secondMomentCompensator] using hCoordData.2
    · -- Proof comment: integrating the density `1` over `[0,t]` gives the deterministic path
      -- `t`.
      intro t ω
      simp [MeasureTheory.secondMomentCompensator]
  have hCoordSquareVariation :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦ W t ω k)
        (fun t _ ↦ (t : ℝ)) := by
    -- Proof comment: rewrite the compensator of the constant-one integral to the identity path.
    simpa [MeasureTheory.secondMomentCompensator] using hCoordData.2
  exact ⟨hCoordData.1, hCoordBracket, hCoordSquareVariation⟩

/-- Helper for Remark 26.24: distinct Brownian coordinates are independent as path-valued
processes. -/
theorem brownianCoordinateProcessIndepFun
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : NNReal → Ω → Fin m → ℝ}
    (hW : IsBrownianMotionWithFiltration ℱ μ W)
    {k l : Fin m} (hkl : k ≠ l) :
    IndepFun
      (fun ω ↦ fun t : NNReal ↦ W t ω k)
      (fun ω ↦ fun t : NNReal ↦ W t ω l)
      μ := by
  -- Proof comment: the standard vector Brownian owner already stores independence of the full
  -- coordinate process family.
  simpa [CoordinateProcess.toEuclidean] using
    hW.1.iIndepFun.indepFun (i := k) (j := l) hkl

/-- Helper for Remark 26.24: continuous `NNReal`-indexed real processes that agree almost surely
at each deterministic time are indistinguishable. -/
theorem areIndistinguishable_of_ae_eq_all_times_of_continuous
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {X Y : NNReal → Ω → ℝ}
    (hXY : ∀ t : NNReal, X t =ᵐ[μ] Y t)
    (hXcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    (hYcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω) :
    AreIndistinguishable μ X Y := by
  let X' : Set.Ici (0 : ℝ) → Ω → ℝ := fun s ω ↦ X s.1.toNNReal ω
  let Y' : Set.Ici (0 : ℝ) → Ω → ℝ := fun s ω ↦ Y s.1.toNNReal ω
  have hXY' : AreModifications μ X' Y' := by
    intro s
    simpa [X', Y', Real.toNNReal_of_nonneg s.2] using hXY s.1.toNNReal
  have hXrc :
      ∀ᵐ ω ∂μ, ∀ t : Set.Ici (0 : ℝ),
        ContinuousWithinAt (processPath X' ω) (Set.Ici t) t := by
    filter_upwards with ω t
    have htoNN :
        Continuous fun s : Set.Ici (0 : ℝ) ↦ (⟨s.1, s.2⟩ : NNReal) := by
      exact continuous_subtype_val.subtype_mk fun s ↦ s.2
    have hcont' : Continuous fun s : Set.Ici (0 : ℝ) ↦ X' s ω := by
      simpa [X'] using (hXcont ω).comp htoNN
    -- Proof comment: continuity on the half-line upgrades to the right-continuity input needed
    -- by the indistinguishability theorem.
    exact hcont'.continuousAt.continuousWithinAt
  have hYrc :
      ∀ᵐ ω ∂μ, ∀ t : Set.Ici (0 : ℝ),
        ContinuousWithinAt (processPath Y' ω) (Set.Ici t) t := by
    filter_upwards with ω t
    have htoNN :
        Continuous fun s : Set.Ici (0 : ℝ) ↦ (⟨s.1, s.2⟩ : NNReal) := by
      exact continuous_subtype_val.subtype_mk fun s ↦ s.2
    have hcont' : Continuous fun s : Set.Ici (0 : ℝ) ↦ Y' s ω := by
      simpa [Y'] using (hYcont ω).comp htoNN
    -- Proof comment: apply the same half-line continuity reduction to `Y`.
    exact hcont'.continuousAt.continuousWithinAt
  rcases
      ProbabilityTheory.indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
        (μ := μ)
        (X := X')
        (Y := Y')
        hXY'
        Set.ordConnected_Ici
        hXrc
        hYrc with
    ⟨N, hNmeas, hNzero, hNsub⟩
  refine ⟨N, hNmeas, hNzero, ?_⟩
  intro t ω hω
  by_contra hneq
  exact
    hω <|
      hNsub
        ⟨(t : ℝ), by exact_mod_cast t.2⟩
        (by simpa [X', Y'] using hneq)

/-- Helper for Remark 26.24: if a continuous quadratic-covariation witness is almost surely zero
at every deterministic time, then the zero process is itself a quadratic-covariation witness. -/
theorem hasContinuousQuadraticCovariation_zero_of_ae_eq_zero_all_times
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M N A : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hCov : HasContinuousQuadraticCovariation ℱ μ M N A)
    (hAzero : ∀ t : NNReal, A t =ᵐ[μ] fun _ ↦ (0 : ℝ)) :
    HasContinuousQuadraticCovariation ℱ μ M N (fun _ _ ↦ (0 : ℝ)) := by
  have hAeqZero :
      AreIndistinguishable μ A (fun _ _ ↦ (0 : ℝ)) :=
    areIndistinguishable_of_ae_eq_all_times_of_continuous
      (μ := μ)
      hAzero
      hCov.continuous
      (fun _ ↦ continuous_const)
  have hAzeroAll :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = 0 := by
    rcases hAeqZero with ⟨N0, hN0meas, hN0zero, hN0sub⟩
    refine (compl_mem_ae_iff.mpr hN0zero).mono ?_
    intro ω hω t
    by_contra hneq
    exact hω (hN0sub t hneq)
  have hProdAdapted :
      Adapted ℱ (fun t ω ↦ M t ω * N t ω) := by
    exact hM.adapted.mul hN.adapted
  have hProdCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω * N t ω := by
    intro ω
    exact (hM.continuous ω).mul (hN.continuous ω)
  refine
    { zero := by
        funext ω
        simp
      adapted := by
        intro t
        simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
      continuous := by
        intro ω
        simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      locally_finite_variation := zeroProcess_locallyFiniteVariation (μ := μ)
      local_martingale_mul_sub := ?_ }
  -- Proof comment: once `A` vanishes outside one null set for all times, the product process
  -- `MN` is exactly the existing local martingale `MN - A`.
  exact
    isLocalMartingale_congr_ae_allTimes
      hCov.local_martingale_mul_sub
      hProdAdapted
      hProdCont
      (by
        filter_upwards [hAzeroAll] with ω hω t
        simp [hω t])

/-- Helper for Remark 26.24: a continuous quadratic-covariation witness can be replaced by any
timewise almost-surely equal compensator once the replacement process already carries the required
adaptedness, continuity, and finite-variation fields. -/
theorem hasContinuousQuadraticCovariation_of_horizonwiseCompensatorEq
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M N A B : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hCovA : HasContinuousQuadraticCovariation ℱ μ M N A)
    (hBzero : B 0 = 0)
    (hBadapted : Adapted ℱ B)
    (hBcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ B t ω)
    (hBLFV :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ B t ω, hBcont ω⟩ : C(NNReal, ℝ))
          Set.univ)
    (hAB : ∀ t : NNReal, A t =ᵐ[μ] B t) :
    HasContinuousQuadraticCovariation ℱ μ M N B := by
  have hAeqB :
      AreIndistinguishable μ A B :=
    areIndistinguishable_of_ae_eq_all_times_of_continuous
      (μ := μ)
      hAB
      hCovA.continuous
      hBcont
  have hABall :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω := by
    rcases hAeqB with ⟨N0, hN0meas, hN0zero, hN0sub⟩
    refine (compl_mem_ae_iff.mpr hN0zero).mono ?_
    intro ω hω t
    by_contra hneq
    exact hω (hN0sub t hneq)
  have hProdAdapted :
      Adapted ℱ (fun t ω ↦ M t ω * N t ω) := by
    exact hM.adapted.mul hN.adapted
  have hProdCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω * N t ω := by
    intro ω
    exact (hM.continuous ω).mul (hN.continuous ω)
  refine
    { zero := hBzero
      adapted := hBadapted
      continuous := hBcont
      locally_finite_variation := hBLFV
      local_martingale_mul_sub := ?_ }
  -- Proof comment: the product process is unchanged, so once `A` and `B` agree outside one null
  -- set for all deterministic times, the same local-martingale owner transports to `MN - B`.
  exact
    isLocalMartingale_congr_ae_allTimes
      hCovA.local_martingale_mul_sub
      hProdAdapted
      hProdCont
      (by
        filter_upwards [hABall] with ω hω t
        simp [hω t])

/-- Helper for Remark 26.24: the source-centered martingale part of a generalized weak SDE
solution is the continuous local martingale needed by the centered `26.21` realization theorem. -/
theorem matrixItoRow_isContinuousLocalMartingale
    {b : DriftCoeff} {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    (L : GeneralizedWeakSDESolution μ₀ σ b)
    {N : NNReal → L.Ω → State}
    (hIto :
      IsMatrixBrownianLocalItoIntegral
        L.ℱ
        L.μ
        L.W
        (fun t ω i j ↦ σ t (L ω t) i j)
        N)
    (i : Fin n) :
    IsContinuousLocalMartingale L.ℱ L.μ
      (fun t ω ↦ ∑ j : Fin m, hIto.Nij i j t ω) := by
  -- Proof comment: each scalar coordinate integral is already a Brownian local Itô integral, and
  -- finite sums preserve the continuous local martingale owner.
  refine
    finsetSum_isContinuousLocalMartingale
      (ℱ := L.ℱ)
      (μ := L.μ)
      (s := Finset.univ)
      (M := fun j ↦ hIto.Nij i j)
      ?_
  intro j _hj
  exact
    (brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
      (ℱ := L.ℱ)
      (μ := L.μ)
      (hIto.Nij i j)).1

/-- Helper for Remark 26.24: once the diffusion decomposition of `L` is fixed, the source-centered
martingale coordinate is exactly the corresponding row sum of the scalar Itô witnesses. -/
theorem GeneralizedWeakSDESolution.sourceMartingalePart_eq_matrixItoRow
    {b : DriftCoeff} {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    (L : GeneralizedWeakSDESolution μ₀ σ b)
    {N : NNReal → L.Ω → State}
    (hIto :
      IsMatrixBrownianLocalItoIntegral
        L.ℱ
        L.μ
        L.W
        (fun t ω i j ↦ σ t (L ω t) i j)
        N)
    (hStateEq :
      ∀ t ω,
        L ω t =
          L.ξ ω + N t ω +
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal))
    (i : Fin n) :
    sourceLocalMartingaleProblemMartingalePart b L i =
      fun t ω ↦ ∑ j : Fin m, hIto.Nij i j t ω := by
  -- Proof comment: rewrite the diffusion equation coordinatewise, then cancel the shared initial
  -- datum and drift integral against the centered source-martingale definition.
  funext t ω
  have hInitialState : L ω 0 = L.ξ ω := L.initialState_eq ω
  have hInitialCoordinate : L ω 0 i = L.ξ ω i := by
    simpa using congrArg (fun x : State ↦ x i) hInitialState
  have hStateCoordinate := congrFun (congrFun (congrFun hStateEq t) ω) i
  calc
    sourceLocalMartingaleProblemMartingalePart b L i t ω =
        L ω t i - L ω 0 i -
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal) i := by
            rfl
    _ =
        (L.ξ ω i +
            N t ω i +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal) i) -
          L ω 0 i -
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal) i := by
              rw [hStateCoordinate]
    _ = N t ω i := by
          rw [hInitialCoordinate]
          ring
    _ = ∑ j : Fin m, hIto.Nij i j t ω := by
          rw [hIto.sum_eq]

/-- Helper for Remark 26.24: the source-centered martingale part of a generalized weak SDE
solution is the continuous local martingale needed by the centered `26.21` realization theorem. -/
theorem GeneralizedWeakSDESolution.sourceMartingalePart_isContinuousLocalMartingale
    {b : DriftCoeff} {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    (L : GeneralizedWeakSDESolution μ₀ σ b) (i : Fin n) :
    IsContinuousLocalMartingale L.ℱ L.μ
      (sourceLocalMartingaleProblemMartingalePart b L i) := by
  -- Route correction: the forward `26.21` bridge no longer needs another remark-local wrapper.
  -- The real missing owner is this source-centered stochastic clause extracted from
  -- `L.solvesGeneralizedDiffusion`.
  rcases L.exists_diffusionTerm_for_sourceMartingalePart (σ := σ) (b := b) i with
    ⟨N, hIto, hSource⟩
  have hRow :
      IsContinuousLocalMartingale L.ℱ L.μ
        (fun t ω ↦ ∑ j : Fin m, hIto.Nij i j t ω) :=
    matrixItoRow_isContinuousLocalMartingale (σ := σ) (b := b) L hIto i
  have hSourceEq :
      sourceLocalMartingaleProblemMartingalePart b L i =
        fun t ω ↦ ∑ j : Fin m, hIto.Nij i j t ω := by
    -- Proof comment: the extracted diffusion decomposition identifies the centered source
    -- martingale coordinate with the corresponding Itô row sum.
    simpa [hSource] using
      L.sourceMartingalePart_eq_matrixItoRow (σ := σ) (b := b) hIto hSource i
  simpa [hSourceEq] using hRow

/-- Helper for Remark 26.24: for one fixed diffusion-term witness `N`, the row sums of the scalar
Itô coordinates carry the expected `σσᵀ` quadratic covariation. -/
theorem matrixItoRowPair_hasQuadraticCovariation
    {b : DriftCoeff} {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    (L : GeneralizedWeakSDESolution μ₀ σ b)
    {N : NNReal → L.Ω → State}
    (hIto :
      IsMatrixBrownianLocalItoIntegral
        L.ℱ
        L.μ
        L.W
        (fun t ω i j ↦ σ t (L ω t) i j)
        N)
    (i j : Fin n) :
    HasContinuousQuadraticCovariation L.ℱ L.μ
      (fun t ω ↦ ∑ k : Fin m, hIto.Nij i k t ω)
      (fun t ω ↦ ∑ k : Fin m, hIto.Nij j k t ω)
      (fun t ω ↦
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          ∑ k : Fin m, σ s.toNNReal (L ω s.toNNReal) i k * σ s.toNNReal (L ω s.toNNReal) j k) := by
  -- TODO: the local route is now fixed. For each pair `(k,l)`, choose a global quadratic-
  -- covariation owner, derive the horizonwise compensator equality from `pair_spec` when `k = l`
  -- and from Brownian-coordinate independence when `k ≠ l`, transport the owner with
  -- `hasContinuousQuadraticCovariation_of_horizonwiseCompensatorEq` or the zero-compensator
  -- helper, then sum by `hasContinuousQuadraticCovariation_finsetSum_right/left`.
  -- Current blocker: the active import `Books.ProbabilityTheory_Klenke_2020/Items/Chap25/Theorem_25_22.lean` does
  -- not elaborate in the current environment, so the `pair_spec` / owner-transport bridge cannot
  -- be validated from this file yet.
  sorry

/-- Helper for Remark 26.24: unfolding the local-martingale-problem covariation for `σσᵀ`
produces the scalar row-sum compensator used in the row-pair argument. -/
theorem localMartingaleProblemCovariation_diffusionMatrixOfCoefficient
    {Ω : Type u} [MeasurableSpace Ω] (X : Ω → PathSpace) (i j : Fin n) :
    localMartingaleProblemCovariation σσᵀ X i j =
      fun t ω ↦
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          ∑ k : Fin m, σ s.toNNReal (X ω s.toNNReal) i k * σ s.toNNReal (X ω s.toNNReal) j k := by
  -- Proof comment: expand the prescribed covariation process and unfold `σσᵀ` once so the
  -- target is expressed in the row-sum normal form expected by the matrix Itô witness.
  funext t ω
  simp [localMartingaleProblemCovariation, diffusionMatrixOfCoefficient_apply]

/-- Helper for Remark 26.24: every prescribed local-martingale-problem covariation process starts
from `0` because its defining integral is taken over the degenerate interval `[0,0]`. -/
theorem localMartingaleProblemCovariation_zero
    {a : NNReal → State → Fin n → Fin n → ℝ}
    {Ω : Type u} [MeasurableSpace Ω] (X : Ω → PathSpace) (i j : Fin n) :
    localMartingaleProblemCovariation a X i j 0 = 0 := by
  -- Proof comment: unfold the compensator at time `0` and evaluate the interval integral over a
  -- singleton interval.
  simp [localMartingaleProblemCovariation]

/-- Helper for Remark 26.24: the source-centered martingale parts of a generalized weak SDE
solution have the prescribed quadratic covariation from `σσᵀ`. -/
theorem GeneralizedWeakSDESolution.sourceMartingalePart_hasQuadraticCovariation
    {b : DriftCoeff} {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    (L : GeneralizedWeakSDESolution μ₀ σ b) (i j : Fin n) :
    HasContinuousQuadraticCovariation L.ℱ L.μ
      (sourceLocalMartingaleProblemMartingalePart b L i)
      (sourceLocalMartingaleProblemMartingalePart b L j)
      (localMartingaleProblemCovariation σσᵀ L i j) := by
  -- Route correction: the forward law-preserving bridge should consume one canonical quadratic-
  -- covariation clause, not reopen the diffusion decomposition inside the remark theorem.
  rcases L.solvesGeneralizedDiffusion with
    ⟨_hBrownian, N, hIto, _hDriftMeas, _hDriftInt, hStateEq⟩
  let hItoMatrix := hIto
  rcases hIto with ⟨Nij, hNij, hNsum⟩
  have hSourceRow :
      ∀ ℓ : Fin n,
        sourceLocalMartingaleProblemMartingalePart b L ℓ =
          fun t ω ↦ ∑ k : Fin m, Nij ℓ k t ω := by
    intro ℓ
    -- Proof comment: the diffusion equation identifies each centered coordinate increment with
    -- the corresponding row sum of scalar Brownian Itô coordinates.
    funext t ω
    have hInitialState : L ω 0 = L.ξ ω := L.initialState_eq ω
    have hInitialCoordinate : L ω 0 ℓ = L.ξ ω ℓ := by
      simpa using congrArg (fun x : State ↦ x ℓ) hInitialState
    have hStateCoordinate := congrFun (congrFun (congrFun hStateEq t) ω) ℓ
    calc
      sourceLocalMartingaleProblemMartingalePart b L ℓ t ω =
          L ω t ℓ - L ω 0 ℓ -
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (L ω s.toNNReal) ℓ := by
              rfl
      _ = N t ω ℓ := by
            rw [hStateCoordinate]
            ring_nf
            rw [hInitialCoordinate]
      _ = ∑ k : Fin m, Nij ℓ k t ω := by
            rw [hNsum]
  have hCovariationExpand :
      localMartingaleProblemCovariation σσᵀ L i j =
        fun t ω ↦
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            ∑ k : Fin m, σ s.toNNReal (L ω s.toNNReal) i k * σ s.toNNReal (L ω s.toNNReal) j k :=
    localMartingaleProblemCovariation_diffusionMatrixOfCoefficient
      (σ := σ)
      (X := L)
      i
      j
  -- Proof comment: once the row-sum covariation theorem is available for the chosen diffusion
  -- witness `N`, the source-centered martingale clauses follow by rewriting both coordinates and
  -- the compensator to that fixed row-sum normal form.
  simpa [hSourceRow i, hSourceRow j, hCovariationExpand] using
    matrixItoRowPair_hasQuadraticCovariation
      (σ := σ)
      (b := b)
      (L := L)
      hItoMatrix
      i
      j

/-- Helper for Remark 26.24: under the usual conditions, a real-valued random variable that is
almost surely equal to a constant is measurable at every deterministic time. -/
theorem measurable_of_aeEq_const_underUsualConditions
    {Ω : Type u} [MeasurableSpace Ω] {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [Filtration.UsualConditions ℱ μ]
    {f : Ω → ℝ} {c : ℝ} (t : NNReal) (hfc : f =ᵐ[μ] fun _ ↦ c) :
    Measurable[ℱ t] f := by
  let E : Set Ω := {ω | f ω ≠ c}
  have hEae : Eᶜ ∈ ae μ := by
    -- Proof comment: rewrite the almost-sure equality as an almost-sure membership statement for
    -- the complement of the exceptional set `E`.
    simpa [E] using hfc
  have hEzero : μ E = 0 := compl_mem_ae_iff.mp hEae
  have hEmeas : MeasurableSet[ℱ t] E :=
    initialAmbientNullMeasurable_mono
      ℱ
      μ
      (usualConditions_timeZeroComplete ℱ μ)
      t
      hEzero
  intro s hs
  by_cases hc : c ∈ s
  · have hNullPart : μ (E ∩ f ⁻¹' s) = 0 := by
      refine measure_mono_null ?_ hEzero
      exact Set.inter_subset_left
    have hPartMeas : MeasurableSet[ℱ t] (E ∩ f ⁻¹' s) :=
      initialAmbientNullMeasurable_mono
        ℱ
        μ
        (usualConditions_timeZeroComplete ℱ μ)
        t
        hNullPart
    have hPreimage :
        f ⁻¹' s = Eᶜ ∪ (E ∩ f ⁻¹' s) := by
      ext ω
      by_cases hω : f ω = c
      · simp [E, hω, hc]
      · simp [E, hω]
    -- Proof comment: outside the null exceptional set the value of `f` is the constant `c`,
    -- while inside that null set every subset is measurable by completeness.
    rw [hPreimage]
    exact hEmeas.compl.union hPartMeas
  · have hSubset : f ⁻¹' s ⊆ E := by
      intro ω hω
      simp [E]
      intro hEq
      exact hc (hEq ▸ hω)
    have hPreimageZero : μ (f ⁻¹' s) = 0 := measure_mono_null hSubset hEzero
    -- Proof comment: if the constant value `c` is not in `s`, then the whole preimage sits
    -- inside the null exceptional set.
    exact
      initialAmbientNullMeasurable_mono
        ℱ
        μ
        (usualConditions_timeZeroComplete ℱ μ)
        t
        hPreimageZero

/-- Helper for Remark 26.24: once a Dirac-start centered realization is built on a witness space,
the remaining `26.21` work is exactly the centered-to-ordinary local-martingale-problem bridge on
that same space. -/
theorem diracCenteredLocalMartingaleProblemSolution_toLocalMartingaleProblemSolution
    {b : DriftCoeff} {x : State}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    (P : ProbabilityMeasure Ω) [Filtration.UsualConditions ℱ (P : Measure Ω)]
    (X : Ω → PathSpace)
    (hX :
      IsCenteredLocalMartingaleProblemSolution
        (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X) :
    IsLocalMartingaleProblemSolution
      (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X := by
  -- Route correction: after the centered realization theorem is imported, the forward bridge has
  -- only one remaining interface gap: recover the ordinary local-martingale owner from the
  -- source-centered owner on the same witness space.
  have hDiracCoordinate :
      ∀ i : Fin n, (fun ω ↦ X ω 0 i) =ᵐ[(P : Measure Ω)] fun _ ↦ x i := by
    intro i
    filter_upwards [aeEq_const_of_diracLaw (ξ := fun ω ↦ X ω 0) hX.initial_law] with ω hω
    exact congrArg (fun y : State ↦ y i) hω
  have hShiftedMartingalePart :
      ∀ i : Fin n,
        IsContinuousLocalMartingale
          ℱ
          (P : Measure Ω)
          (fun t ω ↦ sourceLocalMartingaleProblemMartingalePart b X i t ω + x i) := by
    intro i
    have hConst :
        IsContinuousLocalMartingale
          ℱ
          (P : Measure Ω)
          (fun _ _ ↦ x i) := by
      -- Proof comment: the deterministic Dirac start `x i` is a time-constant continuous local
      -- martingale.
      refine
        ⟨finiteMeasure_martingale_isLocalMartingale
          (μ := (P : Measure Ω))
          (ℱ := ℱ)
          (martingale_const_fun
            ℱ
            (P : Measure Ω)
            stronglyMeasurable_const
            (by simpa using integrable_const (x i))), ?_⟩
      intro ω
      simpa using (continuous_const : Continuous fun _ : NNReal ↦ x i)
    -- Proof comment: shifting the centered martingale part by the deterministic initial value
    -- preserves the continuous local martingale owner.
    refine
      ⟨hX.martingalePart i |>.local_martingale.add hConst.local_martingale, ?_⟩
    intro ω
    simpa using (hX.martingalePart i).continuous ω |>.add continuous_const
  have hOrdinaryEq :
      ∀ i : Fin n,
        AreModifications
          (P : Measure Ω)
          (localMartingaleProblemMartingalePart b X i)
          (fun t ω ↦ sourceLocalMartingaleProblemMartingalePart b X i t ω + x i) := by
    intro i t
    filter_upwards [hDiracCoordinate i] with ω hω
    calc
      localMartingaleProblemMartingalePart b X i t ω
          = (localMartingaleProblemMartingalePart b X i t ω - X ω 0 i) + x i := by
              rw [hω]
              ring
      _ = sourceLocalMartingaleProblemMartingalePart b X i t ω + x i := by
            simp [sourceLocalMartingaleProblemMartingalePart, localMartingaleProblemMartingalePart]
            ring
  have hOrdinaryMartingalePart :
      ∀ i : Fin n,
        IsContinuousLocalMartingale
          ℱ
          (P : Measure Ω)
          (localMartingaleProblemMartingalePart b X i) := by
    intro i
    have hInitialCoordMeas :
        Measurable[ℱ 0] (fun ω ↦ X ω 0 i) :=
      measurable_of_aeEq_const_underUsualConditions
        (ℱ := ℱ)
        (μ := (P : Measure Ω))
        (t := 0)
        (hDiracCoordinate i)
    have hOrdinaryAdapted : Adapted ℱ (localMartingaleProblemMartingalePart b X i) := by
      intro t
      have hInitialCoordMeas_t :
          Measurable[ℱ t] (fun ω ↦ X ω 0 i) :=
        hInitialCoordMeas.mono (ℱ.mono (show (0 : NNReal) ≤ t by simp)) le_rfl
      have hSourceMeas :
          Measurable[ℱ t] (fun ω ↦ sourceLocalMartingaleProblemMartingalePart b X i t ω) :=
        (hX.martingalePart i).adapted t
      have hDecomp :
          (fun ω ↦ localMartingaleProblemMartingalePart b X i t ω) =
            fun ω ↦ sourceLocalMartingaleProblemMartingalePart b X i t ω + X ω 0 i := by
        funext ω
        simp [sourceLocalMartingaleProblemMartingalePart, localMartingaleProblemMartingalePart]
        ring
      -- Proof comment: the ordinary compensated coordinate splits into the centered martingale
      -- part plus the deterministic-time initial slice.
      rw [hDecomp]
      exact hSourceMeas.add hInitialCoordMeas_t
    have hOrdinaryCont :
        ∀ ω : Ω, Continuous (fun t : NNReal ↦ localMartingaleProblemMartingalePart b X i t ω) := by
      intro ω
      have hDecomp :
          (fun t : NNReal ↦ localMartingaleProblemMartingalePart b X i t ω) =
            fun t ↦ sourceLocalMartingaleProblemMartingalePart b X i t ω + X ω 0 i := by
        funext t
        simp [sourceLocalMartingaleProblemMartingalePart, localMartingaleProblemMartingalePart]
        ring
      -- Proof comment: pathwise continuity of the centered martingale part survives after adding
      -- the time-constant initial slice.
      rw [hDecomp]
      exact (hX.martingalePart i).continuous ω |>.add continuous_const
    -- Proof comment: the Dirac initial law identifies the ordinary and shifted centered
    -- compensated coordinates up to modification, so the continuous local martingale owner
    -- transports across that modification.
    exact
      isContinuousLocalMartingale_of_areModifications
        (μ := (P : Measure Ω))
        (hM_adapted := hOrdinaryAdapted)
        (hM_cont := hOrdinaryCont)
        (hOrdinaryEq i)
        (hShiftedMartingalePart i)
  refine
    { initial_law := hX.initial_law
      martingalePart := hOrdinaryMartingalePart
      quadraticCovariation := ?_ }
  · intro i j
    have hShiftedCovariation :
        HasContinuousQuadraticCovariation
          ℱ
          (P : Measure Ω)
          (fun t ω ↦ sourceLocalMartingaleProblemMartingalePart b X i t ω + x i)
          (fun t ω ↦ sourceLocalMartingaleProblemMartingalePart b X j t ω + x j)
          (localMartingaleProblemCovariation σσᵀ X i j) := by
      have hConstProd :
          IsContinuousLocalMartingale
            ℱ
            (P : Measure Ω)
            (fun _ _ ↦ x i * x j) := by
        -- Proof comment: the product of the two deterministic shifts is still a time-constant
        -- continuous local martingale.
        refine
          ⟨finiteMeasure_martingale_isLocalMartingale
            (μ := (P : Measure Ω))
            (ℱ := ℱ)
            (martingale_const_fun
              ℱ
              (P : Measure Ω)
              stronglyMeasurable_const
              (by simpa using integrable_const (x i * x j))), ?_⟩
        intro ω
        simpa using (continuous_const : Continuous fun _ : NNReal ↦ x i * x j)
      have hCrossRight :
          IsLocalMartingale
            ℱ
            (P : Measure Ω)
            (fun t ω ↦ x i * sourceLocalMartingaleProblemMartingalePart b X j t ω) := by
        -- Proof comment: multiplying a local martingale by a deterministic scalar preserves the
        -- local martingale owner.
        simpa [Pi.smul_apply, smul_eq_mul] using
          (hX.martingalePart j).local_martingale.const_mul (x i)
      have hCrossLeft :
          IsLocalMartingale
            ℱ
            (P : Measure Ω)
            (fun t ω ↦ x j * sourceLocalMartingaleProblemMartingalePart b X i t ω) := by
        -- Proof comment: the symmetric cross term is handled by the same scalar-multiplication
        -- closure property.
        simpa [Pi.smul_apply, smul_eq_mul] using
          (hX.martingalePart i).local_martingale.const_mul (x j)
      refine
        { zero := (hX.quadraticCovariation i j).zero
          adapted := (hX.quadraticCovariation i j).adapted
          continuous := (hX.quadraticCovariation i j).continuous
          locally_finite_variation := (hX.quadraticCovariation i j).locally_finite_variation
          local_martingale_mul_sub := ?_ }
      -- Proof comment: shifting both martingale coordinates by deterministic constants adds only
      -- linear martingale cross terms and one constant process, so the same compensator remains
      -- valid.
      simpa [mul_add, add_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm,
        mul_left_comm, mul_assoc] using
        (((hX.quadraticCovariation i j).local_martingale_mul_sub.add hCrossRight).add hCrossLeft)
          .add hConstProd.local_martingale
    -- Proof comment: the quadratic-covariation owner for the shifted centered coordinates now
    -- transports across the same Dirac-start modification used for the martingale clause.
    exact
      hasContinuousQuadraticCovariation_of_areModifications
        (hOrdinaryMartingalePart i)
        (hOrdinaryMartingalePart j)
        (hShiftedMartingalePart i)
        (hShiftedMartingalePart j)
        (hOrdinaryEq i)
        (hOrdinaryEq j)
        hShiftedCovariation

/-- Helper for Remark 26.24: the forward `26.21` bridge should turn a Dirac-start generalized
weak SDE solution into an ordinary local-martingale-problem solution without changing the path
law. -/
theorem existsLocalMartingaleProblemSolution_with_statePathLaw_of_diracGeneralizedWeakSDESolution
    {b : DriftCoeff} {x : State}
    (L : GeneralizedWeakSDESolution (Measure.dirac x) σ b) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
      (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
      IsLocalMartingaleProblemSolution
        (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X ∧
        (P : Measure Ω).map X = L.statePathLaw := by
  let P : ProbabilityMeasure L.Ω := ⟨L.μ⟩
  have hXCentered :
      IsCenteredLocalMartingaleProblemSolution
        (Measure.dirac x) σσᵀ b L.ℱ (P : Measure L.Ω) L := by
    -- Proof comment: the generalized weak solution already lives on a witness space carrying the
    -- centered local-martingale data; only the source-centered stochastic clauses still need the
    -- remark-local bridge lemmas above.
    refine
      { initial_law := L.initialLaw
        martingalePart := ?_
        quadraticCovariation := ?_ }
    · intro i
      exact L.sourceMartingalePart_isContinuousLocalMartingale (σ := σ) (b := b) i
    · intro i j
      exact L.sourceMartingalePart_hasQuadraticCovariation (σ := σ) (b := b) i j
  -- Proof comment: the forward bridge now stays on `L`'s own witness space, so the path-law
  -- equality is definitionally `rfl`.
  refine ⟨L.Ω, inferInstance, L.ℱ, P, L, ?_, rfl⟩
  exact
    diracCenteredLocalMartingaleProblemSolution_toLocalMartingaleProblemSolution
      (σ := σ)
      (b := b)
      (x := x)
      P
      L
      hXCentered

/-- Helper for Remark 26.24: any local-martingale-problem realization can first be normalized to
canonical path space by pushing its law forward along the realized path map. -/
private theorem pushforward_isCanonicalPathSolutionCore_of_sideConditions
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {a : NNReal → State → Fin n → Fin n → ℝ} {b : DriftCoeff}
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X)
    (hPathAdapted : Adapted ℱ (pathProcess X))
    (hMartingalePartAdapted :
      ∀ i : Fin n,
        Adapted canonicalPathFiltration (localMartingaleProblemMartingalePart b id i))
    (hMartingalePartCont :
      ∀ i : Fin n,
        ∀ γ : PathSpace, Continuous (fun t : NNReal ↦ localMartingaleProblemMartingalePart b id i t γ))
    (hCovariationAdapted :
      ∀ i j : Fin n,
        Adapted canonicalPathFiltration (localMartingaleProblemCovariation a id i j))
    (hCovariationCont :
      ∀ i j : Fin n,
        ∀ γ : PathSpace, Continuous (fun t : NNReal ↦ localMartingaleProblemCovariation a id i j t γ))
    (hCovariationLFV :
      ∀ i j : Fin n,
        ∀ᵐ γ ∂(μ.map X),
          LocallyBoundedVariationOn
            (⟨fun t ↦ localMartingaleProblemCovariation a id i j t γ,
              hCovariationCont i j γ⟩ : C(NNReal, ℝ))
            Set.univ) :
    IsLocalMartingaleProblemSolution μ₀ a b canonicalPathFiltration (μ.map X) id := by
  -- Proof comment: once the source path process is adapted and the canonical-path martingale and
  -- covariation fields carry their own target-side side conditions, the repaired pushforward
  -- transport lemmas assemble the canonical owner in one place.
  refine
    { initial_law := ?_
      martingalePart := ?_
      quadraticCovariation := ?_ }
  · -- Proof comment: the time-zero marginal is already transported by the standalone initial-law
    -- pushforward theorem proved above.
    simpa [canonicalPathFiltration] using hX.pushforward_initialLaw_isCanonicalPathInitialLaw
  · intro i
    have hSource :
        IsContinuousLocalMartingale
          ℱ
          μ
          (fun t ω ↦ localMartingaleProblemMartingalePart b id i t (X ω)) := by
      -- Proof comment: normalize the source owner by composing the canonical-path spelling with
      -- the realization map `X`.
      simpa [localMartingaleProblemMartingalePart_id_comp_path] using hX.martingalePart i
    -- Proof comment: the generic pushforward theorem now applies directly to the normalized
    -- canonical-path martingale part.
    simpa [canonicalPathFiltration] using
      (IsContinuousLocalMartingale.pushforward_comp_path
        (μ := μ)
        (X := X)
        (M := localMartingaleProblemMartingalePart b id i)
        hPathAdapted
        (hMartingalePartAdapted i)
        (hMartingalePartCont i)
        hSource)
  · intro i j
    have hSource :
        HasContinuousQuadraticCovariation
          ℱ
          μ
          (fun t ω ↦ localMartingaleProblemMartingalePart b id i t (X ω))
          (fun t ω ↦ localMartingaleProblemMartingalePart b id j t (X ω))
          (fun t ω ↦ localMartingaleProblemCovariation a id i j t (X ω)) := by
      -- Proof comment: rewrite the prescribed source quadratic-covariation field into the
      -- canonical-path spelling before transporting it to path space.
      simpa [localMartingaleProblemMartingalePart_id_comp_path,
        localMartingaleProblemCovariation_id_comp_path] using hX.quadraticCovariation i j
    -- Proof comment: the generic quadratic-covariation pushforward theorem closes the canonical
    -- path-space field once the adaptedness/continuity/finite-variation hypotheses are supplied.
    simpa [canonicalPathFiltration] using
      (HasContinuousQuadraticCovariation.pushforward_comp_path
        (μ := μ)
        (X := X)
        (M := localMartingaleProblemMartingalePart b id i)
        (N := localMartingaleProblemMartingalePart b id j)
        (A := localMartingaleProblemCovariation a id i j)
        hPathAdapted
        (hMartingalePartAdapted i)
        (hMartingalePartAdapted j)
        (localMartingaleProblemCovariation_zero (a := a) (X := id) i j)
        (hCovariationAdapted i j)
        (hMartingalePartCont i)
        (hMartingalePartCont j)
        (hCovariationCont i j)
        (hCovariationLFV i j)
        hSource)

/-- Helper for Remark 26.24: any local-martingale-problem realization can first be normalized to
canonical path space by pushing its law forward along the realized path map. -/
theorem IsLocalMartingaleProblemSolution.pushforward_isCanonicalPathSolutionCore
    {a : NNReal → State → Fin n → Fin n → ℝ} {b : DriftCoeff}
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X)
    (hPathAdapted : Adapted ℱ (pathProcess X))
    (hMartingalePartAdapted :
      ∀ i : Fin n,
        Adapted canonicalPathFiltration (localMartingaleProblemMartingalePart b id i))
    (hMartingalePartCont :
      ∀ i : Fin n,
        ∀ γ : PathSpace,
          Continuous (fun t : NNReal ↦ localMartingaleProblemMartingalePart b id i t γ))
    (hCovariationAdapted :
      ∀ i j : Fin n,
        Adapted canonicalPathFiltration (localMartingaleProblemCovariation a id i j))
    (hCovariationCont :
      ∀ i j : Fin n,
        ∀ γ : PathSpace,
          Continuous (fun t : NNReal ↦ localMartingaleProblemCovariation a id i j t γ))
    (hCovariationLFV :
      ∀ i j : Fin n,
        ∀ᵐ γ ∂(μ.map X),
          LocallyBoundedVariationOn
            (⟨fun t ↦ localMartingaleProblemCovariation a id i j t γ,
              hCovariationCont i j γ⟩ : C(NNReal, ℝ))
            Set.univ) :
    IsLocalMartingaleProblemSolution μ₀ a b canonicalPathFiltration (μ.map X) id := by
  -- Route correction: the previous `hX`-only statement hid the real obstruction. The pushforward
  -- transport is available once the canonical-path side conditions are supplied explicitly.
  exact
    pushforward_isCanonicalPathSolutionCore_of_sideConditions
      (hX := hX)
      hPathAdapted
      hMartingalePartAdapted
      hMartingalePartCont
      hCovariationAdapted
      hCovariationCont
      hCovariationLFV

/-- Helper for Remark 26.24: the unresolved backward `26.21` content is the direct law-preserving
bridge from a Dirac-start local martingale problem solution to a generalized weak SDE solution. -/
theorem exists_diracGeneralizedWeakSDESolution_with_statePathLaw_of_localMartingaleProblemBridge
    {b : DriftCoeff} {x : State}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ μ X) :
    ∃ G : GeneralizedWeakSDESolution (Measure.dirac x) σ b,
      G.statePathLaw = μ.map X := by
  -- TODO: first canonicalize `hX` by the explicit pushforward theorem already proved above, then
  -- build the weak path-space lift and package it with `generalizedWeakSolutionOfWeakPathLift`
  -- so that the final state-path law stays definitionally equal to `μ.map X`.
  -- Current blocker: this backward bridge depends on the unresolved forward row-pair
  -- quadratic-covariation theorem, whose Chapter 25 transport step cannot currently be checked
  -- because the imported `Items/Chap25/Theorem_25_22.lean` file fails to elaborate.
  sorry
/-- Helper for Remark 26.24: view a path-valued weak solution as its time-indexed state process.
-/
abbrev weakSolutionStateProcess {Ω : Type u} (Y : Ω → PathSpace) :
    NNReal → Ω → State :=
  fun t ω ↦ Y ω t

/-- Helper for Remark 26.24: the coefficient-based weak-solution predicate associated to the
generalized SDE with diffusion `σ` and drift `b`. -/
def solvesWeakGeneralizedSDE (σ : DiffusionCoeff) (b : DriftCoeff) :
    {Ω : Type u} → [MeasurableSpace Ω] →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → Measure Ω →
      (Ω → PathSpace) → (NNReal → Ω → Fin m → ℝ) → Prop :=
  fun {_} _ ℱ μ X W ↦
    ∃ _ : IsProbabilityMeasure μ,
      IsGeneralizedNDimensionalDiffusion ℱ μ
        (fun ω ↦ X ω 0)
        W
        σ
        b
        (weakSolutionStateProcess X)

/-- Helper for Remark 26.24: a weak SDE solution with an exact Brownian path lift and an
independent time-zero state packages as a generalized weak solution without changing its
state-path law. -/
theorem generalizedWeakSolutionOfWeakPathLift
    {σ : DiffusionCoeff} {b : DriftCoeff} {x : State}
    (L : WeakSDESolution.{u} n m (Measure.dirac x) (solvesWeakGeneralizedSDE σ b))
    {Wpath : L.Ω → EuclideanPathSpace m}
    (hWpath : L.W = pathProcess Wpath)
    (hIndep : IndepFun (fun ω ↦ L.X ω 0) Wpath L.μ) :
    ∃ G : GeneralizedWeakSDESolution.{u} (Measure.dirac x) σ b,
      G.statePathLaw = L.statePathLaw := by
  -- Proof comment: the weak witness already stores the filtered probability space, Brownian
  -- driver, adapted state path, and initial law; the extra generalized-weak fields are exactly
  -- the explicit path lift `Wpath` and the time-zero datum `fun ω ↦ L.X ω 0`.
  have hBrownian :
      IsBrownianMotionWithFiltration L.ℱ L.μ L.W := by
    simpa [IsBrownianMotionWithFiltration] using L.brownian
  have hBrownianPath :
      GeneralizedSDEBrownianMotion L.μ L.ℱ Wpath := by
    refine ⟨inferInstance, ?_⟩
    simpa [hWpath] using hBrownian
  have hSolvesWeak :
      SolvesGeneralizedSDE σ b L.ℱ L.μ L.X L.W := by
    -- Proof comment: the local weak-solution predicate is just the imported generalized-SDE
    -- predicate under the spelling `weakSolutionStateProcess`.
    simpa [solvesWeakGeneralizedSDE, SolvesGeneralizedSDE, weakSolutionStateProcess, pathProcess]
      using L.solves_sde
  have hSolvesStrong :
      SolvesStrongGeneralizedSDE σ b L.μ L.ℱ (fun ω ↦ L.X ω 0) Wpath L.X := by
    -- Proof comment: once the Brownian driver is rewritten as `pathProcess Wpath`, the standard
    -- Chapter 26 path-lift bridge upgrades the weak predicate to the strong-owner predicate.
    simpa using solvesStrongGeneralizedSDE_of_pathLift hSolvesWeak hWpath
  let G : GeneralizedWeakSDESolution.{u} (Measure.dirac x) σ b :=
    { toWeakSDESolution :=
        { Ω := L.Ω
          instMeasurableSpace := inferInstance
          μ := L.μ
          instIsProbabilityMeasure := inferInstance
          ℱ := L.ℱ
          instUsualConditions := inferInstance
          X := L.X
          W := L.W
          brownian := L.brownian
          coordinate_martingale := L.coordinate_martingale
          adapted := L.adapted
          initialLaw := L.initialLaw
          solves_sde := hSolvesWeak }
      ξ := fun ω ↦ L.X ω 0
      Wpath := Wpath
      w_eq := hWpath
      initial_state_eq := Filter.EventuallyEq.rfl
      initial_data_measurable := L.adapted 0
      independent_initial_brownian := hIndep
      brownian_path := hBrownianPath
      solves_strong_sde := hSolvesStrong }
  -- Proof comment: the wrapper leaves the underlying state-path random variable unchanged, so the
  -- pushed-forward law on `PathSpace` is literally the same.
  exact ⟨G, rfl⟩

/-- Helper for Remark 26.24: once the canonical path-space local-martingale owner is available,
the remaining backward `26.21` work is the weak-path lift to a generalized weak SDE solution with
the same law. -/
theorem exists_diracGeneralizedWeakSDESolution_with_statePathLaw_of_canonicalPathSolution
    {b : DriftCoeff} {x : State} {μ : Measure PathSpace}
    (hX :
      IsLocalMartingaleProblemSolution
        (Measure.dirac x) σσᵀ b canonicalPathFiltration μ id) :
    ∃ G : GeneralizedWeakSDESolution (Measure.dirac x) σ b,
      G.statePathLaw = μ := by
  -- Route correction: after canonicalization, the backward bridge should be one weak-path-lift
  -- theorem rather than a second large remark-local transport proof.
  simpa using
    exists_diracGeneralizedWeakSDESolution_with_statePathLaw_of_localMartingaleProblemBridge
      (σ := σ)
      (b := b)
      (x := x)
      (Ω := PathSpace)
      (mΩ := borel PathSpace)
      (ℱ := canonicalPathFiltration)
      (μ := μ)
      (X := id)
      hX

/-- Helper for Remark 26.24: the backward `26.21` bridge should turn any Dirac-start local
martingale problem solution into a generalized weak SDE solution with the same path law. -/
theorem exists_diracGeneralizedWeakSDESolution_with_statePathLaw_of_localMartingaleProblemSolution
    {b : DriftCoeff} {x : State}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration NNReal mΩ}
    {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ μ X) :
    ∃ G : GeneralizedWeakSDESolution (Measure.dirac x) σ b,
      G.statePathLaw = μ.map X := by
  -- Proof comment: this direct bridge is the exact remaining 26.21 content needed downstream;
  -- canonical-path normalization is now part of the same unresolved transport theorem.
  exact
    exists_diracGeneralizedWeakSDESolution_with_statePathLaw_of_localMartingaleProblemBridge
      (σ := σ)
      (b := b)
      (x := x)
      hX

/-- Helper for Remark 26.24: once the exact forward/backward `26.21` law-preserving bridges are
available, the Dirac-start generalized-weak existence and canonical-law package upgrades to the
Dirac-start local martingale problem existence and unique-law data. -/
theorem diracLocalMartingaleProblemData_of_diracGeneralizedWeakCanonicalLaw
    {b : DriftCoeff} {x : State}
    (hGeneralizedWeak : Nonempty (GeneralizedWeakSDESolution (Measure.dirac x) σ b))
    (hCanonicalLaw :
      ∃ ν : Measure PathSpace,
        ∀ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b, L.statePathLaw = ν) :
    (∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
      (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
      IsLocalMartingaleProblemSolution
        (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X) ∧
      LocalMartingaleProblemHasUniqueLaw (Measure.dirac x) σσᵀ b := by
  refine ⟨?_, ?_⟩
  · rcases hGeneralizedWeak with ⟨L⟩
    -- Proof comment: the forward `26.21` bridge should send one deterministic-start generalized
    -- weak realization to one deterministic-start local-martingale-problem realization.
    rcases
        existsLocalMartingaleProblemSolution_with_statePathLaw_of_diracGeneralizedWeakSDESolution
          (σ := σ)
          (b := b)
          (x := x)
          L with
      ⟨Ω, mΩ, ℱ, P, X, hX, _hLaw⟩
    exact ⟨Ω, mΩ, ℱ, P, X, hX⟩
  · intro Ω mΩ ℱ μ X Ω' mΩ' ℱ' μ' X' hX hX'
    rcases
        exists_diracGeneralizedWeakSDESolution_with_statePathLaw_of_localMartingaleProblemSolution
          (σ := σ)
          (b := b)
          (x := x)
          hX with
      ⟨GX, hGX⟩
    rcases
        exists_diracGeneralizedWeakSDESolution_with_statePathLaw_of_localMartingaleProblemSolution
          (σ := σ)
          (b := b)
          (x := x)
          hX' with
      ⟨GX', hGX'⟩
    rcases hCanonicalLaw with ⟨ν, hν⟩
    -- Proof comment: transport both local-martingale-problem witnesses back to deterministic-start
    -- generalized weak solutions and compare them through the canonical generalized-weak path law.
    calc
      μ.map X = GX.statePathLaw := hGX.symm
      _ = ν := hν GX
      _ = GX'.statePathLaw := (hν GX').symm
      _ = μ'.map X' := hGX'

-- Proof sketch: for each deterministic starting point `x`, Theorem 26.8 gives a unique strong
-- solution of the SDE with coefficients `σ` and `b`. Theorem 26.18 upgrades this to weak
-- existence together with pathwise uniqueness, and Theorem 26.21 identifies those weak solutions
-- with solutions of the local martingale problem for `(σσᵀ, b)`, yielding existence and
-- uniqueness in law for every Dirac initial distribution.
/-- Remark 26.24: if `σ` and `b` satisfy the hypotheses of Theorem 26.8, then the local
martingale problem `LMP (σσᵀ, b)` is well-posed. -/
theorem localMartingaleProblemWellPosed_of_lipschitz_linearGrowth
    (σ : DiffusionCoeff) (b : DriftCoeff) {K : ℝ} (hK : 0 < K)
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2)) :
    LocalMartingaleProblemWellPosed σσᵀ b := by
  -- Proof comment: the main route is to build, for each deterministic start `x`, the exact data
  -- required by `localMartingaleProblemWellPosed_of_diracData`.
  refine localMartingaleProblemWellPosed_of_diracData (a := σσᵀ) (b := b) ?_
  intro x
  have hGeneralizedWeak :
      Nonempty (GeneralizedWeakSDESolution (Measure.dirac x) σ b) ∧
        ∀ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b, L.IsWeaklyUnique :=
    diracGeneralizedWeakData_of_lipschitzLinearGrowth
      (σ := σ)
      (b := b)
      hbσ_lipschitz
      hbσ_growth
      x
  have hCanonicalLaw :
      ∃ ν : Measure PathSpace,
        ∀ L : GeneralizedWeakSDESolution (Measure.dirac x) σ b, L.statePathLaw = ν :=
    exists_diracGeneralizedWeakCanonicalLaw_of_lipschitzLinearGrowth
      (σ := σ)
      (b := b)
      hbσ_lipschitz
      hbσ_growth
      x
  -- Route correction: the blocker is no longer the local `26.8 -> 26.18` packaging. The only
  -- remaining frontier is the exact pair of law-preserving `26.21` bridges isolated just above.
  let _ := hK
  -- Proof comment: after `26.8 -> 26.18`, the remaining assembly is exactly the deterministic-
  -- start local-martingale-problem packaging theorem proved immediately above.
  exact
    diracLocalMartingaleProblemData_of_diracGeneralizedWeakCanonicalLaw
      (σ := σ)
      (b := b)
      (x := x)
      hGeneralizedWeak.1
      hCanonicalLaw

end

end ProbabilityTheory
