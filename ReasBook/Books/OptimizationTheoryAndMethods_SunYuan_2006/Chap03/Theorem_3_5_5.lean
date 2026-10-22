/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_5_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_3_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_5_6

noncomputable section

open Filter
open scoped Topology

section NegativeCurvatureDirectionMethodFiniteRun

variable {n : ℕ}

namespace NegativeCurvatureDirectionMethodRun

/-- The run stops at its terminal iterate through the source small-gradient branch of
Algorithm 3.5.4 rather than through the terminal line-search-failure branch. -/
def terminalStopsBySmallGradient {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) : Prop :=
  negativeCurvatureTerminalSmallGradient
    A.ε (A.g A.terminalIndex) (A.L A.terminalIndex) (A.dDiag A.terminalIndex)
    (A.eDiag A.terminalIndex) (A.pivotStep A.terminalIndex)

/-- Unfolding formula for the terminal small-gradient stopping predicate. -/
@[simp] theorem terminalStopsBySmallGradient_iff {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) :
    A.terminalStopsBySmallGradient ↔
      negativeCurvatureTerminalSmallGradient
        A.ε (A.g A.terminalIndex) (A.L A.terminalIndex) (A.dDiag A.terminalIndex)
        (A.eDiag A.terminalIndex) (A.pivotStep A.terminalIndex) :=
  Iff.rfl

/-- The source-facing finite-run condition for Algorithm 3.5.4: every nonterminal step uses a
genuine line-search step, and termination happens through the textbook small-gradient branch
rather than the auxiliary terminal line-search-failure branch in the canonical run owner. -/
def IsAlgorithm354Run {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) : Prop :=
  (∀ k : ℕ, k < A.terminalIndex → IsLineSearchStep f (A.x k) (A.d k) (A.α k)) ∧
    A.terminalStopsBySmallGradient

/-- Unfolding formula for the source-facing finite-run predicate. -/
@[simp] theorem isAlgorithm354Run_iff {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) :
    A.IsAlgorithm354Run ↔
      (∀ k : ℕ, k < A.terminalIndex → IsLineSearchStep f (A.x k) (A.d k) (A.α k)) ∧
        A.terminalStopsBySmallGradient :=
  Iff.rfl

/-- The source "last element" of a finite run is the terminal iterate in the small-gradient
branch and the post-update iterate in the terminal line-search-failure branch. -/
def lastIterate {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) : NegativeCurvaturePoint n := by
  classical
  exact if hA : A.terminalStopsBySmallGradient then
    A.x A.terminalIndex
  else
    A.x (A.terminalIndex + 1)

/-- In the source small-gradient terminal branch, the last iterate is the terminal iterate. -/
@[simp] theorem lastIterate_eq_terminalIndex {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f)
    (hA : A.terminalStopsBySmallGradient) :
    A.lastIterate = A.x A.terminalIndex := by
  classical
  rw [lastIterate]
  exact if_pos hA

/-- In the source terminal line-search-failure branch, the last iterate is the post-update
iterate. -/
@[simp] theorem lastIterate_eq_terminalIndex_succ {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f)
    (hA : ¬ A.terminalStopsBySmallGradient) :
    A.lastIterate = A.x (A.terminalIndex + 1) := by
  classical
  rw [lastIterate]
  exact if_neg hA

end NegativeCurvatureDirectionMethodRun

-- Domain sampling pass:
-- * primary domain: finite terminating executions of the Chapter 3 negative-curvature
--   direction method on `ℝⁿ`;
-- * sampled source/core owners: `NegativeCurvatureDirectionMethodRun` and
--   `negativeCurvatureTerminalSmallGradient` from `Algorithm_3_5_4`;
-- * owner abstraction chosen here: the existing finite-run owner
--   `NegativeCurvatureDirectionMethodRun`, together with explicit hypotheses recording
--   the source zero-tolerance finite-run hypotheses on the generated iterates;
-- * source/core/bridge triage: this theorem stays source-facing on the canonical run owner,
--   with the bounded/closed/convex level-set hypotheses from the source statement restored
--   explicitly;
-- * primitive/derived split: primitive data are the recorded run together with the source
--   regularity, level-set, and domain-membership hypotheses;
--   the stationary-point conclusion is derived API.

variable {f : NegativeCurvaturePoint n → ℝ}
variable {D : Set (NegativeCurvaturePoint n)}

/-- Helper for Chapter03 Theorem 3.5.5 (1): on a finite Algorithm 3.5.4 run, the source
zero-tolerance small-gradient stopping branch forces the recorded terminal gradient vector to
vanish. -/
lemma NegativeCurvatureDirectionMethodRun.terminalGradientZero_of_zeroTolerance
    (A : NegativeCurvatureDirectionMethodRun n f)
    (hε : A.ε = 0)
    (hTerminal : A.terminalStopsBySmallGradient) :
    A.g A.terminalIndex = 0 := by
  -- The terminal stopping inequality is `‖g_k‖ ≤ ε = 0`, so the terminal gradient norm is zero.
  rcases hTerminal with ⟨hNorm, _⟩
  exact norm_eq_zero.mp <| le_antisymm (by simpa [hε] using hNorm) (norm_nonneg _)

/-- Finite-run part of Chapter03 Theorem 3.5.5: let `f : ℝ^n → ℝ` be twice continuously
differentiable on the
open set `D`. If `A` records a finite run of Algorithm 3.5.4 with tolerance `ε = 0`, all
iterates of the finite sequence in `D`, and the source line-search and terminal small-gradient
rules encoded by `A.IsAlgorithm354Run`, then the last element `A.lastIterate` of that finite
sequence is a stationary point of `f`. -/
theorem zeroToleranceNegativeCurvatureFiniteRun_terminalIterate_stationary
    (A : NegativeCurvatureDirectionMethodRun n f)
    (hε : A.ε = 0)
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hSourceRun : A.IsAlgorithm354Run)
    (hIterates_mem : ∀ k : ℕ, k ≤ A.terminalIndex + 1 → A.x k ∈ D) :
    IsStationaryPoint f A.lastIterate := by
  rcases hSourceRun with ⟨_, hTerminal⟩
  -- The source finite-run owner stops at the terminal iterate through the small-gradient branch.
  have hLast : A.lastIterate = A.x A.terminalIndex :=
    A.lastIterate_eq_terminalIndex hTerminal
  have hGradientZeroRecorded : A.g A.terminalIndex = 0 :=
    A.terminalGradientZero_of_zeroTolerance hε hTerminal
  have hGradientZero :
      gradient f (A.x A.terminalIndex) = 0 := by
    simpa [A.gradient_eq A.terminalIndex le_rfl] using hGradientZeroRecorded
  have hTerminalMem : A.x A.terminalIndex ∈ D :=
    hIterates_mem A.terminalIndex (Nat.le_succ A.terminalIndex)
  have hDifferentiable :
      DifferentiableAt ℝ f (A.x A.terminalIndex) := by
    exact
      ((show ContDiffOn ℝ 1 f D from hC2.of_le (by norm_num)).contDiffAt
        (hD_open.mem_nhds hTerminalMem)).differentiableAt_one
  -- Package the zero-gradient terminal iterate through the Chapter 1 stationary-point criterion.
  rw [hLast, isStationaryPoint_iff]
  exact ⟨hGradientZero, hDifferentiable⟩

end NegativeCurvatureDirectionMethodFiniteRun

section NegativeCurvatureDirectionMethodInfiniteRun

variable {n : ℕ}

-- Domain sampling pass:
-- * primary domain: source-facing infinite sequences generated by Algorithm 3.5.4 on `ℝⁿ`;
-- * sampled source/core owners: `negativeCurvatureLevelSet` from `Theorem_3_5_6` and the
--   concrete Step 4 / Step 5 data from `Algorithm_3_5_4`;
-- * owner abstraction chosen here: a Euclidean sequence owner that records exactly the
--   algorithmic data needed to say that `{x_k}` is generated by Algorithm 3.5.4 with `ε = 0`;
-- * source/core/bridge triage: the labeled theorems stay source-facing, with the textbook
--   bounded/closed/convex level-set hypotheses explicit in the theorem headers;
-- * primitive/derived split: primitive data are the algorithm-generated sequence and the source
--   level-set assumptions, while accumulation-point existence and stationarity remain theorem
--   conclusions.

variable {f : NegativeCurvaturePoint n → ℝ}
variable {D : Set (NegativeCurvaturePoint n)}
variable {xBar x₀ : NegativeCurvaturePoint n}
variable {x : ℕ → NegativeCurvaturePoint n}

/-- Helper for Chapter03 Theorem 3.5.5: the raw infinite-run data recorded by Algorithm 3.5.4 on
`D` with starting point `x₀` and tolerance `ε = 0`. This is the terminal-free infinite analogue
of the local `NegativeCurvatureDirectionMethodRun` owner from `Algorithm_3_5_4`: it records the
Step 2 gradient/Hessian data, the Step 3 modified-Cholesky factorization data, and for every
index `k` the Step 4 / Step 5 search direction, the positive-definite corrected system matrix,
the accepted Step 6 exact line-search step on the nonnegative ray, the Step 6 update, and the
Step 7 strict decrease clause that the source algorithm uses to generate the next iterate. -/
structure ZeroToleranceNegativeCurvatureDirectionMethodSequenceIterates
    (f : NegativeCurvaturePoint n → ℝ)
    (D : Set (NegativeCurvaturePoint n))
    (x₀ : NegativeCurvaturePoint n) (x : ℕ → NegativeCurvaturePoint n) where
  g : ℕ → NegativeCurvaturePoint n
  G : ℕ → Matrix (Fin n) (Fin n) ℝ
  L : ℕ → Matrix (Fin n) (Fin n) ℝ
  dDiag : ℕ → Fin n → ℝ
  eDiag : ℕ → Fin n → ℝ
  pivotStep : ∀ k : ℕ, NegativeCurvaturePivotStep (L k) (dDiag k) (eDiag k)
  d : ℕ → NegativeCurvaturePoint n
  α : ℕ → ℝ
  x_zero : x 0 = x₀
  gradient_eq : ∀ k : ℕ, g k = gradient f (x k)
  hessian :
    ∀ k : ℕ,
      HasFDerivAt (gradient f)
        (((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
              NegativeCurvaturePoint n →L[ℝ] NegativeCurvaturePoint n) (G k)))
        (x k)
  correction_nonneg :
    ∀ k : ℕ, ∀ i : Fin n, 0 ≤ eDiag k i
  factorization :
    ∀ k : ℕ,
      G k + Matrix.diagonal (eDiag k) = modifiedCholeskySystemMatrix (L k) (dDiag k)
  iterateDirection :
    ∀ k : ℕ,
      NegativeCurvatureDirectionStep 0
        (g k) (L k) (dDiag k) (eDiag k) (pivotStep k) (d k)
  corrected_posDef :
    ∀ k : ℕ, (modifiedCholeskySystemMatrix (L k) (dDiag k)).PosDef
  exactLineSearch :
    ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  update :
    ∀ k : ℕ, x (k + 1) = x k + α k • d k
  strictDecrease :
    ∀ k : ℕ, f (x (k + 1)) < f (x k)
  iterates_mem : ∀ k : ℕ, x k ∈ D

namespace NegativeCurvatureDirectionMethodSequence

/-- Helper for Chapter03 Theorem 3.5.5: on the nonstationary linear-system branch of
Algorithm 3.5.4, the source proof uses the same modified-Cholesky descent estimate recalled in
Example 3.3.3. -/
def DescentEstimate
    (f : NegativeCurvaturePoint n → ℝ)
    {D : Set (NegativeCurvaturePoint n)}
    {x₀ : NegativeCurvaturePoint n}
    {x : ℕ → NegativeCurvaturePoint n}
    (A : ZeroToleranceNegativeCurvatureDirectionMethodSequenceIterates f D x₀ x) : Prop :=
  ∃ κ > 0, ∀ k : ℕ, gradient f (x k) ≠ 0 →
    -(inner ℝ (gradient f (x k)) (A.d k)) / ‖A.d k‖ ≥ (1 / κ) * ‖gradient f (x k)‖

end NegativeCurvatureDirectionMethodSequence

/-- Helper for Chapter03 Theorem 3.5.5: `IsZeroToleranceNegativeCurvatureDirectionMethodSequence
f D x₀ x` records that the iterate sequence `x` is generated by Algorithm 3.5.4 on `D` with
starting point `x₀` and tolerance `ε = 0`. Besides the raw Step 2-Step 7 algorithm data above,
this public source-facing owner also packages the modified-Cholesky descent estimate recalled in
Example 3.3.3, so the theorem hypotheses match the book's "generated by Algorithm 3.5.4"
assumption rather than a weaker proof-side surrogate. -/
structure IsZeroToleranceNegativeCurvatureDirectionMethodSequence
    (f : NegativeCurvaturePoint n → ℝ)
    (D : Set (NegativeCurvaturePoint n))
    (x₀ : NegativeCurvaturePoint n) (x : ℕ → NegativeCurvaturePoint n)
    extends ZeroToleranceNegativeCurvatureDirectionMethodSequenceIterates f D x₀ x where
  descentEstimate :
    NegativeCurvatureDirectionMethodSequence.DescentEstimate f
      toZeroToleranceNegativeCurvatureDirectionMethodSequenceIterates

/-- Helper for Chapter03 Theorem 3.5.5: in Euclidean space, the source level set is compact once
it is closed and bounded. -/
lemma negativeCurvatureLevelSet_compact
    (hLevel_bounded : Bornology.IsBounded (negativeCurvatureLevelSet D f xBar))
    (hLevel_closed : IsClosed (negativeCurvatureLevelSet D f xBar)) :
    IsCompact (negativeCurvatureLevelSet D f xBar) := by
  -- Closed-and-bounded is compact in the finite-dimensional Euclidean ambient space.
  exact (Metric.isCompact_iff_isClosed_bounded.2 ⟨hLevel_closed, hLevel_bounded⟩)

/-- Helper for Chapter03 Theorem 3.5.5: strict objective decrease keeps every iterate inside the
initial level set determined by `xBar`. -/
lemma iterates_mem_negativeCurvatureLevelSet
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x)
    (hx₀ : x₀ ∈ negativeCurvatureLevelSet D f xBar) :
    ∀ k : ℕ, x k ∈ negativeCurvatureLevelSet D f xBar := by
  intro k
  induction k with
  | zero =>
      -- The starting iterate is exactly `x₀`, so it inherits the initial level-set membership.
      simpa [negativeCurvatureLevelSet, hAlgorithm.x_zero] using hx₀
  | succ k hk =>
      -- One-step strict decrease propagates the objective bound to the next iterate.
      refine ⟨hAlgorithm.iterates_mem (k + 1), ?_⟩
      exact le_trans (hAlgorithm.strictDecrease k).le hk.2

/-- Helper for Chapter03 Theorem 3.5.5: if an accumulation point `xStar` of the subsequence
`x ∘ φ` is nonstationary, then continuity of `gradient f` yields a positive lower bound for the
subsequence gradient norms on a tail. -/
lemma subsequenceGradientNorm_eventually_ge_of_limitGradient_ne_zero
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    {xStar : NegativeCurvaturePoint n} {φ : ℕ → ℕ}
    (hxStar_mem : xStar ∈ D)
    (hTendsto : Tendsto (x ∘ φ) atTop (nhds xStar))
    (hGradient_ne : gradient f xStar ≠ 0) :
    ∃ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ε ≤ ‖gradient f (x (φ n))‖ := by
  let ε := ‖gradient f xStar‖ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact half_pos (norm_pos_iff.mpr hGradient_ne)
  have hGradCont : ContinuousAt (gradient f) xStar := by
    have hfContDiffAt : ContDiffAt ℝ 1 f xStar :=
      (hC2.of_le (by norm_num)).contDiffAt (hD_open.mem_nhds hxStar_mem)
    have hfderivContDiffAt : ContDiffAt ℝ 0 (fderiv ℝ f) xStar :=
      hfContDiffAt.fderiv_right (by norm_num)
    have hgradContDiffAt :
        ContDiffAt ℝ 0
          (((InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm) ∘ (fderiv ℝ f))
          xStar := by
      exact
        (LinearIsometryEquiv.contDiff
          ((InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm)).contDiffAt.comp xStar
          hfderivContDiffAt
    change ContinuousAt
      (((InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm) ∘ (fderiv ℝ f))
      xStar
    exact hgradContDiffAt.continuousAt
  have hGradTendsto :
      Tendsto (fun n ↦ gradient f (x (φ n))) atTop (nhds (gradient f xStar)) :=
    hGradCont.tendsto.comp hTendsto
  have hNormTendsto :
      Tendsto (fun n ↦ ‖gradient f (x (φ n))‖) atTop (nhds ‖gradient f xStar‖) :=
    hGradTendsto.norm
  rw [Metric.tendsto_atTop] at hNormTendsto
  obtain ⟨N, hN⟩ := hNormTendsto ε hε_pos
  refine ⟨ε, hε_pos, N, ?_⟩
  intro n hn
  have hdist :
      dist ‖gradient f (x (φ n))‖ ‖gradient f xStar‖ < ε :=
    hN n hn
  have hlower :
      ‖gradient f xStar‖ - ε < ‖gradient f (x (φ n))‖ := by
    have habs : |‖gradient f (x (φ n))‖ - ‖gradient f xStar‖| < ε := by
      simpa [Real.dist_eq] using hdist
    have hsub : -ε < ‖gradient f (x (φ n))‖ - ‖gradient f xStar‖ :=
      (abs_lt.mp habs).1
    linarith
  have hε_eq : ‖gradient f xStar‖ - ε = ε := by
    dsimp [ε]
    ring
  have hlt : ε < ‖gradient f (x (φ n))‖ := by
    linarith
  exact hlt.le

/-- Helper for Chapter03 Theorem 3.5.5: at tolerance `0`, any iterate with nonzero gradient is
forced into the linear-system branch of `NegativeCurvatureDirectionStep`. -/
lemma iterateDirection_linearSystem_of_gradient_ne_zero
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x)
    (k : ℕ)
    (hGradient_ne : gradient f (x k) ≠ 0) :
    (modifiedCholeskySystemMatrix (hAlgorithm.L k) (hAlgorithm.dDiag k)).mulVec
        (hAlgorithm.d k) =
      -gradient f (x k) := by
  -- The `‖g_k‖ ≤ 0` branch would force `g_k = 0`, so only the linear-system branch survives.
  rcases hAlgorithm.iterateDirection k with hlinear | hsmall
  · simpa [hAlgorithm.gradient_eq k] using hlinear.2
  · have hgrad_zero : gradient f (x k) = 0 := by
      apply norm_eq_zero.mp
      have hnorm_le : ‖gradient f (x k)‖ ≤ 0 := by
        simpa [hAlgorithm.gradient_eq k] using hsmall.1
      exact le_antisymm hnorm_le (norm_nonneg _)
    exact False.elim (hGradient_ne hgrad_zero)

/-- Helper for Chapter03 Theorem 3.5.5: the shifted objective values
`f (x (φ n + 1))` converge to the same limit as the convergent subsequence `f (x (φ n))`. -/
lemma tendsto_objective_shiftedSubsequence_of_accumulationPoint
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x)
    {xStar : NegativeCurvaturePoint n} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hCont : ContinuousAt f xStar)
    (hTendsto : Tendsto (x ∘ φ) atTop (nhds xStar)) :
    Tendsto (fun n ↦ f (x (φ n + 1))) atTop (nhds (f xStar)) := by
  have hObjectiveTendsto :
      Tendsto (fun n ↦ f (x (φ n))) atTop (nhds (f xStar)) :=
    hCont.tendsto.comp hTendsto
  have hObjectiveTendstoSucc :
      Tendsto (fun n ↦ f (x (φ (n + 1)))) atTop (nhds (f xStar)) :=
    hObjectiveTendsto.comp (tendsto_add_atTop_nat 1)
  have hAntitone : Antitone (fun k : ℕ ↦ f (x k)) := by
    -- The recorded strict objective decrease upgrades to antitonicity on `ℕ`.
    refine antitone_nat_of_succ_le fun k ↦ ?_
    exact (hAlgorithm.strictDecrease k).le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    hObjectiveTendstoSucc hObjectiveTendsto ?_ ?_
  · intro n
    exact hAntitone (Nat.succ_le_of_lt (hφ (Nat.lt_succ_self n)))
  · intro n
    exact (hAlgorithm.strictDecrease (φ n)).le

/-- Helper for Chapter03 Theorem 3.5.5: every subsequential limit of iterates generated by the
zero-tolerance negative-curvature direction method remains in the source level set
`negativeCurvatureLevelSet D f xBar`. -/
lemma accumulationPoint_mem_negativeCurvatureLevelSet
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x)
    (hx₀ : x₀ ∈ negativeCurvatureLevelSet D f xBar)
    (hLevel_closed : IsClosed (negativeCurvatureLevelSet D f xBar))
    {xStar : NegativeCurvaturePoint n} {φ : ℕ → ℕ}
    (hTendsto : Tendsto (x ∘ φ) atTop (nhds xStar)) :
    xStar ∈ negativeCurvatureLevelSet D f xBar := by
  have hLevelEventually :
      ∀ᶠ n in atTop, (x ∘ φ) n ∈ negativeCurvatureLevelSet D f xBar :=
    Filter.Eventually.of_forall fun n ↦
      iterates_mem_negativeCurvatureLevelSet hAlgorithm hx₀ (φ n)
  -- Closedness keeps the whole convergent subsequence inside the original level set.
  exact hLevel_closed.mem_of_tendsto hTendsto hLevelEventually

/-- Helper for Chapter03 Theorem 3.5.5: on any iterate with nonzero gradient, the zero-tolerance
Step 4 linear-system branch produces a genuine descent direction. -/
lemma iterateDirection_isDescentDirectionAt_of_gradient_ne_zero
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x)
    (k : ℕ)
    (hGradient_ne : gradient f (x k) ≠ 0) :
    IsDescentDirectionAt f (x k) (hAlgorithm.d k) := by
  -- Rewrite the Chapter 1 descent predicate to the gradient-pairing inequality.
  rw [isDescentDirectionAt_iff]
  have hd_ne : hAlgorithm.d k ≠ 0 := by
    intro hd_zero
    have hsystem :
        (0 : NegativeCurvaturePoint n) = -gradient f (x k) := by
      simpa [hd_zero] using
        iterateDirection_linearSystem_of_gradient_ne_zero hAlgorithm k hGradient_ne
    have hzero : gradient f (x k) = 0 := by
      have := congrArg Neg.neg hsystem
      simpa using this.symm
    exact hGradient_ne hzero
  have hpos :
      0 <
        dotProduct (hAlgorithm.d k)
          ((modifiedCholeskySystemMatrix (hAlgorithm.L k) (hAlgorithm.dDiag k)).mulVec
            (hAlgorithm.d k)) :=
    Matrix.PosDef.dotProduct_mulVec_pos (hAlgorithm.corrected_posDef k) (by simpa using hd_ne)
  have hrewrite :
      dotProduct (hAlgorithm.d k)
          ((modifiedCholeskySystemMatrix (hAlgorithm.L k) (hAlgorithm.dDiag k)).mulVec
            (hAlgorithm.d k)) =
        -inner ℝ (hAlgorithm.g k) (hAlgorithm.d k) := by
    rw [iterateDirection_linearSystem_of_gradient_ne_zero hAlgorithm k hGradient_ne, dotProduct_neg]
    rw [← hAlgorithm.gradient_eq k]
    have hdot :
        dotProduct (hAlgorithm.d k) (hAlgorithm.g k) =
          inner ℝ (hAlgorithm.g k) (hAlgorithm.d k) := by
      simp [dotProduct, PiLp.inner_apply]
    rw [hdot]
  have hInnerNeg : inner ℝ (hAlgorithm.g k) (hAlgorithm.d k) < 0 := by
    linarith
  simpa [hAlgorithm.gradient_eq k] using hInnerNeg

/-- Helper for Chapter03 Theorem 3.5.5: around an accumulation point inside the open domain,
`gradient f` is uniformly continuous on a small closed ball, and `f` has its canonical gradient
throughout that ball. -/
lemma gradientUniformContinuousOnClosedBall
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    {xStar : NegativeCurvaturePoint n}
    (hxStar_mem : xStar ∈ D) :
    ∃ r > 0,
      Metric.closedBall xStar r ⊆ D ∧
      UniformContinuousOn (gradient f) (Metric.closedBall xStar r) ∧
      ∀ y ∈ Metric.closedBall xStar r, HasGradientAt f (gradient f y) y := by
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hxStar_mem) with ⟨r, hr_pos, hr_ball⟩
  have hclosed_subset : Metric.closedBall xStar (r / 2) ⊆ D := by
    intro y hy
    apply hr_ball
    have hy_lt : dist y xStar < r := by
      calc
        dist y xStar ≤ r / 2 := hy
        _ < r := by linarith
    simpa [Metric.mem_ball, dist_comm] using hy_lt
  have hC1fderiv : ContDiffOn ℝ 1 (fderiv ℝ f) D := by
    -- Differentiate the `C²` objective once on the open domain.
    simpa using hC2.fderiv_of_isOpen hD_open (by norm_num)
  have hC1grad : ContDiffOn ℝ 1 (gradient f) D := by
    -- Rewrite the gradient through the Riesz map to inherit `C¹` regularity.
    change ContDiffOn ℝ 1
      (fun z ↦ (InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm (fderiv ℝ f z)) D
    have hsymmContDiff :
        ContDiff ℝ 1
          ((InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm :
            ((NegativeCurvaturePoint n →L[ℝ] ℝ) → NegativeCurvaturePoint n)) :=
      (LinearIsometryEquiv.contDiff
        ((InnerProductSpace.toDual ℝ (NegativeCurvaturePoint n)).symm))
    exact ContDiff.comp_contDiffOn hsymmContDiff hC1fderiv
  have hgrad_cont :
      ContinuousOn (gradient f) (Metric.closedBall xStar (r / 2)) := by
    exact hC1grad.continuousOn.mono fun _ hy ↦ hclosed_subset hy
  have hhasGradient :
      ∀ y ∈ Metric.closedBall xStar (r / 2), HasGradientAt f (gradient f y) y := by
    intro y hy
    have hy_mem : y ∈ D := hclosed_subset hy
    have hyDiff : DifferentiableAt ℝ f y :=
      (hC2.contDiffAt (hD_open.mem_nhds hy_mem)).differentiableAt (by norm_num)
    -- On the whole closed ball, the canonical gradient agrees with the derivative.
    exact hyDiff.hasGradientAt
  refine ⟨r / 2, by positivity, hclosed_subset, ?_, hhasGradient⟩
  exact (isCompact_closedBall xStar (r / 2)).uniformContinuousOn_of_continuous hgrad_cont

/-- Helper for Chapter03 Theorem 3.5.5: the source descent estimate yields a uniform acute-angle
bound between the search direction and the negative gradient at every nonstationary iterate. -/
lemma descentEstimate_uniformAngleGap
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x) :
    ∃ μ > 0, ∀ k : ℕ, gradient f (x k) ≠ 0 →
      InnerProductGeometry.angle (hAlgorithm.d k) (-(gradient f (x k))) ≤
        Real.pi / 2 - μ := by
  rcases hAlgorithm.descentEstimate with ⟨κ, hκ, hestimate⟩
  refine ⟨Real.pi / 2 - Real.arccos (1 / κ), ?_, ?_⟩
  · -- The reciprocal bound from the source descent estimate gives a positive angle gap.
    have harccos_lt :
        Real.arccos (1 / κ) < Real.pi / 2 :=
      (Real.arccos_lt_pi_div_two).2 (one_div_pos.mpr hκ)
    linarith
  · intro k hk
    let θ := InnerProductGeometry.angle (hAlgorithm.d k) (-(gradient f (x k)))
    have hestimate' :
        (1 / κ) * ‖gradient f (x k)‖ ≤
          -(inner ℝ (gradient f (x k)) (hAlgorithm.d k) / ‖hAlgorithm.d k‖) := by
      -- Re-express the source estimate in the cosine-identity normal form.
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hestimate k hk
    have hcos_times :
        (1 / κ) * ‖gradient f (x k)‖ ≤ ‖gradient f (x k)‖ * Real.cos θ := by
      simpa [θ] using
        (show
          (1 / κ) * ‖gradient f (x k)‖ ≤
            ‖gradient f (x k)‖ *
              Real.cos
                (InnerProductGeometry.angle (hAlgorithm.d k) (-(gradient f (x k)))) by
          simpa [
            gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm,
            θ
          ] using hestimate')
    have hcos_lower : 1 / κ ≤ Real.cos θ := by
      nlinarith [norm_pos_iff.mpr hk]
    have hθ_nonneg : 0 ≤ θ := by
      simpa [θ] using
        InnerProductGeometry.angle_nonneg (hAlgorithm.d k) (-(gradient f (x k)))
    have hθ_le_pi : θ ≤ Real.pi := by
      simpa [θ] using
        InnerProductGeometry.angle_le_pi (hAlgorithm.d k) (-(gradient f (x k)))
    have hθ_le_arccos : θ ≤ Real.arccos (1 / κ) := by
      -- Monotonicity of `arccos` converts the cosine lower bound into an angle upper bound.
      have harccos_cmp :
          Real.arccos (Real.cos θ) ≤ Real.arccos (1 / κ) :=
        Real.arccos_le_arccos hcos_lower
      simpa [Real.arccos_cos hθ_nonneg hθ_le_pi] using harccos_cmp
    simpa [θ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hθ_le_arccos

/-- Accumulation-point existence part of Chapter03 Theorem 3.5.5: assume the level set
`L(xBar) = {x ∈ D | f x ≤ f xBar}` is bounded and closed. If `ε = 0` is used in Algorithm 3.5.4,
the starting point satisfies `x₀ ∈ L(xBar)`, and the sequence `{x_k}` is generated by
Algorithm 3.5.4, then `{x_k}` has an accumulation point in `L(xBar)`. -/
theorem zeroToleranceNegativeCurvatureInfiniteRun_hasAccumulationPoint
    (hLevel_bounded : Bornology.IsBounded (negativeCurvatureLevelSet D f xBar))
    (hLevel_closed : IsClosed (negativeCurvatureLevelSet D f xBar))
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x)
    (hx₀ : x₀ ∈ negativeCurvatureLevelSet D f xBar) :
    ∃ xStar : NegativeCurvaturePoint n,
      xStar ∈ negativeCurvatureLevelSet D f xBar ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (nhds xStar) := by
  -- Convert the source closed-and-bounded hypotheses into compactness of the level set.
  have hCompact : IsCompact (negativeCurvatureLevelSet D f xBar) :=
    negativeCurvatureLevelSet_compact hLevel_bounded hLevel_closed
  have hmem :
      ∀ k : ℕ, x k ∈ negativeCurvatureLevelSet D f xBar :=
    iterates_mem_negativeCurvatureLevelSet hAlgorithm hx₀
  -- Sequential compactness supplies a convergent subsequence whose limit stays in the level set.
  exact hCompact.tendsto_subseq hmem

/-- Chapter03 Theorem 3.5.5: if `f : ℝ^n → ℝ` is twice continuously differentiable on the
open set `D`, the starting point satisfies `x₀ ∈ L(xBar)`, the level set `L(xBar)` is closed,
and `{x_k}` is generated by Algorithm 3.5.4 with `ε = 0`, then every accumulation point of
`{x_k}` is a stationary point of `f`. -/
theorem zeroToleranceNegativeCurvatureInfiniteRun_accumulationPoint_stationary
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevel_closed : IsClosed (negativeCurvatureLevelSet D f xBar))
    (hAlgorithm : IsZeroToleranceNegativeCurvatureDirectionMethodSequence f D x₀ x)
    (hx₀ : x₀ ∈ negativeCurvatureLevelSet D f xBar)
    {xStar : NegativeCurvaturePoint n} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (x ∘ φ) atTop (nhds xStar)) :
    IsStationaryPoint f xStar := by
  have hxStar_level :
      xStar ∈ negativeCurvatureLevelSet D f xBar :=
    accumulationPoint_mem_negativeCurvatureLevelSet hAlgorithm hx₀ hLevel_closed hTendsto
  have hxStar_mem : xStar ∈ D := hxStar_level.1
  have hDifferentiable :
      DifferentiableAt ℝ f xStar := by
    exact
      ((show ContDiffOn ℝ 1 f D from hC2.of_le (by norm_num)).contDiffAt
        (hD_open.mem_nhds hxStar_mem)).differentiableAt_one
  have hCont : ContinuousAt f xStar := by
    exact
      ((show ContDiffOn ℝ 0 f D from hC2.of_le (by norm_num)).contDiffAt
        (hD_open.mem_nhds hxStar_mem)).continuousAt
  rw [isStationaryPoint_iff]
  refine ⟨?_, hDifferentiable⟩
  by_contra hGradient_ne
  -- Route correction: instead of unfolding the whole algorithm at the limit point, reduce to a
  -- tail of the convergent subsequence on a small closed ball and force a uniform accepted drop.
  obtain ⟨μ, hμ_pos, hAngle⟩ := descentEstimate_uniformAngleGap hAlgorithm
  obtain ⟨ε, hε_pos, Ngrad, hGradLower⟩ :=
    subsequenceGradientNorm_eventually_ge_of_limitGradient_ne_zero
      hD_open hC2 hxStar_mem hTendsto hGradient_ne
  obtain ⟨r, hr_pos, hclosed_subset, hgrad_uc, hhasGradient⟩ :=
    gradientUniformContinuousOnClosedBall hD_open hC2 hxStar_mem
  have hhalf_pos : 0 < r / 2 := by
    positivity
  have hBallEventually :
      ∀ᶠ n in atTop, x (φ n) ∈ Metric.ball xStar (r / 2) := by
    exact hTendsto.eventually (Metric.ball_mem_nhds xStar hhalf_pos)
  rcases hBallEventually.exists_forall_of_atTop with ⟨Nball, hNball⟩
  let N : ℕ := max Ngrad Nball
  let xs : ℕ → NegativeCurvaturePoint n := fun k ↦ x (φ (k + N))
  let ds : ℕ → NegativeCurvaturePoint n := fun k ↦ hAlgorithm.d (φ (k + N))
  let ηBall : ℝ := (ε * Real.sin μ) / 2
  have hηBall_pos : 0 < ηBall := by
    have hsin_pos : 0 < Real.sin μ :=
      sin_pos_of_uniformAngleGap f xs ds μ hμ_pos
        (by
          intro k hk
          simpa [xs, ds] using hAngle (φ (k + N)) hk)
        (by
          intro k
          have hkNgrad : Ngrad ≤ k + N := by
            exact le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ _)
          have hbound := hGradLower (k + N) hkNgrad
          exact norm_pos_iff.mp (lt_of_lt_of_le hε_pos hbound))
    positivity
  rcases (Metric.uniformContinuousOn_iff_le.mp hgrad_uc) ηBall hηBall_pos with
    ⟨αuc, hαuc_pos, hαuc_spec⟩
  let αbar : ℝ := min (r / 2) αuc
  have hαbar_pos : 0 < αbar := by
    dsimp [αbar]
    exact lt_min hhalf_pos hαuc_pos
  have hαbar_le_half : αbar ≤ r / 2 := by
    dsimp [αbar]
    exact min_le_left _ _
  have hαbar_le_αuc : αbar ≤ αuc := by
    dsimp [αbar]
    exact min_le_right _ _
  have hxsGrad_ne : ∀ k : ℕ, gradient f (xs k) ≠ 0 := by
    intro k
    have hkNgrad : Ngrad ≤ k + N := by
      exact le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ _)
    have hbound := hGradLower (k + N) hkNgrad
    exact norm_pos_iff.mp (lt_of_lt_of_le hε_pos hbound)
  have hDescentTail :
      ∀ k : ℕ, gradient f (xs k) ≠ 0 → IsDescentDirectionAt f (xs k) (ds k) := by
    intro k hk
    simpa [xs, ds] using
      iterateDirection_isDescentDirectionAt_of_gradient_ne_zero
        hAlgorithm (φ (k + N)) hk
  have hAngleTail :
      ∀ k : ℕ, gradient f (xs k) ≠ 0 →
        InnerProductGeometry.angle (ds k) (-(gradient f (xs k))) ≤ Real.pi / 2 - μ := by
    intro k hk
    simpa [xs, ds] using hAngle (φ (k + N)) hk
  have hαbar_spec :
      ∀ ⦃y z : NegativeCurvaturePoint n⦄,
        y ∈ Metric.closedBall xStar r →
        z ∈ Metric.closedBall xStar r →
        dist y z ≤ αbar →
        ‖gradient f y - gradient f z‖ ≤ ηBall := by
    intro y z hy hz hdist
    exact hαuc_spec y hy z hz (le_trans hdist hαbar_le_αuc)
  have hxsNear :
      ∀ k : ℕ, xs k ∈ Metric.closedBall xStar (r / 2) := by
    intro k
    have hkNball : Nball ≤ k + N := by
      exact le_trans (Nat.le_max_right _ _) (Nat.le_add_left _ _)
    have hkBall : x (φ (k + N)) ∈ Metric.ball xStar (r / 2) :=
      hNball (k + N) hkNball
    exact Metric.mem_closedBall.2 (le_of_lt (by simpa [Metric.mem_ball, dist_comm] using hkBall))
  have htrialDrop :
      ∀ k : ℕ,
        f (xs k + αbar • ((‖ds k‖)⁻¹ • ds k)) ≤
          f (xs k) - αbar * (ε * Real.sin μ) / 2 := by
    intro k
    have hstep_mem :
        ∀ s ∈ Set.Icc (0 : ℝ) αbar,
          xs k + s • ((‖ds k‖)⁻¹ • ds k) ∈ Metric.closedBall xStar r := by
      intro s hs
      have hdesc : IsDescentDirectionAt f (xs k) (ds k) :=
        hDescentTail k (hxsGrad_ne k)
      have hds_ne : ds k ≠ 0 := hdesc.direction_ne
      have hu_norm : ‖((‖ds k‖)⁻¹ • ds k)‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hds_ne))]
        field_simp [norm_ne_zero_iff.mpr hds_ne]
      have hbase_dist :
          dist (xs k) xStar ≤ r / 2 :=
        hxsNear k
      refine Metric.mem_closedBall.2 ?_
      calc
        dist (xs k + s • ((‖ds k‖)⁻¹ • ds k)) xStar ≤
            dist (xs k + s • ((‖ds k‖)⁻¹ • ds k)) (xs k) + dist (xs k) xStar := by
              simpa [dist_comm] using
                dist_triangle_right (xs k + s • ((‖ds k‖)⁻¹ • ds k)) xStar (xs k)
        _ = ‖s • ((‖ds k‖)⁻¹ • ds k)‖ + dist (xs k) xStar := by
              simp [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm]
        _ = |s| * ‖((‖ds k‖)⁻¹ • ds k)‖ + dist (xs k) xStar := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = s + dist (xs k) xStar := by
              rw [hu_norm, abs_of_nonneg hs.1]
              ring
        _ ≤ αbar + r / 2 := by
              exact add_le_add hs.2 hbase_dist
        _ ≤ r / 2 + r / 2 := by
              exact add_le_add hαbar_le_half le_rfl
        _ = r := by ring
    have hdrop :=
      compactLevelSet_normalizedTrialDrop
        f (Metric.closedBall xStar r) xs ds μ αbar ε hDescentTail hhasGradient hμ_pos
        hAngleTail hxsGrad_ne hαbar_pos hαbar_spec
        (by
          have hbound := hGradLower (k + N)
            (le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ _))
          simpa [xs] using hbound)
        hstep_mem
    exact hdrop
  let η : ℝ := αbar * (ε * Real.sin μ) / 2
  have hη_pos : 0 < η := by
    have hprod_pos : 0 < αbar * ((ε * Real.sin μ) / 2) :=
      mul_pos hαbar_pos hηBall_pos
    simpa [η, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hprod_pos
  have hAcceptedDrop :
      ∀ k : ℕ, f (x (φ (k + N) + 1)) ≤ f (xs k) - η := by
    intro k
    have htrial_nonneg : 0 ≤ αbar / ‖ds k‖ := by
      exact div_nonneg hαbar_pos.le (norm_nonneg _)
    have hopt :
        lineSearchObjective f (xs k) (ds k) (hAlgorithm.α (φ (k + N))) ≤
          lineSearchObjective f (xs k) (ds k) (αbar / ‖ds k‖) :=
      (hAlgorithm.exactLineSearch (φ (k + N))).optimal htrial_nonneg
    have haccepted :
        f (x (φ (k + N) + 1)) ≤
          f (xs k + αbar • ((‖ds k‖)⁻¹ • ds k)) := by
      simpa [xs, ds, lineSearchObjective_apply, hAlgorithm.update (φ (k + N)),
        div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hopt
    have htrial :
        f (xs k + αbar • ((‖ds k‖)⁻¹ • ds k)) ≤ f (xs k) - η := by
      simpa [η] using htrialDrop k
    exact haccepted.trans htrial
  have hValueTendsto :
      Tendsto (fun n ↦ f (x (φ n))) atTop (nhds (f xStar)) :=
    hCont.tendsto.comp hTendsto
  have hValueTailTendsto :
      Tendsto (fun k ↦ f (xs k)) atTop (nhds (f xStar)) := by
    simpa [xs, Function.comp_def] using
      hValueTendsto.comp (tendsto_add_atTop_nat N)
  have hShiftedTendsto :
      Tendsto (fun n ↦ f (x (φ n + 1))) atTop (nhds (f xStar)) :=
    tendsto_objective_shiftedSubsequence_of_accumulationPoint hAlgorithm hφ hCont hTendsto
  have hShiftedTailTendsto :
      Tendsto (fun k ↦ f (x (φ (k + N) + 1))) atTop (nhds (f xStar)) := by
    simpa [Function.comp_def] using hShiftedTendsto.comp (tendsto_add_atTop_nat N)
  have hRightTendsto :
      Tendsto (fun k ↦ f (xs k) - η) atTop (nhds (f xStar - η)) := by
    exact hValueTailTendsto.sub tendsto_const_nhds
  have hStrictEventually :
      ∀ᶠ k in atTop, f (xs k) - η < f (x (φ (k + N) + 1)) := by
    have hSep : f xStar - η < f xStar := by
      linarith
    exact hRightTendsto.eventually_lt hShiftedTailTendsto hSep
  have hContradiction : ∀ᶠ k in (atTop : Filter ℕ), False := by
    filter_upwards [hStrictEventually] with k hkStrict
    exact not_lt_of_ge (hAcceptedDrop k) hkStrict
  rcases hContradiction.exists_forall_of_atTop with ⟨k0, hk0⟩
  exact hk0 k0 le_rfl

end NegativeCurvatureDirectionMethodInfiniteRun
