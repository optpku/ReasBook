/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Remark_25_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.ContinuousLocalMartingaleIto
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open Laplacian InnerProductSpace
open scoped BigOperators Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {d : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "Process" => NNReal → Ω → ℝ
local notation "VectorProcess" => NNReal → Ω → State
local notation "MatrixProcess" => NNReal → Ω → Fin d → Fin d → ℝ
local notation "ProcessVector" => Fin d → Process
local notation "dyadicPartitionSequence" => Definition2158.dyadicPartitionSequence

variable {ℱ : TimeFiltration}

/-- Helper for Theorem 25.33: scaling both continuous paths scales each dyadic quadratic-
covariation sum by the product of the scalars. -/
private lemma dyadicQuadraticCovariationSum_smulPath_eq
    (a b : ℝ) (F G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    dyadic_quadratic_covariation_sum (a • F) (b • G) T n =
      (a * b) * dyadic_quadratic_covariation_sum F G T n := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo P n k T) - F (P n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo P n k T) - G (P n k)
  have hscaled :
      Finset.sum (Finset.range N) (fun k ↦
        (((a • F) (partitionNextPointUpTo P n k T) - (a • F) (P n k)) *
          ((b • G) (partitionNextPointUpTo P n k T) - (b • G) (P n k)))) =
        Finset.sum (Finset.range N) (fun k ↦ (a * ΔF k) * (b * ΔG k)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [Pi.smul_apply, ΔF, ΔG, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm,
      mul_comm]
  calc
    dyadic_quadratic_covariation_sum (a • F) (b • G) T n
        = Finset.sum (Finset.range N) (fun k ↦
            (((a • F) (partitionNextPointUpTo P n k T) - (a • F) (P n k)) *
              ((b • G) (partitionNextPointUpTo P n k T) - (b • G) (P n k)))) := by
          rw [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum]
    _ = Finset.sum (Finset.range N) (fun k ↦ (a * ΔF k) * (b * ΔG k)) := hscaled
    _ = Finset.sum (Finset.range N) (fun k ↦ (a * b) * (ΔF k * ΔG k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (a * b) * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) := by
          rw [Finset.mul_sum]
    _ = (a * b) * dyadic_quadratic_covariation_sum F G T n := by
          dsimp [N, ΔF, ΔG, P]
          rw [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum]

/-- Helper for Theorem 25.33: scaling both paths scales the pathwise quadratic-covariation
witness by the product of the scalars. -/
private lemma hasQuadraticCovariationAlong_smulPath
    {F G : C(NNReal, ℝ)} {covFG : NNReal → ℝ}
    (hFG : HasQuadraticCovariationAlong F G covFG) (a b : ℝ) :
    HasQuadraticCovariationAlong (a • F) (b • G) (fun T ↦ (a * b) * covFG T) := by
  intro T
  have hsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the scaled mixed dyadic sum and then move the scalar factor outside
  -- the limit.
  convert hsum.const_mul (a * b) using 1
  ext n
  simpa [dyadic_quadratic_covariation_sum] using
    dyadicQuadraticCovariationSum_smulPath_eq a b F G T n

/-- Helper for Theorem 25.33: polarization turns square-variation witnesses of `F + G` and
`F - G` into a pathwise quadratic-covariation witness of `F` and `G`. -/
private theorem hasQuadraticCovariationAlong_polarizationPath
    {F G : C(NNReal, ℝ)} {brAdd brSub : NNReal → ℝ}
    (hAdd : HasSquareVariationAlong (F + G) brAdd)
    (hSub : HasSquareVariationAlong (F - G) brSub) :
    HasQuadraticCovariationAlong F G ((1 / 4 : ℝ) • (brAdd - brSub)) := by
  intro T
  have hpolarized :
      Tendsto
        (fun n ↦
          ((dyadic_p_variation_sum 2 (F + G) T n) -
            (dyadic_p_variation_sum 2 (F - G) T n)) / 4)
        atTop
        (nhds (((1 / 4 : ℝ) • (brAdd - brSub)) T)) := by
    -- Proof comment: the mixed dyadic sums are the polarized difference of the two square
    -- variation sums, so their limit is the same polarized difference of the witness paths.
    simpa [Pi.smul_apply, Pi.sub_apply, div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((HasSquareVariationAlong.tendsto_partition_sum hAdd T).sub
        (HasSquareVariationAlong.tendsto_partition_sum hSub T)).mul_const (1 / 4 : ℝ)
  convert hpolarized using 1
  ext n
  simpa [dyadic_quadratic_covariation_sum, dyadic_p_variation_sum] using
    (partitionQuadraticCovariationSum_eq_polarization
      Definition2158.dyadicPartitionSequence F G T n)

/-- Helper for Theorem 25.33: square-variation witnesses for `F`, `G`, and their quadratic
covariation combine into the canonical square-variation witness for `F + G`. -/
private lemma dyadicSquareVariationSum_add_eq
    (F G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    dyadic_p_variation_sum 2 (F + G) T n =
      dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
        dyadic_p_variation_sum 2 G T n := by
  let N := partitionBoundIndex dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo dyadicPartitionSequence n k T) - F (dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo dyadicPartitionSequence n k T) - G (dyadicPartitionSequence n k)
  -- Proof comment: expand the square of the dyadic increment of `F + G` and regroup the finite
  -- sum into its pure and mixed components.
  rw [dyadic_p_variation_sum, partitionPVariationSum]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          Real.rpow
            (|((F + G) (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
                ((F + G) (dyadicPartitionSequence n k))|)
            2) =
        Finset.sum (Finset.range N) (fun k ↦ (ΔF k + ΔG k) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [← Real.rpow_natCast]
          have hadd :
              (F (partitionNextPointUpTo dyadicPartitionSequence n k T) +
                  G (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
                (F (dyadicPartitionSequence n k) + G (dyadicPartitionSequence n k)) =
                ΔF k + ΔG k := by
            dsimp [ΔF, ΔG]
            ring
          rw [ContinuousMap.add_apply, ContinuousMap.add_apply, hadd]
          simp [sq_abs]
    _ = Finset.sum (Finset.range N) (fun k ↦ (ΔF k) ^ 2 + 2 * (ΔF k * ΔG k) + (ΔG k) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (Finset.sum (Finset.range N) fun k ↦ (ΔF k) ^ 2) +
          2 * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
          dyadic_p_variation_sum 2 G T n := by
          simp [N, ΔF, ΔG, dyadic_p_variation_sum, dyadic_quadratic_covariation_sum,
            partitionPVariationSum, partitionQuadraticCovariationSum, sq_abs]

/-- Helper for Theorem 25.33: square-variation witnesses for `F`, `G`, and their quadratic
covariation combine into the canonical square-variation witness for `F + G`. -/
private lemma hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong
    {F G : C(NNReal, ℝ)} {brF brG covFG : NNReal → ℝ}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG) :
    HasSquareVariationAlong (F + G) (fun T ↦ brF T + 2 * covFG T + brG T) := by
  intro T
  have hFsum := HasSquareVariationAlong.tendsto_partition_sum hF T
  have hGsum := HasSquareVariationAlong.tendsto_partition_sum hG T
  have hFGsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the dyadic square sum of `F + G` into the three convergent pieces and
  -- pass to the limit termwise.
  have hsum :
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
            dyadic_p_variation_sum 2 G T n)
        atTop
        (nhds (brF T + 2 * covFG T + brG T)) := by
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hFsum.add ((hFGsum.const_mul 2).add hGsum)
  convert hsum using 1
  ext n
  simpa [dyadic_p_variation_sum] using dyadicSquareVariationSum_add_eq F G T n

/-- Helper for Theorem 25.33: the dyadic mixed quadratic-covariation sum is bounded by the
geometric mean of the two dyadic square-variation sums. -/
private lemma abs_partitionQuadraticCovariationSum_le_sqrt_mul
    (F G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    |partitionQuadraticCovariationSum dyadicPartitionSequence F G T n| ≤
      Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 F T n) *
        Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 G T n) := by
  let s := Finset.range (partitionBoundIndex dyadicPartitionSequence n T)
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo dyadicPartitionSequence n k T) - F (dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo dyadicPartitionSequence n k T) - G (dyadicPartitionSequence n k)
  have hAbs :
      |partitionQuadraticCovariationSum dyadicPartitionSequence F G T n| ≤
        Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) := by
    -- Proof comment: bound the absolute value of the mixed finite sum by the sum of absolute
    -- mixed increments.
    simpa [partitionQuadraticCovariationSum, s, ΔF, ΔG, abs_mul] using
      (Finset.abs_sum_le_sum_abs (s := s) (f := fun k ↦ ΔF k * ΔG k))
  have hCS :
      Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) ≤
        Real.sqrt (Finset.sum s (fun k ↦ |ΔF k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |ΔG k| ^ 2)) := by
    -- Proof comment: this is the finite-dimensional Cauchy-Schwarz inequality.
    exact Real.sum_mul_le_sqrt_mul_sqrt s (fun k ↦ |ΔF k|) (fun k ↦ |ΔG k|)
  calc
    |partitionQuadraticCovariationSum dyadicPartitionSequence F G T n|
        ≤ Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) := hAbs
    _ ≤ Real.sqrt (Finset.sum s (fun k ↦ |ΔF k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |ΔG k| ^ 2)) := hCS
    _ =
        Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 F T n) *
          Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 G T n) := by
            simp [partitionPVariationSum, s, ΔF, ΔG]

/-- Helper for Theorem 25.33: if the right path has zero square variation, then the mixed
quadratic covariation with any square-variation path vanishes. -/
private lemma hasQuadraticCovariationAlong_zero_of_rightZeroSquareVariation
    {F G : C(NNReal, ℝ)} {VF : NNReal → ℝ}
    (hVF : HasSquareVariationAlong F VF)
    (hG : HasSquareVariationAlong G 0) :
    HasQuadraticCovariationAlong F G 0 := by
  intro T
  have hFsqrt :
      Tendsto (fun n ↦ Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 F T n))
        atTop
        (nhds (Real.sqrt (VF T))) := by
    -- Proof comment: pass the square-variation limit of `F` through continuity of `sqrt`.
    exact
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hVF T)
  have hGsqrt :
      Tendsto (fun n ↦ Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: the right square-variation path is identically zero, so the square-root
    -- approximants also converge to `0`.
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hG T))
  have hBound :
      Tendsto
        (fun n ↦
          Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 F T n) *
            Real.sqrt (partitionPVariationSum dyadicPartitionSequence 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: the geometric-mean bound tends to `0` because the right factor does.
    simpa [Real.sqrt_zero] using hFsqrt.mul hGsqrt
  exact
    (tendsto_zero_iff_norm_tendsto_zero).2 <| by
      simpa [Real.norm_eq_abs] using
        (squeeze_zero
          (fun n ↦ abs_nonneg _)
          (fun n ↦ abs_partitionQuadraticCovariationSum_le_sqrt_mul F G T n)
          hBound)

/-- Helper for the multidimensional Itô formula: a continuous quadratic-covariation process of continuous local
martingales `M` and `N` is a continuous adapted process `A`, starting at `0` and with almost
surely locally finite variation, such that `MN - A` is a continuous local martingale. -/
structure IsContinuousQuadraticCovariationProcess
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (M N A : NNReal → Ω → ℝ) : Prop where
  zero : A 0 = 0
  adapted : Adapted ℱ A
  continuous : ∀ ω : Ω, Continuous fun t : NNReal ↦ A t ω
  locally_finite_variation :
    ∀ᵐ ω ∂μ,
      LocallyBoundedVariationOn
        (⟨fun t ↦ A t ω, continuous ω⟩ : C(NNReal, ℝ)) Set.univ
  local_martingale_mul_sub :
    IsLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω)

/-- The canonical coordinate martingale part
`Mᵏ_t = Y_t^k - ∫_0^t b_s^k ds`
of the generalized diffusion `Y`. -/
def generalizedDiffusionCoordinateMartingalePart
    (b Y : VectorProcess) (k : Fin d) : Process :=
  fun t ω ↦ Y t ω k - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k

/-- Helper for the multidimensional Itô formula: a point on the `k`-th coordinate line through `x` really has
`k`-th coordinate `t`. -/
lemma point_on_coordinateLine_apply
    (x : State) (k : Fin d) (t : ℝ) :
    (x + EuclideanSpace.single k (t - x k)) k = t := by
  -- Evaluating the coordinate-line point at `k` collapses the inserted displacement.
  simp

/-- Helper for the multidimensional Itô formula: moving first to the `t`-point on the `k`-th coordinate line and then
moving again along the same coordinate is the same as moving directly to the final point. -/
lemma coordinateLine_compose_self
    (x : State) (k : Fin d) (t u : ℝ) :
    x + EuclideanSpace.single k (t - x k) +
        EuclideanSpace.single k (u - (x + EuclideanSpace.single k (t - x k)) k) =
      x + EuclideanSpace.single k (u - x k) := by
  -- Compare coordinates: only the `k`-th coordinate changes, and there the increments add.
  ext j
  by_cases h : j = k
  · subst h
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, point_on_coordinateLine_apply]
  · simp [h]

-- Proof sketch: identify the canonical Euclidean-space Laplacian with the sum of the second
-- derivatives along the standard coordinate basis vectors, and then rewrite those basis
-- derivatives using the coordinate partial derivatives from Theorem 25.30.
/-- For the coordinate model `State = ℝ^d`, the canonical Euclidean Laplacian is the sum of the
diagonal second coordinate derivatives. This is the coordinate bridge for the textbook formula,
while the main Brownian Itô statement below uses the canonical operator `Δ`. -/
theorem laplacian_eq_sum_secondPartialDeriv
    (F : State → ℝ) (hF : ContDiff ℝ 2 F) (x : State) :
    Δ F x =
      ∑ k : Fin d, (∂²[k, k] F) x := by
  -- Route correction: this helper is only valid under a genuine `C²` hypothesis, because we
  -- identify coordinate derivatives with the Fréchet Hessian.
  have hDiag :
      ∀ k : Fin d,
        (∂²[k, k] F) x =
          iteratedFDeriv ℝ 2 F x ![EuclideanSpace.single k 1, EuclideanSpace.single k 1] := by
    intro k
    let g : ℝ → ℝ := fun t ↦ F (x + EuclideanSpace.single k (t - x k))
    have hpartialLine :
        ∀ t : ℝ, (∂[k] F) (x + EuclideanSpace.single k (t - x k)) = deriv g t := by
      intro t
      -- Rewrite the inner coordinate line back to the original one-parameter curve `g`.
      rw [partialDeriv_def]
      have hgEq :
          (fun u ↦ F (x + EuclideanSpace.single k (t - x k) + EuclideanSpace.single k (u - t))) =
            g := by
        funext u
        have hcoord :
            x + EuclideanSpace.single k (t - x k) + EuclideanSpace.single k (u - t) =
              x + EuclideanSpace.single k (u - x k) := by
          simpa [point_on_coordinateLine_apply] using coordinateLine_compose_self x k t u
        exact congrArg F hcoord
      simpa using congrArg (fun h : ℝ → ℝ ↦ h t) (congrArg deriv hgEq)
    have hsecond :
        (∂²[k, k] F) x = iteratedDeriv 2 g (x k) := by
      -- The diagonal second partial is the second one-variable derivative of `g`.
      rw [secondPartialDeriv_def, iteratedDeriv_succ, iteratedDeriv_one]
      congr 1
      funext t
      exact hpartialLine t
    let g0 : ℝ → ℝ := fun s ↦ F (x + EuclideanSpace.single k s)
    have hg : g = fun t ↦ g0 (t - x k) := by
      -- `g` is just the translated coordinate-line curve `g0`.
      funext t
      simp [g, g0]
    have hshift : iteratedDeriv 2 g (x k) = iteratedDeriv 2 g0 0 := by
      -- Shift the basepoint on the one-dimensional curve back to the origin.
      rw [hg]
      simpa using
        congrArg
          (fun h : ℝ → ℝ ↦ h (x k))
          (iteratedDeriv_comp_sub_const 2 g0 (x k))
    let L : ℝ →L[ℝ] State :=
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (EuclideanSpace.single k 1)
    have hg0_comp : g0 = (fun z : State ↦ F (x + z)) ∘ L := by
      -- The axis curve `g0` is the shifted function restricted along the linear axis map `L`.
      funext s
      apply congrArg F
      ext j
      by_cases h : j = k
      · subst h
        simp [L]
      · simp [L, h]
    have hShiftF : ContDiff ℝ 2 (fun z : State ↦ F (x + z)) := by
      -- Translating the input preserves the `C²` regularity needed by the Hessian API.
      simpa using hF.comp ((contDiff_const.add contDiff_id).of_le le_top)
    have hcomp :
        iteratedFDeriv ℝ 2 g0 0 =
          (iteratedFDeriv ℝ 2 (fun z : State ↦ F (x + z)) 0).compContinuousLinearMap
            (fun _ ↦ L) := by
      -- Compose the shifted Hessian with the linear axis map.
      rw [hg0_comp]
      simpa using
        (L.iteratedFDeriv_comp_right hShiftF (0 : ℝ) le_rfl)
    let m : Fin 2 → State := fun i ↦ L (![1, 1] i)
    have hshiftFDeriv :
        iteratedFDeriv ℝ 2 (fun z : State ↦ F (x + z)) 0 = iteratedFDeriv ℝ 2 F x := by
      -- Evaluating the shifted Hessian at `0` recovers the Hessian of `F` at `x`.
      simpa using (iteratedFDeriv_comp_add_left 2 x (0 : State) : _)
    have htranslate :
        (iteratedFDeriv ℝ 2 (fun z : State ↦ F (x + z)) 0) m =
          (iteratedFDeriv ℝ 2 F x) m := by
      exact congrArg (fun A ↦ A m) hshiftFDeriv
    have hm : m = ![EuclideanSpace.single k 1, EuclideanSpace.single k 1] := by
      -- Along both slots, the linear axis map sends `1` to the `k`-th basis vector.
      funext i
      fin_cases i <;> simp [m, L]
    have hvec : (fun _ : Fin 2 ↦ (1 : ℝ)) = ![(1 : ℝ), 1] := by
      funext i
      fin_cases i <;> rfl
    calc
      (∂²[k, k] F) x = iteratedDeriv 2 g (x k) := hsecond
      _ = iteratedDeriv 2 g0 0 := hshift
      _ = iteratedFDeriv ℝ 2 g0 0 (fun _ : Fin 2 ↦ (1 : ℝ)) := by
        rw [iteratedDeriv_eq_iteratedFDeriv]
      _ = iteratedFDeriv ℝ 2 g0 0 ![(1 : ℝ), 1] := by
        rw [hvec]
      _ =
          (iteratedFDeriv ℝ 2 (fun z : State ↦ F (x + z)) 0).compContinuousLinearMap
            (fun _ ↦ L) ![(1 : ℝ), 1] := by
        rw [hcomp]
      _ = (iteratedFDeriv ℝ 2 (fun z : State ↦ F (x + z)) 0) m := by
        rfl
      _ = (iteratedFDeriv ℝ 2 F x) m := htranslate
      _ = iteratedFDeriv ℝ 2 F x ![EuclideanSpace.single k 1, EuclideanSpace.single k 1] := by
        rw [hm]
  have hLap :=
      congrArg
        (fun h : State → ℝ ↦ h x)
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
          F
          (EuclideanSpace.basisFun (Fin d) ℝ))
  -- Expand the canonical Laplacian in the coordinate orthonormal basis and rewrite each diagonal
  -- Hessian entry by the coordinate second derivative proved above.
  calc
    Δ F x =
        ∑ k : Fin d,
          iteratedFDeriv ℝ 2 F x
            ![(EuclideanSpace.basisFun (Fin d) ℝ) k, (EuclideanSpace.basisFun (Fin d) ℝ) k] := hLap
    _ = ∑ k : Fin d, (∂²[k, k] F) x := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [EuclideanSpace.basisFun_apply, hDiag k]

/-- Helper for the multidimensional Itô formula: for `F ∈ C²(ℝᵈ)`, each first coordinate derivative `∂[i] F` is
continuous. -/
theorem continuous_partialDeriv
    (F : State → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin d) :
    Continuous (∂[i] F) := by
  -- The Fréchet derivative varies continuously for a `C²` function, and we evaluate it at a fixed
  -- basis vector.
  have happly :
      Continuous fun x : State ↦ (fderiv ℝ F x) (EuclideanSpace.single i (1 : ℝ)) := by
    simpa using
      (hF.continuous_fderiv_apply (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).comp
        (continuous_id.prodMk continuous_const)
  -- Rewriting through `partialDeriv_eq_fderiv_apply` turns the regularity statement into the
  -- desired continuity of `∂[i] F`.
  simpa [partialDeriv_eq_fderiv_apply F (hF.differentiable (by norm_num)) i] using
    happly

/-- Helper for the multidimensional Itô formula: composing `∂[i] F` with a continuous `State`-valued path preserves
continuity. -/
theorem continuous_partialDeriv_comp
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {X : NNReal → State} (hX : Continuous X) (i : Fin d) :
    Continuous fun t : NNReal ↦ (∂[i] F) (X t) := by
  -- This is the direct composition of the coordinate-derivative continuity with the path.
  exact (continuous_partialDeriv F hF i).comp hX

/-- Helper for the multidimensional Itô formula: a `State`-valued path is continuous once all of its coordinate paths
are continuous. -/
theorem continuous_state_of_coordinates
    {X : NNReal → State}
    (hX : ∀ i : Fin d, Continuous fun t : NNReal ↦ X t i) :
    Continuous X := by
  -- First view the path in coordinates and prove continuity componentwise.
  have hcoords : Continuous fun t : NNReal ↦ (fun i : Fin d ↦ X t i) := by
    exact continuous_pi hX
  -- Then transport that continuity back across the canonical Euclidean-space equivalence.
  simpa using (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp hcoords

/-- Helper for the multidimensional Itô formula: a standard Brownian vector has almost surely continuous `State`-valued
sample paths. -/
theorem ae_continuous_standardBrownianVectorPath
    {W : VectorProcess} (hW : IsStandardBrownianMotionVector μ W) :
    ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ W t ω := by
  have hcoords :
      ∀ᵐ ω ∂μ, ∀ i : Fin d, Continuous fun t : NNReal ↦ W t ω i := by
    -- Each coordinate is a one-dimensional Brownian motion, hence has an almost surely continuous
    -- sample path.
    exact ae_all_iff.2 fun i ↦ by
      simpa [processPath] using (hW.isBrownianMotion i).continuous_paths
  -- Reassemble the coordinatewise continuity into continuity of the vector-valued path.
  filter_upwards [hcoords] with ω hω
  exact continuous_state_of_coordinates hω

/-- Helper for the multidimensional Itô formula: if the dyadic quadratic variation of a continuous path converges to
`cov`, then `cov` is also a dyadic quadratic-covariation realization of the path with itself. -/
theorem hasQuadraticCovariationAlong_self_of_tendsto_partitionQuadraticVariation
    {X : C(NNReal, ℝ)} {cov : NNReal → ℝ}
    (hcov :
      ∀ T : NNReal,
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ))
              X
              dyadicPartitionSequence
              T
              n)
          atTop
          (𝓝 (cov T))) :
    HasQuadraticCovariationAlong X X cov := by
  intro T
  -- On the diagonal, the weighted quadratic-variation sums are exactly the mixed dyadic sums.
  simpa [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum,
    weightedPartitionQuadraticVariationApproximationUpTo_def, one_mul, pow_two] using hcov T
/-- Helper for the multidimensional Itô formula: a self-quadratic-covariation witness is automatically a square
variation witness, because the dyadic mixed sums reduce to the dyadic square sums on the diagonal.
-/
theorem hasSquareVariationAlong_of_self_quadraticCovariation
    {X : C(NNReal, ℝ)} {cov : NNReal → ℝ}
    (hcov : HasQuadraticCovariationAlong X X cov) :
    HasSquareVariationAlong X cov := by
  -- Theorem 25.30 already packages the diagonal identification of quadratic and square variation.
  exact hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self hcov
/-- Helper for the multidimensional Itô formula: a continuous quadratic-covariation process upgrades to an almost-sure
pathwise quadratic-covariation witness by polarizing the canonical square brackets of `M + N` and
`M - N`. -/
theorem ae_hasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcess
    {M N A : Process}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ M N A) :
    ∀ᵐ ω ∂μ,
      HasQuadraticCovariationAlong
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ N t ω, hN.continuous ω⟩ : C(NNReal, ℝ))
        (fun t ↦ A t ω) := by
  have hAdd : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω + N t ω) := by
    -- Proof comment: the sum of two continuous local martingales is again a continuous local
    -- martingale.
    refine ⟨hM.local_martingale.add hN.local_martingale, ?_⟩
    intro ω
    exact (hM.continuous ω).add (hN.continuous ω)
  have hSub : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω - N t ω) := by
    -- Proof comment: the same closure property handles the difference process.
    refine ⟨hM.local_martingale.sub hN.local_martingale, ?_⟩
    intro ω
    exact (hM.continuous ω).sub (hN.continuous ω)
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hAdd with
    ⟨Aadd, hAadd, _⟩
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hSub with
    ⟨Asub, hAsub, _⟩
  let Apolar : Process := fun t ω ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω)
  have hApolar :
      IsContinuousQuadraticCovariationProcess ℱ μ M N Apolar :=
    isContinuousQuadraticCovariationProcess_polarization hAadd hAsub
  rcases existsUnique_continuousQuadraticCovariationProcess hM hN with ⟨B, hB, huniq⟩
  have hApolarEq : AreIndistinguishable μ Apolar A := by
    -- Proof comment: uniqueness of the continuous covariation process identifies the polarized
    -- canonical witness with the supplied witness `A`.
    exact areIndistinguishable_trans
      (areIndistinguishable_symm (huniq Apolar hApolar))
      (huniq A hA)
  have hAddAE :
      ∀ᵐ ω ∂μ,
        HasSquareVariationAlong
          (⟨fun t ↦ M t ω + N t ω, (hM.continuous ω).add (hN.continuous ω)⟩ : C(NNReal, ℝ))
          (fun t ↦ Aadd t ω) := by
    simpa using
      ae_hasSquareVariationAlong_continuousSquareVariationProcess hAdd hAadd
  have hSubAE :
      ∀ᵐ ω ∂μ,
        HasSquareVariationAlong
          (⟨fun t ↦ M t ω - N t ω, (hM.continuous ω).sub (hN.continuous ω)⟩ : C(NNReal, ℝ))
          (fun t ↦ Asub t ω) := by
    simpa using
      ae_hasSquareVariationAlong_continuousSquareVariationProcess hSub hAsub
  have hEqAE : ∀ᵐ ω ∂μ, ∀ t : NNReal, Apolar t ω = A t ω := by
    rcases hApolarEq with ⟨S, hSmeas, hSzero, hSsub⟩
    rw [ae_iff]
    refine ⟨S, hSmeas, hSzero, ?_⟩
    intro ω hω t
    by_contra hneq
    exact hω (hSsub t hneq)
  filter_upwards [hAddAE, hSubAE, hEqAE] with ω hAddω hSubω hEqω
  have hPolarω :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ N t ω, hN.continuous ω⟩ : C(NNReal, ℝ))
        (fun t ↦ Apolar t ω) := by
    -- Proof comment: on each good sample path, the dyadic bracket is the polarization of the
    -- plus/minus square-variation limits.
    simpa [Apolar, Pi.smul_apply, Pi.sub_apply] using
      (hasQuadraticCovariationAlong_polarizationPath hAddω hSubω)
  intro T
  simpa [hEqω T] using hPolarω T
/-- Helper for the multidimensional Itô formula: the deterministic drift density obtained by taking the coordinate
combination `c₁ b^k + c₂ b^l` on the positive half-line and extending it by `0` to negative
times. -/
def coordinateDriftCombinationDensity
    (b : VectorProcess) (ω : Ω) (k l : Fin d) (c₁ c₂ : ℝ) :
    ℝ → ℝ :=
  fun s ↦
    if hs : 0 ≤ s then
      c₁ * b ⟨s, hs⟩ ω k + c₂ * b ⟨s, hs⟩ ω l
    else
      0

/-- Helper for the multidimensional Itô formula: on nonnegative times, the drift-combination density is the expected
coordinate linear combination `c₁ b^k + c₂ b^l`. -/
theorem coordinateDriftCombinationDensity_of_nonneg
    {b : VectorProcess} (ω : Ω) (k l : Fin d) (c₁ c₂ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    coordinateDriftCombinationDensity b ω k l c₁ c₂ s =
      c₁ * b ⟨s, hs⟩ ω k + c₂ * b ⟨s, hs⟩ ω l := by
  -- On the nonnegative half-line, the definition picks the intended coordinate combination.
  simp [coordinateDriftCombinationDensity, hs]
/-- Helper for the multidimensional Itô formula: the auxiliary drift-combination density vanishes on negative times.
-/
theorem coordinateDriftCombinationDensity_of_neg
    {b : VectorProcess} (ω : Ω) (k l : Fin d) (c₁ c₂ : ℝ) {s : ℝ} (hs : s < 0) :
    coordinateDriftCombinationDensity b ω k l c₁ c₂ s = 0 := by
  -- On negative times, the definition switches to the zero branch.
  simp [coordinateDriftCombinationDensity, not_le.mpr hs]

/-- Helper for Theorem 25.33: fixing `ω`, a progressively measurable coordinate drift produces a
measurable real-time section `s ↦ b s.toNNReal ω k`. -/
theorem measurable_coordinateDriftSection_of_progMeasurable
    {b : VectorProcess} {k : Fin d}
    (hkProg : ProgMeasurable ℱ (fun t ω ↦ b t ω k)) (ω : Ω) :
    Measurable fun s : ℝ ↦ b s.toNNReal ω k := by
  have h_uncurry : Measurable (Function.uncurry fun t ω ↦ b t ω k) :=
    MeasureTheory.ProgMeasurable.measurable_uncurry hkProg
  have hmap : Measurable fun s : ℝ ↦ (s.toNNReal, ω) := by
    exact measurable_id.real_toNNReal.prodMk measurable_const
  -- Proof comment: restrict the jointly measurable time-space map to the deterministic sample
  -- line `s ↦ (s.toNNReal, ω)`.
  simpa [Function.uncurry] using h_uncurry.comp hmap
/-- Helper for the multidimensional Itô formula: integrability on every natural horizon `[0,n]` upgrades to
integrability on every deterministic horizon `[0,t]`. -/
theorem integrableOn_Icc_of_natHorizons
    {f : ℝ → ℝ}
    (hNat : ∀ n : ℕ, IntegrableOn f (Set.Icc (0 : ℝ) (n : ℝ))) :
    ∀ t : NNReal, IntegrableOn f (Set.Icc (0 : ℝ) (t : ℝ)) := by
  intro t
  let n : ℕ := Nat.ceil (t : ℝ)
  have ht_le : (t : ℝ) ≤ n := Nat.le_ceil (t : ℝ)
  -- Each deterministic horizon `[0,t]` sits inside a natural horizon `[0,⌈t⌉]`.
  exact (hNat n).mono_set fun s hs ↦ ⟨hs.1, le_trans hs.2 ht_le⟩

/-- Helper for Theorem 25.33: the total variation on `Set.Icc 0 T` bounds the sum of the absolute
dyadic partition increments up to time `T`. -/
theorem sum_abs_dyadicPartitionIncrement_le_eVariationOn
    (Y : C(NNReal, ℝ)) (T : NNReal) (n : ℕ)
    (hYT : BoundedVariationOn Y (Set.Icc 0 T)) :
    ∑ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T),
      |Y (partitionNextPointUpTo dyadicPartitionSequence n k T) - Y (dyadicPartitionSequence n k)| ≤
        (eVariationOn Y (Set.Icc 0 T)).toReal := by
  let point : ℕ → NNReal := fun k ↦ min (dyadicPartitionSequence n k) T
  let m : ℕ := partitionBoundIndex dyadicPartitionSequence n T
  have hpoint_mono : Monotone point := by
    intro i j hij
    exact min_le_min
      ((instStrictMono_of_isAdmissiblePartitionSequence (P := dyadicPartitionSequence) n).monotone
        hij)
      le_rfl
  have hpoint_mem : ∀ i, point i ∈ Set.Icc 0 T := by
    intro i
    constructor
    · exact bot_le
    · exact min_le_right _ _
  have hpoint_left : ∀ k, k < m → point k = dyadicPartitionSequence n k := by
    intro k hk
    dsimp [point, m]
    rw [min_eq_left]
    have hk_not : ¬ T ≤ dyadicPartitionSequence n k := by
      intro hkT
      have hmin : partitionBoundIndex dyadicPartitionSequence n T ≤ k := by
        simpa [partitionBoundIndex] using
          (Nat.find_min' (exists_partition_index_le_time dyadicPartitionSequence n T) hkT)
      exact (not_le_of_gt hk) hmin
    exact le_of_lt (lt_of_not_ge hk_not)
  have hsum :
      ∑ k ∈ Finset.range m, edist (Y (point (k + 1))) (Y (point k)) ≤
        eVariationOn Y (Set.Icc 0 T) :=
    eVariationOn.sum_le (f := Y) (s := Set.Icc 0 T) (n := m) (u := point) hpoint_mono hpoint_mem
  have hsum_real := ENNReal.toReal_mono hYT hsum
  have hsum_real' :
      ∑ k ∈ Finset.range m, |Y (point (k + 1)) - Y (point k)| ≤
        (eVariationOn Y (Set.Icc 0 T)).toReal := by
    rw [ENNReal.toReal_sum] at hsum_real
    · simpa [edist_dist, Real.dist_eq] using hsum_real
    · intro k hk
      simpa using edist_ne_top (Y (point (k + 1))) (Y (point k))
  -- Rewriting the clipped dyadic points back to the active partition row gives the desired bound.
  calc
    ∑ k ∈ Finset.range m,
        |Y (partitionNextPointUpTo dyadicPartitionSequence n k T) - Y (dyadicPartitionSequence n k)| =
      ∑ k ∈ Finset.range m, |Y (point (k + 1)) - Y (point k)| := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hpoint_left k (Finset.mem_range.mp hk)]
          rfl
    _ ≤ (eVariationOn Y (Set.Icc 0 T)).toReal := by
          exact hsum_real'

/-- Helper for Theorem 25.33: a continuous path with locally bounded variation on `univ` has zero
dyadic square variation. -/
theorem hasSquareVariationAlong_zero_of_locallyBoundedVariationOn
    {Y : C(NNReal, ℝ)}
    (hY : LocallyBoundedVariationOn Y Set.univ) :
    HasSquareVariationAlong Y 0 := by
  intro T
  change Tendsto (partitionPVariationSum dyadicPartitionSequence 2 Y T) atTop (nhds (0 : ℝ))
  have hvar : BoundedVariationOn Y (Set.Icc 0 T) := by
    simpa [Set.univ_inter] using hY 0 T (Set.mem_univ _) (Set.mem_univ _)
  have hvar_finite : eVariationOn Y (Set.Icc 0 T) ≠ ⊤ := by
    exact hvar
  have hAbsSum_le :
      ∀ n : ℕ,
        ∑ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T),
          |Y (partitionNextPointUpTo dyadicPartitionSequence n k T) -
              Y (dyadicPartitionSequence n k)| ≤
            (eVariationOn Y (Set.Icc 0 T)).toReal := by
    intro n
    exact sum_abs_dyadicPartitionIncrement_le_eVariationOn Y T n hvar
  rw [Metric.tendsto_atTop]
  intro ε hε
  let varT : ℝ := (eVariationOn Y (Set.Icc 0 T)).toReal
  let η : ℝ := ε / (varT + 1)
  have hη_pos : 0 < η := by
    dsimp [η, varT]
    positivity
  have hUC :
      UniformContinuousOn Y (Set.Icc 0 T) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).uniformContinuousOn_of_continuous
      Y.continuous.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hUC) η hη_pos with ⟨δ, hδ_pos, hδ⟩
  have hmesh :
      ∀ᶠ n in atTop, partitionMesh dyadicPartitionSequence n ≤ ENNReal.ofReal δ := by
    exact
      (ENNReal.tendsto_nhds_zero.1
        (IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := dyadicPartitionSequence)))
        (ENNReal.ofReal δ)
        (ENNReal.ofReal_pos.2 hδ_pos)
  rcases Filter.Eventually.exists_forall_of_atTop hmesh with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hnN
  let inc : ℕ → ℝ := fun k ↦
    Y (partitionNextPointUpTo dyadicPartitionSequence n k T) - Y (dyadicPartitionSequence n k)
  have hsq_repr :
      partitionPVariationSum dyadicPartitionSequence 2 Y T n =
        ∑ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T), (inc k) ^ 2 := by
    rw [partitionPVariationSum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [← Real.rpow_natCast]
    simp [inc, sq_abs]
  have hsq_nonneg : 0 ≤ partitionPVariationSum dyadicPartitionSequence 2 Y T n := by
    rw [hsq_repr]
    exact Finset.sum_nonneg fun k hk ↦ sq_nonneg (inc k)
  have hsq_lt : partitionPVariationSum dyadicPartitionSequence 2 Y T n < ε := by
    calc
      partitionPVariationSum dyadicPartitionSequence 2 Y T n =
          ∑ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T), (inc k) ^ 2 := by
            exact hsq_repr
      _ ≤
          ∑ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T), η * |inc k| := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hk_lt : k < partitionBoundIndex dyadicPartitionSequence n T := Finset.mem_range.mp hk
            have hx_mem :
                dyadicPartitionSequence n k ∈ Set.Icc 0 T := by
              have hk_not : ¬ T ≤ dyadicPartitionSequence n k := by
                intro hkT
                have hmin : partitionBoundIndex dyadicPartitionSequence n T ≤ k := by
                  simpa [partitionBoundIndex] using
                    (Nat.find_min' (exists_partition_index_le_time dyadicPartitionSequence n T) hkT)
                exact (not_le_of_gt hk_lt) hmin
              constructor
              · exact bot_le
              · exact le_of_lt (lt_of_not_ge hk_not)
            have hy_mem :
                partitionNextPointUpTo dyadicPartitionSequence n k T ∈ Set.Icc 0 T := by
              constructor
              · exact bot_le
              · exact min_le_right _ _
            have hdist :
                edist (dyadicPartitionSequence n k)
                    (partitionNextPointUpTo dyadicPartitionSequence n k T) ≤
                  ENNReal.ofReal δ := by
              have hleft :
                  dyadicPartitionSequence n k ≤
                    partitionNextPointUpTo dyadicPartitionSequence n k T := by
                rw [partitionNextPointUpTo]
                refine le_min ?_ ?_
                · exact le_of_lt
                    ((instStrictMono_of_isAdmissiblePartitionSequence (P := dyadicPartitionSequence) n)
                      (Nat.lt_succ_self k))
                · exact hx_mem.2
              have hright :
                  partitionNextPointUpTo dyadicPartitionSequence n k T ≤
                    dyadicPartitionSequence n (k + 1) := by
                rw [partitionNextPointUpTo]
                exact min_le_left _ _
              have hdist_mesh :
                  edist (dyadicPartitionSequence n k)
                      (partitionNextPointUpTo dyadicPartitionSequence n k T) ≤
                    partitionMesh dyadicPartitionSequence n := by
                have hdist_succ :
                    edist (dyadicPartitionSequence n k)
                        (partitionNextPointUpTo dyadicPartitionSequence n k T) ≤
                      edist (dyadicPartitionSequence n k) (dyadicPartitionSequence n (k + 1)) := by
                  have hsucc :
                      dyadicPartitionSequence n k < dyadicPartitionSequence n (k + 1) := by
                    exact
                      (instStrictMono_of_isAdmissiblePartitionSequence (P := dyadicPartitionSequence) n)
                        (Nat.lt_succ_self k)
                  rw [edist_nndist, edist_nndist, NNReal.nndist_eq, NNReal.nndist_eq,
                    tsub_eq_zero_of_le hleft, tsub_eq_zero_of_le (le_of_lt hsucc),
                    max_eq_right, max_eq_right]
                  · exact_mod_cast tsub_le_tsub_right hright _
                  · simp
                  · simp
                calc
                  edist (dyadicPartitionSequence n k)
                      (partitionNextPointUpTo dyadicPartitionSequence n k T)
                      ≤ edist (dyadicPartitionSequence n k) (dyadicPartitionSequence n (k + 1)) :=
                        hdist_succ
                  _ ≤ partitionMesh dyadicPartitionSequence n := by
                        rw [partitionMesh]
                        exact le_iSup (fun j ↦ edist (dyadicPartitionSequence n j)
                          (dyadicPartitionSequence n (j + 1))) k
              exact hdist_mesh.trans (hN n hnN)
            have hdist' :
                dist (dyadicPartitionSequence n k)
                    (partitionNextPointUpTo dyadicPartitionSequence n k T) ≤
                  δ := by
              exact (ENNReal.ofReal_le_ofReal_iff hδ_pos.le).1 <| by
                simpa [edist_dist] using hdist
            have hInc_le : |inc k| ≤ η := by
              simpa [inc, Real.dist_eq, abs_sub_comm] using
                hδ
                  (dyadicPartitionSequence n k)
                  hx_mem
                  (partitionNextPointUpTo dyadicPartitionSequence n k T)
                  hy_mem
                  hdist'
            rw [← sq_abs]
            nlinarith [hInc_le, abs_nonneg (inc k)]
      _ = η *
          ∑ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T), |inc k| := by
            simp_rw [Finset.mul_sum]
      _ ≤ η * (eVariationOn Y (Set.Icc 0 T)).toReal := by
            gcongr
            exact hAbsSum_le n
      _ < η * (varT + 1) := by
            have hvar_lt : (eVariationOn Y (Set.Icc 0 T)).toReal < varT + 1 := by
              dsimp [varT]
              linarith
            exact mul_lt_mul_of_pos_left hvar_lt hη_pos
      _ = ε := by
            dsimp [η, varT]
            field_simp [show (eVariationOn Y (Set.Icc 0 T)).toReal + 1 ≠ 0 by positivity]
  have hdist_eq :
      dist (partitionPVariationSum dyadicPartitionSequence 2 Y T n) 0 =
        partitionPVariationSum dyadicPartitionSequence 2 Y T n := by
    rw [Real.dist_eq]
    simpa using abs_of_nonneg hsq_nonneg
  -- The dyadic quadratic-variation rows are eventually arbitrarily small, so the zero path
  -- realizes the square variation.
  simpa [hdist_eq] using hsq_lt
/-- Helper for the multidimensional Itô formula: on `[0,T]`, weighting the auxiliary drift density by a deterministic
path `H` is the same as weighting the intended coordinate linear combination of drifts. -/
theorem integral_weighted_coordinateDriftCombinationDensity_eq
    {b : VectorProcess} (H : NNReal → ℝ) (ω : Ω) (k l : Fin d) (c₁ c₂ : ℝ) (T : NNReal) :
    ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
      H s.toNNReal * coordinateDriftCombinationDensity b ω k l c₁ c₂ s =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          H s.toNNReal * (c₁ * b s.toNNReal ω k + c₂ * b s.toNNReal ω l) := by
  -- On `[0, T]`, the auxiliary density is already the intended coordinate linear combination.
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (T : ℝ)))] with
    s hs
  have hsNN : (⟨s, hs.1⟩ : NNReal) = s.toNNReal := by
    apply Subtype.ext
    simp [Real.toNNReal_of_nonneg hs.1]
  rw [coordinateDriftCombinationDensity_of_nonneg (ω := ω) (k := k) (l := l)
    (c₁ := c₁) (c₂ := c₂) hs.1]
  simpa [hsNN]
/-- Helper for the multidimensional Itô formula: once the auxiliary drift-combination density is locally integrable,
its indefinite integral path has zero square variation. -/
-- Route correction: the stable proof is not a local replay of the `pVariationUpTo` argument.
-- Import the canonical Chapter 21 corollary and compose it with
-- `locallyBoundedVariationOn_univ_indefiniteIntegralPath`.
theorem hasSquareVariationAlong_zero_of_coordinateDriftCombinationDensity
    {b : VectorProcess} (ω : Ω) (k l : Fin d) (c₁ c₂ : ℝ)
    (hf : LocallyIntegrable (coordinateDriftCombinationDensity b ω k l c₁ c₂) volume) :
    HasSquareVariationAlong
      (indefiniteIntegralPath (coordinateDriftCombinationDensity b ω k l c₁ c₂))
      0 := by
  -- The primitive path of a locally integrable density has locally bounded variation on `univ`.
  have hBV :
      LocallyBoundedVariationOn
        (indefiniteIntegralPath (coordinateDriftCombinationDensity b ω k l c₁ c₂))
        Set.univ :=
    locallyBoundedVariationOn_univ_indefiniteIntegralPath hf
  -- Locally bounded variation forces the dyadic square-variation owner to be the zero path.
  exact hasSquareVariationAlong_zero_of_locallyBoundedVariationOn hBV
/-- Helper for Theorem 25.33: on a fixed compact interval `[0, T]`, the auxiliary drift-combination
density is integrable once the two coordinate drift norms are integrable there. -/
theorem integrableOn_coordinateDriftCombinationDensity_Icc
    {b : VectorProcess}
    (k l : Fin d)
    (hkProg : ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hlProg : ProgMeasurable ℱ (fun t ω ↦ b t ω l))
    (ω : Ω) (c₁ c₂ : ℝ) (T : NNReal)
    (hk :
      IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (T : ℝ)))
    (hl :
      IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω l|) (Set.Icc (0 : ℝ) (T : ℝ))) :
    IntegrableOn
      (coordinateDriftCombinationDensity b ω k l c₁ c₂)
      (Set.Icc (0 : ℝ) (T : ℝ)) := by
  let I : Set ℝ := Set.Icc (0 : ℝ) (T : ℝ)
  have hmeas_k : Measurable fun s : ℝ ↦ b s.toNNReal ω k :=
    measurable_coordinateDriftSection_of_progMeasurable (k := k) hkProg ω
  have hmeas_l : Measurable fun s : ℝ ↦ b s.toNNReal ω l :=
    measurable_coordinateDriftSection_of_progMeasurable (k := l) hlProg ω
  have hk' : IntegrableOn (fun s : ℝ ↦ b s.toNNReal ω k) I := by
    rw [IntegrableOn]
    have hkNorm : Integrable (fun s : ℝ ↦ ‖b s.toNNReal ω k‖) (volume.restrict I) := by
      simpa [I, Real.norm_eq_abs] using hk
    -- Proof comment: on the restricted interval measure, measurability from progressive
    -- measurability lets `integrable_norm_iff` recover integrability of the coordinate drift.
    exact (integrable_norm_iff hmeas_k.aestronglyMeasurable).1 hkNorm
  have hl' : IntegrableOn (fun s : ℝ ↦ b s.toNNReal ω l) I := by
    rw [IntegrableOn]
    have hlNorm : Integrable (fun s : ℝ ↦ ‖b s.toNNReal ω l‖) (volume.restrict I) := by
      simpa [I, Real.norm_eq_abs] using hl
    -- Proof comment: the same norm-to-function bridge applies to the `l`-th coordinate.
    exact (integrable_norm_iff hmeas_l.aestronglyMeasurable).1 hlNorm
  have hLinear :
      IntegrableOn
        (fun s : ℝ ↦ c₁ * b s.toNNReal ω k + c₂ * b s.toNNReal ω l)
        I := by
    rw [IntegrableOn] at hk' hl' ⊢
    -- Proof comment: after both coordinates are integrable, the intended linear combination is
    -- integrable by scalar linearity on the restricted measure.
    exact (hk'.const_mul c₁).add (hl'.const_mul c₂)
  have hEq :
      Set.EqOn
        (coordinateDriftCombinationDensity b ω k l c₁ c₂)
        (fun s : ℝ ↦ c₁ * b s.toNNReal ω k + c₂ * b s.toNNReal ω l)
        I := by
    intro s hs
    have hsNN : (⟨s, hs.1⟩ : NNReal) = s.toNNReal := by
      apply Subtype.ext
      simp [Real.toNNReal_of_nonneg hs.1]
    -- Proof comment: on `[0, T]`, the auxiliary density is definitionally the intended
    -- coordinate linear combination.
    rw [coordinateDriftCombinationDensity_of_nonneg
      (ω := ω) (k := k) (l := l) (c₁ := c₁) (c₂ := c₂) hs.1]
    simp [hsNN]
  exact (integrableOn_congr_fun hEq measurableSet_Icc).2 hLinear
/-- Helper for the multidimensional Itô formula: for a fixed sample point `ω`, local integrability of the auxiliary
drift-combination density follows once both coordinate drifts are integrable on every natural
horizon. -/
theorem coordinateDriftCombination_locallyIntegrable_of_natHorizons
    {b : VectorProcess} (ω : Ω) (k l : Fin d) (c₁ c₂ : ℝ)
    (hkProg : ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hlProg : ProgMeasurable ℱ (fun t ω ↦ b t ω l))
    (hNat :
      ∀ n : ℕ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (n : ℝ)) ∧
          IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω l|) (Set.Icc (0 : ℝ) (n : ℝ))) :
    LocallyIntegrable (coordinateDriftCombinationDensity b ω k l c₁ c₂) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hKMeas : MeasurableSet K := hK.isClosed.measurableSet
  have hSplit :
      K = (K ∩ Set.Iio (0 : ℝ)) ∪ (K ∩ Set.Ici (0 : ℝ)) := by
    ext x
    constructor
    · intro hx
      by_cases hxneg : x < 0
      · exact Or.inl ⟨hx, hxneg⟩
      · exact Or.inr ⟨hx, le_of_not_gt hxneg⟩
    · intro hx
      exact hx.elim (fun hx' ↦ hx'.1) fun hx' ↦ hx'.1
  have hNegEq :
      Set.EqOn
        (coordinateDriftCombinationDensity b ω k l c₁ c₂)
        (fun _ : ℝ ↦ 0)
        (K ∩ Set.Iio (0 : ℝ)) := by
    intro s hs
    exact coordinateDriftCombinationDensity_of_neg (ω := ω) (k := k) (l := l)
      (c₁ := c₁) (c₂ := c₂) hs.2
  have hNeg :
      IntegrableOn
        (coordinateDriftCombinationDensity b ω k l c₁ c₂)
        (K ∩ Set.Iio (0 : ℝ)) := by
    -- On the negative half-line the auxiliary density vanishes identically.
    exact
      (integrableOn_congr_fun hNegEq (hKMeas.inter measurableSet_Iio)).2
        integrableOn_zero
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  let R : ℝ := max R0 1
  have hRpos : 0 < R := by
    positivity
  have hR :
      ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have hxBall : x ∈ Metric.closedBall (0 : ℝ) R0 := hR0 hx
    have hxR0 : ‖x‖ ≤ R0 := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxBall
    exact hxR0.trans (le_max_left _ _)
  let N : ℕ := Nat.ceil R
  have hSubset :
      K ∩ Set.Ici (0 : ℝ) ⊆ Set.Icc (0 : ℝ) (N : ℝ) := by
    intro x hx
    constructor
    · exact hx.2
    · have hxR : x ≤ R := by
        exact le_trans (le_abs_self x) (hR x hx.1)
      exact le_trans hxR (Nat.le_ceil R)
  have hNonnegIcc :
      IntegrableOn
        (coordinateDriftCombinationDensity b ω k l c₁ c₂)
        (Set.Icc (0 : ℝ) (N : ℝ)) := by
    -- The nonnegative compact part sits inside one natural horizon.
    simpa using
      integrableOn_coordinateDriftCombinationDensity_Icc
        (k := k) (l := l) (hkProg := hkProg) (hlProg := hlProg)
        (ω := ω) (c₁ := c₁) (c₂ := c₂) (T := (N : NNReal))
        (hNat N).1 (hNat N).2
  have hNonneg :
      IntegrableOn
        (coordinateDriftCombinationDensity b ω k l c₁ c₂)
        (K ∩ Set.Ici (0 : ℝ)) := by
    exact hNonnegIcc.mono_set hSubset
  -- Combine the negative and nonnegative pieces of the compact set.
  exact hSplit.symm ▸ hNeg.union hNonneg
/-- Helper for the multidimensional Itô formula: the auxiliary drift-combination density is almost surely locally
integrable once each coordinate drift is integrable on every deterministic interval `[0, T]`. -/
theorem ae_coordinateDriftCombination_locallyIntegrable
    {b : VectorProcess}
    (hprog : ∀ i : Fin d, ProgMeasurable ℱ (fun t ω ↦ b t ω i))
    (hint :
      ∀ k : Fin d, ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (T : ℝ)))
    (k l : Fin d) (c₁ c₂ : ℝ) :
    ∀ᵐ ω ∂μ, LocallyIntegrable (coordinateDriftCombinationDensity b ω k l c₁ c₂) volume := by
  have hkNat :
      ∀ᵐ ω ∂μ,
        ∀ n : ℕ,
          IntegrableOn
            (fun s : ℝ ↦ |b s.toNNReal ω k|)
            (Set.Icc (0 : ℝ) (n : ℝ)) := by
    -- Restrict the interval-integrability hypothesis to natural horizons for coordinate `k`.
    simpa using (ae_all_iff.2 fun n : ℕ ↦ hint k (n : NNReal))
  have hlNat :
      ∀ᵐ ω ∂μ,
        ∀ n : ℕ,
          IntegrableOn
            (fun s : ℝ ↦ |b s.toNNReal ω l|)
            (Set.Icc (0 : ℝ) (n : ℝ)) := by
    -- Do the same for coordinate `l`.
    simpa using (ae_all_iff.2 fun n : ℕ ↦ hint l (n : NNReal))
  -- Apply the deterministic compact-set bridge pointwise on the almost-sure event.
  filter_upwards [hkNat, hlNat] with ω hkω hlω
  exact
    coordinateDriftCombination_locallyIntegrable_of_natHorizons
      (ω := ω) (k := k) (l := l) (c₁ := c₁) (c₂ := c₂)
      (hkProg := hprog k) (hlProg := hprog l)
      (fun n ↦ ⟨hkω n, hlω n⟩)
/-- Helper for the multidimensional Itô formula: the generalized diffusion `Y` has almost surely continuous
`State`-valued sample paths once each coordinate martingale part is continuous and the drift
coordinates are integrable on deterministic intervals. -/
theorem ae_continuousGeneralizedDiffusionPath
    {b Y : VectorProcess}
    (hprog : ∀ k : Fin d, ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hM :
      ∀ k : Fin d,
        IsContinuousLocalMartingale ℱ μ
          (generalizedDiffusionCoordinateMartingalePart b Y k))
    (hint :
      ∀ k : Fin d, ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ Y t ω := by
  have hNat :
      ∀ᵐ ω ∂μ,
        ∀ k : Fin d, ∀ n : ℕ,
          IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (n : ℝ)) := by
    refine ae_all_iff.2 ?_
    intro k
    refine ae_all_iff.2 ?_
    intro n
    simpa using hint k (n : NNReal)
  filter_upwards [hNat] with ω hω
  have hcoord : ∀ i : Fin d, Continuous fun t : NNReal ↦ Y t ω i := by
    intro i
    let f : ℝ → ℝ := coordinateDriftCombinationDensity b ω i i 1 0
    have hfLoc : LocallyIntegrable f volume :=
      coordinateDriftCombination_locallyIntegrable_of_natHorizons
        (ω := ω) (k := i) (l := i) (c₁ := 1) (c₂ := 0)
        (hkProg := hprog i) (hlProg := hprog i)
        (fun n ↦ ⟨hω i n, hω i n⟩)
    have hDriftEq :
        (fun t : NNReal ↦ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω i) =
          indefiniteIntegralPath f := by
      funext t
      rw [indefiniteIntegralPath_apply_of_locallyIntegrable hfLoc]
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) by exact_mod_cast t.2)]
      rw [integral_Icc_eq_integral_Ioc]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := ⟨le_of_lt hs.1, hs.2⟩
      have hsNN : (⟨s, hsT.1⟩ : NNReal) = s.toNNReal := by
        apply Subtype.ext
        simp [Real.toNNReal_of_nonneg hsT.1]
      simp [f, hsNN, coordinateDriftCombinationDensity_of_nonneg
        (ω := ω) (k := i) (l := i) (c₁ := 1) (c₂ := 0) hsT.1]
    have hDriftCont :
        Continuous fun t : NNReal ↦ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω i := by
      simpa [hDriftEq] using (indefiniteIntegralPath f).continuous
    have hMartCont :
        Continuous fun t : NNReal ↦ generalizedDiffusionCoordinateMartingalePart b Y i t ω :=
      (hM i).continuous ω
    have hDecomp :
        (fun t : NNReal ↦ Y t ω i) =
          fun t : NNReal ↦
            generalizedDiffusionCoordinateMartingalePart b Y i t ω +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω i := by
      funext t
      dsimp [generalizedDiffusionCoordinateMartingalePart]
      ring
    simpa [hDecomp] using hMartCont.add hDriftCont
  exact continuous_state_of_coordinates hcoord
/-- Helper for the multidimensional Itô formula: the partition point sets of an admissible partition sequence are
monotone in the row index. -/
theorem partitionPointSet_mono
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P] :
    Monotone (partitionPointSet P) := by
  intro m n hmn
  induction hmn with
  | refl =>
      -- The point-set map is trivially monotone along equal indices.
      exact fun _ hx ↦ hx
  | @step n hle ih =>
      -- Each successor step is handled by the admissibility nesting field.
      exact Set.Subset.trans ih (hP.nested n)
/-- Helper for the multidimensional Itô formula: reindexing the rows of an admissible partition sequence along a
strictly monotone subsequence preserves admissibility. -/
instance isAdmissiblePartitionSequence_comp
    {P : ℕ → ℕ → NNReal} [hP : IsAdmissiblePartitionSequence P]
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsAdmissiblePartitionSequence (fun n k ↦ P (φ n) k) where
  zero_eq n := hP.zero_eq (φ n)
  strictMono n := hP.strictMono (φ n)
  nested n :=
    partitionPointSet_mono P (hφ.monotone (Nat.le_succ n))
  tendsto_atTop n := hP.tendsto_atTop (φ n)
  mesh_tendsto_zero := hP.mesh_tendsto_zero.comp hφ.tendsto_atTop

/-- Helper for the multidimensional Itô formula: each fixed linear combination of two coordinates of `Y` splits into
the corresponding martingale combination plus the two drift integrals. -/
theorem linearCombination_coordinate_eq_martingalePart_add_driftIntegrals
    {b Y : VectorProcess} (k l : Fin d) (c₁ c₂ : ℝ) (t : NNReal) (ω : Ω) :
    c₁ * Y t ω k + c₂ * Y t ω l =
      c₁ * generalizedDiffusionCoordinateMartingalePart b Y k t ω +
        c₂ * generalizedDiffusionCoordinateMartingalePart b Y l t ω +
        c₁ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k) +
        c₂ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω l) := by
  -- Expanding both coordinate martingale parts leaves a purely algebraic identity.
  dsimp [generalizedDiffusionCoordinateMartingalePart]
  ring
/-- Helper for the multidimensional Itô formula: the sum of two coordinates of `Y` decomposes into the sum of the
corresponding martingale parts plus the two coordinate drift integrals. -/
theorem add_coordinates_eq_add_martingaleParts_add_driftIntegrals
    {b Y : VectorProcess} (k l : Fin d) (t : NNReal) (ω : Ω) :
    Y t ω k + Y t ω l =
      generalizedDiffusionCoordinateMartingalePart b Y k t ω +
        generalizedDiffusionCoordinateMartingalePart b Y l t ω +
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k) +
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω l) := by
  -- This is the linear-combination identity with coefficients `1` and `1`.
  simpa using
    linearCombination_coordinate_eq_martingalePart_add_driftIntegrals
      (b := b) (Y := Y) k l (1 : ℝ) (1 : ℝ) t ω
/-- Helper for the multidimensional Itô formula: the coordinate difference `Y^k - Y^l` decomposes into the
corresponding martingale difference plus the drift-integral difference. -/
theorem sub_coordinates_eq_sub_martingaleParts_add_driftIntegrals
    {b Y : VectorProcess} (k l : Fin d) (t : NNReal) (ω : Ω) :
    Y t ω k - Y t ω l =
      generalizedDiffusionCoordinateMartingalePart b Y k t ω -
        generalizedDiffusionCoordinateMartingalePart b Y l t ω +
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k) -
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω l) := by
  -- This is the linear-combination identity with coefficients `1` and `-1`.
  simpa [sub_eq_add_neg] using
    linearCombination_coordinate_eq_martingalePart_add_driftIntegrals
      (b := b) (Y := Y) k l (1 : ℝ) (-1 : ℝ) t ω
/-- Helper for the multidimensional Itô formula: a chosen continuous sample path of `Y` yields a continuous path in
its `k`-th coordinate. -/
abbrev generalizedDiffusionCoordinatePath
    (Y : VectorProcess) {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ Y t ω) (k : Fin d) : C(NNReal, ℝ) :=
  ⟨fun t ↦ Y t ω k, by
    fun_prop⟩

/-- Helper for the multidimensional Itô formula: a chosen continuous sample path of `Y` yields the corresponding
continuous path of the linear combination `c₁ Y^k + c₂ Y^l`. -/
abbrev generalizedDiffusionCoordinateLinearCombinationPath
    (Y : VectorProcess) {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ Y t ω)
    (k l : Fin d) (c₁ c₂ : ℝ) : C(NNReal, ℝ) :=
  ⟨fun t ↦ c₁ * Y t ω k + c₂ * Y t ω l, by
    fun_prop⟩

/-- Helper for Theorem 25.33: after rewriting the two drift integrals through the auxiliary
drift-combination density, the actual coordinate linear combination is the martingale linear
combination plus one bundled primitive path. -/
theorem generalizedDiffusionCoordinateLinearCombination_eq_martingalePlusDriftPrimitive
    {b Y : VectorProcess} {ω : Ω}
    (k l : Fin d) (c₁ c₂ : ℝ) (t : NNReal)
    (hkProg : ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hlProg : ProgMeasurable ℱ (fun t ω ↦ b t ω l))
    (hNatω :
      ∀ n : ℕ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (n : ℝ)) ∧
          IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω l|) (Set.Icc (0 : ℝ) (n : ℝ)))
    (hLocω : LocallyIntegrable (coordinateDriftCombinationDensity b ω k l c₁ c₂) volume) :
    c₁ * Y t ω k + c₂ * Y t ω l =
      c₁ * generalizedDiffusionCoordinateMartingalePart b Y k t ω +
        c₂ * generalizedDiffusionCoordinateMartingalePart b Y l t ω +
        indefiniteIntegralPath (coordinateDriftCombinationDensity b ω k l c₁ c₂) t := by
  have hkInt :
      IntegrableOn
        (fun s : ℝ ↦ b s.toNNReal ω k)
        (Set.Icc (0 : ℝ) (t : ℝ)) := by
    -- Proof comment: natural-horizon integrability specializes to the current deterministic time.
    have hkAbs :
        IntegrableOn
          (fun s : ℝ ↦ |b s.toNNReal ω k|)
          (Set.Icc (0 : ℝ) (t : ℝ)) :=
      (integrableOn_Icc_of_natHorizons fun n ↦ (hNatω n).1) t
    rw [IntegrableOn] at hkAbs ⊢
    exact
      (integrable_norm_iff
        (measurable_coordinateDriftSection_of_progMeasurable (k := k) hkProg ω).aestronglyMeasurable).1 <|
        by simpa [Real.norm_eq_abs] using hkAbs
  have hlInt :
      IntegrableOn
        (fun s : ℝ ↦ b s.toNNReal ω l)
        (Set.Icc (0 : ℝ) (t : ℝ)) := by
    -- Proof comment: the same interval-integrability upgrade holds for the `l`-th coordinate.
    have hlAbs :
        IntegrableOn
          (fun s : ℝ ↦ |b s.toNNReal ω l|)
          (Set.Icc (0 : ℝ) (t : ℝ)) :=
      (integrableOn_Icc_of_natHorizons fun n ↦ (hNatω n).2) t
    rw [IntegrableOn] at hlAbs ⊢
    exact
      (integrable_norm_iff
        (measurable_coordinateDriftSection_of_progMeasurable (k := l) hlProg ω).aestronglyMeasurable).1 <|
        by simpa [Real.norm_eq_abs] using hlAbs
  have hDensity :
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), coordinateDriftCombinationDensity b ω k l c₁ c₂ s =
        c₁ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k) +
          c₂ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω l) := by
    -- Proof comment: on `[0, t]`, the auxiliary density is exactly `c₁ b^k + c₂ b^l`, so the
    -- interval integral splits by linearity.
    calc
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), coordinateDriftCombinationDensity b ω k l c₁ c₂ s
          =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          c₁ * b s.toNNReal ω k + c₂ * b s.toNNReal ω l := by
            simpa using
              integral_weighted_coordinateDriftCombinationDensity_eq
                (b := b) (H := fun _ ↦ (1 : ℝ)) ω k l c₁ c₂ t
      _ =
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), c₁ * b s.toNNReal ω k) +
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), c₂ * b s.toNNReal ω l := by
            simpa using integral_add (hkInt.const_mul c₁) (hlInt.const_mul c₂)
      _ =
        c₁ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k) +
          c₂ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω l) := by
            rw [integral_const_mul, integral_const_mul]
  -- Proof comment: substitute the drift primitive for the pair of explicit drift integrals.
  calc
    c₁ * Y t ω k + c₂ * Y t ω l
        =
      c₁ * generalizedDiffusionCoordinateMartingalePart b Y k t ω +
        c₂ * generalizedDiffusionCoordinateMartingalePart b Y l t ω +
        c₁ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k) +
        c₂ * (∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω l) :=
      linearCombination_coordinate_eq_martingalePart_add_driftIntegrals
        (b := b) (Y := Y) k l c₁ c₂ t ω
    _ =
      c₁ * generalizedDiffusionCoordinateMartingalePart b Y k t ω +
        c₂ * generalizedDiffusionCoordinateMartingalePart b Y l t ω +
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), coordinateDriftCombinationDensity b ω k l c₁ c₂ s := by
          rw [hDensity]
          ring
    _ =
      c₁ * generalizedDiffusionCoordinateMartingalePart b Y k t ω +
        c₂ * generalizedDiffusionCoordinateMartingalePart b Y l t ω +
        indefiniteIntegralPath (coordinateDriftCombinationDensity b ω k l c₁ c₂) t := by
          rw [indefiniteIntegralPath_apply_of_locallyIntegrable hLocω]
          rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) by exact_mod_cast t.2)]
          rw [integral_Icc_eq_integral_Ioc]

/-- Helper for the multidimensional Itô formula: once the martingale coordinate covariations are known pathwise and
the drift combination is locally integrable, the actual path `c₁ Y^k + c₂ Y^l` inherits the
expected square-variation witness. -/
theorem hasSquareVariationAlong_generalizedDiffusionCoordinateLinearCombination
    {a : MatrixProcess} {b Y : VectorProcess} {ω : Ω}
    (k l : Fin d) (c₁ c₂ : ℝ)
    (hkProg : ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hlProg : ProgMeasurable ℱ (fun t ω ↦ b t ω l))
    (hcont : Continuous fun t : NNReal ↦ Y t ω)
    (hNatω :
      ∀ n : ℕ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (n : ℝ)) ∧
          IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω l|) (Set.Icc (0 : ℝ) (n : ℝ)))
    (hM :
      ∀ i : Fin d,
        IsContinuousLocalMartingale ℱ μ
          (generalizedDiffusionCoordinateMartingalePart b Y i))
    (hkk :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
          (hM k).continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
          (hM k).continuous ω⟩ : C(NNReal, ℝ))
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k))
    (hll :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
          (hM l).continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
          (hM l).continuous ω⟩ : C(NNReal, ℝ))
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l))
    (hkl :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
          (hM k).continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
          (hM l).continuous ω⟩ : C(NNReal, ℝ))
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l))
    (hLocω : LocallyIntegrable (coordinateDriftCombinationDensity b ω k l c₁ c₂) volume) :
    HasSquareVariationAlong
      (generalizedDiffusionCoordinateLinearCombinationPath Y hcont k l c₁ c₂)
      (fun T ↦
        c₁ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k) +
          2 * ((c₁ * c₂) * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l)) +
          c₂ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l)) := by
  let Mk : C(NNReal, ℝ) :=
    ⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω, (hM k).continuous ω⟩
  let Ml : C(NNReal, ℝ) :=
    ⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω, (hM l).continuous ω⟩
  let D : C(NNReal, ℝ) := indefiniteIntegralPath (coordinateDriftCombinationDensity b ω k l c₁ c₂)
  have hMartSq :
      HasSquareVariationAlong
        ((c₁ : ℝ) • Mk + c₂ • Ml)
        (fun T ↦
          c₁ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k) +
            2 * ((c₁ * c₂) * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l)) +
            c₂ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l)) := by
    have hMkScaled :
        HasSquareVariationAlong
          ((c₁ : ℝ) • Mk)
          (fun T ↦ c₁ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k)) := by
      -- Proof comment: scaling the `k`-coordinate martingale path scales its bracket by `c₁²`.
      simpa [pow_two] using
        hasSquareVariationAlong_of_self_quadraticCovariation
          (hasQuadraticCovariationAlong_smulPath hkk c₁ c₁)
    have hMlScaled :
        HasSquareVariationAlong
          (c₂ • Ml)
          (fun T ↦ c₂ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l)) := by
      -- Proof comment: the same scaling rule applies to the `l`-coordinate martingale path.
      simpa [pow_two] using
        hasSquareVariationAlong_of_self_quadraticCovariation
          (hasQuadraticCovariationAlong_smulPath hll c₂ c₂)
    have hScaledCov :
        HasQuadraticCovariationAlong
          ((c₁ : ℝ) • Mk)
          (c₂ • Ml)
          (fun T ↦ (c₁ * c₂) * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l)) := by
      -- Proof comment: the mixed bracket scales by the product `c₁ c₂`.
      simpa using hasQuadraticCovariationAlong_smulPath hkl c₁ c₂
    -- Proof comment: add the two scaled martingale coordinates using the standard bracket algebra.
    simpa [Mk, Ml, Pi.smul_apply, ContinuousMap.add_apply, smul_eq_mul,
      add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      (hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong
        hMkScaled hMlScaled hScaledCov)
  have hDriftSq : HasSquareVariationAlong D 0 :=
    hasSquareVariationAlong_zero_of_coordinateDriftCombinationDensity
      (b := b) ω k l c₁ c₂ hLocω
  have hZeroCov :
      HasQuadraticCovariationAlong ((c₁ : ℝ) • Mk + c₂ • Ml) D 0 :=
    hasQuadraticCovariationAlong_zero_of_rightZeroSquareVariation hMartSq hDriftSq
  have hSumSq :
      HasSquareVariationAlong
        (((c₁ : ℝ) • Mk + c₂ • Ml) + D)
        (fun T ↦
          c₁ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k) +
            2 * ((c₁ * c₂) * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l)) +
            c₂ ^ 2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l)) := by
    -- Proof comment: the drift primitive is a zero-square perturbation, so it does not change
    -- the martingale square-variation witness.
    simpa [D] using
      (hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong
        hMartSq hDriftSq hZeroCov)
  have hPathEq :
      generalizedDiffusionCoordinateLinearCombinationPath Y hcont k l c₁ c₂ =
        (((c₁ : ℝ) • Mk + c₂ • Ml) + D) := by
    -- Proof comment: bundle the pointwise martingale-plus-drift identity into an equality of
    -- continuous paths and transport the square-variation witness across it.
    ext t
    simpa [Mk, Ml, D, generalizedDiffusionCoordinateLinearCombinationPath,
      Pi.smul_apply, ContinuousMap.add_apply, smul_eq_mul] using
      generalizedDiffusionCoordinateLinearCombination_eq_martingalePlusDriftPrimitive
        (b := b) (Y := Y) (ω := ω) k l c₁ c₂ t hkProg hlProg hNatω hLocω
  simpa [hPathEq] using hSumSq
/-- Helper for the multidimensional Itô formula: by polarizing the pathwise square-variation witnesses for
`Y^k + Y^l` and `Y^k - Y^l`, one gets the desired quadratic covariation of the actual coordinate
paths of `Y`. -/
theorem hasQuadraticCovariationAlong_generalizedDiffusionCoordinates
    {a : MatrixProcess} {b Y : VectorProcess} {ω : Ω}
    (k l : Fin d)
    (hkProg : ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hlProg : ProgMeasurable ℱ (fun t ω ↦ b t ω l))
    (hcont : Continuous fun t : NNReal ↦ Y t ω)
    (hNatω :
      ∀ n : ℕ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (n : ℝ)) ∧
          IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω l|) (Set.Icc (0 : ℝ) (n : ℝ)))
    (hM :
      ∀ i : Fin d,
        IsContinuousLocalMartingale ℱ μ
          (generalizedDiffusionCoordinateMartingalePart b Y i))
    (hkk :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
          (hM k).continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
          (hM k).continuous ω⟩ : C(NNReal, ℝ))
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k))
    (hll :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
          (hM l).continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
          (hM l).continuous ω⟩ : C(NNReal, ℝ))
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l))
    (hkl :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
          (hM k).continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
          (hM l).continuous ω⟩ : C(NNReal, ℝ))
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l))
    (hLocAdd : LocallyIntegrable (coordinateDriftCombinationDensity b ω k l 1 1) volume)
    (hLocSub : LocallyIntegrable (coordinateDriftCombinationDensity b ω k l 1 (-1)) volume) :
    HasQuadraticCovariationAlong
      (generalizedDiffusionCoordinatePath Y hcont k)
      (generalizedDiffusionCoordinatePath Y hcont l)
      (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l) := by
  have hAddSq :
      HasSquareVariationAlong
        (generalizedDiffusionCoordinatePath Y hcont k + generalizedDiffusionCoordinatePath Y hcont l)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k) +
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l)) := by
    -- Proof comment: first transport the `Y^k + Y^l` square variation from the martingale
    -- combination to the actual coordinate sum.
    simpa [generalizedDiffusionCoordinatePath, generalizedDiffusionCoordinateLinearCombinationPath] using
      hasSquareVariationAlong_generalizedDiffusionCoordinateLinearCombination
        (a := a) (b := b) (Y := Y) (ω := ω) k l (1 : ℝ) (1 : ℝ)
        hkProg hlProg hcont hNatω hM hkk hll hkl hLocAdd
  have hSubSq :
      HasSquareVariationAlong
        (generalizedDiffusionCoordinatePath Y hcont k - generalizedDiffusionCoordinatePath Y hcont l)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k) -
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l)) := by
    -- Proof comment: the same zero-square transport works for the difference path.
    simpa [generalizedDiffusionCoordinatePath, generalizedDiffusionCoordinateLinearCombinationPath,
      sub_eq_add_neg] using
      hasSquareVariationAlong_generalizedDiffusionCoordinateLinearCombination
        (a := a) (b := b) (Y := Y) (ω := ω) k l (1 : ℝ) (-1 : ℝ)
        hkProg hlProg hcont hNatω hM hkk hll hkl hLocSub
  -- Proof comment: polarize the sum and difference witnesses to recover the mixed covariation.
  convert hasQuadraticCovariationAlong_polarizationPath hAddSq hSubSq using 1
  ext T
  simp [Pi.smul_apply, Pi.sub_apply]
  ring
/-- Helper for the multidimensional Itô formula: the generalized diffusion coordinates admit the expected almost-sure
pathwise quadratic covariations once the process-level covariation owners are given. -/
theorem ae_hasQuadraticCovariationAlong_generalizedDiffusionCoordinates
    {a : MatrixProcess} {b Y : VectorProcess}
    (hM :
      ∀ i : Fin d,
        IsContinuousLocalMartingale ℱ μ
          (generalizedDiffusionCoordinateMartingalePart b Y i))
    (hCovariation :
      ∀ i j : Fin d,
        IsContinuousQuadraticCovariationProcess
          ℱ
          μ
          (generalizedDiffusionCoordinateMartingalePart b Y i)
          (generalizedDiffusionCoordinateMartingalePart b Y j)
        (fun T ω ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j))
    (hprog : ∀ i : Fin d, ProgMeasurable ℱ (fun t ω ↦ b t ω i))
    (hint :
      ∀ i : Fin d, ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω i|) (Set.Icc (0 : ℝ) (T : ℝ)))
    (k l : Fin d) :
    ∀ᵐ ω ∂μ,
      ∃ hcont : Continuous fun t : NNReal ↦ Y t ω,
        HasQuadraticCovariationAlong
          (generalizedDiffusionCoordinatePath Y hcont k)
          (generalizedDiffusionCoordinatePath Y hcont l)
          (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l) := by
  have hcont :
      ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ Y t ω :=
    ae_continuousGeneralizedDiffusionPath (b := b) (Y := Y) hprog hM hint
  have hkNat :
      ∀ᵐ ω ∂μ,
        ∀ n : ℕ,
          IntegrableOn
            (fun s : ℝ ↦ |b s.toNNReal ω k|)
            (Set.Icc (0 : ℝ) (n : ℝ)) := by
    -- Restrict the drift-integrability hypothesis to natural horizons for coordinate `k`.
    simpa using (ae_all_iff.2 fun n : ℕ ↦ hint k (n : NNReal))
  have hlNat :
      ∀ᵐ ω ∂μ,
        ∀ n : ℕ,
          IntegrableOn
            (fun s : ℝ ↦ |b s.toNNReal ω l|)
            (Set.Icc (0 : ℝ) (n : ℝ)) := by
    -- Do the same for coordinate `l`.
    simpa using (ae_all_iff.2 fun n : ℕ ↦ hint l (n : NNReal))
  have hkk :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
            (hM k).continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
            (hM k).continuous ω⟩ : C(NNReal, ℝ))
          (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k k) :=
    ae_hasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcess
      (hM k) (hM k) (hCovariation k k)
  have hll :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
            (hM l).continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
            (hM l).continuous ω⟩ : C(NNReal, ℝ))
          (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω l l) :=
    ae_hasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcess
      (hM l) (hM l) (hCovariation l l)
  have hkl :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
            (hM k).continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
            (hM l).continuous ω⟩ : C(NNReal, ℝ))
          (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l) :=
    ae_hasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcess
      (hM k) (hM l) (hCovariation k l)
  have hLocAdd :
      ∀ᵐ ω ∂μ,
        LocallyIntegrable
          (coordinateDriftCombinationDensity b ω k l (1 : ℝ) (1 : ℝ))
          volume :=
    ae_coordinateDriftCombination_locallyIntegrable (b := b) hprog hint k l (1 : ℝ) (1 : ℝ)
  have hLocSub :
      ∀ᵐ ω ∂μ,
        LocallyIntegrable
          (coordinateDriftCombinationDensity b ω k l (1 : ℝ) (-1 : ℝ))
          volume :=
    ae_coordinateDriftCombination_locallyIntegrable (b := b) hprog hint k l (1 : ℝ) (-1 : ℝ)
  -- Route correction: after isolating local integrability, the remaining step is the deterministic
  -- polarization theorem for the actual coordinate paths.
  filter_upwards [hcont, hkNat, hlNat, hkk, hll, hkl, hLocAdd, hLocSub] with
    ω hcontω hkω hlω hkkω hllω hklω hLocAddω hLocSubω
  refine ⟨hcontω, ?_⟩
  exact
    hasQuadraticCovariationAlong_generalizedDiffusionCoordinates
      (ω := ω) (k := k) (l := l)
      (hkProg := hprog k) (hlProg := hprog l) hcontω
      (fun n ↦ ⟨hkω n, hlω n⟩) hM hkkω hllω hklω hLocAddω hLocSubω
/-- Helper for the multidimensional Itô formula: along a continuous sample path of `Y`, every Hessian entry
`s ↦ (∂²[i, j] F) (Y s.toNNReal ω)` is continuous on `ℝ`. -/
theorem continuous_secondPartialDeriv_comp_generalizedDiffusionPath
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {Y : VectorProcess} {ω : Ω}
    (hcontω : Continuous fun t : NNReal ↦ Y t ω)
    (i j : Fin d) :
    Continuous fun s : ℝ ↦ (∂²[i, j] F) (Y s.toNNReal ω) := by
  -- Reparametrize the continuous sample path by `Real.toNNReal` to view it on all of `ℝ`.
  have hpath : Continuous fun s : ℝ ↦ Y s.toNNReal ω :=
    hcontω.comp continuous_real_toNNReal
  -- The Hessian entry is continuous by the `C²` regularity of `F`, so composition closes.
  exact (continuous_secondPartialDeriv F hF i j).comp hpath
/-- Helper for the multidimensional Itô formula: the sum and difference coordinate paths have canonical positive
Stieltjes measures whose primitives are the expected polarization combinations of the matrix field
`a`. -/
theorem covariationPrimitivePolarizationWitnesses
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    {Yi Yj : C(NNReal, ℝ)}
    (hii :
      HasQuadraticCovariationAlong
        Yi
        Yi
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i))
    (hjj :
      HasQuadraticCovariationAlong
        Yj
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hij :
      HasQuadraticCovariationAlong
        Yi
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j)) :
    HasSquareVariationAlong
        (Yi + Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)) ∧
    HasSquareVariationAlong
        (Yi - Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)) := by
  have hiiSq :
      HasSquareVariationAlong
        Yi
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) :=
    hasSquareVariationAlong_of_self_quadraticCovariation hii
  have hjjSq :
      HasSquareVariationAlong
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j) :=
    hasSquareVariationAlong_of_self_quadraticCovariation hjj
  have hNegjSq :
      HasSquareVariationAlong
        ((-1 : ℝ) • Yj)
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j) := by
    simpa [pow_two] using
      hasSquareVariationAlong_of_self_quadraticCovariation
        (hasQuadraticCovariationAlong_smulPath hjj (-1) (-1))
  have hINegJ :
      HasQuadraticCovariationAlong
        Yi
        ((-1 : ℝ) • Yj)
        (fun T ↦ -(∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j)) := by
    simpa [neg_mul, one_mul] using
      hasQuadraticCovariationAlong_smulPath hij 1 (-1)
  constructor
  · -- Proof comment: the plus polarization is the standard square-variation formula for `Yi + Yj`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong hiiSq hjjSq hij)
  · -- Proof comment: the minus polarization is the companion formula for `Yi - Yj`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong hiiSq hNegjSq hINegJ)
/-- Helper for the multidimensional Itô formula: the weighted pathwise mixed covariation is the quarter difference
of the corresponding weighted square-variation integrals of the sum and difference paths, using
their canonical square-variation measures. -/
theorem pathwiseQuadraticCovariationIntegral_eq_weightedPolarization
    (H : NNReal → ℝ) (hH : Continuous H)
    {Y Z covAdd covSub : C(NNReal, ℝ)}
    (hAdd : HasSquareVariationAlong (Y + Z) covAdd)
    (hSub : HasSquareVariationAlong (Y - Z) covSub)
    (T : NNReal) :
    pathwiseQuadraticCovariationIntegral H Y Z T =
      (1 / 4 : ℝ) *
        ((∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hAdd)) -
          ∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hSub)) := by
  let L : ℝ :=
    (1 / 4 : ℝ) *
      ((∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hAdd)) -
        ∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hSub))
  have hAddLim :
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum H (Y + Z) T n)
        atTop
        (𝓝 (∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hAdd))) :=
    tendsto_weightedDyadicSquareVariationSum_of_continuous H hH hAdd T
  have hSubLim :
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum H (Y - Z) T n)
        atTop
        (𝓝 (∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hSub))) :=
    tendsto_weightedDyadicSquareVariationSum_of_continuous H hH hSub T
  have hlim :
      Tendsto
        (fun n ↦ dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
        atTop
        (𝓝 L) := by
    have hPolarized :
        Tendsto
          (fun n ↦
            (1 / 4 : ℝ) *
              (weightedDyadicSquareVariationSum H (Y + Z) T n -
                weightedDyadicSquareVariationSum H (Y - Z) T n))
          atTop
          (𝓝 L) := by
      -- The plus/minus weighted square-variation limits assemble into the polarized mixed limit.
      simpa [L] using (hAddLim.sub hSubLim).const_mul (1 / 4 : ℝ)
    refine hPolarized.congr' ?_
    filter_upwards with n
    -- Each dyadic mixed sum is exactly the quarter difference of the plus/minus weighted square
    -- sums.
    simpa [weightedDyadicSquareVariationSum,
      weightedPartitionQuadraticVariationApproximationUpTo_def] using
      (dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization
        H Y Z T n).symm
  -- The canonical pathwise integral is defined as the fixed-time limit of these dyadic mixed sums.
  exact pathwiseQuadraticCovariationIntegral_eq_of_tendsto H Y Z T hlim
/-- Helper for the multidimensional Itô formula: if the anchored interval masses of a measure `μ` are recorded by a
primitive `V`, then integrating the prefix indicator `1_[0,τ]` over `[0,T]` against `μ`
recovers `V τ` whenever `τ ≤ T`. -/
theorem setIntegral_indicatorIcc_eq_prefixMass
    {μ : Measure NNReal} {V : NNReal → ℝ}
    (hV : ∀ T : NNReal, ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μ = V T)
    {τ T : NNReal} (hτT : τ ≤ T) :
    ∫ s in Set.Icc 0 T,
        Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s ∂μ =
      V τ := by
  have hinter :
      Set.Icc 0 T ∩ Set.Icc 0 τ = Set.Icc 0 τ := by
    ext s
    constructor
    · intro hs
      exact hs.2
    · intro hs
      exact ⟨⟨hs.1, le_trans hs.2 hτT⟩, hs⟩
  have hinter' :
      Set.Icc 0 τ ∩ Set.Icc 0 T = Set.Icc 0 τ := by
    rw [Set.inter_comm, hinter]
  -- Proof comment: collapse the outer interval restriction with the inner prefix indicator.
  calc
    ∫ s in Set.Icc 0 T,
        Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s ∂μ
        = ∫ s, Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s ∂(μ.restrict (Set.Icc 0 T)) := by
            rfl
    _ = ∫ s in Set.Icc 0 τ, (1 : ℝ) ∂(μ.restrict (Set.Icc 0 T)) := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ s in Set.Icc 0 τ, (1 : ℝ) ∂μ := by
          simp [Measure.restrict_restrict, hinter']
    _ = V τ := hV τ
/-- Helper for the multidimensional Itô formula: once the restricted measure `μ.restrict (Set.Icc 0 T)` is finite,
integrating a constant-plus-prefix-step weight against `μ` reduces to the corresponding linear
combination of anchored primitive values. -/
theorem setIntegral_prefixStep_eq_linearCombination_of_prefixMass
    {ι : Type*} {μ : Measure NNReal} {V : NNReal → ℝ}
    (hV : ∀ T : NNReal, ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μ = V T)
    (S : Finset ι) (τ : ι → NNReal) (a : ι → ℝ) (c : ℝ)
    (T : NNReal)
    (hτ : ∀ i ∈ S, τ i ≤ T)
    (hμT : μ (Set.Icc 0 T) < ⊤) :
    ∫ s,
        (fun t ↦
          c + Finset.sum S (fun i ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) t)) s
          ∂(μ.restrict (Set.Icc 0 T)) =
      c * V T + Finset.sum S (fun i ↦ a i * V (τ i)) := by
  let ν : Measure NNReal := μ.restrict (Set.Icc 0 T)
  have hν_univ_lt_top : ν Set.univ < ⊤ := by
    simpa [ν] using hμT
  letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
  have hconst :
      Integrable (fun _ : NNReal ↦ c) ν := by
    exact integrable_const c
  have hindicator :
      ∀ i : ι,
        Integrable
          (Set.indicator (Set.Icc 0 (τ i)) (fun _ : NNReal ↦ (1 : ℝ))) ν := by
    intro i
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have htermInt :
      ∀ i ∈ S,
        Integrable
          (fun s : NNReal ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ : NNReal ↦ (1 : ℝ)) s) ν := by
    intro i hi
    exact (hindicator i).const_mul (a i)
  have hsum :
      Integrable
        (fun s : NNReal ↦
          Finset.sum S fun i ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ : NNReal ↦ (1 : ℝ)) s) ν := by
    exact integrable_finset_sum S htermInt
  have htermEval :
      ∀ i ∈ S,
        ∫ s, a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν =
          a i * V (τ i) := by
    intro i hi
    calc
      ∫ s, a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν
          =
        a i * ∫ s, Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
            rw [integral_const_mul]
      _ = a i *
            ∫ s in Set.Icc 0 T,
              Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂μ := by
            rfl
      _ = a i * V (τ i) := by
            rw [setIntegral_indicatorIcc_eq_prefixMass hV (hτ i hi)]
  -- Proof comment: expand the prefix-step weight into its constant part and finitely many
  -- prefix indicators, then integrate termwise and rewrite each interval mass via `V`.
  calc
    ∫ s,
        (fun t ↦
          c + Finset.sum S (fun i ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) t)) s
          ∂ν
        =
      ∫ s, (fun _ : NNReal ↦ c) s ∂ν +
        ∫ s,
          Finset.sum S fun i ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
            change
              ∫ s,
                ((fun _ : NNReal ↦ c) s +
                  Finset.sum S fun i ↦
                    a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s) ∂ν =
                _ + _
            rw [integral_add hconst hsum]
    _ = c * V T +
          ∫ s,
            Finset.sum S fun i ↦
              a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
            simpa [ν] using
              congrArg
                (fun r : ℝ ↦
                  r +
                    ∫ s,
                      Finset.sum S fun i ↦
                        a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν)
                (by simpa [smul_eq_mul, mul_comm] using congrArg (fun r : ℝ ↦ c * r) (hV T))
    _ = c * V T + Finset.sum S fun i ↦
          ∫ s, a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
            rw [integral_finset_sum _ htermInt]
    _ = c * V T + Finset.sum S (fun i ↦ a i * V (τ i)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact htermEval i hi
/-- Helper for the multidimensional Itô formula: if the restricted measure `μ.restrict (Set.Icc 0 T)` is finite,
then integrating the canonical dyadic staircase `coarseIccStep w m T` against `μ` reduces to the
same finite linear combination of anchored primitive values that appears in Remark 21.62. -/
theorem setIntegral_coarseIccStep_eq_linearCombination_of_prefixMass
    {μ : Measure NNReal} {V : NNReal → ℝ}
    (hV : ∀ T : NNReal, ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μ = V T)
    (w : NNReal → ℝ) (m : ℕ) (T : NNReal)
    (hμT : μ (Set.Icc 0 T) < ⊤) :
    ∫ s in Set.Icc 0 T, coarseIccStep w m T s ∂μ =
      w (Definition2158.dyadicPartitionSequence m
            (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) * V T +
        Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
          fun i ↦
            (w (Definition2158.dyadicPartitionSequence m i) -
                w (Definition2158.dyadicPartitionSequence m (i + 1))) *
              V (Definition2158.dyadicPartitionSequence m (i + 1)) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P m T
  let cLast : ℝ := w (P m (N - 1))
  let coeff : ℕ → ℝ := fun i ↦ w (P m i) - w (P m (i + 1))
  have hτ :
      ∀ i ∈ Finset.range (N - 1), P m (i + 1) ≤ T := by
    intro i hi
    have hi_lt : i < N - 1 := Finset.mem_range.mp hi
    have hi_succ_lt : i + 1 < (N - 1) + 1 := Nat.succ_lt_succ hi_lt
    have hN : 0 < N := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ i)
        (le_trans (Nat.succ_le_of_lt hi_lt) (Nat.sub_le _ _))
    have hN_eq : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hN)
    have hi' : i + 1 < N := by
      simpa [hN_eq] using hi_succ_lt
    exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex m hi')
  -- Proof comment: `coarseIccStep` is exactly the finite prefix-step integrand already handled
  -- by the previous lemma.
  simpa [coarseIccStep, P, N, cLast, coeff] using
    setIntegral_prefixStep_eq_linearCombination_of_prefixMass
      (hV := hV)
      (S := Finset.range (N - 1))
      (τ := fun i ↦ P m (i + 1))
      (a := coeff)
      (c := cLast)
      T hτ hμT
/-- Helper for the multidimensional Itô formula: at each dyadic level, the quarter difference of the two
coarse-step polarization integrals already reduces to the same finite linear combination of the
mixed primitive `S ↦ ∫_0^S a_{i,j}`. -/
theorem coarseIccStep_weightedPolarization_eq_linearCombination_of_mixedPrimitive
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    (H : NNReal → ℝ)
    {μAdd μSub : Measure NNReal}
    (hμAdd :
      ∀ T : NNReal,
        ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μAdd =
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hμSub :
      ∀ T : NNReal,
        ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μSub =
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hμAddFinite : ∀ T : NNReal, μAdd (Set.Icc 0 T) < ⊤)
    (hμSubFinite : ∀ T : NNReal, μSub (Set.Icc 0 T) < ⊤)
    (T : NNReal) (m : ℕ) :
    (1 / 4 : ℝ) *
        ((∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μAdd) -
          ∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μSub) =
      H (Definition2158.dyadicPartitionSequence m
            (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) *
        (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
          Finset.sum
            (Finset.range
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
            fun k ↦
              (H (Definition2158.dyadicPartitionSequence m k) -
                  H (Definition2158.dyadicPartitionSequence m (k + 1))) *
                (∫ s in Set.Icc (0 : ℝ)
                    (Definition2158.dyadicPartitionSequence m (k + 1) : ℝ),
                  a s.toNNReal ω i j) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P m T
  let R : Finset ℕ := Finset.range (N - 1)
  let boundary : ℝ := H (P m (N - 1))
  let mixed : NNReal → ℝ :=
    fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j
  let diagAdd : NNReal → ℝ :=
    fun S ↦
      (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
        2 * mixed S +
        (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j)
  let diagSub : NNReal → ℝ :=
    fun S ↦
      (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) -
        2 * mixed S +
        (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j)
  let coeff : ℕ → ℝ := fun k ↦ H (P m k) - H (P m (k + 1))
  let addTerm : ℕ → ℝ := fun k ↦ coeff k * diagAdd (P m (k + 1))
  let subTerm : ℕ → ℝ := fun k ↦ coeff k * diagSub (P m (k + 1))
  have hAddEval :=
    setIntegral_coarseIccStep_eq_linearCombination_of_prefixMass
      (μ := μAdd)
      (V := fun S : NNReal ↦
        (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
          2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j))
      hμAdd H m T (hμAddFinite T)
  have hSubEval :=
    setIntegral_coarseIccStep_eq_linearCombination_of_prefixMass
      (μ := μSub)
      (V := fun S : NNReal ↦
        (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) -
          2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j))
      hμSub H m T (hμSubFinite T)
  have hAddEval' :
      ∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μAdd =
        boundary * diagAdd T + ∑ k ∈ R, addTerm k := by
    simpa [P, N, R, boundary, mixed, diagAdd, coeff, addTerm] using hAddEval
  have hSubEval' :
      ∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μSub =
        boundary * diagSub T + ∑ k ∈ R, subTerm k := by
    simpa [P, N, R, boundary, mixed, diagSub, coeff, subTerm] using hSubEval
  have hBoundary :
      (1 / 4 : ℝ) * (boundary * diagAdd T - boundary * diagSub T) =
        boundary * mixed T := by
    dsimp [boundary, mixed, diagAdd, diagSub]
    ring
  have hSum :
      (1 / 4 : ℝ) * ((∑ k ∈ R, addTerm k) - ∑ k ∈ R, subTerm k) =
        ∑ k ∈ R, coeff k * mixed (P m (k + 1)) := by
    calc
      (1 / 4 : ℝ) * ((∑ k ∈ R, addTerm k) - ∑ k ∈ R, subTerm k)
          = (∑ k ∈ R, (1 / 4 : ℝ) * addTerm k) - ∑ k ∈ R, (1 / 4 : ℝ) * subTerm k := by
              rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ k ∈ R, ((1 / 4 : ℝ) * addTerm k - (1 / 4 : ℝ) * subTerm k) := by
              rw [← Finset.sum_sub_distrib]
      _ = ∑ k ∈ R, coeff k * mixed (P m (k + 1)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              dsimp [addTerm, subTerm, coeff, mixed, diagAdd, diagSub]
              ring
  -- Proof comment: substitute the two coarse-step integral expansions and polarize the resulting
  -- boundary and prefix terms; only the mixed primitive survives.
  calc
    (1 / 4 : ℝ) *
        ((∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μAdd) -
          ∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μSub)
        =
      (1 / 4 : ℝ) * ((boundary * diagAdd T + ∑ k ∈ R, addTerm k) -
        (boundary * diagSub T + ∑ k ∈ R, subTerm k)) := by
          rw [hAddEval', hSubEval']
    _ =
      (1 / 4 : ℝ) * (boundary * diagAdd T - boundary * diagSub T) +
        (1 / 4 : ℝ) * ((∑ k ∈ R, addTerm k) - ∑ k ∈ R, subTerm k) := by
          ring
    _ = boundary * mixed T + (1 / 4 : ℝ) * ((∑ k ∈ R, addTerm k) - ∑ k ∈ R, subTerm k) := by
          rw [hBoundary]
    _ = boundary * mixed T + ∑ k ∈ R, coeff k * mixed (P m (k + 1)) := by
          rw [hSum]
    _ =
      H (Definition2158.dyadicPartitionSequence m
            (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) *
        (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
          Finset.sum
            (Finset.range
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
            fun k ↦
              (H (Definition2158.dyadicPartitionSequence m k) -
                  H (Definition2158.dyadicPartitionSequence m (k + 1))) *
                (∫ s in Set.Icc (0 : ℝ)
                    (Definition2158.dyadicPartitionSequence m (k + 1) : ℝ),
                  a s.toNNReal ω i j) := by
          simp [P, N, R, boundary, mixed, coeff]
/-- Helper for the multidimensional Itô formula: truncating a density to a fixed interval upgrades one
`IntegrableOn` hypothesis on that interval to local integrability on the whole line. -/
theorem locallyIntegrable_indicator_Icc_of_integrableOn
    {f : ℝ → ℝ} {T : NNReal}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) (T : ℝ))) :
    LocallyIntegrable (Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f) volume := by
  let A : Set ℝ := Set.Icc (0 : ℝ) (T : ℝ)
  rw [locallyIntegrable_iff]
  intro K hK
  have hInside :
      IntegrableOn (Set.indicator A f) (K ∩ A) := by
    -- Proof comment: inside the truncation interval the indicator recovers the original density.
    refine (hf.mono_set ?_).congr_fun ?_ (hK.isClosed.measurableSet.inter measurableSet_Icc)
    · intro s hs
      exact hs.2
    · intro s hs
      simp [A, Set.indicator_of_mem hs.2]
  have hOutside :
      IntegrableOn (Set.indicator A f) (K \ A) := by
    -- Proof comment: outside the truncation interval the indicator vanishes identically.
    refine integrableOn_zero.congr_fun ?_ (hK.isClosed.measurableSet.diff measurableSet_Icc)
    intro s hs
    simp [A, hs.2]
  have hUnion : (K ∩ A) ∪ (K \ A) = K := by
    ext s
    by_cases hsA : s ∈ A
    · simp [A, hsA]
    · simp [A, hsA]
  -- Proof comment: split the compact set into the inside and outside pieces of the truncation.
  simpa [hUnion] using hInside.union hOutside
/-- Helper for the multidimensional Itô formula: on a prefix interval `[0,x] ⊆ [0,T]`, the indefinite integral of the
truncated density agrees with the original prefix integral. -/
theorem indefiniteIntegralPath_indicatorIcc_apply
    {f : ℝ → ℝ} {T x : NNReal}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) (T : ℝ))) (hx : x ≤ T) :
    indefiniteIntegralPath (Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f) x =
      ∫ s in Set.Icc (0 : ℝ) (x : ℝ), f s := by
  let densityT : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f
  have hdensityLoc : LocallyIntegrable densityT volume :=
    locallyIntegrable_indicator_Icc_of_integrableOn hf
  -- Proof comment: the truncated primitive is computed by the usual interval integral, and on
  -- `[0, x]` the indicator is identically `1`.
  rw [indefiniteIntegralPath_apply_of_locallyIntegrable hdensityLoc]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (x : ℝ) by exact_mod_cast x.2)]
  rw [integral_Icc_eq_integral_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsT : s ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
    ⟨le_of_lt hs.1, hs.2.trans (by exact_mod_cast hx)⟩
  simp [densityT, Set.indicator_of_mem hsT]
/-- Helper for Theorem 25.33: a bundled primitive path built from a locally integrable density
evaluates to the source interval integral on every nonnegative horizon. -/
theorem polarizationPrimitivePath_apply
    {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (T : NNReal) :
    indefiniteIntegralPath f T =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s := by
  -- Proof comment: first unfold the bundled primitive to the usual interval integral on
  -- `(0, T)`, then switch to the closed interval because the horizon is nonnegative.
  rw [indefiniteIntegralPath_apply_of_locallyIntegrable hf]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (T : ℝ) by exact_mod_cast T.2)]
  rw [integral_Icc_eq_integral_Ioc]
/-- Helper for Theorem 25.33: a square-variation witness given by the raw interval primitive of a
locally integrable density can be rebundled as the canonical path `indefiniteIntegralPath f`. -/
theorem hasSquareVariationAlong_indefiniteIntegralPath_of_intervalIntegral
    {G : C(NNReal, ℝ)} {f : ℝ → ℝ}
    (hSq :
      HasSquareVariationAlong
        G
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s))
    (hf : LocallyIntegrable f volume) :
    HasSquareVariationAlong G (indefiniteIntegralPath f) := by
  intro T
  -- Proof comment: the convergence target is unchanged after rewriting the bundled primitive by
  -- its interval-integral formula.
  simpa [polarizationPrimitivePath_apply hf T] using hSq T

/-- Helper for Theorem 25.33: the canonical Stieltjes measure of a bundled primitive path records
the same interval masses as the underlying source interval integral. -/
theorem squareVariationStieltjesMeasure_mass_eq_intervalIntegral_of_indefiniteIntegralPath
    {G : C(NNReal, ℝ)} {f : ℝ → ℝ}
    (hSq : HasSquareVariationAlong G (indefiniteIntegralPath f))
    (hf : LocallyIntegrable f volume)
    (T : NNReal) :
    ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂(squareVariationStieltjesMeasure hSq) =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s := by
  -- Proof comment: first identify the Stieltjes mass with the bundled primitive path, then unfold
  -- that primitive back to the source interval integral.
  calc
    ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂(squareVariationStieltjesMeasure hSq)
        = indefiniteIntegralPath f T := by
          symm
          exact squareVariationStieltjesMeasure_realizes_path hSq T
    _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s :=
      polarizationPrimitivePath_apply hf T
/-- Helper for Theorem 25.33: if the three matrix entries used in a polarization density are
integrable on every natural horizon, then the resulting density is locally integrable on `ℝ`. -/
theorem polarizationDensityLocallyIntegrable_of_natHorizons
    {a : MatrixProcess} {ω : Ω} (i j : Fin d) (c : ℝ)
    (hii :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hij :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hjj :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (n : ℝ))) :
    LocallyIntegrable
      (fun s : ℝ ↦ a s.toNNReal ω i i + c * a s.toNNReal ω i j + a s.toNNReal ω j j)
      volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let density : ℝ → ℝ := fun s ↦
    a s.toNNReal ω i i + c * a s.toNNReal ω i j + a s.toNNReal ω j j
  have hKMeas : MeasurableSet K := hK.isClosed.measurableSet
  have hSplit :
      K = (K ∩ Set.Iio (0 : ℝ)) ∪ (K ∩ Set.Ici (0 : ℝ)) := by
    ext x
    constructor
    · intro hx
      by_cases hxneg : x < 0
      · exact Or.inl ⟨hx, hxneg⟩
      · exact Or.inr ⟨hx, le_of_not_gt hxneg⟩
    · intro hx
      exact hx.elim (fun hx' ↦ hx'.1) fun hx' ↦ hx'.1
  let density0 : ℝ := a 0 ω i i + c * a 0 ω i j + a 0 ω j j
  have hNegEq :
      Set.EqOn density (fun _ : ℝ ↦ density0) (K ∩ Set.Iio (0 : ℝ)) := by
    intro s hs
    have hs0 : s.toNNReal = (0 : NNReal) := by
      simp [Real.toNNReal_of_nonpos hs.2.le]
    simp [density, density0, hs0]
  have hNeg :
      IntegrableOn density (K ∩ Set.Iio (0 : ℝ)) := by
    -- Proof comment: on the negative half-line the polarization density is constant because
    -- `Real.toNNReal` collapses to `0`.
    exact
      (integrableOn_congr_fun hNegEq (hKMeas.inter measurableSet_Iio)).2 <|
        integrableOn_const
          (((measure_mono (by
            intro s hs
            exact hs.1)).trans_lt hK.measure_lt_top).ne)
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  let R : ℝ := max R0 1
  have hR :
      ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have hxBall : x ∈ Metric.closedBall (0 : ℝ) R0 := hR0 hx
    have hxR0 : ‖x‖ ≤ R0 := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxBall
    exact hxR0.trans (le_max_left _ _)
  let N : ℕ := Nat.ceil R
  have hSubset :
      K ∩ Set.Ici (0 : ℝ) ⊆ Set.Icc (0 : ℝ) (N : ℝ) := by
    intro x hx
    constructor
    · exact hx.2
    · have hxR : x ≤ R := by
        exact le_trans (le_abs_self x) (hR x hx.1)
      exact le_trans hxR (Nat.le_ceil R)
  have hNonnegIcc :
      IntegrableOn density (Set.Icc (0 : ℝ) (N : ℝ)) := by
    -- Proof comment: on a natural horizon, the density is a finite linear combination of the
    -- three supplied entrywise integrable coefficients.
    have hDensityN :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i + c * a s.toNNReal ω i j + a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (N : ℝ)) := by
      simpa [add_assoc] using
        (hii N).add (((hij N).const_mul c).add (hjj N))
    simpa [density] using hDensityN
  have hNonneg :
      IntegrableOn density (K ∩ Set.Ici (0 : ℝ)) := by
    exact hNonnegIcc.mono_set hSubset
  -- Proof comment: combine the constant negative half-line piece and the natural-horizon
  -- positive piece.
  exact hSplit.symm ▸ hNeg.union hNonneg
/-- Helper for the multidimensional Itô formula: discrete summation by parts on `Finset.range` rewrites a weighted
adjacent-difference sum into its terminal boundary term plus the preceding prefix values. -/
theorem sum_range_mul_sub_eq_terminal_add
    (b u : ℕ → ℝ) (n : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun k ↦ b k * (u (k + 1) - u k)) =
      b n * u (n + 1) +
        Finset.sum (Finset.range n) (fun k ↦ (b k - b (k + 1)) * u (k + 1)) -
          b 0 * u 0 := by
  induction n with
  | zero =>
      -- Proof comment: for a single summand, the identity is the endpoint difference formula.
      simp
      ring
  | succ n ih =>
      -- Proof comment: separate the last summand, apply the induction hypothesis to the prefix,
      -- and then regroup the new boundary term into the extended telescoping sum.
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
/-- Helper for the multidimensional Itô formula: the dyadic partition approximation against the truncated primitive
`indefiniteIntegralPath (Set.indicator (Set.Icc 0 T) f)` already has the same boundary-plus-prefix
normal form as the coarse-step polarization identity. -/
theorem partitionPathwiseItoApproximationUpTo_indicatorIcc_eq_linearCombination_of_prefixIntegral
    (H : NNReal → ℝ) {f : ℝ → ℝ} (T : NNReal)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) (T : ℝ))) (m : ℕ) :
    partitionPathwiseItoApproximationUpTo
        H
        (indefiniteIntegralPath (Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f))
        dyadicPartitionSequence
        T
        m
      =
    H (Definition2158.dyadicPartitionSequence m
          (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) *
      (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s) +
        Finset.sum
          (Finset.range
            (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
          fun k ↦
            (H (Definition2158.dyadicPartitionSequence m k) -
                H (Definition2158.dyadicPartitionSequence m (k + 1))) *
              (∫ s in Set.Icc (0 : ℝ)
                  (Definition2158.dyadicPartitionSequence m (k + 1) : ℝ),
                f s) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P m T
  by_cases hN : N = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P m 0 := by
        simpa [N, hN] using le_partitionBoundIndex_time P m T
      simpa [P, Definition2158.dyadicPartitionSequence] using hle
    have hP0 : P m 0 = 0 := by
      simp [P, Definition2158.dyadicPartitionSequence]
    -- Proof comment: when no dyadic interval contributes, the horizon is `0`, so both the
    -- partition sum and the boundary-prefix normal form vanish.
    subst hT0
    simpa [partitionPathwiseItoApproximationUpTo, P, N, hN, hP0]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let u : ℕ → ℝ := fun k ↦
      if hk : k = N then
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s
      else
        ∫ s in Set.Icc (0 : ℝ) (P m k : ℝ), f s
    have hrewrite :
        partitionPathwiseItoApproximationUpTo
            H
            (indefiniteIntegralPath (Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f))
            dyadicPartitionSequence
            T
            m
          =
        Finset.sum (Finset.range N) fun k ↦
          H (P m k) * (u (k + 1) - u k) := by
      -- Proof comment: rewrite each truncated primitive increment either as the next dyadic
      -- prefix integral or, for the final clipped cell, as the terminal integral up to `T`.
      rw [partitionPathwiseItoApproximationUpTo]
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk_lt : k < N := Finset.mem_range.mp hk
      have hk_leT : P m k ≤ T := le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex m hk_lt)
      have hk_neN : k ≠ N := Nat.ne_of_lt hk_lt
      by_cases hlast : k + 1 = N
      · have hnext : partitionNextPointUpTo P m k T = T := by
          rw [partitionNextPointUpTo, min_eq_right]
          simpa [hlast] using le_partitionBoundIndex_time P m T
        rw [hnext]
        rw [indefiniteIntegralPath_indicatorIcc_apply (f := f) (T := T) (x := T) hf le_rfl]
        rw [indefiniteIntegralPath_indicatorIcc_apply (f := f) (T := T) (x := P m k) hf hk_leT]
        -- Proof comment: the last increment is exactly the terminal integral minus the previous
        -- dyadic prefix value.
        simp [u, hlast, hk_neN]
        left
        rfl
      · have hk_succ_lt : k + 1 < N := lt_of_le_of_ne (Nat.succ_le_of_lt hk_lt) hlast
        have hk_succ_leT : P m (k + 1) ≤ T :=
          le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex m hk_succ_lt)
        have hnext : partitionNextPointUpTo P m k T = P m (k + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact hk_succ_leT
        rw [hnext]
        rw [indefiniteIntegralPath_indicatorIcc_apply (f := f) (T := T) (x := P m (k + 1)) hf
          hk_succ_leT]
        rw [indefiniteIntegralPath_indicatorIcc_apply (f := f) (T := T) (x := P m k) hf hk_leT]
        -- Proof comment: before the terminal cell, truncation is inactive and the increment is
        -- the difference of two consecutive dyadic prefix integrals.
        simp [u, Nat.ne_of_lt hk_succ_lt, hk_neN]
        left
        rfl
    have hNsucc : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hNpos)
    have hP0 : P m 0 = 0 := by
      simp [P, Definition2158.dyadicPartitionSequence]
    -- Proof comment: after rewriting the partition sum in terms of prefix primitives, summation
    -- by parts produces the exact boundary-plus-prefix normal form used on the measure side.
    rw [hrewrite, ← hNsucc, sum_range_mul_sub_eq_terminal_add]
    have hsum :
        (∑ k ∈ Finset.range (N - 1),
            (H (P m k) - H (P m (k + 1))) * u (k + 1)) =
          ∑ k ∈ Finset.range (N - 1),
            (H (P m k) - H (P m (k + 1))) *
              ∫ s in Set.Icc (0 : ℝ) (P m (k + 1) : ℝ), f s := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk_lt : k < N - 1 := Finset.mem_range.mp hk
      have hk_succ_lt : k + 1 < N := by
        simpa [hNsucc] using Nat.succ_lt_succ hk_lt
      simp [u, Nat.ne_of_lt hk_succ_lt]
    rw [hsum]
    simp [u, P, N, hNsucc, hP0, Nat.ne_of_lt hNpos]

/-- Helper for the multidimensional Itô formula: integrating the dyadic coarse staircase against a
compact-horizon density produces the same boundary-plus-prefix linear combination as the finite
polarization measure identity. -/
theorem coarseIccStep_intervalIntegral_eq_linearCombination_of_prefixIntegral
    (H : NNReal → ℝ) {f : ℝ → ℝ} (T : NNReal)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) (T : ℝ))) (m : ℕ) :
    ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s * coarseIccStep H m T s.toNNReal =
      H (Definition2158.dyadicPartitionSequence m
            (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) *
        (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s) +
          Finset.sum
            (Finset.range
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
            fun k ↦
              (H (Definition2158.dyadicPartitionSequence m k) -
                  H (Definition2158.dyadicPartitionSequence m (k + 1))) *
                (∫ s in Set.Icc (0 : ℝ)
                    (Definition2158.dyadicPartitionSequence m (k + 1) : ℝ),
                  f s) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P m T
  let ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) (T : ℝ))
  let cLast : ℝ := H (P m (N - 1))
  let coeff : ℕ → ℝ := fun i ↦ H (P m i) - H (P m (i + 1))
  have hfi : Integrable f ν := by
    simpa [IntegrableOn, ν] using hf
  have hconst :
      Integrable (fun s : ℝ ↦ f s * cLast) ν := by
    simpa [mul_comm] using hfi.const_mul cLast
  have htermInt :
      ∀ i ∈ Finset.range (N - 1),
        Integrable
          (fun s : ℝ ↦
            f s *
              (coeff i *
                Set.indicator
                  (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s))
          ν := by
    intro i hi
    let A : Set ℝ := Set.Icc (0 : ℝ) (P m (i + 1) : ℝ)
    have hEq :
        (fun s : ℝ ↦
          f s *
            (coeff i *
              Set.indicator
                (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                (fun _ ↦ (1 : ℝ)) s))
          =
        fun s : ℝ ↦ coeff i * Set.indicator A f s := by
      funext s
      by_cases hsA : s ∈ A
      · simp [A, hsA, mul_assoc, mul_left_comm, mul_comm]
      · simp [A, hsA]
    rw [hEq]
    simpa [A] using ((hfi.indicator measurableSet_Icc).const_mul (coeff i))
  have hsum :
      Integrable
        (fun s : ℝ ↦
          Finset.sum (Finset.range (N - 1)) fun i ↦
            f s *
              (coeff i *
                Set.indicator
                  (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s))
        ν := by
    exact integrable_finset_sum _ htermInt
  have hτ :
      ∀ i ∈ Finset.range (N - 1), (P m (i + 1) : ℝ) ≤ T := by
    intro i hi
    have hi_lt : i < N - 1 := Finset.mem_range.mp hi
    have hi_succ_lt : i + 1 < (N - 1) + 1 := Nat.succ_lt_succ hi_lt
    have hNpos : 0 < N := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ i)
        (le_trans (Nat.succ_le_of_lt hi_lt) (Nat.sub_le _ _))
    have hNsucc : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hNpos)
    have hi' : i + 1 < N := by
      simpa [hNsucc] using hi_succ_lt
    exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex m hi')
  have htermEval :
      ∀ i ∈ Finset.range (N - 1),
        ∫ s,
            f s *
              (coeff i *
                Set.indicator
                  (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s) ∂ν =
          coeff i * ∫ s in Set.Icc (0 : ℝ) (P m (i + 1) : ℝ), f s := by
    intro i hi
    let A : Set ℝ := Set.Icc (0 : ℝ) (P m (i + 1) : ℝ)
    have hsubset : A ⊆ Set.Icc (0 : ℝ) (T : ℝ) := by
      intro s hs
      exact ⟨hs.1, hs.2.trans (hτ i hi)⟩
    calc
      ∫ s,
          f s *
            (coeff i *
              Set.indicator
                (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                (fun _ ↦ (1 : ℝ)) s) ∂ν
          =
        coeff i * ∫ s, Set.indicator A f s ∂ν := by
            have hEq :
                (fun s : ℝ ↦
                  f s *
                    (coeff i *
                      Set.indicator
                        (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                        (fun _ ↦ (1 : ℝ)) s))
                  =
                fun s : ℝ ↦ coeff i * Set.indicator A f s := by
              funext s
              by_cases hsA : s ∈ A
              · simp [A, hsA, mul_assoc, mul_left_comm, mul_comm]
              · simp [A, hsA]
            rw [hEq, integral_const_mul]
      _ = coeff i * ∫ s in A, f s ∂ν := by
            rw [MeasureTheory.integral_indicator measurableSet_Icc]
      _ = coeff i * ∫ s in A, f s := by
            congr 1
            simp [ν, A, Measure.restrict_restrict_of_subset hsubset]
      _ = coeff i * ∫ s in Set.Icc (0 : ℝ) (P m (i + 1) : ℝ), f s := by
            rfl
  have hEqOn :
      ∀ s ∈ Set.Icc (0 : ℝ) (T : ℝ),
        cLast +
            (Finset.sum (Finset.range (N - 1)) fun i ↦
              coeff i *
                Set.indicator
                  (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s)
          =
        coarseIccStep H m T s.toNNReal := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    unfold coarseIccStep
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hmem :
        s ∈ Set.Icc (0 : ℝ) (P m (i + 1) : ℝ) ↔
          s.toNNReal ∈ Set.Icc 0 (P m (i + 1)) := by
      constructor
      · intro hsIcc
        refine ⟨bot_le, ?_⟩
        have hs_le : (s.toNNReal : ℝ) ≤ (P m (i + 1) : ℝ) := by
          simpa [Real.toNNReal_of_nonneg hsIcc.1] using hsIcc.2
        exact_mod_cast hs_le
      · intro hsIcc
        refine ⟨hs0, ?_⟩
        have hs_le : (s.toNNReal : ℝ) ≤ (P m (i + 1) : ℝ) := by
          exact_mod_cast hsIcc.2
        simpa [Real.toNNReal_of_nonneg hs0] using hs_le
    by_cases hsIccNN : s.toNNReal ∈ Set.Icc 0 (P m (i + 1))
    · have hsIcc : s ∈ Set.Icc (0 : ℝ) (P m (i + 1) : ℝ) := hmem.mpr hsIccNN
      simpa [coeff, P, hsIcc, hsIccNN]
    · have hsIcc : s ∉ Set.Icc (0 : ℝ) (P m (i + 1) : ℝ) := by
        intro hs'
        exact hsIccNN (hmem.mp hs')
      simpa [coeff, P, hsIcc, hsIccNN]
  -- Proof comment: expand the coarse staircase into its constant part and prefix indicators on
  -- `[0,T]`, integrate termwise on the restricted measure, and evaluate each indicator integral
  -- as the corresponding prefix integral of `f`.
  calc
    ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s * coarseIccStep H m T s.toNNReal
        = ∫ s, f s *
            (cLast +
              Finset.sum (Finset.range (N - 1)) fun i ↦
                coeff i *
                  Set.indicator
                    (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                    (fun _ ↦ (1 : ℝ)) s) ∂ν := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
            rw [hEqOn s hs]
    _ =
        ∫ s, f s * cLast ∂ν +
          ∫ s,
            Finset.sum (Finset.range (N - 1)) fun i ↦
              f s *
                (coeff i *
                  Set.indicator
                    (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                    (fun _ ↦ (1 : ℝ)) s) ∂ν := by
            have hsplit :
                (fun s : ℝ ↦
                  f s *
                    (cLast +
                      Finset.sum (Finset.range (N - 1)) fun i ↦
                        coeff i *
                          Set.indicator
                            (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                            (fun _ ↦ (1 : ℝ)) s))
                  =
                (fun s : ℝ ↦ f s * cLast) +
                  fun s : ℝ ↦
                    Finset.sum (Finset.range (N - 1)) fun i ↦
                      f s *
                        (coeff i *
                          Set.indicator
                            (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                            (fun _ ↦ (1 : ℝ)) s) := by
              funext s
              simp [mul_add, Finset.mul_sum]
            simpa [hsplit] using integral_add hconst hsum
    _ =
        cLast * ∫ s, f s ∂ν +
          ∫ s,
            Finset.sum (Finset.range (N - 1)) fun i ↦
              f s *
                (coeff i *
                  Set.indicator
                    (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                    (fun _ ↦ (1 : ℝ)) s) ∂ν := by
          congr 1
          simpa [mul_comm] using
            (integral_const_mul cLast (f := fun s : ℝ ↦ f s) (μ := ν))
    _ =
        cLast * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s) +
          ∫ s,
            Finset.sum (Finset.range (N - 1)) fun i ↦
              f s *
                (coeff i *
                  Set.indicator
                    (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                    (fun _ ↦ (1 : ℝ)) s) ∂ν := by
          have hνInt : ∫ s, f s ∂ν = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s := by
            simp [ν]
          rw [hνInt]
    _ =
        cLast * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s) +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            ∫ s,
              f s *
                (coeff i *
                  Set.indicator
                    (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                    (fun _ ↦ (1 : ℝ)) s) ∂ν := by
          rw [integral_finset_sum _ htermInt]
    _ =
        cLast * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s) +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i * ∫ s in Set.Icc (0 : ℝ) (P m (i + 1) : ℝ), f s := by
          have hsumEq :
              (∑ i ∈ Finset.range (N - 1),
                  ∫ s,
                    f s *
                      (coeff i *
                        Set.indicator
                          (Set.Icc (0 : ℝ) (P m (i + 1) : ℝ))
                          (fun _ ↦ (1 : ℝ)) s) ∂ν) =
                ∑ i ∈ Finset.range (N - 1),
                  coeff i * ∫ s in Set.Icc (0 : ℝ) (P m (i + 1) : ℝ), f s := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact htermEval i hi
          rw [hsumEq]
    _ =
        H (Definition2158.dyadicPartitionSequence m
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) *
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s) +
            Finset.sum
              (Finset.range
                (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
              fun k ↦
                (H (Definition2158.dyadicPartitionSequence m k) -
                    H (Definition2158.dyadicPartitionSequence m (k + 1))) *
                  (∫ s in Set.Icc (0 : ℝ)
                      (Definition2158.dyadicPartitionSequence m (k + 1) : ℝ),
                    f s) := by
          dsimp [cLast, coeff, N, P]

/-- Helper for the multidimensional Itô formula: for a continuous weight and an integrable compact
horizon density, the dyadic coarse weighted interval integrals converge to the textbook weighted
interval integral. -/
theorem tendsto_intervalIntegral_mul_coarseIccStep_of_continuous
    (H : NNReal → ℝ) (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    {f : ℝ → ℝ} {T : NNReal}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) (T : ℝ))) :
    Tendsto
      (fun m : ℕ ↦
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s * coarseIccStep H m T s.toNNReal)
      atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s * H s.toNNReal)) := by
  let ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) (T : ℝ))
  have hHNN : Continuous H := by
    convert hH.comp NNReal.continuous_coe using 1
    ext s
    simp
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u ∈ Set.Icc (0 : NNReal) T, ‖H u‖ ≤ C :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
      hHNN.continuousOn
  have hbound :
      ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : NNReal) T, |coarseIccStep H n T s| ≤ C := by
    intro n s hs
    have hpred_mem :
        partitionPredecessorPoint n s ∈ Set.Icc (0 : NNReal) T := by
      exact ⟨bot_le, le_trans (partitionPredecessorPoint_le_time n s) hs.2⟩
    rw [coarseIccStep_eq_partitionPredecessorValue H n T s hs]
    simpa [Real.norm_eq_abs] using hC _ hpred_mem
  have hmeasCoarse : ∀ m : ℕ, Measurable (coarseIccStep H m T) := by
    intro m
    unfold coarseIccStep
    refine measurable_const.add ?_
    refine Finset.measurable_sum _ ?_
    intro i hi
    exact measurable_const.mul (measurable_const.indicator measurableSet_Icc)
  have hfi : Integrable f ν := by
    simpa [IntegrableOn, ν] using hf
  have hmeas :
      ∀ m : ℕ,
        AEStronglyMeasurable
          (fun s : ℝ ↦ f s * coarseIccStep H m T s.toNNReal) ν := by
    intro m
    exact hfi.aestronglyMeasurable.mul
      (Measurable.aestronglyMeasurable
        ((hmeasCoarse m).comp measurable_real_toNNReal))
  let boundFn : ℝ → ℝ := fun s ↦ C * |f s|
  have hboundInt : Integrable boundFn ν := by
    simpa [boundFn, Real.norm_eq_abs, mul_comm] using (hfi.norm.const_mul C)
  have hboundAE :
      ∀ m : ℕ,
        ∀ᵐ s ∂ν,
          ‖f s * coarseIccStep H m T s.toNNReal‖ ≤ boundFn s := by
    intro m
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hsNN : s.toNNReal ∈ Set.Icc 0 T := by
      refine ⟨bot_le, ?_⟩
      have hs_le : (s.toNNReal : ℝ) ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs.1] using hs.2
      exact_mod_cast hs_le
    calc
      ‖f s * coarseIccStep H m T s.toNNReal‖
          = |f s| * |coarseIccStep H m T s.toNNReal| := by simp [Real.norm_eq_abs, abs_mul]
      _ ≤ |f s| * C := by
          exact mul_le_mul_of_nonneg_left (hbound m s.toNNReal hsNN) (abs_nonneg _)
      _ = boundFn s := by simp [boundFn, mul_comm]
  have hlimAE :
      ∀ᵐ s ∂ν,
        Tendsto
          (fun m : ℕ ↦ f s * coarseIccStep H m T s.toNNReal)
          atTop
          (𝓝 (f s * H s.toNNReal)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hsNN : s.toNNReal ∈ Set.Icc 0 T := by
      refine ⟨bot_le, ?_⟩
      have hs_le : (s.toNNReal : ℝ) ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs.1] using hs.2
      exact_mod_cast hs_le
    have hcoarse :
        Tendsto (fun n : ℕ ↦ coarseIccStep H n T s.toNNReal) atTop (𝓝 (H s.toNNReal)) := by
      have hpred :
          Tendsto (fun n : ℕ ↦ partitionPredecessorPoint n s.toNNReal) atTop (𝓝 s.toNNReal) := by
        refine Metric.tendsto_atTop.mpr ?_
        intro ε hε
        let ε' : ℝ := ε / 2
        have hε' : 0 < ε' := by
          dsimp [ε']
          linarith
        have hmesh :
            ∀ᶠ n in atTop, partitionMesh dyadicPartitionSequence n ≤ ENNReal.ofReal ε' := by
          rcases
              (ENNReal.tendsto_atTop_zero.mp
                Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
                (ENNReal.ofReal ε') (ENNReal.ofReal_pos.mpr hε') with
            ⟨N, hN⟩
          exact Filter.eventually_atTop.2 ⟨N, hN⟩
        rcases Filter.eventually_atTop.1 hmesh with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn
        have hedist :
            edist (partitionPredecessorPoint n s.toNNReal) s.toNNReal ≤ ENNReal.ofReal ε' := by
          exact (partitionPredecessorPointWithinMesh n s.toNNReal).trans (hN n hn)
        have hdist : dist (partitionPredecessorPoint n s.toNNReal) s.toNNReal ≤ ε' := by
          exact (ENNReal.ofReal_le_ofReal_iff hε'.le).mp (by simpa [edist_dist] using hedist)
        calc
          dist (partitionPredecessorPoint n s.toNNReal) s.toNNReal ≤ ε' := hdist
          _ < ε := by
            dsimp [ε']
            linarith
      refine (hHNN.continuousAt.tendsto.comp hpred).congr' ?_
      filter_upwards with n
      simpa using (coarseIccStep_eq_partitionPredecessorValue H n T s.toNNReal hsNN).symm
    exact hcoarse.const_mul (f s)
  -- Proof comment: the coarse staircases are uniformly bounded on `[0,T]`, so multiplying by the
  -- integrable density `f` still leaves a dominated-convergence argument on the restricted volume.
  simpa [ν, boundFn] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      boundFn hmeas hboundInt hboundAE hlimAE)
/-- Helper for the multidimensional Itô formula: the mixed entry `a_{i,j}` is the quarter difference of the plus/minus
polarization densities. -/
theorem mixedEntry_eq_quarterDifference
    {a : MatrixProcess} {ω : Ω} (i j : Fin d) :
    (fun s : ℝ ↦ a s.toNNReal ω i j) =
      fun s : ℝ ↦
        (((a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) -
            ((a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))) /
          4 := by
  -- Proof comment: expand the polarization difference pointwise; only the mixed entry survives.
  funext s
  ring
/-- Helper for the multidimensional Itô formula: once the plus/minus polarization densities are integrable on the
fixed horizon, the mixed entry inherits compact-horizon integrability by the quarter-difference
identity. -/
theorem mixedEntry_intervalIntegrableOnIcc_of_polarizationIntegrableOn
    {a : MatrixProcess} {ω : Ω} (i j : Fin d) (T : NNReal)
    (hAdd :
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)))
    (hSub :
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ))) :
    IntegrableOn
      (fun s : ℝ ↦ a s.toNNReal ω i j)
      (Set.Icc (0 : ℝ) (T : ℝ)) := by
  have hQuarter :
      IntegrableOn
        (fun s : ℝ ↦
          (((a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) -
              ((a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))) /
            4)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
    -- Proof comment: the quarter difference is just a constant multiple of the difference of the
    -- two polarization densities, so integrability is preserved by linearity.
    simpa [div_eq_mul_inv, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using
      (hAdd.sub hSub).const_mul ((4 : ℝ)⁻¹)
  -- Proof comment: rewrite the quarter difference back to the mixed entry.
  refine hQuarter.congr_fun ?_ measurableSet_Icc
  intro s hs
  simpa using
    (congrArg (fun g : ℝ → ℝ ↦ g s) (mixedEntry_eq_quarterDifference (a := a) (ω := ω) i j)).symm
/-- Helper for the multidimensional Itô formula: multiplying the mixed entry by the continuous weight
`s ↦ H(s.toNNReal)` preserves compact-horizon integrability once the two polarization densities
are integrable on `[0,T]`. -/
theorem mixedEntry_weightedIntegrableOnIcc_of_polarizationIntegrableOn
    {a : MatrixProcess} {ω : Ω} (i j : Fin d) (H : NNReal → ℝ) (T : NNReal)
    (hAdd :
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)))
    (hSub :
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH : Continuous fun s : ℝ ↦ H s.toNNReal) :
    IntegrableOn
      (fun s : ℝ ↦ a s.toNNReal ω i j * H s.toNNReal)
      (Set.Icc (0 : ℝ) (T : ℝ)) := by
  have hMixed :
      IntegrableOn
        (fun s : ℝ ↦ a s.toNNReal ω i j)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
    mixedEntry_intervalIntegrableOnIcc_of_polarizationIntegrableOn
      (a := a) (ω := ω) i j T hAdd hSub
  -- Proof comment: on the compact interval `[0, T]`, multiplying by a continuous weight keeps an
  -- integrable density integrable.
  exact hMixed.mul_continuousOn hH.continuousOn isCompact_Icc
/-- Helper for the multidimensional Itô formula: once the plus/minus polarization densities are integrable on the
fixed horizon, the weighted quarter difference of their interval integrals collapses to the
weighted mixed-entry integral. -/
theorem mixedEntry_weightedIntervalIntegral_eq_quarterDifference
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    (H : NNReal → ℝ) (T : NNReal)
    (hAdd :
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)))
    (hSub :
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH : Continuous fun s : ℝ ↦ H s.toNNReal) :
    (1 / 4 : ℝ) *
        ((∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            ((a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
              H s.toNNReal) -
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            ((a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
              H s.toNNReal) =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * H s.toNNReal := by
  have hAddWeighted :
      IntegrableOn
        (fun s : ℝ ↦
          ((a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
            H s.toNNReal)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact hAdd.mul_continuousOn hH.continuousOn isCompact_Icc
  have hSubWeighted :
      IntegrableOn
        (fun s : ℝ ↦
          ((a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
            H s.toNNReal)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact hSub.mul_continuousOn hH.continuousOn isCompact_Icc
  -- Proof comment: combine the two weighted polarization integrals into a single integral of
  -- their quarter difference, then simplify the integrand pointwise.
  calc
    (1 / 4 : ℝ) *
        ((∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            ((a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
              H s.toNNReal) -
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            ((a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
              H s.toNNReal)
        =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
        (1 / 4 : ℝ) *
          ((((a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
                H s.toNNReal) -
            (((a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j)) *
                H s.toNNReal)) := by
          rw [← integral_sub hAddWeighted hSubWeighted, ← integral_const_mul]
    _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * H s.toNNReal := by
          refine integral_congr_ae ?_
          filter_upwards with s
          ring
/-- Helper for the multidimensional Itô formula: the predecessor dyadic partition points converge to the evaluation
time because they remain within one dyadic mesh width and the dyadic mesh tends to zero. -/
theorem tendsto_partitionPredecessorPoint_dyadic
    (T : NNReal) :
    Tendsto (fun n : ℕ ↦ partitionPredecessorPoint n T) atTop (𝓝 T) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    linarith
  have hmesh :
      ∀ᶠ n in atTop, partitionMesh dyadicPartitionSequence n ≤ ENNReal.ofReal ε' := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal ε') (ENNReal.ofReal_pos.mpr hε') with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  rcases Filter.eventually_atTop.1 hmesh with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hedist :
      edist (partitionPredecessorPoint n T) T ≤ ENNReal.ofReal ε' := by
    exact (partitionPredecessorPointWithinMesh n T).trans (hN n hn)
  have hdist : dist (partitionPredecessorPoint n T) T ≤ ε' := by
    exact (ENNReal.ofReal_le_ofReal_iff hε'.le).mp (by simpa [edist_dist] using hedist)
  calc
    dist (partitionPredecessorPoint n T) T ≤ ε' := hdist
    _ < ε := by
      dsimp [ε']
      linarith
/-- Helper for the multidimensional Itô formula: on `[0,T]`, the dyadic coarse staircase samples the weight at a
predecessor point that converges back to the evaluation time, so the staircase converges
pointwise to the original continuous weight. -/
theorem tendsto_coarseIccStep_of_continuous
    (w : NNReal → ℝ) (hw : Continuous w)
    (T s : NNReal) (hs : s ∈ Set.Icc 0 T) :
    Tendsto (fun n : ℕ ↦ coarseIccStep w n T s) atTop (𝓝 (w s)) := by
  have hpred :
      Tendsto (fun n : ℕ ↦ partitionPredecessorPoint n s) atTop (𝓝 s) :=
    tendsto_partitionPredecessorPoint_dyadic s
  -- Proof comment: `coarseIccStep` is the weight sampled at the predecessor partition point, and
  -- those predecessor points converge back to `s`.
  refine (hw.continuousAt.tendsto.comp hpred).congr' ?_
  filter_upwards with n
  simpa using (coarseIccStep_eq_partitionPredecessorValue w n T s hs).symm
/-- Helper for Theorem 25.33: the dyadic coarse staircase is piecewise constant, hence measurable,
because it is a constant plus a finite sum of interval indicators. -/
private theorem measurable_coarseIccStep
    (w : NNReal → ℝ) (T : NNReal) (n : ℕ) :
    Measurable (coarseIccStep w n T) := by
  -- Proof comment: unfolding `coarseIccStep` leaves only constants and measurable indicators.
  unfold coarseIccStep
  refine measurable_const.add ?_
  refine Finset.measurable_sum _ ?_
  intro i hi
  exact measurable_const.mul (measurable_const.indicator measurableSet_Icc)
/-- Helper for Theorem 25.33: continuity of the weight on the compact interval `[0,T]` gives a
single absolute bound for all coarse dyadic staircase samples and for the limiting weight itself. -/
private theorem coarseIccStep_abs_le_of_continuous
    (w : NNReal → ℝ) (hw : Continuous w)
    (T : NNReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, |coarseIccStep w n T s| ≤ C) ∧
      ∀ s ∈ Set.Icc 0 T, |w s| ≤ C := by
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u ∈ Set.Icc (0 : NNReal) T, ‖w u‖ ≤ C :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
      hw.continuousOn
  have hC_nonneg : 0 ≤ C := by
    have hzero : ‖w 0‖ ≤ C := hC 0 (by simp : (0 : NNReal) ∈ Set.Icc (0 : NNReal) T)
    exact le_trans (by simp) hzero
  refine ⟨C, hC_nonneg, ?_, ?_⟩
  · intro n s hs
    have hpred_mem :
        partitionPredecessorPoint n s ∈ Set.Icc (0 : NNReal) T := by
      exact ⟨bot_le, le_trans (partitionPredecessorPoint_le_time n s) hs.2⟩
    -- Proof comment: each coarse-step value is just the predecessor-point sample of `w`.
    rw [coarseIccStep_eq_partitionPredecessorValue w n T s hs]
    simpa [Real.norm_eq_abs] using hC _ hpred_mem
  · intro s hs
    simpa [Real.norm_eq_abs] using hC s hs
/-- Helper for the multidimensional Itô formula: integrating the dyadic coarse staircase of a continuous weight
against a finite measure on `[0,T]` converges to the integral of the original weight. -/
theorem tendsto_setIntegral_coarseIccStep_of_continuous
    (w : NNReal → ℝ) (hw : Continuous w)
    {μ : Measure NNReal} (T : NNReal)
    (hμFinite : μ (Set.Icc 0 T) < ⊤) :
    Tendsto
      (fun m : ℕ ↦ ∫ s in Set.Icc 0 T, coarseIccStep w m T s ∂μ)
      atTop
      (𝓝 (∫ s in Set.Icc 0 T, w s ∂μ)) := by
  let ν : Measure NNReal := μ.restrict (Set.Icc 0 T)
  have hν_univ_lt_top : ν Set.univ < ⊤ := by
    simpa [ν] using hμFinite
  letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
  obtain ⟨C, _hC_nonneg, hbound, _hlimitBound⟩ := coarseIccStep_abs_le_of_continuous w hw T
  have hmeas :
      ∀ n : ℕ, AEStronglyMeasurable (fun s : NNReal ↦ coarseIccStep w n T s) ν := by
    intro n
    exact (measurable_coarseIccStep w T n).aestronglyMeasurable
  have hboundAE :
      ∀ n : ℕ, ∀ᵐ s ∂ν, ‖coarseIccStep w n T s‖ ≤ (fun _ : NNReal ↦ C) s := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa [Real.norm_eq_abs] using hbound n s hs
  have hlimAE :
      ∀ᵐ s ∂ν, Tendsto (fun n : ℕ ↦ coarseIccStep w n T s) atTop (𝓝 (w s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact tendsto_coarseIccStep_of_continuous w hw T s hs
  -- Proof comment: on the restricted finite measure `ν`, the coarse staircases are uniformly
  -- bounded and converge pointwise on the full support, so dominated convergence applies.
  simpa [ν] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : NNReal ↦ C) hmeas (integrable_const C) hboundAE hlimAE)
/-- Helper for the multidimensional Itô formula: mapping a measure on `NNReal` to `ℝ` along the coercion preserves
the real mass of the interval `[0,T]`. -/
theorem mapNNRealMeasureRealIccEq
    (μ : Measure NNReal) (T : NNReal) :
    (Measure.map ((↑) : NNReal → ℝ) μ).real (Set.Icc (0 : ℝ) T) =
      μ.real (Set.Icc 0 T) := by
  -- Proof comment: compute the mapped mass using the measurable embedding `NNReal → ℝ`.
  have hpre :
      ((↑) : NNReal → ℝ) ⁻¹' Set.Icc (0 : ℝ) T = Set.Icc 0 T := by
    ext x
    simp
  rw [measureReal_def, measureReal_def,
    Measure.map_apply NNReal.continuous_coe.measurable measurableSet_Icc]
  simp [hpre]
/-- Helper for the multidimensional Itô formula: integrating a real-line weight against the pushforward of a measure
on `NNReal` is the same as integrating the original `NNReal` weight on `Set.Icc 0 T`. -/
theorem setIntegral_mapCoe_eq_setIntegralIcc
    {μ : Measure NNReal} (H : NNReal → ℝ) (T : NNReal) :
    ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) μ) =
      ∫ s in Set.Icc 0 T, H s ∂μ := by
  -- Proof comment: rewrite the real-line interval integral as an unrestricted integral of an
  -- indicator, transport it across `Measure.map`, and simplify the indicator back on `NNReal`.
  calc
    ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) μ)
        =
      ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) T) (fun s ↦ H s.toNNReal) s
        ∂(Measure.map ((↑) : NNReal → ℝ) μ) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    _ =
      ∫ s : NNReal,
        Set.indicator (Set.Icc (0 : ℝ) T) (fun s ↦ H s.toNNReal) (s : ℝ) ∂μ := by
          rw [NNReal.isClosedEmbedding_coe.integral_map]
    _ = ∫ s : NNReal, Set.indicator (Set.Icc 0 T) H s ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with s
          by_cases hsT : s ≤ T
          · simp [Set.indicator, hsT]
          · simp [Set.indicator, hsT]
    _ = ∫ s in Set.Icc 0 T, H s ∂μ := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
/-- Helper for the multidimensional Itô formula: the missing source-faithful side condition is compact-horizon
integrability of the positive polarization densities. Once that is included alongside the
square-variation witnesses of the sum and difference paths, these are exactly the required
integrability statements. -/
theorem polarizationDensities_intervalIntegrableOnIcc_of_squareVariationWitnesses
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    {Yi Yj : C(NNReal, ℝ)}
    (hAdd :
      HasSquareVariationAlong
        (Yi + Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)))
    (hSub :
      HasSquareVariationAlong
        (Yi - Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)))
    (hPolarInt :
      ∀ T : NNReal,
        IntegrableOn
          (fun s : ℝ ↦
            (a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
          (Set.Icc (0 : ℝ) (T : ℝ)) ∧
          IntegrableOn
            (fun s : ℝ ↦
              (a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
            (Set.Icc (0 : ℝ) (T : ℝ)))
    (T : NNReal) :
    IntegrableOn
      (fun s : ℝ ↦
        (a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
      (Set.Icc (0 : ℝ) (T : ℝ)) ∧
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
  -- Proof comment: the square-variation witnesses are bookkeeping here; the compact-horizon
  -- polarization integrability is exactly the supplied side condition.
  exact hPolarInt T
/-- Helper for the multidimensional Itô formula: once the plus/minus square-variation witnesses provide
the source-faithful compact-horizon integrability of the positive polarization densities, the
mixed entry inherits integrability by the quarter-difference identity. -/
theorem mixedEntry_intervalIntegrableOnIcc_of_polarizationSquareVariation
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    {Yi Yj : C(NNReal, ℝ)}
    (hAdd :
      HasSquareVariationAlong
        (Yi + Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)))
    (hSub :
      HasSquareVariationAlong
        (Yi - Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)))
    (hPolarInt :
      ∀ T : NNReal,
        IntegrableOn
          (fun s : ℝ ↦
            (a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
          (Set.Icc (0 : ℝ) (T : ℝ)) ∧
          IntegrableOn
            (fun s : ℝ ↦
              (a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
            (Set.Icc (0 : ℝ) (T : ℝ)))
    (T : NNReal) :
    IntegrableOn
      (fun s : ℝ ↦ a s.toNNReal ω i j)
      (Set.Icc (0 : ℝ) (T : ℝ)) := by
  have hPolarT :
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) + 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)) ∧
      IntegrableOn
        (fun s : ℝ ↦
          (a s.toNNReal ω i i) - 2 * (a s.toNNReal ω i j) + (a s.toNNReal ω j j))
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
    polarizationDensities_intervalIntegrableOnIcc_of_squareVariationWitnesses
      (a := a) (ω := ω) i j hAdd hSub hPolarInt T
  -- Proof comment: once both polarization densities are integrable on `[0, T]`, the mixed entry
  -- follows from the quarter-difference identity.
  exact
    mixedEntry_intervalIntegrableOnIcc_of_polarizationIntegrableOn
      (a := a) (ω := ω) i j T hPolarT.1 hPolarT.2
/-- Helper for the multidimensional Itô formula: the quarter difference of the two weighted polarization measures
reduces to the textbook weighted interval integral against `a_{i,j}` once that mixed density is
integrable on the fixed compact horizon. -/
theorem weightedPolarizationDifference_eq_intervalIntegral
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    (H : NNReal → ℝ)
    {Yi Yj : C(NNReal, ℝ)}
    {μAdd μSub : Measure NNReal}
    (hAddSq :
      HasSquareVariationAlong
        (Yi + Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)))
    (hSubSq :
      HasSquareVariationAlong
        (Yi - Yj)
        (fun T ↦
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j)))
    (hμAdd :
      ∀ T : NNReal,
        ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μAdd =
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hμSub :
      ∀ T : NNReal,
        ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μSub =
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hμAddFinite : ∀ T : NNReal, μAdd (Set.Icc 0 T) < ⊤)
    (hμSubFinite : ∀ T : NNReal, μSub (Set.Icc 0 T) < ⊤)
    (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    (T : NNReal)
    (hMixedInt :
      IntegrableOn
        (fun s : ℝ ↦ a s.toNNReal ω i j)
        (Set.Icc (0 : ℝ) (T : ℝ))) :
    (1 / 4 : ℝ) *
        ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
          ∫ s in Set.Icc 0 T, H s ∂μSub) =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * H s.toNNReal := by
  have hHNN : Continuous H := by
    convert hH.comp NNReal.continuous_coe using 1
    ext s
    simp
  let seqMeasure : ℕ → ℝ := fun m ↦
    (1 / 4 : ℝ) *
      ((∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μAdd) -
        ∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μSub)
  let seqInterval : ℕ → ℝ := fun m ↦
    ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * coarseIccStep H m T s.toNNReal
  have hseqEq : ∀ m : ℕ, seqMeasure m = seqInterval m := by
    intro m
    -- Proof comment: both the measure-side and the interval-side approximations collapse to the
    -- same boundary-plus-prefix linear combination of the mixed primitive at dyadic level `m`.
    calc
      seqMeasure m
          =
        H (Definition2158.dyadicPartitionSequence m
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) *
          (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j) +
            Finset.sum
              (Finset.range
                (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
              fun k ↦
                (H (Definition2158.dyadicPartitionSequence m k) -
                    H (Definition2158.dyadicPartitionSequence m (k + 1))) *
                  (∫ s in Set.Icc (0 : ℝ)
                      (Definition2158.dyadicPartitionSequence m (k + 1) : ℝ),
                    a s.toNNReal ω i j) := by
            exact
              coarseIccStep_weightedPolarization_eq_linearCombination_of_mixedPrimitive
                (a := a) (ω := ω) i j H hμAdd hμSub hμAddFinite hμSubFinite T m
      _ = seqInterval m := by
            symm
            simpa [seqInterval] using
              coarseIccStep_intervalIntegral_eq_linearCombination_of_prefixIntegral
                H
                (T := T)
                (f := fun s : ℝ ↦ a s.toNNReal ω i j)
                hMixedInt
                m
  have hMeasureAdd :
      Tendsto
        (fun m : ℕ ↦ ∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μAdd)
        atTop
        (𝓝 (∫ s in Set.Icc 0 T, H s ∂μAdd)) :=
    tendsto_setIntegral_coarseIccStep_of_continuous H hHNN T (hμAddFinite T)
  have hMeasureSub :
      Tendsto
        (fun m : ℕ ↦ ∫ s in Set.Icc 0 T, coarseIccStep H m T s ∂μSub)
        atTop
        (𝓝 (∫ s in Set.Icc 0 T, H s ∂μSub)) :=
    tendsto_setIntegral_coarseIccStep_of_continuous H hHNN T (hμSubFinite T)
  have hMeasureLim :
      Tendsto seqMeasure atTop
        (𝓝 ((1 / 4 : ℝ) *
          ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
            ∫ s in Set.Icc 0 T, H s ∂μSub))) := by
    simpa [seqMeasure] using (hMeasureAdd.sub hMeasureSub).const_mul (1 / 4 : ℝ)
  have hIntervalLim :
      Tendsto seqInterval atTop
        (𝓝 (∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * H s.toNNReal)) := by
    simpa [seqInterval] using
      tendsto_intervalIntegral_mul_coarseIccStep_of_continuous
        H hH
        (f := fun s : ℝ ↦ a s.toNNReal ω i j)
        hMixedInt
  have hMeasureLim' :
      Tendsto seqInterval atTop
        (𝓝 ((1 / 4 : ℝ) *
          ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
            ∫ s in Set.Icc 0 T, H s ∂μSub))) := by
    refine hMeasureLim.congr' ?_
    filter_upwards with m
    exact hseqEq m
  exact tendsto_nhds_unique hMeasureLim' hIntervalLim
/-- Helper for the multidimensional Itô formula: if a path pair has quadratic-covariation primitive
`S ↦ ∫_0^S a_{i,j}(s) ds`, then the weighted pathwise quadratic-covariation integral at a fixed
horizon is the corresponding weighted interval integral against `a_{i,j}` once the three
polarization densities are available on all natural horizons. -/
theorem pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationPrimitive
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    (H : NNReal → ℝ)
    {Yi Yj : C(NNReal, ℝ)}
    (hii :
      HasQuadraticCovariationAlong
        Yi
        Yi
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i))
    (hjj :
      HasQuadraticCovariationAlong
        Yj
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hij :
      HasQuadraticCovariationAlong
        Yi
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j))
    (hiiNat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hijNat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hjjNat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hH : Continuous H)
    (T : NNReal)
    (hMixedInt :
      IntegrableOn
        (fun s : ℝ ↦ a s.toNNReal ω i j)
        (Set.Icc (0 : ℝ) (T : ℝ))) :
    pathwiseQuadraticCovariationIntegral H Yi Yj T =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * H s.toNNReal := by
  let densityAdd : ℝ → ℝ := fun s ↦
    a s.toNNReal ω i i + 2 * a s.toNNReal ω i j + a s.toNNReal ω j j
  let densitySub : ℝ → ℝ := fun s ↦
    a s.toNNReal ω i i + (-2) * a s.toNNReal ω i j + a s.toNNReal ω j j
  have hPolar := covariationPrimitivePolarizationWitnesses (a := a) (ω := ω) i j hii hjj hij
  rcases hPolar with ⟨hAddRaw, hSubRaw⟩
  have hiiInt :
      ∀ S : NNReal,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
    integrableOn_Icc_of_natHorizons hiiNat
  have hijInt :
      ∀ S : NNReal,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
    integrableOn_Icc_of_natHorizons hijNat
  have hjjInt :
      ∀ S : NNReal,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
    integrableOn_Icc_of_natHorizons hjjNat
  have hAddDensityLoc :
      LocallyIntegrable densityAdd volume :=
    polarizationDensityLocallyIntegrable_of_natHorizons
      (a := a) (ω := ω) i j (2 : ℝ) hiiNat hijNat hjjNat
  have hSubDensityLoc :
      LocallyIntegrable densitySub volume :=
    polarizationDensityLocallyIntegrable_of_natHorizons
      (a := a) (ω := ω) i j (-2 : ℝ) hiiNat hijNat hjjNat
  have hAddRaw' :
      HasSquareVariationAlong
        (Yi + Yj)
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densityAdd s) := by
    intro S
    have hiiS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hiiInt S
    have hijS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hijInt S
    have hjjS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hjjInt S
    have hAddTarget :
        ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densityAdd s =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
      calc
        ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densityAdd s
            =
          ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
            a s.toNNReal ω i i + (2 * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
              simp [densityAdd, add_assoc]
        _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
              (2 * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
                simpa using integral_add hiiS ((hijS.const_mul (2 : ℝ)).add hjjS)
        _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), 2 * a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                simpa [add_assoc] using integral_add (hijS.const_mul (2 : ℝ)) hjjS
        _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                rw [integral_const_mul]
    -- Route correction: now that the natural-horizon integrability is explicit, the raw
    -- polarization primitive rewrites to the bundled interval-integral target.
    simpa [hAddTarget] using hAddRaw S
  have hSubRaw' :
      HasSquareVariationAlong
        (Yi - Yj)
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densitySub s) := by
    intro S
    have hiiS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hiiInt S
    have hijS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hijInt S
    have hjjS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hjjInt S
    have hSubTarget :
        ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densitySub s =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
      calc
        ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densitySub s
            =
          ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
            a s.toNNReal ω i i + ((-2) * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
              simp [densitySub, add_assoc]
        _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
              ((-2) * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
                simpa using integral_add hiiS ((hijS.const_mul (-2 : ℝ)).add hjjS)
        _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), (-2) * a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                simpa [add_assoc] using integral_add (hijS.const_mul (-2 : ℝ)) hjjS
        _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                rw [integral_const_mul]
                ring
    -- Proof comment: the minus polarization uses the same interval-integral normalization, now
    -- with the coefficient `-2` on the mixed entry.
    simpa [hSubTarget] using hSubRaw S
  have hAddSq :
      HasSquareVariationAlong
        (Yi + Yj)
        (indefiniteIntegralPath densityAdd) :=
    hasSquareVariationAlong_indefiniteIntegralPath_of_intervalIntegral hAddRaw' hAddDensityLoc
  have hSubSq :
      HasSquareVariationAlong
        (Yi - Yj)
        (indefiniteIntegralPath densitySub) :=
    hasSquareVariationAlong_indefiniteIntegralPath_of_intervalIntegral hSubRaw' hSubDensityLoc
  let μAdd : Measure NNReal := squareVariationStieltjesMeasure hAddSq
  let μSub : Measure NNReal := squareVariationStieltjesMeasure hSubSq
  have hμAdd :
      ∀ S : NNReal,
        ∫ _ in Set.Icc 0 S, (1 : ℝ) ∂μAdd =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
    intro S
    have hiiS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hiiInt S
    have hijS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hijInt S
    have hjjS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hjjInt S
    -- Proof comment: the canonical Stieltjes mass of the bundled plus-path collapses back to the
    -- textbook plus polarization primitive.
    calc
      ∫ _ in Set.Icc 0 S, (1 : ℝ) ∂μAdd
          = ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densityAdd s := by
              simpa [μAdd] using
                squareVariationStieltjesMeasure_mass_eq_intervalIntegral_of_indefiniteIntegralPath
                  hAddSq hAddDensityLoc S
      _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
          calc
            ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densityAdd s
                =
              ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
                a s.toNNReal ω i i + (2 * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
                  simp [densityAdd, add_assoc]
            _ =
              (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
                ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
                  (2 * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
                    simpa using integral_add hiiS ((hijS.const_mul (2 : ℝ)).add hjjS)
            _ =
              (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
                (∫ s in Set.Icc (0 : ℝ) (S : ℝ), 2 * a s.toNNReal ω i j) +
                (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                    simpa [add_assoc] using integral_add (hijS.const_mul (2 : ℝ)) hjjS
            _ =
              (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
                2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
                (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                    rw [integral_const_mul]
  have hμSub :
      ∀ S : NNReal,
        ∫ _ in Set.Icc 0 S, (1 : ℝ) ∂μSub =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
    intro S
    have hiiS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hiiInt S
    have hijS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hijInt S
    have hjjS :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (S : ℝ)) :=
      hjjInt S
    -- Proof comment: the bundled minus-path gives the second polarization primitive in the same
    -- way, again using the now-explicit interval-integrability data.
    calc
      ∫ _ in Set.Icc 0 S, (1 : ℝ) ∂μSub
          = ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densitySub s := by
              simpa [μSub] using
                squareVariationStieltjesMeasure_mass_eq_intervalIntegral_of_indefiniteIntegralPath
                  hSubSq hSubDensityLoc S
      _ =
          (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) -
            2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
            (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
          calc
            ∫ s in Set.Icc (0 : ℝ) (S : ℝ), densitySub s
                =
              ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
                a s.toNNReal ω i i + ((-2) * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
                  simp [densitySub, add_assoc]
            _ =
              (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
                ∫ s in Set.Icc (0 : ℝ) (S : ℝ),
                  ((-2) * a s.toNNReal ω i j + a s.toNNReal ω j j) := by
                    simpa using integral_add hiiS ((hijS.const_mul (-2 : ℝ)).add hjjS)
            _ =
              (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) +
                (∫ s in Set.Icc (0 : ℝ) (S : ℝ), (-2) * a s.toNNReal ω i j) +
                (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                    simpa [add_assoc] using integral_add (hijS.const_mul (-2 : ℝ)) hjjS
            _ =
              (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i i) -
                2 * (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j) +
                (∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω j j) := by
                    rw [integral_const_mul]
                    ring
  have hμAddFinite : ∀ S : NNReal, μAdd (Set.Icc 0 S) < ⊤ := by
    intro S
    exact lt_of_le_of_ne le_top (squareVariationStieltjesMeasure_Icc_lt_top hAddSq S)
  have hμSubFinite : ∀ S : NNReal, μSub (Set.Icc 0 S) < ⊤ := by
    intro S
    exact lt_of_le_of_ne le_top (squareVariationStieltjesMeasure_Icc_lt_top hSubSq S)
  have hHReal : Continuous fun s : ℝ ↦ H s.toNNReal :=
    hH.comp continuous_real_toNNReal
  -- Proof comment: the weighted mixed bracket is the canonical polarized Stieltjes difference,
  -- and the deterministic weighted-polarization theorem now converts that difference to the
  -- textbook interval integral.
  calc
    pathwiseQuadraticCovariationIntegral H Yi Yj T
        =
      (1 / 4 : ℝ) *
        ((∫ s in Set.Icc 0 T, H s ∂μAdd) - ∫ s in Set.Icc 0 T, H s ∂μSub) := by
      simpa [μAdd, μSub] using
        pathwiseQuadraticCovariationIntegral_eq_weightedPolarization H hH hAddSq hSubSq T
    _ =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * H s.toNNReal := by
      exact
        weightedPolarizationDifference_eq_intervalIntegral
          (a := a) (ω := ω) i j H
          (Yi := Yi) (Yj := Yj)
          hAddRaw hSubRaw hμAdd hμSub hμAddFinite hμSubFinite hHReal T hMixedInt
/-- Helper for the multidimensional Itô formula: two path pairs that realize the same fixed
quadratic-covariation primitive have the same weighted pathwise quadratic-covariation integral on
that horizon, provided the same natural-horizon polarization integrability is available for both
diagonal and mixed entries. -/
theorem pathwiseQuadraticCovariationIntegral_eq_of_shared_covariationPrimitive
    {a : MatrixProcess} {ω : Ω} (i j : Fin d)
    (H : NNReal → ℝ)
    {Yi Yj Mi Mj : C(NNReal, ℝ)}
    (hiiY :
      HasQuadraticCovariationAlong
        Yi
        Yi
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i))
    (hjjY :
      HasQuadraticCovariationAlong
        Yj
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hijY :
      HasQuadraticCovariationAlong
        Yi
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j))
    (hiiM :
      HasQuadraticCovariationAlong
        Mi
        Mi
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i i))
    (hjjM :
      HasQuadraticCovariationAlong
        Mj
        Mj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω j j))
    (hijM :
      HasQuadraticCovariationAlong
        Mi
        Mj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j))
    (hiiNat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i i)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hijNat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hjjNat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω j j)
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hH : Continuous H)
    (T : NNReal)
    (hMixedInt :
      IntegrableOn
        (fun s : ℝ ↦ a s.toNNReal ω i j)
        (Set.Icc (0 : ℝ) (T : ℝ))) :
    pathwiseQuadraticCovariationIntegral H Yi Yj T =
      pathwiseQuadraticCovariationIntegral H Mi Mj T := by
  calc
    pathwiseQuadraticCovariationIntegral H Yi Yj T
        =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω i j * H s.toNNReal :=
      pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationPrimitive
        (a := a) (ω := ω) i j H hiiY hjjY hijY hiiNat hijNat hjjNat hH T hMixedInt
    _ =
      pathwiseQuadraticCovariationIntegral H Mi Mj T := by
      symm
      exact
        pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationPrimitive
          (a := a) (ω := ω) i j H hiiM hjjM hijM hiiNat hijNat hjjNat hH T hMixedInt
/-- Helper for the multidimensional Itô formula: once the pathwise coordinate covariations are identified with the
primitive paths `T ↦ ∫_0^T a_s^{i,j} ds`, the remaining canonical quadratic correction is exactly
the textbook double time integral, provided the coefficient field `a` is entrywise integrable on
the fixed compact horizon. -/
theorem quadraticCorrection_eq_textbookIntegral_of_covariationPrimitive
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {a : MatrixProcess} {Y : VectorProcess}
    (T : NNReal) (ω : Ω)
    (hcontω : Continuous fun t : NNReal ↦ Y t ω)
    (hcov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (generalizedDiffusionCoordinatePath Y hcontω i)
          (generalizedDiffusionCoordinatePath Y hcontω j)
          (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω i j))
    (haNatω :
      ∀ i j : Fin d, ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω i j)
          (Set.Icc (0 : ℝ) (n : ℝ))) :
    ((1 : ℝ) / 2) *
        ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (Y s ω))
            (generalizedDiffusionCoordinatePath Y hcontω i)
            (generalizedDiffusionCoordinatePath Y hcontω j)
            T
      =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d, ∑ j : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              a s.toNNReal ω i j * (∂²[i, j] F) (Y s.toNNReal ω) := by
  have hpair :
      ∀ i j : Fin d,
        pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (Y s ω))
            (generalizedDiffusionCoordinatePath Y hcontω i)
            (generalizedDiffusionCoordinatePath Y hcontω j)
            T
          =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          a s.toNNReal ω i j * (∂²[i, j] F) (Y s.toNNReal ω) := by
    intro i j
    -- Proof comment: the pairwise interval-integral identity is exactly the fixed-horizon
    -- covariation-primitive theorem proved earlier in this file.
    exact
      pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationPrimitive
        (a := a) (ω := ω) i j
        (fun s ↦ (∂²[i, j] F) (Y s ω))
        (hcov i i) (hcov j j) (hcov i j)
        (fun n ↦ haNatω i i n)
        (fun n ↦ haNatω i j n)
        (fun n ↦ haNatω j j n)
        ((continuous_secondPartialDeriv F hF i j).comp hcontω)
        T
        (integrableOn_Icc_of_natHorizons (haNatω i j) T)
  -- Proof comment: once each pairwise bracket term is rewritten by the fixed-horizon weighted
  -- interval integral, the textbook quadratic correction is just the double finite sum of those
  -- pairwise identities.
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact hpair i j
-- Proof sketch: write the canonical coordinate martingale parts as
-- `Mᵏ_t = Y_t^k - ∫_0^t b_s^k ds`, apply the one-dimensional Itô formula of Theorem 25.27 to the
-- stochastic integrals `∫_0^t ∂ₖ F(Y_s) dM_s^k`, and use the quadratic-covariation hypotheses to
-- rewrite the second-order correction by the density field `a`.
-- LeanSearch recall: the canonical Brownian specialization uses the Laplacian API, so the main
-- public surface stays at the source-facing generalized-diffusion owner rather than at an
-- abstract semimartingale package.
/-- Source-facing owner for the multidimensional generalized diffusion from the preceding setup.
It packages the Brownian driver `W`, diffusion matrix `σ`, drift `b`, and
covariance density `a` together with the coordinate martingale/covariation data needed by the
chapter-level multidimensional Itô statement. -/
structure IsMultidimensionalGeneralizedDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (W : VectorProcess) (σ a : MatrixProcess) (b Y : VectorProcess) where
  brownianMotion : IsStandardBrownianMotionVector μ W
  covariance_density_eq :
    ∀ t : NNReal, ∀ ω : Ω, ∀ k l : Fin d,
      a t ω k l = ∑ m : Fin d, σ t ω k m * σ t ω l m
  coordinate_martingaleData :
    ∀ k : Fin d,
      Σ' _hMk : IsContinuousLocalMartingale ℱ μ
          (generalizedDiffusionCoordinateMartingalePart b Y k),
        HasAbsolutelyContinuousSquareVariation
          (generalizedDiffusionCoordinateMartingalePart b Y k)
          (IsContinuousLocalMartingale ℱ μ
            (generalizedDiffusionCoordinateMartingalePart b Y k))
  coordinate_covariation :
    ∀ k l : Fin d,
      IsContinuousQuadraticCovariationProcess
        ℱ
        μ
        (generalizedDiffusionCoordinateMartingalePart b Y k)
        (generalizedDiffusionCoordinateMartingalePart b Y l)
        (fun t ω ↦
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal ω k l)
  drift_progMeasurable :
    ∀ k : Fin d, ProgMeasurable ℱ (fun t ω ↦ b t ω k)
  drift_intervalIntegrable :
    ∀ k : Fin d, ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (T : ℝ))
  covariance_intervalIntegrable :
    ∀ k l : Fin d, ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn
        (fun s : ℝ ↦ a s.toNNReal ω k l)
        (Set.Icc (0 : ℝ) (T : ℝ))

/-- The source stochastic term in formula `(25.17)`, grouped by Brownian driver coordinate:
for each `l`, the integrand is `∑ₖ σ_s^{k,l} ∂ₖ F(Y_s)`. -/
def generalizedDiffusionItoBrownianIntegrand
    (F : State → ℝ) (σ : MatrixProcess) (Y : VectorProcess) (l : Fin d) : Process :=
  fun t ω ↦ ∑ k : Fin d, σ t ω k l * (∂[k] F) (Y t ω)

/-- The canonical quadratic-covariation process
`⟨Mᵏ, Mˡ⟩_t = ∫_0^t a_s^{k,l} ds`
of the coordinate martingale parts of a generalized diffusion. -/
def generalizedDiffusionCoordinateQuadraticCovariation
    (a : MatrixProcess) (k l : Fin d) : Process :=
  fun t ω ↦ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal ω k l

section

omit mΩ

/-- The definition `generalizedDiffusionItoBrownianIntegrand` is exactly the displayed
integrand `∑ₖ σ_s^{k,l} ∂ₖ F(Y_s)` from formula `(25.17)`. -/
@[simp] theorem generalizedDiffusionItoBrownianIntegrand_apply
    (F : State → ℝ) (σ : MatrixProcess) (Y : VectorProcess) (l : Fin d) (t : NNReal) (ω : Ω) :
    generalizedDiffusionItoBrownianIntegrand F σ Y l t ω =
      ∑ k : Fin d, σ t ω k l * (∂[k] F) (Y t ω) :=
  rfl

/-- Evaluating the canonical bracket process `⟨Mᵏ, Mˡ⟩` gives the defining time integral of the
covariance density `a`. -/
@[simp] theorem generalizedDiffusionCoordinateQuadraticCovariation_apply
    (a : MatrixProcess) (k l : Fin d) (t : NNReal) (ω : Ω) :
    generalizedDiffusionCoordinateQuadraticCovariation a k l t ω =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal ω k l :=
  rfl

end

/-- Theorem 25.33 -/
theorem multidimensionalGeneralizedDiffusion_ito_formula_source
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {W : VectorProcess} {σ a : MatrixProcess} {b Y : VectorProcess}
    (hY : IsMultidimensionalGeneralizedDiffusion ℱ μ W σ a b Y) :
    ∀ᵐ ω ∂μ,
      ∃ hcont : Continuous fun t : NNReal ↦ Y t ω,
        ∀ T : NNReal,
          F (Y T ω) - F (Y 0 ω) =
            pathwiseMultidimensionalItoIntegral
                F
                (⟨fun t ↦ Y t ω, hcont⟩ : VectorPathSpace d)
                T +
              ((1 : ℝ) / 2) *
                ∑ k : Fin d, ∑ l : Fin d,
                  pathwiseQuadraticCovariationIntegral
                    (fun s ↦ (∂²[k, l] F) (Y s ω))
                    (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
                      (hY.coordinate_martingaleData k).1.continuous ω⟩ : C(NNReal, ℝ))
                    (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
                      (hY.coordinate_martingaleData l).1.continuous ω⟩ : C(NNReal, ℝ))
                    T := by
  have hcont :
      ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ Y t ω :=
    ae_continuousGeneralizedDiffusionPath
      (b := b) (Y := Y)
      hY.drift_progMeasurable
      (fun k ↦ (hY.coordinate_martingaleData k).1)
      hY.drift_intervalIntegrable
  have hbNat :
      ∀ᵐ ω ∂μ,
        ∀ k : Fin d, ∀ n : ℕ,
          IntegrableOn
            (fun s : ℝ ↦ |b s.toNNReal ω k|)
            (Set.Icc (0 : ℝ) (n : ℝ)) := by
    refine ae_all_iff.2 ?_
    intro k
    refine ae_all_iff.2 ?_
    intro n
    simpa using hY.drift_intervalIntegrable k (n : NNReal)
  have haNat :
      ∀ᵐ ω ∂μ,
        ∀ k l : Fin d, ∀ n : ℕ,
          IntegrableOn
            (fun s : ℝ ↦ a s.toNNReal ω k l)
            (Set.Icc (0 : ℝ) (n : ℝ)) := by
    refine ae_all_iff.2 ?_
    intro k
    refine ae_all_iff.2 ?_
    intro l
    refine ae_all_iff.2 ?_
    intro n
    simpa using hY.covariance_intervalIntegrable k l (n : NNReal)
  have hMartCov :
      ∀ᵐ ω ∂μ,
        ∀ k l : Fin d,
          HasQuadraticCovariationAlong
            (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
              (hY.coordinate_martingaleData k).1.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
              (hY.coordinate_martingaleData l).1.continuous ω⟩ : C(NNReal, ℝ))
            (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal ω k l) := by
    refine ae_all_iff.2 ?_
    intro k
    refine ae_all_iff.2 ?_
    intro l
    simpa using
      (ae_hasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcess
        ((hY.coordinate_martingaleData k).1)
        ((hY.coordinate_martingaleData l).1)
        (hY.coordinate_covariation k l))
  filter_upwards [hcont, hbNat, haNat, hMartCov] with ω hcontω hbNatω haNatω hMartCovω
  refine ⟨hcontω, ?_⟩
  intro T
  let Xω : VectorPathSpace d := ⟨fun t ↦ Y t ω, hcontω⟩
  have hActualCov :
      ∀ k l : Fin d,
        HasQuadraticCovariationAlong
          (generalizedDiffusionCoordinatePath Y hcontω k)
          (generalizedDiffusionCoordinatePath Y hcontω l)
          (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω k l) := by
    intro k l
    have hLocAddω :
        LocallyIntegrable
          (coordinateDriftCombinationDensity b ω k l (1 : ℝ) (1 : ℝ))
          volume :=
      coordinateDriftCombination_locallyIntegrable_of_natHorizons
        (ω := ω) (k := k) (l := l) (c₁ := 1) (c₂ := 1)
        (hkProg := hY.drift_progMeasurable k) (hlProg := hY.drift_progMeasurable l)
        (fun n ↦ ⟨hbNatω k n, hbNatω l n⟩)
    have hLocSubω :
        LocallyIntegrable
          (coordinateDriftCombinationDensity b ω k l (1 : ℝ) (-1 : ℝ))
          volume :=
      coordinateDriftCombination_locallyIntegrable_of_natHorizons
        (ω := ω) (k := k) (l := l) (c₁ := 1) (c₂ := -1)
        (hkProg := hY.drift_progMeasurable k) (hlProg := hY.drift_progMeasurable l)
        (fun n ↦ ⟨hbNatω k n, hbNatω l n⟩)
    -- Route correction: normalize the actual coordinate paths to the shared primitive first,
    -- rather than trying to rewrite the final correction term directly.
    exact
      hasQuadraticCovariationAlong_generalizedDiffusionCoordinates
        (a := a) (b := b) (Y := Y) (ω := ω) k l hcontω
        (fun n ↦ ⟨hbNatω k n, hbNatω l n⟩)
        (fun i ↦ (hY.coordinate_martingaleData i).1)
        (hMartCovω k k) (hMartCovω l l) (hMartCovω k l)
        hLocAddω hLocSubω
  have hXω : Xω ∈ (𝒞_qv^d) := by
    refine (mem_𝒞_qv_d_iff_exists_family Xω).2 ?_
    refine ⟨fun k l ↦ fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal ω k l, ?_⟩
    intro k l
    -- The coordinate paths of `Xω` are definitionally the actual coordinate paths of `Y`.
    simpa [Xω, generalizedDiffusionCoordinatePath, vectorPathComponent]
      using hActualCov k l
  have hMixedIntω :
      ∀ k l : Fin d,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω k l)
          (Set.Icc (0 : ℝ) (T : ℝ)) := by
    intro k l
    let n : ℕ := Nat.ceil (T : ℝ)
    have hNatInt :
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal ω k l)
          (Set.Icc (0 : ℝ) (n : ℝ)) :=
      haNatω k l n
    have hSubset :
        Set.Icc (0 : ℝ) (T : ℝ) ⊆ Set.Icc (0 : ℝ) (n : ℝ) := by
      intro s hs
      refine ⟨hs.1, ?_⟩
      exact le_trans hs.2 (by exact_mod_cast Nat.le_ceil (T : ℝ))
    exact hNatInt.mono_set hSubset
  have hCorrection :
      ((1 : ℝ) / 2) *
          ∑ k : Fin d, ∑ l : Fin d,
            pathwiseQuadraticCovariationIntegral
              (fun s ↦ (∂²[k, l] F) (Y s ω))
              (generalizedDiffusionCoordinatePath Y hcontω k)
              (generalizedDiffusionCoordinatePath Y hcontω l)
              T
        =
      ((1 : ℝ) / 2) *
          ∑ k : Fin d, ∑ l : Fin d,
            pathwiseQuadraticCovariationIntegral
              (fun s ↦ (∂²[k, l] F) (Y s ω))
              (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
                (hY.coordinate_martingaleData k).1.continuous ω⟩ : C(NNReal, ℝ))
              (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
                (hY.coordinate_martingaleData l).1.continuous ω⟩ : C(NNReal, ℝ))
              T := by
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    refine Finset.sum_congr rfl ?_
    intro l hl
    have hWeight :
        Continuous fun s : NNReal ↦ (∂²[k, l] F) (Y s ω) :=
      (continuous_secondPartialDeriv F hF k l).comp hcontω
    exact
      pathwiseQuadraticCovariationIntegral_eq_of_shared_covariationPrimitive
        (a := a) (ω := ω) k l
        (fun s ↦ (∂²[k, l] F) (Y s ω))
        (hActualCov k k) (hActualCov l l) (hActualCov k l)
        (hMartCovω k k) (hMartCovω l l) (hMartCovω k l)
        (haNatω k k) (haNatω k l) (haNatω l l)
        hWeight T (hMixedIntω k l)
  -- Apply the pathwise multidimensional Itô formula to the continuous sample path `Xω`, then
  -- replace its canonical correction by the shared-primitive martingale correction.
  calc
    F (Y T ω) - F (Y 0 ω) =
      pathwiseMultidimensionalItoIntegral F Xω T +
        ((1 : ℝ) / 2) *
          ∑ k : Fin d, ∑ l : Fin d,
            pathwiseQuadraticCovariationIntegral
              (fun s ↦ (∂²[k, l] F) (Y s ω))
              (generalizedDiffusionCoordinatePath Y hcontω k)
              (generalizedDiffusionCoordinatePath Y hcontω l)
              T := by
      simpa [Xω, generalizedDiffusionCoordinatePath, vectorPathComponent]
        using pathwiseMultidimensionalItoFormula F hF Xω hXω T
    _ =
      pathwiseMultidimensionalItoIntegral F Xω T +
        ((1 : ℝ) / 2) *
          ∑ k : Fin d, ∑ l : Fin d,
            pathwiseQuadraticCovariationIntegral
              (fun s ↦ (∂²[k, l] F) (Y s ω))
              (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y k t ω,
                (hY.coordinate_martingaleData k).1.continuous ω⟩ : C(NNReal, ℝ))
              (⟨fun t ↦ generalizedDiffusionCoordinateMartingalePart b Y l t ω,
                (hY.coordinate_martingaleData l).1.continuous ω⟩ : C(NNReal, ℝ))
              T := by
      rw [hCorrection]

end ProbabilityTheory
