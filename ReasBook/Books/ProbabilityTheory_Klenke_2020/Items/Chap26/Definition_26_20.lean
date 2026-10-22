/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

section FixedSpace

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ

/-- Helper for Definition 26.20: a witness that `A` is a continuous quadratic covariation process
for `M` and `N`, namely it starts at `0`, is adapted and pathwise continuous, has almost surely
locally finite variation, and makes `MN - A` a local martingale. -/
structure HasContinuousQuadraticCovariation
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (M N A : NNReal → Ω → ℝ) : Prop where
  /-- The covariation process starts at `0`. -/
  zero : A 0 = 0
  /-- The covariation process is adapted to the ambient filtration. -/
  adapted : Adapted ℱ A
  /-- The covariation process has continuous sample paths. -/
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ A t ω)
  /-- Almost every sample path of the covariation process has locally finite variation. -/
  locally_finite_variation :
    ∀ᵐ ω ∂μ,
      LocallyBoundedVariationOn
        (⟨fun t ↦ A t ω, continuous ω⟩ : C(NNReal, ℝ)) Set.univ
  /-- Subtracting the covariation process from the pointwise product yields a local martingale. -/
  local_martingale_mul_sub :
    IsLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω)

local notation "IsContinuousQuadraticCovariationProcess" => HasContinuousQuadraticCovariation

/-- The `i`-th drift-compensated coordinate process attached to a path-valued process `X`. -/
def localMartingaleProblemMartingalePart
    (b : DriftCoeff) (X : Ω → PathSpace) (i : Fin n) : NNReal → Ω → ℝ :=
  fun t ω ↦ X ω t i - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X ω s.toNNReal) i

-- Proof sketch: unfold `localMartingaleProblemMartingalePart`; it is defined by subtracting the
-- time-integrated drift from the `i`-th coordinate of the path-valued process.
/-- Evaluating the martingale part gives the `i`-th coordinate minus its drift integral. -/
theorem localMartingaleProblemMartingalePart_apply
    (b : DriftCoeff) (X : Ω → PathSpace) (i : Fin n) (t : NNReal) (ω : Ω) :
    localMartingaleProblemMartingalePart b X i t ω =
      X ω t i - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X ω s.toNNReal) i := by
  -- This is the defining formula of the compensated coordinate process.
  rfl

/-- The prescribed quadratic-covariation process for coordinates `i` and `j` in the local
martingale problem with coefficient field `a`. -/
def localMartingaleProblemCovariation
    (a : DiffusionMatrixCoeff) (X : Ω → PathSpace) (i j : Fin n) : NNReal → Ω → ℝ :=
  fun t ω ↦ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal (X ω s.toNNReal) i j

-- Proof sketch: unfold `localMartingaleProblemCovariation`; it is the time integral of the
-- `(i,j)`-entry of `a` evaluated along the sample path `X`.
/-- Evaluating the prescribed covariation gives the time integral of `aᵢⱼ(s, X_s)`. -/
theorem localMartingaleProblemCovariation_apply
    (a : DiffusionMatrixCoeff) (X : Ω → PathSpace) (i j : Fin n) (t : NNReal) (ω : Ω) :
    localMartingaleProblemCovariation a X i j t ω =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal (X ω s.toNNReal) i j := by
  -- This is the defining time integral for the prescribed covariation.
  rfl

/-- A continuous `n`-dimensional path-valued process `X` solves the local martingale problem
`LMP(a, b, μ₀)` if its initial law is `μ₀` and each drift-compensated coordinate is a continuous
local martingale whose quadratic covariation with every other coordinate is given by the integral
of `a` along `X`; this is the solution notion from Definition 26.20. -/
structure IsLocalMartingaleProblemSolution
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (X : Ω → PathSpace) : Prop where
  /-- The initial distribution of the solution is `μ₀`. -/
  initial_law : HasLaw (fun ω ↦ X ω 0) μ₀ μ
  /-- Each drift-compensated coordinate is a continuous local martingale. -/
  martingalePart :
    letI : IsProbabilityMeasure μ := initial_law.isProbabilityMeasure
    ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (localMartingaleProblemMartingalePart b X i)
  /-- The quadratic covariation of the `i`-th and `j`-th martingale parts is the prescribed
  integral of `aᵢⱼ` along the path `X`. -/
  quadraticCovariation :
    letI : IsProbabilityMeasure μ := initial_law.isProbabilityMeasure
    ∀ i j : Fin n,
      IsContinuousQuadraticCovariationProcess ℱ μ
        (localMartingaleProblemMartingalePart b X i)
        (localMartingaleProblemMartingalePart b X j)
        (localMartingaleProblemCovariation a X i j)

namespace IsLocalMartingaleProblemSolution

/-- The measurable-path interface used by downstream pushforward arguments. -/
theorem aemeasurable_path
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {a : DiffusionMatrixCoeff} {b : DriftCoeff}
    {ℱ : TimeFiltration} {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X) :
    AEMeasurable X μ := by
  sorry

/-- Any local-martingale-problem solution is carried by a probability measure because its initial
law is the probability measure `μ₀`. -/
theorem isProbabilityMeasure
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {a : DiffusionMatrixCoeff} {b : DriftCoeff}
    {ℱ : TimeFiltration} {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X) :
    IsProbabilityMeasure μ :=
  hX.initial_law.isProbabilityMeasure

/-- The `Mlocc` formulation of the martingale clause is a derived set-level view of the owner
predicate `IsContinuousLocalMartingale`. -/
theorem martingale_part_mem_Mlocc
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {a : DiffusionMatrixCoeff} {b : DriftCoeff}
    {ℱ : TimeFiltration} {μ : Measure Ω}
    {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X) (i : Fin n) :
    localMartingaleProblemMartingalePart b X i ∈ Mlocc ℱ μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact (mem_Mlocc_iff ℱ μ _).2 (hX.martingalePart i)

end IsLocalMartingaleProblemSolution

/-- A path-valued process is canonically a local-martingale-problem solution once the initial-law,
coordinate local-martingale, and prescribed quadratic-covariation clauses are given. -/
instance
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (X : Ω → PathSpace)
    (hinitialLaw : HasLaw (fun ω ↦ X ω 0) μ₀ μ)
    (hmartingalePart :
      letI : IsProbabilityMeasure μ := hinitialLaw.isProbabilityMeasure
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (localMartingaleProblemMartingalePart b X i))
    (hquadraticCovariation :
      letI : IsProbabilityMeasure μ := hinitialLaw.isProbabilityMeasure
      ∀ i j : Fin n,
        IsContinuousQuadraticCovariationProcess ℱ μ
          (localMartingaleProblemMartingalePart b X i)
          (localMartingaleProblemMartingalePart b X j)
          (localMartingaleProblemCovariation a X i j)) :
    IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X where
  initial_law := hinitialLaw
  martingalePart := hmartingalePart
  quadraticCovariation := hquadraticCovariation

/-- The local martingale problem `LMP(a, b, μ₀)` is unique when any two of its solutions have the
same law on continuous path space. -/
def LocalMartingaleProblemHasUniqueLaw
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (a : DiffusionMatrixCoeff) (b : DriftCoeff) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
      (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) (X : Ω → PathSpace)
      {Ω' : Type v} [mΩ' : MeasurableSpace Ω']
      (ℱ' : Filtration NNReal mΩ') (μ' : Measure Ω')
      (X' : Ω' → PathSpace),
      IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X →
      IsLocalMartingaleProblemSolution μ₀ a b ℱ' μ' X' →
      μ.map X = μ'.map X'

end FixedSpace

section DiffusionMatrix

variable {m : ℕ}

local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ

/-- The diffusion matrix field `a = σσᵀ` associated with a coefficient field `σ`. -/
def diffusionMatrixOfCoefficient (σ : DiffusionCoeff) : DiffusionMatrixCoeff :=
  fun t x i j ↦ ∑ k : Fin m, σ t x i k * σ t x j k

section

variable (σ : NNReal → State → Fin n → Fin m → ℝ)

local notation "σσᵀ" => diffusionMatrixOfCoefficient σ

-- Proof sketch: unfold `σσᵀ`; the value at `(t, x, i, j)` is the defining finite sum over the
-- common noise index `k`.
/-- Evaluating `σσᵀ` gives the coefficient sum `∑ₖ σᵢₖ σⱼₖ`. -/
theorem diffusionMatrixOfCoefficient_apply
    (t : NNReal) (x : State) (i j : Fin n) :
    σσᵀ t x i j = ∑ k : Fin m, σ t x i k * σ t x j k := rfl

-- Proof sketch: unfold `σσᵀ`; the sum over `k` is manifestly symmetric in the two outer indices
-- after swapping the two scalar factors.
/-- The matrix field `σσᵀ` is symmetric in the indices `i` and `j`. -/
theorem diffusionMatrixOfCoefficient_symmetric
    (t : NNReal) (x : State) (i j : Fin n) :
    σσᵀ t x i j = σσᵀ t x j i := by
  -- Unfold `σσᵀ` and commute the scalar factors in each summand.
  simp [diffusionMatrixOfCoefficient_apply, mul_comm]

/-- Helper for Definition 26.20: expanding the quadratic form of `σσᵀ` produces a triple finite
sum in the coefficient entries of `σ`. -/
lemma diffusionMatrixOfCoefficient_quadraticForm_expand
    (t : NNReal) (x v : State) :
    (∑ i : Fin n, ∑ j : Fin n, v i * σσᵀ t x i j * v j) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin m,
        (v i * σ t x i k) * (σ t x j k * v j) := by
  -- Unfold `σσᵀ` entrywise so the whole proof stays in one finite-sum normal form.
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  calc
    v i * σσᵀ t x i j * v j
        = v i * (∑ k : Fin m, σ t x i k * σ t x j k) * v j := by
            rw [diffusionMatrixOfCoefficient_apply (σ := σ) (t := t) (x := x) (i := i) (j := j)]
    _ = (∑ k : Fin m, v i * (σ t x i k * σ t x j k)) * v j := by
          rw [Finset.mul_sum]
    _ = ∑ k : Fin m, (v i * (σ t x i k * σ t x j k)) * v j := by
          rw [Finset.sum_mul]
    _ = ∑ k : Fin m, (v i * σ t x i k) * (σ t x j k * v j) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          ring

/-- Helper for Definition 26.20: for fixed `k`, the inner double sum is the square of the
`k`-th projected coordinate sum. -/
lemma diffusionMatrixOfCoefficient_innerSum_eq_square
    (σ : NNReal → State → Fin n → Fin m → ℝ)
    (t : NNReal) (x v : State) (k : Fin m) :
    (∑ j : Fin n, ∑ i : Fin n, (v i * σ t x i k) * (σ t x j k * v j)) =
      (∑ i : Fin n, v i * σ t x i k)^2 := by
  -- Rewrite the double sum as a product of two finite sums.
  calc
    (∑ j : Fin n, ∑ i : Fin n, (v i * σ t x i k) * (σ t x j k * v j))
        = ∑ j : Fin n, (∑ i : Fin n, v i * σ t x i k) * (σ t x j k * v j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [← Finset.sum_mul]
    _ = (∑ i : Fin n, v i * σ t x i k) * (∑ j : Fin n, σ t x j k * v j) := by
          rw [← Finset.mul_sum]
    _ = (∑ i : Fin n, v i * σ t x i k) * (∑ j : Fin n, v j * σ t x j k) := by
          -- Commute the scalar factors in the second finite sum.
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ = (∑ i : Fin n, v i * σ t x i k)^2 := by
          -- The two factors are the same sum, so this is exactly a square.
          simp [pow_two]

/-- Helper for Definition 26.20: the quadratic form of `σσᵀ` is the finite sum of coordinatewise
squares `∑ k, (∑ i, v i * σ t x i k)^2`. -/
lemma diffusionMatrixOfCoefficient_quadraticForm_eq_sumSquares
    (t : NNReal) (x v : State) :
    (∑ i : Fin n, ∑ j : Fin n, v i * σσᵀ t x i j * v j) =
      ∑ k : Fin m, (∑ i : Fin n, v i * σ t x i k)^2 := by
  -- Route correction: keep the whole calculation in the unfolded `σσᵀ` normal form before
  -- comparing it with the expanded square.
  let f : Fin n → Fin n → Fin m → ℝ :=
    fun i j k ↦ (v i * σ t x i k) * (σ t x j k * v j)
  have hswap_jk : ∀ i : Fin n,
      (∑ j : Fin n, ∑ k : Fin m, f i j k) = ∑ k : Fin m, ∑ j : Fin n, f i j k := by
    intro i
    simpa [f] using
      (Finset.sum_comm : (∑ j : Fin n, ∑ k : Fin m, f i j k) = ∑ k : Fin m, ∑ j : Fin n, f i j k)
  have hswap_ik :
      (∑ i : Fin n, ∑ k : Fin m, ∑ j : Fin n, f i j k) =
        ∑ k : Fin m, ∑ i : Fin n, ∑ j : Fin n, f i j k := by
    simpa [f] using
      (Finset.sum_comm :
        (∑ i : Fin n, ∑ k : Fin m, ∑ j : Fin n, f i j k) =
          ∑ k : Fin m, ∑ i : Fin n, ∑ j : Fin n, f i j k)
  have hswap_ij : ∀ k : Fin m,
      (∑ i : Fin n, ∑ j : Fin n, f i j k) = ∑ j : Fin n, ∑ i : Fin n, f i j k := by
    intro k
    simpa [f] using
      (Finset.sum_comm : (∑ i : Fin n, ∑ j : Fin n, f i j k) = ∑ j : Fin n, ∑ i : Fin n, f i j k)
  calc
    (∑ i : Fin n, ∑ j : Fin n, v i * σσᵀ t x i j * v j)
        = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin m,
            (v i * σ t x i k) * (σ t x j k * v j) := by
            -- Expand the quadratic form into a triple sum indexed by the noise coordinate `k`.
            exact diffusionMatrixOfCoefficient_quadraticForm_expand (σ := σ) t x v
    _ = ∑ k : Fin m, ∑ j : Fin n, ∑ i : Fin n,
          (v i * σ t x i k) * (σ t x j k * v j) := by
            -- Reorder the finite sums so the noise index `k` becomes outermost.
            calc
              ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin m, f i j k
                  = ∑ i : Fin n, ∑ k : Fin m, ∑ j : Fin n, f i j k := by
                      refine Finset.sum_congr rfl ?_
                      intro i _
                      exact hswap_jk i
              _ = ∑ k : Fin m, ∑ i : Fin n, ∑ j : Fin n, f i j k := hswap_ik
              _ = ∑ k : Fin m, ∑ j : Fin n, ∑ i : Fin n, f i j k := by
                    refine Finset.sum_congr rfl ?_
                    intro k _
                    exact hswap_ij k
    _ = ∑ k : Fin m, (∑ i : Fin n, v i * σ t x i k)^2 := by
            -- Collapse each fixed-`k` inner double sum to the corresponding square.
            refine Finset.sum_congr rfl ?_
            intro k _
            simpa [f] using
              (diffusionMatrixOfCoefficient_innerSum_eq_square (σ := σ) t x v k)

-- Proof sketch: rewrite the quadratic form using the definition of `σσᵀ` and identify it with
-- the finite sum `∑ k, (∑ i, v i * σ t x i k)^2`, which is termwise nonnegative.
/-- Definition 26.20: the matrix field `a = σσᵀ` is nonnegative semidefinite through its quadratic
form. -/
theorem diffusionMatrixOfCoefficient_quadraticForm_nonneg
    (t : NNReal) (x v : State) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * σσᵀ t x i j * v j := by
  -- Rewrite the quadratic form as a finite sum of squares using the normalized helper lemma.
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, v i * σσᵀ t x i j * v j) =
        ∑ k : Fin m, (∑ i : Fin n, v i * σ t x i k)^2 :=
    diffusionMatrixOfCoefficient_quadraticForm_eq_sumSquares
      (σ := σ) (t := t) (x := x) (v := v)
  rw [hsum]
  -- Each square is nonnegative, so the whole finite sum is nonnegative.
  exact Finset.sum_nonneg fun k _ ↦ sq_nonneg (∑ i : Fin n, v i * σ t x i k)

end

end DiffusionMatrix

end ProbabilityTheory
