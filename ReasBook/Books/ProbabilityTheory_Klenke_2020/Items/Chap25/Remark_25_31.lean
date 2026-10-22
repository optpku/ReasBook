/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open TopologicalSpace
open scoped BigOperators

noncomputable section

variable {d : ℕ}

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ
local notation "State" => EuclideanSpace ℝ (Fin d)

/-- Helper for Remark 25.31: use the Chapter 21 dyadic partition sequence under the unqualified
name expected by the Chapter 25 pathwise-Itô APIs. -/
abbrev dyadicPartitionSequence : ℕ → ℕ → NNReal := Definition2158.dyadicPartitionSequence

/-- Helper for Remark 25.31: the unqualified dyadic partition sequence carries the inherited
admissible-partition instance from Definition 21.58. -/
instance instIsAdmissiblePartitionSequenceDyadicPartitionSequence :
    IsAdmissiblePartitionSequence dyadicPartitionSequence :=
  Definition2158.instIsAdmissiblePartitionSequenceDyadicPartitionSequence

/-- Helper for Remark 25.31: the left-point partition sum `∑ H_t (X_{t'} - X_t)` on `[0, T]`
along the `n`-th row of an admissible partition sequence `P`. -/
def partitionPathwiseItoApproximationUpTo
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    H (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k))

/-- Helper for Remark 25.31: `HasPathwiseItoIntegralAlong H X P I` means that the left-point
partition sums of `H` against `X` converge pointwise to the chosen realization `I`. -/
def HasPathwiseItoIntegralAlong
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (I : NNReal → ℝ) : Prop :=
  ∀ T : NNReal,
    Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (nhds (I T))

/-- Helper for Remark 25.31: a pathwise Itô realization yields the defining convergence statement
at each fixed horizon. -/
theorem HasPathwiseItoIntegralAlong.tendsto
    {H : NNReal → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P] {I : NNReal → ℝ}
    (hI : HasPathwiseItoIntegralAlong H X P I) (T : NNReal) :
    Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (nhds (I T)) :=
  hI T

/-- Helper for Remark 25.31: the canonical dyadic pathwise integral
`pathwiseItoIntegralAlong H X P` is the pointwise `limUnder` realization of the left-point
partition sums. -/
noncomputable def pathwiseItoIntegralAlong
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] : NNReal → ℝ :=
  fun T ↦ limUnder atTop (partitionPathwiseItoApproximationUpTo H X P T)

/-- Helper for Remark 25.31: any chosen realization of the left-point partition sums agrees with
the canonical `limUnder` integral. -/
theorem HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong
    {H : NNReal → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P] {I : NNReal → ℝ}
    (hI : HasPathwiseItoIntegralAlong H X P I) :
    pathwiseItoIntegralAlong H X P = I := by
  ext T
  simpa [pathwiseItoIntegralAlong] using (hI T).limUnder_eq

/-- Helper for Remark 25.31: the canonical Euclidean model of a continuous `d`-dimensional path
on `[0, ∞)`. -/
abbrev VectorPathSpace (d : ℕ) := C(NNReal, EuclideanSpace ℝ (Fin d))

local notation "StateCoords" => (EuclideanSpace.equiv (Fin d) ℝ : State ≃L[ℝ] Fin d → ℝ)

/-- Helper for Remark 25.31: the `i`-th scalar coordinate path of a continuous vector-valued
path. -/
abbrev vectorPathComponent (X : VectorPathSpace d) (i : Fin d) : PathSpace :=
  { toFun := fun t ↦ X t i
    continuous_toFun := by
      have hX : Continuous fun t ↦ StateCoords (X t) :=
        (StateCoords : State →L[ℝ] Fin d → ℝ).continuous.comp X.continuous
      simpa using (continuous_apply i).comp hX }

/-- Helper for Remark 25.31: evaluating `vectorPathComponent X i` at time `t` returns the `i`-th
coordinate `X t i`. -/
theorem vectorPathComponent_apply
    (X : VectorPathSpace d) (i : Fin d) (t : NNReal) :
    vectorPathComponent X i t = X t i := rfl

/-- Helper for Remark 25.31: the coordinate partial derivative `∂[i] F` obtained by varying only
the `i`-th Euclidean coordinate. -/
noncomputable def partialDeriv
    (F : State → ℝ) (i : Fin d) : State → ℝ :=
  fun x ↦ deriv (fun t ↦ F (x + EuclideanSpace.single i (t - x i))) (x i)

notation:max "∂[" i "] " F:arg => partialDeriv F i

/-- Helper for Remark 25.31: the dyadic left-point Riemann sum for the multidimensional pathwise
Itô integral of `∇F(X)` on `[0, T]`. -/
noncomputable def dyadicMultidimensionalItoApproximationUpTo
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
    ∑ i : Fin d,
      (∂[i] F) (X (dyadicPartitionSequence n k)) *
        (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
          X (dyadicPartitionSequence n k) i)

/-- Helper for Remark 25.31: the pathwise multidimensional Itô integral is the process obtained
from the `limUnder` of the dyadic left-point sums. -/
noncomputable def pathwiseMultidimensionalItoIntegral
    (F : State → ℝ) (X : VectorPathSpace d) : PathwiseProcess :=
  fun T ↦ limUnder atTop (dyadicMultidimensionalItoApproximationUpTo F X T)

/-- Helper for Remark 25.31: evaluating `pathwiseMultidimensionalItoIntegral` gives the `limUnder`
of the dyadic multidimensional Itô sums. -/
theorem pathwiseMultidimensionalItoIntegral_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) :
    pathwiseMultidimensionalItoIntegral F X T =
      limUnder atTop (dyadicMultidimensionalItoApproximationUpTo F X T) := rfl

-- Proof sketch: expand both dyadic sums, evaluate the coordinate-path terms, and interchange the
-- two finite summations.
/-- Expanding the multidimensional dyadic Itô sum shows that it is the finite sum of the dyadic
coordinate integrals of `∂ₖ F (X_s)` against the coordinate paths `Xᵏ`. -/
theorem dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo F X T n =
      ∑ k : Fin d,
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ (∂[k] F) (X t))
          (vectorPathComponent X k)
          dyadicPartitionSequence
          T
          n := by
  rw [dyadicMultidimensionalItoApproximationUpTo, Finset.sum_comm]
  simp [partitionPathwiseItoApproximationUpTo]

-- Proof sketch: the previous identity rewrites the multidimensional dyadic approximations as a
-- finite sum of the coordinate dyadic approximations. The coordinate convergence hypotheses then
-- give convergence of the whole finite sum, and `pathwiseMultidimensionalItoIntegral` is the
-- corresponding `limUnder`.
/-- If one chooses dyadic pathwise Itô realizations of the coordinate integrals
`∫₀ᵀ ∂ₖ F (Xₛ) dXₛᵏ`, then the multidimensional dyadic integral `∫₀ᵀ ∇F(Xₛ) dXₛ`
is the finite sum of those chosen realizations. -/
theorem pathwiseMultidimensionalItoIntegral_eq_sum_of_coordinateRealizations
    (F : State → ℝ) (X : VectorPathSpace d)
    (Ito : Fin d → NNReal → ℝ)
    (hIto :
      ∀ k : Fin d,
        HasPathwiseItoIntegralAlong
          (fun t ↦ (∂[k] F) (X t))
          (vectorPathComponent X k)
          dyadicPartitionSequence
          (Ito k))
    :
    pathwiseMultidimensionalItoIntegral F X = fun T ↦ ∑ k : Fin d, Ito k T := by
  ext T
  let H : Fin d → NNReal → ℝ := fun k t ↦ (∂[k] F) (X t)
  have hsum :
      Tendsto
        (fun n ↦
          ∑ k : Fin d,
            partitionPathwiseItoApproximationUpTo
              (H k)
              (vectorPathComponent X k)
              dyadicPartitionSequence
              T
              n)
        atTop
        (nhds (∑ k : Fin d, Ito k T)) := by
    refine tendsto_finset_sum Finset.univ fun k _ ↦ ?_
    simpa [H] using (hIto k).tendsto T
  have hEq :
      (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n) =
        fun n ↦
          ∑ k : Fin d,
            partitionPathwiseItoApproximationUpTo
              (H k)
              (vectorPathComponent X k)
              dyadicPartitionSequence
              T
              n := by
    funext n
    simpa [H] using dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals F X T n
  simpa [pathwiseMultidimensionalItoIntegral_def, hEq] using hsum.limUnder_eq

-- Proof sketch: choose a realization of each coordinate integral, apply the previous theorem,
-- and then rewrite each chosen realization to the canonical owner `pathwiseItoIntegralAlong`.
/-- Remark 25.31: if the coordinate dyadic pathwise Itô integrals
`∫₀ᵀ ∂ₖ F (Xₛ) dXₛᵏ` exist, then the multidimensional dyadic integral
`∫₀ᵀ ∇F(Xₛ) dXₛ` is the finite sum of the canonical coordinate integrals. -/
theorem pathwiseMultidimensionalItoIntegral_eq_sum_of_coordinateIntegrals
    (F : State → ℝ) (X : VectorPathSpace d)
    (hIto :
      ∀ k : Fin d,
        ∃ I : NNReal → ℝ,
          HasPathwiseItoIntegralAlong
            (fun t ↦ (∂[k] F) (X t))
            (vectorPathComponent X k)
            dyadicPartitionSequence
            I)
    :
    pathwiseMultidimensionalItoIntegral F X =
      fun T ↦
        ∑ k : Fin d,
          pathwiseItoIntegralAlong
            (fun t ↦ (∂[k] F) (X t))
            (vectorPathComponent X k)
            dyadicPartitionSequence
            T := by
  classical
  choose Ito hIto using hIto
  rw [pathwiseMultidimensionalItoIntegral_eq_sum_of_coordinateRealizations F X Ito hIto]
  funext T
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simpa using
    (congrArg (fun I : NNReal → ℝ ↦ I T) ((hIto k).eq_pathwiseItoIntegralAlong)).symm
