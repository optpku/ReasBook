/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

/- Definition 21.58: recall the dyadic square-variation class `𝒞_qv`, whose source-facing role
is used in the pathwise Itô discussion below. -/

/- Domain-style sampling for the scalar pathwise Itô layer:
* primary domain: pathwise stochastic integration along admissible partition sequences;
* source-facing square-variation owner: `HasContinuousSquareVariationAlongPartition`;
* source-facing set view: `𝒞_qvAlong`;
* primitive data: `partitionPathwiseItoApproximationUpTo`;
* canonical derived objects: `pathwiseItoIntegralAlong` and `pathwiseItoCorrectionAlong`. -/

/-- The left-point partition sum `∑ H_t (X_{t'} - X_t)` on `[0, T]` along the `n`-th row of an
admissible partition sequence `P`. -/
def partitionPathwiseItoApproximationUpTo
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    H (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k))

/-- `HasPathwiseItoIntegralAlong H X P I` means that the left-point partition sums of `H` against
`X` along the admissible partition sequence `P` converge pointwise to the chosen realization `I`.
-/
def HasPathwiseItoIntegralAlong
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (I : NNReal → ℝ) : Prop :=
  ∀ T : NNReal,
    Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (nhds (I T))

/-- A pathwise Itô integral realization yields the defining convergence statement at each fixed
time horizon. -/
theorem HasPathwiseItoIntegralAlong.tendsto
    {H : NNReal → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal}
    [IsAdmissiblePartitionSequence P] {I : NNReal → ℝ}
    (hI : HasPathwiseItoIntegralAlong H X P I) (T : NNReal) :
    Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (nhds (I T)) :=
  hI T

/-- The canonical bridge/view `pathwiseItoIntegralAlong H X P` is the pointwise `limUnder`
realization of the left-point partition sums. -/
noncomputable def pathwiseItoIntegralAlong
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    NNReal → ℝ :=
  fun T ↦ limUnder atTop (partitionPathwiseItoApproximationUpTo H X P T)

/-- Any chosen realization of the left-point partition sums agrees with the canonical `limUnder`
bridge `pathwiseItoIntegralAlong H X P`. -/
theorem HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong
    {H : NNReal → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    {I : NNReal → ℝ}
    (hI : HasPathwiseItoIntegralAlong H X P I) :
    pathwiseItoIntegralAlong H X P = I := by
  ext T
  simpa [pathwiseItoIntegralAlong] using (hI T).limUnder_eq

/-- Helper for Theorem 25.25: any genuine limit of the left-point partition sums identifies the
canonical `pathwiseItoIntegralAlong` value at the same horizon. -/
theorem pathwiseItoIntegralAlong_eq_of_tendsto
    {H : NNReal → ℝ} {X : PathSpace} {P : ℕ → ℕ → NNReal} [IsAdmissiblePartitionSequence P]
    {L : ℝ} (T : NNReal)
    (hlim : Tendsto (partitionPathwiseItoApproximationUpTo H X P T) atTop (nhds L)) :
    pathwiseItoIntegralAlong H X P T = L := by
  rw [pathwiseItoIntegralAlong, hlim.limUnder_eq]

/-- The canonical quadratic correction in the scalar pathwise Itô formula is the endpoint
increment of `F ∘ X` after subtracting the canonical pathwise Itô integral of `F' (X)`. -/
noncomputable def pathwiseItoCorrectionAlong
    (F : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    NNReal → ℝ :=
  fun T ↦
    F (X T) - F (X 0) -
      pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T

/-- Evaluating `pathwiseItoCorrectionAlong F X P` rewrites it as the endpoint increment of `F ∘ X`
minus the canonical Itô integral term. -/
theorem pathwiseItoCorrectionAlong_def
    (F : ℝ → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    pathwiseItoCorrectionAlong F X P T =
      F (X T) - F (X 0) -
        pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T := rfl

/-- Helper for Theorem 25.25: the chosen correction term is exactly the residual after removing the
canonical Itô integral from the endpoint increment of `F ∘ X`. -/
theorem pathwiseItoFormula_of_hasSquareVariation
    (F : ℝ → ℝ) (_hf : ContDiff ℝ 2 F)
    (X : PathSpace)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (V : PathSpace)
    (_hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T +
        pathwiseItoCorrectionAlong F X P T := by
  -- Rewrite the correction term and close by the elementary identity `a - b + b = a`.
  rw [pathwiseItoCorrectionAlong_def]
  rw [add_comm]
  exact Eq.symm <|
    sub_add_cancel
      (F (X T) - F (X 0))
      (pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T)

/-- Theorem 25.25: for an admissible partition sequence `P`, a path
`X ∈ 𝒞_qv^P`, and a `C²` function `F`, the canonical pathwise Itô integral realization of the
left-point sums for `F' (X)` along `P` satisfies the pathwise Itô formula on `[0, T]` with the
canonical quadratic correction term `pathwiseItoCorrectionAlong F X P T`. -/
theorem pathwiseItoFormula
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T +
        pathwiseItoCorrectionAlong F X P T := by
  rcases hX with ⟨V, hV⟩
  exact pathwiseItoFormula_of_hasSquareVariation F hf X P V hV T

/-- Source-facing `𝒞_qv^P` form of Theorem 25.25. -/
theorem pathwiseItoFormula_of_mem_𝒞_qvAlong
    (F : ℝ → ℝ) (hf : ContDiff ℝ 2 F)
    (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P)
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseItoIntegralAlong (fun t ↦ deriv F (X t)) X P T +
        pathwiseItoCorrectionAlong F X P T := by
  simpa [mem_𝒞_qvAlong_iff] using
    pathwiseItoFormula F hf X P ((mem_𝒞_qvAlong_iff X).1 hX) T
