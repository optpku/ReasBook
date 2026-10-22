/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Pow
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace
open scoped RightActions

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Proposition 6.33: use the Frobenius normed-group structure on ambient matrices
when differentiating matrix-valued polynomial maps. -/
local instance ambientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 6.33: scalar multiplication on ambient matrices is measured with the
Frobenius norm. -/
local instance ambientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.frobeniusNormedSpace

/-- Helper for Proposition 6.33: the ambient matrix ring carries the Frobenius-compatible normed
ring structure used by `hasFDerivAt_pow'`. -/
local instance ambientMatrixNormedRing : NormedRing Mat :=
  Matrix.frobeniusNormedRing

/-- Helper for Proposition 6.33: the ambient matrix algebra over `ℝ` carries the Frobenius
normed-algebra structure used by the calculus API. -/
local instance ambientMatrixNormedAlgebra : NormedAlgebra ℝ Mat :=
  Matrix.frobeniusNormedAlgebra

attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 1001] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

/-- Helper for Proposition 6.33: package `Matrix.trace` as a continuous linear map on the
ambient Frobenius space of real matrices. -/
private def traceContinuousLinearMap : Mat →L[ℝ] ℝ :=
  { toLinearMap := Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)
    cont := (Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.33: evaluating the bundled trace map recovers the usual trace. -/
@[simp] private theorem traceContinuousLinearMap_apply (A : Mat) :
    traceContinuousLinearMap (n := n) A = Matrix.trace A :=
  rfl

/-- Helper for Proposition 6.33: right multiplication by a fixed ambient matrix, bundled as a
continuous linear map. -/
private def rightMulContinuousLinearMap (A : Mat) : Mat →L[ℝ] Mat :=
  ⟨LinearMap.mulRight ℝ A, (LinearMap.mulRight ℝ A).continuous_of_finiteDimensional⟩

/-- Helper for Proposition 6.33: evaluating the bundled right-multiplication map recovers the
ordinary product `B ↦ B * A`. -/
@[simp] private theorem rightMulContinuousLinearMap_apply (A B : Mat) :
    rightMulContinuousLinearMap (n := n) A B = B * A :=
  rfl

/-- Helper for Proposition 6.33: collapse the insertion-sum derivative of `A ↦ trace (A^k)` to
the scalar formula `k * trace (H * A^(k - 1))` using cyclicity of trace. -/
private theorem tracePowInsertions_eq_natCast_mul_trace_mul_powPred
    (A H : Mat) (k : ℕ) :
    Matrix.trace ((Finset.range k).sum fun i ↦ A ^ (k - 1 - i) * H * A ^ i) =
      (k : ℝ) * Matrix.trace (H * A ^ (k - 1)) := by
  cases k with
  | zero =>
      -- The boundary case is empty on both sides.
      simp
  | succ m =>
      -- Move the trace through the sum and show all summands are cyclic permutations
      -- of the same scalar.
      rw [Matrix.trace_sum]
      have hsum :
          (Finset.range (m + 1)).sum (fun i ↦ Matrix.trace (A ^ (m - i) * H * A ^ i)) =
            (Finset.range (m + 1)).sum (fun _ ↦ Matrix.trace (H * A ^ m)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc
          Matrix.trace (A ^ (m - i) * H * A ^ i)
              = Matrix.trace ((A ^ i * A ^ (m - i)) * H) := by
                  simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A ^ (m - i)) H (A ^ i)
          _ = Matrix.trace (H * (A ^ i * A ^ (m - i))) := by
                simpa using Matrix.trace_mul_comm (A ^ i * A ^ (m - i)) H
          _ = Matrix.trace (H * A ^ m) := by
                have hpow : A ^ i * A ^ (m - i) = A ^ m := by
                  simpa [Nat.add_sub_of_le hi_le] using (pow_add A i (m - i)).symm
                simp [hpow]
      simpa using
        calc
          (Finset.range (m + 1)).sum (fun i ↦ Matrix.trace (A ^ (m - i) * H * A ^ i))
              = (Finset.range (m + 1)).sum (fun _ ↦ Matrix.trace (H * A ^ m)) := hsum
          _ = (m + 1 : ℝ) * Matrix.trace (H * A ^ m) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- Helper for Proposition 6.33: on symmetric matrices, `⟪X^m, H⟫_F` is the ambient trace
`trace (H * X^m)`. -/
private theorem frobeniusInner_pow_eq_trace_mul_pow
    (m : ℕ) (X H : SymmMat) :
    ⟪X ^ m, H⟫_F = Matrix.trace ((H : Mat) * ((X : Mat) ^ m)) := by
  have hpowSymm : (((X : Mat) ^ m)ᵀ) = (X : Mat) ^ m := by
    simpa [Matrix.IsSymm] using (isSymm X).pow m
  -- Rewrite the Frobenius pairing into the ambient trace and remove the transpose by symmetry.
  calc
    ⟪X ^ m, H⟫_F
        = Matrix.trace ((((X ^ m : SymmMat) : Mat)ᵀ) * (H : Mat)) := by
            rw [RealSymmetricMatrixSpace.frobeniusInner_def]
    _ = Matrix.trace (((X : Mat) ^ m) * (H : Mat)) := by
          simp [RealSymmetricMatrixSpace.coe_pow, hpowSymm]
    _ = Matrix.trace ((H : Mat) * ((X : Mat) ^ m)) := by
          simpa using Matrix.trace_mul_comm ((X : Mat) ^ m) (H : Mat)

/-- Helper for Proposition 6.33: the symmetric-subtype inclusion packaged as a continuous linear
map into ambient matrices. -/
private def symmetricInclusion : SymmMat →L[ℝ] Mat :=
  { toLinearMap :=
      { toFun := fun X ↦ (X : Mat)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    cont := by
      exact
        ({ toFun := fun X : SymmMat ↦ (X : Mat)
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun _ _ ↦ rfl } : SymmMat →ₗ[ℝ] Mat).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.33: evaluating the bundled inclusion recovers the ambient matrix
representative of a symmetric matrix. -/
@[simp] private theorem symmetricInclusion_apply (X : SymmMat) :
    symmetricInclusion (n := n) X = (X : Mat) :=
  rfl

/-- Helper for Proposition 6.33: restrict an ambient Fréchet derivative along the canonical
inclusion `𝕊^n ↪ Mat` in one reusable chain-rule step. -/
private theorem ambientHasFDerivAt_comp_symmetricInclusion
    {f : Mat → ℝ} {f' : Mat →L[ℝ] ℝ} {X : SymmMat}
    (hf : HasFDerivAt f f' (symmetricInclusion (n := n) X)) :
    HasFDerivAt
      (fun Y : SymmMat ↦ f (symmetricInclusion (n := n) Y))
      (f' ∘L symmetricInclusion (n := n))
      X := by
  -- Route correction: keep all chain-rule applications on the bundled inclusion so Lean
  -- does not generate competing coercion spellings.
  simpa [Function.comp] using hf.comp X (symmetricInclusion (n := n)).hasFDerivAt

/-- Helper for Proposition 6.33: the ambient derivative alias for `A ↦ trace (A^k)` at a
symmetric base point. -/
private def ambientPowerTraceDerivative
    (k : ℕ) (X : SymmMat) : Mat →L[ℝ] ℝ :=
  (k : ℝ) •
    (traceContinuousLinearMap (n := n)).comp
      (rightMulContinuousLinearMap (n := n) ((X : Mat) ^ (k - 1)))

/-- Helper for Proposition 6.33: evaluating the ambient derivative alias recovers
`k * trace (H * X^(k - 1))`. -/
@[simp] private theorem ambientPowerTraceDerivative_apply
    (k : ℕ) (X : SymmMat) (H : Mat) :
    ambientPowerTraceDerivative (n := n) k X H =
      (k : ℝ) * Matrix.trace (H * ((X : Mat) ^ (k - 1))) := by
  -- Unfold the alias once so later proofs stay on the stable scalar surface.
  simp [ambientPowerTraceDerivative, traceContinuousLinearMap_apply,
    rightMulContinuousLinearMap_apply]

/-- Helper for Proposition 6.33: the restricted derivative of `π[k]` on the intrinsic symmetric
carrier `𝕊^n`. -/
private def powerTraceDerivative
    (k : ℕ) (X : SymmMat) : SymmMat →L[ℝ] ℝ :=
  (ambientPowerTraceDerivative (n := n) k X).comp (symmetricInclusion (n := n))

/-- Helper for Proposition 6.33: evaluating the restricted derivative gives the same scalar trace
formula as in the ambient matrix space. -/
@[simp] private theorem powerTraceDerivative_apply
    (k : ℕ) (X H : SymmMat) :
    powerTraceDerivative (n := n) k X H =
      (k : ℝ) * Matrix.trace ((H : Mat) * ((X : Mat) ^ (k - 1))) := by
  -- Reduce the restricted derivative to the ambient alias on the matrix representative of `H`.
  simp [powerTraceDerivative, ambientPowerTraceDerivative_apply]

/-- Helper for Proposition 6.33: the chapter owner `π[k]` has the textbook Fréchet derivative on
`𝕊^n`, packaged as a continuous linear map. -/
private theorem powerTrace_hasFDerivAt
    (k : ℕ) (X : SymmMat) :
    HasFDerivAt
      (π[k] : SymmMat → ℝ)
      (powerTraceDerivative (n := n) k X)
      X := by
  -- Route correction: first differentiate the ambient owner `A ↦ trace (A^k)`, collapse the
  -- insertion sum there, and only then restrict back to `𝕊^n`.
  have hpow :
      HasFDerivAt
        (fun A : Mat ↦ A ^ k)
        (∑ i ∈ Finset.range k,
          (X : Mat) ^ (k.pred - i) •> ContinuousLinearMap.id ℝ Mat <• (X : Mat) ^ i)
        (X : Mat) := by
    -- Differentiate the ambient matrix power before applying the trace.
    simpa using (hasFDerivAt_pow' (𝕜 := ℝ) (n := k) (x := (X : Mat)))
  have htrace :
      HasFDerivAt
        (fun A : Mat ↦ Matrix.trace (A ^ k))
        (((traceContinuousLinearMap (n := n)).comp
            (∑ i ∈ Finset.range k,
              (X : Mat) ^ (k.pred - i) •> ContinuousLinearMap.id ℝ Mat <• (X : Mat) ^ i)) :
          Mat →L[ℝ] ℝ)
        (X : Mat) := by
    -- Postcompose the power derivative with the continuous trace functional.
    have htraceCLM :
        HasFDerivAt
          ((traceContinuousLinearMap (n := n)) ∘ fun A : Mat ↦ A ^ k)
          (((traceContinuousLinearMap (n := n)).comp
              (∑ i ∈ Finset.range k,
                (X : Mat) ^ (k.pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                  (X : Mat) ^ i)) : Mat →L[ℝ] ℝ)
          (X : Mat) := by
      simpa using (traceContinuousLinearMap (n := n)).hasFDerivAt.comp (X : Mat) hpow
    simpa [Function.comp, traceContinuousLinearMap_apply] using htraceCLM
  have hcollapsed :
      HasFDerivAt
        (fun A : Mat ↦ Matrix.trace (A ^ k))
        (ambientPowerTraceDerivative (n := n) k X)
        (X : Mat) := by
    -- Collapse the insertion sum under the trace to the scalar textbook derivative.
    refine htrace.congr_fderiv ?_
    ext H
    simpa [ambientPowerTraceDerivative, traceContinuousLinearMap_apply,
      rightMulContinuousLinearMap_apply] using
      tracePowInsertions_eq_natCast_mul_trace_mul_powPred (A := (X : Mat)) (H := H) k
  have hrestricted :
      HasFDerivAt
        (fun Y : SymmMat ↦ Matrix.trace ((symmetricInclusion (n := n) Y) ^ k))
        (powerTraceDerivative (n := n) k X)
        X := by
    simpa [Function.comp, powerTraceDerivative] using
      ambientHasFDerivAt_comp_symmetricInclusion (n := n) hcollapsed
  -- Rewrite the restricted ambient owner back to the chapter notation `π[k]`.
  simpa [RealSymmetricMatrixSpace.powerTrace_def, powerTraceDerivative, symmetricInclusion_apply]
    using hrestricted

/-- Helper for Proposition 6.33: the scalar directional first-derivative formula
`Y ↦ k * ⟪Y^(k-1), H⟫_F` has derivative given by the textbook insertion sum. -/
private theorem powerTraceDirectionalFDeriv_eq_frobenius_sum
    (k : ℕ) (hk : 1 ≤ k) (X H : SymmMat) :
    fderiv ℝ (fun Y : SymmMat ↦ (k : ℝ) * ⟪Y ^ (k - 1), H⟫_F) X H =
      (k : ℝ) *
        (Finset.range (k - 1)).sum fun p ↦
          Matrix.trace
            (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
                ((X ^ (k - 2 - p) : SymmMat) : Mat))ᵀ) * (H : Mat)) := by
  have hpow :
      HasFDerivAt
        (fun A : Mat ↦ A ^ (k - 1))
        (∑ i ∈ Finset.range (k - 1),
          (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
            (X : Mat) ^ i)
        (X : Mat) := by
    -- Differentiate the ambient power map at exponent `k - 1`.
    simpa using (hasFDerivAt_pow' (𝕜 := ℝ) (n := k - 1) (x := (X : Mat)))
  have hmul :
      HasFDerivAt
        (fun A : Mat ↦ A ^ (k - 1) * (H : Mat))
        (((rightMulContinuousLinearMap (n := n) (H : Mat)).comp
            (∑ i ∈ Finset.range (k - 1),
              (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                (X : Mat) ^ i)) : Mat →L[ℝ] Mat)
        (X : Mat) := by
    -- Postcompose with right multiplication by the fixed direction `H`.
    have hmulCLM :
        HasFDerivAt
          ((rightMulContinuousLinearMap (n := n) (H : Mat)) ∘ fun A : Mat ↦ A ^ (k - 1))
          (((rightMulContinuousLinearMap (n := n) (H : Mat)).comp
              (∑ i ∈ Finset.range (k - 1),
                (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                  (X : Mat) ^ i)) : Mat →L[ℝ] Mat)
          (X : Mat) := by
      simpa using (rightMulContinuousLinearMap (n := n) (H : Mat)).hasFDerivAt.comp (X : Mat) hpow
    simpa [Function.comp, rightMulContinuousLinearMap_apply] using hmulCLM
  have htrace :
      HasFDerivAt
        (fun A : Mat ↦ (k : ℝ) * Matrix.trace (A ^ (k - 1) * (H : Mat)))
        ((k : ℝ) •
          ((traceContinuousLinearMap (n := n)).comp
            ((rightMulContinuousLinearMap (n := n) (H : Mat)).comp
              (∑ i ∈ Finset.range (k - 1),
                (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                  (X : Mat) ^ i))) )
        (X : Mat) := by
    -- Apply trace to the differentiated right-multiplied power and then scale by `k`.
    have htraceBase :
        HasFDerivAt
          (fun A : Mat ↦ Matrix.trace (A ^ (k - 1) * (H : Mat)))
          (((traceContinuousLinearMap (n := n)).comp
              ((rightMulContinuousLinearMap (n := n) (H : Mat)).comp
                (∑ i ∈ Finset.range (k - 1),
                  (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                    (X : Mat) ^ i))) : Mat →L[ℝ] ℝ)
          (X : Mat) := by
      have htraceCLM :
          HasFDerivAt
            ((traceContinuousLinearMap (n := n)) ∘ fun A : Mat ↦ A ^ (k - 1) * (H : Mat))
            (((traceContinuousLinearMap (n := n)).comp
                ((rightMulContinuousLinearMap (n := n) (H : Mat)).comp
                  (∑ i ∈ Finset.range (k - 1),
                    (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                      (X : Mat) ^ i))) : Mat →L[ℝ] ℝ)
            (X : Mat) := by
        simpa using (traceContinuousLinearMap (n := n)).hasFDerivAt.comp (X : Mat) hmul
      simpa [Function.comp, traceContinuousLinearMap_apply] using htraceCLM
    simpa [smul_eq_mul] using htraceBase.const_smul (k : ℝ)
  have hrestricted :
      HasFDerivAt
        (fun Y : SymmMat ↦
          (k : ℝ) * Matrix.trace (((symmetricInclusion (n := n) Y) ^ (k - 1)) * (H : Mat)))
        ((((k : ℝ) •
            ((traceContinuousLinearMap (n := n)).comp
              ((rightMulContinuousLinearMap (n := n) (H : Mat)).comp
                (∑ i ∈ Finset.range (k - 1),
                  (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                    (X : Mat) ^ i)))) ) ∘L symmetricInclusion (n := n))
        X := by
    simpa [Function.comp] using
      ambientHasFDerivAt_comp_symmetricInclusion (n := n) htrace
  have happlyTrace :
      fderiv ℝ
          (fun Y : SymmMat ↦
            (k : ℝ) * Matrix.trace (((symmetricInclusion (n := n) Y) ^ (k - 1)) * (H : Mat)))
          X H =
        (k : ℝ) *
          (Finset.range (k - 1)).sum fun p ↦
            Matrix.trace ((((X : Mat) ^ ((k - 1).pred - p) * (H : Mat) *
              (X : Mat) ^ p)) * (H : Mat)) := by
    -- Evaluate the restricted derivative at `H` and unfold the composed linear maps.
    have hderiv :=
      congrArg
        (fun L : SymmMat →L[ℝ] ℝ => L H)
        (show
            fderiv ℝ
              (fun Y : SymmMat ↦
                (k : ℝ) * Matrix.trace (((symmetricInclusion (n := n) Y) ^ (k - 1)) * (H : Mat)))
              X =
                ((((k : ℝ) •
                    ((traceContinuousLinearMap (n := n)).comp
                      ((rightMulContinuousLinearMap (n := n) (H : Mat)).comp
                        (∑ i ∈ Finset.range (k - 1),
                          (X : Mat) ^ ((k - 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <•
                            (X : Mat) ^ i)))) ) ∘L symmetricInclusion (n := n))
          from hrestricted.fderiv)
    simpa [ContinuousLinearMap.comp_apply, traceContinuousLinearMap_apply,
      rightMulContinuousLinearMap_apply, Matrix.mul_assoc, Finset.smul_sum] using hderiv
  have htarget :
      (Finset.range (k - 1)).sum
          (fun p ↦
            Matrix.trace
              ((((X : Mat) ^ ((k - 1).pred - p) * (H : Mat) * (X : Mat) ^ p)) * (H : Mat))) =
        (Finset.range (k - 1)).sum fun p ↦
          Matrix.trace
            (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
                ((X ^ (k - 2 - p) : SymmMat) : Mat))ᵀ) * (H : Mat)) := by
    -- Use symmetry to rewrite the summands into the theorem's transpose spelling.
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp_le : p ≤ k - 2 := by
      have hp_lt : p < k - 1 := Finset.mem_range.mp hp
      omega
    have hpowIndex : (k - 1).pred - p = k - 2 - p := by
      calc
        (k - 1).pred - p = ((k - 1) - 1) - p := by rw [Nat.pred_eq_sub_one]
        _ = k - 2 - p := by omega
    calc
      Matrix.trace ((((X : Mat) ^ ((k - 1).pred - p) * (H : Mat) * (X : Mat) ^ p)) * (H : Mat))
          = Matrix.trace ((((X : Mat) ^ (k - 2 - p) * (H : Mat) * (X : Mat) ^ p)) * (H : Mat)) := by
              rw [hpowIndex]
      _ = Matrix.trace
            (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
                ((X ^ (k - 2 - p) : SymmMat) : Mat))ᵀ) * (H : Mat)) := by
            simp [RealSymmetricMatrixSpace.coe_pow, Matrix.transpose_mul, Matrix.mul_assoc,
              (RealSymmetricMatrixSpace.isSymm X).eq, (RealSymmetricMatrixSpace.isSymm H).eq]
  -- Rewrite the source-facing scalar function into the ambient trace surface and use the explicit
  -- derivative computed there.
  have htraceSurface :
      (fun Y : SymmMat ↦ (k : ℝ) * ⟪Y ^ (k - 1), H⟫_F) =
        (fun Y : SymmMat ↦
          (k : ℝ) * Matrix.trace (((symmetricInclusion (n := n) Y) ^ (k - 1)) * (H : Mat))) := by
    funext Y
    rw [frobeniusInner_pow_eq_trace_mul_pow]
    rw [Matrix.trace_mul_comm]
    simp [symmetricInclusion_apply]
  calc
    fderiv ℝ (fun Y : SymmMat ↦ (k : ℝ) * ⟪Y ^ (k - 1), H⟫_F) X H
        = fderiv ℝ
            (fun Y : SymmMat ↦
              (k : ℝ) * Matrix.trace (((symmetricInclusion (n := n) Y) ^ (k - 1)) * (H : Mat)))
            X H := by rw [htraceSurface]
    _ = (k : ℝ) *
          (Finset.range (k - 1)).sum fun p ↦
            Matrix.trace
              ((((X : Mat) ^ ((k - 1).pred - p) * (H : Mat) * (X : Mat) ^ p)) *
                (H : Mat)) := happlyTrace
    _ = (k : ℝ) *
          (Finset.range (k - 1)).sum fun p ↦
            Matrix.trace
              (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
                  ((X ^ (k - 2 - p) : SymmMat) : Mat))ᵀ) * (H : Mat)) := by
              rw [htarget]

/- Proposition 6.33 lies in the chapter's ambient matrix trace-power / Frobenius differential
domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the established
  Frobenius owner on `𝕊^n`;
- mathlib `Matrix.trace`, the canonical ambient owner of `X ↦ Trace (X^k)`;
- `RealSymmetricMatrixSpace.powerTrace` and `powerTrace_eq_frobeniusInner_one` in
  `Definition_6_42`, the source-facing symmetric-matrix owner and bridge to the canonical ambient
  trace expression.

Best owner abstraction:
- source-facing: the differentiability and derivative formulas for `π_k(X) = trace (X^k)` on the
  intrinsic symmetric-matrix carrier `𝕊^n`, written `π[k] X`;
- core/canonical: `fun X : Mat ↦ Matrix.trace (X ^ k)`;
- bridge/view: restriction of the ambient owner to `𝕊^n`, together with the Chapter 5 Frobenius
  owner `⟪·, ·⟫_F` and the ambient Frobenius sum for the second derivative.

Primitive data:
- `k : ℕ`
- `X H : 𝕊^n`

Derived API:
- the source-facing owner `π[k] X`
- the canonical symmetric-matrix power `X ^ k`
- the ambient trace pairing only for the second-derivative bridge expansion
- the derivative theorems below

This refinement keeps the theorem surface of this file on the source-facing symmetric-matrix
quantity `π[k] X` from `Definition_6_42`, while using the canonical ambient trace expression as the
core owner. -/

/-- For Proposition 6.33, on the symmetric-matrix space `𝕊^n`, the trace-power map
`X ↦ Trace (X^k)` is twice Fréchet differentiable for `k ≥ 1`; the companion theorems below recover
the textbook Frobenius first- and second-derivative formulas for `π_k(X) = Trace (X^k)`. -/
theorem powerTrace_contDiff
    (k : ℕ) (hk : 1 ≤ k) :
    ContDiff ℝ 2 (π[k] : SymmMat → ℝ) := by
  have _ : 0 < k := Nat.succ_le_iff.mp hk
  -- The ambient polynomial owner `A ↦ trace (A^k)` is `C²`, and restricting along the bundled
  -- inclusion `𝕊^n ↪ Mat` preserves that regularity.
  have hambientPow : ContDiff ℝ 2 (fun A : Mat ↦ A ^ k) := by
    fun_prop
  have hambientTrace : ContDiff ℝ 2 (fun A : Mat ↦ Matrix.trace (A ^ k)) := by
    simpa [Function.comp, traceContinuousLinearMap_apply] using
      (traceContinuousLinearMap (n := n)).contDiff.comp hambientPow
  have hrestricted :
      ContDiff ℝ 2 (fun Y : SymmMat ↦ Matrix.trace ((symmetricInclusion (n := n) Y) ^ k)) := by
    simpa [Function.comp] using hambientTrace.comp (symmetricInclusion (n := n)).contDiff
  -- The hypothesis `hk` matches the textbook statement; the ambient polynomial route is smooth
  -- for every exponent.
  simpa [RealSymmetricMatrixSpace.powerTrace_def, symmetricInclusion_apply] using hrestricted

/-- On `𝕊^n`, the Fréchet derivative of `X ↦ Trace (X^k)` in the direction `H` is
`k ⟪X^(k-1), H⟫_F` for `k ≥ 1`. -/
theorem powerTrace_fderiv_eq_frobenius
    (k : ℕ) (hk : 1 ≤ k) (X H : SymmMat) :
    fderiv ℝ (π[k] : SymmMat → ℝ) X H =
      (k : ℝ) * ⟪X ^ (k - 1), H⟫_F := by
  have _ : 0 < k := Nat.succ_le_iff.mp hk
  -- Evaluate the packaged Fréchet derivative from `powerTrace_hasFDerivAt`.
  have hderiv :=
    congrArg
      (fun L : SymmMat →L[ℝ] ℝ => L H)
      (show
          fderiv ℝ (π[k] : SymmMat → ℝ) X = powerTraceDerivative (n := n) k X
        from (powerTrace_hasFDerivAt (n := n) k X).fderiv)
  calc
    fderiv ℝ (π[k] : SymmMat → ℝ) X H
        = powerTraceDerivative (n := n) k X H := hderiv
    _ = (k : ℝ) * Matrix.trace ((H : Mat) * ((X : Mat) ^ (k - 1))) := by
          simp [powerTraceDerivative_apply]
    _ = (k : ℝ) * ⟪X ^ (k - 1), H⟫_F := by
          rw [frobeniusInner_pow_eq_trace_mul_pow]

/-- Proposition 6.33: on `𝕊^n`, the second directional derivative of
`X ↦ Trace (X^k)` is the ambient trace/Frobenius sum
`k ∑_{p=0}^{k-2} trace ((X^p H X^(k-2-p))ᵀ H)` for `k ≥ 1`. -/
theorem powerTrace_iteratedFDeriv_two_eq_frobenius_sum
    (k : ℕ) (hk : 1 ≤ k) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] =
      (k : ℝ) *
        (Finset.range (k - 1)).sum fun p ↦
          Matrix.trace
            (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
                ((X ^ (k - 2 - p) : SymmMat) : Mat))ᵀ) * (H : Mat)) := by
  have hfdiff :
      DifferentiableAt ℝ (fderiv ℝ (π[k] : SymmMat → ℝ)) X := by
    -- `π[k]` is `C²`, so its Fréchet derivative field is differentiable.
    let hcontFDeriv : ContDiff ℝ 1 (fderiv ℝ (π[k] : SymmMat → ℝ)) :=
      (powerTrace_contDiff (n := n) k hk).fderiv_right (m := 1) (by norm_num)
    exact hcontFDeriv.contDiffAt.differentiableAt one_ne_zero
  have happly :
      fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ (π[k] : SymmMat → ℝ) Y H) X =
        (fderiv ℝ (fderiv ℝ (π[k] : SymmMat → ℝ)) X).flip H := by
    -- Differentiate the `fderiv` field after freezing the outer direction at `H`.
    simpa using
      (fderiv_clm_apply (𝕜 := ℝ) (x := X)
        (c := fderiv ℝ (π[k] : SymmMat → ℝ)) (u := fun _ : SymmMat ↦ H)
        hfdiff (differentiableAt_const H))
  have hiter :
      iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] =
        fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ (π[k] : SymmMat → ℝ) Y H) X H := by
    -- Rewrite the second iterated derivative as the derivative of the scalar directional slice.
    calc
      iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H]
          = fderiv ℝ (fderiv ℝ (π[k] : SymmMat → ℝ)) X H H := by
              simp [iteratedFDeriv_two_apply]
      _ = ((fderiv ℝ (fderiv ℝ (π[k] : SymmMat → ℝ)) X).flip H) H := by
            rfl
      _ = fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ (π[k] : SymmMat → ℝ) Y H) X H := by
            rw [happly]
  have hreplace :
      (fun Y : SymmMat ↦ fderiv ℝ (π[k] : SymmMat → ℝ) Y H) =
        (fun Y : SymmMat ↦ (k : ℝ) * ⟪Y ^ (k - 1), H⟫_F) := by
    -- Replace the scalar directional derivative by the closed first-derivative formula.
    funext Y
    exact powerTrace_fderiv_eq_frobenius (n := n) k hk Y H
  calc
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H]
        = fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ (π[k] : SymmMat → ℝ) Y H) X H := hiter
    _ = fderiv ℝ (fun Y : SymmMat ↦ (k : ℝ) * ⟪Y ^ (k - 1), H⟫_F) X H := by
          rw [hreplace]
    _ = (k : ℝ) *
          (Finset.range (k - 1)).sum fun p ↦
            Matrix.trace
              (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
                  ((X ^ (k - 2 - p) : SymmMat) : Mat))ᵀ) * (H : Mat)) := by
            exact powerTraceDirectionalFDeriv_eq_frobenius_sum (n := n) k hk X H
