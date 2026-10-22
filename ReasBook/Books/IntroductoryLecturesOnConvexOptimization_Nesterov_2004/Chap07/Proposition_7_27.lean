/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient
open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace
open scoped Matrix.Norms.Frobenius
open scoped RightActions

noncomputable section

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/-- Helper for Proposition 7.27: endow ambient real matrices with the Frobenius normed-group
structure so matrix-valued derivatives use the intended Chapter 5 topology. -/
local instance ambientMatrixNormedAddCommGroup : NormedAddCommGroup Mₙ :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 7.27: scalar multiplication on ambient real matrices is measured with
the Frobenius norm. -/
local instance ambientMatrixNormedSpace : NormedSpace ℝ Mₙ :=
  Matrix.frobeniusNormedSpace

attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 1001] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

local instance instLocalChap07_Proposition_7_271 : CompleteSpace SymmMat := by
  letI : IsUniformAddGroup SymmMat := RealSymmetricMatrixSpace.symmetricMatrixIsUniformAddGroup
  exact FiniteDimensional.complete ℝ SymmMat

/- Proposition 7.27 lies in the repeated-squaring / symmetric-matrix trace-power domain.

Sampled owner-style declarations:
- Chapter 7 `repeatedSquaringX`, `repeatedSquaringY`, and their closed-form theorems in
  `Algorithm_7_11`, the canonical owner of the repeated-squaring orbit;
- Chapter 7 `linearMatrixCombination` and `linearMatrixCombination_apply` in `Definition_7_21`,
  the canonical ambient owner of the coefficient-sum matrix map `y ↦ ∑ᵢ yᵢ Aᵢ`;
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.isSymm`, the chapter owner and coercion bridge
  for real symmetric matrices;
- Chapter 6 `squaredLpMatrixNormSmoothing`, the chapter owner for the half-scaled
  trace-power smoothing functional;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the chapter owner for
  symmetric trace powers.

Best owner abstraction:
- source-facing: Proposition 7.27's repeated-squaring and gradient statements for the
  power-of-two specialization of the smoothing functional;
- core/canonical: `squaredLpMatrixNormSmoothing`, `π[k]` on `𝕊^n`, `repeatedSquaringX`,
  `repeatedSquaringY`, and `linearMatrixCombination`;
- bridge/view: the codomain restriction from the ambient Chapter 7 coefficient-sum map to
  `𝕊^n`, together with the power-of-two specialization of
  `squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace`.

Primitive data:
- `k : ℕ+`;
- a symmetric coefficient family `A : Fin m → SymmMat`;
- a point `y : Eₘ`.

Derived API:
- the thin bridge `symmetricLinearMatrixCombination A : Eₘ →ₗ[ℝ] SymmMat`;
- the positive smoothing order `2^(k-1)` whose Chapter 6 owner gives the `2^k` trace power;
- the proposition's specializations of the repeated-squaring closed forms to the ambient matrix
  underlying `A(y)`;
- the iterate-based rewriting and gradient formula for
  `squaredLpMatrixNormSmoothing (2^(k-1)) (A(y))`.

Source/core/bridge triage:
- source-facing: the Proposition 7.27 theorems below;
- core/canonical: `squaredLpMatrixNormSmoothing`, `π[k]`, `repeatedSquaringX`,
  `repeatedSquaringY`, and `linearMatrixCombination`;
- bridge/view: `symmetricLinearMatrixCombination` and the companion power-of-two trace formula.

This refinement moves the file from raw ambient matrices to the chapter's symmetric-matrix
surface. The only new public owner below is the thin codomain-restriction bridge from
`linearMatrixCombination` to `𝕊^n`; the smoothing objective is no longer rebuilt locally, and the
proposition is stated directly as the repeated-squaring and gradient bridge for the existing
Chapter 6 owner `squaredLpMatrixNormSmoothing`. The gradient theorem records the missing
nonzero-trace domain condition explicitly instead of relying on Lean's totalized division.
-/

private abbrev ambientLinearMatrixCombination
    (A : Fin m → SymmMat) : Eₘ →ₗ[ℝ] Mₙ :=
  linearMatrixCombination fun i ↦ (A i : Mₙ)

/-- The symmetric-matrix bridge `y ↦ A(y)` obtained by restricting the Chapter 7 ambient
coefficient-sum map to the canonical carrier `𝕊^n`. -/
abbrev symmetricLinearMatrixCombination
    (A : Fin m → SymmMat) : Eₘ →ₗ[ℝ] SymmMat :=
  LinearMap.codRestrict (𝕊^n) (ambientLinearMatrixCombination A) fun y ↦ by
    simpa [ambientLinearMatrixCombination, linearMatrixCombination_apply] using
      (show (((∑ i : Fin m, y i • A i : SymmMat) : Mₙ) ∈ 𝕊^n) from
        (∑ i : Fin m, y i • A i).2)

/-- Coercing `symmetricLinearMatrixCombination A y` to ambient matrices recovers the textbook
coefficient formula `A(y) = ∑ᵢ yᵢ Aᵢ`. -/
@[simp] theorem coe_symmetricLinearMatrixCombination_apply
    (A : Fin m → SymmMat) (y : Eₘ) :
    ((symmetricLinearMatrixCombination A y : SymmMat) : Mₙ) =
      ∑ i : Fin m, y i • (A i : Mₙ) :=
  rfl

/-- Evaluating `symmetricLinearMatrixCombination` gives the intrinsic symmetric sum
`A(y) = ∑ᵢ yᵢ Aᵢ` in `𝕊^n`. -/
@[simp] theorem symmetricLinearMatrixCombination_apply
    (A : Fin m → SymmMat) (y : Eₘ) :
    symmetricLinearMatrixCombination A y = ∑ i : Fin m, y i • A i := by
  apply Subtype.ext
  simpa using coe_symmetricLinearMatrixCombination_apply A y

/-- The positive smoothing order whose Chapter 6 owner specializes to the `2^k` trace power from
Proposition 7.27. -/
def powerOfTwoSmoothingOrder (k : ℕ+) : ℕ+ :=
  Nat.toPNat (2 ^ k.natPred) (pow_pos (by decide : 0 < 2) _)

private theorem two_mul_powerOfTwoSmoothingOrder (k : ℕ+) :
    2 * (powerOfTwoSmoothingOrder k : ℕ) = 2 ^ (k : ℕ) := by
  have hk : k.natPred + 1 = (k : ℕ) := by
    change Nat.succ k.natPred = (k : ℕ)
    exact congrArg PNat.val (PNat.succPNat_natPred k)
  change 2 * 2 ^ k.natPred = 2 ^ (k : ℕ)
  rw [← hk, Nat.pow_succ, Nat.mul_comm]

private theorem one_div_powerOfTwoSmoothingOrder (k : ℕ+) :
    1 / (powerOfTwoSmoothingOrder k : ℝ) = (2 : ℝ) / (2 ^ (k : ℕ) : ℝ) := by
  have hp : (powerOfTwoSmoothingOrder k : ℝ) ≠ 0 := by
    positivity
  have hk : (2 ^ (k : ℕ) : ℝ) = 2 * (powerOfTwoSmoothingOrder k : ℝ) := by
    exact_mod_cast (two_mul_powerOfTwoSmoothingOrder k).symm
  calc
    1 / (powerOfTwoSmoothingOrder k : ℝ) = (2 : ℝ) / (2 * (powerOfTwoSmoothingOrder k : ℝ)) := by
      field_simp [hp]
    _ = (2 : ℝ) / (2 ^ (k : ℕ) : ℝ) := by
      rw [hk]

/-- Writing Proposition 7.27's `f_{2^k}(y)` through the Chapter 6 owner expresses it as the
power-of-two specialization of `squaredLpMatrixNormSmoothing`. -/
theorem squaredLpMatrixNormSmoothing_powerOfTwo_eq_half_rpow_trace
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ) :
    squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
      (symmetricLinearMatrixCombination A y) =
      (1 / 2 : ℝ) *
        Real.rpow
          (Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))
          ((2 : ℝ) / (2 ^ (k : ℕ) : ℝ)) := by
  rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace, powerTrace_def,
    two_mul_powerOfTwoSmoothingOrder, one_div_powerOfTwoSmoothingOrder]

-- Proof sketch: specialize the canonical repeated-squaring first-component formula to the matrix
-- `A(y) = symmetricLinearMatrixCombination A y`.
/-- Helper for Proposition 7.27: the repeated-squaring first component `X_k` satisfies
`X_k = A(y)^(2^k)`. -/
theorem repeatedSquaringX_symmetricLinearMatrixCombination_eq_pow
    (A : Fin m → SymmMat) (y : Eₘ) (k : ℕ) :
    repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) k =
      (symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ k) :=
  repeatedSquaringX_eq_pow _ _

-- Proof sketch: specialize the canonical repeated-squaring second-component formula to the matrix
-- `A(y) = symmetricLinearMatrixCombination A y`.
/-- Helper for Proposition 7.27: the repeated-squaring second component `Y_k` satisfies
`Y_k = A(y)^(2^k - 1)`. -/
theorem repeatedSquaringY_symmetricLinearMatrixCombination_eq_pow_pred
    (A : Fin m → SymmMat) (y : Eₘ) (k : ℕ) :
    repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) k =
      (symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ k - 1) :=
  repeatedSquaringY_eq_pow_pred _ _

-- Proof sketch: substitute the identity from part (1) into the definition of
-- `squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)`.
/-- Helper for Proposition 7.27: for the power-of-two specialization of the Chapter 6 smoothing
owner, `f_{2^k}(y) = (1 / 2) * Trace(X_k)^(2 / 2^k)`. -/
theorem squaredLpMatrixNormSmoothing_powerOfTwo_eq_iterateX
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ) :
    squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
      (symmetricLinearMatrixCombination A y) =
      (1 / 2 : ℝ) *
        Real.rpow
          (Matrix.trace (repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ)))
          ((2 : ℝ) / (2 ^ (k : ℕ) : ℝ)) := by
  rw [squaredLpMatrixNormSmoothing_powerOfTwo_eq_half_rpow_trace,
    repeatedSquaringX_symmetricLinearMatrixCombination_eq_pow]

/-- Helper for Proposition 7.27: the matrix trace packaged as a continuous linear map on the
ambient matrix space. -/
private def traceContinuousLinearMap : Mₙ →L[ℝ] ℝ :=
  { toLinearMap := Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)
    cont := (Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)).continuous_of_finiteDimensional }

/-- Helper for Proposition 7.27: evaluating the bundled trace functional recovers the ordinary
matrix trace. -/
@[simp] private theorem traceContinuousLinearMap_apply (M : Mₙ) :
    traceContinuousLinearMap (n := n) M = Matrix.trace M :=
  rfl

/-- Helper for Proposition 7.27: right multiplication by a fixed matrix, bundled as a continuous
linear map on square matrices. -/
private def rightMulContinuousLinearMap (M : Mₙ) : Mₙ →L[ℝ] Mₙ :=
  ⟨LinearMap.mulRight ℝ M, (LinearMap.mulRight ℝ M).continuous_of_finiteDimensional⟩

/-- Helper for Proposition 7.27: evaluating the right-multiplication bundle recovers ordinary
matrix multiplication on the right. -/
@[simp] private theorem rightMulContinuousLinearMap_apply (M N : Mₙ) :
    rightMulContinuousLinearMap (n := n) M N = N * M :=
  rfl

/-- Helper for Proposition 7.27: the insertion-sum derivative of `A ↦ trace (A^k)` collapses by
cyclicity of trace to `k * trace (H * A^(k - 1))`. -/
private theorem tracePowInsertions_eq_natCast_mul_trace_mul_powPred
    (A H : Mₙ) (k : ℕ) :
    Matrix.trace ((Finset.range k).sum fun i ↦ A ^ (k - 1 - i) * H * A ^ i) =
      (k : ℝ) * Matrix.trace (H * A ^ (k - 1)) := by
  cases k with
  | zero =>
      -- The boundary case is empty on both sides.
      simp
  | succ m =>
      -- Move the trace through the finite sum and show each cyclic summand is identical.
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

/-- Helper for Proposition 7.27: the Frobenius pairing `⟪X^m, H⟫_F` is the ambient trace
`trace (H * X^m)` on symmetric matrices. -/
private theorem frobeniusInner_pow_eq_trace_mul_pow
    (m : ℕ) (X H : SymmMat) :
    ⟪X ^ m, H⟫_F = Matrix.trace ((H : Mₙ) * ((X : Mₙ) ^ m)) := by
  have hpowSymm : (((X : Mₙ) ^ m)ᵀ) = (X : Mₙ) ^ m := by
    simpa [Matrix.IsSymm] using (isSymm X).pow m
  -- Rewrite the Frobenius pairing to the ambient trace and remove the transpose by symmetry.
  calc
    ⟪X ^ m, H⟫_F
        = Matrix.trace ((((X ^ m : SymmMat) : Mₙ)ᵀ) * (H : Mₙ)) := by
            rw [RealSymmetricMatrixSpace.frobeniusInner_def]
    _ = Matrix.trace (((X : Mₙ) ^ m) * (H : Mₙ)) := by
          simp [RealSymmetricMatrixSpace.coe_pow, hpowSymm]
    _ = Matrix.trace ((H : Mₙ) * ((X : Mₙ) ^ m)) := by
          simpa using Matrix.trace_mul_comm ((X : Mₙ) ^ m) (H : Mₙ)

/-- Helper for Proposition 7.27: the symmetric-subtype inclusion packaged as a continuous linear
map into ambient matrices. -/
private def symmetricInclusion : SymmMat →L[ℝ] Mₙ :=
  { toLinearMap :=
      { toFun := fun X ↦ (X : Mₙ)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    cont := by
      exact
        ({ toFun := fun X : SymmMat ↦ (X : Mₙ)
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun _ _ ↦ rfl } : SymmMat →ₗ[ℝ] Mₙ).continuous_of_finiteDimensional }

/-- Helper for Proposition 7.27: evaluating the bundled symmetric inclusion recovers the ambient
matrix representative. -/
@[simp] private theorem symmetricInclusion_apply (X : SymmMat) :
    symmetricInclusion (n := n) X = (X : Mₙ) :=
  rfl

/-- Helper for Proposition 7.27: normalize the chain rule for precomposition by a bundled
continuous linear map so the resulting derivative is spelled as `g' ∘L L`. -/
private theorem hasFDerivAt_comp_clm_normalized
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} {g' : F →L[ℝ] ℝ} {L : E →L[ℝ] F} {x : E}
    (hg : HasFDerivAt g g' (L x)) :
    HasFDerivAt
      (fun x' : E ↦ g (L x'))
      (g' ∘L L)
      x := by
  -- Route correction: package bundled-CLM pullbacks once so later proofs stay in the exact
  -- derivative spelling `g' ∘L L`.
  simpa [Function.comp] using
    (HasFDerivAt.comp (f := L) (x := x) hg L.hasFDerivAt)

/-- Helper for Proposition 7.27: normalize scalar-valued chain rules so the derivative is
spelled exactly as a scalar multiple of the inner Fréchet derivative. -/
private theorem hasFDerivAt_comp_scalar_normalized
    {φ : ℝ → ℝ} {φ' : ℝ} {g : SymmMat → ℝ} {g' : SymmMat →L[ℝ] ℝ} {x : SymmMat}
    (hφ : HasDerivAt φ φ' (g x))
    (hg : HasFDerivAt g g' x) :
    HasFDerivAt (φ ∘ g) (φ' • g') x := by
  -- Route correction: package the scalar chain rule once so later proofs can fix the exact inner
  -- function and derivative spellings before composing.
  simpa [Function.comp] using
    (HasDerivAt.comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (f := g) (f' := g') (x := x) hφ hg)

/-- Helper for Proposition 7.27: fix the source-facing spelling of the ambient inclusion
`𝕊^n → Matrix (Fin n) (Fin n) ℝ` so chain-rule applications do not drift between coercions. -/
private abbrev symmetricInclusionFun : SymmMat → Mₙ :=
  fun Y ↦ (Y : Mₙ)

/-- Helper for Proposition 7.27: the symmetric-subtype inclusion has Fréchet derivative equal to
itself on the Frobenius carrier. -/
private theorem hasFDerivAt_symmetricInclusion
    (X : SymmMat) :
    HasFDerivAt
      (symmetricInclusionFun (n := n))
      (symmetricInclusion (n := n))
      X := by
  -- The bundled inclusion is linear, so its derivative is exactly the same map.
  simpa [symmetricInclusionFun] using (symmetricInclusion (n := n)).hasFDerivAt

/-- Helper for Proposition 7.27: an ambient Fréchet derivative restricts along the symmetric
inclusion by one reusable chain-rule step. -/
private theorem ambientHasFDerivAt_comp_symmetricInclusion
    {f : Mₙ → ℝ} {f' : Mₙ →L[ℝ] ℝ} {X : SymmMat}
    (hf : HasFDerivAt f f' (symmetricInclusion (n := n) X)) :
    HasFDerivAt
      (fun Y : SymmMat ↦ f (symmetricInclusion (n := n) Y))
      (f' ∘L symmetricInclusion (n := n))
      X := by
  -- Route correction: compose with the exact `Subtype.val` derivative so Lean does not invent a
  -- second spelling of the inclusion map.
  simpa [Function.comp] using hf.comp X (symmetricInclusion (n := n)).hasFDerivAt

/-- Helper for Proposition 7.27: the ambient matrix-valued derivative alias for
`A ↦ trace (A^k)`. -/
private def ambientPowerTraceDerivative
    (k : ℕ) (X : SymmMat) : Mₙ →L[ℝ] ℝ :=
  (k : ℝ) •
    (traceContinuousLinearMap (n := n)).comp
      (rightMulContinuousLinearMap (n := n) ((X : Mₙ) ^ (k - 1)))

/-- Helper for Proposition 7.27: evaluating the ambient trace-power derivative alias recovers the
textbook scalar formula. -/
@[simp] private theorem ambientPowerTraceDerivative_apply
    (k : ℕ) (X : SymmMat) (H : Mₙ) :
    ambientPowerTraceDerivative (n := n) k X H =
      (k : ℝ) * Matrix.trace (H * ((X : Mₙ) ^ (k - 1))) := by
  -- Unfold the alias once so later proofs can reuse the normalized scalar derivative surface.
  simp [ambientPowerTraceDerivative, traceContinuousLinearMap_apply,
    rightMulContinuousLinearMap_apply]

/-- Helper for Proposition 7.27: the restricted Fréchet derivative of `π[k]` on the symmetric
carrier. -/
private def powerTraceDerivative
    (k : ℕ) (X : SymmMat) : SymmMat →L[ℝ] ℝ :=
  (ambientPowerTraceDerivative (n := n) k X).comp (symmetricInclusion (n := n))

/-- Helper for Proposition 7.27: evaluating the restricted trace-power derivative gives the same
ambient trace formula on symmetric directions. -/
@[simp] private theorem powerTraceDerivative_apply
    (k : ℕ) (X H : SymmMat) :
    powerTraceDerivative (n := n) k X H =
      (k : ℝ) * Matrix.trace ((H : Mₙ) * ((X : Mₙ) ^ (k - 1))) := by
  -- Reduce the restricted derivative to the ambient alias on the matrix representative of `H`.
  simp [powerTraceDerivative, ambientPowerTraceDerivative_apply]

/-- Helper for Proposition 7.27: the symmetric trace-power owner `π[k]` has the textbook
Fréchet derivative packaged as a continuous linear map on `𝕊^n`. -/
private theorem powerTrace_hasFDerivAt
    (k : ℕ) (X : SymmMat) :
    HasFDerivAt
      (π[k] : SymmMat → ℝ)
      (powerTraceDerivative (n := n) k X)
      X := by
  -- Route correction: keep the power derivative on the ambient matrix owner, collapse it there,
  -- and only then restrict back to `𝕊^n`.
  have hpow :
      HasFDerivAt
        (fun A : Mₙ ↦ A ^ k)
        (∑ i ∈ Finset.range k,
          (X : Mₙ) ^ (k.pred - i) •> ContinuousLinearMap.id ℝ Mₙ <• (X : Mₙ) ^ i)
        (X : Mₙ) := by
    -- Differentiate the ambient matrix power before applying the trace.
    simpa using (hasFDerivAt_pow' (𝕜 := ℝ) (n := k) (x := (X : Mₙ)))
  have htrace :
      HasFDerivAt
        (fun A : Mₙ ↦ Matrix.trace (A ^ k))
        (((traceContinuousLinearMap (n := n)).comp
            (∑ i ∈ Finset.range k,
              (X : Mₙ) ^ (k.pred - i) •> ContinuousLinearMap.id ℝ Mₙ <•
                (X : Mₙ) ^ i)) : Mₙ →L[ℝ] ℝ)
        (X : Mₙ) := by
    -- Postcompose the matrix-power derivative with the continuous trace functional.
    have htraceCLM :
        HasFDerivAt
          ((traceContinuousLinearMap (n := n)) ∘ fun A : Mₙ ↦ A ^ k)
          (((traceContinuousLinearMap (n := n)).comp
              (∑ i ∈ Finset.range k,
                (X : Mₙ) ^ (k.pred - i) •> ContinuousLinearMap.id ℝ Mₙ <•
                  (X : Mₙ) ^ i)) : Mₙ →L[ℝ] ℝ)
          (X : Mₙ) := by
      simpa using (traceContinuousLinearMap (n := n)).hasFDerivAt.comp (X : Mₙ) hpow
    simpa [Function.comp, traceContinuousLinearMap_apply] using htraceCLM
  have hcollapsed :
      HasFDerivAt
        (fun A : Mₙ ↦ Matrix.trace (A ^ k))
        (ambientPowerTraceDerivative (n := n) k X)
        (X : Mₙ) := by
    -- Collapse the insertion sum under the trace to the scalar textbook derivative.
    refine htrace.congr_fderiv ?_
    ext H
    simpa [ambientPowerTraceDerivative, traceContinuousLinearMap_apply,
      rightMulContinuousLinearMap_apply] using
      tracePowInsertions_eq_natCast_mul_trace_mul_powPred (A := (X : Mₙ)) (H := H) k
  have hcollapsed' :
      HasFDerivAt
        (fun A : Mₙ ↦ Matrix.trace (A ^ k))
        (ambientPowerTraceDerivative (n := n) k X)
        (symmetricInclusion (n := n) X) := by
    simpa [symmetricInclusion_apply] using hcollapsed
  have hrestricted :
      HasFDerivAt
        (fun Y : SymmMat ↦ Matrix.trace ((symmetricInclusion (n := n) Y) ^ k))
        (powerTraceDerivative (n := n) k X)
        X := by
    simpa [Function.comp, powerTraceDerivative] using
      ambientHasFDerivAt_comp_symmetricInclusion (n := n) hcollapsed'
  -- Rewrite the restricted ambient trace-power function back to the source-facing owner `π[k]`.
  simpa [RealSymmetricMatrixSpace.powerTrace_def, powerTraceDerivative, symmetricInclusion_apply]
    using hrestricted

/-- Helper for Proposition 7.27: the linear map `y ↦ A(y)` as a continuous linear map on the
ambient Euclidean/Frobenius spaces. -/
private def symmetricLinearMatrixCombinationCLM
    (A : Fin m → SymmMat) : Eₘ →L[ℝ] SymmMat :=
  { toLinearMap := symmetricLinearMatrixCombination A
    cont := (symmetricLinearMatrixCombination A).continuous_of_finiteDimensional }

/-- Helper for Proposition 7.27: evaluating the bundled coefficient-sum map recovers the
unbundled linear map `y ↦ A(y)`. -/
@[simp] private theorem symmetricLinearMatrixCombinationCLM_apply
    (A : Fin m → SymmMat) (y : Eₘ) :
    symmetricLinearMatrixCombinationCLM A y = symmetricLinearMatrixCombination A y :=
  rfl

/-- Helper for Proposition 7.27: the even trace power appearing in the power-of-two smoothing
formula is nonnegative. -/
private theorem powerOfTwoTrace_nonneg
    (k : ℕ+) (X : SymmMat) :
    0 ≤ Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ))) := by
  let p : ℕ := powerOfTwoSmoothingOrder k
  have hk : 2 ^ (k : ℕ) = p + p := by
    calc
      2 ^ (k : ℕ) = 2 * p := by
        simpa [p] using (two_mul_powerOfTwoSmoothingOrder k).symm
      _ = p + p := by rw [two_mul]
  calc
    0 ≤ ⟪X ^ p, X ^ p⟫_F := frobeniusInner_self_nonneg (X := X ^ p)
    _ = Matrix.trace (((X ^ p : SymmMat) : Mₙ) * ((X : Mₙ) ^ p)) := by
          rw [frobeniusInner_pow_eq_trace_mul_pow (n := n) (m := p) X (X ^ p)]
    _ = Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ))) := by
          rw [RealSymmetricMatrixSpace.coe_pow, hk, pow_add]

/-- Helper for Proposition 7.27: the scalar coefficient produced by differentiating
`(1 / 2) * Trace(X^(2^k))^(2 / 2^k)` matches the textbook factor
`(2 * F(X)) / ((2^k) * Trace(X^(2^k)))`. -/
private theorem powerOfTwoSmoothingScalarCoefficient_eq
    (k : ℕ+) (X : SymmMat)
    (hXtrace : Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ))) ≠ 0) :
    (1 / 2 : ℝ) *
      (((2 : ℝ) / (2 ^ (k : ℕ) : ℝ)) *
        Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ))) ^
          (((2 : ℝ) / (2 ^ (k : ℕ) : ℝ)) - 1)) =
      ((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X) /
        ((2 ^ (k : ℕ) : ℝ) * Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ)))) := by
  let t : ℝ := Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ)))
  let N : ℝ := (2 ^ (k : ℕ) : ℝ)
  let p : ℝ := (2 : ℝ) / N
  have hN : N ≠ 0 := by
    dsimp [N]
    positivity
  have ht_ne : t ≠ 0 := by
    simpa [t] using hXtrace
  have hsmooth_eq :
      (2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X = t ^ p := by
    rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace, powerTrace_def,
      two_mul_powerOfTwoSmoothingOrder, one_div_powerOfTwoSmoothingOrder]
    simp [t, p, N]
  change (1 / 2 : ℝ) * (p * t ^ (p - 1)) =
    ((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X) / (N * t)
  calc
    (1 / 2 : ℝ) * (p * t ^ (p - 1))
        = (t ^ p) / (N * t) := by
            rw [Real.rpow_sub_one ht_ne]
            dsimp [p]
            field_simp [hN, ht_ne]
    _ = ((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X) / (N * t) := by
          rw [hsmooth_eq]

/-- Helper for Proposition 7.27: the power-of-two smoothing owner has the expected Fréchet
derivative on `𝕊^n` whenever the trace base is nonzero. -/
private theorem powerOfTwoSmoothing_hasFDerivAt
    (k : ℕ+) (X : SymmMat)
    (hXtrace : Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ))) ≠ 0) :
    HasFDerivAt
      (fun Z : SymmMat ↦ squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) Z)
      ((((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X) /
          ((2 ^ (k : ℕ) : ℝ) * Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ))))) •
        powerTraceDerivative (n := n) (2 ^ (k : ℕ)) X)
      X := by
  let p : ℝ := (2 : ℝ) / (2 ^ (k : ℕ) : ℝ)
  have hpowerTrace :
      HasFDerivAt
        (π[2 ^ (k : ℕ)] : SymmMat → ℝ)
        (powerTraceDerivative (n := n) (2 ^ (k : ℕ)) X)
        X :=
    powerTrace_hasFDerivAt (n := n) (2 ^ (k : ℕ)) X
  have hpowerTrace_ne : (π[2 ^ (k : ℕ)] X) ≠ 0 := by
    simpa [RealSymmetricMatrixSpace.powerTrace_def] using hXtrace
  have houter :
      HasDerivAt
        (fun t : ℝ ↦ (1 / 2 : ℝ) * t ^ p)
        ((1 / 2 : ℝ) * (p * (π[2 ^ (k : ℕ)] X) ^ (p - 1)))
        (π[2 ^ (k : ℕ)] X) := by
    have hrpow :
        HasDerivAt
          (fun t : ℝ ↦ t ^ p)
          (p * (π[2 ^ (k : ℕ)] X) ^ (p - 1))
          (π[2 ^ (k : ℕ)] X) := by
      -- Differentiate the scalar power at the nonzero trace value.
      simpa [p] using
        (Real.hasDerivAt_rpow_const (x := π[2 ^ (k : ℕ)] X) (p := p) (Or.inl hpowerTrace_ne))
    -- Scale the scalar derivative by the outer factor `1 / 2`.
    simpa [mul_assoc] using hrpow.const_mul (1 / 2 : ℝ)
  have hscaled :
      HasFDerivAt
        (fun Z : SymmMat ↦ (1 / 2 : ℝ) * (π[2 ^ (k : ℕ)] Z) ^ p)
        (((1 / 2 : ℝ) * (p * (π[2 ^ (k : ℕ)] X) ^ (p - 1))) •
          powerTraceDerivative (n := n) (2 ^ (k : ℕ)) X)
        X := by
    -- Route correction: pin the inner function and derivative explicitly when applying the scalar
    -- chain rule so Lean stays on the existing `powerTraceDerivative` surface.
    simpa [Function.comp, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_assoc, mul_comm, mul_left_comm] using
      hasFDerivAt_comp_scalar_normalized
        (φ := fun t : ℝ ↦ (1 / 2 : ℝ) * t ^ p)
        (φ' := (1 / 2 : ℝ) * (p * (π[2 ^ (k : ℕ)] X) ^ (p - 1)))
        (g := (π[2 ^ (k : ℕ)] : SymmMat → ℝ))
        (g' := powerTraceDerivative (n := n) (2 ^ (k : ℕ)) X)
        (x := X)
        houter
        hpowerTrace
  have hcoeff :
      ((1 / 2 : ℝ) * (p * (π[2 ^ (k : ℕ)] X) ^ (p - 1))) =
        ((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X) /
          ((2 ^ (k : ℕ) : ℝ) * Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ)))) := by
    -- Normalize the scalar coefficient to the textbook expression involving `f_{2^k}(X)`.
    simpa [p, RealSymmetricMatrixSpace.powerTrace_def] using
      powerOfTwoSmoothingScalarCoefficient_eq (n := n) k X hXtrace
  -- Rewrite the owner function to `squaredLpMatrixNormSmoothing` and collapse the scalar factor.
  convert hscaled using 1
  · funext Z
    rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace,
      two_mul_powerOfTwoSmoothingOrder, one_div_powerOfTwoSmoothingOrder]
    simp [p]
  · rw [hcoeff]

/-- Helper for Proposition 7.27: precomposing a scalar field on `𝕊^n` with the linear map
`y ↦ A(y)` pulls back its Fréchet derivative by composition. -/
private abbrev symmetricLinearMatrixCombinationFun
    (A : Fin m → SymmMat) : Eₘ → SymmMat :=
  fun y ↦ symmetricLinearMatrixCombination A y

/-- Helper for Proposition 7.27: precomposing a scalar field on `𝕊^n` with the linear map
`y ↦ A(y)` pulls back its Fréchet derivative by composition. -/
private theorem hasFDerivAt_symmetricLinearMatrixCombination
    (A : Fin m → SymmMat) (y : Eₘ) :
    HasFDerivAt
      (symmetricLinearMatrixCombinationFun A)
      (symmetricLinearMatrixCombinationCLM A)
      y := by
  -- The bundled linear matrix-combination map is its own Fréchet derivative.
  simpa [symmetricLinearMatrixCombinationFun, symmetricLinearMatrixCombinationCLM_apply] using
    (symmetricLinearMatrixCombinationCLM A).hasFDerivAt

/-- Helper for Proposition 7.27: precomposing a scalar field on `𝕊^n` with the linear map
`y ↦ A(y)` pulls back its Fréchet derivative by composition. -/
private theorem hasFDerivAt_comp_symmetricLinearMatrixCombination
    (A : Fin m → SymmMat) {f : SymmMat → ℝ} {f' : SymmMat →L[ℝ] ℝ} {y : Eₘ}
    (hf : HasFDerivAt f f' (symmetricLinearMatrixCombinationCLM A y)) :
    HasFDerivAt
      (fun y' : Eₘ ↦ f (symmetricLinearMatrixCombination A y'))
      (f' ∘L symmetricLinearMatrixCombinationCLM A)
      y := by
  -- Route correction: compose with the exact derivative of the coefficient map, keeping both the
  -- basepoint and the outer derivative on the owner surface already used by `hf`.
  convert hf.comp y (symmetricLinearMatrixCombinationCLM A).hasFDerivAt using 1

/-- Helper for Proposition 7.27: the Frobenius pairing with `A i` matches the ambient
trace formula involving the repeated-squaring iterate `Y_k`. -/
private theorem frobeniusInner_powerOfTwoPred_eq_trace_repeatedSquaringY_mul
    (A : Fin m → SymmMat) (y : Eₘ) (k : ℕ) (i : Fin m) :
    ⟪(symmetricLinearMatrixCombination A y) ^ (2 ^ k - 1), A i⟫_F =
      Matrix.trace
        (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) k * (A i : Mₙ)) := by
  -- Replace the Frobenius pairing by the ambient trace and then substitute the repeated-squaring
  -- closed form for `Y_k`.
  rw [repeatedSquaringY_symmetricLinearMatrixCombination_eq_pow_pred]
  rw [frobeniusInner_pow_eq_trace_mul_pow]
  simpa using
    Matrix.trace_mul_comm
      (A i : Mₙ)
      ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ k - 1))

/-- Helper for Proposition 7.27: evaluating the pulled-back smoothing derivative on the standard
Euclidean basis vector `e_i` gives the advertised `i`-th gradient coordinate. -/
private theorem powerOfTwoSmoothingPullbackDerivative_apply_basisFun
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ) (i : Fin m) :
    ((((((2 : ℝ) *
          squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
            (symmetricLinearMatrixCombination A y)) /
        (((2 ^ (k : ℕ)) : ℝ) *
          Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
      powerTraceDerivative (n := n) (2 ^ (k : ℕ))
        (symmetricLinearMatrixCombination A y)) ∘L
      symmetricLinearMatrixCombinationCLM A)
      (EuclideanSpace.basisFun (Fin m) ℝ i)) =
      ((((2 : ℝ) *
          squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
            (symmetricLinearMatrixCombination A y)) /
        Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ)))) *
        Matrix.trace
          (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
            (A i : Mₙ))) := by
  let X : SymmMat := symmetricLinearMatrixCombination A y
  let c : ℝ :=
    (((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X) /
      (((2 ^ (k : ℕ)) : ℝ) * Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ)))))
  let d : ℝ :=
    (((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) X) /
      Matrix.trace ((X : Mₙ) ^ (2 ^ (k : ℕ))))
  have hcoeff : c * (2 ^ (k : ℕ) : ℝ) = d := by
    -- Cancel the single power-of-two denominator produced by `powerTraceDerivative_apply`.
    dsimp [c, d]
    have hpow_ne : ((2 ^ (k : ℕ)) : ℝ) ≠ 0 := by
      positivity
    field_simp [hpow_ne]
  have hbasis :
      symmetricLinearMatrixCombinationCLM A (EuclideanSpace.basisFun (Fin m) ℝ i) = A i := by
    change symmetricLinearMatrixCombination A (EuclideanSpace.basisFun (Fin m) ℝ i) = A i
    simp [symmetricLinearMatrixCombination_apply]
  -- Evaluate the pullback derivative on the basis vector `e_i`, reduce `A(e_i)` to `A_i`,
  -- and rewrite the resulting power to the repeated-squaring iterate `Y_k`.
  calc
    (((c • powerTraceDerivative (n := n) (2 ^ (k : ℕ)) X) ∘L
          symmetricLinearMatrixCombinationCLM A)
        (EuclideanSpace.basisFun (Fin m) ℝ i))
        = (c • powerTraceDerivative (n := n) (2 ^ (k : ℕ)) X) (A i) := by
            rw [ContinuousLinearMap.comp_apply, hbasis]
    _ = c * ((2 ^ (k : ℕ) : ℝ) *
          Matrix.trace ((A i : Mₙ) * ((X : Mₙ) ^ (2 ^ (k : ℕ) - 1)))) := by
            simp [powerTraceDerivative_apply]
    _ = d * Matrix.trace ((A i : Mₙ) * ((X : Mₙ) ^ (2 ^ (k : ℕ) - 1))) := by
          calc
            c * ((2 ^ (k : ℕ) : ℝ) *
                Matrix.trace ((A i : Mₙ) * ((X : Mₙ) ^ (2 ^ (k : ℕ) - 1))))
                =
              (c * (2 ^ (k : ℕ) : ℝ)) *
                Matrix.trace ((A i : Mₙ) * ((X : Mₙ) ^ (2 ^ (k : ℕ) - 1))) := by
                    ring
            _ = d *
                  Matrix.trace ((A i : Mₙ) * ((X : Mₙ) ^ (2 ^ (k : ℕ) - 1))) := by
                  rw [hcoeff]
    _ = d *
          Matrix.trace
            (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
              (A i : Mₙ)) := by
          rw [repeatedSquaringY_symmetricLinearMatrixCombination_eq_pow_pred]
          congr 1
          simpa [X] using
            Matrix.trace_mul_comm
              (A i : Mₙ)
              ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ) - 1))
    _ = ((((2 : ℝ) *
            squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
              (symmetricLinearMatrixCombination A y)) /
          Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ)))) *
          Matrix.trace
            (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
              (A i : Mₙ))) := by
          simp [d, X]

/-- Helper for Proposition 7.27: after pulling the smoothing derivative back along
`y ↦ A(y)`, the resulting continuous linear functional is the Riesz dual of the advertised
Euclidean gradient vector. -/
private theorem powerOfTwoSmoothingPullbackDerivative_eq_gradientVector
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ) :
    (((((2 : ℝ) *
          squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
            (symmetricLinearMatrixCombination A y)) /
        (((2 ^ (k : ℕ)) : ℝ) *
          Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
      powerTraceDerivative (n := n) (2 ^ (k : ℕ))
        (symmetricLinearMatrixCombination A y)) ∘L
      symmetricLinearMatrixCombinationCLM A) =
      InnerProductSpace.toDual ℝ Eₘ
        ((EuclideanSpace.equiv (Fin m) ℝ).symm <| fun i : Fin m ↦
          (((2 : ℝ) *
              squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
                (symmetricLinearMatrixCombination A y)) /
            Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ)))) *
            Matrix.trace
            (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
              (A i : Mₙ))) := by
  let g : Eₘ :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm <| fun i : Fin m ↦
      ((((2 : ℝ) *
          squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
            (symmetricLinearMatrixCombination A y)) /
        Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ)))) *
        Matrix.trace
          (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
            (A i : Mₙ)))
  -- Compare the two continuous linear maps on the Euclidean basis and then extend by linearity.
  apply ContinuousLinearMap.ext
  intro v
  have hv : (∑ i : Fin m, v i • EuclideanSpace.basisFun (Fin m) ℝ i) = v := by
    simpa using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  calc
    ((((((2 : ℝ) *
            squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
              (symmetricLinearMatrixCombination A y)) /
          (((2 ^ (k : ℕ)) : ℝ) *
            Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
        powerTraceDerivative (n := n) (2 ^ (k : ℕ))
          (symmetricLinearMatrixCombination A y)) ∘L
        symmetricLinearMatrixCombinationCLM A) v)
        =
      ((((((2 : ℝ) *
            squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
              (symmetricLinearMatrixCombination A y)) /
          (((2 ^ (k : ℕ)) : ℝ) *
            Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
        powerTraceDerivative (n := n) (2 ^ (k : ℕ))
          (symmetricLinearMatrixCombination A y)) ∘L
        symmetricLinearMatrixCombinationCLM A)
        (∑ i : Fin m, v i • EuclideanSpace.basisFun (Fin m) ℝ i)) := by
          rw [hv]
    _ = ∑ i : Fin m, v i *
          ((((((2 : ℝ) *
                squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
                  (symmetricLinearMatrixCombination A y)) /
              (((2 ^ (k : ℕ)) : ℝ) *
                Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
            powerTraceDerivative (n := n) (2 ^ (k : ℕ))
              (symmetricLinearMatrixCombination A y)) ∘L
            symmetricLinearMatrixCombinationCLM A)
            (EuclideanSpace.basisFun (Fin m) ℝ i)) := by
          simp
    _ = ∑ i : Fin m, v i * g i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [powerOfTwoSmoothingPullbackDerivative_apply_basisFun (n := n) (k := k) (A := A)
            (y := y) (i := i)]
          simp [g]
    _ = ∑ i : Fin m, v i *
          (InnerProductSpace.toDual ℝ Eₘ g (EuclideanSpace.basisFun (Fin m) ℝ i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [InnerProductSpace.toDual_apply_apply, real_inner_comm]
          exact congrArg (fun t : ℝ ↦ v i * t)
            (EuclideanSpace.basisFun_inner (x := g) (i := i)).symm
    _ = (InnerProductSpace.toDual ℝ Eₘ g)
          (∑ i : Fin m, v i • EuclideanSpace.basisFun (Fin m) ℝ i) := by
          simp
    _ = (InnerProductSpace.toDual ℝ Eₘ g) v := by
          rw [hv]

-- Proof sketch: differentiate the affine matrix map `y ↦ A(y)` entrywise, use the trace-power
-- derivative of `M ↦ Trace(M^(2^k))` on symmetric matrices, note that the even trace power is
-- automatically nonnegative, and finish with the chain rule for the outer power
-- `t ↦ (1 / 2) * t^(2 / 2^k)`.
/-- Proposition 7.27: if `Trace(X_k) ≠ 0`, then the power-of-two specialization of
`squaredLpMatrixNormSmoothing` has gradient
`∇ f_{2^k}(y)^(i) = (2 f_{2^k}(y) / Trace(X_k)) * Trace(Y_k Aᵢ)`. -/
theorem squaredLpMatrixNormSmoothing_powerOfTwo_hasGradientAt
    (k : ℕ+) (A : Fin m → SymmMat) (y : Eₘ)
    (htrace :
      Matrix.trace (repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ)) ≠ 0) :
    HasGradientAt
      (fun y' ↦
        squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
          (symmetricLinearMatrixCombination A y'))
      ((EuclideanSpace.equiv (Fin m) ℝ).symm <| fun i : Fin m ↦
        ((2 : ℝ) *
            squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
              (symmetricLinearMatrixCombination A y) /
            Matrix.trace
              (repeatedSquaringX (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ))) *
          Matrix.trace
              (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
              (A i : Mₙ)))
      y := by
  -- Route correction: assemble the owner derivative first, then rewrite the pulled-back
  -- continuous linear functional to the advertised gradient vector in one step.
  rw [hasGradientAt_iff_hasFDerivAt]
  have htraceAmbient := htrace
  have htraceAmbient :
      Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))) ≠ 0 := by
    rw [repeatedSquaringX_symmetricLinearMatrixCombination_eq_pow] at htraceAmbient
    exact htraceAmbient
  have howner :
      HasFDerivAt
        (fun Z : SymmMat ↦ squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) Z)
        ((((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
              (symmetricLinearMatrixCombination A y)) /
            ((2 ^ (k : ℕ) : ℝ) *
              Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
          powerTraceDerivative (n := n) (2 ^ (k : ℕ))
            (symmetricLinearMatrixCombination A y))
        (symmetricLinearMatrixCombination A y) :=
    powerOfTwoSmoothing_hasFDerivAt
      (n := n) k (symmetricLinearMatrixCombination A y) htraceAmbient
  have howner' :
      HasFDerivAt
        (fun Z : SymmMat ↦ squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k) Z)
        ((((2 : ℝ) * squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
              (symmetricLinearMatrixCombination A y)) /
            ((2 ^ (k : ℕ) : ℝ) *
              Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
          powerTraceDerivative (n := n) (2 ^ (k : ℕ))
            (symmetricLinearMatrixCombination A y))
        (symmetricLinearMatrixCombinationCLM A y) := by
    simpa [symmetricLinearMatrixCombinationCLM_apply] using howner
  have hpullback :
      HasFDerivAt
        (fun y' ↦
          squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
            (symmetricLinearMatrixCombination A y'))
        (((((2 : ℝ) *
              squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
                (symmetricLinearMatrixCombination A y)) /
            (((2 ^ (k : ℕ)) : ℝ) *
              Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ))))) •
          powerTraceDerivative (n := n) (2 ^ (k : ℕ))
            (symmetricLinearMatrixCombination A y)) ∘L
          symmetricLinearMatrixCombinationCLM A)
        y := by
    simpa [Function.comp, symmetricLinearMatrixCombinationCLM_apply] using
      hasFDerivAt_comp_symmetricLinearMatrixCombination (n := n) (A := A) howner'
  have hgradient :
      HasFDerivAt
        (fun y' ↦
          squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
            (symmetricLinearMatrixCombination A y'))
        (InnerProductSpace.toDual ℝ Eₘ
          ((EuclideanSpace.equiv (Fin m) ℝ).symm <| fun i : Fin m ↦
            (((2 : ℝ) *
                squaredLpMatrixNormSmoothing (powerOfTwoSmoothingOrder k)
                  (symmetricLinearMatrixCombination A y)) /
              Matrix.trace ((symmetricLinearMatrixCombination A y : Mₙ) ^ (2 ^ (k : ℕ)))) *
              Matrix.trace
                (repeatedSquaringY (symmetricLinearMatrixCombination A y : Mₙ) (k : ℕ) *
                  (A i : Mₙ))))
        y := by
    -- Replace the pulled-back derivative by the Riesz dual of the coordinate formula.
    exact hpullback.congr_fderiv
      (powerOfTwoSmoothingPullbackDerivative_eq_gradientVector (n := n) k A y)
  convert hgradient using 1
  ext i
  rw [repeatedSquaringX_symmetricLinearMatrixCombination_eq_pow]

end
